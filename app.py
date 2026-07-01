"""
PolisEnergia — Operation Suite
==============================
App Streamlit per gestione autoletture, preventivi di connessione e archivio.

Versione: 2.1
Modifiche 2.1 (fix):
  - Franchigia/limitatore: checkbox con key stabili (lo stato non si perde piu'
    nei rerun) e calcolo di v_att con guardia su SOGLIA_LIMITATORE, simmetrica a v_new.
  - Scadenza firma robusta: timestamp epoch 'Creato_TS' come fonte primaria +
    parsing difensivo (dayfirst) della colonna 'Data' come fallback.

Modifiche principali rispetto alla 1.4:
  - OTP salvato nel Google Sheet (i vecchi link vengono invalidati al reinvio)
  - Funzione `calcola_stato_reale` deduplicata e globale
  - Cache GSheets con TTL configurabile (perf)
  - Cache ARERA in memoria
  - Magic numbers spostati nelle costanti
  - Fix crash su data malformata in pagina firma
  - Import puliti, codice morto rimosso
  - Errori tecnici nascosti in produzione (mostrati solo in modalità debug)
"""

import streamlit as st
import math
import pandas as pd
import secrets
import io
import xml.etree.ElementTree as ET
import re
import os
import smtplib
import ssl
import zipfile
import zlib
import json
import base64 as _b64
import numpy as np
import streamlit.components.v1 as components

from collections import defaultdict
from datetime import datetime, timedelta
from streamlit_gsheets import GSheetsConnection
from fpdf import FPDF
from fpdf.enums import XPos, YPos
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.application import MIMEApplication

# ==============================================================================
# 1. CONFIGURAZIONE PAGINA
# ==============================================================================
st.set_page_config(
    page_title="PolisEnergia - Operation Suite",
    page_icon="⚡",
    layout="wide",
    initial_sidebar_state="auto",
)

# ==============================================================================
# 2. COSTANTI GLOBALI
# ==============================================================================

# --- Dati aziendali ---
IBAN_POLIS          = "IT80P0103015200000007044056"
NOME_BANCA          = "Monte dei Paschi di Siena"
INTESTATARIO        = "POLISENERGIA SRL"
IBAN_LABEL          = f"{IBAN_POLIS} - {NOME_BANCA}"
MAIL_CC             = "assistenza@polisenergia.it"
APP_URL             = "https://operation-polisenergia.streamlit.app"

# --- Configurazione operativa ---
OTP_SCADENZA_GIORNI = 30        # validità link di firma
GSHEETS_CACHE_TTL   = 60        # secondi di cache lettura archivio
GSHEETS_MAX_CHARS   = 49000     # limite per HTML compresso nella cella
DEBUG_MODE          = False     # True per mostrare dettagli errori

# --- Tariffe preventivo ---
TIC_DOMESTICO_LE6   = 62.30
TIC_ALTRI_USI_BT    = 78.81
TIC_MT              = 62.74
ONERI_ISTRUTTORIA   = 27.42
SPOSTAMENTO_10MT    = 226.36
FISSO_BASE_CALCOLO  = 25.88
COSTO_PASSAGGIO_MT  = 494.83

# --- Soglie e tariffe fornitura temporanea ---
TEMP_LE40_NO_ATTR   = 168.01    # ≤40 kW senza attraversamento stradale
TEMP_LE40_ATTR      = 280.01    # ≤40 kW con attraversamento stradale
SOGLIA_TEMP_KW      = 40        # potenza che separa tariffa fissa da quota distributore
SOGLIA_LIMITATORE   = 30        # potenza max per gestione franchigia 10%
SOGLIA_AGEVOL_DOM   = 6         # kW max per tariffa agevolata domestico

# --- Bollo ---
BOLLO_ESENTE        = 2.0
SOGLIA_BOLLO        = 77.47

# ==============================================================================
# 3. CSS
# ==============================================================================
st.markdown("""
    <style>
    .stApp { background-color: #004a99; }
    .stMain h1, .stMain h2, .stMain h3, .stMain p, .stMain label { color: white !important; }
    [data-testid="stSidebar"] { background-color: #f0f2f6; }
    [data-testid="stSidebar"] * { color: #004a99 !important; }
    .stTextInput input { background-color: white !important; color: black !important; }
    div.stButton > button:first-child {
        background-color: #28a745 !important; color: white !important;
        border-radius: 8px !important; font-weight: bold !important; width: 100% !important;
    }
    header { visibility: visible !important; background: transparent !important; }
    footer { visibility: hidden; }
    [data-testid="stSidebarCollapsedControl"] {
        color: white !important;
        background-color: rgba(255,255,255,0.2) !important;
        border-radius: 50% !important;
        left: 10px !important;
        top: 10px !important;
    }
    [data-testid="stSidebarCollapsedControl"] svg { fill: white !important; }
    </style>
""", unsafe_allow_html=True)

# ==============================================================================
# 4. FUNZIONI DI UTILITÀ
# ==============================================================================

def mostra_errore(msg_utente: str, dettaglio: Exception | str = ""):
    """Mostra errore generico all'utente; il dettaglio tecnico solo in DEBUG_MODE."""
    st.error(msg_utente)
    if DEBUG_MODE and dettaglio:
        st.caption(f"Dettaglio tecnico: {dettaglio}")


def formatta_data_italiana(data_raw) -> str:
    """Converte qualsiasi formato data in GG/MM/AAAA usando pandas (robusto)."""
    try:
        return pd.to_datetime(str(data_raw), dayfirst=True, errors="raise").strftime("%d/%m/%Y")
    except Exception:
        # Fallback con regex per casi edge che pandas rifiuta
        d = str(data_raw).strip().split(' ')[0]
        try:
            parti = re.split(r'[/.\-]', d)
            if len(parti) == 3:
                if len(parti[0]) == 4:
                    anno, mese, giorno = parti[0], parti[1].zfill(2), parti[2].zfill(2)
                else:
                    giorno, mese, anno = parti[0].zfill(2), parti[1].zfill(2), parti[2]
                if len(anno) == 2:
                    anno = "20" + anno
                return f"{giorno}/{mese}/{anno}"
        except Exception:
            pass
        return d


def pulisci_valore(valore) -> str | None:
    """Pulisce un valore di lettura per il formato XML (9 cifre con zfill)."""
    val = str(valore).strip().lower()
    if val in {"", "nan", "none", "0", "0,00", "0.00"}:
        return None
    parte_intera = val.split(',')[0]
    if '.' in parte_intera and len(parte_intera.split('.')[-1]) <= 2:
        parte_intera = parte_intera.rsplit('.', 1)[0]
    solo_n = "".join(filter(str.isdigit, parte_intera.replace('.', '')))
    if not solo_n or not solo_n.isdigit():
        return None
    return solo_n.zfill(9) if int(solo_n) > 0 else None


def format_franchigia(p: float) -> float:
    """Applica la franchigia del 10% arrotondando al decimo superiore se necessario."""
    val = round(p * 1.1, 2)
    return float(math.ceil(val * 10) / 10)


def get_smtp_config() -> dict:
    """Legge le credenziali SMTP dai secrets di Streamlit."""
    return {
        "sender":   st.secrets["EMAIL_SENDER"],
        "password": st.secrets["EMAIL_PASSWORD"],
        "server":   st.secrets["EMAIL_SERVER"],
        "port":     int(st.secrets["EMAIL_PORT"]),
    }


def genera_otp() -> str:
    """Genera un OTP a 6 cifre crittograficamente sicuro."""
    return str(secrets.randbelow(900000) + 100000)


def _data_creazione_dt(row) -> "datetime | None":
    """
    Ricava la data di creazione come datetime in modo robusto e non ambiguo.
    Priorita' al timestamp epoch 'Creato_TS' (immune al locale del foglio);
    fallback su parsing difensivo di 'Data' con dayfirst=True.
    Restituisce None se nessuna fonte e' interpretabile.
    """
    ts_str = str(row.get("Creato_TS", "")).strip()
    if ts_str and ts_str not in {"nan", "None"}:
        try:
            return datetime.fromtimestamp(int(float(ts_str)))
        except Exception:
            pass
    dt = pd.to_datetime(str(row.get("Data", "")).strip(), dayfirst=True, errors="coerce")
    if pd.isna(dt):
        return None
    return dt.to_pydatetime()


def calcola_stato_reale(row, giorni_validita: int = OTP_SCADENZA_GIORNI) -> str:
    """
    Calcola lo stato effettivo di un preventivo considerando la scadenza.
    Restituisce uno tra: PAGATO, ACCETTATO, SCADUTO, INVIATO.
    """
    s = str(row.get("Stato", "")).strip().upper()
    if s == "PAGATO":
        return "PAGATO"
    if s == "ACCETTATO":
        return "ACCETTATO"
    data_c = _data_creazione_dt(row)
    if data_c is not None and datetime.now() > data_c + timedelta(days=giorni_validita):
        return "SCADUTO"
    return "INVIATO"


def invia_email(smtp: dict, to: str, subject: str, body: str,
                pdf_bytes: bytes = None, pdf_name: str = None):
    """Invia una email con allegato PDF opzionale."""
    msg = MIMEMultipart()
    msg['From']    = smtp["sender"]
    msg['To']      = to
    msg['Cc']      = MAIL_CC
    msg['Subject'] = subject
    msg.attach(MIMEText(body, 'plain'))
    if pdf_bytes and pdf_name:
        part = MIMEApplication(pdf_bytes, Name=pdf_name)
        part['Content-Disposition'] = f'attachment; filename="{pdf_name}"'
        msg.attach(part)
    ctx = ssl.create_default_context()
    with smtplib.SMTP_SSL(smtp["server"], smtp["port"], context=ctx) as server:
        server.login(smtp["sender"], smtp["password"])
        server.send_message(msg)


@st.cache_data(show_spinner=False)
def carica_arera(percorso: str = "arera.csv") -> dict:
    """Legge il file ARERA una sola volta e lo cacha in memoria."""
    df = pd.read_csv(percorso, encoding='latin-1', sep=';',
                     on_bad_lines='skip', dtype=str)
    df.columns = [c.strip().upper() for c in df.columns]
    return {
        "".join(filter(str.isdigit, str(r['PARTITA IVA']))).zfill(11):
        {'nome': str(r['RAGIONE SOCIALE']).strip().upper()}
        for _, r in df.iterrows()
    }


def comprimi_html(html: str) -> str:
    """Comprime con zlib e codifica Base64; restituisce '' se troppo grande."""
    b64 = _b64.b64encode(zlib.compress(html.encode("utf-8"), level=9)).decode("utf-8")
    return b64 if len(b64) <= GSHEETS_MAX_CHARS else ""


def decomprimi_html(b64_value: str) -> str:
    """Decomprime HTML compresso. Fallback su Base64 semplice per retrocompatibilità."""
    if not b64_value or b64_value in {"", "nan", "None"}:
        return ""
    try:
        return zlib.decompress(_b64.b64decode(b64_value)).decode("utf-8")
    except Exception:
        try:
            return _b64.b64decode(b64_value).decode("utf-8")
        except Exception:
            return ""

# ==============================================================================
# 5. GENERAZIONE PDF PREVENTIVO
# ==============================================================================

def genera_pdf_polis(d: dict) -> bytes:
    """Genera il PDF del preventivo con font Lato e logo aziendale."""

    # --- Palette ---
    BLUE_DARK  = (0,   51, 102)
    BLUE_LIGHT = (230, 240, 250)
    BLUE_MID   = (0,   90, 170)
    GRAY_BG    = (247, 248, 250)
    GRAY_TEXT  = (60,  60,  60)
    GRAY_MUTED = (140, 140, 140)
    WHITE      = (255, 255, 255)
    BLACK      = (20,  20,  20)

    pdf = FPDF()
    pdf.set_margins(14, 14, 14)
    pdf.add_page()

    try:
        pdf.add_font("Lato", "",  "Lato-Regular.ttf", uni=True)
        pdf.add_font("Lato", "B", "Lato-Bold.ttf",    uni=True)
        FONT = "Lato"
    except Exception:
        FONT = "helvetica"

    # ── HEADER ──
    pdf.set_fill_color(*BLUE_DARK)
    pdf.rect(0, 0, 210, 48, 'F')
    pdf.set_fill_color(*BLUE_MID)
    pdf.rect(0, 48, 210, 1.5, 'F')

    try:
        pdf.image("logo_polis.png", x=14, y=7, w=38)
    except Exception:
        pdf.set_xy(14, 14)
        pdf.set_text_color(*WHITE)
        pdf.set_font(FONT, "B", 18)
        pdf.cell(60, 10, "PolisEnergia")

    pdf.set_xy(110, 10)
    pdf.set_text_color(*WHITE)
    pdf.set_font(FONT, "B", 8.5)
    pdf.cell(86, 5, "POLISENERGIA SRL", align='R', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_x(110)
    pdf.set_font(FONT, "", 7.5)
    for riga in [
        "Via Terre delle Risaie, 4  —  84131 Salerno (SA)",
        "P.IVA 05050950657",
        "assistenza@polisenergia.it  |  www.polisenergia.it",
    ]:
        pdf.set_x(110)
        pdf.set_text_color(200, 220, 245)
        pdf.cell(86, 4.5, riga, align='R', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── TITOLO ──
    pdf.set_xy(14, 57)
    pdf.set_text_color(*BLACK)
    pdf.set_font(FONT, "B", 17)
    pdf.cell(0, 9, f"Preventivo n. {d['Codice']}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.set_x(14)
    pdf.set_font(FONT, "", 9)
    pdf.set_text_color(*GRAY_MUTED)
    data_str = datetime.now().strftime("%d/%m/%Y")
    scad_str = (datetime.now() + timedelta(days=OTP_SCADENZA_GIORNI)).strftime("%d/%m/%Y")
    pratica_label = d.get("Pratica", "")
    pdf.cell(0, 5.5,
             f"Emesso il {data_str}  —  Valido fino al {scad_str}"
             + (f"  —  {pratica_label}" if pratica_label else ""),
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── BOX CLIENTE ──
    pdf.ln(6)
    box_y = pdf.get_y()
    box_h = 20
    pdf.set_fill_color(*GRAY_BG)
    pdf.rect(14, box_y, 182, box_h, 'F')
    pdf.set_fill_color(*BLUE_MID)
    pdf.rect(14, box_y, 3, box_h, 'F')

    pdf.set_xy(20, box_y + 3.5)
    pdf.set_text_color(*GRAY_MUTED)
    pdf.set_font(FONT, "", 7.5)
    pdf.cell(0, 4, "SPETT.LE", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_x(20)
    pdf.set_text_color(*BLACK)
    pdf.set_font(FONT, "B", 10.5)
    pdf.cell(100, 5, d['Cliente'], new_x=XPos.RIGHT, new_y=YPos.TOP)

    pdf.set_xy(122, box_y + 3.5)
    pdf.set_text_color(*GRAY_MUTED)
    pdf.set_font(FONT, "", 7.5)
    pdf.cell(0, 4, "POD", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_x(122)
    pdf.set_text_color(*GRAY_TEXT)
    pdf.set_font(FONT, "", 9)
    pdf.cell(74, 4.5, d['POD'], new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_x(122)
    pdf.set_font(FONT, "", 8)
    pdf.set_text_color(*GRAY_MUTED)
    pdf.cell(74, 4, d['Indirizzo'], new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── COSTRUZIONE VOCI ──
    voci_tec = _costruisci_voci_tecniche(d)
    voci = voci_tec + [
        ("Oneri Amministrativi",   d['Oneri']),
        ("Oneri Gestione Pratica", d['Gestione']),
    ]

    # ── TABELLA ──
    pdf.ln(9)
    pdf.set_draw_color(220, 225, 232)
    pdf.set_line_width(0.2)
    pdf.set_fill_color(*BLUE_DARK)
    pdf.set_text_color(*WHITE)
    pdf.set_font(FONT, "B", 9)
    pdf.cell(134, 9, "  Descrizione prestazione", border=0, fill=True)
    pdf.cell(48,  9, "Importo", border=0, fill=True, align='R',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    for i, (voce, importo) in enumerate(voci):
        bg = GRAY_BG if i % 2 == 0 else WHITE
        pdf.set_fill_color(*bg)
        pdf.set_text_color(*GRAY_TEXT)
        pdf.set_font(FONT, "", 9.5)
        pdf.cell(134, 9, f"  {voce}", border='B', fill=True)
        pdf.cell(48,  9, f"{importo:.2f} EUR", border='B', fill=True, align='R',
                 new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── SUBTOTALI ──
    pdf.ln(2)
    pdf.set_font(FONT, "", 9)
    pdf.set_text_color(*GRAY_MUTED)
    for label, valore in [
        ("Totale imponibile", f"{d['Imponibile']:.2f} EUR"),
        (f"IVA ({d['IVA_Perc']}%)", f"{d['IVA_Euro']:.2f} EUR"),
    ]:
        pdf.cell(134, 7, label, align='R')
        pdf.cell(48,  7, valore, align='R', new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.ln(1)
    pdf.set_fill_color(*BLUE_LIGHT)
    pdf.set_text_color(*BLUE_DARK)
    pdf.set_font(FONT, "B", 11)
    pdf.cell(134, 12, "  Totale da corrispondere", fill=True)
    pdf.cell(48,  12, f"{d['Totale']:.2f} EUR", fill=True, align='R',
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── PAGAMENTO ──
    pdf.ln(10)
    pdf.set_font(FONT, "B", 8)
    pdf.set_text_color(*BLUE_MID)
    pdf.cell(0, 5, "MODALITA' DI PAGAMENTO", new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.set_draw_color(*BLUE_MID)
    pdf.set_line_width(0.4)
    pdf.line(14, pdf.get_y(), 196, pdf.get_y())
    pdf.ln(3)

    pdf.set_text_color(*GRAY_TEXT)
    pdf.set_font(FONT, "", 9.5)
    pdf.cell(30, 5.5, "Bonifico bancario")
    pdf.set_font(FONT, "B", 9.5)
    pdf.cell(0, 5.5, f"IBAN: {d['IBAN']}", new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    pdf.set_font(FONT, "", 9)
    pdf.set_text_color(*GRAY_MUTED)
    pdf.cell(30, 5, "Causale:")
    pdf.set_text_color(*GRAY_TEXT)
    pdf.cell(0, 5, f"Accettazione Preventivo {d['Codice']} — {d.get('Cliente', '')}",
             new_x=XPos.LMARGIN, new_y=YPos.NEXT)

    # ── FIRMA ──
    pdf.ln(8)
    pdf.set_font(FONT, "", 8.5)
    pdf.set_text_color(*GRAY_MUTED)
    pdf.cell(96, 5, "Per accettazione (timbro e firma leggibile):", align='L')
    pdf.cell(86, 5, "Data:", align='L', new_x=XPos.LMARGIN, new_y=YPos.NEXT)
    pdf.ln(10)
    pdf.set_draw_color(*GRAY_MUTED)
    pdf.set_line_width(0.3)
    pdf.line(14,  pdf.get_y(), 106, pdf.get_y())
    pdf.line(112, pdf.get_y(), 160, pdf.get_y())

    # ── FOOTER ──
    pdf.set_y(-28)
    pdf.set_fill_color(*BLUE_DARK)
    pdf.rect(0, pdf.get_y(), 210, 28, 'F')
    pdf.set_x(14)
    pdf.set_text_color(200, 220, 245)
    pdf.set_font(FONT, "", 6.5)
    pdf.set_line_width(0)
    note = (
        "L'esecuzione della prestazione e' subordinata a: conferma della proposta entro 30 gg e "
        "completamento di eventuali opere/autorizzazioni a cura del cliente.  "
        "Inviare il documento firmato a assistenza@polisenergia.it"
    )
    pdf.multi_cell(182, 4, note, align='L')

    return bytes(pdf.output())


def _costruisci_voci_tecniche(d: dict) -> list[tuple[str, float]]:
    """
    Costruisce la lista di voci tecniche (descrizione, importo) in base al tipo pratica.
    Estratta per essere riusata sia da PDF che HTML.
    """
    pratica        = d.get("Pratica", "")
    delta          = d.get("Delta", 0.0)
    tar            = d.get("Tariffa", 0.0)
    c_dist         = d.get("C_Dist", 0.0)
    pass_mt        = d.get("Passaggio_MT", False)
    tipo_fornitura = d.get("Tipo_Fornitura", "Permanente")
    p_new_d        = d.get("P_New", 0.0)
    c_tec          = d.get("C_Tec", 0.0)

    if "Spostamento" in pratica:
        entro = c_dist == SPOSTAMENTO_10MT
        return [(f"Quota Spostamento {'entro' if entro else 'oltre'} 10 mt", c_tec)]

    if "Nuova" in pratica:
        if tipo_fornitura == "Temporanea":
            if p_new_d <= SOGLIA_TEMP_KW:
                attr = "con attraversamento stradale" if c_dist == TEMP_LE40_ATTR else "senza attraversamento stradale"
                return [(f"Fornitura Temporanea ({attr})", c_tec)]
            return [("Fornitura Temporanea >40 kW (quota distributore)", c_tec)]

        voci = []
        quota_pot = delta * tar
        if quota_pot:
            voci.append((f"Quota Potenza  ({tar:.2f} €/kW × {delta:.1f} kW)", quota_pot))
        if c_dist:
            voci.append(("Quota Distanza", c_dist))
        if pass_mt:
            voci.append(("Passaggio a MT", COSTO_PASSAGGIO_MT))
        return voci or [("Quota Tecnica", c_tec)]

    # Aumento Potenza / Subentro / Attivazione
    quota_pot = c_tec - (COSTO_PASSAGGIO_MT if pass_mt else 0)
    voci = [(f"Quota Potenza  ({tar:.2f} €/kW × {delta:.1f} kW)", quota_pot)]
    if pass_mt:
        voci.append(("Passaggio a MT", COSTO_PASSAGGIO_MT))
    return voci

# ==============================================================================
# 5b. GENERAZIONE HTML PREVENTIVO
# ==============================================================================

def genera_html_polis(d: dict) -> str:
    """Genera il preventivo come HTML standalone."""
    data_str = datetime.now().strftime("%d/%m/%Y")
    scad_str = (datetime.now() + timedelta(days=OTP_SCADENZA_GIORNI)).strftime("%d/%m/%Y")

    logo_tag = '<div style="color:#fff;font-size:18px;font-weight:700;letter-spacing:.5px;">PolisEnergia srl</div>'

    voci_tec = _costruisci_voci_tecniche(d)
    voci = voci_tec + [
        ("Oneri Amministrativi",   d['Oneri']),
        ("Oneri Gestione Pratica", d['Gestione']),
    ]

    righe_voci = ""
    for i, (voce, importo) in enumerate(voci):
        bg = "#f7f8fa" if i % 2 == 0 else "#ffffff"
        righe_voci += (
            f'<tr style="background:{bg}">'
            f'<td style="padding:8px 12px;border-bottom:1px solid #e2e6ec;">{voce}</td>'
            f'<td style="padding:8px 12px;text-align:right;border-bottom:1px solid #e2e6ec;">'
            f'{importo:.2f} EUR</td></tr>'
        )

    pratica = d.get("Pratica", "")
    subtitle_extra = f" &nbsp;—&nbsp; {pratica}" if pratica else ""

    return f"""<!DOCTYPE html>
<html lang="it"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Preventivo {d['Codice']} — PolisEnergia</title>
<style>
  body{{margin:0;font-family:Helvetica,Arial,sans-serif;font-size:13px;color:#141414;background:#f0f2f5}}
  .page{{max-width:740px;margin:32px auto;background:#fff;box-shadow:0 2px 16px rgba(0,0,0,.10)}}
  .header{{background:#003366;padding:18px 24px;display:flex;justify-content:space-between;align-items:center}}
  .header-info{{text-align:right;color:#c8dcf5;font-size:11px;line-height:1.8}}
  .header-info strong{{color:#fff;display:block;font-size:12px;font-weight:700;margin-bottom:2px}}
  .accent{{height:3px;background:#005aaa}}
  .body{{padding:28px 24px}}
  .title{{font-size:22px;font-weight:700;margin:0 0 4px;color:#141414}}
  .subtitle{{color:#8c8c8c;font-size:11px;margin:0 0 20px}}
  .cliente-box{{background:#f7f8fa;border-left:3px solid #005aaa;padding:12px 16px;
                display:flex;justify-content:space-between;margin-bottom:24px;border-radius:2px}}
  .cliente-label{{font-size:9px;color:#8c8c8c;text-transform:uppercase;letter-spacing:.5px;margin-bottom:3px}}
  .cliente-name{{font-size:14px;font-weight:700;color:#141414}}
  .pod-val{{font-size:12px;font-weight:700;color:#003366}}
  .pod-addr{{font-size:11px;color:#8c8c8c;margin-top:2px}}
  table{{width:100%;border-collapse:collapse;font-size:12.5px}}
  thead td{{background:#003366;color:#fff;padding:9px 12px;font-weight:700}}
  .subtotal td{{padding:5px 12px;color:#8c8c8c;font-size:12px}}
  .total-row td{{background:#e6f0fa;color:#003366;font-weight:700;font-size:14px;padding:10px 12px}}
  .section-label{{font-size:9px;font-weight:700;color:#005aaa;letter-spacing:.8px;
                  text-transform:uppercase;margin:24px 0 4px}}
  .section-line{{border:none;border-top:1px solid #005aaa;margin:0 0 10px}}
  .pagamento-row{{display:flex;gap:8px;align-items:baseline;margin-bottom:4px;font-size:12px}}
  .pagamento-label{{color:#8c8c8c;min-width:90px}}
  .iban{{font-family:monospace;background:#f0f2f5;padding:2px 8px;border-radius:3px;font-size:11px}}
  .firma-area{{display:flex;gap:24px;margin-top:28px;align-items:flex-end}}
  .firma-col{{flex:1}}.firma-col.data{{max-width:130px}}
  .firma-label{{font-size:10px;color:#8c8c8c;margin-bottom:18px}}
  .firma-line{{border-top:1px solid #aaa;padding-top:4px;color:#ccc;font-size:10px}}
  .footer{{background:#003366;padding:10px 24px}}
  .footer p{{color:#c8dcf5;font-size:10px;margin:0;line-height:1.7}}
  @media print{{body{{background:#fff}}.page{{box-shadow:none;margin:0}}}}
</style></head><body>
<div class="page">
  <div class="header">
    {logo_tag}
    <div class="header-info">
      <strong>POLISENERGIA SRL</strong>
      Via Terre delle Risaie, 4 — 84131 Salerno (SA)<br>
      P.IVA 05050950657<br>
      assistenza@polisenergia.it · www.polisenergia.it
    </div>
  </div>
  <div class="accent"></div>
  <div class="body">
    <p class="title">Preventivo n. {d['Codice']}</p>
    <p class="subtitle">Emesso il {data_str} &nbsp;—&nbsp; Valido fino al {scad_str}{subtitle_extra}</p>
    <div class="cliente-box">
      <div>
        <div class="cliente-label">Spett.le</div>
        <div class="cliente-name">{d['Cliente']}</div>
      </div>
      <div style="text-align:right">
        <div class="cliente-label">POD</div>
        <div class="pod-val">{d['POD']}</div>
        <div class="pod-addr">{d['Indirizzo']}</div>
      </div>
    </div>
    <table style="margin-bottom:4px">
      <thead><tr>
        <td style="width:76%">Descrizione prestazione</td>
        <td style="text-align:right">Importo</td>
      </tr></thead>
      <tbody>{righe_voci}</tbody>
    </table>
    <table style="margin-top:4px;margin-bottom:4px">
      <tbody>
        <tr class="subtotal">
          <td style="text-align:right;width:76%">Totale imponibile</td>
          <td style="text-align:right">{d['Imponibile']:.2f} EUR</td>
        </tr>
        <tr class="subtotal">
          <td style="text-align:right">IVA ({d['IVA_Perc']}%)</td>
          <td style="text-align:right">{d['IVA_Euro']:.2f} EUR</td>
        </tr>
        <tr class="total-row">
          <td>Totale da corrispondere</td>
          <td style="text-align:right">{d['Totale']:.2f} EUR</td>
        </tr>
      </tbody>
    </table>
    <p class="section-label">Modalità di pagamento</p>
    <hr class="section-line">
    <div class="pagamento-row">
      <span class="pagamento-label">Bonifico bancario</span>
      <span class="iban">{d['IBAN']}</span>
    </div>
    <div class="pagamento-row">
      <span class="pagamento-label">Causale:</span>
      <span>Accettazione Preventivo {d['Codice']} — {d['Cliente']}</span>
    </div>
    <div class="firma-area">
      <div class="firma-col">
        <div class="firma-label">Per accettazione (timbro e firma leggibile):</div>
        <div class="firma-line">___________________________________</div>
      </div>
      <div class="firma-col data">
        <div class="firma-label">Data:</div>
        <div class="firma-line">________________</div>
      </div>
    </div>
  </div>
  <div class="footer">
    <p>L'esecuzione della prestazione è subordinata a: conferma della proposta entro 30 gg e
    completamento di eventuali opere/autorizzazioni a cura del cliente finale.<br>
    Inviare il documento firmato a <strong style="color:#fff">assistenza@polisenergia.it</strong></p>
  </div>
</div></body></html>"""

# ==============================================================================
# 6. PAGINA CLIENTE: ACCETTAZIONE ONLINE
# ==============================================================================

codice_param = st.query_params.get("codice", "")
otp_param    = st.query_params.get("otp", "")

if codice_param:
    st.title("🖋️ Visualizzazione Preventivo")
    cod_u = str(codice_param).strip().replace('.0', '')
    otp_u = str(otp_param).strip()

    try:
        conn = st.connection("gsheets", type=GSheetsConnection)
        df   = conn.read(ttl=0)
        df['Codice_Clean'] = df['Codice'].astype(str).str.strip().str.replace('.0', '', regex=False)

        if cod_u not in df['Codice_Clean'].values:
            st.error("⚠️ Link non valido o preventivo non trovato. Contatta PolisEnergia.")
            st.stop()

        idx           = df[df['Codice_Clean'] == cod_u].index[0]
        nome_cliente  = df.at[idx, "Cliente"]
        stato_attuale = str(df.at[idx, "Stato"]).strip()

        # ── Modalità anteprima operatore (senza OTP) ──
        if not otp_u:
            st.info(f"🔍 Modalità Anteprima Operatore - Cliente: **{nome_cliente}**")
            dati_per_html = df.iloc[idx].to_dict()
            try:
                codice_html = genera_html_polis(dati_per_html)
                st.components.v1.html(codice_html, height=900, scrolling=True)
                st.download_button(
                    label="📥 Scarica file HTML",
                    data=codice_html,
                    file_name=f"Preventivo_{cod_u}.html",
                    mime="text/html"
                )
            except Exception as e:
                mostra_errore("Errore nella generazione grafica.", e)
                if DEBUG_MODE:
                    st.write("Dati grezzi preventivo:", dati_per_html)
            st.stop()

        # ── Già firmato ──
        if stato_attuale.upper() == "ACCETTATO":
            st.success("✅ Questo preventivo è già stato firmato. Grazie!")
            st.stop()

        # ── OTP attivo dal foglio (non dall'URL) ──
        otp_nel_foglio = ""
        if "OTP" in df.columns:
            otp_nel_foglio = str(df.at[idx, "OTP"]).strip()
            if otp_nel_foglio in {"nan", "None"}:
                otp_nel_foglio = ""

        # Fallback retrocompatibile: preventivi vecchi senza OTP nel foglio
        # usano ancora il valore del param URL come fonte di verità.
        otp_valido = otp_nel_foglio or otp_u

        # Se c'è OTP nel foglio ed è diverso dal param → link vecchio (reinvio fatto)
        if otp_nel_foglio and otp_u != otp_nel_foglio:
            st.error(
                "⚠️ Questo link non è più valido. È stato inviato un preventivo aggiornato: "
                "controlla la mail più recente o contatta PolisEnergia."
            )
            st.stop()

        # ── Scadenza basata su data creazione (timestamp robusto, fallback su 'Data') ──
        data_per_scadenza = _data_creazione_dt(df.loc[idx])
        if data_per_scadenza is None:
            st.error("Data preventivo non leggibile. Contatta PolisEnergia.")
            st.stop()

        data_scadenza    = data_per_scadenza + timedelta(days=OTP_SCADENZA_GIORNI)
        if datetime.now() > data_scadenza:
            st.error(
                f"⏰ Il link di firma è scaduto (validità {OTP_SCADENZA_GIORNI} giorni). "
                f"Contatta PolisEnergia per ricevere un nuovo preventivo."
            )
            st.stop()

        try:
            importo_totale = float(df.at[idx, "Totale"])
        except Exception:
            importo_totale = 0.0

        giorni_rimanenti = (data_scadenza - datetime.now()).days

        # ── Box istruzioni pagamento ──
        st.markdown(f"""
            <div style="background:rgba(255,255,255,0.1);padding:20px;border-radius:10px;
                        border:1px solid white;margin-bottom:25px;">
                <h3 style="color:white;margin-top:0;">💳 Istruzioni per il pagamento</h3>
                <p style="color:white;font-size:1.1em;"><strong>Cliente:</strong> {nome_cliente}</p>
                <p style="color:white;font-size:1.1em;">
                    <strong>Importo:</strong> {importo_totale:.2f} EUR
                </p>
                <p style="color:#ffe08a;font-size:0.9em;">
                    ⏳ Link valido ancora per <strong>{giorni_rimanenti} giorni</strong>
                    (scade il {data_scadenza.strftime('%d/%m/%Y')})
                </p>
                <hr style="border-color:rgba(255,255,255,0.3);">
                <p style="color:white;font-weight:bold;margin-bottom:5px;">COORDINATE BANCARIE:</p>
                <ul style="color:white;list-style-type:none;padding-left:0;">
                    <li><strong>Intestatario:</strong> {INTESTATARIO}</li>
                    <li><strong>Banca:</strong> {NOME_BANCA}</li>
                    <li><strong>IBAN:</strong>
                        <span style="font-family:monospace;background:rgba(0,0,0,0.2);
                                     padding:2px 5px;">{IBAN_POLIS}</span>
                    </li>
                    <li><strong>Causale:</strong> Accettazione Preventivo {cod_u} - {nome_cliente}</li>
                </ul>
            </div>
        """, unsafe_allow_html=True)

        st.markdown("<p style='color:white;font-weight:bold;'>Inserisci l'OTP ricevuto via mail:</p>",
                    unsafe_allow_html=True)
        otp_in = st.text_input("OTP:", max_chars=6, label_visibility="collapsed")

        if st.button("✅ FIRMA E ACCETTA ORA"):
            if not otp_in.strip():
                st.warning("Inserisci il codice OTP prima di procedere.")
            elif otp_in.strip() == otp_valido:
                df.at[idx, "Stato"]      = "ACCETTATO"
                df.at[idx, "Data Firma"] = datetime.now().strftime("%d/%m/%Y %H:%M")
                conn.update(data=df.drop(columns=['Codice_Clean']))

                try:
                    smtp = get_smtp_config()
                    invia_email(
                        smtp=smtp,
                        to=smtp["sender"],
                        subject=f"✅ PREVENTIVO FIRMATO: {nome_cliente}",
                        body=(
                            f"Il cliente {nome_cliente} ha accettato il preventivo {cod_u}.\n"
                            f"Data firma: {datetime.now().strftime('%d/%m/%Y %H:%M')}\n"
                            f"Controlla il database."
                        )
                    )
                except Exception:
                    pass  # Notifica interna non bloccante

                st.success("✅ Documento firmato con successo!")
                st.balloons()
            else:
                st.error("❌ OTP non corretto. Riprova o contatta PolisEnergia.")

    except Exception as e:
        mostra_errore("Si è verificato un errore tecnico. Contatta PolisEnergia.", e)

    st.stop()

# ==============================================================================
# 7. AUTENTICAZIONE OPERATORI
# ==============================================================================
if "autenticato" not in st.session_state:
    st.session_state.autenticato = False

if not st.session_state.autenticato:
    st.sidebar.title("🔒 Area Riservata")
    pwd = st.sidebar.text_input("Password", type="password")
    if pwd:
        password_corretta = st.secrets.get("APP_PASSWORD", "")
        if password_corretta and pwd == password_corretta:
            st.session_state.autenticato = True
            st.rerun()
        else:
            st.sidebar.error("Password errata")
    st.title("Polisenergia - Operation Suite")
    st.info("Effettua il login nella barra laterale per accedere.")
    st.stop()

# ==============================================================================
# 8. NAVIGAZIONE (solo operatori autenticati)
# ==============================================================================
st.sidebar.success("✅ Accesso Autorizzato")
st.sidebar.title("Navigazione")
scelta = st.sidebar.radio(
    "Cosa vuoi fare?",
    ["Autoletture", "Preventivo di Connessione", "📋 Archivio Preventivi",
     "📊 Statistiche", "⚙️ Impostazioni"]
)
st.sidebar.divider()
st.sidebar.caption(f"PolisEnergia Internal Tools v2.1 © {datetime.now().year}")

# ==============================================================================
# 9. SEZIONE: AUTOLETTURE
# ==============================================================================
if scelta == "Autoletture":
    st.header("📊 Generatore Flussi Autoletture")
    FILE_ARERA = "arera.csv"

    if not os.path.exists(FILE_ARERA):
        st.error(f"❌ File '{FILE_ARERA}' non trovato. Caricalo nel repository per continuare.")
        st.stop()

    piva_mittente = st.text_input("P.IVA Venditore (Mittente)", value="05050950657")
    st.divider()
    st.subheader("📁 Caricamento File")
    col1, col2 = st.columns(2)
    file_tech    = col1.file_uploader("1. Anagrafica Tecnica (Excel)", type=["xlsx", "xls"])
    file_letture = col2.file_uploader("2. Autoletture (CSV)", type="csv")

    if file_tech and file_letture:
        if st.button("🚀 GENERA PACCHETTO XML (.ZIP)", use_container_width=True):
            try:
                zip_buffer   = io.BytesIO()
                progress_bar = st.progress(0)

                with st.spinner("Elaborazione in corso..."):
                    mappa_piva_distr = carica_arera(FILE_ARERA)

                    # --- Anagrafica Tecnica ---
                    df_tech = pd.read_excel(file_tech, dtype=str)
                    df_tech.columns = [c.strip().upper() for c in df_tech.columns]

                    piva_polis_clean = "".join(filter(str.isdigit, piva_mittente)).zfill(11)
                    df_tech['PIVA_UDD_CLEAN'] = (df_tech['PIVA_UDD']
                                                  .str.replace(r'\D', '', regex=True).str.zfill(11))
                    df_tech['PIVA_DD_CLEAN']  = (df_tech['PIVA_DD']
                                                  .str.replace(r'\D', '', regex=True).str.zfill(11))
                    df_tech['COD_PDR_CLEAN']  = (df_tech['COD_PDR']
                                                  .str.split('.').str[0].str.strip().str.zfill(14))

                    df_tech_polis   = df_tech[df_tech['PIVA_UDD_CLEAN'] == piva_polis_clean].copy()
                    df_tech_esterni = df_tech[df_tech['PIVA_UDD_CLEAN'] != piva_polis_clean].copy()

                    mappa_matr_pdr  = pd.Series(
                        df_tech_polis['MATR_MIS'].values,
                        index=df_tech_polis['COD_PDR_CLEAN']
                    ).to_dict()
                    mappa_pdr_distr = pd.Series(
                        df_tech_polis['PIVA_DD_CLEAN'].values,
                        index=df_tech_polis['COD_PDR_CLEAN']
                    ).to_dict()
                    c_matr_corr = next((c for c in df_tech.columns if 'CORR' in c), None)
                    mappa_matr_corr = (
                        pd.Series(df_tech_polis[c_matr_corr].values,
                                  index=df_tech_polis['COD_PDR_CLEAN']).to_dict()
                        if c_matr_corr else {}
                    )

                    # --- Autoletture ---
                    df_let = pd.read_csv(
                        file_letture, sep=None, engine='python',
                        encoding='utf-8-sig', dtype=str
                    )
                    df_let.columns = [c.strip().upper() for c in df_let.columns]
                    col_pdr  = next(c for c in df_let.columns if 'PDR' in c)
                    col_data = next(c for c in df_let.columns if 'DATA' in c)
                    col_lett = next(c for c in df_let.columns if 'LETTURA' in c and 'CORRE' not in c)
                    col_corr = next((c for c in df_let.columns if 'CORRETTORE' in c or 'CONVERT' in c), None)

                    progress_bar.progress(25)

                    with zipfile.ZipFile(zip_buffer, "w", zipfile.ZIP_DEFLATED) as zip_file:
                        # Excel per distributori esterni
                        if not df_tech_esterni.empty:
                            grp_cols = ['PIVA_UDD', 'RAGIONE_SOCIALE_UDD']
                            for (piva_udd, rag_soc), group in df_tech_esterni.groupby(grp_cols):
                                group_pdr_clean = group['COD_PDR_CLEAN'].tolist()
                                autolett_est = df_let[
                                    df_let[col_pdr].str.split('.').str[0].str.zfill(14)
                                    .isin(group_pdr_clean)
                                ]
                                if not autolett_est.empty:
                                    nome_ex = (f"AUTOLETTURE_ESTERNE_{piva_udd}_"
                                               f"{re.sub(r'\\W+', '', rag_soc)[:15]}.xlsx")
                                    buf = io.BytesIO()
                                    autolett_est.to_excel(buf, index=False)
                                    zip_file.writestr(nome_ex, buf.getvalue())

                        progress_bar.progress(50)

                        # Raggruppamento XML per Polis
                        gruppi: dict[str, list] = defaultdict(list)
                        for _, riga in df_let.iterrows():
                            pdr_clean = str(riga[col_pdr]).split('.')[0].zfill(14)
                            piva_dd   = mappa_pdr_distr.get(pdr_clean)
                            if not piva_dd:
                                continue
                            info_arera = mappa_piva_distr.get(piva_dd)
                            if not info_arera:
                                continue
                            ln = pulisci_valore(riga[col_lett])
                            lc = pulisci_valore(riga[col_corr]) if col_corr else None
                            if ln:
                                gruppi[piva_dd].append({
                                    'distr_nome': info_arera['nome'],
                                    'pdr':   pdr_clean,
                                    'data':  formatta_data_italiana(riga[col_data]),
                                    'lett':  ln,
                                    'corr':  lc,
                                    'm_pdr': str(mappa_matr_pdr.get(pdr_clean, "0")).split('.')[0],
                                    'm_corr': (str(mappa_matr_corr[pdr_clean]).split('.')[0]
                                               if pdr_clean in mappa_matr_corr else None),
                                })

                        # Scrittura XML
                        tot_g = len(gruppi)
                        for i, (piva_d, lista) in enumerate(gruppi.items()):
                            root = ET.Element("Prestazione", cod_servizio="TAL", cod_flusso="0050")
                            id_req = ET.SubElement(root, "IdentificativiRichiesta")
                            ET.SubElement(id_req, "piva_utente").text = piva_mittente
                            ET.SubElement(id_req, "piva_distr").text  = piva_d
                            for item in lista:
                                d = ET.SubElement(root, "DatiPdR")
                                ET.SubElement(d, "cod_pdr").text             = item['pdr']
                                ET.SubElement(d, "matr_mis").text            = item['m_pdr']
                                ET.SubElement(d, "data_com_autolet_cf").text = item['data']
                                ET.SubElement(d, "let_tot_prel").text        = item['lett']
                                if item['corr']:
                                    ET.SubElement(d, "let_tot_conv").text = item['corr']
                                    if item['m_corr'] and item['m_corr'] not in {"nan", "None", ""}:
                                        ET.SubElement(d, "matr_conv").text = item['m_corr']

                            xml_str = ET.tostring(root, encoding='utf-8', xml_declaration=True)

                            try:
                                data_prima = formatta_data_italiana(lista[0]['data'])
                                parti_d    = data_prima.split('/')
                                mmaaaa     = f"{parti_d[1]}{parti_d[2]}"
                            except Exception:
                                mmaaaa = datetime.now().strftime("%m%Y")

                            rag_soc_safe = re.sub(r'[\\/:*?"<>|]+', '_',
                                                   lista[0]['distr_nome'])[:40].strip()
                            piva_mitt_clean = "".join(filter(str.isdigit, piva_mittente))
                            nome_file = f"TAL_0050_{piva_mitt_clean}_{piva_d}_{mmaaaa}.xml"
                            zip_file.writestr(f"{rag_soc_safe}/{nome_file}", xml_str)
                            progress_bar.progress(50 + int(((i + 1) / tot_g) * 50))

                zip_buffer.seek(0)
                progress_bar.empty()
                st.success(f"✅ Completato! Creati {len(gruppi)} file XML.")
                st.download_button(
                    label="📥 SCARICA PACCHETTO ZIP",
                    data=zip_buffer,
                    file_name=f"Autoletture_{datetime.now().strftime('%d_%m_%H%M')}.zip",
                    mime="application/zip",
                    use_container_width=True,
                )

            except Exception as e:
                mostra_errore("Errore durante l'elaborazione.", e)

# ==============================================================================
# 10. SEZIONE: PREVENTIVO DI CONNESSIONE
# ==============================================================================
elif scelta == "Preventivo di Connessione":
    st.title("⚡ PolisEnergia - Preventivatore")

    # --- Dati cliente ---
    c1, c2 = st.columns(2)
    nome       = c1.text_input("Ragione Sociale", key="n").upper()
    email_dest = c1.text_input("Email Cliente",   key="m")
    indirizzo  = c1.text_input("Indirizzo Impianto", key="ind")
    pod        = c2.text_input("POD",              key="p").upper()
    regime     = c2.selectbox("Regime IVA", ["10%", "22%", "Esente", "P.A."], key="r")

    st.divider()

    # --- Configurazione pratica ---
    c3, c4 = st.columns([2, 1])
    pratica = c3.selectbox(
        "Tipo Pratica",
        ["Aumento Potenza", "Subentro con Modifica",
         "Attivazione su Preposato con Modifica",
         "Nuova Connessione", "Spostamento Contatore"],
        key="prat"
    )
    tipo_ut = c4.radio("Utenza", ["Domestico", "Altri Usi"], horizontal=True, key="ut")

    # Inizializzazione valori
    p_att, p_new, c_dist, delta, tar = 0.0, 0.0, 0.0, 0.0, 0.0
    passaggio_mt     = False
    t_partenza       = "BT"
    tipo_fornitura   = "Permanente"
    no_lim_attuale   = st.session_state.get("no_lim_att", False)
    richiesta_no_lim = st.session_state.get("no_lim_new", False)
    escludi_gestione = st.checkbox("Sconto 100% Gestione Polis", value=False)

    if "Potenza" in pratica or "Subentro" in pratica or "Attivazione" in pratica:
        col1, col2 = st.columns(2)
        if tipo_ut == "Altri Usi":
            t_partenza = col1.selectbox("Tensione", ["BT", "MT"], key="t")
            if t_partenza == "BT":
                passaggio_mt = col1.checkbox("Passaggio a MT?", key="mt")
        p_att = col1.number_input("kW Attuali (Contrattuali)",   value=0.0, key="pa")
        p_new = col2.number_input("kW Richiesti (Contrattuali)", value=0.0, key="pn")

        mostra_att = p_att > 0 and p_att <= SOGLIA_LIMITATORE
        mostra_new = p_new <= SOGLIA_LIMITATORE
        if tipo_ut == "Altri Usi" and (mostra_att or mostra_new):
            st.info("⚙️ Gestione Limitatore (Franchigia 10%)")
            cx1, cx2 = st.columns(2)
            if mostra_att:
                no_lim_attuale = cx1.checkbox(
                    "Stato Attuale: POD SENZA limitatore", key="no_lim_att",
                    help="Spunta se il cliente ha già il prelievo libero (senza +10%)"
                )
            if mostra_new:
                richiesta_no_lim = cx2.checkbox(
                    "Nuova Config: Rimuovere Limitatore", key="no_lim_new",
                    help="Spunta per richiedere potenza a prelievo libero (senza franchigia)"
                )

    elif "Nuova" in pratica:
        tipo_fornitura = st.radio(
            "Tipo fornitura", ["Permanente", "Temporanea"],
            horizontal=True, key="forn"
        )

        if tipo_fornitura == "Permanente":
            p_new  = st.number_input("kW Richiesti", value=0.0, key="pnc")
            c_dist = st.number_input("Quota Distanza €", 0.0,   key="dist")
            if tipo_ut == "Altri Usi" and p_new <= SOGLIA_LIMITATORE:
                richiesta_no_lim = st.checkbox(
                    "Richiedere potenza a prelievo LIBERO (senza franchigia)", key="no_lim_new"
                )
        else:  # Temporanea
            p_new = st.number_input("kW Richiesti", value=0.0, key="pnc")
            if p_new <= SOGLIA_TEMP_KW:
                attr_str = st.radio(
                    "Attraversamento stradale?",
                    [f"No ({TEMP_LE40_NO_ATTR:.2f} €)", f"Sì ({TEMP_LE40_ATTR:.2f} €)"],
                    horizontal=True, key="attr_str"
                )
                c_dist = TEMP_LE40_ATTR if "Sì" in attr_str else TEMP_LE40_NO_ATTR
                st.info(f"Quota fissa fornitura temporanea: **{c_dist:.2f} €**")
            else:
                st.info(f"Potenza > {SOGLIA_TEMP_KW} kW: inserire la quota comunicata dal distributore.")
                c_dist = st.number_input("Quota fissa distributore €", 0.0, key="dist")

    elif "Spostamento" in pratica:
        s_dist = st.radio("Distanza", ["Entro 10 metri", "Oltre 10 metri"], key="sd")
        c_dist = (SPOSTAMENTO_10MT if "Entro" in s_dist
                  else st.number_input("Costo Rilievo €", 0.0, key="sdc"))

    # --- Calcolo delta e tariffa ---
    if p_new > 0:
        if p_new <= SOGLIA_LIMITATORE and (tipo_ut == "Domestico" or not richiesta_no_lim):
            v_new = round(p_new * 1.1, 1)
        else:
            v_new = p_new

        if p_att > 0:
            if p_att <= SOGLIA_LIMITATORE and (tipo_ut == "Domestico" or not no_lim_attuale):
                v_att = round(p_att * 1.1, 1)
            else:
                v_att = p_att
        else:
            v_att = 0.0

        delta = max(round(v_new - v_att, 1), 0.0)

        if "Nuova" in pratica:
            tar = TIC_ALTRI_USI_BT
        elif t_partenza == "MT" or passaggio_mt:
            tar = TIC_MT
        elif tipo_ut == "Domestico" and p_new <= SOGLIA_AGEVOL_DOM and "Potenza" in pratica:
            tar = TIC_DOMESTICO_LE6
        else:
            tar = TIC_ALTRI_USI_BT

    # --- Calcolo importi ---
    if "Spostamento" in pratica:
        c_tec = c_dist
    elif "Nuova" in pratica:
        if tipo_fornitura == "Temporanea":
            c_tec = c_dist
        else:
            c_tec = round((delta * tar) + c_dist, 2)
    else:
        c_tec = round(delta * tar, 2)

    if passaggio_mt:
        c_tec += COSTO_PASSAGGIO_MT

    c_gest = 0.0 if escludi_gestione else round((c_tec + FISSO_BASE_CALCOLO) * 0.1, 2)
    imp    = round(c_tec + c_gest + ONERI_ISTRUTTORIA, 2)
    iva_p  = 10 if "10" in regime else (22 if "22" in regime or "P.A." in regime else 0)
    iva_e  = round(imp * (iva_p / 100), 2)
    bollo  = BOLLO_ESENTE if (regime == "Esente" and imp > SOGLIA_BOLLO) else 0.0
    totale = (round(imp + bollo, 2)
              if "P.A." in regime
              else round(imp + iva_e + bollo, 2))

    # --- Anteprima ---
    st.subheader("📊 Anteprima Calcolo")
    col_t1, col_t2 = st.columns([2, 1])
    with col_t1:
        st.table(pd.DataFrame({
            "Voce":       ["Quota TIC", "Gestione Polis", "Istruttoria", "IVA", "Bollo"],
            "Valore (€)": [f"{c_tec:.2f}", f"{c_gest:.2f}",
                           f"{ONERI_ISTRUTTORIA:.2f}", f"{iva_e:.2f}", f"{bollo:.2f}"],
        }))
    with col_t2:
        st.metric("TOTALE", f"{totale:.2f} €")
        if "Spostamento" not in pratica:
            st.info(f"Delta: {delta} kW | Tariffa: {tar} €/kW")

    st.divider()

    # --- Azioni ---
    btn1, btn2 = st.columns(2)

    with btn1:
        if st.button("📄 1. GENERA PDF E ARCHIVIA", type="primary",
                     use_container_width=True, key="btn_genera"):
            errori = []
            if not nome.strip():
                errori.append("Ragione Sociale")
            if not pod.strip() and "Nuova" not in pratica:
                errori.append("POD")
            if not email_dest.strip():
                errori.append("Email Cliente")
            if p_new <= 0 and "Spostamento" not in pratica:
                errori.append("kW Richiesti (deve essere > 0)")

            if errori:
                st.error(f"⚠️ Compila i campi obbligatori: {', '.join(errori)}")
            else:
                cod = datetime.now().strftime("%y%m%d%H%M%S")
                st.session_state.current_cod = cod

                # OTP generato subito così lo salviamo nel foglio
                otp_corrente = genera_otp()
                st.session_state.current_otp = otp_corrente

                # Controllo duplicati POD
                cod_padre = ""
                try:
                    conn_check = st.connection("gsheets", type=GSheetsConnection)
                    df_check   = conn_check.read(ttl=0)
                    if not df_check.empty and "POD" in df_check.columns:
                        attivi = df_check[
                            (df_check["POD"].astype(str).str.strip() == pod.strip()) &
                            (df_check["Stato"].astype(str).str.strip().str.upper().isin(["INVIATO"]))
                        ]
                        if not attivi.empty:
                            cod_padre = str(attivi.iloc[-1]["Codice"]).strip()
                            st.warning(
                                f"⚠️ Esiste già un preventivo attivo per il POD **{pod}** "
                                f"(codice: `{cod_padre}`). "
                                f"Il nuovo sarà archiviato come revisione."
                            )
                except Exception:
                    pass

                dati_preventivo = {
                    "Codice": cod, "Cliente": nome, "POD": pod, "Indirizzo": indirizzo,
                    "C_Tec": c_tec, "Oneri": ONERI_ISTRUTTORIA, "Gestione": c_gest,
                    "Imponibile": imp, "IVA_Perc": iva_p, "IVA_Euro": iva_e,
                    "Totale": totale, "IBAN": IBAN_LABEL,
                    "Pratica":        pratica,
                    "Tipo_Fornitura": tipo_fornitura,
                    "Delta":          delta,
                    "Tariffa":        tar,
                    "P_New":          p_new,
                    "P_Att":          p_att,
                    "C_Dist":         c_dist,
                    "Passaggio_MT":   passaggio_mt,
                }
                st.session_state.pdf_bytes = genera_pdf_polis(dati_preventivo)
                html_preventivo            = genera_html_polis(dati_preventivo)
                html_b64                   = comprimi_html(html_preventivo)

                if not html_b64:
                    st.warning("⚠️ HTML troppo grande per il foglio — solo PDF disponibile.")

                try:
                    conn       = st.connection("gsheets", type=GSheetsConnection)
                    df_current = conn.read(ttl=0)
                    nuova_riga = pd.DataFrame([{
                        "Data":        datetime.now().strftime("%d/%m/%Y"),
                        "Creato_TS":   int(datetime.now().timestamp()),
                        "Codice":      str(cod),
                        "Versione_Di": cod_padre,
                        "Cliente":     nome,
                        "POD":         pod,
                        "Totale":      totale,
                        "C_Tec":       c_tec,
                        "Gestione":    c_gest,
                        "Oneri":       ONERI_ISTRUTTORIA,
                        "Stato":       "Inviato",
                        "Email":       email_dest,
                        "HTML_B64":    html_b64,
                        "OTP":         otp_corrente,
                    }])
                    df_finale = pd.concat([df_current, nuova_riga], ignore_index=True)
                    conn.update(data=df_finale)
                    st.success(f"✅ Preventivo {cod} generato e archiviato!")
                except Exception as e:
                    mostra_errore("PDF generato, ma errore salvataggio Google Sheets.", e)

    with btn2:
        if st.session_state.get('pdf_bytes'):
            st.download_button(
                label="📥 2. SCARICA PDF",
                data=io.BytesIO(st.session_state.pdf_bytes),
                file_name=f"Preventivo_{st.session_state.get('current_cod', 'draft')}.pdf",
                mime="application/pdf",
                use_container_width=True,
                key="btn_download",
            )
        else:
            st.button("📥 2. SCARICA PDF", disabled=True,
                      use_container_width=True, key="btn_download_dis")

    # --- Invio email ---
    if 'current_cod' in st.session_state and 'pdf_bytes' in st.session_state:
        st.divider()
        st.subheader("📧 Invio Documentazione al Cliente")

        otp  = st.session_state.current_otp
        cod  = st.session_state.current_cod
        link = f"{APP_URL}/?codice={cod}&otp={otp}"

        template = st.session_state.get("email_template",
            "Spett.le {nome},\n"
            "in allegato il preventivo n. {codice}.\n\n"
            "Per firmare digitalmente clicca qui: {link}\n"
            "OTP: {otp}\n\n"
            "Il link è valido per {giorni} giorni.\n\n"
            "Cordiali saluti,\nPolisEnergia srl"
        )
        testo_default = template.format(
            nome=nome, codice=cod, link=link,
            otp=otp, giorni=OTP_SCADENZA_GIORNI,
            totale=f"{totale:.2f}", pod=pod,
        )
        corpo_mail = st.text_area("Modifica testo email:", value=testo_default, height=180)

        if st.button("🚀 INVIA EMAIL AL CLIENTE", use_container_width=True, key="btn_invia"):
            if not email_dest:
                st.error("Inserisci l'indirizzo email del cliente prima di inviare.")
            else:
                try:
                    with st.spinner("Invio in corso..."):
                        smtp = get_smtp_config()
                        invia_email(
                            smtp=smtp,
                            to=email_dest,
                            subject=f"Preventivo PolisEnergia n. {cod}",
                            body=corpo_mail,
                            pdf_bytes=st.session_state.pdf_bytes,
                            pdf_name=f"Preventivo_{cod}.pdf",
                        )
                    st.success("✅ Email inviata con successo!")
                except Exception as e:
                    mostra_errore("Errore durante l'invio.", e)
    else:
        st.info("ℹ️ Genera il PDF prima di procedere con l'invio della mail.")

    st.divider()

    # Pulisci con conferma
    if 'conferma_pulizia' not in st.session_state:
        st.session_state.conferma_pulizia = False

    if not st.session_state.conferma_pulizia:
        if st.button("🧹 PULISCI TUTTO", use_container_width=True, key="pulisci"):
            st.session_state.conferma_pulizia = True
            st.rerun()
    else:
        st.warning("⚠️ Sei sicuro? Tutti i dati del preventivo corrente verranno persi.")
        c_si, c_no = st.columns(2)
        if c_si.button("✅ Sì, pulisci", use_container_width=True, key="pulisci_si"):
            CONSERVA = {"autenticato", "email_template"}
            for key in [k for k in st.session_state.keys() if k not in CONSERVA]:
                del st.session_state[key]
            st.rerun()
        if c_no.button("❌ Annulla", use_container_width=True, key="pulisci_no"):
            st.session_state.conferma_pulizia = False
            st.rerun()

# ==============================================================================
# 11. SEZIONE: ARCHIVIO PREVENTIVI
# ==============================================================================
elif scelta == "📋 Archivio Preventivi":
    st.title("📋 Archivio Preventivi")

    try:
        conn = st.connection("gsheets", type=GSheetsConnection)
        df   = conn.read(ttl=GSHEETS_CACHE_TTL)

        if df.empty:
            st.info("Nessun preventivo in archivio.")
            st.stop()

        df["Stato Reale"] = df.apply(calcola_stato_reale, axis=1)

        # KPI
        n_inv = len(df[df["Stato Reale"] == "INVIATO"])
        n_acc = len(df[df["Stato Reale"].isin(["ACCETTATO", "PAGATO"])])
        n_sca = len(df[df["Stato Reale"] == "SCADUTO"])
        try:
            val_acc = float(df[df["Stato Reale"].isin(["ACCETTATO", "PAGATO"])]["Totale"].astype(float).sum())
        except Exception:
            val_acc = 0.0

        # Costruzione righe JSON
        ha_link = "HTML_B64" in df.columns
        righe = []
        for _, r in df.iterrows():
            data_uri = ""
            if ha_link:
                html_dec = decomprimi_html(str(r.get("HTML_B64", "")).strip())
                if html_dec:
                    b64_clean = _b64.b64encode(html_dec.encode("utf-8")).decode("utf-8")
                    data_uri  = f"data:text/html;base64,{b64_clean}"
            righe.append({
                "data":    str(r.get("Data",       "")).strip(),
                "cod":     str(r.get("Codice",     "")).strip().replace(".0", ""),
                "ver":     str(r.get("Versione_Di","")).strip(),
                "cliente": str(r.get("Cliente",    "")).strip(),
                "pod":     str(r.get("POD",        "")).strip(),
                "totale":  float(r["Totale"]) if str(r.get("Totale","")).replace(".","").isdigit() else 0.0,
                "stato":   str(r.get("Stato Reale","")).strip(),
                "firma":   str(r.get("Data Firma", "")).strip(),
                "link":    data_uri,
            })

        html_archivio = f"""<!DOCTYPE html><html><head><meta charset="UTF-8">
<style>
*{{box-sizing:border-box;margin:0;padding:0}}
body{{font-family:Helvetica,Arial,sans-serif;font-size:13px;color:#141414;background:transparent}}
.kpi-row{{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:10px;margin-bottom:16px}}
.kpi{{background:#fff;border:0.5px solid #e2e6ec;border-radius:10px;padding:.85rem 1rem}}
.kpi-label{{font-size:11px;color:#8c8c8c;margin-bottom:4px}}
.kpi-val{{font-size:20px;font-weight:500}}
.toolbar{{display:flex;gap:8px;margin-bottom:12px;align-items:center;flex-wrap:wrap}}
.search{{flex:1;min-width:160px;padding:7px 11px;border:0.5px solid #d0d4dc;border-radius:8px;
         font-size:13px;outline:none;background:#fff;color:#141414}}
.search:focus{{border-color:#185FA5}}
.fbtn{{padding:6px 13px;border:0.5px solid #d0d4dc;border-radius:8px;background:#fff;
       font-size:12px;color:#555;cursor:pointer;white-space:nowrap}}
.fbtn.on{{background:#003366;color:#fff;border-color:#003366}}
.table-wrap{{background:#fff;border:0.5px solid #e2e6ec;border-radius:12px;overflow:hidden}}
table{{width:100%;border-collapse:collapse;font-size:12px}}
thead tr{{background:#f7f8fa;border-bottom:1px solid #e2e6ec}}
th{{padding:9px 12px;text-align:left;font-size:11px;font-weight:500;color:#8c8c8c;
    text-transform:uppercase;letter-spacing:.4px;white-space:nowrap;cursor:pointer;user-select:none}}
th:hover{{color:#003366}}
th.asc::after{{content:" ↑"}}
th.desc::after{{content:" ↓"}}
td{{padding:9px 12px;border-bottom:0.5px solid #f0f2f5;vertical-align:middle}}
tr:last-child td{{border-bottom:none}}
tr:hover td{{background:#fafbfc}}
.badge{{display:inline-block;padding:3px 10px;border-radius:20px;font-size:11px;font-weight:500}}
.b-acc{{background:#EAF3DE;color:#27500A}}
.b-pag{{background:#E6F1FB;color:#0C447C}}
.b-inv{{background:#FAEEDA;color:#633806}}
.b-sca{{background:#FCEBEB;color:#791F1F}}
.pdf-btn{{display:inline-flex;align-items:center;gap:3px;padding:3px 9px;
          border:0.5px solid #d0d4dc;border-radius:6px;background:#f7f8fa;
          font-size:11px;color:#555;text-decoration:none;white-space:nowrap}}
.pdf-btn:hover{{background:#e6f0fa;border-color:#185FA5;color:#185FA5}}
.footer{{display:flex;justify-content:space-between;align-items:center;
         padding:9px 12px;background:#f7f8fa;border-top:0.5px solid #e2e6ec;
         font-size:11px;color:#8c8c8c}}
.ver{{font-size:10px;color:#aaa;margin-top:2px}}
</style></head><body>

<div class="kpi-row">
  <div class="kpi"><div class="kpi-label">Inviati</div>
    <div class="kpi-val" style="color:#854F0B">{n_inv}</div></div>
  <div class="kpi"><div class="kpi-label">Accettati</div>
    <div class="kpi-val" style="color:#27500A">{n_acc}</div></div>
  <div class="kpi"><div class="kpi-label">Scaduti</div>
    <div class="kpi-val" style="color:#791F1F">{n_sca}</div></div>
  <div class="kpi"><div class="kpi-label">Valore accettato</div>
    <div class="kpi-val">{val_acc:,.0f} €</div></div>
</div>

<div class="toolbar">
  <input class="search" id="q" placeholder="Cerca cliente, codice, POD…">
  <button class="fbtn on" onclick="fil('Tutti',this)">Tutti</button>
  <button class="fbtn" onclick="fil('INVIATO',this)">Inviati</button>
  <button class="fbtn" onclick="fil('ACCETTATO',this)">Accettati</button>
  <button class="fbtn" onclick="fil('SCADUTO',this)">Scaduti</button>
</div>

<div class="table-wrap">
<table>
<thead><tr>
  <th onclick="sort('data')">Data</th>
  <th onclick="sort('cod')">Codice</th>
  <th onclick="sort('cliente')">Cliente</th>
  <th onclick="sort('pod')">POD</th>
  <th onclick="sort('totale')" style="text-align:right">Totale €</th>
  <th onclick="sort('stato')">Stato</th>
  <th onclick="sort('firma')">Firmato il</th>
  <th>Preventivo</th>
</tr></thead>
<tbody id="tb"></tbody>
        <tr id="expand-row" style="display:none"></tr>
</table>
<div class="footer">
  <span id="cnt"></span>
  <span>PolisEnergia — Archivio Preventivi</span>
</div>
</div>

<script>
const ALL = {json.dumps(righe, ensure_ascii=False)};
let fStato='Tutti', sortCol='data', sortDir=1;

const badge = s => {{
  const m={{ACCETTATO:'b-acc',PAGATO:'b-pag',INVIATO:'b-inv',SCADUTO:'b-sca'}};
  const l={{ACCETTATO:'Accettato',PAGATO:'Pagato',INVIATO:'Inviato',SCADUTO:'Scaduto'}};
  return `<span class="badge ${{m[s]||''}}">${{l[s]||s}}</span>`;
}};

let mostraTutti = false;

function render(){{
  const q = document.getElementById('q').value.toLowerCase();
  let rows = ALL.filter(r=>{{
    const mq = !q || r.cliente.toLowerCase().includes(q) ||
                r.cod.includes(q) || r.pod.toLowerCase().includes(q);
    const ms = fStato==='Tutti' || r.stato===fStato;
    return mq && ms;
  }});
  rows.sort((a,b)=>{{
    let va=a[sortCol], vb=b[sortCol];
    if(sortCol==='totale'){{ return (va-vb)*sortDir; }}
    return String(va).localeCompare(String(vb),'it')*sortDir;
  }});

  const totale = rows.length;
  const visibili = mostraTutti ? rows : rows.slice(0, 10);

  document.getElementById('tb').innerHTML = visibili.map(r=>`
    <tr>
      <td style="color:#8c8c8c;font-size:11px">${{r.data}}</td>
      <td>
        <div style="font-weight:500;font-size:12px;color:#141414">${{r.cod}}</div>
        ${{r.ver && r.ver!='nan' ? `<div class="ver">rev. di ${{r.ver}}</div>` : ''}}
      </td>
      <td style="font-weight:500">${{r.cliente}}</td>
      <td style="font-family:monospace;font-size:11px;color:#666">${{r.pod}}</td>
      <td style="text-align:right;font-weight:500;font-variant-numeric:tabular-nums">
        ${{r.totale.toLocaleString('it-IT',{{minimumFractionDigits:2}})}}
      </td>
      <td>${{badge(r.stato)}}</td>
      <td style="color:#8c8c8c;font-size:11px">${{r.firma||'—'}}</td>
      <td>${{r.link
        ? `<button class="pdf-btn" onclick="apriHTML('${{r.link}}')">📄 Apri</button>`
        : '<span style="color:#ccc;font-size:11px">—</span>'}}</td>
    </tr>`).join('');

  const expandRow = document.getElementById('expand-row');
  if(totale > 10){{
    expandRow.style.display = '';
    expandRow.innerHTML = `<td colspan="8" style="text-align:center;padding:10px 0;border-top:1px solid #e2e6ec;">
      <button onclick="toggleMostraTutti()" style="background:none;border:0.5px solid #d0d4dc;
        border-radius:6px;padding:5px 18px;font-size:12px;color:#555;cursor:pointer;">
        ${{mostraTutti
          ? '▲ Mostra solo ultimi 10'
          : `▼ Mostra tutti i ${{totale}} preventivi`}}
      </button>
    </td>`;
  }} else {{
    expandRow.style.display = 'none';
  }}

  document.getElementById('cnt').textContent =
    `${{mostraTutti || totale<=10 ? totale : '10 di '+totale}} preventiv${{totale===1?'o':'i'}}`;

  document.querySelectorAll('th').forEach(th=>th.classList.remove('asc','desc'));
  const cols=['data','cod','cliente','pod','totale','stato','firma'];
  const idx=cols.indexOf(sortCol);
  if(idx>=0) document.querySelectorAll('th')[idx].classList.add(sortDir===1?'asc':'desc');
}}

function toggleMostraTutti(){{
  mostraTutti = !mostraTutti;
  render();
}}

function apriHTML(b64url) {{
  const b64 = b64url.replace('data:text/html;base64,', '');
  const bin = atob(b64);
  const arr = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  const blob = new Blob([arr], {{type: 'text/html'}});
  const url  = URL.createObjectURL(blob);
  window.open(url, '_blank');
  setTimeout(() => URL.revokeObjectURL(url), 10000);
}}

function fil(s,btn){{
  fStato=s;
  document.querySelectorAll('.fbtn').forEach(b=>b.classList.remove('on'));
  btn.classList.add('on');
  render();
}}

function sort(col){{
  if(sortCol===col) sortDir*=-1; else {{ sortCol=col; sortDir=1; }}
  render();
}}

document.getElementById('q').addEventListener('input',render);
render();
</script></body></html>"""

        h = min(900, max(400, 280 + min(len(df), 10) * 44))
        components.html(html_archivio, height=h, scrolling=True)

        # ── EXPORT EXCEL ──
        buf_xls = io.BytesIO()
        export_cols = [c for c in ["Data", "Codice", "Versione_Di", "Cliente", "POD",
                                    "Totale", "Stato Reale", "Email", "Data Firma"]
                       if c in df.columns]
        df[export_cols].to_excel(buf_xls, index=False, engine="openpyxl")
        buf_xls.seek(0)
        st.download_button(
            label="📊 Esporta in Excel",
            data=buf_xls,
            file_name=f"Archivio_Preventivi_{datetime.now().strftime('%d%m%Y')}.xlsx",
            mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
            use_container_width=True,
        )

        # ── REINVIO EMAIL ──
        st.divider()
        st.subheader("📨 Reinvia email a cliente")

        reinviabili = df[
            df["Stato Reale"].isin(["INVIATO", "SCADUTO"])
        ]["Codice"].astype(str).tolist()

        if not reinviabili:
            st.info("Nessun preventivo da reinviare.")
        else:
            cod_reinvio = st.selectbox("Seleziona preventivo:", reinviabili, key="sel_reinvio")
            row_r = df[df["Codice"].astype(str) == cod_reinvio]

            if not row_r.empty:
                r       = row_r.iloc[0]
                nome_r  = str(r.get("Cliente", ""))
                email_r = str(r.get("Email", ""))
                pod_r   = str(r.get("POD", ""))

                col_r1, col_r2 = st.columns(2)
                email_reinvio = col_r1.text_input(
                    "Email destinatario",
                    value=email_r if email_r not in {"", "nan"} else "",
                    key="email_reinvio"
                )
                otp_key   = f"otp_reinvio_{cod_reinvio}"
                if otp_key not in st.session_state:
                    st.session_state[otp_key] = genera_otp()
                nuovo_otp    = st.session_state[otp_key]
                link_reinvio = f"{APP_URL}/?codice={cod_reinvio}&otp={nuovo_otp}"

                template = st.session_state.get("email_template",
                    "Spett.le {nome},\nin allegato il preventivo n. {codice}.\n\n"
                    "Per firmare digitalmente clicca qui: {link}\nOTP: {otp}\n\n"
                    "Il link è valido per {giorni} giorni.\n\nCordiali saluti,\nPolisEnergia srl"
                )
                try:
                    testo_r = template.format(
                        nome=nome_r, codice=cod_reinvio, link=link_reinvio,
                        otp=nuovo_otp, giorni=OTP_SCADENZA_GIORNI,
                        totale=str(r.get("Totale", "")), pod=pod_r,
                    )
                except Exception:
                    testo_r = (f"Spett.le {nome_r},\nin allegato il preventivo n. {cod_reinvio}.\n\n"
                               f"Firma qui: {link_reinvio}\nOTP: {nuovo_otp}\n\n"
                               f"Cordiali saluti,\nPolisEnergia srl")

                corpo_r = st.text_area("Testo email:", value=testo_r, height=160, key="corpo_reinvio")

                if col_r2.button("🚀 REINVIA EMAIL", use_container_width=True, key="btn_reinvio"):
                    if not email_reinvio.strip():
                        st.error("Inserisci l'indirizzo email.")
                    else:
                        try:
                            with st.spinner("Invio in corso..."):
                                smtp = get_smtp_config()
                                invia_email(smtp=smtp, to=email_reinvio.strip(),
                                            subject=f"Preventivo PolisEnergia n. {cod_reinvio}",
                                            body=corpo_r)
                            idx_r = df[df["Codice"].astype(str) == cod_reinvio].index[0]
                            df.at[idx_r, "Stato"] = "Inviato"
                            # Salva il NUOVO OTP nel foglio: invalida automaticamente il vecchio link
                            df.at[idx_r, "OTP"]   = nuovo_otp
                            if "Email" in df.columns:
                                df.at[idx_r, "Email"] = email_reinvio.strip()
                            conn.update(data=df.drop(columns=["Stato Reale"], errors="ignore"))
                            del st.session_state[otp_key]
                            st.success(f"✅ Email reinviata a {email_reinvio}! Il vecchio link non è più valido.")
                        except Exception as e:
                            mostra_errore("Errore invio.", e)

        # ── STORICO REVISIONI ──
        if "Versione_Di" in df.columns and df["Versione_Di"].notna().any():
            ver_non_vuote = df["Versione_Di"].astype(str).str.strip()
            if (ver_non_vuote != "").any() and (ver_non_vuote != "nan").any():
                st.divider()
                st.subheader("🔄 Storico revisioni")
                pod_con_rev = df[
                    ver_non_vuote.isin(ver_non_vuote[ver_non_vuote != ""].values)
                ]["POD"].unique()
                if len(pod_con_rev):
                    pod_sel = st.selectbox("POD:", pod_con_rev, key="pod_storico")
                    catena = df[df["POD"].astype(str) == pod_sel][
                        ["Data", "Codice", "Versione_Di", "Totale", "Stato Reale"]
                    ].sort_values("Data")
                    st.dataframe(catena, use_container_width=True, hide_index=True)

    except Exception as e:
        mostra_errore("Impossibile caricare l'archivio.", e)


# ==============================================================================
# 12. SEZIONE: STATISTICHE + PAGAMENTI
# ==============================================================================
elif scelta == "📊 Statistiche":
    st.title("📊 Statistiche")
    try:
        conn = st.connection("gsheets", type=GSheetsConnection)
        df   = conn.read(ttl=GSHEETS_CACHE_TTL)

        if df.empty:
            st.info("Nessun dato disponibile.")
            st.stop()

        def to_float(v):
            try: return float(str(v).replace(",", "."))
            except: return 0.0

        def to_float_or_nan(v):
            try:
                s = str(v).strip()
                if s in {"", "nan", "None", "0", "0.0"}:
                    return float("nan")
                return float(s.replace(",", "."))
            except:
                return float("nan")

        df["Stato Reale"] = df.apply(calcola_stato_reale, axis=1)
        df["Totale_N"]    = df["Totale"].apply(to_float)

        if "Gestione" in df.columns and "Oneri" in df.columns:
            df["Gestione_N"] = df["Gestione"].apply(to_float_or_nan)
            df["Oneri_N"]    = df["Oneri"].apply(to_float_or_nan)
            df["Margine_N"]  = df["Gestione_N"] + df["Oneri_N"]
        else:
            df["Gestione_N"] = float("nan")
            df["Oneri_N"]    = float("nan")
            df["Margine_N"]  = float("nan")

        try:
            df["_Data"] = pd.to_datetime(df["Data"], format="%d/%m/%Y", errors="coerce")
            df["Mese"]  = df["_Data"].dt.to_period("M").astype(str)
        except Exception:
            df["Mese"] = "N/D"

        # KPI
        n_tot      = len(df)
        n_acc      = len(df[df["Stato Reale"].isin(["ACCETTATO", "PAGATO"])])
        n_pag      = len(df[df["Stato Reale"] == "PAGATO"])
        n_scad     = len(df[df["Stato Reale"] == "SCADUTO"])
        inc_pag    = df[df["Stato Reale"] == "PAGATO"]["Totale_N"].sum()
        marg_pag   = float(np.nansum(df[df["Stato Reale"] == "PAGATO"]["Margine_N"]))
        n_con_marg = int(df[df["Stato Reale"] == "PAGATO"]["Margine_N"].notna().sum())
        marg_pct   = round(marg_pag / inc_pag * 100, 1) if inc_pag and marg_pag else 0
        tasso      = round(n_acc / n_tot * 100, 1) if n_tot else 0
        n_inv_puro = n_tot - n_acc - n_scad

        mesi_sorted = sorted(df["Mese"].dropna().unique().tolist())
        mesi_label  = [m[-2:] + "/" + m[:4] for m in mesi_sorted]

        def conta_per_mese(stato):
            return [int(df[(df["Mese"] == m) & (df["Stato Reale"] == stato)].shape[0])
                    for m in mesi_sorted]

        inv_mese  = conta_per_mese("INVIATO")
        acc_mese  = [int(df[(df["Mese"]==m)&(df["Stato Reale"].isin(["ACCETTATO","PAGATO"]))].shape[0])
                     for m in mesi_sorted]
        pag_mese  = conta_per_mese("PAGATO")
        scad_mese = conta_per_mese("SCADUTO")
        val_mese  = [round(float(df[(df["Mese"]==m)&(df["Stato Reale"]=="PAGATO")]["Totale_N"].sum()),2)
                     for m in mesi_sorted]
        marg_mese = [round(float(np.nansum(df[(df["Mese"]==m)&(df["Stato Reale"]=="PAGATO")]["Margine_N"])),2)
                     for m in mesi_sorted]

        html_stats = f"""<!DOCTYPE html><html><head><meta charset="UTF-8">
<style>
  body{{margin:0;font-family:Helvetica,Arial,sans-serif;color:#141414;background:transparent}}
  .kpi-grid{{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:12px;margin-bottom:2rem}}
  .kpi{{background:#f7f8fa;border-radius:8px;padding:1rem;display:flex;flex-direction:column;gap:4px}}
  .kpi-label{{font-size:12px;color:#8c8c8c}}
  .kpi-value{{font-size:26px;font-weight:500;color:#141414}}
  .kpi-sub{{font-size:11px;color:#b0b0b0}}
  .charts-grid{{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:16px;margin-bottom:16px}}
  .card{{background:#fff;border:0.5px solid #e2e6ec;border-radius:12px;padding:1.25rem}}
  .card-title{{font-size:11px;font-weight:500;color:#8c8c8c;text-transform:uppercase;letter-spacing:.5px;margin:0 0 10px}}
  .legend{{display:flex;gap:14px;margin-bottom:10px;font-size:11px;color:#666;flex-wrap:wrap}}
  .legend span{{display:flex;align-items:center;gap:4px}}
  .dot{{width:10px;height:10px;border-radius:2px;flex-shrink:0}}
</style></head><body>
<div class="kpi-grid">
  <div class="kpi"><span class="kpi-label">Preventivi totali</span>
    <span class="kpi-value">{n_tot}</span><span class="kpi-sub">tasso firma {tasso}%</span></div>
  <div class="kpi"><span class="kpi-label">Pagati</span>
    <span class="kpi-value" style="color:#0C447C">{n_pag}</span>
    <span class="kpi-sub">incassato {inc_pag:,.0f} €</span></div>
  <div class="kpi"><span class="kpi-label">Margine reale</span>
    <span class="kpi-value" style="color:#3B6D11">{marg_pag:,.0f} €</span>
    <span class="kpi-sub">{marg_pct}% sul fatturato{f" · su {n_con_marg}/{n_pag} pagati" if n_pag and n_con_marg < n_pag else ""}</span></div>
  <div class="kpi"><span class="kpi-label">Scaduti</span>
    <span class="kpi-value" style="color:#A32D2D">{n_scad}</span>
    <span class="kpi-sub">da reinviare</span></div>
</div>
<div class="charts-grid">
  <div class="card">
    <p class="card-title">Preventivi per mese</p>
    <div class="legend">
      <span><span class="dot" style="background:#B5D4F4"></span>Inviati</span>
      <span><span class="dot" style="background:#97C459"></span>Accettati</span>
      <span><span class="dot" style="background:#185FA5"></span>Pagati</span>
      <span><span class="dot" style="background:#F09595"></span>Scaduti</span>
    </div>
    <div style="position:relative;height:200px"><canvas id="c1"></canvas></div>
  </div>
  <div class="card">
    <p class="card-title">Incassato per mese (€)</p>
    <div style="position:relative;height:224px"><canvas id="c2"></canvas></div>
  </div>
</div>
<div class="charts-grid">
  <div class="card">
    <p class="card-title">Margine reale per mese (€)</p>
    <div style="position:relative;height:200px"><canvas id="c4"></canvas></div>
  </div>
  <div class="card">
    <p class="card-title">Distribuzione stati</p>
    <div style="position:relative;height:200px"><canvas id="c3"></canvas></div>
  </div>
</div>
<script src="https://cdnjs.cloudflare.com/ajax/libs/Chart.js/4.4.1/chart.umd.js"></script>
<script>
const mesi={json.dumps(mesi_label)};const inv={json.dumps(inv_mese)};const acc={json.dumps(acc_mese)};
const pag={json.dumps(pag_mese)};const scad={json.dumps(scad_mese)};
const valori={json.dumps(val_mese)};const margini={json.dumps(marg_mese)};
const grid='rgba(0,0,0,0.06)';const tick='#999';
const base={{responsive:true,maintainAspectRatio:false,plugins:{{legend:{{display:false}}}},
  scales:{{x:{{grid:{{color:grid}},ticks:{{color:tick,font:{{size:11}},autoSkip:false,maxRotation:45}},border:{{display:false}}}},
           y:{{grid:{{color:grid}},ticks:{{color:tick,font:{{size:11}}}},border:{{display:false}}}}}}}};
new Chart(document.getElementById('c1'),{{type:'bar',data:{{labels:mesi,datasets:[
  {{label:'Inviati',data:inv,backgroundColor:'#B5D4F4',borderRadius:3,stack:'s'}},
  {{label:'Accettati',data:acc,backgroundColor:'#97C459',borderRadius:3,stack:'s'}},
  {{label:'Pagati',data:pag,backgroundColor:'#185FA5',borderRadius:3,stack:'s'}},
  {{label:'Scaduti',data:scad,backgroundColor:'#F09595',borderRadius:3,stack:'s'}}]}},
  options:{{...base,scales:{{x:{{...base.scales.x,stacked:true}},y:{{...base.scales.y,stacked:true,ticks:{{...base.scales.y.ticks,stepSize:1}}}}}}}}}});
new Chart(document.getElementById('c2'),{{type:'bar',data:{{labels:mesi,datasets:[
  {{label:'€',data:valori,backgroundColor:'#185FA5',borderRadius:3}}]}},
  options:{{...base,scales:{{x:base.scales.x,y:{{...base.scales.y,ticks:{{...base.scales.y.ticks,callback:v=>v.toLocaleString('it-IT')+'€'}}}}}}}}}});
new Chart(document.getElementById('c4'),{{type:'bar',data:{{labels:mesi,datasets:[
  {{label:'Margine €',data:margini,backgroundColor:'#3B6D11',borderRadius:3}}]}},
  options:{{...base,scales:{{x:base.scales.x,y:{{...base.scales.y,ticks:{{...base.scales.y.ticks,callback:v=>v.toLocaleString('it-IT')+'€'}}}}}}}}}});
new Chart(document.getElementById('c3'),{{type:'bar',
  data:{{labels:['Inviato','Accettato','Pagato','Scaduto'],
    datasets:[{{data:[{n_inv_puro},{n_acc},{n_pag},{n_scad}],
      backgroundColor:['#B5D4F4','#97C459','#185FA5','#F09595'],borderRadius:4}}]}},
  options:{{indexAxis:'y',responsive:true,maintainAspectRatio:false,
    plugins:{{legend:{{display:false}}}},
    scales:{{x:{{grid:{{color:grid}},ticks:{{color:tick,font:{{size:11}},stepSize:1}},border:{{display:false}}}},
             y:{{grid:{{display:false}},ticks:{{color:tick,font:{{size:12,weight:'500'}}}},border:{{display:false}}}}}}}}}});
</script></body></html>"""

        components.html(html_stats, height=880, scrolling=False)

        # ── PAGAMENTI ──
        st.divider()
        st.subheader("💰 Gestione Pagamenti")

        pagati = df[df["Stato Reale"] == "PAGATO"]

        if not pagati.empty:
            cols_p = [c for c in ["Data", "Codice", "Cliente", "POD",
                                   "Totale_N", "Margine_N", "Data Pagamento"]
                      if c in pagati.columns]
            st.dataframe(
                pagati[cols_p].rename(columns={"Totale_N":"Totale €","Margine_N":"Margine €"}),
                use_container_width=True, hide_index=True,
                column_config={
                    "Totale €":  st.column_config.NumberColumn(format="%.2f"),
                    "Margine €": st.column_config.NumberColumn(format="%.2f"),
                }
            )
        else:
            st.info("Nessun preventivo pagato ancora registrato.")

        # Matching fatture
        st.divider()
        st.subheader("📂 Carica file fatture per matching")
        st.caption("Il matching avviene per POD (criterio principale), poi importo + nome.")
        file_fatt = st.file_uploader(
            "File fatture (Excel o CSV)", type=["xlsx", "xls", "csv"], key="fatt_up"
        )

        if file_fatt:
            try:
                if file_fatt.name.endswith(".csv"):
                    df_fatt = pd.read_csv(file_fatt, sep=None, engine="python",
                                          encoding="utf-8-sig", dtype=str)
                else:
                    df_fatt = pd.read_excel(file_fatt, dtype=str)

                df_fatt.columns = [c.strip() for c in df_fatt.columns]

                def trova_col(dff, keywords):
                    for c in dff.columns:
                        if any(k in c.upper() for k in keywords):
                            return c
                    return None

                col_pod  = trova_col(df_fatt, ["POD"])
                col_cli  = trova_col(df_fatt, ["CLIENTE","CLIENT","RAGIO","DENOMINAZ","NOME"])
                col_dpag = trova_col(df_fatt, ["DATA PAGAMENTO","DATA PAG"])
                col_num  = trova_col(df_fatt, ["NUMERO","NUM. FATT","N. FATT","FATTURA"])

                COL_COMP = ["Totale Imponibile","Totale Non Imponibile","Totale Iva",
                            "Totale Canone RAI","Totale Deposito Cauzionale"]
                col_comp = [c for c in COL_COMP if c in df_fatt.columns]

                def to_f(v):
                    try: return float(str(v).replace(",",".").replace(" ",""))
                    except: return 0.0

                if col_comp:
                    df_fatt["_imp"] = sum(df_fatt[c].apply(to_f) for c in col_comp)
                else:
                    col_imp = trova_col(df_fatt, ["IMPORT","TOTAL","AMOUNT"])
                    if col_imp is None:
                        st.error("Colonna importo non trovata.")
                        if DEBUG_MODE:
                            st.write("Colonne:", list(df_fatt.columns))
                        st.stop()
                    df_fatt["_imp"] = df_fatt[col_imp].apply(to_f)

                if col_pod:  df_fatt["_pod"]  = df_fatt[col_pod].astype(str).str.strip().str.upper()
                if col_cli:  df_fatt["_cli"]  = df_fatt[col_cli].astype(str).str.strip().str.upper()
                if col_dpag: df_fatt["_dpag"] = df_fatt[col_dpag].astype(str).str.strip()

                candidati = df[df["Stato Reale"] != "PAGATO"].copy()
                col_diag1, col_diag2 = st.columns(2)
                col_diag1.metric("Preventivi da abbinare", len(candidati))
                col_diag2.metric("Fatture nel file", len(df_fatt))

                if candidati.empty:
                    st.info("Tutti i preventivi sono già stati segnati come PAGATO.")
                    st.stop()

                def normalizza(s):
                    s = str(s).upper().strip()
                    for t in ["S.R.L.","SRL","S.P.A.","SPA","S.N.C.","SNC","SAS","."," ,","-"]:
                        s = s.replace(t, " ")
                    return " ".join(s.split())

                def sim(a, b):
                    pa = set(normalizza(a).split())
                    pb = set(normalizza(b).split())
                    return len(pa & pb) / len(pa) if pa else 0.0

                matches, non_trovati = [], []

                for _, prev in candidati.iterrows():
                    tot_p    = prev["Totale_N"]
                    pod_prev = str(prev.get("POD","")).strip().upper()
                    nom_prev = str(prev.get("Cliente",""))
                    cod_prev = str(prev.get("Codice","")).replace(".0","")
                    fatt_row = None; metodo = ""; affid = ""

                    if col_pod and pod_prev:
                        per_pod = df_fatt[df_fatt["_pod"] == pod_prev]
                        if not per_pod.empty:
                            fatt_row = per_pod.iloc[0]; metodo = "POD"; affid = "✅ Alta (POD)"

                    if fatt_row is None:
                        per_imp = df_fatt[(df_fatt["_imp"] - tot_p).abs() < 0.05]
                        if not per_imp.empty:
                            if col_cli:
                                per_imp = per_imp.copy()
                                per_imp["_sim"] = per_imp["_cli"].apply(lambda n: sim(nom_prev, n))
                                buone = per_imp[per_imp["_sim"] >= 0.5].sort_values("_sim", ascending=False)
                                if not buone.empty:
                                    fatt_row = buone.iloc[0]; metodo = "Importo+Nome"
                                    affid = "✅ Alta" if fatt_row["_sim"] >= 0.8 else "🟡 Media"
                                else:
                                    non_trovati.append({"Codice":cod_prev,"Cliente":nom_prev,
                                        "Motivo":f"Importo OK ma nome diverso ({per_imp.iloc[0].get('_cli','?')})"})
                                    continue
                            else:
                                fatt_row = per_imp.iloc[0]; metodo = "Solo importo"; affid = "⚠️ Verificare"
                        else:
                            non_trovati.append({"Codice":cod_prev,"Cliente":nom_prev,
                                                "Motivo":"Nessuna fattura corrispondente"})
                            continue

                    dpag_f = str(fatt_row.get("_dpag","")).strip() if col_dpag else ""
                    margine_val = prev["Margine_N"]
                    matches.append({
                        "Codice": cod_prev, "Cliente": nom_prev, "POD": pod_prev,
                        "Totale": tot_p,
                        "Margine": margine_val if not pd.isna(margine_val) else None,
                        "N. Fattura": str(fatt_row.get(col_num,"—")) if col_num else "—",
                        "Importo fatt.": fatt_row["_imp"],
                        "Data pag.": dpag_f, "Match": metodo, "Affidabilità": affid,
                    })

                if matches:
                    st.success(f"✅ {len(matches)} corrispondenze trovate!")
                    df_match = pd.DataFrame(matches)
                    st.dataframe(df_match, use_container_width=True, hide_index=True,
                        column_config={
                            "Totale":        st.column_config.NumberColumn("Totale prev. €", format="%.2f"),
                            "Margine":       st.column_config.NumberColumn("Margine €",      format="%.2f"),
                            "Importo fatt.": st.column_config.NumberColumn("Importo fatt. €",format="%.2f"),
                        })
                elif not non_trovati:
                    st.warning("Nessuna corrispondenza trovata. Verifica i dati:")
                    c1, c2 = st.columns(2)
                    with c1:
                        st.caption("POD nei preventivi archivio:")
                        st.write(candidati["POD"].dropna().unique().tolist())
                    with c2:
                        st.caption("POD nelle fatture:")
                        if col_pod:
                            st.write(df_fatt["_pod"].dropna().unique().tolist()[:10])
                        else:
                            st.write("Colonna POD non trovata nel file fatture")

                if non_trovati:
                    with st.expander(f"⚠️ {len(non_trovati)} senza corrispondenza"):
                        st.dataframe(pd.DataFrame(non_trovati), use_container_width=True, hide_index=True)

                if matches:
                    st.divider()
                    st.subheader("✅ Conferma pagamenti")
                    opzioni = [f"{r['Codice']} — {r['Cliente']} ({r['Affidabilità']})"
                               for _, r in df_match.iterrows()]
                    default_sel = [o for o,(_, r) in zip(opzioni, df_match.iterrows())
                                   if "Solo importo" not in r["Affidabilità"]]
                    sel_opz = st.multiselect("Preventivi da confermare:", opzioni, default=default_sel)
                    sel = [o.split(" — ")[0] for o in sel_opz]

                    date_fatt = {r["Codice"]: r["Data pag."] for _, r in df_match.iterrows()
                                 if r.get("Data pag.")}
                    usa_data_fatt = col_dpag and any(date_fatt.values())
                    if usa_data_fatt:
                        st.info("📅 Verrà usata la data pagamento dal file fatture.")
                    else:
                        data_pag = st.date_input("Data pagamento", value=datetime.now())

                    if st.button("💾 SEGNA COME PAGATO", type="primary",
                                 use_container_width=True, key="btn_paga"):
                        if not sel:
                            st.error("Seleziona almeno un preventivo.")
                        else:
                            try:
                                df_upd = conn.read(ttl=0)
                                df_upd["Codice_Clean"] = (df_upd["Codice"].astype(str)
                                    .str.strip().str.replace(".0","",regex=False))
                                for cod_s in sel:
                                    idx = df_upd[df_upd["Codice_Clean"] == cod_s].index
                                    if not idx.empty:
                                        ds = date_fatt.get(cod_s,"") if usa_data_fatt else data_pag.strftime("%d/%m/%Y")
                                        df_upd.at[idx[0], "Stato"]          = "PAGATO"
                                        df_upd.at[idx[0], "Data Pagamento"] = ds
                                conn.update(data=df_upd.drop(columns=["Codice_Clean"], errors="ignore"))
                                st.success(f"✅ {len(sel)} preventiv{'o' if len(sel)==1 else 'i'} segnati come PAGATO!")
                                st.rerun()
                            except Exception as e:
                                mostra_errore("Errore aggiornamento foglio.", e)

            except Exception as e:
                mostra_errore("Errore lettura file fatture.", e)

    except Exception as e:
        mostra_errore("Impossibile caricare le statistiche.", e)

# ==============================================================================
# 13. SEZIONE: IMPOSTAZIONI
# ==============================================================================
elif scelta == "⚙️ Impostazioni":
    st.title("⚙️ Impostazioni")

    st.subheader("📝 Template Email")
    st.markdown(
        "Personalizza il testo della mail inviata ai clienti. "
        "Usa le variabili tra `{` `}` per inserire i dati dinamici:"
    )
    st.code(
        "{nome}  →  Ragione Sociale cliente\n"
        "{codice}  →  Numero preventivo\n"
        "{link}  →  Link di firma\n"
        "{otp}  →  Codice OTP\n"
        "{giorni}  →  Giorni di validità\n"
        "{totale}  →  Importo totale\n"
        "{pod}  →  Codice POD",
        language=None
    )

    default_template = (
        "Spett.le {nome},\n"
        "in allegato il preventivo n. {codice}.\n\n"
        "Per firmare digitalmente clicca qui: {link}\n"
        "OTP: {otp}\n\n"
        "Il link è valido per {giorni} giorni.\n\n"
        "Cordiali saluti,\nPolisEnergia srl"
    )
    template_attuale = st.session_state.get("email_template", default_template)
    nuovo_template   = st.text_area(
        "Template email:",
        value=template_attuale,
        height=220,
        key="input_template"
    )

    col_s1, col_s2 = st.columns(2)
    if col_s1.button("💾 Salva template", use_container_width=True):
        mancanti = [v for v in ["{nome}", "{codice}", "{link}", "{otp}"]
                    if v not in nuovo_template]
        if mancanti:
            st.error(f"⚠️ Il template deve contenere: {', '.join(mancanti)}")
        else:
            st.session_state["email_template"] = nuovo_template
            st.success("✅ Template salvato per questa sessione!")
            st.info("ℹ️ Il template viene salvato in sessione — verrà reimpostato al riavvio dell'app.")

    if col_s2.button("↩️ Ripristina default", use_container_width=True):
        st.session_state["email_template"] = default_template
        st.success("Template ripristinato.")
        st.rerun()

    # Anteprima
    st.divider()
    st.subheader("👁 Anteprima")
    try:
        anteprima = nuovo_template.format(
            nome="ROSSI MARIO SRL",
            codice="260403143022",
            link=f"{APP_URL}/?codice=260403143022&otp=123456",
            otp="123456",
            giorni=OTP_SCADENZA_GIORNI,
            totale="414.40",
            pod="IT001E12345678",
        )
        st.text(anteprima)
    except KeyError as e:
        st.warning(f"Variabile non riconosciuta nel template: {e}")
