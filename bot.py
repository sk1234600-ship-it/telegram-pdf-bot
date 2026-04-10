import os
import logging
import tempfile
import zipfile
import io
import re
import random
import json
import time
from datetime import datetime, timedelta
from threading import Thread

from flask import Flask
from telegram import Update
from telegram.ext import ApplicationBuilder, CommandHandler, MessageHandler, filters, ContextTypes
import fitz  # PyMuPDF
from google import genai

# ================= CONFIGURATION (READ FROM ENVIRONMENT) =================
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")

if not TELEGRAM_BOT_TOKEN:
    raise ValueError("Missing TELEGRAM_BOT_TOKEN environment variable")
if not GEMINI_API_KEY:
    raise ValueError("Missing GEMINI_API_KEY environment variable")

# Path to your template PDF – must be in the same directory as bot.py
INPUT_PDF = "template.pdf"
PARSER_MODE = "gemini"   # or "fallback"

# Default customer details (can be overridden per entry)
DEFAULT_CUST_NAME   = "VIPUL MITTAL"
DEFAULT_CUST_ID     = "11593956"
DEFAULT_MOBILE      = "9826260443"
DEFAULT_TAG_ACCOUNT = "21434130"

# ================= COLORS & METRICS (unchanged) =================
TEXT_COLOR = (0, 0, 0)
FONT_SIZE = 8

COORD = {
    "row_date_x_default": (22.0, 62.91),
    "row_time_x_default": (65.14, 96.27),
    "row_date_x_last": (22.0, 62.91),
    "row_time_x_last": (65.14, 96.27),
    "row_tops": [352.336, 369.336, 386.336, 409.336, 426.336, 444.336, 465.336, 488.336, 509.336, 527.336, 544.336, 562.336, 580.336],
    "bal_ob_1": (297.8, 256.336, 385.0, 264.336, 384.464, 256.836),
    "bal_cr_1": (387.0, 256.336, 434.0, 264.336, 433.912, 256.836),
    "bal_db_1": (457.8, 256.336, 493.0, 264.336, 458.640, 256.836),
    "bal_cl_1": (494.64, 259.336, 573.2, 267.336, 574.0, 256.836),
    "bal_ob_2": (297.8, 269.336, 385.0, 277.336, 384.464, 270.000),
    "bal_cr_2": (387.0, 269.336, 434.0, 277.336, 433.912, 270.000),
    "bal_db_2": (457.8, 270.336, 493.0, 278.336, 459.000, 270.000),
    "bal_cl_2": (494.64, 270.336, 574.2, 278.336, 574.0, 270.000),
    "pay_1": (499.0, 426.336, 530.14, 434.336, 530.14, 425.636),
    "pay_2": (499.0, 563.336, 530.14, 571.336, 530.14, 561.636),
    "stmt_sd": (125.0, 154.336, 165.03, 162.336, 125.0, 154.336),
    "stmt_t1": (367.0, 158.336, 407.03, 166.336, 367.0, 158.336),
    "stmt_t11": (367.0, 176.336, 407.03, 184.336, 367.0, 176.336),
    "name_left": (125.0, 83.336, 215.0, 91.336, 125.0, 83.336),
    "name_right": (367.0, 82.336, 500.0, 90.336, 367.0, 82.336),
    "cust_id": (125.0, 102.336, 180.0, 110.336, 125.0, 102.336),
    "mobile": (367.0, 140.336, 425.0, 148.336, 367.0, 140.336),
    "tag_account": (22.0, 256.336, 62.0, 264.336, 22.0, 257.336),
    "vehicle_no": (104.0, 256.336, 158.0, 264.336, 104.0, 257.336),
    "header_rect": (20.0, 329.5, 200.0, 341.0),
    "header_text": (21.0, 331.336),
}

TOLL_DEBITS = [250, 335, 340, 85, 515, 260, 410, 480, 815, 720, 720]

# ================= DATE NORMALIZATION =================
def add_current_year_if_missing(date_str):
    """Convert dd-mm to dd-mm-yyyy using current year; keep dd-mm-yyyy unchanged."""
    if not date_str:
        return date_str
    s = date_str.strip()
    m_full = re.fullmatch(r'(\d{2})-(\d{2})-(\d{4})', s)
    if m_full:
        return s
    m_short = re.fullmatch(r'(\d{2})-(\d{2})', s)
    if m_short:
        return f"{m_short.group(1)}-{m_short.group(2)}-{datetime.now().year}"
    return s

def normalize_datetime_year(dt_str):
    """Normalize datetime string to ensure date has year (dd-mm-yyyy HH:MM:SS)."""
    if not dt_str:
        return dt_str
    s = dt_str.strip()
    m = re.fullmatch(r'(\d{2})-(\d{2})(?:-(\d{4}))?\s+(\d{2}:\d{2}:\d{2})', s)
    if not m:
        return s
    day, month, year, t = m.group(1), m.group(2), m.group(3), m.group(4)
    if not year:
        year = str(datetime.now().year)
    return f"{day}-{month}-{year} {t}"

def inject_current_year_in_raw_text(raw_text):
    """Replace dd-mm with dd-mm-currentyear when year is missing in raw text."""
    current_year = str(datetime.now().year)
    return re.sub(
        r'(?<!\d)(\d{2}-\d{2})(?!-\d{4})',
        rf'\1-{current_year}',
        raw_text
    )

# ================= GEMINI PARSER =================
def parse_with_gemini(raw_text, max_retries=3, base_delay=1):
    """Use the Google GenAI SDK to extract structured data with retry logic."""
    client = genai.Client(api_key=GEMINI_API_KEY)

    prompt = f"""
Extract vehicle registration, DC number, start datetime (eway), and received datetime from the text below.
Return ONLY a valid JSON array of objects with keys: "vehicle", "dc", "eway", "received".

Rules:
- vehicle: registration like "XX00XX0000". Extract only the number.
- dc: a 2-4 digit number (standalone or after "DC-" / "DC:").
- eway: format exactly as "dd-mm-yyyy HH:MM:SS" (24-hour).
- received: format exactly as "dd-mm-yyyy HH:MM:SS" (24-hour). This is the end time, always the later date.

Time conversion (be precise):
- "1621pm" → "16:21:00"
- "01:17pm" → "13:17:00"
- "1516 hrs" → "15:16:00"
- "11:51 am" → "11:51:00"
- "11:46 pm" → "23:46:00"
- "at noon" → "12:00:00"
- "today @ 10:15 am" → use the date provided.

If seconds are missing, add ":00". For "today", use the date mentioned in the text.

Text:
{raw_text}

JSON:
"""
    for attempt in range(max_retries):
        try:
            response = client.models.generate_content(
                model="gemini-2.5-flash-lite",
                contents=prompt
            )
            content = response.text
            content = re.sub(r'```json\s*', '', content)
            content = re.sub(r'```\s*$', '', content)
            parsed = json.loads(content)
            if isinstance(parsed, list):
                for entry in parsed:
                    if isinstance(entry, dict):
                        entry["eway"] = normalize_datetime_year(entry.get("eway"))
                        entry["received"] = normalize_datetime_year(entry.get("received"))
                return parsed
            elif isinstance(parsed, dict) and "entries" in parsed:
                for entry in parsed["entries"]:
                    if isinstance(entry, dict):
                        entry["eway"] = normalize_datetime_year(entry.get("eway"))
                        entry["received"] = normalize_datetime_year(entry.get("received"))
                return parsed["entries"]
            else:
                return []
        except Exception as e:
            error_str = str(e).lower()
            if "503" in error_str or "service unavailable" in error_str or "rate limit" in error_str or "429" in error_str:
                if attempt < max_retries - 1:
                    delay = base_delay * (2 ** attempt) + random.uniform(0, 1)
                    print(f"⚠️ Gemini API error (attempt {attempt+1}/{max_retries}): {e}. Retrying in {delay:.2f}s...")
                    time.sleep(delay)
                    continue
                else:
                    print(f"⚠️ Gemini API failed after {max_retries} attempts: {e}")
                    return []
            else:
                print(f"⚠️ Gemini API error: {e}")
                return []

# ================= REGEX PARSER (FALLBACK) =================
def parse_time_string(time_str):
    time_str = time_str.strip().lower()
    time_str = re.sub(r'\s*(hrs|hr|hours)\s*$', '', time_str).strip()
    meridian = None
    match = re.search(r'\s*(am|pm)$', time_str)
    if match:
        meridian = match.group(1)
        time_str = re.sub(r'\s*(am|pm)$', '', time_str).strip()
    if ':' in time_str:
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        second = int(parts[2]) if len(parts) > 2 else 0
    else:
        if len(time_str) == 4 and time_str.isdigit():
            hour = int(time_str[:2])
            minute = int(time_str[2:])
            second = 0
        elif len(time_str) == 3 and time_str.isdigit():
            hour = int(time_str[0])
            minute = int(time_str[1:])
            second = 0
        else:
            return "00:00:00"
    if meridian:
        if 1 <= hour <= 12:
            if meridian == 'pm' and hour != 12:
                hour += 12
            elif meridian == 'am' and hour == 12:
                hour = 0
    if not (0 <= hour <= 23 and 0 <= minute <= 59):
        return "00:00:00"
    return f"{hour:02d}:{minute:02d}:{second:02d}"

def parse_with_regex(raw_text):
    entries = []
    blocks = re.split(r'\n\s*\n', raw_text.strip())
    for block in blocks:
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if not lines:
            continue
        vehicle = None
        vehicle_pattern = r'([A-Z]{2}[0-9]{2}[A-Z]{1,2}[0-9]{4})'
        for i, line in enumerate(lines):
            match = re.search(vehicle_pattern, line.upper())
            if match:
                vehicle = match.group(1)
                lines[i] = re.sub(vehicle_pattern, '', line, flags=re.IGNORECASE).strip()
                if not lines[i]:
                    del lines[i]
                break
        if not vehicle:
            continue
        dc = None
        for i, line in enumerate(lines[:]):
            if re.match(r'^\d{2,4}$', line):
                dc = line
                del lines[i]
                break
            match = re.search(r'(?:DC[:\-\s]*)?(\d{2,4})', line, re.IGNORECASE)
            if match:
                dc = match.group(1)
                lines[i] = re.sub(r'DC[:\-\s]*\d{2,4}', '', line, flags=re.IGNORECASE).strip()
                if not lines[i]:
                    del lines[i]
                break
        if not dc:
            continue
        date_str = None
        time_str = None
        received_date = None
        received_time = None
        for i, line in enumerate(lines):
            if "received" in line.lower():
                date_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)', line)
                if date_match:
                    received_date = add_current_year_if_missing(date_match.group(1))
                time_match = re.search(r'(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                if time_match:
                    received_time = time_match.group(1).strip()
                elif i+1 < len(lines) and re.search(r'^\d', lines[i+1]):
                    received_time = lines[i+1].strip()
            else:
                date_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)', line)
                if date_match:
                    date_str = add_current_year_if_missing(date_match.group(1))
                    time_match = re.search(r'(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                    if time_match:
                        time_str = time_match.group(1).strip()
                    elif i+1 < len(lines) and re.search(r'^\d', lines[i+1]):
                        time_str = lines[i+1].strip()
        if not date_str or not time_str:
            continue
        parsed_time = parse_time_string(time_str)
        parsed_received = parse_time_string(received_time) if received_time else None
        entries.append({
            "vehicle": vehicle,
            "dc": dc,
            "eway": f"{date_str} {parsed_time}",
            "received": f"{received_date} {parsed_received}" if received_date and parsed_received else None
        })
    return entries

# ================= PDF GENERATION HELPERS =================
def calculate_data(start_time_str, end_dt_str):
    """
    Generates a timeline that starts at start_time_str and ends exactly at end_dt_str.
    t1 is set to start_time + 2.5 hours + random 10-20 mins.
    Returns (timestamps dict, balances dict).
    """
    t1 = datetime.strptime(start_time_str, "%d-%m-%Y %H:%M:%S") + timedelta(hours=2.5) + timedelta(minutes=random.randint(10, 20))

    def _fallback_morning_end(base_dt):
        natural = base_dt + timedelta(minutes=sum(base_intervals))
        hh = random.randint(5, 8)
        mm = random.randint(0, 50) if hh == 8 else random.randint(0, 59)
        return natural.replace(hour=hh, minute=mm, second=0, microsecond=0)

    def _in_morning_window(dt):
        if dt.hour < 5 or dt.hour > 8:
            return False
        if dt.hour == 8 and dt.minute > 50:
            return False
        return True

    base_intervals = [40, 1713, 1465, 611, 805, 550, 166, 33, 48, 27, 264, 733]

    try:
        end_datetime = datetime.strptime(end_dt_str, "%d-%m-%Y %H:%M:%S")
    except Exception:
        end_datetime = _fallback_morning_end(t1)

    if not _in_morning_window(end_datetime):
        hh = random.randint(5, 8)
        mm = random.randint(0, 50) if hh == 8 else random.randint(0, 59)
        end_datetime = end_datetime.replace(hour=hh, minute=mm, second=0, microsecond=0)

    fixed_indices = {0, 7}
    adjustable_indices = [i for i in range(len(base_intervals)) if i not in fixed_indices]

    target_total = (end_datetime - t1).total_seconds() / 60.0
    fixed_total = sum(base_intervals[i] for i in fixed_indices)
    target_adjustable_total = int(round(target_total - fixed_total))

    base_adjustable = [base_intervals[i] for i in adjustable_indices]
    base_adjustable_total = sum(base_adjustable)
    delta = target_adjustable_total - base_adjustable_total

    weights = [pow(v, 1.12) for v in base_adjustable]
    weight_sum = sum(weights) if weights else 1.0

    float_adjusted = []
    for v, w in zip(base_adjustable, weights):
        share = delta * (w / weight_sum)
        var_span = 0.02 + 0.03 * (w / weight_sum) * len(base_adjustable)
        variation = random.uniform(1.0 - var_span, 1.0 + var_span)
        float_adjusted.append(max(1.0, v + share * variation))

    rounded = [max(1, int(round(x))) for x in float_adjusted]
    current_total = sum(rounded)
    remainder = target_adjustable_total - current_total

    if remainder != 0:
        fractions = [x - int(x) for x in float_adjusted]
        if remainder > 0:
            order = sorted(range(len(rounded)), key=lambda k: (fractions[k], weights[k]), reverse=True)
            step = 1
        else:
            order = sorted(range(len(rounded)), key=lambda k: (rounded[k] > 1, -fractions[k], -weights[k]), reverse=True)
            step = -1
        idx = 0
        guard = 0
        while remainder != 0 and guard < 100000:
            j = order[idx % len(order)]
            if step > 0 or (step < 0 and rounded[j] > 1):
                rounded[j] += step
                remainder -= step
            idx += 1
            guard += 1

    scaled_intervals = base_intervals[:]
    for pos, idx in enumerate(adjustable_indices):
        scaled_intervals[idx] = rounded[pos]

    pay2 = t1 + timedelta(minutes=scaled_intervals[0])
    t2   = pay2 + timedelta(minutes=scaled_intervals[1])
    t3   = t2 + timedelta(minutes=scaled_intervals[2])
    t4   = t3 + timedelta(minutes=scaled_intervals[3])
    t5   = t4 + timedelta(minutes=scaled_intervals[4])
    t6   = t5 + timedelta(minutes=scaled_intervals[5])
    t7   = t6 + timedelta(minutes=scaled_intervals[6])
    pay1 = t7 + timedelta(minutes=scaled_intervals[7])
    t8   = pay1 + timedelta(minutes=scaled_intervals[8])
    t9   = t8 + timedelta(minutes=scaled_intervals[9])
    t10  = t9 + timedelta(minutes=scaled_intervals[10])
    t11  = t10 + timedelta(minutes=scaled_intervals[11])

    ts = {
        't1': t1, 'pay2': pay2, 't2': t2, 't3': t3, 't4': t4,
        't5': t5, 't6': t6, 't7': t7, 'pay1': pay1, 't8': t8,
        't9': t9, 't10': t10, 't11': t11
    }

    ob = float(random.choice(range(800, 1050, 5)))
    td = sum(TOLL_DEBITS)
    while True:
        cr = float(random.choice(range(5000, 5750, 50)))
        p1_val = float(random.choice(range(1000, 1550, 50)))
        p2_val = cr - p1_val
        if 4000 <= p2_val <= 4500:
            break
    bal = {
        'ob': ob, 'cr': cr, 'td': td,
        'cl': round(ob + cr - td, 2),
        'p1': p1_val, 'p2': p2_val
    }
    return ts, bal

def scrub_and_put(page, x0, y0, x1, y1, tx, ty, text, bold=False, right=False):
    """White-out rectangle and place new text."""
    inset = 1.0
    if x1 - inset > x0 + inset and y1 - inset > y0 + inset:
        page.add_redact_annot(fitz.Rect(x0 + inset, y0 + inset, x1 - inset, y1 - inset), fill=(1, 1, 1))
        page.apply_redactions()
    font = "helvetica-bold" if bold else "helvetica"
    if right:
        w = fitz.get_text_length(text, fontname=font, fontsize=FONT_SIZE)
        page.insert_text((tx - w, ty + FONT_SIZE), text, fontsize=FONT_SIZE, fontname=font, color=TEXT_COLOR)
    else:
        page.insert_text((tx, ty + FONT_SIZE), text, fontsize=FONT_SIZE, fontname=font, color=TEXT_COLOR)

def generate_pdf_to_path(template_doc, entry, output_path):
    """Generate a PDF using the template and entry, save to output_path."""
    vehicle_no = entry["vehicle"]
    dc_number = entry["dc"]
    start_time = entry["eway"]
    end_time = entry.get("received")
    cust_name = entry.get("cust_name", DEFAULT_CUST_NAME)
    cust_id   = entry.get("cust_id", DEFAULT_CUST_ID)
    mobile    = entry.get("mobile", DEFAULT_MOBILE)
    tag_acct  = entry.get("tag_account", DEFAULT_TAG_ACCOUNT)

    doc = fitz.open()
    doc.insert_pdf(template_doc, from_page=0, to_page=0)
    page = doc[0]

    ts, bal = calculate_data(start_time, end_time)

    # Header Table Background
    hx0, hy0, hx1, hy1 = COORD["header_rect"]
    page.draw_rect(fitz.Rect(hx0, hy0, hx1, hy1), color=None, fill=(1, 129/255, 57/255))
    page.insert_text((COORD["header_text"][0], COORD["header_text"][1] + FONT_SIZE),
                     f"{vehicle_no} - {tag_acct}", fontsize=FONT_SIZE, fontname="helvetica-bold", color=(0,0,0))

    # Date/Time Rows
    dt_values = [ts['t11'], ts['t10'], ts['t9'], ts['t8'], ts['pay1'], ts['t7'], ts['t6'], ts['t5'], ts['t4'], ts['t3'], ts['t2'], ts['pay2'], ts['t1']]
    for i, dt in enumerate(dt_values):
        top = COORD["row_tops"][i]
        bot = top + 8.0
        dx0, dx1 = COORD["row_date_x_last"] if i == 12 else COORD["row_date_x_default"]
        tx0, tx1 = COORD["row_time_x_last"] if i == 12 else COORD["row_time_x_default"]
        scrub_and_put(page, dx0, top, dx1, bot, dx0, top, dt.strftime("%d-%m-%Y"))
        scrub_and_put(page, tx0, top, tx1, bot, tx0, top, dt.strftime("%H:%M:%S"))

    # Balances & Payments
    scrub_and_put(page, *COORD["bal_ob_1"], f"{bal['ob']:.2f}", right=True)
    scrub_and_put(page, *COORD["bal_cr_1"], f"{bal['cr']:.2f}", right=True)
    scrub_and_put(page, *COORD["bal_db_1"], f"- {bal['td']:.2f}")
    scrub_and_put(page, *COORD["bal_cl_1"], f"{bal['cl']:.2f}", right=True)
    scrub_and_put(page, *COORD["bal_ob_2"], f"{bal['ob']:.2f}", right=True, bold=True)
    scrub_and_put(page, *COORD["bal_cr_2"], f"{bal['cr']:.2f}", right=True, bold=True)
    scrub_and_put(page, *COORD["bal_db_2"], f"- {bal['td']:.2f}", bold=True)
    scrub_and_put(page, *COORD["bal_cl_2"], f"{bal['cl']:.2f}", right=True, bold=True)
    scrub_and_put(page, *COORD["pay_1"], f"{bal['p1']:,.2f}", right=True)
    scrub_and_put(page, *COORD["pay_2"], f"{bal['p2']:,.2f}", right=True)

    # Personal Details
    scrub_and_put(page, *COORD["stmt_sd"], (ts['t11'] + timedelta(days=1)).strftime("%d/%m/%Y"))
    scrub_and_put(page, *COORD["stmt_t1"], ts['t1'].strftime("%d/%m/%Y"))
    scrub_and_put(page, *COORD["stmt_t11"], ts['t11'].strftime("%d/%m/%Y"))
    scrub_and_put(page, *COORD["name_left"], cust_name)
    scrub_and_put(page, *COORD["name_right"], f"{cust_name}, Morena,")
    scrub_and_put(page, *COORD["cust_id"], cust_id)
    scrub_and_put(page, *COORD["mobile"], mobile)
    scrub_and_put(page, *COORD["tag_account"], tag_acct)
    scrub_and_put(page, *COORD["vehicle_no"], vehicle_no)

    now_str = datetime.now().strftime("D:%Y%m%d%H%M%S")
    doc.set_metadata({"creationDate": now_str, "modDate": now_str})
    doc.save(output_path, garbage=4, deflate=True, clean=True)
    doc.close()

# ================= TELEGRAM BOT HANDLERS =================
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "🤖 *PDF Generator Bot Ready!*\n\n"
        "Send me raw trip data (like you'd paste into your script) and I'll extract vehicle numbers, DC numbers, and dates using Gemini AI, then generate the PDF statements.\n\n"
        "Example:\n"
        "`MP09HH4340\\nDC:482\\nReceived: 13-03\\nEway: 09-03 @10:36am`\n\n"
        "I can handle multiple trips in one message.",
        parse_mode="Markdown"
    )

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_input = update.message.text
    await update.message.reply_text("📄 Processing your data with Gemini AI...")

    try:
        # Normalize years (add current year if missing)
        normalized = inject_current_year_in_raw_text(user_input)

        # Parse using Gemini (or fallback)
        if PARSER_MODE == "gemini":
            entries = parse_with_gemini(normalized)
        elif PARSER_MODE == "fallback":
            entries = parse_with_gemini(normalized)
            if not entries:
                entries = parse_with_regex(normalized)
        else:
            entries = parse_with_regex(normalized)

        if not entries:
            await update.message.reply_text("❌ Could not extract any valid trip data from your message. Please check the format.")
            return

        await update.message.reply_text(f"✅ Extracted {len(entries)} trip(s). Generating PDFs...")

        # Open template once
        template_doc = fitz.open(INPUT_PDF)
        pdf_paths = []

        # Create a temporary directory for this request
        with tempfile.TemporaryDirectory() as tmpdir:
            for entry in entries:
                output_path = os.path.join(tmpdir, f"FT-{entry['dc']}.pdf")
                generate_pdf_to_path(template_doc, entry, output_path)
                pdf_paths.append(output_path)
            template_doc.close()

            # Send PDFs back
            if len(pdf_paths) == 1:
                with open(pdf_paths[0], 'rb') as f:
                    await update.message.reply_document(
                        document=f,
                        filename=os.path.basename(pdf_paths[0]),
                        caption=f"✅ Generated for {entries[0]['vehicle']}"
                    )
            else:
                # Create zip in memory
                zip_buffer = io.BytesIO()
                with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                    for pdf_path in pdf_paths:
                        zipf.write(pdf_path, os.path.basename(pdf_path))
                zip_buffer.seek(0)
                await update.message.reply_document(
                    document=zip_buffer,
                    filename="statements.zip",
                    caption=f"✅ {len(pdf_paths)} PDFs generated"
                )
    except Exception as e:
        logger.error(f"Error: {e}", exc_info=True)
        await update.message.reply_text(f"❌ An error occurred: {str(e)}")

# ================= FLASK KEEP-ALIVE SERVER =================
# This ensures Render's free tier keeps the bot alive
flask_app = Flask('')

@flask_app.route('/')
def home():
    return "Bot is alive!"

def run_flask():
    flask_app.run(host='0.0.0.0', port=int(os.environ.get('PORT', 8080)))

def keep_alive():
    t = Thread(target=run_flask)
    t.start()

# ================= MAIN =================
if __name__ == '__main__':
    # Start the Flask server for Render
    keep_alive()

    # Build and run the Telegram bot
    application = ApplicationBuilder().token(TELEGRAM_BOT_TOKEN).build()
    application.add_handler(CommandHandler("start", start))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))

    print("🤖 Bot is polling...")
    application.run_polling()