import os
import logging
import tempfile
import zipfile
import io
import re
import random
import asyncio
from datetime import datetime, timedelta
from contextlib import asynccontextmanager

from fastapi import FastAPI, Request, Response
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    CallbackQueryHandler, filters, ContextTypes
)
import uvicorn
import fitz

# ================= CONFIGURATION =================
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
if not TELEGRAM_BOT_TOKEN:
    raise ValueError("Missing TELEGRAM_BOT_TOKEN environment variable")

# ================= USER AUTHORISATION =================
ALLOWED_USERS = {6615254738}  # Replace with your own user ID

# ================= LOGGING =================
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# ================= COMMON HELPERS =================
def add_current_year_if_missing(date_str):
    if not date_str:
        return date_str
    s = date_str.strip()
    if re.fullmatch(r'\d{2}-\d{2}-\d{4}', s):
        return s
    m = re.fullmatch(r'(\d{2})-(\d{2})', s)
    if m:
        return f"{m.group(1)}-{m.group(2)}-{datetime.now().year}"
    return s

def normalize_datetime_year(dt_str):
    if not dt_str:
        return dt_str
    s = dt_str.strip()
    m = re.fullmatch(r'(\d{2})-(\d{2})(?:-(\d{2,4}))?\s+(\d{2}:\d{2}:\d{2})', s)
    if m:
        day, month, year, t = m.group(1), m.group(2), m.group(3), m.group(4)
        if not year:
            year = str(datetime.now().year)
        else:
            year_int = int(year)
            if len(year) == 2:
                year_int = 2000 + year_int
            if year_int < 2025:
                year_int = 2026
            year = str(year_int)
        return f"{day}-{month}-{year} {t}"
    return s

def random_morning_time():
    hour = random.randint(5, 9)
    if hour == 9:
        minute = random.randint(0, 40)
    else:
        minute = random.randint(0, 59)
    return f"{hour:02d}:{minute:02d}:00"

def normalize_received(received_str):
    if not received_str:
        return None
    if re.search(r'\d{2}:\d{2}:\d{2}', received_str):
        return normalize_datetime_year(received_str)
    return normalize_datetime_year(received_str.strip() + " " + random_morning_time())

def strip_markdown_code_fences(text: str) -> str:
    text = re.sub(r'```\w*\n', '', text)
    text = re.sub(r'```', '', text)
    return text.strip()

# ================= UNIFIED TIME SCALING ENGINE =================
def scale_timeline(start_time_str, end_time_str, base_intervals, fixed_indices, random_factor=0.05):
    t_start = datetime.strptime(start_time_str, "%d-%m-%Y %H:%M:%S")
    
    def in_morning_window(dt):
        return 5 <= dt.hour <= 9 and not (dt.hour == 9 and dt.minute > 40)
    
    def natural_morning_end(base_dt):
        natural = base_dt + timedelta(minutes=sum(base_intervals))
        hh = random.randint(5, 9)
        if hh == 9:
            mm = random.randint(0, 40)
        else:
            mm = random.randint(0, 59)
        return natural.replace(hour=hh, minute=mm, second=0, microsecond=0)
    
    if end_time_str:
        try:
            target_end = datetime.strptime(end_time_str, "%d-%m-%Y %H:%M:%S")
        except:
            target_end = natural_morning_end(t_start)
    else:
        target_end = natural_morning_end(t_start)
    
    if not in_morning_window(target_end):
        hh = random.randint(5, 9)
        if hh == 9:
            mm = random.randint(0, 40)
        else:
            mm = random.randint(0, 59)
        target_end = target_end.replace(hour=hh, minute=mm, second=0, microsecond=0)
    
    total_target = (target_end - t_start).total_seconds() / 60.0
    fixed_total = sum(base_intervals[i] for i in fixed_indices)
    target_adjustable = int(round(total_target - fixed_total))
    adjustable_indices = [i for i in range(len(base_intervals)) if i not in fixed_indices]
    base_adjustable = [base_intervals[i] for i in adjustable_indices]
    base_adjustable_total = sum(base_adjustable)
    delta = target_adjustable - base_adjustable_total
    weights = [pow(v, 1.12) for v in base_adjustable]
    weight_sum = sum(weights) if weights else 1.0
    float_adjusted = []
    for v, w in zip(base_adjustable, weights):
        share = delta * (w / weight_sum)
        var_span = random_factor * (1 + (w / weight_sum) * len(base_adjustable))
        variation = random.uniform(1.0 - var_span, 1.0 + var_span)
        float_adjusted.append(max(1.0, v + share * variation))
    rounded = [max(1, int(round(x))) for x in float_adjusted]
    current_total = sum(rounded)
    remainder = target_adjustable - current_total
    if remainder != 0:
        fractions = [x - int(x) for x in float_adjusted]
        if remainder > 0:
            order = sorted(range(len(rounded)), key=lambda k: (fractions[k], weights[k]), reverse=True)
            step = 1
        else:
            order = sorted(range(len(rounded)), key=lambda k: (rounded[k] > 1, -fractions[k], -weights[k]), reverse=True)
            step = -1
        idx = 0
        while remainder != 0:
            j = order[idx % len(order)]
            if step > 0 or (step < 0 and rounded[j] > 1):
                rounded[j] += step
                remainder -= step
            idx += 1
    scaled = base_intervals[:]
    for pos, idx in enumerate(adjustable_indices):
        scaled[idx] = rounded[pos]
    return scaled, target_end

def random_morning_datetime(base_dt):
    hour = random.randint(5, 9)
    if hour == 9:
        minute = random.randint(0, 40)
    else:
        minute = random.randint(0, 59)
    return base_dt.replace(hour=hour, minute=minute, second=0, microsecond=0)

# ================= IMPROVED TIME PARSER =================
def parse_time_string(time_str):
    """Parse time string in 12h or 24h format. Returns HH:MM:SS."""
    if not time_str:
        return "00:00:00"
    time_str = time_str.strip().lower()
    # Remove suffixes like "hrs"
    time_str = re.sub(r'\s*(hrs|hr|hours)\s*$', '', time_str).strip()
    meridian = None
    match = re.search(r'\s*(am|pm)$', time_str)
    if match:
        meridian = match.group(1)
        time_str = re.sub(r'\s*(am|pm)$', '', time_str).strip()
    
    # Parse hour, minute, second
    if ':' in time_str:
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        second = int(parts[2]) if len(parts) > 2 else 0
    else:
        # Compact format like 1621 (16:21) or 521 (5:21) – only if followed by am/pm? Actually we already stripped am/pm, so handle digits only
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
    
    # Apply meridian (only if present)
    if meridian:
        if meridian == 'pm' and hour != 12:
            hour += 12
        elif meridian == 'am' and hour == 12:
            hour = 0
    
    # Clamp to valid ranges
    hour = max(0, min(23, hour))
    minute = max(0, min(59, minute))
    second = max(0, min(59, second))
    
    return f"{hour:02d}:{minute:02d}:{second:02d}"

# ================= REGEX PARSERS =================
def parse_baroda_data(raw_text):
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
        
        eway_date = None
        eway_time = None
        received_date = None
        received_time = None
        cust_name = None
        cust_id = None
        mobile = None
        tag_account = None
        
        # Improved time regex: requires colon OR explicit am/pm/hrs for digit-only times
        time_regex = r'(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs))'
        
        for i, line in enumerate(lines):
            lower = line.lower()
            if "eway" in lower:
                date_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)', line)
                if date_match:
                    eway_date = add_current_year_if_missing(date_match.group(1))
                time_match = re.search(time_regex, line, re.IGNORECASE)
                if time_match:
                    eway_time = time_match.group(1).strip()
                    logger.info(f"DEBUG BARODA: eway_time extracted = '{eway_time}'")
                elif i+1 < len(lines) and re.search(r'^\d', lines[i+1]):
                    eway_time = lines[i+1].strip()
                    logger.info(f"DEBUG BARODA: eway_time from next line = '{eway_time}'")
            elif "received" in lower:
                date_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)', line)
                if date_match:
                    received_date = add_current_year_if_missing(date_match.group(1))
                time_match = re.search(time_regex, line, re.IGNORECASE)
                if time_match:
                    received_time = time_match.group(1).strip()
                elif i+1 < len(lines) and re.search(r'^\d', lines[i+1]):
                    received_time = lines[i+1].strip()
            elif "name" in lower:
                name_match = re.search(r'name[:\s]+(.*?)(?:\s*(?:id|mobile|tag|$))', line, re.IGNORECASE)
                if name_match:
                    cust_name = name_match.group(1).strip()
            elif "id" in lower and "cust" not in lower:
                id_match = re.search(r'id[:\s]+(\d+)', line, re.IGNORECASE)
                if id_match:
                    cust_id = id_match.group(1)
            elif "mobile" in lower or "phone" in lower:
                mob_match = re.search(r'(?:mobile|phone)[:\s]+(\d{10})', line, re.IGNORECASE)
                if mob_match:
                    mobile = mob_match.group(1)
            elif "tag" in lower:
                tag_match = re.search(r'tag[:\s]+(\d+)', line, re.IGNORECASE)
                if tag_match:
                    tag_account = tag_match.group(1)
        
        if not eway_date or not eway_time:
            continue
        
        parsed_eway_time = parse_time_string(eway_time)
        entry = {
            "vehicle": vehicle,
            "dc": dc,
            "eway": f"{eway_date} {parsed_eway_time}",
        }
        if received_date and received_time:
            parsed_received_time = parse_time_string(received_time)
            entry["received"] = f"{received_date} {parsed_received_time}"
        if cust_name:
            entry["cust_name"] = cust_name
        if cust_id:
            entry["cust_id"] = cust_id
        if mobile:
            entry["mobile"] = mobile
        if tag_account:
            entry["tag_account"] = tag_account
        entries.append(entry)
    return entries

def parse_idfc_data(raw_text):
    entries = []
    blocks = re.split(r'\n\s*\n', raw_text.strip())
    for block in blocks:
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if not lines:
            continue
        
        # Extract DC - mandatory
        dc = None
        for line in lines:
            match = re.search(r'\bDC\s*[:]?\s*(\d{2,4})\b', line, re.IGNORECASE)
            if match:
                dc = match.group(1)
                break
        if not dc:
            continue
        
        start_time = None
        received_time = None
        customer_name = None
        mobile = None
        truck_number = None
        truck_owner = None
        recharge_amount = None
        opening_balance = None
        toll_debits = None
        
        for line in lines:
            lower = line.lower()
            if "start" in lower:
                dt_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)\s+(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                if dt_match:
                    date_part = add_current_year_if_missing(dt_match.group(1))
                    time_part = parse_time_string(dt_match.group(2))
                    start_time = f"{date_part} {time_part}"
            elif "received" in lower:
                dt_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)\s+(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                if dt_match:
                    date_part = add_current_year_if_missing(dt_match.group(1))
                    time_part = parse_time_string(dt_match.group(2))
                    received_time = f"{date_part} {time_part}"
            elif "name" in lower:
                name_match = re.search(r'name[:\s]+(.*?)(?:\s*(?:mobile|truck|owner|recharge|opening|$))', line, re.IGNORECASE)
                if name_match:
                    customer_name = name_match.group(1).strip()
            elif "mobile" in lower or "phone" in lower:
                mob_match = re.search(r'(?:mobile|phone)[:\s]+(\d{10})', line, re.IGNORECASE)
                if mob_match:
                    mobile = mob_match.group(1)
            elif "truck" in lower and "number" in lower or "truck" in lower and not "owner" in lower:
                truck_match = re.search(r'truck[:\s]+([A-Z0-9]+)', line, re.IGNORECASE)
                if truck_match:
                    truck_number = truck_match.group(1)
            elif "owner" in lower:
                owner_match = re.search(r'owner[:\s]+(.*?)(?:\s*(?:recharge|opening|$))', line, re.IGNORECASE)
                if owner_match:
                    truck_owner = owner_match.group(1).strip()
            elif "recharge" in lower:
                amt_match = re.search(r'recharge[:\s]+(\d+)', line, re.IGNORECASE)
                if amt_match:
                    recharge_amount = int(amt_match.group(1))
            elif "opening balance" in lower or "opening" in lower:
                bal_match = re.search(r'(?:opening balance|ob)[:\s]+(\d+)', line, re.IGNORECASE)
                if bal_match:
                    opening_balance = int(bal_match.group(1))
            elif "toll debits" in lower:
                arr_match = re.search(r'\[(.*?)\]', line)
                if arr_match:
                    numbers = re.findall(r'\d+', arr_match.group(1))
                    toll_debits = [int(n) for n in numbers]
        
        if not start_time:
            continue
        
        entry = {
            "start_time": start_time,
            "dc": dc,
        }
        if received_time:
            entry["received_time"] = received_time
        if customer_name:
            entry["customer_name"] = customer_name
        if mobile:
            entry["mobile"] = mobile
        if truck_number:
            entry["truck_number"] = truck_number
        if truck_owner:
            entry["truck_owner"] = truck_owner
        if recharge_amount is not None:
            entry["recharge_amount"] = recharge_amount
        if opening_balance is not None:
            entry["opening_balance"] = opening_balance
        if toll_debits:
            entry["toll_debits"] = toll_debits
        entries.append(entry)
    return entries

# ================= PDF GENERATION FOR BARODA_BANK =================
DEFAULT_CUST_NAME   = "VIPUL MITTAL"
DEFAULT_CUST_ID     = "11593956"
DEFAULT_MOBILE      = "9826260443"
DEFAULT_TAG_ACCOUNT = "21434130"
TEXT_COLOR = (0,0,0)
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
TOLL_DEBITS_BARODA = [250, 335, 340, 85, 515, 260, 410, 480, 815, 720, 720]

# ---------- NEW: Transaction ID randomisation (BARODA only) ----------
def generate_random_transaction_id(original: str) -> str:
    """
    Replace every contiguous block of digits in the original string
    with a random digit block of exactly the same length.
    All non-digit characters (letters, slash, space) stay unchanged.
    """
    def repl(match):
        digits = match.group(0)
        return ''.join(str(random.randint(0, 9)) for _ in digits)
    out = re.sub(r'\d+', repl, original)
    # Hard guarantee: output must keep exact character count.
    return out if len(out) == len(original) else original

def process_transaction_ids(page):
    """
    Redact and replace only the transaction-id column text.
    Keeps letters/symbols unchanged and randomizes digits with same length.
    Coordinates are specific to the BARODA template.
    """
    # Tight bounds of the transaction column from template PDF.
    x0_min, x1_max = 193.5, 303.0
    y0_min, y1_max = 345.5, 595.5

    # Only words in this column that contain at least one digit are replaced.
    replacements = []
    for w in page.get_text("words"):
        x0, y0, x1, y1, text = w[0], w[1], w[2], w[3], w[4]
        if not (x0_min <= x0 and x1 <= x1_max and y0_min <= y0 and y1 <= y1_max):
            continue
        if not re.search(r"\d", text):
            continue

        new_text = generate_random_transaction_id(text)
        if new_text == text:
            continue

        # Small inset keeps nearby orange borders and separators intact.
        pad_x = 0.2
        inset_y = 1.0
        rx0 = x0 - pad_x
        ry0 = y0 + inset_y
        rx1 = x1 + pad_x
        ry1 = y1 - inset_y
        if rx1 <= rx0 or ry1 <= ry0:
            continue
        page.add_redact_annot(fitz.Rect(rx0, ry0, rx1, ry1), fill=(1, 1, 1))
        replacements.append((x0, y0, new_text))

    if replacements:
        page.apply_redactions()
        for x0, y0, new_text in replacements:
            page.insert_text((x0, y0 + FONT_SIZE), new_text, fontsize=FONT_SIZE, fontname="helvetica", color=TEXT_COLOR)

# ---------- End of new transaction ID functions ----------

def calculate_data_baroda(start_time_str, end_dt_str):
    logger.info(f"DEBUG BARODA: start_time_str = {start_time_str}")
    t1 = datetime.strptime(start_time_str, "%d-%m-%Y %H:%M:%S") + timedelta(hours=2.5) + timedelta(minutes=random.randint(10, 20))
    logger.info(f"DEBUG BARODA: t1 = {t1}")

    if end_dt_str:
        # Base intervals: now all intervals are adjustable (pay1 and pay2 are no longer fixed)
        base_intervals = [40, 1440, 900, 150, 120, 240, 150, 25, 60, 15, 240, 720]
        fixed_indices = set()   # <-- No fixed intervals, everything scales
        scaled, target_end = scale_timeline(start_time_str, end_dt_str, base_intervals, fixed_indices)
        logger.info(f"DEBUG BARODA: target_end = {target_end}")

        pay2 = t1 + timedelta(minutes=scaled[0])
        t2   = pay2 + timedelta(minutes=scaled[1])
        t3   = t2 + timedelta(minutes=scaled[2])
        t4   = t3 + timedelta(minutes=scaled[3])
        t5   = t4 + timedelta(minutes=scaled[4])
        t6   = t5 + timedelta(minutes=scaled[5])
        t7   = t6 + timedelta(minutes=scaled[6])
        pay1 = t7 + timedelta(minutes=scaled[7])
        t8   = pay1 + timedelta(minutes=scaled[8])
        t9   = t8 + timedelta(minutes=scaled[9])
        t10  = t9 + timedelta(minutes=scaled[10])
        t11  = t10 + timedelta(minutes=scaled[11])

        # Exact correction to hit target_end
        diff = (target_end - t11).total_seconds() / 60.0
        if abs(diff) > 0.1:
            scaled[11] += int(round(diff))
            t11 = t10 + timedelta(minutes=scaled[11])

        # Optional safety clamp (should rarely trigger)
        if t11.hour > 9 or (t11.hour == 9 and t11.minute > 40) or t11.hour < 5:
            t11 = random_morning_datetime(t11)
    else:
        # No scaling branch (unchanged)
        pay2 = t1 + timedelta(minutes=40 + random.randint(10, 20))
        t2   = pay2 + timedelta(minutes=24*60 + random.randint(15, 30))
        t3   = t2   + timedelta(minutes=15*60 + random.randint(15, 30))
        t4   = t3   + timedelta(minutes=2*60 + 30 + random.randint(15, 30))
        t5   = t4   + timedelta(minutes=2*60 + random.randint(15, 30))
        t6   = t5   + timedelta(minutes=4*60 + random.randint(15, 30))
        t7   = t6   + timedelta(minutes=2*60 + 30 + random.randint(15, 30))
        pay1 = t7   + timedelta(minutes=25 + random.randint(5, 15))
        t8   = pay1 + timedelta(minutes=60 + random.randint(15, 30))
        t9   = t8   + timedelta(minutes=15 + random.randint(5, 10))
        t10  = t9   + timedelta(minutes=4*60 + random.randint(15, 30))
        t11  = t10  + timedelta(minutes=12*60 + random.randint(15, 30))

    ts = {'t1': t1, 'pay2': pay2, 't2': t2, 't3': t3, 't4': t4,
          't5': t5, 't6': t6, 't7': t7, 'pay1': pay1, 't8': t8,
          't9': t9, 't10': t10, 't11': t11}
    # Balances
    ob = float(random.choice(range(800, 1050, 5)))
    td = sum(TOLL_DEBITS_BARODA)
    while True:
        cr = float(random.choice(range(5000, 5750, 50)))
        p1_val = float(random.choice(range(1000, 1550, 50)))
        p2_val = cr - p1_val
        if 4000 <= p2_val <= 4500:
            break
    bal = {'ob': ob, 'cr': cr, 'td': td,
           'cl': round(ob + cr - td, 2),
           'p1': p1_val, 'p2': p2_val}
    return ts, bal

def scrub_and_put(page, x0, y0, x1, y1, tx, ty, text, bold=False, right=False):
    inset = 1.0
    if x1 - inset > x0 + inset and y1 - inset > y0 + inset:
        page.add_redact_annot(fitz.Rect(x0 + inset, y0 + inset, x1 - inset, y1 - inset), fill=(1,1,1))
        page.apply_redactions()
    font = "helvetica-bold" if bold else "helvetica"
    if right:
        w = fitz.get_text_length(text, fontname=font, fontsize=FONT_SIZE)
        page.insert_text((tx - w, ty + FONT_SIZE), text, fontsize=FONT_SIZE, fontname=font, color=TEXT_COLOR)
    else:
        page.insert_text((tx, ty + FONT_SIZE), text, fontsize=FONT_SIZE, fontname=font, color=TEXT_COLOR)

def generate_baroda_pdf_to_path(template_doc, entry, output_path):
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

    # NEW: Process transaction IDs first (before any other redactions)
    process_transaction_ids(page)

    ts, bal = calculate_data_baroda(start_time, end_time)
    hx0, hy0, hx1, hy1 = COORD["header_rect"]
    page.draw_rect(fitz.Rect(hx0, hy0, hx1, hy1), color=None, fill=(1, 129/255, 57/255))
    page.insert_text((COORD["header_text"][0], COORD["header_text"][1] + FONT_SIZE),
                     f"{vehicle_no} - {tag_acct}", fontsize=FONT_SIZE, fontname="helvetica-bold", color=(0,0,0))
    dt_values = [ts['t11'], ts['t10'], ts['t9'], ts['t8'], ts['pay1'], ts['t7'], ts['t6'], ts['t5'], ts['t4'], ts['t3'], ts['t2'], ts['pay2'], ts['t1']]
    for i, dt in enumerate(dt_values):
        top = COORD["row_tops"][i]
        bot = top + 8.0
        dx0, dx1 = COORD["row_date_x_last"] if i == 12 else COORD["row_date_x_default"]
        tx0, tx1 = COORD["row_time_x_last"] if i == 12 else COORD["row_time_x_default"]
        scrub_and_put(page, dx0, top, dx1, bot, dx0, top, dt.strftime("%d-%m-%Y"))
        scrub_and_put(page, tx0, top, tx1, bot, tx0, top, dt.strftime("%H:%M:%S"))
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
    scrub_and_put(page, *COORD["stmt_sd"], (ts['t11'] + timedelta(days=1)).strftime("%d/%m/%Y"))
    scrub_and_put(page, *COORD["stmt_t1"], ts['t1'].strftime("%d/%m/%Y"))
    scrub_and_put(page, *COORD["stmt_t11"], ts['t11'].strftime("%d/%m/%Y"))
    scrub_and_put(page, *COORD["name_left"], cust_name)
    scrub_and_put(page, *COORD["name_right"], f"{cust_name}, Morena,")
    scrub_and_put(page, *COORD["cust_id"], cust_id)
    scrub_and_put(page, *COORD["mobile"], mobile)
    scrub_and_put(page, *COORD["tag_account"], tag_acct)
    scrub_and_put(page, *COORD["vehicle_no"], vehicle_no)
    doc.save(output_path, garbage=4, deflate=True, clean=True)
    doc.close()

# ================= PDF GENERATION FOR IDFC_BANK =================
DEFAULT_CUSTOMER_NAME = "KULDEEP KUMAR YADAV"
DEFAULT_MOBILE_IDFC   = "8743893682"
DEFAULT_TRUCK_NUMBER  = "UP67AT1939"
DEFAULT_TRUCK_OWNER   = "KULDEEP YADAV SINGH"
DEFAULT_RECHARGE_AMOUNT = 6400
DEFAULT_OPENING_BALANCE = 800
DEFAULT_TOLL_DEBITS = [720, 815, 480, 410, 260, 515, 85, 340, 335, 250]

DATE_COLOR = (0.15, 0.15, 0.15)
TIME_COLOR = (0.48, 0.48, 0.48)
ROW_BG_ODD  = (1.0, 1.0, 1.0)
ROW_BG_EVEN = (0.953, 0.953, 0.953)
COL_PROC  = (36.8, 94.4)
COL_TXN   = (96.4, 154.0)
COL_CB    = (252.4, 305.4)
COL_AMT   = (197.4, 250.4)
CX_PROC = 65.8
CX_TXN  = 125.5
CX_AMT  = 224.1
CX_CB   = 279.1

def fmt_date(dt): return dt.strftime("%d %b %y")
def fmt_time(dt): return dt.strftime("%I:%M %p")
def fmt_bal(v):   return f"{int(v):,}"

def clear_idfc(page, x1, y1, x2, y2, fill):
    page.add_redact_annot(fitz.Rect(x1, y1, x2, y2), fill=fill)
    page.apply_redactions()

def put_centered_idfc(page, cx, y, text, size=8.8, color=(0.15,0.15,0.15), bold=False):
    font = "Helvetica-Bold" if bold else "Helvetica"
    w = fitz.get_text_length(str(text), fontname=font, fontsize=size)
    page.insert_text((cx - w/2, y), str(text), fontsize=size, color=color, fontname=font)

def put_text_idfc(page, x, y, text, size=8.8, color=(0.15,0.15,0.15), bold=False):
    font = "Helvetica-Bold" if bold else "Helvetica"
    page.insert_text((x, y), str(text), fontsize=size, color=color, fontname=font)

def calculate_timeline_idfc(start_time_str, end_time_str=None):
    logger.info(f"DEBUG IDFC: start_time_str = {start_time_str}")
    try:
        base_start = datetime.strptime(start_time_str, "%d-%m-%Y %H:%M:%S")
    except Exception as e:
        logger.error(f"ERROR: Failed to parse start_time '{start_time_str}': {e}")
        date_match = re.search(r'(\d{2}-\d{2}-\d{4})', start_time_str)
        if date_match:
            base_start = datetime.strptime(date_match.group(1) + " 00:00:00", "%d-%m-%Y %H:%M:%S")
        else:
            raise ValueError(f"Could not parse start_time: {start_time_str}")
    logger.info(f"DEBUG IDFC: base_start = {base_start}")
    offset = timedelta(hours=2, minutes=30) + timedelta(minutes=random.randint(10, 20))
    T1 = base_start + offset
    logger.info(f"DEBUG IDFC: T1 = {T1}")
    if end_time_str:
        base_intervals = [40, 1, 1440, 900, 150, 120, 240, 150, 60, 15, 960]
        fixed_indices = {0, 1}   # Note: IDFC remains unchanged, still has fixed intervals
        t1_str = T1.strftime("%d-%m-%Y %H:%M:%S")
        scaled, target_end = scale_timeline(t1_str, end_time_str, base_intervals, fixed_indices)
        Recharge = T1 + timedelta(minutes=scaled[0])
        Fee = Recharge + timedelta(minutes=scaled[1])
        T2 = Fee + timedelta(minutes=scaled[2])
        T3 = T2 + timedelta(minutes=scaled[3])
        T4 = T3 + timedelta(minutes=scaled[4])
        T5 = T4 + timedelta(minutes=scaled[5])
        T6 = T5 + timedelta(minutes=scaled[6])
        T7 = T6 + timedelta(minutes=scaled[7])
        T8 = T7 + timedelta(minutes=scaled[8])
        T9 = T8 + timedelta(minutes=scaled[9])
        T10 = T9 + timedelta(minutes=scaled[10])
        if T10.hour > 9 or (T10.hour == 9 and T10.minute > 40) or T10.hour < 5:
            T10 = random_morning_datetime(T10)
    else:
        Recharge = T1 + timedelta(minutes=40 + random.randint(10, 20))
        Fee = Recharge + timedelta(minutes=1)
        T2 = Fee + timedelta(minutes=24*60 + random.randint(10, 20))
        T3 = T2 + timedelta(minutes=15*60 + random.randint(10, 20))
        T4 = T3 + timedelta(minutes=2*60 + 30 + random.randint(10, 20))
        T5 = T4 + timedelta(minutes=2*60 + random.randint(10, 20))
        T6 = T5 + timedelta(minutes=4*60 + random.randint(10, 20))
        T7 = T6 + timedelta(minutes=2*60 + 30 + random.randint(10, 20))
        T8 = T7 + timedelta(minutes=1*60 + random.randint(10, 20))
        T9 = T8 + timedelta(minutes=15 + random.randint(10, 20))
        T10 = T9 + timedelta(minutes=16*60 + random.randint(10, 20))
    return {
        "T1": T1, "Recharge": Recharge, "Fee": Fee,
        "T2": T2, "T3": T3, "T4": T4, "T5": T5, "T6": T6,
        "T7": T7, "T8": T8, "T9": T9, "T10": T10
    }

def draw_idfc_row(page, i, k, y, times, txn_times, balances, recharge_amount):
    row_bg = ROW_BG_ODD if (i % 2 == 0) else ROW_BG_EVEN
    clear_idfc(page, COL_PROC[0], y+1, COL_PROC[1], y+27, fill=row_bg)
    clear_idfc(page, COL_TXN[0],  y+1, COL_TXN[1],  y+27, fill=row_bg)
    clear_idfc(page, COL_CB[0],   y+1, COL_CB[1],   y+27, fill=row_bg)
    put_centered_idfc(page, CX_PROC, y+9.8,  fmt_date(times[k]), 9.0, DATE_COLOR)
    put_centered_idfc(page, CX_PROC, y+23.3, fmt_time(times[k]), 9.0, TIME_COLOR)
    put_centered_idfc(page, CX_TXN,  y+9.8,  fmt_date(txn_times[k]), 9.0, DATE_COLOR)
    put_centered_idfc(page, CX_TXN,  y+23.3, fmt_time(txn_times[k]), 9.0, TIME_COLOR)
    if k == "Recharge":
        clear_idfc(page, COL_AMT[0], y+1, COL_AMT[1], y+27, fill=row_bg)
        put_centered_idfc(page, CX_AMT, y+14.255, fmt_bal(recharge_amount), 8.8)
    put_centered_idfc(page, CX_CB, y+14.255, fmt_bal(balances[i]), 8.8)

def generate_idfc_pdf_to_path(template_doc, entry, output_path):
    start_time = entry["start_time"]
    end_time = entry.get("received_time")
    times = calculate_timeline_idfc(start_time, end_time)
    txn_times = {k: v + timedelta(minutes=random.randint(1, 4)) for k, v in times.items()}
    txn_times["Fee"] = times["Fee"]
    cust_name = entry.get("customer_name", DEFAULT_CUSTOMER_NAME)
    mobile    = entry.get("mobile", DEFAULT_MOBILE_IDFC)
    truck_no  = entry.get("truck_number", DEFAULT_TRUCK_NUMBER)
    owner     = entry.get("truck_owner", DEFAULT_TRUCK_OWNER)
    recharge  = entry.get("recharge_amount", DEFAULT_RECHARGE_AMOUNT)
    opening   = entry.get("opening_balance", DEFAULT_OPENING_BALANCE)
    tolls     = entry.get("toll_debits", DEFAULT_TOLL_DEBITS)
    bal = opening
    balances = []
    idx = 0
    for i in range(12):
        if i == 1:
            bal += recharge
        elif i == 2:
            bal -= 29
        else:
            bal -= tolls[idx]
            idx += 1
        balances.append(bal)
    doc = fitz.open()
    doc.insert_pdf(template_doc, from_page=0, to_page=template_doc.page_count-1)
    page = doc[0]
    clear_idfc(page, 145, 88, 350, 180, fill=(1,1,1))
    put_text_idfc(page, 147, 100.935, cust_name, 10.6, TEXT_COLOR, bold=True)
    put_text_idfc(page, 147, 124.935, mobile, 10.6, TEXT_COLOR, bold=True)
    put_text_idfc(page, 147, 148.935, truck_no, 10.6, TEXT_COLOR, bold=True)
    put_text_idfc(page, 147, 172.935, owner, 10.6, TEXT_COLOR, bold=True)
    clear_idfc(page, 145, 184, 350, 205, fill=(1,1,1))
    put_text_idfc(page, 147, 196.935,
                  f"{times['T1'].strftime('%d %B %y')} - {times['T10'].strftime('%d %B %y')}",
                  10.6, TEXT_COLOR, bold=True)
    clear_idfc(page, 150, 260, 190, 280, fill=(1,1,1))
    put_text_idfc(page, 152.8, 276, fmt_bal(recharge), 10.6)
    keys = ["T1","Recharge","Fee","T2","T3","T4","T5","T6","T7","T8","T9"]
    for i, k in enumerate(keys):
        draw_idfc_row(page, i, k, 344.3 + i*40.0, times, txn_times, balances, recharge)
    if doc.page_count > 1:
        p2 = doc[1]
        y = 44.8
        clear_idfc(p2, COL_PROC[0], y+1, COL_PROC[1], y+27, fill=ROW_BG_EVEN)
        clear_idfc(p2, COL_TXN[0], y+1, COL_TXN[1], y+27, fill=ROW_BG_EVEN)
        clear_idfc(p2, COL_CB[0],  y+1, COL_CB[1],  y+27, fill=ROW_BG_EVEN)
        put_centered_idfc(p2, CX_PROC, y+9.8,  fmt_date(times["T10"]), 9.0, DATE_COLOR)
        put_centered_idfc(p2, CX_PROC, y+23.3, fmt_time(times["T10"]), 9.0, TIME_COLOR)
        put_centered_idfc(p2, CX_TXN,  y+9.8,  fmt_date(txn_times["T10"]), 9.0, DATE_COLOR)
        put_centered_idfc(p2, CX_TXN,  y+23.3, fmt_time(txn_times["T10"]), 9.0, TIME_COLOR)
        put_centered_idfc(p2, CX_CB,   y+14.255, fmt_bal(balances[11]), 8.8)
    doc.save(output_path, garbage=4, deflate=True, clean=True)
    doc.close()

# ================= TELEGRAM BOT HANDLERS =================
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id not in ALLOWED_USERS:
        await update.message.reply_text("⛔ You are not authorised to use this bot.")
        return
    keyboard = [
        [InlineKeyboardButton("🏦 BARODA_BANK", callback_data="baroda")],
        [InlineKeyboardButton("🚛 IDFC_BANK", callback_data="idfc")]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)
    await update.message.reply_text(
        "Welcome! Please choose your bank template:👇",
        reply_markup=reply_markup
    )

async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id not in ALLOWED_USERS:
        await update.callback_query.answer("⛔ Unauthorised", show_alert=True)
        return
    query = update.callback_query
    await query.answer()
    choice = query.data
    if choice == "baroda":
        context.user_data["template"] = "baroda"
        await query.edit_message_text(
            "✅ *BARODA_BANK* template selected.\n\n"
            "📋 *Example input (copy and edit):*\n"
            "```\n"
            "Vehicle: MP09HH4381\n"
            "DC: 482\n"
            "Eway: 09-03-2026 10:36:00\n"
            "Received: 13-03-2026 06:00:00\n"
            "Name: VIPUL MITTAL\n"
            "ID: 11593956\n"
            "Mobile: 9826260443\n"
            "Tag: 21434130\n"
            "```\n\n"
            "🚛🚛You can send multiple trips separated by blank lines.\n",
            parse_mode="Markdown"
        )
    elif choice == "idfc":
        context.user_data["template"] = "idfc"
        await query.edit_message_text(
            "✅ *IDFC_BANK* template selected.\n\n"
            "📋 *Example input (copy and edit):*\n"
            "```\n"
            "Start: 09-03-2026 10:36:00\n"
            "Received: 13-03-2026 06:00:00\n"
            "DC: 482\n"
            "Name: KULDEEP KUMAR YADAV\n"
            "Mobile: 8743893682\n"
            "Truck: UP67AT1939\n"
            "Owner: KULDEEP YADAV SINGH\n"
            "Recharge: 6400\n"
            "Opening balance: 800\n"
            "```\n\n"
            "🚛🚛You can send multiple trips separated by blank lines.\n",
            parse_mode="Markdown"
        )

async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if user_id not in ALLOWED_USERS:
        await update.message.reply_text("⛔ You are not authorised to use this bot.")
        return

    user_input = update.message.text
    user_input = strip_markdown_code_fences(user_input)

    template = context.user_data.get("template")
    if not template:
        await update.message.reply_text("Please choose a template first using /start")
        return

    ack_msg = await update.message.reply_text("⏳ Processing your request. This may take a moment...")

    async def generate_and_send():
        try:
            if template == "baroda":
                entries = parse_baroda_data(user_input)
                if not entries:
                    await ack_msg.edit_text("❌ Could not extract any baroda trip data. Please follow the example format.")
                    return
                vehicle_pattern = re.compile(r'^[A-Z]{2}[0-9]{2}[A-Z]{1,2}[0-9]{4}$')
                for entry in entries:
                    vehicle = entry.get("vehicle", "")
                    if not vehicle_pattern.match(vehicle):
                        await ack_msg.edit_text(f"❌ Invalid vehicle: '{vehicle}'. Use full registration like MP09HH4381.")
                        return
                    if not entry.get("dc"):
                        await ack_msg.edit_text("❌ Missing DC number in one of the trips. Please provide 'DC: ...'")
                        return
                await ack_msg.edit_text(f"✅ Extracted {len(entries)} trip(s). Generating PDFs...⚡⚡⚡")
                try:
                    template_doc = fitz.open("baroda_template.pdf")
                except Exception as e:
                    await ack_msg.edit_text(f"❌ Cannot open baroda_template.pdf: {e}")
                    return
                pdf_paths = []
                with tempfile.TemporaryDirectory() as tmpdir:
                    for entry in entries:
                        out_path = os.path.join(tmpdir, f"FT-{entry['dc']}.pdf")
                        try:
                            generate_baroda_pdf_to_path(template_doc, entry, out_path)
                            if not os.path.exists(out_path):
                                raise Exception(f"File not created at {out_path}")
                            pdf_paths.append(out_path)
                        except Exception as e:
                            await ack_msg.edit_text(f"❌ Failed to generate PDF for DC {entry['dc']}: {e}")
                            template_doc.close()
                            return
                    template_doc.close()
                    if len(pdf_paths) == 1:
                        with open(pdf_paths[0], 'rb') as f:
                            await update.message.reply_document(
                                document=f,
                                filename=os.path.basename(pdf_paths[0]),
                                caption="✅ Successfully generated PDF!"
                            )
                    else:
                        zip_buffer = io.BytesIO()
                        with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                            for p in pdf_paths:
                                zipf.write(p, os.path.basename(p))
                        zip_buffer.seek(0)
                        await update.message.reply_document(
                            document=zip_buffer,
                            filename="statements.zip",
                            caption="✅ Successfully generated PDFs!"
                        )
                await ack_msg.delete()
            else:  # idfc
                entries = parse_idfc_data(user_input)
                if not entries:
                    await ack_msg.edit_text("❌ Could not extract any IDFC trip data. Please follow the example format.")
                    return
                for entry in entries:
                    if not entry.get("start_time"):
                        await ack_msg.edit_text("❌ One of the trips missing start time. Please provide 'Start: ...'")
                        return
                    if not entry.get("dc"):
                        await ack_msg.edit_text("❌ One of the trips missing DC number. Please provide 'DC: ...'")
                        return
                await ack_msg.edit_text(f"✅ Extracted {len(entries)} trip(s). Generating PDFs...⚡⚡⚡")
                try:
                    template_doc = fitz.open("idfc_template.pdf")
                except Exception as e:
                    await ack_msg.edit_text(f"❌ Cannot open idfc_template.pdf: {e}")
                    return
                pdf_paths = []
                with tempfile.TemporaryDirectory() as tmpdir:
                    for entry in entries:
                        out_path = os.path.join(tmpdir, f"FT-{entry['dc']}.pdf")
                        try:
                            generate_idfc_pdf_to_path(template_doc, entry, out_path)
                            if not os.path.exists(out_path):
                                raise Exception(f"File not created at {out_path}")
                            pdf_paths.append(out_path)
                        except Exception as e:
                            await ack_msg.edit_text(f"❌ Failed to generate PDF for DC {entry['dc']}: {e}")
                            template_doc.close()
                            return
                    template_doc.close()
                    if len(pdf_paths) == 1:
                        with open(pdf_paths[0], 'rb') as f:
                            await update.message.reply_document(
                                document=f,
                                filename=os.path.basename(pdf_paths[0]),
                                caption="✅ Successfully generated PDF!"
                            )
                    else:
                        zip_buffer = io.BytesIO()
                        with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                            for p in pdf_paths:
                                zipf.write(p, os.path.basename(p))
                        zip_buffer.seek(0)
                        await update.message.reply_document(
                            document=zip_buffer,
                            filename="statements.zip",
                            caption="✅ Successfully generated PDFs!"
                        )
                await ack_msg.delete()
        except Exception as e:
            logger.error(f"Error in background task: {e}", exc_info=True)
            await ack_msg.edit_text(f"❌ Error: {str(e)}")

    asyncio.create_task(generate_and_send())

# ================= FASTAPI WEBHOOK =================
@asynccontextmanager
async def lifespan(app: FastAPI):
    global application
    application = Application.builder().token(TELEGRAM_BOT_TOKEN).updater(None).build()
    application.add_handler(CommandHandler("start", start))
    application.add_handler(CallbackQueryHandler(button_callback))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    await application.initialize()
    webhook_url = f"{os.environ['RENDER_EXTERNAL_URL']}/webhook"
    await application.bot.set_webhook(url=webhook_url, allowed_updates=Update.ALL_TYPES)
    logger.info(f"Webhook set to {webhook_url}")
    yield
    await application.bot.delete_webhook()
    await application.shutdown()

fastapi_app = FastAPI(lifespan=lifespan)

@fastapi_app.post("/webhook")
async def process_update(request: Request):
    req = await request.json()
    update = Update.de_json(req, application.bot)
    await application.process_update(update)
    return Response()

@fastapi_app.get("/healthcheck")
async def health():
    return Response()

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(fastapi_app, host="0.0.0.0", port=port)
