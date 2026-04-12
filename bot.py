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
from contextlib import asynccontextmanager

from fastapi import FastAPI, Request, Response
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    CallbackQueryHandler, filters, ContextTypes
)
import uvicorn
import fitz
from google import genai

# ================= CONFIGURATION =================
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
GEMINI_API_KEY = os.environ.get("GEMINI_API_KEY")
if not TELEGRAM_BOT_TOKEN or not GEMINI_API_KEY:
    raise ValueError("Missing TELEGRAM_BOT_TOKEN or GEMINI_API_KEY")

# ================= USER AUTHORISATION =================
# Replace with your own Telegram user ID (get from @userinfobot)
ALLOWED_USERS = {6615254738}

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
    # Allow 2-digit or 4-digit year
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
    """Return a random time string HH:MM:00 within 05:00 - 09:40."""
    hour = random.randint(5, 9)
    if hour == 9:
        minute = random.randint(0, 40)
    else:
        minute = random.randint(0, 59)
    return f"{hour:02d}:{minute:02d}:00"

def normalize_received(received_str):
    """If time missing, append a random morning time (05:00-09:40)."""
    if not received_str:
        return None
    if re.search(r'\d{2}:\d{2}:\d{2}', received_str):
        return normalize_datetime_year(received_str)
    return normalize_datetime_year(received_str.strip() + " " + random_morning_time())

def inject_current_year_in_raw_text(raw_text):
    current_year = str(datetime.now().year)
    return re.sub(r'(?<!\d)(\d{2}-\d{2})(?!-\d{4})', rf'\1-{current_year}', raw_text)

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
    
    # Force target end into morning window
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
    """Return a new datetime with the same date as base_dt but random time 05:00-09:40."""
    hour = random.randint(5, 9)
    if hour == 9:
        minute = random.randint(0, 40)
    else:
        minute = random.randint(0, 59)
    return base_dt.replace(hour=hour, minute=minute, second=0, microsecond=0)

# ================= TEMPLATE 1: BARODA_BANK =================
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

def calculate_data_baroda(start_time_str, end_dt_str):
    # Start offset: +2.5h + random 10-20 min
    t1 = datetime.strptime(start_time_str, "%d-%m-%Y %H:%M:%S") + timedelta(hours=2.5) + timedelta(minutes=random.randint(10, 20))

    if end_dt_str:
        base_intervals = [40, 1440, 900, 150, 120, 240, 150, 25, 60, 15, 240, 720]
        fixed_indices = {0, 7}
        scaled, target_end = scale_timeline(start_time_str, end_dt_str, base_intervals, fixed_indices)
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
        # If final time is outside morning window, replace with random morning time on the same date
        if t11.hour > 9 or (t11.hour == 9 and t11.minute > 40) or t11.hour < 5:
            t11 = random_morning_datetime(t11)
    else:
        # No scaling: explicit random intervals
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

def parse_baroda_data(raw_text, max_retries=3):
    client = genai.Client(api_key=GEMINI_API_KEY)
    prompt = f"""
Extract the following from the text. Return ONLY a JSON array of objects with keys: "vehicle","dc","eway","received","cust_name","cust_id","mobile","tag_account".
Rules:
- vehicle: full registration e.g. "MP09HH4381".
- dc: a 2-4 digit number (standalone or after "DC-" / "DC:").
- eway: datetime "dd-mm-yyyy HH:MM:SS".
- received: datetime (optional) – can be just date, default time 08:00:00.
- cust_name: after "Name:" etc.
- cust_id: digits after "ID:".
- mobile: 10 digits.
- tag_account: digits after "Tag:".
If missing, omit.
Text:
{raw_text}
JSON:
"""
    for attempt in range(max_retries):
        try:
            response = client.models.generate_content(model="gemini-2.5-flash-lite", contents=prompt)
            content = response.text
            content = re.sub(r'```json\s*', '', content)
            content = re.sub(r'```\s*$', '', content)
            parsed = json.loads(content)
            if isinstance(parsed, list):
                for entry in parsed:
                    if "eway" in entry:
                        entry["eway"] = normalize_datetime_year(entry["eway"])
                    if "received" in entry:
                        entry["received"] = normalize_received(entry["received"])
                return parsed
            return []
        except Exception:
            time.sleep(2**attempt)
    return []

# ================= TEMPLATE 2: IDFC_BANK =================
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
    base_start = datetime.strptime(start_time_str, "%d-%m-%Y %H:%M:%S")
    offset = timedelta(hours=2, minutes=30) + timedelta(minutes=random.randint(10, 20))
    T1 = base_start + offset

    if end_time_str:
        base_intervals = [40, 1, 1440, 900, 150, 120, 240, 150, 60, 15, 960]
        fixed_indices = {0, 1}
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
        # If final time is outside morning window, replace with random morning time
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
    txn_times = {k: v + timedelta(minutes=2) for k, v in times.items()}
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

def parse_idfc_data(raw_text, max_retries=3):
    client = genai.Client(api_key=GEMINI_API_KEY)
    prompt = f"""
Extract from the text. Return ONLY a JSON array of objects, each object may have keys:
"start_time","received_time","dc","customer_name","mobile","truck_number","truck_owner","recharge_amount","opening_balance","toll_debits".

Rules:
- start_time: datetime "dd-mm-yyyy HH:MM:SS"
- received_time: optional – can be just date, default time 08:00:00
- dc: a 2-4 digit number (standalone or after "DC-" / "DC:")
- customer_name: after "Name:"
- mobile: 10 digits
- truck_number: like "UP67AT1939"
- truck_owner: after "Owner:"
- recharge_amount: number after "Recharge:"
- opening_balance: number after "Opening balance:"
- toll_debits: array of numbers (optional)
If a field is not present in a trip, omit it.

Text:
{raw_text}

JSON:
"""
    for attempt in range(max_retries):
        try:
            response = client.models.generate_content(model="gemini-2.5-flash-lite", contents=prompt)
            content = response.text
            content = re.sub(r'```json\s*', '', content)
            content = re.sub(r'```\s*$', '', content)
            parsed = json.loads(content)
            if isinstance(parsed, list):
                for entry in parsed:
                    if "start_time" in entry:
                        entry["start_time"] = normalize_datetime_year(entry["start_time"])
                    if "received_time" in entry:
                        entry["received_time"] = normalize_received(entry["received_time"])
                return parsed
            elif isinstance(parsed, dict):
                if "start_time" in parsed:
                    parsed["start_time"] = normalize_datetime_year(parsed["start_time"])
                if "received_time" in parsed:
                    parsed["received_time"] = normalize_received(parsed["received_time"])
                return [parsed]
            return []
        except Exception:
            time.sleep(2**attempt)
    return []

# ================= TELEGRAM BOT HANDLERS =================
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

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
    template = context.user_data.get("template")
    if not template:
        await update.message.reply_text("Please choose a template first using /start")
        return
    await update.message.reply_text("📄 Processing your data with Gemini AI...")
    try:
        normalized = inject_current_year_in_raw_text(user_input)
        if template == "baroda":
            entries = parse_baroda_data(normalized)
            if not entries:
                await update.message.reply_text("❌ Could not extract any baroda trip data.")
                return
            vehicle_pattern = re.compile(r'^[A-Z]{2}[0-9]{2}[A-Z]{1,2}[0-9]{4}$')
            for entry in entries:
                vehicle = entry.get("vehicle", "")
                if not vehicle_pattern.match(vehicle):
                    await update.message.reply_text(f"❌ Invalid vehicle: '{vehicle}'. Use full registration like MP09HH4381.")
                    return
                if not entry.get("dc"):
                    await update.message.reply_text("❌ Missing DC number in one of the trips. Please provide 'DC: ...'")
                    return
            await update.message.reply_text(f"✅ Extracted {len(entries)} trip(s). Generating PDFs...⚡⚡⚡")
            try:
                template_doc = fitz.open("baroda_template.pdf")
            except Exception as e:
                await update.message.reply_text(f"❌ Cannot open baroda_template.pdf: {e}")
                return
            pdf_paths = []
            with tempfile.TemporaryDirectory() as tmpdir:
                for entry in entries:
                    out_path = os.path.join(tmpdir, f"FT-{entry['dc']}.pdf")
                    try:
                        generate_baroda_pdf_to_path(template_doc, entry, out_path)
                        pdf_paths.append(out_path)
                    except Exception as e:
                        await update.message.reply_text(f"❌ Failed to generate PDF for DC {entry['dc']}: {e}")
                        template_doc.close()
                        return
                template_doc.close()
                if len(pdf_paths) == 1:
                    with open(pdf_paths[0], 'rb') as f:
                        await update.message.reply_text("✅ Successfully generated PDF!")
                        await update.message.reply_document(document=f, filename=os.path.basename(pdf_paths[0]))
                else:
                    zip_buffer = io.BytesIO()
                    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                        for p in pdf_paths:
                            zipf.write(p, os.path.basename(p))
                    zip_buffer.seek(0)
                    await update.message.reply_text("✅ Successfully generated PDFs!")
                    await update.message.reply_document(document=zip_buffer, filename="statements.zip")
        else:  # idfc
            entries = parse_idfc_data(normalized)
            if not entries:
                await update.message.reply_text("❌ Could not extract any IDFC trip data.")
                return
            for entry in entries:
                if not entry.get("start_time"):
                    await update.message.reply_text("❌ One of the trips missing start time. Please provide 'Start: ...'")
                    return
                if not entry.get("dc"):
                    await update.message.reply_text("❌ One of the trips missing DC number. Please provide 'DC: ...'")
                    return
            await update.message.reply_text(f"✅ Extracted {len(entries)} trip(s). Generating PDFs...⚡⚡⚡")
            try:
                template_doc = fitz.open("idfc_template.pdf")
            except Exception as e:
                await update.message.reply_text(f"❌ Cannot open idfc_template.pdf: {e}")
                return
            pdf_paths = []
            with tempfile.TemporaryDirectory() as tmpdir:
                for entry in entries:
                    out_path = os.path.join(tmpdir, f"FT-{entry['dc']}.pdf")
                    try:
                        generate_idfc_pdf_to_path(template_doc, entry, out_path)
                        pdf_paths.append(out_path)
                    except Exception as e:
                        await update.message.reply_text(f"❌ Failed to generate PDF for DC {entry['dc']}: {e}")
                        template_doc.close()
                        return
                template_doc.close()
                if len(pdf_paths) == 1:
                    with open(pdf_paths[0], 'rb') as f:
                        await update.message.reply_text("✅ Successfully generated PDF!")
                        await update.message.reply_document(document=f, filename=os.path.basename(pdf_paths[0]))
                else:
                    zip_buffer = io.BytesIO()
                    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zipf:
                        for p in pdf_paths:
                            zipf.write(p, os.path.basename(p))
                    zip_buffer.seek(0)
                    await update.message.reply_text("✅ Successfully generated PDFs!")
                    await update.message.reply_document(document=zip_buffer, filename="statements.zip")
    except Exception as e:
        logger.error(f"Error: {e}", exc_info=True)
        await update.message.reply_text(f"❌ Error: {str(e)}")

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