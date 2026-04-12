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
    """Ensure dd-mm-yyyy HH:MM:SS, force year to 2026 if <2025."""
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
    """Remove ``` ... ``` code blocks and return the inner text."""
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

# ================= REGEX PARSERS (WITH ALL FIELDS) =================
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

def parse_baroda_data(raw_text):
    """Regex parser for BARODA_BANK – extracts all fields."""
    entries = []
    # Split by blank lines
    blocks = re.split(r'\n\s*\n', raw_text.strip())
    for block in blocks:
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if not lines:
            continue
        
        # Extract vehicle
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
        
        # Extract DC
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
        
        # Extract eway (start datetime)
        eway_date = None
        eway_time = None
        # Extract received (end datetime) – optional
        received_date = None
        received_time = None
        cust_name = None
        cust_id = None
        mobile = None
        tag_account = None
        
        for i, line in enumerate(lines):
            # Look for labels
            lower = line.lower()
            if "eway" in lower:
                date_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)', line)
                if date_match:
                    eway_date = add_current_year_if_missing(date_match.group(1))
                time_match = re.search(r'(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                if time_match:
                    eway_time = time_match.group(1).strip()
                elif i+1 < len(lines) and re.search(r'^\d', lines[i+1]):
                    eway_time = lines[i+1].strip()
            elif "received" in lower:
                date_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)', line)
                if date_match:
                    received_date = add_current_year_if_missing(date_match.group(1))
                time_match = re.search(r'(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                if time_match:
                    received_time = time_match.group(1).strip()
                elif i+1 < len(lines) and re.search(r'^\d', lines[i+1]):
                    received_time = lines[i+1].strip()
            elif "name" in lower:
                # Extract after colon
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
    """Regex parser for IDFC_BANK – extracts all fields."""
    entries = []
    blocks = re.split(r'\n\s*\n', raw_text.strip())
    for block in blocks:
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if not lines:
            continue
        
        # Extract DC (can be anywhere)
        dc = None
        for line in lines:
            match = re.search(r'(?:DC[:\-\s]*)?(\d{2,4})', line, re.IGNORECASE)
            if match:
                dc = match.group(1)
                break
        if not dc:
            continue
        
        # Extract start_time, received_time, customer_name, mobile, truck_number, truck_owner, recharge_amount, opening_balance, toll_debits
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
                # Look for datetime
                dt_match = re.search(r'(\d{2}-\d{2}(?:-\d{4})?)\s+(\d{1,2}:\d{2}(?::\d{2})?\s*(?:am|pm)?|\d{3,4}\s*(?:am|pm|hrs)?)', line, re.IGNORECASE)
                if dt_match:
                    date_part = add_current_year_if_missing(dt_match.group(1))
                    time_part = parse_time_string(dt_match.group(2))
                    start_time = f"{date_part} {time_part}"
                else:
                    # Try separate lines
                    pass
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
                # Extract array like [720, 815, ...]
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

# ================= PDF GENERATION HELPERS (unchanged) =================
# ... (keep all the existing PDF generation functions exactly as they were)
# For brevity, I'll include them but you already have them in your code.
# I'll copy the essential parts from your previous working version.

# ================= TEMPLATE 1: BARODA_BANK =================
DEFAULT_CUST_NAME   = "VIPUL MITTAL"
DEFAULT_CUST_ID     = "11593956"
DEFAULT_MOBILE      = "9826260443"
DEFAULT_TAG_ACCOUNT = "21434130"
TEXT_COLOR = (0,0,0)
FONT_SIZE = 8
COORD = { ... }  # Keep your existing COORD dictionary (same as before)
TOLL_DEBITS_BARODA = [250, 335, 340, 85, 515, 260, 410, 480, 815, 720, 720]

def calculate_data_baroda(start_time_str, end_dt_str):
    # ... (same as your working version) ...
    pass

def scrub_and_put(page, x0, y0, x1, y1, tx, ty, text, bold=False, right=False):
    # ... (same) ...
    pass

def generate_baroda_pdf_to_path(template_doc, entry, output_path):
    # ... (same) ...
    pass

# ================= TEMPLATE 2: IDFC_BANK =================
DEFAULT_CUSTOMER_NAME = "KULDEEP KUMAR YADAV"
DEFAULT_MOBILE_IDFC   = "8743893682"
DEFAULT_TRUCK_NUMBER  = "UP67AT1939"
DEFAULT_TRUCK_OWNER   = "KULDEEP YADAV SINGH"
DEFAULT_RECHARGE_AMOUNT = 6400
DEFAULT_OPENING_BALANCE = 800
DEFAULT_TOLL_DEBITS = [720, 815, 480, 410, 260, 515, 85, 340, 335, 250]

# ... (keep all IDFC functions: DATE_COLOR, TIME_COLOR, etc., calculate_timeline_idfc, draw_idfc_row, generate_idfc_pdf_to_path) ...

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