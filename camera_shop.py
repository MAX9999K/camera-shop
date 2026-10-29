# -*- coding: utf-8 -*-
"""
ระบบร้านขายกล้องออนไลน์ (Camera Shop) — รวมโค้ด Python ทั้งหมดไว้ในไฟล์เดียว

วิธีรัน
    python -m pip install -r requirements.txt     (ทำครั้งเดียว)
    python camera_shop.py                         รันทั้ง 2 เว็บพร้อมกัน (กด Ctrl+C เพื่อปิด)
    python camera_shop.py shop                    รันเฉพาะเว็บร้านค้า   http://127.0.0.1:5000
    python camera_shop.py admin                   รันเฉพาะเว็บ Admin    http://127.0.0.1:5001

ไฟล์นี้ต้องวางไว้ข้างๆ โฟลเดอร์ templates_shop/, templates_admin/ และ static/
(ส่วนหน้าตาเว็บเป็นไฟล์ HTML จึงแยกอยู่ในโฟลเดอร์เหล่านั้น)

สารบัญ — อ่านจากบนลงล่าง ส่วนล่างเรียกใช้ส่วนบน
    ส่วนที่  1- 9  เครื่องมือพื้นฐาน: error, config, เงิน, ตรวจข้อมูล, ความปลอดภัย, QR, อัปโหลดรูป, ฐานข้อมูล
    ส่วนที่ 10     ตั้งค่า Flask ที่ 2 เว็บใช้ร่วมกัน
    ส่วนที่ 11-16  SERVICE = ตรรกะของร้าน (ตั้งค่า, สินค้า, สมาชิก, ส่วนลด, ตะกร้า, คำสั่งซื้อ)
    ส่วนที่ 17     เว็บร้านค้า (ลูกค้า)      ← หน้าเว็บเรียกใช้ service
    ส่วนที่ 18     เว็บผู้ดูแลระบบ (Admin)
    ส่วนที่ 19     จุดเริ่มต้นโปรแกรม
"""
from io import BytesIO
from PIL import Image, UnidentifiedImageError
import hashlib
import hmac
import os
import re
import secrets
import sqlite3
import sys
import threading
import time
from datetime import date, datetime
from decimal import Decimal, InvalidOperation
from functools import wraps

from flask import (Flask, abort, flash, g, redirect, render_template, request,
                   session, url_for, send_from_directory)
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename


# ============================================================================
# ส่วนที่ 1: ชนิดของข้อผิดพลาดที่แสดงให้ผู้ใช้อ่านได้
#
# ชนิดของ "ข้อผิดพลาดที่แสดงให้ผู้ใช้อ่านได้" ที่ใช้ทั้งโปรเจกต์
#
# แยกให้ชัดว่า error แบบไหนเป็นความผิดของผู้ใช้ (กรอกผิด/สั่งเกินสต็อก)
# ซึ่งต้องแจ้งเตือนอย่างสุภาพ ต่างจาก bug ของโปรแกรมซึ่งควรให้ขึ้น error จริง
# ============================================================================

class ValidationError(ValueError):
    """ข้อมูลช่องเดียวที่ผู้ใช้กรอกไม่ถูกต้อง เช่น เบอร์โทรผิดรูปแบบ"""


class FormErrors(Exception):
    """ฟอร์มหนึ่งฟอร์มมีหลายช่องผิดพร้อมกัน เก็บข้อความทั้งหมดไว้ใน .errors"""

    def __init__(self, errors):
        super().__init__("; ".join(errors))
        self.errors = errors


class ShopError(Exception):
    """ผิดกติกาของร้าน เช่น สต็อกไม่พอ, โค้ดส่วนลดใช้ไม่ได้"""


# ใช้ในคำสั่ง except เพื่อจับ error ทุกแบบที่ "แจ้งผู้ใช้ได้" ในครั้งเดียว
USER_ERRORS = (ValidationError, FormErrors, ShopError)


# ============================================================================
# ส่วนที่ 2: ค่าตั้งต้นของระบบ (Config)
#
# ค่าตั้งต้นทั้งหมดของระบบรวมไว้ที่เดียว (แก้ที่นี่ที่เดียว ไม่ต้องไล่หาในโค้ด)
# บางค่าเปลี่ยนได้โดยไม่ต้องแก้ไฟล์ ผ่าน environment variable (ดูใน README)
# ============================================================================

# --- ตำแหน่งไฟล์ ---------------------------------------------------------
ROOT_DIR = os.path.dirname(os.path.abspath(__file__))  # โฟลเดอร์ที่ไฟล์นี้อยู่
DB_FILE = os.environ.get("SHOP_DB", os.path.join(ROOT_DIR, "camera_shop.db"))
STATIC_DIR = os.path.join(ROOT_DIR, "static")
UPLOAD_DIR = os.path.join(STATIC_DIR, "uploads")
ALLOWED_IMAGE_EXTENSIONS = {"png", "jpg", "jpeg", "webp", "gif"}
MAX_IMAGES_PER_PRODUCT = 5          # สินค้า 1 ชิ้นมีรูปได้สูงสุดกี่รูป
MAX_IMAGE_BYTES = 4 * 1024 * 1024   # ขนาดไฟล์สูงสุดต่อ 1 รูป (4 MB)

# --- ข้อมูลสินค้า --------------------------------------------------------
BRANDS = ["Canon", "Sony", "Nikon"]
CATEGORIES = ["กล้อง", "เลนส์"]
LOW_STOCK_LIMIT = 2      # สต็อกเหลือเท่านี้หรือน้อยกว่า = แสดงเตือน "เหลือน้อย"
FEATURED_COUNT = 4       # จำนวนสินค้าแนะนำที่โชว์ในหน้าแรก

# --- การชำระเงินและสถานะคำสั่งซื้อ -------------------------------------
PAYMENT_METHODS = {
    "promptpay": "สแกน QR Code (PromptPay)",
    "card": "บัตรเครดิต/เดบิต (จำลอง)",
    "cod": "เก็บเงินปลายทาง (COD)",
}
STATUS_PENDING = "pending"   # รอชำระเงิน / รอร้านตรวจสอบ
STATUS_PAID = "paid"         # ชำระเงินแล้ว
STATUS_LABELS = {"review": "รอตรวจสอบสลิป", "cod_pending": "รอเก็บเงินปลายทาง", STATUS_PENDING: "รอชำระเงิน", STATUS_PAID: "ชำระเงินแล้ว", "cancelled": "ยกเลิกแล้ว"}

# --- ความปลอดภัย ---------------------------------------------------------
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "admin1234")
MAX_LOGIN_FAILS = 5      # ใส่รหัสผิดได้กี่ครั้ง
LOCK_SECONDS = 300       # ถูกล็อกกี่วินาที (300 = 5 นาที)

# --- ข้อมูลร้านที่แสดงท้ายเว็บ (แก้เป็นข้อมูลจริงของร้าน) ---------------
SHOP_INFO = {
    "address": os.environ.get("SHOP_ADDRESS", "259 ม.5 ต.บ้านค้อ อ.เมืองขอนแก่น จ.ขอนแก่น 40000"),
    "phone": os.environ.get("SHOP_PHONE", "083-218-6156"),
    "email": os.environ.get("SHOP_EMAIL", "khunsapy.t@kkumail.com"),
}


# ============================================================================
# ส่วนที่ 3: เรื่องเงิน: บาท <-> สตางค์
#
# เรื่องเงิน: แปลง "บาท" <-> "สตางค์"
#
# ทำไมต้องเก็บเป็นสตางค์?
#   คอมพิวเตอร์เก็บทศนิยม (float) ไม่แม่นยำ เช่น 0.1 + 0.2 = 0.30000000000000004
#   ถ้าเก็บเงินเป็น "จำนวนเต็มของสตางค์" (100 บาท = 10000 สตางค์) จะไม่คลาดเคลื่อน
#   ในฐานข้อมูลทุกช่องที่เป็นเงินจึงเป็นสตางค์ และแปลงเป็นบาทเฉพาะตอนแสดงผล
# ============================================================================

MAX_BAHT = Decimal("100000000")  # เพดานกันกรอกตัวเลขใหญ่ผิดปกติ


def parse_baht(raw_text, label="จำนวนเงิน"):
    """รับข้อความเช่น '1,234.50' แล้วคืนค่าเป็นสตางค์ (123450)"""
    try:
        amount = Decimal((raw_text or "").strip().replace(",", ""))
    except InvalidOperation:
        raise ValidationError(f"{label}ต้องเป็นตัวเลข")
    if not amount.is_finite():
        raise ValidationError(f"{label}ไม่ถูกต้อง")
    if amount < 0:
        raise ValidationError(f"{label}ห้ามติดลบ")
    if amount > MAX_BAHT:
        raise ValidationError(f"{label}สูงเกินไป")
    return int((amount * 100).to_integral_value())


def format_baht(satang):
    """แปลงสตางค์เป็นข้อความสำหรับแสดงผล เช่น 123450 -> '1,234.50'"""
    return f"{satang / 100:,.2f}"


# ============================================================================
# ส่วนที่ 4: ตัวตรวจข้อมูลที่ผู้ใช้กรอก (Validation)
#
# ตัวตรวจข้อมูลที่ผู้ใช้กรอก (Validation)
#
# หลักการ: ห้ามเชื่อข้อมูลจากฟอร์มเด็ดขาด ต้องตรวจฝั่งเซิร์ฟเวอร์ทุกครั้ง
#   - ฟังก์ชัน clean_xxx แต่ละตัวตรวจ "ช่องเดียว"
#       ถูกต้อง  -> คืนค่าที่ทำความสะอาดแล้ว
#       ผิด      -> raise ValidationError พร้อมข้อความภาษาไทย
#   - FormChecker ช่วยรวม error จากหลายช่องให้แสดงทีเดียว
# ============================================================================

# ตัวอักษรไทย (U+0E01-U+0E5B) หรืออังกฤษ ตามด้วยช่องว่าง . ' - ได้ (ไม่รับตัวเลข)
NAME_PATTERN = re.compile(r"^[A-Za-z\u0E01-\u0E5B][A-Za-z\u0E01-\u0E5B .'\-]*$")
PHONE_PATTERN = re.compile(r"^0[0-9]{8,9}$")  # ขึ้นต้นด้วย 0 รวม 9-10 หลัก


class FormChecker:
    """รวม error ของหลายช่อง: เรียก check() ทีละช่อง แล้วค่อย raise_if_failed() ตอนท้าย"""

    def __init__(self):
        self.errors = []

    def check(self, validator, *args):
        try:
            return validator(*args)
        except ValidationError as error:
            self.errors.append(str(error))
            return None

    def add_error(self, message):
        self.errors.append(message)

    def raise_if_failed(self):
        if self.errors:
            raise FormErrors(self.errors)


def clean_text(label, raw_text, max_length):
    text = " ".join((raw_text or "").split())  # ตัดช่องว่างซ้ำ/หัวท้าย
    if not text:
        raise ValidationError(f"กรุณากรอก{label}")
    if len(text) > max_length:
        raise ValidationError(f"{label}ต้องไม่เกิน {max_length} ตัวอักษร")
    return text


def clean_description(raw_text):
    """รายละเอียดสินค้า (ไม่บังคับ) เก็บการขึ้นบรรทัดใหม่ไว้ ตัดบรรทัดว่างที่ซ้อนกันเกิน 1 บรรทัด"""
    text = (raw_text or "").replace("\r\n", "\n").strip()
    text = re.sub(r"\n{3,}", "\n\n", text)
    if len(text) > 1000:
        raise ValidationError("รายละเอียดสินค้าต้องไม่เกิน 1,000 ตัวอักษร")
    return text


def clean_name(label, raw_text):
    name = clean_text(label, raw_text, 50)
    if not NAME_PATTERN.match(name):
        raise ValidationError(f"{label}ใช้ได้เฉพาะตัวอักษรไทยหรืออังกฤษ (ห้ามมีตัวเลขหรือสัญลักษณ์พิเศษ)")
    return name


def clean_birth_date(raw_text):
    """รับ 'YYYY-MM-DD' (ค่าจากช่อง <input type=date>) ต้องไม่เป็นอนาคต"""
    try:
        birth_date = datetime.strptime((raw_text or "").strip(), "%Y-%m-%d").date()
    except ValueError:
        raise ValidationError("กรุณาเลือกวันเดือนปีเกิดให้ถูกต้อง")
    if birth_date > date.today():
        raise ValidationError("วันเกิดต้องไม่เป็นวันในอนาคต")
    if birth_date.year < 1900:
        raise ValidationError("วันเกิดไม่ถูกต้อง")
    return birth_date.isoformat()


def clean_phone(raw_text):
    """ลบช่องว่าง/ขีดออก เหลือเฉพาะตัวเลข เช่น '081-234 5678' -> '0812345678'"""
    phone = re.sub(r"[\s-]", "", raw_text or "")
    if not PHONE_PATTERN.match(phone):
        raise ValidationError("เบอร์โทรไม่ถูกต้อง (ตัวเลข 9-10 หลัก ขึ้นต้นด้วย 0)")
    return phone


def clean_password(password, confirmation):
    if len(password) < 8:
        raise ValidationError("รหัสผ่านต้องยาวอย่างน้อย 8 ตัวอักษร")
    if len(password) > 128:
        raise ValidationError("รหัสผ่านยาวเกินไป (ไม่เกิน 128 ตัวอักษร)")
    if password != confirmation:
        raise ValidationError("รหัสผ่านและการยืนยันรหัสผ่านไม่ตรงกัน")
    return password


def clean_address(raw_text):
    address = clean_text("ที่อยู่จัดส่ง", raw_text, 300)
    if len(address) < 10:
        raise ValidationError("ที่อยู่จัดส่งสั้นเกินไป กรุณากรอกให้ครบ (บ้านเลขที่ ถนน ตำบล อำเภอ จังหวัด รหัสไปรษณีย์)")
    return address


def clean_integer(label, raw_text, minimum=0, maximum=1_000_000):
    try:
        number = int((raw_text or "").strip())
    except ValueError:
        raise ValidationError(f"{label}ต้องเป็นจำนวนเต็ม")
    if number < minimum:
        raise ValidationError(f"{label}ต้องไม่น้อยกว่า {minimum}")
    if number > maximum:
        raise ValidationError(f"{label}ต้องไม่เกิน {maximum:,}")
    return number


def clean_choice(label, raw_text, allowed_values):
    """ค่าที่เลือกต้องอยู่ในรายการที่อนุญาตเท่านั้น (กันคนแก้ HTML ส่งค่าแปลกๆ)"""
    if raw_text not in allowed_values:
        raise ValidationError(f"{label}ไม่ถูกต้อง")
    return raw_text


def clean_promptpay_id(raw_text):
    """PromptPay ID คือเบอร์มือถือ 10 หลัก หรือเลขบัตรประชาชน 13 หลัก"""
    digits = re.sub(r"[\s-]", "", raw_text or "")
    is_phone = re.fullmatch(r"0[0-9]{9}", digits)
    is_national_id = re.fullmatch(r"[0-9]{13}", digits)
    if not (is_phone or is_national_id):
        raise ValidationError("PromptPay ID ต้องเป็นเบอร์มือถือ 10 หลัก หรือเลขบัตรประชาชน 13 หลัก")
    return digits


# ============================================================================
# ส่วนที่ 5: ความปลอดภัย: hash รหัสผ่าน, กันเดารหัส, redirect ปลอดภัย
#
# เรื่องความปลอดภัยที่ใช้ทั้ง 2 เว็บ
#
# 1) เก็บรหัสผ่านแบบ hash   - ไม่เก็บรหัสจริง เก็บเฉพาะ "ลายนิ้วมือ" ที่ย้อนกลับไม่ได้
# 2) LoginThrottle           - กันการเดารหัสผ่านซ้ำๆ (brute force)
# 3) safe_redirect_target    - กันลิงก์หลอกให้เด้งไปเว็บอื่นหลังล็อกอิน (open redirect)
# ============================================================================

def hash_password(password):
    return generate_password_hash(password)


def verify_password(password_hash, password):
    return check_password_hash(password_hash, password)


# ใช้ตอน "ไม่พบเบอร์นี้ในระบบ" เพื่อให้ใช้เวลาตรวจเท่ากับกรณีพบเบอร์
# ไม่งั้นคนร้ายจับเวลาตอบสนองแล้วเดาได้ว่าเบอร์ไหนสมัครแล้ว
_DUMMY_HASH = generate_password_hash("dummy-password")


def verify_unknown_user(password):
    check_password_hash(_DUMMY_HASH, password)


def safe_redirect_target(next_url, default_url):
    """ยอมรับเฉพาะลิงก์ภายในเว็บเรา (ขึ้นต้นด้วย / ไม่ใช่ //)"""
    if next_url and next_url.startswith("/") and not next_url.startswith("//"):
        return next_url
    return default_url


class LoginThrottle:
    """จำจำนวนครั้งที่ใส่ผิดของแต่ละ key (เช่น IP+เบอร์) ผิดครบกำหนดจะถูกล็อกชั่วคราว"""

    def __init__(self):
        self._failures = {}  # key -> (จำนวนครั้งที่ผิด, เวลาที่ผิดครั้งแรก)

    def is_locked(self, key):
        count, first_time = self._failures.get(key, (0, 0))
        return count >= MAX_LOGIN_FAILS and time.time() - first_time < LOCK_SECONDS

    def record_failure(self, key):
        count, first_time = self._failures.get(key, (0, 0))
        if count == 0 or time.time() - first_time >= LOCK_SECONDS:
            count, first_time = 0, time.time()  # เริ่มนับรอบใหม่
        self._failures[key] = (count + 1, first_time)

    def reset(self, key):
        self._failures.pop(key, None)


# ============================================================================
# ส่วนที่ 6: สร้างข้อความ QR พร้อมเพย์ (PromptPay)
#
# สร้างข้อความ (payload) สำหรับ QR Code พร้อมเพย์ (Thai QR Payment / PromptPay)
#
# QR ที่แอพธนาคารสแกนได้ คือข้อความมาตรฐาน EMVCo ที่ประกอบจาก "แท็ก" ต่อกัน:
#     [รหัสแท็ก 2 หลัก][ความยาว 2 หลัก][ค่า]
# ตัวอย่าง "5802TH" = แท็ก 58 (ประเทศ) ยาว 02 ค่า "TH"
#
# ไฟล์นี้สร้างได้เฉพาะ "ข้อความ" ส่วนการวาดเป็นภาพ QR อยู่ที่ core/qr_image.py
# ============================================================================

PROMPTPAY_APP_ID = "A000000677010111"  # รหัสบริการ Credit Transfer ของพร้อมเพย์
CURRENCY_THB = "764"                    # รหัสสกุลเงินบาทตามมาตรฐาน ISO 4217


def _tag(tag_id, value):
    """ประกอบ 1 แท็ก: รหัส + ความยาว(2 หลัก) + ค่า"""
    return f"{tag_id}{len(value):02d}{value}"


def crc16_ccitt(text):
    """
    ตัวตรวจความถูกต้อง (checksum) ท้าย QR  ถ้าสแกนแล้วค่าไม่ตรง แอพธนาคารจะปฏิเสธ
    ใช้อัลกอริทึม CRC-16/CCITT-FALSE (เริ่ม 0xFFFF, polynomial 0x1021)
    """
    crc = 0xFFFF
    for byte in text.encode("ascii"):
        crc ^= byte << 8
        for _ in range(8):
            if crc & 0x8000:
                crc = (crc << 1) ^ 0x1021
            else:
                crc <<= 1
            crc &= 0xFFFF
    return crc


def _format_target(promptpay_id):
    """
    แปลง PromptPay ID เป็นรูปแบบที่ QR ต้องการ
      เบอร์มือถือ 10 หลัก  0812345678    -> ประเภท 01, ค่า 0066812345678
      เลขบัตร ปชช. 13 หลัก               -> ประเภท 02, ค่าเลข 13 หลักเดิม
    """
    if len(promptpay_id) == 13:
        return _tag("02", promptpay_id)
    return _tag("01", "0066" + promptpay_id[1:])


def build_payload(promptpay_id, amount_satang=None):
    """
    สร้างข้อความ QR
      promptpay_id   : เบอร์มือถือ 10 หลัก หรือเลขบัตรประชาชน 13 หลัก (ตัวเลขล้วน)
      amount_satang  : ยอดเงินเป็นสตางค์ ถ้าไม่ใส่ = QR แบบให้ผู้โอนกรอกยอดเอง
    """
    merchant_info = _tag("00", PROMPTPAY_APP_ID) + _format_target(promptpay_id)

    parts = [
        _tag("00", "01"),                                    # เวอร์ชันของ QR
        _tag("01", "12" if amount_satang else "11"),         # 12 = ระบุยอด, 11 = ไม่ระบุยอด
        _tag("29", merchant_info),                           # ข้อมูลผู้รับเงิน
        _tag("53", CURRENCY_THB),                            # สกุลเงิน
    ]
    if amount_satang:
        baht, satang = divmod(amount_satang, 100)
        parts.append(_tag("54", f"{baht}.{satang:02d}"))     # ยอดเงิน
    parts.append(_tag("58", "TH"))                           # ประเทศ

    payload_without_crc = "".join(parts) + "6304"            # 63 04 = แท็ก CRC ยาว 4 ตัว
    return payload_without_crc + f"{crc16_ccitt(payload_without_crc):04X}"


# ============================================================================
# ส่วนที่ 7: วาดข้อความเป็นรูป QR Code
#
# วาดข้อความเป็นภาพ QR Code (SVG) ด้วยไลบรารี segno
# ติดตั้งด้วย:  pip install segno   (อยู่ใน requirements.txt แล้ว)
# ============================================================================

class QrUnavailable(Exception):
    """ยังไม่ได้ติดตั้ง segno"""


def make_qr_svg(text):
    """คืนโค้ด SVG ของ QR ที่ฝังในหน้า HTML ได้เลย (ใช้ error correction ระดับ M)"""
    try:
        import segno
    except ImportError:
        raise QrUnavailable("ยังไม่ได้ติดตั้ง segno กรุณารัน: python -m pip install segno")
    return segno.make(text, error="m").svg_inline(scale=6, border=2)


# ============================================================================
# ส่วนที่ 8: อัปโหลดรูปสินค้า
#
# จัดการไฟล์รูปสินค้าที่ Admin อัปโหลด (หลายรูปต่อสินค้า)
#
# ขั้นตอนที่ปลอดภัย: ตรวจทุกไฟล์ให้ผ่านก่อน (pick_valid_images) แล้วค่อยบันทึกลงดิสก์ (save_image_file)
# จะได้ไม่เกิดกรณีบันทึกไปแล้วครึ่งหนึ่ง แล้วไฟล์ที่เหลือผิด
# ============================================================================

def _extension_of(filename):
    return filename.rsplit(".", 1)[-1].lower() if "." in filename else ""


def _size_of(uploaded_file):
    """ขนาดไฟล์เป็น byte: เลื่อนไปท้ายไฟล์เพื่อดูตำแหน่ง แล้วเลื่อนกลับมาต้นไฟล์"""
    uploaded_file.stream.seek(0, os.SEEK_END)
    size = uploaded_file.stream.tell()
    uploaded_file.stream.seek(0)
    return size


def pick_valid_images(uploaded_files, max_count):
    """
    รับรายการไฟล์จากฟอร์ม คืนเฉพาะไฟล์ที่ผู้ใช้เลือกจริงและผ่านการตรวจแล้ว
      - ช่องที่ไม่ได้เลือกไฟล์ (ชื่อว่าง) จะถูกข้าม
      - ผิดเงื่อนไขข้อไหน raise ValidationError (ยังไม่มีไฟล์ไหนถูกบันทึก)
    """
    chosen = [f for f in uploaded_files if f and f.filename]
    if len(chosen) > max_count:
        raise ValidationError(f"เพิ่มรูปได้อีกไม่เกิน {max_count} รูป "
                              f"(สินค้า 1 ชิ้นมีได้สูงสุด {MAX_IMAGES_PER_PRODUCT} รูป)")
    for uploaded in chosen:
        if _extension_of(uploaded.filename) not in ALLOWED_IMAGE_EXTENSIONS:
            raise ValidationError(f"ไฟล์ '{uploaded.filename}' ไม่ใช่รูปที่รองรับ (png, jpg, jpeg, webp, gif)")
        if _size_of(uploaded) > MAX_IMAGE_BYTES:
            raise ValidationError(f"ไฟล์ '{uploaded.filename}' ใหญ่เกิน {MAX_IMAGE_BYTES // (1024 * 1024)} MB")
    return chosen


def save_image_file(uploaded_file):
    """บันทึกไฟล์ลงโฟลเดอร์ uploads แล้วคืนชื่อไฟล์ที่ใช้เก็บจริง"""
    os.makedirs(UPLOAD_DIR, exist_ok=True)
    # ใส่เลขสุ่มนำหน้า กันชื่อไฟล์ชนกัน และใช้ secure_filename กันชื่อไฟล์อันตราย
    saved_name = f"{secrets.token_hex(8)}_{secure_filename(uploaded_file.filename)}"
    uploaded_file.save(os.path.join(UPLOAD_DIR, saved_name))
    return saved_name


def delete_image_file(filename):
    """ลบไฟล์รูปออกจากโฟลเดอร์ uploads (ใช้ตอนลบรูปสินค้า)"""
    if not filename:
        return
    # basename = ตัดส่วนที่เป็นโฟลเดอร์ทิ้ง กันชื่อไฟล์แปลกๆ ชี้ออกนอกโฟลเดอร์ uploads
    path = os.path.join(UPLOAD_DIR, os.path.basename(filename))
    if os.path.exists(path):
        os.remove(path)


# ============================================================================
# ส่วนที่ 9: ฐานข้อมูล SQLite
#
# ฐานข้อมูล SQLite: เชื่อมต่อ, สร้างตาราง, ใส่ข้อมูลตัวอย่าง
#
# ตารางทั้งหมด
#   products     สินค้า                      members   สมาชิก
#   coupons      โค้ดส่วนลด                  settings  ค่าตั้งค่าร้าน (เช่น PromptPay ID)
#   orders       หัวบิลคำสั่งซื้อ + ข้อมูลผู้ซื้อ
#   order_items  รายการสินค้าในแต่ละบิล
#   product_images  รูปสินค้า (สินค้า 1 ชิ้นมีได้หลายรูป รูปแรกคือรูปหลัก)
#
# หมายเหตุ: ช่องที่เป็นเงินทุกช่องเก็บเป็น "สตางค์" (ดู core/money.py)
# ============================================================================

SCHEMA = """
CREATE TABLE IF NOT EXISTS products (
    product_id INTEGER PRIMARY KEY AUTOINCREMENT,
    name       TEXT NOT NULL,
    brand      TEXT NOT NULL,
    category   TEXT NOT NULL,
    price      INTEGER NOT NULL CHECK (price >= 0),
    stock      INTEGER NOT NULL CHECK (stock >= 0),
    description TEXT NOT NULL DEFAULT '',   -- รายละเอียดสินค้า (ขึ้นในหน้า "ดูด่วน")
    hidden INTEGER NOT NULL DEFAULT 0 CHECK (hidden IN (0,1))
);

CREATE TABLE IF NOT EXISTS product_images (
    image_id   INTEGER PRIMARY KEY AUTOINCREMENT,
    product_id INTEGER NOT NULL REFERENCES products(product_id),
    filename   TEXT NOT NULL,
    position   INTEGER NOT NULL DEFAULT 0   -- ลำดับรูป 0 = รูปหลัก (แสดงบนการ์ดสินค้า)
);

CREATE TABLE IF NOT EXISTS coupons (
    code          TEXT PRIMARY KEY,
    discount_type TEXT NOT NULL CHECK (discount_type IN ('percent', 'fixed')),
    value         REAL NOT NULL CHECK (value >= 0),   -- percent = %, fixed = สตางค์
    min_spend     INTEGER NOT NULL CHECK (min_spend >= 0),
    enabled       INTEGER NOT NULL DEFAULT 1 CHECK (enabled IN (0,1)),
    expires_at    TEXT NOT NULL DEFAULT ''
);

CREATE TABLE IF NOT EXISTS members (
    member_id     INTEGER PRIMARY KEY AUTOINCREMENT,
    first_name    TEXT NOT NULL,
    last_name     TEXT NOT NULL,
    birth_date    TEXT NOT NULL,            -- รูปแบบ YYYY-MM-DD
    phone         TEXT NOT NULL UNIQUE,     -- ใช้เป็นชื่อผู้ใช้ตอนล็อกอิน
    password_hash TEXT NOT NULL,
    consent_at    TEXT NOT NULL,            -- เวลาที่ผู้ใช้ยินยอมให้เก็บข้อมูล
    created_at    TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS orders (
    order_id         INTEGER PRIMARY KEY AUTOINCREMENT,
    order_date       TEXT NOT NULL,
    total_amount     INTEGER NOT NULL CHECK (total_amount >= 0),
    discount_amount  INTEGER NOT NULL CHECK (discount_amount >= 0),
    final_amount     INTEGER NOT NULL CHECK (final_amount >= 0),
    payment_method   TEXT,
    member_id        INTEGER REFERENCES members(member_id),
    buyer_name       TEXT NOT NULL DEFAULT '',
    buyer_phone      TEXT NOT NULL DEFAULT '',
    shipping_address TEXT NOT NULL DEFAULT '',
    status           TEXT NOT NULL DEFAULT 'paid'   -- pending = รอชำระ, paid = ชำระแล้ว
);

CREATE TABLE IF NOT EXISTS order_items (
    id         INTEGER PRIMARY KEY AUTOINCREMENT,
    order_id   INTEGER NOT NULL REFERENCES orders(order_id),
    product_id INTEGER NOT NULL REFERENCES products(product_id),
    quantity   INTEGER NOT NULL CHECK (quantity > 0),
    unit_price INTEGER NOT NULL CHECK (unit_price >= 0)
);

CREATE TABLE IF NOT EXISTS settings (
    key   TEXT PRIMARY KEY,
    value TEXT NOT NULL
);
"""

# คอลัมน์ที่เพิ่มเข้ามาทีหลัง: ถ้าเป็นฐานข้อมูลเก่าจะเพิ่มให้อัตโนมัติ (ไม่ต้องลบไฟล์ทิ้ง)
COLUMNS_ADDED_LATER = {
    "orders": {
        "fulfillment": "TEXT NOT NULL DEFAULT 'delivery'",
        "slip_file": "TEXT NOT NULL DEFAULT ''",
        "slip_note": "TEXT NOT NULL DEFAULT ''",
        "member_id": "INTEGER REFERENCES members(member_id)",
        "buyer_name": "TEXT NOT NULL DEFAULT ''",
        "buyer_phone": "TEXT NOT NULL DEFAULT ''",
        "shipping_address": "TEXT NOT NULL DEFAULT ''",
        "status": "TEXT NOT NULL DEFAULT 'paid'",
    },
    "products": {
        "description": "TEXT NOT NULL DEFAULT ''",
        "hidden": "INTEGER NOT NULL DEFAULT 0",
    },
    "coupons": {
        "enabled": "INTEGER NOT NULL DEFAULT 1",
        "expires_at": "TEXT NOT NULL DEFAULT ''",
    },
}

# (ชื่อ, ยี่ห้อ, ประเภท, ราคาบาท, สต็อก, รายละเอียด)  *รายละเอียดเป็นข้อความตัวอย่าง ควรแก้เป็นสเปกจริงใน Admin
SAMPLE_PRODUCTS = [
    ("EOS R5", "Canon", "กล้อง", 139900, 5, "กล้องมิเรอร์เลสฟูลเฟรม ความละเอียดประมาณ 45 ล้านพิกเซล"),
    ("EOS R6 Mark II", "Canon", "กล้อง", 78900, 8, "กล้องมิเรอร์เลสฟูลเฟรม ความละเอียดประมาณ 24 ล้านพิกเซล"),
    ("RF 24-70mm f/2.8L IS USM", "Canon", "เลนส์", 82900, 4, "เลนส์ซูมมาตรฐาน รูรับแสงกว้างคงที่ f/2.8 สำหรับกล้อง Canon ตระกูล R"),
    ("Alpha A7 IV", "Sony", "กล้อง", 85900, 6, "กล้องมิเรอร์เลสฟูลเฟรม ความละเอียดประมาณ 33 ล้านพิกเซล"),
    ("Alpha A7R V", "Sony", "กล้อง", 129900, 3, "กล้องมิเรอร์เลสฟูลเฟรม ความละเอียดสูงประมาณ 61 ล้านพิกเซล"),
    ("FE 70-200mm f/2.8 GM II", "Sony", "เลนส์", 99900, 2, "เลนส์เทเลโฟโต้ซูม รูรับแสงกว้างคงที่ f/2.8 สำหรับกล้อง Sony ตระกูล E"),
    ("Z8", "Nikon", "กล้อง", 144900, 3, "กล้องมิเรอร์เลสฟูลเฟรม ความละเอียดประมาณ 45.7 ล้านพิกเซล"),
    ("Z6 III", "Nikon", "กล้อง", 83900, 7, "กล้องมิเรอร์เลสฟูลเฟรม ความละเอียดประมาณ 24.5 ล้านพิกเซล"),
    ("NIKKOR Z 24-120mm f/4 S", "Nikon", "เลนส์", 47900, 5, "เลนส์ซูมอเนกประสงค์ รูรับแสงคงที่ f/4 สำหรับกล้อง Nikon ตระกูล Z"),
]

# (โค้ด, ประเภท, ค่า, ยอดขั้นต่ำเป็นบาท)  fixed: ค่าเป็นบาท  percent: ค่าเป็น %
SAMPLE_COUPONS = [
    ("WELCOME10", "percent", 10, 5000),
    ("SAVE2000", "fixed", 2000, 20000),
]


def open_connection():
    """
    เปิดการเชื่อมต่อฐานข้อมูล
    isolation_level=None = โหมด autocommit: เราสั่ง BEGIN / COMMIT / ROLLBACK เอง
    ในจุดที่ต้องทำหลายคำสั่งให้สำเร็จพร้อมกัน (เช่น ตอนสั่งซื้อ)
    """
    connection = sqlite3.connect(DB_FILE, isolation_level=None, timeout=15)
    connection.row_factory = sqlite3.Row  # เข้าถึงคอลัมน์ด้วยชื่อ เช่น row["name"]
    connection.execute("PRAGMA foreign_keys = ON")
    return connection


def _add_missing_columns(db):
    """ตารางไหนในฐานข้อมูลเก่ายังไม่มีคอลัมน์ใหม่ ให้เพิ่มเข้าไป"""
    for table, columns in COLUMNS_ADDED_LATER.items():
        existing = [row["name"] for row in db.execute(f"PRAGMA table_info({table})")]
        for column, definition in columns.items():
            if column not in existing:
                db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")


def _move_old_single_images(db):
    """
    เวอร์ชันก่อนหน้าเก็บรูปไว้ที่คอลัมน์ products.image (1 สินค้า 1 รูป)
    ย้ายมาไว้ในตาราง product_images แล้วเคลียร์ช่องเก่า (ทำซ้ำได้ ไม่ย้ายซ้ำ)
    """
    columns = [row["name"] for row in db.execute("PRAGMA table_info(products)")]
    if "image" in columns:
        db.execute("INSERT INTO product_images (product_id, filename, position) "
                   "SELECT product_id, image, 0 FROM products WHERE image IS NOT NULL AND image != ''")
        db.execute("UPDATE products SET image = NULL")


def _insert_sample_data(db):
    if db.execute("SELECT COUNT(*) FROM products").fetchone()[0] == 0:
        db.executemany(
            "INSERT INTO products (name, brand, category, price, stock, description) VALUES (?, ?, ?, ?, ?, ?)",
            [(name, brand, category, baht * 100, stock, description)
             for name, brand, category, baht, stock, description in SAMPLE_PRODUCTS],
        )
    if db.execute("SELECT COUNT(*) FROM coupons").fetchone()[0] == 0:
        db.executemany(
            "INSERT INTO coupons (code, discount_type, value, min_spend) VALUES (?, ?, ?, ?)",
            [(code, kind, value * 100 if kind == "fixed" else value, min_baht * 100)
             for code, kind, value, min_baht in SAMPLE_COUPONS],
        )


def init_database():
    """สร้างตารางและข้อมูลตัวอย่าง เรียกซ้ำกี่ครั้งก็ได้ (ไม่ทับข้อมูลเดิม)"""
    db = open_connection()
    db.execute("PRAGMA journal_mode = WAL")  # ให้ 2 เว็บใช้ฐานข้อมูลเดียวกันได้ลื่นขึ้น
    db.executescript(SCHEMA)
    _add_missing_columns(db)
    _move_old_single_images(db)
    _insert_sample_data(db)
    db.close()


# ============================================================================
# ส่วนที่ 10: ตั้งค่า Flask ที่ 2 เว็บใช้ร่วมกัน
#
# ตั้งค่า Flask ที่ทั้งเว็บร้านค้าและเว็บ Admin ใช้ร่วมกัน
#
#   create_flask_app()  สร้างแอพ + ใส่ระบบพื้นฐาน (session, CSRF, ปิดฐานข้อมูล, ตัวช่วยใน template)
#   get_db()            ขอการเชื่อมต่อฐานข้อมูลของ request นี้
#   flash_errors()      แสดง error ของผู้ใช้เป็นแถบแจ้งเตือน
# ============================================================================

# ------------------------------------------------------------- ฐานข้อมูล
def get_db():
    """เปิดการเชื่อมต่อครั้งแรกของ request แล้วเก็บไว้ใน g ให้ใช้ซ้ำจนจบ request"""
    if "db" not in g:
        g.db = open_connection()
    return g.db


def _close_db_after_request(_error):
    db = g.pop("db", None)
    if db is not None:
        db.close()


# ------------------------------------------------------------- secret key
def _load_secret_key(site_name):
    """
    secret key ใช้เซ็น cookie ของ session กันคนปลอม
    เก็บไว้ในไฟล์ .secret_<ชื่อเว็บ> เพื่อให้ผู้ใช้ไม่หลุดล็อกอินเมื่อรีสตาร์ทโปรแกรม
    """
    from_env = os.environ.get(f"SECRET_KEY_{site_name.upper()}")
    if from_env:
        return from_env
    path = os.path.join(ROOT_DIR, f".secret_{site_name}")
    if os.path.exists(path):
        with open(path) as file:
            return file.read().strip()
    key = secrets.token_hex(32)
    with open(path, "w") as file:
        file.write(key)
    return key


# ------------------------------------------------------------- CSRF
def _csrf_token():
    """โทเคนลับประจำ session ที่ทุกฟอร์ม POST ต้องแนบมา"""
    if "_csrf" not in session:
        session["_csrf"] = secrets.token_hex(16)
    return session["_csrf"]


def _reject_forged_post_requests():
    """
    ป้องกัน CSRF: เว็บอื่นแอบสั่งให้เบราว์เซอร์เราส่งฟอร์มมายังร้านโดยที่เราไม่รู้ตัว
    เว็บอื่นไม่รู้โทเคนลับของเรา ฟอร์มที่ไม่มีโทเคนที่ถูกต้องจึงถูกปฏิเสธ
    """
    if request.method != "POST":
        return
    sent = request.form.get("_csrf", "")
    expected = session.get("_csrf")
    if not expected or not hmac.compare_digest(sent, expected):
        abort(400, "CSRF token ไม่ถูกต้อง กรุณารีเฟรชหน้าแล้วลองใหม่")


# ------------------------------------------------------------- ตัวช่วยใน template
def _payment_label(value):
    return PAYMENT_METHODS.get(value, value or "-")


def _register_template_helpers(app):
    app.jinja_env.filters["baht"] = format_baht
    app.jinja_env.filters["payment_label"] = _payment_label
    app.jinja_env.filters["status_label"] = lambda status: STATUS_LABELS.get(status, status)
    app.jinja_env.globals["csrf"] = _csrf_token


# ------------------------------------------------------------- สร้างแอพ
def create_flask_app(site_name, template_folder):
    app = Flask(site_name, template_folder=template_folder, static_folder=STATIC_DIR)
    app.secret_key = _load_secret_key(site_name)
    app.config.update(
        # cookie ไม่แยกตามพอร์ต จึงตั้งชื่อต่างกัน กัน session ของ 2 เว็บปนกัน
        SESSION_COOKIE_NAME=f"camera_{site_name}_session",
        SESSION_COOKIE_HTTPONLY=True,    # JavaScript อ่าน cookie ไม่ได้
        SESSION_COOKIE_SAMESITE="Lax",
        # ขนาดรวมของคำขอที่รับได้ = รูปเต็มจำนวน + เผื่อข้อมูลฟอร์มอีกเล็กน้อย
        MAX_CONTENT_LENGTH=MAX_IMAGE_BYTES * MAX_IMAGES_PER_PRODUCT + 2 * 1024 * 1024,
    )
    app.teardown_appcontext(_close_db_after_request)
    app.before_request(_reject_forged_post_requests)
    _register_template_helpers(app)
    app.register_error_handler(413, _file_too_large)
    return app


def _file_too_large(_error):
    return "ไฟล์ที่อัปโหลดมีขนาดรวมใหญ่เกินไป กรุณาย่อรูปแล้วลองใหม่ (รูปละไม่เกิน 4 MB)", 413


def flash_errors(error):
    """แสดงข้อความ error ของผู้ใช้ (ไม่ว่าจะ 1 ข้อความหรือหลายข้อความ) เป็นแถบสีแดง"""
    messages = error.errors if isinstance(error, FormErrors) else [str(error)]
    for message in messages:
        flash(message, "danger")


# ============================================================================
# ส่วนที่ 11: SERVICE: ค่าตั้งค่าร้าน
#
# ค่าตั้งค่าของร้านที่ Admin แก้ได้จากหน้าเว็บ (เก็บในตาราง settings แบบ key-value)
# ============================================================================

PROMPTPAY_ID_KEY = "promptpay_id"
PROMPTPAY_IMAGE_KEY = "promptpay_image"


def get_setting(db, key, default=""):
    row = db.execute("SELECT value FROM settings WHERE key = ?", (key,)).fetchone()
    return row["value"] if row else default


def set_setting(db, key, value):
    # INSERT ... ON CONFLICT = ถ้ายังไม่มี key นี้ให้เพิ่ม ถ้ามีแล้วให้อัปเดตค่า
    db.execute(
        "INSERT INTO settings (key, value) VALUES (?, ?) "
        "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (key, value),
    )


# ============================================================================
# ส่วนที่ 12: SERVICE: สินค้า
#
# ตรรกะเกี่ยวกับสินค้า: ค้นหา, ดูรายละเอียด, เพิ่มสินค้าใหม่, แก้ไขข้อมูล/รูป, เติมสต็อก, แก้ราคา
#
# สินค้าที่ดึงออกไปเป็น dict ที่มี 2 ช่องพิเศษเพิ่มจากตาราง:
#     images       รายชื่อไฟล์รูปทั้งหมด (เรียงตามลำดับ รูปแรก = รูปหลัก)
#     cover_image  ชื่อไฟล์รูปหลัก (ไม่มีรูป = None)
#
# หมายเหตุเรื่อง SQL: ใช้เครื่องหมาย ? แล้วส่งค่าแยกเป็น tuple เสมอ (parameterized query)
# ห้ามเอาข้อความจากผู้ใช้มาต่อสตริง SQL ตรงๆ เพราะจะโดน SQL Injection
# ============================================================================

# ------------------------------------------------------------------ ดึงข้อมูล
def _attach_images(db, rows):
    """แปลงแถวสินค้าเป็น dict แล้วเติมรูปของทุกสินค้า (ดึงรูปทั้งหมดในคำสั่ง SQL เดียว)"""
    products = [dict(row) for row in rows]
    if not products:
        return products
    ids = [product["product_id"] for product in products]
    placeholders = ",".join("?" * len(ids))   # "?,?,?" ตามจำนวนสินค้า
    images_by_product = {}
    for row in db.execute(
        f"SELECT product_id, filename FROM product_images WHERE product_id IN ({placeholders}) "
        "ORDER BY position, image_id", ids
    ):
        images_by_product.setdefault(row["product_id"], []).append(row["filename"])
    for product in products:
        product["images"] = images_by_product.get(product["product_id"], [])
        product["cover_image"] = product["images"][0] if product["images"] else None
    return products


def get_product(db, product_id):
    row = db.execute("SELECT * FROM products WHERE product_id = ?", (product_id,)).fetchone()
    return _attach_images(db, [row])[0] if row else None


def list_products(db):
    return _attach_images(db, db.execute("SELECT * FROM products ORDER BY product_id").fetchall())


def featured_products(db, limit):
    """กล้อง Canon, Sony, Nikon อย่างละหนึ่ง ตามด้วยเลนส์หนึ่งรายการ"""
    if limit <= 0:
        return []
    selected = []
    for brand, category in [("Canon", "กล้อง"), ("Sony", "กล้อง"), ("Nikon", "กล้อง"), (None, "เลนส์")]:
        sql = "SELECT * FROM products WHERE hidden = 0 AND category = ?"
        params = [category]
        if brand:
            sql += " AND brand = ?"
            params.append(brand)
        row = db.execute(sql + " ORDER BY product_id LIMIT 1", params).fetchone()
        if row is not None:
            selected.append(row)
        if len(selected) >= limit:
            break
    return _attach_images(db, selected)


def search_products(db, brand="", category="", keyword=""):
    """กรองตามยี่ห้อ/ประเภท/คำค้น เงื่อนไขไหนเว้นว่างแปลว่าไม่กรอง"""
    sql = "SELECT * FROM products WHERE hidden = 0"
    values = []
    if brand:
        sql += " AND brand = ?"
        values.append(brand)
    if category:
        sql += " AND category = ?"
        values.append(category)
    if keyword:
        sql += " AND name LIKE ?"
        values.append(f"%{keyword}%")
    return _attach_images(db, db.execute(sql + " ORDER BY brand, product_id", values).fetchall())


def list_images(db, product_id):
    """รูปของสินค้า (ต้องการ image_id ด้วย ใช้ในหน้าแก้ไข) เรียงตามลำดับ"""
    return db.execute("SELECT * FROM product_images WHERE product_id = ? ORDER BY position, image_id",
                      (product_id,)).fetchall()


# ------------------------------------------------------------------ เพิ่มสินค้าใหม่
def add_product(db, form, image_files):
    """เพิ่มสินค้าใหม่จากฟอร์มของ Admin (ตรวจทุกช่องก่อนบันทึก) พร้อมรูปได้สูงสุดตามที่กำหนด"""
    checker = FormChecker()
    name = checker.check(clean_text, "ชื่อสินค้า", form.get("name"), 100)
    brand = checker.check(clean_choice, "ยี่ห้อ", form.get("brand"), BRANDS)
    category = checker.check(clean_choice, "หมวดหมู่", form.get("category"), CATEGORIES)
    price = checker.check(parse_baht, form.get("price"), "ราคา")
    stock = checker.check(clean_integer, "สต็อกเริ่มต้น", form.get("stock"), 0)
    description = checker.check(clean_description, form.get("description"))
    new_images = checker.check(pick_valid_images, image_files, MAX_IMAGES_PER_PRODUCT)
    checker.raise_if_failed()

    cursor = db.execute(
        "INSERT INTO products (name, brand, category, price, stock, description) VALUES (?, ?, ?, ?, ?, ?)",
        (name, brand, category, price, stock, description),
    )
    _insert_images(db, cursor.lastrowid, new_images)


# ------------------------------------------------------------------ แก้ไขสินค้า
def update_product_details(db, product, form, image_files):
    """
    แก้ชื่อ / รายละเอียด / รูปของสินค้าที่มีอยู่แล้ว (ฟอร์มหน้าแก้ไขของ Admin)
      remove_image   (checkbox หลายอัน)  รูปที่ติ๊ก = ลบทิ้ง
      cover_image_id (radio)             รูปที่เลือก = ตั้งเป็นรูปหลัก
      images         (ไฟล์ใหม่ได้หลายไฟล์) เพิ่มเข้าไป โดยรูปรวมต้องไม่เกินที่กำหนด
    ตรวจข้อมูลทั้งหมดให้ผ่านก่อน แล้วค่อยแก้ฐานข้อมูล (ทำใน Transaction เดียว)
    """
    product_id = product["product_id"]
    current_images = list_images(db, product_id)
    removed_ids = {int(value) for value in form.getlist("remove_image") if value.isdigit()}
    removed_images = [image for image in current_images if image["image_id"] in removed_ids]
    room_left = MAX_IMAGES_PER_PRODUCT - (len(current_images) - len(removed_images))

    checker = FormChecker()
    name = checker.check(clean_text, "ชื่อสินค้า", form.get("name"), 100)
    brand = checker.check(clean_text, "ยี่ห้อ", form.get("brand"), 60)
    category = checker.check(clean_text, "หมวดหมู่", form.get("category"), 60)
    description = checker.check(clean_description, form.get("description"))
    new_images = checker.check(pick_valid_images, image_files, room_left)
    checker.raise_if_failed()

    db.execute("BEGIN")
    try:
        db.execute("UPDATE products SET name = ?, brand = ?, category = ?, description = ? WHERE product_id = ?",
                   (name, brand, category, description, product_id))
        for image in removed_images:
            db.execute("DELETE FROM product_images WHERE image_id = ?", (image["image_id"],))
        _insert_images(db, product_id, new_images)
        _arrange_images(db, product_id, form.get("cover_image_id"))
        db.execute("COMMIT")
    except Exception:
        db.execute("ROLLBACK")
        raise
    for image in removed_images:          # ลบไฟล์จริงหลังฐานข้อมูลบันทึกสำเร็จแล้วเท่านั้น
        delete_image_file(image["filename"])


def _insert_images(db, product_id, uploaded_files):
    """บันทึกไฟล์ใหม่ลงดิสก์ แล้วต่อท้ายลำดับรูปของสินค้า"""
    next_position = db.execute(
        "SELECT COALESCE(MAX(position), -1) + 1 FROM product_images WHERE product_id = ?", (product_id,)
    ).fetchone()[0]
    for offset, uploaded in enumerate(uploaded_files):
        db.execute("INSERT INTO product_images (product_id, filename, position) VALUES (?, ?, ?)",
                   (product_id, save_image_file(uploaded), next_position + offset))


def _arrange_images(db, product_id, cover_image_id_text):
    """ย้ายรูปที่เลือกให้เป็นรูปหลัก (ลำดับ 0) แล้วเรียงเลขลำดับใหม่ให้ต่อเนื่อง 0, 1, 2, ..."""
    image_ids = [image["image_id"] for image in list_images(db, product_id)]
    if cover_image_id_text and cover_image_id_text.isdigit() and int(cover_image_id_text) in image_ids:
        cover_id = int(cover_image_id_text)
        image_ids.remove(cover_id)
        image_ids.insert(0, cover_id)
    for position, image_id in enumerate(image_ids):
        db.execute("UPDATE product_images SET position = ? WHERE image_id = ?", (position, image_id))


# ------------------------------------------------------------------ สต็อก / ราคา
def add_stock(db, product_id, quantity):
    """เติมสต็อก คืน True ถ้าพบสินค้า"""
    result = db.execute(
        "UPDATE products SET stock = stock + ? WHERE product_id = ?", (quantity, product_id)
    )
    return result.rowcount == 1


def set_stock(db, product_id, quantity):
    result = db.execute("UPDATE products SET stock = ? WHERE product_id = ?", (quantity, product_id))
    return result.rowcount == 1


def set_product_hidden(db, product_id, hidden):
    result = db.execute("UPDATE products SET hidden = ? WHERE product_id = ?", (1 if hidden else 0, product_id))
    return result.rowcount == 1


def set_price(db, product_id, price_satang):
    result = db.execute(
        "UPDATE products SET price = ? WHERE product_id = ?", (price_satang, product_id)
    )
    return result.rowcount == 1


# ============================================================================
# ส่วนที่ 13: SERVICE: สมาชิก
#
# ตรรกะเกี่ยวกับสมาชิก: สมัคร, ตรวจรหัสผ่านตอนล็อกอิน, ดึงข้อมูล
# ============================================================================

def _now_text():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def register_member(db, form):
    """
    สมัครสมาชิกใหม่ คืนค่า member_id
    ถ้าข้อมูลผิดจะ raise FormErrors (รวมทุกช่องที่ผิด) ให้หน้าเว็บแสดงผล
    """
    checker = FormChecker()
    first_name = checker.check(clean_name, "ชื่อ", form.get("first_name"))
    last_name = checker.check(clean_name, "นามสกุล", form.get("last_name"))
    birth_date = checker.check(clean_birth_date, form.get("birth_date"))
    phone = checker.check(clean_phone, form.get("phone"))
    password = checker.check(clean_password, form.get("password", ""), form.get("password2", ""))
    if not form.get("consent"):
        checker.add_error("กรุณายอมรับการเก็บและใช้ข้อมูลส่วนบุคคลเพื่อสมัครสมาชิก")
    checker.raise_if_failed()

    now = _now_text()
    try:
        cursor = db.execute(
            "INSERT INTO members (first_name, last_name, birth_date, phone, password_hash, consent_at, created_at)"
            " VALUES (?, ?, ?, ?, ?, ?, ?)",
            (first_name, last_name, birth_date, phone, hash_password(password), now, now),
        )
    except sqlite3.IntegrityError:  # คอลัมน์ phone เป็น UNIQUE จึงสมัครเบอร์ซ้ำไม่ได้
        raise ValidationError("เบอร์โทรนี้สมัครสมาชิกแล้ว กรุณาเข้าสู่ระบบ")
    return cursor.lastrowid


def verify_login(db, phone, password):
    """ตรวจเบอร์+รหัสผ่าน ถูกต้องคืน member_id ผิดคืน None"""
    member = db.execute("SELECT member_id, password_hash FROM members WHERE phone = ?", (phone,)).fetchone()
    if member is None:
        verify_unknown_user(password)  # ใช้เวลาเท่ากัน ไม่เผยว่าเบอร์นี้มีในระบบหรือไม่
        return None
    return member["member_id"] if verify_password(member["password_hash"], password) else None


def get_member(db, member_id):
    return db.execute("SELECT * FROM members WHERE member_id = ?", (member_id,)).fetchone()


def list_members_with_sales(db):
    """รายชื่อสมาชิก + จำนวนออเดอร์ + ยอดซื้อรวม (เฉพาะออเดอร์ที่ชำระแล้ว) สำหรับหน้า Admin"""
    return db.execute(
        "SELECT m.*, COUNT(o.order_id) AS orders_count, COALESCE(SUM(o.final_amount), 0) AS spent "
        "FROM members m "
        "LEFT JOIN orders o ON o.member_id = m.member_id AND o.status = 'paid' "
        "GROUP BY m.member_id ORDER BY m.member_id DESC"
    ).fetchall()


# ============================================================================
# ส่วนที่ 14: SERVICE: โค้ดส่วนลด
#
# ตรรกะโค้ดส่วนลด
# ============================================================================

def find_coupon(db, code):
    return db.execute("SELECT * FROM coupons WHERE code = ?", (code,)).fetchone()


def list_coupons(db):
    return db.execute("SELECT * FROM coupons ORDER BY code").fetchall()


def calculate_discount(coupon, subtotal):
    """
    คำนวณส่วนลดเป็นสตางค์ ถ้าใช้โค้ดนี้ไม่ได้จะ raise ShopError
    กฎสำคัญ: ส่วนลดต้องไม่เกินยอดรวมสินค้า (ยอดสุทธิจะได้ไม่ติดลบ)
    """
    if coupon is None or not coupon["enabled"]:
        raise ShopError("โค้ดส่วนลดนี้ถูกปิดใช้งานหรือไม่มีอยู่")
    if coupon["expires_at"] and coupon["expires_at"] < date.today().isoformat():
        raise ShopError("โค้ดส่วนลดนี้หมดอายุแล้ว")
    if subtotal < coupon["min_spend"]:
        raise ShopError(f"ยอดซื้อไม่ถึงขั้นต่ำ {format_baht(coupon['min_spend'])} บาท")

    if coupon["discount_type"] == "percent":
        discount = round(subtotal * coupon["value"] / 100)
    else:
        discount = int(coupon["value"])
    return min(discount, subtotal)


def create_coupon(db, form):
    """สร้างหรือแก้ไขโค้ดส่วนลด รวมวันหมดอายุ"""
    checker = FormChecker()
    code = (form.get("code") or "").strip().upper()
    if not code or " " in code or len(code) > 40:
        checker.add_error("ชื่อโค้ดต้องไม่ว่าง ไม่มีช่องว่าง และยาวไม่เกิน 40 ตัวอักษร")
    kind = checker.check(clean_choice, "ประเภทส่วนลด", form.get("discount_type"), ["percent", "fixed"])
    value = checker.check(parse_baht, form.get("value"), "ส่วนลด")
    min_spend = checker.check(parse_baht, form.get("min_spend"), "ยอดซื้อขั้นต่ำ")
    expires_at = (form.get("expires_at") or "").strip()
    if expires_at:
        try: date.fromisoformat(expires_at)
        except ValueError: checker.add_error("วันหมดอายุไม่ถูกต้อง")
    enabled = 1 if form.get("enabled") == "on" else 0
    checker.raise_if_failed()
    if kind == "percent":
        value = value / 100
        if value > 100: raise ValidationError("ส่วนลดเปอร์เซ็นต์ต้องไม่เกิน 100")
    try:
        db.execute("INSERT INTO coupons (code, discount_type, value, min_spend, enabled, expires_at) VALUES (?, ?, ?, ?, ?, ?) "
                   "ON CONFLICT(code) DO UPDATE SET discount_type=excluded.discount_type, value=excluded.value, "
                   "min_spend=excluded.min_spend, enabled=excluded.enabled, expires_at=excluded.expires_at",
                   (code, kind, value, min_spend, enabled, expires_at))
    except sqlite3.IntegrityError:
        raise ValidationError("บันทึกโค้ดส่วนลดไม่สำเร็จ")
    return code


def cancel_order(db, order_id, member_id=None):
    """ยกเลิกออเดอร์ที่ยังไม่ชำระเงินและคืนสต็อกแบบ transaction ป้องกันคืนซ้ำ"""
    db.execute("BEGIN IMMEDIATE")
    try:
        sql = "SELECT * FROM orders WHERE order_id = ?"
        params = [order_id]
        if member_id is not None:
            sql += " AND member_id = ?"
            params.append(member_id)
        order = db.execute(sql, params).fetchone()
        if order is None: raise ShopError("ไม่พบคำสั่งซื้อ")
        if order["status"] == "cancelled": raise ShopError("คำสั่งซื้อนี้ถูกยกเลิกแล้ว")
        if order["status"] == STATUS_PAID: raise ShopError("ไม่สามารถยกเลิกคำสั่งซื้อที่ชำระเงินแล้วได้")
        for item in db.execute("SELECT product_id, quantity FROM order_items WHERE order_id = ?", (order_id,)).fetchall():
            db.execute("UPDATE products SET stock = stock + ? WHERE product_id = ?", (item["quantity"], item["product_id"]))
        db.execute("UPDATE orders SET status = 'cancelled' WHERE order_id = ?", (order_id,))
        db.execute("COMMIT")
        return True
    except Exception:
        db.execute("ROLLBACK")
        raise


# ============================================================================
# ส่วนที่ 15: SERVICE: ตะกร้าสินค้า
#
# ตรรกะตะกร้าสินค้า
#
# ตะกร้าคือ dict ธรรมดาที่เก็บใน session ของลูกค้า:  {"รหัสสินค้า": จำนวน}
# เช่น {"1": 2, "6": 1} = สินค้ารหัส 1 จำนวน 2 ชิ้น และรหัส 6 จำนวน 1 ชิ้น
# ฟังก์ชันในไฟล์นี้แก้ dict ที่ส่งเข้ามา แล้วให้ฝั่งหน้าเว็บเป็นคนบันทึกกลับลง session
# ============================================================================

def add_to_cart(db, cart, product_id_text, quantity_text):
    """เพิ่มสินค้าลงตะกร้า (ตรวจสต็อกรวมกับที่อยู่ในตะกร้าแล้ว) คืนข้อมูลสินค้าที่เพิ่ม"""
    product_id = clean_integer("รหัสสินค้า", product_id_text, 1)
    quantity = clean_integer("จำนวน", quantity_text, 1)

    product = get_product(db, product_id)
    if product is None or product["hidden"]:
        raise ShopError("ไม่พบสินค้าหรือสินค้านี้ถูกซ่อน")

    already_in_cart = cart.get(str(product_id), 0)
    if already_in_cart + quantity > product["stock"]:
        raise ShopError(
            f"สต็อกไม่พอ: '{product['name']}' คงเหลือ {product['stock']} ชิ้น "
            f"(ในตะกร้าแล้ว {already_in_cart} ชิ้น)"
        )
    cart[str(product_id)] = already_in_cart + quantity
    return product


def set_quantity(db, cart, product_id_text, quantity_text):
    """ตั้งจำนวนใหม่ของสินค้าในตะกร้า (ใส่ 0 = ลบออก)"""
    product_id = clean_integer("รหัสสินค้า", product_id_text, 1)
    quantity = clean_integer("จำนวน", quantity_text, 0)
    if str(product_id) not in cart:
        return
    if quantity == 0:
        del cart[str(product_id)]
        return
    product = get_product(db, product_id)
    if product is None or quantity > product["stock"]:
        stock = product["stock"] if product else 0
        raise ShopError(f"สต็อกไม่พอ: คงเหลือ {stock} ชิ้น")
    cart[str(product_id)] = quantity


def build_cart_summary(db, cart, coupon_code):
    """
    อ่านตะกร้ามาคำนวณราคา คืน dict สำหรับแสดงหน้าตะกร้า/ชำระเงิน
      lines       รายการสินค้า (สินค้า p, จำนวน qty, ราคารวมต่อรายการ line)
      subtotal    ยอดรวมสินค้า    discount ส่วนลด    final ยอดสุทธิ
      coupon_err  ข้อความ error ถ้าโค้ดที่ใส่ไว้ใช้ไม่ได้
      notices     ข้อความแจ้งว่าระบบปรับตะกร้าตามสต็อกจริง

    ระหว่างทางจะ "ซ่อมตะกร้า": สินค้าที่หมดสต็อกถูกเอาออก จำนวนที่เกินสต็อกถูกลดลง
    """
    lines, subtotal, notices = [], 0, []
    for product_id, quantity in list(cart.items()):
        product = get_product(db, int(product_id))
        if product is None or product["hidden"] or product["stock"] == 0:
            del cart[product_id]
            notices.append("มีสินค้าในตะกร้าที่หมดแล้ว ระบบนำออกให้")
            continue
        if quantity > product["stock"]:
            quantity = cart[product_id] = product["stock"]
            notices.append(f"ปรับจำนวน '{product['name']}' เหลือ {quantity} ชิ้นตามสต็อกคงเหลือ")
        line_total = product["price"] * quantity
        subtotal += line_total
        lines.append({"p": product, "qty": quantity, "line": line_total})

    discount, coupon_error = 0, None
    if coupon_code:
        try:
            discount = calculate_discount(find_coupon(db, coupon_code), subtotal)
        except ShopError as error:
            coupon_error = str(error)

    return {"lines": lines, "subtotal": subtotal, "discount": discount,
            "final": subtotal - discount, "coupon": coupon_code,
            "coupon_err": coupon_error, "notices": notices}


# ============================================================================
# ส่วนที่ 16: SERVICE: คำสั่งซื้อ
#
# ตรรกะคำสั่งซื้อ: ตรวจข้อมูลผู้ซื้อ, สร้างคำสั่งซื้อ (หัวใจของระบบ), ดู/ยืนยันการชำระเงิน
# ============================================================================

# ---------------------------------------------------------------- ข้อมูลผู้ซื้อ
def read_checkout_form(form):
    """
    ตรวจฟอร์มหน้าชำระเงิน คืน (ข้อมูลผู้ซื้อ, วิธีชำระเงิน)
    ถ้ามีช่องผิดจะ raise FormErrors
    """
    checker = FormChecker()
    name = checker.check(clean_text, "ชื่อผู้รับ", form.get("buyer_name"), 100)
    phone = checker.check(clean_phone, form.get("buyer_phone"))
    fulfillment = checker.check(clean_choice, "วิธีรับสินค้า", form.get("fulfillment", "delivery"), ["delivery", "pickup"])
    address = "รับสินค้าที่หน้าร้าน: " + SHOP_INFO["address"] if fulfillment == "pickup" else checker.check(clean_address, form.get("shipping_address"))
    method = checker.check(clean_choice, "วิธีชำระเงิน", form.get("payment"), list(PAYMENT_METHODS))
    checker.raise_if_failed()
    return {"name": name, "phone": phone, "address": address, "fulfillment": fulfillment}, method


def initial_status(payment_method, final_amount):
    """ยอดศูนย์ชำระแล้ว; COD รอเก็บเงิน; QR และบัตรรอผลชำระเงินจริง"""
    if final_amount == 0:
        return STATUS_PAID
    return "cod_pending" if payment_method == "cod" else STATUS_PENDING


# ---------------------------------------------------------------- สร้างคำสั่งซื้อ
def place_order(db, member_id, cart, coupon_code, buyer, payment_method):
    """
    สร้างคำสั่งซื้อ คืน order_id

    ทุกขั้นตอนอยู่ใน "Transaction" เดียว = สำเร็จทั้งหมด หรือยกเลิกทั้งหมด (ไม่มีครึ่งๆ กลางๆ)
      BEGIN IMMEDIATE  ล็อกฐานข้อมูลสำหรับเขียน คนอื่นต้องรอ (กัน 2 คนซื้อชิ้นสุดท้ายพร้อมกัน)
      ...ทำงานหลายขั้น...
      COMMIT           บันทึกถาวร
      ROLLBACK         ถ้าพลาดตรงไหน ยกเลิกทุกอย่างที่ทำมา (เช่น ไม่ให้สต็อกหายโดยไม่มียอดขาย)
    """
    db.execute("BEGIN IMMEDIATE")
    try:
        lines = _read_lines_and_check_stock(db, cart)
        subtotal = sum(line["unit_price"] * line["quantity"] for line in lines)
        discount = _discount_for(db, coupon_code, subtotal)
        final_amount = subtotal - discount

        order_id = _insert_order(db, member_id, buyer, payment_method,
                                 subtotal, discount, final_amount)
        for line in lines:
            _insert_item_and_cut_stock(db, order_id, line)

        db.execute("COMMIT")
        return order_id
    except Exception:
        db.execute("ROLLBACK")
        raise


def _read_lines_and_check_stock(db, cart):
    """อ่านราคา/สต็อก "ล่าสุด" จากฐานข้อมูลอีกครั้ง (Double Check) ไม่เชื่อข้อมูลเก่าในตะกร้า"""
    if not cart:
        raise ShopError("ตะกร้าว่างเปล่า")
    lines = []
    for product_id, quantity in cart.items():
        product = db.execute("SELECT * FROM products WHERE product_id = ?", (int(product_id),)).fetchone()
        if product is None or product["hidden"]:
            raise ShopError("มีสินค้าในตะกร้าที่ไม่มีในระบบหรือถูกซ่อนแล้ว")
        if product["stock"] < quantity:
            raise ShopError(f"'{product['name']}' มีสต็อกไม่พอ (เหลือ {product['stock']} ชิ้น)")
        lines.append({"product_id": product["product_id"], "quantity": quantity,
                      "unit_price": product["price"]})
    return lines


def _discount_for(db, coupon_code, subtotal):
    if not coupon_code:
        return 0
    return calculate_discount(find_coupon(db, coupon_code), subtotal)


def _insert_order(db, member_id, buyer, payment_method, subtotal, discount, final_amount):
    cursor = db.execute(
        "INSERT INTO orders (order_date, total_amount, discount_amount, final_amount, payment_method,"
        " member_id, buyer_name, buyer_phone, shipping_address, status, fulfillment)"
        " VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        (datetime.now().strftime("%Y-%m-%d %H:%M:%S"), subtotal, discount, final_amount, payment_method,
         member_id, buyer["name"], buyer["phone"], buyer["address"],
         initial_status(payment_method, final_amount), buyer.get("fulfillment", "delivery")),
    )
    return cursor.lastrowid


def _insert_item_and_cut_stock(db, order_id, line):
    db.execute(
        "INSERT INTO order_items (order_id, product_id, quantity, unit_price) VALUES (?, ?, ?, ?)",
        (order_id, line["product_id"], line["quantity"], line["unit_price"]),
    )
    # "AND stock >= ?" = ด่านป้องกันสุดท้าย ถ้าสต็อกไม่พอจะไม่มีแถวถูกแก้ -> rowcount เป็น 0
    result = db.execute(
        "UPDATE products SET stock = stock - ? WHERE product_id = ? AND stock >= ?",
        (line["quantity"], line["product_id"], line["quantity"]),
    )
    if result.rowcount != 1:
        raise ShopError("ตัดสต็อกไม่สำเร็จ สินค้าอาจถูกซื้อไปแล้ว")


# ---------------------------------------------------------------- ดูข้อมูล
def get_order(db, order_id):
    return db.execute("SELECT * FROM orders WHERE order_id = ?", (order_id,)).fetchone()


def get_order_items(db, order_id):
    return db.execute(
        "SELECT oi.*, p.name FROM order_items oi JOIN products p USING (product_id) WHERE oi.order_id = ?",
        (order_id,),
    ).fetchall()


def group_items_by_order(db, orders):
    """คืน dict {order_id: [รายการสินค้า]} ของ orders ที่ส่งมา (ใช้แสดงในตารางหลายบิล)"""
    items = {}
    for order in orders:
        items[order["order_id"]] = get_order_items(db, order["order_id"])
    return items


def list_member_orders(db, member_id):
    return db.execute("SELECT * FROM orders WHERE member_id = ? ORDER BY order_id DESC", (member_id,)).fetchall()


def list_all_orders(db):
    return db.execute("SELECT * FROM orders ORDER BY order_id DESC").fetchall()


def sales_totals(db):
    """คืน (ยอดขายที่ชำระแล้ว, ยอดที่รอชำระ) เป็นสตางค์"""
    def total_for(status):
        row = db.execute("SELECT COALESCE(SUM(final_amount), 0) FROM orders WHERE status = ?", (status,)).fetchone()
        return row[0]
    return total_for(STATUS_PAID), db.execute("SELECT COALESCE(SUM(final_amount),0) FROM orders WHERE status IN ('pending','review','cod_pending')").fetchone()[0]


def confirm_payment(db, order_id):
    """Admin ตรวจสอบเงินเข้าแล้ว กดยืนยัน คืน True ถ้ามีออเดอร์ที่รอชำระอยู่จริง"""
    result = db.execute(
        "UPDATE orders SET status = ? WHERE order_id = ? AND "
        "((payment_method = 'promptpay' AND status = 'review' AND slip_file != '') "
        "OR (payment_method = 'cod' AND status IN ('pending', 'cod_pending')))",
        (STATUS_PAID, order_id),
    )
    return result.rowcount == 1



# ============================================================================
# ส่วนที่ 17: เว็บร้านค้า (ฝั่งลูกค้า)
#
# เว็บร้านค้า (ฝั่งลูกค้า)  ->  http://127.0.0.1:5000
#
# ไฟล์นี้มีหน้าที่แค่ "รับคำขอจากเบราว์เซอร์ -> เรียก service ทำงาน -> ส่งหน้าเว็บกลับ"
# ตรรกะจริงๆ (ตรวจข้อมูล, คิดเงิน, สร้างออเดอร์) อยู่ในโฟลเดอร์ services/ และ core/
#
# แบ่งเป็นหมวด:  1) ตัวช่วย  2) หน้าสินค้า  3) สมาชิก  4) ตะกร้า  5) ชำระเงิน/คำสั่งซื้อ
# ============================================================================

shop = create_flask_app("shop", os.path.join(ROOT_DIR, "templates_shop"))
shop_login_throttle = LoginThrottle()


# =============================================================== 1) ตัวช่วย
@shop.context_processor
def shop_template_variables():
    """ตัวแปรที่ทุกหน้า (template) ใช้ได้เลย โดยไม่ต้องส่งทีละหน้า"""
    member = None
    if session.get("member_id"):
        member = get_member(get_db(), session["member_id"])
        if member is None:                       # สมาชิกถูกลบไปแล้ว
            session.pop("member_id", None)
    return {
        "member": member,
        "cart_count": sum(session.get("cart", {}).values()),
        "shop_info": SHOP_INFO,
        "brands": BRANDS,
        "categories": CATEGORIES,
        "today": date.today().isoformat(),   # ใช้จำกัดวันเกิดในฟอร์มสมัครสมาชิก
    }


def member_required(view):
    """ตัวครอบ (decorator): หน้าที่ติดตัวนี้ต้องล็อกอินก่อน ไม่งั้นส่งไปหน้าเข้าสู่ระบบ"""
    @wraps(view)
    def wrapper(*args, **kwargs):
        if not session.get("member_id"):
            flash("กรุณาเข้าสู่ระบบก่อนสั่งซื้อสินค้า", "warning")
            return redirect(url_for("login", next=request.path))
        return view(*args, **kwargs)
    return wrapper


def login_member(member_id):
    """
    บันทึกว่าล็อกอินแล้ว: ล้าง session เก่าทิ้งก่อน (กัน session fixation)
    แต่เก็บตะกร้าและโค้ดส่วนลดไว้ ให้ลูกค้าไม่ต้องเริ่มเลือกของใหม่
    """
    kept = {key: session[key] for key in ("cart", "coupon") if key in session}
    session.clear()
    session.update(kept)
    session["member_id"] = member_id


def get_own_order_or_404(order_id):
    """ดึงออเดอร์ที่เป็นของสมาชิกที่ล็อกอินอยู่เท่านั้น (ดูของคนอื่นไม่ได้)"""
    order = get_order(get_db(), order_id)
    if order is None or order["member_id"] != session["member_id"]:
        abort(404)
    return order


def save_cart(cart, notices=()):
    session["cart"] = cart                 # ต้องกำหนดกลับเอง เพื่อให้ Flask รู้ว่า session เปลี่ยน
    for notice in notices:
        flash(notice, "warning")


# =============================================================== 2) หน้าสินค้า
@shop.get("/")
def home():
    featured = featured_products(get_db(), FEATURED_COUNT)
    return render_template("index.html", products=featured)


@shop.get("/products")
def products():
    brand = request.args.get("brand", "")
    category = request.args.get("category", "")
    keyword = request.args.get("q", "").strip()
    found = search_products(get_db(), brand, category, keyword)
    db = get_db()
    brands = [r[0] for r in db.execute("SELECT DISTINCT brand FROM products WHERE hidden=0 ORDER BY brand")]
    categories = [r[0] for r in db.execute("SELECT DISTINCT category FROM products WHERE hidden=0 ORDER BY category")]
    return render_template("products.html", products=found, brand=brand, category=category, keyword=keyword, brands=brands, categories=categories)


@shop.get("/contact")
def contact():
    return render_template("contact.html")


# =============================================================== 3) สมาชิก
@shop.route("/register", methods=["GET", "POST"])
def register():
    if session.get("member_id"):
        return redirect(url_for("account"))
    entered = {}
    if request.method == "POST":
        entered = request.form
        try:
            member_id = register_member(get_db(), request.form)
        except USER_ERRORS as error:
            flash_errors(error)
        else:
            login_member(member_id)
            flash("สมัครสมาชิกสำเร็จ ยินดีต้อนรับ", "success")
            return redirect(safe_redirect_target(request.values.get("next"), url_for("home")))
    return render_template("register.html", v=entered)


@shop.route("/login", methods=["GET", "POST"])
def login():
    if session.get("member_id"):
        return redirect(url_for("account"))
    phone = ""
    if request.method == "POST":
        phone = request.form.get("phone", "")
        try:
            phone = clean_phone(phone)
            throttle_key = f"{request.remote_addr}|{phone}"
            if shop_login_throttle.is_locked(throttle_key):
                raise ShopError("ใส่รหัสผิดหลายครั้งเกินไป กรุณารอ 5 นาทีแล้วลองใหม่")
            member_id = verify_login(get_db(), phone, request.form.get("password", ""))
            if member_id is None:
                shop_login_throttle.record_failure(throttle_key)
                raise ShopError("เบอร์โทรหรือรหัสผ่านไม่ถูกต้อง")
        except USER_ERRORS as error:
            flash_errors(error)
        else:
            shop_login_throttle.reset(throttle_key)
            login_member(member_id)
            return redirect(safe_redirect_target(request.values.get("next"), url_for("home")))
    return render_template("login.html", phone=phone)


@shop.post("/logout")
def logout():
    session.pop("member_id", None)
    flash("ออกจากระบบแล้ว", "info")
    return redirect(url_for("home"))


@shop.get("/account")
@member_required
def account():
    db = get_db()
    orders = list_member_orders(db, session["member_id"])
    return render_template("account.html", me=get_member(db, session["member_id"]), orders=orders)


@shop.post("/account/profile")
@member_required
def update_profile():
    db = get_db()
    try:
        checker = FormChecker()
        first = checker.check(clean_name, "ชื่อ", request.form.get("first_name"))
        last = checker.check(clean_name, "นามสกุล", request.form.get("last_name"))
        birth = checker.check(clean_birth_date, request.form.get("birth_date"))
        phone = checker.check(clean_phone, request.form.get("phone"))
        checker.raise_if_failed()
        db.execute("UPDATE members SET first_name=?, last_name=?, birth_date=?, phone=? WHERE member_id=?",
                   (first, last, birth, phone, session["member_id"]))
        flash("บันทึกข้อมูลส่วนตัวแล้ว", "success")
    except sqlite3.IntegrityError:
        flash("เบอร์โทรนี้ถูกใช้แล้ว", "danger")
    except USER_ERRORS as error:
        flash_errors(error)
    return redirect(url_for("account"))


@shop.post("/account/password")
@member_required
def change_password():
    db = get_db()
    try:
        me = get_member(db, session["member_id"])
        if not verify_password(me["password_hash"], request.form.get("old_password", "")):
            raise ValidationError("รหัสผ่านเดิมไม่ถูกต้อง")
        password = clean_password(request.form.get("password", ""), request.form.get("password2", ""))
        db.execute("UPDATE members SET password_hash=? WHERE member_id=?", (hash_password(password), me["member_id"]))
        session.pop("_csrf", None)
        flash("เปลี่ยนรหัสผ่านแล้ว", "success")
    except USER_ERRORS as error:
        flash_errors(error)
    return redirect(url_for("account"))


# =============================================================== 4) ตะกร้า (ต้องล็อกอินทุกหน้า)
@shop.post("/cart/add")
@member_required
def cart_add():
    cart = session.get("cart", {})
    try:
        product = add_to_cart(get_db(), cart, request.form.get("product_id"), request.form.get("qty"))
    except USER_ERRORS as error:
        flash_errors(error)
    else:
        save_cart(cart)
        flash(f"เพิ่ม '{product['name']}' ลงตะกร้าแล้ว", "success")
    return redirect(request.referrer or url_for("products"))


@shop.get("/cart")
@member_required
def cart_view():
    cart = session.get("cart", {})
    summary = build_cart_summary(get_db(), cart, session.get("coupon"))
    save_cart(cart, summary["notices"])
    return render_template("cart.html", s=summary)


@shop.post("/cart/update")
@member_required
def cart_update():
    cart = session.get("cart", {})
    try:
        set_quantity(get_db(), cart, request.form.get("product_id"), request.form.get("qty"))
    except USER_ERRORS as error:
        flash_errors(error)
    else:
        save_cart(cart)
    return redirect(url_for("cart_view"))


@shop.post("/cart/coupon")
@member_required
def cart_coupon():
    code = request.form.get("code", "").strip().upper()
    if not code:
        session.pop("coupon", None)
        flash("ยกเลิกโค้ดส่วนลดแล้ว", "info")
        return redirect(url_for("cart_view"))

    summary = build_cart_summary(get_db(), session.get("cart", {}), code)
    if summary["coupon_err"]:
        flash(summary["coupon_err"], "danger")
    else:
        session["coupon"] = code
        flash(f"ใช้โค้ด {code} สำเร็จ", "success")
    return redirect(url_for("cart_view"))


# =============================================================== 5) ชำระเงิน / คำสั่งซื้อ
@shop.route("/checkout", methods=["GET", "POST"])
@member_required
def checkout():
    db = get_db()
    cart = session.get("cart", {})
    summary = build_cart_summary(db, cart, session.get("coupon"))
    save_cart(cart, summary["notices"])
    if not summary["lines"]:
        flash("ตะกร้าว่างเปล่า", "warning")
        return redirect(url_for("products"))
    if summary["coupon_err"]:
        flash(f"โค้ด {summary['coupon']}: {summary['coupon_err']}", "danger")
        return redirect(url_for("cart_view"))

    me = get_member(db, session["member_id"])
    form_values = {"buyer_name": f"{me['first_name']} {me['last_name']}", "buyer_phone": me["phone"],
                   "shipping_address": "", "payment": "promptpay"}
    qr_ready = bool(get_setting(db, PROMPTPAY_ID_KEY) or get_setting(db, PROMPTPAY_IMAGE_KEY))

    if request.method == "POST":
        form_values = request.form
        try:
            buyer, method = read_checkout_form(request.form)
            if method == "promptpay" and not qr_ready:
                raise ShopError("ร้านยังไม่ได้ตั้งค่า PromptPay กรุณาเลือกวิธีชำระเงินอื่น")
            order_id = place_order(db, session["member_id"], cart,
                                                 session.get("coupon"), buyer, method)
        except FormErrors as error:
            flash_errors(error)                     # กรอกผิด -> แสดงฟอร์มเดิมพร้อมข้อความ
        except ShopError as error:
            flash_errors(error)                     # สต็อกไม่พอ ฯลฯ -> กลับไปแก้ที่ตะกร้า
            return redirect(url_for("cart_view"))
        else:
            session.pop("cart", None)
            session.pop("coupon", None)
            if method == "promptpay" and get_order(db, order_id)["status"] != STATUS_PAID:
                return redirect(url_for("pay_with_qr", order_id=order_id))
            if method == "card" and get_order(db, order_id)["status"] != STATUS_PAID:
                return redirect(url_for("pay_card", order_id=order_id))
            flash("สั่งซื้อสำเร็จ", "success")
            return redirect(url_for("order_receipt", order_id=order_id))

    return render_template("checkout.html", s=summary, v=form_values, qr_ready=qr_ready,
                           payment_methods=PAYMENT_METHODS)


@shop.get("/orders/<int:order_id>/pay")
@member_required
def pay_with_qr(order_id):
    """หน้าแสดง QR PromptPay ตามยอดของออเดอร์ ให้ลูกค้าสแกนจ่ายด้วยแอพธนาคาร"""
    order = get_own_order_or_404(order_id)
    if order["payment_method"] != "promptpay" or order["status"] not in (STATUS_PENDING, "review"):
        return redirect(url_for("order_detail", order_id=order_id))

    promptpay_id = get_setting(get_db(), PROMPTPAY_ID_KEY)
    qr_svg, qr_problem = None, None
    qr_image = get_setting(get_db(), PROMPTPAY_IMAGE_KEY)
    if qr_image:
        return render_template("pay_qr.html", order=order, qr_svg=None, qr_image=qr_image, qr_problem=None)
    if not promptpay_id:
        qr_problem = "ร้านยังไม่ได้ตั้งค่า PromptPay กรุณาติดต่อร้าน"
    else:
        try:
            qr_svg = make_qr_svg(build_payload(promptpay_id, order["final_amount"]))
        except QrUnavailable as error:
            qr_problem = str(error)
    return render_template("pay_qr.html", order=order, qr_svg=qr_svg, qr_image=None, qr_problem=qr_problem)


@shop.post("/orders/<int:order_id>/cancel")
@member_required
def customer_cancel_order(order_id):
    try:
        cancel_order(get_db(), order_id, session["member_id"])
        flash("ยกเลิกคำสั่งซื้อและคืนสต็อกแล้ว", "success")
    except USER_ERRORS as error: flash_errors(error)
    return redirect(url_for("order_detail", order_id=order_id))


@shop.get("/orders/<int:order_id>/receipt")
@member_required
def order_receipt(order_id):
    order = get_own_order_or_404(order_id)
    return render_template("receipt.html", order=order, items=get_order_items(get_db(), order_id))


@shop.get("/orders/<int:order_id>")
@member_required
def order_detail(order_id):
    order = get_own_order_or_404(order_id)
    return render_template("order_detail.html", order=order, items=get_order_items(get_db(), order_id))



# =============================================================== เริ่มโปรแกรม


# ============================================================================
# ส่วนที่ 18: เว็บผู้ดูแลระบบ (Admin)
#
# เว็บผู้ดูแลระบบ (Admin)  ->  http://127.0.0.1:5001
# เปิดรับเฉพาะเครื่องตัวเอง (127.0.0.1) เป็นค่าเริ่มต้น
#
# ไฟล์นี้เป็นแค่ชั้นหน้าเว็บ ตรรกะจริงอยู่ใน services/ (เหมือน shop_app.py)
# ============================================================================

SHOP_URL = os.environ.get("SHOP_URL", "http://127.0.0.1:5000")

admin = create_flask_app("admin", os.path.join(ROOT_DIR, "templates_admin"))
admin_login_throttle = LoginThrottle()


@admin.context_processor
def admin_template_variables():
    return {"is_admin": session.get("admin", False), "shop_url": SHOP_URL}


def admin_required(view):
    """หน้าที่ติดตัวนี้ต้องล็อกอิน Admin ก่อน"""
    @wraps(view)
    def wrapper(*args, **kwargs):
        if not session.get("admin"):
            return redirect(url_for("admin_login", next=request.path))
        return view(*args, **kwargs)
    return wrapper


def password_is_correct(typed_password):
    """เทียบรหัสผ่านแบบ constant-time (ใช้เวลาเท่ากันไม่ว่าผิดตรงไหน) กันการจับเวลาเดารหัส"""
    typed = hashlib.sha256(typed_password.encode()).digest()
    real = hashlib.sha256(ADMIN_PASSWORD.encode()).digest()
    return hmac.compare_digest(typed, real)


# =============================================================== เข้า/ออกระบบ
@admin.route("/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        throttle_key = request.remote_addr or "unknown"
        if admin_login_throttle.is_locked(throttle_key):
            flash("ใส่รหัสผิดหลายครั้งเกินไป กรุณารอ 5 นาทีแล้วลองใหม่", "danger")
        elif password_is_correct(request.form.get("password", "")):
            admin_login_throttle.reset(throttle_key)
            session.clear()
            session["admin"] = True
            return redirect(safe_redirect_target(request.args.get("next"), url_for("admin_dashboard")))
        else:
            admin_login_throttle.record_failure(throttle_key)
            flash("รหัสผ่านไม่ถูกต้อง", "danger")
    return render_template("admin_login.html")


@admin.get("/")
def admin_home():
    return redirect(url_for("admin_dashboard"))


@admin.post("/logout")
def admin_logout():
    session.clear()
    return redirect(url_for("admin_login"))


# =============================================================== สินค้า / สต็อก / ราคา
@admin.get("/dashboard")
@admin_required
def admin_dashboard():
    db = get_db()
    period = request.args.get("period", "day")
    if period not in ("day", "month", "year"):
        period = "day"
    formats = {"day": "%Y-%m-%d", "month": "%Y-%m", "year": "%Y"}
    rows = db.execute("SELECT strftime(?, order_date) AS label, COUNT(*) AS count, SUM(final_amount) AS revenue "
                      "FROM orders WHERE status='paid' GROUP BY label ORDER BY label DESC LIMIT 30",
                      (formats[period],)).fetchall()
    now = datetime.now()
    totals = []
    for key, label in (("day", "วันนี้"), ("month", "เดือนนี้"), ("year", "ปีนี้")):
        value = db.execute("SELECT COALESCE(SUM(final_amount),0) FROM orders WHERE status='paid' AND strftime(?,order_date)=?",
                           (formats[key], now.strftime(formats[key]))).fetchone()[0]
        totals.append((label, value))
    return render_template("admin_dashboard.html", rows=rows, totals=totals, period=period,
                           peak=max([r["revenue"] for r in rows] or [1]) or 1)


@admin.get("/products")
@admin_required
def admin_products():
    db = get_db()
    brands = sorted(set(BRANDS + [r[0] for r in db.execute("SELECT DISTINCT brand FROM products")]))
    categories = sorted(set(CATEGORIES + [r[0] for r in db.execute("SELECT DISTINCT category FROM products")]))
    return render_template("admin_products.html", products=list_products(db), brands=brands, categories=categories)


@admin.post("/products/add")
@admin_required
def admin_add_product():
    try:
        add_product(get_db(), request.form, request.files.getlist("images"))
        flash("เพิ่มสินค้าใหม่สำเร็จ", "success")
    except USER_ERRORS as error:
        flash_errors(error)
    return redirect(url_for("admin_products"))


@admin.route("/products/<int:product_id>/edit", methods=["GET", "POST"])
@admin_required
def admin_edit_product(product_id):
    """หน้าแก้ไขชื่อ / รายละเอียด / รูปของสินค้า"""
    db = get_db()
    product = get_product(db, product_id)
    if product is None:
        abort(404)
    if request.method == "POST":
        try:
            update_product_details(db, product, request.form, request.files.getlist("images"))
            flash("บันทึกข้อมูลสินค้าแล้ว", "success")
            return redirect(url_for("admin_products"))
        except USER_ERRORS as error:
            flash_errors(error)
    return render_template("admin_product_edit.html", product=product,
                           images=list_images(db, product_id), max_images=MAX_IMAGES_PER_PRODUCT)


@admin.post("/products/<int:product_id>/restock")
@admin_required
def admin_restock(product_id):
    try:
        quantity = clean_integer("จำนวนที่เติม", request.form.get("qty"), 1)
        found = add_stock(get_db(), product_id, quantity)
        flash("เติมสต็อกสำเร็จ" if found else "ไม่พบสินค้า", "success" if found else "danger")
    except USER_ERRORS as error:
        flash_errors(error)
    return redirect(url_for("admin_products"))


@admin.post("/products/<int:product_id>/stock")
@admin_required
def admin_set_stock(product_id):
    try:
        quantity = clean_integer("สต็อกใหม่", request.form.get("stock"), 0)
        found = set_stock(get_db(), product_id, quantity)
        flash("ตั้งสต็อกใหม่สำเร็จ" if found else "ไม่พบสินค้า", "success" if found else "danger")
    except USER_ERRORS as error: flash_errors(error)
    return redirect(url_for("admin_products"))


@admin.post("/products/<int:product_id>/visibility")
@admin_required
def admin_product_visibility(product_id):
    hidden = request.form.get("hidden") == "1"
    if set_product_hidden(get_db(), product_id, hidden): flash("ซ่อน/แสดงสินค้าเรียบร้อย", "success")
    else: flash("ไม่พบสินค้า", "danger")
    return redirect(url_for("admin_products"))


@admin.post("/products/<int:product_id>/price")
@admin_required
def admin_price(product_id):
    try:
        price = parse_baht(request.form.get("price"), "ราคา")
        found = set_price(get_db(), product_id, price)
        flash("ปรับราคาสำเร็จ" if found else "ไม่พบสินค้า", "success" if found else "danger")
    except USER_ERRORS as error:
        flash_errors(error)
    return redirect(url_for("admin_products"))


# =============================================================== โปรโมชั่น
@admin.route("/coupons", methods=["GET", "POST"])
@admin_required
def admin_coupons():
    if request.method == "POST":
        try:
            code = create_coupon(get_db(), request.form)
            flash(f"สร้างโค้ด {code} สำเร็จ", "success")
        except USER_ERRORS as error:
            flash_errors(error)
        return redirect(url_for("admin_coupons"))
    return render_template("admin_coupons.html", coupons=list_coupons(get_db()))


# =============================================================== คำสั่งซื้อ / รายงาน
@admin.get("/reports")
@admin_required
def admin_reports():
    db = get_db()
    orders = list_all_orders(db)
    paid_total, pending_total = sales_totals(db)
    return render_template("admin_reports.html", orders=orders, paid_total=paid_total, pending_total=pending_total,
                           items=group_items_by_order(db, orders))


@admin.post("/orders/<int:order_id>/cancel")
@admin_required
def admin_cancel_order(order_id):
    try:
        cancel_order(get_db(), order_id)
        flash(f"ยกเลิกคำสั่งซื้อ #{order_id} และคืนสต็อกแล้ว", "success")
    except USER_ERRORS as error: flash_errors(error)
    return redirect(url_for("admin_reports"))


@admin.post("/orders/<int:order_id>/confirm-payment")
@admin_required
def admin_confirm_payment(order_id):
    if confirm_payment(get_db(), order_id):
        flash(f"ยืนยันรับเงินคำสั่งซื้อ #{order_id} แล้ว", "success")
    else:
        flash("ไม่พบคำสั่งซื้อที่รอชำระเงิน", "danger")
    return redirect(url_for("admin_reports"))


# =============================================================== สมาชิก
@admin.get("/members")
@admin_required
def admin_members():
    return render_template("admin_members.html", members=list_members_with_sales(get_db()))


# =============================================================== ตั้งค่า PromptPay
@admin.route("/settings", methods=["GET", "POST"])
@admin_required
def admin_settings():
    db = get_db()
    if request.method == "POST":
        try:
            raw_promptpay_id = (request.form.get("promptpay_id") or "").strip()
            promptpay_id = clean_promptpay_id(raw_promptpay_id) if raw_promptpay_id else ""
            if promptpay_id:
                set_setting(db, PROMPTPAY_ID_KEY, promptpay_id)
            qr_file = request.files.get("qr_image")
            if qr_file and qr_file.filename:
                valid = pick_valid_images([qr_file], 1)
                filename = save_image_file(valid[0])
                old_image = get_setting(db, PROMPTPAY_IMAGE_KEY)
                set_setting(db, PROMPTPAY_IMAGE_KEY, filename)
                if old_image and old_image != filename: delete_image_file(old_image)
            if request.form.get("remove_qr_image") == "on":
                old_image = get_setting(db, PROMPTPAY_IMAGE_KEY)
                set_setting(db, PROMPTPAY_IMAGE_KEY, "")
                if old_image: delete_image_file(old_image)
            flash("บันทึกการตั้งค่าการชำระเงินแล้ว", "success")
        except USER_ERRORS as error:
            flash_errors(error)
        return redirect(url_for("admin_settings"))

    promptpay_id = get_setting(db, PROMPTPAY_ID_KEY)
    qr_image = get_setting(db, PROMPTPAY_IMAGE_KEY)
    preview_svg, preview_problem = None, None
    if promptpay_id:  # QR ทดสอบ 1 บาท ให้ Admin ลองสแกนเช็คว่าเป็นบัญชีของตัวเองจริง
        try:
            preview_svg = make_qr_svg(build_payload(promptpay_id, 100))
        except QrUnavailable as error:
            preview_problem = str(error)
    return render_template("admin_settings.html", promptpay_id=promptpay_id, qr_image=qr_image,
                           preview_svg=preview_svg, preview_problem=preview_problem)



SLIP_DIR = os.path.join(ROOT_DIR, "private_slips")

@shop.post("/orders/<int:order_id>/slip")
@member_required
def upload_slip(order_id):
    order = get_own_order_or_404(order_id)
    if order["payment_method"] != "promptpay" or order["status"] != STATUS_PENDING:
        abort(409)
    file = request.files.get("slip")
    try:
        if not file:
            raise ValueError()
        data = file.read(MAX_IMAGE_BYTES + 1)
        if len(data) > MAX_IMAGE_BYTES:
            raise ValueError()
        with Image.open(BytesIO(data)) as im:
            if im.format not in ("JPEG", "PNG") or im.width * im.height > 20000000:
                raise ValueError()
            im.load()
            os.makedirs(SLIP_DIR, exist_ok=True)
            filename = secrets.token_hex(24) + ".jpg"
            im.convert("RGB").save(os.path.join(SLIP_DIR, filename), "JPEG")
    except (ValueError, OSError, UnidentifiedImageError, Image.DecompressionBombError):
        flash("กรุณาอัปโหลดรูปสลิป JPG/PNG ไม่เกิน 4 MB", "danger")
        return redirect(url_for("pay_with_qr", order_id=order_id))
    result = get_db().execute("UPDATE orders SET slip_file=?, slip_note='', status='review' WHERE order_id=? AND status='pending'",
                             (filename, order_id))
    if not result.rowcount:
        os.remove(os.path.join(SLIP_DIR, filename))
        abort(409)
    flash("ส่งสลิปแล้ว รอแอดมินตรวจสอบ", "success")
    return redirect(url_for("order_detail", order_id=order_id))

@admin.get("/orders/<int:order_id>/slip")
@admin_required
def admin_slip(order_id):
    order = get_order(get_db(), order_id)
    if not order or not order["slip_file"]:
        abort(404)
    response = send_from_directory(SLIP_DIR, order["slip_file"])
    response.headers["Cache-Control"] = "no-store"
    return response

@admin.post("/orders/<int:order_id>/reject-slip")
@admin_required
def reject_slip(order_id):
    note = request.form.get("note", "").strip()[:300]
    if not note:
        flash("กรุณาระบุเหตุผลที่ไม่ผ่าน", "danger")
    else:
        get_db().execute("UPDATE orders SET status='pending', slip_note=? WHERE order_id=? AND status='review' AND payment_method='promptpay'", (note, order_id))
        flash("แจ้งให้ลูกค้าส่งสลิปใหม่แล้ว", "success")
    return redirect(url_for("admin_reports"))

def validate_demo_card(form):
    """ตรวจข้อมูลสมมติเท่านั้น ไม่ส่งข้อมูลออกและไม่จัดเก็บข้อมูลบัตร"""
    name = (form.get("card_name") or "").strip()
    number = re.sub(r"[ -]", "", form.get("card_number") or "")
    expiry = (form.get("card_expiry") or "").strip()
    cvv = form.get("card_cvv") or ""
    errors = []
    if not name or len(name) > 100:
        errors.append("กรุณากรอกชื่อผู้ถือบัตรไม่เกิน 100 ตัวอักษร")
    if not re.fullmatch(r"[0-9]{16}", number):
        errors.append("เลขบัตรสมมติต้องเป็นตัวเลข 16 หลัก")
    match = re.fullmatch(r"(0[1-9]|1[0-2])/([0-9]{2})", expiry)
    if not match:
        errors.append("วันหมดอายุต้องเป็น MM/YY เช่น 12/30")
    elif (2000 + int(match[2]), int(match[1])) < (date.today().year, date.today().month):
        errors.append("บัตรหมดอายุแล้ว กรุณาใช้วันหมดอายุในอนาคต")
    if not re.fullmatch(r"[0-9]{3,4}", cvv):
        errors.append("CVV สมมติต้องเป็นตัวเลข 3 หรือ 4 หลัก")
    return errors

@shop.route("/orders/<int:order_id>/card", methods=["GET", "POST"])
@member_required
def pay_card(order_id):
    order = get_own_order_or_404(order_id)
    if order["payment_method"] != "card" or order["status"] != STATUS_PENDING:
        return redirect(url_for("order_detail", order_id=order_id))
    errors = []
    if request.method == "POST":
        errors = validate_demo_card(request.form)
        if not errors:
            result = get_db().execute(
                "UPDATE orders SET status='paid' WHERE order_id=? AND member_id=? AND payment_method='card' AND status='pending'",
                (order_id, session["member_id"]))
            if result.rowcount:
                flash("ชำระเงินจำลองสำเร็จ ไม่มีการตัดเงินจริง", "success")
            return redirect(url_for("order_detail", order_id=order_id))
    return render_template("pay_card.html", order=order, errors=errors)


# =============================================================== เริ่มโปรแกรม


# ============================================================================
# ส่วนที่ 19: จุดเริ่มต้นโปรแกรม
#
# แต่ละเว็บ (shop / admin) คือ Flask app คนละตัว รันคนละพอร์ต แต่อยู่ในไฟล์นี้ไฟล์เดียว
# รันทั้งคู่: ให้เว็บ Admin ทำงานใน thread แยก ส่วนเว็บร้านค้าทำงานใน thread หลัก
# ============================================================================
def run_shop_site():
    shop.run(host=os.environ.get("SHOP_HOST", "127.0.0.1"),
             port=int(os.environ.get("SHOP_PORT", 5000)), use_reloader=False)


def run_admin_site():
    admin.run(host=os.environ.get("ADMIN_HOST", "127.0.0.1"),
              port=int(os.environ.get("ADMIN_PORT", 5001)), use_reloader=False)


def main():
    choice = sys.argv[1] if len(sys.argv) > 1 else "both"
    if choice not in ("both", "shop", "admin"):
        sys.exit("วิธีใช้:  python camera_shop.py [shop | admin]   (ไม่ใส่ = รันทั้งสองเว็บ)")

    init_database()
    if choice == "shop":
        run_shop_site()
    elif choice == "admin":
        run_admin_site()
    else:
        print(f"\n  ร้านค้า (ลูกค้า): http://127.0.0.1:{os.environ.get('SHOP_PORT', 5000)}"
              f"\n  ผู้ดูแลระบบ    : http://127.0.0.1:{os.environ.get('ADMIN_PORT', 5001)}"
              "\n  กด Ctrl+C เพื่อปิด\n")
        # daemon=True: เมื่อปิดโปรแกรมหลัก thread นี้จะปิดตามไปด้วย
        threading.Thread(target=run_admin_site, daemon=True).start()
        run_shop_site()


if __name__ == "__main__":
    main()
