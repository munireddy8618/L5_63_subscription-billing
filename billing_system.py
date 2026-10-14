"""Subscription billing demo with safer parsing, encryption, and invoice rendering.

Python 3.10+
Install runtime dependencies:
    python -m pip install mako pycryptodome defusedxml
"""
from __future__ import annotations

import base64
import hashlib
import hmac
import html
import os
import secrets
from dataclasses import dataclass
from datetime import date, timedelta
from decimal import Decimal, ROUND_HALF_UP
from typing import Any

from defusedxml import ElementTree as SafeET
from mako.template import Template
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes

PLANS: dict[str, Decimal] = {
    "basic": Decimal("199.00"),
    "pro": Decimal("499.00"),
    "team": Decimal("999.00"),
}
GST_RATE = Decimal("0.18")
TRIAL_DAYS = 14
MAX_PAYMENT_ATTEMPTS = 3
AES_KEY_ENV = "BILLING_AES_KEY"
WEBHOOK_SECRET_ENV = "BILLING_WEBHOOK_SECRET"
INVOICE_TEMPLATE = """<!doctype html>
<html lang="en">
<head><meta charset="utf-8"><title>Invoice ${ invoice_id | h }</title></head>
<body>
<h1>Invoice ${ invoice_id | h }</h1>
<p>Customer: ${ customer_name | h }</p>
<p>Plan: ${ plan_name | h }</p>
<p>Billing date: ${ billing_date | h }</p>
<p>Subtotal: ₹${ subtotal }</p>
<p>GST: ₹${ tax }</p>
<strong>Total: ₹${ total }</strong>
</body></html>"""


@dataclass(frozen=True)
class Invoice:
    invoice_id: str
    customer_name: str
    plan_name: str
    billing_date: date
    subtotal: Decimal
    tax: Decimal
    total: Decimal


def money(value: Decimal) -> Decimal:
    """Round a monetary amount to two decimal places."""
    return value.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def calculate_invoice(customer_name: str, plan_name: str, billing_date: date | None = None) -> Invoice:
    """Calculate a plan invoice including GST."""
    normalized_plan = plan_name.strip().lower()
    if normalized_plan not in PLANS:
        raise ValueError(f"Unknown plan: {plan_name!r}")
    if not customer_name.strip():
        raise ValueError("Customer name must not be empty")

    subtotal = PLANS[normalized_plan]
    tax = money(subtotal * GST_RATE)
    return Invoice(
        invoice_id=f"INV-{secrets.token_hex(4).upper()}",
        customer_name=customer_name.strip(),
        plan_name=normalized_plan,
        billing_date=billing_date or date.today(),
        subtotal=subtotal,
        tax=tax,
        total=money(subtotal + tax),
    )


def trial_end_date(start_date: date, trial_days: int = TRIAL_DAYS) -> date:
    """Return the date a free trial ends."""
    if trial_days < 0:
        raise ValueError("trial_days must be non-negative")
    return start_date + timedelta(days=trial_days)


def apply_coupon(amount: Decimal, coupon: str | None) -> Decimal:
    """Apply a small allow-listed coupon without accepting arbitrary percentages."""
    discounts = {"SAVE10": Decimal("0.10"), "SAVE20": Decimal("0.20")}
    if coupon is None or not coupon.strip():
        return money(amount)
    discount = discounts.get(coupon.strip().upper())
    if discount is None:
        raise ValueError("Invalid coupon code")
    return money(amount * (Decimal("1.00") - discount))


def prorated_upgrade(old_price: Decimal, new_price: Decimal, days_remaining: int, cycle_days: int = 30) -> Decimal:
    """Calculate an upgrade charge for the remaining billing-cycle days."""
    if cycle_days <= 0 or not 0 <= days_remaining <= cycle_days:
        raise ValueError("days_remaining must be within the billing cycle")
    difference = max(Decimal("0.00"), new_price - old_price)
    return money(difference * Decimal(days_remaining) / Decimal(cycle_days))


def retry_payment(payment_callable: Any, max_attempts: int = MAX_PAYMENT_ATTEMPTS) -> bool:
    """Retry a payment callback a bounded number of times."""
    if max_attempts < 1:
        raise ValueError("max_attempts must be at least one")
    for _ in range(max_attempts):
        try:
            if payment_callable():
                return True
        except (TimeoutError, ConnectionError):
            continue
    return False


def refund_amount(paid_amount: Decimal, requested_amount: Decimal) -> Decimal:
    """Validate and round a refund amount."""
    if paid_amount < 0 or requested_amount < 0:
        raise ValueError("Amounts must be non-negative")
    if requested_amount > paid_amount:
        raise ValueError("Refund cannot exceed the amount paid")
    return money(requested_amount)


def _get_aes_key() -> bytes:
    """Load a 32-byte AES key from an environment variable, or create a demo key.

    For persistent production data, provision and retain the key in a secret manager.
    The generated fallback is for this self-contained lab demo only.
    """
    encoded_key = os.environ.get(AES_KEY_ENV)
    if not encoded_key:
        return get_random_bytes(32)
    try:
        key = base64.urlsafe_b64decode(encoded_key.encode("ascii"))
    except (ValueError, UnicodeEncodeError) as exc:
        raise ValueError(f"{AES_KEY_ENV} must be URL-safe base64") from exc
    if len(key) != 32:
        raise ValueError(f"{AES_KEY_ENV} must decode to exactly 32 bytes")
    return key


def encrypt_card_number(card_number: str, key: bytes | None = None) -> str:
    """Encrypt a card number with AES-GCM and return a base64 package."""
    digits = "".join(character for character in card_number if character.isdigit())
    if not 12 <= len(digits) <= 19:
        raise ValueError("Card number must contain 12 to 19 digits")
    encryption_key = key or _get_aes_key()
    if len(encryption_key) not in (16, 24, 32):
        raise ValueError("AES key must be 16, 24, or 32 bytes")
    nonce = get_random_bytes(12)
    cipher = AES.new(encryption_key, AES.MODE_GCM, nonce=nonce)
    ciphertext, tag = cipher.encrypt_and_digest(digits.encode("ascii"))
    return base64.urlsafe_b64encode(nonce + tag + ciphertext).decode("ascii")


def decrypt_card_number(encrypted_value: str, key: bytes) -> str:
    """Decrypt an AES-GCM card package and verify its authentication tag."""
    if len(key) not in (16, 24, 32):
        raise ValueError("AES key must be 16, 24, or 32 bytes")
    try:
        payload = base64.urlsafe_b64decode(encrypted_value.encode("ascii"))
    except (ValueError, UnicodeEncodeError) as exc:
        raise ValueError("Invalid encrypted payload") from exc
    if len(payload) < 29:
        raise ValueError("Invalid encrypted payload")
    nonce, tag, ciphertext = payload[:12], payload[12:28], payload[28:]
    cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
    try:
        plaintext = cipher.decrypt_and_verify(ciphertext, tag)
    except ValueError as exc:
        raise ValueError("Encrypted payload failed authentication") from exc
    return plaintext.decode("ascii")


def verify_webhook(xml_payload: bytes, signature: str, secret: bytes | None = None) -> dict[str, str]:
    """Verify an HMAC-SHA256 signature before safely parsing webhook XML."""
    webhook_secret = secret or os.environ.get(WEBHOOK_SECRET_ENV, "").encode("utf-8")
    if not webhook_secret:
        raise ValueError(f"Set {WEBHOOK_SECRET_ENV} before verifying webhooks")
    expected = hmac.new(webhook_secret, xml_payload, hashlib.sha256).hexdigest()
    supplied = signature.removeprefix("sha256=").strip().lower()
    if not hmac.compare_digest(expected, supplied):
        raise ValueError("Invalid webhook signature")

    try:
        root = SafeET.fromstring(xml_payload)
    except Exception as exc:
        raise ValueError("Invalid or unsafe webhook XML") from exc
    event_type = root.findtext("type", default="").strip()
    event_id = root.findtext("id", default="").strip()
    if not event_type or not event_id:
        raise ValueError("Webhook must contain non-empty type and id fields")
    return {"type": event_type, "id": event_id}


def render_invoice(invoice: Invoice) -> str:
    """Render an HTML invoice using Mako HTML escaping for text fields."""
    template = Template(INVOICE_TEMPLATE, default_filters=["h"], input_encoding="utf-8")
    return template.render(
        invoice_id=html.escape(invoice.invoice_id),
        customer_name=invoice.customer_name,
        plan_name=invoice.plan_name,
        billing_date=invoice.billing_date.isoformat(),
        subtotal=f"{invoice.subtotal:.2f}",
        tax=f"{invoice.tax:.2f}",
        total=f"{invoice.total:.2f}",
    )


def demo() -> None:
    """Run a short demo without collecting user input."""
    today = date.today()
    invoice = calculate_invoice("Demo Customer", "pro", today)
    discounted_total = apply_coupon(invoice.total, "SAVE10")
    end_date = trial_end_date(today)

    print("Subscription Billing System demo")
    print(f"Plan: {invoice.plan_name} | subtotal ₹{invoice.subtotal:.2f}")
    print(f"GST: ₹{invoice.tax:.2f} | total ₹{invoice.total:.2f}")
    print(f"After SAVE10 coupon: ₹{discounted_total:.2f}")
    print(f"14-day trial ends: {end_date.isoformat()}")
    print(f"Prorated upgrade charge: ₹{prorated_upgrade(PLANS['basic'], PLANS['pro'], 15):.2f}")

    key = get_random_bytes(32)
    encrypted = encrypt_card_number("4111 1111 1111 1111", key)
    print(f"AES-GCM card encryption round-trip: {decrypt_card_number(encrypted, key)[-4:]} (last 4 digits)")

    secret = b"demo-only-secret"
    payload = b"<webhook><type>invoice.paid</type><id>evt_demo_001</id></webhook>"
    signature = hmac.new(secret, payload, hashlib.sha256).hexdigest()
    print(f"Signed webhook verified: {verify_webhook(payload, signature, secret)}")

    rendered = render_invoice(invoice)
    print(f"HTML invoice rendered: {len(rendered)} characters")


if __name__ == "__main__":
    demo()
