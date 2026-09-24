#!/usr/bin/env python3
"""DeviantArt auto-commenter — dark HTML GUI, single account, multi-thread.

Everything runs over plain HTTP requests — no browser at all. Paste one
account's cookies, a feed/gallery/search page URL, and comment text:

    GET  <feed_url>                                                (polled
         every ~20s; DeviantArt server-renders the visible grid for SEO, so
         deviation links are pulled straight out of the returned HTML with
         no need to run JS or scroll anything)
    GET  https://www.deviantart.com/                              (once, to
         scrape the page's csrfToken — cookie-scoped, reused for every call
         — or paste one manually in the UI to skip this entirely)
    POST https://www.deviantart.com/_napi/shared_api/comments/post
         {"typeid":1,"itemid":<deviation id>,"editorRaw":<tiptap doc JSON>,
          "da_minor_version":20230710,"csrf_token":...}

Discovered posts feed into a shared queue; N worker threads (thread count
set in the UI) pull from it and post the comment via the API above.

After a successful comment, the post's author goes into a persisted
blacklist — any future post by that same author is skipped, unless the
"ignore blacklist" checkbox is on. Independent of that permanent blacklist,
a live in-memory reservation set stops two threads from working the same
author at the same instant (a thread claims the author before posting,
releases it right after) so nobody double-comments a single author's
posts in a race.
"""
import base64
import io
import json
import mimetypes
import os
import queue
import random
import re
import string
import sys
import threading
import time
import urllib.parse
import uuid
from datetime import datetime, timedelta
from pathlib import Path
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs

try:
    import requests
except ImportError:
    requests = None
try:
    import curl_cffi.requests as curl_requests
    from curl_cffi import CurlMime
except ImportError:
    curl_requests = None
    CurlMime = None
try:
    from PIL import Image
except ImportError:
    Image = None
try:
    from playwright.sync_api import sync_playwright
except ImportError:
    sync_playwright = None

# Cap concurrent Chromium instances. With 20+ threads all launching Playwright
# at once for WAF solving, they thrash CPU/memory and each takes far longer
# than it would running alone — measured live: 6 concurrent finish in ~6s
# each; 20 concurrent stall past 60s and start timing out. 8 keeps GUI thread
# responsive while still parallelizing solves.
_PLAYWRIGHT_SEMAPHORE = threading.BoundedSemaphore(8)

for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

PORT = 8796
REQUEST_TIMEOUT = 30
DA_MINOR_VERSION = 20230710
MAX_LOG_LINES = 5000
LOG_TAIL_SENT = 400
DEVIATION_LINK_RE = re.compile(
    r"https://www\.deviantart\.com/([a-zA-Z0-9_-]+)/art/([a-zA-Z0-9_-]+)-(\d+)")

BASE_DIR = Path(__file__).resolve().parent
BLACKLIST_FILE = BASE_DIR / "deviantart_blacklist.txt"
NOTEBOOK_FILE = BASE_DIR / "deviantart_posts.txt"
PARSER_LOG_FILE = BASE_DIR / "deviantart_parser_log.txt"
SENDER_LOG_FILE = BASE_DIR / "deviantart_sender_log.txt"
TEMP_EMAIL_COUNTER_FILE = BASE_DIR / "temp_email_counter.txt"
# Append-only ledger of every account number ever handed out (number + the
# resolved username it produced) — the source of truth for "never reuse a
# login", since it's written the instant a number is issued (before the
# registration attempt even runs), not just on success.
TEMP_ACCOUNT_REGISTRY_FILE = BASE_DIR / "deviantart_registered_account_numbers.txt"
# Working accounts saved when the sender is stopped, so the next run can
# reuse them instead of registering from scratch — see save_account_to_pool/
# pop_account_from_pool. One JSON object per line: {"username","cookies"}.
ACCOUNT_POOL_FILE = BASE_DIR / "deviantart_account_pool.jsonl"
DA_SETTINGS_FILE = BASE_DIR / "tmp" / "da_gui_settings.json"

# ============================================================================
# Temp-mail providers for auto-registration
# ============================================================================

# --- tempmail4u ---
TEMPMAIL4U_API = "https://api.tempmail4u.com/api"
TEMPMAIL4U_DOMAIN = "jsontoexcel.net"

def tempmail4u_get_email(domain=None):
    try:
        local_part = "".join(random.choices(string.ascii_lowercase + string.digits, k=8))
        return f"{local_part}@{TEMPMAIL4U_DOMAIN}", None
    except Exception:
        return None, None

def tempmail4u_get_emails(email, _ctx=None):
    try:
        resp = curl_requests.get(f"{TEMPMAIL4U_API}/fakeemails/?email={email}", timeout=REQUEST_TIMEOUT) if curl_requests else requests.get(f"{TEMPMAIL4U_API}/fakeemails/?email={email}", timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        data = resp.json()
        return data if isinstance(data, list) else []
    except Exception:
        return []

# --- 1secmail ---
ONESECMAIL_API = "https://www.1secmail.com/api/v1/"
# .com dropped: confirmed live that DeviantArt's signup rejects it specifically
# as a banned/disposable domain (email_banned) while .net and .org still pass —
# same provider, per-domain reputation differs.
ONESECMAIL_DOMAINS = ["1secmail.org", "1secmail.net"]

def onesecmail_get_email(domain=None):
    try:
        domain = random.choice(ONESECMAIL_DOMAINS)
        local_part = "".join(random.choices(string.ascii_lowercase + string.digits, k=10))
        return f"{local_part}@{domain}", None
    except Exception:
        return None, None

def onesecmail_get_emails(email, _ctx=None):
    try:
        login, domain = email.split("@", 1)
        _http = curl_requests or requests
        resp = _http.get(f"{ONESECMAIL_API}?action=getMessages&login={login}&domain={domain}",
                         timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        messages = resp.json()
        if not isinstance(messages, list) or not messages:
            return []
        result = []
        for msg in messages:
            body_resp = _http.get(
                f"{ONESECMAIL_API}?action=readMessage&login={login}&domain={domain}&id={msg['id']}",
                timeout=REQUEST_TIMEOUT)
            if body_resp.status_code == 200:
                bd = body_resp.json()
                result.append({"body_html": bd.get("htmlBody", ""), "body": bd.get("textBody", "")})
        return result
    except Exception:
        return []

# --- tempmail.lol ---
TEMPLOL_API = "https://api.tempmail.lol"

def templol_get_email(domain=None):
    try:
        _http = curl_requests or requests
        resp = _http.get(f"{TEMPLOL_API}/generate", timeout=REQUEST_TIMEOUT)
        if resp.status_code == 200:
            data = resp.json()
            return data.get("address"), data.get("token")
    except Exception:
        pass
    return None, None

def templol_get_emails(email, ctx=None):
    if not ctx:
        return []
    try:
        _http = curl_requests or requests
        resp = _http.get(f"{TEMPLOL_API}/auth/{ctx}", timeout=REQUEST_TIMEOUT)
        if resp.status_code == 200:
            data = resp.json()
            emails = data.get("email", [])
            if isinstance(emails, list):
                return [{"body_html": e.get("html", ""), "body": e.get("body", "")} for e in emails]
    except Exception:
        pass
    return []

# --- mail.tm ---
MAILTM_API = "https://api.mail.tm"

def _mailtm_session():
    if curl_requests:
        return curl_requests.Session()
    return requests.Session()

def mailtm_get_email(domain=None):
    s = _mailtm_session()
    try:
        resp = s.get(f"{MAILTM_API}/domains", timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        domains = resp.json()
        members = domains.get("hydra:member", []) if isinstance(domains, dict) else []
        if not members:
            return None, None
        domain = members[0]["domain"] if isinstance(members[0], dict) else str(members[0])
        local_part = "".join(random.choices(string.ascii_lowercase + string.digits, k=10))
        address = f"{local_part}@{domain}"
        password = "".join(random.choices(string.ascii_letters + string.digits, k=16))
        resp = s.post(f"{MAILTM_API}/accounts",
                      json={"address": address, "password": password},
                      headers={"content-type": "application/json"},
                      timeout=REQUEST_TIMEOUT)
        if resp.status_code not in (200, 201):
            return None, None
        resp = s.post(f"{MAILTM_API}/token",
                      json={"address": address, "password": password},
                      headers={"content-type": "application/json"},
                      timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        token = resp.json().get("token")
        return address, token
    except Exception:
        return None, None
    finally:
        s.close()

def mailtm_get_emails(email, ctx=None):
    if not ctx:
        return []
    s = _mailtm_session()
    try:
        resp = s.get(f"{MAILTM_API}/messages",
                     headers={"authorization": f"Bearer {ctx}"},
                     timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        data = resp.json()
        messages = data.get("hydra:member", []) if isinstance(data, dict) else []
        result = []
        for msg in messages:
            msg_id = msg.get("id") or msg.get("@id", "").split("/")[-1]
            if not msg_id:
                continue
            detail = s.get(f"{MAILTM_API}/messages/{msg_id}",
                           headers={"authorization": f"Bearer {ctx}"},
                           timeout=REQUEST_TIMEOUT)
            if detail.status_code == 200:
                md = detail.json()
                html_body = md.get("html", "")
                if isinstance(html_body, list):
                    html_body = html_body[0] if html_body else ""
                result.append({"body_html": html_body, "body": md.get("text", "")})
        return result
    except Exception:
        return []
    finally:
        s.close()

# --- mail.gw (same Hydra/JSON-LD API family as mail.tm, confirmed live —
# but unlike mail.tm it does NOT default to JSON without an explicit Accept
# header: omitting it serves the HTML Swagger docs page instead (status 200,
# so a naive .json() call throws). Domain pool confirmed live against DA's
# signup: oakon.com is banned, pastryofistanbul.com was inconclusive
# (csrf_fail — proxy blip, not a real rejection), the rest accepted. ---
MAILGW_API = "https://api.mail.gw"
MAILGW_JHDR = {"content-type": "application/json", "accept": "application/ld+json"}
# mail.gw's /domains response includes oakon.com, which DA rejects — never
# trust "whatever the API returns first" like mail.tm's code does; only pick
# from domains individually confirmed live against DA's signup.
MAILGW_DOMAINS = ["teihu.com", "raleigh-construction.com", "questtechsystems.com"]

def mailgw_get_email(domain=None):
    s = _mailtm_session()
    try:
        domain = domain or random.choice(MAILGW_DOMAINS)
        local_part = "".join(random.choices(string.ascii_lowercase + string.digits, k=10))
        address = f"{local_part}@{domain}"
        password = "".join(random.choices(string.ascii_letters + string.digits, k=16))
        resp = s.post(f"{MAILGW_API}/accounts", json={"address": address, "password": password},
                      headers=MAILGW_JHDR, timeout=REQUEST_TIMEOUT)
        if resp.status_code not in (200, 201):
            return None, None
        resp = s.post(f"{MAILGW_API}/token", json={"address": address, "password": password},
                      headers=MAILGW_JHDR, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        token = resp.json().get("token")
        return address, token
    except Exception:
        return None, None
    finally:
        s.close()

def mailgw_get_emails(email, ctx=None):
    if not ctx:
        return []
    s = _mailtm_session()
    try:
        headers = {"authorization": f"Bearer {ctx}", "accept": "application/ld+json"}
        resp = s.get(f"{MAILGW_API}/messages", headers=headers, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        messages = resp.json().get("hydra:member", [])
        result = []
        for msg in messages:
            msg_id = msg.get("id") or msg.get("@id", "").split("/")[-1]
            if not msg_id:
                continue
            detail = s.get(f"{MAILGW_API}/messages/{msg_id}", headers=headers, timeout=REQUEST_TIMEOUT)
            if detail.status_code == 200:
                md = detail.json()
                html_body = md.get("html", "")
                if isinstance(html_body, list):
                    html_body = html_body[0] if html_body else ""
                result.append({"body_html": html_body, "body": md.get("text", "")})
        return result
    except Exception:
        return []
    finally:
        s.close()

# --- emailnator (ported from superfaktura_proxy_checker.py's en_session/
# generate_random_email/fetch_verify_link) ---
EMAILNATOR_BASE = "https://www.emailnator.com"
# "googleMail" (@googlemail.com) is the domain key SuperFaktura's own script
# settled on: most throwaway-style options get rejected by signup forms, this
# one is a real Google-owned domain and gets accepted. The other 3 are
# confirmed live against emailnator's own API (POST /generate-email):
# "domain" hands out a rotating real throwaway domain (e.g. tmpmailtor.com),
# "plusGmail"/"dotGmail" are genuine @gmail.com addresses using the +tag/dot
# tricks — same underlying inbox as the base account, just addressed
# differently.
EMAILNATOR_DOMAINS = {
    "googleMail": "Googlemail.com",
    "domain":     "Случайный домен",
    "plusGmail":  "Gmail (+тег)",
    "dotGmail":   "Gmail (через точки)",
}
EMAILNATOR_DOMAIN_KEY = "googleMail"

def _emailnator_session():
    """Fresh emailnator session carrying the XSRF token its API requires.
    Returns (session, headers) or (None, None). The XSRF-TOKEN cookie handed
    out by the homepage must be echoed back in the x-xsrf-token header
    (Laravel CSRF) or every API call is rejected.
    """
    session = curl_requests.Session(impersonate="chrome124") if curl_requests else requests.Session()
    try:
        session.get(EMAILNATOR_BASE + "/", timeout=REQUEST_TIMEOUT)
    except Exception:
        return None, None
    try:
        xsrf = urllib.parse.unquote(dict(session.cookies).get("XSRF-TOKEN", ""))
    except Exception:
        xsrf = ""
    if not xsrf:
        return None, None
    headers = {
        "accept": "application/json, text/plain, */*",
        "content-type": "application/json",
        "origin": EMAILNATOR_BASE,
        "referer": EMAILNATOR_BASE + "/",
        "x-requested-with": "XMLHttpRequest",
        "x-xsrf-token": xsrf,
    }
    return session, headers

def emailnator_get_email(domain=None):
    """ctx is (session, headers) — emailnator's inbox is tied to the exact
    authenticated session/XSRF pair that generated the address, unlike the
    other providers' stateless-by-address or bearer-token designs.
    """
    domain_key = domain if domain in EMAILNATOR_DOMAINS else EMAILNATOR_DOMAIN_KEY
    session, headers = _emailnator_session()
    if not session:
        return None, None
    try:
        resp = session.post(f"{EMAILNATOR_BASE}/generate-email", headers=headers,
                            json={"email": [domain_key]}, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        addresses = resp.json().get("email") or []
        return (addresses[0], (session, headers)) if addresses else (None, None)
    except Exception:
        return None, None

def emailnator_get_emails(email, ctx=None):
    if not ctx:
        return []
    session, headers = ctx
    try:
        resp = session.post(f"{EMAILNATOR_BASE}/message-list", headers=headers,
                            json={"email": email}, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        result = []
        for msg in resp.json().get("messageData", []):
            msg_id = msg.get("messageID")
            if not msg_id:
                continue
            body_resp = session.post(f"{EMAILNATOR_BASE}/message-list", headers=headers,
                                     json={"email": email, "messageID": msg_id}, timeout=REQUEST_TIMEOUT)
            if body_resp.status_code != 200:
                continue
            body = body_resp.text
            # googleMail addresses are dot-variants of one shared underlying
            # Gmail inbox, so concurrent registration threads can see each
            # other's mail here — confirmed live by SuperFaktura's own script,
            # which guards against exactly this. Only accept a message that
            # names OUR address, or two threads could steal each other's
            # confirmation links.
            if email not in body:
                continue
            result.append({"body_html": body, "body": body})
        return result
    except Exception:
        return []

# Maildrop, GuerrillaMail (all its ~11 domains), TempMail.plus, and
# Temp-Mail.io were all tried and removed: confirmed live via DeviantArt's
# own signup validation (POST _sisu/do/signup2 responding with
# error_message=email_banned instead of the normal 301 redirect) that every
# domain each of them offers is already on DeviantArt's disposable-email
# blocklist — registering through them always fails at signup, regardless
# of proxy/account/anything else in this tool. Not implemented further per
# the rule of testing domain-acceptance before writing automation for it.

# --- mohmal.com (session-cookie-based, HTML message reading — confirmed
# live end-to-end with a real DeviantArt signup: POST /en/create picks a
# mailbox on one of its domains, GET /en/inbox lists messages by
# data-msg-id, GET /en/message/<id> returns the full message HTML that
# extract_deviantart_verify_link() already parses correctly with zero
# changes needed) ---
MOHMAL_DOMAINS = ["mailna.co", "mailna.in", "mailna.me", "mohmal.im", "mohmal.in"]
# mozej.com is also offered by mohmal's own domain picker but confirmed live
# to be email_banned on DeviantArt — deliberately left out of this list.

def mohmal_get_email(domain=None):
    try:
        _http = curl_requests or requests
        sess = _http.Session()
        local_part = "".join(random.choices(string.ascii_lowercase + string.digits, k=10))
        dom = domain or random.choice(MOHMAL_DOMAINS)
        resp = sess.post("https://www.mohmal.com/en/create", data={"name": local_part, "domain": dom},
                         timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        sid = sess.cookies.get("connect.sid")
        if not sid:
            return None, None
        return f"{local_part}@{dom}", sid  # ctx = the connect.sid session cookie value
    except Exception:
        return None, None

def mohmal_get_emails(email, ctx=None):
    if not ctx:
        return []
    try:
        _http = curl_requests or requests
        sess = _http.Session()
        sess.cookies.set("connect.sid", ctx, domain="www.mohmal.com")
        resp = sess.get("https://www.mohmal.com/en/inbox", timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        msg_ids = re.findall(r'data-msg-id="(\d+)"', resp.text)
        result = []
        for msg_id in msg_ids:
            r2 = sess.get(f"https://www.mohmal.com/en/message/{msg_id}", timeout=REQUEST_TIMEOUT)
            if r2.status_code == 200:
                result.append({"body_html": r2.text, "body": r2.text})
        return result
    except Exception:
        return []

# --- tempmailg.com (Cloudflare Managed Challenge in front of everything — a
# bare curl_cffi/requests call never gets past it, and confirmed live that
# even a real, unflagged headless Chrome gets stuck looping the same
# interstitial forever (Cloudflare's automatic scoring flags headless
# specifically — GPU/WebGL renderer signal — regardless of "--headless=new"
# or spoofing navigator.webdriver/plugins/languages). The one thing that
# DOES work headless: intercepting the page's own `turnstile.render(a, b)`
# call (see TEMPMAILG_INTERCEPT_JS) the instant Cloudflare's JS tries to
# render the interactive widget, to grab {sitekey, action, cData,
# chlPageData} — confirmed live this fires within ~1s even in headless mode,
# well before any visual challenge would need to resolve. Those params go to
# 2captcha's TurnstileTaskProxyless; the solved token is then replayed
# through the SAME intercepted `b.callback` from inside the still-open page
# — that's Cloudflare's own JS driving the verify POST and setting
# `cf_clearance`, not something worth reimplementing by hand. Confirmed live
# end-to-end that once you have that cookie, a plain curl_cffi session (same
# user-agent) can reuse it directly: POST /change (new mailbox), POST
# /get_messages (poll), GET /view/<id> (message body) all work as pure HTTP
# with zero further browser/JS involvement — the flow reverse-engineered
# from the site's own assets/themes/basic/js/app.js (blank `name` 422s on
# /change — "The name field is required", confirmed live). The browser is
# only alive for the ~10-20s it takes 2captcha to solve the widget; every
# registration+poll cycle after that is 100% HTTP, same shape as every
# other provider here. ---
TEMPMAILG_2CAPTCHA_KEY = os.environ.get("TEMPMAILG_2CAPTCHA_KEY", "7060ee639aa37c94b7bdfab0a275bf31")
TEMPMAILG_DOMAINS = ["jazzvip.site", "oegmail.store", "boommail.online", "babyfun.fun",
                      "speedlooking.fun", "flashemail.site", "nondon.site", "ingam.online"]
TEMPMAILG_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
TEMPMAILG_2CAPTCHA_POLL_S = 3
TEMPMAILG_2CAPTCHA_MAX_POLLS = 40  # ~2 minutes ceiling

# Installed before any site JS runs (Playwright add_init_script) — Cloudflare's
# own challenge script defines window.turnstile and calls .render(container,
# params) once it decides the automatic pass failed and the widget needs to
# show. Overriding .render lets us capture those params without ever needing
# the widget to actually become visible/interactive.
TEMPMAILG_INTERCEPT_JS = """
window.__ts_params = null;
window.__ts_callback = null;
const __tsWait = setInterval(() => {
    if (window.turnstile) {
        clearInterval(__tsWait);
        window.turnstile.render = (a, b) => {
            window.__ts_params = {sitekey: b.sitekey, action: b.action,
                                   cData: b.cData, chlPageData: b.chlPageData,
                                   websiteURL: window.location.href};
            window.__ts_callback = b.callback;
            return 'tempmailg-intercepted';
        };
    }
}, 10);
"""


def _tempmailg_2captcha_solve(params):
    """POST /createTask + poll /getTaskResult — pure HTTP, this is the part
    that actually solves the widget. Returns the solved token, or None.
    """
    _http = curl_requests or requests
    try:
        resp = _http.post("https://api.2captcha.com/createTask", json={
            "clientKey": TEMPMAILG_2CAPTCHA_KEY,
            "task": {
                "type": "TurnstileTaskProxyless",
                "websiteURL": params["websiteURL"],
                "websiteKey": params["sitekey"],
                "action": params["action"],
                "data": params["cData"],
                "pagedata": params["chlPageData"],
                "useragent": TEMPMAILG_UA,
            },
        }, timeout=20)
        data = resp.json()
        if data.get("errorId") != 0:
            return None
        task_id = data["taskId"]
    except Exception:
        return None

    for _ in range(TEMPMAILG_2CAPTCHA_MAX_POLLS):
        time.sleep(TEMPMAILG_2CAPTCHA_POLL_S)
        try:
            resp = _http.post("https://api.2captcha.com/getTaskResult",
                               json={"clientKey": TEMPMAILG_2CAPTCHA_KEY, "taskId": task_id},
                               timeout=20)
            data = resp.json()
        except Exception:
            continue
        if data.get("status") == "ready":
            return (data.get("solution") or {}).get("token")
        if data.get("errorId") not in (0, None):
            return None
    return None


def _tempmailg_solve_challenge():
    """The only part of this provider that touches a browser: a brief
    headless burst just to get past Cloudflare (load page, grab Turnstile
    params, hand them to 2captcha, replay the solved token through the
    site's own callback, wait for the page to confirm it cleared). Returns
    a {cookie_name: value} dict (tempmailg.com cookies only, including
    cf_clearance) on success, or None.
    """
    if sync_playwright is None:
        return None
    try:
        with sync_playwright() as pw:
            try:
                browser = pw.chromium.launch(
                    headless=True, channel="chrome",
                    args=["--disable-blink-features=AutomationControlled", "--headless=new"],
                    ignore_default_args=["--enable-automation"])
            except Exception:
                browser = pw.chromium.launch(
                    headless=True,
                    args=["--disable-blink-features=AutomationControlled", "--headless=new"],
                    ignore_default_args=["--enable-automation"])
            try:
                context = browser.new_context(user_agent=TEMPMAILG_UA)
                context.add_init_script(TEMPMAILG_INTERCEPT_JS)
                page = context.new_page()
                page.goto("https://tempmailg.com/", timeout=45000)

                params = None
                for _ in range(20):
                    page.wait_for_timeout(500)
                    try:
                        params = page.evaluate("window.__ts_params")
                    except Exception:
                        params = None
                    if params:
                        break
                if not params:
                    return None

                token = _tempmailg_2captcha_solve(params)
                if not token:
                    return None

                page.evaluate("(tok) => window.__ts_callback && window.__ts_callback(tok)", token)

                cleared = False
                for _ in range(20):
                    page.wait_for_timeout(1000)
                    try:
                        cleared = bool(page.eval_on_selector(
                            'meta[name="csrf-token"]',
                            "el => el && el.content && el.content.length > 10"))
                    except Exception:
                        cleared = False
                    if cleared:
                        break
                if not cleared:
                    return None

                cookies = {c["name"]: c["value"] for c in context.cookies()
                           if "tempmailg.com" in c.get("domain", "")}
                return cookies if cookies.get("cf_clearance") else None
            finally:
                browser.close()
    except Exception:
        return None


def tempmailg_get_email(domain=None):
    cookies = _tempmailg_solve_challenge()
    if not cookies:
        return None, None

    _http_mod = curl_requests or requests
    session = _http_mod.Session(impersonate="chrome124") if curl_requests else _http_mod.Session()
    for name, value in cookies.items():
        session.cookies.set(name, value, domain="tempmailg.com")
    session.headers.update({"User-Agent": TEMPMAILG_UA})

    try:
        resp = session.get("https://tempmailg.com/", timeout=REQUEST_TIMEOUT)
        m = re.search(r'<meta name="csrf-token" content="([^"]+)"', resp.text or "")
        token = m.group(1) if m else None
        if not token:
            return None, None

        dom = domain if domain in TEMPMAILG_DOMAINS else random.choice(TEMPMAILG_DOMAINS)
        local_part = "".join(random.choices(string.ascii_lowercase + string.digits, k=10))
        headers = {"Content-Type": "application/json", "Accept": "application/json",
                   "X-Requested-With": "XMLHttpRequest", "Referer": "https://tempmailg.com/"}
        resp = session.post("https://tempmailg.com/change", headers=headers, json={
            "_token": token, "name": local_part, "domain": dom, "provider": "standard",
            "gmail_alias_mode": "auto", "gmail_alias_domain": "random",
            "alias_username": "", "lifetime": "1h",
        }, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        mailbox = resp.json().get("mailbox")
        if not mailbox:
            return None, None
        return mailbox, {"session": session, "token": token}
    except Exception:
        return None, None


def tempmailg_get_emails(email, ctx=None):
    if not ctx:
        return []
    session = ctx.get("session")
    token = ctx.get("token")
    if not session or not token:
        return []
    try:
        headers = {"Content-Type": "application/json", "Accept": "application/json",
                   "X-Requested-With": "XMLHttpRequest", "Referer": "https://tempmailg.com/"}
        resp = session.post("https://tempmailg.com/get_messages", headers=headers, json={
            "_token": token, "provider": "standard", "gmail_alias_mode": "auto",
            "gmail_alias_domain": "random", "alias_username": "",
        }, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        messages = (resp.json() or {}).get("messages") or []
        if not messages:
            return []
        result = []
        for msg in messages:
            msg_id = msg.get("id")
            if msg_id is None:
                continue
            try:
                r2 = session.get(f"https://tempmailg.com/view/{msg_id}", timeout=REQUEST_TIMEOUT)
                html = r2.text if r2.status_code == 200 else ""
            except Exception:
                html = ""
            result.append({"body_html": html or "", "body": html or ""})
        return result
    except Exception:
        return []


# --- temp-mail.org (pool-based — a handful of background threads keep a
# queue of pre-generated mailboxes topped up, so a registration usually
# grabs one instantly instead of waiting on the create-mailbox round trip;
# falls back to creating one inline if the pool is empty) ---
TEMPMAIL_ORG_API = "https://web2.temp-mail.org"
_tmorg_pool = queue.Queue()
_TMORG_FILLER_THREADS = 4
_TMORG_POOL_MAX = 60
_tmorg_proxy_text = None

def tempmailorg_set_proxy(proxy_str):
    global _tmorg_proxy_text
    _tmorg_proxy_text = proxy_str

def _tmorg_proxy_kwargs():
    """Build proxy kwargs for one-off curl_cffi / requests calls."""
    raw = _tmorg_proxy_text
    if not raw or not raw.strip():
        return {}
    host_port_url, auth = split_proxy_auth(raw.strip())
    if not host_port_url:
        return {}
    if curl_requests:
        kw = {"proxies": {"http": host_port_url, "https": host_port_url}}
        if auth:
            kw["proxy_auth"] = auth
        return kw
    else:
        if auth:
            scheme, rest = host_port_url.split("://", 1)
            url = (f"{scheme}://{urllib.parse.quote(auth[0], safe='')}:"
                   f"{urllib.parse.quote(auth[1], safe='')}@{rest}")
        else:
            url = host_port_url
        return {"proxies": {"http": url, "https": url}}

def _tmorg_pool_filler(filler_id):
    """Each filler thread has its own rate limiter — no global lock."""
    last_req = 0.0
    while True:
        try:
            if _tmorg_pool.qsize() >= _TMORG_POOL_MAX:
                time.sleep(2)
                continue
            now = time.time()
            wait = 1.0 - (now - last_req)
            if wait > 0:
                time.sleep(wait)
            last_req = time.time()
            headers = {"Accept": "application/json", "Content-Type": "application/json"}
            proxy_kw = _tmorg_proxy_kwargs()
            for attempt in range(3):
                try:
                    if curl_requests:
                        resp = curl_requests.post(f"{TEMPMAIL_ORG_API}/mailbox",
                                                  headers=headers, json={},
                                                  timeout=REQUEST_TIMEOUT, impersonate="chrome120",
                                                  **proxy_kw)
                    else:
                        resp = requests.post(f"{TEMPMAIL_ORG_API}/mailbox",
                                             headers=headers, json={}, timeout=REQUEST_TIMEOUT,
                                             **proxy_kw)
                    if resp.status_code == 429:
                        time.sleep(3 + attempt * 3)
                        continue
                    if resp.status_code == 200:
                        data = resp.json()
                        email = data.get("mailbox")
                        token = data.get("token")
                        if email and token:
                            _tmorg_pool.put((email, token))
                    break
                except Exception:
                    if attempt < 2:
                        time.sleep(2)
                        continue
                    break
        except Exception:
            time.sleep(5)

def _start_tmorg_pool():
    for i in range(_TMORG_FILLER_THREADS):
        t = threading.Thread(target=_tmorg_pool_filler, args=(i,), daemon=True)
        t.start()
        time.sleep(0.3)

_start_tmorg_pool()


def _tmorg_request(method, path, token=None, json_body=None):
    """Used for reading messages (not pool filling)."""
    headers = {"Accept": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    if json_body is not None:
        headers["Content-Type"] = "application/json"
    proxy_kw = _tmorg_proxy_kwargs()
    for attempt in range(3):
        try:
            if curl_requests:
                if method == "POST":
                    resp = curl_requests.post(f"{TEMPMAIL_ORG_API}{path}",
                                              headers=headers, json=json_body,
                                              timeout=REQUEST_TIMEOUT, impersonate="chrome120",
                                              **proxy_kw)
                else:
                    resp = curl_requests.get(f"{TEMPMAIL_ORG_API}{path}",
                                             headers=headers, timeout=REQUEST_TIMEOUT, impersonate="chrome120",
                                             **proxy_kw)
            else:
                if method == "POST":
                    resp = requests.post(f"{TEMPMAIL_ORG_API}{path}",
                                         headers=headers, json=json_body, timeout=REQUEST_TIMEOUT,
                                         **proxy_kw)
                else:
                    resp = requests.get(f"{TEMPMAIL_ORG_API}{path}",
                                        headers=headers, timeout=REQUEST_TIMEOUT,
                                        **proxy_kw)
            if resp.status_code == 429:
                time.sleep(3 + attempt * 2)
                continue
            return resp
        except Exception:
            if attempt < 2:
                time.sleep(2)
                continue
            raise
    return resp


def _tmorg_create_inline():
    """Create a Temp-Mail.org mailbox directly (bypass pool)."""
    headers = {"Accept": "application/json", "Content-Type": "application/json"}
    proxy_kw = _tmorg_proxy_kwargs()
    for attempt in range(3):
        try:
            if curl_requests:
                resp = curl_requests.post(f"{TEMPMAIL_ORG_API}/mailbox",
                                          headers=headers, json={},
                                          timeout=REQUEST_TIMEOUT, impersonate="chrome120",
                                          **proxy_kw)
            else:
                resp = requests.post(f"{TEMPMAIL_ORG_API}/mailbox",
                                     headers=headers, json={}, timeout=REQUEST_TIMEOUT,
                                     **proxy_kw)
            if resp.status_code == 429:
                time.sleep(2 + attempt * 2)
                continue
            if resp.status_code == 200:
                data = resp.json()
                email = data.get("mailbox")
                token = data.get("token")
                if email and token:
                    return email, token
            break
        except Exception:
            if attempt < 2:
                time.sleep(1)
                continue
            break
    return None, None

def tempmailorg_get_email(timeout=90):
    try:
        return _tmorg_pool.get(timeout=min(timeout, 5))
    except queue.Empty:
        return _tmorg_create_inline()

def tempmailorg_get_emails(email, ctx=None):
    if not ctx:
        return []
    try:
        resp = _tmorg_request("GET", "/messages", token=ctx)
        if resp.status_code != 200:
            return []
        data = resp.json()
        messages = data.get("messages", [])
        if not messages:
            return []
        result = []
        for msg in messages:
            mid = msg.get("_id") or msg.get("id", "")
            try:
                detail = _tmorg_request("GET", f"/messages/{mid}", token=ctx)
                if detail.status_code == 200:
                    d = detail.json()
                    body = d.get("bodyHtml") or d.get("body") or ""
                    result.append({"body_html": body, "body": body})
            except Exception:
                continue
        return result
    except Exception:
        return []


# --- tinyhost.shop ---
TINYHOST_API = "https://tinyhost.shop"

def _tinyhost_proxy_kwargs():
    return _tmorg_proxy_kwargs()

def tinyhost_get_email(timeout=30):
    proxy_kw = _tinyhost_proxy_kwargs()
    for attempt in range(3):
        try:
            if curl_requests:
                resp = curl_requests.get(f"{TINYHOST_API}/api/random-domains/?limit=20",
                                         timeout=REQUEST_TIMEOUT, impersonate="chrome120", **proxy_kw)
            else:
                resp = requests.get(f"{TINYHOST_API}/api/random-domains/?limit=20",
                                    timeout=REQUEST_TIMEOUT, **proxy_kw)
            if resp.status_code != 200:
                time.sleep(2)
                continue
            data = resp.json()
            domains = data.get("domains", [])
            if not domains:
                time.sleep(2)
                continue
            domain = random.choice(domains)
            user = ''.join(random.choices('abcdefghijklmnopqrstuvwxyz0123456789', k=12))
            email = f"{user}@{domain}"
            return email, {"domain": domain, "user": user}
        except Exception:
            if attempt < 2:
                time.sleep(2)
                continue
            break
    return None, None

def tinyhost_get_emails(email, ctx=None):
    if not ctx:
        return []
    proxy_kw = _tinyhost_proxy_kwargs()
    try:
        domain = ctx["domain"]
        user = ctx["user"]
        if curl_requests:
            resp = curl_requests.get(f"{TINYHOST_API}/api/email/{domain}/{user}/?page=1&limit=50",
                                     timeout=REQUEST_TIMEOUT, impersonate="chrome120", **proxy_kw)
        else:
            resp = requests.get(f"{TINYHOST_API}/api/email/{domain}/{user}/?page=1&limit=50",
                                timeout=REQUEST_TIMEOUT, **proxy_kw)
        if resp.status_code != 200:
            return []
        data = resp.json()
        emails_list = data.get("emails", [])
        result = []
        for msg in emails_list:
            body = msg.get("html_body") or msg.get("body") or ""
            result.append({"body_html": body, "body": body})
        return result
    except Exception:
        return []

# --- best-temp-mail.com ---
BESTTEMPMAIL_API = "https://best-temp-mail.com/api/v3"

def besttempmail_get_email(timeout=30):
    proxy_kw = _tmorg_proxy_kwargs()
    headers = {"Accept": "application/json", "Content-Type": "application/json",
               "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
               "Origin": "https://best-temp-mail.com", "Referer": "https://best-temp-mail.com/"}
    for attempt in range(3):
        try:
            if curl_requests:
                resp = curl_requests.post(f"{BESTTEMPMAIL_API}/createEmail",
                                          headers=headers, json={},
                                          timeout=REQUEST_TIMEOUT, impersonate="chrome120", **proxy_kw)
            else:
                resp = requests.post(f"{BESTTEMPMAIL_API}/createEmail",
                                     headers=headers, json={}, timeout=REQUEST_TIMEOUT, **proxy_kw)
            if resp.status_code != 200:
                time.sleep(2)
                continue
            data = resp.json()
            if data.get("status") != "success":
                time.sleep(2)
                continue
            info = data.get("data", {})
            address = info.get("address")
            mail_id = info.get("id")
            update_tag = info.get("update_tag")
            if address and mail_id:
                return address, {"id": mail_id, "update_tag": update_tag}
            break
        except Exception:
            if attempt < 2:
                time.sleep(2)
                continue
            break
    return None, None

def besttempmail_get_emails(email, ctx=None):
    if not ctx:
        return []
    proxy_kw = _tmorg_proxy_kwargs()
    headers = {"Accept": "application/json", "Content-Type": "application/json",
               "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
               "Origin": "https://best-temp-mail.com", "Referer": "https://best-temp-mail.com/"}
    try:
        body = {"id": ctx["id"]}
        if ctx.get("update_tag"):
            body["update_tag"] = ctx["update_tag"]
        if curl_requests:
            resp = curl_requests.post(f"{BESTTEMPMAIL_API}/getEmailList",
                                      headers=headers, json=body,
                                      timeout=REQUEST_TIMEOUT, impersonate="chrome120", **proxy_kw)
        else:
            resp = requests.post(f"{BESTTEMPMAIL_API}/getEmailList",
                                 headers=headers, json=body, timeout=REQUEST_TIMEOUT, **proxy_kw)
        if resp.status_code != 200:
            return []
        data = resp.json()
        info = data.get("data", {})
        if not info.get("hasNewEmail", False):
            return []
        emails_list = info.get("emails", [])
        result = []
        for msg in emails_list:
            body_html = msg.get("html_body") or msg.get("body") or msg.get("text") or ""
            result.append({"body_html": body_html, "body": body_html})
        return result
    except Exception:
        return []

# --- tmailor.com (Cloudflare-protected — same Turnstile bypass as tempmailg) ---
TMAILOR_API = "https://tmailor.com/api"
TMAILOR_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
_tmailor_cf_cache = {"session": None, "expire": 0}
_tmailor_cf_lock = threading.Lock()


def _tmailor_solve_challenge():
    if sync_playwright is None:
        return None
    try:
        with sync_playwright() as pw:
            try:
                browser = pw.chromium.launch(
                    headless=True, channel="chrome",
                    args=["--disable-blink-features=AutomationControlled", "--headless=new"],
                    ignore_default_args=["--enable-automation"])
            except Exception:
                browser = pw.chromium.launch(
                    headless=True,
                    args=["--disable-blink-features=AutomationControlled", "--headless=new"],
                    ignore_default_args=["--enable-automation"])
            try:
                context = browser.new_context(user_agent=TMAILOR_UA)
                context.add_init_script(TEMPMAILG_INTERCEPT_JS)
                page = context.new_page()
                page.goto("https://tmailor.com/", timeout=45000)

                params = None
                for _ in range(20):
                    page.wait_for_timeout(500)
                    try:
                        params = page.evaluate("window.__ts_params")
                    except Exception:
                        params = None
                    if params:
                        break
                if not params:
                    return None

                token = _tempmailg_2captcha_solve(params)
                if not token:
                    return None

                page.evaluate("(tok) => window.__ts_callback && window.__ts_callback(tok)", token)

                cleared = False
                for _ in range(20):
                    page.wait_for_timeout(1000)
                    try:
                        title = page.title() or ""
                        if "just a moment" not in title.lower() and len(title) > 0:
                            cleared = True
                            break
                    except Exception:
                        pass
                if not cleared:
                    return None

                cookies = {c["name"]: c["value"] for c in context.cookies()
                           if "tmailor.com" in c.get("domain", "")}
                return cookies if cookies.get("cf_clearance") else None
            finally:
                browser.close()
    except Exception:
        return None


def _tmailor_get_session():
    with _tmailor_cf_lock:
        cache = _tmailor_cf_cache
        if cache["session"] and time.time() < cache["expire"]:
            return cache["session"]

    cookies = _tmailor_solve_challenge()
    if not cookies:
        return None

    _http_mod = curl_requests or requests
    session = _http_mod.Session(impersonate="chrome124") if curl_requests else _http_mod.Session()
    for name, value in cookies.items():
        session.cookies.set(name, value, domain="tmailor.com")
    session.headers.update({"User-Agent": TMAILOR_UA})

    with _tmailor_cf_lock:
        _tmailor_cf_cache["session"] = session
        _tmailor_cf_cache["expire"] = time.time() + 300
    return session


def tmailor_get_email(timeout=30):
    session = _tmailor_get_session()
    if not session:
        return None, None

    headers = {"Accept": "application/json", "Content-Type": "application/json",
               "Origin": "https://tmailor.com", "Referer": "https://tmailor.com/"}
    for attempt in range(2):
        try:
            resp = session.post(f"{TMAILOR_API}/webapp-newemail",
                                headers=headers, json={}, timeout=REQUEST_TIMEOUT)
            if resp.status_code == 403:
                with _tmailor_cf_lock:
                    _tmailor_cf_cache["expire"] = 0
                session = _tmailor_get_session()
                if not session:
                    return None, None
                continue
            if resp.status_code != 200:
                time.sleep(1)
                continue
            data = resp.json()
            if data.get("msg") != "ok":
                time.sleep(1)
                continue
            email = data.get("email")
            atoken = data.get("accesstoken")
            if email and atoken:
                return email, {"accesstoken": atoken, "session": session}
            break
        except Exception:
            if attempt < 1:
                time.sleep(1)
                continue
            break
    return None, None


def tmailor_get_emails(email, ctx=None):
    if not ctx:
        return []
    if isinstance(ctx, dict):
        accesstoken = ctx.get("accesstoken")
        session = ctx.get("session")
    else:
        accesstoken = ctx
        session = None
    if not accesstoken:
        return []
    if not session:
        session = _tmailor_get_session()
    if not session:
        return []

    headers = {"Accept": "application/json", "Content-Type": "application/json",
               "Origin": "https://tmailor.com", "Referer": "https://tmailor.com/"}
    try:
        resp = session.post(f"{TMAILOR_API}/webapp-emaillist",
                            headers=headers, json={"accesstoken": accesstoken},
                            timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        raw = resp.text.strip()
        if not raw:
            return []
        data = resp.json()
        emails_list = data if isinstance(data, list) else data.get("emails", data.get("messages", []))
        if not isinstance(emails_list, list):
            return []
        result = []
        for msg in emails_list:
            body_html = ""
            if isinstance(msg, dict):
                body_html = msg.get("html_body") or msg.get("body_html") or msg.get("body") or msg.get("text") or ""
            elif isinstance(msg, str):
                body_html = msg
            if body_html:
                result.append({"body_html": body_html, "body": body_html})
        return result
    except Exception:
        return []

# --- mail.td ---
MAILTD_API = "https://api.mail.td"
_mailtd_token = None

def mailtd_set_token(token):
    global _mailtd_token
    _mailtd_token = token

def mailtd_get_email(timeout=30):
    if not _mailtd_token:
        return None, None
    proxy_kw = _tmorg_proxy_kwargs()
    headers = {"Authorization": f"Bearer {_mailtd_token}",
               "Content-Type": "application/json", "Accept": "application/json"}
    for attempt in range(3):
        try:
            # get available domains
            if curl_requests:
                dr = curl_requests.get(f"{MAILTD_API}/api/domains",
                                       timeout=REQUEST_TIMEOUT, impersonate="chrome120", **proxy_kw)
            else:
                dr = requests.get(f"{MAILTD_API}/api/domains", timeout=REQUEST_TIMEOUT, **proxy_kw)
            if dr.status_code != 200:
                time.sleep(2)
                continue
            domains_data = dr.json()
            domains = [d["domain"] for d in domains_data.get("domains", []) if d.get("is_active")]
            if not domains:
                break
            domain = random.choice(domains)
            user = ''.join(random.choices('abcdefghijklmnopqrstuvwxyz0123456789', k=10))
            address = f"{user}@{domain}"
            password = ''.join(random.choices('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=20))
            body = {"address": address, "password": password}
            if curl_requests:
                resp = curl_requests.post(f"{MAILTD_API}/api/accounts",
                                          headers=headers, json=body,
                                          timeout=REQUEST_TIMEOUT, impersonate="chrome120", **proxy_kw)
            else:
                resp = requests.post(f"{MAILTD_API}/api/accounts",
                                     headers=headers, json=body, timeout=REQUEST_TIMEOUT, **proxy_kw)
            if resp.status_code in (200, 201):
                data = resp.json()
                account_id = data.get("id") or address
                return address, {"account_id": account_id, "token": _mailtd_token}
            break
        except Exception:
            if attempt < 2:
                time.sleep(2)
                continue
            break
    return None, None

def mailtd_get_emails(email, ctx=None):
    if not ctx:
        return []
    proxy_kw = _tmorg_proxy_kwargs()
    headers = {"Authorization": f"Bearer {ctx['token']}",
               "Accept": "application/json"}
    try:
        account_id = ctx["account_id"]
        if curl_requests:
            resp = curl_requests.get(f"{MAILTD_API}/api/accounts/{account_id}/messages?page=1",
                                     headers=headers, timeout=REQUEST_TIMEOUT,
                                     impersonate="chrome120", **proxy_kw)
        else:
            resp = requests.get(f"{MAILTD_API}/api/accounts/{account_id}/messages?page=1",
                                headers=headers, timeout=REQUEST_TIMEOUT, **proxy_kw)
        if resp.status_code != 200:
            return []
        data = resp.json()
        messages = data.get("messages", [])
        result = []
        for msg in messages:
            mid = msg.get("id", "")
            try:
                if curl_requests:
                    det = curl_requests.get(f"{MAILTD_API}/api/accounts/{account_id}/messages/{mid}",
                                            headers=headers, timeout=REQUEST_TIMEOUT,
                                            impersonate="chrome120", **proxy_kw)
                else:
                    det = requests.get(f"{MAILTD_API}/api/accounts/{account_id}/messages/{mid}",
                                       headers=headers, timeout=REQUEST_TIMEOUT, **proxy_kw)
                if det.status_code == 200:
                    d = det.json()
                    body = d.get("html_body") or d.get("text_body") or ""
                    result.append({"body_html": body, "body": body})
            except Exception:
                continue
        return result
    except Exception:
        return []


# --- temp.tf (real Outlook/Gmail/Hotmail via plus-aliases — no captcha) ---
TEMPTF_API = "https://temp.tf/api"
TEMPTF_PROVIDERS_DEFAULT = "outlook,hotmail,gmail"

def temptf_get_email(domain=None):
    _http = curl_requests or requests
    providers = TEMPTF_PROVIDERS_DEFAULT
    if domain:
        providers = domain
    try:
        url = f"{TEMPTF_API}/account?providers={urllib.parse.quote(providers)}&dot=1&plus=1"
        if curl_requests:
            resp = curl_requests.get(url, timeout=REQUEST_TIMEOUT, impersonate="chrome124")
        else:
            resp = _http.get(url, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        data = resp.json()
        email = data.get("email")
        if not email:
            return None, None
        return email, {"email": email}
    except Exception:
        return None, None

def temptf_get_emails(email, ctx=None):
    _http = curl_requests or requests
    address = email
    if ctx and isinstance(ctx, dict):
        address = ctx.get("email", email)
    try:
        if curl_requests:
            resp = curl_requests.post(f"{TEMPTF_API}/check",
                                       json={"email": address, "wait": True},
                                       timeout=60, impersonate="chrome124")
        else:
            resp = _http.post(f"{TEMPTF_API}/check",
                              json={"email": address, "wait": True},
                              headers={"Content-Type": "application/json"},
                              timeout=60)
        if resp.status_code != 200:
            return []
        data = resp.json()
        messages = data.get("data", [])
        if not isinstance(messages, list):
            return []
        result = []
        for msg in messages:
            body = msg.get("body", "")
            is_html = msg.get("bodyContentType") == "html"
            result.append({"body_html": body if is_html else "", "body": body})
        return result
    except Exception:
        return []


# --- mailyra.com (10 disposable domains, session-cookie-based, no captcha) ---
MAILYRA_DOMAINS = ["mailyra.com", "invoxica.com", "receivory.com", "go9.co", "tmtm.me",
                    "aigram.kr", "beauturn.com", "leaseyo.kr", "krseller.com", "1004cat.com"]

def mailyra_get_email(domain=None):
    _http_mod = curl_requests or requests
    try:
        session = _http_mod.Session(impersonate="chrome124") if curl_requests else _http_mod.Session()
        dom = domain if domain in MAILYRA_DOMAINS else random.choice(MAILYRA_DOMAINS)
        resp = session.post(f"https://mailyra.com/en/api/new.php",
                            data={"domain": dom} if domain else {},
                            timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        data = resp.json()
        if not data.get("ok"):
            return None, None
        inbox = data.get("data", {}).get("inbox", {})
        email = inbox.get("email")
        if not email:
            return None, None
        return email, {"session": session}
    except Exception:
        return None, None

def mailyra_get_emails(email, ctx=None):
    if not ctx or not isinstance(ctx, dict):
        return []
    session = ctx.get("session")
    if not session:
        return []
    try:
        resp = session.get("https://mailyra.com/en/api/list.php", timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        data = resp.json()
        if not data.get("ok"):
            return []
        messages = data.get("data", {}).get("messages", [])
        if not messages:
            return []
        result = []
        for msg in messages:
            msg_id = msg.get("id")
            if not msg_id:
                continue
            try:
                detail = session.get(f"https://mailyra.com/en/api/view.php?id={msg_id}",
                                     timeout=REQUEST_TIMEOUT)
                if detail.status_code == 200:
                    md = detail.json()
                    if md.get("ok"):
                        msg_data = md.get("data", {}).get("message", md.get("data", {}))
                        body_html = msg_data.get("html") or msg_data.get("body") or msg_data.get("content") or ""
                        result.append({"body_html": body_html, "body": body_html})
                        continue
            except Exception:
                pass
            body_html = msg.get("html") or msg.get("body") or msg.get("content") or ""
            if body_html:
                result.append({"body_html": body_html, "body": body_html})
        return result
    except Exception:
        return []


# --- smailpro.com (Outlook / Gmail / Hotmail temp email via API) ---
# Pure HTTP: GET /app/create → address + JWT key, POST /app/inbox → messages,
# GET /app/message → payload → GET api.sonjj.com → body.
# x-captcha header with a Cloudflare Turnstile token is required for /app/create
# and /app/message. With rotating proxies the captcha may not appear (invisible
# mode auto-passes), but if it does, 2captcha TurnstileTaskProxyless is used.
SMAILPRO_TURNSTILE_SITEKEY = "0x4AAAAAAABIS_gEec2IwOhI"
SMAILPRO_DOMAIN_TYPES = {
    "gmail.com": "google", "googlemail.com": "google",
    "outlook.com": "microsoft", "hotmail.com": "microsoft",
    "outlook.kr": "microsoft", "outlook.fr": "microsoft",
    "outlook.com.vn": "microsoft", "outlook.co.id": "microsoft",
    "outlook.co.th": "microsoft", "outlook.com.ar": "microsoft",
    "outlook.co.il": "microsoft",
}
SMAILPRO_MSG_URLS = {
    "google":    "https://api.sonjj.com/v1/temp_gmail/message",
    "microsoft": "https://api.sonjj.com/v1/temp_outlook/message",
    "other":     "https://api.sonjj.com/v1/temp_email/message",
}
SMAILPRO_FREE_DOMAINS = [
    "outlook.com", "hotmail.com", "outlook.kr", "outlook.fr",
    "outlook.com.vn", "outlook.co.id", "outlook.co.th",
    "outlook.com.ar", "outlook.co.il",
    "gmail.com", "googlemail.com",
    "melbourne.edu.pl", "sydney.edu.pl", "tokyo.edu.pl", "storegmail.net",
]
_smailpro_2captcha_key = os.environ.get("SMAILPRO_2CAPTCHA_KEY", "")

def smailpro_set_2captcha_key(key):
    global _smailpro_2captcha_key
    _smailpro_2captcha_key = key

def _smailpro_log(msg):
    try:
        sender_log(f"[Smailpro] {msg}")
    except Exception:
        pass

def _smailpro_solve_turnstile(action="smailpro_create"):
    api_key = _smailpro_2captcha_key or TEMPMAILG_2CAPTCHA_KEY
    if not api_key:
        _smailpro_log("нет 2captcha API ключа — капчу не решить")
        return ""
    _smailpro_log(f"решаю Turnstile через 2captcha (action={action})...")
    _http = curl_requests or requests
    try:
        resp = _http.post("https://api.2captcha.com/createTask", json={
            "clientKey": api_key,
            "task": {
                "type": "TurnstileTaskProxyless",
                "websiteURL": "https://smailpro.com/temporary-email",
                "websiteKey": SMAILPRO_TURNSTILE_SITEKEY,
                "action": action,
            },
        }, timeout=20)
        data = resp.json()
        if data.get("errorId") != 0:
            _smailpro_log(f"2captcha createTask ошибка: {data.get('errorDescription', data.get('errorId'))}")
            return ""
        task_id = data["taskId"]
        _smailpro_log(f"2captcha задача создана (taskId={task_id}), жду решение...")
    except Exception as e:
        _smailpro_log(f"2captcha createTask исключение: {e}")
        return ""
    for poll_i in range(TEMPMAILG_2CAPTCHA_MAX_POLLS):
        time.sleep(TEMPMAILG_2CAPTCHA_POLL_S)
        try:
            resp = _http.post("https://api.2captcha.com/getTaskResult",
                               json={"clientKey": api_key, "taskId": task_id},
                               timeout=20)
            data = resp.json()
        except Exception:
            continue
        if data.get("status") == "ready":
            token = (data.get("solution") or {}).get("token") or ""
            if token:
                _smailpro_log(f"Turnstile решён ({len(token)} символов)")
            return token
        if data.get("errorId") not in (0, None):
            _smailpro_log(f"2captcha ошибка: {data.get('errorDescription', data.get('errorId'))}")
            return ""
    _smailpro_log("2captcha таймаут — капча не решена")
    return ""

def smailpro_get_email(domain=None):
    domain = domain if domain and domain in SMAILPRO_FREE_DOMAINS else "outlook.com"
    _http = curl_requests or requests
    url = f"https://smailpro.com/app/create?username=random&type=alias&domain={domain}&server=1"
    headers = {"Content-Type": "application/json",
               "Referer": "https://smailpro.com/temporary-email",
               "User-Agent": TEMPMAILG_UA}
    _smailpro_log(f"создаю email (домен={domain})...")
    captcha_token = _smailpro_solve_turnstile("smailpro_create")
    if not captcha_token:
        _smailpro_log("не удалось получить Turnstile-токен — email не создан")
        return None, None
    for attempt in range(3):
        try:
            resp = _http.get(url, headers={**headers, "x-captcha": captcha_token}, timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                err_text = ""
                try:
                    err_text = resp.json().get("msg", "")
                except Exception:
                    err_text = resp.text[:100] if resp.text else ""
                _smailpro_log(f"HTTP {resp.status_code}: {err_text}")
                if resp.status_code in (403, 429) and attempt < 2:
                    _smailpro_log("пересоздаю Turnstile-токен...")
                    captcha_token = _smailpro_solve_turnstile("smailpro_create")
                    if not captcha_token:
                        return None, None
                continue
            data = resp.json()
            address = data.get("address")
            if not address:
                _smailpro_log(f"ответ без address: {str(data)[:100]}")
                continue
            _smailpro_log(f"email создан: {address}")
            ctx = {
                "address": address,
                "timestamp": data.get("timestamp"),
                "key": data.get("key"),
                "domain": domain,
            }
            return address, ctx
        except Exception as e:
            _smailpro_log(f"исключение (попытка {attempt+1}/3): {e}")
            continue
    return None, None

def _smailpro_email_type(address):
    domain = address.rsplit("@", 1)[-1] if "@" in address else ""
    return SMAILPRO_DOMAIN_TYPES.get(domain, "other")

def smailpro_get_emails(email, ctx=None):
    """Smailpro inbox: 4-step flow per the HAR.
    1) POST /app/inbox [{address, timestamp, key}] → {payload} JWT per email
    2) GET api.sonjj.com/v1/temp_{type}/inbox?payload=<JWT> → {messages:[{mid,...}]}
    3) GET /app/message?email=&mid= (x-captcha) → message payload
    4) GET api.sonjj.com/v1/temp_{type}/message?payload= → {body}
    """
    if not ctx or not isinstance(ctx, dict):
        return []
    _http = curl_requests or requests
    address = ctx.get("address") or email
    timestamp = ctx.get("timestamp")
    key = ctx.get("key")
    if not address or not timestamp:
        return []
    headers = {"Content-Type": "application/json",
               "Referer": "https://smailpro.com/temporary-email",
               "User-Agent": TEMPMAILG_UA}
    email_type = _smailpro_email_type(address)
    inbox_url_map = {
        "google":    "https://api.sonjj.com/v1/temp_gmail/inbox",
        "microsoft": "https://api.sonjj.com/v1/temp_outlook/inbox",
        "other":     "https://api.sonjj.com/v1/temp_email/inbox",
    }
    sonjj_inbox_url = inbox_url_map.get(email_type, inbox_url_map["other"])
    sonjj_msg_url = SMAILPRO_MSG_URLS.get(email_type, SMAILPRO_MSG_URLS["other"])

    try:
        inbox_body = [{"address": address, "timestamp": timestamp, "key": key or ""}]
        resp = _http.post("https://smailpro.com/app/inbox",
                          json=inbox_body, headers=headers, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        emails_data = resp.json()
        if not isinstance(emails_data, list):
            return []
        our = None
        for e in emails_data:
            if e.get("address") == address:
                our = e
                break
        if not our:
            return []
        inbox_payload = our.get("payload")
        new_key = our.get("key")
        if new_key:
            ctx["key"] = new_key
        if not inbox_payload:
            return []
    except Exception:
        return []

    try:
        resp2 = _http.get(f"{sonjj_inbox_url}?payload={urllib.parse.quote(inbox_payload)}",
                          timeout=REQUEST_TIMEOUT)
        if resp2.status_code != 200:
            return []
        messages = resp2.json().get("messages") or []
        if not messages:
            return []
    except Exception:
        return []

    captcha_token = _smailpro_solve_turnstile("smailpro_message")
    result = []
    for msg in messages:
        mid = msg.get("mid")
        if not mid:
            continue
        try:
            msg_params = f"?email={urllib.parse.quote(address)}&mid={urllib.parse.quote(str(mid))}"
            msg_headers = {**headers, "x-captcha": captcha_token}
            pr = _http.get("https://smailpro.com/app/message" + msg_params,
                           headers=msg_headers, timeout=REQUEST_TIMEOUT)
            if pr.status_code in (403, 429):
                captcha_token = _smailpro_solve_turnstile("smailpro_message")
                msg_headers["x-captcha"] = captcha_token
                pr = _http.get("https://smailpro.com/app/message" + msg_params,
                               headers=msg_headers, timeout=REQUEST_TIMEOUT)
            if pr.status_code != 200:
                continue
            msg_payload = pr.text.strip()
            if not msg_payload:
                continue
            body_resp = _http.get(f"{sonjj_msg_url}?payload={urllib.parse.quote(msg_payload)}",
                                 timeout=REQUEST_TIMEOUT)
            if body_resp.status_code != 200:
                continue
            body_data = body_resp.json()
            body_html = body_data.get("body") or ""
            result.append({"body_html": body_html, "body": body_html})
        except Exception:
            continue
    return result


# --- Provider registry ---
TEMPMAIL_PROVIDERS = {
    "tempmailorg": {"label": "Temp-Mail.org",                "get_email": tempmailorg_get_email, "get_emails": tempmailorg_get_emails},
    "tinyhost":    {"label": "TinyHost.shop",                "get_email": tinyhost_get_email,   "get_emails": tinyhost_get_emails},
    "besttempmail":{"label": "Best-Temp-Mail.com",           "get_email": besttempmail_get_email,"get_emails": besttempmail_get_emails},
    "tmailor":     {"label": "Tmailor.com (CF + 2captcha)",   "get_email": tmailor_get_email,    "get_emails": tmailor_get_emails},
    "mailtd":      {"label": "Mail.td (Pro — нужен токен)",  "get_email": mailtd_get_email,     "get_emails": mailtd_get_emails},
    "tempmail4u":  {"label": "TempMail4u (jsontoexcel.net)", "get_email": tempmail4u_get_email, "get_emails": tempmail4u_get_emails},
    "1secmail":    {"label": "1secMail (.org/.net)",         "get_email": onesecmail_get_email, "get_emails": onesecmail_get_emails},
    "tempmail_lol":{"label": "TempMail.lol",                 "get_email": templol_get_email,    "get_emails": templol_get_emails},
    "mailtm":      {"label": "Mail.tm",                      "get_email": mailtm_get_email,     "get_emails": mailtm_get_emails},
    "mailgw":      {"label": "Mail.gw",                      "get_email": mailgw_get_email,     "get_emails": mailgw_get_emails},
    "emailnator":  {"label": "Emailnator (Gmail)",           "get_email": emailnator_get_email, "get_emails": emailnator_get_emails},
    "mohmal":      {"label": "Mohmal",                       "get_email": mohmal_get_email,     "get_emails": mohmal_get_emails},
    "tempmailg":   {"label": "TempMailG (Cloudflare + 2captcha)", "get_email": tempmailg_get_email, "get_emails": tempmailg_get_emails},
    "smailpro":    {"label": "Smailpro (Outlook/Gmail/Hotmail)", "get_email": smailpro_get_email, "get_emails": smailpro_get_emails},
    "temptf":      {"label": "Temp.tf (Gmail/Outlook/Hotmail)", "get_email": temptf_get_email,   "get_emails": temptf_get_emails},
    "mailyra":     {"label": "Mailyra (10 доменов)",            "get_email": mailyra_get_email,  "get_emails": mailyra_get_emails},
}
# Temp-Mail.org is the pipeline that's actually been confirmed live to get
# past DA's current signup validation (paired with the lu_token-aware
# da_register_account below) — it's the default and the first provider
# "auto" tries. Every provider below it is a fallback/manual-pick option.
DEFAULT_TEMPMAIL_PROVIDER = "tempmailorg"

AUTO_PROVIDER_ORDER = ["temptf", "smailpro", "mailtm", "tempmail_lol", "tempmailorg", "tinyhost", "besttempmail", "tmailor", "mailtd"]

def get_tempmail_provider(name=None):
    return TEMPMAIL_PROVIDERS.get(name or DEFAULT_TEMPMAIL_PROVIDER, TEMPMAIL_PROVIDERS[DEFAULT_TEMPMAIL_PROVIDER])


def auto_get_email(log_fn=None):
    """Try providers in order until one returns a valid email.
    Returns (email, ctx, provider_name) or (None, None, None).
    """
    for prov_name in AUTO_PROVIDER_ORDER:
        prov = TEMPMAIL_PROVIDERS.get(prov_name)
        if not prov:
            continue
        try:
            if prov_name == "tempmailorg":
                pool_sz = _tmorg_pool.qsize()
                if pool_sz > 0:
                    email, ctx = tempmailorg_get_email(timeout=5)
                else:
                    if log_fn:
                        log_fn(f"[auto] Temp-Mail.org пул пуст — создаю напрямую...")
                    email, ctx = _tmorg_create_inline()
            else:
                email, ctx = prov["get_email"]()
            if email:
                if log_fn:
                    log_fn(f"[auto] ✓ {prov['label']}: {email}")
                return email, ctx, prov_name
        except Exception:
            pass
        if log_fn:
            log_fn(f"[auto] {prov['label']} — не удалось, пробую следующий...")
    return None, None, None


def extract_deviantart_verify_link(email_body):
    """Extract the DeviantArt email confirmation link from the confirmation
    email's HTML body. DA sends these through SendGrid, which wraps every
    link as sg.deviantart.com/wf/click?upn=... (wf/open?upn=... is just the
    open-tracking pixel, not clickable — never return that one).
    """
    if not email_body:
        return None
    # Preferred: the anchor whose visible text mentions confirm/verify.
    match = re.search(r'href="([^"]*sg\.deviantart\.com/wf/click[^"]*)"[^>]*>\s*(?:<[^>]+>\s*)*(?:Confirm|Verify)',
                       email_body, re.IGNORECASE | re.DOTALL)
    if match:
        return match.group(1)
    # Any wf/click link at all (the confirm button is usually the first/only one).
    match = re.search(r'(https?://sg\.deviantart\.com/wf/click\?[^"\s]+)', email_body)
    if match:
        return match.group(1)
    # Older SendGrid path seen in some templates.
    match = re.search(r'href="([^"]*sg\.deviantart\.com/ls/click[^"]*)"[^>]*>\s*(?:<[^>]+>\s*)*(?:Confirm|Verify)',
                       email_body, re.IGNORECASE | re.DOTALL)
    if match:
        return match.group(1)
    match = re.search(r'(https?://sg\.deviantart\.com/ls/click\?[^"\s]+)', email_body)
    if match:
        return match.group(1)
    return None


REGISTER_DEBUG_FILE = BASE_DIR / "deviantart_register_debug.html"


def _describe_http_error(resp, step_name):
    """Build a readable error string for a failed registration HTTP call and
    dump the raw response body to disk so the real cause (WAF block,
    wrong endpoint, HTML error page, etc.) can be inspected afterwards.
    """
    body = resp.text or ""
    saved_path = ""
    try:
        REGISTER_DEBUG_FILE.write_text(
            f"<!-- step: {step_name} | status: {resp.status_code} | url: {resp.url} -->\n{body}",
            encoding="utf-8", errors="replace")
        saved_path = str(REGISTER_DEBUG_FILE)
    except Exception:
        pass

    reason = ""
    stripped = body.strip()
    if stripped.startswith("<!DOCTYPE") or stripped.startswith("<html") or stripped.startswith("<HTML"):
        title_match = re.search(r"<title[^>]*>(.*?)</title>", body, re.IGNORECASE | re.DOTALL)
        h1_match = re.search(r"<h1[^>]*>(.*?)</h1>", body, re.IGNORECASE | re.DOTALL)
        readable = (title_match.group(1) if title_match else (h1_match.group(1) if h1_match else "")).strip()
        reason = f"сервер вернул HTML-страницу ошибки{(' — ' + readable) if readable else ''} (не JSON API-ответ — вероятно, неверный эндпоинт, блок WAF/CDN или неверный домен)"
    elif resp.status_code in (401, 403):
        reason = "доступ запрещён (403/401) — возможно бан IP/прокси, неверные заголовки или блокировка антибот-защитой"
    elif resp.status_code == 429:
        reason = "слишком много запросов (429) — рейт-лимит"
    elif resp.status_code >= 500:
        reason = "ошибка на стороне сервера (5xx)"
    else:
        reason = "неожиданный ответ API"

    msg = f"{step_name} провалился: HTTP {resp.status_code} ({resp.url}) — {reason}"
    if saved_path:
        msg += f". HTML сохранён в {saved_path}"
    return msg


def _generate_password(length=14):
    chars = string.ascii_letters + string.digits + "!@#$%"
    while True:
        pwd = "".join(random.choices(chars, k=length))
        if any(c.isupper() for c in pwd) and any(c.islower() for c in pwd) and any(c.isdigit() for c in pwd):
            return pwd


def _extract_initial_state(html):
    m = re.search(r'window\.__INITIAL_STATE__\s*=\s*JSON\.parse\("(.+?)"\)\s*;', html or "")
    if not m:
        return None
    try:
        raw = m.group(1).encode().decode("unicode_escape")
        return json.loads(raw)
    except Exception:
        return None


def _signup_nav_headers(referer):
    return {
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7",
        "Referer": referer,
        "Origin": "https://www.deviantart.com",
        "Content-Type": "application/x-www-form-urlencoded",
        "sec-fetch-dest": "document",
        "sec-fetch-mode": "navigate",
        "sec-fetch-site": "same-origin",
        "sec-fetch-user": "?1",
        "upgrade-insecure-requests": "1",
        "cache-control": "max-age=0",
    }


_LU_PATTERNS = (
    re.compile(r'luToken\\":\\"([^"\\]+)'),
    re.compile(r'"luToken"\s*:\s*"([^"\\]+)'),
)


def _solve_awswaf_challenge_via_playwright(proxy_text=None, log_fn=None):
    """Launch Playwright headlessly, navigate to /join/, wait for the AWS WAF
    challenge JS to auto-solve, and extract (csrf_token, lu_token, cookies).

    Confirmed live: the AWS WAF challenge is proof-of-work (no captcha), and
    Playwright headless clears it in ~4s. Returns (csrf, lu, cookies, err) —
    cookies is a list of Playwright cookie dicts ready to inject into
    curl_cffi. The `aws-waf-token` cookie in that list is what lets
    subsequent curl_cffi requests through without another 202.
    """
    if sync_playwright is None:
        return None, "", None, "Playwright не установлен (pip install playwright)"

    proxy_cfg = None
    if proxy_text and proxy_text.strip():
        try:
            host_port_url, auth = split_proxy_auth(proxy_text)
            if host_port_url:
                proxy_cfg = {"server": host_port_url}
                if auth:
                    proxy_cfg["username"], proxy_cfg["password"] = auth
        except Exception:
            proxy_cfg = None

    # Free HTTP proxies often intercept HTTPS traffic (MITM) and re-sign it
    # with their own CA — Chromium then throws ERR_CERT_AUTHORITY_INVALID
    # and refuses to load the page. `--ignore-certificate-errors` in the
    # Chromium args plus `ignore_https_errors=True` on the context tells it
    # to trust whatever cert the proxy hands over. This alone recovered
    # ~9/100 attempts in the strategy-test log that had been failing on the
    # SSL check. Also `--disable-web-security` so mixed-content or CORS
    # inside the WAF challenge script doesn't block it under a proxied
    # request.
    _launch_args = [
        "--disable-blink-features=AutomationControlled",
        "--ignore-certificate-errors",
        "--allow-running-insecure-content",
        "--blink-settings=imagesEnabled=false",
    ]
    # Wait behind the semaphore so we don't have 20+ Chromium instances
    # fighting for CPU. Bounded wait — if we can't get a slot in 30s the
    # caller (a per-account retry loop) is better off rotating IP than
    # blocking here indefinitely.
    if not _PLAYWRIGHT_SEMAPHORE.acquire(timeout=30):
        return None, "", None, "Playwright: слот занят >30с (перегрузка)"
    try:
        with sync_playwright() as pw:
            try:
                browser = pw.chromium.launch(
                    headless=True, channel="chrome", proxy=proxy_cfg,
                    args=_launch_args,
                    ignore_default_args=["--enable-automation"])
            except Exception:
                browser = pw.chromium.launch(
                    headless=True, proxy=proxy_cfg,
                    args=_launch_args,
                    ignore_default_args=["--enable-automation"])
            try:
                context = browser.new_context(ignore_https_errors=True)
                page = context.new_page()
                page.route("**/*", lambda route: route.abort()
                           if route.request.resource_type in ("image", "font", "media", "stylesheet")
                           else route.continue_())
                try:
                    # 45s cap on the initial load — proxies that need longer
                    # are almost always dead; failing fast lets the caller
                    # rotate to a working IP instead of stalling this thread.
                    page.goto("https://www.deviantart.com/join/",
                              timeout=45000, wait_until="domcontentloaded")
                except Exception as e:
                    return None, "", None, f"Playwright goto: {str(e)[:150]}"

                csrf = None
                lu = ""
                # Poll up to 60s (was 120s). If challenge hasn't finished by
                # then the proxy is too slow to be useful — rotate faster.
                # 300ms polls (was 500ms) grab the csrf sooner on fast proxies.
                for _ in range(200):
                    page.wait_for_timeout(300)
                    try:
                        html = page.content()
                    except Exception:
                        continue

                    state = _extract_initial_state(html)
                    if state:
                        csrf = (state.get("@@config", {}).get("csrfToken")
                                or state.get("@@publicSession", {}).get("csrfToken")
                                or state.get("csrfToken"))
                        lu = state.get("luToken") or ""

                    if not csrf:
                        for pat in CSRF_PATTERNS:
                            m = pat.search(html)
                            if m:
                                csrf = m.group(1)
                                break
                    if not lu:
                        for lp in _LU_PATTERNS:
                            m = lp.search(html)
                            if m:
                                lu = m.group(1)
                                break
                    if csrf:
                        break

                if not csrf:
                    return None, "", None, "Playwright не смог получить csrf (challenge не прошёл за 60с)"

                cookies = context.cookies()
                return str(csrf), str(lu or ""), cookies, ""
            finally:
                try:
                    browser.close()
                except Exception:
                    pass
    except Exception as e:
        return None, "", None, f"Playwright исключение: {str(e)[:200]}"
    finally:
        _PLAYWRIGHT_SEMAPHORE.release()


def _apply_playwright_cookies_to_session(session, cookies):
    """Replace curl_cffi session cookies with Playwright's cookie jar.

    After Playwright solves the WAF challenge and loads /join/, its cookie
    set is the authoritative one — the csrf_token and lu_token it extracted
    are bound to these cookies. curl_cffi's old cookies (from the initial
    202 response) can conflict: DA may reject signup2 if it sees a stale or
    mismatched session cookie alongside the fresh WAF token. Clearing first
    ensures the POST uses exactly the session state Playwright established.
    """
    if not cookies:
        return 0
    try:
        session.cookies.clear()
    except Exception:
        pass
    n = 0
    for c in cookies:
        try:
            name = c.get("name")
            value = c.get("value")
            if not name:
                continue
            domain = c.get("domain") or ".deviantart.com"
            path = c.get("path") or "/"
            try:
                session.cookies.set(name, value, domain=domain, path=path)
            except TypeError:
                session.cookies.set(name, value)
            n += 1
        except Exception:
            continue
    return n


def _fetch_signup_tokens(session, log_fn=None):
    """GET /join/ and return (csrf_token, lu_token, err).

    lu_token is embedded in __INITIAL_STATE__ alongside csrfToken and is
    required as a hidden field in the signup2 POST — without it DA rejects
    the submission as a bot (confirmed live: this is exactly what was
    silently breaking every registration before — signup2 used to always
    respond 301/302 to /join/intent, now it just re-renders the join page
    with fresh tokens and a 200 whenever lu_token is missing/wrong).

    HTTP 202 with `x-amzn-waf-action: challenge` means DA/CloudFront served
    an AWS WAF proof-of-work challenge. curl_cffi can't execute JS, so we
    fall back to Playwright headless (which auto-solves in ~4s), then copy
    the resulting `aws-waf-token` cookie into this session so signup2 also
    passes.
    """
    try:
        resp = session.get("https://www.deviantart.com/join/",
                           headers=nav_h(session), timeout=45)
        html = resp.text or ""

        is_awswaf_challenge = (
            resp.status_code == 202
            and ("awswaf.com" in html or "AwsWafIntegration" in html
                 or resp.headers.get("x-amzn-waf-action") == "challenge")
        )
        if is_awswaf_challenge:
            if log_fn:
                log_fn("AWS WAF challenge (HTTP 202) — решаю через Playwright...")
            proxy_text = getattr(session, "_proxy_text", None)
            csrf, lu, cookies, err = _solve_awswaf_challenge_via_playwright(
                proxy_text=proxy_text, log_fn=log_fn)
            if csrf:
                added = _apply_playwright_cookies_to_session(session, cookies)
                if log_fn:
                    log_fn(f"WAF challenge пройден, csrf получен, куки скопированы ({added})")
                return csrf, lu, ""
            return None, "", f"AWS WAF: {err}"

        state = _extract_initial_state(html)
        if state:
            csrf = (state.get("@@config", {}).get("csrfToken")
                    or state.get("@@publicSession", {}).get("csrfToken")
                    or state.get("csrfToken"))
            lu = state.get("luToken") or ""
            if csrf:
                return str(csrf), str(lu), ""

        lu = ""
        for lp in _LU_PATTERNS:
            lm = lp.search(html)
            if lm:
                lu = lm.group(1)
                break

        for pat in CSRF_PATTERNS:
            m = pat.search(html)
            if m:
                return m.group(1), lu, ""

        if resp.status_code == 403:
            return None, "", "request could not be satisfied — /join/ вернул HTTP 403 (IP заблокирован)"
        return None, "", f"Не удалось найти csrfToken на /join/ (HTTP {resp.status_code})"
    except Exception as e:
        return None, "", str(e)[:200]


# Global rate limiter: ensures signup2 POSTs are spaced apart across all
# threads. Reduced to 0.5 s — with 45 threads old 5.0 s caused 225 s waits
# that expired csrf/lu_token, causing mass bot-detect failures.
_signup_rate_lock = threading.Lock()
_signup_last_time = 0.0
_SIGNUP_MIN_INTERVAL = 0.5  # seconds between successive signup2 POSTs


def _signup_rate_wait():
    """Block until at least _SIGNUP_MIN_INTERVAL has passed since the last
    signup POST, then record this slot's start time."""
    global _signup_last_time
    with _signup_rate_lock:
        now = time.time()
        wait = _signup_last_time + _SIGNUP_MIN_INTERVAL - now
        if wait > 0:
            time.sleep(wait)
        _signup_last_time = time.time()


def da_register_account(session, email, username, mail_provider=None, mail_ctx=None, log_prefix=""):
    """Register a new DeviantArt account via _sisu/do/signup2.

    Rewritten after DA's signup form stopped honoring the old classic-form
    flow (always came back 200 with the join page re-rendered instead of a
    301/302 redirect, confirmed live via a real browser session too — the
    payload shape hadn't changed, DA just started requiring a `lu_token`
    hidden field pulled from /join/'s __INITIAL_STATE__ that the old code
    never sent). Now: GET /join/ for csrf+lu_token, POST signup2 with both,
    follow through /join/intent + onboarding (saveintents,
    save_content_filter) to land in the same fully-logged-in state the old
    redirect-following used to reach. Confirms via auth/auth_secure cookies
    being present rather than trusting a redirect that no longer happens.

    Email confirmation now runs in a background thread instead of blocking
    here — browsing works right after signup, only write actions (avatar,
    sta.sh) need the confirmed email, so the caller can proceed and wait on
    the returned event only if/when it actually needs that.

    Returns (session, success, error_msg, confirmed_event) — confirmed_event
    is a threading.Event set once the confirmation link has been clicked.
    """
    _log = lambda msg: sender_log(f"{log_prefix} [REG {username}] {msg}" if log_prefix else f"[REG {username}] {msg}")
    try:
        _log("GET /join/ — получаю csrf + lu_token...")
        csrf_token, lu_token, err = _fetch_signup_tokens(session, log_fn=_log)
        if not csrf_token:
            return None, False, f"Не удалось получить csrf_token: {err}", None
        _log(f"csrf OK ({csrf_token[:20]}...), lu_token={'OK' if lu_token else 'пусто'}")

        password = _generate_password()
        signup_url = "https://www.deviantart.com/_sisu/do/signup2"
        dob_years_ago = random.randint(20, 35)
        birth = datetime.now() - timedelta(days=dob_years_ago * 365)
        payload = {
            "referer": "https://www.deviantart.com/",
            "referer_type": "",
            "csrf_token": csrf_token,
            "join_mode": "email",
            "oauth": "0",
            "email": email,
            "password": password,
            "token_id": "",
            "username": username,
            "dobMonth": str(birth.month),
            "dobDay": str(birth.day),
            "dobYear": str(birth.year),
            "lu_token": lu_token,
            "lu_token2": "",
            "challenge": "0",
        }
        base_headers = nav_h(session)
        headers = {**base_headers,
                   "Content-Type": "application/x-www-form-urlencoded",
                   "Referer": "https://www.deviantart.com/join/",
                   "Origin": "https://www.deviantart.com",
                   "sec-fetch-dest": "document",
                   "sec-fetch-mode": "navigate",
                   "sec-fetch-site": "same-origin",
                   "sec-fetch-user": "?1",
                   "cache-control": "max-age=0"}
        _signup_rate_wait()
        _log("POST signup2...")
        try:
            resp = session.post(signup_url, headers=headers, data=payload,
                                 timeout=45, allow_redirects=True)
        except Exception as e:
            return None, False, f"Signup request исключение: {str(e)[:200]}", None
        _log(f"signup2 ответ: HTTP {resp.status_code}, url={resp.url[:80]}")

        if resp.status_code >= 400:
            return None, False, _describe_http_error(resp, f"Signup HTTP {resp.status_code}"), None

        state = _extract_initial_state(resp.text or "")
        if state:
            join = state.get("join") or {}
            if join.get("usernameError"):
                return None, False, f"username занят: {join['usernameError']}", None
            if join.get("emailError"):
                return None, False, f"email отклонён: {join['emailError']}", None
            errs = join.get("passwordError") or join.get("dobError") or join.get("generalError")
            if errs:
                return None, False, f"Ошибка регистрации: {errs}", None
            _log("__INITIAL_STATE__ — ошибок нет")
        else:
            _log("__INITIAL_STATE__ не найден в ответе")

        _log("GET /join/intent...")
        intent_url = "https://www.deviantart.com/join/intent?referer=https%3A%2F%2Fwww.deviantart.com%2F"
        try:
            intent_resp = session.get(intent_url, headers=nav_h(session), timeout=45, allow_redirects=True)
        except Exception:
            intent_resp = None
        _log(f"intent: {intent_resp.status_code if intent_resp else 'FAIL'}")

        try:
            cookie_names = list(session.cookies.get_dict().keys())
        except Exception:
            cookie_names = []
        _log(f"cookies: {cookie_names}")
        if not any(n in cookie_names for n in ("auth", "auth_secure")):
            signup_body = resp.text or ""

            # Определяем причину отказа по телу ответа
            if "da-signup-signin" in signup_body or "parastorage.com" in signup_body:
                reject_reason = "DA вернул страницу входа/регистрации (бот-детект или невалидный token_id)"
            elif resp.status_code == 403:
                reject_reason = f"HTTP 403 — заблокирован DA"
            elif resp.status_code == 429:
                reject_reason = f"HTTP 429 — rate limit DA"
            else:
                # Ищем текстовые ошибки в ответе
                err_m = re.search(r'"(?:error|message|detail)"\s*:\s*"([^"]{5,150})"', signup_body)
                reject_reason = f'DA ответил: {err_m.group(1)}' if err_m else f"HTTP {resp.status_code}, нет auth cookies"

            intent_url_str = ""
            if intent_resp:
                intent_url_str = f", intent→{intent_resp.url[:80]}"

            _log(f"❌ ОТКАЗ: {reject_reason} | cookies={cookie_names}{intent_url_str}")

            try:
                diag_path = BASE_DIR / "reg_fail_diag.txt"
                diag_path.write_text(
                    f"=== signup2 response ===\nHTTP {resp.status_code}\nURL: {resp.url}\nПричина: {reject_reason}\n\n{signup_body[:5000]}\n\n"
                    f"=== intent response ===\n{(intent_resp.text or '')[:3000] if intent_resp else 'N/A'}\n",
                    encoding="utf-8", errors="replace")
            except Exception:
                pass

            return None, False, f"auth cookies отсутствуют после signup — {reject_reason}", None

        confirmed_event = threading.Event()

        def _bg_verify():
            prov = get_tempmail_provider(mail_provider)
            poll_fn = prov["get_emails"]
            _stop = sender_state.get("stop")
            for attempt in range(90):
                if _stop and _stop.is_set():
                    return
                inbox = poll_fn(email, mail_ctx)
                if inbox:
                    for mail in inbox:
                        body = mail.get("body_html", "") or mail.get("body", "")
                        if isinstance(body, list):
                            body = body[0] if body else ""
                        link = extract_deviantart_verify_link(body)
                        if link:
                            try:
                                session.get(link, headers=_signup_nav_headers("https://www.deviantart.com/join/"), timeout=60, allow_redirects=True)
                                _log("email подтверждён (фон)")
                                confirmed_event.set()
                            except Exception:
                                pass
                            return
                for _ in range(3):
                    if _stop and _stop.is_set():
                        return
                    time.sleep(1)

        _log("аккаунт создан, верификация email в фоне")
        threading.Thread(target=_bg_verify, daemon=True).start()

        return session, True, "", confirmed_event
    except Exception as e:
        return None, False, str(e)[:150], None


# The browser's avatarEdit crop tool always outputs a fixed-size square before
# uploading — the API rejects anything else with a (broken, un-substituted)
# "must be exactly {{width}} x {{height}} pixels" error that doesn't reveal
# the real numbers. 200x200 is DeviantArt's long-standing avatar size; try it
# first and fall back to a couple of other historically-seen sizes if rejected.
AVATAR_CANDIDATE_SIZES = (200, 150, 100)


def _square_avatar_bytes(avatar_bytes, size):
    """Center-crop to square and resize to size x size, re-encoded as JPEG."""
    if Image is None:
        return None
    img = Image.open(io.BytesIO(avatar_bytes)).convert("RGB")
    w, h = img.size
    side = min(w, h)
    left = (w - side) // 2
    top = (h - side) // 2
    img = img.crop((left, top, left + side, top + side)).resize((size, size), Image.LANCZOS)
    buf = io.BytesIO()
    img.save(buf, format="JPEG", quality=92)
    return buf.getvalue()


def da_set_avatar(session, csrf_token, avatar_bytes, avatar_filename="avatar.jpg"):
    """Upload a new avatar for the logged-in user via POST /user/set_avatar.
    Field set confirmed from HAR: avatar_file, csrf_token, da_minor_version.
    Returns (success, error_msg).
    """
    url = "https://www.deviantart.com/_puppy/dashared/user/set_avatar"
    data = {"csrf_token": csrf_token, "da_minor_version": str(DA_MINOR_VERSION)}
    headers = {
        "accept": "application/json, text/plain, */*",
        "origin": "https://www.deviantart.com",
    }

    sizes_to_try = AVATAR_CANDIDATE_SIZES if Image is not None else (None,)
    last_err = ""
    for size in sizes_to_try:
        try:
            if size is not None:
                body = _square_avatar_bytes(avatar_bytes, size)
                fname, mime = "avatar.jpg", "image/jpeg"
            else:
                body = avatar_bytes
                fname = avatar_filename
                mime = mimetypes.guess_type(avatar_filename)[0] or "image/jpeg"
            if body is None:
                body, fname, mime = avatar_bytes, avatar_filename, (mimetypes.guess_type(avatar_filename)[0] or "image/jpeg")

            resp = da_post_multipart(session, url, "avatar_file", fname, body, mime, data, headers)
            if resp.status_code == 200 and '"usericon"' in resp.text:
                return True, ""
            last_err = _describe_http_error(resp, f"Avatar upload ({size or 'original'}px)")
            # Only worth retrying other sizes if it's specifically the exact-dimensions error.
            if "exactly" not in (resp.text or "").lower():
                break
        except Exception as e:
            last_err = str(e)[:150]
            break
    return False, last_err


# A CloudFront-blocked exit IP isn't a transient blip that clears up if you
# wait — that IP is just bad for this origin. The only thing that helps is a
# different IP, so on this specific error the whole registration is retried
# with a freshly-tagged (i.e. different) sticky session instead of giving up.
CLOUDFRONT_BLOCK_MARKER = "could not be satisfied"
# The per-run counter is now lock-protected (see get_next_temp_account_number)
# so duplicate usernames shouldn't happen within one run any more — but the
# counter file persists across runs, so a leftover account from an earlier
# session can still collide once in a while. Same fix either way: draw a new
# number and retry.
USERNAME_TAKEN_MARKER = "already in use"
# The proxy gateway itself can fail a given exit node (dead upstream, tunnel
# refused, TLS handshake broken by that node's fingerprint) — same fix as a
# CloudFront block: it's the IP's problem, not something worth retrying on
# the same one.
PROXY_CONNECTION_ERROR_MARKERS = (
    "connect tunnel failed", "failed to perform, curl:", "connection reset",
    "connection refused", "could not connect to proxy", "timed out",
)
def _is_bad_ip_error(err_text):
    low = (err_text or "").lower()
    return CLOUDFRONT_BLOCK_MARKER in low or any(m in low for m in PROXY_CONNECTION_ERROR_MARKERS)


def _is_plain_proxy(proxy_text):
    """True when proxy_text is a bare host:port with no auth credentials —
    sticky sessions don't work on these, so retrying the same string just
    hits the same IP over and over."""
    text = (proxy_text or "").strip()
    if not text:
        return True
    if "://" in text:
        _, text = text.split("://", 1)
    if "@" in text:
        return False
    return len(text.split(":")) < 4


def da_fresh_account_session(proxy_text, username_template, avatar_bytes, log_prefix="", keep_proxy_for_comments=True, mail_provider=None, mail_domain=None, stop_event=None, attach_image=False, image_bytes=None, image_filename=""):
    """Build a brand-new session from scratch: no pasted cookies needed.
    Generates a temp email, registers a fresh account (username from the
    template with the XXXXXXX counter substituted), fetches a csrf_token,
    and optionally sets the avatar. `proxy_text` is the raw, *unpinned*
    proxy string — this function generates its own sticky-session tag (and,
    on any failure, a new one on a fresh IP) rather than taking a pre-pinned
    one, so it can rotate to another IP without the caller's help.

    Retries forever (new IP + new temp-mail draw each time) rather than
    giving up after a fixed number of attempts — confirmed live this is what
    it actually takes to get a clean registration through DA's current
    signup validation some sessions (dozens of blocked attempts is normal),
    and the caller (a sender/parser worker thread) already has its own
    stop-aware wrapper around this call for anyone who needs an early exit.

    `mail_domain` is only meaningful for emailnator (its address-style
    picker) — every other provider's get_email() takes no arguments.

    Returns (session, csrf_token, error, confirmed_event, image_deviation)
    — confirmed_event is da_register_account's email-confirmation event,
    image_deviation is the sta.sh deviation dict (or None).
    """
    has_proxy = bool(proxy_text and proxy_text.strip())
    ip_attempt = 0
    # Hard cap on IP-rotation attempts. Free proxies fail 50-70% of the time
    # with connection errors, and da_register_account has its own retries too
    # — without a cap this loop could run 500+ iterations on one account
    # (seen live during the spam-strategy test), burning hundreds of temp
    # emails while the caller waits indefinitely. 50 is a generous ceiling.
    # Overridable per-caller via a module attribute so tests / experimental
    # callers can cap it lower (see spam_strategy_test.py — needs 3 so a
    # single dead pool proxy doesn't burn 50 temp emails).
    MAX_IP_ATTEMPTS = globals().get("MAX_IP_ATTEMPTS_OVERRIDE") or 50
    _is_plain = has_proxy and _is_plain_proxy(proxy_text)
    _POOL_FALLBACK_AFTER = 10
    _consecutive_ip_fails = 0
    _using_pool = False
    _pool_logged = False
    _pool_addr = None
    _effective_mail_provider = mail_provider
    _stop = stop_event or sender_state.get("stop")

    def _stopped():
        return _stop and _stop.is_set()

    def _sleep(secs):
        for _ in range(int(secs * 2)):
            if _stopped():
                return
            time.sleep(0.5)

    while True:
        if _stopped():
            return None, "", "остановлено пользователем", None, None
        if ip_attempt >= MAX_IP_ATTEMPTS:
            if log_prefix:
                sender_log(f"{log_prefix} ❌ Достигнут лимит {MAX_IP_ATTEMPTS} попыток регистрации — сдаюсь")
            return None, "", f"превышен лимит попыток регистрации ({MAX_IP_ATTEMPTS})", None, None
        ip_attempt += 1
        pinned_proxy_str = None
        _pool_addr = None
        effective_proxy = proxy_text if has_proxy else ""
        if has_proxy and (_is_plain or _using_pool):
            _pa = PROXY_POOL.get_best()
            if _pa:
                effective_proxy = _pa
                _pool_addr = _pa
                if _using_pool and not _pool_logged and log_prefix:
                    sender_log(f"{log_prefix} 🔄 Основной прокси не работает ({_consecutive_ip_fails} ошибок подряд) — пробую прокси из пула")
                    _pool_logged = True
            elif log_prefix and ip_attempt % 10 == 0:
                sender_log(f"{log_prefix} ⚠ Пул прокси пуст — нет живых альтернатив")
        if effective_proxy and effective_proxy.strip():
            sticky_tag = "da" + uuid.uuid4().hex[:10]
            pinned_proxy_str = with_sticky_session(effective_proxy, sticky_tag)
            if log_prefix:
                src = " (пул)" if _pool_addr else ""
                sender_log(f"{log_prefix} 📌 [попытка {ip_attempt}] Новый IP{src} (sessid-{sticky_tag})")

        try:
            profile = pick_browser_profile()
            session = make_session(profile)
            if log_prefix:
                sender_log(f"{log_prefix} 🌐 Отпечаток: {profile['impersonate']}")
            if pinned_proxy_str:
                apply_proxy_to_session(session, pinned_proxy_str)
                session._proxy_text = pinned_proxy_str
            else:
                session._proxy_text = None
            tempmailorg_set_proxy(None)

            _log_fn = (lambda msg: sender_log(f"{log_prefix} {msg}")) if log_prefix else None
            use_auto = (_effective_mail_provider or "").lower() in ("auto", "")
            if use_auto:
                temp_email, mail_ctx, resolved_provider = auto_get_email(log_fn=_log_fn)
                prov_label = TEMPMAIL_PROVIDERS.get(resolved_provider, {}).get("label", "?") if resolved_provider else "auto"
            else:
                resolved_provider = _effective_mail_provider
                if _effective_mail_provider == "tempmailorg":
                    pool_sz = _tmorg_pool.qsize()
                    if pool_sz > 0:
                        if _log_fn:
                            _log_fn(f"[Temp-Mail.org] пул: {pool_sz} — беру...")
                        temp_email, mail_ctx = tempmailorg_get_email(timeout=10)
                    else:
                        if _log_fn:
                            _log_fn(f"[Temp-Mail.org] пул пуст — жду до 30 сек...")
                        temp_email, mail_ctx = tempmailorg_get_email(timeout=30)
                else:
                    prov = get_tempmail_provider(_effective_mail_provider)
                    if _effective_mail_provider in ("emailnator", "smailpro", "temptf", "mailyra"):
                        temp_email, mail_ctx = prov["get_email"](mail_domain)
                    else:
                        temp_email, mail_ctx = prov["get_email"]()
                prov_label = TEMPMAIL_PROVIDERS.get(resolved_provider, {}).get("label", resolved_provider)
            if not temp_email and not use_auto:
                if _log_fn:
                    _log_fn(f"[{prov_label}] недоступен — пробую остальные провайдеры...")
                fallback_email, fallback_ctx, fallback_prov = auto_get_email(log_fn=_log_fn)
                if fallback_email:
                    temp_email, mail_ctx, resolved_provider = fallback_email, fallback_ctx, fallback_prov
                    prov_label = TEMPMAIL_PROVIDERS.get(resolved_provider, {}).get("label", resolved_provider)
                    _effective_mail_provider = "auto"
            if not temp_email:
                if log_prefix:
                    sender_log(f"{log_prefix} ⚠ Не удалось сгенерировать temp email ({prov_label}) — пробую снова...")
                _sleep(random.uniform(3.0, 6.0))
                continue

            if _stopped():
                return None, "", "остановлено пользователем", None, None

            acc_num = get_next_temp_account_number(username_template)
            new_username = username_template.replace("XXXXXXX", f"{acc_num:07d}")
            if log_prefix:
                sender_log(f"{log_prefix} 📧 [{prov_label}] Email: {temp_email}, Username: {new_username}")

            actual_mail_provider = resolved_provider or mail_provider
            new_session, reg_ok, reg_err, confirmed_event = da_register_account(
                session, temp_email, new_username,
                mail_provider=actual_mail_provider, mail_ctx=mail_ctx, log_prefix=log_prefix)
            if not reg_ok:
                if _stopped():
                    return None, "", "остановлено пользователем", None, None
                if USERNAME_TAKEN_MARKER in (reg_err or "").lower():
                    if log_prefix:
                        sender_log(f"{log_prefix} ⚠ Имя «{new_username}» уже занято — пробую другой номер...")
                    continue
                if "auth cookies отсутствуют" in (reg_err or ""):
                    _consecutive_ip_fails += 1
                    if _pool_addr:
                        PROXY_POOL.mark_bad(_pool_addr, ttl_seconds=600)
                    if not _is_plain and not _using_pool and _consecutive_ip_fails >= _POOL_FALLBACK_AFTER:
                        _using_pool = True
                    if log_prefix:
                        sender_log(f"{log_prefix} ⚠ DA отклонил signup (бот-детект) — меняю IP...")
                    _sleep(random.uniform(0.5, 1.5))
                    continue
                if _is_bad_ip_error(reg_err):
                    _consecutive_ip_fails += 1
                    if _pool_addr:
                        _cf_blocked = CLOUDFRONT_BLOCK_MARKER in (reg_err or "").lower()
                        PROXY_POOL.mark_bad(_pool_addr, ttl_seconds=3600 if _cf_blocked else 600)
                    if not _is_plain and not _using_pool and _consecutive_ip_fails >= _POOL_FALLBACK_AFTER:
                        _using_pool = True
                    if log_prefix:
                        sender_log(f"{log_prefix} ⚠ Проблема с IP/соединением — беру другой IP...")
                    _sleep(random.uniform(0.5, 1.5))
                    continue
                _consecutive_ip_fails += 1
                if _pool_addr:
                    PROXY_POOL.mark_bad(_pool_addr, ttl_seconds=300)
                if not _is_plain and not _using_pool and _consecutive_ip_fails >= _POOL_FALLBACK_AFTER:
                    _using_pool = True
                if log_prefix:
                    sender_log(f"{log_prefix} ⚠ Ошибка регистрации: {(reg_err or '')[:150]} — пробую снова с другим IP...")
                _sleep(random.uniform(1.5, 3.0))
                continue
            _consecutive_ip_fails = 0
            if reg_err and log_prefix:
                sender_log(f"{log_prefix} ⚠ {reg_err}")

            csrf_token, err = da_fetch_csrf(new_session, sender_log if log_prefix else None, log_prefix)
            if not csrf_token:
                if log_prefix:
                    sender_log(f"{log_prefix} ⚠ Не удалось получить csrf_token: {err[:100]} — меняю IP...")
                _sleep(random.uniform(2.0, 5.0))
                continue

            if avatar_bytes:
                ok, err = da_set_avatar(new_session, csrf_token, avatar_bytes, "avatar.jpg")
                if log_prefix:
                    if ok:
                        sender_log(f"{log_prefix} ✅ Аватарка установлена")
                    else:
                        sender_log(f"{log_prefix} ⚠ Не удалось установить аватарку: {err}")

            if log_prefix:
                sender_log(f"{log_prefix} ✅ Аккаунт зарегистрирован с {ip_attempt}-й попытки: {new_username}")

            img_deviation = None
            if attach_image and image_bytes:
                if confirmed_event and not confirmed_event.is_set():
                    if log_prefix:
                        sender_log(f"{log_prefix} ⏳ Жду подтверждения email (макс 60 сек)...")
                    if confirmed_event.wait(timeout=60):
                        if log_prefix:
                            sender_log(f"{log_prefix} ✅ Email подтверждён, продолжаю")
                    else:
                        if log_prefix:
                            sender_log(f"{log_prefix} ⚠ Таймаут ожидания email — продолжаю")
                if log_prefix:
                    sender_log(f"{log_prefix} ⏳ Загрузка изображения в sta.sh (через прокси)...")
                img_deviation, _was_up, img_err = da_get_or_upload_stash_deviation(
                    new_session, csrf_token, image_bytes,
                    image_filename or "image.png", new_account=True)
                if img_deviation:
                    if log_prefix:
                        sender_log(f"{log_prefix} 🖼 Изображение загружено в sta.sh")
                else:
                    if log_prefix:
                        sender_log(f"{log_prefix} ⚠ sta.sh не удалось: {img_err}")

            new_session._reg_proxy = pinned_proxy_str
            if pinned_proxy_str:
                clear_session_proxy(new_session)
                if keep_proxy_for_comments:
                    apply_proxy_to_session(new_session, pinned_proxy_str)
                    if log_prefix:
                        sender_log(f"{log_prefix} 🔌 Регистрация завершена — прокси включён для комментариев")
                else:
                    if log_prefix:
                        sender_log(f"{log_prefix} 🔌 Регистрация завершена — прокси отключен, дальше работаю напрямую")

            return new_session, csrf_token, "", confirmed_event, img_deviation
        except Exception as e:
            if _stopped():
                return None, "", "остановлено пользователем", None, None
            _consecutive_ip_fails += 1
            if _pool_addr:
                PROXY_POOL.mark_bad(_pool_addr, ttl_seconds=300)
            if not _is_plain and not _using_pool and _consecutive_ip_fails >= _POOL_FALLBACK_AFTER:
                _using_pool = True
            last_err = str(e)[:150]
            if log_prefix:
                sender_log(f"{log_prefix} ⚠ Исключение: {last_err} — пробую снова...")
            _sleep(random.uniform(3.0, 7.0))
            continue


def ensure_working_da_cookies(cookie_text, proxy_text, username_template="Verification-XXXXXXX"):
    """Check whether `cookie_text` still logs into a working account (empty,
    a dead csrf fetch, or an unresolvable username all count as "not
    working" — the last one specifically covers a userinfo cookie with an
    empty "username" field, confirmed live to mean the account is unusable
    even though a plain csrf fetch still succeeds). If it doesn't, register
    a fresh account and use its cookies instead — this is what backs the
    parser's "auto-register if the account died" checkbox.

    Registration progress logs to the sender tab's log (same as the
    parser's manual "🚀 Зарегистрировать аккаунт" button), since
    da_fresh_account_session always logs through sender_log.

    Returns (cookie_text_to_use, was_replaced, error_msg_if_replacement_failed).
    """
    if cookie_text.strip():
        session, profile, err = da_session_from_cookies(cookie_text, proxy_text)
        if session:
            csrf_token, csrf_err = da_fetch_csrf(session)
            if csrf_token:
                resolved_username, _ = username_from_userinfo_cookie(session)
                if resolved_username:
                    return cookie_text, False, ""

    new_session, csrf_token, err, _confirmed, _ = da_fresh_account_session(
        proxy_text, username_template, None, "[Авто-регистрация для парсера]")
    if not new_session:
        return cookie_text, False, err
    return session_cookies_to_text(new_session), True, ""


def is_spam_error(cerr):
    """Check if a failed comment-post's error string is DA's spam/anti-bot
    rejection (errorCode 3, media_content_violation, "spam" violation) that
    should trigger account rotation.

    Takes the raw error text, not a parsed dict: da_post_comment's `cerr` is
    formatted as "код <status>: <body>" (plus an optional set-cookie
    fragment), not clean JSON, so json.loads() on it always raised
    JSONDecodeError — silently swallowed by the caller's except clause,
    meaning account rotation never actually fired on this error. Substring
    matching on the distinctive fields sidesteps that (and the body-text
    truncation) entirely.
    """
    if not cerr:
        return False
    return ('"errorCode":3' in cerr and '"media_content_violation"' in cerr
            and '"spam"' in cerr)


def _probe_spam_type(session, csrf_token, dev_id, url, sender_log, prefix, stop_event=None):
    """After a spam-error on the main comment text, send a handful of tiny
    random strings on the same target to figure out whether DA is flagging
    the specific text pattern or the whole account.

    Both outcomes still trigger re-registration (the main text can't land on
    a text-flagged account either), but the log severity differs so it's
    obvious in the UI which one is happening — text-only shadowbans usually
    mean the comment content itself needs a rewrite, while account-wide
    shadowbans mean signup itself is being rate-limited by IP/fingerprint.

    Returns ``"text"`` (at least one probe posted OK — text pattern only) or
    ``"account"`` (every probe was also spam-rejected — account itself is
    shadowbanned).
    """
    probes = 3
    for i in range(probes):
        if stop_event and stop_event.is_set():
            return "account"
        probe_text = "".join(random.choices(string.ascii_lowercase, k=random.randint(2, 4)))
        sender_log(f"{prefix} 🧪 Проба {i + 1}/{probes}: пытаюсь отправить '{probe_text}'...")
        try:
            ok, cerr, _ = da_post_comment(session, csrf_token, int(dev_id), probe_text, url, None)
        except Exception as e:
            sender_log(f"{prefix} ⚠ Проба '{probe_text}' упала с исключением: {str(e)[:100]}")
            return "account"
        if ok:
            sender_log(f"{prefix} ⚠ Проба '{probe_text}' прошла — заспамлен ТЕКСТ, аккаунт живой")
            return "text"
        if not is_spam_error(cerr):
            sender_log(f"{prefix} ⚠ Проба '{probe_text}' упала не по спаму — считаю аккаунт мёртвым")
            return "account"
        if i < probes - 1:
            time.sleep(random.uniform(1.2, 2.5))
    return "account"


def is_expired_session_error(cerr):
    """Check if a failed comment-post's error string means the session's
    csrf_token has gone stale/missing (errorCode 400, "csrf":"missing",
    "Invalid or expired form submission") — seen live to repeat forever
    otherwise, since the same broken token gets reused on every retry.
    """
    if not cerr:
        return False
    return '"csrf":"missing"' in cerr or "Invalid or expired form submission" in cerr


def is_unverified_account_error(cerr):
    """Check if a failed comment-post's error string means the account's
    email was never confirmed ("unverified_account" — seen live to repeat
    forever otherwise, since a never-confirmed account stays unverified no
    matter how many times the same comment is retried on it). Distinct from
    a stale csrf_token: refreshing the token doesn't help here, only a new
    (properly confirmed) account does.
    """
    if not cerr:
        return False
    return '"unverified_account"' in cerr


def is_unauthorized_error(cerr):
    """Check if a failed comment-post's error string means the session is no
    longer authenticated at all ("unauthorized" / "Not authorized" — seen
    live to repeat forever otherwise, since a logged-out session stays
    logged out no matter how many times the same comment is retried on it).
    DeviantArt hands this out when an account gets banned/suspended mid-run
    or the session cookie is otherwise invalidated server-side — a csrf
    refresh doesn't fix it, only a new account does.
    """
    if not cerr:
        return False
    return '"unauthorized"' in cerr and "Not authorized" in cerr


temp_account_counter_lock = threading.Lock()


_temp_account_counter_state = {"next": None}
_USERNAME_NUMBER_RE = re.compile(r"-(\d{7})\b")


def _recover_next_temp_account_number():
    """Derive the correct next-to-issue number after a (re)start by taking
    one past the highest number found anywhere it could have been recorded:
    the small persisted counter file, the append-only issued-number
    registry, and — covering numbers issued before this registry existed —
    every "Username: ...-NNNNNNN" line in the sender log. Never trusts a
    single source alone, so a deleted/stale counter file can't cause a
    number (and therefore a login) to be reused.
    """
    max_seen = -1
    try:
        if TEMP_EMAIL_COUNTER_FILE.exists():
            max_seen = max(max_seen, int(TEMP_EMAIL_COUNTER_FILE.read_text().strip() or "0") - 1)
    except Exception:
        pass
    try:
        if TEMP_ACCOUNT_REGISTRY_FILE.exists():
            for line in TEMP_ACCOUNT_REGISTRY_FILE.read_text(encoding="utf-8", errors="replace").splitlines():
                num_str = line.split("\t", 1)[0].strip()
                if num_str.isdigit():
                    max_seen = max(max_seen, int(num_str))
    except Exception:
        pass
    try:
        if SENDER_LOG_FILE.exists():
            text = SENDER_LOG_FILE.read_text(encoding="utf-8", errors="replace")
            for m in re.finditer(r"Username:\s*\S*" + _USERNAME_NUMBER_RE.pattern, text):
                max_seen = max(max_seen, int(m.group(1)))
    except Exception:
        pass
    return max_seen + 1


def get_next_temp_account_number(username_template=""):
    """Reserve and return the next never-before-used account number.

    Guarded by an in-process lock: without it, concurrent registration
    threads all read the same on-disk value before any of them wrote the
    increment back, so several threads got the identical number (confirmed
    live — 6 of 10 threads all drew "Verification-0000000" in one run) and
    DA rejected every duplicate signup with "username already in use").

    The number (and, if a template is given, the exact login it resolves
    to) is appended to the registry the instant it's reserved — before any
    registration attempt runs — so it can never be handed out again even if
    that attempt fails, crashes, or the app restarts.
    """
    with temp_account_counter_lock:
        try:
            if _temp_account_counter_state["next"] is None:
                _temp_account_counter_state["next"] = _recover_next_temp_account_number()
            num = _temp_account_counter_state["next"]
            _temp_account_counter_state["next"] = num + 1

            try:
                TEMP_EMAIL_COUNTER_FILE.write_text(str(num + 1))
            except Exception:
                pass
            try:
                username = username_template.replace("XXXXXXX", f"{num:07d}") if username_template else ""
                with open(TEMP_ACCOUNT_REGISTRY_FILE, "a", encoding="utf-8") as f:
                    f.write(f"{num}\t{username}\n")
            except Exception:
                pass

            return num
        except Exception:
            return 0


# Two independent tabs, two independent run states: the parser tab only
# discovers posts and writes them to the notebook file; the sender tab only
# reads that notebook and posts comments. Neither talks to the other in
# memory — the notebook file is the sole handoff, so either tab can be
# started/stopped independently (parser can keep filling the notebook while
# sender is stopped, or vice versa).
parser_lock = threading.Lock()
parser_state = {"running": False, "found": 0, "logs": [], "stop": None}
sender_lock = threading.Lock()
sender_state = {"running": False, "sent": 0, "logs": [], "stop": None}

blacklist_lock = threading.Lock()
blacklist_cache = set()
# lowercased username -> {"username": original-case username, "urls": {post urls}}
blacklist_entries = {}
notebook_lock = threading.Lock()


def write_log_file(path, msg):
    try:
        with open(path, "a", encoding="utf-8") as f:
            f.write(msg + "\n")
    except Exception:
        pass


def parser_log(text):
    with parser_lock:
        msg = f"[{time.strftime('%H:%M:%S')}] {text}"
        parser_state["logs"].append(msg)
        if len(parser_state["logs"]) > MAX_LOG_LINES:
            parser_state["logs"].pop(0)
    print(f"[da-parser] {text}")
    write_log_file(PARSER_LOG_FILE, msg)


def sender_log(text):
    with sender_lock:
        msg = f"[{time.strftime('%H:%M:%S')}] {text}"
        sender_state["logs"].append(msg)
        if len(sender_state["logs"]) > MAX_LOG_LINES:
            sender_state["logs"].pop(0)
    print(f"[da-sender] {text}")
    write_log_file(SENDER_LOG_FILE, msg)


def read_notebook():
    """Pending posts to comment on — one URL per line, de-duplicated.

    Pulls the deviation URL out via .search() rather than requiring the
    whole line to BE the URL, and keeps only that matched span as `url` —
    so a blacklist line pasted in as-is ("username<TAB>url", now that the
    blacklist stores urls too) still works: the username prefix is just
    ignored instead of getting glued onto the url and corrupting every
    request that uses it (Referer header, blacklist re-entry, etc.).
    """
    if not NOTEBOOK_FILE.exists():
        return []
    out = []
    seen = set()
    with open(NOTEBOOK_FILE, "r", encoding="utf-8") as f:
        for line in f:
            raw = line.strip()
            if not raw:
                continue
            m = DEVIATION_LINK_RE.search(raw)
            if not m:
                continue
            url = m.group(0)
            if url in seen:
                continue
            seen.add(url)
            out.append({"username": m.group(1), "deviation_id": m.group(3), "url": url})
    return out


def append_notebook(urls):
    if not urls:
        return
    with notebook_lock:
        try:
            needs_newline = (NOTEBOOK_FILE.exists() and NOTEBOOK_FILE.stat().st_size > 0
                             and not NOTEBOOK_FILE.read_text(encoding="utf-8", errors="ignore").endswith("\n"))
            with open(NOTEBOOK_FILE, "a", encoding="utf-8") as f:
                if needs_newline:
                    f.write("\n")
                for u in urls:
                    f.write(u + "\n")
        except Exception:
            pass


def take_next_unreserved(ignore_blacklist, reserved, reserved_lock):
    """Atomically find the first notebook entry whose author isn't already
    being handled by another thread right now, remove it from the notebook,
    and reserve that author — all under one lock so two threads can never
    both claim the same line (a plain read-then-write race would let that
    happen) or pick the same author. Returns None if nothing claimable.

    Along the way, any entry whose author is *already* blacklisted gets
    purged from the notebook instead of just being skipped-in-place: leaving
    it there and re-skipping it on every single future scan (which is what
    this used to do) let blacklisted-author leftovers pile up as permanent
    dead weight — confirmed live as the cause of the notebook's claimable
    count looking stuck even while the parser kept adding to it. The purged
    url is recorded against that author in the blacklist (not just dropped)
    so it can be moved back to the notebook later via remove_from_blacklist.
    """
    purged = []  # (username, url) pairs whose author is already blacklisted
    claimed = None
    with notebook_lock:
        items = read_notebook()
        keep = []
        for it in items:
            if claimed is not None:
                keep.append(it["url"])
                continue
            if not ignore_blacklist and is_blacklisted(it["username"]):
                purged.append((it["username"], it["url"]))
                continue
            key = it["username"].lower()
            with reserved_lock:
                if key in reserved:
                    keep.append(it["url"])
                    continue
                reserved.add(key)
            claimed = it
        if claimed is None and not purged:
            return None
        try:
            with open(NOTEBOOK_FILE, "w", encoding="utf-8") as f:
                if keep:
                    f.write("\n".join(keep) + "\n")
        except Exception:
            pass
    # append_blacklist takes its own lock and does its own file I/O — no
    # need to hold notebook_lock for it.
    for purged_username, purged_url in purged:
        append_blacklist(purged_username, purged_url)
    return claimed


def clear_notebook():
    with notebook_lock:
        try:
            NOTEBOOK_FILE.unlink(missing_ok=True)
        except Exception:
            pass


def load_blacklist():
    """Blacklist lines are "username\turl" — the url lets a blacklisted
    entry be moved back to the notebook later (see remove_from_blacklist).
    Older files (or a manually-edited line) may have just a bare username
    with no tab; those load fine too, just with no url to restore.
    """
    global blacklist_cache, blacklist_entries
    if not BLACKLIST_FILE.exists():
        return
    cache = set()
    entries = {}
    with open(BLACKLIST_FILE, "r", encoding="utf-8") as f:
        for ln in f:
            ln = ln.rstrip("\n")
            if not ln.strip():
                continue
            username, _, url = ln.partition("\t")
            username = username.strip()
            url = url.strip()
            if not username:
                continue
            key = username.lower()
            cache.add(key)
            entry = entries.setdefault(key, {"username": username, "urls": set()})
            if url:
                entry["urls"].add(url)
    with blacklist_lock:
        blacklist_cache = cache
        blacklist_entries = entries


def is_blacklisted(username):
    with blacklist_lock:
        return username.lower() in blacklist_cache




def append_blacklist(username, url=""):
    """Record that `username` is blacklisted, and (if given) that `url`
    specifically is one of theirs — so it can be found again and moved back
    to the notebook later via remove_from_blacklist. Safe to call again for
    a username that's already blacklisted with a *different* url (e.g. a
    second post by the same author getting swept out of the notebook by
    take_next_unreserved) — only an exact duplicate (username, url) pair
    is a no-op.

    Cache update AND the file write happen under the same lock — both
    matter: two threads blacklisting different authors at once could
    otherwise glue their lines together (each reads the "needs a leading
    newline?" state independently), and a concurrent clear_blacklist()
    could delete the file between this function's cache update and its
    file write, leaving the on-disk file missing an entry the in-memory
    cache (and therefore the running session) already considers blacklisted.
    """
    key = username.lower()
    with blacklist_lock:
        entry = blacklist_entries.setdefault(key, {"username": username, "urls": set()})
        if url and url in entry["urls"]:
            return
        already_blacklisted = key in blacklist_cache
        if url:
            entry["urls"].add(url)
        blacklist_cache.add(key)
        if already_blacklisted and url:
            # New url for an already-blacklisted username — appending a
            # fresh line is cheaper than a full rewrite and just as correct.
            try:
                needs_newline = (BLACKLIST_FILE.exists() and BLACKLIST_FILE.stat().st_size > 0
                                 and not BLACKLIST_FILE.read_text(encoding="utf-8", errors="ignore").endswith("\n"))
                with open(BLACKLIST_FILE, "a", encoding="utf-8") as f:
                    if needs_newline:
                        f.write("\n")
                    f.write(f"{username}\t{url}\n")
            except Exception:
                pass
        elif not already_blacklisted:
            try:
                needs_newline = (BLACKLIST_FILE.exists() and BLACKLIST_FILE.stat().st_size > 0
                                 and not BLACKLIST_FILE.read_text(encoding="utf-8", errors="ignore").endswith("\n"))
                with open(BLACKLIST_FILE, "a", encoding="utf-8") as f:
                    if needs_newline:
                        f.write("\n")
                    f.write(f"{username}\t{url}\n" if url else f"{username}\n")
            except Exception:
                pass


def remove_from_blacklist(username):
    """Un-blacklist `username` and return the list of post URLs that were
    recorded for them (possibly empty, for a legacy bare-username entry) —
    the caller re-queues those into the notebook so they can be
    re-attempted, per the "move back and try again" workflow.

    Reads the file directly and only drops this one username's lines,
    rather than rewriting the whole file from the in-memory
    blacklist_entries cache — that cache is only ever *supposed* to mirror
    the file, but if it were ever stale for any reason (a missed reload, a
    second process touching the file, anything), trusting it as "everything
    that should remain" would silently discard every on-disk entry it
    didn't know about. This way, removing one username can never touch any
    other username's data, no matter what state the cache is in.
    """
    key = username.lower()
    urls = set()
    with blacklist_lock:
        kept_lines = []
        if BLACKLIST_FILE.exists():
            try:
                raw = BLACKLIST_FILE.read_text(encoding="utf-8", errors="replace")
            except Exception:
                raw = ""
            for ln in raw.splitlines():
                if not ln.strip():
                    continue
                line_username, _, line_url = ln.partition("\t")
                if line_username.strip().lower() == key:
                    line_url = line_url.strip()
                    if line_url:
                        urls.add(line_url)
                    continue
                kept_lines.append(ln)
        try:
            with open(BLACKLIST_FILE, "w", encoding="utf-8") as f:
                if kept_lines:
                    f.write("\n".join(kept_lines) + "\n")
        except Exception:
            pass
        blacklist_entries.pop(key, None)
        blacklist_cache.discard(key)
    return sorted(urls)


def clear_blacklist():
    with blacklist_lock:
        blacklist_cache.clear()
        blacklist_entries.clear()
        try:
            BLACKLIST_FILE.unlink(missing_ok=True)
        except Exception:
            pass


account_pool_lock = threading.Lock()


def save_account_to_pool(cookies_text, username=""):
    """Called when a worker stops with a still-working auto-registered
    account (see comment_worker's stop handling) — appends it so the next
    run can pick it up via pop_account_from_pool instead of registering
    from scratch.
    """
    if not cookies_text or not cookies_text.strip():
        return
    with account_pool_lock:
        try:
            with open(ACCOUNT_POOL_FILE, "a", encoding="utf-8") as f:
                f.write(json.dumps({"username": username, "cookies": cookies_text}, ensure_ascii=False) + "\n")
        except Exception:
            pass


def pop_account_from_pool():
    """Remove and return one saved {"username","cookies"} account, or None
    if the pool is empty. The removal happens immediately (read + rewrite
    under the same lock) so two threads starting at once can never both be
    handed the same saved account.
    """
    with account_pool_lock:
        if not ACCOUNT_POOL_FILE.exists():
            return None
        try:
            lines = [ln for ln in ACCOUNT_POOL_FILE.read_text(encoding="utf-8", errors="replace").splitlines() if ln.strip()]
        except Exception:
            return None
        if not lines:
            return None
        first, rest = lines[0], lines[1:]
        try:
            with open(ACCOUNT_POOL_FILE, "w", encoding="utf-8") as f:
                if rest:
                    f.write("\n".join(rest) + "\n")
        except Exception:
            pass
        try:
            return json.loads(first)
        except Exception:
            return None


def account_pool_size():
    with account_pool_lock:
        if not ACCOUNT_POOL_FILE.exists():
            return 0
        try:
            return sum(1 for ln in ACCOUNT_POOL_FILE.read_text(encoding="utf-8", errors="replace").splitlines() if ln.strip())
        except Exception:
            return 0


def clear_account_pool():
    """The "Сброс" button — after this, the next sender start has nothing
    to pop from the pool and always registers fresh accounts, regardless
    of what was saved when the sender was last stopped.
    """
    with account_pool_lock:
        try:
            ACCOUNT_POOL_FILE.unlink(missing_ok=True)
        except Exception:
            pass


MAX_POOL_ACCOUNT_ATTEMPTS = 5


def da_session_from_pool(proxy_text, keep_proxy, log_prefix=""):
    """Try a few saved accounts from the pool (verifying each with a fresh
    csrf fetch AND that its own username can actually be resolved, since one
    may have gone dead/banned/incomplete since it was saved — confirmed
    live: a batch of pooled accounts all had an empty "username" in their
    userinfo cookie and a 500 from the folders-API fallback, meaning they
    were unusable, but a bare csrf fetch alone didn't catch that) before
    giving up. Returns (session, csrf_token, username) or
    (None, None, None) if the pool is empty or nothing in it still works.
    """
    for _ in range(MAX_POOL_ACCOUNT_ATTEMPTS):
        entry = pop_account_from_pool()
        if not entry:
            return None, None, None
        saved_username = entry.get("username") or ""
        session, profile, err = da_session_from_cookies(entry.get("cookies") or "", proxy_text if keep_proxy else "")
        if not session:
            continue
        csrf_token, err = da_fetch_csrf(session, sender_log if log_prefix else None, log_prefix)
        if not csrf_token:
            if log_prefix:
                sender_log(f"{log_prefix} ⚠ Сохранённый аккаунт {saved_username or '(?)'} больше не работает, пробую другой...")
            continue
        resolved_username, _ = username_from_userinfo_cookie(session)
        if not resolved_username:
            if log_prefix:
                sender_log(f"{log_prefix} ⚠ Сохранённый аккаунт {saved_username or '(?)'} не резолвится (сломан) — пробую другой...")
            continue
        return session, csrf_token, resolved_username
    return None, None, None


def open_file(path):
    try:
        if not path.exists():
            path.touch()
        os.startfile(str(path))
        return True, str(path)
    except Exception as e:
        return False, str(e)[:100]


def parse_cookie_pairs(text):
    """Extract (name, value) pairs from whatever cookie text was pasted.

    Handles both the standard single-line header form ("a=1; b=2") and a
    one-per-line paste (DevTools' per-row "Copy value", or just pasting a
    multi-line blob into the textarea) — confirmed live as the actual cause
    of both a curl error 43 (raw newlines in an HTTP header) and Playwright's
    "Invalid cookie fields" (a single cookie object with newlines baked into
    its name/value) when the naive single-line-only parser choked on a
    multi-line paste. Splits on ';' and newlines equally, strips an optional
    leading "Cookie:" prefix, and drops anything that isn't a real name=value
    pair instead of feeding garbage further down.

    Also handles a JSON export (Cookie-Editor/EditThisCookie style: a list of
    {"name": ..., "value": ..., ...} objects, or a single such object) —
    confirmed as the actual cause of a real "unauthorized" failure where the
    naive splitter mangled the JSON into two garbage pairs both literally
    named "value", so none of the real session cookies were ever sent.
    """
    raw = (text or "").strip()
    try:
        data = json.loads(raw)
        if isinstance(data, dict):
            data = [data]
        if isinstance(data, list) and data and all(
                isinstance(d, dict) and "name" in d and "value" in d for d in data):
            return [(d["name"], d["value"]) for d in data if d.get("name")]
    except (json.JSONDecodeError, TypeError):
        pass

    text = re.sub(r"(?i)^\s*cookie\s*:\s*", "", raw)
    pairs = []
    for part in re.split(r"[;\r\n]+", text):
        part = part.strip()
        if not part or "=" not in part:
            continue
        name, _, value = part.partition("=")
        name = name.strip()
        value = value.strip()
        if name:
            pairs.append((name, value))
    return pairs


def parse_cookie_header(text):
    """Canonical single-line "a=1; b=2" form, safe to use as an HTTP header
    value (no embedded newlines) regardless of how it was pasted.
    """
    return "; ".join(f"{n}={v}" for n, v in parse_cookie_pairs(text))


def with_sticky_session(proxy_str, tag, lifetime_minutes=30):
    """Pin a rotating proxy to one exit IP by adding a session id to its login.

    These pools hand a different IP to every new connection, so an account
    registered on one address would later send from another and get rejected.
    ";sessid-<tag>" (matching the same convention used by the SuperFaktura
    proxy checker in this repo) keeps the whole account on one IP for
    `lifetime_minutes`. Proxies without a login, or that already carry a
    session id, are handled by stripping any stale id before adding the new
    one. Returns the proxy string unchanged if there's no login to pin.
    """
    proxy_str = (proxy_str or "").strip()
    if not proxy_str:
        return proxy_str

    scheme = ""
    rest = proxy_str
    if "://" in rest:
        scheme, rest = rest.split("://", 1)

    parts = rest.split(":")
    if len(parts) < 4:
        return proxy_str  # host:port only — no login to attach the id to

    host, port, user = parts[0], parts[1], parts[2]
    password = ":".join(parts[3:])
    # Drop any id already on the login: one account gets one fresh IP, so a
    # carried-over id would silently hand the next account the same address.
    user = re.sub(r';(?:sessid|lifetime)[.\-][^;]*', '', user)
    user = f"{user};sessid-{tag};lifetime.{lifetime_minutes}"
    out = f"{host}:{port}:{user}:{password}"
    return f"{scheme}://{out}" if scheme else out


def parse_proxy(text):
    """Accepts host:port, host:port:user:pass, or scheme://[user:pass@]host:port.
    Returns a {"http":url,"https":url} mapping for curl_cffi/requests, or None.

    Used only where a proxy's mere validity needs checking (no request is
    actually made with this dict) — for live requests, use
    `apply_proxy_to_session()` instead; see its docstring for why.
    """
    text = (text or "").strip()
    if not text:
        return None
    scheme = ""
    if "://" in text:
        scheme, text = text.split("://", 1)
    if "@" not in text:
        parts = text.split(":")
        if len(parts) >= 4:
            host, port, user = parts[0], parts[1], parts[2]
            password = ":".join(parts[3:])
            auth = f"{urllib.parse.quote(user, safe='')}:{urllib.parse.quote(password, safe='')}@"
            text = f"{auth}{host}:{port}"
            scheme = scheme or "http"
        else:
            scheme = scheme or "http"
    else:
        scheme = scheme or "http"
    url = f"{scheme}://{text}"
    try:
        parsed = urlparse(url)
        if not parsed.hostname or not parsed.port:
            return None
    except Exception:
        return None
    return {"http": url, "https": url}


def split_proxy_auth(text):
    """Split a proxy string into a bare host:port URL and a separate
    (user, password) credentials tuple, instead of embedding percent-encoded
    credentials in the URL.

    Confirmed live: curl_cffi's proxy URL parser breaks on a long,
    heavily-escaped username (residential pools routinely hand out ones like
    "<id>__cr.<200-country list>;anon.1", which balloons past 1KB once
    percent-encoded) — the connection then fails with a nonsensical
    "TLS connect error ... OPENSSL_internal:invalid library" instead of a
    clean proxy-auth error. Keeping the URL to just host:port and handing
    raw (unescaped) credentials to curl separately via `proxy_auth=`
    sidesteps that parser entirely.

    Returns (host_port_url, (user, password) | None), or (None, None) if
    unparseable.
    """
    text = (text or "").strip()
    if not text:
        return None, None
    scheme = "http"
    if "://" in text:
        scheme, text = text.split("://", 1)
    if "@" in text:
        creds, hostport = text.rsplit("@", 1)
        user, _, password = creds.partition(":")
        user = urllib.parse.unquote(user)
        password = urllib.parse.unquote(password)
    else:
        parts = text.split(":")
        if len(parts) >= 4:
            hostport = f"{parts[0]}:{parts[1]}"
            user = parts[2]
            password = ":".join(parts[3:])
        elif len(parts) == 2:
            hostport, user, password = text, "", ""
        else:
            return None, None
    url = f"{scheme}://{hostport}"
    try:
        parsed = urlparse(url)
        if not parsed.hostname or not parsed.port:
            return None, None
    except Exception:
        return None, None
    return url, ((user, password) if user else None)


def apply_proxy_to_session(session, proxy_str):
    """Attach a proxy to a session the safe way (see split_proxy_auth): for
    curl_cffi, credentials go through `.proxy_auth` instead of the URL; the
    plain `requests` fallback has no such option, so it still embeds
    percent-encoded credentials in the URL (that path isn't affected by the
    curl_cffi bug this works around).
    """
    host_port_url, auth = split_proxy_auth(proxy_str)
    if not host_port_url:
        return
    if curl_requests is not None and isinstance(session, curl_requests.Session):
        session.proxies = {"http": host_port_url, "https": host_port_url}
        session.proxy_auth = auth
    else:
        if auth:
            scheme, rest = host_port_url.split("://", 1)
            url = (f"{scheme}://{urllib.parse.quote(auth[0], safe='')}:"
                   f"{urllib.parse.quote(auth[1], safe='')}@{rest}")
        else:
            url = host_port_url
        session.proxies = {"http": url, "https": url}


def clear_session_proxy(session):
    session.proxies = {}
    if hasattr(session, "proxy_auth"):
        session.proxy_auth = None


BROWSER_OPEN_MAX_ATTEMPTS = 3
BROWSER_OPEN_NAV_TIMEOUT_MS = 20000


def open_browser_with_proxy(proxy_text):
    """Launch one real, visible Chrome window with `proxy_text` pinned to a
    single exit IP for the browser's entire lifetime (via with_sticky_session
    — same pinning the automation itself uses per-thread), instead of the
    rotating-per-request behavior a raw backconnect proxy string would give
    it if handed to a browser unpinned.

    Uses Playwright (already a dependency of the sibling Skool tooling in
    this repo) purely as a launcher here — not for automation — because it's
    the one option that hands the proxy's username/password to Chrome
    without triggering a Basic-Auth popup Chrome would otherwise show for an
    authenticated HTTP proxy passed via a bare --proxy-server flag.

    Rotates to a fresh exit IP (up to BROWSER_OPEN_MAX_ATTEMPTS times) if the
    homepage either fails to load within BROWSER_OPEN_NAV_TIMEOUT_MS or lands
    on /users/login or /users/register instead — confirmed live that some
    exit IPs from a rotating pool get force-redirected to a login wall (a
    dead end with nothing to do but close the window) while most don't; a
    single bad draw from the pool shouldn't be the end of it.

    Runs synchronously (call this from inside a background thread) and
    blocks until the window is closed, so the driver/browser process is
    cleaned up as soon as the user is done with it instead of leaking.
    """
    if sync_playwright is None:
        sender_log("✗ Playwright не установлен — 'pip install playwright' и 'playwright install chrome'")
        return

    has_proxy = bool(proxy_text.strip())
    try:
        with sync_playwright() as p:
            browser = None
            page = None
            for attempt in range(BROWSER_OPEN_MAX_ATTEMPTS):
                proxy_cfg = None
                if has_proxy:
                    tag = "br" + uuid.uuid4().hex[:10]
                    pinned = with_sticky_session(proxy_text, tag, lifetime_minutes=180)
                    host_port_url, auth = split_proxy_auth(pinned)
                    if host_port_url:
                        proxy_cfg = {"server": host_port_url}
                        if auth:
                            proxy_cfg["username"], proxy_cfg["password"] = auth
                    sender_log(f"🌐 Открываю браузер с прокси, закреплён на один IP (sessid-{tag})")
                else:
                    sender_log("🌐 Открываю браузер без прокси (поле пустое или не распозналось)")

                try:
                    browser = p.chromium.launch(
                        headless=False, channel="chrome", proxy=proxy_cfg,
                        args=["--disable-blink-features=AutomationControlled"],
                        ignore_default_args=["--enable-automation"])
                except Exception:
                    # Falls back to Playwright's bundled Chromium if the system
                    # Chrome install (channel="chrome") isn't found.
                    browser = p.chromium.launch(
                        headless=False, proxy=proxy_cfg,
                        args=["--disable-blink-features=AutomationControlled"],
                        ignore_default_args=["--enable-automation"])
                page = browser.new_page()

                nav_ok = True
                try:
                    page.goto("https://www.deviantart.com/", timeout=BROWSER_OPEN_NAV_TIMEOUT_MS)
                except Exception as e:
                    nav_ok = False
                    sender_log(f"⚠ Страница не загрузилась за {BROWSER_OPEN_NAV_TIMEOUT_MS // 1000}с "
                               f"({str(e)[:120]})")

                # /join/ counts as a bad landing too, not just /users/login —
                # confirmed live it's not always a stuck/broken page (some
                # exit IPs get a perfectly functional "Continue with Email"
                # variant), but the button's whole point is browsing via this
                # proxy, not being funnelled into a signup/login gate either
                # way, so treat any of the three the same.
                is_gate_page = nav_ok and any(
                    p in page.url for p in ("/users/login", "/users/register", "/join/"))
                if is_gate_page:
                    sender_log("⚠ Этот IP перенаправляет на страницу входа/регистрации вместо главной — "
                               "похоже, прокси-провайдер считает его подозрительным")

                last_attempt = attempt == BROWSER_OPEN_MAX_ATTEMPTS - 1
                if (nav_ok and not is_gate_page) or last_attempt or not has_proxy:
                    break

                sender_log(f"🔁 Пробую другой IP ({attempt + 2}/{BROWSER_OPEN_MAX_ATTEMPTS})...")
                browser.close()
                browser = None
                page = None

            if browser is None:
                return

            closed = threading.Event()
            page.on("close", lambda _=None: closed.set())
            browser.on("disconnected", lambda: closed.set())
            closed.wait()
    except Exception as e:
        sender_log(f"✗ Не удалось открыть браузер: {str(e)[:200]}")
        return
    sender_log("🌐 Браузер с прокси закрыт")


BROWSER_PROFILES = [
    {"impersonate": "chrome119", "type": "chrome",
     "sec-ch-ua": '"Google Chrome";v="119", "Chromium";v="119", "Not?A_Brand";v="24"'},
    {"impersonate": "chrome120", "type": "chrome",
     "sec-ch-ua": '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"'},
    {"impersonate": "chrome123", "type": "chrome",
     "sec-ch-ua": '"Google Chrome";v="123", "Not:A-Brand";v="8", "Chromium";v="123"'},
    {"impersonate": "chrome124", "type": "chrome",
     "sec-ch-ua": '"Chromium";v="124", "Google Chrome";v="124", "Not-A.Brand";v="99"'},
]


def pick_browser_profile():
    return random.choice(BROWSER_PROFILES)


def make_nav_headers(profile=None):
    if profile is None:
        profile = pick_browser_profile()
    return {
        "accept": ("text/html,application/xhtml+xml,application/xml;q=0.9,"
                  "image/avif,image/webp,image/apng,*/*;q=0.8"),
        "accept-language": "en-US,en;q=0.9",
        "sec-ch-ua": profile["sec-ch-ua"],
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": '"Windows"',
        "sec-fetch-dest": "document",
        "sec-fetch-mode": "navigate",
        "sec-fetch-site": "none",
        "sec-fetch-user": "?1",
        "upgrade-insecure-requests": "1",
    }


def make_session(profile=None):
    if profile is None:
        profile = pick_browser_profile()
    if curl_requests:
        session = curl_requests.Session(impersonate=profile["impersonate"])
    else:
        session = requests.Session()
    session._nav_headers = make_nav_headers(profile)
    session._profile = profile
    return session


NAV_HEADERS = make_nav_headers(BROWSER_PROFILES[3])


def nav_h(session):
    return getattr(session, '_nav_headers', NAV_HEADERS)


# ─── Autonomous proxy pool ────────────────────────────────────────────────────
# Ported and adapted from printables_bot/proxy_pool.py. Continuously scrapes
# free proxies from public GitHub lists, checks each one against DeviantArt
# (accepts either a plain 200 OR a 202 with the AWS WAF challenge signature —
# both prove the proxy actually reached CloudFront), keeps them sorted by
# latency, and hands out the fastest available one on demand. All state is
# persisted to disk so a restart resumes from the last known-good pool.
DA_PROXY_SOURCES = [
    "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt",
    "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt",
    "https://raw.githubusercontent.com/proxifly/free-proxy-list/main/proxies/protocols/http/data.txt",
    "https://raw.githubusercontent.com/mmpx12/proxy-list/master/http.txt",
    "https://raw.githubusercontent.com/mmpx12/proxy-list/master/https.txt",
    "https://raw.githubusercontent.com/prxchk/proxy-list/main/http.txt",
    "https://raw.githubusercontent.com/vakhov/fresh-proxy-list/master/http.txt",
    "https://raw.githubusercontent.com/vakhov/fresh-proxy-list/master/https.txt",
    "https://raw.githubusercontent.com/Zaeem20/FREE_PROXIES_LIST/master/http.txt",
    "https://raw.githubusercontent.com/rdavydov/proxy-list/main/proxies/http.txt",
    "https://raw.githubusercontent.com/rdavydov/proxy-list/main/proxies_anonymous/http.txt",
    "https://raw.githubusercontent.com/casals-ar/proxy-list/main/http",
    "https://raw.githubusercontent.com/casals-ar/proxy-list/main/https",
    "https://raw.githubusercontent.com/berkay-digital/Proxy-Scraper/main/proxies.txt",
    "https://api.proxyscrape.com/v3/free-proxy-list/get?request=displayproxies&protocol=http&timeout=5000&country=all",
    "https://api.proxyscrape.com/v2/?request=displayproxies&protocol=http&timeout=5000",
    "https://www.proxy-list.download/api/v1/get?type=http",
    "https://www.proxy-list.download/api/v1/get?type=https",
    "https://raw.githubusercontent.com/officialputuid/KangProxy/KangProxy/http/http.txt",
    "https://raw.githubusercontent.com/officialputuid/KangProxy/KangProxy/https/https.txt",
    "https://raw.githubusercontent.com/MuRongPIG/Proxy-Master/main/http.txt",
    "https://raw.githubusercontent.com/ErcinDedeoglu/proxies/main/proxies/http.txt",
    "https://raw.githubusercontent.com/ErcinDedeoglu/proxies/main/proxies/https.txt",
    "https://raw.githubusercontent.com/sunny9577/proxy-scraper/master/generated/http_proxies.txt",
    "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt",
    "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/https.txt",
    "https://raw.githubusercontent.com/HyperBeats/proxy-list/main/http.txt",
    "https://raw.githubusercontent.com/HyperBeats/proxy-list/main/https.txt",
    "https://raw.githubusercontent.com/almroot/proxylist/master/list.txt",
    "https://raw.githubusercontent.com/aslisk/proxyhttps/main/https.txt",
    "https://raw.githubusercontent.com/BlackSnowDot/proxylist-update-every-minute/main/http.txt",
    "https://raw.githubusercontent.com/BlackSnowDot/proxylist-update-every-minute/main/https.txt",
    "https://raw.githubusercontent.com/Tsprnay/Proxy-lists/master/proxies/http.txt",
    "https://raw.githubusercontent.com/zloi-user/hideip.me/main/http.txt",
    "https://raw.githubusercontent.com/zloi-user/hideip.me/main/https.txt",
    "https://raw.githubusercontent.com/Anonym0usWork1221/Free-Proxies/main/proxy_files/http_proxies.txt",
    "https://raw.githubusercontent.com/Anonym0usWork1221/Free-Proxies/main/proxy_files/https_proxies.txt",
]

DA_POOL_STATE_FILE = BASE_DIR / "da_proxy_pool_state.json"
DA_POOL_ANON_CHECK_URL = "https://api.ipify.org/"
DA_POOL_CHECK_TIMEOUT = 15
DA_POOL_CHECK_WORKERS = 120
DA_POOL_TARGET_ALIVE = 100
DA_POOL_MIN_ALIVE_TRIGGER = 60
# Hard cap on pool size. Without this the 51 proxy sources add up to 1.2M
# entries (many are stale but still unique), and _pick_next used to copy the
# whole dict to a list under the lock on every worker call — with 120
# checker threads all doing that, throughput dropped to ~1 check/sec (vs.
# ~30/sec at 25K entries). When we hit the cap, `_fetch_proxies` drops the
# oldest dead entries first so fresh unchecked ones always get room.
DA_POOL_MAX_SIZE = 30000
DA_POOL_ALIVE_RECHECK_S = 60
DA_POOL_DEAD_RECHECK_S = 1800
DA_POOL_REFETCH_S = 180
DA_POOL_STALE_MAX_AGE = 24 * 3600


class ProxyPool:
    def __init__(self):
        self.lock = threading.Lock()
        self.proxies = {}
        self._reserved = set()
        self._burned_ips = set()
        self._bad_until = {}
        self._stop = threading.Event()
        self._started = False
        self._fetching = False
        self._last_fetch = ""
        self._last_check = ""
        self._checking_set = set()
        self._check_count = 0
        self._active_checkers = 0
        self._fetch_lock = threading.Lock()
        self._cursor = 0
        self._direct_ip = None
        self._direct_ip_ts = 0

    def start(self):
        if self._started:
            return
        self._started = True
        self._stop.clear()
        self._load_state()
        for _ in range(DA_POOL_CHECK_WORKERS):
            threading.Thread(target=self._check_worker, daemon=True).start()
        threading.Thread(target=self._fetch_loop, daemon=True).start()
        threading.Thread(target=self._alive_watchdog, daemon=True).start()
        threading.Thread(target=self._save_loop, daemon=True).start()

    def stop(self):
        self._stop.set()
        try:
            self._save_state()
        except Exception:
            pass

    def _load_state(self):
        try:
            if not DA_POOL_STATE_FILE.exists():
                return
            with open(DA_POOL_STATE_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            return
        self._burned_ips = set(str(ip) for ip in data.get("burned_ips", []) if ip)
        now = time.time()
        for entry in data.get("proxies", []):
            addr = entry.get("addr", "")
            if not addr or ":" not in addr:
                continue
            ip = addr.split(":", 1)[0]
            if ip in self._burned_ips:
                continue
            last_ts = float(entry.get("lastCheckTs") or 0)
            status = entry.get("status", "unchecked")
            if status in ("dead", "cf_blocked") and last_ts and (now - last_ts) > DA_POOL_STALE_MAX_AGE:
                continue
            self.proxies[addr] = {
                "addr": addr,
                "latency": entry.get("latency", -1),
                "status": status,
                "lastCheck": entry.get("lastCheck", ""),
                "lastCheckTs": last_ts,
            }

    def _save_state(self):
        with self.lock:
            data = {
                "savedAt": time.time(),
                "burned_ips": sorted(self._burned_ips),
                "proxies": [
                    {"addr": p["addr"], "latency": p.get("latency", -1),
                     "status": p.get("status", "unchecked"),
                     "lastCheck": p.get("lastCheck", ""),
                     "lastCheckTs": p.get("lastCheckTs", 0)}
                    for p in self.proxies.values()
                ],
            }
        tmp = str(DA_POOL_STATE_FILE) + ".tmp"
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f)
            os.replace(tmp, str(DA_POOL_STATE_FILE))
        except Exception:
            try:
                os.remove(tmp)
            except Exception:
                pass

    def _save_loop(self):
        while not self._stop.is_set():
            for _ in range(30):
                if self._stop.is_set():
                    return
                time.sleep(1)
            try:
                self._save_state()
            except Exception:
                pass

    @staticmethod
    def _ip_of(addr):
        return addr.split(":", 1)[0] if addr else ""

    def get_best(self, reserve=False, unique_ip=True):
        now = time.time()
        with self.lock:
            self._bad_until = {a: t for a, t in self._bad_until.items() if t > now}
            reserved_ips = {self._ip_of(a) for a in self._reserved}

            def _ok(v):
                if v["status"] != "alive" or v["latency"] <= 0:
                    return False
                if v["addr"] in self._reserved:
                    return False
                if v["addr"] in self._bad_until:
                    return False
                return True

            alive = [v for v in self.proxies.values()
                     if _ok(v)
                     and (not unique_ip or self._ip_of(v["addr"]) not in reserved_ips)]
            if not alive:
                alive = [v for v in self.proxies.values() if _ok(v)]
                if not alive:
                    return None
            alive.sort(key=lambda x: x["latency"])
            top_k = min(5, len(alive))
            choice = random.choice(alive[:top_k])
            addr = choice["addr"]
            if reserve:
                self._reserved.add(addr)
            return addr

    def mark_bad(self, addr, ttl_seconds=300):
        if not addr:
            return
        with self.lock:
            self._bad_until[addr] = time.time() + max(30, int(ttl_seconds))
            self._reserved.discard(addr)

    def release(self, addr):
        if not addr:
            return
        with self.lock:
            self._reserved.discard(addr)

    def mark_burned(self, addr):
        with self.lock:
            ip = self._ip_of(addr)
            if ip:
                self._burned_ips.add(ip)
            self._reserved.discard(addr)
            for a in [a for a in list(self.proxies.keys()) if self._ip_of(a) == ip]:
                self._reserved.discard(a)
                self.proxies.pop(a, None)
        threading.Thread(target=self._save_state, daemon=True).start()

    def add_manual(self, addr):
        if not addr or ":" not in addr:
            return False
        ip = self._ip_of(addr)
        if ip in self._burned_ips:
            return False
        with self.lock:
            if addr in self.proxies:
                return False
            self.proxies[addr] = {"addr": addr, "latency": -1, "status": "unchecked",
                                  "lastCheck": "", "lastCheckTs": 0}
        return True

    def remove(self, addr):
        with self.lock:
            self.proxies.pop(addr, None)
            self._reserved.discard(addr)

    def clear_dead(self):
        with self.lock:
            self.proxies = {k: v for k, v in self.proxies.items() if v["status"] not in ("dead", "cf_blocked")}

    def clear_all(self):
        with self.lock:
            self.proxies.clear()
            self._reserved.clear()

    def get_all(self, limit=500):
        with self.lock:
            result = list(self.proxies.values())
        _order = {"alive": 0, "unchecked": 1, "cf_blocked": 2, "dead": 3}
        result.sort(key=lambda p: (
            _order.get(p["status"], 4),
            p["latency"] if p["latency"] > 0 else 99999,
        ))
        return result[:limit]

    def stats(self):
        with self.lock:
            total = len(self.proxies)
            alive = sum(1 for p in self.proxies.values() if p["status"] == "alive")
            dead = sum(1 for p in self.proxies.values() if p["status"] == "dead")
            cf_blocked = sum(1 for p in self.proxies.values() if p["status"] == "cf_blocked")
            unchecked = total - alive - dead - cf_blocked
            reserved = len(self._reserved)
            in_flight = len(self._checking_set)
            active = self._active_checkers
            check_count = self._check_count
        return {
            "total": total, "alive": alive, "dead": dead, "cf_blocked": cf_blocked,
            "unchecked": unchecked, "reserved": reserved,
            "checking": active > 0 and in_flight > 0,
            "fetching": self._fetching,
            "lastFetch": self._last_fetch, "lastCheck": self._last_check,
            "activeCheckers": active, "inFlight": in_flight,
            "checkCount": check_count, "burnedIps": len(self._burned_ips),
        }

    def _fetch_loop(self):
        while not self._stop.is_set():
            self._fetch_proxies()
            for _ in range(DA_POOL_REFETCH_S):
                if self._stop.is_set():
                    return
                time.sleep(1)

    def _alive_watchdog(self):
        while not self._stop.is_set():
            time.sleep(2)
            try:
                with self.lock:
                    alive = sum(1 for p in self.proxies.values() if p["status"] == "alive")
                if alive < DA_POOL_MIN_ALIVE_TRIGGER and not self._fetching:
                    with self._fetch_lock:
                        if not self._fetching:
                            threading.Thread(target=self._fetch_proxies, daemon=True).start()
            except Exception:
                pass

    def _fetch_proxies(self):
        self._fetching = True
        all_addrs = set()
        http_mod = requests or curl_requests
        for url in DA_PROXY_SOURCES:
            if http_mod is None:
                break
            try:
                r = http_mod.get(url, timeout=15)
                for line in (r.text or "").splitlines():
                    line = line.strip()
                    if not line or line.startswith("#"):
                        continue
                    if line.lower().startswith(("http://", "https://", "socks4://", "socks5://")):
                        line = line.split("://", 1)[1]
                    if ":" in line:
                        parts = line.split(":")
                        ip = parts[0].strip()
                        port_str = parts[1].strip().split()[0]
                        if ip and port_str.isdigit() and 1 <= int(port_str) <= 65535:
                            all_addrs.add(f"{ip}:{port_str}")
            except Exception:
                pass
        with self.lock:
            free_slots = DA_POOL_MAX_SIZE - len(self.proxies)
            if free_slots < len(all_addrs):
                to_free = len(all_addrs) - free_slots
                dead = sorted(
                    (p for p in self.proxies.values() if p["status"] in ("dead", "cf_blocked")),
                    key=lambda p: p.get("lastCheckTs") or 0,
                )
                for p in dead[:to_free]:
                    self.proxies.pop(p["addr"], None)
                    to_free -= 1
                if to_free > 0:
                    unchecked = [p for p in self.proxies.values() if p["status"] == "unchecked"]
                    for p in unchecked[:to_free]:
                        self.proxies.pop(p["addr"], None)

            for addr in all_addrs:
                if len(self.proxies) >= DA_POOL_MAX_SIZE:
                    break
                ip = self._ip_of(addr)
                if ip in self._burned_ips:
                    continue
                if addr not in self.proxies:
                    self.proxies[addr] = {"addr": addr, "latency": -1, "status": "unchecked",
                                          "lastCheck": "", "lastCheckTs": 0}
        self._last_fetch = time.strftime("%H:%M:%S")
        self._fetching = False

    def _pick_next(self):
        now = time.time()
        with self.lock:
            items = list(self.proxies.items())
            n = len(items)
            if not n:
                return None
            start = self._cursor % n
            SCAN = min(500, n)
            for i in range(SCAN):
                addr, p = items[(start + i) % n]
                if p["status"] == "unchecked" and addr not in self._checking_set:
                    self._checking_set.add(addr)
                    self._cursor = (start + i + 1) % n
                    return addr
            best = None
            best_ts = float("inf")
            for addr, p in items:
                if (p["status"] == "alive"
                        and addr not in self._checking_set
                        and now - (p.get("lastCheckTs") or 0) > DA_POOL_ALIVE_RECHECK_S):
                    ts = p.get("lastCheckTs") or 0
                    if ts < best_ts:
                        best_ts = ts
                        best = addr
            if best:
                self._checking_set.add(best)
                return best
            for i in range(SCAN):
                addr, p = items[(start + i) % n]
                if (p["status"] in ("dead", "cf_blocked")
                        and addr not in self._checking_set
                        and now - (p.get("lastCheckTs") or 0) > DA_POOL_DEAD_RECHECK_S):
                    self._checking_set.add(addr)
                    self._cursor = (start + i + 1) % n
                    return addr
            self._cursor = (start + SCAN) % n
        return None

    def _ensure_direct_ip(self):
        if self._direct_ip and (time.time() - self._direct_ip_ts < 600):
            return
        http_mod = requests or curl_requests
        if not http_mod:
            return
        for url in ("http://api.ipify.org/", "http://ifconfig.me/ip",
                     "http://icanhazip.com/"):
            try:
                r = http_mod.get(url, timeout=10)
                ip = r.text.strip().split(",")[0].strip()
                if re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', ip):
                    self._direct_ip = ip
                    self._direct_ip_ts = time.time()
                    return
            except Exception:
                continue

    def _check_one_addr(self, addr):
        """Return (latency_ms, status).

        Anonymity check: request an IP-echo service through the proxy.
        Dead if: can't connect, response isn't a valid IP (not a real proxy),
        or exit IP equals our direct IP (transparent proxy — useless).
        """
        self._ensure_direct_ip()
        proxy = {"http": f"http://{addr}", "https": f"http://{addr}"}
        ua = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                             "AppleWebKit/537.36 (KHTML, like Gecko) "
                             "Chrome/124.0.0.0 Safari/537.36"}
        http_mod = requests or curl_requests
        if http_mod is None:
            return -1, "dead"
        try:
            t0 = time.time()
            r = http_mod.get(DA_POOL_ANON_CHECK_URL, proxies=proxy,
                             timeout=DA_POOL_CHECK_TIMEOUT,
                             allow_redirects=True, headers=ua,
                             verify=False)
        except Exception:
            return -1, "dead"
        ms = round((time.time() - t0) * 1000)
        if r.status_code != 200:
            return -1, "dead"
        exit_ip = (r.text or "").strip().split(",")[0].strip()
        if not re.match(r'^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', exit_ip):
            return -1, "dead"
        if self._direct_ip and exit_ip == self._direct_ip:
            return -1, "dead"
        return ms, "alive"

    def _check_worker(self):
        with self.lock:
            self._active_checkers += 1
        try:
            idle_backoff = 1
            while not self._stop.is_set():
                addr = self._pick_next()
                if not addr:
                    time.sleep(idle_backoff)
                    idle_backoff = min(idle_backoff + 1, 5)
                    continue
                idle_backoff = 1
                lat, status = self._check_one_addr(addr)
                with self.lock:
                    self._checking_set.discard(addr)
                    if addr in self.proxies:
                        self.proxies[addr]["latency"] = lat
                        self.proxies[addr]["status"] = status
                        self.proxies[addr]["lastCheck"] = time.strftime("%H:%M:%S")
                        self.proxies[addr]["lastCheckTs"] = time.time()
                    self._check_count += 1
                    self._last_check = time.strftime("%H:%M:%S")
        finally:
            with self.lock:
                self._active_checkers -= 1


PROXY_POOL = ProxyPool()


def _ensure_proxy_pool_started():
    """Start the proxy pool once — safe to call from any code path.

    The pool used to start only from ``if __name__ == "__main__"``, which
    isn't hit when the app is launched via a wrapper (start.bat, pythonw
    shim, module import for tests, …) — the tab then sat at all-zero stats
    forever with no threads doing anything. Called from Handler.do_GET/POST
    and from the __main__ block, so it always fires as soon as anything
    reaches the process.
    """
    if PROXY_POOL._started:
        return
    try:
        PROXY_POOL.start()
        print(f"[proxy_pool] started with {DA_POOL_CHECK_WORKERS} checker threads")
    except Exception as e:
        print(f"[proxy_pool] start failed: {e}")


# Fire-and-forget on module load so a bare `python -c "import ..."` or any
# other non-__main__ entry point still gets the pool spinning.
_ensure_proxy_pool_started()


# ─── Proxy checker (ported from superfaktura_proxy_checker.py, checked ────────
# against deviantart.com instead) ──────────────────────────────────────────────
PXC_CHECK_URL = "https://www.deviantart.com/"
PXC_ALIVE_FILE = BASE_DIR / "deviantart_alive_proxies.txt"
PXC_DEAD_FILE = BASE_DIR / "deviantart_dead_proxies.txt"
PXC_LOG_FILE = BASE_DIR / "deviantart_proxy_log.txt"

pxc_log_lines = []
pxc_log_lock = threading.Lock()
pxc_checking_lock = threading.Lock()
pxc_is_checking = False
pxc_is_rechecking_alive = False
pxc_alive_cache = set()
pxc_dead_cache = set()
pxc_cache_lock = threading.RLock()
pxc_stop_check_event = threading.Event()
pxc_fail_threshold = 2
pxc_fail_counts = {}

pxc_continuous_event = threading.Event()
pxc_continuous_thread = None
pxc_continuous_control_lock = threading.Lock()
pxc_continuous_extra_list = []

# Proxies a thread is currently using — reserved so no two threads (parser or
# sender, each thread gets its own) ever pick the same exit IP at once.
pxc_in_use = set()
pxc_in_use_lock = threading.Lock()


def pxc_log(text):
    with pxc_log_lock:
        msg = f"[{time.strftime('%H:%M:%S')}] {text}"
        pxc_log_lines.append(msg)
        if len(pxc_log_lines) > MAX_LOG_LINES:
            pxc_log_lines.pop(0)
    print(f"[da-pxc] {text}")
    write_log_file(PXC_LOG_FILE, msg)


def pxc_load_alive():
    global pxc_alive_cache
    if PXC_ALIVE_FILE.exists():
        with open(PXC_ALIVE_FILE, "r", encoding="utf-8") as f:
            with pxc_cache_lock:
                pxc_alive_cache = {line.strip() for line in f if line.strip()}


def pxc_load_dead():
    global pxc_dead_cache
    if PXC_DEAD_FILE.exists():
        with open(PXC_DEAD_FILE, "r", encoding="utf-8") as f:
            with pxc_cache_lock:
                pxc_dead_cache = {line.strip() for line in f if line.strip()}


def pxc_save_alive():
    with pxc_cache_lock:
        proxies = sorted(pxc_alive_cache)
    try:
        with open(PXC_ALIVE_FILE, "w", encoding="utf-8") as f:
            f.write("\n".join(proxies))
    except Exception as e:
        pxc_log(f"Ошибка сохранения живых прокси: {e}")


def pxc_save_dead():
    with pxc_cache_lock:
        proxies = sorted(pxc_dead_cache)
    try:
        with open(PXC_DEAD_FILE, "w", encoding="utf-8") as f:
            f.write("\n".join(proxies))
    except Exception as e:
        pxc_log(f"Ошибка сохранения мёртвых прокси: {e}")


def pxc_check_one(proxy_dict, timeout=REQUEST_TIMEOUT):
    try:
        profile = pick_browser_profile()
        session = make_session(profile)
        resp = session.get(PXC_CHECK_URL, proxies=proxy_dict, headers=make_nav_headers(profile), timeout=timeout)
        return resp.status_code < 500
    except Exception:
        return False


def pxc_check_task(task_q, results_q):
    while True:
        item = task_q.get()
        if item is None:
            break
        idx, proxy_str = item
        if pxc_stop_check_event.is_set() or not proxy_str.strip():
            task_q.task_done()
            continue

        proxy_dict = parse_proxy(proxy_str)
        key = proxy_str.strip()
        if not proxy_dict:
            pxc_log(f"[{idx + 1}] Некорректный формат: {proxy_str}")
            with pxc_cache_lock:
                pxc_dead_cache.add(key)
                pxc_save_dead()
            results_q.put((proxy_str, False))
            task_q.task_done()
            continue

        pxc_log(f"[{idx + 1}] Проверка: {proxy_str}...")
        if pxc_check_one(proxy_dict):
            pxc_log("  ✓ OK")
            with pxc_cache_lock:
                pxc_fail_counts.pop(key, None)
                pxc_alive_cache.add(key)
                pxc_dead_cache.discard(key)
                pxc_save_alive()
            results_q.put((proxy_str, True))
        else:
            with pxc_cache_lock:
                was_alive = key in pxc_alive_cache
                if was_alive:
                    fails = pxc_fail_counts.get(key, 0) + 1
                    pxc_fail_counts[key] = fails
                    if fails < pxc_fail_threshold:
                        pxc_log(f"  ⚠ Неудача {fails}/{pxc_fail_threshold} (остаётся живым): {key}")
                        results_q.put((proxy_str, True))
                        task_q.task_done()
                        continue
                    pxc_log(f"  ✗ DEAD (после {fails} неудач подряд)")
                else:
                    pxc_log("  ✗ DEAD")
                pxc_fail_counts.pop(key, None)
                pxc_dead_cache.add(key)
                pxc_alive_cache.discard(key)
                pxc_save_dead()
                if was_alive:
                    pxc_save_alive()
            results_q.put((proxy_str, False))
        task_q.task_done()


def _pxc_run_pool(proxy_list, thread_count):
    task_q = queue.Queue()
    results_q = queue.Queue()
    for idx, proxy_str in enumerate(proxy_list):
        task_q.put((idx, proxy_str))
    workers = []
    for _ in range(max(1, min(thread_count, len(proxy_list)))):
        t = threading.Thread(target=pxc_check_task, args=(task_q, results_q), daemon=True)
        t.start()
        workers.append(t)
    task_q.join()
    for _ in workers:
        task_q.put(None)
    for t in workers:
        t.join()


def pxc_check_worker(proxy_list, thread_count):
    global pxc_is_checking
    with pxc_checking_lock:
        if pxc_is_checking or pxc_is_rechecking_alive:
            pxc_log("Проверка уже выполняется, подождите...")
            return
        pxc_is_checking = True
    pxc_stop_check_event.clear()
    pxc_log(f"Начало проверки {len(proxy_list)} прокси {thread_count} потоками...")
    _pxc_run_pool(proxy_list, thread_count)
    with pxc_cache_lock:
        alive_count = len(pxc_alive_cache)
        dead_count = len(pxc_dead_cache)
        pxc_save_alive()
        pxc_save_dead()
    verb = "остановлена" if pxc_stop_check_event.is_set() else "завершена"
    pxc_log(f"Проверка {verb}: {alive_count} живых, {dead_count} мёртвых")
    with pxc_checking_lock:
        pxc_is_checking = False


def pxc_start_check(proxy_list, thread_count):
    threading.Thread(target=pxc_check_worker, args=(proxy_list, thread_count), daemon=True).start()


def pxc_recheck_alive_worker(thread_count=3):
    global pxc_is_rechecking_alive
    with pxc_cache_lock:
        proxy_list = sorted(pxc_alive_cache)
    if not proxy_list:
        return
    with pxc_checking_lock:
        if pxc_is_rechecking_alive or pxc_is_checking:
            return
        pxc_is_rechecking_alive = True
    pxc_stop_check_event.clear()
    try:
        thread_count = max(1, min(thread_count, len(proxy_list)))
        pxc_log(f"Перепроверка {len(proxy_list)} живых прокси ({thread_count} потоков)...")
        _pxc_run_pool(proxy_list, thread_count)
        alive_count = len(pxc_alive_cache)
        dead_count = len(pxc_dead_cache)
        pxc_save_alive()
        pxc_save_dead()
        pxc_log(f"Перепроверка завершена: {alive_count} живых, {dead_count} мёртвых")
    finally:
        with pxc_checking_lock:
            pxc_is_rechecking_alive = False


def pxc_continuous_pass(thread_count):
    global pxc_is_rechecking_alive
    with pxc_cache_lock:
        full_list = sorted(set(pxc_alive_cache) | set(pxc_dead_cache) | set(pxc_continuous_extra_list))
    if not full_list:
        return
    with pxc_checking_lock:
        if pxc_is_checking or pxc_is_rechecking_alive:
            return
        pxc_is_rechecking_alive = True
    try:
        threads = max(1, min(thread_count, len(full_list)))
        pxc_log(f"Непрерывная перепроверка: {len(full_list)} прокси ({threads} потоков)...")
        _pxc_run_pool(full_list, threads)
        with pxc_cache_lock:
            alive_count = len(pxc_alive_cache)
            dead_count = len(pxc_dead_cache)
            pxc_save_alive()
            pxc_save_dead()
        pxc_log(f"Непрерывная перепроверка завершена: {alive_count} живых, {dead_count} мёртвых")
    finally:
        with pxc_checking_lock:
            pxc_is_rechecking_alive = False


def pxc_continuous_worker(thread_count):
    while pxc_continuous_event.is_set():
        with pxc_cache_lock:
            n = len(set(pxc_alive_cache) | set(pxc_dead_cache) | set(pxc_continuous_extra_list))
        if n == 0:
            time.sleep(2)
            continue
        pxc_continuous_pass(thread_count)
        time.sleep(1)


def pxc_set_continuous(on, thread_count=3, proxies_text=""):
    global pxc_continuous_thread
    with pxc_continuous_control_lock:
        if on:
            pxc_continuous_extra_list[:] = [p.strip() for p in (proxies_text or "").splitlines() if p.strip()]
            pxc_continuous_event.set()
            if pxc_continuous_thread is None or not pxc_continuous_thread.is_alive():
                pxc_continuous_thread = threading.Thread(
                    target=pxc_continuous_worker, args=(thread_count,), daemon=True)
                pxc_continuous_thread.start()
        else:
            pxc_continuous_event.clear()


def pxc_clear_alive():
    with pxc_cache_lock:
        removed = len(pxc_alive_cache)
        pxc_alive_cache.clear()
        pxc_fail_counts.clear()
        pxc_save_alive()
    pxc_log(f"Удалено {removed} живых прокси")
    return removed


def pxc_prune_dead():
    with pxc_cache_lock:
        stale = {p for p in pxc_alive_cache if p in pxc_dead_cache or pxc_fail_counts.get(p, 0) > 0}
        for p in stale:
            pxc_alive_cache.discard(p)
            pxc_dead_cache.add(p)
            pxc_fail_counts.pop(p, None)
        removed = len(stale)
        if removed:
            pxc_save_alive()
            pxc_save_dead()
    pxc_log(f"Убрано {removed} мёртвых из живых")
    return removed


def pick_live_proxy(exclude=None):
    """Return the fastest currently-alive proxy from the autonomous pool,
    reserving it so no other thread gets the same one (unique-IP dedup, since
    different ports of one host share upstream rate limits). Release with
    ``release_live_proxy()`` when done. Returns None if the pool has nothing
    verified alive right now (worker should back off and retry). Also falls
    back to the legacy pxc_alive_cache (manually pasted / checked proxies),
    so if the user still has that flow going it keeps working.
    """
    addr = PROXY_POOL.get_best(reserve=True, unique_ip=True)
    if addr and addr != exclude:
        return addr
    with pxc_cache_lock:
        alive = list(pxc_alive_cache)
    with pxc_in_use_lock:
        reserved = set(pxc_in_use)
        free = [p for p in alive if p != exclude and p not in reserved]
        if not free:
            return None
        choice = random.choice(free)
        pxc_in_use.add(choice)
        return choice


def release_live_proxy(proxy_str):
    if not proxy_str:
        return
    PROXY_POOL.release(proxy_str)
    with pxc_in_use_lock:
        pxc_in_use.discard(proxy_str)


def da_session_from_cookies(cookie_text, proxy_str=None):
    """Build a session with the pasted cookies loaded into the real cookie
    jar (session.cookies), not a frozen "cookie" header string. A static
    header would never pick up a `Set-Cookie` the server sends back on a
    later request (e.g. a session/auth cookie DeviantArt rotates after the
    first authenticated call) — the jar-based approach lets curl_cffi/
    requests merge any such rotation in automatically, the same way a real
    browser does.
    """
    pairs = parse_cookie_pairs(cookie_text)
    if not pairs:
        return None, None, "куки пустые или не распознаны (нужен формат name=value, по одному на строку или через ;)"
    profile = pick_browser_profile()
    session = make_session(profile)
    for name, value in pairs:
        session.cookies.set(name, value, domain=".deviantart.com")
    if proxy_str:
        apply_proxy_to_session(session, proxy_str)
    return session, profile, ""


def da_headers():
    return {
        "accept": "application/json, text/plain, */*",
        "content-type": "application/json",
        "origin": "https://www.deviantart.com",
    }


def da_post_multipart(session, url, file_field, filename, file_bytes, mime, data_fields, headers, timeout=None):
    """POST a multipart/form-data request across both backends: curl_cffi's
    Session.post() dropped the requests-style `files=` dict (raises "files is
    not supported, use `multipart`") and needs a CurlMime instance instead;
    the stdlib `requests` fallback still wants the classic `files=` dict.
    """
    timeout = timeout or REQUEST_TIMEOUT
    if curl_requests is not None and isinstance(session, curl_requests.Session):
        mp = CurlMime()
        mp.addpart(name=file_field, filename=filename, data=file_bytes, content_type=mime)
        for key, value in data_fields.items():
            mp.addpart(name=key, data=str(value).encode("utf-8"))
        try:
            return session.post(url, multipart=mp, headers=headers, timeout=timeout)
        finally:
            mp.close()
    files = {file_field: (filename, file_bytes, mime)}
    return session.post(url, files=files, data=data_fields, headers=headers, timeout=timeout)


CSRF_DUMP_FILE = BASE_DIR / "deviantart_csrf_debug.html"
# A couple of shapes seen/expected for the embedded config blob: escaped
# (inside a JSON-stringified string, confirmed live) and a plain unescaped
# "csrfToken":"..." in case a logged-in render serializes it differently.
CSRF_PATTERNS = (
    re.compile(r'csrfToken\\"\s*:\s*\\"([^"\\]+)'),
    re.compile(r'csrfToken"\s*:\s*"([^"\\]+)'),
    re.compile(r'csrf_token=([A-Za-z0-9._-]{20,})'),
)


def da_fetch_csrf(session, log_fn=None, prefix=""):
    """Scrape the page-lifetime csrfToken out of /join/'s HTML.

    `log_fn`/`prefix`, if given, report progress on each CloudFront
    burst-block retry below — without them this can silently sit for up to
    ~40s (4 attempts x up to ~11s backoff) with zero log output, which reads
    as a hung thread from a live log even though it's still working.

    Fetches /join/ (not the homepage) and prefers parsing the embedded
    `window.__INITIAL_STATE__ = JSON.parse("...")` blob via
    _extract_initial_state() — the same source _fetch_signup_tokens() reads
    lu_token from — falling back to the regex-only CSRF_PATTERNS for shapes
    that blob doesn't cover. Confirmed live (logged-out): the value shows up
    escaped, since it's embedded inside a JSON-stringified config blob, as
    `csrfToken\\":\\"...` — same token is reused across every _puppy/_napi
    call for the session, so this is done once per run, not per request. On
    failure, dumps the actual fetched HTML to deviantart_csrf_debug.html and
    reports the HTTP status + a content snippet so a real failure (bad
    cookies, login wall, geo/consent redirect) can be told apart from just a
    wrong regex in one look.
    """
    # CloudFront returns a generic "The request could not be satisfied" 403
    # page when several identical homepage requests land in the same instant
    # from one IP (e.g. several no-proxy threads registering at once) — it's
    # a transient burst-block, not a real ban, so retry with backoff before
    # giving up. Any other failure (login wall, geo redirect, etc.) is
    # reported immediately without retrying.
    attempts = 4
    last_err = ""
    for attempt in range(attempts):
        try:
            resp = session.get("https://www.deviantart.com/join/",
                               headers=nav_h(session), timeout=REQUEST_TIMEOUT)

            is_awswaf_challenge = (
                resp.status_code == 202
                and ("awswaf.com" in (resp.text or "") or "AwsWafIntegration" in (resp.text or "")
                     or resp.headers.get("x-amzn-waf-action") == "challenge")
            )
            if is_awswaf_challenge:
                if log_fn:
                    log_fn(f"{prefix} AWS WAF challenge (HTTP 202) — решаю через Playwright...")
                proxy_text = getattr(session, "_proxy_text", None)
                p_csrf, _p_lu, cookies, err = _solve_awswaf_challenge_via_playwright(
                    proxy_text=proxy_text, log_fn=log_fn)
                if p_csrf:
                    _apply_playwright_cookies_to_session(session, cookies)
                    return str(p_csrf), ""
                last_err = f"AWS WAF: {err}"
                if attempt < attempts - 1:
                    time.sleep(2 + attempt)
                    continue
                return None, last_err

            state = _extract_initial_state(resp.text)
            if state:
                token = (state.get("@@config", {}).get("csrfToken")
                         or state.get("@@publicSession", {}).get("csrfToken")
                         or state.get("csrfToken"))
                if token:
                    return str(token), ""
            for pattern in CSRF_PATTERNS:
                m = pattern.search(resp.text)
                if m:
                    return m.group(1), ""

            title_m = re.search(r"<title[^>]*>(.*?)</title>", resp.text or "", re.S | re.I)
            title = (title_m.group(1).strip()[:100] if title_m else "")[:100]
            is_cloudfront_burst_block = resp.status_code == 403 and "could not be satisfied" in title.lower()

            try:
                CSRF_DUMP_FILE.write_text(resp.text or "", encoding="utf-8", errors="replace")
            except Exception:
                pass
            snippet = re.sub(r"\s+", " ", (resp.text or "")[:300]).strip()
            last_err = (f"csrfToken не найден (код {resp.status_code}, длина {len(resp.text or '')}, "
                        f"title: {title!r}) — страница сохранена в deviantart_csrf_debug.html; "
                        f"начало: {snippet[:150]}")

            if is_cloudfront_burst_block and attempt < attempts - 1:
                wait_s = 3 + attempt * 3 + random.uniform(0, 2)
                if log_fn:
                    log_fn(f"{prefix} ⏳ CloudFront burst-блок при получении csrf_token "
                           f"(попытка {attempt + 1}/{attempts}) — повтор через {wait_s:.0f} сек")
                time.sleep(wait_s)
                continue
            return None, last_err
        except Exception as e:
            # A real connection failure (proxy auth/timeout/DNS/etc.) won't
            # fix itself by hammering the same proxy again — fail fast
            # instead of silently burning 4×REQUEST_TIMEOUT with no log line.
            return None, str(e)[:200]
    return None, last_err


# Match both {displayed;target} and {target} formats
LINK_PLACEHOLDER_RE = re.compile(r"\{(?:([^;{}]+);)?([^;{}]+)\}")

INVISIBLE_CHARS = {
    "zwsp": "​",  # Zero Width Space
    "zwnj": "‌",  # Zero Width Non-Joiner
    "zwj": "‍",   # Zero Width Joiner
    "wj": "⁠",    # Word Joiner
    "shy": "­",   # Soft Hyphen
}


def insert_invisible_chars(text, char_key, count):
    """Scatter `count` invisible characters (`char_key` from INVISIBLE_CHARS)
    at random positions in `text`, called fresh before every send so each
    comment gets a slightly different byte pattern. Never inserts inside a
    `{displayed;target}` link placeholder — those spans are re-located after
    every single insertion (positions shift), so an insertion can never land
    inside one even after earlier insertions changed the text length.
    """
    char = INVISIBLE_CHARS.get(char_key)
    if not char or not count:
        return text
    result = list(text)
    for _ in range(int(count)):
        current = "".join(result)
        protected = [m.span() for m in LINK_PLACEHOLDER_RE.finditer(current)]
        safe_positions = [p for p in range(len(result) + 1)
                          if not any(s < p < e for s, e in protected)]
        if not safe_positions:
            break
        pos = random.choice(safe_positions)
        result.insert(pos, char)
    return "".join(result)


_ALL_HOMOGLYPH_CHARS = None

def _has_special_chars(text):
    """Return True if text contains any invisible zero-width chars or homoglyph replacements."""
    global _ALL_HOMOGLYPH_CHARS
    for ch in ("​", "‌", "‍"):
        if ch in text:
            return True
    if _ALL_HOMOGLYPH_CHARS is None:
        _ALL_HOMOGLYPH_CHARS = set()
        for alts in HOMOGLYPHS.values():
            _ALL_HOMOGLYPH_CHARS.update(alts)
    return bool(_ALL_HOMOGLYPH_CHARS.intersection(text))


# Lookalikes from Cyrillic, Greek, Cherokee, mathematical, roman-numeral and
# fullwidth blocks. Each ASCII letter maps to several visually indistinct
# alternatives so successive sends land on different glyphs even for the same
# letter — cheap way to give every send a distinct byte signature that DA's
# text-hash spam filter can't match against the previously flagged text.
HOMOGLYPHS = {
    'a': ['а', 'ɑ', 'ａ', 'ⲁ'],
    'b': ['ƅ', 'ᏼ', 'ｂ'],
    'c': ['с', 'ϲ', 'ⲥ', 'ⅽ', 'ｃ'],
    'd': ['ⅾ', 'ԁ', 'ⅆ', 'ｄ'],
    'e': ['е', 'ｅ', 'ⅇ', 'ꬲ'],
    'f': ['ｆ', 'ϝ', 'ẝ'],
    'g': ['ց', 'ｇ', 'ǵ'],
    'h': ['һ', 'հ', 'ｈ'],
    'i': ['і', 'ⅰ', 'ｉ', 'ɩ'],
    'j': ['ј', 'ϳ', 'ｊ'],
    'k': ['κ', 'ｋ', 'ⲕ'],
    'l': ['ⅼ', 'ӏ', 'ｌ', 'ⅼ'],
    'm': ['ⅿ', 'ｍ', 'ⲙ'],
    'n': ['ո', 'ｎ'],
    'o': ['о', 'ο', 'ⲟ', 'ｏ'],
    'p': ['р', 'ρ', 'ｐ', 'ⲣ'],
    'q': ['ԛ', 'ｑ'],
    'r': ['ｒ', 'ꭇ', 'г'],
    's': ['ѕ', 'ｓ', 'ꮪ'],
    't': ['τ', 'ｔ', 'т'],
    'u': ['ս', 'υ', 'ｕ'],
    'v': ['ⅴ', 'ν', 'ｖ', 'ѵ'],
    'w': ['ԝ', 'ｗ', 'ѡ'],
    'x': ['х', 'ⅹ', 'ｘ'],
    'y': ['у', 'ү', 'ｙ', 'ỿ'],
    'z': ['ｚ', 'ᴢ'],
    'A': ['Α', 'А', 'Ꭺ', 'Ａ'],
    'B': ['Β', 'В', 'Ᏼ', 'Ｂ'],
    'C': ['С', 'Ϲ', 'Ꮯ', 'Ⲥ', 'Ｃ'],
    'D': ['Ꭰ', 'Ⅾ', 'Ｄ'],
    'E': ['Ε', 'Е', 'Ꭼ', 'Ｅ'],
    'F': ['Ϝ', 'Ｆ'],
    'G': ['Ꮐ', 'Ԍ', 'Ｇ'],
    'H': ['Η', 'Н', 'Ꮋ', 'Ｈ'],
    'I': ['Ι', 'І', 'Ⅰ', 'Ｉ'],
    'J': ['Ј', 'Ꭻ', 'Ｊ'],
    'K': ['Κ', 'К', 'Ꮶ', 'Ｋ'],
    'L': ['Ꮮ', 'Ⅼ', 'Ｌ'],
    'M': ['Μ', 'М', 'Ꮇ', 'Ｍ'],
    'N': ['Ν', 'Ｎ'],
    'O': ['Ο', 'О', 'Ꮎ', 'Ｏ', 'Ⲟ'],
    'P': ['Ρ', 'Р', 'Ꮲ', 'Ｐ'],
    'Q': ['Ԛ', 'Ｑ'],
    'R': ['Ꭱ', 'Ꮢ', 'Ｒ'],
    'S': ['Ѕ', 'Ꮪ', 'Ｓ'],
    'T': ['Τ', 'Т', 'Ꭲ', 'Ｔ'],
    'U': ['Ս', 'Ｕ'],
    'V': ['Ѵ', 'Ⅴ', 'Ｖ'],
    'W': ['Ꮃ', 'Ｗ'],
    'X': ['Χ', 'Х', 'Ⅹ', 'Ｘ'],
    'Y': ['Υ', 'Ү', 'Ｙ'],
    'Z': ['Ζ', 'Ꮓ', 'Ｚ'],
}


def homoglyph_uniqueify(text, ratio=0.55):
    """Randomly replace ~`ratio` of the Latin letters in `text` with visually
    identical characters from other Unicode blocks (Cyrillic, Greek, Cherokee,
    roman-numeral, fullwidth). Called fresh before every send so no two
    comments carry the same byte pattern — the point is to slip past DA's
    text-hash spam filter, which locks onto the exact codepoint sequence of a
    previously flagged comment. Never touches characters inside a
    ``{displayed;target}`` link placeholder (those need to stay ASCII so the
    URL parser accepts them) and never touches non-letters (digits,
    punctuation, whitespace, emoji) so the shape of the message is preserved.
    """
    if not text:
        return text
    protected = [m.span() for m in LINK_PLACEHOLDER_RE.finditer(text)]

    def is_protected(idx):
        return any(s <= idx < e for s, e in protected)

    out = []
    for i, ch in enumerate(text):
        if is_protected(i):
            out.append(ch)
            continue
        alts = HOMOGLYPHS.get(ch)
        if alts and random.random() < ratio:
            out.append(random.choice(alts))
        else:
            out.append(ch)
    return "".join(out)


def shorten_url_treeee(session, long_url):
    """POST to tr.ee using Next.js Server Actions to shorten URL and extract slug.
    Returns the slug (e.g. 'Pap3Gr') or None on error.
    Requires full 4-step Server Action sequence.
    """
    try:
        import json as json_lib

        # Ensure session has cookies from tr.ee
        try:
            session.get("https://tr.ee/", timeout=10)
        except Exception:
            pass

        # Server Action IDs from tr.ee (Next.js Server Action hashes).
        # These are stable but may change with site updates.
        action_init1 = "0016aa7c1efbb559c6f527f4faf9eb9bc35c7a9782"  # Init step 1
        action_init2 = "0071c85183a00ec6e92d2a2c3e650edff1205fb58a"  # Init step 2
        action_send = "40990b5f82c286782fa8e6b8825f59c1ea228e2ef0"   # Send URL
        action_fetch = "003dbcc1448c8a89129b201feccf152ba460c1281e"  # Fetch result

        headers_base = {
            "content-type": "text/plain;charset=UTF-8",
            "accept": "text/x-component",
            "next-router-state-tree": "%5B%22%22%2C%7B%22children%22%3A%5B%22(site)%22%2C%7B%22children%22%3A%5B%22(home)%22%2C%7B%22children%22%3A%5B%22__PAGE__%22%2C%7B%7D%2Cnull%2Cnull%2C0%5D%2C%22faqs%22%3A%5B%22__DEFAULT__%22%2C%7B%7D%2Cnull%2Cnull%2C0%5D%7D%2Cnull%2Cnull%2C4%5D%2C%22auth%22%3A%5B%22__DEFAULT__%22%2C%7B%7D%2Cnull%2Cnull%2C0%5D%2C%22footer%22%3A%5B%22__DEFAULT__%22%2C%7B%7D%2Cnull%2Cnull%2C0%5D%2C%22header%22%3A%5B%22__DEFAULT__%22%2C%7B%7D%2Cnull%2Cnull%2C0%5D%2C%22pinned%22%3A%5B%22__DEFAULT__%22%2C%7B%7D%2Cnull%2Cnull%2C0%5D%7D%2Cnull%2Cnull%2C8%5D%7D%2Cnull%2Cnull%2C24%5D",
            "origin": "https://tr.ee",
            "referer": "https://tr.ee/",
        }

        # Step 1: Initialize
        headers = headers_base.copy()
        headers["next-action"] = action_init1
        resp = session.post("https://tr.ee/", headers=headers, data=b"[]", timeout=15)
        if resp.status_code != 200:
            return None

        # Step 2: Initialize again
        headers["next-action"] = action_init2
        resp = session.post("https://tr.ee/", headers=headers, data=b"[]", timeout=15)
        if resp.status_code != 200:
            return None

        # Step 3: Send the URL to shorten
        headers["next-action"] = action_send
        payload = [{"url": long_url}]
        body = json_lib.dumps(payload).encode("utf-8")
        resp = session.post("https://tr.ee/", headers=headers, data=body, timeout=15)
        if resp.status_code != 200:
            return None

        # Step 4: Fetch the result with the actual slug
        headers["next-action"] = action_fetch
        resp_fetch = session.post("https://tr.ee/", headers=headers, data=b"[]", timeout=15)
        if resp_fetch.status_code != 200:
            return None

        # Extract slug from JSON: "shortId":"8HtXkx"
        # The response contains the actual shortened link data
        m = re.search(r'"shortId":"([A-Za-z0-9]+)"', resp_fetch.text)
        if m:
            return m.group(1)
    except Exception:
        pass
    return None


def shorten_url_isgd(session, long_url):
    """Shorten via is.gd — simple GET API, no registration needed.
    Returns the full shortened URL (e.g. 'https://is.gd/abc123') or None.
    """
    try:
        _http = curl_requests or requests
        resp = _http.get("https://is.gd/create.php",
                         params={"format": "simple", "url": long_url},
                         timeout=15)
        if resp.status_code == 200 and resp.text.strip().startswith("http"):
            return resp.text.strip()
    except Exception:
        pass
    return None


def shorten_url(session, long_url, shortener="treeee"):
    if shortener == "isgd":
        return shorten_url_isgd(session, long_url)
    slug = shorten_url_treeee(session, long_url)
    return f"https://tr.ee/{slug}" if slug else None


def extract_first_target_url(text):
    """Pull the first target URL out of the comment-text field: from a
    `{displayed;url}` / `{url}` placeholder if present, otherwise treat the
    whole trimmed field as the URL. Returns the URL string or None.
    """
    m = LINK_PLACEHOLDER_RE.search(text or "")
    if m:
        target = m.group(2).strip()
        return target if target.startswith("http") else None
    stripped = (text or "").strip()
    return stripped if stripped.startswith("http") else None


def replace_links_with_shortened(text, session, shortener="treeee"):
    """Find all {displayed;target_url} or {target_url} in text, shorten each
    target_url, and replace. Returns the modified text and a log string.
    """
    log = []
    result = text
    found_links = list(LINK_PLACEHOLDER_RE.finditer(text))

    if not found_links:
        log.append("⚠ Ссылки не найдены в формате {url} или {displayed;url}")

    for m in found_links:
        displayed = m.group(1).strip() if m.group(1) else None
        target = m.group(2).strip()
        if not target.startswith("http"):
            log.append(f"⚠ Пропущена ссылка (не HTTP): {target[:50]}")
            continue
        short = shorten_url(session, target, shortener)
        if short:
            if displayed:
                result = result.replace(f"{{{displayed};{target}}}", f"{{{displayed};{short}}}", 1)
            else:
                result = result.replace(f"{{{target}}}", f"{{{short}}}", 1)
            log.append(f"✅ {target[:70]} → {short}")
        else:
            log.append(f"❌ {target[:70]} (не сократилась)")
    return result, "\n".join(log) if log else ""


# Confirmed live (2026): a deviation page's server-rendered HTML never
# contains any comment content at all — the whole comments section is an
# empty `<div id="comments"></div>` placeholder that DeviantArt's own
# client-side JS fills in AFTER load via a separate API call. The previous
# approach here (searching the plain-GET response body for the comment's
# text/link) could therefore NEVER have found a real comment, genuinely
# posted or not — a 100% false-negative method. This calls the same JSON
# API the browser's JS uses to populate that div, and matches by the exact
# commentId da_post_comment returns (not by guessing at text content).
DA_COMMENTS_THREAD_URL = "https://www.deviantart.com/_puppy/dashared/comments/thread"
VERIFY_LOAD_MAX_ATTEMPTS = 3


def _copy_waf_cookie(dest_session, src_session):
    """Preload `aws-waf-token` from `src_session` into `dest_session` so the
    verification thread doesn't get hit by the AWS WAF challenge on its first
    request. The token in the posting session was won by Playwright already;
    it's session-scoped, not account-scoped, so it's safe to share within
    the same run.
    """
    if src_session is None:
        return False
    try:
        src_cookies = src_session.cookies.get_dict()
    except Exception:
        return False
    token = src_cookies.get("aws-waf-token")
    if not token:
        return False
    for domain in (".www.deviantart.com", ".deviantart.com"):
        try:
            dest_session.cookies.set("aws-waf-token", token, domain=domain, path="/")
        except TypeError:
            try:
                dest_session.cookies.set("aws-waf-token", token)
            except Exception:
                pass
    return True


def verify_comment_posted(deviation_id, comment_id, proxy_text="", src_session=None, csrf_token=""):
    """Confirm a specific comment (by the exact commentId da_post_comment
    returned) is actually present and visible in the deviation's real
    comment thread.

    `csrf_token`, if given, is reused directly on the first attempt (skips
    the slow da_fetch_csrf call that hits /join/ and may trigger WAF).

    Returns (True, msg) if found and not hidden, (False, msg) if the thread
    loaded fine but the comment isn't there, or (None, msg) if inconclusive.
    """
    if not comment_id:
        return None, "Проверка невозможна — commentId не был получен из ответа на отправку"

    last_err = ""
    for load_attempt in range(VERIFY_LOAD_MAX_ATTEMPTS):
        if src_session is not None and load_attempt == 0:
            vsession = src_session
            owns_session = False
        else:
            vsession = make_session()
            owns_session = True
            if proxy_text.strip():
                tag = "vf" + uuid.uuid4().hex[:10]
                pinned = with_sticky_session(proxy_text, tag, lifetime_minutes=5)
                apply_proxy_to_session(vsession, pinned)
                vsession._proxy_text = pinned
            else:
                vsession._proxy_text = None
            _copy_waf_cookie(vsession, src_session)
            if src_session is not None:
                try:
                    src_cookies = src_session.cookies.get_dict()
                    for cname in ("auth", "auth_secure", "userinfo"):
                        cval = src_cookies.get(cname)
                        if cval:
                            for domain in (".www.deviantart.com", ".deviantart.com"):
                                try:
                                    vsession.cookies.set(cname, cval, domain=domain, path="/")
                                except TypeError:
                                    vsession.cookies.set(cname, cval)
                except Exception:
                    pass

        if csrf_token and load_attempt == 0:
            _csrf = csrf_token
        else:
            _csrf, csrf_err = da_fetch_csrf(vsession)
            if not _csrf:
                last_err = f"csrf: {csrf_err}"
                continue

        try:
            params = {"typeid": 1, "itemid": deviation_id,
                      "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": _csrf}
            resp = vsession.get(DA_COMMENTS_THREAD_URL, params=params, headers=da_headers(), timeout=15)
        except Exception as e:
            last_err = str(e)[:150]
            continue
        if resp.status_code != 200:
            last_err = f"код {resp.status_code}"
            continue
        try:
            thread = (resp.json() or {}).get("thread") or []
        except Exception as e:
            last_err = f"не-JSON ответ: {str(e)[:100]}"
            continue

        # Page (of comments) loaded fine — from here on, whatever we
        # conclude is real signal, not a proxy/IP problem.
        for c in thread:
            if c.get("commentId") == comment_id:
                if c.get("isHidden") or c.get("isSpam") or c.get("isAdminHidden") or c.get("isDeleted"):
                    return False, "Комментарий создан, но скрыт/помечен как спам модерацией DA"
                return True, "Комментарий найден в ленте комментариев"
        return False, "Комментарий не найден в ленте комментариев после проверки"

    return None, f"Не удалось загрузить ленту комментариев после {VERIFY_LOAD_MAX_ATTEMPTS} попыток ({last_err})"


def build_paragraph_content(text):
    """Split `text` on `{displayed;target}` placeholders into tiptap
    text/link nodes for one paragraph. Confirmed against a real captured
    comment: a link is a plain "text" node carrying a "link" mark —
    `text` is what's shown, `marks[0].attrs.href` is where it points, e.g.:
        {"type":"text","marks":[{"type":"link","attrs":{"href":...,
         "target":"_blank","rel":"noopener noreferrer nofollow ugc",
         "class":None}}],"text":"<displayed>"}
    Everything outside `{...;...}` stays a plain text node as before.
    """
    nodes = []
    pos = 0
    for m in LINK_PLACEHOLDER_RE.finditer(text):
        if m.start() > pos:
            nodes.append({"type": "text", "text": text[pos:m.start()]})
        displayed = m.group(1).strip() if m.group(1) else None
        target = m.group(2).strip()
        # If no displayed text, use target URL as link text
        link_text = displayed if displayed else target
        nodes.append({
            "type": "text",
            "marks": [{"type": "link", "attrs": {
                "href": target, "target": "_blank",
                "rel": "noopener noreferrer nofollow ugc", "class": None,
            }}],
            "text": link_text,
        })
        pos = m.end()
    if pos < len(text):
        nodes.append({"type": "text", "text": text[pos:]})
    return nodes or [{"type": "text", "text": ""}]


def build_deviation_attachment_node(deviation, link=None):
    """Wrap a stash/gallery deviation dict (as returned by DA's gallection
    endpoints) into the tiptap `da-deviation` node that renders an attached
    image at the top of a comment. Confirmed against a real captured
    comment that included an uploaded image. When `link` is given, it's set
    as the photo's clickable link (the `link` attr, normally null).
    """
    return {
        "type": "da-deviation",
        "attrs": {"deviation": deviation, "alignment": "center", "link": link, "width": None},
    }


def build_editor_raw(text, image_deviation=None, image_link=None, empty_text=False):
    content = []
    if image_deviation:
        content.append(build_deviation_attachment_node(image_deviation, image_link))
    # "Link in photo" mode: the document is ONLY the da-deviation node, with
    # no paragraph at all — confirmed against a real captured comment where a
    # photo carried a link and no text (content: [{da-deviation}], nothing else).
    if not (empty_text and image_deviation):
        content.append({
            "type": "paragraph",
            "attrs": {"indentType": None, "indentation": None},
            "content": build_paragraph_content(text),
        })
    doc = {"version": "1", "document": {"type": "doc", "content": content}}
    return json.dumps(doc)


_COMMENT_ID_RE = re.compile(r'"commentId"\s*:\s*(\d+)')


def da_post_comment(session, csrf_token, deviation_id, text, referer_url,
                    image_deviation=None, image_link=None, empty_text=False):
    """Returns (ok, err, comment_id). comment_id is the freshly-created
    comment's id (pulled via regex — robust to whatever exact JSON nesting
    the response uses), needed by verify_comment_posted to look this exact
    comment up afterward instead of guessing from its text content."""
    url = "https://www.deviantart.com/_napi/shared_api/comments/post"
    payload = {
        "typeid": 1,
        "itemid": deviation_id,
        "editorRaw": build_editor_raw(text, image_deviation, image_link, empty_text),
        "da_minor_version": DA_MINOR_VERSION,
        "csrf_token": csrf_token,
    }
    headers = da_headers()
    headers["referer"] = referer_url
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    try:
        resp = session.post(url, headers=headers, data=body, timeout=REQUEST_TIMEOUT)
        if resp.status_code == 200 and '"commentId"' in resp.text:
            m = _COMMENT_ID_RE.search(resp.text)
            return True, "", (int(m.group(1)) if m else None)
        set_cookie = resp.headers.get("set-cookie", "") if resp.headers else ""
        extra = f" | set-cookie: {set_cookie[:200]}" if set_cookie else ""
        # Keep enough of the body untruncated for is_spam_error()'s substring
        # match to still see errorCode/errorType/violations even on a longer
        # errorDescription.
        return False, f"код {resp.status_code}: {resp.text[:400]}{extra}", None
    except Exception as e:
        return False, str(e)[:150], None


def da_delete_comment(session, csrf_token, comment_id, deviation_id, referer_url):
    """Delete a comment by its ID. Returns (ok, err)."""
    url = "https://www.deviantart.com/_napi/shared_api/comments/delete"
    payload = {
        "typeid": 1,
        "itemid": deviation_id,
        "commentid": comment_id,
        "da_minor_version": DA_MINOR_VERSION,
        "csrf_token": csrf_token,
    }
    headers = da_headers()
    headers["referer"] = referer_url
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    try:
        resp = session.post(url, headers=headers, data=body, timeout=REQUEST_TIMEOUT)
        if resp.status_code == 200:
            return True, ""
        return False, f"код {resp.status_code}: {resp.text[:300]}"
    except Exception as e:
        return False, str(e)[:150]


_USERNAME_PATTERNS = (
    re.compile(r'"username"\s*:\s*"([^"]+)"'),          # plain JSON
    re.compile(r'\\+"username\\+"\s*:\s*\\+"([^"\\]+)'), # backslash-escaped JSON
    re.compile(r'username%22%3A%22([^%]+)%22'),          # still URL-encoded JSON
    re.compile(r'username%253A%2522([^%]+)%2522'),       # double URL-encoded
)


def _raw_userinfo_value(session, cookie_text):
    """Return the raw `userinfo` cookie value from either the pasted cookie
    text (preferred — never mangled by a jar) or the live session jar."""
    if cookie_text:
        for name, value in parse_cookie_pairs(cookie_text):
            if name == "userinfo" and value:
                return value
    try:
        v = session.cookies.get("userinfo")
        if v:
            return v
    except Exception:
        pass
    try:
        for c in session.cookies.jar:
            if c.name == "userinfo":
                return c.value
    except Exception:
        pass
    return None


def session_cookies_to_text(session):
    """Serialize a session's live cookie jar back into the "name=value;
    name2=value2" text format the cookie textareas (pCookies/sCookies)
    expect — the inverse of parse_cookie_pairs. Used to hand a freshly
    registered account's session over to a plain-cookies field.
    """
    pairs = []
    try:
        for c in session.cookies.jar:
            pairs.append((c.name, c.value))
    except Exception:
        try:
            pairs = list(session.cookies.items())
        except Exception:
            pairs = []
    return "; ".join(f"{name}={value}" for name, value in pairs if name)


def username_from_userinfo_cookie(session, cookie_text=None):
    """Pull the account's own username straight out of the `userinfo`
    cookie — DeviantArt stores it there (URL-encoded JSON), so no API call
    (and no csrf/authorization) is needed. Tries the raw value, one and two
    URL-decodes, and several key shapes. Returns (username, debug_preview);
    username is None if nothing matched, and debug_preview is a short
    scrubbed sample of what was actually in the cookie for logging.
    """
    raw = _raw_userinfo_value(session, cookie_text)
    if not raw:
        return None, "userinfo cookie не найдена среди кук"

    candidates = [raw]
    try:
        once = urllib.parse.unquote(raw)
        if once != raw:
            candidates.append(once)
        twice = urllib.parse.unquote(once)
        if twice != once:
            candidates.append(twice)
    except Exception:
        pass

    for text in candidates:
        for pat in _USERNAME_PATTERNS:
            m = pat.search(text)
            if m:
                return m.group(1).strip(), ""

    preview = urllib.parse.unquote(raw)[:160]
    return None, f"не распознал username в userinfo (начало: {preview!r})"


def da_get_own_username(session, csrf_token, cookie_text=None):
    """Return the logged-in account's own username. Prefers the `userinfo`
    cookie (no API call, works even when the folders endpoint 500s); falls
    back to the gallery-folders endpoint called WITHOUT a `username` param
    (DA returns the caller's own folders, each carrying an `owner` object).
    """
    cookie_name, cookie_dbg = username_from_userinfo_cookie(session, cookie_text)
    if cookie_name:
        return cookie_name, ""

    url = "https://www.deviantart.com/_puppy/dashared/gallection/folders"
    params = {
        "offset": 0, "limit": 250, "type": "gallery",
        "with_all_folder": "true", "with_permissions": "false",
        "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token,
    }
    try:
        resp = session.get(url, params=params, headers=nav_h(session), timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, f"из cookie: {cookie_dbg}; из API: код {resp.status_code}: {resp.text[:120]}"
        data = resp.json()
        results = data.get("results") or []
        if not results:
            return None, "пустой список папок галереи"
        username = ((results[0].get("owner") or {}).get("username") or "").strip()
        if not username:
            return None, "не удалось извлечь username из ответа"
        return username, ""
    except Exception as e:
        return None, str(e)[:150]


def da_get_stash_folder_id(session, csrf_token, username):
    """Return the id of the account's default sta.sh stash folder (always
    present, even when empty — confirmed live)."""
    url = "https://www.deviantart.com/_puppy/dashared/gallection/folders"
    params = {
        "offset": 0, "limit": 250, "type": "stash",
        "with_all_folder": "false", "with_permissions": "false",
        "username": username,
        "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token,
    }
    try:
        resp = session.get(url, params=params, headers=nav_h(session), timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, f"код {resp.status_code}: {resp.text[:150]}"
        data = resp.json()
        results = data.get("results") or []
        if not results:
            return None, "папка sta.sh не найдена"
        return results[0].get("folderId"), ""
    except Exception as e:
        return None, str(e)[:150]


def da_get_stash_contents(session, csrf_token, username, folderid):
    """Return the list of deviations currently sitting in a stash folder."""
    url = "https://www.deviantart.com/_puppy/dashared/gallection/contents"
    params = {
        "username": username, "type": "stash", "folderid": folderid,
        "offset": 0, "limit": 24, "mature_content": "true",
        "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token,
    }
    try:
        resp = session.get(url, params=params, headers=nav_h(session), timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return [], f"код {resp.status_code}: {resp.text[:150]}"
        data = resp.json()
        return data.get("results") or [], ""
    except Exception as e:
        return [], str(e)[:150]


def da_upload_stash_image(session, csrf_token, folderid, image_bytes, filename):
    """Upload raw image bytes into a stash folder via multipart/form-data.
    Confirmed live against a real captured upload."""
    url = "https://www.deviantart.com/_puppy/dashared/deviation/submit/upload/deviation"
    mime = mimetypes.guess_type(filename)[0] or "image/png"
    data = {
        "use_defaults": "false",
        "folderid": str(folderid),
        "da_minor_version": str(DA_MINOR_VERSION),
        "csrf_token": csrf_token,
    }
    headers = {
        "accept": "application/json, text/plain, */*",
        "origin": "https://www.deviantart.com",
    }
    try:
        resp = da_post_multipart(session, url, "upload_file", filename, image_bytes, mime, data, headers)
        if resp.status_code != 200 or '"status":"success"' not in resp.text:
            return False, f"код {resp.status_code}: {resp.text[:200]}"
        return True, ""
    except Exception as e:
        return False, str(e)[:150]


def da_get_or_upload_stash_deviation(session, csrf_token, image_bytes, filename, cookie_text=None,
                                      new_account=False):
    """One-time (per worker/session) helper: if the account's sta.sh
    folder already has an image, reuse it as-is; otherwise upload the
    given bytes and re-fetch to get the full deviation object DA needs
    for the comment payload. Returns (deviation_dict, was_uploaded, err).

    On a freshly-registered account (`new_account=True`) the sta.sh folder
    isn't provisioned instantly — observed live: the very first attempt
    right after signup fails to find/list it, and it starts working once
    the account has been "touched" (e.g. opening sta.sh once in a real
    browser). Retry with backoff instead of failing the whole worker.
    """
    attempts = 6 if new_account else 1
    delay = 5

    username, err = None, ""
    for i in range(attempts):
        username, err = da_get_own_username(session, csrf_token, cookie_text)
        if username:
            break
        if i < attempts - 1:
            time.sleep(delay)
    if not username:
        return None, False, f"не удалось узнать свой username: {err}"

    folderid, err = None, ""
    for i in range(attempts):
        folderid, err = da_get_stash_folder_id(session, csrf_token, username)
        if folderid:
            break
        if i < attempts - 1:
            time.sleep(delay)
    if not folderid:
        return None, False, f"не удалось найти папку sta.sh (аккаунт мог ещё не успеть проинициализировать её): {err}"

    contents, err = da_get_stash_contents(session, csrf_token, username, folderid)
    if contents:
        return contents[0], False, ""

    ok, err = None, ""
    for i in range(attempts):
        ok, err = da_upload_stash_image(session, csrf_token, folderid, image_bytes, filename)
        if ok:
            break
        if i < attempts - 1:
            time.sleep(delay)
    if not ok:
        return None, False, f"не удалось загрузить изображение: {err}"

    contents, err = da_get_stash_contents(session, csrf_token, username, folderid)
    if not contents:
        return None, True, f"изображение загружено, но не удалось получить его данные: {err}"
    return contents[0], True, ""


def da_force_upload_stash_deviation(session, csrf_token, image_bytes, cookie_text=None):
    username, err = da_get_own_username(session, csrf_token, cookie_text)
    if not username:
        return None, f"не удалось узнать username: {err}"
    folderid, err = da_get_stash_folder_id(session, csrf_token, username)
    if not folderid:
        return None, f"папка sta.sh не найдена: {err}"
    rand_name = f"img_{uuid.uuid4().hex[:10]}.png"
    ok, err = da_upload_stash_image(session, csrf_token, folderid, image_bytes, rand_name)
    if not ok:
        return None, f"не удалось загрузить: {err}"
    contents, err = da_get_stash_contents(session, csrf_token, username, folderid)
    if not contents:
        return None, f"загружено, но не удалось получить данные: {err}"
    return contents[0], ""


FEED_POLL_INTERVAL = 20  # seconds between re-fetching the feed page over HTTP

# A pinned sticky-session IP is good for the thread's whole life (see
# with_sticky_session) — but if that exact IP turns out to be CloudFront-
# blocked or otherwise dead, resetting csrf_token alone (the old behavior)
# just means the same dead IP gets asked for a new token forever. Confirmed
# live: a thread that lands on a blocked IP on its very first request stays
# 403'd every single poll for the rest of the run. After this many
# consecutive failed rounds, rotate to a fresh IP instead (same fix
# da_fresh_account_session already applies during registration).
PARSER_ROTATE_AFTER_FAILURES = 2

# A plain (non-home-feed) URL has no known pagination — one fetch always
# returns the same fixed first batch DA server-renders (confirmed live), so
# once that batch has all been seen, every future poll adds nothing until
# the underlying tag/gallery's "best of" set actually changes, which happens
# slowly. Re-fetching it every FEED_POLL_INTERVAL forever wastes a request
# and a thread-slot for nothing — back off exponentially per URL once it's
# gone quiet, and reset the moment it produces something new again.
FEED_ZERO_YIELD_BACKOFF_AFTER = 3  # give a URL this many empty polls first
FEED_MAX_BACKOFF_SECONDS = 20 * 60

# Confirmed via a real scroll HAR: DeviantArt's own homepage JS pages through
# this exact cursor-based JSON endpoint on scroll (not a guess — every field
# below is copied from an actual captured request/response pair). It's the
# "recommended for you" home-feed widget specifically; tag/category pages
# may use a different dabrowse path that hasn't been captured yet, so those
# still fall back to the plain SSR-regex batch.
DABROWSE_RFY_URL = "https://www.deviantart.com/_puppy/dabrowse/networkbar/rfy/deviations"
SCROLL_MAX_PAGES_DEFAULT = 0  # 0 = nonstop, keep paging until hasMore=false or stopped

# Confirmed via a captured HAR of a real search ("q=a", ~2.5k results): the
# search results page has no server-rendered content at all (no
# __NEXT_DATA__, no deviation ids anywhere in the HTML) — every result comes
# from this same dabrowse cursor API family, just under /search/all instead
# of /networkbar/rfy. First page omits `cursor` entirely; response shape
# ({"hasMore","nextCursor","estTotal","deviations":[...]}) is identical to
# the home-feed endpoint, so it reuses the same paging loop.
DABROWSE_SEARCH_URL = "https://www.deviantart.com/_puppy/dabrowse/search/all"


def is_home_feed_url(url):
    u = url.strip().rstrip("/")
    return u in ("https://www.deviantart.com", "http://www.deviantart.com",
                 "https://deviantart.com", "http://deviantart.com")


def fetch_home_feed_scroll(session, csrf_token, prefix, start_cursor=None,
                           max_pages=0, stop_event=None, on_page=None):
    """Follow the real cursor chain (nextCursor -> cursor) exactly like the
    browser does on scroll, starting from `start_cursor` if given (so
    repeated polls can continue deeper into the feed instead of re-fetching
    the same first pages every time).

    `max_pages` caps how many pages this single call will fetch — 0 means
    nonstop (keep going until the server itself says hasMore=false, or
    `stop_event` gets set). `on_page(page_num, page_matches)`, if given, is
    called immediately after each individual page is fetched — so a caller
    can write results to disk page-by-page instead of waiting for the whole
    call to finish.

    Returns (next_cursor, reached_end, pages_fetched):
    - next_cursor: cursor to resume from on the *next* call (None if the
      feed genuinely ran out, i.e. the server itself said hasMore=false).
    - reached_end: True if the server said hasMore=false (as opposed to just
      hitting our own max_pages cap or being stopped mid-way).
    - pages_fetched: how many pages were actually retrieved this call.
    """
    cursor = start_cursor
    reached_end = False
    pages_fetched = 0
    while True:
        if max_pages and pages_fetched >= max_pages:
            break
        if stop_event is not None and stop_event.is_set():
            break
        page_num = pages_fetched + 1
        params = {"da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token}
        if cursor:
            params["cursor"] = cursor
        try:
            resp = session.get(DABROWSE_RFY_URL, params=params, headers=nav_h(session),
                               timeout=REQUEST_TIMEOUT)
        except Exception as e:
            parser_log(f"{prefix} ✗ Скролл, страница {page_num}: {str(e)[:150]}")
            break
        if resp.status_code != 200:
            body = (resp.text or "")[:300]
            parser_log(f"{prefix} Скролл, страница {page_num}: код {resp.status_code} — {body}")
            break
        try:
            data = resp.json()
        except Exception:
            parser_log(f"{prefix} Скролл, страница {page_num}: ответ не JSON — стоп")
            break
        pages_fetched += 1
        page_matches = []
        for d in (data.get("deviations") or []):
            m = DEVIATION_LINK_RE.search(d.get("url") or "")
            if m:
                page_matches.append(m.groups())
        if on_page:
            on_page(page_num, page_matches)
        if not data.get("hasMore") or not data.get("nextCursor"):
            reached_end = True
            cursor = None
            break
        cursor = data["nextCursor"]
    return cursor, reached_end, pages_fetched


def fetch_search_scroll(session, csrf_token, query, stop_event=None, on_page=None):
    """Page all the way through a DA search query via the same cursor
    mechanism as fetch_home_feed_scroll (see DABROWSE_SEARCH_URL) — always
    starts at page 1 (no start_cursor param) and always runs to the end,
    since search threads move to a *different* query for their next pass
    rather than resuming this one from where they left off.

    Returns (reached_end, pages_fetched, est_total, total_matches):
    - reached_end: True if the server said hasMore=false (as opposed to
      being cut short by `stop_event`).
    - est_total: DA's own estimated result count for this query (from the
      first page), or None if never obtained.
    """
    cursor = None
    reached_end = False
    pages_fetched = 0
    est_total = None
    total_matches = 0
    while True:
        if stop_event is not None and stop_event.is_set():
            break
        page_num = pages_fetched + 1
        params = {"q": query, "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token}
        if cursor:
            params["cursor"] = cursor
        try:
            resp = session.get(DABROWSE_SEARCH_URL, params=params, headers=nav_h(session),
                               timeout=REQUEST_TIMEOUT)
        except Exception:
            break
        if resp.status_code != 200:
            break
        try:
            data = resp.json()
        except Exception:
            break
        pages_fetched += 1
        if est_total is None:
            est_total = data.get("estTotal")
        page_matches = []
        for d in (data.get("deviations") or []):
            m = DEVIATION_LINK_RE.search(d.get("url") or "")
            if m:
                page_matches.append(m.groups())
        total_matches += len(page_matches)
        if on_page:
            on_page(page_num, page_matches)
        if not data.get("hasMore") or not data.get("nextCursor"):
            reached_end = True
            break
        cursor = data["nextCursor"]
    return reached_end, pages_fetched, est_total, total_matches


# Confirmed via a captured HAR of a real artist search
# (/search/artists?q=a&order=this-month): same dabrowse cursor family again,
# just under /search/artists. The response body itself wasn't captured (HAR
# omitted it), but every "username":"..." occurrence in an author/deviant
# object across every other dabrowse endpoint follows the same shape, so
# usernames are pulled out with a plain regex over the raw JSON text instead
# of trusting a specific container key name that was never actually seen.
DABROWSE_ARTIST_SEARCH_URL = "https://www.deviantart.com/_puppy/dabrowse/search/artists"
ARTIST_SEARCH_URL_RE = re.compile(r"^https?://(?:www\.)?deviantart\.com/search/artists\?", re.IGNORECASE)
_USERNAME_IN_JSON_RE = re.compile(r'"username"\s*:\s*"([^"]+)"')

# Confirmed live via a captured profile-gallery fetch (username=Flushart):
# one call gets both the watcher count (pageExtraData.stats.watchers) and,
# if any exist, the artist's most recent gallery deviation (the
# "folder_deviations" module, folderId -1 = the "All" folder) — exactly what
# "skip 0-watcher artists, otherwise grab their first illustration" needs,
# in a single request instead of two.
DAUSERPROFILE_GALLERY_INIT_URL = "https://www.deviantart.com/_puppy/dauserprofile/init/gallery"


def is_artist_search_url(url):
    return bool(ARTIST_SEARCH_URL_RE.match(url.strip()))


def parse_artist_search_url(url):
    """Pull `q` and `order` straight out of a pasted /search/artists?... URL."""
    qs = parse_qs(urlparse(url.strip()).query)
    return (qs.get("q") or [""])[0], (qs.get("order") or [""])[0]


def fetch_artist_search_scroll(session, csrf_token, query, order, start_cursor=None,
                               stop_event=None, on_artist=None):
    """Page all the way through a DA artist search via the same cursor
    mechanism as fetch_search_scroll, just over /search/artists. Calls
    on_artist(page_num, username) for every not-yet-seen-this-call username
    found — the caller (parser_feed_thread) decides what to do with each one
    (watcher-count filtering, gallery fetch), kept separate so this function
    only has to know how to walk the cursor chain.

    Returns (next_cursor, reached_end, pages_fetched, artists_seen):
    - next_cursor: cursor to resume from on the *next* poll (None if the
      search genuinely ran out), same resumable-scroll pattern as the
      home-feed walker.
    """
    cursor = start_cursor
    reached_end = False
    pages_fetched = 0
    seen_usernames = set()
    while True:
        if stop_event is not None and stop_event.is_set():
            break
        page_num = pages_fetched + 1
        params = {"q": query, "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token}
        if order:
            params["order"] = order
        if cursor:
            params["cursor"] = cursor
        try:
            resp = session.get(DABROWSE_ARTIST_SEARCH_URL, params=params, headers=nav_h(session),
                               timeout=REQUEST_TIMEOUT)
        except Exception:
            break
        if resp.status_code != 200:
            break
        text = resp.text or ""
        try:
            data = resp.json()
        except Exception:
            break
        pages_fetched += 1
        page_usernames = []
        for m in _USERNAME_IN_JSON_RE.finditer(text):
            uname = m.group(1)
            if not uname or uname in seen_usernames:
                continue
            seen_usernames.add(uname)
            page_usernames.append(uname)
        if on_artist:
            for uname in page_usernames:
                if stop_event is not None and stop_event.is_set():
                    break
                on_artist(page_num, uname)
        if not data.get("hasMore") or not data.get("nextCursor"):
            reached_end = True
            cursor = None
            break
        cursor = data["nextCursor"]
    return cursor, reached_end, pages_fetched, len(seen_usernames)


def da_get_artist_first_illustration(session, csrf_token, username):
    """Fetch `username`'s watcher count and, if they have any deviations,
    the URL of their single most recent one ("illustration 1") — see
    DAUSERPROFILE_GALLERY_INIT_URL. Returns (illustration_url_or_None,
    watchers_or_None); watchers is None if it couldn't be determined at all
    (treat that like 0 — skip), not just when it's actually zero.
    """
    params = {
        "username": username, "with_subfolders": "true", "deviations_limit": "24",
        "da_minor_version": str(DA_MINOR_VERSION), "csrf_token": csrf_token,
    }
    try:
        resp = session.get(DAUSERPROFILE_GALLERY_INIT_URL, params=params, headers=nav_h(session),
                           timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return None, None
        data = resp.json()
    except Exception:
        return None, None
    watchers = ((data.get("pageExtraData") or {}).get("stats") or {}).get("watchers")
    modules = ((data.get("gruser") or {}).get("page") or {}).get("modules") or []
    for mod in modules:
        module_data = mod.get("moduleData") or {}
        if module_data.get("dataKey") != "folder_deviations":
            continue
        deviations = (module_data.get("folderDeviations") or {}).get("deviations") or []
        if deviations:
            return deviations[0].get("url"), watchers
        break
    return None, watchers


def distribute_urls(urls, n):
    """Split `urls` into `n` non-empty round-robin chunks (n is expected to
    already be <= len(urls), so every chunk gets at least one).
    """
    chunks = [[] for _ in range(n)]
    for i, u in enumerate(urls):
        chunks[i % n].append(u)
    return [c for c in chunks if c]


THREAD_START_STAGGER_SECONDS = 1


def stagger_before_next_thread(stop_event=None):
    """Pause between spawning each parser/sender thread so a big thread
    count doesn't all hit DeviantArt (proxy setup, csrf fetch, registration,
    first request) in the very same instant. Interruptible so hitting Stop
    right after Start doesn't wait out the full pause first.
    """
    for _ in range(THREAD_START_STAGGER_SECONDS):
        if stop_event is not None and stop_event.is_set():
            break
        time.sleep(1)


def record_matches(prefix, matches, seen_ids, seen_lock, ignore_blacklist=False):
    """Dedupe `matches` against `seen_ids`, skip blacklisted authors, and
    append whatever's left straight to the notebook immediately. Returns
    (new_count, duplicates, blacklisted_count) for logging.
    """
    new_urls = []
    duplicates = 0
    blacklisted_count = 0
    for username, slug, dev_id in matches:
        with seen_lock:
            if dev_id in seen_ids:
                duplicates += 1
                continue
            seen_ids.add(dev_id)
        if not ignore_blacklist and is_blacklisted(username):
            blacklisted_count += 1
            continue
        new_urls.append(f"https://www.deviantart.com/{username}/art/{slug}-{dev_id}")

    if new_urls:
        append_notebook(new_urls)
        with parser_lock:
            parser_state["found"] += len(new_urls)

    return len(new_urls), duplicates, blacklisted_count


# ============================================================================
# Auto-search discovery — only kicks in when there are more parser threads
# than pasted feed URLs (see parser_worker): idle thread capacity searches DA
# via fetch_search_scroll instead of uselessly re-hitting an already-fetched
# feed URL from extra threads (a single fetch of a given URL only ever
# returns the same first batch, so piling more threads onto it adds nothing).
# ============================================================================

# Single letters/digits: guaranteed huge, near-inexhaustible result sets
# (confirmed live: "a" alone returned an estimated ~2554 results) since they
# substring-match almost every title/tag. Ordered by standard English letter
# frequency as a stand-in for "most content" — no real DA search-volume data
# to sort by.
SEARCH_LETTERS_DIGITS = list("etaoinshrdlcumwfgypbvkjxqz") + list("1203456789")

# Every 2-letter combo (26x26=676) — a cheap, systematic way to massively
# widen the pool beyond hand-curated words: still broad substring matches
# (nowhere near as huge as single letters, but far from exhausted either),
# and unlike a curated word list this needs no upkeep to keep growing.
# Confirmed live: 15+ concurrent search threads sharing ~136 queries (26
# letters/digits + ~100 words) burn through the whole pool in under an hour
# and then sit idle in 5-minute cooldown-wait loops for the next 12-24h —
# the pool has to be an order of magnitude bigger to keep that many threads
# fed continuously.
SEARCH_TWO_LETTER_COMBOS = [a + b for a in string.ascii_lowercase for b in string.ascii_lowercase]

# Hand-curated words expected to have heavy DeviantArt coverage: broadest
# medium/format terms first, then popular subjects/styles, creatures/genres,
# top mainstream fandoms, and adoptable/OC-culture/scene terms last. This is
# a reasonable guess at what's actually tagged a lot on DA, not a measurement
# against real search-volume data.
SEARCH_POPULAR_WORDS = list(dict.fromkeys([
    "art", "digitalart", "fanart", "anime", "drawing", "illustration",
    "photography", "traditionalart", "painting", "sketch",
    "oc", "fantasy", "portrait", "manga", "characterdesign", "nature",
    "landscape", "cosplay", "chibi", "conceptart", "watercolor", "cute",
    "comic", "pixelart",
    "dragon", "wolf", "cat", "dog", "fox", "furry", "scifi", "dark",
    "gothic", "horror", "abstract", "surreal", "kawaii", "steampunk",
    "cyberpunk", "vampire", "elf", "fairy", "angel", "demon", "witch",
    "magic", "warrior", "knight", "princess", "mermaid", "dinosaur",
    "robot", "mecha", "ninja", "samurai", "pirate", "alien", "space", "galaxy",
    "pokemon", "sonic", "undertale", "marvel", "starwars", "harrypotter",
    "naruto", "zelda", "dragonball", "onepiece", "minecraft", "fnaf",
    "overwatch", "kirby", "disney", "batman",
    "adoptable", "ych", "fursona", "lineart", "inktober", "acrylic",
    "oilpainting", "sculpture", "doodle", "colorpencil", "digitalpainting",
    "speedpaint",
    "love", "couple", "model", "cityscape", "architecture", "forest",
    "ocean", "mountain", "sunset", "winter", "autumn", "castle", "dungeon",
    # --- techniques/media ---
    "linework", "shading", "coloring", "flatcolor", "cellshading", "render3d",
    "vectorart", "papercraft", "clayart", "sculpting", "ceramics",
    "printmaking", "collage", "mixedmedia", "gouache", "charcoal", "pastelart",
    "penandink", "markerart", "crayonart", "graffiti", "streetart", "muralart",
    "typography", "calligraphy", "lettering", "handlettering", "stencilart",
    "airbrushart", "pyrography", "embroidery", "crochet", "knitting", "sewing",
    "costumedesign", "propmaking", "makeupart", "sfxmakeup", "facepaint",
    "bodypaint", "tattoodesign", "tattooart", "hennaart",
    # --- software/tools ---
    "procreate", "clipstudio", "photoshopart", "paintsai", "krita", "blender",
    "zbrush", "gimpart", "illustratorart", "affinityphoto", "mspaintart",
    "substancepainter",
    # --- style/aesthetic ---
    "cybergoth", "vaporwave", "synthwave", "retrowave", "y2kaesthetic",
    "grungeart", "vintageart", "retroart", "noirart", "minimalist",
    "minimalism", "geometricart", "psychedelic", "trippyart", "glitchart",
    "lowpoly", "isometricart", "pixelsprite", "spriteart", "melancholy",
    "dreamy", "ethereal", "moodyart", "cozyart", "aesthetic",
    "pastelaesthetic", "darkaesthetic", "cottagecore", "goblincore",
    "fairycore", "dreamcore", "weirdcore", "cyberaesthetic",
    # --- colors ---
    "monochrome", "blackandwhite", "grayscale", "colorful", "pastelcolors",
    "neonart", "rainbowart", "colorgradient",
    # --- creatures/species ---
    "griffin", "phoenix", "unicorn", "centaur", "werewolf", "wendigo",
    "kitsune", "yokai", "cryptid", "monsterart", "monstergirl", "kaiju",
    "reptileart", "lizardart", "snakeart", "birdart", "owlart", "raven",
    "crow", "eagle", "hawk", "horseart", "ponyart", "mlp", "brony", "deerart",
    "stagart", "rabbitart", "bunnyart", "bearart", "lionart", "tigerart",
    "pantherart", "hyenaart", "sharkart", "whaleart", "dolphinart",
    "octopusart", "jellyfish", "insectart", "butterflyart", "mothart",
    "spiderart", "beetleart", "dragonflyart",
    # --- fandoms ---
    "genshinimpact", "honkai", "fridaynightfunkin", "hazbinhotel",
    "helluvaboss", "stevenuniverse", "adventuretime", "gravityfalls",
    "regularshow", "amphibia", "owlhouse", "littlewitchacademia", "rwby",
    "hetalia", "voltron", "transformers", "gijoe", "teentitans", "dcuniverse",
    "spiderman", "avengers", "xmen", "deadpool", "supernatural", "doctorwho",
    "sherlock", "gameofthrones", "witcher", "skyrim", "elderscrolls",
    "finalfantasy", "kingdomhearts", "persona", "danganronpa", "fireemblem",
    "splatoon", "animalcrossing", "smashbros", "metroid", "megaman",
    "castlevania", "silenthill", "residentevil", "bloodborne", "darksouls",
    "eldenring", "warhammer", "diablo", "warcraft", "worldofwarcraft",
    "leagueoflegends", "valorant", "apexlegends", "fortnite", "amongus",
    "cuphead", "hollowknight", "terraria", "stardewvalley", "helltaker",
    "yugioh", "digimon", "beyblade", "cardcaptorsakura", "sailormoon",
    "inuyasha", "bleach", "attackontitan", "demonslayer", "jujutsukaisen",
    "myheroacademia", "tokyoghoul", "deathnote", "fullmetalalchemist",
    "hunterxhunter", "onepunchman", "jojobizarreadventure", "evangelion",
    "cowboybebop", "spyxfamily", "chainsawman", "blueperiod", "haikyuu",
    "toradora",
    # --- nature/scenery ---
    "waterfall", "river", "lake", "desert", "jungle", "meadow", "garden",
    "flowers", "floral", "treeart", "skyart", "clouds", "stars", "moonart",
    "sunart", "storm", "rainart", "snowart", "icart", "fireart", "lava",
    "volcano", "cave", "cliff", "island", "beach", "underwater", "coral",
    "reef",
    # --- character/people ---
    "malecharacter", "femalecharacter", "childcharacter", "elderly",
    "family", "friendship", "wedding", "battle", "actionpose", "dynamicpose",
    "expression", "emotionart", "eyesart", "handsart", "hairart", "wingsart",
    "armorart", "weaponart", "swordart", "shieldart", "bowart", "gunart",
    "crownart", "jewelryart", "clothingdesign", "fashionart", "dressdesign",
    "uniformdesign",
    # --- DA culture/community ---
    "artchallenge", "artstream", "wip", "workinprogress", "commission",
    "commissionsopen", "artrequest", "artraffle", "giveaway", "collab",
    "collaboration", "artshare", "artcommunity", "artistsupport",
    "supportartists", "smallartist", "beginnerartist", "artimprovement",
    "artprogress", "referencesheet", "characterreference", "designsheet",
    "turnaround", "expressionsheet", "palettechallenge", "colorpalette",
    "designchallenge",
    # --- stock/resources ---
    "stockphoto", "textures", "brushes", "overlay", "background",
    "wallpaper", "icon", "avatarart", "banner", "header", "emote", "emoji",
    "sticker", "stamp", "badge", "pin",
    # --- holidays/seasons ---
    "halloween", "christmas", "easter", "valentine", "newyear", "spring",
    "summer", "spooky", "pumpkin", "santa", "snowman",
    # --- literature ---
    "poetry", "poem", "shortstory", "fanfiction", "worldbuilding",
    "storytelling",
    # --- photography ---
    "streetphotography", "macrophotography", "wildlifephotography",
    "portraitphotography", "blackandwhitephoto", "filmphotography",
    "naturephotography", "urbanphotography", "nightphotography",
    "longexposure",
    # --- misc DA tags ---
    "pride", "prideart", "meme", "crossover", "parody", "alternateuniverse",
    "headcanon", "shipart", "angst", "fluff", "hurtcomfort",
]))

SEARCH_QUERY_QUEUE = SEARCH_LETTERS_DIGITS + SEARCH_TWO_LETTER_COMBOS + SEARCH_POPULAR_WORDS

SEARCH_QUERY_STATE_FILE = BASE_DIR / "deviantart_search_query_state.json"
search_query_state_lock = threading.Lock()
search_queries_in_use = set()

# A query paged all the way to the end is left alone this long before it's
# worth re-checking for new posts.
SEARCH_FULL_SCAN_COOLDOWN_SECONDS = 24 * 3600
# A query that was interrupted (stop/error) but still added fewer than this
# many genuinely new posts is probably just scraps of what's already been
# seen — cool it down too, just for less time than a real full pass.
SEARCH_LOW_YIELD_THRESHOLD = 100
SEARCH_LOW_YIELD_COOLDOWN_SECONDS = 12 * 3600


def _load_search_query_state():
    if not SEARCH_QUERY_STATE_FILE.exists():
        return {}
    try:
        return json.loads(SEARCH_QUERY_STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _save_search_query_state(state):
    try:
        SEARCH_QUERY_STATE_FILE.write_text(json.dumps(state, ensure_ascii=False), encoding="utf-8")
    except Exception:
        pass


def claim_next_search_query():
    """Pick a random available query — neither on cooldown nor already being
    worked by another search thread right now — and mark it in-use. Returns
    None if everything is unavailable right now (caller should wait a bit
    and retry).

    Randomized rather than always scanning SEARCH_QUERY_QUEUE in the same
    fixed order: with hundreds of threads-worth of concurrent claims a fixed
    order means everyone races for the same handful of queries at the front
    of the list first, and repeat runs re-explore the pool in an identical,
    predictable sequence instead of spreading out across letters, 2-letter
    combos, and curated words.
    """
    now = time.time()
    with search_query_state_lock:
        state = _load_search_query_state()
        for q in random.sample(SEARCH_QUERY_QUEUE, len(SEARCH_QUERY_QUEUE)):
            if q in search_queries_in_use:
                continue
            if now < (state.get(q) or {}).get("cooldown_until", 0):
                continue
            search_queries_in_use.add(q)
            return q
        return None


def seconds_until_next_available_query(min_wait=15, max_wait=300):
    """How long until the soonest-expiring cooldown clears, clamped to a
    sane range — used instead of a blind fixed sleep when every query is
    unavailable, so a search thread doesn't sit idle way longer than
    necessary just because it happened to check right after everything
    went on cooldown at once.
    """
    now = time.time()
    with search_query_state_lock:
        state = _load_search_query_state()
    soonest = None
    for q in SEARCH_QUERY_QUEUE:
        if q in search_queries_in_use:
            continue
        cooldown_until = (state.get(q) or {}).get("cooldown_until", 0)
        if cooldown_until <= now:
            return min_wait  # something should actually be claimable already
        if soonest is None or cooldown_until < soonest:
            soonest = cooldown_until
    if soonest is None:
        return max_wait
    return max(min_wait, min(max_wait, soonest - now))


def release_search_query(query, new_count, reached_end, est_total=None, fetch_failed=False):
    """Record how this pass over `query` went and set its next cooldown.

    `fetch_failed=True` means the very first request for this query failed
    outright (pages_fetched==0 — a blocked/dead exit IP, not a real search
    result) — that says nothing about the query itself, so it's released
    with no cooldown and no stats touched instead of being punished with the
    same 12h "low yield" cooldown a genuinely-scanned-but-scraps query gets.
    Confirmed live: without this, a proxy hiccup permanently burns a query
    out of the pool for half a day for no reason, compounding the "pool too
    small for this many concurrent threads" problem.
    """
    now = time.time()
    with search_query_state_lock:
        search_queries_in_use.discard(query)
        if fetch_failed:
            return
        state = _load_search_query_state()
        info = state.setdefault(query, {})
        info["last_scanned_at"] = now
        info["last_new_count"] = new_count
        if est_total is not None:
            info["est_total"] = est_total
        if reached_end:
            info["cooldown_until"] = now + SEARCH_FULL_SCAN_COOLDOWN_SECONDS
        elif new_count < SEARCH_LOW_YIELD_THRESHOLD:
            info["cooldown_until"] = now + SEARCH_LOW_YIELD_COOLDOWN_SECONDS
        else:
            info["cooldown_until"] = 0
        _save_search_query_state(state)


SEARCH_QUERY_RANKING_FILE = BASE_DIR / "deviantart_search_query_ranking.txt"


def write_search_query_ranking_file():
    """Snapshot the current search-query state as a human-readable, ranked
    text file — queries DA reports the most results for first, so it's easy
    to see at a glance which auto-picked words/letters are actually worth
    having in SEARCH_POPULAR_WORDS and which barely add anything.
    """
    with search_query_state_lock:
        state = _load_search_query_state()
    now = time.time()
    rows = []
    for q in SEARCH_QUERY_QUEUE:
        info = state.get(q) or {}
        rows.append((
            info.get("est_total"),
            q,
            info.get("last_new_count"),
            info.get("last_scanned_at"),
            info.get("cooldown_until", 0),
        ))
    # Scanned queries first (ranked by DA's own estTotal, highest first),
    # never-scanned ones after (still in priority-queue order).
    rows.sort(key=lambda r: (r[0] is None, -(r[0] or 0)))

    lines = [
        f"Рейтинг поисковых запросов — по оценке DeviantArt (estTotal), самые крупные сверху.",
        f"Снято: {time.strftime('%Y-%m-%d %H:%M:%S')}",
        "",
        f"{'запрос':<20} {'estTotal':>10} {'записано в последний раз':>26} {'последний скан':>20} {'статус':>16}",
    ]
    for est_total, q, last_new, last_scanned, cooldown_until in rows:
        est_str = str(est_total) if est_total is not None else "—"
        new_str = str(last_new) if last_new is not None else "—"
        scanned_str = time.strftime("%m-%d %H:%M", time.localtime(last_scanned)) if last_scanned else "никогда"
        if not last_scanned:
            status = "не проверялся"
        elif now < cooldown_until:
            remaining_min = int((cooldown_until - now) / 60)
            status = f"кулдаун {remaining_min} мин"
        else:
            status = "доступен"
        lines.append(f"{q:<20} {est_str:>10} {new_str:>26} {scanned_str:>20} {status:>16}")

    try:
        SEARCH_QUERY_RANKING_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except Exception:
        pass
    return SEARCH_QUERY_RANKING_FILE


# ============================================================================
# Artist-search rotation — the same "more threads than URLs" search threads
# also alternate into /search/artists queries (see fetch_artist_search_scroll
# / da_get_artist_first_illustration), not just plain deviation search. Own
# cooldown tracking, kept completely separate from the deviation-search one
# above: the same word means something different in each ("art" as a
# deviation-search term vs. "art" as an artist-search term aren't the same
# query and shouldn't share a cooldown).
# ============================================================================

# Per the user's explicit ask ("список юзеров отфильтрованых в этом месяца")
# and confirmed as a real option live (seen in a captured referer alongside
# "most-recent" and "personalized") — DA's own artist-search order values.
ARTIST_SEARCH_ORDER = "this-month"

ARTIST_SEARCH_QUERY_STATE_FILE = BASE_DIR / "deviantart_artist_search_query_state.json"
artist_search_state_lock = threading.Lock()
artist_search_queries_in_use = set()

# Each artist "hit" costs an extra request (the gallery-init fetch) and
# yields at most one illustration, so the bar for "this query panned out" is
# much lower than the 100-new-posts bar deviation search uses.
ARTIST_SEARCH_LOW_YIELD_THRESHOLD = 10


def _load_artist_search_state():
    if not ARTIST_SEARCH_QUERY_STATE_FILE.exists():
        return {}
    try:
        return json.loads(ARTIST_SEARCH_QUERY_STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _save_artist_search_state(state):
    try:
        ARTIST_SEARCH_QUERY_STATE_FILE.write_text(json.dumps(state, ensure_ascii=False), encoding="utf-8")
    except Exception:
        pass


def claim_next_artist_search_query():
    # Randomized for the same reason as claim_next_search_query — see there.
    now = time.time()
    with artist_search_state_lock:
        state = _load_artist_search_state()
        for q in random.sample(SEARCH_QUERY_QUEUE, len(SEARCH_QUERY_QUEUE)):
            if q in artist_search_queries_in_use:
                continue
            if now < (state.get(q) or {}).get("cooldown_until", 0):
                continue
            artist_search_queries_in_use.add(q)
            return q
        return None


def release_artist_search_query(query, written_count, reached_end, fetch_failed=False):
    # fetch_failed: see release_search_query — a proxy/IP failure shouldn't
    # burn this query's cooldown either.
    now = time.time()
    with artist_search_state_lock:
        artist_search_queries_in_use.discard(query)
        if fetch_failed:
            return
        state = _load_artist_search_state()
        info = state.setdefault(query, {})
        info["last_scanned_at"] = now
        info["last_new_count"] = written_count
        if reached_end:
            info["cooldown_until"] = now + SEARCH_FULL_SCAN_COOLDOWN_SECONDS
        elif written_count < ARTIST_SEARCH_LOW_YIELD_THRESHOLD:
            info["cooldown_until"] = now + SEARCH_LOW_YIELD_COOLDOWN_SECONDS
        else:
            info["cooldown_until"] = 0
        _save_artist_search_state(state)


def seconds_until_next_available_artist_query(min_wait=15, max_wait=300):
    now = time.time()
    with artist_search_state_lock:
        state = _load_artist_search_state()
    soonest = None
    for q in SEARCH_QUERY_QUEUE:
        if q in artist_search_queries_in_use:
            continue
        cooldown_until = (state.get(q) or {}).get("cooldown_until", 0)
        if cooldown_until <= now:
            return min_wait
        if soonest is None or cooldown_until < soonest:
            soonest = cooldown_until
    if soonest is None:
        return max_wait
    return max(min_wait, min(max_wait, soonest - now))


def run_artist_search_pass(session, csrf_token, prefix, query, seen_ids, seen_lock,
                           ignore_blacklist, stop_event, start_cursor=None, order=None):
    """Runs one (start_cursor-resumable) pass over an artist-search query,
    visiting each newly-found artist's gallery to decide whether to record
    their most recent illustration (see da_get_artist_first_illustration).
    Shared by parser_feed_thread (a pasted /search/artists?... URL, which may
    specify its own `order`) and parser_search_thread (the auto-rotation,
    which always uses ARTIST_SEARCH_ORDER) so the actual per-artist logic
    only lives in one place.

    Returns (next_cursor, reached_end, pages_fetched, artists_seen,
    checked_total, with_watchers_total, written_total).
    """
    order = order or ARTIST_SEARCH_ORDER
    checked_total = 0
    with_watchers_total = 0
    written_total = 0

    def _on_artist(page_num, username):
        nonlocal checked_total, with_watchers_total, written_total
        if stop_event.is_set():
            return
        checked_total += 1
        illustration_url, watchers = da_get_artist_first_illustration(session, csrf_token, username)
        if not watchers:
            # No watchers almost always means no posts either (per live
            # observation) — skip the extra work of even looking.
            return
        with_watchers_total += 1
        if not illustration_url:
            return
        m = DEVIATION_LINK_RE.search(illustration_url)
        if not m:
            return
        written, dup, bl = record_matches(prefix, [m.groups()], seen_ids, seen_lock, ignore_blacklist)
        written_total += written
        if written:
            parser_log(f"{prefix} 🎨 {username} (watchers: {watchers}): {illustration_url}")

    next_cursor, reached_end, pages_fetched, artists_seen = fetch_artist_search_scroll(
        session, csrf_token, query, order, start_cursor,
        stop_event=stop_event, on_artist=_on_artist)
    return (next_cursor, reached_end, pages_fetched, artists_seen,
            checked_total, with_watchers_total, written_total)


def parser_search_thread(idx, cookie_text, proxy_text, use_live_proxies,
                         stop_event, seen_ids, seen_lock, ignore_blacklist=False,
                         search_illustrations_only=False):
    """Dedicated search-discovery thread — only spun up when there are more
    parser threads than pasted feed URLs (see parser_worker). Alternates
    between two independent, independently-cooling-down query pools each
    cycle: plain deviation search (claim_next_search_query /
    fetch_search_scroll) and artist search, filtered to artists with any
    watchers, writing their most recent illustration (claim_next_artist_
    search_query / run_artist_search_pass) — per the user's explicit ask to
    "чередовать поиск иллюстраций и список юзеров". If the preferred mode
    for this cycle has nothing available, falls through to the other mode
    before actually waiting, so one pool being fully on cooldown doesn't
    idle the thread while the other pool has work.
    """
    prefix = f"[{idx + 1}]"
    reserved_proxy = None
    try:
        if use_live_proxies:
            reserved_proxy = pick_live_proxy()
            if not reserved_proxy:
                parser_log(f"{prefix} ⚠ Нет свободных живых прокси (все заняты другими потоками, "
                           f"или живых прокси ещё нет — проверь их на вкладке «Прокси»)")
                return
            base_proxy_str = reserved_proxy
            raw_proxy_str = reserved_proxy
            parser_log(f"{prefix} ✓ Занял живой прокси: {reserved_proxy}")
        else:
            base_proxy_str = proxy_text
            raw_proxy_str = proxy_text
            if proxy_text.strip() and not parse_proxy(proxy_text):
                parser_log(f"{prefix} ⚠ Не удалось разобрать прокси: {proxy_text.strip()[:80]}")

        # A rotating proxy hands a different exit IP to every new connection
        # (see with_sticky_session) — left unpinned, every single request
        # this long-lived thread makes could land on a different, possibly
        # broken, exit node (confirmed live: every thread hitting the same
        # rotating pool unpinned failed with an identical TLS/cert error).
        # Pin one IP for the thread's whole lifetime, same as registration
        # already does. No-op for proxies without a login (live-pool ones).
        if raw_proxy_str.strip():
            sticky_tag = "ps" + uuid.uuid4().hex[:10]
            raw_proxy_str = with_sticky_session(raw_proxy_str, sticky_tag)

        session, profile, err = da_session_from_cookies(cookie_text, raw_proxy_str)
        if not session:
            parser_log(f"{prefix} ✗ {err}")
            return
        parser_log(f"{prefix} 🌐 Отпечаток: {profile['impersonate']}")
        parser_log(f"{prefix} Поисковый поток (потоков больше чем ссылок) — сам подбирает слова для поиска")

        def _rotate_ip():
            """Give up on the current exit IP and move to a fresh one — see
            PARSER_ROTATE_AFTER_FAILURES."""
            nonlocal raw_proxy_str, reserved_proxy, csrf_token
            if use_live_proxies:
                release_live_proxy(reserved_proxy)
                new_proxy = pick_live_proxy()
                if new_proxy:
                    reserved_proxy = new_proxy
                    raw_proxy_str = new_proxy
                    parser_log(f"{prefix} 🔁 Похоже, IP заблокирован — сменил живой прокси на {new_proxy}")
                else:
                    reserved_proxy = None
                    parser_log(f"{prefix} ⚠ Похоже, IP заблокирован, но свободных живых прокси больше нет")
            elif base_proxy_str.strip():
                new_tag = "ps" + uuid.uuid4().hex[:10]
                raw_proxy_str = with_sticky_session(base_proxy_str, new_tag)
                parser_log(f"{prefix} 🔁 Похоже, IP заблокирован — беру новый IP (sessid-{new_tag})")
            apply_proxy_to_session(session, raw_proxy_str)
            csrf_token = None

        csrf_token, csrf_err = da_fetch_csrf(session, parser_log, prefix)
        for _ in range(PARSER_ROTATE_AFTER_FAILURES):
            if csrf_token or stop_event.is_set():
                break
            _rotate_ip()
            csrf_token, csrf_err = da_fetch_csrf(session, parser_log, prefix)
        if not csrf_token:
            parser_log(f"{prefix} ✗ Не удалось получить csrf_token для поиска: {csrf_err}")
            return

        consecutive_failures = 0  # rounds with pages_fetched==0 (either query type)
        want_artist_search = False  # alternates every cycle
        while not stop_event.is_set():
            # _rotate_ip() clears csrf_token whenever it swaps the exit IP —
            # confirmed live as the actual cause of a thread burning through
            # dozens of queries and IP rotations with 100% failure and never
            # recovering: nothing here ever re-fetched it, so every search
            # after the first rotation silently ran with csrf_token=None
            # forever, guaranteeing pages_fetched==0 forever, which just
            # triggered another pointless rotation every couple of rounds.
            if not csrf_token:
                csrf_token, csrf_err = da_fetch_csrf(session, parser_log, prefix)
                if not csrf_token:
                    parser_log(f"{prefix} ✗ Не удалось обновить csrf_token для поиска: {csrf_err}")
                    for _ in range(15):
                        if stop_event.is_set():
                            break
                        time.sleep(1)
                    continue

            deviation_query = artist_query = None
            if search_illustrations_only:
                deviation_query = claim_next_search_query()
            else:
                want_artist_search = not want_artist_search
                if want_artist_search:
                    artist_query = claim_next_artist_search_query()
                    if not artist_query:
                        deviation_query = claim_next_search_query()
                else:
                    deviation_query = claim_next_search_query()
                    if not deviation_query:
                        artist_query = claim_next_artist_search_query()

            if artist_query:
                parser_log(f"{prefix} 🎨🔎 Поиск артистов: «{artist_query}» (order={ARTIST_SEARCH_ORDER})")
                (next_cursor, reached_end, pages_fetched, artists_seen,
                 checked_total, with_watchers_total, written_total) = run_artist_search_pass(
                    session, csrf_token, prefix, artist_query, seen_ids, seen_lock,
                    ignore_blacklist, stop_event)
                release_artist_search_query(artist_query, written_total, reached_end,
                                             fetch_failed=(pages_fetched == 0))
                parser_log(f"{prefix} «{artist_query}» (артисты) готово: {pages_fetched} стр., "
                           f"артистов: {artists_seen}, проверено: {checked_total}, "
                           f"с watchers: {with_watchers_total}, записано новых: {written_total}"
                           + (" — сбой запроса (IP?), без кулдауна, попробую другой запрос" if pages_fetched == 0
                              else (" — дошли до конца, кулдаун 24ч" if reached_end
                                    else (" — прервано, мало нового, кулдаун 12ч"
                                          if written_total < ARTIST_SEARCH_LOW_YIELD_THRESHOLD
                                          else " — прервано (стоп), без кулдауна"))))
                if pages_fetched == 0 and not stop_event.is_set():
                    consecutive_failures += 1
                    if consecutive_failures >= PARSER_ROTATE_AFTER_FAILURES:
                        _rotate_ip()
                        consecutive_failures = 0
                else:
                    consecutive_failures = 0
                continue

            if deviation_query:
                written_total = 0

                def _on_page(page_num, page_matches, _query=deviation_query):
                    nonlocal written_total
                    written, dup, bl = record_matches(prefix, page_matches, seen_ids, seen_lock, ignore_blacklist)
                    written_total += written
                    parser_log(
                        f"{prefix} поиск «{_query}» стр. {page_num}: найдено {len(page_matches)}, "
                        f"записано {written}"
                        + (f", дубликаты: {dup}" if dup else "")
                        + (f", в блеклисте: {bl}" if bl else ""))

                parser_log(f"{prefix} 🔎 Поиск: «{deviation_query}»")
                reached_end, pages_fetched, est_total, total_matches = fetch_search_scroll(
                    session, csrf_token, deviation_query, stop_event=stop_event, on_page=_on_page)
                release_search_query(deviation_query, written_total, reached_end, est_total,
                                      fetch_failed=(pages_fetched == 0))
                parser_log(f"{prefix} «{deviation_query}» готово: {pages_fetched} стр."
                           + (f", всего по оценке DA: {est_total}" if est_total else "")
                           + f", записано новых: {written_total}"
                           + (" — сбой запроса (IP?), без кулдауна, попробую другой запрос" if pages_fetched == 0
                              else (" — дошли до конца, кулдаун 24ч" if reached_end
                                    else (" — прервано, мало нового, кулдаун 12ч" if written_total < SEARCH_LOW_YIELD_THRESHOLD
                                          else " — прервано (стоп), без кулдауна"))))
                if pages_fetched == 0 and not stop_event.is_set():
                    consecutive_failures += 1
                    if consecutive_failures >= PARSER_ROTATE_AFTER_FAILURES:
                        _rotate_ip()
                        consecutive_failures = 0
                else:
                    consecutive_failures = 0
                continue

            # The relevant pool(s) are fully on cooldown right now.
            if search_illustrations_only:
                wait_s = seconds_until_next_available_query()
                pools_label = "иллюстрации"
            else:
                wait_s = min(seconds_until_next_available_query(), seconds_until_next_available_artist_query())
                pools_label = "иллюстрации и артисты"
            parser_log(f"{prefix} ⏳ Все поисковые запросы ({pools_label}) сейчас на кулдауне — "
                       f"жду {int(wait_s)} сек...")
            for _ in range(int(wait_s)):
                if stop_event.is_set():
                    break
                time.sleep(1)
    except Exception as e:
        parser_log(f"{prefix} 🔴 Поток упал с необработанной ошибкой: {e}")
    finally:
        release_live_proxy(reserved_proxy)


def parser_feed_thread(idx, feed_urls, cookie_text, proxy_text, use_live_proxies,
                       stop_event, seen_ids, seen_lock, scroll_max_pages=0,
                       ignore_blacklist=False):
    """One parser thread, responsible for its own slice of feed URLs — own
    session, own (optionally reserved) proxy. Multiple threads share
    `seen_ids`/`seen_lock` and the notebook/blacklist files so no duplicate
    or blacklisted post gets written twice regardless of which thread found it.
    """
    prefix = f"[{idx + 1}]"
    reserved_proxy = None
    try:
        if use_live_proxies:
            reserved_proxy = pick_live_proxy()
            if not reserved_proxy:
                parser_log(f"{prefix} ⚠ Нет свободных живых прокси (все заняты другими потоками, "
                           f"или живых прокси ещё нет — проверь их на вкладке «Прокси»)")
                return
            base_proxy_str = reserved_proxy
            raw_proxy_str = reserved_proxy
            parser_log(f"{prefix} ✓ Занял живой прокси: {reserved_proxy}")
        else:
            base_proxy_str = proxy_text
            raw_proxy_str = proxy_text
            if proxy_text.strip() and not parse_proxy(proxy_text):
                parser_log(f"{prefix} ⚠ Не удалось разобрать прокси: {proxy_text.strip()[:80]}")

        # A rotating proxy hands a different exit IP to every new connection
        # (see with_sticky_session) — left unpinned, every single request
        # this long-lived thread makes could land on a different, possibly
        # broken, exit node (confirmed live: every thread hitting the same
        # rotating pool unpinned failed with an identical TLS/cert error).
        # Pin one IP for the thread's whole lifetime, same as registration
        # already does. No-op for proxies without a login (live-pool ones).
        if raw_proxy_str.strip():
            sticky_tag = "pf" + uuid.uuid4().hex[:10]
            raw_proxy_str = with_sticky_session(raw_proxy_str, sticky_tag)

        session, profile, err = da_session_from_cookies(cookie_text, raw_proxy_str)
        if not session:
            parser_log(f"{prefix} ✗ {err}")
            return

        parser_log(f"{prefix} 🌐 Отпечаток: {profile['impersonate']}")
        parser_log(f"{prefix} Обслуживает {len(feed_urls)} ссылок"
                   + (f", через прокси {raw_proxy_str.strip()}" if raw_proxy_str.strip() else ", без прокси"))

        csrf_token = None  # lazily fetched, only if a home-feed URL needs the scroll API
        scroll_cursors = {}  # feed_url -> cursor to resume from on the next poll
        zero_streak = {}  # feed_url -> consecutive empty-poll count (non-home-feed only)
        next_check = {}  # feed_url -> earliest time.time() this URL is worth re-fetching
        consecutive_failures = 0  # rounds with pages_fetched==0 / a blocked response, across any URL

        def _rotate_ip():
            """Give up on the current exit IP and move to a fresh one — see
            PARSER_ROTATE_AFTER_FAILURES."""
            nonlocal raw_proxy_str, reserved_proxy, csrf_token
            if use_live_proxies:
                release_live_proxy(reserved_proxy)
                new_proxy = pick_live_proxy()
                if new_proxy:
                    reserved_proxy = new_proxy
                    raw_proxy_str = new_proxy
                    parser_log(f"{prefix} 🔁 Похоже, IP заблокирован — сменил живой прокси на {new_proxy}")
                else:
                    reserved_proxy = None
                    parser_log(f"{prefix} ⚠ Похоже, IP заблокирован, но свободных живых прокси больше нет")
            elif base_proxy_str.strip():
                new_tag = "pf" + uuid.uuid4().hex[:10]
                raw_proxy_str = with_sticky_session(base_proxy_str, new_tag)
                parser_log(f"{prefix} 🔁 Похоже, IP заблокирован — беру новый IP (sessid-{new_tag})")
            apply_proxy_to_session(session, raw_proxy_str)
            csrf_token = None

        while not stop_event.is_set():
            for feed_url in feed_urls:
                if stop_event.is_set():
                    break

                if not is_home_feed_url(feed_url) and time.time() < next_check.get(feed_url, 0):
                    continue

                if is_home_feed_url(feed_url):
                    if not csrf_token:
                        csrf_token, csrf_err = da_fetch_csrf(session, parser_log, prefix)
                        if not csrf_token:
                            parser_log(f"{prefix} ✗ Не удалось получить csrf_token для скролла: "
                                       f"{csrf_err}")
                            continue
                    start_cursor = scroll_cursors.get(feed_url)

                    def _on_page(page_num, page_matches, _feed_url=feed_url):
                        written, dup, bl = record_matches(prefix, page_matches, seen_ids, seen_lock, ignore_blacklist)
                        parser_log(
                            f"{prefix} {_feed_url} стр. {page_num}: найдено {len(page_matches)}, "
                            f"записано {written}"
                            + (f", дубликаты: {dup}" if dup else "")
                            + (f", в блеклисте: {bl}" if bl else ""))

                    next_cursor, reached_end, pages_fetched = fetch_home_feed_scroll(
                        session, csrf_token, prefix, start_cursor,
                        max_pages=scroll_max_pages, stop_event=stop_event, on_page=_on_page)
                    scroll_cursors[feed_url] = next_cursor
                    pages_label = "нонстоп" if not scroll_max_pages else f"до {scroll_max_pages} стр."
                    parser_log(f"{prefix} {feed_url} (скролл{' с продолжения' if start_cursor else ''}"
                               f", {pages_label}, прошли {pages_fetched} стр."
                               f"{' — дошли до конца ленты, дальше по кругу' if reached_end else ''})")
                    if pages_fetched == 0 and not stop_event.is_set():
                        # Page 1 itself failed (confirmed live: DA can start
                        # rejecting this thread's csrf_token as "invalid" —
                        # without this, the exact same dead token gets reused
                        # forever, every single poll, and the feed thread
                        # never recovers on its own for the rest of the run.
                        csrf_token = None
                        consecutive_failures += 1
                        parser_log(f"{prefix} ⚠ Похоже, csrf_token протух — обновлю перед следующей попыткой")
                        if consecutive_failures >= PARSER_ROTATE_AFTER_FAILURES:
                            _rotate_ip()
                            consecutive_failures = 0
                    elif pages_fetched > 0:
                        consecutive_failures = 0
                    continue
                elif is_artist_search_url(feed_url):
                    if not csrf_token:
                        csrf_token, csrf_err = da_fetch_csrf(session, parser_log, prefix)
                        if not csrf_token:
                            parser_log(f"{prefix} ✗ Не удалось получить csrf_token для поиска артистов: "
                                       f"{csrf_err}")
                            continue
                    query, order = parse_artist_search_url(feed_url)
                    start_cursor = scroll_cursors.get(feed_url)

                    (next_cursor, reached_end, pages_fetched, artists_seen,
                     checked_total, with_watchers_total, written_total) = run_artist_search_pass(
                        session, csrf_token, prefix, query, seen_ids, seen_lock,
                        ignore_blacklist, stop_event, start_cursor, order)
                    scroll_cursors[feed_url] = next_cursor
                    parser_log(f"{prefix} {feed_url} (поиск артистов{' с продолжения' if start_cursor else ''}"
                               f", прошли {pages_fetched} стр., артистов: {artists_seen}"
                               f", проверено: {checked_total}, с watchers: {with_watchers_total}"
                               f", записано новых: {written_total}"
                               f"{' — дошли до конца, дальше по кругу' if reached_end else ''})")
                    if pages_fetched == 0 and not stop_event.is_set():
                        csrf_token = None
                        consecutive_failures += 1
                        parser_log(f"{prefix} ⚠ Похоже, csrf_token протух — обновлю перед следующей попыткой")
                        if consecutive_failures >= PARSER_ROTATE_AFTER_FAILURES:
                            _rotate_ip()
                            consecutive_failures = 0
                    elif pages_fetched > 0:
                        consecutive_failures = 0
                    continue
                else:
                    try:
                        resp = session.get(feed_url, headers=nav_h(session), timeout=REQUEST_TIMEOUT)
                    except Exception as e:
                        parser_log(f"{prefix} ✗ Не удалось загрузить {feed_url}: {str(e)[:150]}")
                        consecutive_failures += 1
                        if consecutive_failures >= PARSER_ROTATE_AFTER_FAILURES:
                            _rotate_ip()
                            consecutive_failures = 0
                        continue

                    title_m = re.search(r"<title[^>]*>(.*?)</title>", resp.text or "", re.S | re.I)
                    title = (title_m.group(1).strip() if title_m else "")[:100]
                    matches = DEVIATION_LINK_RE.findall(resp.text or "")
                    parser_log(f"{prefix} {feed_url}: код {resp.status_code}, title={title!r}, "
                               f"ссылок на посты найдено: {len(matches)}")
                    if resp.status_code != 200 or (title and (
                            "error" in title.lower() or "blocked" in title.lower()
                            or "could not be satisfied" in title.lower())):
                        h = resp.headers or {}
                        hdr_dump = ", ".join(
                            f"{k}={h[k]}" for k in
                            ("server", "x-cache", "via", "x-amz-cf-pop", "x-amz-cf-id")
                            if k in h)
                        parser_log(f"{prefix} ✗ Ответ не похож на реальный контент. "
                                   f"Заголовки: {hdr_dump or '(нет из перечисленных)'}")
                        consecutive_failures += 1
                        if consecutive_failures >= PARSER_ROTATE_AFTER_FAILURES:
                            _rotate_ip()
                            consecutive_failures = 0
                    else:
                        consecutive_failures = 0

                new_urls = []
                duplicates = 0
                blacklisted_count = 0
                for username, slug, dev_id in matches:
                    with seen_lock:
                        if dev_id in seen_ids:
                            duplicates += 1
                            continue
                        seen_ids.add(dev_id)
                    if not ignore_blacklist and is_blacklisted(username):
                        blacklisted_count += 1
                        continue
                    new_urls.append(f"https://www.deviantart.com/{username}/art/{slug}-{dev_id}")

                if new_urls:
                    append_notebook(new_urls)
                    with parser_lock:
                        parser_state["found"] += len(new_urls)

                parser_log(
                    f"{prefix} Найдено: {len(matches)}, записано в блокнот: {len(new_urls)}"
                    + (f", дубликаты (уже видели/уже в блокноте): {duplicates}" if duplicates else "")
                    + (f", в блеклисте: {blacklisted_count}" if blacklisted_count else ""))

                if new_urls:
                    zero_streak[feed_url] = 0
                    next_check.pop(feed_url, None)
                else:
                    zero_streak[feed_url] = zero_streak.get(feed_url, 0) + 1
                    streak = zero_streak[feed_url]
                    if streak >= FEED_ZERO_YIELD_BACKOFF_AFTER:
                        backoff = min(
                            FEED_POLL_INTERVAL * (2 ** (streak - FEED_ZERO_YIELD_BACKOFF_AFTER + 1)),
                            FEED_MAX_BACKOFF_SECONDS)
                        next_check[feed_url] = time.time() + backoff
                        parser_log(f"{prefix} {feed_url}: {streak} опрос(ов) подряд без нового — "
                                   f"следующая проверка через {int(backoff)} сек")

            for _ in range(FEED_POLL_INTERVAL):
                if stop_event.is_set():
                    break
                time.sleep(1)
    except Exception as e:
        # Without this, an unexpected exception here (like the stale-variable
        # NameError this used to hit right after a successful cookie parse)
        # kills the thread silently — the GUI runs headless via pythonw, so
        # the traceback goes nowhere and the log just shows "Остановлено"
        # with zero clue why.
        parser_log(f"{prefix} 🔴 Поток упал с необработанной ошибкой: {e}")
    finally:
        release_live_proxy(reserved_proxy)


def parser_worker(feed_url_text, cookie_text, thread_count, proxy_text, use_live_proxies=False,
                  scroll_max_pages=0, ignore_blacklist=False, search_illustrations_only=False):
    """Pure HTTP feed discovery — no browser at all. Tab 1: only ever writes
    discovered post URLs into the notebook file; never posts anything.

    Fetches each feed URL with the account's cookies and regex-extracts
    every deviation link straight out of the returned HTML (DeviantArt
    server-side renders the visible grid for SEO, so this is the same
    content a browser would show without needing to run any JS or scroll
    anything). One HTTP fetch only ever returns the same fixed first batch
    the server renders (confirmed live: ~24-30 unique posts from the plain
    homepage, repeatedly, no matter how many times it's re-fetched) —
    there's no known HTTP-only pagination/infinite-scroll endpoint for this,
    so more volume means pasting more feed URLs (different category tabs,
    tags, search queries), not scrolling one page further.

    Always spawns exactly `thread_count` threads. If there are more URLs than
    threads, each thread gets a round-robin share of several URLs (many URLs
    per thread). If there are more threads than URLs, one thread covers each
    URL and every thread beyond that becomes a dedicated search-discovery
    thread instead (see parser_search_thread) — piling more threads onto an
    already-covered URL doesn't add anything (a single fetch only ever
    returns the same first batch), whereas an idle thread can independently
    search DA for fresh illustrations. Each feed thread polls its URL(s)
    every FEED_POLL_INTERVAL seconds, so a rotating feed (newest, popular)
    still surfaces fresh posts over time.
    """
    # No running-guard here — the /api/parser_start handler already claims
    # parser_state["running"] before this even gets spawned (necessary since
    # that handler's own auto-register-if-dead step can block for a couple
    # of minutes; leaving the claim until here left that whole window
    # unguarded, so an impatient second click while registration was still
    # in progress raced a second, fully independent registration+worker).
    with parser_lock:
        parser_state["stop"] = threading.Event()
        stop_event = parser_state["stop"]

    try:
        if not cookie_text.strip():
            parser_log("⚠️ Вставьте куки аккаунта")
            return
        feed_urls = [u.strip() for u in feed_url_text.splitlines() if u.strip()]
        if not feed_urls:
            parser_log("⚠️ Укажите хотя бы одну ссылку (можно несколько, по одной на строку)")
            return

        thread_count = max(1, int(thread_count or 1))
        search_thread_count = 0
        if thread_count <= len(feed_urls):
            chunks = distribute_urls(feed_urls, thread_count)
        else:
            # one thread per URL; every thread beyond that searches instead
            # of uselessly re-hitting an already-covered URL.
            chunks = [[u] for u in feed_urls]
            search_thread_count = thread_count - len(feed_urls)

        seen_ids = {item["deviation_id"] for item in read_notebook()}
        seen_lock = threading.Lock()
        parser_log(f"Старт парсинга: {len(feed_urls)} ссылок, {len(chunks)} поток(ов) на ссылки"
                   + (f", {search_thread_count} поисковых поток(ов) (потоков больше чем ссылок)"
                      if search_thread_count else ""))

        threads = []
        for i, chunk in enumerate(chunks):
            if threads:
                stagger_before_next_thread(stop_event)
            t = threading.Thread(target=parser_feed_thread,
                                 args=(i, chunk, cookie_text, proxy_text, use_live_proxies,
                                       stop_event, seen_ids, seen_lock, scroll_max_pages,
                                       ignore_blacklist),
                                 daemon=True)
            t.start()
            threads.append(t)
        for j in range(search_thread_count):
            if threads:
                stagger_before_next_thread(stop_event)
            t = threading.Thread(target=parser_search_thread,
                                 args=(len(chunks) + j, cookie_text, proxy_text, use_live_proxies,
                                       stop_event, seen_ids, seen_lock, ignore_blacklist,
                                       search_illustrations_only),
                                 daemon=True)
            t.start()
            threads.append(t)
        for t in threads:
            t.join()

        parser_log("Остановлено")
    finally:
        with parser_lock:
            parser_state["running"] = False


VERIFY_MISS_ROTATE_THRESHOLD = 2  # consecutive genuinely-missing comments on one account before re-registering


def _reregister_account_for_thread(prefix, raw_proxy_str, username_template, avatar_bytes,
                                   proxy_for_comments, mail_provider, mail_domain,
                                   attach_image, image_bytes, image_filename,
                                   stop_event=None):
    """Register a brand-new account for a sender thread (fresh sticky IP,
    never the previous account's) and, if this thread attaches images,
    re-upload to the new account's sta.sh — per-account, so the old upload
    is invalid here. Shared by both rotation triggers: a hard API error
    (spam/unauthorized/etc.) and a comment repeatedly failing verification.

    Returns (session, csrf_token, image_deviation, err) — image_deviation is
    None when attach_image is False; err is "" on success.
    """
    new_session, csrf_token, err, confirmed_event, img_deviation = da_fresh_account_session(
        raw_proxy_str, username_template, avatar_bytes, prefix, proxy_for_comments,
        mail_provider=mail_provider, mail_domain=mail_domain, stop_event=stop_event,
        attach_image=attach_image, image_bytes=image_bytes, image_filename=image_filename)
    if not new_session:
        return None, "", None, err

    if not (attach_image and image_bytes) and confirmed_event and not confirmed_event.is_set():
        sender_log(f"{prefix} ⏳ Жду подтверждения email (макс 60 сек)...")
        if confirmed_event.wait(timeout=60):
            sender_log(f"{prefix} ✅ Email подтверждён, продолжаю")
        else:
            sender_log(f"{prefix} ⚠ Таймаут ожидания подтверждения email — продолжаю без гарантии")

    if attach_image and image_bytes and not img_deviation:
        sender_log(f"{prefix} ❌ Не удалось подготовить изображение для нового аккаунта")
        return None, "", None, "не удалось подготовить изображение"

    return new_session, csrf_token, img_deviation, ""


def comment_worker(idx, cookie_text, comment_text, ignore_blacklist,
                   stop_event, reserved, reserved_lock, manual_csrf_token="", proxy_text="",
                   dry_run=False, use_live_proxies=False, invis_char="", invis_count=0, shortener="",
                   verify_comment=True, attach_image=False, image_bytes=None, image_filename="",
                   photo_link=False, auto_register=False, username_template="", avatar_bytes=None,
                   proxy_for_comments=True, mail_provider=None, comment_delay=0, mail_domain=None,
                   uniqueify_text=False, send_random_after_spam=False, delete_special_comments=False,
                   reupload_image=False, single_comment=False, fallback_letters=False):
    """Tab 2 worker: pulls from the notebook file (never talks to the parser
    directly), reserving its author in-memory for the duration of the
    attempt so no other thread can double-claim the same author's post at
    the same instant — see take_next_unreserved. When `use_live_proxies` is
    set, this thread claims one exclusive live proxy for its whole lifetime
    (released when it exits) instead of the shared `proxy_text` — each of
    the N sender threads ends up on its own IP, never sharing one.
    """
    prefix = f"[{idx + 1}]"
    reserved_proxy = None
    # Set up front so the finally-block save-to-pool logic below can safely
    # check them even if something fails before they'd normally get assigned.
    session = None
    is_fresh_account = False
    used_pool_account = False
    account_healthy = False
    consecutive_verify_misses = 0  # posts in a row genuinely confirmed missing on THIS account
    try:
        if use_live_proxies:
            reserved_proxy = pick_live_proxy()
            if not reserved_proxy:
                sender_log(f"{prefix} ⚠ Нет свободных живых прокси (все заняты другими потоками, "
                           f"или живых прокси ещё нет — проверь их на вкладке «Прокси»)")
                return
            raw_proxy_str = reserved_proxy
            sender_log(f"{prefix} ✓ Занял живой прокси: {reserved_proxy}")
        else:
            raw_proxy_str = proxy_text
            if proxy_text.strip() and not parse_proxy(proxy_text):
                sender_log(f"{prefix} ⚠ Не удалось разобрать прокси: {proxy_text.strip()[:80]}")

        csrf_token = ""
        is_fresh_account = auto_register and not cookie_text.strip()
        if is_fresh_account:
            # Prefer a saved account that was still working when the sender
            # was last stopped over registering a brand new one — see
            # save_account_to_pool/pop_account_from_pool. The "Сброс" button
            # empties the pool, which naturally forces fresh registration
            # again next time since there's nothing left to pop.
            session, csrf_token, pooled_username = da_session_from_pool(raw_proxy_str, proxy_for_comments, prefix)
            if session:
                used_pool_account = True
                # Deliberately NOT marking account_healthy here — a csrf
                # fetch succeeding doesn't mean the account actually works
                # (confirmed live: pooled accounts that fail to even resolve
                # their own username, then get stopped before sending
                # anything, used to get saved right back to the pool in this
                # same broken state — poisoning it with dead accounts that
                # just cycle through every run). Only an actual successful
                # comment send (further down) earns account_healthy = True.
                sender_log(f"{prefix} ♻️ Использую сохранённый рабочий аккаунт: {pooled_username or '(?)'}")
            if not raw_proxy_str.strip() and not session:
                # Without a proxy every thread hits DeviantArt from the same
                # IP — firing the homepage request at the exact same instant
                # trips CloudFront's burst-block ("could not be satisfied").
                # Stagger thread starts so they don't collide.
                stagger = idx * random.uniform(1.5, 3.0)
                if stagger:
                    time.sleep(stagger)
            # da_fresh_account_session pins its own sticky IP (and rotates to
            # a new one if CloudFront blocks it) — just hand it the raw pool.
            # da_fresh_account_session already retries the temp-mail step and
            # rotates IPs internally — but if EVERYTHING it tries fails (e.g.
            # a sustained provider outage), don't let that kill this thread
            # for the rest of the run. Keep retrying here until it works or
            # the user hits Stop, instead of returning and ending the thread.
            confirmed_event = None
            _init_img_dev = None
            while not session and not stop_event.is_set():
                sender_log(f"{prefix} 🚀 Авто-регистрация: создаю новый аккаунт с нуля...")
                session, csrf_token, err, confirmed_event, _init_img_dev = da_fresh_account_session(raw_proxy_str, username_template, avatar_bytes, prefix, proxy_for_comments, mail_provider=mail_provider, mail_domain=mail_domain, stop_event=stop_event, attach_image=attach_image, image_bytes=image_bytes, image_filename=image_filename)
                if session:
                    break
                sender_log(f"{prefix} ✗ {err} — повтор через 15 сек...")
                for _ in range(15):
                    if stop_event.is_set():
                        break
                    time.sleep(1)
            if not session:
                return
            if dry_run:
                sender_log(f"{prefix} 🧪 Тестовый режим — комментарии реально отправляться не будут")
        else:
            confirmed_event = None
            # Same reasoning as the parser threads: a rotating proxy hands a
            # different exit IP to every new connection, so an unpinned
            # session risks a different (possibly broken) IP on every single
            # request. Pin one for this thread's whole lifetime.
            pinned_proxy_str = raw_proxy_str
            if raw_proxy_str.strip():
                sticky_tag = "dm" + uuid.uuid4().hex[:10]
                pinned_proxy_str = with_sticky_session(raw_proxy_str, sticky_tag)
            session, profile, err = da_session_from_cookies(cookie_text, pinned_proxy_str)
            if not session:
                sender_log(f"{prefix} ✗ {err}")
                return
            sender_log(f"{prefix} 🌐 Отпечаток: {profile['impersonate']}")
            cookie_names = sorted({name for name, _ in parse_cookie_pairs(cookie_text)})
            sender_log(f"{prefix} Распознано кук: {len(cookie_names)} — {', '.join(cookie_names)}")

            if dry_run:
                sender_log(f"{prefix} 🧪 Тестовый режим — комментарии реально отправляться не будут, "
                           f"csrf_token не нужен")
            elif manual_csrf_token.strip():
                csrf_token = manual_csrf_token.strip()
                sender_log(f"{prefix} ✓ Использую csrf_token, вставленный вручную")
            else:
                csrf_token, err = da_fetch_csrf(session, sender_log, prefix)
                if not csrf_token:
                    sender_log(f"{prefix} ✗ Не удалось получить csrf_token: {err}")
                    return
                sender_log(f"{prefix} ✓ csrf_token получен, начинаю обработку блокнота")

        if not (is_fresh_account and not used_pool_account and attach_image and image_bytes):
            if confirmed_event and not confirmed_event.is_set():
                sender_log(f"{prefix} ⏳ Жду подтверждения email (макс 60 сек)...")
                if confirmed_event.wait(timeout=60):
                    sender_log(f"{prefix} ✅ Email подтверждён, продолжаю")
                else:
                    sender_log(f"{prefix} ⚠ Таймаут ожидания подтверждения email — продолжаю без гарантии")

        image_deviation = None
        if is_fresh_account and not used_pool_account:
            image_deviation = _init_img_dev
        if attach_image and image_bytes and not dry_run and image_deviation is None:
            _stash_attempts = 0
            _STASH_MAX_RETRIES = 3
            while image_deviation is None:
                if stop_event and stop_event.is_set():
                    return
                _stash_attempts += 1
                sender_log(f"{prefix} ⏳ Загрузка изображения в sta.sh (попытка {_stash_attempts})...")
                _reg_proxy = getattr(session, '_reg_proxy', None)
                _need_stash_proxy = not proxy_for_comments and bool(_reg_proxy or (raw_proxy_str and raw_proxy_str.strip()))
                if _need_stash_proxy:
                    _sproxy = _reg_proxy or with_sticky_session(raw_proxy_str, "st" + uuid.uuid4().hex[:10], lifetime_minutes=5)
                    apply_proxy_to_session(session, _sproxy)
                deviation, was_uploaded, err = da_get_or_upload_stash_deviation(
                    session, csrf_token, image_bytes, image_filename or "image.png", cookie_text,
                    new_account=(is_fresh_account and not used_pool_account))
                if _need_stash_proxy:
                    clear_session_proxy(session)
                if deviation:
                    image_deviation = deviation
                    if was_uploaded:
                        sender_log(f"{prefix} 🖼 Изображение загружено в sta.sh и будет прикрепляться к комментариям")
                    else:
                        sender_log(f"{prefix} 🖼 В sta.sh уже есть изображение — использую его для прикрепления")
                else:
                    sender_log(f"{prefix} 🔴 Не удалось подготовить изображение (попытка {_stash_attempts}): {err}")
                    if _stash_attempts >= _STASH_MAX_RETRIES:
                        if auto_register and username_template:
                            sender_log(f"{prefix} 🔄 Изображение не загружается — регистрирую новый аккаунт...")
                            new_s, new_c, new_id, reg_err = _reregister_account_for_thread(
                                prefix, raw_proxy_str, username_template, avatar_bytes, proxy_for_comments,
                                mail_provider, mail_domain, attach_image, image_bytes, image_filename,
                                stop_event=stop_event)
                            if new_s:
                                session = new_s
                                csrf_token = new_c
                                image_deviation = new_id
                                account_healthy = False
                                used_pool_account = False
                            else:
                                sender_log(f"{prefix} ❌ {reg_err}")
                                return
                        else:
                            sender_log(f"{prefix} ⛔ Изображение не загружается — поток остановлен")
                            return
                    else:
                        time.sleep(random.uniform(3, 6))

        # "Link in photo" mode needs a prepared photo to attach the link to.
        if photo_link and not dry_run and not image_deviation:
            sender_log(f"{prefix} 🔴 ОШИБКА: «Ссылка в фото» включена, но изображение не подготовлено "
                       f"(нужна включённая галочка «Прикреплять изображение» и выбранный файл) — поток остановлен")
            return

        empty_polls = 0
        while not stop_event.is_set():
            item = take_next_unreserved(ignore_blacklist, reserved, reserved_lock)
            if not item:
                # An empty/fully-blacklisted notebook looks identical to a
                # hung thread from the log alone — nothing gets printed while
                # this polls every second. Say so once, then remind every
                # ~30s while it's still empty, instead of going silent.
                empty_polls += 1
                if empty_polls == 1 or empty_polls % 30 == 0:
                    sender_log(f"{prefix} ⏳ Блокнот пуст (или все посты в блеклисте) — жду, пока парсер найдёт новые...")
                time.sleep(1)
                continue
            empty_polls = 0

            username = item["username"]
            dev_id = item["deviation_id"]
            url = item["url"]
            key = username.lower()

            if reupload_image and attach_image and image_bytes and image_deviation and not dry_run:
                _reg_proxy = getattr(session, '_reg_proxy', None)
                _need_reup_proxy = not proxy_for_comments and bool(_reg_proxy or (raw_proxy_str and raw_proxy_str.strip()))
                if _need_reup_proxy:
                    _reup_px = _reg_proxy or with_sticky_session(raw_proxy_str, "ru" + uuid.uuid4().hex[:10], lifetime_minutes=5)
                    apply_proxy_to_session(session, _reup_px)
                new_dev, rerr = da_force_upload_stash_deviation(session, csrf_token, image_bytes)
                if _need_reup_proxy:
                    clear_session_proxy(session)
                if new_dev:
                    image_deviation = new_dev
                    sender_log(f"{prefix} 🖼 Перезалито новое изображение в sta.sh")
                else:
                    sender_log(f"{prefix} ⚠ Не удалось перезалить изображение, использую предыдущее")

            try:
                if photo_link:
                    # Link-in-photo: no comment text at all. Take the URL from
                    # the comment-text field, shorten it, and set it as the
                    # photo's clickable link.
                    target = extract_first_target_url(comment_text)
                    if not target:
                        sender_log(f"{prefix} ❌ Не нашёл ссылку в поле текста для вставки в фото "
                                   f"(нужен формат {{текст;https://...}} или просто URL)")
                        continue
                    if shortener:
                        photo_url = shorten_url(session, target, shortener)
                        if not photo_url:
                            sender_log(f"{prefix} 🔴 ОШИБКА: не удалось сократить ссылку {target[:70]} — пропуск")
                            continue
                        sender_log(f"{prefix} ✅ {target[:70]} → {photo_url}")
                    else:
                        photo_url = target
                        sender_log(f"{prefix} ✅ Ссылка в фото (без сокращения): {photo_url[:70]}")
                    if dry_run:
                        sender_log(f"{prefix} 🧪 [тест] Прикрепил бы фото со ссылкой {photo_url}: {url} (автор {username})")
                        continue
                    sender_log(f"{prefix} → Отправляю на {username} ({url}) [🖼 {photo_url}]")
                    ok, cerr, posted_comment_id = da_post_comment(session, csrf_token, int(dev_id), "", url,
                                               image_deviation, image_link=photo_url, empty_text=True)
                    verify_needle = photo_url
                else:
                    # Step 1: Shorten links BEFORE adding invisible chars (so regex can find placeholders)
                    text_to_send = comment_text
                    if shortener:
                        text_to_send, shorten_log = replace_links_with_shortened(text_to_send, session, shortener)
                        if shorten_log:
                            for line in shorten_log.split("\n"):
                                sender_log(f"{prefix} {line}")

                    # Step 2: Add invisible chars AFTER link replacement
                    text_to_send = insert_invisible_chars(text_to_send, invis_char, invis_count)
                    # Step 3: Homoglyph uniquification, fresh randomization on every
                    # single send (including the first). DA's text-hash spam filter
                    # locks onto the exact codepoint sequence of a flagged comment,
                    # so keeping every send byte-unique is what slips past it.
                    if uniqueify_text:
                        text_to_send = homoglyph_uniqueify(text_to_send)
                    if dry_run:
                        sender_log(f"{prefix} 🧪 [тест] Нашёл бы и отправил комментарий: {url} (автор {username})")
                        continue
                    _is_image_only = attach_image and image_deviation and not text_to_send.strip()
                    if _is_image_only:
                        sender_log(f"{prefix} → Отправляю на {username} ({url}) [🖼 только изображение]")
                        ok, cerr, posted_comment_id = da_post_comment(session, csrf_token, int(dev_id), "", url, image_deviation, empty_text=True)
                        verify_needle = ""
                    else:
                        text_preview = text_to_send[:60].replace("\n", " ")
                        sender_log(f"{prefix} → Отправляю на {username} ({url}) [текст: {text_preview}...]")
                        ok, cerr, posted_comment_id = da_post_comment(session, csrf_token, int(dev_id), text_to_send, url, image_deviation)
                        verify_needle = text_to_send[:80]

                if ok:
                    # A successful post proves this account (fresh, pooled, or
                    # rotated-to) is currently alive — worth saving to the pool
                    # if the sender stops while it's still in this state.
                    account_healthy = True
                    sender_log(f"{prefix} ✓ Комментарий отправлен: {url} (автор {username})")
                    if photo_link:
                        sender_log(f"{prefix} 🖼 Фото со ссылкой {verify_needle}")
                    else:
                        sender_log(f"{prefix} 📝 Отправленный текст: {verify_needle[:120]}...")

                    if delete_special_comments and posted_comment_id and not photo_link:
                        if _has_special_chars(text_to_send):
                            sender_log(f"{prefix} 🗑 Комментарий содержит спецсимволы, удаляю...")
                            dok, derr = da_delete_comment(session, csrf_token, posted_comment_id, int(dev_id), url)
                            if dok:
                                sender_log(f"{prefix} 🗑 Комментарий удалён (спецсимволы)")
                            else:
                                sender_log(f"{prefix} ⚠ Не удалось удалить комментарий: {derr[:100]}")

                    if verify_comment:
                        verified, verify_msg = verify_comment_posted(
                            int(dev_id), posted_comment_id, raw_proxy_str, src_session=session, csrf_token=csrf_token)
                        if verified:
                            sender_log(f"{prefix} ✅ {verify_msg}")
                            append_blacklist(username, url)
                            with sender_lock:
                                sender_state["sent"] += 1
                            consecutive_verify_misses = 0
                        elif verified is False:
                            # Page loaded fine, comment genuinely isn't there —
                            # real signal (unlike a load failure below), so it
                            # counts toward the miss streak.
                            consecutive_verify_misses += 1
                            sender_log(f"{prefix} 🔴 ОШИБКА: {verify_msg} (подряд не найдено: {consecutive_verify_misses})")
                            sender_log(f"{prefix} ⚠ Комментарий не добавлен в счётчик и блеклист")
                            if (auto_register and username_template
                                    and consecutive_verify_misses >= VERIFY_MISS_ROTATE_THRESHOLD):
                                sender_log(f"{prefix} 🚨 {consecutive_verify_misses} коммента подряд не появились "
                                           f"на странице после отправки — похоже, аккаунт теневой/ограничен, "
                                           f"создаю новый...")
                                new_session, new_csrf, new_image_dev, reg_err = _reregister_account_for_thread(
                                    prefix, raw_proxy_str, username_template, avatar_bytes, proxy_for_comments,
                                    mail_provider, mail_domain, attach_image, image_bytes, image_filename,
                                    stop_event=stop_event)
                                if new_session:
                                    session = new_session
                                    csrf_token = new_csrf
                                    if attach_image and image_bytes:
                                        image_deviation = new_image_dev
                                    account_healthy = False
                                    used_pool_account = False
                                    consecutive_verify_misses = 0
                                else:
                                    sender_log(f"{prefix} ❌ {reg_err}")
                        else:
                            # verified is None — page never loaded despite
                            # rotating proxy IPs; no signal either way, so this
                            # doesn't count toward (or reset) the miss streak.
                            sender_log(f"{prefix} ⚠ {verify_msg} — проверка неубедительна, "
                                       f"не считаю ни успехом ни провалом")
                    else:
                        sender_log(f"{prefix} ✅ Проверка отключена, считаю как успех")
                        append_blacklist(username, url)
                        with sender_lock:
                            sender_state["sent"] += 1

                    if single_comment and auto_register and username_template:
                        sender_log(f"{prefix} 🔄 1 отправка — создаю новый аккаунт...")
                        new_session, new_csrf, new_image_dev, reg_err = _reregister_account_for_thread(
                            prefix, raw_proxy_str, username_template, avatar_bytes, proxy_for_comments,
                            mail_provider, mail_domain, attach_image, image_bytes, image_filename,
                            stop_event=stop_event)
                        if new_session:
                            session = new_session
                            csrf_token = new_csrf
                            if attach_image and image_bytes:
                                image_deviation = new_image_dev
                            account_healthy = False
                            used_pool_account = False
                            consecutive_verify_misses = 0
                        else:
                            sender_log(f"{prefix} ❌ {reg_err}")
                else:
                    # Always log up-front what DA said before we do anything else
                    # (probing, rotating account, refreshing csrf). Otherwise the
                    # log jumps straight from "→ Отправляю..." to whatever the
                    # recovery path prints, and it's impossible to tell whether
                    # DA rejected the text or something else went wrong.
                    if is_spam_error(cerr):
                        if fallback_letters:
                            sender_log(f"{prefix} 🚫 DA отклонил комментарий на {username} как СПАМ "
                                       f"— запускаю пробы, чтобы понять текст или весь аккаунт")
                        else:
                            sender_log(f"{prefix} 🚫 DA отклонил комментарий на {username} как СПАМ")
                    elif is_unverified_account_error(cerr):
                        sender_log(f"{prefix} 🚫 DA отклонил комментарий на {username}: "
                                   f"email аккаунта не подтверждён")
                    elif is_unauthorized_error(cerr):
                        sender_log(f"{prefix} 🚫 DA отклонил комментарий на {username}: "
                                   f"сессия разлогинена/забанена")
                    elif is_expired_session_error(cerr):
                        sender_log(f"{prefix} 🚫 DA отклонил комментарий на {username}: "
                                   f"csrf_token протух")
                    else:
                        sender_log(f"{prefix} 🚫 DA отклонил комментарий на {username}: "
                                   f"{(cerr or '')[:180]}")

                    # A stale/missing csrf_token repeats forever if left alone (same
                    # broken token gets reused on every retry) — refreshing it on the
                    # very same account is cheap, so try that before anything heavier.
                    if is_expired_session_error(cerr) and not is_spam_error(cerr):
                        sender_log(f"{prefix} ⚠ csrf_token протух, обновляю...")
                        fresh_csrf, csrf_err = da_fetch_csrf(session, sender_log, prefix)
                        if fresh_csrf:
                            csrf_token = fresh_csrf
                            sender_log(f"{prefix} 🔄 csrf_token обновлён, продолжаю")
                            continue

                    # Spam block, unverified-account rejection, a fully logged-out
                    # session, or a csrf refresh that itself failed (session is likely
                    # dead, not just the token) — none of these clear up on their own,
                    # so rotate to a new account.
                    if auto_register and username_template and (
                            is_spam_error(cerr) or is_expired_session_error(cerr)
                            or is_unverified_account_error(cerr) or is_unauthorized_error(cerr)):
                        if is_spam_error(cerr):
                            if fallback_letters:
                                spam_type = _probe_spam_type(
                                    session, csrf_token, dev_id, url,
                                    sender_log, prefix, stop_event)
                            else:
                                spam_type = "account"
                            if spam_type == "text" and fallback_letters:
                                fb_text = "".join(random.choices(string.ascii_lowercase, k=random.randint(2, 5)))
                                sender_log(f"{prefix} 🔤 Текст заспамлен — отправляю '{fb_text}' вместо текста...")
                                try:
                                    fb_ok, fb_err, fb_cid = da_post_comment(
                                        session, csrf_token, int(dev_id), fb_text, url, image_deviation)
                                    if fb_ok:
                                        account_healthy = True
                                        sender_log(f"{prefix} ✓ Буквы отправлены: {url} ('{fb_text}')")
                                        if verify_comment:
                                            v, vmsg = verify_comment_posted(
                                                int(dev_id), fb_cid, raw_proxy_str, src_session=session, csrf_token=csrf_token)
                                            if v:
                                                sender_log(f"{prefix} ✅ {vmsg}")
                                                append_blacklist(username, url)
                                                with sender_lock:
                                                    sender_state["sent"] += 1
                                            elif v is False:
                                                sender_log(f"{prefix} 🔴 {vmsg}")
                                            else:
                                                sender_log(f"{prefix} ⚠ {vmsg}")
                                        else:
                                            append_blacklist(username, url)
                                            with sender_lock:
                                                sender_state["sent"] += 1
                                        continue
                                    else:
                                        sender_log(f"{prefix} ⚠ Буквы тоже отклонены: {(fb_err or '')[:100]}")
                                except Exception as fb_e:
                                    sender_log(f"{prefix} ⚠ Ошибка при отправке букв: {str(fb_e)[:100]}")
                            if spam_type == "text":
                                sender_log(f"{prefix} ⚠ Итог: заспамлен ТЕКСТ на аккаунте "
                                           f"{username} ({url}) — создаю новый аккаунт...")
                            else:
                                sender_log(f"{prefix} 🔴 Итог: аккаунт целиком в спам-бане на "
                                           f"{username} ({url}) — создаю новый аккаунт...")
                            if send_random_after_spam:
                                rnd_text = "".join(random.choices(
                                    string.ascii_lowercase + string.digits + " ",
                                    k=random.randint(10, 40)))
                                sender_log(f"{prefix} 🎲 Отправляю рандом-текст после спама: '{rnd_text[:30]}...'")
                                try:
                                    rok, rerr, rid = da_post_comment(
                                        session, csrf_token, int(dev_id), rnd_text, url, None)
                                    if rok:
                                        sender_log(f"{prefix} 🎲 Рандом-текст отправлен")
                                        if delete_special_comments and rid:
                                            dok, derr = da_delete_comment(session, csrf_token, rid, int(dev_id), url)
                                            if dok:
                                                sender_log(f"{prefix} 🗑 Рандом-комментарий удалён")
                                            else:
                                                sender_log(f"{prefix} ⚠ Не удалось удалить рандом-комментарий: {derr[:100]}")
                                    else:
                                        sender_log(f"{prefix} 🎲 Рандом-текст тоже отклонён: {(rerr or '')[:100]}")
                                except Exception as rnd_e:
                                    sender_log(f"{prefix} ⚠ Ошибка при отправке рандом-текста: {str(rnd_e)[:100]}")
                        else:
                            reason = ("неподтверждённый email" if is_unverified_account_error(cerr)
                                      else "аккаунт разлогинен/забанен" if is_unauthorized_error(cerr)
                                      else "мёртвая сессия")
                            sender_log(f"{prefix} 🚨 {reason} на {username} ({url}) — создаю новый аккаунт...")

                        new_session, new_csrf, new_image_dev, err = _reregister_account_for_thread(
                            prefix, raw_proxy_str, username_template, avatar_bytes, proxy_for_comments,
                            mail_provider, mail_domain, attach_image, image_bytes, image_filename,
                            stop_event=stop_event)
                        if not new_session:
                            sender_log(f"{prefix} ❌ {err}")
                            continue
                        session = new_session
                        csrf_token = new_csrf
                        if attach_image and image_bytes:
                            image_deviation = new_image_dev
                        # Brand new account, unproven — don't save it to the
                        # pool if the sender gets stopped before it lands a
                        # comment, and it no longer needs the pooled-account
                        # sta.sh shortcut (used_pool_account only ever meant
                        # "the very first account this thread had").
                        account_healthy = False
                        used_pool_account = False
                        consecutive_verify_misses = 0

                        # Actually retry the same target on the new account.
                        # Confirmed live: DA silently spam-flags an account on
                        # its 2nd comment attempt, so the target the flag was
                        # detected on was lost every time before this — the
                        # loop just moved on. Now we retry it here.
                        sender_log(f"{prefix} 🔄 Повторяю отправку на {username} с новым аккаунтом...")
                        if photo_link:
                            ok, cerr, posted_comment_id = da_post_comment(
                                session, csrf_token, int(dev_id), "", url,
                                image_deviation, image_link=photo_url, empty_text=True)
                        else:
                            ok, cerr, posted_comment_id = da_post_comment(
                                session, csrf_token, int(dev_id), text_to_send, url, image_deviation)

                        if ok:
                            account_healthy = True
                            sender_log(f"{prefix} ✓ Комментарий отправлен: {url} (автор {username})")
                            if photo_link:
                                sender_log(f"{prefix} 🖼 Фото со ссылкой {verify_needle}")
                            else:
                                sender_log(f"{prefix} 📝 Отправленный текст: {verify_needle[:120]}...")
                            if delete_special_comments and posted_comment_id and not photo_link:
                                if _has_special_chars(text_to_send):
                                    sender_log(f"{prefix} 🗑 Комментарий содержит спецсимволы, удаляю...")
                                    dok, derr = da_delete_comment(session, csrf_token, posted_comment_id, int(dev_id), url)
                                    if dok:
                                        sender_log(f"{prefix} 🗑 Комментарий удалён (спецсимволы)")
                                    else:
                                        sender_log(f"{prefix} ⚠ Не удалось удалить комментарий: {derr[:100]}")
                            if verify_comment:
                                verified, verify_msg = verify_comment_posted(
                                    int(dev_id), posted_comment_id, raw_proxy_str, src_session=session, csrf_token=csrf_token)
                                if verified:
                                    sender_log(f"{prefix} ✅ {verify_msg}")
                                    append_blacklist(username, url)
                                    with sender_lock:
                                        sender_state["sent"] += 1
                                    consecutive_verify_misses = 0
                                elif verified is False:
                                    consecutive_verify_misses += 1
                                    sender_log(f"{prefix} 🔴 ОШИБКА: {verify_msg} (подряд не найдено: {consecutive_verify_misses})")
                                else:
                                    sender_log(f"{prefix} ⚠ {verify_msg} — проверка неубедительна, "
                                               f"не считаю ни успехом ни провалом")
                            else:
                                append_blacklist(username, url)
                                with sender_lock:
                                    sender_state["sent"] += 1
                        else:
                            sender_log(f"{prefix} ❌ Повтор не удался ({username}): {cerr}")
                    else:
                        sender_log(f"{prefix} ❌ {username} ({url}): {cerr}")
            finally:
                with reserved_lock:
                    reserved.discard(key)

            if comment_delay > 0:
                # Small random jitter on top of the base delay so N threads
                # started together don't stay in lockstep hitting DA at the
                # same instant every cycle.
                for _ in range(int((comment_delay + random.uniform(0, comment_delay * 0.3)) * 10)):
                    if stop_event.is_set():
                        break
                    time.sleep(0.1)
    except Exception as e:
        # Same reasoning as parser_feed_thread's matching except: this runs
        # headless via pythonw, so an uncaught exception here would kill the
        # thread with the traceback going nowhere — log it instead.
        sender_log(f"{prefix} 🔴 Поток упал с необработанной ошибкой: {e}")
    finally:
        # Auto-registered accounts that were still landing comments when the
        # sender stopped go into the pool so the next run can reuse them
        # instead of registering from scratch (pop_account_from_pool). An
        # account that never sent anything, or died before this point,
        # isn't worth saving — account_healthy tracks exactly that.
        if is_fresh_account and account_healthy and session:
            try:
                saved_username, _ = username_from_userinfo_cookie(session)
            except Exception:
                saved_username = ""
            save_account_to_pool(session_cookies_to_text(session), saved_username or "")
            sender_log(f"{prefix} 💾 Аккаунт {saved_username or '(?)'} сохранён в пул для следующего запуска")
        release_live_proxy(reserved_proxy)


def sender_worker(cookie_text, comment_text, thread_count, ignore_blacklist,
                  manual_csrf_token="", proxy_text="", dry_run=False, use_live_proxies=False,
                  invis_char="", invis_count=0, shortener="", verify_comment=True,
                  attach_image=False, image_bytes=None, image_filename="", photo_link=False,
                  auto_register=False, username_template="", avatar_bytes=None,
                  proxy_for_comments=True, mail_provider=None, comment_delay=0, mail_domain=None,
                  uniqueify_text=False, send_random_after_spam=False, delete_special_comments=False,
                  reupload_image=False, single_comment=False, fallback_letters=False):
    """Tab 2: reads from the notebook file the parser tab fills — no feed
    URL of its own, no scrolling, nothing but consuming the notebook.
    """
    with sender_lock:
        if sender_state["running"]:
            sender_log("Уже запущено")
            return
        sender_state["running"] = True
        sender_state["stop"] = threading.Event()
        stop_event = sender_state["stop"]

    try:
        if not cookie_text.strip() and not auto_register:
            sender_log("⚠️ Вставьте куки аккаунта")
            return
        if auto_register and not username_template.strip():
            sender_log("⚠️ Для авто-регистрации укажите шаблон имени пользователя")
            return
        if not dry_run and not comment_text.strip() and not photo_link and not attach_image:
            sender_log("⚠️ Введите текст комментария")
            return
        thread_count = max(1, int(thread_count or 1))

        sender_log(f"Старт отправки: {thread_count} поток(ов)"
                   + (", блеклист игнорируется" if ignore_blacklist else "")
                   + (", каждый поток на своём живом прокси" if use_live_proxies
                      else (f", прокси {proxy_text.strip()}" if proxy_text.strip() else ", без прокси"))
                   + (", ТЕСТОВЫЙ РЕЖИМ (комментарии не отправляются)" if dry_run else "")
                   + (f", невидимые символы: {invis_char} x{invis_count}"
                      if invis_char and invis_count else "")
                   + (f", сокращение ссылок через {'is.gd' if shortener == 'isgd' else 'tr.ee'}" if shortener else "")
                   + (", прикрепление изображения" if attach_image and image_bytes else "")
                   + (", перезаливка изображения каждый раз" if reupload_image and attach_image else "")
                   + (", ссылка в фото (без текста)" if photo_link else "")
                   + (", каждый поток регистрирует свой аккаунт с нуля" if auto_register and not cookie_text.strip() else "")
                   + (", 1 отправка на аккаунт" if single_comment else "")
                   + (", буквы при спаме текста" if fallback_letters else "")
                   + (f", задержка между комментариями ~{comment_delay:g} сек" if comment_delay > 0 else ""))

        reserved = set()
        reserved_lock = threading.Lock()

        workers = []
        for i in range(thread_count):
            if workers:
                stagger_before_next_thread(stop_event)
            t = threading.Thread(target=comment_worker,
                                 args=(i, cookie_text, comment_text, ignore_blacklist,
                                       stop_event, reserved, reserved_lock,
                                       manual_csrf_token, proxy_text, dry_run, use_live_proxies,
                                       invis_char, invis_count, shortener, verify_comment,
                                       attach_image, image_bytes, image_filename, photo_link,
                                       auto_register, username_template, avatar_bytes,
                                       proxy_for_comments, mail_provider, comment_delay, mail_domain,
                                       uniqueify_text, send_random_after_spam, delete_special_comments,
                                       reupload_image, single_comment, fallback_letters),
                                 daemon=True)
            t.start()
            workers.append(t)

        for t in workers:
            t.join()

        sender_log("Остановлено")
    finally:
        with sender_lock:
            sender_state["running"] = False


# ─── HTML ───────────────────────────────────────────────────────────────────
HTML_PAGE = """<!DOCTYPE html>
<html lang="ru">
<head>
<meta charset="UTF-8">
<title>DeviantArt Commenter</title>
<style>
* { box-sizing: border-box; }
body { background:#0d0d0d; color:#eee; font-family: -apple-system, Segoe UI, Arial, sans-serif; margin:0; }
header { background:#151515; padding:16px 24px; border-bottom:1px solid #2a2a2a; }
header h1 { font-size:18px; margin:0; }
.tabs { display:flex; gap:4px; padding:10px 24px 0; background:#111; border-bottom:1px solid #2a2a2a; }
.tab-btn { background:#1a1a1a; color:#aaa; border:1px solid #2a2a2a; border-bottom:none;
           padding:8px 16px; cursor:pointer; border-radius:6px 6px 0 0; font-size:13px; }
.tab-btn.active { background:#0d0d0d; color:#4ade80; border-color:#333; }
.tab-content { display:none; padding:20px 24px; max-width:1000px; }
.tab-content.active { display:block; }
.section { background:#151515; border:1px solid #2a2a2a; border-radius:8px; padding:16px; margin-bottom:16px; }
.section h3 { margin:0 0 10px; font-size:14px; color:#9ca3af; text-transform:uppercase; letter-spacing:.05em; }
textarea, input[type=text], input[type=number] {
  width:100%; background:#1a1a1a; border:1px solid #333; color:#eee; border-radius:4px;
  padding:8px; font-family:inherit; font-size:13px;
}
textarea { min-height:70px; resize:vertical; }
button { background:#166534; color:#fff; border:none; padding:8px 14px; border-radius:4px;
         cursor:pointer; font-size:13px; margin-right:6px; }
button:hover { background:#15803d; }
button:disabled { background:#333; color:#777; cursor:not-allowed; }
.log { background:#0a0a0a; border:1px solid #2a2a2a; border-radius:4px; height:320px;
       overflow-y:auto; padding:8px; font-family:Consolas,monospace; font-size:12px; }
.log-line.ok { color:#4ade80; }
.log-line.sent { color:#facc15; }
.log-line.warn { color:#facc15; }
.log-line.error { color:#f87171; }
.stat { color:#888; font-size:12px; margin-left:10px; }
label.chk { display:flex; align-items:center; gap:6px; font-size:13px; cursor:pointer; margin-top:6px; }
label.chk input { width:auto; }
</style>
</head>
<body>
<header><h1>🎨 DeviantArt Commenter</h1></header>
<div class="tabs">
    <button class="tab-btn active" onclick="showTab(0)">Парсер</button>
    <button class="tab-btn" onclick="showTab(1)">Отправка</button>
    <button class="tab-btn" onclick="showTab(2)">Прокси</button>
</div>

<!-- TAB 0: Parser — discovers posts, writes to the notebook, never posts -->
<div class="tab-content active">
    <div class="section">
        <h3>Аккаунт (для чтения страниц)</h3>
        <label style="font-size:12px; color:#9ca3af;">Куки</label>
        <textarea id="pCookies" placeholder="Cookie: name=value; name2=value2 ... (из Network любого запроса к deviantart.com)"></textarea>
        <label style="font-size:12px; color:#9ca3af;">Прокси (необязательно)</label>
        <input type="text" id="pProxy" placeholder="host:port или host:port:user:pass или scheme://user:pass@host:port">
        <label class="chk"><input type="checkbox" id="pUseLiveProxies"> Использовать живой прокси (со вкладки «Прокси»)</label>
        <label class="chk"><input type="checkbox" id="pAutoRegisterIfDead" checked> При старте проверять аккаунт и, если куки пустые/мёртвые, авто-зарегистрировать новый</label>
        <label class="chk"><input type="checkbox" id="pSearchIllustrationsOnly"> Поисковые потоки: искать только иллюстрации (не по юзерам/артистам)</label>
        <div style="margin-top:10px;">
            <button id="pRegisterBtn" onclick="pRegisterAccount()">🚀 Зарегистрировать аккаунт и вставить куки</button>
        </div>
        <div style="color:#666; font-size:11px; margin-top:4px;">Регистрирует новый аккаунт с нуля (через прокси выше, если указан) и подставляет его куки в поле выше — то же самое, что авто-регистрация на вкладке «Отправка», прогресс смотри там в логе</div>
    </div>
    <div class="section">
        <h3>Ссылки на страницы</h3>
        <label style="font-size:12px; color:#9ca3af;">По одной на строку — галереи / поиск / теги / разные вкладки категорий. Для главной страницы (https://www.deviantart.com) используется настоящий скролл через курсорный API; для остальных ссылок — одна отрисованная сервером партия за опрос, чтобы постов было больше — добавь несколько разных ссылок</label>
        <textarea id="pFeedUrl" placeholder="https://www.deviantart.com/&#10;https://www.deviantart.com/tag/fantasy" style="margin-bottom:10px;"></textarea>
        <label style="font-size:12px; color:#9ca3af;">Количество потоков</label>
        <input type="number" id="pThreads" value="1" min="1" style="max-width:120px; margin-bottom:10px;">
        <label style="font-size:12px; color:#9ca3af;">Страниц скролла за один заход (0 = нонстоп, пока не кончится лента)</label>
        <input type="number" id="pScrollMaxPages" value="0" min="0" style="max-width:120px;">
        <label class="chk"><input type="checkbox" id="pIgnoreBlacklist"> Парсить посты авторов из блеклиста (по умолчанию они пропускаются)</label>
        <p style="color:#888; font-size:11px; margin-top:4px;">
            Если потоков меньше, чем ссылок — ссылки делятся между потоками поровну (по кругу).
            Если потоков больше, чем ссылок — лишние потоки равномерно распределяются по тем же ссылкам (несколько потоков на одну ссылку).
        </p>
    </div>
    <div class="section">
        <div>
            <button id="pStartBtn" onclick="pStart()">Старт</button>
            <button id="pStopBtn" onclick="pStop()" style="background:#b45309;">Стоп</button>
            <button id="pRestartBtn" onclick="pRestart()" style="background:#1d4ed8;">🔄 Перезапустить</button>
            <span>Найдено: <b id="pFound" style="color:#4ade80;">0</b></span>
            <span id="pStat" class="stat"></span>
            <button onclick="daOpen('notebook')" style="margin-left:10px;">📄 Открыть блокнот</button>
            <button onclick="pClearNotebook()" style="background:#7f1d1d;">Очистить блокнот</button>
            <button onclick="daOpen('search_ranking')">📊 Топ поисковых запросов</button>
        </div>
        <div style="color:#666; font-size:11px; margin-top:6px;">deviantart_posts.txt — читает вкладка «Отправка»; топ запросов — по оценке DeviantArt (estTotal), от самых крупных</div>
        <h3 style="margin-top:14px;">Лог</h3>
        <div style="margin-bottom:6px;"><button onclick="daCopyLog('pLog')">Копировать лог</button></div>
        <div class="log" id="pLog"></div>
    </div>
</div>

<!-- TAB 1: Sender — reads the notebook, posts comments -->
<div class="tab-content">
    <div class="section">
        <h3>Аккаунт</h3>
        <label style="font-size:12px; color:#9ca3af;">Куки</label>
        <textarea id="sCookies" placeholder="Cookie: name=value; name2=value2 ... (из Network любого запроса к deviantart.com)"></textarea>
        <label style="font-size:12px; color:#9ca3af;">csrf_token вручную (необязательно)</label>
        <input type="text" id="sCsrfToken" placeholder="если пусто — скрипт попробует получить сам с главной страницы">
        <p style="color:#888; font-size:11px; margin-top:4px;">
            Проще всего: открой deviantart.com под этим аккаунтом → DevTools → Network → поставь
            любой лайк/коммент вручную → найди запрос comments/post → ПКМ → Copy → Copy as fetch —
            в теле сразу видно "csrf_token":"..." — скопируй только само значение сюда (без кавычек).
        </p>
        <label style="font-size:12px; color:#9ca3af;">Прокси (необязательно)</label>
        <input type="text" id="sProxy" placeholder="host:port или host:port:user:pass или scheme://user:pass@host:port">
        <label class="chk"><input type="checkbox" id="sUseLiveProxies"> Использовать живые прокси (со вкладки «Прокси») — каждый поток берёт свой уникальный, никто не делится</label>
        <div style="margin-top:6px;">
            <button id="sOpenBrowserBtn" onclick="sOpenBrowserWithProxy()">🌐 Открыть браузер с этим прокси</button>
            <span style="color:#666; font-size:11px;">— один Chrome, IP закреплён на всю сессию (не ротируется по запросам, как в самом скрипте)</span>
        </div>
    </div>
    <div class="section">
        <h3>Комментарий</h3>
        <label style="font-size:12px; color:#9ca3af;">Текст комментария</label>
        <textarea id="sCommentText" placeholder="Текст комментария"></textarea>
        <p style="color:#888; font-size:11px; margin-top:4px;">
            Чтобы вставить ссылку прямо в текст: {как_отображается;куда_ведёт} — например
            {Смотри тут;https://example.com} покажется как кликабельный текст «Смотри тут».
        </p>
        <label style="font-size:12px; color:#9ca3af;">Невидимый символ (перемешивает текст перед каждой отправкой)</label>
        <select id="sInvisChar" style="max-width:320px; margin-bottom:6px;">
            <option value="">— не вставлять —</option>
            <option value="zwsp">Zero Width Space (U+200B)</option>
            <option value="zwnj">Zero Width Non-Joiner (U+200C)</option>
            <option value="zwj">Zero Width Joiner (U+200D)</option>
            <option value="wj">Word Joiner (U+2060)</option>
            <option value="shy">Soft Hyphen (U+00AD)</option>
        </select>
        <label style="font-size:12px; color:#9ca3af;">Количество символов</label>
        <input type="number" id="sInvisCount" value="0" min="0" style="max-width:120px;">
        <p style="color:#888; font-size:11px; margin-top:4px;">
            Каждый раз перед отправкой в случайные места текста вставляется указанное количество
            невидимых символов — в ссылку {как_отображается;куда_ведёт} они никогда не попадают.
        </p>
        <label class="chk"><input type="checkbox" id="sUniqueifyText"> Уникализировать текст перед каждой отправкой (замена латинских букв на визуально идентичные из кириллицы/греческого/чероки/фуллвайдт)</label>
        <p style="color:#888; font-size:11px; margin-top:4px;">
            Каждая отправка (включая первую) получает свежую случайную замену букв.
            Для человека выглядит одинаково («Ꭰеаr Μember»), но для DA каждое сообщение —
            новая последовательность кодпоинтов, поэтому спам-фильтр по хэшу не срабатывает.
            Ссылки {как_отображается;куда_ведёт} не трогает. При спам-ошибке диагностика из букв
            определит: заспамлен весь аккаунт или только текст.
        </p>
    </div>
    <div class="section">
        <h3>Потоки и блеклист</h3>
        <label style="font-size:12px; color:#9ca3af;">Количество потоков</label>
        <input type="number" id="sThreads" value="1" min="1" style="max-width:120px; margin-bottom:6px;">
        <label style="font-size:12px; color:#9ca3af;">Задержка между комментариями на поток, сек (0 = без задержки)</label>
        <input type="number" id="sCommentDelay" value="0" min="0" step="0.5" style="max-width:120px; margin-bottom:6px;">
        <label class="chk"><input type="checkbox" id="sIgnoreBlacklist"> Игнорировать блеклист (комментировать даже повторных авторов)</label>
        <label class="chk"><input type="checkbox" id="sDryRun"> Тестовый режим — только читать блокнот, комментарии не отправлять</label>
        <div style="margin-bottom:6px;">
            <label style="font-size:12px; color:#9ca3af;">Сокращалка ссылок {display;url}</label>
            <select id="sShortener" style="max-width:320px;">
                <option value="">Не использовать</option>
                <option value="treeee">tr.ee</option>
                <option value="isgd">is.gd</option>
            </select>
        </div>
        <label class="chk"><input type="checkbox" id="sVerifyComment" checked> Проверять наличие комментария после отправки (если отключено, сразу считается успехом)</label>
        <label class="chk"><input type="checkbox" id="sAttachImage"> Прикреплять изображение к комментарию (если в sta.sh аккаунта уже есть картинка — берётся она, иначе загружается выбранный файл один раз)</label>
        <input type="file" id="sImageFile" accept="image/*" style="max-width:320px; margin-bottom:6px;">
        <div id="sImageFileName" style="color:#666; font-size:11px; margin-bottom:6px;"></div>
        <label class="chk"><input type="checkbox" id="sReuploadImage"> Перезаливать изображение при каждой отправке (новая копия в sta.sh каждый раз — обход антиспама по хешу картинки)</label>
        <label class="chk"><input type="checkbox" id="sPhotoLink"> Ссылка в фото — текст комментария НЕ отправляется; ссылка из поля текста сокращается и вставляется как ссылка на фото</label>
        <label class="chk"><input type="checkbox" id="sProxyForComments" checked> Использовать прокси при отправке комментариев (если выключено — прокси только для регистрации)</label>
        <label class="chk"><input type="checkbox" id="sAutoRegister"> Авто-регистрация при антиспаме — при ошибке 3 (spam) создаёт новый аккаунт</label>
        <label class="chk"><input type="checkbox" id="sSingleComment"> 1 отправка на аккаунт — после одного комментария сразу регистрирует новый аккаунт</label>
        <label class="chk"><input type="checkbox" id="sSendRandomAfterSpam"> Отправлять рандом-текст после спама (перед созданием нового аккаунта)</label>
        <label class="chk"><input type="checkbox" id="sFallbackLetters"> Пару букв при спаме текста — если текст заспамлен, отправить случайные буквы (с изображением если есть) и продолжить без перерегистрации</label>
        <label class="chk"><input type="checkbox" id="sDeleteSpecialComments"> Удалять комментарии со спецсимволами (гомоглифы, невидимые символы) после отправки</label>
        <div style="margin-left:20px; margin-top:6px;">
            <input type="text" id="sUsernameTemplate" placeholder="Шаблон: Verification-XXXXXXX" style="max-width:300px; padding:4px 8px; margin-bottom:6px;">
            <div style="font-size:11px; color:#666; margin-bottom:6px;">Вместо XXXXXXX подставится 7-цифровой счётчик (0000000, 0000001, ...)</div>
            <label style="font-size:12px; color:#9ca3af;">Сервис временной почты</label>
            <select id="sMailProvider" onchange="daToggleMailDomain()" style="max-width:320px; margin-bottom:6px;">
                <option value="auto" selected>Авто (все по очереди)</option>
                <option value="mailtm">Mail.tm (web-library.net)</option>
                <option value="tempmail_lol">TempMail.lol (рандом домены)</option>
                <option value="tempmailorg">Temp-Mail.org (через прокси)</option>
                <option value="tinyhost">TinyHost.shop</option>
                <option value="besttempmail">Best-Temp-Mail.com</option>
                <option value="tmailor">Tmailor.com (CF+2captcha)</option>
                <option value="mailtd">Mail.td (Pro — нужен токен)</option>
                <option value="mailgw">Mail.gw</option>
                <option value="1secmail">1secMail (.org/.net)</option>
                <option value="emailnator">Emailnator (Gmail)</option>
                <option value="tempmail4u">TempMail4u (jsontoexcel.net)</option>
                <option value="mohmal">Mohmal</option>
                <option value="tempmailg">TempMailG (Cloudflare + 2captcha)</option>
                <option value="smailpro">Smailpro (Outlook/Gmail/Hotmail)</option>
                <option value="temptf">Temp.tf (Gmail/Outlook/Hotmail)</option>
                <option value="mailyra">Mailyra (10 доменов)</option>
            </select>
            <input type="text" id="sMailtdToken" placeholder="Mail.td API токен (td_xxx...)" style="max-width:320px; margin-bottom:6px; display:none;">
            <div id="sMailDomainWrap" style="display:none;">
                <label style="font-size:12px; color:#9ca3af;">Домен Emailnator</label>
                <select id="sMailDomain" style="max-width:320px; margin-bottom:6px;">
                    <option value="googleMail">Googlemail.com</option>
                    <option value="domain">Случайный домен</option>
                    <option value="plusGmail">Gmail (+тег)</option>
                    <option value="dotGmail">Gmail (через точки)</option>
                </select>
            </div>
            <div id="sSmailproDomainWrap" style="display:none;">
                <label style="font-size:12px; color:#9ca3af;">Домен Smailpro</label>
                <select id="sSmailproDomain" style="max-width:320px; margin-bottom:6px;">
                    <option value="outlook.com" selected>outlook.com</option>
                    <option value="hotmail.com">hotmail.com</option>
                    <option value="outlook.kr">outlook.kr</option>
                    <option value="outlook.fr">outlook.fr</option>
                    <option value="outlook.com.vn">outlook.com.vn</option>
                    <option value="outlook.co.id">outlook.co.id</option>
                    <option value="outlook.co.th">outlook.co.th</option>
                    <option value="outlook.com.ar">outlook.com.ar</option>
                    <option value="outlook.co.il">outlook.co.il</option>
                    <option value="gmail.com">gmail.com</option>
                    <option value="googlemail.com">googlemail.com</option>
                    <option value="melbourne.edu.pl">melbourne.edu.pl</option>
                    <option value="sydney.edu.pl">sydney.edu.pl</option>
                    <option value="tokyo.edu.pl">tokyo.edu.pl</option>
                    <option value="storegmail.net">storegmail.net</option>
                </select>
            </div>
            <input type="text" id="sSmailpro2captchaKey" placeholder="2captcha API ключ (для Smailpro, если капча)" style="max-width:320px; margin-bottom:6px; display:none;">
            <div id="sTemptfDomainWrap" style="display:none;">
                <label style="font-size:12px; color:#9ca3af;">Провайдеры Temp.tf</label>
                <select id="sTemptfDomain" style="max-width:320px; margin-bottom:6px;">
                    <option value="outlook,hotmail,gmail" selected>Все (Outlook+Hotmail+Gmail)</option>
                    <option value="outlook">Outlook</option>
                    <option value="hotmail">Hotmail</option>
                    <option value="gmail">Gmail</option>
                    <option value="outlook,hotmail">Outlook+Hotmail</option>
                </select>
            </div>
            <div id="sMailyraDomainWrap" style="display:none;">
                <label style="font-size:12px; color:#9ca3af;">Домен Mailyra</label>
                <select id="sMailyraDomain" style="max-width:320px; margin-bottom:6px;">
                    <option value="" selected>Случайный</option>
                    <option value="mailyra.com">mailyra.com</option>
                    <option value="invoxica.com">invoxica.com</option>
                    <option value="receivory.com">receivory.com</option>
                    <option value="go9.co">go9.co</option>
                    <option value="tmtm.me">tmtm.me</option>
                    <option value="aigram.kr">aigram.kr</option>
                    <option value="beauturn.com">beauturn.com</option>
                    <option value="leaseyo.kr">leaseyo.kr</option>
                    <option value="krseller.com">krseller.com</option>
                    <option value="1004cat.com">1004cat.com</option>
                </select>
            </div>
            <input type="file" id="sAvatarFile" accept="image/*" style="max-width:320px; margin-bottom:6px;">
            <div id="sAvatarFileName" style="color:#666; font-size:11px;"></div>
            <div style="margin-top:10px;">
                <span style="font-size:12px; color:#9ca3af;">Сохранённых рабочих аккаунтов в пуле: <b id="sPoolCount" style="color:#4ade80;">0</b></span><br>
                <span style="font-size:11px; color:#666;">При остановке отправки аккаунты, которые ещё успешно комментировали, сохраняются и при следующем запуске переиспользуются вместо новой регистрации.</span><br>
                <button onclick="sResetAccountPool()" style="background:#7f1d1d; margin-top:6px;">🗑️ Сброс — след. запуск всегда с новой регистрации</button>
            </div>
        </div>
        <div style="margin-top:10px;">
            <button onclick="daOpen('blacklist')">📕 Открыть блеклист</button>
            <button onclick="daClearBlacklist()" style="background:#7f1d1d;">Очистить блеклист</button>
        </div>
        <div style="color:#666; font-size:11px; margin-top:6px;">deviantart_blacklist.txt — теперь хранит username{TAB}ссылка_на_пост</div>
        <div style="margin-top:10px;">
            <label style="font-size:12px; color:#9ca3af;">Восстановить из блеклиста в блокнот по username</label><br>
            <input type="text" id="sRestoreUsername" placeholder="username" style="max-width:200px;">
            <button onclick="sRestoreFromBlacklist()">↩️ Вернуть в блокнот</button>
        </div>
    </div>
    <div class="section">
        <div>
            <button id="sStartBtn" onclick="sStart()">Старт</button>
            <button id="sStopBtn" onclick="sStop()" style="background:#b45309;">Стоп</button>
            <button id="sRestartBtn" onclick="sRestart()" style="background:#1d4ed8;">🔄 Перезапустить</button>
            <span>Отправлено: <b id="sSent" style="color:#4ade80;">0</b></span>
            <span>В блокноте: <b id="sNotebookCount" style="color:#60a5fa;">0</b></span>
            <span>В блеклисте: <b id="sBlacklistCount" style="color:#f87171;">0</b></span>
            <span id="sStat" class="stat"></span>
        </div>
        <h3 style="margin-top:14px;">Лог</h3>
        <div style="margin-bottom:6px;"><button onclick="daCopyLog('sLog')">Копировать лог</button></div>
        <div class="log" id="sLog"></div>
    </div>
</div>

<!-- TAB 2: Autonomous proxy pool — scrapes public proxy sources, checks against DA, sorts by ping -->
<div class="tab-content">
    <div class="section">
        <h3>Автономный пул прокси <span id="ppStatus" class="stat"></span></h3>
        <p style="color:#888; font-size:12px; margin-bottom:10px;">
            Скрипт сам качает свежие прокси из <b id="ppSourceCount">50+</b> публичных источников каждые 3 минуты,
            непрерывно проверяет каждый на реальную доступность <b>https://www.deviantart.com/</b>
            (200/3xx/202+WAF-challenge/403+CloudFront = прокси реально достиг DA-CDN),
            сортирует по пингу. Все воркеры (регер, парсер, отправщик) при включённой галке
            «Использовать живые прокси» всегда получают самый быстрый живой прокси на момент запроса;
            те, что реально не проходят регистрацию, воркеры сами помечают bad через mark_bad.
        </p>
        <div id="ppStatsBar" style="display:grid; grid-template-columns:repeat(6,minmax(0,1fr)); gap:8px; margin:10px 0; font-size:12px;">
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">Всего</div>
                <div id="ppStatTotal" style="font-size:18px; color:#e5e7eb; font-weight:bold;">0</div>
            </div>
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">Живых</div>
                <div id="ppStatAlive" style="font-size:18px; color:#4ade80; font-weight:bold;">0</div>
            </div>
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">CF-blocked</div>
                <div id="ppStatCfBlocked" style="font-size:18px; color:#fb923c; font-weight:bold;">0</div>
            </div>
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">Мёртвых</div>
                <div id="ppStatDead" style="font-size:18px; color:#f87171; font-weight:bold;">0</div>
            </div>
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">В очереди</div>
                <div id="ppStatUnchecked" style="font-size:18px; color:#facc15; font-weight:bold;">0</div>
            </div>
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">Проверок</div>
                <div id="ppStatChecks" style="font-size:18px; color:#60a5fa; font-weight:bold;">0</div>
            </div>
            <div style="background:#1f2937; padding:8px; border-radius:4px;">
                <div style="color:#9ca3af;">Забанено IP</div>
                <div id="ppStatBurned" style="font-size:18px; color:#a78bfa; font-weight:bold;">0</div>
            </div>
        </div>
        <div style="font-size:11px; color:#666; margin-bottom:10px;">
            Последний фетч: <span id="ppLastFetch">—</span> &nbsp;|&nbsp;
            Последняя проверка: <span id="ppLastCheck">—</span> &nbsp;|&nbsp;
            Активных чекеров: <span id="ppActiveCheckers">0</span>
        </div>
        <div style="margin-bottom:10px;">
            <button onclick="ppRefresh()">🔄 Скачать сейчас</button>
            <button onclick="ppClearDead()">Убрать мёртвых</button>
            <button onclick="ppClearAll()" style="background:#b45309;">Очистить весь пул</button>
        </div>
        <div style="margin-bottom:10px;">
            <label style="font-size:12px; color:#9ca3af;">Добавить свои прокси (по одному в строке)</label>
            <textarea id="ppManualBox" placeholder="host:port или host:port:user:pass&#10;http://user:pass@host:port" style="height:80px;"></textarea>
            <button onclick="ppAddManual()" style="margin-top:6px;">Добавить в пул</button>
        </div>
    </div>
    <div class="section">
        <h3>Прокси (сортировка: живые по пингу → непроверенные → мёртвые)</h3>
        <div style="max-height:520px; overflow-y:auto; border:1px solid #374151; border-radius:4px;">
            <table id="ppTable" style="width:100%; border-collapse:collapse; font-size:12px;">
                <thead style="position:sticky; top:0; background:#111827; z-index:1;">
                    <tr>
                        <th style="text-align:left; padding:6px; border-bottom:1px solid #374151;">Адрес</th>
                        <th style="text-align:center; padding:6px; border-bottom:1px solid #374151; width:80px;">Статус</th>
                        <th style="text-align:right; padding:6px; border-bottom:1px solid #374151; width:90px;">Пинг (мс)</th>
                        <th style="text-align:center; padding:6px; border-bottom:1px solid #374151; width:90px;">Проверен</th>
                        <th style="text-align:center; padding:6px; border-bottom:1px solid #374151; width:120px;"></th>
                    </tr>
                </thead>
                <tbody id="ppTableBody"></tbody>
            </table>
        </div>
        <div style="font-size:11px; color:#666; margin-top:6px;">Показаны первые 300 записей.</div>
    </div>
</div>

<script>
function showTab(n, skipSave) {
    document.querySelectorAll('.tab-content').forEach(el => el.classList.remove('active'));
    document.querySelectorAll('.tab-btn').forEach(el => el.classList.remove('active'));
    document.querySelectorAll('.tab-content')[n].classList.add('active');
    document.querySelectorAll('.tab-btn')[n].classList.add('active');
    // daRestoreState() calls this first, before any other field has been
    // put back into the DOM yet — saving here would blow away the very
    // state daRestoreState() is about to restore (every other field still
    // reads back blank at this point), which is exactly what was silently
    // wiping every saved field on every single page load/reload.
    if (!skipSave) daSaveState();
}

function _daGetVal(id) { try { const e = document.getElementById(id); return e ? e.value : ''; } catch(x) { return ''; } }
function _daGetChk(id) { try { const e = document.getElementById(id); return e ? e.checked : false; } catch(x) { return false; } }

function daSaveState() {
    try {
        const s = {
            activeTab: Array.from(document.querySelectorAll('.tab-btn')).findIndex(b => b.classList.contains('active')),
            pCookies: _daGetVal('pCookies'),
            pProxy: _daGetVal('pProxy'),
            pUseLiveProxies: _daGetChk('pUseLiveProxies'),
            pFeedUrl: _daGetVal('pFeedUrl'),
            pThreads: _daGetVal('pThreads'),
            pScrollMaxPages: _daGetVal('pScrollMaxPages'),
            pIgnoreBlacklist: _daGetChk('pIgnoreBlacklist'),
            pAutoRegisterIfDead: _daGetChk('pAutoRegisterIfDead'),
            pSearchIllustrationsOnly: _daGetChk('pSearchIllustrationsOnly'),
            sCookies: _daGetVal('sCookies'),
            sCsrfToken: _daGetVal('sCsrfToken'),
            sProxy: _daGetVal('sProxy'),
            sUseLiveProxies: _daGetChk('sUseLiveProxies'),
            sCommentText: _daGetVal('sCommentText'),
            sThreads: _daGetVal('sThreads'),
            sCommentDelay: _daGetVal('sCommentDelay'),
            sIgnoreBlacklist: _daGetChk('sIgnoreBlacklist'),
            sDryRun: _daGetChk('sDryRun'),
            sInvisChar: _daGetVal('sInvisChar'),
            sInvisCount: _daGetVal('sInvisCount'),
            sUniqueifyText: _daGetChk('sUniqueifyText'),
            sShortener: _daGetVal('sShortener'),
            sVerifyComment: _daGetChk('sVerifyComment'),
            sAttachImage: _daGetChk('sAttachImage'),
            sPhotoLink: _daGetChk('sPhotoLink'),
            sProxyForComments: _daGetChk('sProxyForComments'),
            sAutoRegister: _daGetChk('sAutoRegister'),
            sSendRandomAfterSpam: _daGetChk('sSendRandomAfterSpam'),
            sDeleteSpecialComments: _daGetChk('sDeleteSpecialComments'),
            sUsernameTemplate: _daGetVal('sUsernameTemplate'),
            sMailProvider: _daGetVal('sMailProvider'),
            sMailDomain: _daGetVal('sMailDomain'),
            sMailtdToken: _daGetVal('sMailtdToken'),
            sSmailproDomain: _daGetVal('sSmailproDomain'),
            sSmailpro2captchaKey: _daGetVal('sSmailpro2captchaKey'),
            sTemptfDomain: _daGetVal('sTemptfDomain'),
            sMailyraDomain: _daGetVal('sMailyraDomain'),
            _ppReserved: 0  // reserved slot for backward compat
        };
        try { localStorage.setItem('daState', JSON.stringify(s)); } catch(e) {}
        if (!daSaveState._srvTimer) {
            daSaveState._srvTimer = setTimeout(() => {
                daSaveState._srvTimer = null;
                fetch('/api/save_settings', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify(s)}).catch(()=>{});
            }, 2000);
        }
    } catch(e) { console.error('daSaveState:', e); }
}

function _daSet(id, val) { try { const e = document.getElementById(id); if (e) e.value = val; } catch(x) {} }
function _daChk(id, val) { try { const e = document.getElementById(id); if (e) e.checked = val; } catch(x) {} }

function daApplyState(s) {
    if (!s) return;
    if (s.activeTab >= 0) showTab(s.activeTab, true);
    if ('pCookies' in s) _daSet('pCookies', s.pCookies);
    if ('pProxy' in s) _daSet('pProxy', s.pProxy);
    if ('pUseLiveProxies' in s) _daChk('pUseLiveProxies', s.pUseLiveProxies);
    if ('pFeedUrl' in s) _daSet('pFeedUrl', s.pFeedUrl);
    if ('pThreads' in s) _daSet('pThreads', s.pThreads);
    if ('pScrollMaxPages' in s) _daSet('pScrollMaxPages', s.pScrollMaxPages);
    if ('pIgnoreBlacklist' in s) _daChk('pIgnoreBlacklist', s.pIgnoreBlacklist);
    if ('pAutoRegisterIfDead' in s) _daChk('pAutoRegisterIfDead', s.pAutoRegisterIfDead);
    if ('pSearchIllustrationsOnly' in s) _daChk('pSearchIllustrationsOnly', s.pSearchIllustrationsOnly);
    if ('sCookies' in s) _daSet('sCookies', s.sCookies);
    if ('sCsrfToken' in s) _daSet('sCsrfToken', s.sCsrfToken);
    if ('sProxy' in s) _daSet('sProxy', s.sProxy);
    if ('sUseLiveProxies' in s) _daChk('sUseLiveProxies', s.sUseLiveProxies);
    if ('sCommentText' in s) _daSet('sCommentText', s.sCommentText);
    if ('sThreads' in s) _daSet('sThreads', s.sThreads);
    if ('sCommentDelay' in s) _daSet('sCommentDelay', s.sCommentDelay);
    if ('sIgnoreBlacklist' in s) _daChk('sIgnoreBlacklist', s.sIgnoreBlacklist);
    if ('sDryRun' in s) _daChk('sDryRun', s.sDryRun);
    if ('sInvisChar' in s) _daSet('sInvisChar', s.sInvisChar);
    if ('sInvisCount' in s) _daSet('sInvisCount', s.sInvisCount);
    if ('sUniqueifyText' in s) _daChk('sUniqueifyText', s.sUniqueifyText);
    if ('sShortener' in s) _daSet('sShortener', s.sShortener);
    else if (s.sUseTr) _daSet('sShortener', 'treeee');
    if ('sVerifyComment' in s) _daChk('sVerifyComment', s.sVerifyComment);
    if ('sAttachImage' in s) _daChk('sAttachImage', s.sAttachImage);
    if ('sPhotoLink' in s) _daChk('sPhotoLink', s.sPhotoLink);
    if ('sProxyForComments' in s) _daChk('sProxyForComments', s.sProxyForComments);
    if ('sAutoRegister' in s) _daChk('sAutoRegister', s.sAutoRegister);
    if ('sSendRandomAfterSpam' in s) _daChk('sSendRandomAfterSpam', s.sSendRandomAfterSpam);
    if ('sDeleteSpecialComments' in s) _daChk('sDeleteSpecialComments', s.sDeleteSpecialComments);
    if ('sUsernameTemplate' in s) _daSet('sUsernameTemplate', s.sUsernameTemplate);
    if ('sMailProvider' in s) _daSet('sMailProvider', s.sMailProvider);
    if ('sMailDomain' in s) _daSet('sMailDomain', s.sMailDomain);
    if ('sMailtdToken' in s) _daSet('sMailtdToken', s.sMailtdToken);
    if ('sSmailproDomain' in s) _daSet('sSmailproDomain', s.sSmailproDomain);
    if ('sSmailpro2captchaKey' in s) _daSet('sSmailpro2captchaKey', s.sSmailpro2captchaKey);
    if ('sTemptfDomain' in s) _daSet('sTemptfDomain', s.sTemptfDomain);
    if ('sMailyraDomain' in s) _daSet('sMailyraDomain', s.sMailyraDomain);
    daToggleMailDomain();
    // (legacy pxProxiesText/pxThreadCount/pxContinuousOn removed — pool is autonomous now)
}

function daRestoreState() {
    let s = null;
    try { s = JSON.parse(localStorage.getItem('daState') || 'null'); } catch(e) {}
    if (!s && window.__daServerSettings) s = window.__daServerSettings;
    daApplyState(s);
}

function daToggleMailDomain() {
    const prov = document.getElementById('sMailProvider').value;
    document.getElementById('sMailDomainWrap').style.display = prov === 'emailnator' ? 'block' : 'none';
    document.getElementById('sMailtdToken').style.display = prov === 'mailtd' ? '' : 'none';
    document.getElementById('sSmailproDomainWrap').style.display = prov === 'smailpro' ? 'block' : 'none';
    document.getElementById('sSmailpro2captchaKey').style.display = prov === 'smailpro' ? '' : 'none';
    document.getElementById('sTemptfDomainWrap').style.display = prov === 'temptf' ? 'block' : 'none';
    document.getElementById('sMailyraDomainWrap').style.display = prov === 'mailyra' ? 'block' : 'none';
}

async function daPost(url, payload) {
    const res = await fetch(url, { method: 'POST', headers: {'Content-Type':'application/json'}, body: JSON.stringify(payload || {}) });
    return res.json();
}

async function pStart() {
    daSaveState();
    const cookies = document.getElementById('pCookies').value;
    const proxy = document.getElementById('pProxy').value;
    const use_live_proxies = document.getElementById('pUseLiveProxies').checked;
    const auto_register_if_dead = document.getElementById('pAutoRegisterIfDead').checked;
    const feed_url = document.getElementById('pFeedUrl').value;
    const threads = parseInt(document.getElementById('pThreads').value, 10) || 1;
    const scroll_max_pages = parseInt(document.getElementById('pScrollMaxPages').value, 10) || 0;
    const ignore_blacklist = document.getElementById('pIgnoreBlacklist').checked;
    const search_illustrations_only = document.getElementById('pSearchIllustrationsOnly').checked;
    if (!cookies.trim() && !auto_register_if_dead) {
        alert('Вставьте куки (или включите «При старте проверять аккаунт...», чтобы скрипт сам зарегистрировал аккаунт)');
        return;
    }
    if (!feed_url.trim()) { alert('Укажите хотя бы одну ссылку на страницу'); return; }
    const d = await daPost('/api/parser_start', { cookies, proxy, use_live_proxies, auto_register_if_dead, feed_url, threads, scroll_max_pages, ignore_blacklist, search_illustrations_only });
    if (d.cookies) {
        document.getElementById('pCookies').value = d.cookies;
        daSaveState();
    }
    if (!d.ok) {
        alert('Не удалось запустить парсер: ' + (d.error || 'неизвестная ошибка'));
    }
}
async function pStop() { await daPost('/api/parser_stop', {}); }
async function pRestart() {
    await pStop();
    const btn = document.getElementById('pRestartBtn');
    btn.disabled = true;
    btn.textContent = '⏳ Останавливаю...';
    const poll = setInterval(async () => {
        try {
            const res = await (await fetch('/api/parser_state')).json();
            if (!res.running) {
                clearInterval(poll);
                btn.disabled = false;
                btn.textContent = '🔄 Перезапустить';
                await pStart();
            }
        } catch(e) {}
    }, 500);
}

async function pRegisterAccount() {
    const proxy = document.getElementById('pProxy').value;
    const btn = document.getElementById('pRegisterBtn');
    btn.disabled = true;
    btn.textContent = '⏳ Регистрирую... (прогресс в логе на вкладке «Отправка»)';
    try {
        const username_template = document.getElementById('sUsernameTemplate').value || 'Verification-XXXXXXX';
        const mail_provider = document.getElementById('sMailProvider').value;
        let mail_domain;
        if (mail_provider === 'smailpro') mail_domain = document.getElementById('sSmailproDomain').value;
        else if (mail_provider === 'temptf') mail_domain = document.getElementById('sTemptfDomain').value;
        else if (mail_provider === 'mailyra') mail_domain = document.getElementById('sMailyraDomain').value;
        else mail_domain = document.getElementById('sMailDomain').value;
        const mailtd_token = document.getElementById('sMailtdToken').value;
        const smailpro_2captcha_key = document.getElementById('sSmailpro2captchaKey').value;
        const d = await daPost('/api/register_account', { proxy, username_template, mail_provider, mail_domain, mailtd_token, smailpro_2captcha_key });
        if (d.ok) {
            document.getElementById('pCookies').value = d.cookies;
            daSaveState();
            alert('Аккаунт зарегистрирован, куки вставлены');
        } else {
            alert('Не удалось зарегистрировать аккаунт: ' + d.error);
        }
    } finally {
        btn.disabled = false;
        btn.textContent = '🚀 Зарегистрировать аккаунт и вставить куки';
    }
}
async function sOpenBrowserWithProxy() {
    const proxy = document.getElementById('sProxy').value;
    const btn = document.getElementById('sOpenBrowserBtn');
    btn.disabled = true;
    const original = btn.textContent;
    btn.textContent = '⏳ Открываю... (прогресс в логе ниже)';
    try {
        await daPost('/api/open_browser_with_proxy', { proxy });
    } finally {
        setTimeout(() => { btn.disabled = false; btn.textContent = original; }, 1500);
    }
}
async function pClearNotebook() {
    if (!confirm('Очистить блокнот с найденными постами?')) return;
    await daPost('/api/clear_notebook', {});
}

// File inputs can't be repopulated from JS after a reload (browser security),
// so persisted picks are cached here as base64 and used by sStart() whenever
// the input itself is empty — the filename label makes clear it's a saved pick.
let sImageDataCache = null;   // { name, data }
let sAvatarDataCache = null;  // { name, data }

function daCacheFile(file, storageKey, cacheSetter, labelId) {
    const reader = new FileReader();
    reader.onload = () => {
        const data = reader.result.split(',')[1];
        cacheSetter({ name: file.name, data });
        try { localStorage.setItem(storageKey, JSON.stringify({ name: file.name, data })); } catch(e) {}
        document.getElementById(labelId).textContent = 'Выбрано: ' + file.name;
    };
    reader.readAsDataURL(file);
}

function daRestoreCachedFile(storageKey, cacheSetter, labelId) {
    try {
        const saved = JSON.parse(localStorage.getItem(storageKey) || 'null');
        if (saved && saved.name && saved.data) {
            cacheSetter(saved);
            document.getElementById(labelId).textContent = 'Выбрано (сохранено): ' + saved.name;
        }
    } catch(e) {}
}

document.addEventListener('DOMContentLoaded', () => {
    daRestoreCachedFile('daImageFile', (v) => { sImageDataCache = v; }, 'sImageFileName');
    daRestoreCachedFile('daAvatarFile', (v) => { sAvatarDataCache = v; }, 'sAvatarFileName');

    const fi = document.getElementById('sImageFile');
    if (fi) fi.addEventListener('change', () => {
        const f = fi.files && fi.files[0];
        if (f) daCacheFile(f, 'daImageFile', (v) => { sImageDataCache = v; }, 'sImageFileName');
    });
    const af = document.getElementById('sAvatarFile');
    if (af) af.addEventListener('change', () => {
        const f = af.files && af.files[0];
        if (f) daCacheFile(f, 'daAvatarFile', (v) => { sAvatarDataCache = v; }, 'sAvatarFileName');
    });
});

async function sStart() {
    daSaveState();
    const cookies = document.getElementById('sCookies').value;
    const csrf_token = document.getElementById('sCsrfToken').value;
    const proxy = document.getElementById('sProxy').value;
    const comment_text = document.getElementById('sCommentText').value;
    const threads = parseInt(document.getElementById('sThreads').value, 10) || 1;
    const comment_delay = parseFloat(document.getElementById('sCommentDelay').value) || 0;
    const ignore_blacklist = document.getElementById('sIgnoreBlacklist').checked;
    const dry_run = document.getElementById('sDryRun').checked;
    const use_live_proxies = document.getElementById('sUseLiveProxies').checked;
    const invis_char = document.getElementById('sInvisChar').value;
    const invis_count = parseInt(document.getElementById('sInvisCount').value, 10) || 0;
    const uniqueify_text = document.getElementById('sUniqueifyText').checked;
    const shortener = document.getElementById('sShortener').value;
    const verify_comment = document.getElementById('sVerifyComment').checked;
    const attach_image = document.getElementById('sAttachImage').checked;
    const reupload_image = document.getElementById('sReuploadImage').checked;
    const photo_link = document.getElementById('sPhotoLink').checked;
    const proxy_for_comments = document.getElementById('sProxyForComments').checked;
    const auto_register = document.getElementById('sAutoRegister').checked;
    const single_comment = document.getElementById('sSingleComment').checked;
    const send_random_after_spam = document.getElementById('sSendRandomAfterSpam').checked;
    const fallback_letters = document.getElementById('sFallbackLetters').checked;
    const delete_special_comments = document.getElementById('sDeleteSpecialComments').checked;
    const username_template = document.getElementById('sUsernameTemplate').value;
    if (!cookies.trim() && !auto_register) { alert('Вставьте куки (или включите «Авто-регистрация», чтобы каждый поток сам создавал аккаунт)'); return; }
    if (!dry_run && !comment_text.trim() && !attach_image) { alert('Введите текст комментария'); return; }
    if (!dry_run && !comment_text.trim() && photo_link) { alert('Вставьте ссылку в поле текста (она пойдёт в фото)'); return; }
    if (photo_link && !attach_image) { alert('Для «Ссылка в фото» включите галочку «Прикреплять изображение» и выберите файл'); return; }
    if (auto_register && !username_template.trim()) { alert('Для авто-регистрации укажите шаблон имени пользователя (например, Verification-XXXXXXX)'); return; }

    let image_data = '';
    let image_filename = '';
    if (attach_image) {
        const fileInput = document.getElementById('sImageFile');
        const file = fileInput.files && fileInput.files[0];
        if (file) {
            image_filename = file.name;
            image_data = await new Promise((resolve, reject) => {
                const reader = new FileReader();
                reader.onload = () => resolve(reader.result.split(',')[1]);
                reader.onerror = reject;
                reader.readAsDataURL(file);
            });
        } else if (sImageDataCache) {
            image_filename = sImageDataCache.name;
            image_data = sImageDataCache.data;
        } else {
            alert('Выберите файл изображения (галочка «Прикреплять изображение» включена)'); return;
        }
    }

    let avatar_data = '';
    if (auto_register) {
        const avatarInput = document.getElementById('sAvatarFile');
        const file = avatarInput.files && avatarInput.files[0];
        if (file) {
            avatar_data = await new Promise((resolve, reject) => {
                const reader = new FileReader();
                reader.onload = () => resolve(reader.result.split(',')[1]);
                reader.onerror = reject;
                reader.readAsDataURL(file);
            });
        } else if (sAvatarDataCache) {
            avatar_data = sAvatarDataCache.data;
        } else {
            alert('Для авто-регистрации выберите файл аватарки'); return;
        }
    }

    const mail_provider = document.getElementById('sMailProvider').value;
    let mail_domain;
    if (mail_provider === 'smailpro') mail_domain = document.getElementById('sSmailproDomain').value;
    else if (mail_provider === 'temptf') mail_domain = document.getElementById('sTemptfDomain').value;
    else if (mail_provider === 'mailyra') mail_domain = document.getElementById('sMailyraDomain').value;
    else mail_domain = document.getElementById('sMailDomain').value;
    const mailtd_token = document.getElementById('sMailtdToken').value;
    const smailpro_2captcha_key = document.getElementById('sSmailpro2captchaKey').value;
    await daPost('/api/sender_start', { cookies, csrf_token, proxy, comment_text, threads, comment_delay, ignore_blacklist, dry_run, use_live_proxies, invis_char, invis_count, uniqueify_text, shortener, verify_comment, attach_image, reupload_image, image_data: image_data, image_filename, photo_link, proxy_for_comments, auto_register, single_comment, send_random_after_spam, fallback_letters, delete_special_comments, username_template, avatar_data, mail_provider, mail_domain, mailtd_token, smailpro_2captcha_key });
}
async function sStop() { await daPost('/api/sender_stop', {}); }
async function sRestart() {
    await sStop();
    const btn = document.getElementById('sRestartBtn');
    btn.disabled = true;
    btn.textContent = '⏳ Останавливаю...';
    const poll = setInterval(async () => {
        try {
            const res = await (await fetch('/api/sender_state')).json();
            if (!res.running) {
                clearInterval(poll);
                btn.disabled = false;
                btn.textContent = '🔄 Перезапустить';
                await sStart();
            }
        } catch(e) {}
    }, 500);
}

async function daOpen(which) {
    const d = await daPost('/api/open', { which });
    if (!d.ok) alert('Не удалось открыть файл: ' + d.info);
}

async function daClearBlacklist() {
    if (!confirm('Очистить блеклист?')) return;
    await daPost('/api/clear_blacklist', {});
}

async function sResetAccountPool() {
    if (!confirm('Удалить все сохранённые рабочие аккаунты? Следующий запуск отправки начнёт с регистрации новых.')) return;
    await daPost('/api/reset_account_pool', {});
    document.getElementById('sPoolCount').textContent = '0';
}

async function sRestoreFromBlacklist() {
    const username = document.getElementById('sRestoreUsername').value.trim();
    if (!username) { alert('Введите username'); return; }
    const d = await daPost('/api/blacklist_restore', { username });
    if (d.ok) {
        alert(d.restored > 0
            ? `Вернул в блокнот ${d.restored} ссылок(и) от ${username}, убрал из блеклиста`
            : `${username} убран из блеклиста, но сохранённых ссылок для него не было (старая запись без URL)`);
        document.getElementById('sRestoreUsername').value = '';
    } else {
        alert('Не удалось: ' + (d.error || 'неизвестная ошибка'));
    }
}

function daCopyLog(boxId) {
    const text = document.getElementById(boxId).innerText;
    if (!text.trim()) { alert('Лог пуст'); return; }
    navigator.clipboard.writeText(text).then(() => alert('Лог скопирован'));
}

function renderLog(boxId, lines) {
    const box = document.getElementById(boxId);
    box.innerHTML = lines.map(l => {
        // ✅ (heavy check) = fully confirmed (comment verified found, account
        // registered, etc.) -> green. Plain ✓ = did-the-action-but-not-yet-
        // confirmed (comment sent, proxy claimed, token fetched) -> yellow.
        // ✗/🔴 = error, in either case -> red. ⚠ = warning (transient
        // problem, retry-worthy, or non-fatal degradation) -> yellow.
        let cls = l.includes('✅') ? 'ok'
                : l.includes('✓') ? 'sent'
                : (l.includes('✗') || l.includes('🔴')) ? 'error'
                : l.includes('⚠') ? 'warn'
                : '';
        return '<div class="log-line ' + cls + '">' + l.replace(/</g, '&lt;') + '</div>';
    }).join('');
    box.scrollTop = box.scrollHeight;
}

// Autonomous proxy pool — the tab is a dashboard, not a form. It polls
// /api/proxy_pool_state every ~1.5s and re-renders the stats + table so
// what you see is always the current live state of the pool.
async function ppRefresh() { await daPost('/api/proxy_pool_refresh', {}); ppUpdate(); }
async function ppClearDead() { await daPost('/api/proxy_pool_clear_dead', {}); ppUpdate(); }
async function ppClearAll() {
    if (!confirm('Очистить весь пул (все прокси, живые и мёртвые)? Скачаются заново через несколько секунд.')) return;
    await daPost('/api/proxy_pool_clear_all', {}); ppUpdate();
}
async function ppRemove(addr) { await daPost('/api/proxy_pool_remove', { addr }); ppUpdate(); }
async function ppBurn(addr) {
    if (!confirm('Забанить IP этого прокси навсегда? Он больше не появится в пуле.')) return;
    await daPost('/api/proxy_pool_burn', { addr }); ppUpdate();
}
async function ppAddManual() {
    const proxies = document.getElementById('ppManualBox').value;
    if (!proxies.trim()) return;
    const d = await daPost('/api/proxy_pool_add', { proxies });
    if (d.ok) {
        document.getElementById('ppManualBox').value = '';
        alert('Добавлено: ' + d.added);
        ppUpdate();
    }
}

function _ppStatusChip(s) {
    if (s === 'alive') return '<span style="color:#4ade80;">● живой</span>';
    if (s === 'cf_blocked') return '<span style="color:#fb923c;">● CF-blocked</span>';
    if (s === 'dead') return '<span style="color:#f87171;">● мёртвый</span>';
    return '<span style="color:#facc15;">● в очереди</span>';
}

async function ppUpdate() {
    try {
        const data = await daPost('/api/proxy_pool_state', { limit: 300 });
        const st = data.stats || {};
        document.getElementById('ppStatTotal').textContent = st.total || 0;
        document.getElementById('ppStatAlive').textContent = st.alive || 0;
        document.getElementById('ppStatCfBlocked').textContent = st.cf_blocked || 0;
        document.getElementById('ppStatDead').textContent = st.dead || 0;
        document.getElementById('ppStatUnchecked').textContent = st.unchecked || 0;
        document.getElementById('ppStatChecks').textContent = st.checkCount || 0;
        document.getElementById('ppStatBurned').textContent = st.burnedIps || 0;
        document.getElementById('ppLastFetch').textContent = st.lastFetch || '—';
        document.getElementById('ppLastCheck').textContent = st.lastCheck || '—';
        document.getElementById('ppActiveCheckers').textContent = st.activeCheckers || 0;
        let statusTxt = '⏸ Готов';
        if (st.fetching) statusTxt = '📥 Скачиваю новые...';
        else if (st.checking) statusTxt = '🔄 Проверяю (' + (st.inFlight || 0) + ' в полёте)';
        document.getElementById('ppStatus').textContent = statusTxt;
        // Render table
        const body = document.getElementById('ppTableBody');
        const rows = (data.proxies || []).map(p => {
            const lat = p.latency > 0 ? p.latency : '—';
            const lastCheck = p.lastCheck || '—';
            return '<tr>' +
                '<td style="padding:5px 6px; border-bottom:1px solid #1f2937; font-family:monospace;">' + p.addr + '</td>' +
                '<td style="padding:5px 6px; text-align:center; border-bottom:1px solid #1f2937;">' + _ppStatusChip(p.status) + '</td>' +
                '<td style="padding:5px 6px; text-align:right; border-bottom:1px solid #1f2937; color:#9ca3af;">' + lat + '</td>' +
                '<td style="padding:5px 6px; text-align:center; border-bottom:1px solid #1f2937; color:#6b7280;">' + lastCheck + '</td>' +
                '<td style="padding:5px 6px; text-align:center; border-bottom:1px solid #1f2937;">' +
                    '<button onclick="ppRemove(\\'' + p.addr + '\\')" style="padding:2px 8px; font-size:11px;">🗑</button> ' +
                    '<button onclick="ppBurn(\\'' + p.addr + '\\')" style="padding:2px 8px; font-size:11px; background:#7f1d1d;">🚫</button>' +
                '</td></tr>';
        }).join('');
        body.innerHTML = rows || '<tr><td colspan="5" style="text-align:center; padding:20px; color:#6b7280;">Пул пока пуст — скрипт качает первые прокси...</td></tr>';
    } catch (e) { /* polling */ }
}

async function daUpdate() {
    try {
        const pRes = await fetch('/api/parser_state');
        const p = await pRes.json();
        document.getElementById('pStartBtn').disabled = p.running;
        document.getElementById('pStopBtn').disabled = !p.running;
        document.getElementById('pFound').textContent = p.found;
        document.getElementById('pStat').textContent = 'в блокноте: ' + p.notebook_count;
        renderLog('pLog', p.logs);
    } catch (e) { /* polling */ }
    try {
        const sRes = await fetch('/api/sender_state');
        const s = await sRes.json();
        document.getElementById('sStartBtn').disabled = s.running;
        document.getElementById('sStopBtn').disabled = !s.running;
        document.getElementById('sSent').textContent = s.sent;
        document.getElementById('sNotebookCount').textContent = s.notebook_count;
        document.getElementById('sBlacklistCount').textContent = s.blacklisted;
        document.getElementById('sStat').textContent = 'в пуле аккаунтов: ' + s.pool_count;
        document.getElementById('sPoolCount').textContent = s.pool_count;
        renderLog('sLog', s.logs);
    } catch (e) { /* polling */ }
    await ppUpdate();
}

window.__daServerSettings = /*__DA_SERVER_SETTINGS__*/null;
daRestoreState();
daToggleMailDomain();
setInterval(daUpdate, 1000);
daUpdate();

window.addEventListener('beforeunload', daSaveState);
window.addEventListener('pagehide', daSaveState);
document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'hidden') daSaveState();
});
document.querySelectorAll('textarea, input[type=text], input[type=number], select').forEach(el => {
    el.addEventListener('input', daSaveState);
});
document.querySelectorAll('input[type=checkbox]').forEach(el => {
    el.addEventListener('change', daSaveState);
});
// beforeunload alone is unreliable for a window closed abruptly (task-killed
// process, OS shutdown, some browsers skip it outright) — a periodic save is
// a cheap safety net so at most a few seconds of edits are ever at risk,
// regardless of how the app gets closed.
setInterval(daSaveState, 3000);
</script>
</body>
</html>
"""


def build_html_page():
    settings_json = "null"
    try:
        with open(DA_SETTINGS_FILE, "r", encoding="utf-8") as f:
            raw = f.read().strip()
            if raw:
                json.loads(raw)
                settings_json = raw
    except Exception:
        pass
    return HTML_PAGE.replace("/*__DA_SERVER_SETTINGS__*/null", settings_json)


class Handler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

    def do_GET(self):
        _ensure_proxy_pool_started()
        if self.path == "/":
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
            self.end_headers()
            self.wfile.write(build_html_page().encode("utf-8"))
        elif self.path.startswith("/api/parser_state"):
            with parser_lock:
                payload = {
                    "running": parser_state["running"],
                    "found": parser_state["found"],
                    "logs": parser_state["logs"][-LOG_TAIL_SENT:],
                }
            payload["notebook_count"] = len(read_notebook())
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps(payload).encode("utf-8"))
        elif self.path.startswith("/api/sender_state"):
            with sender_lock:
                payload = {
                    "running": sender_state["running"],
                    "sent": sender_state["sent"],
                    "logs": sender_state["logs"][-LOG_TAIL_SENT:],
                }
            payload["notebook_count"] = len(read_notebook())
            load_blacklist()
            with blacklist_lock:
                payload["blacklisted"] = len(blacklist_cache)
            payload["pool_count"] = account_pool_size()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps(payload).encode("utf-8"))
        elif self.path.startswith("/api/pxc_state"):
            with pxc_log_lock:
                logs = pxc_log_lines[-LOG_TAIL_SENT:]
            with pxc_cache_lock:
                alive_count = len(pxc_alive_cache)
                dead_count = len(pxc_dead_cache)
            state = {
                "alive_count": alive_count,
                "dead_count": dead_count,
                "is_checking": pxc_is_checking,
                "is_rechecking_alive": pxc_is_rechecking_alive,
                "continuous_recheck": pxc_continuous_event.is_set(),
                "logs": logs,
            }
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps(state).encode("utf-8"))
        elif self.path.startswith("/api/pxc_alive_proxies"):
            with pxc_cache_lock:
                proxies = sorted(pxc_alive_cache)
            self.send_response(200)
            self.send_header("Content-Type", "text/plain")
            self.end_headers()
            self.wfile.write("\n".join(proxies).encode("utf-8"))
        elif self.path == "/api/load_settings":
            settings_json = "null"
            try:
                with open(DA_SETTINGS_FILE, "r", encoding="utf-8") as f:
                    raw = f.read().strip()
                    if raw:
                        json.loads(raw)
                        settings_json = raw
            except Exception:
                pass
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(settings_json.encode("utf-8"))
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        _ensure_proxy_pool_started()
        length = int(self.headers.get("Content-Length", 0))
        raw = self.rfile.read(length) if length else b""
        try:
            payload = json.loads(raw.decode("utf-8")) if raw else {}
        except Exception:
            payload = {}

        if self.path == "/api/parser_start":
            cookies = payload.get("cookies") or ""
            feed_url = payload.get("feed_url") or ""
            threads = int(payload.get("threads") or 1)
            proxy_text = payload.get("proxy") or ""
            use_live_proxies = bool(payload.get("use_live_proxies"))
            scroll_max_pages = max(0, int(payload.get("scroll_max_pages") or 0))
            ignore_blacklist = bool(payload.get("ignore_blacklist"))
            auto_register_if_dead = bool(payload.get("auto_register_if_dead"))
            search_illustrations_only = bool(payload.get("search_illustrations_only"))

            # Claim "running" here, before the auto-register step below —
            # not after it, and not left to parser_worker itself. Confirmed
            # live: registration (up to 5 IP-rotation attempts against a
            # flaky temp-mail provider) can take minutes, and leaving the
            # claim that long unset meant parser_state["running"] stayed
            # False the whole time — the Start button never disabled, so an
            # impatient second click fired a second, fully independent
            # registration racing the first one's (interleaved log lines,
            # temp-mail accounts burned for nothing).
            with parser_lock:
                if parser_state["running"]:
                    response = {"ok": False, "error": "Парсер уже запущен"}
                    already_running = True
                else:
                    parser_state["running"] = True
                    already_running = False
            if already_running:
                pass
            else:
                response = {"ok": True}
                if auto_register_if_dead:
                    # Runs synchronously (ThreadingHTTPServer gives this
                    # request its own thread) so the possibly-fresh cookies
                    # can be reported back and dropped into the GUI's cookie
                    # field before parser_worker (which reads `cookies` once
                    # at startup) is even spawned.
                    cookies, was_replaced, reg_err = ensure_working_da_cookies(cookies, proxy_text)
                    if was_replaced:
                        if cookies.strip():
                            response["cookies"] = cookies
                            parser_log("♻️ Аккаунт парсера был мёртв/пуст — зарегистрирован новый, куки обновлены")
                        else:
                            response = {"ok": False, "error": f"Не удалось авто-зарегистрировать аккаунт: {reg_err}"}
                if response.get("ok"):
                    threading.Thread(target=parser_worker,
                                     args=(feed_url, cookies, threads, proxy_text, use_live_proxies,
                                           scroll_max_pages, ignore_blacklist, search_illustrations_only),
                                     daemon=True).start()
                else:
                    # Registration failed before parser_worker could take
                    # ownership of the flag via its own finally-block — release
                    # it here so the next Start attempt isn't locked out forever.
                    with parser_lock:
                        parser_state["running"] = False

        elif self.path == "/api/parser_stop":
            with parser_lock:
                if parser_state.get("stop"):
                    parser_state["stop"].set()
            response = {"ok": True}

        elif self.path == "/api/register_account":
            # Same one-account registration the sender's auto-register uses,
            # just triggered manually and handed straight to the parser's
            # cookie field instead of staying inside a running worker.
            # Runs synchronously — ThreadingHTTPServer gives this request its
            # own thread, so it doesn't block the rest of the app.
            proxy_text = payload.get("proxy") or ""
            username_template = payload.get("username_template") or "Verification-XXXXXXX"
            reg_mail_prov = payload.get("mail_provider") or None
            reg_mail_domain = payload.get("mail_domain") or None
            if payload.get("mailtd_token"):
                mailtd_set_token(payload["mailtd_token"])
            if payload.get("smailpro_2captcha_key"):
                smailpro_set_2captcha_key(payload["smailpro_2captcha_key"])
            session, csrf_token, err, _confirmed, _ = da_fresh_account_session(
                proxy_text, username_template, None, "[Регистрация для парсера]",
                mail_provider=reg_mail_prov, mail_domain=reg_mail_domain)
            if session:
                response = {"ok": True, "cookies": session_cookies_to_text(session)}
            else:
                response = {"ok": False, "error": err}

        elif self.path == "/api/open_browser_with_proxy":
            # Fire-and-forget — the browser window stays open until the user
            # closes it themselves, so this can't run on the request thread
            # (it would hold the HTTP connection open for the whole session).
            proxy_text = payload.get("proxy") or ""
            threading.Thread(target=open_browser_with_proxy, args=(proxy_text,), daemon=True).start()
            response = {"ok": True}

        elif self.path == "/api/sender_start":
            cookies = payload.get("cookies") or ""
            comment_text = payload.get("comment_text") or ""
            threads = int(payload.get("threads") or 1)
            comment_delay = max(0.0, float(payload.get("comment_delay") or 0))
            ignore_blacklist = bool(payload.get("ignore_blacklist"))
            csrf_token = payload.get("csrf_token") or ""
            proxy_text = payload.get("proxy") or ""
            dry_run = bool(payload.get("dry_run"))
            use_live_proxies = bool(payload.get("use_live_proxies"))
            invis_char = payload.get("invis_char") or ""
            invis_count = max(0, int(payload.get("invis_count") or 0))
            shortener = payload.get("shortener") or ""
            verify_comment = bool(payload.get("verify_comment", True))
            attach_image = bool(payload.get("attach_image"))
            image_filename = payload.get("image_filename") or "image.png"
            image_data_b64 = payload.get("image_data") or ""
            photo_link = bool(payload.get("photo_link"))
            proxy_for_comments = bool(payload.get("proxy_for_comments", True))
            auto_register = bool(payload.get("auto_register"))
            username_template = payload.get("username_template") or ""
            avatar_data_b64 = payload.get("avatar_data") or ""
            image_bytes = None
            if attach_image and image_data_b64:
                try:
                    image_bytes = base64.b64decode(image_data_b64)
                except Exception:
                    image_bytes = None
            avatar_bytes = None
            if auto_register and avatar_data_b64:
                try:
                    avatar_bytes = base64.b64decode(avatar_data_b64)
                except Exception:
                    avatar_bytes = None
            s_mail_provider = payload.get("mail_provider") or None
            s_mail_domain = payload.get("mail_domain") or None
            uniqueify_text = bool(payload.get("uniqueify_text"))
            send_random_after_spam = bool(payload.get("send_random_after_spam"))
            delete_special_comments = bool(payload.get("delete_special_comments"))
            reupload_image = bool(payload.get("reupload_image"))
            single_comment = bool(payload.get("single_comment"))
            fallback_letters = bool(payload.get("fallback_letters"))
            if payload.get("mailtd_token"):
                mailtd_set_token(payload["mailtd_token"])
            if payload.get("smailpro_2captcha_key"):
                smailpro_set_2captcha_key(payload["smailpro_2captcha_key"])
            threading.Thread(target=sender_worker,
                             args=(cookies, comment_text, threads, ignore_blacklist,
                                   csrf_token, proxy_text, dry_run, use_live_proxies,
                                   invis_char, invis_count, shortener, verify_comment,
                                   attach_image, image_bytes, image_filename, photo_link,
                                   auto_register, username_template, avatar_bytes,
                                   proxy_for_comments, s_mail_provider, comment_delay, s_mail_domain,
                                   uniqueify_text, send_random_after_spam, delete_special_comments,
                                   reupload_image, single_comment, fallback_letters),
                             daemon=True).start()
            response = {"ok": True}

        elif self.path == "/api/sender_stop":
            with sender_lock:
                if sender_state.get("stop"):
                    sender_state["stop"].set()
            response = {"ok": True}

        elif self.path == "/api/open":
            which = payload.get("which", "blacklist")
            if which == "notebook":
                path = NOTEBOOK_FILE
            elif which == "search_ranking":
                path = write_search_query_ranking_file()
            else:
                path = BLACKLIST_FILE
            ok, info = open_file(path)
            response = {"ok": ok, "info": info}

        elif self.path == "/api/clear_blacklist":
            clear_blacklist()
            sender_log("Блеклист очищен")
            response = {"ok": True}

        elif self.path == "/api/reset_account_pool":
            clear_account_pool()
            sender_log("🗑️ Пул сохранённых аккаунтов очищен — следующий запуск начнёт с регистрации новых")
            response = {"ok": True}

        elif self.path == "/api/blacklist_restore":
            username = (payload.get("username") or "").strip()
            if not username:
                response = {"ok": False, "error": "username пустой"}
            else:
                urls = remove_from_blacklist(username)
                if urls:
                    append_notebook(urls)
                sender_log(f"↩️ {username} убран из блеклиста"
                           + (f", возвращено в блокнот: {len(urls)}" if urls else ", сохранённых ссылок не было"))
                response = {"ok": True, "restored": len(urls)}

        elif self.path == "/api/clear_notebook":
            clear_notebook()
            parser_log("Блокнот очищен")
            response = {"ok": True}

        elif self.path == "/api/pxc_check":
            proxies_text = payload.get("proxies", "")
            thread_count = max(1, int(payload.get("thread_count", 5)))
            proxy_list = [p.strip() for p in proxies_text.split("\n") if p.strip()]
            if proxy_list:
                pxc_start_check(proxy_list, thread_count)
                response = {"ok": True}
            else:
                response = {"ok": False, "error": "Не указаны прокси"}

        elif self.path == "/api/pxc_stop_check":
            pxc_stop_check_event.set()
            pxc_log("Остановка проверки...")
            response = {"ok": True}

        elif self.path == "/api/pxc_start_recheck":
            thread_count = max(1, int(payload.get("thread_count", 3)))
            threading.Thread(target=pxc_recheck_alive_worker, args=(thread_count,),
                             daemon=True).start()
            response = {"ok": True}

        elif self.path == "/api/pxc_continuous_recheck":
            thread_count = max(1, int(payload.get("thread_count", 3)))
            on = bool(payload.get("on"))
            proxies_text = payload.get("proxies", "")
            pxc_set_continuous(on, thread_count, proxies_text)
            response = {"ok": True}

        elif self.path == "/api/pxc_clear_alive":
            response = {"ok": True, "removed": pxc_clear_alive()}

        elif self.path == "/api/pxc_prune_dead":
            response = {"ok": True, "removed": pxc_prune_dead()}

        # ─── Autonomous proxy pool endpoints ──────────────────────────────
        elif self.path == "/api/proxy_pool_state":
            response = {"ok": True, "stats": PROXY_POOL.stats(),
                        "proxies": PROXY_POOL.get_all(limit=int(payload.get("limit") or 300))}

        elif self.path == "/api/proxy_pool_refresh":
            threading.Thread(target=PROXY_POOL._fetch_proxies, daemon=True).start()
            response = {"ok": True}

        elif self.path == "/api/proxy_pool_clear_dead":
            PROXY_POOL.clear_dead()
            response = {"ok": True}

        elif self.path == "/api/proxy_pool_clear_all":
            PROXY_POOL.clear_all()
            response = {"ok": True}

        elif self.path == "/api/proxy_pool_remove":
            PROXY_POOL.remove(payload.get("addr") or "")
            response = {"ok": True}

        elif self.path == "/api/proxy_pool_burn":
            PROXY_POOL.mark_burned(payload.get("addr") or "")
            response = {"ok": True}

        elif self.path == "/api/proxy_pool_add":
            added = 0
            for line in (payload.get("proxies") or "").splitlines():
                line = line.strip()
                if not line:
                    continue
                if line.lower().startswith(("http://", "https://", "socks4://", "socks5://")):
                    line = line.split("://", 1)[1]
                if PROXY_POOL.add_manual(line):
                    added += 1
            response = {"ok": True, "added": added}

        elif self.path == "/api/save_settings":
            try:
                os.makedirs(os.path.dirname(DA_SETTINGS_FILE), exist_ok=True)
                with open(DA_SETTINGS_FILE, "w", encoding="utf-8") as f:
                    json.dump(payload, f, ensure_ascii=False)
                response = {"ok": True}
            except Exception as e:
                response = {"ok": False, "error": str(e)}

        else:
            self.send_response(404)
            self.end_headers()
            return

        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(response).encode("utf-8"))


def _kill_old_instance(port):
    """Kill any existing process listening on the given port (Windows).

    A prior run whose console window got closed via the X button (or that
    just hung) can leave its python.exe holding the port — the run script's
    own readiness-poll would then see *that* old, pre-restart process
    answering and open the browser against it, silently discarding every
    code change (and any impression that a "restart" actually restarted
    anything) while the new process fails to bind and dies unnoticed.
    """
    import socket
    import subprocess
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.settimeout(1)
        sock.connect(("127.0.0.1", port))
        sock.close()
    except (ConnectionRefusedError, OSError):
        return
    try:
        out = subprocess.check_output(
            f'netstat -ano | findstr ":{port} "',
            shell=True, text=True, stderr=subprocess.DEVNULL)
        pids = set()
        for line in out.strip().splitlines():
            parts = line.split()
            if len(parts) >= 5 and "LISTENING" in line:
                pids.add(parts[-1])
        for pid in pids:
            if pid and pid != "0":
                subprocess.call(f"taskkill /F /PID {pid}",
                                shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                print(f"Закрыт предыдущий экземпляр (PID {pid})")
    except Exception:
        pass
    time.sleep(0.5)


if __name__ == "__main__":
    _kill_old_instance(PORT)
    load_blacklist()
    pxc_load_alive()
    pxc_load_dead()
    _ensure_proxy_pool_started()
    server = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    print(f"DeviantArt Commenter running at http://localhost:{PORT}")
    server.serve_forever()
