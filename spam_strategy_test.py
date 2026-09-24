"""Big autonomous test: register N accounts per strategy, try to land up to
5 comments with each, log everything to a live JSONL + a live-updated MD
summary so we can see which text-uniquification strategy actually slips past
DA's spam filter for longer than 1 comment.

Uses the app's own registration + posting functions to stay in sync with
whatever the sender does in production. Reads live proxies from the running
PROXY_POOL, so it only fires when the pool is warmed up.
"""
import json, os, random, string, sys, threading, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

# Importing the main module boots the proxy pool as a side effect (module load
# starts PROXY_POOL.start()), so by the time we reach the loop below the pool
# is already spinning up its 120 checkers in the background.
import deviantart_commenter_gui as da

# Cap the inner MAX_IP_ATTEMPTS. Free pool proxies don't rotate their outgoing
# IP the way Bright Data-style sessid providers do, so 50 attempts on one bad
# proxy would burn 50 temp emails. 3 means: if this proxy doesn't yield an
# account in 3 tries, give up and let the test's outer loop grab a fresh one.
da.MAX_IP_ATTEMPTS_OVERRIDE = 3

BASE_TEXT = (
    "A wiki is a form of hypertext publication on the internet which is "
    "collaboratively edited and managed by its audience directly through a "
    "web browser. A typical wiki contains multiple pages that can either be "
    "edited by the public or any organization. The name derives from the "
    "first user-editable website called WikiWikiWeb — wiki being a Hawaiian "
    "word meaning quick. Wikis are enabled by wiki software, otherwise known "
    "as wiki engines. Wiki engines are a type of content management system, "
    "but they differ from most other such systems, including blog software, "
    "in that the content is created without any defined owner or leader, and "
    "wikis have little inherent structure, allowing structure to emerge "
    "according to the needs of the users."
)

OUT_DIR = Path(__file__).resolve().parent / "spam_test_results"
OUT_DIR.mkdir(exist_ok=True)
RUN_STAMP = time.strftime("%Y%m%d_%H%M%S")
RESULTS_JSONL = OUT_DIR / f"results_{RUN_STAMP}.jsonl"
SUMMARY_MD = OUT_DIR / f"summary_{RUN_STAMP}.md"

_log_lock = threading.Lock()


def log_line(msg):
    stamp = time.strftime("%H:%M:%S")
    line = f"[{stamp}] {msg}"
    print(line, flush=True)


def log_result(entry):
    entry["ts"] = time.time()
    entry["ts_iso"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    with _log_lock:
        with open(RESULTS_JSONL, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry, ensure_ascii=False) + "\n")


def load_targets():
    """Load target URLs from the main script's notebook, extract dev_id."""
    notebook = da.BASE_DIR / "deviantart_posts.txt"
    if not notebook.exists():
        return []
    targets = []
    seen = set()
    with open(notebook, "r", encoding="utf-8") as f:
        for line in f:
            raw = line.strip()
            if not raw:
                continue
            m = da.DEVIATION_LINK_RE.search(raw)
            if not m:
                continue
            username, slug, dev_id = m.group(1), m.group(2), m.group(3)
            key = int(dev_id)
            if key in seen:
                continue
            seen.add(key)
            targets.append({"username": username, "dev_id": int(dev_id),
                            "url": m.group(0)})
    random.shuffle(targets)
    return targets


# ─── Strategies ────────────────────────────────────────────────────────────
# Each strategy is (name, transform_fn). transform_fn takes (base_text,
# target_username, seq_index, base_text_for_seed) and returns the text to
# actually send.

def _rand_id(n=8):
    return "".join(random.choices(string.ascii_uppercase + string.digits, k=n))


def _scatter_extra_spaces(text, extra=15):
    """Insert `extra` random single spaces at word boundaries."""
    words = text.split(" ")
    for _ in range(extra):
        if len(words) < 2:
            break
        pos = random.randint(1, len(words) - 1)
        words.insert(pos, "")  # empty element = extra space when re-joined
    return " ".join(words)


def _sentence_reorder(text):
    """Split into sentences, keep first, shuffle the rest."""
    parts = [p.strip() for p in text.replace("!", ".").replace("?", ".").split(".") if p.strip()]
    if len(parts) < 3:
        return text
    head = parts[0]
    rest = parts[1:]
    random.shuffle(rest)
    return head + ". " + ". ".join(rest) + "."


def _add_paragraph_breaks(text):
    """Insert 1-3 random paragraph breaks."""
    words = text.split(" ")
    if len(words) < 20:
        return text
    n_breaks = random.randint(1, 3)
    for _ in range(n_breaks):
        pos = random.randint(10, len(words) - 10)
        words[pos] = words[pos] + "\n\n"
    return " ".join(words)


def _inject_emoji(text, count=2):
    """Sprinkle emoji at random word boundaries."""
    emojis = ["✨", "🌸", "🎨", "💫", "🌿", "🌺", "🎭", "🌊", "🍃", "⭐"]
    words = text.split(" ")
    for _ in range(count):
        if len(words) < 2:
            break
        pos = random.randint(1, len(words) - 1)
        words.insert(pos, random.choice(emojis))
    return " ".join(words)


# Focus round: only strategies that DON'T substitute Latin codepoints. The
# earlier run proved homoglyph replacement gets silently shadow-banned (DA
# accepts the post via the API but hides it from the thread), so re-testing
# those variants would just burn accounts. What's left to learn: does DA's
# spam filter key on the exact byte hash of the base text? If so, PREFIXING
# something unique per send (username, request ID, extra whitespace, sentence
# reorder) should let more comments land visibly.
STRATEGIES = [
    ("prefix_username_plain",
     lambda t, u, i: f"Hi @{u}, {t}"),

    ("request_id_header_plain",
     lambda t, u, i: f"[Ref #{_rand_id(6)}-{u[:3].upper()}]\n\n{t}"),

    ("scattered_spaces_plain",
     lambda t, u, i: _scatter_extra_spaces(t, 15)),

    ("sentence_reorder_plain",
     lambda t, u, i: _sentence_reorder(t)),

    ("paragraph_breaks_plain",
     lambda t, u, i: _add_paragraph_breaks(t)),

    ("emoji_plain",
     lambda t, u, i: _inject_emoji(t, 3)),

    ("prefix_username_plus_request_id",
     lambda t, u, i: f"Hi @{u},\n\n[Ref #{_rand_id(6)}]\n\n{t}"),
]

ACCOUNTS_PER_STRATEGY = 2
MSGS_PER_ACCOUNT = 3
EMAIL_CONFIRM_TIMEOUT = 180  # 3 min — Outlook/temp.tf sometimes lags
USERNAME_TEMPLATE = "Verification-XXXXXXX"


def wait_for_pool_ready(min_alive=30, timeout=120):
    """Block until the pool has at least `min_alive` proxies verified or we
    time out. Cheap sanity check so the test doesn't hammer no-proxy while
    the pool is still cold."""
    t0 = time.time()
    while time.time() - t0 < timeout:
        s = da.PROXY_POOL.stats()
        if s["alive"] >= min_alive:
            log_line(f"Пул готов: {s['alive']} живых, {s['checkCount']} проверок")
            return True
        log_line(f"Жду прогрева пула ({s['alive']}/{min_alive} живых, {s['checkCount']} проверок)...")
        time.sleep(5)
    return False


def test_one_account(strategy_name, transform_fn, targets_iter, acct_idx):
    """Register one account, try up to MSGS_PER_ACCOUNT sends, log every send.
    Returns count of verified successful sends (the metric that matters —
    if a strategy lets us land 5, that beats the baseline landing 1)."""
    acct_id = f"{strategy_name}#{acct_idx + 1}"

    # Outer proxy-rotation loop. Free-pool proxies fail 90%+ of the time on
    # the /join/ POST (CF 403), so we grab a new fastest-available one on
    # each attempt. Inner cap MAX_IP_ATTEMPTS_OVERRIDE=3 means the module
    # burns at most 3 emails per proxy before giving back control here to
    # try the next.
    session, csrf, err, confirmed_event, proxy_addr = None, None, "", None, ""
    tried_addrs = []
    for outer_try in range(1, 9):
        proxy_addr = da.PROXY_POOL.get_best(reserve=True, unique_ip=True) or ""
        if proxy_addr and proxy_addr in tried_addrs:
            da.PROXY_POOL.release(proxy_addr)
            proxy_addr = ""
        if proxy_addr:
            tried_addrs.append(proxy_addr)
            log_line(f"[{acct_id}] Попытка #{outer_try}: прокси {proxy_addr}")
        else:
            log_line(f"[{acct_id}] Попытка #{outer_try}: без прокси (пул пуст)")

        t0 = time.time()
        try:
            session, csrf, err, confirmed_event = da.da_fresh_account_session(
                proxy_text=proxy_addr,
                username_template=USERNAME_TEMPLATE,
                avatar_bytes=None,
                log_prefix=f"[{acct_id}]",
                keep_proxy_for_comments=False,
                mail_provider="temptf",
                mail_domain=None,
                stop_event=None,
            )
        except Exception as e:
            log_line(f"[{acct_id}] Исключение при регистрации: {str(e)[:150]}")
            session, csrf, err = None, None, f"exception: {str(e)[:150]}"
            confirmed_event = None
        reg_time = round(time.time() - t0, 1)

        if session and csrf:
            log_result({"strategy": strategy_name, "acct_idx": acct_idx, "acct_id": acct_id,
                        "phase": "register", "ok": True, "reg_seconds": reg_time,
                        "proxy": proxy_addr, "outer_try": outer_try})
            log_line(f"[{acct_id}] ✅ Аккаунт готов за {reg_time}с (попытка #{outer_try})")
            break

        log_line(f"[{acct_id}] Попытка #{outer_try} упала за {reg_time}с: {(err or '')[:80]}")
        # Release + mark bad so pool doesn't hand it right back to us
        if proxy_addr:
            da.PROXY_POOL.mark_bad(proxy_addr, ttl_seconds=600)
        if not proxy_addr:
            # Home IP failed too — no point in more tries this session
            break

    if not session or not csrf:
        log_result({"strategy": strategy_name, "acct_idx": acct_idx, "acct_id": acct_id,
                    "phase": "register", "ok": False, "err": err,
                    "outer_tries": len(tried_addrs)})
        log_line(f"[{acct_id}] ❌ Регистрация сдалась после {len(tried_addrs)} прокси")
        return 0

    # Comment posting requires a verified email (DA returns
    # `unverified_account` otherwise — seen live in prior iteration where 5
    # sends all failed on the same account because we timed out at 60s and
    # posted anyway). Wait longer here, then bail if the email really didn't
    # confirm — sending to `unverified_account` gates the whole test.
    if confirmed_event and not confirmed_event.wait(timeout=EMAIL_CONFIRM_TIMEOUT):
        log_line(f"[{acct_id}] Email не подтвердился за {EMAIL_CONFIRM_TIMEOUT}с — пропускаю аккаунт")
        log_result({"strategy": strategy_name, "acct_idx": acct_idx, "acct_id": acct_id,
                    "phase": "email_timeout"})
        da.PROXY_POOL.release(proxy_addr) if proxy_addr else None
        return 0

    verified_sends = 0
    for msg_idx in range(1, MSGS_PER_ACCOUNT + 1):
        try:
            target = next(targets_iter)
        except StopIteration:
            log_line(f"[{acct_id}] Кончились цели")
            break

        try:
            text = transform_fn(BASE_TEXT, target["username"], msg_idx)
        except Exception as e:
            log_line(f"[{acct_id}] Стратегия '{strategy_name}' упала: {str(e)[:100]}")
            break

        log_line(f"[{acct_id}] Отправка #{msg_idx} → {target['username']} "
                 f"(текст: {text[:50].replace(chr(10),' ')}...)")

        try:
            ok, cerr, comment_id = da.da_post_comment(
                session, csrf, target["dev_id"], text, target["url"], None)
        except Exception as e:
            ok, cerr, comment_id = False, f"exception: {str(e)[:150]}", None

        entry = {
            "strategy": strategy_name, "acct_idx": acct_idx, "acct_id": acct_id,
            "phase": "send", "msg_idx": msg_idx,
            "target": target["username"], "target_url": target["url"],
            "sent_ok": bool(ok), "err": cerr[:200] if cerr else "",
            "is_spam": bool(cerr and da.is_spam_error(cerr)),
        }

        if ok:
            verified, verify_msg = da.verify_comment_posted(
                target["dev_id"], comment_id, "", src_session=session)
            entry["verified"] = True if verified else (False if verified is False else None)
            entry["verify_msg"] = verify_msg[:150] if verify_msg else ""
            log_line(f"[{acct_id}] ✓ Отправка #{msg_idx} — верификация: "
                     f"{entry['verified']} ({verify_msg[:60] if verify_msg else ''})")
            if verified is True:
                verified_sends += 1
        else:
            log_line(f"[{acct_id}] ✗ Отправка #{msg_idx} упала "
                     f"({'СПАМ' if entry['is_spam'] else 'др.ошибка'}): {(cerr or '')[:100]}")

        log_result(entry)

        # Bail early on spam — the account is likely flagged; any further
        # sends will just add noise to the log without new information.
        if not ok and entry["is_spam"]:
            log_result({"strategy": strategy_name, "acct_idx": acct_idx, "acct_id": acct_id,
                        "phase": "spam_bail", "verified_sends": verified_sends,
                        "msg_idx": msg_idx})
            break

        # Small jitter between sends so we're not machine-gun-punching the API
        time.sleep(random.uniform(2.0, 4.0))

    da.PROXY_POOL.release(proxy_addr) if proxy_addr else None
    log_result({"strategy": strategy_name, "acct_idx": acct_idx, "acct_id": acct_id,
                "phase": "acct_done", "verified_sends": verified_sends})
    log_line(f"[{acct_id}] Аккаунт закончил: {verified_sends} успешных верифицированных сообщений")
    return verified_sends


def rewrite_summary():
    """Read the JSONL, aggregate by strategy, write a live MD summary."""
    strategies = {}
    if not RESULTS_JSONL.exists():
        return
    with open(RESULTS_JSONL, "r", encoding="utf-8") as f:
        for line in f:
            try:
                e = json.loads(line)
            except Exception:
                continue
            s = e.get("strategy") or "?"
            strategies.setdefault(s, {"reg_ok": 0, "reg_fail": 0,
                                       "sends_attempted": 0, "sends_ok": 0,
                                       "verified": 0, "spam_bail_at": []})
            row = strategies[s]
            if e.get("phase") == "register":
                row["reg_ok" if e.get("ok") else "reg_fail"] += 1
            elif e.get("phase") == "send":
                row["sends_attempted"] += 1
                if e.get("sent_ok"):
                    row["sends_ok"] += 1
                if e.get("verified") is True:
                    row["verified"] += 1
            elif e.get("phase") == "spam_bail":
                row["spam_bail_at"].append(e.get("msg_idx", 0))

    with open(SUMMARY_MD, "w", encoding="utf-8") as f:
        f.write(f"# Spam-strategy test — {RUN_STAMP}\n\n")
        f.write(f"Base text (~90 words): `{BASE_TEXT[:80]}...`\n\n")
        f.write(f"- Accounts per strategy: **{ACCOUNTS_PER_STRATEGY}**\n")
        f.write(f"- Sends per account:     **up to {MSGS_PER_ACCOUNT}**\n")
        f.write(f"- Live JSONL:            `{RESULTS_JSONL.name}`\n\n")
        f.write("## Aggregated results\n\n")
        f.write("| Strategy | Reg OK | Sends | Verified | Avg spam-bail msg# | Verified/acct |\n")
        f.write("|---|---:|---:|---:|---:|---:|\n")
        rows = []
        for name, r in strategies.items():
            avg_bail = (sum(r["spam_bail_at"]) / len(r["spam_bail_at"])) if r["spam_bail_at"] else 0
            per_acct = (r["verified"] / r["reg_ok"]) if r["reg_ok"] else 0
            rows.append((name, r, avg_bail, per_acct))
        rows.sort(key=lambda x: (-x[3], -x[1]["verified"]))
        for name, r, avg_bail, per_acct in rows:
            f.write(f"| `{name}` | {r['reg_ok']} | {r['sends_attempted']} | "
                    f"{r['verified']} | {avg_bail:.1f} | {per_acct:.2f} |\n")
        f.write("\n_Higher `Verified/acct` = strategy survives longer before spam-lock._\n")


def main():
    log_line(f"START — {len(STRATEGIES)} стратегий × {ACCOUNTS_PER_STRATEGY} акка × до {MSGS_PER_ACCOUNT} сообщений")
    log_line(f"Режим: без прокси (home IP)")
    log_line(f"Результаты: {RESULTS_JSONL}")
    log_line(f"Сводка:     {SUMMARY_MD}")

    targets = load_targets()
    if not targets:
        log_line("Нет целей в блокноте — прерываю")
        return
    log_line(f"Загружено {len(targets)} целей из notebook")

    # Round-robin over targets across all strategies
    targets_pool = iter(targets * 20)  # plenty of headroom

    for s_idx, (name, fn) in enumerate(STRATEGIES):
        log_line(f"════ Стратегия {s_idx + 1}/{len(STRATEGIES)}: {name} ════")
        for acct_idx in range(ACCOUNTS_PER_STRATEGY):
            try:
                test_one_account(name, fn, targets_pool, acct_idx)
            except Exception as e:
                log_line(f"[{name}#{acct_idx+1}] Аккаунт упал с исключением: {str(e)[:150]}")
                log_result({"strategy": name, "acct_idx": acct_idx,
                            "phase": "exception", "err": str(e)[:200]})
            rewrite_summary()
            # Longer sleep between accounts so DA's per-IP anti-bot cooldown
            # gets a chance to relax — 45-90s spacing lets us fit more
            # successful regs into one session than back-to-back does.
            sleep_s = random.uniform(45, 90)
            log_line(f"[{name}#{acct_idx+1}] Пауза {sleep_s:.0f}с перед следующим аккаунтом...")
            time.sleep(sleep_s)
        rewrite_summary()

    log_line(f"✅ ЗАВЕРШЕНО. Результаты: {RESULTS_JSONL}")
    log_line(f"   Сводка:                  {SUMMARY_MD}")


if __name__ == "__main__":
    main()
