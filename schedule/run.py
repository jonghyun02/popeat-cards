"""POP&EAT 예약 게시 — GitHub Actions(이미지 저장소 popeat-cards)에서 15분마다 실행한다. 표준 라이브러리만 쓴다.

이 파일이 원본이고, `cardnews schedule setup` 이 저장소의 schedule/run.py 로 복사한다 (저장소에서 직접 고치지 말 것).

하는 일:
- schedule/config.json 의 시간대마다 하루 한 번, 날짜로 정해지는 무작위 시각을 고른다 (앞 시각과 최소 간격을 지킴).
- 지난 시각 수보다 오늘(한국 시간) 올라간 게시물이 적고, 마지막 게시물과 최소 간격이 지났으면
  대기열(schedule/queue/<qid>.json, PC 의 cardnews 가 올림)에서 가장 먼저 예약된 것 하나를 올린다.
- 결과는 schedule/state/<qid>.json 에 적고 커밋·푸시한다 → PC 의 `cardnews schedule sync` 가 받아 기록한다.

두 번 게시하지 않는 장치:
- media_publish 를 보내기 전에 state 를 sending(creation_id·캡션 지문·보낸 시각)으로 커밋·푸시한다. 푸시가 안 되면 보내지 않는다.
  푸시한 뒤 대기열 파일이 그새 지워졌으면(PC 에서 예약 취소) 보내지 않고 canceled 로 적는다.
- sending 이 남아 있으면 새로 올리지 않고 먼저 확인한다: 컨테이너 상태 PUBLISHED 또는 최근 게시물에 같은 캡션 → published.
  둘 다 확인됐는데 없고 보낸 지 10분이 지났으면 not_published (다시 올릴 수 있음). 확인이 안 되면 그대로 두고 다음 실행에서 다시.
- 403 code 4(요청 한도·스팸 의심 2207051) 거절은 실제로 올라간 적이 있어(2026-10-04) 실패로 치지 않고 위 확인을 거친다.
- 워크플로 concurrency 로 한 번에 하나만 돈다.

토큰은 환경변수(IG_ACCESS_TOKEN, GitHub 비밀값)에서만 읽고 Authorization 헤더로만 보낸다. 출력에는 나오지 않게 가린다.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

KST = timezone(timedelta(hours=9))                  # 한국은 서머타임이 없어 고정 오프셋으로 충분
API = "https://graph.instagram.com/v25.0"
RAW = "https://raw.githubusercontent.com"
SETTLE_MIN = 10                                     # 보낸 뒤 이만큼 지나야 '게시 안 됨'으로 결론
CLOCK_SKEW_MIN = 10
MEDIA_LOOKUP = 25
CONTAINER_TTL_H = 24                                # 컨테이너는 만든 지 24시간이 지나면 만료
POLL_SEC, POLL_MAX_SEC = 60, 300                    # 컨테이너 상태: 문서 권장 1분에 한 번, 5분 이내
MAYBE_POSTED_CODES = {"4"}                          # 거절로 와도 올라갔을 수 있음
TRANSIENT_CODES = {"1", "2", "4", "17", "32", "613"}  # 일시 오류·한도: 실패로 적지 않고 다음 실행에서 다시
DEFAULT_CONFIG = {"windows": ["11:00-13:00", "15:00-18:00", "19:00-22:00"], "min_gap_min": 120}


class IGError(Exception):
    def __init__(self, msg: str, status: int | None = None, code=None, subcode=None):
        super().__init__(msg)
        self.status, self.code, self.subcode = status, code, subcode

    @property
    def rejected(self) -> bool:
        """API 가 확실히 거절함: 4xx + 오류 코드 (일시 오류 1·2 와 응답 없음은 빼고)."""
        return (self.status is not None and 400 <= self.status < 500
                and str(self.code) not in ("None", "", "1", "2"))


def redact(text: str, *secrets: str) -> str:
    for s in secrets:
        if s:
            text = text.replace(s, "***")
    return text


# --------------------------------------------------------------------------- 시각

def _hm(s: str) -> int:
    h, m = s.strip().split(":")
    return int(h) * 60 + int(m)


def parse_windows(windows: list[str]) -> list[tuple[int, int]]:
    out = []
    for w in windows:
        a, b = w.split("-")
        lo, hi = _hm(a), _hm(b)
        if not 0 <= lo <= hi <= 24 * 60:
            raise ValueError(f"시간대 형식 오류: {w}")
        out.append((lo, hi))
    return sorted(out)


def plan_slots(day: date, cfg: dict) -> list[datetime]:
    """그날의 게시 시각들 (한국 시간). 날짜로 정해지는 무작위라 15분마다 다시 계산해도 같다.
    시간대마다 하나씩, 앞 시각과 min_gap_min 분 이상 띄운다 (시간대가 좁아 못 띄우면 그 시간대 끝으로)."""
    rng = random.Random(f"popeat-{day.isoformat()}")
    gap = int(cfg.get("min_gap_min", 120))
    slots, prev = [], None
    for lo, hi in parse_windows(cfg.get("windows") or DEFAULT_CONFIG["windows"]):
        start = lo if prev is None else max(lo, prev + gap)
        start = min(start, hi)
        minute = rng.randint(start, hi)
        slots.append(datetime(day.year, day.month, day.day, tzinfo=KST) + timedelta(minutes=minute))
        prev = minute
    return slots


def ts(value) -> datetime | None:
    """인스타그램 timestamp(2026-09-27T03:00:05+0000) 또는 ISO 시각."""
    if not value:
        return None
    s = str(value).strip()
    s = re.sub(r"([+-]\d\d)(\d\d)$", r"\1:\2", s.replace("Z", "+00:00"))
    try:
        t = datetime.fromisoformat(s)
    except ValueError:
        return None
    return t if t.tzinfo else t.replace(tzinfo=timezone.utc)


def iso(t: datetime) -> str:
    return t.astimezone(timezone.utc).replace(microsecond=0).isoformat()


def caption_fp(text: str) -> str:
    """cardnews.publish.caption_fp 와 같아야 한다: NFC 정규화 후 공백을 모두 빼고 sha256 앞 16자."""
    return hashlib.sha256(re.sub(r"\s+", "", unicodedata.normalize("NFC", text or "")).encode("utf-8")).hexdigest()[:16]


# --------------------------------------------------------------------------- Graph API

def urllib_http(method: str, url: str, headers: dict, body: bytes | None) -> tuple[int, dict, bytes]:
    req = urllib.request.Request(url, data=body, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=30) as r:  # noqa: S310 - 고정된 https 주소만
            return r.status, dict(r.headers), r.read()
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers or {}), e.read() or b""


class Graph:
    def __init__(self, token: str, http=urllib_http, sleep=time.sleep):
        self.token, self.http, self.sleep = token, http, sleep

    def req(self, method: str, path: str, params: dict | None = None, data: dict | None = None) -> dict:
        url = f"{API}/{path.lstrip('/')}" + (f"?{urllib.parse.urlencode(params)}" if params else "")
        body = urllib.parse.urlencode(data).encode() if data is not None else None
        headers = {"Authorization": f"Bearer {self.token}"}
        if body is not None:
            headers["Content-Type"] = "application/x-www-form-urlencoded"
        try:
            status, _, raw = self.http(method, url, headers, body)
        except Exception as e:  # noqa: BLE001 - 연결 끊김·시간 초과: 처리됐는지 알 수 없음
            raise IGError(redact(f"인스타그램 API 연결 실패 ({type(e).__name__}): {e}", self.token)) from None
        try:
            out = json.loads(raw.decode("utf-8") or "{}")
        except ValueError:
            out = {}
        out = out if isinstance(out, dict) else {}
        if status >= 400 or "error" in out:
            err = out.get("error") if isinstance(out.get("error"), dict) else {}
            raise IGError(redact(f"인스타그램 API 오류 {status}: {err.get('message') or raw[:200]!r} "
                                 f"(code {err.get('code')}, subcode {err.get('error_subcode')})", self.token),
                          status=status, code=err.get("code"), subcode=err.get("error_subcode"))
        return out

    def me(self) -> dict:
        return self.req("GET", "me", {"fields": "user_id,username"})

    def limit(self, ig_id: str) -> tuple[int, int]:
        row = (self.req("GET", f"{ig_id}/content_publishing_limit", {"fields": "quota_usage,config"}).get("data")
               or [{}])[0]
        return int(row.get("quota_usage") or 0), int((row.get("config") or {}).get("quota_total") or 100)

    def recent(self, ig_id: str, limit: int = MEDIA_LOOKUP) -> tuple[list[dict], bool]:
        out = self.req("GET", f"{ig_id}/media", {"fields": "id,caption,timestamp,permalink", "limit": str(limit)})
        if not isinstance(out.get("data"), list):
            raise IGError("최근 게시물 목록 응답에 data 가 없음")
        return [m for m in out["data"] if isinstance(m, dict)], not (out.get("paging") or {}).get("next")

    def status(self, cid: str) -> str:
        return str(self.req("GET", cid, {"fields": "status_code"}).get("status_code") or "")

    def permalink(self, mid: str) -> str:
        return str(self.req("GET", mid, {"fields": "permalink"}).get("permalink") or "")

    def create_item(self, ig_id: str, url: str) -> str:
        return str(self.req("POST", f"{ig_id}/media", data={"image_url": url, "is_carousel_item": "true"})["id"])

    def create_carousel(self, ig_id: str, children: list[str], caption: str) -> str:
        return str(self.req("POST", f"{ig_id}/media", data={"media_type": "CAROUSEL", "children": ",".join(children),
                                                            "caption": caption})["id"])

    def create_single(self, ig_id: str, url: str, caption: str) -> str:
        return str(self.req("POST", f"{ig_id}/media", data={"image_url": url, "caption": caption})["id"])

    def wait_ready(self, cid: str) -> None:
        waited = 0
        while True:
            st = self.status(cid)
            if st in ("FINISHED", "PUBLISHED"):
                return
            if st in ("ERROR", "EXPIRED"):
                raise IGError(f"게시 컨테이너 상태 {st} — 이미지 주소·형식을 확인하세요", status=400, code="container")
            if waited >= POLL_MAX_SEC:
                raise IGError(f"게시 컨테이너가 {POLL_MAX_SEC}초 안에 준비되지 않음 (상태 {st or '없음'})")
            self.sleep(POLL_SEC)
            waited += POLL_SEC

    def publish(self, ig_id: str, cid: str) -> str:
        mid = self.req("POST", f"{ig_id}/media_publish", data={"creation_id": cid}).get("id")
        if not mid:
            raise IGError("게시 응답에 게시물 ID 가 없음")
        return str(mid)


def reconcile(g: Graph, ig_id: str, st: dict, now: datetime) -> tuple[str, dict]:
    """보낸(sending) 게시 요청이 올라갔는지 확인한다. 게시는 하지 않는다.
    → ('published', 게시물) / ('not_published', {}) / ('wait', {}) / ('unknown', {'reason'})"""
    sent = ts(st.get("sent_at")) or now
    since = sent - timedelta(minutes=CLOCK_SKEW_MIN)
    errors, status = [], ""
    try:
        status = g.status(st["creation_id"])
    except IGError as e:
        errors.append(f"컨테이너 상태 확인 실패 ({e})")
    match, covered = None, False
    try:
        items, complete = g.recent(ig_id)
        times = [ts(m.get("timestamp")) for m in items]
        for m, t in zip(items, times):
            if t and t >= since and caption_fp(str(m.get("caption") or "")) == st.get("caption_fp"):
                match = m
        covered = complete or any(t and t < since for t in times)
    except IGError as e:
        errors.append(f"최근 게시물 확인 실패 ({e})")
    if status == "PUBLISHED" or match:
        return "published", match or {}
    if not status and covered and len(errors) <= 1 and now - sent > timedelta(hours=CONTAINER_TTL_H):
        return "not_published", {}          # 컨테이너는 하루 지나면 못 읽음 — 목록으로 확인됐고 없으면 대기열이 막히지 않게
    if errors or not status:
        return "unknown", {"reason": "; ".join(errors) or "컨테이너 상태 응답이 비어 있음"}
    if not covered:
        return "unknown", {"reason": f"최근 게시물 {MEDIA_LOOKUP}개가 보낸 때까지 거슬러 올라가지 않음"}
    if now - sent < timedelta(minutes=SETTLE_MIN):
        return "wait", {}
    return "not_published", {}


# --------------------------------------------------------------------------- 저장소

class Repo:
    """체크아웃한 popeat-cards 저장소. 커밋·푸시는 state 파일만 (PC 쪽은 사진·queue 만 커밋하므로 겹치지 않음)."""

    def __init__(self, root: Path, run=subprocess.run):
        self.root, self._run = root, run

    def git(self, *args: str) -> str:
        r = self._run(["git", *args], cwd=str(self.root), capture_output=True, text=True, encoding="utf-8",
                      errors="replace")
        if r.returncode != 0:
            raise RuntimeError(f"git {args[0]} 실패: {(r.stderr or r.stdout).strip()[-300:]}")
        return r.stdout

    def head(self) -> str:
        return self.git("rev-parse", "HEAD").strip()

    def queue(self) -> dict[str, dict]:
        return _load_dir(self.root / "schedule" / "queue")

    def states(self) -> dict[str, dict]:
        return _load_dir(self.root / "schedule" / "state")

    def save_state(self, qid: str, st: dict, message: str) -> None:
        """state 하나를 적고 커밋·푸시. 다른 쪽이 먼저 푸시했으면 rebase 해서 다시 (경로가 겹치지 않음)."""
        p = self.root / "schedule" / "state" / f"{qid}.json"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(st, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        self.git("add", "--", p.relative_to(self.root).as_posix())
        self.git("commit", "-q", "-m", message)
        for i in range(4):
            try:
                self.git("push", "-q", "origin", "HEAD:main")
                return
            except RuntimeError:
                if i == 3:
                    raise
                self.git("pull", "-q", "--rebase", "origin", "main")


def _load_dir(d: Path) -> dict[str, dict]:
    out = {}
    for p in sorted(d.glob("*.json")) if d.is_dir() else []:
        try:
            v = json.loads(p.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if isinstance(v, dict):
            out[p.stem] = v
    return out


def raw_ok(url: str, http=urllib_http) -> bool:
    try:
        status, headers, _ = http("HEAD", url, {}, None)
    except Exception:  # noqa: BLE001
        return False
    ctype = {k.lower(): v for k, v in headers.items()}.get("content-type", "")
    return status == 200 and ctype.split(";")[0].strip() == "image/jpeg"


# --------------------------------------------------------------------------- 한 번 실행

def settle(g: Graph, repo: Repo, ig_id: str, states: dict[str, dict], now: datetime, log) -> bool:
    """sending 으로 남은 것을 확인한다. 아직 모르는 것이 남으면 False (이번에는 새로 올리지 않음)."""
    clear = True
    for qid, st in states.items():
        if st.get("status") != "sending":
            continue
        state, info = reconcile(g, ig_id, st, now)
        if state == "published":
            mid = str(info.get("id") or "")
            link = str(info.get("permalink") or "")
            if mid and not link:
                try:
                    link = g.permalink(mid)
                except IGError:
                    link = ""
            st.update(status="published", media_id=mid or None, permalink=link or None,
                      published_at=iso(ts(info.get("timestamp")) or ts(st.get("sent_at")) or now), error=None,
                      note="보낸 뒤 확인해서 게시된 것을 찾음")
            repo.save_state(qid, st, f"published {qid}")
            log(f"{qid}: 지난 게시 요청이 올라간 것을 확인 {link}")
        elif state == "not_published":
            st.update(status="not_published", note="컨테이너·최근 게시물 모두 확인했고 없음 — 다시 올릴 수 있음")
            repo.save_state(qid, st, f"not published {qid}")
            log(f"{qid}: 지난 게시 요청은 올라가지 않았음 — 다시 올릴 수 있음")
        else:
            clear = False
            log(f"{qid}: 게시 여부를 아직 모름 ({info.get('reason') or '보낸 지 얼마 안 됨'}) — 다음 실행에서 다시 확인")
    return clear


def publish_one(g: Graph, repo: Repo, ig_id: str, qid: str, q: dict, prev: dict | None, repo_name: str,
                now: datetime, log, http=urllib_http) -> dict:
    caption = str(q.get("caption") or "")
    images = [str(x) for x in q.get("images") or []]
    attempt = int((prev or {}).get("attempt") or 0) + 1
    base = {"qid": qid, "date": q.get("date"), "slug": q.get("slug"), "item_id": q.get("item_id"), "attempt": attempt}
    bad = [p for p, h in zip(images, q.get("sha256") or [])
           if not (repo.root / p).is_file() or hashlib.sha256((repo.root / p).read_bytes()).hexdigest() != h]
    if not images or not caption or len(q.get("sha256") or []) != len(images) or bad:
        st = base | {"status": "failed", "error": f"예약 내용이 잘못됐거나 사진이 예약 때와 다름: {', '.join(bad[:3])}",
                     "failed_at": iso(now)}
        repo.save_state(qid, st, f"failed {qid}")
        return st
    sha = repo.head()
    urls = [f"{RAW}/{repo_name}/{sha}/{p}" for p in images]
    try:
        usage, total = g.limit(ig_id)
        if usage >= total:
            log(f"게시 한도(24시간 {total}개)에 도달 — 나중에 다시")
            return base | {"status": "skipped"}
        for u in urls:
            if not raw_ok(u, http):
                log(f"공개 이미지 주소가 아직 안 열림 — 다음 실행에서 다시: {u}")
                return base | {"status": "skipped"}
        if len(urls) == 1:
            cid = g.create_single(ig_id, urls[0], caption)
        else:
            cid = g.create_carousel(ig_id, [g.create_item(ig_id, u) for u in urls], caption)
        g.wait_ready(cid)
    except IGError as e:
        if e.rejected and str(e.code) not in TRANSIENT_CODES:
            st = base | {"status": "failed", "error": str(e), "failed_at": iso(now)}
            repo.save_state(qid, st, f"failed {qid}")
            return st
        log(f"{qid}: 일시 오류로 이번에는 못 올림 — 다음 실행에서 다시 ({e})")
        return base | {"status": "skipped"}
    st = base | {"status": "sending", "creation_id": cid, "caption_fp": caption_fp(caption), "sent_at": iso(now)}
    repo.save_state(qid, st, f"sending {qid}")                  # 푸시가 안 되면 여기서 예외 → 보내지 않음
    if not (repo.root / "schedule" / "queue" / f"{qid}.json").is_file():   # 그새 PC 에서 예약 취소
        st.update(status="canceled", note="보내기 직전에 대기열에서 빠진 것을 확인 — 보내지 않음")
        repo.save_state(qid, st, f"canceled {qid}")
        return st
    try:
        mid = g.publish(ig_id, cid)
    except IGError as e:
        if e.rejected and str(e.code) not in MAYBE_POSTED_CODES:
            st.update(status="failed", error=str(e), failed_at=iso(now))
            repo.save_state(qid, st, f"failed {qid}")
            return st
        log(f"{qid}: 게시 결과를 알 수 없음 — 바로 확인 ({e})")
        st["note"] = f"게시 응답: {e}"
        state, info = reconcile(g, ig_id, st, now)            # 보낸 직후라 '안 올라감'으로는 결론 내지 않음
        if state != "published":
            repo.save_state(qid, st, f"sending {qid} (확인 대기)")
            return st
        mid = str(info.get("id") or "")
        st["permalink"] = info.get("permalink")
    link = st.get("permalink") or ""
    if mid and not link:
        try:
            link = g.permalink(mid)
        except IGError:
            link = ""
    st.update(status="published", media_id=mid or None, permalink=link or None, published_at=iso(datetime.now(KST)),
              error=None)
    repo.save_state(qid, st, f"published {qid}")
    return st


def run(now: datetime, g: Graph, repo: Repo, ig_id: str, repo_name: str, *, dry_run: bool = False, log=print,
        http=urllib_http) -> dict:
    cfg = DEFAULT_CONFIG | _load_json(repo.root / "schedule" / "config.json")
    now = now.astimezone(KST)
    slots = plan_slots(now.date(), cfg)
    due = sum(1 for s in slots if s <= now)
    log("오늘 게시 시각(한국): " + ", ".join(s.strftime("%H:%M") for s in slots) + f" · 지난 시각 {due}개")
    states, queue = repo.states(), repo.queue()
    if dry_run:
        me = g.me()
        usage, total = g.limit(ig_id)
        log(f"[확인만] 토큰 유효 @{me.get('username')} · 24시간 게시 {usage}/{total} · 대기열 {len(queue)}개")
    elif not settle(g, repo, ig_id, states, now, log):
        return {"action": "wait"}
    items, _ = g.recent(ig_id)
    times = [t for t in (ts(m.get("timestamp")) for m in items) if t]
    today = sum(1 for t in times if t.astimezone(KST).date() == now.date())
    last = max(times) if times else None
    waiting = sorted((qid for qid, q in queue.items()
                      if (states.get(qid) or {}).get("status") in (None, "not_published")),
                     key=lambda qid: (str(queue[qid].get("queued_at") or ""), qid))
    gap = timedelta(minutes=int(cfg.get("min_gap_min", 120)))
    log(f"오늘 올라간 게시물 {today}개 · 마지막 {last.astimezone(KST).strftime('%m-%d %H:%M') if last else '없음'} · "
        f"예약 대기 {len(waiting)}개")
    if today >= due:
        return {"action": "none", "reason": "지난 시각만큼 이미 올림"}
    if last and now - last < gap:
        return {"action": "none", "reason": f"마지막 게시물과 {int(gap.total_seconds() // 60)}분이 안 지남"}
    if not waiting:
        return {"action": "none", "reason": "예약 대기 없음"}
    qid = waiting[0]
    if dry_run:
        log(f"[확인만] 지금 실제 실행이면 {qid} 를 올립니다")
        return {"action": "would_publish", "qid": qid}
    st = publish_one(g, repo, ig_id, qid, queue[qid], states.get(qid), repo_name, now, log, http)
    log(f"{qid}: {st.get('status')} {st.get('permalink') or st.get('error') or ''}")
    return {"action": "publish", "qid": qid, "status": st.get("status")}


def _load_json(p: Path) -> dict:
    try:
        v = json.loads(p.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return v if isinstance(v, dict) else {}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="POP&EAT 예약 게시 (GitHub Actions)")
    ap.add_argument("--dry-run", action="store_true", help="확인만 (게시·커밋 안 함)")
    a = ap.parse_args(argv)
    token, ig_id = os.environ.get("IG_ACCESS_TOKEN", ""), os.environ.get("IG_USER_ID", "")
    repo_name = os.environ.get("GITHUB_REPOSITORY", "")
    if not token or not ig_id or not repo_name:
        print("IG_ACCESS_TOKEN·IG_USER_ID(저장소 비밀값)·GITHUB_REPOSITORY 가 필요합니다", file=sys.stderr)
        return 2
    repo = Repo(Path.cwd())
    if not a.dry_run:
        repo.git("config", "user.name", "popeat-scheduler")
        repo.git("config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
    log = lambda m: print(redact(str(m), token), flush=True)  # noqa: E731
    try:
        out = run(datetime.now(KST), Graph(token), repo, ig_id, repo_name, dry_run=a.dry_run, log=log)
    except IGError as e:
        log(f"인스타그램 API 오류로 이번 실행은 멈춤 — 다음 실행에서 다시: {e}")
        return 0
    log(json.dumps(out, ensure_ascii=False))
    return 1 if out.get("status") == "failed" else 0


if __name__ == "__main__":
    sys.exit(main())
