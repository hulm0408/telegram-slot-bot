import fs from 'fs';
import path from 'path';
import os from 'os';
import crypto from 'crypto';
import puppeteer from 'puppeteer-core';
import { updateAccount, getNextAutoUserName, cleanEssentialSwiggyCookies } from './store.js';
import { normalizeIndianMobileNumber } from './phone-utils.js';

export function findChromePath() {
  if (process.env.PUPPETEER_EXECUTABLE_PATH) return process.env.PUPPETEER_EXECUTABLE_PATH;
  if (process.env.CHROME_BIN) return process.env.CHROME_BIN;
  if (process.platform === 'win32') {
    return 'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe';
  }
  const linuxPaths = [
    '/usr/bin/chromium',
    '/usr/bin/chromium-browser',
    '/usr/bin/google-chrome',
    '/usr/bin/google-chrome-stable',
    '/opt/playwright/browsers/chromium-1247/chrome-linux64/chrome'
  ];
  for (const p of linuxPaths) {
    try { if (fs.existsSync(p)) return p; } catch (e) {}
  }
  for (const rootDir of ['/opt/playwright/browsers', path.join(os.homedir(), '.cache', 'puppeteer'), '/root/.cache/puppeteer']) {
    try {
      if (!fs.existsSync(rootDir)) continue;
      for (const entry of fs.readdirSync(rootDir)) {
        for (const sub of ['chrome-linux64/chrome', 'chrome-linux/chrome']) {
          const full = path.join(rootDir, entry, sub);
          if (fs.existsSync(full)) return full;
        }
      }
    } catch (e) {}
  }
  return '/usr/bin/chromium';
}

const CHROME_PATH = findChromePath();
const IS_LINUX = process.platform === 'linux';
const HEADLESS_MODE = (IS_LINUX || process.env.RAILWAY_ENVIRONMENT || process.env.HEADLESS === 'true') ? 'new' : false;

// Active login sessions keyed by userId:
// { [userId]: { browser, page, phone, otp, targetAcc, targetAccName, signupEmail, isNewUser, safetyTimer } }
const activeSessions = {};
// Dedicated in-memory session map for Swiggy account deletions (strictly isolated from login)
const activeDeleteSessions = {};
let deleteOtpRequestCount = 0;
let deleteVerifyRequestCount = 0;

// Pre-warmed browser pool for instantaneous (<1s) OTP dispatch
let prewarmedBrowser = null;
let prewarmedPage = null;
let isPrewarming = false;
let prewarmedAt = 0;
let latestSharedWafToken = '';
let latestSharedWafAt = 0;
let wafSolvePromise = null;
const WAF_CACHE_TTL_MS = 8 * 60 * 1000; // 8 minutes

const SWIGGY_WAF_COOKIE_WAIT_MS = 15000;
const SWIGGY_WAF_COOKIE_POLL_MS = 250;
const AUTH_PAGE_EVALUATE_TIMEOUT_MS = 9000;

async function waitForSwiggyWafCookie(page, timeoutMs = SWIGGY_WAF_COOKIE_WAIT_MS) {
  const deadline = Date.now() + Math.max(0, Number(timeoutMs) || 0);
  while (Date.now() < deadline) {
    const cookies = await page.cookies().catch(() => []);
    const wafCookie = cookies.find(cookie => cookie.name === 'aws-waf-token' && String(cookie.value || '').length > 50);
    if (wafCookie) return wafCookie.value;
    const remainingMs = deadline - Date.now();
    if (remainingMs > 0) {
      await new Promise(resolve => setTimeout(resolve, Math.min(SWIGGY_WAF_COOKIE_POLL_MS, remainingMs)));
    }
  }
  return '';
}

async function waitForSwiggyLoginCookies(page, timeoutMs = 800) {
  const deadline = Date.now() + Math.max(0, Number(timeoutMs) || 0);
  let cookies = [];
  do {
    cookies = await page.cookies().catch(() => []);
    if (checkLoggedInFromCookies(cookies)) return cookies;
    const remainingMs = deadline - Date.now();
    if (remainingMs <= 0) break;
    await new Promise(resolve => setTimeout(resolve, Math.min(100, remainingMs)));
  } while (Date.now() < deadline);
  return cookies;
}

export function stripStaleWafCookie(cookieStr = '') {
  if (!cookieStr || typeof cookieStr !== 'string') return '';
  return cookieStr
    .split(';')
    .map(s => s.trim())
    .filter(s => s && !s.startsWith('aws-waf-token='))
    .join('; ');
}

function mergeSetCookiesIntoJar(existingCookieStr = '', setCookieHeaders = []) {
  const map = new Map();
  for (const part of stripStaleWafCookie(existingCookieStr).split(';')) {
    const trimmed = part.trim();
    if (!trimmed || !trimmed.includes('=')) continue;
    const idx = trimmed.indexOf('=');
    map.set(trimmed.slice(0, idx).trim(), trimmed.slice(idx + 1).trim());
  }
  for (const raw of (setCookieHeaders || [])) {
    const first = String(raw || '').split(';')[0].trim();
    if (!first || !first.includes('=')) continue;
    const idx = first.indexOf('=');
    const k = first.slice(0, idx).trim();
    const v = first.slice(idx + 1).trim();
    if (k && v && k !== '_guest_tid' && k !== 'aws-waf-token') {
      map.set(k, v);
    }
  }
  return Array.from(map.entries()).map(([k, v]) => `${k}=${v}`).join('; ');
}

// Helper to decode JWT payload safely
export function decodeJwtPayload(jwtToken) {
  if (!jwtToken || typeof jwtToken !== 'string') return null;
  try {
    const parts = jwtToken.split('.');
    if (parts.length < 2) return null;
    const jsonStr = Buffer.from(parts[1], 'base64').toString('utf-8');
    return JSON.parse(jsonStr);
  } catch (e) {
    return null;
  }
}

export function sanitizeSwiggyName(name) {
  if (!name) return 'Customer';
  // Strip any previously appended "(User 1)" or "(6296591407)" tag first
  const withoutSlotTag = String(name).replace(/\([^)]*\)/g, ' ');
  const cleaned = withoutSlotTag.replace(/[^\p{L}\p{M}\p{N}\s]/gu, '').replace(/\s+/g, ' ').trim();
  if ([...cleaned].length < 2 || !/\p{L}/u.test(cleaned) || /^user\s*\d*$/i.test(cleaned)) {
    return 'Customer';
  }
  return cleaned;
}

function generateUniqueSwiggyEmail(phone, name) {
  const prefix = String(name || 'user').toLowerCase().replace(/[^a-z]/g, '').slice(0, 8) || 'user';
  const last4 = String(phone || '').slice(-4) || '1000';
  const rand = Math.floor(1000 + Math.random() * 9000);
  return `${prefix}${last4}.${rand}@gmail.com`;
}

// Helper to check if cookies or account contain a verified logged-in user
export function checkLoggedInFromCookies(input) {
  if (!input) return false;
  let tidValue = '';
  let sessionTid = '';
  let tokenVal = '';
  let isLoggedFlag = '';

  if (typeof input === 'object' && !Array.isArray(input)) {
    if (input.isLoggedIn === false) return false;
    if (input.tid) tidValue = String(input.tid);
    if (input._session_tid || input.session_tid || input.sessionTid) {
      sessionTid = String(input._session_tid || input.session_tid || input.sessionTid);
    }
    if (!sessionTid && tidValue && !tidValue.includes('.')) {
      sessionTid = tidValue;
    }
    if (input.token || input.auth_token || input.access_token || input.authToken || input.accessToken) {
      tokenVal = String(input.token || input.auth_token || input.access_token || input.authToken || input.accessToken);
    }
    if (input.cookies) input = input.cookies;
    else if (!tidValue && !tokenVal && !sessionTid) return Boolean(input.isLoggedIn);
  }

  if (Array.isArray(input)) {
    const getC = (n) => input.find(c => c && c.name === n)?.value || '';
    tidValue = tidValue || getC('tid');
    sessionTid = sessionTid || getC('_session_tid');
    tokenVal = tokenVal || getC('token');
    isLoggedFlag = getC('_is_logged_in');
  } else if (typeof input === 'string') {
    const getS = (re) => {
      const m = input.match(re);
      return m ? decodeURIComponent(m[1]).trim() : '';
    };
    tidValue = tidValue || getS(/(?:^|;\s*)tid=([^;]+)/);
    sessionTid = sessionTid || getS(/(?:^|;\s*)_session_tid=([^;]+)/);
    tokenVal = tokenVal || getS(/(?:^|;\s*)token=([^;]+)/);
    isLoggedFlag = getS(/(?:^|;\s*)_is_logged_in=([^;]+)/);
    if (!tidValue && input.includes('.') && input.length > 50 && !input.includes(';')) {
      tidValue = input.trim();
    }
    if (!sessionTid && /^[0-9a-fA-F]{40,}$/.test(input.trim())) {
      sessionTid = input.trim();
    }
  }

  if (tidValue && tidValue.includes('.')) {
    const payload = decodeJwtPayload(tidValue);
    if (payload && payload.user_id && payload.user_id !== '0' && payload.user_id !== '-1') {
      return true;
    }
    // If `tid` is an explicit guest pre-OTP JWT (`user_id === "0"`) and there is NO real `_session_tid`, it is NOT logged in!
    if (payload && (payload.user_id === '0' || payload.user_id === '-1') && !sessionTid && (!tokenVal || tokenVal === tidValue)) {
      return false;
    }
  }

  if (isLoggedFlag === '1' && (sessionTid.length >= 16 || tokenVal.length >= 10)) {
    return true;
  }
  if (isLoggedFlag !== '0' && (sessionTid.length >= 32 || tokenVal.length >= 24 || (tokenVal.length >= 16 && tidValue.length >= 50))) {
    return true;
  }

  return false;
}

// ---------------------------------------------------------------------------
// Auto-claim & 14-Day Advance Pre-Book Swiggy Event Offers:
// 1. Breakfast Morning (`book-your-offer` — voting before 05:00 IST, redeem 07:00–11:00 IST)
// 2. Late Night Offer (`pick-your-late-night-offer` — voting before 18:30 IST, redeem 21:00–06:00 IST)
// Locks in TODAY + ALL NEXT 14 UPCOMING DAYS in advance via `POST` + `PATCH` on `events.swiggy.com/api/notify`
// so Swiggy's daily batch cutoff (`18:30 IST` LN / `05:00 IST` BF) NEVER misses crediting Free Cash / Coupons!
// ---------------------------------------------------------------------------
export const EVENT_OFFER_OPTIONS = {
  1: { value: 1, shortLabel: '₹50 Free Cash (>₹199)', fullLabel: '₹ ₹50 Free Cash (MOV ₹199 • Stacks Over Coupons)' },
  2: { value: 2, shortLabel: '₹150 OFF Coupon (>₹249)', fullLabel: '# ₹150 OFF Coupon (MOV ₹249)' },
  3: { value: 3, shortLabel: '₹175 LN / ₹100 BF Coupon', fullLabel: '! ₹175 OFF LN (>₹399) / ₹100 OFF BF' },
  4: { value: 4, shortLabel: '₹100 OFF Coupon (>₹149)', fullLabel: '! ₹100 OFF Coupon (MOV ₹149)' }
};

const offerClaimCache = new Map(); // `${accSig}:${offerValue}` -> { result, ts }
const OFFER_CLAIM_TTL_MS = 30 * 60 * 1000;

let cachedEventCampaignMeta = null;
let cachedEventCampaignMetaAt = 0;
const EVENT_META_TTL_MS = 15 * 60 * 1000;

function decodeJwtExpSec(jwt) {
  if (!jwt || typeof jwt !== 'string' || !jwt.includes('.')) return 0;
  const payload = decodeJwtPayload(jwt);
  return Number(payload?.exp || 0);
}

async function getLiveEventCampaignMeta(forceRefresh = false) {
  if (!forceRefresh && cachedEventCampaignMeta && (Date.now() - cachedEventCampaignMetaAt < EVENT_META_TTL_MS)) {
    return cachedEventCampaignMeta;
  }
  const fallback = {
    bfPrefix: 'byo-bf-v10-',
    lnPrefix: 'byo-ln-v5-',
    bfBoundaries: [],
    lnBoundaries: []
  };
  try {
    const [bfRes, lnRes] = await Promise.all([
      fetch('https://events.swiggy.com/book-your-offer?utm_source=app&utm_medium=share', { signal: AbortSignal.timeout(5000) }),
      fetch('https://events.swiggy.com/pick-your-late-night-offer?utm_source=app&utm_medium=share', { signal: AbortSignal.timeout(5000) })
    ]);
    const [bfHtml, lnHtml] = await Promise.all([bfRes.text(), lnRes.text()]);
    const parseNexus = (html, defPrefix) => {
      const m = html.match(/<script id="__NEXT_DATA__"[^>]*>([\s\S]*?)<\/script>/);
      if (!m) return { prefix: defPrefix, boundaries: [] };
      try {
        const parsed = JSON.parse(m[1]);
        const nexus = parsed?.props?.pageProps?.nexusData || {};
        return {
          prefix: nexus.notifyCampaignIdPrefix || defPrefix,
          boundaries: Array.isArray(nexus.dayBoundaries) ? nexus.dayBoundaries : []
        };
      } catch {
        return { prefix: defPrefix, boundaries: [] };
      }
    };
    const bf = parseNexus(bfHtml, 'byo-bf-v10-');
    const ln = parseNexus(lnHtml, 'byo-ln-v5-');
    cachedEventCampaignMeta = {
      bfPrefix: bf.prefix,
      lnPrefix: ln.prefix,
      bfBoundaries: bf.boundaries,
      lnBoundaries: ln.boundaries
    };
    cachedEventCampaignMetaAt = Date.now();
    return cachedEventCampaignMeta;
  } catch (e) {
    console.warn('[EventsClaim] Dynamic campaign lookup fallback used:', e.message);
    return cachedEventCampaignMeta || fallback;
  }
}

function resolveCampaignWindowInfo(boundaries, prefix, defaultDay = 15, isLateNight = false, nowMs = Date.now()) {
  let matched = null;
  for (const d of (boundaries || [])) {
    const start = Date.parse(d.startTime);
    const end = Date.parse(d.endTime);
    if (nowMs >= start && nowMs < end) {
      matched = { ...d, startMs: start, endMs: end };
      break;
    }
  }
  if (!matched && Array.isArray(boundaries) && boundaries.length > 0) {
    const start1 = Date.parse(boundaries[0].startTime);
    const diff = Math.floor((nowMs - start1) / (24 * 3600 * 1000)) + 1;
    const clampedIdx = Math.max(0, Math.min(diff - 1, boundaries.length - 1));
    const b = boundaries[clampedIdx];
    matched = { ...b, startMs: Date.parse(b.startTime), endMs: Date.parse(b.endTime) };
  }
  const currentDay = matched?.day || defaultDay;
  const maxDay = (boundaries && boundaries.length > 0)
    ? Math.max(...boundaries.map(b => Number(b.day) || 0), currentDay + 14)
    : currentDay + 14;

  // Exact Swiggy cutoff timestamps from `pick-your-late-night-offer` module 17858 (`day` starts 11:00 IST):
  // - Late Night: voting closes at 18:30 IST (+7.5h from 11:00 startTime), active redeem slot 21:00–06:00 IST (+10h..+19h)
  // - Breakfast: voting closes at 05:00 IST (+18h from 11:00 startTime), active redeem slot 07:00–11:00 IST (+20h..+24h)
  let cutoffMs = null;
  let slotOpenMs = null;
  if (matched?.startMs) {
    cutoffMs = matched.startMs + (isLateNight ? 7.5 * 3600 * 1000 : 18 * 3600 * 1000);
    slotOpenMs = matched.startMs + (isLateNight ? 10 * 3600 * 1000 : 20 * 3600 * 1000);
  }

  return {
    currentDay,
    maxDay,
    todayCampaign: `${prefix}${currentDay}`,
    upcomingDays: Array.from(
      { length: Math.min(2, Math.max(1, maxDay - currentDay + 1)) },
      (_, idx) => `${prefix}${currentDay + idx}`
    ),
    cutoffMs,
    slotOpenMs,
    endMs: matched?.endMs || null
  };
}

export async function claimSwiggyBreakfastAndLateNightOffers(account, { force = false, offerValue = null, forcePatch = false } = {}) {
  if (!account) return { success: false, reason: 'No account provided' };
  const chosenVal = [1, 2, 3, 4].includes(Number(offerValue || account.preferredOfferValue))
    ? Number(offerValue || account.preferredOfferValue)
    : 1;
  const chosenMeta = EVENT_OFFER_OPTIONS[chosenVal] || EVENT_OFFER_OPTIONS[1];
  const accSig = `${String(account.id || account.phone || account.customerId || account.token || (account.cookies || '').slice(0, 60))}:v${chosenVal}`;
  if (!force && !forcePatch && accSig && offerClaimCache.has(accSig)) {
    const prev = offerClaimCache.get(accSig);
    if (Date.now() - prev.ts < OFFER_CLAIM_TTL_MS) return prev.result;
  }

  let token = account.token || '';
  let jwtTid = account.tid || '';
  let cookieStr = stripStaleWafCookie(account.cookies || '');

  if (cookieStr) {
    const tidCookie = cookieStr.split(';').map(s => s.trim()).find(s => s.startsWith('tid='));
    if (tidCookie && tidCookie.slice(4).includes('.')) {
      jwtTid = tidCookie.slice(4);
    }
    if (!token) {
      const tokCookie = cookieStr.split(';').map(s => s.trim()).find(s => s.startsWith('token='));
      if (tokCookie) {
        token = tokCookie.slice(6);
      }
    }
  }

  // Refresh live 30-day `jwtTid` via zero-WAF Android `chkout` first (fast ~180ms), fallback to `/dapi/order/all`!
  let liveSessionDead = false;
  const nowSec = Math.floor(Date.now() / 1000);
  if ((!jwtTid || decodeJwtExpSec(jwtTid) < nowSec + 120) && (token || jwtTid || cookieStr)) {
    try {
      const chkRes = await fetch('https://chkout.swiggy.com/api/v2/cart/client', {
        headers: {
          'User-Agent': 'Swiggy-Android',
          'app-version': '4.67.0',
          'version-code': '1365',
          'os-version': '13',
          'Accept': 'application/json',
          ...(jwtTid ? { tid: jwtTid } : {}),
          ...(token ? { token } : {}),
          ...(account.sid ? { sid: account.sid } : {}),
          ...(account.deviceId ? { deviceId: account.deviceId, swuid: account.deviceId } : {})
        },
        signal: AbortSignal.timeout(5000)
      });
      const chkJson = await chkRes.json().catch(() => null);
      if (chkJson?.statusCode === 0 && chkJson?.tid && String(chkJson.tid).includes('.')) {
        jwtTid = chkJson.tid;
        account.jwtTid = jwtTid;
        if (!account.tid || String(account.tid).includes('.')) account.tid = jwtTid;
      } else if (chkJson?.statusCode === 999) {
        liveSessionDead = true;
      }
    } catch {}
  }

  if ((!jwtTid || decodeJwtExpSec(jwtTid) < nowSec + 120) && cookieStr) {
    try {
      const authRes = await fetch('https://www.swiggy.com/dapi/order/all', {
        headers: {
          'Cookie': cookieStr,
          'User-Agent': 'Swiggy-Android',
          'Accept': 'application/json',
          'Referer': 'https://www.swiggy.com/my-account'
        },
        signal: AbortSignal.timeout(5000)
      });
      const authJson = await authRes.json().catch(() => null);
      if (authRes.status === 200 && authJson?.statusCode === 0 && authJson?.tid) {
        jwtTid = authJson.tid;
        account.jwtTid = jwtTid;
        if (!account.tid || String(account.tid).includes('.')) account.tid = jwtTid;
        const setCookies = typeof authRes.headers.getSetCookie === 'function' ? authRes.headers.getSetCookie() : [];
        if (setCookies.length > 0) {
          cookieStr = mergeSetCookiesIntoJar(cookieStr, setCookies);
        }
      } else if (authJson?.statusCode === 1) {
        liveSessionDead = true;
      }
    } catch {}
  }

  if (!token && jwtTid) {
    token = jwtTid;
  }

  if (!jwtTid && !token) {
    return { success: false, sessionExpired: true, reason: 'Session Logged Out — Re-login required' };
  }

  if (!cookieStr && jwtTid) {
    cookieStr = `tid=${jwtTid}` + (account.sid ? `; _sid=${account.sid}` : '') + (account.deviceId ? `; _device_id=${account.deviceId}` : '');
  }

  const nowMs = Date.now();
  const meta = await getLiveEventCampaignMeta(false);
  const bfWin = resolveCampaignWindowInfo(meta.bfBoundaries, meta.bfPrefix, 15, false, nowMs);
  const lnWin = resolveCampaignWindowInfo(meta.lnBoundaries, meta.lnPrefix, 15, true, nowMs);

  // CRITICAL: `events.swiggy.com/api/notify` authenticates strictly via `{ token, tid }` headers!
  // Sending `Cookie:` triggers CloudFront WAF `403 Forbidden` on accounts with multi-domain web cookies!
  const baseHeaders = {
    'Content-Type': 'application/json',
    'Accept': 'application/json',
    'token': token || jwtTid,
    'tid': jwtTid,
    'Origin': 'https://events.swiggy.com',
    'User-Agent': 'Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Mobile Safari/537.36'
  };

  try {
    // CloudFront WAF-safe (`<40 req/10s/IP`) 48-Hour Rolling Pre-Book (`Today + Tomorrow` = `4` campaigns total!):
    // 1) `GET /api/notify?campaign=<id>` checks real live state (`shouldNotify`, `value`, `timestamp`).
    // 2) If already `shouldNotify === true` AND `Number(value) === chosenVal` -> `0` extra mutations needed!
    // 3) If unsubscribed -> single `POST`; if subscribed with a different `value` -> single `PATCH` (never redundant `POST + PATCH`)!
    // 4) If CloudFront burst limit (`403`/`429`) triggers, waits `5.5s` for window reset and retries cleanly!
    const prevLockedMap = (account.offers && typeof account.offers.lockedMap === 'object' && account.offers.lockedMap)
      ? { ...account.offers.lockedMap }
      : {};

    const syncSingleCampaign = async (campaignId, referer) => {
      for (let tryIdx = 0; tryIdx < 2; tryIdx++) {
        if (tryIdx > 0) await new Promise(r => setTimeout(r, 5500));

        const statusRes = await fetch(`https://events.swiggy.com/api/notify?campaign=${encodeURIComponent(campaignId)}`, {
          headers: baseHeaders,
          signal: AbortSignal.timeout(5500)
        });
        if ((statusRes.status === 403 || statusRes.status === 429) && tryIdx === 0) continue;
        const statusJson = await statusRes.json().catch(() => ({}));

        const isSubscribed = Boolean(statusJson?.shouldNotify);
        const curVal = Number(statusJson?.value || 0);

        // Already locked on Swiggy's server with the exact desired reward value!
        if (statusRes.ok && isSubscribed && curVal === chosenVal) {
          prevLockedMap[campaignId] = chosenVal;
          return { res: statusRes, json: { ...statusJson, message: 'Already active' }, statusJson };
        }

        // Need either `POST` (first time subscribing) or `PATCH` (switching reward option 1..4)!
        const writeMethod = isSubscribed ? 'PATCH' : 'POST';
        const writeRes = await fetch('https://events.swiggy.com/api/notify', {
          method: writeMethod,
          headers: { ...baseHeaders, 'Referer': referer },
          body: JSON.stringify({ campaign: campaignId, value: chosenVal }),
          signal: AbortSignal.timeout(6500)
        });
        if ((writeRes.status === 403 || writeRes.status === 429) && tryIdx === 0) continue;
        const writeJson = await writeRes.json().catch(() => ({}));

        // If `POST` says already subscribed with a different value, do a single `PATCH` to update `value`:
        const alreadyMsg = String(writeJson?.message || '').toLowerCase().includes('already');
        if (writeMethod === 'POST' && alreadyMsg && Number(writeJson?.value || 0) !== chosenVal) {
          const patchRes = await fetch('https://events.swiggy.com/api/notify', {
            method: 'PATCH',
            headers: { ...baseHeaders, 'Referer': referer },
            body: JSON.stringify({ campaign: campaignId, value: chosenVal }),
            signal: AbortSignal.timeout(6500)
          });
          if ((patchRes.status === 403 || patchRes.status === 429) && tryIdx === 0) continue;
          const patchJson = await patchRes.json().catch(() => ({}));
          if (patchRes.ok) prevLockedMap[campaignId] = chosenVal;
          return { res: patchRes, json: patchJson, statusJson: { ...statusJson, shouldNotify: true, value: chosenVal } };
        }

        if (writeRes.ok || alreadyMsg) {
          prevLockedMap[campaignId] = chosenVal;
        }
        return {
          res: writeRes,
          json: writeJson,
          statusJson: {
            ...statusJson,
            shouldNotify: Boolean(writeRes.ok || alreadyMsg || isSubscribed),
            value: chosenVal,
            timestamp: statusJson?.timestamp || writeJson?.currentTime || new Date().toISOString()
          }
        };
      }
      return { res: { ok: false, status: 403, statusText: 'Rate Limited' }, json: {}, statusJson: {} };
    };

    const bfAll = [];
    const lnAll = [];
    const maxLen = Math.max(bfWin.upcomingDays.length, lnWin.upcomingDays.length);
    for (let i = 0; i < maxLen; i++) {
      const [bItem, lItem] = await Promise.all([
        bfWin.upcomingDays[i]
          ? syncSingleCampaign(bfWin.upcomingDays[i], 'https://events.swiggy.com/book-your-offer')
          : Promise.resolve(null),
        lnWin.upcomingDays[i]
          ? syncSingleCampaign(lnWin.upcomingDays[i], 'https://events.swiggy.com/pick-your-late-night-offer')
          : Promise.resolve(null)
      ]);
      if (bItem) bfAll.push(bItem);
      if (lItem) lnAll.push(lItem);
    }

    const bfStatusNow = bfAll[0]?.statusJson || {};
    const lnStatusNow = lnAll[0]?.statusJson || {};

    const { res: resBf, json: bfJson } = bfAll[0];
    const { res: resLn, json: lnJson } = lnAll[0];

    const bfLockedCount = bfAll.filter(x => x.res.ok || String(x.json?.message || '').toLowerCase().includes('already')).length;
    const lnLockedCount = lnAll.filter(x => x.res.ok || String(x.json?.message || '').toLowerCase().includes('already')).length;

    const bfOk = bfLockedCount > 0;
    const lnOk = lnLockedCount > 0;

    const describeSlotState = (ok, res, json, statusNow, win, isLn) => {
      if (!ok) {
        if (res.status === 401 || liveSessionDead) return { state: 'EXPIRED', msg: 'Session Expired — Re-login required' };
        if (res.status === 403) return { state: 'FORBIDDEN', msg: 'HTTP 403 Forbidden (WAF Blocked)' };
        return { state: 'FAILED', msg: `HTTP ${res.status} (${json.message || res.statusText || 'Error'})` };
      }
      const bookedAtMs = statusNow?.timestamp ? Date.parse(statusNow.timestamp) : nowMs;
      const bookedBeforeCutoff = !win.cutoffMs || bookedAtMs <= win.cutoffMs;
      const inRedeemSlotNow = Boolean(win.slotOpenMs && win.endMs && nowMs >= win.slotOpenMs && nowMs < win.endMs);
      const valTag = (EVENT_OFFER_OPTIONS[statusNow?.value || chosenVal] || chosenMeta).shortLabel;
      const daysTag = `+${Math.max(0, (isLn ? lnLockedCount : bfLockedCount) - 1)} next days pre-locked`;

      if (bookedBeforeCutoff && inRedeemSlotNow) {
        return { state: 'ACTIVE_NOW', msg: `● LIVE IN CART NOW (${valTag} • ${daysTag})` };
      }
      if (bookedBeforeCutoff) {
        return {
          state: 'LOCKED_FOR_TODAY',
          msg: `✓ Booked Before Cutoff (${valTag} • activates ${isLn ? '9:00 PM' : '7:00 AM'} • ${daysTag})`
        };
      }
      return {
        state: 'CUTOFF_PASSED_LOCKED_NEXT_14D',
        msg: `◷ Today's ${isLn ? '6:30 PM' : '5:00 AM'} cutoff passed before login — Next 14 Days PRE-LOCKED (${valTag})!`
      };
    };

    const bfDesc = describeSlotState(bfOk, resBf, bfJson, bfStatusNow, bfWin, false);
    const lnDesc = describeSlotState(lnOk, resLn, lnJson, lnStatusNow, lnWin, true);

    console.log(`[EventsClaim] Account ${account.phone || account.name || 'User'} result:`, {
      offerValue: chosenVal,
      breakfast: { campaign: bfWin.todayCampaign, lockedDays: bfLockedCount, state: bfDesc.state },
      lateNight: { campaign: lnWin.todayCampaign, lockedDays: lnLockedCount, state: lnDesc.state }
    });

    const claimOut = {
      success: bfOk || lnOk,
      bothClaimed: bfOk && lnOk,
      offerValue: chosenVal,
      offerLabel: chosenMeta.shortLabel,
      lockedMap: prevLockedMap,
      sessionExpired: !bfOk && !lnOk && (resBf.status === 401 || resLn.status === 401 || liveSessionDead),
      breakfast: {
        name: 'Breakfast Morning (7AM–11AM)',
        campaign: bfWin.todayCampaign,
        lockedDaysCount: bfLockedCount,
        upcomingCampaigns: bfWin.upcomingDays,
        slotState: bfDesc.state,
        status: bfOk ? 'CLAIMED' : 'FAILED',
        statusCode: resBf.status,
        discount: chosenMeta.shortLabel,
        offerValue: Number(bfStatusNow?.value || chosenVal),
        rawMessage: bfJson.message || '',
        message: bfDesc.msg
      },
      lateNight: {
        name: 'Late Night (9PM–6AM)',
        campaign: lnWin.todayCampaign,
        lockedDaysCount: lnLockedCount,
        upcomingCampaigns: lnWin.upcomingDays,
        slotState: lnDesc.state,
        status: lnOk ? 'CLAIMED' : 'FAILED',
        statusCode: resLn.status,
        discount: chosenMeta.shortLabel,
        offerValue: Number(lnStatusNow?.value || chosenVal),
        rawMessage: lnJson.message || '',
        message: lnDesc.msg
      }
    };
    if (accSig) offerClaimCache.set(accSig, { result: claimOut, ts: Date.now() });
    return claimOut;
  } catch (err) {
    console.error('[EventsClaim] Request error:', err.message);
    return { success: false, error: err.message };
  }
}

async function launchStealthSwiggyBrowser() {
  const browser = await puppeteer.launch({
    executablePath: CHROME_PATH,
    headless: HEADLESS_MODE,
    protocolTimeout: 60000,
    ignoreDefaultArgs: ['--enable-automation'],
    args: [
      '--disable-blink-features=AutomationControlled',
      '--no-sandbox',
      '--disable-setuid-sandbox',
      '--disable-gpu',
      '--disable-dev-shm-usage',
      '--no-first-run',
      '--no-default-browser-check',
      '--disable-background-timer-throttling',
      '--disable-backgrounding-occluded-windows',
      '--disable-renderer-backgrounding',
      '--window-size=1366,768',
      '--lang=en-IN,en-US,en'
    ]
  });

  const page = await browser.newPage();
  const cleanSyntheticEntityId = crypto.randomUUID();
  await page.setViewport({ width: 1366, height: 768 });
  await page.emulateTimezone('Asia/Kolkata').catch(() => {});
  await page.setUserAgent('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36');

  // Intercept `fna.swiggy.com/api/fraudnabuse/*` so Headless Linux container never flags newly logged-in accounts into Promo-Restricted segment!
  await page.setRequestInterception(true);
  page.on('request', (req) => {
    const u = req.url();
    if (u.includes('fna.swiggy.com/api/fraudnabuse')) {
      return req.respond({
        status: 200,
        contentType: 'application/json',
        headers: {
          'Access-Control-Allow-Origin': 'https://www.swiggy.com',
          'Access-Control-Allow-Credentials': 'true',
          'Access-Control-Allow-Headers': 'Content-Type, Accept'
        },
        body: JSON.stringify({ statusCode: 0, statusMessage: 'success', data: cleanSyntheticEntityId, successful: true })
      }).catch(() => {});
    }
    req.continue().catch(() => {});
  });

  await page.evaluateOnNewDocument(() => {
    try {
      const proto = Object.getPrototypeOf(navigator);
      delete proto.webdriver;
    } catch (e) {}
    Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
    Object.defineProperty(navigator, 'platform', { get: () => 'Win32' });
    Object.defineProperty(navigator, 'hardwareConcurrency', { get: () => 8 });
    Object.defineProperty(navigator, 'deviceMemory', { get: () => 8 });
    if (!window.chrome) window.chrome = {};
    window.chrome.runtime = window.chrome.runtime || { connect: () => {}, sendMessage: () => {} };
    window.chrome.loadTimes = window.chrome.loadTimes || (() => ({}));
    window.chrome.csi = window.chrome.csi || (() => ({}));
    window.chrome.app = window.chrome.app || {};
    Object.defineProperty(navigator, 'languages', { get: () => ['en-IN', 'en-US', 'en'] });
    if (!navigator.plugins || navigator.plugins.length === 0) {
      Object.defineProperty(navigator, 'plugins', {
        get: () => [
          { name: 'Chrome PDF Plugin', filename: 'internal-pdf-viewer', description: 'Portable Document Format' },
          { name: 'Chrome PDF Viewer', filename: 'mhjfbmdgcfjbbpaeojofohoefgiehjai', description: '' }
        ]
      });
    }
    if (navigator.permissions && navigator.permissions.query) {
      const origQuery = navigator.permissions.query;
      navigator.permissions.query = (params) => {
        if (params && params.name === 'notifications') {
          return Promise.resolve({ state: Notification.permission });
        }
        return origQuery.call(navigator.permissions, params);
      };
    }
  });
  return { browser, page };
}

// Pre-warm browser in background so when user asks for OTP, it fires instantly
export async function prewarmBrowser() {
  if (isPrewarming || (prewarmedPage && prewarmedBrowser?.connected && (Date.now() - prewarmedAt < 180000))) return;
  isPrewarming = true;

  try {
    if (prewarmedBrowser) {
      await prewarmedBrowser.close().catch(() => {});
      prewarmedBrowser = null;
      prewarmedPage = null;
    }

    const { browser, page } = await launchStealthSwiggyBrowser();
    await page.goto('https://www.swiggy.com/', { waitUntil: 'domcontentloaded', timeout: 30000 }).catch(() => {});

    const wafToken = await waitForSwiggyWafCookie(page, SWIGGY_WAF_COOKIE_WAIT_MS);
    if (!wafToken) {
      console.warn('! [SwiggyBridge] Prewarm: Swiggy did not issue its WAF cookie within timeout; stopping prewarm without bypassing the check.');
      await browser.close().catch(() => {});
      return;
    }

    // Allow WAF page reload/navigation to settle
    await new Promise(r => setTimeout(r, 2000));

    latestSharedWafToken = wafToken;
    latestSharedWafAt = Date.now();
    prewarmedBrowser = browser;
    prewarmedPage = page;
    prewarmedAt = Date.now();
    console.log('! [SwiggyBridge] Pre-warmed Chrome is primed with valid AWS WAF token on swiggy.com! Next OTP will fire in <1s.');
  } catch (err) {
    console.error('Failed to prewarm Chrome:', err.message);
    if (prewarmedBrowser) {
      await prewarmedBrowser.close().catch(() => {});
      prewarmedBrowser = null;
      prewarmedPage = null;
    }
  } finally {
    isPrewarming = false;
  }
}

// Universal cached / live AWS WAF token provider for both swiggy-bridge and swiggy-cart
export async function getLiveSwiggyWafToken(forceRefresh = false) {
  const now = Date.now();
  if (!forceRefresh && latestSharedWafToken && (now - latestSharedWafAt < WAF_CACHE_TTL_MS)) {
    return latestSharedWafToken;
  }

  // 1. Check if prewarmedPage is alive and has an active WAF cookie (<5ms check):
  if (!forceRefresh && prewarmedPage && prewarmedBrowser?.connected) {
    try {
      const cookies = await prewarmedPage.cookies('https://www.swiggy.com').catch(() => []);
      const waf = cookies.find(c => c.name === 'aws-waf-token' && String(c.value || '').length > 50);
      if (waf && waf.value) {
        latestSharedWafToken = waf.value;
        latestSharedWafAt = Date.now();
        return latestSharedWafToken;
      }
    } catch {}
  }

  // 2. Coalesce concurrent requests so we only launch one solver:
  if (wafSolvePromise) return wafSolvePromise;

  wafSolvePromise = (async () => {
    let browser = null;
    try {
      const launched = await launchStealthSwiggyBrowser();
      browser = launched.browser;
      const page = launched.page;

      await page.goto('https://www.swiggy.com/', {
        waitUntil: 'domcontentloaded',
        timeout: 30000
      }).catch(() => {});

      const token = await waitForSwiggyWafCookie(page, SWIGGY_WAF_COOKIE_WAIT_MS);
      if (token) {
        latestSharedWafToken = token;
        latestSharedWafAt = Date.now();
        // Allow challenge reload/navigation to settle
        await new Promise(r => setTimeout(r, 1500));
      }
      await browser.close().catch(() => {});
      return latestSharedWafToken || '';
    } catch (err) {
      if (browser) await browser.close().catch(() => {});
      console.warn('[SwiggyBridge] WAF solver error:', err.message);
      return latestSharedWafToken || '';
    } finally {
      wafSolvePromise = null;
    }
  })();

  return wafSolvePromise;
}

export async function safeEvaluateAuthOnce(page, fn, ...args) {
  let timeoutId;
  try {
    const executeEval = async () => {
      try {
        return await page.evaluate(fn, ...args);
      } catch (err) {
        if (/execution context was destroyed|most likely because of a navigation/i.test(err.message)) {
          console.warn('[SwiggyBridge] Page navigated/reloaded during evaluate; waiting for document ready to retry...');
          await new Promise(r => setTimeout(r, 2000));
          await page.waitForFunction(() => document.readyState === 'complete', { timeout: 6000 }).catch(() => {});
          return await page.evaluate(fn, ...args);
        }
        throw err;
      }
    };

    return await Promise.race([
      executeEval(),
      new Promise((_, reject) => {
        timeoutId = setTimeout(
          () => reject(new Error(`Auth browser request timed out after ${AUTH_PAGE_EVALUATE_TIMEOUT_MS}ms; no automatic retry was attempted.`)),
          AUTH_PAGE_EVALUATE_TIMEOUT_MS
        );
      })
    ]);
  } finally {
    if (timeoutId) clearTimeout(timeoutId);
  }
}

export function parseSwiggyOtpError(otpResult) {
  if (!otpResult) {
    return {
      code: 'NO_RESPONSE',
      retryable: true,
      message: 'Swiggy ne OTP request ka response nahi diya. Network check karke baad mein ek baar retry karein.',
      swiggyStatus: 'No Response',
      details: 'Empty response from Swiggy'
    };
  }

  const swiggyMsg = (otpResult.data?.statusMessage || otpResult.data?.message || '').trim();
  const rawLower = ((otpResult.rawText || '') + ' ' + swiggyMsg).toLowerCase();
  const status = Number(otpResult.status || 0);
  const swiggyCode = Number(otpResult.data?.statusCode);

  if (status === 429 || swiggyCode === 429 || /rate limit|too many|limit reached|maximum attempts/.test(rawLower)) {
    return {
      code: 'SWIGGY_RATE_LIMIT',
      retryable: false,
      message: 'Swiggy ne OTP requests par temporary limit lagayi hai. Abhi dobara request na bhejein; 15–30 minute rukkar official Swiggy app/site se try karein. Repeated attempts limit ko badha sakte hain.',
      swiggyStatus: swiggyMsg || 'Swiggy Rate Limit (429 Too Many Requests)',
      details: `HTTP ${status || 429} | Swiggy rate limit`
    };
  }

  if (status === 403 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic/.test(rawLower)) {
    return {
      code: 'SWIGGY_SECURITY_CHALLENGE',
      retryable: false,
      message: 'Swiggy security verification stopped this OTP request. This bot will not retry or bypass that check. Complete any verification in the official Swiggy app/site, or use an existing session export; try again later only if Swiggy allows it.',
      swiggyStatus: swiggyMsg || 'Security challenge (HTTP 403)',
      details: `HTTP ${status || 403} | Swiggy security challenge; no automated retry attempted`
    };
  }

  if (status === 400 || status === 422 || /invalid mobile|valid 10 digit/.test(rawLower)) {
    return {
      code: 'INVALID_MOBILE',
      retryable: false,
      message: `Swiggy rejected the number (${swiggyMsg || 'invalid format'}). Send a standalone valid Indian mobile number: 10 digits, or 12 digits beginning with 91.`,
      swiggyStatus: swiggyMsg || 'Invalid Mobile Number',
      details: `HTTP ${status || 400}`
    };
  }

  if ([500, 502, 503, 504].includes(status)) {
    return {
      code: 'SWIGGY_SERVER_ERROR',
      retryable: true,
      message: `Swiggy returned a temporary server error (HTTP ${status}). Wait a minute or two before retrying.`,
      swiggyStatus: swiggyMsg || `Swiggy Server Error (${status})`,
      details: `HTTP ${status}`
    };
  }

  if (otpResult.error) {
    return {
      code: 'SYSTEM_ERROR',
      retryable: true,
      message: `Could not complete the OTP request: ${otpResult.error}`,
      swiggyStatus: otpResult.error,
      details: 'Network or browser context error'
    };
  }

  if (swiggyMsg) {
    return {
      code: 'SWIGGY_ERROR',
      retryable: false,
      message: `Swiggy rejected the OTP request: ${swiggyMsg} (HTTP ${status || 200}).`,
      swiggyStatus: swiggyMsg,
      details: `HTTP ${status || 200} | Swiggy Code: ${otpResult.data?.statusCode ?? 'none'}`
    };
  }

  return {
    code: 'SWIGGY_ERROR',
    retryable: false,
    message: `Swiggy did not confirm the OTP request (HTTP ${status || 'unknown'}). Check the official Swiggy app/site or try an existing session export.`,
    swiggyStatus: `HTTP ${status || 'unknown'} - OTP not confirmed`,
    details: `HTTP ${status || 'unknown'}`
  };
}
export async function requestSwiggyOtpViaBridge(userId, phone, targetAcc = '', targetAccName = null) {
  const cleanPhone = normalizeIndianMobileNumber(phone) || '';

  if (cleanPhone.length !== 10) {
    return { success: false, message: 'Send a standalone 10-digit Indian mobile number or a 12-digit number beginning with 91.' };
  }

  let browser;
  let page;
  let isReused = false;

  if (
    activeSessions[userId] &&
    activeSessions[userId].needsName &&
    activeSessions[userId].phone === cleanPhone &&
    activeSessions[userId].browser?.connected &&
    activeSessions[userId].page
  ) {
    console.log(`! [SwiggyBridge] Reusing warm browser session for ${cleanPhone} with name "${targetAccName}"...`);
    browser = activeSessions[userId].browser;
    page = activeSessions[userId].page;
    isReused = true;
    if (activeSessions[userId].safetyTimer) {
      clearTimeout(activeSessions[userId].safetyTimer);
    }
  } else {
    if (activeSessions[userId]) {
      try {
        if (activeSessions[userId].safetyTimer) clearTimeout(activeSessions[userId].safetyTimer);
        await activeSessions[userId].browser.close();
      } catch (e) {}
      delete activeSessions[userId];
    }

    let isUsable = false;
    if (prewarmedPage && prewarmedBrowser?.connected && (Date.now() - prewarmedAt < 180000)) {
      try {
        await Promise.race([
          prewarmedPage.evaluate(() => 1),
          new Promise((_, reject) => setTimeout(() => reject(new Error('Ping timeout')), 1200))
        ]);
        isUsable = true;
      } catch (pingErr) {
        isUsable = false;
      }
    }

    if (isUsable) {
      browser = prewarmedBrowser;
      page = prewarmedPage;
      prewarmedBrowser = null;
      prewarmedPage = null;
      console.log(`! [SwiggyBridge] Using primed Chrome for instantaneous OTP to ${cleanPhone}...`);
    } else {
      if (prewarmedBrowser) {
        await prewarmedBrowser.close().catch(() => {});
        prewarmedBrowser = null;
        prewarmedPage = null;
      }

      const launched = await launchStealthSwiggyBrowser();
      browser = launched.browser;
      page = launched.page;
      await page.goto('https://www.swiggy.com/', { waitUntil: 'domcontentloaded', timeout: 30000 }).catch(() => {});
      const wafToken = await waitForSwiggyWafCookie(page, SWIGGY_WAF_COOKIE_WAIT_MS);
      if (!wafToken) {
        console.warn('[SwiggyBridge] No WAF cookie was issued in the normal browser session; the OTP endpoint will be tried once, and any challenge will be honored.');
      } else {
        await new Promise(r => setTimeout(r, 2000));
      }
    }
  }

  try {
    // Ensure the page document context is ready and stable before evaluate
    try {
      await page.waitForFunction(() => document.readyState === 'complete', { timeout: 5000 }).catch(() => {});
    } catch (e) {}

    // Ensure clean unauthenticated cookie context inside browser before triggering fresh OTP / Re-Login!
    const existingBrowserCookies = await page.cookies();
    const staleAuthCookies = existingBrowserCookies.filter(c => ['_session_tid', 'tid', 'token', '_is_logged_in'].includes(c.name));
    if (staleAuthCookies.length > 0) {
      await page.deleteCookie(...staleAuthCookies).catch(() => {});
    }

    let otpResult;
    if (isReused && targetAccName) {
      otpResult = { status: 200, data: { statusCode: 1, statusMessage: 'not registered' } };
    } else {
      otpResult = await safeEvaluateAuthOnce(page, async (mobileNumber) => {
        try {
          const headers = {
            'Content-Type': 'application/json',
            'Accept': 'application/json'
          };

          let res = await fetch('/dapi/auth/sms-otp', {
            method: 'POST',
            headers,
            body: JSON.stringify({ mobile: mobileNumber }),
            credentials: 'include',
            signal: AbortSignal.timeout(8000)
          });

          let rawText = await res.text().catch(() => '');
          let data = {};
          try { data = JSON.parse(rawText); } catch (e) {}
          const responseLower = `${rawText} ${data.statusMessage || data.message || ''}`.toLowerCase();
          const blockedOrLimited = res.status === 403 || res.status === 429 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic|rate limit|too many|limit reached/.test(responseLower);

          if (!blockedOrLimited && ((res.status !== 200 && res.status !== 202) || (data.statusCode && data.statusCode !== 0 && data.statusCode !== 1))) {
            try {
              const altRes = await fetch('/dapi/auth/otp-generate', {
                method: 'POST',
                headers,
                body: JSON.stringify({ mobile: mobileNumber }),
                credentials: 'include',
                signal: AbortSignal.timeout(8000)
              });
              const altText = await altRes.text().catch(() => '');
              const altData = JSON.parse(altText);
              if (altRes.status === 200 && (altData.statusCode === 0 || !altData.statusCode)) {
                return { status: altRes.status, data: altData, rawText: altText, endpoint: 'otp-generate' };
              }
            } catch (e) {}
          }

          return { status: res.status, data, rawText };
        } catch (err) {
          return { status: 500, error: err.message };
        }
      }, cleanPhone);
    }

    console.log('[SwiggyBridge] OTP dispatch raw result for ' + cleanPhone + ':', JSON.stringify(otpResult));

    const msgLower = `${otpResult.data?.statusMessage || ''} ${otpResult.data?.message || ''} ${otpResult.rawText || ''}`.toLowerCase();
    const isRateOrInvalid =
      msgLower.includes('rate limit') ||
      msgLower.includes('too many') ||
      msgLower.includes('limit reached') ||
      msgLower.includes('maximum') ||
      msgLower.includes('valid 10 digit');
    const isSecurityBlocked = otpResult.status === 403 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic/.test(msgLower);
    const acceptedOtpResponse = otpResult.status === 200 || otpResult.status === 202;

    // Only treat a confirmed ordinary API response as an unregistered account. A WAF/challenge
    // response must never fall through to signup or an alternate OTP flow.
    const isUnregistered = acceptedOtpResponse && otpResult.data?.statusCode === 1 && !isRateOrInvalid && !isSecurityBlocked;

    if (isUnregistered) {
      const hasRealName = targetAccName &&
        !/^user\s*\d*$/i.test(String(targetAccName).trim()) &&
        !/^acc_\d+$/i.test(String(targetAccName).trim()) &&
        !/^\d+$/.test(String(targetAccName).trim()) &&
        String(targetAccName).trim().length >= 2;

      if (!hasRealName) {
        console.log(`[SwiggyBridge] Number ${cleanPhone} is a NEW ACCOUNT on Swiggy. Keeping browser warm and requesting user's name.`);
        const safetyTimer = setTimeout(() => {
          if (activeSessions[userId]?.needsName) {
            console.log(`[SwiggyBridge] Session for ${cleanPhone} timed out waiting for name. Closing browser.`);
            activeSessions[userId].browser?.close().catch(() => {});
            delete activeSessions[userId];
          }
        }, 180000);

        activeSessions[userId] = {
          browser,
          page,
          phone: cleanPhone,
          targetAcc: targetAcc || `acc_${cleanPhone}`,
          needsName: true,
          isNewUser: true,
          safetyTimer,
          createdAt: Date.now()
        };

        return {
          success: false,
          needsName: true,
          isNewUser: true,
          phone: cleanPhone,
          message: 'New account detected on Swiggy. Please enter the name for this account.'
        };
      }

      const signupName = sanitizeSwiggyName(targetAccName);
      // Unique email prevents collision with any previous archived/deleted Swiggy account on the same mobile number!
      const signupEmail = generateUniqueSwiggyEmail(cleanPhone, signupName);
      console.log(`[SwiggyBridge] Number ${cleanPhone} unregistered/fresh on Swiggy. Triggering signup OTP as "${signupName}" (${signupEmail})...`);

      const signupInitResult = await safeEvaluateAuthOnce(page, async (mobileNumber, name, email) => {
        try {
          const headers = {
            'Content-Type': 'application/json',
            'Accept': 'application/json'
          };
          const res = await fetch('https://www.swiggy.com/dapi/auth/signup', {
            method: 'POST',
            headers,
            body: JSON.stringify({
              mobile: mobileNumber,
              name,
              email
            }),
            credentials: 'include',
            signal: AbortSignal.timeout(8000)
          });
          const text = await res.text().catch(() => '');
          let data = {};
          try { data = JSON.parse(text); } catch (e) {}
          return { status: res.status, data, rawText: text };
        } catch (err) {
          return { status: 500, error: err.message };
        }
      }, cleanPhone, signupName, signupEmail);

      console.log('[SwiggyBridge] Signup dispatch raw result:', JSON.stringify(signupInitResult));
      const signupResponseLower = `${signupInitResult.rawText || ''} ${signupInitResult.data?.statusMessage || signupInitResult.data?.message || ''}`.toLowerCase();
      const signupBlocked = signupInitResult.status === 403 || signupInitResult.status === 429 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic|rate limit|too many|limit reached/.test(signupResponseLower);
      const signupSent = !signupBlocked && (signupInitResult.status === 200 || signupInitResult.status === 202) && (
        signupInitResult.data?.statusCode === 0 || !signupInitResult.data?.statusCode
      );

      if (signupSent) {
        const safetyTimer = setTimeout(() => {
          if (activeSessions[userId]?.phone === cleanPhone) {
            activeSessions[userId].browser?.close().catch(() => {});
            delete activeSessions[userId];
          }
        }, 300000);

        activeSessions[userId] = {
          browser,
          page,
          phone: cleanPhone,
          targetAcc: targetAcc || `acc_${cleanPhone}`,
          targetAccName: String(targetAccName || signupName).trim() || signupName,
          signupName,
          signupEmail,
          isNewUser: true,
          safetyTimer,
          createdAt: Date.now()
        };

        return {
          success: true,
          phone: cleanPhone,
          isNewUser: true,
          accountName: String(targetAccName || signupName).trim() || signupName,
          message: 'OTP Sent',
          swiggyStatus: 'OTP Sent'
        };
      } else {
        await browser.close().catch(() => {});
        const parsedErr = parseSwiggyOtpError(signupInitResult);
        if (process.env.PREWARM_CHROME === 'true') setTimeout(() => prewarmBrowser().catch(() => {}), 1000);
        return {
          success: false,
          code: parsedErr.code,
          retryable: parsedErr.retryable,
          message: parsedErr.message,
          swiggyStatus: parsedErr.swiggyStatus,
          details: parsedErr.details
        };
      }
    }

    const isSent = !isRateOrInvalid && !isSecurityBlocked && acceptedOtpResponse && (
      otpResult.data?.statusCode === 0 || !otpResult.data?.statusCode
    );

    if (isSent) {
      const safetyTimer = setTimeout(() => {
        if (activeSessions[userId]?.phone === cleanPhone) {
          console.log(`[SwiggyBridge] Session for ${cleanPhone} timed out after 5 mins. Closing browser.`);
          activeSessions[userId].browser?.close().catch(() => {});
          delete activeSessions[userId];
        }
      }, 300000);

      activeSessions[userId] = {
        browser,
        page,
        phone: cleanPhone,
        targetAcc: targetAcc || `acc_${cleanPhone}`,
        targetAccName: targetAccName || null,
        isNewUser: false,
        safetyTimer,
        createdAt: Date.now()
      };

      return {
        success: true,
        phone: cleanPhone,
        message: 'OTP Sent',
        swiggyStatus: 'OTP Sent'
      };
    } else {
      await browser.close().catch(() => {});
      const parsedErr = parseSwiggyOtpError(otpResult);
      if (process.env.PREWARM_CHROME === 'true') setTimeout(() => prewarmBrowser().catch(() => {}), 1000);
      return {
        success: false,
        code: parsedErr.code,
        retryable: parsedErr.retryable,
        message: parsedErr.message,
        swiggyStatus: parsedErr.swiggyStatus,
        details: parsedErr.details
      };
    }
  } catch (err) {
    if (browser) await browser.close().catch(() => {});
    delete activeSessions[userId];
    if (process.env.PREWARM_CHROME === 'true') setTimeout(() => prewarmBrowser().catch(() => {}), 1000);
    const lower = String(err.message || '').toLowerCase();
    const inferredStatus = /429|rate limit|too many requests/.test(lower)
      ? 429
      : (/403|waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic/.test(lower) ? 403 : 500);
    const diagnostic = parseSwiggyOtpError({
      status: inferredStatus,
      error: err.message,
      data: { statusMessage: err.message }
    });
    return {
      success: false,
      code: diagnostic.code,
      retryable: diagnostic.retryable,
      message: diagnostic.message,
      swiggyStatus: diagnostic.swiggyStatus,
      details: err.stack ? err.stack.split('\n')[0] : diagnostic.details
    };
  }
}

export async function requestSwiggyDeleteOtpViaBridge(userId, phone, targetAcc = '', targetAccName = null) {
  const cleanPhone = normalizeIndianMobileNumber(phone) || '';
  if (!cleanPhone) {
    return { success: false, code: 'INVALID_MOBILE', message: 'Send a standalone 10-digit Indian mobile number or a 12-digit number beginning with 91.' };
  }

  delete activeDeleteSessions[userId];

  const { getDb } = await import('./store.js');
  const db = getDb();
  let acc = db.config?.accounts?.[targetAcc];

  let rawCookieString = acc?.cookies || '';
  if (!rawCookieString && cleanPhone) {
    for (const [k, a] of Object.entries(db.config?.accounts || {})) {
      if ((a.phone === cleanPhone || k === `acc_${cleanPhone}`) && a.cookies) {
        rawCookieString = a.cookies;
        acc = a;
        targetAcc = k;
        break;
      }
    }
  }

  // Always strip stale `aws-waf-token` so AWS WAF never returns a false 403!
  let cookieString = stripStaleWafCookie(rawCookieString);

  if (!cookieString) {
    return {
      success: false,
      isAuthError: true,
      message: 'Account session cookies not found. Please log in first or remove account from Bot DB.'
    };
  }

  const isAuth = checkLoggedInFromCookies(cookieString) || checkLoggedInFromCookies(acc);
  if (!isAuth) {
    return {
      success: false,
      isAuthError: true,
      message: 'Selected account session is logged out or expired. Re-login or remove from Bot DB.'
    };
  }

  deleteOtpRequestCount++;
  const reqNum = deleteOtpRequestCount;
  const maskedPhone = cleanPhone.length >= 4 ? '******' + cleanPhone.slice(-4) : '***';
  console.log(`[SwiggyDelete] [Request #${reqNum}] Triggering Delete OTP: GET /mapi/auth/delete/userCheck | Target: ${targetAcc} | Phone: ${maskedPhone}`);

  try {
    let status = 0;
    let data = {};
    let mergedCookies = cookieString;

    const res = await fetch('https://www.swiggy.com/mapi/auth/delete/userCheck', {
      method: 'GET',
      headers: {
        'Cookie': cookieString,
        'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1',
        'Accept': 'application/json',
        'Referer': 'https://www.swiggy.com/my-account/settings',
        'Origin': 'https://www.swiggy.com'
      },
      signal: AbortSignal.timeout(10000)
    });

    status = res.status;
    const rawText = await res.text().catch(() => '');
    try { data = JSON.parse(rawText); } catch { data = {}; }
    const responseLower = `${rawText} ${data.statusMessage || data.message || data.error || ''}`.toLowerCase();
    const setCookies = typeof res.headers.getSetCookie === 'function' ? res.headers.getSetCookie() : [];
    if (setCookies.length > 0) {
      mergedCookies = mergeSetCookiesIntoJar(cookieString, setCookies);
    }

    if (status === 403 || status === 202 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic/.test(responseLower)) {
      delete activeDeleteSessions[userId];
      return {
        success: false,
        code: 'SWIGGY_SECURITY_CHALLENGE',
        retryable: false,
        message: 'Swiggy security verification stopped the deletion OTP request. No automated retry was attempted. Complete any check in the official Swiggy app/site, or remove the account from this bot only.',
        swiggyStatus: `HTTP ${status} security challenge`,
        details: `HTTP ${status} | Swiggy security challenge; no automated retry attempted`
      };
    }

    console.log(`[SwiggyDelete] [Request #${reqNum}] Response: HTTP ${status} | SwiggyCode: ${data.statusCode ?? 'none'} | Message: ${data.statusMessage || data.error || 'ok'}`);

    const isSent = status === 200 && (data.statusCode === 28 || data.statusCode === 0);

    if (!isSent) {
      if (status === 429 || /rate limit|too many|limit reached|maximum attempts/.test(responseLower)) {
        return {
          success: false,
          code: 'SWIGGY_RATE_LIMIT',
          retryable: false,
          message: 'Swiggy rate-limited the deletion OTP request. Wait 15–30 minutes and finish deletion through the official Swiggy app/site; do not retry repeatedly.',
          details: 'HTTP 429 | Swiggy rate limit'
        };
      }
      const isAuthError = status === 401 || data.statusCode === 1 || (data.statusMessage && data.statusMessage.toLowerCase().includes('login'));
      const errMsg = isAuthError
        ? 'Swiggy session has expired on Swiggy servers. Re-login or remove this account from Bot DB.'
        : (data.statusMessage || data.error || `Swiggy returned status ${status} (code ${data.statusCode ?? 'unknown'})`);
      return {
        success: false,
        isAuthError,
        message: errMsg,
        swiggyStatus: errMsg
      };
    }

    activeDeleteSessions[userId] = {
      accountKey: targetAcc,
      phone: cleanPhone,
      tid: data.tid || '',
      csrfToken: data.csrfToken || '',
      sid: data.sid || '',
      deviceId: data.deviceId || '',
      cookies: mergedCookies,
      createdAt: Date.now()
    };

    return {
      success: true,
      phone: cleanPhone,
      message: data.statusMessage || 'Archive OTP Sent',
      swiggyStatus: 'Swiggy Account Deletion OTP sent to ' + cleanPhone
    };
  } catch (err) {
    console.error(`[SwiggyDelete] [Request #${reqNum}] Exception calling /mapi/auth/delete/userCheck:`, err.message);
    return {
      success: false,
      message: 'Failed to contact Swiggy deletion endpoint: ' + err.message
    };
  }
}

export async function verifyAndDeleteSwiggyAccountViaBridge(userId, otp, accountKey) {
  const session = activeDeleteSessions[userId];
  const cleanOtp = String(otp).replace(/[^0-9]/g, '').trim();

  if (cleanOtp.length !== 6) {
    return { success: false, message: 'Please enter the exact 6-digit OTP.' };
  }

  const { getDb } = await import('./store.js');
  const db = getDb();
  const acc = db.config?.accounts?.[accountKey];
  const phone = session?.phone || acc?.phone || accountKey.replace('acc_', '');
  const cookieString = stripStaleWafCookie(session?.cookies || acc?.cookies || '');
  const csrfToken = session?.csrfToken || '';
  const tid = session?.tid || acc?.tid || '';

  if (!cookieString) {
    return {
      success: false,
      message: 'Deletion session or cookies expired. Please tap Delete Account again to get a fresh OTP.'
    };
  }

  deleteVerifyRequestCount++;
  const reqNum = deleteVerifyRequestCount;
  const maskedPhone = phone.length >= 4 ? '******' + phone.slice(-4) : '***';
  console.log(`[SwiggyDelete] [Verify #${reqNum}] Verifying Delete OTP: POST /mapi/auth/delete/user | Target: ${accountKey} | Phone: ${maskedPhone}`);

  try {
    let status = 0;
    let verifyResult = null;
    const fullCookieHeader = cookieString + (tid && !cookieString.includes('tid=') ? `; tid=${tid}` : '') + (csrfToken ? `; _csrf=${csrfToken}` : '');

    const res = await fetch('https://www.swiggy.com/mapi/auth/delete/user', {
      method: 'POST',
      headers: {
        'Cookie': fullCookieHeader,
        'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1',
        'Content-Type': 'application/json',
        'Accept': 'application/json',
        'Origin': 'https://www.swiggy.com',
        'Referer': 'https://www.swiggy.com/my-account/settings'
      },
      body: JSON.stringify({ otp: cleanOtp, _csrf: csrfToken }),
      signal: AbortSignal.timeout(10000)
    });

    status = res.status;
    const rawText = await res.text().catch(() => '');
    try { verifyResult = JSON.parse(rawText); } catch { verifyResult = {}; }
    const responseLower = `${rawText} ${verifyResult?.statusMessage || verifyResult?.message || verifyResult?.error || ''}`.toLowerCase();

    if (status === 403 || status === 202 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic/.test(responseLower)) {
      delete activeDeleteSessions[userId];
      return {
        success: false,
        code: 'SWIGGY_SECURITY_CHALLENGE',
        retryable: false,
        message: 'Swiggy security verification stopped the deletion request. No automated retry was attempted. Finish account deletion in the official Swiggy app/site.',
        details: `HTTP ${status} | Swiggy security challenge; no automated retry attempted`
      };
    }

    console.log(`[SwiggyDelete] [Verify #${reqNum}] Response: HTTP ${status} | SwiggyCode: ${verifyResult?.statusCode ?? 'none'} | Message: ${verifyResult?.statusMessage || verifyResult?.error || 'ok'}`);

    if (status === 429 || /rate limit|too many|limit reached|maximum attempts/.test(responseLower)) {
      delete activeDeleteSessions[userId];
      return {
        success: false,
        code: 'SWIGGY_RATE_LIMIT',
        retryable: false,
        message: 'Swiggy rate-limited deletion verification. Wait 15–30 minutes and use the official Swiggy app/site; do not repeatedly resend the OTP.',
        details: 'HTTP 429 | Swiggy rate limit'
      };
    }

    if (!verifyResult || verifyResult.error) {
      return {
        success: false,
        message: verifyResult?.error || 'Failed to communicate with Swiggy servers. Please try again.'
      };
    }

    if (verifyResult.statusCode === 29) {
      return {
        success: false,
        message: verifyResult.statusMessage || 'Invalid OTP. Please check and re-enter.'
      };
    }

    if (verifyResult.statusCode === 25) {
      delete activeDeleteSessions[userId];
      return { success: false, message: 'You have pending cancellation charges. Please clear them first on Swiggy.' };
    }
    if (verifyResult.statusCode === 26) {
      delete activeDeleteSessions[userId];
      return { success: false, message: 'You have an ongoing order. Please try after delivery.' };
    }
    if (verifyResult.statusCode === 34) {
      delete activeDeleteSessions[userId];
      return { success: false, message: 'Cannot delete: active Swiggy Money wallet exists.' };
    }

    const isSuccess = (verifyResult.statusCode === 33 || verifyResult.statusCode === 0 || (status === 200 && verifyResult.statusCode === undefined));

    if (isSuccess) {
      delete activeDeleteSessions[userId];
      return {
        success: true,
        phone,
        message: verifyResult.statusMessage || 'Account permanently deleted from Swiggy servers!'
      };
    }

    return {
      success: false,
      message: verifyResult.statusMessage || `Deletion blocked by Swiggy (Code ${verifyResult.statusCode})`
    };
  } catch (err) {
    console.error(`[SwiggyDelete] [Verify #${reqNum}] Error in delete OTP verification:`, err.message);
    return { success: false, message: err.message };
  }
}

export async function verifySwiggyOtpViaBridge(userId, otp) {
  const session = activeSessions[userId];
  if (!session) {
    return { success: false, message: 'Session expired. Please enter phone number again.' };
  }

  const cleanOtp = String(otp).replace(/[^0-9]/g, '').trim();
  if (cleanOtp.length !== 6) {
    return { success: false, message: 'Please enter the exact 6-digit OTP.' };
  }

  const { browser, page, phone, targetAcc } = session;

  try {
    const pageCookies = await page.cookies();
    const wafCookie = pageCookies.find(c => c.name === 'aws-waf-token');
    const wafToken = wafCookie?.value || '';

    let verifyResult = null;
    let statusCode = null;
    let statusMsg = '';
    let isSuccess = false;

    if (!session.isNewUser) {
      try {
        verifyResult = await safeEvaluateAuthOnce(page, async (mobileNumber, otpCode) => {
          try {
            const headers = {
              'Content-Type': 'application/json',
              'Accept': 'application/json'
            };
            const res = await fetch('/dapi/auth/otp-verify', {
              method: 'POST',
              headers,
              body: JSON.stringify({ mobile: mobileNumber, otp: otpCode }),
              credentials: 'include',
              signal: AbortSignal.timeout(8000)
            });
            const rawText = await res.text().catch(() => '');
            let data = {};
            try { data = JSON.parse(rawText); } catch {}
            return { status: res.status, data, rawText };
          } catch (err) {
            return { status: 500, error: err.message };
          }
        }, phone, cleanOtp);
      } catch (evalErr) {
        console.log('[SwiggyBridge] Evaluation error during verify:', evalErr.message);
        verifyResult = { status: 500, error: evalErr.message };
      }

      console.log(`[SwiggyBridge] Verify raw result for ${phone}:`, JSON.stringify(verifyResult));
      statusCode = verifyResult?.data?.statusCode;
      statusMsg = (verifyResult?.data?.statusMessage || '').trim();
      isSuccess = (verifyResult?.status === 200 || verifyResult?.status === 202) && statusCode === 0;

      const verifyLower = `${verifyResult?.rawText || ''} ${statusMsg} ${verifyResult?.data?.message || ''}`.toLowerCase();
      const verificationBlocked = verifyResult?.status === 403 || /waf|captcha|challenge|forbidden|security check|access denied|verify you are human|bot verification|automated traffic/.test(verifyLower);
      const verificationRateLimited = verifyResult?.status === 429 || /rate limit|too many|limit reached|maximum attempts/.test(verifyLower);
      if (verificationBlocked || verificationRateLimited) {
        if (session.safetyTimer) clearTimeout(session.safetyTimer);
        await browser.close().catch(() => {});
        delete activeSessions[userId];
        const diagnostic = parseSwiggyOtpError({ status: verifyResult?.status, data: verifyResult?.data, rawText: verifyResult?.rawText });
        return {
          success: false,
          code: diagnostic.code,
          retryable: false,
          swiggyStatus: diagnostic.swiggyStatus,
          message: diagnostic.message
        };
      }
    }

    const isUnregistered =
      session.isNewUser ||
      statusCode === 999 ||
      statusMsg.toLowerCase().includes('not registered') ||
      statusMsg.toLowerCase().includes('invalid mobile number') ||
      statusMsg.toLowerCase().includes('user not found');

    if (statusCode === 1 && !isUnregistered) {
      if (session.safetyTimer) clearTimeout(session.safetyTimer);
      session.safetyTimer = setTimeout(() => {
        if (activeSessions[userId]?.phone === phone) {
          activeSessions[userId].browser?.close().catch(() => {});
          delete activeSessions[userId];
        }
      }, 180000);

      return {
        success: false,
        swiggyStatus: statusMsg || 'Galat OTP (Invalid OTP)',
        message: statusMsg || 'Galat OTP enter kiya hai. Kripya check karke dubara daalein.'
      };
    }

    const hasSessionName = session.targetAccName &&
      !/^user\s*\d*$/i.test(String(session.targetAccName).trim()) &&
      !/^acc_\d+$/i.test(String(session.targetAccName).trim()) &&
      !/^\d+$/.test(String(session.targetAccName).trim()) &&
      String(session.targetAccName).trim().length >= 2;

    if (isUnregistered && !hasSessionName) {
      session.otp = cleanOtp;
      session.isNewUser = true;
      return {
        success: false,
        isNewUser: true,
        phone,
        message: 'New account detected on Swiggy. Please enter the name for this account.'
      };
    }

    if (isUnregistered) {
      const signupName = sanitizeSwiggyName(session.targetAccName);
      const signupEmail = session.signupEmail || generateUniqueSwiggyEmail(phone, signupName);
      session.signupEmail = signupEmail;
      console.log(`[SwiggyBridge] Completing fresh Swiggy signup for ${phone} as "${signupName}" (${signupEmail})...`);

      let signupResult = null;
      try {
        signupResult = await safeEvaluateAuthOnce(page, async (mobileNumber, otpCode, name, email) => {
          try {
            const headers = {
              'Content-Type': 'application/json',
              'Accept': 'application/json'
            };
            const res = await fetch('https://www.swiggy.com/dapi/auth/signup', {
              method: 'POST',
              headers,
              body: JSON.stringify({
                mobile: mobileNumber,
                otp: otpCode,
                name,
                email
              }),
              credentials: 'include',
              signal: AbortSignal.timeout(8000)
            });
            const rawText = await res.text().catch(() => '');
            let data = {};
            try { data = JSON.parse(rawText); } catch {}
            return { status: res.status, data, rawText };
          } catch (err) {
            return { status: 500, error: err.message };
          }
        }, phone, cleanOtp, signupName, signupEmail);
      } catch (signupErr) {
        console.log('[SwiggyBridge] Signup evaluation error:', signupErr.message);
        signupResult = { status: 500, error: signupErr.message };
      }

      console.log('[SwiggyBridge] Signup raw result:', JSON.stringify(signupResult));
      if (signupResult?.status === 200 && (signupResult?.data?.statusCode === 0 || !signupResult?.data?.statusCode)) {
        verifyResult = signupResult;
        statusCode = 0;
        statusMsg = 'done successfully';
        isSuccess = true;
      } else {
        const errMessage = signupResult?.data?.statusMessage || signupResult?.error || 'Invalid or expired Signup OTP';
        const diagnostic = signupResult ? parseSwiggyOtpError(signupResult) : null;
        if (diagnostic && ['SWIGGY_SECURITY_CHALLENGE', 'SWIGGY_RATE_LIMIT'].includes(diagnostic.code)) {
          if (session.safetyTimer) clearTimeout(session.safetyTimer);
          await browser.close().catch(() => {});
          delete activeSessions[userId];
          return {
            success: false,
            code: diagnostic.code,
            retryable: false,
            swiggyStatus: diagnostic.swiggyStatus,
            message: diagnostic.message
          };
        }
        return {
          success: false,
          swiggyStatus: errMessage,
          message: errMessage
        };
      }
    }

    const cookies = await waitForSwiggyLoginCookies(page, 800);
    const isReallyLoggedIn = checkLoggedInFromCookies(cookies);

    if (!isSuccess && !isReallyLoggedIn) {
      if (session.safetyTimer) clearTimeout(session.safetyTimer);
      session.safetyTimer = setTimeout(() => {
        if (activeSessions[userId]?.phone === phone) {
          activeSessions[userId].browser?.close().catch(() => {});
          delete activeSessions[userId];
        }
      }, 180000);

      const errReason = statusMsg || verifyResult?.error || (verifyResult?.status === 429 ? 'Maximum OTP verification attempts exceeded' : 'Invalid or expired OTP');
      return {
        success: false,
        swiggyStatus: errReason,
        message: errReason
      };
    }

    if (session.safetyTimer) {
      clearTimeout(session.safetyTimer);
    }

    const swiggyActualName = (verifyResult?.data?.data?.name || session.targetAccName || '').trim();
    const swiggyEmail = verifyResult?.data?.data?.email || session.signupEmail || '';
    const requestedAccountLabel = String(session.targetAccName || '').trim();
    const cleanActual = swiggyActualName.replace(/\([^)]*\)/g, '').trim();
    const finalName = (requestedAccountLabel && !/^user\s*\d+$/i.test(requestedAccountLabel) && !/^acc_\d+$/i.test(requestedAccountLabel))
      ? requestedAccountLabel
      : (cleanActual || getNextAutoUserName());
    const accKey = targetAcc || `acc_${phone}`;

    const tidCookie = cookies.find(c => c.name === 'tid');
    const sidCookie = cookies.find(c => c.name === '_sid');
    const deviceCookie = cookies.find(c => c.name === '_device_id');
    const tokenCookie = cookies.find(c => c.name === 'token');
    const jwtPayload = decodeJwtPayload(tidCookie?.value);
    const customerId = (jwtPayload && jwtPayload.user_id && jwtPayload.user_id !== '0')
      ? jwtPayload.user_id
      : (verifyResult?.data?.data?.user_id || verifyResult?.data?.data?.id || 'RegisteredUser');

    const fullCookieStr = cleanEssentialSwiggyCookies(
      cookies.map(c => `${c.name}=${c.value}`).join('; '),
      { tid: tidCookie?.value || '', sid: sidCookie?.value || '', deviceId: deviceCookie?.value || '', token: tokenCookie?.value || '' }
    );

    console.log(`[SwiggyBridge] Auto-claiming 50 off on 199 for Breakfast & Late Night offers on ${phone}...`);
    const offersResult = await claimSwiggyBreakfastAndLateNightOffers({
      phone,
      token: tokenCookie?.value || '',
      tid: tidCookie?.value || '',
      cookies: fullCookieStr
    });

    const savedData = {
      name: finalName,
      swiggyName: cleanActual || finalName || '',
      botTag: rawSlot,
      email: swiggyEmail,
      phone,
      mobile: phone,
      customerId,
      tid: tidCookie?.value || '',
      sid: sidCookie?.value || '',
      deviceId: deviceCookie?.value || '',
      token: tokenCookie?.value || tidCookie?.value || '',
      isLoggedIn: true,
      cookies: fullCookieStr,
      offers: offersResult,
      savedAt: new Date().toISOString()
    };

    updateAccount(accKey, savedData);

    await browser.close().catch(() => {});
    delete activeSessions[userId];

    // Full 100% session code including complete Swiggy auth `cookies`
    const exportJson = {
      account: accKey,
      name: finalName,
      swiggyName: cleanActual || '',
      botTag: rawSlot,
      mobile: phone,
      phone,
      customerId,
      token: savedData.token,
      tid: savedData.tid,
      sid: savedData.sid,
      deviceId: savedData.deviceId,
      cookies: fullCookieStr,
      savedAt: savedData.savedAt
    };

    return {
      success: true,
      isNewUser: false,
      name: finalName,
      swiggyName: cleanActual || '',
      botTag: rawSlot,
      accountKey: accKey,
      phone,
      customerId,
      offers: offersResult,
      exportJson,
      message: verifyResult?.data?.statusMessage || 'done successfully',
      swiggyStatus: verifyResult?.data?.statusMessage || 'done successfully'
    };
  } catch (err) {
    return {
      success: false,
      isNewUser: false,
      swiggyStatus: err.message,
      message: `System Error: ${err.message}`
    };
  }
}

export async function signupSwiggyViaBridge(userId, enteredName) {
  const session = activeSessions[userId];
  if (!session || !session.otp) {
    return { success: false, message: 'Session expired. Please enter phone number again.' };
  }

  const { browser, page, phone, otp } = session;
  const cleanName = sanitizeSwiggyName(enteredName);
  const accountLabel = String(enteredName || cleanName).trim() || cleanName;
  const signupEmail = session.signupEmail || generateUniqueSwiggyEmail(phone, cleanName);
  const accKey = session.targetAcc || `acc_${phone}`;

  try {
    const signupResult = await safeEvaluateAuthOnce(page, async (mobileNumber, otpCode, name, email) => {
      try {
        const headers = {
          'Content-Type': 'application/json',
          'Accept': 'application/json'
        };
        const res = await fetch('https://www.swiggy.com/dapi/auth/signup', {
          method: 'POST',
          headers,
          body: JSON.stringify({
            mobile: mobileNumber,
            otp: otpCode,
            name,
            email
          }),
          credentials: 'include',
          signal: AbortSignal.timeout(8000)
        });
        const rawText = await res.text().catch(() => '');
        let data = {};
        try { data = JSON.parse(rawText); } catch {}
        return { status: res.status, data, rawText };
      } catch (err) {
        return { status: 500, error: err.message };
      }
    }, phone, otp, cleanName, signupEmail);

    const cookies = await waitForSwiggyLoginCookies(page, 800);
    const isReallyLoggedIn = checkLoggedInFromCookies(cookies);

    if (
      isReallyLoggedIn ||
      (signupResult?.status === 200 && signupResult?.data?.statusCode === 0)
    ) {
      const tidCookie = cookies.find(c => c.name === 'tid');
      const sidCookie = cookies.find(c => c.name === '_sid');
      const deviceCookie = cookies.find(c => c.name === '_device_id');
      const tokenCookie = cookies.find(c => c.name === 'token');
      const jwtPayload = decodeJwtPayload(tidCookie?.value);
      const customerId = (jwtPayload && jwtPayload.user_id && jwtPayload.user_id !== '0')
        ? jwtPayload.user_id
        : (signupResult?.data?.data?.user_id || signupResult?.data?.data?.id || 'RegisteredUser');

      const fullCookieStr = cleanEssentialSwiggyCookies(
        cookies.map(c => `${c.name}=${c.value}`).join('; '),
        { tid: tidCookie?.value || '', sid: sidCookie?.value || '', deviceId: deviceCookie?.value || '', token: tokenCookie?.value || '' }
      );

      const offersResult = await claimSwiggyBreakfastAndLateNightOffers({
        phone,
        token: tokenCookie?.value || '',
        tid: tidCookie?.value || '',
        cookies: fullCookieStr
      });

      const savedData = {
        name: accountLabel,
        swiggyName: cleanName,
        phone,
        mobile: phone,
        customerId,
        tid: tidCookie?.value || '',
        sid: sidCookie?.value || '',
        deviceId: deviceCookie?.value || '',
        token: tokenCookie?.value || tidCookie?.value || '',
        isLoggedIn: true,
        cookies: fullCookieStr,
        offers: offersResult,
        savedAt: new Date().toISOString()
      };

      updateAccount(accKey, savedData);

      await browser.close().catch(() => {});
      delete activeSessions[userId];

      const exportJson = {
        account: accKey,
        name: accountLabel,
        swiggyName: cleanName,
        mobile: phone,
        phone,
        customerId,
        token: savedData.token,
        tid: savedData.tid,
        sid: savedData.sid,
        deviceId: savedData.deviceId,
        cookies: fullCookieStr,
        savedAt: savedData.savedAt
      };

      return {
        success: true,
        name: accountLabel,
        swiggyName: cleanName,
        accountKey: accKey,
        phone,
        customerId,
        offers: offersResult,
        exportJson,
        message: 'Swiggy account created and logged in successfully!'
      };
    } else {
      const errorMsg =
        signupResult?.data?.statusMessage ||
        signupResult?.error ||
        'Failed to signup on Swiggy';
      const diagnostic = parseSwiggyOtpError(signupResult || {});
      if (['SWIGGY_SECURITY_CHALLENGE', 'SWIGGY_RATE_LIMIT'].includes(diagnostic.code)) {
        if (session.safetyTimer) clearTimeout(session.safetyTimer);
        await browser.close().catch(() => {});
        delete activeSessions[userId];
        return {
          success: false,
          code: diagnostic.code,
          retryable: false,
          message: diagnostic.message,
          swiggyStatus: diagnostic.swiggyStatus
        };
      }
      return { success: false, message: errorMsg };
    }
  } catch (err) {
    const diagnostic = parseSwiggyOtpError({
      status: /429|rate limit|too many/i.test(err.message || '') ? 429 : (/403|waf|captcha|challenge|forbidden/i.test(err.message || '') ? 403 : 500),
      error: err.message,
      data: { statusMessage: err.message }
    });
    if (['SWIGGY_SECURITY_CHALLENGE', 'SWIGGY_RATE_LIMIT'].includes(diagnostic.code)) {
      if (session.safetyTimer) clearTimeout(session.safetyTimer);
      await browser.close().catch(() => {});
      delete activeSessions[userId];
      return { success: false, code: diagnostic.code, retryable: false, message: diagnostic.message };
    }
    return { success: false, code: diagnostic.code, retryable: diagnostic.retryable, message: err.message };
  }
}

// Closes any open browser session cleanly without destroying exported tokens unless revokeRemote = true
export async function deactivateSwiggyAccountViaBridge(userId, targetAcc, revokeRemote = false) {
  const session = activeSessions[userId];
  if (session) {
    try {
      if (session.safetyTimer) clearTimeout(session.safetyTimer);
      if (session.browser) {
        await session.browser.close().catch(() => {});
      }
    } catch (e) {}
    delete activeSessions[userId];
  }
  delete activeDeleteSessions[userId];

  if (revokeRemote) {
    try {
      const { getDb } = await import('./store.js');
      const db = getDb();
      const acc = db.config?.accounts?.[targetAcc];
      const cleanCk = stripStaleWafCookie(acc?.cookies || '');
      if (cleanCk) {
        await fetch('https://www.swiggy.com/dapi/auth/logout', {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
            'Accept': 'application/json',
            'User-Agent': 'Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X)',
            'Cookie': cleanCk
          },
          body: '{}',
          signal: AbortSignal.timeout(3000)
        }).catch(() => {});
      }
    } catch (e) {}
  }

  return true;
}
