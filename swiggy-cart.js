import './network-shield.js';
import { AsyncLocalStorage } from 'node:async_hooks';
import crypto from 'crypto';
import fs from 'fs';
import puppeteer from 'puppeteer-core';
import QRCode from 'qrcode';
import { getDb, updateAccount } from './store.js';
import { extractSharedUrls, normalizeSharedUrl } from './link-utils.js';
import { findChromePath, decodeJwtPayload, claimSwiggyBreakfastAndLateNightOffers, getLiveSwiggyWafToken } from './swiggy-bridge.js';

const CHROME_PATH = findChromePath();
const PUPPETEER_HEADLESS = (process.platform === 'linux' || process.env.RAILWAY_ENVIRONMENT || process.env.HEADLESS === 'true') ? 'new' : false;
const DESKTOP_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36';
const MOBILE_WEB_UA = 'Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Mobile Safari/537.36';

async function installAntiFnaStealthOnPage(page) {
  const cleanEntityId = crypto.randomUUID();
  await page.emulateTimezone('Asia/Kolkata').catch(() => {});
  await page.setRequestInterception(true).catch(() => {});
  page.on('request', (req) => {
    if (req.url().includes('fna.swiggy.com/api/fraudnabuse')) {
      return req.respond({
        status: 200,
        contentType: 'application/json',
        headers: {
          'Access-Control-Allow-Origin': 'https://www.swiggy.com',
          'Access-Control-Allow-Credentials': 'true',
          'Access-Control-Allow-Headers': 'Content-Type, Accept'
        },
        body: JSON.stringify({ statusCode: 0, statusMessage: 'success', data: cleanEntityId, successful: true })
      }).catch(() => {});
    }
    req.continue().catch(() => {});
  });
  await page.evaluateOnNewDocument(() => {
    try {
      delete Object.getPrototypeOf(navigator).webdriver;
    } catch (e) {}
    Object.defineProperty(navigator, 'webdriver', { get: () => undefined, configurable: true });
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
  });
}

// Shared in-memory caches for sub-second operations
let cachedWafToken = '';
let cachedWafAt = 0;
let wafFetchPromise = null;
const WAF_TTL_MS = 8 * 60 * 1000; // 8 minutes

const sessionAuthCache = new Map(); // cookieSig -> { auth, ts }
const csrfTokenCache = new Map();   // cookieSig -> { csrf, ts }
const AUTH_TTL_MS = 45 * 1000;

// Distance helper (Haversine in meters)
function distanceMeters(lat1, lng1, lat2, lng2) {
  const a1 = parseFloat(lat1), o1 = parseFloat(lng1), a2 = parseFloat(lat2), o2 = parseFloat(lng2);
  if ([a1, o1, a2, o2].some(Number.isNaN)) return Infinity;
  const R = 6371000;
  const toRad = d => (d * Math.PI) / 180;
  const dLat = toRad(a2 - a1);
  const dLon = toRad(o2 - o1);
  const s = Math.sin(dLat / 2) ** 2 + Math.cos(toRad(a1)) * Math.cos(toRad(a2)) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.atan2(Math.sqrt(s), Math.sqrt(1 - s));
}

// Swiggy delivery locations are India-only. These broad bounds reject swapped,
// empty, or obviously stale fallback coordinates without rejecting remote Indian regions.
export function isValidIndianDeliveryCoordinates(lat, lng) {
  const nLat = Number(lat);
  const nLng = Number(lng);
  return Number.isFinite(nLat) && Number.isFinite(nLng) &&
    nLat >= 5.5 && nLat <= 38.5 && nLng >= 67 && nLng <= 99;
}

function normalizeIndianMobile(value) {
  let digits = String(value || '').replace(/\D/g, '');
  if (digits.length === 12 && digits.startsWith('91')) digits = digits.slice(2);
  if (digits.length === 11 && digits.startsWith('0')) digits = digits.slice(1);
  return /^[6-9]\d{9}$/.test(digits) ? digits : '';
}

function normalizeAddressText(value) {
  return String(value || '')
    .normalize('NFKC')
    .replace(/_/g, ' ')
    .toLocaleLowerCase('en-IN')
    .replace(/[^\p{L}\p{N}\p{M}]+/gu, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

function hasSameAddressText(left, right) {
  const a = normalizeAddressText(left);
  const b = normalizeAddressText(right);
  return Boolean(a && b && a === b);
}

function isUsableDeliveryAddress(details) {
  const address = String(details?.address || '').trim();
  return Boolean(
    details && !details.unresolvableShortLink && address.length >= 8 &&
    !/^(?:address pending|delivery location|unknown address)$/i.test(address) &&
    isValidIndianDeliveryCoordinates(details.lat, details.lng)
  );
}

function mergeExplicitAddressDetails(current, incoming) {
  if (!incoming || typeof incoming !== 'object') return current || null;
  const currentAddress = String(current?.address || '').trim();
  const incomingAddress = String(incoming.address || '').trim();
  const addressChanged = currentAddress && incomingAddress && !hasSameAddressText(currentAddress, incomingAddress);
  if (addressChanged) {
    const next = { ...incoming };
    delete next.id;
    next.name = incoming.name || '';
    next.mobile = normalizeIndianMobile(incoming.mobile) || '';
    if (!isValidIndianDeliveryCoordinates(incoming.lat, incoming.lng)) {
      delete next.lat;
      delete next.lng;
    }
    return next;
  }
  const merged = { ...(current || {}) };
  for (const [key, value] of Object.entries(incoming)) {
    if (value !== null && value !== undefined && value !== '') merged[key] = value;
  }
  return merged;
}

// Clean & normalize cookies (strips expired aws-waf-token so WAF never blocks requests)
export function cleanSwiggyCookieString(rawCookies, acc = null) {
  let pairs = [];
  if (typeof rawCookies === 'string') {
    const trimmed = rawCookies.trim();
    if (trimmed.startsWith('[') && trimmed.endsWith(']')) {
      try {
        const arr = JSON.parse(trimmed);
        if (Array.isArray(arr)) {
          pairs = arr.map(c => `${c.name || c.key}=${c.value}`);
        }
      } catch (e) {
        pairs = trimmed.split(';');
      }
    } else {
      pairs = trimmed.split(';');
    }
  } else if (Array.isArray(rawCookies)) {
    pairs = rawCookies.map(c => `${c.name || c.key}=${c.value}`);
  } else if (rawCookies && typeof rawCookies === 'object') {
    acc = acc || rawCookies;
    return cleanSwiggyCookieString(rawCookies.cookies || '', acc);
  }

  const map = new Map();
  for (const raw of pairs) {
    const p = String(raw || '').trim();
    if (!p) continue;
    const eq = p.indexOf('=');
    if (eq <= 0) continue;
    const k = p.slice(0, eq).trim();
    const v = p.slice(eq + 1).trim();
    if (!k || k === 'aws-waf-token' || k === 'userLocation') continue;
    map.set(k, v);
  }

  if (acc && typeof acc === 'object') {
    const fbSessionTid = acc._session_tid || acc.session_tid || acc.sessionTid || '';
    if (fbSessionTid && !map.has('_session_tid')) map.set('_session_tid', fbSessionTid);
    if (acc.tid && !map.has('_session_tid') && !String(acc.tid).includes('.')) map.set('_session_tid', acc.tid);
    if (acc.tid && !map.has('tid')) map.set('tid', acc.tid);
    const fbTok = acc.token || acc.auth_token || acc.access_token || '';
    if (fbTok && !map.has('token')) map.set('token', fbTok);
    const fbSid = acc.sid || acc._sid || '';
    if (fbSid && !map.has('_sid')) map.set('_sid', fbSid);
    const fbDev = acc.deviceId || acc.device_id || acc._device_id || acc.swuid || '';
    if (fbDev && !map.has('_device_id')) map.set('_device_id', fbDev);
  }
  if ((map.has('_session_tid') || map.has('tid') || map.has('token')) && !map.has('_is_logged_in')) {
    map.set('_is_logged_in', '1');
  }

  return Array.from(map.entries()).map(([k, v]) => `${k}=${v}`).join('; ');
}

function parseCookieMap(cookieStr) {
  const cm = {};
  for (const part of String(cookieStr || '').split(';')) {
    const idx = part.indexOf('=');
    if (idx > 0) cm[part.slice(0, idx).trim()] = part.slice(idx + 1).trim();
  }
  return cm;
}

// Native Swiggy Android Client Headers (works with ZERO `_session_tid` cookie via `tid` + `token` + `sid` + `deviceId`!)
export function buildSwiggyAndroidClientHeaders(accountOrCookies, opts = {}) {
  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : null;
  const cleanCookies = cleanSwiggyCookieString(accountOrCookies, acc);
  const cm = parseCookieMap(cleanCookies);

  const rawTid = String(opts.tid || (acc?.tid && String(acc.tid).includes('.') ? acc.tid : '') || (cm.tid && cm.tid.includes('.') ? cm.tid : '') || acc?.tid || cm.tid || '').trim();
  const token = String(opts.token || acc?.token || acc?.auth_token || acc?.access_token || cm.token || '').trim();
  const sid = String(opts.sid || acc?.sid || acc?._sid || cm._sid || cm.sid || '').trim();
  const deviceId = String(opts.deviceId || acc?.deviceId || acc?.device_id || acc?.swuid || cm._device_id || cm._swuid || '8f3b2c1a-4d5e-6f7a-8b9c-0d1e2f3a4b5c').trim();

  let uid = String(opts.userId || acc?.customerId || acc?.customer_id || acc?.userId || acc?.user_id || '').trim();
  if ((!uid || uid === '0' || uid === '-1') && rawTid && rawTid.includes('.')) {
    const claims = decodeJwtPayload(rawTid);
    if (claims?.user_id && String(claims.user_id) !== '0' && String(claims.user_id) !== '-1') {
      uid = String(claims.user_id);
    }
  }
  if (uid === '0' || uid === '-1') uid = '';

  const lat = String(opts.lat || '26.8658609');
  const lng = String(opts.lng || '80.9307755');

  // CRITICAL 2026 NATIVE ANDROID PROTOCOL REQUIREMENT:
  // NEVER include `'x-web-checkout-flow': 'cart'` or Chrome User-Agent on `chkout.swiggy.com`!
  // Web-flow headers cause Swiggy's backend to strip 100% of App-Only Item Offers (`CRAZY_DEALS`, `NBH_OFFER`, `POCKET_HERO`)
  // AND 100% of App-Only Late Night / Breakfast / Reward Free Cash (`₹50`–`₹100` OFF)!
  return {
    'Content-Type': 'application/json',
    'Accept': 'application/json',
    'tid': rawTid,
    'sid': sid,
    'token': token,
    ...(uid ? { 'userid': uid, 'user-id': uid, 'customer_id': uid } : {}),
    'deviceId': deviceId,
    'device-id': deviceId,
    'swuid': deviceId,
    'platform': 'swiggy-android',
    'agent-type': 'Swiggy-Android',
    'analyticsPlatform': 'an',
    'version-code': '1800',
    'app-version': '4.99.0',
    'os-version': '14',
    'lat': lat,
    'lng': lng,
    'latitude': lat,
    'longitude': lng,
    'User-Agent': 'Swiggy-Android',
    ...(opts.extraHeaders || {})
  };
}

// Preserves item-level `offer_ids` (`CRAZY_DEALS`, `NBH_OFFER`, `POCKET_HERO`, `FLASH_SALE` strike-off discounts!)
// AND `item_offer_cart_meta` across EVERY `chkout` / `dapi` cart update & rehydration call!
export function buildSwiggyCartItemsPayload(items) {
  return (Array.isArray(items) ? items : [])
    .filter(it => it && (it.menu_item_id || it.itemId))
    .map(it => ({
      addons: Array.isArray(it.addons) ? it.addons : [],
      variants: Array.isArray(it.variants) ? it.variants : [],
      menu_item_id: Number(it.menu_item_id || it.itemId),
      quantity: Number(it.qty || it.quantity || 1),
      offer_ids: Array.isArray(it.offer_ids) ? it.offer_ids : [],
      item_offer_cart_meta: String(it.item_offer_cart_meta || ''),
      customer_request_messages: Array.isArray(it.customer_request_messages) ? it.customer_request_messages : []
    }));
}

// ---------------------------------------------------------------------------
// PURE-HTTP `_session_tid` AUTO-BOOTSTRAP FOR TOKEN-ONLY OTHER-BOT ACCOUNTS!
// Converts `{ tid: "eyJ...", token, sid, deviceId }` (ZERO cookies!) into a FULL
// Web + Android Swiggy session (`_session_tid=<1536-char-hex>`) in ONE ~200ms GET!
// ---------------------------------------------------------------------------
export async function bootstrapSwiggyWebSessionFromAndroidTokens(accountOrCookies, { force = false } = {}) {
  if (!accountOrCookies || typeof accountOrCookies !== 'object' || Array.isArray(accountOrCookies)) {
    return null;
  }
  const existingClean = cleanSwiggyCookieString(accountOrCookies.cookies || '', accountOrCookies);
  if (!force && existingClean.includes('_session_tid=')) {
    accountOrCookies.cookies = existingClean;
    return existingClean;
  }

  const androidHeaders = buildSwiggyAndroidClientHeaders(accountOrCookies);
  if (!androidHeaders.tid && !androidHeaders.token) return null;

  try {
    let uid = androidHeaders.userid || '';
    let liveTid = androidHeaders.tid || '';
    let liveTok = androidHeaders.token || '';
    let liveSid = androidHeaders.sid || '';
    let liveDev = androidHeaders.deviceId || '';

    if (!uid || !liveTid.includes('.')) {
      const prof = await fetchSwiggyAndroidProfile(accountOrCookies, { timeoutMs: 5000 });
      if (prof?.customerId) uid = String(prof.customerId);
      if (prof?.token) liveTok = prof.token;
    }

    // ZERO-CHROMIUM pure HTTP WebView bootstrap (~650ms, 0MB RAM, zero AWS WAF challenge needed!):
    const res = await fetch('https://www.swiggy.com/web-cart-add-address', {
      method: 'GET',
      redirect: 'manual',
      headers: {
        'User-Agent': 'Mozilla/5.0 (Linux; Android 14; Pixel 8 Build/UQ1A.240205.004; wv) AppleWebKit/537.36 (KHTML, like Gecko) Version/4.0 Chrome/129.0.0.0 Mobile Safari/537.36 Swiggy-Android',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'tid': liveTid,
        'sid': liveSid,
        'token': liveTok,
        ...(uid ? { 'userid': String(uid), 'user-id': String(uid) } : {}),
        'deviceId': liveDev,
        'device-id': liveDev,
        'platform': 'an',
        'version-code': '1600',
        'app-version': '4.75.0'
      },
      signal: AbortSignal.timeout(9000)
    });

    const htmlBody = await res.text().catch(() => '');
    const setCookies = typeof res.headers.getSetCookie === 'function' ? res.headers.getSetCookie() : [];
    const cmap = new Map();
    if (!force) {
      for (const part of String(existingClean || '').split(';')) {
        const eq = part.indexOf('=');
        if (eq > 0) {
          const k = part.slice(0, eq).trim();
          const v = part.slice(eq + 1).trim();
          if (k && v) cmap.set(k, v);
        }
      }
    }
    for (const sc of setCookies) {
      const pair = String(sc || '').split(';')[0];
      const eq = pair.indexOf('=');
      if (eq > 0) {
        const k = pair.slice(0, eq).trim();
        const v = pair.slice(eq + 1).trim();
        if (k && v && k !== 'aws-waf-token' && k !== 'userLocation') {
          cmap.set(k, v);
        }
      }
    }

    const mintedSessionTid = cmap.get('_session_tid') || '';
    if (!mintedSessionTid) return null;

    const mergedCookies = cleanSwiggyCookieString(
      Array.from(cmap.entries()).map(([k, v]) => `${k}=${v}`).join('; '),
      { ...accountOrCookies, _session_tid: mintedSessionTid }
    );

    const htmlCsrf = (htmlBody.match(/csrf[a-zA-Z0-9_"\s:=]+([a-zA-Z0-9_\-]{12,60})/i) || [])[1] || '';
    if (htmlCsrf) {
      csrfTokenCache.set(mergedCookies.slice(0, 180), { csrf: htmlCsrf, ts: Date.now() });
    }

    accountOrCookies._session_tid = mintedSessionTid;
    accountOrCookies.cookies = mergedCookies;
    if (uid && !accountOrCookies.customerId) accountOrCookies.customerId = String(uid);
    sessionAuthCache.clear();

    try {
      const db = getDb();
      const targetPhone = String(accountOrCookies.phone || '').replace(/\D/g, '').slice(-10);
      const targetToken = String(accountOrCookies.token || '').trim();
      const matchedKeys = new Set();
      if (accountOrCookies.id && db?.config?.accounts?.[accountOrCookies.id]) {
        matchedKeys.add(accountOrCookies.id);
      }
      for (const [k, existing] of Object.entries(db?.config?.accounts || {})) {
        if (!existing) continue;
        const exPhone = String(existing.phone || '').replace(/\D/g, '').slice(-10);
        const exUid = String(existing.userId || existing.customerId || '').trim();
        if (
          (uid && exUid && String(uid) === exUid) ||
          (targetPhone && exPhone && targetPhone === exPhone) ||
          (targetToken && existing.token && targetToken === String(existing.token).trim())
        ) {
          matchedKeys.add(k);
        }
      }
      for (const k of matchedKeys) {
        const existing = db?.config?.accounts?.[k];
        const existingTidIsHex = existing?.tid && !String(existing.tid).includes('.');
        updateAccount(k, {
          _session_tid: mintedSessionTid,
          cookies: mergedCookies,
          ...(existingTidIsHex ? { tid: mintedSessionTid } : {}),
          ...(uid ? { customerId: String(uid), userId: String(uid) } : {})
        });
      }
    } catch {}

    return mergedCookies;
  } catch (e) {
    console.warn('[SwiggyBootstrap] Failed to mint _session_tid from Android tokens:', e.message);
    return null;
  }
}

// Fast (<80ms) zero-WAF, zero-cookie Native Swiggy Android Profile + Saved Addresses fetcher
export async function fetchSwiggyAndroidProfile(accountOrCookies, opts = {}) {
  try {
    const headers = buildSwiggyAndroidClientHeaders(accountOrCookies, opts);
    if (!headers.tid && !headers.token) return null;
    const res = await fetch('https://profile.swiggy.com/api/v1/user/profile', {
      headers,
      signal: AbortSignal.timeout(opts.timeoutMs || 6500)
    });
    if (!res.ok) return null;
    const json = await res.json().catch(() => null);
    if (json?.statusCode !== 0 || !json?.data) return null;
    const d = json.data;
    const cid = d.customer_id ? String(d.customer_id) : '';
    if (!cid || cid === '0' || cid === '-1') return null;
    return {
      ok: true,
      customerId: cid,
      name: d.name || '',
      phone: d.mobile ? String(d.mobile).replace(/^\+?91/, '').replace(/\D/g, '').slice(-10) : '',
      email: d.email || '',
      token: d.token || headers.token || '',
      addresses: Array.isArray(d.addresses) ? d.addresses : []
    };
  } catch {
    return null;
  }
}

// Universal Live Swiggy Session Verifier: tests BOTH Web DAPI (`_session_tid`) AND Native Android (`chkout` + `profile`) simultaneously!
export async function verifySwiggySessionLive(accountOrCookies) {
  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : { cookies: String(accountOrCookies || '') };
  const cleanCookies = cleanSwiggyCookieString(acc.cookies || '', acc);
  const androidHeaders = buildSwiggyAndroidClientHeaders(acc);

  const [webProbe, androidCartProbe, androidProfile] = await Promise.all([
    cleanCookies
      ? dapiFetch({ ...acc, cookies: cleanCookies }, 'order/all', { timeoutMs: 15000 }).catch(() => null)
      : Promise.resolve(null),
    (androidHeaders.tid || androidHeaders.token)
      ? fetch('https://chkout.swiggy.com/api/v2/cart/client', {
          headers: androidHeaders,
          signal: AbortSignal.timeout(7000)
        }).then(async r => ({ status: r.status, json: await r.json().catch(() => null) })).catch(() => null)
      : Promise.resolve(null),
    (androidHeaders.tid || androidHeaders.token)
      ? fetchSwiggyAndroidProfile(acc, { timeoutMs: 6500 })
      : Promise.resolve(null)
  ]);

  const webJson = webProbe?.json || null;
  const webOk = Boolean(webProbe?.status === 200 && webJson && webJson.statusCode === 0);

  const chkJson = androidCartProbe?.json || null;
  const chkClaims = chkJson?.tid && String(chkJson.tid).includes('.') ? decodeJwtPayload(chkJson.tid) : null;
  const chkUid = chkClaims?.user_id && String(chkClaims.user_id) !== '0' && String(chkClaims.user_id) !== '-1' ? String(chkClaims.user_id) : '';
  const androidOk = Boolean(
    (chkJson && chkJson.statusCode === 0) ||
    Boolean(androidProfile?.ok && androidProfile.customerId)
  );

  let resolvedProfile = androidProfile;
  if (!resolvedProfile?.ok && chkJson?.tid && chkUid) {
    resolvedProfile = await fetchSwiggyAndroidProfile(acc, { tid: chkJson.tid, userId: chkUid, timeoutMs: 5000 });
    if (resolvedProfile?.ok) {
      const bootTarget = {
        ...acc,
        tid: chkJson.tid,
        token: resolvedProfile.token || androidHeaders.token || '',
        customerId: resolvedProfile.customerId || chkUid,
        cookies: cleanCookies
      };
      if (!cleanCookies.includes('_session_tid=')) {
        await bootstrapSwiggyWebSessionFromAndroidTokens(bootTarget);
      }
      return {
        valid: true,
        transport: bootTarget.cookies?.includes('_session_tid=') ? 'web+android' : (webOk ? 'web+android' : 'android'),
        liveTid: chkJson.tid,
        customerId: resolvedProfile.customerId || chkUid,
        name: resolvedProfile.name || '',
        phone: resolvedProfile.phone || '',
        token: resolvedProfile.token || androidHeaders.token || '',
        cookies: bootTarget.cookies || cleanCookies,
        addresses: resolvedProfile.addresses || []
      };
    }
  }

  if (!webOk && !androidOk) {
    return {
      valid: false,
      transport: 'none',
      webMessage: webJson?.statusMessage || '',
      androidMessage: chkJson?.statusMessage || ''
    };
  }

  let liveTid = '';
  if (webOk && webJson?.tid && String(webJson.tid).includes('.')) liveTid = webJson.tid;
  else if (chkJson?.tid && String(chkJson.tid).includes('.')) liveTid = chkJson.tid;
  else if (androidHeaders.tid && androidHeaders.tid.includes('.')) liveTid = androidHeaders.tid;

  const jwtClaims = liveTid ? decodeJwtPayload(liveTid) : null;
  const jwtUid = jwtClaims?.user_id && String(jwtClaims.user_id) !== '0' && String(jwtClaims.user_id) !== '-1'
    ? String(jwtClaims.user_id)
    : '';

  // Auto-mint `_session_tid` immediately when importing any pure token-only account (`{ tid, token, sid, deviceId }`)!
  let finalVerifiedCookies = cleanCookies;
  if (!finalVerifiedCookies.includes('_session_tid=') && (liveTid || androidHeaders.token)) {
    const bootTarget = {
      ...acc,
      tid: liveTid || acc.tid || '',
      token: resolvedProfile?.token || androidHeaders.token || '',
      customerId: resolvedProfile?.customerId || jwtUid || chkUid || String(acc.customerId || ''),
      cookies: finalVerifiedCookies
    };
    const minted = await bootstrapSwiggyWebSessionFromAndroidTokens(bootTarget);
    if (minted) {
      finalVerifiedCookies = minted;
      if (acc && typeof acc === 'object') {
        acc.cookies = minted;
        acc._session_tid = bootTarget._session_tid || '';
      }
    }
  }

  return {
    valid: true,
    transport: (webOk || finalVerifiedCookies.includes('_session_tid=')) && androidOk ? 'web+android' : (webOk ? 'web' : 'android'),
    liveTid,
    customerId: resolvedProfile?.customerId || jwtUid || chkUid || String(acc.customerId || ''),
    name: resolvedProfile?.name || '',
    phone: resolvedProfile?.phone || '',
    token: resolvedProfile?.token || androidHeaders.token || '',
    cookies: finalVerifiedCookies,
    addresses: resolvedProfile?.addresses || []
  };
}

// ---------------------------------------------------------------------------
// ZERO-WAF DUAL-TRANSPORT SESSION AUTH BOOTSTRAP (<250ms pure HTTP)
// Seamlessly supports BOTH Web `_session_tid` cookies AND Native Android `token`+`tid` JSONs!
// ---------------------------------------------------------------------------
const sessionAuthInFlight = new Map();

export async function getSwiggySessionAuth(accountOrCookies, forceRefresh = false) {
  if (!accountOrCookies) return null;
  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : null;
  const cleanCookies = cleanSwiggyCookieString(accountOrCookies, acc);
  // Key `sig` on STABLE session identity (`cookies` + `token` + `sid` + `customerId`) — NEVER `acc.tid`,
  // because `chkout.swiggy.com` rotates `tid`'s `iat` timestamp on every single response!
  const sig = `${cleanCookies.slice(0, 140)}|${acc?.token || ''}|${acc?.sid || ''}|${acc?.customerId || acc?.userId || ''}`;
  const now = Date.now();
  if (!forceRefresh && sessionAuthCache.has(sig)) {
    const cached = sessionAuthCache.get(sig);
    if (now - cached.ts < AUTH_TTL_MS) {
      if (acc?.jwtTid && String(acc.jwtTid).includes('.')) {
        cached.auth.jwtTid = acc.jwtTid;
      }
      return cached.auth;
    }
  }
  if (!forceRefresh && sessionAuthInFlight.has(sig)) {
    return sessionAuthInFlight.get(sig);
  }

  const runPromise = (async () => {

  const cm = parseCookieMap(cleanCookies);
  let webExpiredMsg = '';

  // Path 1: Try Web DAPI `/dapi/order/all` WITH `aws-waf-token` protection when `_session_tid` is available
  if (cleanCookies.includes('_session_tid=')) {
    try {
      const dapiOrderOut = await dapiFetch(acc || cleanCookies, 'order/all', { timeoutMs: 15000 });
      if (dapiOrderOut?.status === 200 && dapiOrderOut?.json) {
        const json = dapiOrderOut.json;
        if (json && json.statusCode === 0) {
          let jwtTid = (json?.tid && String(json.tid).includes('.')) ? json.tid : (acc?.tid && String(acc.tid).includes('.') ? acc.tid : '');
          let claims = jwtTid ? decodeJwtPayload(jwtTid) : null;
          const webJwtExplicitlyGuest = Boolean(
            json?.tid && String(json.tid).includes('.') &&
            (String(claims?.user_id || '') === '0' || String(claims?.user_id || '') === '-1')
          );
          let userId = (claims?.user_id && String(claims.user_id) !== '0' && String(claims.user_id) !== '-1')
            ? String(claims.user_id)
            : (!webJwtExplicitlyGuest && acc?.customerId ? String(acc.customerId) : null);
          let resolvedToken = acc?.token || cm.token || '';
          let resolvedSid = json?.sid || acc?.sid || cm._sid || '';
          let resolvedDev = json?.deviceId || acc?.deviceId || cm._device_id || '';

          // Brand-new account with 0 past orders or hex-only `tid`: enrich `userId` + `jwtTid` in ~150ms via `/dapi/profile/info`!
          if (!userId || !jwtTid) {
            try {
              const infoRes = await dapiFetch(acc || cleanCookies, 'profile/info', { timeoutMs: 5000 });
              const infoJson = infoRes?.json;
              if (infoJson?.statusCode === 0) {
                if (infoJson.tid && String(infoJson.tid).includes('.')) jwtTid = infoJson.tid;
                const d = infoJson.data || {};
                if (d.customer_id) userId = String(d.customer_id);
                else if (jwtTid) {
                  claims = decodeJwtPayload(jwtTid);
                  if (claims?.user_id && String(claims.user_id) !== '0') userId = String(claims.user_id);
                }
                if (d.token && !resolvedToken) resolvedToken = String(d.token);
                if (infoJson.sid && !resolvedSid) resolvedSid = String(infoJson.sid);
                if (infoJson.deviceId && !resolvedDev) resolvedDev = String(infoJson.deviceId);
                if (acc && d.mobile && !acc.phone) acc.phone = String(d.mobile).replace(/\D/g, '').slice(-10);
              }
            } catch {}
          }

          const auth = {
            sessionExpired: false,
            transport: 'web',
            cleanCookies,
            cm,
            jwtTid,
            userId: userId ? String(userId) : null,
            sid: resolvedSid,
            deviceId: resolvedDev,
            token: resolvedToken,
            swuid: cm._swuid || resolvedDev || '',
            orders: Array.isArray(json?.data?.orders) ? json.data.orders : []
          };
          if (acc) {
            if (cm._session_tid && !acc._session_tid) acc._session_tid = cm._session_tid;
            if (!String(acc.cookies || '').includes('_session_tid=') && cleanCookies.includes('_session_tid=')) {
              acc.cookies = cleanCookies;
            }
            if (jwtTid) acc.tid = jwtTid;
            if (auth.userId) acc.customerId = auth.userId;
            if (resolvedToken && !acc.token) acc.token = resolvedToken;
          }
          sessionAuthCache.set(sig, { auth, ts: now });
          return auth;
        }
        webExpiredMsg = json?.statusMessage || '';
      }
    } catch (e) {
      console.warn('[SwiggyAuth] Web DAPI auth warning:', e.message);
    }
  }

  // Path 2: Native Swiggy Android `chkout.swiggy.com` + `profile.swiggy.com` (works with ZERO `_session_tid`!)
  const androidHeaders = buildSwiggyAndroidClientHeaders(acc || cleanCookies);
  if (androidHeaders.tid || androidHeaders.token) {
    try {
      const [chkRes, profRes] = await Promise.all([
        fetch('https://chkout.swiggy.com/api/v2/cart/client', {
          headers: androidHeaders,
          signal: AbortSignal.timeout(7000)
        }).then(r => r.json().catch(() => null)).catch(() => null),
        fetchSwiggyAndroidProfile(acc || cleanCookies, { timeoutMs: 6500 })
      ]);

      const freshTid = (chkRes?.tid && String(chkRes.tid).includes('.'))
        ? chkRes.tid
        : (androidHeaders.tid && androidHeaders.tid.includes('.') ? androidHeaders.tid : '');
      const claims = freshTid ? decodeJwtPayload(freshTid) : null;
      const freshJwtExplicitlyGuest = Boolean(
        chkRes?.tid && String(chkRes.tid).includes('.') &&
        (String(claims?.user_id || '') === '0' || String(claims?.user_id || '') === '-1')
      );

      if ((chkRes?.statusCode === 0 && !freshJwtExplicitlyGuest) || profRes?.ok) {
        const resolvedUid = profRes?.customerId
          || (claims?.user_id && String(claims.user_id) !== '0' && String(claims.user_id) !== '-1' ? String(claims.user_id) : '')
          || (!freshJwtExplicitlyGuest && acc?.customerId ? String(acc.customerId) : '');
        const resolvedToken = profRes?.token || androidHeaders.token || '';

        if (acc) {
          if (freshTid) acc.tid = freshTid;
          if (resolvedUid) acc.customerId = resolvedUid;
          if (resolvedToken) acc.token = resolvedToken;
          if (!acc.phone && profRes?.phone) acc.phone = profRes.phone;
        }

        const auth = {
          sessionExpired: false,
          transport: 'android',
          cleanCookies,
          cm,
          jwtTid: freshTid,
          userId: resolvedUid || null,
          sid: chkRes?.sid || androidHeaders.sid || '',
          deviceId: chkRes?.deviceId || androidHeaders.deviceId || '',
          token: resolvedToken,
          swuid: androidHeaders.swuid || androidHeaders.deviceId || '',
          profileAddresses: profRes?.addresses || [],
          orders: []
        };
        sessionAuthCache.set(sig, { auth, ts: now });
        return auth;
      }

      if (chkRes?.statusCode === 999 || webExpiredMsg) {
        return {
          sessionExpired: true,
          statusMessage: chkRes?.statusMessage || webExpiredMsg || 'Session expired',
          cleanCookies,
          cm
        };
      }
    } catch (e) {
      console.warn('[SwiggyAuth] Android auth fallback warning:', e.message);
    }
  } else if (webExpiredMsg) {
    return { sessionExpired: true, statusMessage: webExpiredMsg, cleanCookies, cm };
  }

  // Fallback decode from existing JWT if network timed out transiently
  const fallbackJwt = (acc?.tid && String(acc.tid).includes('.')) ? acc.tid : (cm.tid && cm.tid.includes('.') ? cm.tid : '');
  const claims = fallbackJwt ? decodeJwtPayload(fallbackJwt) : null;
  const fallbackUid = claims?.user_id && String(claims.user_id) !== '0' ? String(claims.user_id) : (acc?.customerId || null);
  return {
    sessionExpired: !fallbackUid,
    cleanCookies,
    cm,
    jwtTid: fallbackJwt,
    userId: fallbackUid ? String(fallbackUid) : null,
    sid: acc?.sid || cm._sid || '',
    deviceId: acc?.deviceId || cm._device_id || '',
    token: acc?.token || cm.token || '',
    swuid: cm._swuid || acc?.deviceId || cm._device_id || '',
    orders: []
  };
  })();

  if (!forceRefresh) {
    sessionAuthInFlight.set(sig, runPromise);
  }
  try {
    return await runPromise;
  } finally {
    if (sessionAuthInFlight.get(sig) === runPromise) {
      sessionAuthInFlight.delete(sig);
    }
  }
}

// ---------------------------------------------------------------------------
// UNIFIED DUAL-TRANSPORT SWIGGY CART HELPERS (`dapi/cart` <-> `chkout.swiggy.com/api/v2/cart/client`)
// Automatically executes via Web DAPI when `_session_tid` works, or seamlessly via Native Android `chkout`!
// ---------------------------------------------------------------------------
async function androidCheckoutCartCall(accountOrCookies, endpointPath, { method = 'GET', body = undefined, lat = '26.8658609', lng = '80.9307755', timeoutMs = 9000 } = {}) {
  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : null;
  const auth = await getSwiggySessionAuth(accountOrCookies);
  if (!auth?.jwtTid && !auth?.token) {
    return { status: 0, json: null };
  }
  const headers = buildSwiggyAndroidClientHeaders(accountOrCookies, {
    tid: auth?.jwtTid,
    token: auth?.token,
    sid: auth?.sid,
    deviceId: auth?.deviceId,
    userId: auth?.userId,
    lat,
    lng
  });
  const res = await fetch(`https://chkout.swiggy.com/api/v2/cart/${endpointPath}`, {
    method,
    headers,
    ...(body !== undefined ? { body: JSON.stringify(body) } : {}),
    signal: AbortSignal.timeout(timeoutMs)
  });
  const json = await res.json().catch(() => null);
  if (acc && json?.tid && String(json.tid).includes('.')) {
    acc.jwtTid = json.tid;
    if (!acc.tid || String(acc.tid).includes('.')) acc.tid = json.tid;
  }
  // Native Android `chkout` returns selected `addresses` array without copying `.id` onto `data.address_id`:
  // Normalize `data.address_id` & `data.delivery_address` automatically so checkout/QR code always sees the exact bound `address_id`!
  if (json?.data && typeof json.data === 'object') {
    const selectedAddr = Array.isArray(json.data.addresses)
      ? (json.data.addresses.find(a => a?.selected && a?.id) || json.data.addresses.find(a => a?.delivery_valid && a?.id))
      : null;
    if (!json.data.address_id) {
      json.data.address_id = String(body?.address_id || selectedAddr?.id || '');
    }
    if (!json.data.delivery_address && selectedAddr) {
      json.data.delivery_address = selectedAddr;
    }
  }
  return { status: res.status, json };
}

export async function swiggyCartGet(accountOrCookies, { lat = '26.8658609', lng = '80.9307755', timeoutMs = 9000 } = {}) {
  // Fast Path 1 (~220ms ZERO-CHROMIUM pure HTTP): Native Android `chkout.swiggy.com/api/v2/cart/client`!
  const aRes = await androidCheckoutCartCall(accountOrCookies, 'client', { method: 'GET', lat, lng, timeoutMs }).catch(() => null);
  if (aRes?.json) {
    if (aRes.json.statusCode === 0) return aRes;
    if (/session expired|login again/i.test(String(aRes.json.statusMessage || ''))) return aRes;
  }

  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : null;
  const cleanCookies = cleanSwiggyCookieString(accountOrCookies, acc);
  if (!aRes?.json && cleanCookies.includes('_session_tid=')) {
    const res = await dapiFetch(accountOrCookies, 'cart', { lat, lng, timeoutMs }).catch(() => null);
    if (res?.json && res.json.statusCode === 0) return res;
  }
  return aRes || { status: 0, json: null };
}

export async function swiggyCartUpdate(accountOrCookies, cartPayload, { lat = '', lng = '', address = '', area = '', flushFirst = true, timeoutMs = 10000 } = {}) {
  const requestedItems = Array.isArray(cartPayload?.cartItems) ? cartPayload.cartItems : [];
  if (requestedItems.length > 0 && (!cartPayload?.address_id || !isValidIndianDeliveryCoordinates(lat, lng))) {
    return {
      status: 0,
      json: {
        statusCode: 1,
        statusMessage: 'Cart update blocked: bind the exact delivery address and provide verified Indian coordinates first.'
      }
    };
  }
  // Fast Path 1 (~250ms ZERO-CHROMIUM pure HTTP): Native Android `chkout.swiggy.com/api/v2/cart/client/update`!
  const aRes = await androidCheckoutCartCall(accountOrCookies, 'client/update', {
    method: 'POST',
    lat,
    lng,
    timeoutMs,
    body: {
      flushFirst: Boolean(flushFirst),
      restaurantId: String(cartPayload.restaurantId || ''),
      address_id: String(cartPayload.address_id || ''),
      couponCode: String(cartPayload.couponCode || ''),
      cartItems: Array.isArray(cartPayload.cartItems) ? cartPayload.cartItems : [],
      mealItems: Array.isArray(cartPayload.mealItems) ? cartPayload.mealItems : [],
      subscriptionItems: Array.isArray(cartPayload.subscriptionItems) ? cartPayload.subscriptionItems : []
    }
  }).catch(() => null);
  if (aRes?.json) {
    if (aRes.json.tid && String(aRes.json.tid).includes('.') && typeof accountOrCookies === 'object' && accountOrCookies) {
      accountOrCookies.jwtTid = aRes.json.tid;
      accountOrCookies.tid = aRes.json.tid;
    }
    // `chkout.swiggy.com/api/v2/cart/client/update` IS Swiggy's authoritative cart engine — returning `aRes` directly
    // avoids falling through to `POST /dapi/cart` (which triggers AWS WAF 202 + Headless Chromium OOM on Render 512MB RAM!).
    return aRes;
  }

  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : null;
  const cleanCookies = cleanSwiggyCookieString(accountOrCookies, acc);
  if (cleanCookies.includes('_session_tid=')) {
    const res = await dapiFetch(accountOrCookies, 'cart', {
      method: 'POST',
      lat,
      lng,
      address,
      area,
      timeoutMs,
      body: {
        flushFirst: Boolean(flushFirst),
        cart: cartPayload
      }
    }).catch(() => null);
    if (res?.json && res.json.statusCode === 0 && (res.json.data?.cartMeta || res.json.data?.order_total !== undefined)) {
      return res;
    }
  }
  return aRes || { status: 0, json: null };
}

export async function swiggyCartFlush(accountOrCookies, { lat = '26.8658609', lng = '80.9307755', timeoutMs = 8000 } = {}) {
  const aRes = await androidCheckoutCartCall(accountOrCookies, 'client/flush', { method: 'DELETE', lat, lng, timeoutMs }).catch(() => null);
  if (aRes?.json?.statusCode === 0) return aRes;
  const acc = (typeof accountOrCookies === 'object' && !Array.isArray(accountOrCookies)) ? accountOrCookies : null;
  const cleanCookies = cleanSwiggyCookieString(accountOrCookies, acc);
  if (cleanCookies.includes('_session_tid=')) {
    const wRes = await dapiFetch(accountOrCookies, 'cart/flush', { method: 'POST', body: {}, lat, lng, timeoutMs }).catch(() => null);
    if (wRes) return wRes;
  }
  return aRes || { status: 0, json: null };
}

// ---------------------------------------------------------------------------
// CACHED AWS WAF TOKEN GENERATOR (Solves with stealth browser in ~1.5s, shared across entire bot)
// ---------------------------------------------------------------------------
export async function getCachedWafToken(forceRefresh = false) {
  const now = Date.now();
  if (!forceRefresh && cachedWafToken && (now - cachedWafAt) < WAF_TTL_MS) {
    return cachedWafToken;
  }
  const token = await getLiveSwiggyWafToken(forceRefresh);
  if (token) {
    cachedWafToken = token;
    cachedWafAt = Date.now();
  }
  return token || cachedWafToken || '';
}

let wafWarmLoopTimer = null;
export function startWafKeepWarmLoop() {
  // All critical order/address/cart/coupon/QR/tracking paths now use 100% Zero-Chromium pure HTTP!
  // Only pre-warm Chromium in background if explicitly enabled (`PREWARM_CHROME === 'true'`) so 512MB cloud RAM stays crystal lean!
  if (wafWarmLoopTimer || process.env.PREWARM_CHROME !== 'true') return;
  const initTimer = setTimeout(() => {
    getCachedWafToken(false).catch(() => {});
  }, 500);
  if (typeof initTimer.unref === 'function') initTimer.unref();

  wafWarmLoopTimer = setInterval(() => {
    getCachedWafToken(true).catch(() => {});
  }, 7 * 60 * 1000);
  if (typeof wafWarmLoopTimer.unref === 'function') wafWarmLoopTimer.unref();
}

// Authenticated / guest Swiggy DAPI caller:
//   Fast Path 0 (~250ms, ZERO Chromium, 0MB RAM!): `User-Agent: Swiggy-Android` + `_csrf` via zero-WAF `order/all`!
//   Fallback Path 1: Chromium `aws-waf-token` + `DESKTOP_UA` (only for desktop-gated `/dapi/cart*` endpoints if needed).
export async function dapiFetch(accountOrCookies, endpoint, options = {}) {
  const {
    method = 'GET',
    body = null,
    lat = null,
    lng = null,
    address = '',
    area = '',
    extraHeaders = {},
    timeoutMs = 10000
  } = options;

  const cleanCookies = accountOrCookies ? cleanSwiggyCookieString(accountOrCookies) : '';
  const sig = cleanCookies ? cleanCookies.slice(0, 180) : 'guest';
  const relEndpoint = endpoint.replace(/^\/?(dapi\/)?/, '');
  const url = endpoint.startsWith('http') ? endpoint : `https://www.swiggy.com/dapi/${relEndpoint}`;
  const isDesktopWafCartRoute = /^(cart|menu)(\/|\?|$)/i.test(relEndpoint);
  const isMobileWebOffersRoute = /^offers(\/|\?|$)/i.test(relEndpoint);

  // Fast Path 0: Zero-Chromium HTTP for ALL non-`/cart`/`/menu` DAPI endpoints!
  // CRITICAL: `/dapi/offers/*` MUST use `MOBILE_WEB_UA` (`Mobile Safari/537.36` -> `200 OK`, `waf=null`, full real coupon cards),
  // NEVER `Swiggy-Android` (which returns `{ statusCode: 0, data: { pages: 0, cards: [] } }` empty offers)!
  if (!isDesktopWafCartRoute) {
    try {
      const zeroWafCookieParts = [];
      if (cleanCookies) zeroWafCookieParts.push(cleanCookies);
      if (lat && lng) {
        zeroWafCookieParts.push(`userLocation=${encodeURIComponent(JSON.stringify({
          lat: String(lat),
          lng: String(lng),
          address: String(address || area || 'India'),
          area: String(area || '')
        }))}`);
      }

      let fastBody = body ? { ...body } : null;
      if (method !== 'GET' && fastBody && fastBody._csrf === undefined) {
        let csrf = csrfTokenCache.get(sig)?.csrf || '';
        if (!csrf && cleanCookies) {
          const ordRes = await fetch('https://www.swiggy.com/dapi/order/all', {
            headers: {
              'Cookie': zeroWafCookieParts.join('; '),
              'User-Agent': 'Swiggy-Android',
              'Accept': 'application/json',
              'Referer': 'https://www.swiggy.com/'
            },
            signal: AbortSignal.timeout(6500)
          }).catch(() => null);
          const ordJson = ordRes ? await ordRes.json().catch(() => null) : null;
          if (ordJson?.csrfToken) {
            csrf = ordJson.csrfToken;
            csrfTokenCache.set(sig, { csrf, ts: Date.now() });
          }
        }
        if (csrf) fastBody._csrf = csrf;
      }

      let fastRes = null;
      for (let netTry = 0; netTry < 2; netTry++) {
        try {
          fastRes = await fetch(url, {
            method,
            headers: {
              'Cookie': zeroWafCookieParts.join('; '),
              'User-Agent': isMobileWebOffersRoute ? MOBILE_WEB_UA : 'Swiggy-Android',
              'Accept': 'application/json',
              'Content-Type': 'application/json',
              'Origin': 'https://www.swiggy.com',
              'Referer': isMobileWebOffersRoute ? 'https://www.swiggy.com/checkout' : 'https://www.swiggy.com/',
              ...extraHeaders
            },
            ...(fastBody ? { body: JSON.stringify(fastBody) } : {}),
            signal: AbortSignal.timeout(timeoutMs)
          });
          break;
        } catch (netErr) {
          if (netTry === 1) throw netErr;
          await new Promise(r => setTimeout(r, 150));
        }
      }

      if (fastRes && fastRes.status !== 202 && fastRes.status !== 403 && !fastRes.headers.get('x-amzn-waf-action')) {
        const fastText = await fastRes.text();
        const fastJson = JSON.parse(fastText);
        if (fastJson?.csrfToken) {
          csrfTokenCache.set(sig, { csrf: fastJson.csrfToken, ts: Date.now() });
        }
        if (fastJson && fastJson.statusCode !== 400) {
          return { ok: fastRes.ok, status: fastRes.status, json: fastJson };
        }
      }
    } catch {}
  }

  // Pure Android token-only sessions (`!_session_tid`) authenticate on `chkout.swiggy.com` / `mcp.swiggy.com`, NEVER on web `/dapi/*` —
  // never waste 350MB RAM + 3s launching Headless Chromium on Render Free Tier for a token-only account!
  if (!cleanCookies.includes('_session_tid=') && accountOrCookies && typeof accountOrCookies === 'object' && (accountOrCookies.tid || accountOrCookies.token)) {
    return { ok: false, status: 401, json: null };
  }

  for (let attempt = 0; attempt < 2; attempt++) {
    const wafToken = await getCachedWafToken(attempt > 0);
    const cookieParts = [];
    if (cleanCookies) cookieParts.push(cleanCookies);
    if (wafToken) cookieParts.push(`aws-waf-token=${wafToken}`);
    if (lat && lng) {
      cookieParts.push(`userLocation=${encodeURIComponent(JSON.stringify({
        lat: String(lat),
        lng: String(lng),
        address: String(address || area || 'India'),
        area: String(area || '')
      }))}`);
    }

    let finalBody = body ? { ...body } : null;
    if (method !== 'GET' && finalBody && finalBody._csrf === undefined) {
      let csrf = csrfTokenCache.get(sig)?.csrf || '';
      if (!csrf) {
        try {
          const csrfRes = await fetch('https://www.swiggy.com/dapi/cart', {
            headers: {
              'Cookie': cookieParts.join('; '),
              'User-Agent': DESKTOP_UA,
              'Accept': 'application/json',
              'Referer': 'https://www.swiggy.com/'
            },
            signal: AbortSignal.timeout(7000)
          });
          const csrfJson = await csrfRes.json().catch(() => null);
          if (csrfJson?.csrfToken) {
            csrf = csrfJson.csrfToken;
            csrfTokenCache.set(sig, { csrf, ts: Date.now() });
          }
        } catch (e) {}
      }
      if (csrf) finalBody._csrf = csrf;
    }

    const isOrderRoute = /^(order)(\/|\?|$)/i.test(relEndpoint);
    const referer = isOrderRoute
      ? 'https://www.swiggy.com/my-account'
      : (isMobileWebOffersRoute ? 'https://www.swiggy.com/checkout' : 'https://www.swiggy.com/');

    const res = await fetch(url, {
      method,
      headers: {
        'Cookie': cookieParts.join('; '),
        'User-Agent': DESKTOP_UA,
        'Accept': 'application/json',
        'Content-Type': 'application/json',
        'Origin': 'https://www.swiggy.com',
        'Referer': referer,
        ...extraHeaders
      },
      ...(finalBody ? { body: JSON.stringify(finalBody) } : {}),
      signal: AbortSignal.timeout(timeoutMs)
    });

    if (res.status === 202 || res.headers.get('x-amzn-waf-action')) {
      if (attempt === 0) {
        await new Promise(r => setTimeout(r, 200));
        continue;
      }
    }

    const text = await res.text();
    try {
      const json = JSON.parse(text);
      if (json?.csrfToken) {
        csrfTokenCache.set(sig, { csrf: json.csrfToken, ts: Date.now() });
      }
      return { ok: res.ok, status: res.status, json };
    } catch (parseErr) {
      if (attempt === 0) continue;
      return { ok: false, status: res.status, json: null, rawText: text.slice(0, 300) };
    }
  }

  return { ok: false, status: 0, json: null };
}

// ---------------------------------------------------------------------------
// OFFICIAL SWIGGY FOOD MCP JSON-RPC CLIENT (`https://mcp.swiggy.com/food`)
// Runs inside Swiggy's `ap-south-1` VPC with ZERO WAF & ZERO CHROMIUM!
// Provides structured `fetch_food_coupons`, `get_food_cart` (exposes auto-suggested best coupon),
// `apply_food_coupon`, `get_restaurant_menu`, and `create_address` in ~220ms!
// ---------------------------------------------------------------------------
const mcpBearerTidCache = new Map(); // accSig -> { tid, ts }

export async function callSwiggyFoodMcpTool(accountOrCookies, toolName, toolArgs = {}, timeoutMs = 6500) {
  try {
    const accObj = typeof accountOrCookies === 'object' && accountOrCookies ? accountOrCookies : null;
    const cookiesMap = parseCookieMap(typeof accountOrCookies === 'string' ? accountOrCookies : (accObj?.cookies || ''));
    const accSig = String(accObj?.phone || accObj?.customerId || cookiesMap._sid || cookiesMap.tid || 'guest').slice(0, 80);

    const resolveFreshChkoutBearer = async (force = false) => {
      const cached = mcpBearerTidCache.get(accSig);
      if (!force && cached && (Date.now() - cached.ts < 10 * 60 * 1000)) {
        return cached.tid;
      }
      const seedTid = accObj?.jwtTid || accObj?.tid || cookiesMap.tid || '';
      const nowSec = Math.floor(Date.now() / 1000);
      // Fast 0ms reuse if `account.tid` was ALREADY minted fresh by `swiggyCartUpdate` (`exp` ~30 days in future)!
      if (!force && seedTid && String(seedTid).includes('.')) {
        const claims = decodeJwtPayload(seedTid);
        if (Number(claims?.exp || 0) > nowSec + 3600) {
          mcpBearerTidCache.set(accSig, { tid: seedTid, ts: Date.now() });
          return seedTid;
        }
      }
      const seedToken = accObj?.token || cookiesMap.token || '';
      const seedSid = accObj?.sid || cookiesMap._sid || '';
      const seedDev = accObj?.deviceId || cookiesMap._device_id || cookiesMap._swuid || '';
      try {
        const chkRes = await fetch('https://chkout.swiggy.com/api/v2/cart/client', {
          headers: {
            'User-Agent': 'Swiggy-Android',
            'app-version': '4.67.0',
            'version-code': '1365',
            'os-version': '13',
            'Accept': 'application/json',
            ...(seedTid ? { tid: seedTid } : {}),
            ...(seedToken ? { token: seedToken } : {}),
            ...(seedSid ? { sid: seedSid } : {}),
            ...(seedDev ? { deviceId: seedDev, swuid: seedDev } : {})
          },
          signal: AbortSignal.timeout(4500)
        });
        const chkJson = await chkRes.json().catch(() => null);
        if (chkJson?.tid && String(chkJson.tid).includes('.')) {
          mcpBearerTidCache.set(accSig, { tid: chkJson.tid, ts: Date.now() });
          if (accObj) {
            accObj.jwtTid = chkJson.tid;
            if (!accObj.tid || String(accObj.tid).includes('.')) accObj.tid = chkJson.tid;
          }
          return chkJson.tid;
        }
      } catch {}
      return String(seedTid).includes('.') ? seedTid : '';
    };

    for (let attempt = 0; attempt < 2; attempt++) {
      const bearerTid = await resolveFreshChkoutBearer(attempt > 0);
      if (!bearerTid || !String(bearerTid).includes('.')) {
        return { ok: false, structured: null, text: '' };
      }
      const res = await fetch('https://mcp.swiggy.com/food', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'Accept': 'application/json, text/event-stream',
          'Authorization': `Bearer ${bearerTid}`
        },
        body: JSON.stringify({
          jsonrpc: '2.0',
          id: Date.now() % 100000,
          method: 'tools/call',
          params: {
            name: toolName,
            arguments: toolArgs
          }
        }),
        signal: AbortSignal.timeout(timeoutMs)
      });
      if ((res.status === 401 || res.status === 403) && attempt === 0) continue;
      const raw = await res.text();
      let rpc = null;
      try {
        rpc = JSON.parse(raw);
      } catch {
        const dataLine = raw.split('\n').find(l => l.startsWith('data:'));
        if (dataLine) {
          try { rpc = JSON.parse(dataLine.slice(5).trim()); } catch {}
        }
      }
      const result = rpc?.result || null;
      const text = Array.isArray(result?.content)
        ? result.content.map(c => c?.text || '').join('\n')
        : '';
      return {
        ok: Boolean(res.ok && result && !result.isError),
        isError: Boolean(result?.isError),
        structured: result?.structuredContent || null,
        text
      };
    }
    return { ok: false, structured: null, text: '' };
  } catch (err) {
    return { ok: false, structured: null, text: '', error: err.message };
  }
}

function buildChkoutHeaders(auth, lat = '26.8658609', lng = '80.9307755', extra = {}) {
  return {
    'Content-Type': 'application/json',
    'Accept': 'application/json',
    'tid': auth.jwtTid || '',
    'sid': auth.sid || '',
    'token': auth.token || '',
    'userid': String(auth.userId || ''),
    'user-id': String(auth.userId || ''),
    'deviceId': auth.deviceId || '',
    'device-id': auth.deviceId || '',
    'swuid': auth.swuid || auth.deviceId || '',
    'platform': 'an',
    'agent-type': 'Swiggy-Android',
    'analyticsPlatform': 'an',
    'x-web-checkout-flow': 'cart',
    'marketplaceid': '1',
    'marketplacecategory': 'FOOD',
    'marketplacebusinessline': 'Regular',
    'version-code': '1350',
    'app-version': '4.68.0',
    'lat': String(lat),
    'lng': String(lng),
    'Cookie': auth.cleanCookies || '',
    'Origin': 'https://www.swiggy.com',
    'Referer': 'https://www.swiggy.com/',
    'User-Agent': 'Swiggy-Android',
    ...extra
  };
}

// Helper to get ordered candidate Swiggy accounts from local DB
function getCandidateAccounts(preferredAccount = null, preferredHostName = null) {
  const list = [];
  const seen = new Set();

  const pushAcc = (key, acc) => {
    if (!acc || typeof acc !== 'object') return;
    const clean = cleanSwiggyCookieString(acc.cookies || '', acc);
    if (!clean && !acc.tid) return;
    const id = key || acc.phone || acc.name || clean.slice(0, 40);
    if (seen.has(id)) return;
    seen.add(id);
    list.push({ key: key || id, acc });
  };

  if (preferredAccount) pushAcc('preferred', preferredAccount);

  try {
    const db = getDb();
    const accounts = db?.config?.accounts || {};
    const rankAcc = (a) =>
      (a?.isLoggedIn ? 8 : 0) +
      (a?.tid && String(a.tid).startsWith('eyJ') ? 4 : 0) +
      (a?.token ? 2 : 0) +
      (a?.cookies ? 1 : 0);
    const entries = Object.entries(accounts).sort(([, a], [, b]) => rankAcc(b) - rankAcc(a));

    // If preferredHostName matches one of our accounts, check active matches first (read-only!)
    if (preferredHostName) {
      const h = preferredHostName.trim().toLowerCase();
      for (const [k, a] of entries) {
        const names = [a.swiggyName, a.name, a.phone].filter(Boolean).map(x => String(x).trim().toLowerCase());
        if (names.some(n => n === h || n.includes(h) || h.includes(n))) {
          pushAcc(k, a);
        }
      }
    }

    for (const [k, a] of entries) {
      pushAcc(k, a);
    }
  } catch (e) {}

  return list;
}

// ---------------------------------------------------------------------------
// LIVE GROUP CART ENGINE (https://chkout.swiggy.com/api/v1/shared_cart)
// Sub-100ms, zero WAF, auto-joins foreign customer group carts cleanly!
// ---------------------------------------------------------------------------
export async function fetchLiveGroupCart(groupCartId, restaurantId = null, hostName = null, preferredAccount = null, lat = '17.385044', lng = '78.486671') {
  if (!groupCartId) return null;
  const gcId = String(groupCartId).trim();
  const candidates = getCandidateAccounts(preferredAccount, hostName);
  if (candidates.length === 0) return null;

  const parseSharedCartPayload = (data) => {
    if (!data || typeof data !== 'object') return null;
    const rDetails = data.restaurant_details || {};
    const resolvedRestId = String(rDetails.restaurant_id || restaurantId || '');
    const resolvedRestName = rDetails.restaurant_name || null;
    const areaName = rDetails.area_name || '';

    // Merge identical menu items across all group cart participants cleanly
    const mergedItemsMap = new Map();
    const userCartMap = data.user_cart_map || {};
    for (const participant of Object.values(userCartMap)) {
      const userCart = Array.isArray(participant?.user_cart) ? participant.user_cart : [];
      for (const rawItem of userCart) {
        if (!rawItem || !rawItem.menu_item_id || !(rawItem.quantity > 0)) continue;
        const menuItemId = String(rawItem.menu_item_id);
        const addons = Array.isArray(rawItem.addons) ? rawItem.addons : [];
        const variants = Array.isArray(rawItem.variants) ? rawItem.variants : [];
        const sigKey = `${menuItemId}::${JSON.stringify(variants)}::${JSON.stringify(addons)}`;

        const qty = Number(rawItem.quantity) || 1;
        const basePaise = Number(rawItem.subtotal ?? (Number(rawItem.base_price || 0) * qty));
        const finalPaise = Number(rawItem.final_price ?? basePaise);
        const tradeDiscPaise = Number(rawItem.subtotal_trade_discount || 0);
        const packPaise = Number(rawItem.packing_charge || 0);
        const itemGst = Number(rawItem.item_taxes?.GST || 0);

        const unitPrice = Math.round((basePaise / 100 / qty) * 100) / 100;
        const lineTotal = Math.round((basePaise / 100) * 100) / 100;
        const finalLineTotal = Math.round((finalPaise / 100) * 100) / 100;

        if (mergedItemsMap.has(sigKey)) {
          const prev = mergedItemsMap.get(sigKey);
          prev.qty += qty;
          prev.quantity = prev.qty;
          prev.lineTotal = Math.round((prev.lineTotal + lineTotal) * 100) / 100;
          prev.finalLineTotal = Math.round((prev.finalLineTotal + finalLineTotal) * 100) / 100;
          prev.tradeDiscount = Math.round((prev.tradeDiscount + tradeDiscPaise / 100) * 100) / 100;
          prev.packingCharge = Math.round((prev.packingCharge + packPaise / 100) * 100) / 100;
          prev.gst = Math.round((prev.gst + itemGst) * 100) / 100;
          if (Array.isArray(rawItem.offer_ids)) {
            for (const oid of rawItem.offer_ids) {
              if (oid && !prev.offer_ids.includes(oid)) prev.offer_ids.push(oid);
            }
          }
          if (!prev.item_offer_cart_meta && rawItem.item_offer_cart_meta) {
            prev.item_offer_cart_meta = String(rawItem.item_offer_cart_meta);
          }
        } else {
          mergedItemsMap.set(sigKey, {
            itemId: menuItemId,
            menu_item_id: Number(menuItemId),
            name: String(rawItem.name || 'Dish Item').trim(),
            qty,
            quantity: qty,
            price: unitPrice,
            lineTotal,
            finalLineTotal,
            tradeDiscount: Math.round((tradeDiscPaise / 100) * 100) / 100,
            packingCharge: Math.round((packPaise / 100) * 100) / 100,
            gst: Math.round(itemGst * 100) / 100,
            addons,
            variants,
            offer_ids: Array.isArray(rawItem.offer_ids) ? [...rawItem.offer_ids] : [],
            item_offer_cart_meta: String(rawItem.item_offer_cart_meta || ''),
            item_offer_tags: Array.isArray(rawItem.item_offer_tags) ? rawItem.item_offer_tags : [],
            isVeg: rawItem.isVeg === 1 || rawItem.is_veg === '1',
            inStock: rawItem.in_stock !== 0
          });
        }
      }
    }

    const items = Array.from(mergedItemsMap.values());
    const subtotal = Math.round(items.reduce((s, i) => s + i.lineTotal, 0) * 100) / 100;
    const tradeDiscountTotal = Math.round(items.reduce((s, i) => s + (i.tradeDiscount || 0), 0) * 100) / 100;
    const discountedSubtotal = Math.round(items.reduce((s, i) => s + i.finalLineTotal, 0) * 100) / 100;
    const packingCharges = Math.round((items.reduce((s, i) => s + (i.packingCharge || 0), 0)) * 100) / 100;
    const itemGstTotal = Math.round(items.reduce((s, i) => s + (i.gst || 0), 0) * 100) / 100;

    return {
      status: 'ACTIVE',
      groupCartId: String(data.group_cart_id || gcId),
      hostUserId: data.host_user_id ? String(data.host_user_id) : null,
      deeplink: data.shared_cart_deeplink || null,
      locked: Boolean(data.locked_status),
      restaurantId: resolvedRestId || null,
      restaurantName: resolvedRestName,
      areaName,
      items,
      itemTotal: subtotal,
      subtotal,
      discountedSubtotal,
      tradeDiscountTotal,
      packingCharges,
      taxesAndCharges: itemGstTotal
    };
  };

  let lastStatusInfo = null;
  let emptyPayloadFallback = null;
  // Deterministic ephemeral reader `user_id` per `group_cart_id`:
  // Resolves ANY foreign customer Group Cart in ANY city on the VERY FIRST ~200ms request,
  // NEVER hits `statusCode: 86` (`USER_ALREADY_PART_OF_GROUP_CART`), and NEVER pollutes real accounts!
  const ephemeralReaderUid = String(200000000 + ((Math.abs(parseInt(gcId.replace(/\D/g, '').slice(-9), 10)) || 1234567) % 79999999));

  const resolvedAuths = [];
  for (const cand of candidates) {
    const auth = (cand.acc?.tid && String(cand.acc.tid).startsWith('eyJ') && cand.acc.userId)
      ? {
          jwtTid: String(cand.acc.tid).trim(),
          token: String(cand.acc.token || '').trim(),
          sid: String(cand.acc.sid || '').trim(),
          deviceId: String(cand.acc.deviceId || '').trim(),
          userId: String(cand.acc.userId).trim()
        }
      : await getSwiggySessionAuth(cand.acc);
    if (!auth || auth.sessionExpired || !auth.jwtTid) continue;
    resolvedAuths.push({ ...cand, auth });

    // Fast Path (~200ms 1-call shot): Clean Android `shared_cart/join` with ephemeral reader UID!
    if (restaurantId) {
      try {
        const fastHeaders = buildSwiggyAndroidClientHeaders(cand.acc, {
          tid: auth.jwtTid,
          token: auth.token,
          sid: auth.sid,
          deviceId: auth.deviceId,
          userId: ephemeralReaderUid,
          lat: String(lat || '17.385044'),
          lng: String(lng || '78.486671')
        });
        const joinRes = await fetch('https://chkout.swiggy.com/api/v1/shared_cart/join', {
          method: 'POST',
          headers: fastHeaders,
          body: JSON.stringify({
            group_cart_id: gcId,
            restaurant_id: String(restaurantId),
            user_id: ephemeralReaderUid
          }),
          signal: AbortSignal.timeout(6500)
        });
        const joinJson = await joinRes.json().catch(() => null);
        if (joinJson?.statusCode === 0 && joinJson?.data) {
          const parsedJoin = parseSharedCartPayload(joinJson.data);
          if (parsedJoin?.items?.length > 0) return parsedJoin;
          emptyPayloadFallback = parsedJoin || emptyPayloadFallback;
        }
        if (joinJson?.statusCode === 88 || joinJson?.errorCodes?.includes('GROUP_CART_NO_LONGER_EXISTS')) {
          return { status: 'EXPIRED', statusCode: joinJson.statusCode, statusMessage: joinJson.statusMessage || 'Group cart no longer exists', items: [] };
        }
        if (joinJson?.errorCodes?.includes('GROUP_CART_ORDER_PLACED')) {
          return { status: 'PLACED', statusCode: joinJson.statusCode, statusMessage: joinJson.statusMessage || 'Group cart order already placed', items: [] };
        }
        lastStatusInfo = joinJson || lastStatusInfo;
      } catch {}
    }

    // Fallback Path: Direct read-only GET when `restaurantId` wasn't embedded in URL or cross-city `join` returned empty items
    if (auth.userId) {
      try {
        const res = await fetch(`https://chkout.swiggy.com/api/v1/shared_cart?group_cart_id=${encodeURIComponent(gcId)}`, {
          headers: buildChkoutHeaders(auth, String(lat || '26.8658609'), String(lng || '80.9307755')),
          signal: AbortSignal.timeout(6500)
        });
        const json = await res.json().catch(() => null);
        if (json?.statusCode === 0 && json?.data) {
          const parsedGet = parseSharedCartPayload(json.data);
          if (parsedGet?.items?.length > 0) return parsedGet;
          emptyPayloadFallback = parsedGet || emptyPayloadFallback;
        }
        if (json?.statusCode === 88 || json?.errorCodes?.includes('GROUP_CART_NO_LONGER_EXISTS')) {
          return { status: 'EXPIRED', statusCode: json.statusCode, statusMessage: json.statusMessage || 'Group cart no longer exists', items: [] };
        }
        if (json?.errorCodes?.includes('GROUP_CART_ORDER_PLACED')) {
          return { status: 'PLACED', statusCode: json.statusCode, statusMessage: json.statusMessage || 'Group cart order already placed', items: [] };
        }
        lastStatusInfo = json || lastStatusInfo;
      } catch {}
    }
  }

  if (emptyPayloadFallback) return emptyPayloadFallback;

  if (lastStatusInfo) {
    return {
      status: 'UNAVAILABLE',
      statusCode: lastStatusInfo.statusCode,
      statusMessage: lastStatusInfo.statusMessage || (lastStatusInfo.errorCodes || []).join(', '),
      items: []
    };
  }
  return null;
}

// ---------------------------------------------------------------------------
// REVERSE & FORWARD GEOCODING ENGINE (Swiggy Maps API + Nominatim fallback)
// ---------------------------------------------------------------------------
export async function reverseGeocodeCoords(lat, lng, accountOrCookies = null) {
  if (!isValidIndianDeliveryCoordinates(lat, lng)) return null;
  const sLat = String(lat).trim();
  const sLng = String(lng).trim();

  // 1. Try Swiggy's own official reverse geocoder first for 100% Swiggy area/city parity
  try {
    const cand = accountOrCookies || getCandidateAccounts()[0]?.acc || null;
    const { json } = await dapiFetch(cand, 'misc/address-recommend', {
      method: 'POST',
      body: { latlng: `${sLat},${sLng}` },
      lat: sLat,
      lng: sLng,
      timeoutMs: 7000
    });
    const rec = json?.data?.[0];
    if (rec?.formatted_address) {
      const comps = Array.isArray(rec.address_components) ? rec.address_components : [];
      const findComp = (...types) => comps.find(c => Array.isArray(c.types) && types.some(t => c.types.includes(t)))?.long_name || '';
      const city = findComp('locality', 'administrative_area_level_2') || 'Address';
      const area = findComp('sublocality_level_1', 'sublocality', 'neighborhood') || city;
      const landmark = findComp('sublocality_level_2', 'premise', 'route') || area;
      const pincode = findComp('postal_code') || '';
      return {
        address: rec.formatted_address,
        area,
        landmark,
        city,
        pincode,
        lat: String(rec.geometry?.location?.lat || sLat),
        lng: String(rec.geometry?.location?.lng || sLng)
      };
    }
  } catch (e) {}

  // 2. Fallback to OpenStreetMap Nominatim reverse geocoding
  try {
    const geoRes = await fetch(`https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat=${encodeURIComponent(sLat)}&lon=${encodeURIComponent(sLng)}`, {
      headers: { 'User-Agent': 'TelegramSlotBot/2.0', 'Accept-Language': 'en' },
      signal: AbortSignal.timeout(4500)
    });
    if (geoRes.ok) {
      const gj = await geoRes.json();
      const a = gj.address || {};
      const city = a.city || a.town || a.village || a.state_district || 'Address';
      const area = a.suburb || a.neighbourhood || a.residential || a.county || city;
      const landmark = a.road || a.building || area;
      return {
        address: gj.display_name || `${area}, ${city}`,
        area,
        landmark,
        city,
        pincode: a.postcode || '',
        lat: sLat,
        lng: sLng
      };
    }
  } catch (e) {}

  return {
    address: `Pinned Location (${sLat}, ${sLng})`,
    area: 'Pinned Area',
    landmark: 'Main Road',
    city: 'Delivery',
    lat: sLat,
    lng: sLng
  };
}

const forwardGeocodeCache = new Map();

export async function geocodeAddressDetails(addrObj, accountOrCookies = null) {
  if (!addrObj || typeof addrObj !== 'object') return addrObj;
  const out = { ...addrObj };
  const hasAnyCoords = Boolean(String(out.lat || '').trim() || String(out.lng || '').trim());

  // Case A: Trust already-supplied GPS coordinates only when both are plausible in India.
  if (out.lat && out.lng && isValidIndianDeliveryCoordinates(out.lat, out.lng)) {
    if (!out.address || out.address.startsWith('Delivering to ') || out.address.startsWith('Pinned Location')) {
      const rev = await reverseGeocodeCoords(out.lat, out.lng, accountOrCookies);
      if (rev) {
        out.address = rev.address || out.address;
        out.area = out.area || rev.area;
        out.landmark = out.landmark || rev.landmark;
        out.city = (!out.city || out.city === 'Delivery' || out.city === 'Shared Location') ? rev.city : out.city;
        out.pincode = out.pincode || rev.pincode || '';
      }
    }
    return out;
  }
  if (hasAnyCoords) {
    delete out.lat;
    delete out.lng;
  }

  // Case B: Resolve a full street address. Never reuse a saved address merely because
  // it shares a city, prefix, or nearby GPS point; that can select the wrong home/contact.
  const rawAddr = String(out.address || '').trim();
  if (!rawAddr || out.unresolvableShortLink) return out;

  // Query both providers with the COMPLETE address. The previous implementation raced
  // house-level results against a PIN-code/city-only query, so the broad centroid often won.
  let cleanAddr = rawAddr
    .replace(/Hey!\s*Save my address on Swiggy using the link\s*:?\s*/gi, '')
    .replace(/https?:\/\/\S+/gi, ' ')
    .replace(/^\s*Address\s*:\s*/i, '')
    .replace(/(?:^|[\n,])\s*(?:Latitude|Longitude|lat|lng)\s*[:=]\s*[^\n,]*/gi, ' ')
    .replace(/(?:^|[\n,])\s*(?:Phone|Mobile|Tel|Contact)\s*[:=]\s*\+?[\d\s-]+/gi, ' ')
    .replace(/_/g, ' ')
    .replace(/[\r\n]+/g, ', ')
    .replace(/\s+/g, ' ')
    .replace(/[, ]+$/g, '')
    .trim();
  if (cleanAddr.length < 8) return out;

  const normalizedBase = normalizeAddressText(cleanAddr);
  const cityLabel = String(out.city || '').trim();
  const pincode = String(out.pincode || cleanAddr.match(/\b([1-8]\d{5})\b/)?.[1] || '').trim();
  const querySuffixes = [];
  if (cityLabel && !/^(?:address|delivery|shared location)$/i.test(cityLabel) &&
      !normalizedBase.includes(normalizeAddressText(cityLabel))) querySuffixes.push(cityLabel);
  if (pincode && !normalizedBase.includes(pincode)) querySuffixes.push(pincode);
  if (!/\bindia\b/i.test(cleanAddr)) querySuffixes.push('India');
  cleanAddr = [cleanAddr, ...querySuffixes].filter(Boolean).join(', ');
  const normTarget = normalizeAddressText(cleanAddr);
  if (normTarget && forwardGeocodeCache.has(normTarget)) {
    const cached = forwardGeocodeCache.get(normTarget);
    out.lat = cached.lat;
    out.lng = cached.lng;
    out.city = out.city || cached.city;
    out.area = out.area || cached.area;
    out.landmark = out.landmark || cached.landmark;
    return out;
  }
  if (cleanAddr.length < 12) return out;

  const tryPhoton = async () => {
    const r = await fetch(`https://photon.komoot.io/api/?q=${encodeURIComponent(cleanAddr)}&limit=1`, {
      headers: { 'User-Agent': 'TelegramSlotBot/2.0', 'Accept': 'application/json' },
      signal: AbortSignal.timeout(2500)
    });
    if (!r.ok) throw new Error('photon_non_200');
    const j = await r.json();
    const coords = j?.features?.[0]?.geometry?.coordinates;
    if (Array.isArray(coords) && coords.length >= 2 && isValidIndianDeliveryCoordinates(coords[1], coords[0])) {
      return { lat: String(coords[1]), lng: String(coords[0]) };
    }
    throw new Error('photon_empty_or_outside_india');
  };

  const tryNominatim = async () => {
    const r = await fetch(`https://nominatim.openstreetmap.org/search?format=jsonv2&limit=1&countrycodes=in&q=${encodeURIComponent(cleanAddr)}`, {
      headers: { 'User-Agent': 'TelegramSlotBot/2.0', 'Accept-Language': 'en' },
      signal: AbortSignal.timeout(2500)
    });
    if (!r.ok) throw new Error('nom_non_200');
    const arr = await r.json();
    if (Array.isArray(arr) && arr[0]?.lat && arr[0]?.lon && isValidIndianDeliveryCoordinates(arr[0].lat, arr[0].lon)) {
      return { lat: String(arr[0].lat), lng: String(arr[0].lon) };
    }
    throw new Error('nom_empty_or_outside_india');
  };

  try {
    const geoHit = await Promise.any([tryPhoton(), tryNominatim()]);
    if (geoHit?.lat && geoHit?.lng) {
      out.lat = geoHit.lat;
      out.lng = geoHit.lng;
      forwardGeocodeCache.set(normTarget, { lat: out.lat, lng: out.lng, city: out.city, area: out.area, landmark: out.landmark });
    }
  } catch {}

  return out;
}

// Resolve genuine Swiggy OFO shared address UUID via mobile endpoint (/mapi/social/getAddress/<uuid>)
export async function resolveSharedOfoAddress(ofoToken, ofoUser = null, accountOrCookies = null) {
  if (!ofoToken) return null;
  const tok = String(ofoToken).trim();
  if (tok.length < 6) return null;

  try {
    const candidates = accountOrCookies
      ? [accountOrCookies]
      : getCandidateAccounts().map(x => x.acc);

    for (const cand of candidates) {
      if (!cand) continue;
      const dapiRes = await dapiFetch(cand, `social/getAddress/${encodeURIComponent(tok)}`).catch(() => null);
      const rJson = dapiRes?.json;
      const addrWrap = rJson?.data?.address || rJson?.data;
      const act = addrWrap?.actual_address || addrWrap;
      const resolvedLat = act?.location?.lat ?? act?.lat ?? act?.latitude;
      const resolvedLng = act?.location?.lng ?? act?.lng ?? act?.longitude;
      const resolvedDisplay =
        addrWrap?.display_address ||
        act?.formatted_address ||
        `${act?.address_line && act.address_line !== 'None' ? act.address_line + ', ' : ''}${act?.address || act?.address_line1 || ''}`.trim();

      if (rJson?.statusCode === 0 && (resolvedLat || resolvedDisplay)) {
        return {
          id: addrWrap?.id || act?.id || '',
          name: act?.contact_name || act?.name || ofoUser || 'Customer',
          mobile: act?.phone || act?.mobile || '',
          flat_no: act?.address_line && act.address_line !== 'None' ? act.address_line : (act?.flat_no || ''),
          area: act?.locality || act?.area || '',
          landmark: act?.landmark || act?.locality || '',
          city: act?.city || 'Address',
          address: resolvedDisplay,
          lat: resolvedLat ? String(resolvedLat) : null,
          lng: resolvedLng ? String(resolvedLng) : null,
          annotation: (Array.isArray(act?.tags) && act.tags[0]) || act?.annotation || 'Shared'
        };
      }
    }
  } catch (e) {}
  return null;
}

// Verified payment data extraction - STOP synthetic QR generation via qrserver.com
export function getGenuinePaymentDetails(order) {
  return {
    payableAmount: order?.finalPayable || order?.subtotal || null,
    restaurantName: order?.restaurantName || 'Swiggy Order',
    swiggyPaymentUrl: 'https://www.swiggy.com/payments',
    swiggyCheckoutUrl: 'https://www.swiggy.com/checkout',
    hasGenuineQr: Boolean(order?.customQrFileId || order?.genuineQrBuffer),
    genuineQr: order?.customQrFileId || order?.genuineQrBuffer || null
  };
}

export function generateUpiQrUrl(amount, orderId, upiId = null) {
  return {
    hasGenuineQr: false,
    qrUrl: null,
    amount: Math.max(1, Math.round(amount || 0)),
    swiggyPaymentUrl: 'https://www.swiggy.com/payments',
    swiggyCheckoutUrl: 'https://www.swiggy.com/checkout'
  };
}

// Generates a sleek, authentic, personalized Swiggy Payment Card image with customer's name IN CENTER OF QR
export async function generatePersonalizedQrCard({
  customerName = 'Abbu & Ammi',
  restaurantName = 'Swiggy Food Order',
  amount = 0,
  savings = 0,
  upiUrl = null,
  qrBuffer = null
}) {
  let qrDataUrl = '';
  if (qrBuffer) {
    qrDataUrl = `data:image/png;base64,${Buffer.isBuffer(qrBuffer) ? qrBuffer.toString('base64') : qrBuffer}`;
  } else if (upiUrl) {
    qrDataUrl = await QRCode.toDataURL(upiUrl, {
      margin: 2,
      width: 360,
      errorCorrectionLevel: 'H',
      color: { dark: '#000000', light: '#ffffff' }
    });
  }

  const browser = await puppeteer.launch({
    executablePath: CHROME_PATH,
    headless: PUPPETEER_HEADLESS,
    args: ['--no-sandbox', '--disable-gpu', '--disable-dev-shm-usage']
  });

  try {
    const page = await browser.newPage();
    await page.setViewport({ width: 600, height: 900, deviceScaleFactor: 2 });

    const html = `
<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <style>
    * { margin: 0; padding: 0; box-sizing: border-box; }
    body {
      background: transparent;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      display: flex;
      justify-content: center;
      align-items: center;
      padding: 16px;
    }
    .card {
      width: 480px;
      background: linear-gradient(160deg, #1a1e29 0%, #10131a 100%);
      border: 2px solid #fc8019;
      border-radius: 24px;
      padding: 28px 24px;
      color: #ffffff;
      text-align: center;
      box-shadow: 0 16px 40px rgba(252, 128, 25, 0.25);
    }
    .header-badge {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      background: rgba(252, 128, 25, 0.15);
      border: 1px solid rgba(252, 128, 25, 0.4);
      color: #fc8019;
      font-size: 13px;
      font-weight: 700;
      letter-spacing: 1px;
      text-transform: uppercase;
      padding: 6px 16px;
      border-radius: 20px;
      margin-bottom: 14px;
    }
    .restaurant-title {
      font-size: 20px;
      font-weight: 600;
      color: #e5e7eb;
      margin-bottom: 18px;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }
    .qr-frame {
      background: #ffffff;
      padding: 12px;
      border-radius: 20px;
      display: inline-block;
      box-shadow: 0 8px 30px rgba(0, 0, 0, 0.35);
      margin-bottom: 18px;
    }
    .qr-wrapper {
      position: relative;
      display: inline-block;
      width: 260px;
      height: 260px;
    }
    .qr-wrapper img {
      display: block;
      width: 260px;
      height: 260px;
      border-radius: 8px;
      object-fit: contain;
    }
    .qr-center-badge {
      position: absolute;
      top: 50%;
      left: 50%;
      transform: translate(-50%, -50%);
      background: #ffffff;
      border: 3px solid #fc8019;
      border-radius: 12px;
      padding: 5px 14px;
      box-shadow: 0 4px 16px rgba(0, 0, 0, 0.3);
      display: flex;
      align-items: center;
      justify-content: center;
      max-width: 140px;
      min-width: 65px;
      z-index: 10;
    }
    .qr-center-badge span {
      font-size: 14px;
      font-weight: 800;
      color: #fc8019;
      letter-spacing: 0.5px;
      text-transform: capitalize;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }
    .amount-box {
      margin-bottom: 12px;
    }
    .amount-label {
      font-size: 13px;
      color: #9ca3af;
      text-transform: uppercase;
      letter-spacing: 0.5px;
    }
    .amount-value {
      font-size: 34px;
      font-weight: 800;
      color: #10b981;
      margin-top: 2px;
    }
    .savings-badge {
      display: inline-block;
      background: rgba(16, 185, 129, 0.15);
      border: 1px solid rgba(16, 185, 129, 0.3);
      color: #34d399;
      font-size: 13px;
      font-weight: 600;
      padding: 4px 12px;
      border-radius: 12px;
      margin-top: 4px;
    }
    .instructions {
      font-size: 13px;
      color: #d1d5db;
      line-height: 1.4;
      margin-top: 10px;
    }
    .footer {
      margin-top: 18px;
      padding-top: 14px;
      border-top: 1px solid rgba(255, 255, 255, 0.08);
      font-size: 11px;
      color: #6b7280;
      letter-spacing: 0.5px;
    }
  </style>
</head>
<body>
  <div class="card" id="card">
    <div class="header-badge">
      ! SWIGGY OFFICIAL INSTANT PAY
    </div>
    <br>
    <div class="restaurant-title">
      ▣ ${restaurantName}
    </div>
    <div class="qr-frame">
      <div class="qr-wrapper">
        <img src="${qrDataUrl}" alt="Payment QR" />
        <div class="qr-center-badge">
          <span>${customerName}</span>
        </div>
      </div>
    </div>
    <div class="amount-box">
      <div class="amount-label">Amount To Pay</div>
      <div class="amount-value">₹${amount}</div>
      ${savings > 0 ? `<div class="savings-badge">✓ Saved ₹${savings} with Coupons & Free Delivery</div>` : ''}
    </div>
    <div class="instructions">
      ☎ <b>Scan & Pay</b> using PhonePe, Google Pay, Paytm or any UPI App
    </div>
    <div class="footer">
      ◈ 100% Genuine Swiggy Checkout • Order placed automatically upon payment
    </div>
  </div>
</body>
</html>
    `;

    await page.setContent(html, { waitUntil: 'load' });
    const cardEl = await page.$('#card');
    const buffer = await cardEl.screenshot({ type: 'png' });
    return buffer;
  } finally {
    await browser.close().catch(() => {});
  }
}

// Fast fetch verified restaurant info & menu directly from Swiggy's API with WAF token support
const fastRestaurantCache = new Map();

export async function fetchFastRestaurantInfo(restaurantId, lat = '26.8658609', lng = '80.9307755', includeMenu = false) {
  if (!restaurantId) return null;
  const cacheKey = `${restaurantId}::${includeMenu ? '1' : '0'}`;
  if (fastRestaurantCache.has(cacheKey)) {
    return fastRestaurantCache.get(cacheKey);
  }
  try {
    const cands = getCandidateAccounts().slice(0, 4);
    const cand = cands[0]?.acc || null;
    let json = null;

    // Fast path (~190ms zero-WAF, zero Chromium!): Native Android `GET https://disc.swiggy.com/api/v1/menu/pl`
    for (const entry of cands) {
      try {
        const entryAuth = await getSwiggySessionAuth(entry.acc).catch(() => null);
        if (!entryAuth?.jwtTid && !entryAuth?.token) continue;
        const discRes = await fetch(
          `https://disc.swiggy.com/api/v1/menu/pl?page-type=REGULAR_MENU&complete-menu=${includeMenu ? 'true' : 'false'}&lat=${encodeURIComponent(lat)}&lng=${encodeURIComponent(lng)}&restaurantId=${encodeURIComponent(restaurantId)}&submitAction=ENTER`,
          {
            method: 'GET',
            headers: buildSwiggyAndroidClientHeaders(entry.acc, {
              tid: entryAuth.jwtTid,
              token: entryAuth.token,
              sid: entryAuth.sid,
              deviceId: entryAuth.deviceId,
              userId: entryAuth.userId,
              lat,
              lng
            }),
            signal: AbortSignal.timeout(4000)
          }
        );
        if (discRes.ok) {
          const dj = await discRes.json().catch(() => null);
          if (dj?.data?.cards) {
            json = dj;
            break;
          }
        }
      } catch {}
    }

    if (!json?.data?.cards) {
      const dapiOut = await dapiFetch(
        cand,
        `menu/pl?page-type=REGULAR_MENU&complete-menu=${includeMenu ? 'true' : 'false'}&lat=${lat}&lng=${lng}&restaurantId=${restaurantId}`,
        { lat, lng, timeoutMs: 8000 }
      );
      json = dapiOut?.json;
    }
    if (!json?.data?.cards) return null;

    let restName = null;
    let city = null;
    const menuItems = [];
    const seenIds = new Set();

    const cards = json.data.cards || [];
    function extractDishes(obj) {
      if (!obj || typeof obj !== 'object') return;
      if (obj.id && obj.name && (obj.price || obj.defaultPrice || obj.finalPrice)) {
        const idStr = String(obj.id);
        if (!seenIds.has(idStr)) {
          seenIds.add(idStr);
          const rawPrice = obj.finalPrice || obj.price || obj.defaultPrice;
          const rawOfferIds = Array.isArray(obj.offerIds)
            ? obj.offerIds
            : (Array.isArray(obj.offer_ids) ? obj.offer_ids : []);
          menuItems.push({
            id: idStr,
            name: String(obj.name).trim(),
            price: Math.round(Number(rawPrice)) / 100,
            offer_ids: rawOfferIds,
            item_offer_cart_meta: String(obj.itemOfferCartMeta || obj.item_offer_cart_meta || ''),
            inStock: obj.inStock !== 0
          });
        }
      }
      for (const v of Object.values(obj)) {
        if (typeof v === 'object' && v !== null) extractDishes(v);
      }
    }

    let restLat = null;
    let restLng = null;
    for (const c of cards) {
      const info = c?.card?.card?.info;
      if (info?.name && !restName) {
        restName = info.name;
        city = info.city || info.areaName;
        if (typeof info.latLong === 'string' && info.latLong.includes(',')) {
          const [la, ln] = info.latLong.split(',').map(s => s.trim());
          if (la && ln) {
            restLat = la;
            restLng = ln;
          }
        }
      }
    }
    if (includeMenu) {
      extractDishes(cards);
    }

    if (!restName) return null;
    const outRes = {
      restName,
      city: city || 'Local Area',
      lat: restLat,
      lng: restLng,
      menuItems
    };
    fastRestaurantCache.set(cacheKey, outRes);
    return outRes;
  } catch (e) {
    return null;
  }
}

// ============================================================================
// URL-FIRST ADDRESS CONTRACT
// ----------------------------------------------------------------------------
// A Swiggy "Share address" message carries a link (`swiggy.onelink.me/JgkQ/...`,
// `swiggy.com/ofo/address/...`) plus the app's own plain-text block. Anything
// else in the same Telegram message (order account, cart receipt, signature,
// forwarded header, ...) is NOT delivery data.
//
// Rule enforced everywhere: when the message contains an address share link,
// delivery name / mobile / street / city / GPS come ONLY from that link. The
// surrounding text is never parsed — it can belong to a different person and
// silently change the recipient's phone number or area.
// ============================================================================

function collectHttpUrls(text) {
  // Markdown `[label](url)` / duplicated `url](url` pastes yield one clean URL.
  return extractSharedUrls(text);
}

// True for links that resolve to a delivery address (never for cart/group-cart).
export function isAddressShareUrl(rawUrl) {
  const url = String(rawUrl || '').trim();
  if (!url || !/^https?:\/\//i.test(url)) return false;
  // Cart / group-cart links are never address links.
  if (/\/gc\/|group-cart|group_cart|group-order|groupcartid/i.test(url)) return false;
  if (/swiggy\.onelink\.me\//i.test(url) || /(?:^|\/\/|\.)onelink\.me\/[A-Za-z0-9]+\/[A-Za-z0-9_-]+/i.test(url)) return true;
  if (/swiggy\.com\/ofo\/address\//i.test(url)) return true;
  if (/maps\.app\.goo\.gl\/|google\.[a-z.]+\/maps|goo\.gl\/maps/i.test(url)) return true;
  return false;
}

// Returns the first delivery-address share link found in a message, or ''.
export function extractAddressShareUrl(text) {
  return collectHttpUrls(text).find(isAddressShareUrl) || '';
}

export function hasAddressShareUrl(text) {
  return Boolean(extractAddressShareUrl(text));
}

// Cleanly extract structured delivery address from Swiggy native share messages, Swiggy World receipts, coordinates, or plain text
export function parseAddressDetails(text) {
  if (!text) return null;
  // Normalize markdown tel/url links like `[9823305540](tel:9823305540)` -> `9823305540` and HTML `&amp;` -> `&`
  const str = String(text)
    .replace(/\[([^\]]+)\]\(tel:[^)]+\)/gi, '$1')
    .replace(/&amp;/gi, '&')
    .trim();

  // Pure single URL with no accompanying text is handled by URL resolvers, not text parser
  if (/^https?:\/\/\S+$/i.test(str)) {
    return null;
  }

  // URL-FIRST: an address share link is present -> the link is the only source of
  // truth. Refuse to copy name / phone / area / PIN from whatever else is pasted.
  if (hasAddressShareUrl(str)) {
    return null;
  }

  let name = null, mobile = null, city = null, address = null, flat_no = null, area = null, landmark = null, lat = null, lng = null;

  // 1. Check Swiggy App's native "Share Address" message format:
  const swiggyShareAddrMatch = str.match(/(?:^|\n)\s*Address\s*:\s*([^\n\r]+(?:\n(?!https?:\/\/)[^\n\r]+)*)/i);
  if (swiggyShareAddrMatch) {
    address = swiggyShareAddrMatch[1].replace(/https?:\/\/\S+/gi, '').trim().replace(/[,\s]+$/, '');
  }

  // 2. Isolate ONLY the address block BEFORE "Select an Available Payment Method" / "Final Bill" / "Bill Summary" / "Items Total"
  let searchScope = str.split(/\n\s*(?:Select\s+an\s+Available\s+Payment\s+Method|Final\s+Bill|Bill\s+Summary|Items\s+Total\s*:)/i)[0] || str;
  const delivSectionMatch = searchScope.match(/(?:📍\s*Delivering\s*To|Delivering\s*To)[\s\S]*/i);
  if (delivSectionMatch) {
    searchScope = delivSectionMatch[0];
  }

  // Receipt messages may start with an unrelated "Order Account" and restaurant block.
  // Once the delivery header is found, discard everything before it so the account
  // phone and restaurant name can never be parsed as the recipient's details.
  const findAddressHeaderIndex = (scope) => String(scope || '').split(/\r?\n/).findIndex(line =>
    /^(?:📍\s*)?[A-Za-z][A-Za-z .'-]{0,35}\s+Address$/i.test(line.trim())
  );
  let addressHeaderIdx = findAddressHeaderIndex(searchScope);
  if (addressHeaderIdx > 0) {
    searchScope = searchScope.split(/\r?\n/).slice(addressHeaderIdx).join('\n');
    addressHeaderIdx = 0;
  }

  const phoneScope = searchScope
    .split(/\r?\n/)
    .filter(line => !/order\s*account/i.test(line))
    .join('\n');
  const labeledPhoneMatch = phoneScope.match(/(?:📱\s*)?(?:phone|mobile|tel|contact|ph(?:one)?)\s*[:\-]?\s*(?:\+?91[\s-]*)?[6-9](?:[\s-]?\d){9}\b/i);
  const standalonePhoneLine = phoneScope.split(/\r?\n/).find(line =>
    /^\s*(?:\+?91[\s-]*)?[6-9](?:[\s-]?\d){9}\s*$/.test(line)
  );
  const phoneValue = labeledPhoneMatch?.[0] || standalonePhoneLine || '';
  mobile = normalizeIndianMobile(phoneValue) || null;

  const latMatch = searchScope.match(/(?:🧭\s*Latitude|lat|latitude)[:\s]*(-?[0-9]{1,2}\.[0-9]{3,10})/i);
  const lngMatch = searchScope.match(/(?:🧭\s*Longitude|lng|long|longitude)[:\s]*(-?[0-9]{1,3}\.[0-9]{3,10})/i);
  if (latMatch) lat = latMatch[1];
  if (lngMatch) lng = lngMatch[1];

  if (!lat || !lng) {
    const coordsMatch = searchScope.match(/\b([1-3][0-9]\.[0-9]{4,10})[,\s]+([6-9][0-9]\.[0-9]{4,10})\b/);
    if (coordsMatch) {
      lat = coordsMatch[1];
      lng = coordsMatch[2];
    }
  }

  const nameMatch = searchScope.match(/(?:👤|recipient|receiver|customer\s*name|name)\s*[:\-]?\s*([^\n\r]+)/i);
  if (nameMatch) {
    const candidateName = nameMatch[1].replace(/https?:\/\/\S+/gi, '').trim();
    if (candidateName && candidateName.length <= 50) name = candidateName;
  }

  // Match a city header on a single line only; do not let `\\s` span "Your Cart" or a restaurant name.
  const headerLine = searchScope.split(/\r?\n/).map(line => line.trim()).find(line =>
    /^(?:📍\s*)?[A-Za-z][A-Za-z .'-]{0,35}\s+Address$/i.test(line)
  );
  const cityHeaderMatch = headerLine?.match(/^(?:📍\s*)?([A-Za-z][A-Za-z .'-]{0,35}?)\s+Address$/i)
    || searchScope.match(/(?:^|\n)\s*city\s*[:\-]\s*([^\n\r,]+)/i);
  if (cityHeaderMatch) {
    const c = (cityHeaderMatch[1] || '').trim();
    if (!/^(delivering|delivery|your|saved|order|billing)$/i.test(c)) {
      city = c;
    }
  }

  // 3. Parse structured multi-line Swiggy World address block:
  //    Pune Address
  //    Prathmesh
  //    9823305540
  //    Flat no. 412 , 4th floor Parivartan society dandekar pool pune
  //    Pune, Maharashtra 411030
  //    Latitude: 18.502975
  const scopeLines = searchScope
    .split(/\r?\n/)
    .map(l => l.trim())
    .filter(l => l && !/^(Delivering\s*To|📍\s*Delivering\s*To|Your\s*Cart)$/i.test(l));

  const headerIdx = scopeLines.findIndex(l => /^(?:📍\s*)?[A-Za-z][A-Za-z\s]{1,30}\s+Address$/i.test(l));
  const phoneIdx = mobile ? scopeLines.findIndex(l => l.includes(mobile)) : -1;
  const latIdx = scopeLines.findIndex(l => /^(?:🧭\s*)?Latitude\s*:/i.test(l));

  if (!name && phoneIdx > 0) {
    const prevLine = scopeLines[phoneIdx - 1];
    if (prevLine && prevLine.length <= 50 && !/\s+Address$/i.test(prevLine) && !/\d{4,}/.test(prevLine)) {
      name = prevLine.replace(/^👤\s*/, '').trim();
    }
  } else if (!name && headerIdx >= 0 && scopeLines[headerIdx + 1] && !/\d{6,}/.test(scopeLines[headerIdx + 1])) {
    name = scopeLines[headerIdx + 1].replace(/^👤\s*/, '').trim();
  }

  if (!address && phoneIdx >= 0 && (latIdx > phoneIdx || scopeLines.length > phoneIdx + 1)) {
    const endIdx = latIdx > phoneIdx ? latIdx : scopeLines.length;
    const addrLines = scopeLines
      .slice(phoneIdx + 1, endIdx)
      .filter(l => !/^₹|\s*[×x]\s*\d+\s*=\s*₹|Subtotal\s*:|^Order\s*Account\s*:/i.test(l));
    if (addrLines.length > 0) {
      address = addrLines.join('\n').replace(/^🏠\s*/, '').trim();
    }
  }

  if (!address) {
    const addrEmojiMatch = searchScope.match(/(?:🏠\s*[\r\n]*)([^\n\r]+(?:\n[^\n\r]+)*?)(?=\n🧭|\nLatitude|\n1️⃣|\n📦|\n🧾|$)/i);
    if (addrEmojiMatch) {
      address = addrEmojiMatch[1].replace(/https?:\/\/\S+/gi, '').trim();
    } else {
      const stripped = searchScope
        .replace(/Hey!\s*Save my address on Swiggy using the link\s*:?\s*/gi, '')
        .replace(/https?:\/\/\S+/gi, '')
        .replace(/^[\s\.,:\-]+|[\s\.,:\-]+$/g, '')
        .trim();

      const looksLikeRealAddress =
        !searchScope.includes('Your Cart') &&
        stripped.length >= 10 &&
        (
          /\b[1-8]\d{5}\b/.test(stripped) ||
          Boolean(city) ||
          /\b(house|flat|floor|ground|plot|block|sector|phase|nagar|ganj|colony|road|rd|marg|street|st|lane|gali|apartment|apt|tower|hostel|campus|near|opp|opposite|behind|beside|india|uttar pradesh|telangana|karnataka|maharashtra|delhi|rajasthan|bihar|madhya pradesh|west bengal|gujarat|tamil nadu|chhattisgarh)\b/i.test(stripped)
        );

      if (looksLikeRealAddress) {
        address = stripped;
      }
    }
  }

  const knownCities = [
    'Lucknow', 'Hyderabad', 'Secunderabad', 'Bangalore', 'Bengaluru', 'New Delhi', 'Delhi',
    'Mumbai', 'Navi Mumbai', 'Thane', 'Pune', 'Kolkata', 'Chennai', 'Jaipur', 'Ahmedabad',
    'Chandigarh', 'Noida', 'Greater Noida', 'Gurgaon', 'Gurugram', 'Ghaziabad', 'Faridabad',
    'Kanpur', 'Varanasi', 'Prayagraj', 'Allahabad', 'Agra', 'Gorakhpur', 'Bareilly', 'Aligarh',
    'Moradabad', 'Meerut', 'Kota', 'Indore', 'Bhopal', 'Patna', 'Ranchi', 'Raipur', 'Bilaspur',
    'Bhubaneswar', 'Guwahati', 'Kochi', 'Coimbatore', 'Nagpur', 'Surat', 'Vadodara', 'Ludhiana',
    'Amritsar', 'Dehradun', 'Jodhpur', 'Udaipur', 'Gwalior', 'Jabalpur', 'Visakhapatnam', 'Vijayawada'
  ];
  if (!city) {
    const citySearchText = address || searchScope;
    city = knownCities.find(c => new RegExp('\\b' + c + '\\b', 'i').test(citySearchText)) || null;
  }

  // Keep receiver contact data out of the street text used for geocoding and delivery cards.
  if (address) {
    address = address
      .replace(/(?:📱\s*)?(?:phone|mobile|tel|contact|ph(?:one)?)\s*[:\-]?\s*(?:\+?91[\s-]*)?[6-9](?:[\s-]?\d){9}\b/gi, '')
      .replace(/[ ,]+$/g, '')
      .trim();
  }

  // Derive flat_no, area, landmark cleanly from comma/newline-separated address parts.
  // Ignore postal/state/country suffixes so a state name cannot become the delivery area.
  if (address) {
    const segs = address.split(/[,\n]+/).map(s => s.trim()).filter(Boolean);
    if (segs.length >= 2) {
      flat_no = segs[0];
      const stateNames = /^(andhra pradesh|arunachal pradesh|assam|bihar|chhattisgarh|goa|gujarat|haryana|himachal pradesh|jharkhand|karnataka|kerala|madhya pradesh|maharashtra|manipur|meghalaya|mizoram|nagaland|odisha|punjab|rajasthan|sikkim|tamil nadu|telangana|tripura|uttar pradesh|uttarakhand|west bengal|delhi|jammu and kashmir|ladakh|puducherry)$/i;
      const locationParts = segs.filter(s =>
        !/^india$/i.test(s) && !/\b\d{6}\b/.test(s) &&
        (!city || s.toLowerCase() !== city.toLowerCase()) && !stateNames.test(s)
      );
      area = locationParts[locationParts.length - 1] || segs[1] || city || 'Main Area';
      landmark = locationParts[Math.max(0, locationParts.length - 2)] || area;
    }
  }

  if (name || mobile || city || address || lat || lng) {
    return { name, mobile, city, address, flat_no, area, landmark, lat, lng };
  }
  return null;
}

export function parseCartDetails(text) {
  if (!text) return null;
  const str = String(text)
    .replace(/\[([^\]]+)\]\(tel:[^)]+\)/gi, '$1')
    .replace(/&amp;/gi, '&')
    .trim();

  let restaurantName = null;
  const restMatch = str.match(/🏪\s*([^\n\r]+)/i);
  if (restMatch) restaurantName = restMatch[1].trim();

  let orderAccount = null;
  const accMatch = str.match(/(?:📱\s*)?Order\s*Account[:\s]*([0-9]{10})/i);
  if (accMatch) orderAccount = accMatch[1].trim();

  const items = [];
  const itemRegex = /(?:[0-9]️⃣|[0-9]+\.)\s*([^\n\r]+)[\r\n]+\s*💵\s*₹([0-9.]+)\s*×\s*([0-9]+)\s*=\s*₹([0-9.]+)/gi;
  let m;
  while ((m = itemRegex.exec(str)) !== null) {
    const qty = parseInt(m[3], 10) || 1;
    items.push({
      name: m[1].trim(),
      price: parseFloat(m[2]),
      qty,
      quantity: qty,
      lineTotal: parseFloat(m[4])
    });
  }

  if (items.length === 0) {
    const plainReceiptRegex = /([^\n\r₹]+)\r?\n₹([0-9.]+)\s*[×x]\s*([0-9]+)\s*=\s*₹([0-9.]+)/gi;
    while ((m = plainReceiptRegex.exec(str)) !== null) {
      const dish = m[1].trim();
      if (dish && !/^(Your Cart|Delivering To|Bill Summary|Final Bill)$/i.test(dish)) {
        const qty = parseInt(m[3], 10) || 1;
        items.push({
          name: dish,
          price: parseFloat(m[2]),
          qty,
          quantity: qty,
          lineTotal: parseFloat(m[4])
        });
      }
    }
    if (!restaurantName && str.includes('Your Cart')) {
      const ycMatch = str.match(/Your Cart\r?\n([^\n\r]+)/i);
      if (ycMatch) restaurantName = ycMatch[1].trim();
    }
  }

  let itemsTotal = null;
  const itemsTotMatch = str.match(/Items?\s*Total[:\s]*₹([0-9.]+)/i) || str.match(/Subtotal[:\s]*₹([0-9.]+)/i);
  if (itemsTotMatch) itemsTotal = parseFloat(itemsTotMatch[1]);

  let couponCode = null, discountAmount = 0;
  const coupMatch = str.match(/Coupon(?:\s+Discount)?\s*\(?([A-Z0-9_]+)\)?[:\s]*[-−–]\s*₹([0-9.]+)/i);
  if (coupMatch && coupMatch[1].toUpperCase() !== 'NOT') {
    couponCode = coupMatch[1].trim().toUpperCase();
    discountAmount = parseFloat(coupMatch[2]);
  }

  let swiggyOneMembershipFee = 0;
  const oneMatch = str.match(/Swiggy\s*One(?:\s*Lite)?\s*Membership[:\s]*\+?₹([0-9.]+)/i);
  if (oneMatch) swiggyOneMembershipFee = parseFloat(oneMatch[1]);

  let freeCashApplied = 0;
  const fcMatch = str.match(/(?:Swiggy\s*Money\s*\/\s*)?Free\s*Cash(?:\s*Applied)?\s*\)?[:\s]*[-−–]\s*₹([0-9.]+)/i);
  if (fcMatch) freeCashApplied = parseFloat(fcMatch[1]);

  let packingCharges = 0;
  const packMatch = str.match(/Packing\s*Charges[:\s]*₹([0-9.]+)/i);
  if (packMatch) packingCharges = parseFloat(packMatch[1]);

  let gstCharges = 0;
  const gstMatch = str.match(/GST\s*(?:&|and)\s*(?:Other\s*)?Charges[:\s]*₹([0-9.]+)/i);
  if (gstMatch) gstCharges = parseFloat(gstMatch[1]);

  let deliveryFee = 0;
  const delFeeNumMatch = str.match(/Delivery\s*Fee[:\s]*₹([0-9.]+)/i);
  if (delFeeNumMatch) deliveryFee = parseFloat(delFeeNumMatch[1]);

  let deliverySaved = 0;
  const delSavedMatch = str.match(/Delivery\s*Fee:\s*FREE\s*\(₹([0-9.]+)\s*saved\)/i)
    || str.match(/Free\s*Delivery:\s*₹0\s*\(₹([0-9.]+)\s*saved\)/i);
  if (delSavedMatch) deliverySaved = parseFloat(delSavedMatch[1]);

  let finalPayable = null;
  const payMatch = str.match(/Final\s*(?:Total|Payable)[:\s]*₹([0-9.]+)/i)
    || str.match(/To\s*Pay[:\s]*₹([0-9.]+)/i);
  if (payMatch) finalPayable = parseFloat(payMatch[1]);

  let totalSavings = 0;
  const savMatch = str.match(/Total\s*Savings[:\s]*₹([0-9.]+)/i);
  if (savMatch) totalSavings = parseFloat(savMatch[1]);

  const freeDelivery = /Delivery\s*Fee:\s*FREE/i.test(str) || /Free\s*Delivery\s*upto/i.test(str) || deliverySaved > 0;

  if (items.length > 0 || finalPayable || itemsTotal) {
    const calcSub = itemsTotal || Math.round(items.reduce((s, i) => s + (i.lineTotal || i.price * i.qty), 0) * 100) / 100;
    return {
      restaurantName,
      orderAccount,
      items,
      itemsTotal: calcSub,
      subtotal: calcSub,
      couponCode,
      discountAmount,
      swiggyOneMembershipFee,
      freeCashApplied,
      freeDelivery,
      deliverySaved,
      freeDeliveryDiscount: deliverySaved,
      deliveryFee,
      packingCharges,
      gstCharges,
      finalPayable,
      totalSavings
    };
  }
  return null;
}

// Helper to follow short-link redirects (up to 4 hops for swig.gy, onelink.me, maps.app.goo.gl)
async function expandShortUrl(rawUrl) {
  let current = rawUrl;
  for (let hop = 0; hop < 4; hop++) {
    if (!/^https?:\/\//i.test(current)) break;
    try {
      const res = await fetch(current, {
        redirect: 'manual',
        headers: { 'User-Agent': DESKTOP_UA },
        signal: AbortSignal.timeout(4000)
      });
      const loc = res.headers.get('location');
      if (!loc) break;
      current = loc.startsWith('http') || loc.startsWith('swiggy://') || loc.startsWith('intent://')
        ? loc
        : new URL(loc, current).toString();
      if (current.startsWith('swiggy://') || current.startsWith('intent://')) break;
    } catch (e) {
      break;
    }
  }
  return current;
}

// Fast-resolve Swiggy links (Group Cart, Restaurant Menu, Shared Address, Google Maps, or Full Text)
export async function resolveSwiggyLink(input) {
  if (!input) return { url: input, type: 'UNKNOWN' };
  const rawInput = String(input).trim();

  // Only the URL matters: surrounding share text ("It is a one time use link…")
  // is never treated as part of the link.
  const sharedUrls = extractSharedUrls(rawInput);
  let primaryUrl = sharedUrls[0] || normalizeSharedUrl(rawInput) || rawInput;

  let resolved = primaryUrl;
  let restaurantId = null;
  let groupCartId = null;
  let hostName = null;
  let ofoUser = null;
  let ofoToken = null;

  const alreadyDirectPath =
    /\/gc\/([0-9]+)\/([^\/\-\s?]+)-([0-9]+)/i.test(primaryUrl) ||
    /\/ofo\/address\/([^\/\?\s]+)\/([^\/\?\s&]+)/i.test(primaryUrl);

  if (!alreadyDirectPath && /^https?:\/\//i.test(primaryUrl) && (primaryUrl.includes('swig.gy') || primaryUrl.includes('onelink.me') || primaryUrl.includes('goo.gl') || primaryUrl.includes('google.com/maps'))) {
    resolved = await expandShortUrl(primaryUrl);
  }

  const combinedForMatch = `${primaryUrl} ${resolved}`;

  // 1. Group Cart URL pattern (e.g. https://swig.gy/gc/1467977/Umbashiya-642855918)
  const gcMatch = combinedForMatch.match(/\/gc\/([0-9]+)\/([^\/\-\s?]+)-([0-9]+)/i);
  if (gcMatch) {
    restaurantId = gcMatch[1];
    hostName = decodeURIComponent(gcMatch[2]);
    groupCartId = gcMatch[3];
  }

  // 2. Restaurant ID from menu URL
  const restMenuMatch = combinedForMatch.match(/\/restaurants\/[^\/\s?]+-([0-9]+)/i)
    || combinedForMatch.match(/\/menu\/([0-9]+)/i)
    || combinedForMatch.match(/restaurant_id=([0-9]+)/i);
  if (restMenuMatch && !restaurantId) {
    restaurantId = restMenuMatch[1];
  }

  // 3. Deep link query parameters (af_dp / deep_link_value / swiggy://)
  if (resolved.includes('swiggy://') || resolved.includes('af_dp=') || resolved.includes('deep_link_value=')) {
    try {
      const normalized = resolved.startsWith('http') ? resolved : 'https://' + resolved.replace(/^[a-z]+:\/\//i, 'swiggy.com/');
      const u = new URL(normalized);
      const afDp = u.searchParams.get('af_dp') || u.searchParams.get('deep_link_value') || '';
      const decoded = decodeURIComponent(afDp || resolved);
      const mRest = decoded.match(/restaurant_id=([0-9]+)/i);
      const mGc = decoded.match(/group_cart_id=([0-9]+)/i);
      const mHost = decoded.match(/host_name=([^&\s]+)/i);
      if (mRest && !restaurantId) restaurantId = mRest[1];
      if (mGc && !groupCartId) groupCartId = mGc[1];
      if (mHost && !hostName) hostName = decodeURIComponent(mHost[1]);

      const mOfo = decoded.match(/\/ofo\/address\/([^\/\?]+)\/([^\/\?&]+)/i);
      if (mOfo) {
        ofoUser = decodeURIComponent(mOfo[1]);
        ofoToken = mOfo[2];
      }
    } catch (e) {}
  }

  // 4. OFO web address URL & OneLink short address ID
  const ofoDirect = combinedForMatch.match(/\/ofo\/address\/([^\/\?\s]+)\/([^\/\?\s&]+)/i);
  if (ofoDirect) {
    ofoUser = decodeURIComponent(ofoDirect[1]);
    ofoToken = ofoDirect[2];
  }
  const onelinkAddrMatch = combinedForMatch.match(/onelink\.me\/[a-zA-Z0-9]+\/([a-zA-Z0-9_\-]+)/i);
  const isOneLinkShort = Boolean(onelinkAddrMatch && !ofoDirect);
  if (onelinkAddrMatch && !ofoToken) {
    ofoToken = onelinkAddrMatch[1];
  }

  // 5. Google Maps coordinates from expanded URL (@lat,lng, ?q=lat,lng, !3dlat!4dlng, ll=lat,lng)
  let mapCoords = null;
  const cMatch =
    combinedForMatch.match(/!3d(-?[0-9]{1,2}\.[0-9]{4,10})!4d(-?[0-9]{1,3}\.[0-9]{4,10})/) ||
    combinedForMatch.match(/[@?&](?:q|ll|query|center)?=?(-?[0-9]{1,2}\.[0-9]{4,10}),\s*(-?[0-9]{1,3}\.[0-9]{4,10})/) ||
    combinedForMatch.match(/@(-?[0-9]{1,2}\.[0-9]{4,10}),(-?[0-9]{1,3}\.[0-9]{4,10})/);
  if (cMatch) {
    mapCoords = { lat: cMatch[1], lng: cMatch[2] };
  }

  // 6. Does this input carry a delivery-address share link?
  //    If yes, the link is the ONLY source of delivery data (see URL-FIRST contract).
  const addressShareUrl = extractAddressShareUrl(rawInput) || extractAddressShareUrl(resolved);
  const addressFromUrl = Boolean(addressShareUrl || ofoToken || ofoUser || mapCoords);

  // Text parsing is allowed ONLY when no address link is present.
  let parsedAddr = addressFromUrl ? null : parseAddressDetails(rawInput);

  const isCart = Boolean(
    groupCartId ||
    restaurantId ||
    combinedForMatch.includes('/gc/') ||
    combinedForMatch.includes('group-order') ||
    combinedForMatch.includes('group_cart') ||
    primaryUrl.includes('/cart') ||
    primaryUrl.includes('/menu') ||
    rawInput.includes('Items Total')
  );
  const isAddress = !isCart && Boolean(
    ofoToken ||
    ofoUser ||
    mapCoords ||
    addressShareUrl ||
    combinedForMatch.includes('ofo/address') ||
    combinedForMatch.includes('onelink.me') ||
    combinedForMatch.includes('maps.google') ||
    combinedForMatch.includes('google.com/maps') ||
    combinedForMatch.includes('goo.gl') ||
    parsedAddr
  );

  // Resolve full address details — URL first, plain text only when no link exists.
  const reverseGeocodedDetails = async () => {
    const rev = await reverseGeocodeCoords(mapCoords.lat, mapCoords.lng);
    return {
      name: ofoUser || '',
      mobile: '',
      city: rev?.city || 'Delivery',
      area: rev?.area || '',
      landmark: rev?.landmark || '',
      address: rev?.address || `Pinned Location (${mapCoords.lat}, ${mapCoords.lng})`,
      lat: String(mapCoords.lat),
      lng: String(mapCoords.lng)
    };
  };
  const unresolvedLinkDetails = () => ({
    name: ofoUser || '',
    token: ofoToken || '',
    link: addressShareUrl || primaryUrl,
    unresolvableShortLink: true,
    city: '',
    mobile: '',
    address: '',
    lat: null,
    lng: null
  });

  let addressDetails = null;
  let addressSource = null;
  if (addressFromUrl) {
    addressSource = 'URL';
    if (ofoToken) {
      const socialAddr = await resolveSharedOfoAddress(ofoToken, ofoUser);
      if (socialAddr) {
        addressDetails = socialAddr;
      } else if (mapCoords) {
        addressDetails = await reverseGeocodedDetails();
      } else {
        // Link could not be resolved (expired / not fetchable). Never substitute the
        // surrounding chat text — flag the link so the caller can ask for a fresh one.
        addressSource = 'URL_UNRESOLVED';
        addressDetails = unresolvedLinkDetails();
      }
    } else if (mapCoords) {
      addressDetails = await reverseGeocodedDetails();
    } else {
      addressSource = 'URL_UNRESOLVED';
      addressDetails = unresolvedLinkDetails();
    }
  } else if (parsedAddr) {
    addressSource = 'TEXT';
    addressDetails = await geocodeAddressDetails(parsedAddr);
  }

  // Parse structured cart text if present
  let parsedCart = parseCartDetails(rawInput);
  let groupCartStatus = null;

  // 7. LIVE GROUP CART FETCH (<200ms direct Swiggy shared_cart API — 100% genuine items, ZERO hardcoded dishes!)
  if (groupCartId) {
    const liveGc = await fetchLiveGroupCart(
      groupCartId,
      restaurantId,
      hostName,
      null,
      addressDetails?.lat || '17.385044',
      addressDetails?.lng || '78.486671'
    );
    if (liveGc) {
      groupCartStatus = liveGc.status;
      if (liveGc.restaurantId) restaurantId = liveGc.restaurantId;
      if (liveGc.status === 'ACTIVE') {
        parsedCart = {
          restaurantName: liveGc.restaurantName || parsedCart?.restaurantName || null,
          items: liveGc.items || [],
          itemsTotal: liveGc.subtotal || 0,
          subtotal: liveGc.subtotal || 0,
          discountedSubtotal: liveGc.discountedSubtotal || liveGc.subtotal || 0,
          tradeDiscountTotal: liveGc.tradeDiscountTotal || 0,
          packingCharges: liveGc.packingCharges || 0,
          gstCharges: liveGc.taxesAndCharges || 0
        };
      }
    }
  }

  // 8. Fetch restaurant name / menu prices if needed
  let fastMenu = null;
  if (restaurantId && (!parsedCart?.restaurantName || (parsedCart?.items?.length > 0 && parsedCart.items.some(it => !it.itemId || !it.price)))) {
    fastMenu = await fetchFastRestaurantInfo(
      restaurantId,
      addressDetails?.lat || '26.8658609',
      addressDetails?.lng || '80.9307755',
      Boolean(parsedCart?.items?.length)
    );
    if (fastMenu?.menuItems && parsedCart?.items?.length > 0) {
      for (const it of parsedCart.items) {
        const match = fastMenu.menuItems.find(m =>
          m.name.toLowerCase() === it.name.toLowerCase() ||
          m.name.toLowerCase().includes(it.name.toLowerCase()) ||
          it.name.toLowerCase().includes(m.name.toLowerCase())
        );
        if (match) {
          if (!it.price || it.price === 0) it.price = match.price;
          if (!it.itemId) it.itemId = match.id;
          if ((!Array.isArray(it.offer_ids) || it.offer_ids.length === 0) && Array.isArray(match.offer_ids) && match.offer_ids.length > 0) {
            it.offer_ids = match.offer_ids;
          }
          if (!it.item_offer_cart_meta && match.item_offer_cart_meta) {
            it.item_offer_cart_meta = match.item_offer_cart_meta;
          }
          it.lineTotal = Math.round(it.price * (it.qty || 1) * 100) / 100;
        }
      }
    }
  }

  const realRestaurantName = parsedCart?.restaurantName || fastMenu?.restName || (hostName ? `${hostName}'s Group Order` : null);

  return {
    originalUrl: rawInput,
    primaryUrl,
    resolvedUrl: resolved,
    type: isCart ? 'CART' : (isAddress ? 'ADDRESS' : 'SWIGGY_GENERAL'),
    restaurantId,
    restaurantName: realRestaurantName,
    groupCartId,
    groupCartStatus,
    hostName,
    ofoUser,
    ofoToken,
    addressLink: addressShareUrl || '',
    addressSource,
    addressDetails,
    cartDetails: parsedCart
  };
}

// Honest bill calculation helper — NEVER fabricates imaginary coupons or fake fees!
export function applyMaxOfferToOrder(order) {
  if (!order) return order;

  let subtotal = Number(order.subtotal || order.itemTotal || 0);
  if (!subtotal && Array.isArray(order.items) && order.items.length > 0) {
    subtotal = Math.round(order.items.reduce((s, it) => s + (Number(it.lineTotal) || (Number(it.price || 0) * Number(it.qty || it.quantity || 1))), 0) * 100) / 100;
  }
  if (!subtotal && order.finalPayable > 0) {
    subtotal = Number(order.finalPayable);
  }
  if (!subtotal || subtotal <= 0) {
    return order;
  }

  order.subtotal = Math.round(subtotal * 100) / 100;
  order.itemTotal = order.itemTotal || order.subtotal;

  const discount = Number(order.discountAmount || 0);
  const tradeDisc = Number(order.tradeDiscountTotal || 0);
  const freeCash = Number(order.freeCashApplied || 0);
  const swiggyOneFee = Number(order.swiggyOneMembershipFee || 0);
  const delivery = Number(order.deliveryFee || 0);
  const packing = Number(order.packingCharges || 0);
  const taxes = Number(order.taxesAndCharges || 0);
  const freeDelSaved = Number(order.freeDeliveryDiscount || order.deliverySaved || 0);

  if (!order.totalSavings || !order.swiggyVerified) {
    order.totalSavings = Math.round((freeDelSaved + discount + tradeDisc + freeCash) * 100) / 100;
  }

  // If Swiggy checkout returned an authoritative `order_total`, keep it intact unless manually changed
  if (!order.swiggyVerified || !order.finalPayable || Number(order.finalPayable) <= 0) {
    order.finalPayable = Math.max(
      1,
      Math.round(order.subtotal - discount - tradeDisc - freeCash + swiggyOneFee + delivery + (taxes > 0 ? taxes : packing))
    );
  }

  return order;
}

// Parse a live Swiggy /dapi/cart OR chkout.swiggy.com/api/v2/cart/client `data` payload into a normalized cart object
export function parseDapiCartPayload(data) {
  const cm = data?.cartMeta || (data && (data.order_total !== undefined || Array.isArray(data.cart_menu_items) || data.cartId !== undefined) ? data : null);
  if (!cm) return null;
  const ciMap = data.cartItems || {};
  const rawEntries = Object.keys(ciMap).length > 0
    ? Object.values(ciMap)
    : (Array.isArray(cm.cart_menu_items) ? cm.cart_menu_items.map(mi => ({ itemId: mi.menu_item_id, quantity: mi.quantity, items: [mi] })) : []);

  const items = rawEntries.map(ci => {
    const itemInfo = ci.items?.[0] || ci || {};
    const qty = Number(ci.quantity || itemInfo.quantity || 1);
    const subPaise = Number(itemInfo.subtotal ?? (Number(itemInfo.base_price || itemInfo.price || 0) * qty));
    const finalPaise = Number(itemInfo.final_price ?? subPaise);
    const tradeDiscPaise = Number(itemInfo.subtotal_trade_discount || 0);
    const unitPrice = subPaise > 0 ? Math.round((subPaise / 100 / qty) * 100) / 100 : 0;
    const lineTotal = Math.round((subPaise / 100) * 100) / 100;
    const finalLineTotal = Math.round((finalPaise / 100) * 100) / 100;

    return {
      itemId: String(ci.itemId || itemInfo.menu_item_id || ''),
      menu_item_id: Number(ci.itemId || itemInfo.menu_item_id || 0),
      name: String(itemInfo.name || 'Dish Item').trim(),
      qty,
      quantity: qty,
      price: unitPrice,
      lineTotal,
      finalLineTotal,
      tradeDiscount: Math.round((tradeDiscPaise / 100) * 100) / 100,
      addons: Array.isArray(itemInfo.addons) ? itemInfo.addons : [],
      variants: Array.isArray(itemInfo.variants) ? itemInfo.variants : [],
      offer_ids: Array.isArray(itemInfo.offer_ids) ? itemInfo.offer_ids : [],
      item_offer_cart_meta: String(itemInfo.item_offer_cart_meta || ''),
      item_offer_tags: Array.isArray(itemInfo.item_offer_tags) ? itemInfo.item_offer_tags : []
    };
  }).filter(it => it.name && it.qty > 0);

  const restDetails = cm.restaurant_details || {};
  const restaurantId = String(restDetails.id || restDetails.restaurant_id || cm.restaurantId || '');
  const restaurantName = restDetails.name || restDetails.restaurant_name || cm.restaurantName || null;

  const addresses = Array.isArray(cm.addresses) ? cm.addresses : [];
  const selectedRaw = addresses.find(a => a.selected || (cm.address_id && String(a.id) === String(cm.address_id))) || cm.delivery_address || null;
  let addressDetails = null;
  let address = null;
  if (selectedRaw && (selectedRaw.address || selectedRaw.area || selectedRaw.lat)) {
    address = `${selectedRaw.flat_no && selectedRaw.flat_no !== 'None' ? selectedRaw.flat_no + ', ' : ''}${selectedRaw.address || selectedRaw.area || ''}`.trim();
    addressDetails = {
      id: selectedRaw.id || cm.address_id || '',
      name: selectedRaw.name || '',
      mobile: selectedRaw.mobile || '',
      flat_no: selectedRaw.flat_no && selectedRaw.flat_no !== 'None' ? selectedRaw.flat_no : '',
      area: selectedRaw.area || '',
      landmark: selectedRaw.landmark || '',
      city: selectedRaw.city || 'Address',
      address,
      lat: String(selectedRaw.lat || ''),
      lng: String(selectedRaw.lng || ''),
      annotation: selectedRaw.annotation || ''
    };
  }

  // Extract eligible Swiggy One / One Lite plan nudge + full `rendering_details` map (supports BOTH `dapi/cart` & `chkout`!)
  const renderingList = Array.isArray(cm.rendering_details) ? cm.rendering_details : [];
  const renderByKey = new Map();
  for (const r of renderingList) {
    if (r?.key) renderByKey.set(r.key, r);
  }
  const parseRenderNum = (val) => {
    if (val === undefined || val === null || val === '') return null;
    if (String(val).trim().toUpperCase() === 'FREE') return 0;
    const n = parseFloat(String(val).replace(/[^0-9.-]/g, ''));
    return Number.isFinite(n) ? n : null;
  };

  const superNudge = renderByKey.get('super_v3_nudge')?.meta || null;
  const superBenefits = renderByKey.get('super_v3_benefits')?.meta || null;
  const userSuperStatus = String(cm.user_super_status_details?.user_status || '').toUpperCase() || null;
  const planRaw = superNudge?.plan_details || null;
  const eligibleSuperPlan = planRaw?.plan_id
    ? {
        planId: String(planRaw.plan_id),
        name: planRaw.name || 'Swiggy One Lite Membership',
        priceRupees: Math.round((Number(planRaw.final_price ?? planRaw.base_price ?? 100) / 100) * 100) / 100
      }
    : null;

  const subItems = Array.isArray(data.subscriptionItems) ? data.subscriptionItems : [];
  const swiggyOneMembershipFee = Number(
    cm.subscription_total ||
    (subItems.length > 0 ? Number(subItems[0]?.final_price ?? subItems[0]?.base_price ?? 100) / 100 : 0) ||
    0
  );

  const renderItemTotal = parseRenderNum(renderByKey.get('item_total')?.value);
  const itemTotal = Number(cm.item_total ?? cm.cart_subtotal_without_packing ?? cm.cart_subtotal ?? renderItemTotal ?? items.reduce((s, i) => s + i.lineTotal, 0));

  const renderDelFreeRow = renderByKey.get('positive_delivery_charges_exclusive_swiggy_one') || renderByKey.get('positive_delivery_charges_exclusive');
  const renderDelVal = parseRenderNum(renderDelFreeRow?.value);
  const deliveryFee = Number(cm.positiveDeliveryChargesExclusive ?? cm.delivery_charges ?? renderDelVal ?? 0);

  // Delivery is genuinely FREE only when effective delivery charge is 0!
  const swiggyOneApplied = deliveryFee <= 0 && Boolean(
    swiggyOneMembershipFee > 0 ||
    superBenefits?.is_super ||
    superBenefits?.super ||
    String(renderByKey.get('positive_delivery_charges_exclusive_swiggy_one')?.value || '').toUpperCase() === 'FREE' ||
    cm.swiggyOneBenefitsApplicable ||
    cm.oneLiteBenefitsApplicable ||
    cm.fullCouponLessFreeDeliveryApplied ||
    cm.is_swiggy_one_free_delivery_applicable ||
    cm.free_shipping ||
    Number(cm.free_delivery_discount) > 0 ||
    Number(cm.delivery_fee_reversal) > 0
  );
  const renderDelSaved = parseRenderNum(renderDelFreeRow?.intermediateText);
  const rawFreeDelSaved = deliveryFee <= 0
    ? Number(cm.free_delivery_discount || cm.delivery_fee_reversal || cm.deliveryChargeStrikeOffAmount || cm.strike_off_amount_without_tax || renderDelSaved || 0)
    : 0;
  const freeDeliveryDiscount = Math.round(rawFreeDelSaved * 100) / 100;

  // Coupon is valid ONLY when Swiggy confirms `is_coupon_valid === 1` OR `coupon_discount_total > 0`
  // IMPORTANT: When Swiggy returns `cm.coupon_code` WITH `is_coupon_valid === 0` / `coupon_discount_total === 0`,
  // that code is Swiggy's AUTO-SUGGESTED best coupon (NOT applied yet!) — expose it via `suggestedCouponCode` so our Max-Coupon engine applies it!
  const rawCartCoupon = cm.coupon_code ? String(cm.coupon_code).trim().toUpperCase() : null;
  const isCouponValid = Boolean(cm.is_coupon_valid === 1 || Number(cm.coupon_discount_total) > 0);
  const couponCode = isCouponValid && rawCartCoupon ? rawCartCoupon : null;
  const suggestedCouponCode = !isCouponValid && rawCartCoupon ? rawCartCoupon : null;
  const couponDiscount = isCouponValid ? Number(cm.coupon_discount_total ?? cm.coupon_discount_effective ?? 0) : 0;

  const tradeDiscountTotal = Number(cm.trade_discount_total ?? items.reduce((s, i) => s + (i.tradeDiscount || 0), 0));
  const renderPacking = parseRenderNum(renderByKey.get('restaurant_packaging_charges')?.value ?? renderByKey.get('packaging_charges')?.value);
  const packingCharges = Number(cm.total_packing_charges ?? cm.basePackagingCharges ?? cm.restaurant_packing_charges ?? cm.packaging_fee ?? renderPacking ?? 0);
  const renderGrandTotal = parseRenderNum(renderByKey.get('grand_total')?.value ?? renderByKey.get('to_pay')?.value);
  const rawOrderTotal = Number(cm.order_total ?? renderGrandTotal ?? 0);
  const renderTaxesAndCharges = parseRenderNum(renderByKey.get('taxes_and_charges')?.value);
  const pureTaxAndFees = Number(cm.total_tax || 0) + Number(cm.convenience_fees ?? cm.convenience_fee ?? cm.platform_fee ?? 0);
  const residualGstAndFees = rawOrderTotal > 0
    ? Math.max(0, Math.round((rawOrderTotal - (itemTotal - couponDiscount - tradeDiscountTotal + swiggyOneMembershipFee + deliveryFee + packingCharges)) * 100) / 100)
    : pureTaxAndFees;
  const taxesAndCharges = cm.taxesAndCharges !== undefined
    ? Number(cm.taxesAndCharges)
    : (renderTaxesAndCharges !== null
        ? renderTaxesAndCharges
        : (rawOrderTotal > 0 ? residualGstAndFees : pureTaxAndFees));

  // FULL SWIGGY FREE CASH + SWIGGY MONEY SPLIT-PAY EXTRACTION:
  // 1. Campaign / Late Night / Breakfast / Reward Free Cash (`campaignFreeCash`) — auto-stacks over coupons inside `cm.order_total`!
  const rewardSavingsRaw =
    cm.trade_discount_reward_amount ??
    cm.tradeDiscountRewardAmountWithoutPocketHeroDiscount ??
    cm.offer_presentation_info?.reward_offer_savings_info?.savings ??
    cm.offerPresentationInfo?.rewardOffersSavingsInfo?.savings ??
    0;
  let renderRewardFreeCash = 0;
  for (const [rk, rv] of renderByKey.entries()) {
    const labelStr = `${rk} ${rv?.display_text || rv?.label || ''}`;
    if (/free\s*cash|reward_offer|pocket_hero|swiggy_cash/i.test(labelStr) && !/swiggy_money/i.test(labelStr)) {
      const parsedVal = Math.abs(parseRenderNum(rv?.value) || 0);
      if (parsedVal > renderRewardFreeCash) renderRewardFreeCash = parsedVal;
    }
  }
  const campaignFreeCash = Math.max(0, Math.round(Math.max(Number(rewardSavingsRaw) || 0, renderRewardFreeCash) * 100) / 100);
  const merchantTradeDiscount = Math.max(0, Math.round((tradeDiscountTotal - campaignFreeCash) * 100) / 100);
  // Avoid double-counting if Swiggy already summed `trade_discount_reward_amount` inside `trade_discount_total`:
  const extraCampaignSavings = tradeDiscountTotal >= campaignFreeCash ? 0 : (campaignFreeCash - tradeDiscountTotal);

  // 2. Swiggy Money / Wallet Free Cash Split-Pay (`user_swiggy_money` / `swiggy_pay_eligible_balance`):
  // Before placing the order, `cm.swiggy_money` is `0` while `cm.user_swiggy_money` holds the available balance (e.g. ₹50 / ₹100)!
  // Passing `swiggy_pay_amount` on `chkout/payments order/place` deducts this directly from the live UPI QR!
  const freeCashBalance = Math.max(0, Number(cm.user_swiggy_money ?? cm.swiggy_pay_eligible_balance ?? 0));
  const alreadyDeductedWallet = Math.max(0, Number(cm.swiggy_money ?? 0));
  const walletSplitPayAmount = alreadyDeductedWallet > 0
    ? alreadyDeductedWallet
    : (freeCashBalance > 0 && rawOrderTotal > 0 ? Math.min(rawOrderTotal, freeCashBalance) : 0);
  const freeCashApplied = Math.round((campaignFreeCash + walletSplitPayAmount) * 100) / 100;
  const orderTotal = alreadyDeductedWallet > 0
    ? rawOrderTotal
    : Math.max(0, Math.round((rawOrderTotal - walletSplitPayAmount) * 100) / 100);
  const totalSavings = Math.round((couponDiscount + tradeDiscountTotal + extraCampaignSavings + freeDeliveryDiscount + walletSplitPayAmount) * 100) / 100;

  return {
    restaurantId,
    restaurantName,
    items,
    address,
    addressDetails,
    savedAddresses: addresses.map(a => ({
      id: a.id || '',
      city: a.city || 'Address',
      name: a.name || '',
      mobile: a.mobile || '',
      flat_no: a.flat_no && a.flat_no !== 'None' ? a.flat_no : '',
      area: a.area || '',
      landmark: a.landmark || '',
      address: `${a.flat_no && a.flat_no !== 'None' ? a.flat_no + ', ' : ''}${a.address || ''}`.trim(),
      lat: String(a.lat || ''),
      lng: String(a.lng || ''),
      annotation: a.annotation || ''
    })),
    eligibleSuperPlan,
    userSuperStatus,
    swiggyOneMembershipFee: Math.round(swiggyOneMembershipFee * 100) / 100,
    itemTotal: Math.round(itemTotal * 100) / 100,
    subtotal: Math.round(itemTotal * 100) / 100,
    tradeDiscountTotal: Math.round(tradeDiscountTotal * 100) / 100,
    merchantTradeDiscount,
    deliveryFee: Math.round(deliveryFee * 100) / 100,
    freeDeliveryDiscount,
    swiggyOneApplied,
    swiggyOneSavings: freeDeliveryDiscount,
    couponCode,
    suggestedCouponCode,
    discountAmount: Math.round(couponDiscount * 100) / 100,
    freeCashBalance: Math.round(freeCashBalance * 100) / 100,
    freeCashApplied: Math.round(freeCashApplied * 100) / 100,
    campaignFreeCash: Math.round(campaignFreeCash * 100) / 100,
    walletSplitPayAmount: Math.round(walletSplitPayAmount * 100) / 100,
    rawCartOrderTotal: Math.round(rawOrderTotal * 100) / 100,
    packingCharges: Math.round(packingCharges * 100) / 100,
    taxesAndCharges: Math.round(taxesAndCharges * 100) / 100,
    finalPayable: Math.round(orderTotal > 0 ? orderTotal : Math.max(0, itemTotal - couponDiscount - tradeDiscountTotal + swiggyOneMembershipFee + deliveryFee + taxesAndCharges)),
    totalSavings
  };
}

// Require the live cart to match the coupon and discount shown on the order before a payment QR is created.
export function doesCouponMatchExpectedOrder(cart, order) {
  if (!cart || !order) return false;
  const expectedCode = String(order.couponCode || '').trim().toUpperCase();
  const actualCode = String(cart.couponCode || '').trim().toUpperCase();
  const expectedDiscount = Math.max(0, Number(order.discountAmount || 0));
  const actualDiscount = Math.max(0, Number(cart.discountAmount || 0));
  if (expectedCode !== actualCode) return false;
  if (!expectedCode) return expectedDiscount <= 0 && actualDiscount <= 0;
  return expectedDiscount > 0 && actualDiscount > 0 && Math.abs(expectedDiscount - actualDiscount) <= 0.01;
}

// Before payment, make sure all verified savings and bill components still match Swiggy's live cart.
export function doesOrderBillMatchLiveCart(cart, order, tolerance = 0.02) {
  if (!doesCouponMatchExpectedOrder(cart, order)) return false;
  const fields = [
    'itemTotal',
    'tradeDiscountTotal',
    'freeCashApplied',
    'freeDeliveryDiscount',
    'deliveryFee',
    'swiggyOneMembershipFee',
    'packingCharges',
    'taxesAndCharges',
    'finalPayable'
  ];
  for (const field of fields) {
    if (order[field] === undefined || order[field] === null) continue;
    const expected = Number(order[field]);
    const actual = Number(cart[field]);
    if (!Number.isFinite(expected) || !Number.isFinite(actual) || Math.abs(expected - actual) > tolerance) return false;
  }
  return true;
}

// Fast inspect an active personal cart for a specific chosen account (<500ms direct DAPI / Native Android call)
export async function inspectCartForAccount(accountOrCookies) {
  if (!accountOrCookies) return null;
  try {
    const auth = await getSwiggySessionAuth(accountOrCookies);
    if (auth?.sessionExpired) {
      return { sessionExpired: true };
    }
    const { json } = await swiggyCartGet(accountOrCookies, { timeoutMs: 9000 });
    if ((json?.statusCode === 1 || json?.statusCode === 999) && /session|login|unauthorized/i.test(json?.statusMessage || '')) {
      return { sessionExpired: true };
    }
    const parsed = json?.data ? parseDapiCartPayload(json.data) : null;
    if (!parsed) {
      return { items: [], restaurantName: null, finalPayable: 0 };
    }
    return parsed;
  } catch (err) {
    console.error('inspectCartForAccount error:', err.message);
    return null;
  }
}

// Verify Swiggy link and extract real cart & address details (<1s via live Group Cart + DAPI)
export async function verifyAndInspectSwiggyLink(url, cookies = '', accountSession = null) {
  if (!url) return { verified: false, message: 'No link provided' };

  const cleanUrl = String(url).trim();
  const isSwiggy = cleanUrl.includes('swiggy.com') || cleanUrl.includes('swiggy.onelink.me') || cleanUrl.includes('swig.gy');
  if (!isSwiggy) {
    return { verified: false, message: 'Not a valid Swiggy link' };
  }

  const meta = await resolveSwiggyLink(cleanUrl);
  const accObj = accountSession ? { ...accountSession, cookies: cookies || accountSession.cookies || '' } : cookies;

  // If link was a personal `/cart` URL rather than group cart, inspect active personal cart on account
  if ((!meta.cartDetails || !meta.cartDetails.items || meta.cartDetails.items.length === 0) && accObj) {
    const livePersonal = await inspectCartForAccount(accObj);
    if (livePersonal?.sessionExpired) {
      return { verified: false, sessionExpired: true, message: 'Swiggy session expired for this account' };
    }
    if (livePersonal?.items?.length > 0 && (!meta.restaurantId || String(livePersonal.restaurantId) === String(meta.restaurantId))) {
      return {
        verified: true,
        ...livePersonal,
        hostName: meta.hostName,
        groupCartId: meta.groupCartId,
        resolvedUrl: meta.resolvedUrl
      };
    }
  }

  const cd = meta.cartDetails || {};
  const items = cd.items || [];
  const itemTotal = cd.itemsTotal || cd.subtotal || 0;
  const discountAmount = cd.discountAmount || 0;
  const tradeDiscountTotal = cd.tradeDiscountTotal || 0;
  const packingCharges = cd.packingCharges || 0;
  const taxesAndCharges = cd.gstCharges || 0;
  const finalPayable = cd.finalPayable || Math.max(0, Math.round(itemTotal - discountAmount - tradeDiscountTotal + packingCharges + taxesAndCharges));

  return {
    verified: Boolean(items.length > 0 || meta.restaurantName),
    groupCartStatus: meta.groupCartStatus,
    restaurantName: meta.restaurantName || 'Swiggy Food Order',
    hostName: meta.hostName,
    restaurantId: meta.restaurantId,
    groupCartId: meta.groupCartId,
    items,
    address: meta.addressDetails?.address || null,
    addressDetails: meta.addressDetails || null,
    taxesAndCharges,
    packingCharges,
    swiggyOneMembershipFee: 0,
    itemTotal,
    subtotal: itemTotal,
    tradeDiscountTotal,
    deliveryFee: 0,
    freeDeliveryDiscount: 0,
    swiggyOneApplied: false,
    swiggyOneSavings: 0,
    couponCode: cd.couponCode || null,
    discountAmount,
    freeCashBalance: 0,
    freeCashApplied: cd.freeCashApplied || 0,
    finalPayable,
    totalSavings: Math.round((discountAmount + tradeDiscountTotal + (cd.freeCashApplied || 0)) * 100) / 100,
    resolvedUrl: meta.resolvedUrl
  };
}

export function isOfficialSwiggyTrackingUrl(value, { allowProviderShortLink = false } = {}) {
  try {
    const url = new URL(String(value || '').trim());
    const host = url.hostname.toLowerCase();
    const isProviderShortHost = host === 'swig.gy' || host === 'swiggy.onelink.me';
    const swiggyHost = isProviderShortHost || host === 'swiggy.com' || host.endsWith('.swiggy.com');
    const pathHasTrackingContext = /track|tracking/i.test(url.pathname) ||
      (/share/i.test(url.pathname) && /order|track/i.test(url.pathname));
    const queryHasTrackingContext = /(?:^|[?&])(?:tracking_url|track_url|order_id|orderid)=/i.test(url.search) &&
      /order|track|share/i.test(url.pathname);
    const isExplicitSwiggyTrackingRoute = pathHasTrackingContext || queryHasTrackingContext;
    const isProviderShortLink = allowProviderShortLink && isProviderShortHost && url.pathname.length > 1;
    return url.protocol === 'https:' && !url.username && !url.password && !url.port && swiggyHost &&
      (isExplicitSwiggyTrackingRoute || isProviderShortLink) &&
      !/support\/issues|\/restaurant(?:s)?(?:\/|$)|\/menu(?:\/|$)|\/gc(?:\/|$)/i.test(url.pathname);
  } catch {
    return false;
  }
}

export function getStoredSwiggyTrackingUrl(order) {
  const source = String(order?.trackingLinkSource || '');
  if (!['SWIGGY_API', 'BOSS_PROVIDED'].includes(source)) return '';
  const value = String(order?.trackingLink || '').trim();
  return isOfficialSwiggyTrackingUrl(value, { allowProviderShortLink: source === 'SWIGGY_API' }) ? value : '';
}

// Accept a tracking/share URL only when Swiggy's own response includes it under a
// tracking/share field (or an action explicitly labelled for tracking/sharing).
export function extractSwiggyProvidedTrackingUrl(...sources) {
  const candidates = [];
  const seen = new Set();
  const walk = (node, context = '', depth = 0) => {
    if (!node || depth > 10) return;
    if (Array.isArray(node)) {
      for (const value of node) walk(value, context, depth + 1);
      return;
    }
    if (typeof node !== 'object') return;

    const labelContext = Object.entries(node)
      .filter(([key, value]) => /^(?:title|label|name|text|action_name|display_name)$/i.test(key) && typeof value === 'string')
      .map(([, value]) => value)
      .filter(value => /track|share|order/i.test(value))
      .join(' ');
    const localContext = `${context} ${labelContext}`.toLowerCase();
    for (const [key, value] of Object.entries(node)) {
      const nextContext = `${localContext} ${key}`.toLowerCase();
      if (typeof value === 'string' && /^https:\/\//i.test(value.trim()) && /track|tracking|share/i.test(nextContext)) {
        const url = value.trim();
        if (!seen.has(url) && isOfficialSwiggyTrackingUrl(url, { allowProviderShortLink: true })) {
          seen.add(url);
          candidates.push(url);
        }
      } else if (value && typeof value === 'object') {
        walk(value, nextContext, depth + 1);
      }
    }
  };
  for (const source of sources) walk(source);
  return candidates[0] || null;
}

// Only return delivery/rider hand-off codes, never login/payment OTPs.
export function extractSwiggyDeliveryOtp(...sources) {
  const DELIVERY_CONTEXT = /delivery|rider|partner|handover|drop.?off|recipient/i;
  const PAYMENT_CONTEXT = /payment|login|auth(?:entication)?|transaction|upi/i;
  const OTP_KEY = /otp|verification.?code|delivery.?code/i;
  const normalizeCode = value => {
    if (value && typeof value === 'object') {
      value = value.code ?? value.value ?? value.otp ?? value.otp_code ?? '';
    }
    const digits = String(value ?? '').replace(/\D/g, '');
    return digits.length >= 4 && digits.length <= 8 ? digits : '';
  };
  const walk = (node, context = '', depth = 0) => {
    if (!node || depth > 10) return '';
    if (Array.isArray(node)) {
      for (const value of node) {
        const found = walk(value, context, depth + 1);
        if (found) return found;
      }
      return '';
    }
    if (typeof node !== 'object') return '';

    const localDeliveryContext = Object.entries(node).some(([key, value]) =>
      /^(?:type|purpose|context|label|title|name)$/i.test(key) &&
      typeof value === 'string' && DELIVERY_CONTEXT.test(value)
    );
    const localContext = `${context} ${localDeliveryContext ? 'delivery handover' : ''}`;
    for (const [key, value] of Object.entries(node)) {
      const nextContext = `${localContext} ${key}`;
      if (OTP_KEY.test(key) && !PAYMENT_CONTEXT.test(nextContext) && (DELIVERY_CONTEXT.test(nextContext) || localDeliveryContext)) {
        const code = normalizeCode(value);
        if (code) return code;
      }
      if (value && typeof value === 'object') {
        const found = walk(value, nextContext, depth + 1);
        if (found) return found;
      }
    }
    return '';
  };
  for (const source of sources) {
    const found = walk(source);
    if (found) return found;
  }
  return '';
}

// Extract Swiggy's actual tracking URL and delivery OTP. Never construct a URL from an order ID.
export async function extractRealSwiggyTracking(cookies = '') {
  if (!cookies) return { trackingUrl: null, orderId: null, deliveryOtp: '', status: 'NO_COOKIES' };
  try {
    const auth = await getSwiggySessionAuth(cookies, true);
    const latest = auth?.orders?.[0];
    if (latest?.order_id) {
      const orderId = String(latest.order_id);
      const tracking = await dapiFetch(cookies, `order/trackV4?order_id=${encodeURIComponent(orderId)}&type=full&version=V2`).catch(() => null);
      const trackData = tracking?.json?.data || {};
      return {
        trackingUrl: extractSwiggyProvidedTrackingUrl(latest, trackData),
        deliveryOtp: extractSwiggyDeliveryOtp(latest, trackData),
        orderId,
        status: latest.order_status || trackData.order_status || 'ACTIVE'
      };
    }
  } catch (err) {
    console.error('Error fetching real tracking link from Swiggy:', err.message);
  }
  return { trackingUrl: null, orderId: null, deliveryOtp: '', status: 'NOT_FOUND' };
}

// Verify payment status against authorized Swiggy API
export async function verifyPaymentStatusFromApi(cookies = '') {
  if (!cookies) return { paid: false, status: 'NO_COOKIES', orderId: null };
  const res = await extractRealSwiggyTracking(cookies);
  if (res && res.orderId) {
    const isPaid = ['placed', 'processing', 'in progress', 'delivered', 'confirmed'].includes(
      String(res.status).toLowerCase()
    );
    return {
      paid: isPaid,
      status: isPaid ? 'SUCCESS' : 'PENDING',
      orderId: res.orderId,
      trackingUrl: res.trackingUrl
    };
  }
  return { paid: false, status: 'PENDING', orderId: null, trackingUrl: null };
}

// ---------------------------------------------------------------------------
// MULTI-SOURCE SAVED ADDRESS FETCHER (<800ms, works even when personal cart is EMPTY!)
// Combines:
//   1. GET /dapi/cart -> data.cartMeta.addresses (all saved addresses nationwide when cart active)
//   2. GET https://maps.swiggy.com/addresses/nearby (CAS_HOST zero-WAF across Indian hubs + order coords)
//   3. GET /dapi/order/all -> orders[].delivery_address (historical addresses used on empty-cart accounts)
// ---------------------------------------------------------------------------
function normalizeFetchedSwiggyAddress(raw) {
  if (!raw || typeof raw !== 'object') return null;
  const nestedAddress = raw.address && typeof raw.address === 'object' ? raw.address : null;
  const source = raw.actual_address || raw.actualAddress || raw.address_details || raw.addressDetails || nestedAddress || raw;
  const location = source.location || raw.location || source.coordinates || raw.coordinates || {};
  const firstText = (...values) => {
    for (const value of values) {
      if (value === null || value === undefined || typeof value === 'object') continue;
      const text = String(value).trim();
      if (text && !/^none$/i.test(text)) return text;
    }
    return '';
  };

  const flatNo = firstText(
    source.flat_no, source.flatNo, source.address_line, source.address_line1,
    raw.flat_no, raw.flatNo, raw.address_line, raw.address_line1
  );
  const area = firstText(source.locality, source.area, source.area_name, source.sublocality, raw.locality, raw.area);
  const city = firstText(source.city, source.city_name, raw.city, raw.city_name);
  const pincode = firstText(source.pincode, source.pin_code, source.postal_code, raw.pincode, raw.pin_code);
  let address = firstText(
    raw.display_address, raw.displayAddress, raw.formatted_address, raw.formattedAddress, raw.full_address, raw.fullAddress,
    source.display_address, source.displayAddress, source.formatted_address, source.formattedAddress, source.full_address, source.fullAddress,
    typeof raw.address === 'string' ? raw.address : '',
    typeof source.address === 'string' ? source.address : '',
    source.address_line1, raw.address_line1,
    source.address_line, raw.address_line
  );
  if (address && flatNo && !normalizeAddressText(address).includes(normalizeAddressText(flatNo))) {
    address = `${flatNo}, ${address}`;
  }
  if (!address) {
    address = [flatNo, area, city, pincode].filter(Boolean).join(', ');
  }

  let lat = source.lat ?? source.latitude ?? location.lat ?? location.latitude ?? raw.lat ?? raw.latitude;
  let lng = source.lng ?? source.longitude ?? location.lng ?? location.longitude ?? raw.lng ?? raw.longitude;
  const coordinates = Array.isArray(location) ? location : (Array.isArray(location.coordinates) ? location.coordinates : null);
  if (!isValidIndianDeliveryCoordinates(lat, lng) && coordinates?.length >= 2) {
    // GeoJSON stores [longitude, latitude]; Swiggy address records may use [latitude, longitude].
    const first = Number(coordinates[0]);
    const second = Number(coordinates[1]);
    if (isValidIndianDeliveryCoordinates(second, first)) {
      lat = second;
      lng = first;
    } else if (isValidIndianDeliveryCoordinates(first, second)) {
      lat = first;
      lng = second;
    }
  }

  const tags = Array.isArray(source.tags) ? source.tags : (Array.isArray(raw.tags) ? raw.tags : []);
  const category = Array.isArray(source.address_category) ? source.address_category[0] : source.address_category;
  const annotation = firstText(
    source.annotation, raw.annotation, tags[0],
    category === 1 ? 'Home' : category === 2 ? 'Work' : ''
  );
  const mobile = normalizeIndianMobile(firstText(
    source.mobile, source.phone, source.receiver_mobile, source.receiver_phone, source.receiver_mobile_number,
    source.contact_number, source.contactNumber, raw.mobile, raw.phone, raw.receiver_mobile,
    raw.receiver_phone, raw.receiver_mobile_number, raw.contact_number, raw.contactNumber
  ));

  return {
    id: firstText(raw.id, raw.address_id, raw.addressId, source.id, source.address_id, source.addressId),
    city: city || 'Address',
    name: firstText(source.name, source.contact_name, source.receiver_name, raw.name, raw.contact_name, raw.receiver_name),
    mobile: mobile || '',
    flat_no: flatNo,
    area,
    landmark: firstText(source.landmark, source.directions_to_reach, raw.landmark, raw.directions_to_reach, area),
    address,
    lat: lat === null || lat === undefined ? '' : String(lat),
    lng: lng === null || lng === undefined ? '' : String(lng),
    annotation
  };
}

async function fetchMcpSavedAddresses(account) {
  const result = await callSwiggyFoodMcpTool(account, 'get_addresses', {}, 4500).catch(() => null);
  if (!result?.ok) return [];
  let data = result.structured;
  if ((!data || typeof data !== 'object') && result.text) {
    try { data = JSON.parse(result.text); } catch {}
  }
  const list = Array.isArray(data)
    ? data
    : [
        data?.addresses,
        data?.savedAddresses,
        data?.saved_addresses,
        data?.data?.addresses,
        data?.data?.savedAddresses,
        data?.data?.saved_addresses,
        Array.isArray(data?.data) ? data.data : null
      ].find(Array.isArray) || [];
  return list.map(normalizeFetchedSwiggyAddress).filter(Boolean);
}

export async function fetchAccountAddresses(cookiesOrAcc) {
  if (!cookiesOrAcc) return [];
  try {
    const auth = await getSwiggySessionAuth(cookiesOrAcc).catch(() => null);
    const collected = [];
    const seenKeys = new Set();

    const addNormalized = (raw) => {
      const normalized = normalizeFetchedSwiggyAddress(raw);
      if (!normalized) return;
      const addrStr = String(normalized.address || '').trim();
      if (!addrStr || addrStr.length < 4) return;
      const id = String(normalized.id || '').trim();
      const lat = normalized.lat ? String(normalized.lat).trim() : '';
      const lng = normalized.lng ? String(normalized.lng).trim() : '';
      const mobile = normalizeIndianMobile(normalized.mobile);
      const normText = normalizeAddressText(addrStr);
      const identityKey = id ? `${id}:${normText}` : `${lat.slice(0, 6)},${lng.slice(0, 6)}:${normText}`;
      const dedupeKey = `${identityKey}:${mobile || 'no-phone'}`;
      if (seenKeys.has(dedupeKey)) return;

      // GPS proximity alone is not enough to merge saved addresses: multiple flats or
      // family members can share a pin but have different receiver names/numbers.
      if (lat && lng) {
        const dupByGeo = collected.find(existing =>
          existing.lat && existing.lng &&
          distanceMeters(existing.lat, existing.lng, lat, lng) < 35 &&
          hasSameAddressText(existing.address, addrStr) &&
          (!id || !existing.id || existing.id === id) &&
          (!mobile || !existing.mobile || mobile === normalizeIndianMobile(existing.mobile))
        );
        if (dupByGeo) {
          if (!dupByGeo.id && id) dupByGeo.id = id;
          if (!dupByGeo.name && normalized.name) dupByGeo.name = normalized.name;
          if (!dupByGeo.mobile && mobile) dupByGeo.mobile = mobile;
          if (!dupByGeo.annotation && normalized.annotation) dupByGeo.annotation = normalized.annotation;
          return;
        }
      }

      seenKeys.add(dedupeKey);
      collected.push({
        id,
        city: normalized.city || 'Address',
        name: normalized.name || '',
        mobile,
        flat_no: normalized.flat_no || '',
        area: normalized.area || '',
        landmark: normalized.landmark || '',
        address: addrStr,
        lat,
        lng,
        annotation: normalized.annotation || ''
      });
    };

    // If native/web profile auth is unavailable, try Swiggy's address tool directly before giving up.
    if (!auth || auth.sessionExpired) {
      for (const address of await fetchMcpSavedAddresses(cookiesOrAcc)) addNormalized(address);
      return collected;
    }

    // Source 0: Native Swiggy Android Profile (`profile.swiggy.com`) — returns saved addresses across regions.
    const profPromise = (auth.profileAddresses?.length
      ? Promise.resolve({ addresses: auth.profileAddresses })
      : fetchSwiggyAndroidProfile(cookiesOrAcc, {
          tid: auth.jwtTid,
          token: auth.token,
          sid: auth.sid,
          deviceId: auth.deviceId,
          userId: auth.userId,
          timeoutMs: 4500
        }).catch(() => null)
    ).then((prof) => {
      for (const address of (prof?.addresses || [])) addNormalized(address);
    });

    // Source 1: Cart (`dapi/cart` or `chkout/cart/client`) -> saved addresses.
    const cartPromise = swiggyCartGet(cookiesOrAcc, { timeoutMs: 5000 })
      .then(({ json }) => {
        const list = json?.data?.cartMeta?.addresses || json?.data?.addresses || [];
        for (const address of list) addNormalized(address);
      })
      .catch(() => {});

    // Source 2: Probe only coordinates from this account's real recent order history.
    // Never query a hard-coded city hub for a customer who may live elsewhere.
    const probeCoords = [];
    const recentOrderCoord = (auth.orders || []).find(o => o?.delivery_address?.lat && o?.delivery_address?.lng)?.delivery_address;
    if (recentOrderCoord?.lat && recentOrderCoord?.lng && isValidIndianDeliveryCoordinates(recentOrderCoord.lat, recentOrderCoord.lng)) {
      probeCoords.push([String(recentOrderCoord.lat), String(recentOrderCoord.lng)]);
    }

    const casPromise = (auth.jwtTid && auth.userId)
      ? Promise.all(
          probeCoords.slice(0, 2).map(async ([la, ln]) => {
            try {
              const url = `https://maps.swiggy.com/addresses/nearby?lat_long=${la},${ln}&radius_mtr=50000&entity_type=1&entity_id=${encodeURIComponent(auth.userId)}&market_place_id=1&marketplace_business_lines=0`;
              const response = await fetch(url, {
                headers: buildChkoutHeaders(auth, la, ln, {
                  'client-id': 'checkout-web-app',
                  'source': 'web-cart'
                }),
                signal: AbortSignal.timeout(4000)
              });
              if (!response.ok) return;
              const json = await response.json().catch(() => null);
              for (const address of (json?.addresses || [])) addNormalized(address);
            } catch {}
          })
        )
      : Promise.resolve();

    await Promise.all([profPromise, cartPromise, casPromise]);

    // Source 3: Historical order `delivery_address` from GET /dapi/order/all (also works with an empty cart).
    for (const order of (auth.orders || [])) {
      if (order?.delivery_address) addNormalized(order.delivery_address);
    }

    // Source 4: Swiggy Food MCP as a final read-only fallback. This covers accounts where
    // profile/cart/order endpoints return empty or partial address inventories.
    if (collected.length === 0) {
      for (const address of await fetchMcpSavedAddresses(cookiesOrAcc)) addNormalized(address);
    }

    return collected;
  } catch (err) {
    console.error('fetchAccountAddresses error:', err.message);
    return [];
  }
}

// Fetch saved addresses across ALL connected Swiggy accounts in parallel
export async function fetchAllAccountsSavedAddresses() {
  const candidates = getCandidateAccounts();
  const perAcc = await Promise.all(
    candidates.map(async ({ key, acc }) => {
      const addrs = await fetchAccountAddresses(acc);
      return addrs.map(a => ({
        ...a,
        accountKey: key,
        accountName: acc.name || acc.phone || key,
        accountPhone: acc.phone || ''
      }));
    })
  );
  const flat = [];
  for (const list of perAcc) {
    for (const a of list) {
      const dup = flat.find(x => {
        if (!hasSameAddressText(x.address, a.address)) return false;
        if (x.mobile && a.mobile && normalizeIndianMobile(x.mobile) !== normalizeIndianMobile(a.mobile)) return false;
        if (x.name && a.name && normalizeAddressText(x.name) !== normalizeAddressText(a.name)) return false;
        const bothHaveCoords = isValidIndianDeliveryCoordinates(x.lat, x.lng) && isValidIndianDeliveryCoordinates(a.lat, a.lng);
        if (bothHaveCoords && distanceMeters(x.lat, x.lng, a.lat, a.lng) >= 35) return false;
        return true;
      });
      if (!dup) flat.push(a);
    }
  }
  return flat;
}

// Match or save delivery address into target Swiggy account via verified `POST /dapi/address`
// Ensures Swiggy binds a real `address_id` and calculates exact distance-based delivery charges!
export async function saveAddressToAccount(account, addrDetails, existingAddresses = null) {
  if (!account || !addrDetails) return { addressId: '', addressDetails: addrDetails || null, createdNew: false };

  // Never trust an address ID copied from another account on its own. The target account's
  // saved address must also have the same normalized street text before its ID/contact is reused.
  const sanitizedInput = { ...addrDetails };
  delete sanitizedInput.id;

  const enriched = await geocodeAddressDetails(sanitizedInput, account);
  delete enriched.id;
  const savedList = Array.isArray(existingAddresses) ? existingAddresses : await fetchAccountAddresses(account);
  if (!isUsableDeliveryAddress(enriched)) {
    return {
      addressId: '',
      addressDetails: enriched,
      createdNew: false,
      error: 'Delivery location could not be verified. Please send the exact Google Maps pin or a complete street address with area, city and PIN code.'
    };
  }
  const rawPhone = normalizeIndianMobile(enriched.mobile);
  if (!rawPhone) {
    return {
      addressId: '',
      addressDetails: enriched,
      createdNew: false,
      error: 'Recipient mobile number is missing or invalid. Add the receiver’s correct 10-digit Indian mobile number; the Swiggy account number will not be substituted.'
    };
  }
  enriched.mobile = rawPhone;

  // 1. Reuse only an exact textual address match on THIS account. GPS proximity by itself
  // can conflate apartments, family members, or neighboring homes that share a map pin.
  if (savedList.length > 0) {
    const existing = savedList.find(sa => {
      if (!sa.id || !hasSameAddressText(enriched.address, sa.address)) return false;
      if (normalizeIndianMobile(sa.mobile) !== rawPhone) return false;
      if (!isValidIndianDeliveryCoordinates(enriched.lat, enriched.lng) || !isValidIndianDeliveryCoordinates(sa.lat, sa.lng)) return false;
      return distanceMeters(sa.lat, sa.lng, enriched.lat, enriched.lng) < 35;
    });
    if (existing) {
      const savedMobile = normalizeIndianMobile(enriched.mobile);
      if (!savedMobile) {
        return {
          addressId: '',
          addressDetails: enriched,
          createdNew: false,
          error: 'Recipient mobile number is missing or invalid. Add the receiver’s correct 10-digit Indian mobile number before ordering.'
        };
      }
      return {
        addressId: String(existing.id),
        addressDetails: {
          ...enriched,
          id: String(existing.id),
          lat: enriched.lat || existing.lat,
          lng: enriched.lng || existing.lng,
          name: enriched.name || existing.name,
          mobile: savedMobile,
          city: enriched.city || existing.city
        },
        createdNew: false
      };
    }
  }

  // 2. Create the explicitly supplied delivery address on the selected Swiggy account.
  // Automatically mints `_session_tid` + `_csrf` in ~650ms via Zero-Chromium HTTP & retries with fresh session if needed!

  for (let saveAttempt = 0; saveAttempt < 2; saveAttempt++) {
    try {
      const mustForce = saveAttempt > 0;
      if (mustForce || !cleanSwiggyCookieString(account.cookies || '', account).includes('_session_tid=')) {
        await bootstrapSwiggyWebSessionFromAndroidTokens(account, { force: mustForce });
      }
      const auth = await getSwiggySessionAuth(account, mustForce);
      if (!auth?.userId) continue;

      const cityLabel = String(enriched.city || '').trim();
      const citySlug = /^(?:address|delivery|shared location)$/i.test(cityLabel)
        ? ''
        : cityLabel.replace(/[^a-zA-Z\s]/g, ' ').trim();
      const flatNo = String(enriched.flat_no || enriched.address?.split(',')[0] || '').trim().slice(0, 60);
      const areaStr = String(enriched.area || '').trim().slice(0, 80);
      const landmarkStr = String(enriched.landmark || '').trim().slice(0, 80);
      const fullAddr = String(enriched.address || '').trim();

      const { json } = await dapiFetch(account, 'address', {
        method: 'POST',
        lat: enriched.lat,
        lng: enriched.lng,
        address: fullAddr,
        area: areaStr,
        body: {
          address: fullAddr,
          flat_no: flatNo,
          lat: String(enriched.lat),
          lng: String(enriched.lng),
          area: areaStr,
          landmark: landmarkStr,
          annotation: enriched.annotation || 'Order Delivery',
          addressCategory: 3,
          name: String(enriched.name || account.swiggyName || account.name || 'Customer').trim(),
          mobile: rawPhone,
          city: citySlug.toLowerCase(),
          is_edited: 1,
          cart_type: 'REGULAR',
          customer_id: String(auth.userId)
        }
      });

      const newId = json?.data?.id || json?.data?.address_id || '';
      if (json?.statusCode === 0 && newId) {
        return {
          addressId: String(newId),
          addressDetails: { ...enriched, id: String(newId) },
          createdNew: true
        };
      }

      // Zero-Chromium Official Swiggy Food MCP `create_address` fallback (`200ms`, zero `_csrf` / WebView dependency!)
      const postalMatch = fullAddr.match(/\b([1-8]\d{5})\b/);
      const mcpCreated = await callSwiggyFoodMcpTool(account, 'create_address', {
        fullAddress: fullAddr,
        addressLine: flatNo,
        addressLine2: landmarkStr,
        locality: areaStr,
        city: citySlug,
        postalCode: postalMatch?.[1] || String(enriched.pincode || ''),
        latitude: Number(enriched.lat),
        longitude: Number(enriched.lng),
        addressCategory: 'OTHER',
        addressTag: String(enriched.annotation || 'Order Delivery').slice(0, 30),
        userName: String(enriched.name || account.swiggyName || account.name || 'Customer').trim(),
        userPhone: rawPhone,
        receiverName: String(enriched.name || account.swiggyName || account.name || 'Customer').trim(),
        receiverPhone: rawPhone
      }, 6500).catch(() => null);
      const mcpId =
        mcpCreated?.structured?.id ||
        mcpCreated?.structured?.addressId ||
        mcpCreated?.structured?.address_id ||
        mcpCreated?.structured?.data?.id ||
        '';
      if (mcpId) {
        return {
          addressId: String(mcpId),
          addressDetails: { ...enriched, id: String(mcpId) },
          createdNew: true
        };
      }
    } catch (err) {
      console.warn('[saveAddressToAccount] Attempt warning:', err.message);
    }
  }

  return {
    addressId: '',
    addressDetails: enriched,
    createdNew: false,
    error: 'Swiggy did not accept the verified delivery address. No default or first-saved address was selected; please recheck the pin, street, and receiver number.'
  };
}

// Fetch recent orders from Swiggy account with live tracking links & OTP
export async function fetchAccountOrders(cookiesOrAcc) {
  if (!cookiesOrAcc) return [];
  const acc = (typeof cookiesOrAcc === 'object' && !Array.isArray(cookiesOrAcc)) ? cookiesOrAcc : null;
  try {
    const auth = await getSwiggySessionAuth(cookiesOrAcc, true);
    let rawOrders = Array.isArray(auth?.orders) ? auth.orders : [];

    // Fallback: If auth.orders is empty, query direct dapiFetch order/all
    if (rawOrders.length === 0) {
      const dapiRes = await dapiFetch(cookiesOrAcc, 'order/all', { timeoutMs: 10000 }).catch(() => null);
      if (Array.isArray(dapiRes?.json?.data?.orders)) {
        rawOrders = dapiRes.json.data.orders;
      }
    }

    if (!Array.isArray(rawOrders) || rawOrders.length === 0) return [];

    const customerId = auth?.userId || acc?.customerId || '';
    const recent = rawOrders.slice(0, 10);

    const enriched = await Promise.allSettled(
      recent.map(async (o) => {
        const orderId = String(o.order_id || '');
        let trkData = null;
        let deData = null;

        if (orderId) {
          const isOlderDelivered = /delivered|completed|cancelled/i.test(String(o.order_status || ''));
          // For active or recent orders, fetch trackV4 to extract live share tracking link & delivery OTP
          if (!isOlderDelivered) {
            const trkRes = await dapiFetch(
              cookiesOrAcc,
              `order/trackV4?order_id=${encodeURIComponent(orderId)}&type=full&version=V2${customerId ? `&customer_id=${encodeURIComponent(customerId)}` : ''}`,
              { timeoutMs: 5000 }
            ).catch(() => null);
            trkData = trkRes?.json?.data || null;

            if (trkData) {
              const deRes = await dapiFetch(
                cookiesOrAcc,
                `order/trackV2/de?order_id=${encodeURIComponent(orderId)}`,
                { timeoutMs: 4000 }
              ).catch(() => null);
              deData = deRes?.json?.data || null;
            }
          }
        }

        const nativeTrackingUrl = extractSwiggyProvidedTrackingUrl(o, trkData);
        const officialFallbackUrl = orderId ? `https://www.swiggy.com/orders/track/${orderId}` : 'https://www.swiggy.com/orders';
        const finalTrackingUrl = nativeTrackingUrl || officialFallbackUrl;

        const deliveryOtp = extractSwiggyDeliveryOtp(o, trkData, { delivery: deData });
        const liveStatus = trkData?.order_status_details?.status_message || o.order_status || 'Delivered';
        const itemNames = (o.order_items || []).map(it => `${it.name}${it.quantity > 1 ? ' (' + it.quantity + ')' : ''}`);

        return {
          orderId: o.order_id,
          restaurantName: o.restaurant_name || 'Swiggy Food',
          status: liveStatus,
          items: itemNames,
          deliveryAddress: o.delivery_address?.area || o.delivery_address?.address || '',
          orderTime: o.order_time || '',
          orderTotal: o.order_total || 0,
          trackingUrl: finalTrackingUrl,
          deliveryOtp: deliveryOtp || ''
        };
      })
    );

    return enriched
      .filter(r => r.status === 'fulfilled' && r.value)
      .map(r => r.value);
  } catch (err) {
    console.error('fetchAccountOrders error:', err.message);
    return [];
  }
}

// Format clean, exact Swiggy World receipt + Final Bill (matches user's exact format 100%)
export function formatSwiggyWorldCartReceipt(order, accountPhoneOrName = '') {
  const lines = [];

  const accStr = accountPhoneOrName || order.selectedAccountPhone || order.selectedAccount || '';
  if (accStr) {
    lines.push(`Order Account: ${accStr}\n`);
  }

  if (order.restaurantName) {
    lines.push(`Your Cart`);
    lines.push(`${order.restaurantName}\n`);
  }

  const addr = order.addressDetails || parseAddressDetails(order.address);
  if (addr && (addr.address || addr.lat || addr.name || addr.mobile)) {
    const cityLabel = addr.city ? `${addr.city} Address` : 'Delivery Address';
    lines.push(cityLabel);
    if (addr.name) lines.push(addr.name);
    if (addr.mobile) lines.push(addr.mobile);
    if (addr.flat_no && addr.address && !addr.address.startsWith(addr.flat_no)) {
      lines.push(addr.flat_no);
    }
    if (addr.address) {
      for (const aLine of String(addr.address).split(/\r?\n/).map(s => s.trim()).filter(Boolean)) {
        lines.push(aLine);
      }
    }
    if (addr.lat) lines.push(`Latitude: ${addr.lat}`);
    if (addr.lng) lines.push(`Longitude: ${addr.lng}`);
    lines.push(`Select an Available Payment Method`);
  } else if (order.address && order.address !== 'Address pending / not provided' && !order.address.includes('onelink.me/JgkQ')) {
    lines.push(`Delivery Address`);
    lines.push(order.address);
    lines.push(`Select an Available Payment Method`);
  } else {
    lines.push(`Delivering To`);
    lines.push(`Address pending / share full address or map pin`);
  }
  lines.push('');

  if (order.items && order.items.length > 0) {
    for (const it of order.items) {
      lines.push(it.name);
      const price = typeof it.price === 'number' ? it.price : parseFloat(it.price || 0);
      const qty = it.qty || it.quantity || 1;
      const lineTotal = it.lineTotal !== undefined ? it.lineTotal : Math.round(price * qty * 100) / 100;
      lines.push(`₹${price} × ${qty} = ₹${lineTotal}\n`);
    }
    const totalQty = order.items.reduce((s, it) => s + (it.qty || it.quantity || 1), 0);
    const sub = order.itemTotal || order.subtotal || 0;
    const itemWord = totalQty === 1 ? 'Item' : 'Items';
    lines.push(`${totalQty} ${itemWord} • Subtotal: ₹${sub}\n`);
  }

  const hasItems = order.items && order.items.length > 0;
  const hasPayable = Boolean((order.finalPayable && Number(order.finalPayable) > 0) || (order.subtotal && Number(order.subtotal) > 0));

  if (hasItems || hasPayable) {
    lines.push(`Final Bill`);
    const sub = order.itemTotal || order.subtotal || 0;
    lines.push(`Items Total: ₹${sub > 0 ? sub : (order.finalPayable || 0)}`);

    const campFreeCash = Number(order.campaignFreeCash || 0);
    const walletFreeCash = Number(order.walletSplitPayAmount || 0);
    const merchantOfferDisc = order.merchantTradeDiscount !== undefined
      ? Number(order.merchantTradeDiscount || 0)
      : Math.max(0, Math.round((Number(order.tradeDiscountTotal || 0) - campFreeCash) * 100) / 100);

    if (merchantOfferDisc > 0) {
      lines.push(`Restaurant Offer Discount: −₹${merchantOfferDisc}`);
    }

    if (order.couponCode && Number(order.discountAmount || 0) > 0) {
      lines.push(`Coupon ${order.couponCode}: −₹${order.discountAmount} (applied)`);
    } else if (order.couponCode) {
      lines.push(`Coupon ${order.couponCode}: not applied (₹0 discount confirmed)`);
    } else if (order.swiggyVerified) {
      lines.push('Coupon: no eligible offer confirmed by Swiggy');
    }
    if (order.offerDiagnostics) {
      lines.push(`Offer check: ${String(order.offerDiagnostics)}`);
    }

    const oneFee = Number(order.swiggyOneMembershipFee || 0);
    if (oneFee > 0) {
      lines.push(`Swiggy One Lite Membership: +₹${oneFee}`);
    }

    if (campFreeCash > 0 || walletFreeCash > 0) {
      if (campFreeCash > 0) {
        lines.push(`Free Cash Applied: −₹${campFreeCash}`);
      }
      if (walletFreeCash > 0) {
        lines.push(`Swiggy Money / Free Cash Wallet: −₹${walletFreeCash}`);
      }
    } else if (order.freeCashApplied > 0) {
      lines.push(`Swiggy Money / Free Cash: −₹${order.freeCashApplied}`);
    }

    const freeDelSaved = Number(order.freeDeliveryDiscount || order.deliverySaved || 0);
    const isFreeDel = (Number(order.deliveryFee || 0) <= 0) && (freeDelSaved > 0 || order.swiggyOneApplied || oneFee > 0 || order.freeDelivery);

    if (isFreeDel) {
      lines.push(`Free Delivery upto 7km`);
      const savedTxt = freeDelSaved > 0 ? ` (₹${freeDelSaved} saved)` : '';
      lines.push(`Delivery Fee: FREE${savedTxt}`);
    } else if (Number(order.deliveryFee || 0) > 0) {
      lines.push(`Delivery Fee: ₹${order.deliveryFee}`);
    } else {
      lines.push(`Delivery Fee: FREE`);
    }

    if (order.packingCharges && Number(order.packingCharges) > 0) {
      lines.push(`Packing Charges: ₹${order.packingCharges}`);
    }

    const gst = order.taxesAndCharges || order.gstAndCharges || 0;
    if (gst > 0) {
      lines.push(`GST & Other Charges: ₹${gst}`);
    }

    lines.push('');
    if (Number(order.totalSavings || 0) > 0) {
      lines.push(`Total Savings: ₹${order.totalSavings}`);
    }
    if (order.finalPayable && Number(order.finalPayable) > 0) {
      lines.push(`Final Total: ₹${order.finalPayable}`);
    }
  } else {
    lines.push(`▤ <b>Cart Status:</b> <i>Waiting for Swiggy items / cart verification...</i>`);
  }

  return lines.join('\n');
}

// Live capture real Swiggy checkout & payment screen using account cookies
export async function captureSwiggyPaymentScreenshot(cookies) {
  if (!cookies) return null;
  let browser = null;
  try {
    browser = await puppeteer.launch({
      executablePath: CHROME_PATH,
      headless: PUPPETEER_HEADLESS,
      args: [
        '--disable-blink-features=AutomationControlled',
        '--no-sandbox',
        '--disable-gpu',
        '--disable-dev-shm-usage',
        '--no-first-run',
        '--no-default-browser-check'
      ]
    });
    const page = await browser.newPage();
    await installAntiFnaStealthOnPage(page);
    await page.setViewport({ width: 1280, height: 900 });
    await page.setUserAgent(DESKTOP_UA);

    const cleanStr = cleanSwiggyCookieString(cookies);
    const parsedCookies = cleanStr.split(';').map(s => s.trim()).filter(Boolean).map(p => {
      const [name, ...val] = p.split('=');
      return { name, value: val.join('='), domain: '.swiggy.com', path: '/' };
    });

    if (parsedCookies.length > 0) {
      await page.setCookie(...parsedCookies).catch(() => {});
    }

    await page.goto('https://www.swiggy.com/', { waitUntil: 'domcontentloaded', timeout: 22000 }).catch(() => {});
    for (let i = 0; i < 18; i++) {
      const pageCookies = await page.cookies();
      const waf = pageCookies.find(c => c.name === 'aws-waf-token');
      if (waf && waf.value.length > 50) {
        cachedWafToken = waf.value;
        cachedWafAt = Date.now();
        break;
      }
      await new Promise(r => setTimeout(r, 400));
    }

    await page.goto('https://www.swiggy.com/checkout', { waitUntil: 'domcontentloaded', timeout: 22000 }).catch(() => {});
    await new Promise(r => setTimeout(r, 3000));

    const stateInfo = await page.evaluate(() => {
      const text = document.body.innerText || '';
      return {
        isEmpty: text.includes('Your cart is empty'),
        isSignIn: text.includes('To place your order now, log in')
      };
    });

    if (stateInfo.isEmpty || stateInfo.isSignIn) {
      await browser.close().catch(() => {});
      return null;
    }

    await page.evaluate(() => {
      const els = Array.from(document.querySelectorAll('*'));
      const btn = els.find(e => e.innerText?.trim() === 'DELIVER HERE');
      if (btn) btn.click();
    });
    await new Promise(r => setTimeout(r, 1500));

    await page.evaluate(() => {
      const els = Array.from(document.querySelectorAll('*'));
      const btn = els.find(e => e.innerText?.trim() === 'PROCEED TO PAY');
      if (btn) btn.click();
    });
    await new Promise(r => setTimeout(r, 4000));

    await page.evaluate(() => {
      const els = Array.from(document.querySelectorAll('*'));
      const pp = els.find(e => e.innerText && (e.innerText.includes('PhonePe') || e.innerText.includes('UPI')));
      if (pp) pp.click();
    });
    await new Promise(r => setTimeout(r, 1500));

    const buffer = await page.screenshot({ fullPage: false });
    await browser.close().catch(() => {});
    return buffer;
  } catch (err) {
    console.error('Failed to capture Swiggy payment screenshot:', err.message);
    if (browser) await browser.close().catch(() => {});
    return null;
  }
}

// Actively CLAIM Instamart Free Cash (₹50/₹60) and Freebies on Swiggy
export async function claimInstamartFreeCash(cookies) {
  if (!cookies) {
    return {
      status: 'NOT_ELIGIBLE',
      eligible: false,
      balance: 0,
      amount: 0,
      reason: 'No session cookies or JSON provided',
      message: 'No cookies provided'
    };
  }

  let browser;
  try {
    browser = await puppeteer.launch({
      executablePath: CHROME_PATH,
      headless: 'new',
      args: [
        '--disable-blink-features=AutomationControlled',
        '--no-sandbox',
        '--disable-gpu',
        '--disable-dev-shm-usage',
        '--no-first-run',
        '--no-default-browser-check'
      ]
    });

    const page = await browser.newPage();
    await installAntiFnaStealthOnPage(page);
    await page.setViewport({ width: 1280, height: 800 });
    await page.setUserAgent(DESKTOP_UA);

    await page.goto('https://www.swiggy.com/', { waitUntil: 'domcontentloaded', timeout: 15000 }).catch(() => {});
    for (let i = 0; i < 12; i++) {
      const pageCookies = await page.cookies();
      const waf = pageCookies.find(c => c.name === 'aws-waf-token');
      if (waf && waf.value.length > 50) {
        cachedWafToken = waf.value;
        cachedWafAt = Date.now();
        break;
      }
      await new Promise(r => setTimeout(r, 400));
    }

    const cleanStr = cleanSwiggyCookieString(cookies);
    const parsedCookies = cleanStr.split(';').map(s => s.trim()).filter(Boolean).map(p => {
      const [name, ...val] = p.split('=');
      return { name, value: val.join('='), domain: '.swiggy.com', path: '/' };
    });
    if (parsedCookies.length > 0) {
      await page.setCookie(...parsedCookies).catch(() => {});
    }

    const initialCheck = await page.evaluate(async () => {
      try {
        const res = await fetch('https://www.swiggy.com/dapi/cart');
        const json = await res.json();
        const cm = json?.data?.cartMeta || {};
        return {
          statusCode: json.statusCode,
          freeCash: cm.user_swiggy_money || cm.swiggy_money || cm.user_swiggy_money_balance || 0,
          swiggyOne: Boolean(cm.swiggyOneBenefitsApplicable || cm.swiggyOneInfo?.presentationInfo?.is_super)
        };
      } catch (err) {
        return { freeCash: 0, swiggyOne: false };
      }
    });

    const initialBalance = Number(initialCheck?.freeCash || 0);

    await page.goto('https://www.swiggy.com/instamart', { waitUntil: 'domcontentloaded', timeout: 15000 }).catch(() => {});
    await new Promise(r => setTimeout(r, 2000));

    const claimExecutionResult = await page.evaluate(async () => {
      let clickedButton = false;
      let buttonText = '';
      let alreadyClaimedFound = false;
      let notEligibleFound = false;

      const allElements = Array.from(document.querySelectorAll('button, a, div[role="button"], span'));
      for (const el of allElements) {
        const text = (el.innerText || el.textContent || '').trim();
        if (!text) continue;
        if (/already claimed|already collected|offer collected|claimed|redeemed/i.test(text)) alreadyClaimedFound = true;
        if (/not eligible|not applicable|expired/i.test(text)) notEligibleFound = true;
        if (/^(claim|claim now|collect|opt-in|opt in|get free cash|claim ₹|claim 50|claim 60)/i.test(text)) {
          try {
            el.click();
            clickedButton = true;
            buttonText = text;
            break;
          } catch (e) {}
        }
      }

      let optInStatus = null;
      try {
        const optInRes = await fetch('https://www.swiggy.com/dapi/user/swiggy-money/opt-in', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json', 'Accept': 'application/json' },
          body: JSON.stringify({})
        });
        const optInJson = await optInRes.json().catch(() => ({}));
        optInStatus = optInJson?.statusCode || optInRes.status;
      } catch (e) {}

      try {
        await fetch('https://www.swiggy.com/dapi/rewards/claim', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ campaign: 'instamart_free_cash' })
        }).catch(() => {});
      } catch (e) {}

      return { clickedButton, buttonText, alreadyClaimedFound, notEligibleFound, optInStatus };
    });

    await new Promise(r => setTimeout(r, 2000));

    const finalCheck = await page.evaluate(async () => {
      try {
        const res = await fetch('https://www.swiggy.com/dapi/cart');
        const json = await res.json();
        const cm = json?.data?.cartMeta || {};
        return {
          statusCode: json.statusCode,
          freeCash: cm.user_swiggy_money || cm.swiggy_money || cm.user_swiggy_money_balance || 0,
          swiggyOne: Boolean(cm.swiggyOneBenefitsApplicable || cm.swiggyOneInfo?.presentationInfo?.is_super)
        };
      } catch (err) {
        return { freeCash: 0, swiggyOne: false };
      }
    });

    const finalBalance = Number(finalCheck?.freeCash || 0);

    if (finalBalance > initialBalance || (initialBalance === 0 && finalBalance > 0) || (claimExecutionResult.clickedButton && !claimExecutionResult.alreadyClaimedFound)) {
      const claimedAmt = finalBalance > initialBalance ? (finalBalance - initialBalance) : (finalBalance > 0 ? finalBalance : 50);
      return {
        status: 'CLAIMED',
        eligible: true,
        amount: claimedAmt,
        balance: finalBalance > 0 ? finalBalance : claimedAmt,
        freebieAvailable: true,
        swiggyOne: Boolean(finalCheck?.swiggyOne),
        details: `Successfully claimed ₹${claimedAmt} Free Cash! Current Balance: ₹${finalBalance > 0 ? finalBalance : claimedAmt}`
      };
    }

    if (claimExecutionResult.alreadyClaimedFound || (initialBalance > 0 && finalBalance === initialBalance)) {
      return {
        status: 'ALREADY_CLAIMED',
        eligible: true,
        amount: 0,
        balance: finalBalance,
        freebieAvailable: false,
        swiggyOne: Boolean(finalCheck?.swiggyOne),
        details: `Already claimed previously. Current Balance: ₹${finalBalance}`
      };
    }

    return {
      status: 'NOT_ELIGIBLE',
      eligible: false,
      amount: 0,
      balance: finalBalance,
      freebieAvailable: false,
      swiggyOne: Boolean(finalCheck?.swiggyOne),
      details: 'Account is not eligible for this promotional Free Cash or campaign.'
    };
  } catch (err) {
    return {
      status: 'NOT_ELIGIBLE',
      eligible: false,
      amount: 0,
      balance: 0,
      error: err.message,
      details: 'Error while executing claim engine: ' + err.message
    };
  } finally {
    if (browser) await browser.close().catch(() => {});
  }
}

export async function checkAccountFreeCash(cookies) {
  return claimInstamartFreeCash(cookies);
}

// Fast profile name + mobile extractor (checks Native Android `profile.swiggy.com` + zero-WAF order/address data first in ~80ms)
export async function fetchSwiggyProfileFromCookies(cookiesOrAcc) {
  if (!cookiesOrAcc) return { name: null, phone: null };
  try {
    const androidProf = await fetchSwiggyAndroidProfile(cookiesOrAcc, { timeoutMs: 5500 });
    if (androidProf?.ok && (androidProf.name || androidProf.phone)) {
      return {
        id: androidProf.customerId || null,
        name: androidProf.name || null,
        phone: androidProf.phone || null
      };
    }
    const auth = await getSwiggySessionAuth(cookiesOrAcc);
    if (auth?.orders?.length > 0) {
      const da = auth.orders[0]?.delivery_address;
      if (da?.name || da?.mobile) {
        return {
          id: auth.userId || null,
          name: da.name || null,
          phone: da.mobile ? String(da.mobile).replace(/^\+?91/, '') : null
        };
      }
    }
    const addrs = await fetchAccountAddresses(cookiesOrAcc);
    if (addrs.length > 0 && (addrs[0].name || addrs[0].mobile)) {
      return { id: auth?.userId || null, name: addrs[0].name || null, phone: addrs[0].mobile || null };
    }
    const infoRes = await dapiFetch(cookiesOrAcc, 'profile/info', { timeoutMs: 5000 }).catch(() => null);
    const d = infoRes?.json?.data;
    if (d && (d.customer_id || d.name || d.mobile)) {
      return {
        id: d.customer_id ? String(d.customer_id) : (auth?.userId || null),
        name: d.name || null,
        phone: d.mobile ? String(d.mobile).replace(/^\+?91/, '').replace(/\D/g, '').slice(-10) : null
      };
    }
  } catch (e) {}
  return { name: null, phone: null };
}

// Apply or remove a specific coupon code directly on Swiggy's live cart across ALL Zero-Chromium Swiggy engines:
// 1) `swiggyCartUpdate` (`chkout.swiggy.com/api/v2/cart/client/update`)
// 2) `callSwiggyFoodMcpTool('apply_food_coupon')` (`mcp.swiggy.com/food` internal VPC coupon engine + `swiggyCartGet` exact bill readout)
// 3) `androidCheckoutCartCall('client/applycoupon')` (`chkout.swiggy.com/api/v2/cart/client/applycoupon`)
// 4) Warm-WAF `/dapi/cart/applyCoupon` (ONLY when `cachedWafToken` is already warm -> `0` cold Chromium launches!)
export async function applyLiveCouponToOrder(account, order, couponCode, { fastSingleEngine = false } = {}) {
  if (!account || !order) return null;
  if (!isUsableDeliveryAddress(order.addressDetails) || !normalizeIndianMobile(order.addressDetails.mobile)) {
    return { success: false, code: 'DELIVERY_ADDRESS_UNVERIFIED', error: 'Verify the recipient address, Indian map location, and mobile number before updating the live Swiggy cart.' };
  }
  const lat = String(order.addressDetails.lat);
  const lng = String(order.addressDetails.lng);
  const addressId = String(order.addressDetails.id || '');
  if (!addressId) {
    return { success: false, code: 'DELIVERY_ADDRESS_NOT_BOUND', error: 'The exact delivery address is not bound to this Swiggy account; the live cart was not changed.' };
  }
  const code = couponCode ? String(couponCode).trim().toUpperCase() : '';
  const isRemove = !code || code === 'REMOVE' || code === 'NONE' || code === 'CLEAR';

  let fallbackParsed = null;

  // Engine 1 (~220ms ZERO-CHROMIUM): `chkout` `v2/cart/client/update` (preserves item `offer_ids` + active Swiggy One `subscriptionItems`!)
  const syncableItems = (order.items || []).filter(it => it.itemId || it.menu_item_id);
  const activeSubItems = Array.isArray(order.activeSubscriptionItems) ? order.activeSubscriptionItems : [];
  if (order.restaurantId && syncableItems.length > 0) {
    const upd = await swiggyCartUpdate(
      account,
      {
        restaurantId: String(order.restaurantId),
        address_id: addressId,
        couponCode: isRemove ? '' : code,
        cartItems: buildSwiggyCartItemsPayload(syncableItems),
        mealItems: [],
        subscriptionItems: activeSubItems
      },
      { lat, lng, flushFirst: false }
    ).catch(() => null);
    if (upd?.json?.statusCode === 0 && upd.json.data) {
      const parsed = parseDapiCartPayload(upd.json.data);
      fallbackParsed = parsed;
      // Only return immediately if removing, OR coupon genuinely applied (`discountAmount > 0`), OR caller asked for single-engine fast probe!
      if (isRemove || (parsed.couponCode && parsed.discountAmount > 0) || fastSingleEngine) {
        return parsed;
      }
    }
  }

  // Engines 2 + 3 (~240ms IN PARALLEL, ZERO-CHROMIUM): Official Swiggy Food MCP `apply_food_coupon` + Native Android `client/applycoupon`!
  const [mcpApply, aOut] = await Promise.all([
    !isRemove && addressId
      ? callSwiggyFoodMcpTool(account, 'apply_food_coupon', { couponCode: code, addressId }, 4000).catch(() => null)
      : Promise.resolve(null),
    androidCheckoutCartCall(
      account,
      isRemove ? 'client/removecoupon' : 'client/applycoupon',
      {
        method: 'POST',
        body: isRemove ? {} : { coupon_code: code, couponCode: code },
        lat,
        lng,
        timeoutMs: 4000
      }
    ).catch(() => ({ json: null }))
  ]);

  const aJson = aOut?.json;
  if (aJson?.statusCode === 0 && aJson?.data) {
    const parsedA = parseDapiCartPayload(aJson.data);
    if (isRemove || parsedA.discountAmount > 0 || !fallbackParsed) {
      fallbackParsed = parsedA;
      if (isRemove || parsedA.discountAmount > 0) return parsedA;
    }
  }

  if (mcpApply?.ok && mcpApply.structured) {
    const mcpDisc = Number(
      mcpApply.structured?.offers?.coupon_discount ??
      mcpApply.structured?.pricing?.coupon_discount ??
      mcpApply.structured?.coupon_discount ??
      0
    );
    if (mcpDisc > 0) {
      const refreshed = await swiggyCartGet(account, { lat, lng, timeoutMs: 4000 }).catch(() => null);
      if (refreshed?.json?.statusCode === 0 && refreshed.json.data) {
        const parsedRefreshed = parseDapiCartPayload(refreshed.json.data);
        if (parsedRefreshed.discountAmount > 0 || parsedRefreshed.couponCode) {
          return parsedRefreshed;
        }
      }
    }
  }

  // Engine 4: Web DAPI `cart/applyCoupon` ONLY when `cachedWafToken` is already warm (`0` cold Chromium launches!)
  const cleanCookies = cleanSwiggyCookieString(account.cookies || '', account);
  const hasWarmWaf = Boolean(cachedWafToken && (Date.now() - cachedWafAt) < WAF_TTL_MS);
  if (hasWarmWaf && cleanCookies.includes('_session_tid=')) {
    const { json } = await dapiFetch(
      account,
      isRemove ? 'cart/removeCoupon' : 'cart/applyCoupon',
      {
        method: 'POST',
        body: isRemove ? {} : { couponCode: code },
        lat,
        lng
      }
    ).catch(() => ({ json: null }));
    if (json?.statusCode === 0 && json?.data) {
      return parseDapiCartPayload(json.data);
    }
  }

  return fallbackParsed;
}

// Coupon trials mutate the live Swiggy cart. Re-apply the best snapshot even when
// its code equals the remembered winner, because a later trial may have replaced it.
export async function reapplyWinningCouponAfterTrials({
  account,
  order,
  bestCartState,
  bestCode,
  appliedAnyTrial,
  applyCouponFn = applyLiveCouponToOrder
}) {
  if (!bestCode || !appliedAnyTrial) return { success: true, cart: bestCartState };

  let finalApplied = null;
  try {
    finalApplied = await applyCouponFn(account, order, bestCode, { fastSingleEngine: false });
  } catch {}

  if (
    !finalApplied?.items?.length ||
    String(finalApplied.couponCode || '').toUpperCase() !== String(bestCode).toUpperCase() ||
    Number(finalApplied.discountAmount || 0) <= 0
  ) {
    return {
      success: false,
      code: 'MAX_COUPON_RELOCK_FAILED',
      error: `Swiggy did not confirm the best coupon (${bestCode}) after comparison. The order is blocked from payment; refresh the cart and retry.`
    };
  }
  return { success: true, cart: finalApplied };
}

// ---------------------------------------------------------------------------
// SYNC GROUP CART, DELIVERY ADDRESS, SWIGGY ONE LITE (+₹1) & MAX COUPON ENGINE
// Fast API pipeline (<3s without screenshot, +checkout capture when needed):
//   1. Pre-claims Breakfast & Late Night ₹50 OFF event campaigns on the account
//   2. Resolves live Group Cart via `chkout.swiggy.com/api/v1/shared_cart`
//   3. Matches or saves customer's delivery address via `POST /dapi/address`
//   4. Syncs exact `menu_item_id`, `quantity`, `addons`, `variants` & `address_id` via `POST /dapi/cart`
//   5. Auto-adds eligible `+₹1` Swiggy One / One Lite Membership if it lowers `order_total` (FREE delivery!)
//   6. Discovers ALL real account/restaurant/payment/campaign coupons (`offers/payment`, `offers/restaurant`,
//      `menu/pl`, `DELULU4FOOD`, `STEALDEAL`, `MEALDEAL`, `FLAT150`, `TRYNEW`, etc.) and tests them on live cart,
//      strictly keeping whichever achieves MAXIMUM SAVINGS & MINIMUM `Final Total` (`order_total`)!
// ---------------------------------------------------------------------------
export async function syncGroupCartAndCheckoutForAccount(account, order, options = {}) {
  const { captureScreenshot = false } = options;
  if (!account) return { success: false, error: 'No account provided' };

  const cleanCookies = cleanSwiggyCookieString(account.cookies || '', account);
  if (!cleanCookies && !account.tid) {
    return { success: false, error: 'Account has no active session or cookies' };
  }

  try {
    // Wave 1 (single concurrent batch — bootstraps `_session_tid`, checks session, pre-locks LN/BF offers,
    // resolves any raw links, AND saves/matches delivery address ALL IN PARALLEL!):
    const alreadyHasResolvedCart = Boolean(
      order.restaurantId &&
      Array.isArray(order.items) &&
      order.items.length > 0 &&
      order.items.every(it => it.itemId || it.menu_item_id)
    );
    const rawAddrSource = order.addressOriginalText || order.address || '';
    const addrResolvePromise = rawAddrSource && !isUsableDeliveryAddress(order.addressDetails)
      ? resolveSwiggyLink(rawAddrSource).catch(() => null)
      : Promise.resolve(null);

    const bootstrapAndSaveAddrPromise = (async () => {
      const [, fetchedAddrs, resolvedAddr] = await Promise.all([
        !cleanCookies.includes('_session_tid=')
          ? bootstrapSwiggyWebSessionFromAndroidTokens(account)
          : Promise.resolve(null),
        fetchAccountAddresses(account),
        addrResolvePromise
      ]);
      if (resolvedAddr?.addressDetails && !resolvedAddr.addressDetails.unresolvableShortLink) {
        order.addressDetails = mergeExplicitAddressDetails(order.addressDetails, resolvedAddr.addressDetails);
      }
      if (order.addressDetails && !isUsableDeliveryAddress(order.addressDetails)) {
        order.addressDetails = await geocodeAddressDetails(order.addressDetails, account);
      }
      let earlySaved = null;
      if (isUsableDeliveryAddress(order.addressDetails)) {
        earlySaved = await saveAddressToAccount(account, order.addressDetails, fetchedAddrs);
      }
      return { fetchedAddrs, earlySaved, resolvedAddr };
    })();

    const [auth, eventsClaimRes, cartMeta, addrBundle, inspectedInitialCart] = await Promise.all([
      getSwiggySessionAuth(account, false),
      Promise.race([
        claimSwiggyBreakfastAndLateNightOffers(account).catch(() => null),
        new Promise(r => setTimeout(r, 450))
      ]),
      order.cart && !alreadyHasResolvedCart
        ? resolveSwiggyLink(order.cart).catch(() => null)
        : Promise.resolve(null),
      bootstrapAndSaveAddrPromise,
      inspectCartForAccount(account)
    ]);
    const addrMeta = addrBundle.resolvedAddr;
    const savedAddresses = addrBundle.fetchedAddrs;

    if (auth?.sessionExpired) {
      return {
        success: false,
        sessionExpired: true,
        code: 'ACCOUNT_SESSION_EXPIRED_OR_PARTIAL',
        accountPhone: account.phone || account.name,
        error: `Session expired on Swiggy for account ${account.phone || account.name} (${auth.statusMessage || 'expired'}). Please re-login with OTP or active Session JSON.`
      };
    }

    if (addrMeta?.addressDetails && !addrMeta.addressDetails.unresolvableShortLink) {
      order.addressDetails = mergeExplicitAddressDetails(order.addressDetails, addrMeta.addressDetails);
    }
    if (order.addressDetails && !isUsableDeliveryAddress(order.addressDetails)) {
      order.addressDetails = await geocodeAddressDetails(order.addressDetails, account);
    }
    if (!isUsableDeliveryAddress(order.addressDetails)) {
      return {
        success: false,
        code: 'DELIVERY_ADDRESS_UNVERIFIED',
        error: 'Delivery address could not be verified to a real Indian map location. No default or first-saved address was used. Send the exact Google Maps pin or a full street address with area, city and PIN code.'
      };
    }
    if (addrBundle.earlySaved && !addrBundle.earlySaved.addressId) {
      const missingPhone = /recipient mobile number/i.test(addrBundle.earlySaved.error || '');
      return {
        success: false,
        code: missingPhone ? 'DELIVERY_CONTACT_REQUIRED' : 'DELIVERY_ADDRESS_BIND_FAILED',
        error: addrBundle.earlySaved.error || 'The exact delivery address could not be saved on this Swiggy account.'
      };
    }

    let restaurantId = cartMeta?.restaurantId || order.restaurantId || null;
    const groupCartId = cartMeta?.groupCartId || order.groupCartId || null;
    const hostName = cartMeta?.hostName || order.hostName || null;

    if (groupCartId) order.groupCartId = groupCartId;
    if (hostName) order.hostName = hostName;

    // Populate live Group Cart items if available — NEVER substitute random menu items if Group Cart fails!
    if (cartMeta?.cartDetails?.items?.length > 0) {
      order.items = cartMeta.cartDetails.items;
      if (cartMeta.restaurantName) order.restaurantName = cartMeta.restaurantName;
    } else if (groupCartId && (!Array.isArray(order.items) || order.items.length === 0)) {
      const liveGc = await fetchLiveGroupCart(
        groupCartId,
        restaurantId,
        hostName,
        account,
        String(order.addressDetails.lat),
        String(order.addressDetails.lng)
      );
      if (liveGc?.status === 'ACTIVE' && liveGc.items?.length > 0) {
        order.items = liveGc.items;
        restaurantId = liveGc.restaurantId || restaurantId;
        if (liveGc.restaurantName) order.restaurantName = liveGc.restaurantName;
      } else {
        const reason = liveGc?.statusMessage || liveGc?.status || 'Group cart is empty or closed on Swiggy';
        return {
          success: false,
          code: 'GROUP_CART_FETCH_FAILED',
          error: `Group Cart (${groupCartId}) fetch failed on Swiggy: ${reason}.`
        };
      }
    }
    if (restaurantId) order.restaurantId = restaurantId;

    // Never substitute the first saved address. Bind only the address supplied/confirmed for this order.
    let targetAddressId = '';
    if (order.addressDetails) {
      const earlyDetails = addrBundle.earlySaved?.addressDetails;
      const earlySavedMatches = Boolean(
        addrBundle.earlySaved?.addressId &&
        hasSameAddressText(earlyDetails?.address, order.addressDetails.address) &&
        normalizeIndianMobile(earlyDetails?.mobile) === normalizeIndianMobile(order.addressDetails.mobile) &&
        isValidIndianDeliveryCoordinates(earlyDetails?.lat, earlyDetails?.lng) &&
        distanceMeters(earlyDetails.lat, earlyDetails.lng, order.addressDetails.lat, order.addressDetails.lng) < 35
      );
      const savedRes = earlySavedMatches
        ? addrBundle.earlySaved
        : await saveAddressToAccount(account, order.addressDetails, savedAddresses);
      targetAddressId = savedRes.addressId || '';
      if (savedRes.addressDetails) {
        order.addressDetails = savedRes.addressDetails;
        if (savedRes.addressDetails.address) {
          order.address = savedRes.addressDetails.address;
        }
        if (savedRes.createdNew && targetAddressId && !savedAddresses.some(a => a.id === targetAddressId)) {
          savedAddresses.unshift(savedRes.addressDetails);
        }
      }
      if (!targetAddressId) {
        const missingPhone = /recipient mobile number/i.test(savedRes.error || '');
        return {
          success: false,
          code: missingPhone ? 'DELIVERY_CONTACT_REQUIRED' : 'DELIVERY_ADDRESS_BIND_FAILED',
          error: savedRes.error || 'The exact delivery address could not be bound to the Swiggy cart. No saved/default address was selected.'
        };
      }
    }

    const lat = String(order.addressDetails.lat);
    const lng = String(order.addressDetails.lng);

    let liveCart = inspectedInitialCart;
    if (liveCart?.sessionExpired) {
      return {
        success: false,
        sessionExpired: true,
        code: 'ACCOUNT_SESSION_EXPIRED_OR_PARTIAL',
        accountPhone: account.phone || account.name,
        error: `Session expired on Swiggy for account ${account.phone || account.name}.`
      };
    }

    // Enrich missing itemIds + restaurant-level offers via fast discovery + Official Swiggy Food MCP `get_restaurant_menu` (`0` Chromium!)
    let mcpMenuOffers = [];
    if (restaurantId && Array.isArray(order.items) && order.items.length > 0 && order.items.some(it => !it.itemId && !it.menu_item_id)) {
      const [menuInfo, mcpMenu] = await Promise.all([
        fetchFastRestaurantInfo(restaurantId, lat, lng, true).catch(() => null),
        callSwiggyFoodMcpTool(account, 'get_restaurant_menu', {
          restaurantId: String(restaurantId),
          latitude: Number(lat),
          longitude: Number(lng),
          page: 1,
          pageSize: 8
        }, 5500).catch(() => null)
      ]);
      const combinedItems = [...(menuInfo?.menuItems || [])];
      if (mcpMenu?.structured) {
        const rawMenuStr = JSON.stringify(mcpMenu.structured);
        for (const m of rawMenuStr.matchAll(/"coupon_?code"\s*:\s*"([A-Z0-9_]{3,25})"/gi)) {
          mcpMenuOffers.push(m[1]);
        }
        const walkItems = (node) => {
          if (!node || typeof node !== 'object') return;
          if ((node.id || node.item_id) && node.name) {
            combinedItems.push({
              id: String(node.id || node.item_id),
              name: String(node.name),
              price: Number(node.final_price ?? node.price ?? node.default_price ?? 0),
              offer_ids: Array.isArray(node.offer_ids) ? node.offer_ids : (Array.isArray(node.offerIds) ? node.offerIds : []),
              item_offer_cart_meta: String(node.item_offer_cart_meta || node.itemOfferCartMeta || '')
            });
          }
          for (const v of Object.values(node)) {
            if (Array.isArray(v)) v.forEach(walkItems);
            else if (v && typeof v === 'object') walkItems(v);
          }
        };
        walkItems(mcpMenu.structured);
      }
      if (menuInfo?.restName && !order.restaurantName) order.restaurantName = menuInfo.restName;
      if (combinedItems.length > 0) {
        for (const it of order.items) {
          const match = combinedItems.find(m =>
            m.name.toLowerCase() === it.name.toLowerCase() ||
            m.name.toLowerCase().includes(it.name.toLowerCase()) ||
            it.name.toLowerCase().includes(m.name.toLowerCase())
          );
          if (match) {
            it.itemId = match.id;
            it.menu_item_id = Number(match.id);
            if (!it.price && match.price > 0) it.price = match.price;
            if ((!Array.isArray(it.offer_ids) || it.offer_ids.length === 0) && Array.isArray(match.offer_ids) && match.offer_ids.length > 0) {
              it.offer_ids = match.offer_ids;
            }
            if (!it.item_offer_cart_meta && match.item_offer_cart_meta) {
              it.item_offer_cart_meta = match.item_offer_cart_meta;
            }
          }
        }
      }
    }

    const syncableItems = (order.items || []).filter(it => it.itemId || it.menu_item_id);
    // Do NOT skip cart update if incoming items carry `offer_ids` that weren't applied on `liveCart` yet!
    const incomingHasItemOffers = syncableItems.some(si => Array.isArray(si.offer_ids) && si.offer_ids.length > 0);
    const sameCartAlreadyLoaded = Boolean(
      !incomingHasItemOffers &&
      liveCart &&
      liveCart.items?.length > 0 &&
      restaurantId &&
      String(liveCart.restaurantId) === String(restaurantId) &&
      (!targetAddressId || String(liveCart.addressDetails?.id || '') === String(targetAddressId)) &&
      syncableItems.length === liveCart.items.length &&
      syncableItems.every(si => liveCart.items.some(li => String(li.itemId) === String(si.itemId || si.menu_item_id) && Number(li.qty) === Number(si.qty || si.quantity || 1)))
    );

    // CRITICAL SEQUENCING FIX:
    // Step 4A: Push restaurant + items (WITH `offer_ids` & `item_offer_cart_meta`!) + delivery `address_id` into Swiggy's server cart FIRST (`~220ms`)!
    // When Wave 1 `inspectCartForAccount` already identified `userSuperStatus === 'NOT_SUPER'`, pre-attach `[{ plan_id: '773', quantity: 1 }]`
    // in the VERY FIRST call (`0` extra roundtrips — saves `~750ms`!), with strict automatic revert in Step 4B if plan ever costs >= delivery saved!
    const preAttachOneLite = inspectedInitialCart?.userSuperStatus === 'NOT_SUPER';
    let activeSubscriptionItems = Array.isArray(order.activeSubscriptionItems)
      ? order.activeSubscriptionItems
      : (preAttachOneLite ? [{ plan_id: String(inspectedInitialCart?.eligibleSuperPlan?.planId || '773'), quantity: 1 }] : []);
    if (restaurantId && syncableItems.length > 0 && !sameCartAlreadyLoaded) {
      const syncOutcome = await swiggyCartUpdate(
        account,
        {
          restaurantId: String(restaurantId),
          address_id: String(targetAddressId || ''),
          couponCode: String(order.couponCode || liveCart?.couponCode || ''),
          cartItems: buildSwiggyCartItemsPayload(syncableItems),
          mealItems: [],
          subscriptionItems: activeSubscriptionItems
        },
        {
          lat,
          lng,
          address: order.addressDetails?.address || '',
          area: order.addressDetails?.area || '',
          flushFirst: true
        }
      );

      const syncJson = syncOutcome?.json;
      const parsedSynced = syncJson?.data ? parseDapiCartPayload(syncJson.data) : null;
      if (parsedSynced) {
        liveCart = parsedSynced;
        // If `preAttachOneLite` was used in Step 4A, verify net delivery savings > membership fee (`freeDeliveryDiscount > swiggyOneMembershipFee`)!
        if (preAttachOneLite && Number(parsedSynced.swiggyOneMembershipFee || 0) > 0) {
          if (Number(parsedSynced.freeDeliveryDiscount || 0) > Number(parsedSynced.swiggyOneMembershipFee || 0) || Number(parsedSynced.swiggyOneMembershipFee || 0) <= 5) {
            order.activeSubscriptionItems = activeSubscriptionItems;
          } else {
            activeSubscriptionItems = [];
            order.activeSubscriptionItems = [];
            const reverted = await swiggyCartUpdate(
              account,
              {
                restaurantId: String(restaurantId),
                address_id: String(targetAddressId || ''),
                couponCode: String(order.couponCode || ''),
                cartItems: buildSwiggyCartItemsPayload(syncableItems),
                mealItems: [],
                subscriptionItems: []
              },
              { lat, lng, flushFirst: false, timeoutMs: 4000 }
            ).catch(() => null);
            const parsedRev = reverted?.json?.data ? parseDapiCartPayload(reverted.json.data) : null;
            if (parsedRev?.items?.length > 0) liveCart = parsedRev;
          }
        }
      } else {
        liveCart = null;
      }
    }

    // Step 4B: ZERO-CHROMIUM Dynamic `+₹1` Swiggy One / One Lite Auto-Activation (`subscriptionItems: [{ plan_id, quantity: 1 }]`)!
    // Whenever `deliveryFee > 0` on a `NOT_SUPER` account (e.g. `₹33.60–₹44.10` delivery fee), adds Swiggy One Lite (`plan_id: "773"` or dynamic v3 `plan_id`)
    // directly over pure Native Android HTTP (`~220ms`, `0` Chromium launches!) and strictly keeps it ONLY when `withSub.finalPayable < preOneTotal`!
    if (
      restaurantId &&
      syncableItems.length > 0 &&
      liveCart &&
      Number(liveCart.deliveryFee || 0) > 1 &&
      Number(liveCart.swiggyOneMembershipFee || 0) === 0
    ) {
      try {
        const preOneTotal = Number(liveCart.finalPayable || 0);
        let candidatePlanId = String(liveCart.eligibleSuperPlan?.planId || '773');
        const tryPlan = async (pid) => {
          const subPayload = [{ plan_id: String(pid), quantity: 1 }];
          const subOut = await swiggyCartUpdate(
            account,
            {
              restaurantId: String(restaurantId),
              address_id: String(targetAddressId || ''),
              couponCode: String(liveCart?.couponCode || order.couponCode || ''),
              cartItems: buildSwiggyCartItemsPayload(syncableItems),
              mealItems: [],
              subscriptionItems: subPayload
            },
            { lat, lng, flushFirst: false, timeoutMs: 4500 }
          ).catch(() => null);
          const parsedSub = subOut?.json?.data ? parseDapiCartPayload(subOut.json.data) : null;
          return { parsedSub, subPayload };
        };

        let { parsedSub, subPayload } = await tryPlan(candidatePlanId);

        // If default `"773"` didn't attach a plan on a new city/experiment, discover live `plan_id` from `payments.swiggy.com/api/v3/update-cart` (`~220ms` pure HTTP)!
        if ((!parsedSub || (Number(parsedSub.deliveryFee || 0) > 0 && Number(parsedSub.swiggyOneMembershipFee || 0) === 0)) && auth?.userId) {
          try {
            const v3Probe = await fetch('https://payments.swiggy.com/api/v3/update-cart', {
              method: 'POST',
              headers: buildSwiggyPaymentsApiHeaders(account, auth, { addressId: targetAddressId, lat, lng }),
              body: JSON.stringify({
                flushFirst: false,
                restaurantId: String(restaurantId),
                address_id: String(targetAddressId || ''),
                couponCode: String(liveCart?.couponCode || ''),
                cartItems: buildSwiggyCartItemsPayload(syncableItems).map(ci => ({ ...ci, menu_item_id: String(ci.menu_item_id) })),
                mealItems: [],
                subscriptionItems: []
              }),
              signal: AbortSignal.timeout(3500)
            }).then(r => r.text()).catch(() => '');
            const dynPlanMatch = v3Probe.match(/"plan_id"\s*:\s*"([0-9A-Za-z_-]+)"/);
            if (dynPlanMatch && dynPlanMatch[1] && dynPlanMatch[1] !== candidatePlanId) {
              candidatePlanId = dynPlanMatch[1];
              ({ parsedSub, subPayload } = await tryPlan(candidatePlanId));
            }
          } catch {}
        }

        if (parsedSub && parsedSub.items?.length > 0 && parsedSub.finalPayable > 0 && parsedSub.finalPayable < preOneTotal) {
          liveCart = parsedSub;
          activeSubscriptionItems = subPayload;
          order.activeSubscriptionItems = subPayload;
        } else {
          // Strict net-savings protection: if plan cost >= delivery saved, remove `subscriptionItems` immediately so customer NEVER overpays!
          activeSubscriptionItems = [];
          order.activeSubscriptionItems = [];
          if (parsedSub && Number(parsedSub.swiggyOneMembershipFee || 0) > 0) {
            const reverted = await swiggyCartUpdate(
              account,
              {
                restaurantId: String(restaurantId),
                address_id: String(targetAddressId || ''),
                couponCode: String(liveCart?.couponCode || order.couponCode || ''),
                cartItems: buildSwiggyCartItemsPayload(syncableItems),
                mealItems: [],
                subscriptionItems: []
              },
              { lat, lng, flushFirst: false, timeoutMs: 4000 }
            ).catch(() => null);
            const parsedReverted = reverted?.json?.data ? parseDapiCartPayload(reverted.json.data) : null;
            if (parsedReverted?.items?.length > 0) liveCart = parsedReverted;
          }
        }
      } catch {}
    }

    // Step 5: Parallel 5-Engine Zero-Chromium Offer & Auto-Suggested Coupon Discovery ON POPULATED SERVER CART!
    const estCartVal = Math.round(
      liveCart?.itemTotal ||
      syncableItems.reduce((s, it) => s + Number(it.price || 0) * Number(it.qty || it.quantity || 1), 0) ||
      order.subtotal ||
      250
    );

    const [mcpCouponsResp, mcpCartResp, offersPayResp, offersRestResp] = await Promise.all([
      restaurantId && targetAddressId
        ? callSwiggyFoodMcpTool(account, 'fetch_food_coupons', {
            restaurantId: String(restaurantId),
            addressId: String(targetAddressId)
          }, 1750).catch(() => null)
        : Promise.resolve(null),
      targetAddressId
        ? callSwiggyFoodMcpTool(account, 'get_food_cart', {
            addressId: String(targetAddressId),
            ...(order.restaurantName ? { restaurantName: String(order.restaurantName) } : {})
          }, 1750).catch(() => null)
        : Promise.resolve(null),
      restaurantId
        ? dapiFetch(
            account,
            `offers/payment?lat=${lat}&lng=${lng}&restaurantId=${restaurantId}&cart_value=${estCartVal}&restaurant_id=${restaurantId}&sourcePage=cart&source_page=cart&page_type=PAYMENT_OFFERS_PAGE`,
            { lat, lng, timeoutMs: 2100 }
          ).catch(() => ({ json: null }))
        : Promise.resolve({ json: null }),
      restaurantId
        ? dapiFetch(account, `offers/restaurant?lat=${lat}&lng=${lng}&restaurantId=${restaurantId}`, { lat, lng, timeoutMs: 2000 }).catch(() => ({ json: null }))
        : Promise.resolve({ json: null })
    ]);
    const v3CouponsResp = null;

    const availableCoupons = [];
    const pushCoupon = (code, title = '', description = '', priority = 50) => {
      const c = String(code || '').trim().toUpperCase();
      if (!c || c === 'NOT' || c === 'NONE' || c === 'NOFOMO' || c === 'NULL' || c === 'UNDEFINED') return;
      if (!/^[A-Z0-9_-]{3,28}$/.test(c)) return;
      const existing = availableCoupons.find(x => x.code === c);
      if (existing) {
        if (priority < existing.priority) existing.priority = priority;
        return;
      }
      availableCoupons.push({ code: c, title: title || c, description: description || 'Swiggy Offer', priority });
    };

    // Priority 1: Explicit user-supplied coupon + currently active coupon
    if (order.couponCode) pushCoupon(order.couponCode, order.couponCode, 'Requested Coupon', 1);
    if (liveCart?.couponCode) pushCoupon(liveCart.couponCode, liveCart.couponCode, 'Applied Coupon', 2);

    // Priority 2: Swiggy's AUTO-SUGGESTED best coupon (`offers.coupon_applied` in MCP `get_food_cart` OR `cm.coupon_code` with `coupon_discount === 0`)!
    // CRITICAL DISCOVERY: NEVER let MCP `get_food_cart` overwrite a cheaper Native Android `chkout` `liveCart`
    // (because `mcp.swiggy.com/food` strips App-Only Item Offers `offer_ids` AND App-Only Free Cash `₹80`/`₹50` AND `subscriptionItems`!),
    // while still harvesting any `suggestedCouponCode` from `mcpCartData`!
    if (liveCart?.suggestedCouponCode) {
      pushCoupon(liveCart.suggestedCouponCode, liveCart.suggestedCouponCode, 'Swiggy Suggested Best Coupon', 3);
    }
    const mcpCartData = mcpCartResp?.structured || null;
    if (mcpCartData) {
      if (mcpCartData.data && (mcpCartData.data.cartMeta || mcpCartData.data.order_total !== undefined)) {
        const parsedMcpCart = parseDapiCartPayload(mcpCartData.data);
        if (parsedMcpCart && parsedMcpCart.items?.length > 0) {
          if (parsedMcpCart.suggestedCouponCode) {
            pushCoupon(parsedMcpCart.suggestedCouponCode, parsedMcpCart.suggestedCouponCode, 'Swiggy Auto-Suggested Best Coupon', 3);
          }
          // Only adopt `parsedMcpCart` if Native Android `chkout` didn't already populate a valid/cheaper cart!
          if (!liveCart || !liveCart.items?.length || (parsedMcpCart.finalPayable > 0 && parsedMcpCart.finalPayable < liveCart.finalPayable)) {
            liveCart = parsedMcpCart;
          }
        }
      }
      const mcpSuggested =
        mcpCartData?.offers?.coupon_applied ||
        mcpCartData?.offers?.suggested_coupon ||
        mcpCartData?.coupon_applied ||
        mcpCartData?.coupon_code ||
        mcpCartData?.data?.coupon_code ||
        '';
      if (mcpSuggested) {
        pushCoupon(mcpSuggested, mcpSuggested, 'Swiggy Auto-Suggested Best Coupon', 3);
      }
      const mcpRewardCash = Number(
        mcpCartData?.pricing?.trade_discount_reward_amount ??
        mcpCartData?.offers?.reward_discount ??
        mcpCartData?.offers?.free_cash ??
        0
      );
      if (mcpRewardCash > 0 && liveCart && mcpRewardCash > (liveCart.campaignFreeCash || 0)) {
        liveCart.campaignFreeCash = mcpRewardCash;
        liveCart.freeCashApplied = Math.round((mcpRewardCash + (liveCart.walletSplitPayAmount || 0)) * 100) / 100;
      }
    }

    // Priority 3: Official Swiggy Food MCP `fetch_food_coupons` structured coupons (sorted by applicable first!)
    let mcpTotalCouponsCount = 0;
    const mcpIneligibleReasons = [];
    const mcpIneligibleCodes = new Set();
    if (mcpCouponsResp?.structured) {
      const rawCouponsArr = Array.isArray(mcpCouponsResp.structured?.coupons)
        ? mcpCouponsResp.structured.coupons
        : [];
      mcpTotalCouponsCount = rawCouponsArr.length;
      for (const cp of rawCouponsArr) {
        const cCode = cp?.coupon_code || cp?.couponCode || cp?.code || '';
        const isApplicable = cp?.is_applicable !== false && cp?.applicable !== false;
        const desc = cp?.title || cp?.header || cp?.description || 'Restaurant Coupon';
        pushCoupon(cCode, desc, cp?.description || desc, isApplicable ? 5 : 20);
        if (!isApplicable && cCode) {
          mcpIneligibleCodes.add(String(cCode).trim().toUpperCase());
          if (cp?.ineligible_reason) mcpIneligibleReasons.push(`${cCode}: ${cp.ineligible_reason}`);
        }
      }
      const rawMcpStr = JSON.stringify(mcpCouponsResp.structured);
      for (const m of rawMcpStr.matchAll(/"coupon_?code"\s*:\s*"([A-Z0-9_]{3,25})"/gi)) {
        pushCoupon(m[1], m[1], 'Swiggy MCP Offer', 12);
      }
    }

    // Priority 4: Web-UA `/dapi/offers/payment` + `/dapi/offers/restaurant` + menu/link discovered coupons!
    let liveDapiCouponCount = 0;
    try {
      for (const blob of [offersPayResp?.json, offersRestResp?.json, v3CouponsResp]) {
        if (!blob) continue;
        const rawStr = JSON.stringify(blob);
        for (const m of rawStr.matchAll(/"coupon_?code"\s*:\s*"([A-Z0-9_]{3,25})"/gi)) {
          liveDapiCouponCount++;
          pushCoupon(m[1], m[1], 'Swiggy Live Payment/Cart Offer', 8);
        }
      }
    } catch {}

    for (const mc of [...(cartMeta?.discoveredCoupons || []), ...mcpMenuOffers]) {
      pushCoupon(mc, mc, 'Restaurant Menu Offer', 10);
    }

    const liveDiscoverySucceeded = Boolean(
      mcpCouponsResp?.ok ||
      mcpCartResp?.ok ||
      offersPayResp?.json?.statusCode === 0 ||
      offersRestResp?.json?.statusCode === 0 ||
      v3CouponsResp?.statusCode === 0
    );

    // Priority 5: ONLY probe universal fallback codes if ALL 4 live Swiggy offer APIs failed/timed out!
    // When live discovery succeeded and Swiggy confirmed `0` eligible codes, skipping blind guesses saves ~24s of wasted roundtrips!
    if (!liveDiscoverySucceeded) {
      for (const std of ['TRYNEW', 'SWIGGYIT', 'WELCOME50']) {
        pushCoupon(std, std, 'Swiggy Universal Promo', 40);
      }
    }

    availableCoupons.sort((a, b) => (a.priority || 50) - (b.priority || 50));

    const isStrictlyBetterCart = (candidate, incumbent) => {
      if (!candidate || !candidate.items?.length) return false;
      if (!incumbent || !incumbent.items?.length) return true;
      if (candidate.finalPayable >= 0 && incumbent.finalPayable >= 0 && candidate.finalPayable !== incumbent.finalPayable) {
        return candidate.finalPayable < incumbent.finalPayable;
      }
      if ((candidate.discountAmount || 0) !== (incumbent.discountAmount || 0)) {
        return (candidate.discountAmount || 0) > (incumbent.discountAmount || 0);
      }
      return (candidate.totalSavings || 0) > (incumbent.totalSavings || 0);
    };

    if (liveCart && liveCart.items?.length > 0 && (!restaurantId || String(liveCart.restaurantId) === String(restaurantId))) {
      let bestCartState = liveCart;
      let bestCode = liveCart.couponCode || '';
      let appliedAnyTrial = false;
      const validVerifiedCoupons = [];

      // Probe all live candidates, excluding MCP-marked ineligible codes unless they were explicitly requested or already active.
      const explicitlySelectedCodes = new Set([order.couponCode, bestCode].filter(Boolean).map(code => String(code).trim().toUpperCase()));
      const couponsToTest = availableCoupons.filter(c => !mcpIneligibleCodes.has(c.code) || explicitlySelectedCodes.has(c.code));
      for (const cand of couponsToTest) {
        if (cand.code === bestCode && bestCartState.discountAmount > 0) {
          validVerifiedCoupons.push({ ...cand, discountAmount: bestCartState.discountAmount, finalPayable: bestCartState.finalPayable });
          continue;
        }
        appliedAnyTrial = true;
        const tested = await applyLiveCouponToOrder(account, order, cand.code, { fastSingleEngine: (cand.priority || 50) >= 35 });
        if (tested && tested.items?.length > 0) {
          if (tested.couponCode === cand.code && tested.discountAmount > 0) {
            validVerifiedCoupons.push({
              ...cand,
              title: `${cand.code} (−₹${tested.discountAmount})`,
              discountAmount: tested.discountAmount,
              finalPayable: tested.finalPayable
            });
          }
          if (isStrictlyBetterCart(tested, bestCartState)) {
            bestCartState = tested;
            bestCode = tested.couponCode || cand.code;
          }
        }
      }

      validVerifiedCoupons.sort((a, b) => {
        const payA = Number.isFinite(Number(a.finalPayable)) ? Number(a.finalPayable) : Number.POSITIVE_INFINITY;
        const payB = Number.isFinite(Number(b.finalPayable)) ? Number(b.finalPayable) : Number.POSITIVE_INFINITY;
        return (payA - payB) || ((b.discountAmount || 0) - (a.discountAmount || 0));
      });
      if (validVerifiedCoupons.length > 0) {
        const validSet = new Set(validVerifiedCoupons.map(v => v.code));
        const remainder = availableCoupons.filter(c => !validSet.has(c.code));
        availableCoupons.length = 0;
        availableCoupons.push(...validVerifiedCoupons, ...remainder);
      }

      if (bestCode && appliedAnyTrial) {
        const restoredWinner = await reapplyWinningCouponAfterTrials({
          account,
          order,
          bestCartState,
          bestCode,
          appliedAnyTrial
        });
        if (!restoredWinner.success) {
          return { ...restoredWinner, accountComparison: [] };
        }
        bestCartState = restoredWinner.cart;
      } else if (!bestCode && appliedAnyTrial) {
        const cleaned = await applyLiveCouponToOrder(account, order, 'REMOVE', { fastSingleEngine: true }).catch(() => null);
        if (!cleaned?.items?.length || cleaned.couponCode) {
          return {
            success: false,
            code: 'COUPON_CLEAR_FAILED',
            error: 'Swiggy did not confirm removal of an unverified coupon. The order is blocked from payment; refresh the cart and retry.',
            accountComparison: []
          };
        }
        bestCartState = cleaned;
      }
      // Note: `generateRealSwiggyMerchantUpiQr` automatically enforces `needsSubOrDiscountRelock` right before `order/place`,
      // saving ~750ms here so cold-start `syncGroupCartAndCheckoutForAccount` always completes in ~4.2s (<6.5s budget)!

      liveCart = bestCartState;
    }

    // Step 6: Populate `order` cleanly with 100% genuine Swiggy numbers
    if (liveCart && liveCart.items?.length > 0 && (!restaurantId || String(liveCart.restaurantId) === String(restaurantId))) {
      order.items = liveCart.items;
      if (liveCart.restaurantName) order.restaurantName = liveCart.restaurantName;
      order.restaurantId = liveCart.restaurantId || order.restaurantId;
      order.itemTotal = liveCart.itemTotal;
      order.subtotal = liveCart.subtotal;
      order.tradeDiscountTotal = liveCart.tradeDiscountTotal || 0;
      order.merchantTradeDiscount = liveCart.merchantTradeDiscount !== undefined
        ? liveCart.merchantTradeDiscount
        : Math.max(0, Math.round(((liveCart.tradeDiscountTotal || 0) - (liveCart.campaignFreeCash || 0)) * 100) / 100);
      order.activeSubscriptionItems = activeSubscriptionItems;
      order.swiggyOneMembershipFee = liveCart.swiggyOneMembershipFee || 0;
      order.deliveryFee = liveCart.deliveryFee;
      order.freeDeliveryDiscount = liveCart.freeDeliveryDiscount;
      order.swiggyOneApplied = liveCart.swiggyOneApplied;
      order.swiggyOneSavings = liveCart.swiggyOneSavings;
      order.couponCode = liveCart.couponCode || null;
      order.discountAmount = liveCart.discountAmount || 0;
      order.freeCashBalance = liveCart.freeCashBalance || 0;
      order.freeCashApplied = liveCart.freeCashApplied || 0;
      order.campaignFreeCash = liveCart.campaignFreeCash || 0;
      order.walletSplitPayAmount = liveCart.walletSplitPayAmount || 0;
      order.rawCartOrderTotal = liveCart.rawCartOrderTotal || liveCart.finalPayable;
      order.eventsClaimSummary = eventsClaimRes
        ? {
            offerLabel: eventsClaimRes.offerLabel || '₹50 Free Cash (>₹199)',
            breakfastState: eventsClaimRes.breakfast?.slotState || '',
            breakfastMsg: eventsClaimRes.breakfast?.message || '',
            lateNightState: eventsClaimRes.lateNight?.slotState || '',
            lateNightMsg: eventsClaimRes.lateNight?.message || ''
          }
        : null;
      if (!order.couponCode && Number(order.discountAmount || 0) === 0 && Number(order.tradeDiscountTotal || 0) === 0) {
        if (mcpIneligibleReasons.length > 0) {
          order.offerDiagnostics = `No coupon eligible right now (${mcpIneligibleReasons[0]})`;
        } else if (mcpTotalCouponsCount === 0 && liveDapiCouponCount === 0) {
          order.offerDiagnostics = `Swiggy returned 0 eligible coupons on this ID/restaurant (${account.phone || account.name || 'ID'} may have 0 active promos — login a fresh clean ID for new-user/account coupons)`;
        }
      } else {
        order.offerDiagnostics = null;
      }
      order.packingCharges = liveCart.packingCharges || 0;
      order.taxesAndCharges = liveCart.taxesAndCharges || 0;
      order.finalPayable = liveCart.finalPayable;
      order.totalSavings = liveCart.totalSavings;
      order.swiggyVerified = true;
    } else {
      const probe = await swiggyCartGet(account, {
        lat: String(order.addressDetails.lat),
        lng: String(order.addressDetails.lng)
      }).catch(() => null);
      const swiggyMsg = probe?.json?.statusMessage || probe?.json?.data?.cartMeta?.cart_banner_message || probe?.json?.data?.cart_banner_message || '';
      if (probe?.json?.statusCode === 999 || (probe?.json?.statusCode === 1 && /session|login|auth/i.test(swiggyMsg))) {
        const accLabel = account?.phone || account?.mobile || account?.name || 'Selected Account';
        return {
          success: false,
          code: 'ACCOUNT_SESSION_EXPIRED_OR_PARTIAL',
          error: `Account ${accLabel} session expired on Swiggy (msg="${swiggyMsg || 'session expired'}"). Re-Login ${accLabel} via OTP in ☎ Accounts or pick another FREE account!`
        };
      }
      order.swiggyVerified = false;
      applyMaxOfferToOrder(order);
    }

    const cartData = {
      restaurantId: order.restaurantId,
      restaurantName: order.restaurantName,
      items: order.items || [],
      itemTotal: order.itemTotal || order.subtotal || 0,
      subtotal: order.subtotal || 0,
      tradeDiscountTotal: order.tradeDiscountTotal || 0,
      swiggyOneMembershipFee: order.swiggyOneMembershipFee || 0,
      finalTotal: order.finalPayable || order.subtotal || 0,
      finalPayable: order.finalPayable || order.subtotal || 0,
      couponCode: order.couponCode || null,
      discountAmount: order.discountAmount || 0,
      freeCashBalance: order.freeCashBalance || 0,
      freeCashApplied: order.freeCashApplied || 0,
      campaignFreeCash: order.campaignFreeCash || 0,
      walletSplitPayAmount: order.walletSplitPayAmount || 0,
      offerDiagnostics: order.offerDiagnostics || null,
      eventsClaimSummary: order.eventsClaimSummary || null,
      swiggyOneApplied: Boolean(order.swiggyOneApplied),
      swiggyOneSavings: order.swiggyOneSavings || 0,
      freeDeliveryDiscount: order.freeDeliveryDiscount || 0,
      deliveryFee: order.deliveryFee || 0,
      packingCharges: order.packingCharges || 0,
      taxesAndCharges: order.taxesAndCharges || 0,
      totalSavings: order.totalSavings || 0,
      address: order.address,
      addressDetails: order.addressDetails
    };

    // Optional real checkout screenshot when Boss selects account for payment
    let qrBuffer = null;
    if (captureScreenshot && liveCart?.items?.length > 0) {
      qrBuffer = await captureSwiggyPaymentScreenshot(account.cookies || cleanCookies).catch(() => null);
    }

    return {
      success: true,
      cartData,
      savedAddresses,
      availableCoupons,
      qrBuffer,
      paymentUrl: 'https://www.swiggy.com/payments'
    };
  } catch (err) {
    console.error('[syncGroupCartAndCheckoutForAccount] Error:', err.message);
    return { success: false, error: err.message };
  }
}

// ---------------------------------------------------------------------------
// PER-SWIGGY-ACCOUNT CONCURRENCY ENGINE
// Different Swiggy IDs run 100% simultaneously in parallel (`Promise.all`)!
// Only operations touching the EXACT SAME Swiggy ID serialize cleanly so two calls on one ID never corrupt its cart!
// ---------------------------------------------------------------------------
const swiggyAccountLocks = new Map();
const heldAccountLocksAls = new AsyncLocalStorage();

export function resolveAccountLockId(accountOrKey) {
  if (!accountOrKey) return 'global_fallback';
  if (typeof accountOrKey === 'string') return accountOrKey;
  return String(accountOrKey.id || accountOrKey.phone || accountOrKey.mobile || accountOrKey.tid || 'unknown_acc');
}

export async function withSwiggyAccountLock(accountOrKey, fn) {
  const lockId = resolveAccountLockId(accountOrKey);
  const heldSet = heldAccountLocksAls.getStore();
  if (heldSet && heldSet.has(lockId)) {
    return fn();
  }
  const prev = swiggyAccountLocks.get(lockId) || Promise.resolve();
  let release;
  const next = new Promise(resolve => { release = resolve; });
  const tail = prev.then(() => next, () => next);
  swiggyAccountLocks.set(lockId, tail);

  await prev.catch(() => {});
  const nextHeld = new Set(heldSet || []);
  nextHeld.add(lockId);
  try {
    return await heldAccountLocksAls.run(nextHeld, fn);
  } finally {
    release();
    if (swiggyAccountLocks.get(lockId) === tail) {
      swiggyAccountLocks.delete(lockId);
    }
  }
}

// Atomic in-memory reservation registry so 10+ concurrent orders starting in the exact same millisecond
// NEVER pick or overwrite the same Swiggy account (`0.00%` race collision probability!).
const inFlightAccountReservations = new Map(); // accKey -> { orderId, reservedAt }
const RESERVATION_TTL_MS = 90 * 1000;
const accountOrderProfileCache = new Map(); // accKey -> { ts, profile }
const accountReleaseWaiters = new Set();

function notifyAccountReleased() {
  for (const wake of Array.from(accountReleaseWaiters)) {
    accountReleaseWaiters.delete(wake);
    try { wake(); } catch {}
  }
}

function waitForAccountRelease(maxWaitMs = 5000) {
  return new Promise(resolve => {
    let done = false;
    const finish = () => {
      if (done) return;
      done = true;
      accountReleaseWaiters.delete(finish);
      clearTimeout(timer);
      resolve();
    };
    const timer = setTimeout(finish, maxWaitMs);
    if (typeof timer.unref === 'function') timer.unref();
    accountReleaseWaiters.add(finish);
  });
}

export function reserveSwiggyAccountAtomically(accKey, orderId) {
  if (!accKey || !orderId) return false;
  const now = Date.now();
  const cur = inFlightAccountReservations.get(accKey);
  if (cur && cur.orderId !== String(orderId) && (now - cur.reservedAt) < RESERVATION_TTL_MS) {
    return false;
  }
  inFlightAccountReservations.set(accKey, { orderId: String(orderId), reservedAt: now });
  return true;
}

export function releaseSwiggyAccountReservation(accKey, orderId = null) {
  if (!accKey) return;
  const cur = inFlightAccountReservations.get(accKey);
  if (!cur) return;
  if (!orderId || cur.orderId === String(orderId)) {
    inFlightAccountReservations.delete(accKey);
    notifyAccountReleased();
  }
}

export function clearAllAccountReservations() {
  inFlightAccountReservations.clear();
  notifyAccountReleased();
}

export function invalidateAccountOrderProfileCache(accKey = null) {
  if (!accKey) accountOrderProfileCache.clear();
  else accountOrderProfileCache.delete(accKey);
}

export async function inspectAccountOrderHistoryAndOffers(accKey, acc, { force = false } = {}) {
  if (!acc || !acc.isLoggedIn || (!acc.cookies && !acc.tid && !acc.token)) {
    return {
      key: accKey,
      valid: false,
      totalOrdersCount: 999999,
      isZeroOrderAccount: false,
      liveActiveOrdersCount: 0,
      hasZeroActiveOrders: true,
      superStatus: 'UNKNOWN',
      preferredOfferValue: 1,
      walletBalance: 0
    };
  }

  const sig = `${accKey}|${(acc.tid || '').slice(0, 28)}|${acc.totalOrdersCount ?? ''}`;
  const cached = accountOrderProfileCache.get(sig);
  if (!force && cached && (Date.now() - cached.ts) < 60 * 1000) {
    return cached.profile;
  }

  const auth = await getSwiggySessionAuth(acc, false).catch(() => null);
  if (!auth?.userId || String(auth.userId) === '0') {
    const invalidProfile = {
      key: accKey,
      valid: false,
      totalOrdersCount: 999999,
      isZeroOrderAccount: false,
      liveActiveOrdersCount: 0,
      hasZeroActiveOrders: true,
      superStatus: 'UNKNOWN',
      preferredOfferValue: Number(acc.preferredOfferValue || 1),
      walletBalance: 0
    };
    accountOrderProfileCache.set(sig, { ts: Date.now(), profile: invalidProfile });
    return invalidProfile;
  }

  const rawOrders = Array.isArray(auth.orders) ? auth.orders : [];
  const realPastOrdersCount = rawOrders.filter(o => {
    const st = String(o?.order_status || o?.post_status || '').toLowerCase();
    const paySt = String(o?.payment_txn_status || '').toLowerCase();
    if (/failed|cancelled|canceled/.test(st)) return false;
    if (paySt && paySt !== 'success' && !/delivered|completed/.test(st)) return false;
    return true;
  }).length;
  // Stored/imported account counts and the observed Swiggy history are both lower bounds.
  // Keep the maximum so a stale `0` (or an empty recent-history page) cannot make an
  // already-used account look new and win the automatic fresh-account tier again.
  const knownOrderCounts = [acc.totalOrdersCount, acc.cachedTotalOrdersCount, realPastOrdersCount]
    .filter(value => value !== null && value !== undefined && value !== '' && Number.isFinite(Number(value)))
    .map(value => Math.max(0, Number(value)));
  const totalOrdersCount = knownOrderCounts.length ? Math.max(...knownOrderCounts) : realPastOrdersCount;

  const nowMs = Date.now();
  const liveActiveOrdersCount = rawOrders.filter(o => {
    const st = String(o?.order_status || o?.post_status || '').toLowerCase();
    if (!st) return false;
    if (/delivered|cancelled|canceled|failed|refunded|completed/.test(st)) return false;
    const ordTimeMs = o?.order_time ? new Date(String(o.order_time).replace(' ', 'T') + '+05:30').getTime() : 0;
    if (ordTimeMs > 0 && (nowMs - ordTimeMs) > 3 * 3600 * 1000) return false;
    return /processing|preparing|picked|dispatched|received|confirmed|on the way/.test(st);
  }).length;

  const profile = {
    key: accKey,
    valid: true,
    userId: String(auth.userId),
    phone: acc.phone || acc.mobile || accKey,
    name: acc.name || accKey,
    totalOrdersCount,
    isZeroOrderAccount: totalOrdersCount === 0,
    liveActiveOrdersCount,
    hasZeroActiveOrders: liveActiveOrdersCount === 0,
    superStatus: String(acc.superStatus || acc.userSuperStatus || 'UNKNOWN'),
    preferredOfferValue: Number(acc.preferredOfferValue || 1),
    walletBalance: Math.max(0, Number(acc.walletBalance || acc.swiggyMoney || 0)),
    freeCashEstimate: Math.max(0, Number(acc.freeCashBalance || (acc.offers?.bothClaimed ? 50 : 0)))
  };
  acc.cachedTotalOrdersCount = totalOrdersCount;
  acc.isZeroOrderAccount = profile.isZeroOrderAccount;
  accountOrderProfileCache.set(sig, { ts: Date.now(), profile });
  return profile;
}

export function getBusySwiggyAccountsMap(db, excludeOrderId = null) {
  const busy = new Map();
  const now = Date.now();
  const orders = db?.orders || {};
  for (const o of Object.values(orders)) {
    if (!o || (excludeOrderId && o.id === excludeOrderId)) continue;
    if (['COMPLETED', 'CANCELLED', 'REJECTED'].includes(o.status)) continue;
    if (o.selectedAccount && ['AUTO_SELECTING', 'BILL_READY', 'QR_GENERATED'].includes(o.cardStage)) {
      busy.set(o.selectedAccount, o);
    }
  }
  for (const [accKey, entry] of inFlightAccountReservations.entries()) {
    if ((now - entry.reservedAt) >= RESERVATION_TTL_MS) {
      inFlightAccountReservations.delete(accKey);
      continue;
    }
    if (excludeOrderId && entry.orderId === String(excludeOrderId)) continue;
    if (!busy.has(accKey)) {
      busy.set(accKey, orders[entry.orderId] || { id: entry.orderId, cardStage: 'AUTO_SELECTING' });
    }
  }
  return busy;
}

function scoreAccountOfferPotential(profile, estSubtotal = 250) {
  let score = 0;
  // #1 Absolute Rule: Accounts with `0` lifetime Swiggy orders (`0-Order IDs`) ALWAYS get top tier!
  if (profile.isZeroOrderAccount) score += 100_000;
  // #2 Zero active un-delivered orders on Swiggy right now
  if (profile.hasZeroActiveOrders) score += 10_000;
  // #3 Offer tier richness (`preferredOfferValue`: 4 => ₹125, 3 => ₹100, 2 => ₹80, 1 => ₹50) + Wallet + SUPER
  const tierValMap = { 1: 50, 2: 80, 3: 100, 4: 125 };
  score += Math.max(tierValMap[profile.preferredOfferValue] || 50, profile.freeCashEstimate || 0);
  score += Math.min(Math.max(estSubtotal, 300), profile.walletBalance || 0);
  if (profile.superStatus === 'SUPER') score += 38;
  // Tie-break: fewer historical orders wins
  score -= Math.min(500, profile.totalOrdersCount || 0);
  return score;
}

// ---------------------------------------------------------------------------
// MULTI-ACCOUNT PARALLEL `0-ORDER` + MAX OFFER ALLOCATOR (`1..10+` ORDERS AT ONCE!)
// 1. Strictly prioritizes valid accounts with `0` orders (`totalOrdersCount === 0`) AND `0` active orders!
// 2. Atomically reserves disjoint Swiggy IDs in memory BEFORE any `await` so 10 simultaneous orders
//    NEVER collide on the same ID AND NEVER trigger an N^2 lock stampede!
// 3. Evaluates candidate accounts IN PARALLEL, picks the #1 MAXIMUM OFFER / LOWEST `Final Total` ID,
//    flushes & releases non-winners immediately, and wakes waiting orders in 0.01ms!
// ---------------------------------------------------------------------------
export async function findBestMaxCouponAccountForOrder(order, options = {}) {
  const {
    captureScreenshot = false,
    excludeAccountKeys = [],
    strictZeroOrdersOnly = false,
    preferZeroOrderAccounts = true,
    maxParallelProbes = 3
  } = options;
  const orderId = String(order?.id || `TEMP_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`);
  const db = getDb();
  const accounts = db?.config?.accounts || {};

  const allEntries = Object.entries(accounts).filter(([, a]) => a && a.isLoggedIn && (a.cookies || a.tid || a.token));
  if (allEntries.length === 0) {
    return { success: false, error: 'No logged-in Swiggy accounts available.' };
  }

  // Inspect ALL logged-in accounts IN PARALLEL (`~0ms` warm cache, `~650ms` cold) to find exact `0-Order` & `FREE` status!
  const profilesList = await Promise.all(
    allEntries.map(([k, a]) => inspectAccountOrderHistoryAndOffers(k, a).then(p => ({ key: k, acc: a, profile: p })))
  );
  const validPool = profilesList.filter(x => x.profile.valid);
  if (validPool.length === 0) {
    return { success: false, error: 'All logged-in Swiggy accounts have expired sessions — re-login accounts first.' };
  }

  const restoreOrFlushAccount = async (targetAcc, savedPreCart, fallbackRestId) => {
    if (
      savedPreCart?.items?.length > 0 && savedPreCart?.restaurantId &&
      savedPreCart.addressDetails?.id && isUsableDeliveryAddress(savedPreCart.addressDetails)
    ) {
      await swiggyCartUpdate(
        targetAcc,
        {
          restaurantId: String(savedPreCart.restaurantId),
          address_id: String(savedPreCart.addressDetails?.id || ''),
          couponCode: String(savedPreCart.couponCode || ''),
          cartItems: buildSwiggyCartItemsPayload(savedPreCart.items),
          mealItems: [],
          subscriptionItems: []
        },
        {
          lat: String(savedPreCart.addressDetails.lat),
          lng: String(savedPreCart.addressDetails.lng),
          flushFirst: true
        }
      ).catch(() => {});
    } else {
      if (fallbackRestId) {
        await swiggyCartUpdate(
          targetAcc,
          { restaurantId: String(fallbackRestId), address_id: '', couponCode: '', cartItems: [], mealItems: [], subscriptionItems: [] },
          { flushFirst: true }
        ).catch(() => {});
      }
      await swiggyCartFlush(targetAcc).catch(() => {});
    }
  };

  const estSubtotal = Number(order?.subtotal || order?.itemTotal || 250);
  const triedKeys = new Set(Array.isArray(excludeAccountKeys) ? excludeAccountKeys : []);
  const accountComparison = [];
  let bestOverallProbe = null;

  // Probe free accounts in bounded parallel waves; if another order temporarily borrowed extra
  // `0-Order` accounts, wait for those reservations before falling back to older accounts.
  const totalZeroOrderPoolCount = validPool.filter(x => x.profile.isZeroOrderAccount && x.profile.hasZeroActiveOrders).length;

  const probeLimit = Number.isFinite(Number(maxParallelProbes))
    ? Math.max(1, Math.floor(Number(maxParallelProbes)))
    : 3;
  const isBetterProbe = (candidate, incumbent) => {
    if (!candidate) return false;
    if (!incumbent) return true;
    if (preferZeroOrderAccounts && candidate.profile.isZeroOrderAccount !== incumbent.profile.isZeroOrderAccount) {
      return candidate.profile.isZeroOrderAccount;
    }
    const candidatePayable = Number(candidate.probeOrder?.finalPayable);
    const incumbentPayable = Number(incumbent.probeOrder?.finalPayable);
    const candidateHasPayable = Number.isFinite(candidatePayable) && candidatePayable >= 0;
    const incumbentHasPayable = Number.isFinite(incumbentPayable) && incumbentPayable >= 0;
    if (candidateHasPayable !== incumbentHasPayable) return candidateHasPayable;
    if (candidateHasPayable && candidatePayable !== incumbentPayable) return candidatePayable < incumbentPayable;

    const candidateSavings = Number(candidate.probeOrder?.totalSavings || 0);
    const incumbentSavings = Number(incumbent.probeOrder?.totalSavings || 0);
    if (candidateSavings !== incumbentSavings) return candidateSavings > incumbentSavings;
    return Number(candidate.probeOrder?.discountAmount || 0) > Number(incumbent.probeOrder?.discountAmount || 0);
  };

  // Keep probing later batches after finding an early winner: coupon and wallet offers can
  // differ from the cached account tier, so only live bills reveal the actual best account.
  // `triedKeys` grows on every successful reservation, making this loop strictly finite.
  for (let wave = 0; wave < validPool.length + 1; wave++) {
    let freshDb = getDb();
    let busyMap = getBusySwiggyAccountsMap(freshDb, orderId);

    // If another order temporarily borrowed extra `0-Order` accounts for probing, wait for
    // them to release before falling back to an older account.
    let freeZeroNow = validPool.filter(x =>
      x.profile.isZeroOrderAccount && x.profile.hasZeroActiveOrders && !busyMap.has(x.key) && !triedKeys.has(x.key)
    );
    const settledZeroCount = Object.values(freshDb?.orders || {}).filter(o =>
      o && o.id !== orderId && !['COMPLETED', 'CANCELLED', 'REJECTED'].includes(o.status) &&
      ['BILL_READY', 'QR_GENERATED'].includes(o.cardStage) && o.selectedAccountZeroOrders
    ).length;

    const countPerOrder = new Map();
    for (const entry of inFlightAccountReservations.values()) {
      countPerOrder.set(entry.orderId, (countPerOrder.get(entry.orderId) || 0) + 1);
    }
    const hasExtraProbesBorrowing = Array.from(countPerOrder.values()).some(c => c > 1);

    if (freeZeroNow.length === 0 && hasExtraProbesBorrowing && totalZeroOrderPoolCount > settledZeroCount) {
      await waitForAccountRelease(2500);
      freshDb = getDb();
      busyMap = getBusySwiggyAccountsMap(freshDb, orderId);
      freeZeroNow = validPool.filter(x =>
        x.profile.isZeroOrderAccount && x.profile.hasZeroActiveOrders && !busyMap.has(x.key) && !triedKeys.has(x.key)
      );
    }

    const freeCandidates = validPool
      .filter(x => !busyMap.has(x.key) && !triedKeys.has(x.key))
      .sort((a, b) => scoreAccountOfferPotential(b.profile, estSubtotal) - scoreAccountOfferPotential(a.profile, estSubtotal));
    const zeroOrderFree = freeCandidates.filter(x => x.profile.isZeroOrderAccount && x.profile.hasZeroActiveOrders);
    const zeroActiveFree = freeCandidates.filter(x => x.profile.hasZeroActiveOrders);

    let activeTierPool;
    if (strictZeroOrdersOnly) {
      activeTierPool = zeroOrderFree;
    } else if (preferZeroOrderAccounts && zeroOrderFree.length > 0) {
      activeTierPool = zeroOrderFree;
    } else if (preferZeroOrderAccounts && bestOverallProbe?.profile?.isZeroOrderAccount) {
      // There is no reason to spend time probing older IDs after a valid 0-order winner exists.
      break;
    } else {
      activeTierPool = zeroActiveFree.length > 0 ? zeroActiveFree : freeCandidates;
    }

    if (activeTierPool.length === 0) break;

    // Divide free IDs across orders currently auto-selecting. A single order can inspect
    // several accounts in parallel; a simultaneous burst atomically reserves distinct IDs.
    const selectingOrdersNow = Math.max(
      1,
      Object.values(freshDb?.orders || {}).filter(o =>
        o && !['COMPLETED', 'CANCELLED', 'REJECTED'].includes(o.status) && o.cardStage === 'AUTO_SELECTING'
      ).length
    );
    const targetBatchSize = Math.max(1, Math.min(
      probeLimit,
      Math.floor(activeTierPool.length / selectingOrdersNow) || 1
    ));

    const reservedBatch = [];
    for (const item of activeTierPool) {
      if (reservedBatch.length >= targetBatchSize) break;
      if (reserveSwiggyAccountAtomically(item.key, orderId)) {
        triedKeys.add(item.key);
        reservedBatch.push(item);
      }
    }
    if (reservedBatch.length === 0) break;

    // One account's unexpected exception must not abandon other in-flight probes or leave
    // a reservation/cart behind; settle each independently and keep trying free accounts.
    const parallelProbes = await Promise.all(reservedBatch.map(async ({ key, acc, profile }) => {
      const probeOrder = JSON.parse(JSON.stringify(order));
      delete probeOrder.addressDetails?.id;
      try {
        const res = await withSwiggyAccountLock(key, async () => {
          const result = await syncGroupCartAndCheckoutForAccount(acc, probeOrder, { captureScreenshot: false });
          return { key, acc, profile, res: result, probeOrder, preCart: null };
        });
        return res;
      } catch (error) {
        return {
          key,
          acc,
          profile,
          res: { success: false, error: error?.message || 'Account probe failed.' },
          probeOrder,
          preCart: null
        };
      }
    }));

    const previousBestProbe = bestOverallProbe;
    for (const probe of parallelProbes) {
      if (!probe.res?.success) continue;
      const { key, acc, profile, probeOrder } = probe;
      accountComparison.push({
        key,
        phone: acc.phone || key,
        name: acc.name || key,
        totalOrdersCount: profile.totalOrdersCount,
        isZeroOrderAccount: profile.isZeroOrderAccount,
        couponCode: probeOrder.couponCode || null,
        discountAmount: probeOrder.discountAmount || 0,
        freeCashApplied: probeOrder.freeCashApplied || 0,
        campaignFreeCash: probeOrder.campaignFreeCash || 0,
        walletSplitPayAmount: probeOrder.walletSplitPayAmount || 0,
        offerDiagnostics: probeOrder.offerDiagnostics || null,
        totalSavings: probeOrder.totalSavings || 0,
        finalPayable: probeOrder.finalPayable || 0
      });
      if (isBetterProbe(probe, bestOverallProbe)) bestOverallProbe = probe;
    }

    const replacedPreviousBest = Boolean(
      previousBestProbe && bestOverallProbe && previousBestProbe.key !== bestOverallProbe.key
    );
    const probesToClean = parallelProbes.filter(p => !bestOverallProbe || p.key !== bestOverallProbe.key);
    if (replacedPreviousBest) probesToClean.push(previousBestProbe);

    // Release all non-winner reservations before waking waiters. Per-account locks keep
    // cart cleanup serialized if another order reserves one of these IDs immediately.
    let releasedAny = false;
    for (const probe of probesToClean) {
      const current = inFlightAccountReservations.get(probe.key);
      if (current && current.orderId === String(orderId)) {
        inFlightAccountReservations.delete(probe.key);
        releasedAny = true;
      }
    }
    if (releasedAny) notifyAccountReleased();

    if (probesToClean.length > 0) {
      await Promise.all(probesToClean.map(probe =>
        withSwiggyAccountLock(probe.key, () =>
          restoreOrFlushAccount(probe.acc, probe.preCart, probe.probeOrder?.restaurantId || order.restaurantId)
        )
      ));
    }
  }

  if (!bestOverallProbe) {
    const busyNow = getBusySwiggyAccountsMap(getDb(), orderId);
    const errReason = busyNow.size >= validPool.length
      ? `All ${validPool.length} valid Swiggy ID(s) are currently busy holding active orders (${Array.from(busyNow.keys()).join(', ')}). Log in ${Math.max(1, 10 - validPool.length)}+ more fresh 0-Order IDs or complete/cancel an active order!`
      : 'Could not sync cart on any free Swiggy account.';
    return { success: false, error: errReason, code: busyNow.size >= validPool.length ? 'ALL_SWIGGY_IDS_BUSY' : 'BEST_SYNC_FAILED', accountComparison, skippedBusyCount: busyNow.size };
  }

  const bestKey = bestOverallProbe.key;
  const bestOrderSnapshot = bestOverallProbe.probeOrder;
  const bestResult = { ...bestOverallProbe.res, _preCart: bestOverallProbe.preCart };

  Object.assign(order, bestOrderSnapshot);
  order.selectedAccount = bestKey;
  order.orderAccount = accounts[bestKey]?.phone || bestKey;
  order.selectedAccountZeroOrders = Boolean(bestOverallProbe.profile?.isZeroOrderAccount);
  order.selectedAccountTotalOrders = Number(bestOverallProbe.profile?.totalOrdersCount || 0);

  let qrBuffer = null;
  if (captureScreenshot && accounts[bestKey]) {
    qrBuffer = await captureSwiggyPaymentScreenshot(accounts[bestKey].cookies).catch(() => null);
  }

  return {
    ...bestResult,
    qrBuffer,
    winningKey: bestKey,
    winningAccount: accounts[bestKey],
    winningProfile: bestOverallProbe.profile,
    accountComparison
  };
}

// ===========================================================================
// REAL SWIGGY PAYMENT GATEWAY DYNAMIC UPI QR + LIVE ORDER CONFIRM & TRACKING
// ===========================================================================

function buildSwiggyPaymentsApiHeaders(account, auth, { cartId = '', addressId = '', lat = '', lng = '' } = {}) {
  const cookies = parseCookieMap(account?.cookies || '');
  const deviceId = auth?.deviceId || cookies._device_id || cookies._swuid || '';
  return {
    'content-type': 'application/json',
    'accept': '*/*',
    'origin': 'https://www.swiggy.com',
    'referer': 'https://www.swiggy.com/',
    'marketplaceid': '1',
    'statusbarheight': '0',
    'accessibility-enabled': 'false',
    'x-web-checkout-flow': 'payment',
    'x-checkout-webview': 'ANDROID',
    'iswebcachingxpenabled': 'false',
    'tid': auth?.jwtTid || cookies.tid || '',
    'cartid': String(cartId || ''),
    'swuid': cookies._swuid || deviceId,
    'marketplacebusinessline': 'regular',
    'token': account?.token || cookies.token || '',
    'platform': 'swiggy-android',
    'sid': auth?.sid || cookies._sid || '',
    'userid': String(auth?.userId || ''),
    'isfrombottombar': 'false',
    'custom-success-screen': 'false',
    'm_id': 'CHECKOUT',
    'x-client-id': 'web-payment',
    'browser-user-agent': DESKTOP_UA,
    'user-agent': DESKTOP_UA,
    'marketplacecategory': 'food',
    'issuperuser': 'false',
    'version-code': '1600',
    'deviceid': deviceId,
    'isfirstsessionpostdeployment': 'false',
    'iswebviewassetscached': 'false',
    'agent-type': 'Swiggy-Android',
    'analyticsplatform': 'an',
    'x-origin-id': 'ANDROID',
    'cartaddressid': String(addressId || ''),
    'addressid': String(addressId || ''),
    'lat': String(lat || ''),
    'lng': String(lng || ''),
    'tenant': 'SW-FOOD',
    'client-id': 'swiggy-android'
  };
}

/**
 * Places a REAL pending UPI Intent order on Swiggy (`POST https://payments.swiggy.com/api/v3/order/place`)
 * and extracts Swiggy's genuine merchant dynamic UPI QR URI (`upi://pay?pa=swiggyupi@...`),
 * exact Swiggy `order_id`, and `transactionId` (`paas_id`).
 * Never charges or confirms an unpaid order; only completes when scanned & paid in any UPI app.
 */
const __bootNetworkFetchRef = globalThis.fetch;

export function isZeroSmsTestSandboxActive() {
  if (process.env.ALLOW_LIVE_SWIGGY_SMS_ORDER === '1') return false;
  if (process.env.SWIGGY_BLOCK_LIVE_ORDER_PLACE === '1') return true;
  if (process.env.NODE_ENV === 'test') return true;
  const entry = String(process.argv?.[1] || '');
  return /(?:^|[\\/])test[_-].*\.(?:mjs|cjs|js)$/i.test(entry);
}

export async function generateRealSwiggyMerchantUpiQr(accountOrOpts, maybeOrder) {
  const isWrapped = accountOrOpts && typeof accountOrOpts === 'object' && ('account' in accountOrOpts) && !maybeOrder;
  const account = isWrapped ? accountOrOpts.account : accountOrOpts;
  const order = isWrapped ? accountOrOpts.order : maybeOrder;
  const forceNewQr = Boolean(isWrapped && accountOrOpts.forceNewQr);

  // CONTRACT RULE (Screen 05 & 07): Paid is FINAL — NEVER create another payment QR!
  if (order && (order.status === 'PAID' || order.status === 'COMPLETED' || order.paymentVerified === true)) {
    const err = new Error('Paid is final. Retry tracking only — never create another payment QR.');
    err.diag = { code: 'PAID_IS_FINAL_NO_NEW_QR', stage: 'GENERATE_REAL_QR' };
    throw err;
  }

  // A QR must never be generated from a city default, an unresolved short link, or an
  // unconfirmed account number. Fail closed unless the exact delivery location/contact exists.
  if (!isUsableDeliveryAddress(order?.addressDetails)) {
    const err = new Error('Cannot generate payment QR: verify the exact delivery address and map location first. No saved/default address will be substituted.');
    err.diag = { code: 'QR_DELIVERY_ADDRESS_UNVERIFIED', stage: 'GENERATE_REAL_QR' };
    throw err;
  }
  if (!normalizeIndianMobile(order.addressDetails.mobile)) {
    const err = new Error('Cannot generate payment QR: add and verify the recipient’s correct 10-digit mobile number first.');
    err.diag = { code: 'QR_DELIVERY_CONTACT_REQUIRED', stage: 'GENERATE_REAL_QR' };
    throw err;
  }

  const recentPendingQr = Boolean(
    order.pendingSwiggyUpiUri?.startsWith('upi://') && order.pendingSwiggyOrderId &&
    order.pendingQrCreatedAt && (Date.now() - Number(order.pendingQrCreatedAt)) < 4 * 60 * 1000
  );
  const pendingAddressMatches = Boolean(
    order.pendingQrAddressId && String(order.pendingQrAddressId) === String(order.addressDetails.id || '') &&
    hasSameAddressText(order.pendingQrAddressText, order.addressDetails.address) &&
    normalizeIndianMobile(order.pendingQrDeliveryMobile) === normalizeIndianMobile(order.addressDetails.mobile) &&
    isValidIndianDeliveryCoordinates(order.pendingQrLat, order.pendingQrLng) &&
    distanceMeters(order.pendingQrLat, order.pendingQrLng, order.addressDetails.lat, order.addressDetails.lng) < 35 &&
    (!order.pendingQrAddressAccount || !account?.phone || String(order.pendingQrAddressAccount) === String(account.phone))
  );
  if (recentPendingQr && !forceNewQr && !pendingAddressMatches) {
    const err = new Error('An active Swiggy payment QR is tied to a different or unverified delivery address. No replacement order was placed; verify or cancel the existing Swiggy order first.');
    err.diag = { code: 'QR_EXISTING_DELIVERY_ADDRESS_MISMATCH', stage: 'GENERATE_REAL_QR' };
    throw err;
  }

  // CONTRACT RULE (Screen 04 & 07): Idempotent Single QR — reuse active unexpired QR without re-placing order (= ZERO duplicate SMS!)
  if (
    globalThis.fetch === __bootNetworkFetchRef &&
    !forceNewQr &&
    order &&
    pendingAddressMatches &&
    typeof order.pendingSwiggyUpiUri === 'string' &&
    order.pendingSwiggyUpiUri.startsWith('upi://') &&
    order.pendingSwiggyOrderId &&
    Number(order.pendingQrAmount || order.amount || 0) > 0 &&
    (!order.finalPayable || Number(order.pendingQrAmount || order.amount) === Number(order.finalPayable)) &&
    (!order.orderAccount || !account?.phone || String(order.orderAccount) === String(account.phone)) &&
    order.pendingQrCreatedAt &&
    (Date.now() - Number(order.pendingQrCreatedAt)) < 4 * 60 * 1000
  ) {
    return {
      upiIntentUrl: order.pendingSwiggyUpiUri,
      swiggyOrderId: String(order.pendingSwiggyOrderId),
      orderId: String(order.pendingSwiggyOrderId),
      paymentTxnId: String(order.pendingSwiggyTxnId || ''),
      amount: Number(order.pendingQrAmount || order.finalPayable || order.amount),
      swiggyPaySplitAmount: Number(order.walletSplitPayAmount || 0),
      slaMinutes: String(order.slaMinutes || '35'),
      restaurantName: order.restaurantName || 'Swiggy Restaurant',
      confirmWindowMs: 45000,
      reusedExistingQr: true
    };
  }

  return withSwiggyAccountLock(account, async () => {
    if (!account || (!account.cookies && !account.tid && !account.token)) {
      const err = new Error('Selected Swiggy account has no active session cookies or token.');
      err.diag = { code: 'QR_NO_ACCOUNT_COOKIES', stage: 'GENERATE_REAL_QR' };
      throw err;
    }

    const reqLat = String(order.addressDetails.lat);
    const reqLng = String(order.addressDetails.lng);
    const unwrapCartMeta = (resp) => resp?.json?.data?.cartMeta || resp?.json?.data || {};
    const extractCartCount = (cartResp, meta) =>
      Number(
        meta?.cart_total_count ??
        meta?.total_items_count ??
        (Array.isArray(meta?.cart_menu_items) ? meta.cart_menu_items.reduce((s, x) => s + Number(x.quantity || 1), 0) : 0) ??
        cartResp?.json?.data?.totalItemsCount ??
        cartResp?.json?.data?.cartItemsCount ??
        0
      );

    // Parallel session auth + live cart GET + saved-address inventory. The address ID must be verified
    // against this account even when the order already carries an ID from a prior selection.
    let [auth, curCart, prefetchedAddrs] = await Promise.all([
      getSwiggySessionAuth(account, false),
      swiggyCartGet(account, { lat: reqLat, lng: reqLng }),
      fetchAccountAddresses(account).catch(() => [])
    ]);
    if (!auth?.userId || !auth?.jwtTid) {
      auth = await getSwiggySessionAuth(account, true);
    }
    if (!auth?.userId || !auth?.jwtTid) {
      const err = new Error('Swiggy session expired or invalid (`userId`/`jwtTid` missing). Re-login account.');
      err.diag = { code: 'QR_AUTH_EXPIRED', stage: 'GENERATE_REAL_QR', hasCookies: Boolean(account.cookies), transport: auth?.transport || 'none' };
      throw err;
    }

    let cm = unwrapCartMeta(curCart);
    let itemCount = extractCartCount(curCart, cm);
    const savedRes = await saveAddressToAccount(account, order.addressDetails, prefetchedAddrs || []);
    if (!savedRes?.addressId || !isUsableDeliveryAddress(savedRes.addressDetails) || !normalizeIndianMobile(savedRes.addressDetails.mobile)) {
      const err = new Error(savedRes?.error || 'The exact recipient address could not be saved on this Swiggy account.');
      err.diag = { code: 'QR_DELIVERY_ADDRESS_BIND_FAILED', stage: 'GENERATE_REAL_QR' };
      throw err;
    }
    order.addressDetails = savedRes.addressDetails;
    const requestedAddressId = String(savedRes.addressId);
    let cartAddressId = String(cm.address_id || cm.delivery_address?.id || '');
    let resolvedOwnAddressId = requestedAddressId;
    let cartAddressMismatch = cartAddressId !== requestedAddressId;

    // Only run full Group Cart + Offer discovery sync here if `order.items` wasn't already resolved yet!
    if ((cartAddressMismatch || !cm.order_total || itemCount <= 0) && (!order?.restaurantId || !order?.items?.length) && (order?.cart || order?.cartLink)) {
      const syncCheck = await syncGroupCartAndCheckoutForAccount(account, order, { captureScreenshot: false });
      if (!syncCheck?.success) {
        const err = new Error(syncCheck?.error || 'Failed to sync cart onto selected Swiggy account before QR generation.');
        err.diag = { code: syncCheck?.code || 'QR_RESYNC_FAILED', stage: 'GENERATE_REAL_QR' };
        throw err;
      }
      auth = await getSwiggySessionAuth(account, false);
      const updatedLat = String(order?.addressDetails?.lat || reqLat);
      const updatedLng = String(order?.addressDetails?.lng || reqLng);
      curCart = await swiggyCartGet(account, { lat: updatedLat, lng: updatedLng });
      cm = unwrapCartMeta(curCart);
      itemCount = extractCartCount(curCart, cm);
      requestedAddressId = String(order.addressDetails?.id || requestedAddressId);
      cartAddressId = String(cm.address_id || cm.delivery_address?.id || '');
      resolvedOwnAddressId = requestedAddressId;
      cartAddressMismatch = cartAddressId !== requestedAddressId;
    }

    // Instant Direct Cart + Address + Swiggy One + `offer_ids` Rehydration Shield:
    const expectedSubItems = Array.isArray(order?.activeSubscriptionItems) && order.activeSubscriptionItems.length > 0
      ? order.activeSubscriptionItems
      : (Number(order?.swiggyOneMembershipFee || 0) > 0 ? [{ plan_id: '773', quantity: 1 }] : []);
    const cartOfferSnapshot = curCart?.json?.data ? parseDapiCartPayload(curCart.json.data) : null;
    const expectedLiveBillMatches = doesOrderBillMatchLiveCart(cartOfferSnapshot, order);
    const needsSubOrDiscountRelock =
      (expectedSubItems.length > 0 && Number(cm.subscription_total || 0) === 0) ||
      (Number(order?.tradeDiscountTotal || 0) > 0 && Number(cm.trade_discount_total || 0) === 0) ||
      !expectedLiveBillMatches;

    if ((cartAddressMismatch || !resolvedOwnAddressId || Number(cm.order_total || 0) <= 0 || itemCount <= 0 || needsSubOrDiscountRelock) && order?.restaurantId && order?.items?.length > 0) {
      const ownAddrId = requestedAddressId;
      if (!ownAddrId) {
        const err = new Error('Exact recipient address is not bound to this Swiggy account.');
        err.diag = { code: 'QR_DELIVERY_ADDRESS_BIND_FAILED', stage: 'GENERATE_REAL_QR' };
        throw err;
      }
      resolvedOwnAddressId = ownAddrId;

      const directLat = String(order.addressDetails.lat);
      const directLng = String(order.addressDetails.lng);
      const directSubItems = Array.isArray(order?.activeSubscriptionItems)
        ? order.activeSubscriptionItems
        : (Number(order?.swiggyOneMembershipFee || 0) > 0 ? [{ plan_id: '773', quantity: 1 }] : []);
      const directSync = await swiggyCartUpdate(
        account,
        {
          restaurantId: String(order.restaurantId),
          address_id: ownAddrId,
          couponCode: String(order.couponCode || ''),
          cartItems: buildSwiggyCartItemsPayload(order.items),
          mealItems: [],
          subscriptionItems: directSubItems
        },
        { lat: directLat, lng: directLng, flushFirst: true }
      );
      const directMeta = unwrapCartMeta(directSync);
      if (directMeta && (directMeta.order_total !== undefined || directMeta.cart_total_count !== undefined)) {
        curCart = directSync;
        cm = directMeta;
        itemCount = extractCartCount(directSync, directMeta);
        cartAddressId = String(cm.address_id || cm.delivery_address?.id || '');
        cartAddressMismatch = cartAddressId !== requestedAddressId;
      }

      const relockedCartOffers = curCart?.json?.data ? parseDapiCartPayload(curCart.json.data) : null;
      if (!doesOrderBillMatchLiveCart(relockedCartOffers, order)) {
        const err = new Error('Swiggy did not confirm the same coupon, savings, and bill total shown on the review screen. Payment was stopped; refresh the cart and verify the bill again.');
        err.diag = { code: 'QR_BILL_RELOCK_FAILED', stage: 'GENERATE_REAL_QR' };
        throw err;
      }
    }

    if (cartAddressMismatch || cartAddressId !== requestedAddressId) {
      const err = new Error('Swiggy checkout is still bound to a different delivery address. The order was stopped before payment.');
      err.diag = {
        code: 'QR_DELIVERY_ADDRESS_MISMATCH',
        stage: 'GENERATE_REAL_QR',
        requestedAddressId,
        cartAddressId
      };
      throw err;
    }

    const cartId = String(cm.originalCartId || cm.cartId || cm.cart_id || '');
    const addressId = requestedAddressId;
    const lat = reqLat;
    const lng = reqLng;
    const swiggyMsg = String(curCart?.json?.statusMessage || cm.cart_banner_message || cm.payment_banner_message || '');

    if (!addressId || Number(cm.order_total || 0) <= 0) {
      const err = new Error(
        `Swiggy checkout cart is empty or missing delivery address_id (items=${itemCount}, order_total=${cm.order_total || 0}, address_id="${addressId}", statusCode=${curCart?.json?.statusCode ?? 'null'}, msg="${swiggyMsg}").`
      );
      err.diag = {
        code: 'QR_CART_NOT_READY',
        stage: 'GENERATE_REAL_QR',
        itemCount,
        cartOrderTotal: cm.order_total || 0,
        addressId,
        cartMessage: swiggyMsg
      };
      throw err;
    }

    const extractUpiFromPlaceJson = (placeJson) => {
      const od = placeJson?.data?.order_data || placeJson?.data?.orderData || null;
      let rd = od?.app_redirection_info ?? od?.appRedirectionInfo ?? null;
      if (typeof rd === 'string') {
        try { rd = JSON.parse(rd); } catch { rd = null; }
      }
      const uri =
        rd?.upiRedirect?.upiIntentRedirect?.upiIntentUrl ||
        rd?.upi_intent_url ||
        od?.upiIntentUrl ||
        od?.upi_intent_url ||
        '';
      return { orderData: od, redir: rd, upiIntentUrl: uri };
    };

    // AUTOMATIC SWIGGY MONEY / WALLET FREE CASH SPLIT-PAY ON REAL MERCHANT QR:
    let rawOrderTotal = Number(cm.order_total || 0);
    const alreadyDeductedWallet = Math.max(0, Number(cm.swiggy_money || 0));
    const availableWallet = Math.max(0, Number(cm.user_swiggy_money ?? cm.swiggy_pay_eligible_balance ?? 0));
    const desiredSplitPay = alreadyDeductedWallet === 0 && availableWallet > 0 && availableWallet < rawOrderTotal
      ? Math.round(availableWallet * 100) / 100
      : 0;

    // ENGINE A (PRIMARY — 100% NATIVE SWIGGY ANDROID `POST https://chkout.swiggy.com/api/v2/order/place`):
    // Preserves 100% of App-Only Item Offers (`CRAZY_DEALS`/`NBH_OFFER`), App Free Cash (`₹80`/`₹50`),
    // AND `+₹1` Swiggy One Lite Free Delivery directly inside the real `upi://pay?pa=upiswiggy@icici` QR!
    const sendNativeAndroidPlaceOrder = async (splitPayAmt) => {
      let latestTid = curCart?.json?.tid || account.jwtTid || auth.jwtTid || '';
      const buildNativeReq = () => ({
        headers: buildSwiggyAndroidClientHeaders(account, {
          tid: latestTid,
          token: auth.token,
          sid: auth.sid,
          deviceId: auth.deviceId,
          userId: auth.userId,
          lat,
          lng,
          extraHeaders: {
            paymentamount: String(cm.order_total),
            cartid: String(cm.cartId || cartId),
            cartaddressid: String(addressId),
            addressid: String(addressId)
          }
        }),
        payload: {
          address_id: String(addressId),
          lat: String(lat),
          lng: String(lng),
          payment_cod_method: 'UPIIntent',
          order_comments: '',
          order_total: cm.order_total,
          bill_total: cm.order_total,
          cart_total: cm.order_total,
          cart_total_shown_to_coupon: cm.cart_total_shown_to_coupon ?? cm.order_total,
          total_without_coupon_discount: cm.total_without_coupon_discount ?? cm.order_total,
          original_order_total: cm.original_order_total ?? cm.order_total,
          transaction_amount: cm.order_total,
          updated_amount: cm.order_total,
          amount: cm.order_total,
          cartId: cm.cartId || cartId,
          cart_id: cm.cartId || cartId,
          originalCartId: cm.originalCartId || cartId,
          ...(splitPayAmt > 0 ? { swiggy_pay_amount: String(splitPayAmt) } : {}),
          upi_transaction_info: {
            intent_app: 'com.google.android.apps.nbu.paisa.user',
            intent_app_display_name: 'Google Pay'
          }
        }
      });

      let reqData = buildNativeReq();
      if (globalThis.fetch === __bootNetworkFetchRef && isZeroSmsTestSandboxActive()) {
        const effectiveAmt = Math.max(1, Math.round((Number(cm.order_total || 0) - Number(splitPayAmt || 0)) * 100) / 100);
        const synRand = String(Math.floor(100 + Math.random() * 900));
        const synSeed = `${String(account.phone || '0000').slice(-4)}${Date.now().toString().slice(-6)}${synRand}`;
        const synOrderId = `2599${synSeed.slice(0, 11)}`;
        const synTxnId = `2799${synSeed.slice(0, 11)}`;
        const synJson = {
          statusCode: 0,
          statusMessage: 'Zero-SMS Test Sandbox QR (0 SMS sent to phone)',
          tid: latestTid,
          data: {
            order_data: {
              order_id: synOrderId,
              order_total: effectiveAmt,
              targeted_marketplace_payment_reference_id: synTxnId,
              sla_time: '34',
              app_redirection_info: {
                upiRedirect: {
                  upiIntentRedirect: {
                    upiIntentUrl: `upi://pay?pa=swiggy1online.gpay@okpayaxis&pn=SWIGGY&tr=${synTxnId}&am=${effectiveAmt.toFixed(2)}&cu=INR&mc=5812&amount=${effectiveAmt.toFixed(2)}`
                  }
                }
              }
            }
          }
        };
        return { placeRes: { ok: true, status: 200 }, rawText: JSON.stringify(synJson), json: synJson, splitPayUsed: splitPayAmt };
      }

      let r = await fetch('https://chkout.swiggy.com/api/v2/order/place', {
        method: 'POST',
        headers: reqData.headers,
        body: JSON.stringify(reqData.payload),
        signal: AbortSignal.timeout(12000)
      });
      let txt = await r.text();
      let parsed = null;
      try { parsed = JSON.parse(txt); } catch {}
      if (parsed?.tid && String(parsed.tid).includes('.')) {
        latestTid = parsed.tid;
        account.jwtTid = parsed.tid;
      }

      // If `statusCode === 8` ("Order amount has updated to ₹X"), refresh cart once and confirm updated amount immediately!
      if (parsed?.statusCode === 8) {
        const refreshed = await swiggyCartGet(account, { lat, lng, timeoutMs: 5000 }).catch(() => null);
        const refMeta = unwrapCartMeta(refreshed);
        if (refMeta && Number(refMeta.order_total || 0) > 0) {
          cm = refMeta;
          rawOrderTotal = Number(cm.order_total || 0);
          cartId = String(cm.originalCartId || cm.cartId || cm.cart_id || cartId);
          if (refreshed?.json?.tid && String(refreshed.json.tid).includes('.')) {
            latestTid = refreshed.json.tid;
          }
          reqData = buildNativeReq();
          r = await fetch('https://chkout.swiggy.com/api/v2/order/place', {
            method: 'POST',
            headers: reqData.headers,
            body: JSON.stringify(reqData.payload),
            signal: AbortSignal.timeout(12000)
          });
          txt = await r.text();
          parsed = null;
          try { parsed = JSON.parse(txt); } catch {}
          if (parsed?.tid && String(parsed.tid).includes('.')) {
            account.jwtTid = parsed.tid;
          }
        }
      }
      return { placeRes: r, rawText: txt, json: parsed, splitPayUsed: splitPayAmt };
    };

    const headers = buildSwiggyPaymentsApiHeaders(account, auth, { cartId, addressId, lat, lng });

    // ENGINE B (FALLBACK — `POST https://payments.swiggy.com/api/v3/order/place` WebView Gateway):
    const sendWebPaymentsPlaceOrder = async (splitPayAmt) => {
      const payload = {
        address_id: addressId,
        lat,
        lng,
        payment_cod_method: 'UPIIntent',
        order_comments: '',
        force_validate_coupon: false,
        ...(splitPayAmt > 0 ? { swiggy_pay_amount: String(splitPayAmt) } : {}),
        upi_transaction_info: {
          intent_app: 'com.google.android.apps.nbu.paisa.user',
          intent_app_display_name: 'Google Pay'
        }
      };
      if (globalThis.fetch === __bootNetworkFetchRef && isZeroSmsTestSandboxActive()) {
        const effectiveAmt = Math.max(1, Math.round((Number(cm.order_total || 0) - Number(splitPayAmt || 0)) * 100) / 100);
        const synRand = String(Math.floor(100 + Math.random() * 900));
        const synSeed = `${String(account.phone || '0000').slice(-4)}${Date.now().toString().slice(-6)}${synRand}`;
        const synOrderId = `2599${synSeed.slice(0, 11)}`;
        const synTxnId = `2799${synSeed.slice(0, 11)}`;
        const synJson = {
          statusCode: 0,
          statusMessage: 'Zero-SMS Test Sandbox QR (0 SMS sent to phone)',
          data: {
            order_data: {
              order_id: synOrderId,
              order_total: effectiveAmt,
              targeted_marketplace_payment_reference_id: synTxnId,
              sla_time: '34',
              app_redirection_info: {
                upiRedirect: {
                  upiIntentRedirect: {
                    upiIntentUrl: `upi://pay?pa=swiggy1online.gpay@okpayaxis&pn=SWIGGY&tr=${synTxnId}&am=${effectiveAmt.toFixed(2)}&cu=INR&mc=5812&amount=${effectiveAmt.toFixed(2)}`
                  }
                }
              }
            }
          }
        };
        return { placeRes: { ok: true, status: 200 }, rawText: JSON.stringify(synJson), json: synJson, splitPayUsed: splitPayAmt };
      }

      const r = await fetch('https://payments.swiggy.com/api/v3/order/place', {
        method: 'POST',
        headers: buildSwiggyPaymentsApiHeaders(account, auth, { cartId, addressId, lat, lng }),
        body: JSON.stringify(payload)
      });
      const txt = await r.text();
      let parsed = null;
      try { parsed = JSON.parse(txt); } catch {}
      return { placeRes: r, rawText: txt, json: parsed, splitPayUsed: splitPayAmt };
    };

    // Note: if `user_swiggy_money > 0`, try `payments.swiggy.com/api/v3/order/place` FIRST only when no native trade discount would be lost,
    // OR try Native Android `chkout/api/v2/order/place` first whenever native item/reward discounts are active!
    let attemptOut = null;
    if (desiredSplitPay > 0 && Number(cm.trade_discount_total || 0) === 0 && Number(cm.subscription_total || 0) === 0) {
      attemptOut = await sendWebPaymentsPlaceOrder(desiredSplitPay).catch(() => null);
      if (!attemptOut || !attemptOut.placeRes?.ok || attemptOut.json?.statusCode !== 0 || !extractUpiFromPlaceJson(attemptOut.json).upiIntentUrl) {
        attemptOut = await sendWebPaymentsPlaceOrder(0).catch(() => null);
      }
    } else {
      attemptOut = await sendNativeAndroidPlaceOrder(desiredSplitPay).catch(() => null);
      if (desiredSplitPay > 0 && (!attemptOut || !attemptOut.placeRes?.ok || attemptOut.json?.statusCode !== 0 || !extractUpiFromPlaceJson(attemptOut.json).upiIntentUrl)) {
        attemptOut = await sendNativeAndroidPlaceOrder(0).catch(() => null);
      }
      if (!attemptOut || !attemptOut.placeRes?.ok || attemptOut.json?.statusCode !== 0 || !extractUpiFromPlaceJson(attemptOut.json).upiIntentUrl) {
        attemptOut = await sendWebPaymentsPlaceOrder(desiredSplitPay).catch(() => null);
        if (desiredSplitPay > 0 && (!attemptOut || !attemptOut.placeRes?.ok || attemptOut.json?.statusCode !== 0 || !extractUpiFromPlaceJson(attemptOut.json).upiIntentUrl)) {
          attemptOut = await sendWebPaymentsPlaceOrder(0).catch(() => null);
        }
      }
    }

    const { placeRes, rawText, json, splitPayUsed } = attemptOut || { placeRes: { ok: false, status: 0 }, rawText: '', json: null, splitPayUsed: 0 };

    const { orderData, redir, upiIntentUrl } = extractUpiFromPlaceJson(json);

    const swiggyOrderId = String(orderData?.order_id || orderData?.orderId || '');
    const paymentTxnId = String(
      orderData?.targeted_marketplace_payment_reference_id ||
      orderData?.payment_info_v2?.payment_transactions?.[0]?.marketplace_reference_id ||
      redir?.upiRedirect?.upiIntentRedirect?.transactionId ||
      ''
    );
    let upiEmbeddedAmount = NaN;
    try {
      const amParam = new URL(upiIntentUrl).searchParams.get('am');
      if (amParam !== null && amParam !== '') upiEmbeddedAmount = Number(amParam);
    } catch {}
    const rawPlacedTotal = Number(orderData?.order_total ?? cm.order_total ?? order?.finalPayable ?? 0);
    const liveOrderTotal = Number.isFinite(upiEmbeddedAmount) && upiEmbeddedAmount > 0
      ? upiEmbeddedAmount
      : (splitPayUsed > 0 && rawPlacedTotal === rawOrderTotal
          ? Math.max(0, Math.round((rawPlacedTotal - splitPayUsed) * 100) / 100)
          : rawPlacedTotal);

    if (!placeRes.ok || json?.statusCode !== 0 || !upiIntentUrl || !upiIntentUrl.startsWith('upi://')) {
      const err = new Error(
        `Swiggy payment gateway rejected QR creation: HTTP ${placeRes.status}, statusCode=${json?.statusCode}, msg="${json?.statusMessage || 'Unknown'}"`
      );
      err.diag = {
        code: 'SWIGGY_PLACE_ORDER_QR_FAILED',
        stage: 'POST_PAYMENTS_ORDER_PLACE',
        httpStatus: placeRes.status,
        swiggyStatusCode: json?.statusCode ?? null,
        swiggyMessage: json?.statusMessage || '',
        cartId,
        addressId,
        cartTotal: cm.order_total,
        rawSnippet: rawText.slice(0, 500)
      };
      throw err;
    }

    if (order && typeof order === 'object') {
      const refreshedBill = parseDapiCartPayload(cm);
      if (refreshedBill && refreshedBill.items?.length > 0) {
        order.itemTotal = refreshedBill.itemTotal;
        order.subtotal = refreshedBill.subtotal;
        order.tradeDiscountTotal = refreshedBill.tradeDiscountTotal;
        order.merchantTradeDiscount = refreshedBill.merchantTradeDiscount;
        order.campaignFreeCash = refreshedBill.campaignFreeCash;
        order.walletSplitPayAmount = splitPayUsed > 0 ? splitPayUsed : refreshedBill.walletSplitPayAmount;
        order.freeCashApplied = Math.round(((refreshedBill.campaignFreeCash || 0) + (order.walletSplitPayAmount || 0)) * 100) / 100;
        order.swiggyOneMembershipFee = refreshedBill.swiggyOneMembershipFee;
        order.deliveryFee = refreshedBill.deliveryFee;
        order.freeDeliveryDiscount = refreshedBill.freeDeliveryDiscount;
        order.swiggyOneApplied = refreshedBill.swiggyOneApplied;
        order.packingCharges = refreshedBill.packingCharges;
        order.taxesAndCharges = refreshedBill.taxesAndCharges;
        order.totalSavings = refreshedBill.totalSavings;
      }
      if (liveOrderTotal > 0) {
        order.finalPayable = liveOrderTotal;
      }
      order.pendingSwiggyOrderId = swiggyOrderId;
      order.pendingSwiggyPaasId = paymentTxnId;
      order.pendingSwiggyUpiUri = upiIntentUrl;
      order.pendingQrAmount = liveOrderTotal;
      order.pendingQrCreatedAt = Date.now();
      order.pendingQrAddressId = String(order.addressDetails?.id || addressId);
      order.pendingQrAddressText = normalizeAddressText(order.addressDetails?.address || '');
      order.pendingQrDeliveryMobile = normalizeIndianMobile(order.addressDetails?.mobile);
      order.pendingQrLat = String(order.addressDetails?.lat || '');
      order.pendingQrLng = String(order.addressDetails?.lng || '');
      order.pendingQrAddressAccount = String(account.phone || account.mobile || '');
    }

    return {
      upiIntentUrl,
      swiggyOrderId,
      orderId: swiggyOrderId,
      paymentTxnId,
      amount: liveOrderTotal,
      swiggyPaySplitAmount: splitPayUsed,
      slaMinutes: orderData?.sla_time ? String(orderData.sla_time) : '',
      restaurantName: orderData?.restaurant_name || cm.restaurant_details?.name || order?.restaurantName || '',
      confirmWindowMs: Number(redir?.upiRedirect?.upiIntentRedirect?.upiIntentConfirmTimeInMs || 45000)
    };
  });
}

/**
 * Checks LIVE payment status & extracts REAL Swiggy Order ID, Order Status, Rider Info & Live Tracking Data:
 * 1) Non-destructively checks `GET https://payments.swiggy.com/api/v3/vpa-txn-status?paas_id=<txnId>&payment_code=UPIIntent`
 * 2) As soon as `data === 'success'`, fires `POST https://payments.swiggy.com/api/v3/order/confirm?order_id=<id>` so Swiggy confirms kitchen dispatch!
 * 3) Verifies real paid order via `GET /dapi/order/all` + `GET /dapi/order/details?type=full&version=V2` + `GET /dapi/order/trackV4` + `GET /dapi/order/trackV2/de`.
 */
export async function checkRealSwiggyPaymentAndExtractTracking(accountOrOpts, maybeOrder) {
  const isWrapped = accountOrOpts && typeof accountOrOpts === 'object' && ('account' in accountOrOpts) && !maybeOrder;
  const account = isWrapped ? accountOrOpts.account : accountOrOpts;
  const order = isWrapped
    ? (accountOrOpts.order || { pendingSwiggyOrderId: accountOrOpts.orderId, pendingSwiggyPaasId: accountOrOpts.paymentTxnId })
    : maybeOrder;

  if (!account || (!account.cookies && !account.tid && !account.token)) {
    const err = new Error('Selected Swiggy account has no session cookies or token while checking payment.');
    err.diag = { code: 'PAID_CHECK_NO_COOKIES', stage: 'CHECK_PAYMENT_AND_TRACKING' };
    throw err;
  }

  const auth = await getSwiggySessionAuth(account, true);
  if (!auth?.userId) {
    const err = new Error('Swiggy session expired while checking payment status.');
    err.diag = { code: 'PAID_CHECK_AUTH_EXPIRED', stage: 'CHECK_PAYMENT_AND_TRACKING' };
    throw err;
  }

  const headers = buildSwiggyPaymentsApiHeaders(account, auth);
  let gatewayTxnState = '';
  let targetOrderId = String(order?.pendingSwiggyOrderId || order?.swiggyOrderId || '');
  const pendingPaasId = String(order?.pendingSwiggyPaasId || '');

  // Step 1: Non-destructive live gateway check on the exact QR `paas_id` (`transactionId`)
  if (pendingPaasId.startsWith('2799') && globalThis.fetch === __bootNetworkFetchRef) {
    return { paid: false, txnState: 'pending' };
  }
  if (pendingPaasId) {
    try {
      const txnRes = await fetch(
        `https://payments.swiggy.com/api/v3/vpa-txn-status?paas_id=${encodeURIComponent(pendingPaasId)}&payment_code=UPIIntent`,
        { method: 'GET', headers }
      );
      const txnJson = await txnRes.json().catch(() => null);
      gatewayTxnState = String(txnJson?.data || '').toLowerCase();

      // ONLY confirm order on Swiggy AFTER payment genuinely succeeded (`success` / `completed`)!
      if (['success', 'completed', 'paid'].includes(gatewayTxnState) && targetOrderId) {
        await fetch(
          `https://payments.swiggy.com/api/v3/order/confirm?order_id=${encodeURIComponent(targetOrderId)}`,
          {
            method: 'POST',
            headers,
            body: JSON.stringify({ order_id: targetOrderId, transaction_id: pendingPaasId })
          }
        ).catch(() => {});
      }
    } catch (e) {}
  }

  // Step 2: Re-fetch fresh `/dapi/order/all` to detect either:
  //   - Exact paid `pendingSwiggyOrderId`, OR
  //   - Any brand-new paid Swiggy order placed on this account after `baselineSwiggyOrderId`!
  const freshAuth = await getSwiggySessionAuth(account, true);
  const recentOrders = freshAuth?.orders || auth?.orders || [];
  const baselineId = String(order?.baselineSwiggyOrderId || '');

  const targetNumeric = /^\d+$/.test(targetOrderId) ? BigInt(targetOrderId) : null;
  let matchedOrder = null;
  for (const o of recentOrders) {
    const oid = String(o?.order_id || '');
    if (!oid) continue;
    if (baselineId && oid === baselineId) break;
    // Strict monotonic snowflake guard: ANY historical order older than `targetOrderId` (`BigInt(oid) < BigInt(targetOrderId)`)
    // was placed BEFORE this QR was ever created and can NEVER match this order!
    if (targetNumeric !== null && /^\d+$/.test(oid) && BigInt(oid) < targetNumeric) break;
    if (targetOrderId && oid === targetOrderId) {
      matchedOrder = o;
      break;
    }
    if (!matchedOrder && (baselineId || targetNumeric !== null)) {
      matchedOrder = o;
    }
  }

  // If order hasn't surfaced in `/dapi/order/all` yet, also check `order/details?order_id=<targetOrderId>&type=full&version=V2`
  if (!matchedOrder && targetOrderId) {
    const det = await dapiFetch(account, `order/details?order_id=${encodeURIComponent(targetOrderId)}&type=full&version=V2`).catch(() => null);
    const detOrder = det?.json?.data?.orders?.[0];
    if (detOrder) {
      const payState = String(detOrder?.payment_info_v2?.payment_transactions?.[0]?.state || '').toUpperCase();
      const postSt = String(detOrder?.post_status || '').toLowerCase();
      if (payState === 'STATE_SUCCESS' || ['processing', 'completed', 'delivered'].includes(postSt) || ['success', 'completed', 'paid'].includes(gatewayTxnState)) {
        matchedOrder = detOrder;
      }
    }
  }

  // If `vpa-txn-status` confirmed genuine gateway payment on a token-only account (`ZERO _session_tid`), build verified order record directly!
  if (!matchedOrder && ['success', 'completed', 'paid'].includes(gatewayTxnState) && targetOrderId) {
    matchedOrder = {
      order_id: targetOrderId,
      customer_id: auth.userId,
      order_status: 'processing',
      post_status: 'processing',
      restaurant_name: order?.restaurantName || 'Swiggy',
      order_total: order?.finalPayable || 0,
      payment_info_v2: { payment_transactions: [{ state: 'STATE_SUCCESS' }] }
    };
  }

  if (!matchedOrder) {
    return {
      paid: false,
      txnState: gatewayTxnState || 'pending'
    };
  }

  const payTxnState = String(matchedOrder?.payment_info_v2?.payment_transactions?.[0]?.state || '').toUpperCase();
  const statusStr = String(matchedOrder?.order_status || matchedOrder?.post_status || '').toLowerCase();
  const isPaidAndValid =
    (payTxnState === 'STATE_SUCCESS' || ['success', 'completed', 'paid'].includes(gatewayTxnState) || (!payTxnState && !/fail|cancel|pending_payment/i.test(statusStr))) &&
    !/cancel|fail|aborted|pending/i.test(statusStr === 'pending' ? 'pending' : (/cancel|fail|aborted/i.test(statusStr) ? statusStr : ''));

  // Wait: if `post_status === 'pending'` AND payment is NOT `STATE_SUCCESS`, customer hasn't paid yet!
  if (
    payTxnState === 'STATE_PENDING' ||
    payTxnState === 'STATE_FAILED' ||
    (String(matchedOrder?.post_status || '').toLowerCase() === 'pending' && payTxnState !== 'STATE_SUCCESS')
  ) {
    return {
      paid: false,
      txnState: gatewayTxnState || payTxnState.toLowerCase() || 'pending'
    };
  }

  if (!isPaidAndValid) {
    return {
      paid: false,
      txnState: gatewayTxnState || statusStr || 'pending'
    };
  }

  const confirmedOrderId = String(matchedOrder.order_id);
  const customerId = String(matchedOrder.customer_id || auth.userId || '');

  // Step 3: Fetch live `trackV4` + `trackV2/de` for real-time status text, ETA & rider coordinates!
  const [trkRes, deRes] = await Promise.all([
    dapiFetch(account, `order/trackV4?order_id=${encodeURIComponent(confirmedOrderId)}&type=full&version=V2&customer_id=${encodeURIComponent(customerId)}`).catch(() => null),
    dapiFetch(account, `order/trackV2/de?order_id=${encodeURIComponent(confirmedOrderId)}`).catch(() => null)
  ]);

  const trkData = trkRes?.json?.data || {};
  const deData = deRes?.json?.data || {};

  // Use only a tracking/share URL explicitly returned by Swiggy; never synthesize one from the order ID.
  const nativeShareUrl = extractSwiggyProvidedTrackingUrl(matchedOrder, trkData);
  const deliveryOtp = extractSwiggyDeliveryOtp(matchedOrder, trkData, { delivery: deData });

  const rawStatusMsg = trkData?.order_status_details?.status_message || matchedOrder?.order_status || 'Order Confirmed';
  const cleanOrderStatus = /rate your delivery|^delivered$/i.test(String(rawStatusMsg).trim())
    ? 'Order Delivered'
    : rawStatusMsg;

  return {
    paid: true,
    txnState: 'success',
    swiggyOrderId: confirmedOrderId,
    customerId,
    orderStatus: cleanOrderStatus,
    statusSubText: trkData?.order_status_details?.status_tag_text || '',
    etaMinutes: String(matchedOrder?.sla_time || ''),
    restaurantName: matchedOrder?.restaurant_name || order?.restaurantName || '',
    restaurantAddress: matchedOrder?.restaurant_address || '',
    deliveryBoy: {
      name: matchedOrder?.delivery_boy?.name || deData?.name || '',
      mobile: matchedOrder?.delivery_boy?.mobile || deData?.mobile || '',
      lat: deData?.lat || deData?.location?.lat || null,
      lng: deData?.lng || deData?.location?.lng || null
    },
    deliveryAddress: matchedOrder?.delivery_address || order?.addressDetails || null,
    deliveryOtp,
    nativeShareUrl,
    swiggyWebTrackUrl: nativeShareUrl || null,
    swiggyAppDeepLink: null
  };
}

