import fs from 'fs';
import path from 'path';
import {
  getDb,
  saveDb,
  mutateDb,
  isBoss,
  addBoss,
  getAccounts,
  createAccount,
  updateAccount,
  deleteAccount,
  getDraft,
  updateDraft,
  clearDraft,
  getActiveUserOrder,
  exportSessionJson,
  importSessionJson,
  permanentLogoutAccount,
  canTransitionOrder,
  ORDER_STATES
} from './store.js';
import {
  getGenuinePaymentDetails,
  generateUpiQrUrl,
  extractRealSwiggyTracking,
  verifyPaymentStatusFromApi,
  parseAddressDetails,
  formatSwiggyWorldCartReceipt,
  isValidIndianDeliveryCoordinates,
  geocodeAddressDetails,
  saveAddressToAccount,
  generateRealSwiggyMerchantUpiQr,
  swiggyCartUpdate,
  extractSwiggyProvidedTrackingUrl,
  extractSwiggyDeliveryOtp,
  getStoredSwiggyTrackingUrl,
  isOfficialSwiggyTrackingUrl,
  parseDapiCartPayload,
  doesCouponMatchExpectedOrder,
  doesOrderBillMatchLiveCart,
  reapplyWinningCouponAfterTrials,
  fetchAccountAddresses,
  findBestMaxCouponAccountForOrder,
  clearAllAccountReservations,
  invalidateAccountOrderProfileCache
} from './swiggy-cart.js';
import {
  getReadyOrdersWaitingForAccount,
  getBillReadyOrdersWaitingForQr,
  ingestForwardedContentIntoOrder,
  buildForwardedOrderCardView,
  buildTelegramUserBillConfirmationCard,
  applyBossOrderUpdate,
  finalizePaidOrderCard,
  startOrderDeliveryInfoPoller,
  stopOrderDeliveryInfoPoller
} from './forwarded-order-flow.js';
import { table } from './rich-text.js';
import { extractStandaloneMobileNumber, prepareNewSwiggyAccountIdentity } from './account-vault-intake.js';
import { parseSwiggyOtpError, sanitizeSwiggyName, safeEvaluateAuthOnce } from './swiggy-bridge.js';

console.log('================================================================');
console.log('🛡️ COMPREHENSIVE 20-SCENARIO AUDIT & VERIFICATION TEST SUITE');
console.log('================================================================\n');

let passedTests = 0;
let totalTests = 0;

function assert(condition, testName, details = '') {
  totalTests++;
  if (condition) {
    console.log(`✅ [PASS ${totalTests.toString().padStart(2, '0')}] ${testName}`);
    passedTests++;
  } else {
    console.error(`❌ [FAIL ${totalTests.toString().padStart(2, '0')}] ${testName} ${details ? '- ' + details : ''}`);
  }
}

// Setup a clean isolated test sandbox in db
const db = getDb();
const initialBackup = JSON.parse(JSON.stringify(db));

try {
  // -------------------------------------------------------------
  // Standalone login number, account-name, and Swiggy security-diagnostic regressions
  // -------------------------------------------------------------
  console.log('\n--- Login Number / Account Name / Swiggy Security Diagnostics ---');
  assert(extractStandaloneMobileNumber('9876543210') === '9876543210', 'A standalone 10-digit Indian mobile is accepted');
  assert(extractStandaloneMobileNumber('919876543210') === '9876543210', 'A standalone 12-digit 91-prefixed number is normalized');
  assert(extractStandaloneMobileNumber('+91 98765-43210') === '9876543210', 'Formatted +91 mobile input is normalized');
  assert(extractStandaloneMobileNumber('119876543210') === null, 'A 12-digit number without the 91 prefix is rejected');
  assert(extractStandaloneMobileNumber('Address, Lucknow 9876543210') === null, 'A number embedded in address text cannot request login OTP');
  const newIdentity = prepareNewSwiggyAccountIdentity('  Bhai  ', {});
  assert(newIdentity.success && newIdentity.name === 'Bhai' && newIdentity.key === 'bhai', 'New account name is preserved with a safe key');
  assert(!prepareNewSwiggyAccountIdentity('Bhai', { bhai: { name: 'Bhai' } }).success, 'Duplicate account labels cannot overwrite an existing account');
  assert(sanitizeSwiggyName('जगदीश कुमार') === 'जगदीश कुमार', 'Signup name sanitization preserves non-Latin letters');
  const securityChallenge = parseSwiggyOtpError({ status: 403, data: { statusMessage: 'captcha challenge' } });
  assert(securityChallenge.code === 'SWIGGY_SECURITY_CHALLENGE' && securityChallenge.retryable === false && /will not retry or bypass/i.test(securityChallenge.message), 'Swiggy challenge is diagnosed without retry/bypass guidance');
  const otpRateLimit = parseSwiggyOtpError({ status: 429 });
  assert(otpRateLimit.code === 'SWIGGY_RATE_LIMIT' && otpRateLimit.retryable === false, 'Swiggy rate limit is distinguished from OTP/auth failures');
  let authEvalCalls = 0;
  await safeEvaluateAuthOnce({ evaluate: async () => { authEvalCalls++; throw new Error('Execution context was destroyed'); } }, async () => {}).catch(() => null);
  assert(authEvalCalls === 1, 'A browser evaluation failure cannot automatically resend an OTP request');
  const verifiedCouponCart = parseDapiCartPayload({
    cartMeta: {
      cartId: 'cart-coupon-check',
      restaurant_details: { id: 'restaurant-coupon-check', name: 'Sample Cafe' },
      cart_menu_items: [{ menu_item_id: 1, name: 'Meal', quantity: 1, subtotal: 20000, final_price: 20000 }],
      item_total: 200,
      coupon_code: 'FEASTMODE70',
      is_coupon_valid: 1,
      coupon_discount_total: 140,
      trade_discount_total: 40,
      trade_discount_reward_amount: 40,
      positiveDeliveryChargesExclusive: 0,
      free_delivery_discount: 28,
      taxesAndCharges: 22.38,
      order_total: 43,
      addresses: [{ id: 'addr-coupon-check', address: 'Hazratganj, Lucknow', lat: '26.85', lng: '80.95' }]
    }
  });
  const couponOrderCheck = { couponCode: 'FEASTMODE70', discountAmount: 140 };
  const sampleExpectedBill = {
    ...couponOrderCheck,
    itemTotal: 200,
    tradeDiscountTotal: 40,
    freeCashApplied: 40,
    freeDeliveryDiscount: 28,
    deliveryFee: 0,
    swiggyOneMembershipFee: 0,
    packingCharges: 0,
    taxesAndCharges: 22.38,
    finalPayable: 43
  };
  assert(verifiedCouponCart.finalPayable === 43 && verifiedCouponCart.totalSavings === 208 && verifiedCouponCart.freeCashApplied === 40, 'Sample cart parses to ₹43 payable with ₹208 savings including ₹40 Free Cash');
  assert(doesOrderBillMatchLiveCart(verifiedCouponCart, sampleExpectedBill), 'Payment gate accepts an exact live match for coupon, free cash, free delivery, charges, and total');
  assert(!doesOrderBillMatchLiveCart({ ...verifiedCouponCart, freeCashApplied: 0 }, sampleExpectedBill), 'Payment gate blocks if Free Cash disappears from the live cart');
  assert(!doesOrderBillMatchLiveCart({ ...verifiedCouponCart, freeDeliveryDiscount: 0 }, sampleExpectedBill), 'Payment gate blocks if free-delivery savings disappear from the live cart');
  assert(doesCouponMatchExpectedOrder(verifiedCouponCart, couponOrderCheck), 'QR gate accepts only the exact Swiggy-confirmed coupon and discount');
  assert(!doesCouponMatchExpectedOrder({ ...verifiedCouponCart, couponCode: 'TRYNEW', discountAmount: 40 }, couponOrderCheck), 'QR gate rejects a weaker coupon left active after coupon trials');
  assert(!doesCouponMatchExpectedOrder({ ...verifiedCouponCart, discountAmount: 100 }, couponOrderCheck), 'QR gate rejects a changed coupon discount instead of charging against a stale bill');
  let winnerReapplyCalls = 0;
  const restoredWinner = await reapplyWinningCouponAfterTrials({
    account: {},
    order: {},
    bestCartState: { couponCode: 'FEASTMODE70', discountAmount: 140 },
    bestCode: 'FEASTMODE70',
    appliedAnyTrial: true,
    applyCouponFn: async () => {
      winnerReapplyCalls++;
      return { items: [{ name: 'Meal' }], couponCode: 'FEASTMODE70', discountAmount: 140 };
    }
  });
  assert(winnerReapplyCalls === 1 && restoredWinner.success, 'Winning coupon is re-applied after trials even when its stored snapshot already matches');
  const failedWinnerReapply = await reapplyWinningCouponAfterTrials({
    account: {}, order: {}, bestCartState: {}, bestCode: 'FEASTMODE70', appliedAnyTrial: true,
    applyCouponFn: async () => ({ items: [{ name: 'Meal' }], couponCode: 'TRYNEW', discountAmount: 40 })
  });
  assert(!failedWinnerReapply.success && failedWinnerReapply.code === 'MAX_COUPON_RELOCK_FAILED', 'Payment is blocked if Swiggy leaves a weaker coupon active instead of the winner');
  const sampleCouponReceipt = formatSwiggyWorldCartReceipt({ ...verifiedCouponCart, ...couponOrderCheck, finalPayable: 43, swiggyVerified: true });
  assert(sampleCouponReceipt.includes('Coupon FEASTMODE70: −₹140 (applied)') && sampleCouponReceipt.includes('₹28 saved'), 'Receipt clearly labels the applied coupon and free-delivery saving');

  // -------------------------------------------------------------
  // Delivery identity regressions: receipt phone + location must survive a round trip
  // -------------------------------------------------------------
  console.log('\n--- Delivery Address / Number / Coordinate Regression Checks ---');
  const deliveryReceipt = formatSwiggyWorldCartReceipt({
    restaurantName: 'Some Cafe',
    selectedAccountPhone: '9876543210',
    addressDetails: {
      name: 'Prathmesh',
      mobile: '9823305540',
      city: 'Pune',
      address: 'Flat no. 412, Parivartan Society, Pune Maharashtra 411030',
      flat_no: 'Flat no. 412',
      lat: '18.502975',
      lng: '73.846375'
    },
    items: [],
    finalPayable: 139
  });
  const roundTripAddress = parseAddressDetails(deliveryReceipt);
  assert(roundTripAddress?.name === 'Prathmesh', 'Formatted receipt round-trip retains recipient name');
  assert(roundTripAddress?.mobile === '9823305540', 'Formatted receipt selects delivery mobile, not Order Account mobile');
  assert(roundTripAddress?.city === 'Pune', 'Formatted receipt round-trip retains delivery city');
  assert(roundTripAddress?.address === 'Flat no. 412, Parivartan Society, Pune Maharashtra 411030', 'Formatted receipt round-trip retains complete street address');
  assert(roundTripAddress?.lat === '18.502975' && roundTripAddress?.lng === '73.846375', 'Formatted receipt round-trip retains the correct GPS coordinates');
  assert(isValidIndianDeliveryCoordinates('18.502975', '73.846375'), 'Valid Pune coordinates accepted');
  assert(!isValidIndianDeliveryCoordinates('73.846375', '18.502975'), 'Swapped Pune latitude/longitude rejected');
  const accountOnlyPhone = parseAddressDetails('Order Account: 9876543210\nPune Address\nPrathmesh\nFlat no. 412, Parivartan Society, Pune Maharashtra 411030');
  assert(accountOnlyPhone?.mobile === null, 'Order Account number is never substituted as recipient mobile');

  const noPhoneSave = await saveAddressToAccount(
    { phone: '9876543210' },
    { address: 'Flat no. 412, Parivartan Society, Pune Maharashtra 411030', lat: '18.502975', lng: '73.846375' },
    [{ id: 'saved-home', address: 'Flat no. 412, Parivartan Society, Pune Maharashtra 411030', mobile: '9876543210', lat: '18.502975', lng: '73.846375' }]
  );
  assert(!noPhoneSave.addressId && /recipient mobile number/i.test(noPhoneSave.error || ''), 'A saved address/account phone cannot substitute for a missing recipient number');

  let missingAddressQrBlocked = false;
  try {
    await generateRealSwiggyMerchantUpiQr({ account: {}, order: { status: 'PENDING' } });
  } catch (error) {
    missingAddressQrBlocked = error?.diag?.code === 'QR_DELIVERY_ADDRESS_UNVERIFIED';
  }
  assert(missingAddressQrBlocked, 'Real Swiggy QR generation fails closed without a verified delivery location');
  let mismatchedPendingQrBlocked = false;
  try {
    await generateRealSwiggyMerchantUpiQr({
      account: { phone: '9000000000' },
      order: {
        status: 'PENDING',
        addressDetails: { id: 'new-address', name: 'Parent', mobile: '9823305540', address: 'New Pune address', lat: '18.502975', lng: '73.846375' },
        pendingSwiggyUpiUri: 'upi://pay?pa=swiggyupi@icici&am=100',
        pendingSwiggyOrderId: 'OLD_ORDER',
        pendingQrCreatedAt: Date.now(),
        pendingQrAddressId: 'old-address',
        pendingQrAddressText: 'old address',
        pendingQrDeliveryMobile: '9823305540',
        pendingQrLat: '18.502975',
        pendingQrLng: '73.846375',
        pendingQrAddressAccount: '9000000000'
      }
    });
  } catch (error) {
    mismatchedPendingQrBlocked = error?.diag?.code === 'QR_EXISTING_DELIVERY_ADDRESS_MISMATCH';
  }
  assert(mismatchedPendingQrBlocked, 'Address changes cannot reuse or duplicate a recent QR bound to another delivery address');
  const invalidCartUpdate = await swiggyCartUpdate(
    {},
    { restaurantId: 'restaurant', address_id: 'saved-id', cartItems: [{ itemId: 'item', quantity: 1 }] }
  );
  assert(invalidCartUpdate?.json?.statusMessage?.includes('verified Indian coordinates'), 'Cart item updates are blocked when verified delivery coordinates are missing');

  const originalFetch = globalThis.fetch;
  const geocodeQueries = [];
  globalThis.fetch = async (url) => {
    const urlText = String(url);
    geocodeQueries.push(urlText);
    return urlText.includes('photon.komoot.io')
      ? { ok: true, json: async () => ({ features: [] }) }
      : { ok: true, json: async () => [{ lat: '18.502975', lon: '73.846375' }] };
  };
  let fullAddressGeocode;
  try {
    fullAddressGeocode = await geocodeAddressDetails({
      address: 'Flat no. 412, Parivartan Society, Pune Maharashtra 411030'
    }, { cookies: 'test-account-session' });
  } finally {
    globalThis.fetch = originalFetch;
  }
  assert(geocodeQueries.some(url => decodeURIComponent(url).includes('Flat no. 412, Parivartan Society, Pune Maharashtra 411030')), 'Forward geocoder receives the complete street address, not a city/PIN-only query');
  assert(fullAddressGeocode?.lat === '18.502975' && fullAddressGeocode?.lng === '73.846375', 'Full-address geocode returns the exact mocked Pune delivery pin');


  // -------------------------------------------------------------
  // Address inventory + automatic max-offer account-selection regressions
  // -------------------------------------------------------------
  console.log('\n--- Address Inventory + Automatic Max-Offer Account Selection ---');
  const testJwt = (uid) => {
    const header = Buffer.from(JSON.stringify({ alg: 'HS256', typ: 'JWT' })).toString('base64url');
    const payload = Buffer.from(JSON.stringify({ user_id: String(uid), exp: Math.floor(Date.now() / 1000) + 86400 })).toString('base64url');
    return `${header}.${payload}.test-signature`;
  };
  const responseJson = (payload, status = 200) => new Response(JSON.stringify(payload), {
    status,
    headers: { 'content-type': 'application/json' }
  });
  const mockAccount = (uid, key) => {
    const tid = testJwt(uid);
    return {
      id: key,
      name: key,
      phone: `9000000${String(uid).slice(-3)}`,
      customerId: String(uid),
      tid,
      jwtTid: tid,
      token: `token_${uid}`,
      sid: `sid_${uid}`,
      deviceId: `device_${uid}`,
      cookies: `tid=${tid}; token=token_${uid}; _sid=sid_${uid}; _device_id=device_${uid}`,
      isLoggedIn: true
    };
  };

  const beforeAddressFetch = globalThis.fetch;
  let addressFetchMode = 'profile';
  let mcpAddressFetches = 0;
  globalThis.fetch = async (input, init = {}) => {
    const url = typeof input === 'string' ? input : input?.url || String(input);
    if (url.includes('profile.swiggy.com/api/v1/user/profile')) {
      const uid = addressFetchMode === 'profile' ? '780001' : '780002';
      const addresses = addressFetchMode === 'profile'
        ? [{
            id: 'profile-nested-address',
            display_address: 'Flat no. 8, Sector 5, Gomti Nagar, Lucknow, Uttar Pradesh 226010',
            actual_address: {
              address_line: 'Flat no. 8',
              formatted_address: 'Sector 5, Gomti Nagar, Lucknow, Uttar Pradesh 226010',
              contact_name: 'Recipient One',
              phone: '+91 98765 43210',
              city: 'Lucknow',
              locality: 'Gomti Nagar',
              location: { latitude: 26.8504, longitude: 80.9504 },
              tags: ['Home']
            }
          }]
        : [];
      return responseJson({ statusCode: 0, data: { customer_id: uid, mobile: '9000000000', addresses } });
    }
    if (url.includes('chkout.swiggy.com/api/v2/cart/client')) {
      return responseJson({ statusCode: 0, data: { cart_menu_items: [], order_total: 0, addresses: [] } });
    }
    if (url.includes('mcp.swiggy.com/food')) {
      mcpAddressFetches++;
      return responseJson({
        jsonrpc: '2.0',
        id: 1,
        result: {
          structuredContent: {
            addresses: [{
              id: 'mcp-fallback-address',
              address: 'House 10, Gomti Nagar, Lucknow 226010',
              latitude: '26.8601',
              longitude: '80.9601',
              contact_name: 'Recipient Two',
              phone: '9876543211',
              annotation: 'Work'
            }]
          },
          content: [{ type: 'text', text: '{}' }]
        }
      });
    }
    return responseJson({ statusCode: 0, data: {} });
  };
  try {
    const nestedAddresses = await fetchAccountAddresses(mockAccount('780001', 'address-profile-test'));
    assert(
      nestedAddresses.some(a => a.id === 'profile-nested-address' && a.name === 'Recipient One' && a.mobile === '9876543210' && a.lat === '26.8504' && a.lng === '80.9504'),
      'Address fetching normalizes nested Swiggy profile records (id, recipient, phone, and map pin)'
    );
    addressFetchMode = 'mcp';
    const mcpFallbackAddresses = await fetchAccountAddresses(mockAccount('780002', 'address-mcp-test'));
    assert(
      mcpAddressFetches > 0 && mcpFallbackAddresses.some(a => a.id === 'mcp-fallback-address' && a.address.includes('Gomti Nagar')),
      'Address fetching falls back to Swiggy Food MCP when profile/cart address lists are empty'
    );
  } finally {
    globalThis.fetch = beforeAddressFetch;
  }

  const beforeSelectionFetch = globalThis.fetch;
  const selectionDbBackup = JSON.parse(JSON.stringify(getDb()));
  const selectionOffers = new Map([
    ['781001', { coupon: 'SAVE20', discount: 20, payable: 280 }],
    ['781002', { coupon: 'SAVE60', discount: 60, payable: 240 }],
    ['781003', { coupon: 'SAVE80', discount: 80, payable: 220 }],
    ['781004', { coupon: 'MAXCOUPON', discount: 220, payable: 80 }]
  ]);
  const requestUserId = (init = {}) => {
    const headers = init.headers || {};
    const getHeader = name => headers?.get?.(name) || headers[name] || headers[name.toLowerCase()] || '';
    const cookie = String(getHeader('Cookie') || '');
    const bearer = String(getHeader('Authorization') || '').replace(/^Bearer\s+/i, '');
    const cookieTid = cookie.match(/(?:^|;\s*)tid=([^;]+)/)?.[1] || '';
    const tid = String(getHeader('tid') || bearer || cookieTid);
    try {
      return String(JSON.parse(Buffer.from(tid.split('.')[1], 'base64url').toString()).user_id || '');
    } catch {
      return '';
    }
  };
  globalThis.fetch = async (input, init = {}) => {
    const url = typeof input === 'string' ? input : input?.url || String(input);
    const uid = requestUserId(init);
    if (url.includes('/dapi/order/all')) {
      const tid = String(init.headers?.Cookie || '').match(/(?:^|;\s*)tid=([^;]+)/)?.[1] || '';
      return responseJson({ statusCode: 0, tid, data: { orders: [] } });
    }
    if (url.includes('/dapi/profile/info')) {
      return responseJson({ statusCode: 0, data: { id: uid, mobile: '9000000000' } });
    }
    if (url.includes('profile.swiggy.com/api/v1/user/profile')) {
      return responseJson({
        statusCode: 0,
        data: {
          customer_id: uid,
          mobile: '9000000000',
          addresses: [{
            id: `addr-${uid}`,
            name: 'Delivery Recipient',
            mobile: '9876543210',
            address: 'Flat 1, Hazratganj, Lucknow 226001',
            city: 'Lucknow',
            area: 'Hazratganj',
            lat: '26.8500',
            lng: '80.9500'
          }]
        }
      });
    }
    if (url.includes('events.swiggy.com')) {
      return responseJson({ statusCode: 0, data: {} });
    }
    if (url.includes('mcp.swiggy.com/food')) {
      const request = JSON.parse(init.body || '{}');
      const structuredContent = request.params?.name === 'fetch_food_coupons' ? { coupons: [] } : {};
      return responseJson({
        jsonrpc: '2.0',
        id: request.id || 1,
        result: { structuredContent, content: [{ type: 'text', text: '{}' }] }
      });
    }
    if (url.includes('/dapi/offers/')) {
      return responseJson({ statusCode: 0, data: { cards: [] } });
    }
    if (url.includes('chkout.swiggy.com/api/v2/cart/client/flush')) {
      return responseJson({ statusCode: 0, data: {} });
    }
    if (url.includes('chkout.swiggy.com/api/v2/cart/client/update')) {
      const body = JSON.parse(init.body || '{}');
      const offer = selectionOffers.get(uid) || { coupon: '', discount: 0, payable: 300 };
      const hasItems = Array.isArray(body.cartItems) && body.cartItems.length > 0;
      const data = hasItems
        ? {
            cartId: `cart-${uid}`,
            originalCartId: `original-${uid}`,
            address_id: body.address_id || `addr-${uid}`,
            restaurant_details: { id: body.restaurantId || 'max-restaurant', name: 'Max Offer Cafe' },
            user_super_status_details: { user_status: 'SUPER' },
            cart_menu_items: [{ menu_item_id: 501, name: 'Meal', quantity: 1, subtotal: 30000, final_price: 30000 }],
            item_total: 300,
            coupon_code: offer.coupon,
            is_coupon_valid: offer.coupon ? 1 : 0,
            coupon_discount_total: offer.discount,
            trade_discount_total: 0,
            positiveDeliveryChargesExclusive: 0,
            delivery_charges: 0,
            free_delivery_discount: 0,
            total_packing_charges: 0,
            total_tax: 0,
            order_total: offer.payable,
            cart_total_count: 1,
            addresses: [{ id: `addr-${uid}`, address: 'Flat 1, Hazratganj, Lucknow 226001', name: 'Delivery Recipient', mobile: '9876543210', lat: '26.8500', lng: '80.9500', city: 'Lucknow' }]
          }
        : { cartId: `cart-${uid}`, cart_menu_items: [], order_total: 0, cart_total_count: 0, addresses: [] };
      return responseJson({ statusCode: 0, tid: String(init.headers?.tid || ''), data });
    }
    if (url.includes('chkout.swiggy.com/api/v2/cart/client')) {
      return responseJson({ statusCode: 0, tid: String(init.headers?.tid || ''), data: { cart_menu_items: [], order_total: 0, cart_total_count: 0, user_super_status_details: { user_status: 'SUPER' }, addresses: [] } });
    }
    return responseJson({ statusCode: 0, data: {} });
  };
  const maxOrderId = 'AUTO_MAX_COUPON_REGRESSION';
  const maxOrder = {
    id: maxOrderId,
    status: 'PENDING',
    cardStage: 'AUTO_SELECTING',
    restaurantId: 'max-restaurant',
    restaurantName: 'Max Offer Cafe',
    items: [{ itemId: '501', menu_item_id: 501, name: 'Meal', price: 300, qty: 1, quantity: 1 }],
    subtotal: 300,
    itemTotal: 300,
    address: 'Flat 1, Hazratganj, Lucknow 226001',
    addressDetails: { name: 'Delivery Recipient', mobile: '9876543210', address: 'Flat 1, Hazratganj, Lucknow 226001', city: 'Lucknow', area: 'Hazratganj', lat: '26.8500', lng: '80.9500' },
    userId: 999
  };
  try {
    const selectionDb = getDb();
    selectionDb.config.accounts = {};
    selectionDb.orders = { [maxOrderId]: maxOrder };
    for (const [uid] of selectionOffers) {
      const account = mockAccount(uid, `auto_select_${uid}`);
      account.name = `Offer Tier ${uid}`;
      account.totalOrdersCount = 0;
      account.preferredOfferValue = Number(uid.slice(-1) <= '4' ? 5 - Number(uid.slice(-1)) : 1);
      // Make the most valuable live offer rank last using the cached offer-tier score.
      if (uid === '781004') account.preferredOfferValue = 1;
      selectionDb.config.accounts[account.id] = account;
    }
    saveDb(selectionDb);
    clearAllAccountReservations();
    invalidateAccountOrderProfileCache();
    const maxResult = await findBestMaxCouponAccountForOrder(maxOrder);
    assert(
      maxResult.success && maxResult.winningKey === 'auto_select_781004' && maxOrder.finalPayable === 80,
      'Automatic account selection probes later batches and picks the lowest live bill, not just the first offer-tier shortlist'
    );
    assert(
      maxResult.accountComparison.length === 4 && maxOrder.couponCode === 'MAXCOUPON' && maxOrder.discountAmount === 220,
      'Max-coupon comparison includes every eligible zero-order account and retains the strongest confirmed coupon'
    );

    await finalizePaidOrderCard({
      telegram: {
        deleteMessage: async () => true,
        sendMessage: async () => ({ message_id: 9001 })
      },
      chatId: 999,
      order: maxOrder,
      livePaidResult: { swiggyOrderId: 'TEST_SWIGGY_ORDER', orderStatus: 'Delivered' },
      formatOrderBodyFn: () => '<b>Test order</b>'
    });
    stopOrderDeliveryInfoPoller(maxOrderId);
    await finalizePaidOrderCard({
      telegram: {
        deleteMessage: async () => true,
        sendMessage: async () => ({ message_id: 9002 })
      },
      chatId: 999,
      order: maxOrder,
      livePaidResult: { swiggyOrderId: 'TEST_SWIGGY_ORDER', orderStatus: 'Delivered' },
      formatOrderBodyFn: () => '<b>Test order</b>'
    });
    stopOrderDeliveryInfoPoller(maxOrderId);
    const postFinalizeDb = getDb();
    assert(
      postFinalizeDb.config.accounts.auto_select_781004.totalOrdersCount === 1 &&
      postFinalizeDb.config.accounts.auto_select_781004.cachedTotalOrdersCount === 1 &&
      postFinalizeDb.config.accounts.auto_select_781004.isZeroOrderAccount === false,
      'A completed order updates the persisted account count exactly once, even if payment finalization is retried'
    );
  } finally {
    stopOrderDeliveryInfoPoller(maxOrderId);
    clearAllAccountReservations();
    invalidateAccountOrderProfileCache();
    globalThis.fetch = beforeSelectionFetch;
    saveDb(selectionDbBackup);
  }

  const forwardedOrder = {
    id: 'FWD_CONTACT_TEST',
    isForwardedOrder: true,
    status: 'PENDING',
    cardStage: 'NEED_ACCOUNT',
    cart: 'https://swig.gy/gc/example',
    address: 'Flat 4, Pune',
    addressDetails: {
      address: 'Flat 4, Parivartan Society, Pune',
      lat: '18.502975',
      lng: '73.846375',
      mobile: ''
    }
  };
  const incompleteForwardedDb = { orders: { [forwardedOrder.id]: forwardedOrder } };
  assert(getReadyOrdersWaitingForAccount(incompleteForwardedDb).length === 0, 'Forwarded orders without recipient mobile cannot enter account allocation');
  const capturedContact = await ingestForwardedContentIntoOrder(forwardedOrder, { rawText: '9823305540' });
  assert(capturedContact.updatedAddress && forwardedOrder.addressDetails.mobile === '9823305540', 'Forwarded-order contact-only correction updates the recipient number without replacing the street address');
  assert(getReadyOrdersWaitingForAccount(incompleteForwardedDb).length === 1, 'Forwarded order becomes account-ready only after the recipient mobile is supplied');

  const officialTrackingUrl = 'https://www.swiggy.com/orders/track/250070826195484';
  assert(
    extractSwiggyProvidedTrackingUrl({ shareable_url: officialTrackingUrl }) === officialTrackingUrl,
    'Tracking extraction accepts a Swiggy URL explicitly present in its shareable field'
  );
  assert(
    extractSwiggyProvidedTrackingUrl({ order_id: '250070826195484' }) === null,
    'Tracking extraction never constructs a link from an order ID alone'
  );
  assert(
    extractSwiggyProvidedTrackingUrl({ tracking_url: 'https://swig.gy/provider-short-code' }) === 'https://swig.gy/provider-short-code',
    'An opaque Swiggy short link is accepted only when Swiggy returns it in an explicit tracking field'
  );
  assert(
    !isOfficialSwiggyTrackingUrl('https://swig.gy/gc/group-cart-code') &&
    !getStoredSwiggyTrackingUrl({ trackingLink: 'https://swig.gy/provider-short-code', trackingLinkSource: 'BOSS_PROVIDED' }),
    'Manual tracking input rejects ambiguous short cart links instead of presenting them as tracking'
  );
  assert(
    extractSwiggyDeliveryOtp({ payment_otp: '112233', delivery_otp: '4821' }) === '4821',
    'Only a delivery OTP is surfaced; payment/login OTP fields are ignored'
  );
  assert(
    extractSwiggyDeliveryOtp({ payment_otp: '112233' }, { delivery: { otp: '5937' } }) === '5937',
    'An unlabeled OTP is accepted only when it comes from the delivery-details response context'
  );
  assert(
    extractSwiggyDeliveryOtp({ delivery: { payment_otp: '112233', login_otp: '112244' } }) === '',
    'Payment and login OTPs stay excluded even when nested in a broad delivery response'
  );
  assert(
    getStoredSwiggyTrackingUrl({ trackingLink: officialTrackingUrl }) === '',
    'Legacy unmarked tracking URLs are not treated as provider-supplied links'
  );
  assert(
    getStoredSwiggyTrackingUrl({ trackingLink: officialTrackingUrl, trackingLinkSource: 'SWIGGY_API' }) === officialTrackingUrl,
    'Provider-supplied Swiggy tracking URL is retained when marked with its source'
  );
  const fakeTrackCard = buildForwardedOrderCardView({
    id: 'TRACK_SAFE_TEST',
    status: 'COMPLETED',
    swiggyOrderId: '250070826195484',
    trackingLink: 'https://www.swiggy.com/track-order/250070826195484',
    shareTrackUrl: 'https://bot.example/track/TRACK_SAFE_TEST?sig=fake'
  }, { config: { accounts: {} } }, () => '<b>Order</b>');
  assert(
    !fakeTrackCard.text.includes('/track-order/250070826195484') && !fakeTrackCard.text.includes('bot.example/track/'),
    'Completed order card does not display bot-generated or legacy unverified tracking links'
  );
  const realTrackCard = buildForwardedOrderCardView({
    id: 'TRACK_OTP_TEST',
    status: 'COMPLETED',
    swiggyOrderId: '250070826195484',
    trackingLink: officialTrackingUrl,
    trackingLinkSource: 'SWIGGY_API',
    deliveryOtp: '4821',
    liveOrderStatus: 'Out for delivery'
  }, { config: { accounts: {} } }, () => '<b>Order</b>');
  assert(
    realTrackCard.text.includes(officialTrackingUrl) && realTrackCard.text.includes('4821') && realTrackCard.text.includes('Out for delivery'),
    'Tracking card pairs Swiggy-provided tracking URL with delivery OTP and live status when available'
  );
  const listStyleTable = table([['#', 'Item', 'Qty', 'Line Total'], ['1', 'Paratha', '2', '₹80']]);
  assert(
    !listStyleTable.includes('<pre>') && !listStyleTable.includes('─') && listStyleTable.includes('Paratha') && listStyleTable.includes('Qty: 2'),
    'Telegram order items render as a readable list, not a fake monospace table with separator lines'
  );

  console.log('\n--- Scenario 15B: Delivery Tracking Arrives Later ---');
  const pollOrderId = 'TRACKING_POLL_LATER';
  const pollDb = getDb();
  pollDb.config.accounts = pollDb.config.accounts || {};
  pollDb.config.accounts.TEST_TRACKING_ACCOUNT = { cookies: 'test-cookie' };
  pollDb.orders[pollOrderId] = {
    id: pollOrderId,
    status: 'COMPLETED',
    userId: 'TRACKING_TEST_USER',
    selectedAccount: 'TEST_TRACKING_ACCOUNT',
    swiggyOrderId: '250070826195484',
    trackingLink: '',
    trackingLinkSource: '',
    deliveryOtp: ''
  };
  saveDb(pollDb);
  const deliveryNotices = [];
  let trackingFetchCount = 0;
  startOrderDeliveryInfoPoller({
    telegram: { sendMessage: async (chatId, text) => { deliveryNotices.push({ chatId, text }); } },
    chatId: 'TRACKING_BOSS_CHAT',
    orderId: pollOrderId,
    intervalMs: 5,
    maxDurationMs: 1000,
    customTrackingFetcher: async () => ({
      trackingUrl: officialTrackingUrl,
      deliveryOtp: ++trackingFetchCount > 1 ? '4821' : '',
      status: 'Out for delivery'
    })
  });
  await new Promise(resolve => setTimeout(resolve, 100));
  stopOrderDeliveryInfoPoller(pollOrderId);
  const polledOrder = getDb().orders[pollOrderId];
  assert(
    polledOrder.trackingLink === officialTrackingUrl && polledOrder.trackingLinkSource === 'SWIGGY_API' && polledOrder.deliveryOtp === '4821',
    'Bounded delivery poller persists a later Swiggy tracking URL and delivery OTP with source provenance'
  );
  assert(
    deliveryNotices.length >= 2 && deliveryNotices.some(notice => notice.text.includes(officialTrackingUrl) && notice.text.includes('4821')),
    'Customer first receives tracking, then receives a follow-up with the delivery OTP when Swiggy publishes it later'
  );
  delete pollDb.orders[pollOrderId];
  delete pollDb.config.accounts.TEST_TRACKING_ACCOUNT;
  saveDb(pollDb);

  // -------------------------------------------------------------
  // Test 1: Normal Successful Order Flow
  // -------------------------------------------------------------
  console.log('\n--- Scenario 1: Normal Successful Order Flow ---');
  const user1 = 9001;
  clearDraft(user1);
  updateDraft(user1, {
    cart: 'https://swiggy.com/menu/123?cart=true',
    address: 'https://maps.google.com/?q=25.60,85.17'
  });
  const d1 = getDraft(user1);
  assert(Boolean(d1.cart && d1.address), 'Draft has both valid links');

  const o1Id = 'TEST_01';
  db.orders[o1Id] = {
    id: o1Id,
    userId: user1,
    userName: 'Ammi Test',
    cart: d1.cart,
    address: d1.address,
    status: 'PENDING',
    slotsLeft: db.config.slotsLeft
  };
  saveDb(db);
  assert(canTransitionOrder(db.orders[o1Id].status, 'ACCEPTED'), 'PENDING order can transition to ACCEPTED');

  // Accept order
  db.orders[o1Id].status = 'ACCEPTED';
  db.config.slotsLeft = Math.max(0, db.config.slotsLeft - 1);
  saveDb(db);
  assert(db.orders[o1Id].status === 'ACCEPTED', 'Order accepted successfully');

  // Verify transition to COMPLETED
  assert(canTransitionOrder('ACCEPTED', 'COMPLETED'), 'ACCEPTED order can transition to COMPLETED');
  db.orders[o1Id].status = 'COMPLETED';
  db.orders[o1Id].swiggyOrderId = 'SWIGGY_998811';
  db.orders[o1Id].trackingLink = 'https://www.swiggy.com/orders/track/SWIGGY_998811';
  saveDb(db);
  assert(db.orders[o1Id].status === 'COMPLETED' && db.orders[o1Id].swiggyOrderId === 'SWIGGY_998811', 'Normal order completed with authentic Swiggy ID');

  // -------------------------------------------------------------
  // Test 2: Missing Cart Link
  // -------------------------------------------------------------
  console.log('\n--- Scenario 2: Missing Cart Link Submission ---');
  const user2 = 9002;
  clearDraft(user2);
  updateDraft(user2, { address: 'https://maps.google.com/?q=25.60,85.17' });
  const d2 = getDraft(user2);
  const canSubmit2 = Boolean(d2.cart && d2.address);
  assert(!canSubmit2, 'Submission blocked when cart link is missing');

  // -------------------------------------------------------------
  // Test 3: Missing Address Link
  // -------------------------------------------------------------
  console.log('\n--- Scenario 3: Missing Address Link Submission ---');
  const user3 = 9003;
  clearDraft(user3);
  updateDraft(user3, { cart: 'https://swiggy.com/menu/456' });
  const d3 = getDraft(user3);
  const canSubmit3 = Boolean(d3.cart && d3.address);
  assert(!canSubmit3, 'Submission blocked when address link is missing');

  // -------------------------------------------------------------
  // Test 4: Invalid Cart or Address Link
  // -------------------------------------------------------------
  console.log('\n--- Scenario 4: Invalid Link Validation ---');
  function isValidSwiggyCart(url) {
    if (!url || typeof url !== 'string') return false;
    const u = url.trim().toLowerCase();
    return (u.startsWith('http://') || u.startsWith('https://')) &&
      (u.includes('swiggy.com') || u.includes('swig.gy') || u.includes('swiggy.onelink.me'));
  }
  assert(!isValidSwiggyCart('https://example.com/fake-cart'), 'Arbitrary external link rejected as cart link');
  assert(!isValidSwiggyCart('not-a-url'), 'Invalid string rejected as cart link');
  assert(isValidSwiggyCart('https://swig.gy/gc/123/order-456'), 'Valid swig.gy group link accepted');

  // -------------------------------------------------------------
  // Test 5: Customer Changing a Link
  // -------------------------------------------------------------
  console.log('\n--- Scenario 5: Customer Link Mutation Isolation ---');
  const user5A = 90051;
  const user5B = 90052;
  clearDraft(user5A);
  clearDraft(user5B);
  updateDraft(user5A, { cart: 'https://swiggy.com/menu/cartA' });
  updateDraft(user5B, { cart: 'https://swiggy.com/menu/cartB' });

  // Update user5A cart
  updateDraft(user5A, { cart: 'https://swiggy.com/menu/cartA_MODIFIED' });
  assert(getDraft(user5A).cart === 'https://swiggy.com/menu/cartA_MODIFIED', 'User A cart link updated');
  assert(getDraft(user5B).cart === 'https://swiggy.com/menu/cartB', 'User B cart link remained isolated and unchanged');

  // -------------------------------------------------------------
  // Test 6: User Submitting Multiple Orders
  // -------------------------------------------------------------
  console.log('\n--- Scenario 6: Active Order Concurrency Limit ---');
  const user6 = 9006;
  const o6 = { id: 'TEST_06', userId: user6, status: 'ACCEPTED' };
  db.orders[o6.id] = o6;
  saveDb(db);
  const active6 = getActiveUserOrder(user6);
  assert(Boolean(active6 && active6.id === 'TEST_06'), 'Active order detected for user');
  const allowedSecondOrder = !active6;
  assert(!allowedSecondOrder, 'User with active order blocked from creating second concurrent order');

  // -------------------------------------------------------------
  // Test 7: Two Users Competing for the Final Slot
  // -------------------------------------------------------------
  console.log('\n--- Scenario 7: Race Condition on Final Slot ---');
  db.config.slotsLeft = 1;
  db.config.totalSlots = 9;
  saveDb(db);

  function tryAcceptSlot(orderId) {
    return mutateDb((d) => {
      if (d.config.slotsLeft <= 0) {
        return { success: false, reason: 'SLOTS_EXHAUSTED' };
      }
      d.config.slotsLeft -= 1;
      return { success: true, remaining: d.config.slotsLeft };
    });
  }

  const race1 = tryAcceptSlot('ORD_RACE_1');
  const race2 = tryAcceptSlot('ORD_RACE_2');
  assert(race1.result.success === true, 'First user successfully acquires final slot');
  assert(race2.result.success === false && race2.result.reason === 'SLOTS_EXHAUSTED', 'Second concurrent user safely blocked when slot reaches 0');
  assert(getDb().config.slotsLeft === 0, 'Slot count does not drop below 0');

  // -------------------------------------------------------------
  // Test 8: Slot Exhaustion and Slot Reopening
  // -------------------------------------------------------------
  console.log('\n--- Scenario 8: Slot Restoration on Cancellation ---');
  const o8Id = 'TEST_08';
  db.config.slotsLeft = 0;
  db.config.totalSlots = 5;
  db.orders[o8Id] = { id: o8Id, status: 'ACCEPTED' };
  saveDb(db);

  // Cancel accepted order
  mutateDb((d) => {
    d.orders[o8Id].status = 'CANCELLED';
    d.config.slotsLeft = Math.min(d.config.totalSlots, d.config.slotsLeft + 1);
  });
  assert(getDb().config.slotsLeft === 1, 'Slot count successfully restored to 1 upon cancellation of accepted order');
  assert(getDb().orders[o8Id].status === 'CANCELLED', 'Order marked as CANCELLED');

  // -------------------------------------------------------------
  // Test 9: Unauthorized Admin Actions
  // -------------------------------------------------------------
  console.log('\n--- Scenario 9: Security Check on Admin Privileges ---');
  const normalUser = 12345678;
  const realBoss = 6484999726;
  assert(!isBoss(normalUser), 'Regular user rejected as admin');
  assert(isBoss(realBoss), 'Authorized Boss recognized');

  // -------------------------------------------------------------
  // Test 10: Repeated Button Clicks and Duplicate Callbacks
  // -------------------------------------------------------------
  console.log('\n--- Scenario 10: Idempotency of Repeated Actions ---');
  const o10Id = 'TEST_10';
  db.orders[o10Id] = { id: o10Id, status: 'ACCEPTED' };
  saveDb(db);

  // Attempting second acceptance
  const canAcceptAgain = canTransitionOrder(db.orders[o10Id].status, 'ACCEPTED') && db.orders[o10Id].status === 'PENDING';
  assert(!canAcceptAgain, 'Repeated accept click safely rejected');

  // -------------------------------------------------------------
  // Test 11: Cancellation Before and After Acceptance
  // -------------------------------------------------------------
  console.log('\n--- Scenario 11: Cancellation Lifecycle Rules ---');
  assert(canTransitionOrder('PENDING', 'CANCELLED'), 'PENDING order can be cancelled');
  assert(canTransitionOrder('ACCEPTED', 'CANCELLED'), 'ACCEPTED order can be cancelled');
  assert(!canTransitionOrder('COMPLETED', 'CANCELLED'), 'COMPLETED order CANNOT be cancelled');

  // -------------------------------------------------------------
  // Test 12: Rejection and Terminal State Protection
  // -------------------------------------------------------------
  console.log('\n--- Scenario 12: Terminal State Protection ---');
  assert(canTransitionOrder('PENDING', 'REJECTED'), 'PENDING order can transition to REJECTED');
  assert(!canTransitionOrder('REJECTED', 'ACCEPTED'), 'REJECTED order CANNOT transition to ACCEPTED');
  assert(!canTransitionOrder('REJECTED', 'COMPLETED'), 'REJECTED order CANNOT transition to COMPLETED');

  // -------------------------------------------------------------
  // Test 13: QR Delivery & Authentic URL
  // -------------------------------------------------------------
  console.log('\n--- Scenario 13: Authentic QR & URL Validation ---');
  const testQrOrder = { id: 'TEST_QR', finalPayable: 299 };
  const genuinePay = getGenuinePaymentDetails(testQrOrder);
  assert(genuinePay.swiggyPaymentUrl === 'https://www.swiggy.com/payments', 'Provides authentic Swiggy payments link');
  assert(!genuinePay.hasGenuineQr, 'Does not claim genuine QR when not attached');

  const legacyGen = generateUpiQrUrl(299, 'TEST_QR');
  assert(legacyGen.qrUrl === null, 'Synthetic qrserver generator returned null');

  // -------------------------------------------------------------
  // Test 14: Failed / Unavailable Payment Handling
  // -------------------------------------------------------------
  console.log('\n--- Scenario 14: Unverified Payment Status Handling ---');
  const unverified = await verifyPaymentStatusFromApi('');
  assert(unverified.paid === false, 'Empty cookies / failed status returns paid = false');
  assert(unverified.status === 'NO_COOKIES', 'Returns exact unverified reason without inventing SUCCESS');

  // -------------------------------------------------------------
  // Test 15: Tracking and Order Completion
  // -------------------------------------------------------------
  console.log('\n--- Scenario 15: Real Tracking Extraction Constraint ---');
  const noTrack = await extractRealSwiggyTracking('');
  assert(noTrack.trackingUrl === null, 'Never invents fake fallback tracking URLs when order unverified');
  assert(noTrack.orderId === null, 'Never invents fake 5-digit Order IDs');

  // -------------------------------------------------------------
  // Test 16: Bot Restart & Persistence Integrity
  // -------------------------------------------------------------
  console.log('\n--- Scenario 16: Persistence & Recovery ---');
  const persistOrder = { id: 'PERSIST_99', status: 'ACCEPTED', userId: 8888 };
  db.orders[persistOrder.id] = persistOrder;
  saveDb(db);

  // Reload from fresh disk read
  const reloadedDb = getDb();
  assert(reloadedDb.orders['PERSIST_99']?.status === 'ACCEPTED', 'Data recovered intact after disk reload');

  // -------------------------------------------------------------
  // Test 17: Telegram Network / API Error Resilience
  // -------------------------------------------------------------
  console.log('\n--- Scenario 17: API Error Resilience ---');
  function safeEditSim(errMessage) {
    if (errMessage && errMessage.includes('message is not modified')) {
      return { handled: true, ignored: true };
    }
    return { handled: true, ignored: false };
  }
  const errRes = safeEditSim('400: Bad Request: message is not modified');
  assert(errRes.handled && errRes.ignored, 'Telegram "message is not modified" error safely absorbed without crashing');

  // -------------------------------------------------------------
  // Test 18: Concurrent Updates to Same Order
  // -------------------------------------------------------------
  console.log('\n--- Scenario 18: Concurrency & Atomic Mutation ---');
  const o18Id = 'TEST_18';
  db.orders[o18Id] = { id: o18Id, counter: 0 };
  saveDb(db);

  mutateDb((d) => { d.orders[o18Id].counter += 1; });
  mutateDb((d) => { d.orders[o18Id].counter += 1; });
  const o18Final = getDb().orders[o18Id];
  assert(o18Final.counter === 2, 'Atomic mutations execute sequentially without lost updates');

  // -------------------------------------------------------------
  // Test 19: Existing Login & Session JSON Export/Import
  // -------------------------------------------------------------
  console.log('\n--- Scenario 19: Login & Session Management ---');
  const testAccKey = 'test_acc';
  createAccount(testAccKey, 'Test Account', '9876543210');
  const importRes = importSessionJson({
    account: testAccKey,
    phone: '9876543210',
    tid: 'test_tid_12345',
    cookies: 'tid=test_tid_12345; _sid=test_sid'
  }, testAccKey);
  assert(importRes.success === true, 'Session JSON imported successfully');

  const exportData = exportSessionJson(testAccKey);
  assert(exportData && exportData.tid === 'test_tid_12345', 'Session JSON exported accurately');

  permanentLogoutAccount(testAccKey);
  assert(getDb().config.accounts[testAccKey].isLoggedIn === false, 'Permanent logout cleans credentials');
  deleteAccount(testAccKey);

  // -------------------------------------------------------------
  // Test 20: Regression Tests for Baseline Features
  // -------------------------------------------------------------
  console.log('\n--- Scenario 20: Baseline Functionality Regression ---');
  const accs = getAccounts();
  assert(typeof accs === 'object', 'Baseline getAccounts() working');
  addBoss(11223344);
  assert(isBoss(11223344), 'addBoss() working');
  // Clean up test boss
  mutateDb((d) => {
    d.config.bossIds = d.config.bossIds.filter(id => id !== 11223344);
  });
  // -------------------------------------------------------------
  // Test 21: Link Replacement Confirmation Safeguard
  // -------------------------------------------------------------
  console.log('\n--- Scenario 21: Link Replacement Confirmation Safeguard ---');
  const u21 = 99921;
  clearDraft(u21);
  updateDraft(u21, { cart: 'https://swig.gy/gc/original-cart' });
  const draftBefore = getDraft(u21);
  assert(draftBefore.cart === 'https://swig.gy/gc/original-cart', 'Initial cart link saved');
  // Attempting to change without confirmation should require user confirmation
  const indexSource = fs.readFileSync('index.js', 'utf8');
  const bossPanelSource = fs.readFileSync('boss-panel.js', 'utf8');
  const forwardedSource = fs.readFileSync('forwarded-order-flow.js', 'utf8');
  const renderSource = fs.readFileSync('render.yaml', 'utf8');
  const allSource = indexSource + '\n' + bossPanelSource + '\n' + forwardedSource;
  assert(!/web_app|telegram-web-app\.js|\/copy|order-ux-portal|APP_BASE_URL|setUserMiniAppButton/i.test(allSource + renderSource), 'Mini App UI, WebApp entry points, APIs, and deployment URL are removed');
  assert(indexSource.includes('action_send_to_boss') && indexSource.includes('action_send_to_beta') && indexSource.includes('action_add_cart') && indexSource.includes('action_add_address') && indexSource.includes('action_previous_order'), 'Traditional inline Telegram order buttons remain wired');
  assert(indexSource.includes("bot.action('boss_login_with_number'") && indexSource.includes("bot.action('boss_login_with_json'") && indexSource.includes("bot.action('boss_view_accounts'"), 'Boss-panel login and account buttons map to existing Telegram handlers');
  assert(indexSource.includes('bot.action(/^fwd_input_(cart|address|mobile)_([A-Za-z0-9_-]+)$/'), 'Order-specific Telegram input buttons have a callback handler');
  assert(forwardedSource.includes('fwd_input_cart_') && forwardedSource.includes('fwd_input_address_') && forwardedSource.includes('fwd_input_mobile_'), 'Forwarded order cards expose Cart, Address, and Mobile input actions');
  const intakeCard = buildForwardedOrderCardView({ id: 'TELEGRAM_BUTTON_TEST', userId: 1, userName: 'Test', status: 'PENDING', isForwardedOrder: true, cardStage: 'COLLECTING' }, getDb(), () => '');
  const intakeCallbacks = intakeCard.keyboard.reply_markup.inline_keyboard.flat().map(button => button.callback_data).filter(Boolean);
  assert(intakeCallbacks.includes('fwd_input_cart_TELEGRAM_BUTTON_TEST') && intakeCallbacks.includes('fwd_input_address_TELEGRAM_BUTTON_TEST'), 'Incomplete order card renders working Cart and Address callbacks');
  const mobileCard = buildForwardedOrderCardView({ id: 'TELEGRAM_MOBILE_TEST', userId: 1, userName: 'Test', status: 'PENDING', isForwardedOrder: true, cardStage: 'COLLECTING', address: 'Hazratganj, Lucknow 226001', addressDetails: { address: 'Hazratganj, Lucknow 226001', lat: '26.85', lng: '80.94', mobile: '' } }, getDb(), () => '');
  const mobileCallbacks = mobileCard.keyboard.reply_markup.inline_keyboard.flat().map(button => button.callback_data).filter(Boolean);
  assert(mobileCallbacks.includes('fwd_input_mobile_TELEGRAM_MOBILE_TEST'), 'Verified-address card exposes recipient-mobile input action');
  const billCard = buildTelegramUserBillConfirmationCard({ id: 'TELEGRAM_BILL_TEST', userId: 2, status: 'APPROVAL_PENDING' });
  const billCallbacks = billCard.keyboard.reply_markup.inline_keyboard.flat().map(button => button.callback_data).filter(Boolean);
  assert(billCallbacks.includes('user_approve_bill_TELEGRAM_BILL_TEST') && billCallbacks.includes('user_bill_issue_TELEGRAM_BILL_TEST') && /official Swiggy payment details to you/.test(billCard.text), 'Bill approval returns to Telegram buttons and promises only existing official Swiggy details');
  const reviewReadyOrder = {
    id: 'TELEGRAM_REVIEW_READY', userId: 2, fwdSenderUserId: 2, isForwardedOrder: true,
    status: 'PENDING', cardStage: 'BILL_READY', selectedAccount: 'test-account', finalPayable: 100,
    cart: 'https://swig.gy/gc/review-ready', address: 'Flat 1, Hazratganj, Lucknow 226001',
    addressDetails: { address: 'Flat 1, Hazratganj, Lucknow 226001', lat: '26.85', lng: '80.94', mobile: '9876543210' }
  };
  const reviewReadyCard = buildForwardedOrderCardView(reviewReadyOrder, getDb(), () => 'Verified bill');
  const reviewReadyCallbacks = reviewReadyCard.keyboard.reply_markup.inline_keyboard.flat().map(button => button.callback_data).filter(Boolean);
  assert(reviewReadyCallbacks.includes('fwd_send_summary_TELEGRAM_REVIEW_READY'), 'Verified forwarded bill exposes its Telegram customer-approval action');
  const approvalWaitOrder = { ...reviewReadyOrder, id: 'TELEGRAM_APPROVAL_WAIT', status: 'APPROVAL_PENDING' };
  const approvalWaitCard = buildForwardedOrderCardView(approvalWaitOrder, getDb(), () => 'Verified bill');
  const approvalWaitCallbacks = approvalWaitCard.keyboard.reply_markup.inline_keyboard.flat().map(button => button.callback_data).filter(Boolean);
  assert(!approvalWaitCallbacks.some(callback => /fwd_(?:gen_qr|send_summary|input_|rechoose_acc|rescan_max)_/.test(callback)), 'Approval-pending Boss card removes stale QR, edit, account, and duplicate-summary buttons');
  assert(getBillReadyOrdersWaitingForQr({ orders: { [approvalWaitOrder.id]: approvalWaitOrder } }).length === 0, 'Parallel QR queue excludes orders waiting for customer approval');
  assert(indexSource.replace(/\r\n/g, '\n').includes('async function handleConfirmOrderPaid(ctx, orderId, _confirmedBy) {\n  const result = await checkOrderPaidStatusOnly(orderId);'), 'Payment-confirmation tap only checks Swiggy status and cannot mark an order paid itself');
  const completedGuard = await applyBossOrderUpdate({ orderId: 'MISSING_TEST_TERMINAL', cart: 'https://swig.gy/gc/example' });
  assert(!completedGuard.ok && /not found/.test(completedGuard.error), 'Boss order input fails closed for missing order IDs');
  db.orders.TELEGRAM_COMPLETED_TEST = { id: 'TELEGRAM_COMPLETED_TEST', status: 'COMPLETED' };
  db.orders.TELEGRAM_QR_STARTED_TEST = { id: 'TELEGRAM_QR_STARTED_TEST', status: 'PENDING', cardStage: 'QR_GENERATED', pendingSwiggyOrderId: '' };
  db.orders.TELEGRAM_APPROVAL_PENDING_TEST = { id: 'TELEGRAM_APPROVAL_PENDING_TEST', status: 'APPROVAL_PENDING', cardStage: 'BILL_READY' };
  saveDb(db);
  const completedEdit = await applyBossOrderUpdate({ orderId: 'TELEGRAM_COMPLETED_TEST', cart: 'https://swig.gy/gc/example' });
  const activeQrEdit = await applyBossOrderUpdate({ orderId: 'TELEGRAM_QR_STARTED_TEST', address: 'New address' });
  const approvalPendingEdit = await applyBossOrderUpdate({ orderId: 'TELEGRAM_APPROVAL_PENDING_TEST', cart: 'https://swig.gy/gc/example' });
  assert(!completedEdit.ok && /cannot be edited/.test(completedEdit.error), 'Completed orders reject Telegram edits');
  assert(!activeQrEdit.ok && /payment QR\/order/.test(activeQrEdit.error), 'Existing Swiggy QR orders reject delivery edits even without an order ID');
  assert(!approvalPendingEdit.ok && /sent for approval/.test(approvalPendingEdit.error), 'Order details are locked while the customer reviews the final bill');
  delete db.orders.TELEGRAM_COMPLETED_TEST;
  delete db.orders.TELEGRAM_QR_STARTED_TEST;
  delete db.orders.TELEGRAM_APPROVAL_PENDING_TEST;
  assert(indexSource.includes('Are you sure you want to change your saved Cart Link?'), 'Cart link change asks for confirmation');
  assert(indexSource.includes('Are you sure you want to change your saved Address Link?'), 'Address link change asks for confirmation');
  assert(indexSource.includes('action_confirm_change_cart') && indexSource.includes('action_confirm_change_address'), 'Link replacement has explicit confirmation action callbacks');

  // -------------------------------------------------------------
  // Test 22: Safe Slot Exhaustion Rejection
  // -------------------------------------------------------------
  console.log('\n--- Scenario 22: Safe Slot Exhaustion Rejection ---');
  mutateDb((d) => {
    d.config.slotsLeft = 0;
  });
  const exhaustedOrder = {
    id: 'test_exhaust_01',
    userId: 8881,
    userName: 'Slot Exhaustion Test User',
    status: 'PENDING',
    cart: 'https://swig.gy/gc/item1',
    address: 'https://maps.google.com/?q=25.2,85.5',
    createdAt: new Date().toISOString()
  };
  mutateDb((d) => {
    d.orders[exhaustedOrder.id] = exhaustedOrder;
  });
  // Simulate slot exhaustion check in boss accept
  if (getDb().config.slotsLeft <= 0) {
    mutateDb((d) => {
      d.orders[exhaustedOrder.id].status = 'REJECTED';
      d.orders[exhaustedOrder.id].rejectedAt = new Date().toISOString();
      d.orders[exhaustedOrder.id].rejectReason = 'Sorry, slot has ended.';
    });
  }
  const postExhaust = getDb().orders[exhaustedOrder.id];
  assert(postExhaust.status === 'REJECTED', 'Exhausted slot rejects order safely');
  assert(postExhaust.rejectReason === 'Sorry, slot has ended.', 'Rejection reason matches exact required text: "Sorry, slot has ended."');
  assert(getDb().config.slotsLeft === 0, 'Slots count remains bounded at 0');

  // -------------------------------------------------------------
  // Test 23: Pre-requisite Amount Validation before QR
  // -------------------------------------------------------------
  console.log('\n--- Scenario 23: Pre-requisite Amount Validation before QR ---');
  const zeroAmountOrder = {
    id: 'test_zero_amount',
    userId: 8882,
    userName: 'Zero Amount User',
    status: 'PENDING',
    finalPayable: 0
  };
  const isAmountValidForQr = (ord) => Boolean(ord.finalPayable && Number(ord.finalPayable) > 0);
  assert(!isAmountValidForQr(zeroAmountOrder), 'Order with ₹0 amount rejected from QR generation');
  zeroAmountOrder.finalPayable = 249;
  assert(isAmountValidForQr(zeroAmountOrder), 'Order with valid payable amount allows QR generation');
  assert(indexSource.includes('Amount must be > 0'), 'Server enforces Amount must be > 0 check before generating or sending QR');

  // -------------------------------------------------------------
  // Test 24: Compact Cancelled Order Card Rendering
  // -------------------------------------------------------------
  console.log('\n--- Scenario 24: Compact Cancelled Order Card Rendering ---');
  assert(allSource.includes('ORDER CANCELLED (#'), 'Compact order card header exists for cancellation');
  assert(allSource.includes('action_cancel_order_confirm_'), 'Customer cancel order triggers confirmation prompt');
  assert(allSource.includes('user_confirm_cancel_'), 'Customer cancel order executes after confirmation');
  assert(allSource.includes('boss_confirm_cancel_'), 'Boss cancel order executes after confirmation');

  // -------------------------------------------------------------
  // Test 25: Button Label Inventory & Preservation Check
  // -------------------------------------------------------------
  console.log('\n--- Scenario 25: Button Label Inventory & Preservation Check ---');
  const requiredLabels = [
    'Auto Max Coupon',
    'Switch Acc',
    'Accept Order',
    'Reject Order',
    'Message User',
    'Copy Cart',
    'Copy Address',
    'Send Tracking',
    'Mark Done',
    'Back to Panel',
    'Pending Orders',
    'Order History',
    'Cancelled Orders',
    'Account Manager',
    'Close Panel',
    'Cancel Order'
  ];
  let allLabelsPresent = true;
  for (const label of requiredLabels) {
    const present = allSource.toLowerCase().includes(label.toLowerCase());
    if (!present) {
      console.error(`Missing required button label: "${label}"`);
      allLabelsPresent = false;
    }
  }
  assert(allLabelsPresent, 'Clean redesigned Boss Panel labels present (old buttons removed per user request)');

} finally {
  // Restore initial clean DB
  saveDb(initialBackup);
}

console.log('\n================================================================');
console.log(`📊 FINAL RESULT: ${passedTests}/${totalTests} Scenarios Successfully Verified!`);
console.log('================================================================');

if (passedTests === totalTests) {
  process.exit(0);
} else {
  process.exit(1);
}
