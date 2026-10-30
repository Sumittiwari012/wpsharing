require('dotenv').config();
const express = require('express');
const http = require('http');
const cors = require('cors');
const multer = require('multer');
const fs = require('fs');
const path = require('path');
const { spawn } = require('child_process');
const { Server } = require('socket.io');
const mysql = require('mysql2/promise');
const crypto = require('crypto');
const {
  default: makeWASocket,
  useMultiFileAuthState,
  DisconnectReason,
  fetchLatestBaileysVersion,
  downloadMediaMessage,
  getContentType,
  normalizeMessageContent,
  BufferJSON,
  WAMessageStubType
} = require('@whiskeysockets/baileys');
const qrcode = require('qrcode');
const pino = require('pino');

/* ───────────────────────── setup ───────────────────────── */

const app = express();
// Development: every website may call this server (no CORS restrictions)
const ORIGIN = '*';
app.set('trust proxy', 1);
app.use(cors({ origin: ORIGIN }));
app.use(express.json());
app.use(express.static('public')); // put your UI (index.html etc.) in ./public

const server = http.createServer(app);
const io = new Server(server, { cors: { origin: ORIGIN } });

const upload = multer({ storage: multer.memoryStorage(), limits: { fileSize: 64 * 1024 * 1024 } });
const logger = pino({ level: 'silent' });

const PORT = process.env.PORT || 4001;
const AUTH_FOLDER = 'auth_info';
const MEDIA_DIR = path.resolve('media');
fs.mkdirSync(MEDIA_DIR, { recursive: true });

// .env: DB_HOST, DB_PORT, DB_USER, DB_PASSWORD, DB_NAME
const pool = mysql.createPool({
  host: process.env.DB_HOST || 'localhost',
  port: Number(process.env.DB_PORT) || 3306,
  user: process.env.DB_USER,
  password: process.env.DB_PASSWORD,
  database: process.env.DB_NAME,
  charset: 'utf8mb4', // needed for emojis
  waitForConnections: true,
  connectionLimit: 10
});

let sock = null;
let latestQr = null;
let isReady = false;
let isStarting = false;

/* ───────────────────────── database ───────────────────────── */

async function initDb() {
  const T = 'ENGINE=InnoDB DEFAULT CHARSET=utf8mb4';
  await pool.query(`CREATE TABLE IF NOT EXISTS chats (
    id VARCHAR(80) PRIMARY KEY,
    name VARCHAR(255) NULL,
    unread_count INT NOT NULL DEFAULT 0,
    last_message_time BIGINT NOT NULL DEFAULT 0,
    pinned TINYINT NOT NULL DEFAULT 0,
    archived TINYINT NOT NULL DEFAULT 0
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS contacts (
    id VARCHAR(80) PRIMARY KEY,
    name VARCHAR(255) NULL,
    notify VARCHAR(255) NULL
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS messages (
    chat_id VARCHAR(80) NOT NULL,
    id VARCHAR(80) NOT NULL,
    ts BIGINT NOT NULL,
    from_me TINYINT NOT NULL DEFAULT 0,
    status TINYINT NOT NULL DEFAULT 0,
    deleted TINYINT NOT NULL DEFAULT 0,
    body MEDIUMTEXT NULL,
    data MEDIUMTEXT NOT NULL,
    raw MEDIUMTEXT NOT NULL,
    media_path VARCHAR(255) NULL,
    PRIMARY KEY (chat_id, id),
    KEY idx_chat_ts (chat_id, ts)
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS reactions (
    message_id VARCHAR(80) NOT NULL,
    reactor VARCHAR(80) NOT NULL,
    emoji VARCHAR(16) NOT NULL,
    PRIMARY KEY (message_id, reactor)
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS users (
    id INT AUTO_INCREMENT PRIMARY KEY,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(190) NOT NULL UNIQUE,
    phone VARCHAR(20) NULL,
    role VARCHAR(10) NOT NULL DEFAULT 'agent',
    active TINYINT NOT NULL DEFAULT 1
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS otps (
    email VARCHAR(190) PRIMARY KEY,
    code_hash CHAR(64) NOT NULL,
    expires_at BIGINT NOT NULL,
    attempts INT NOT NULL DEFAULT 0,
    last_sent BIGINT NOT NULL
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS sessions (
    token_hash CHAR(64) PRIMARY KEY,
    user_id INT NOT NULL,
    expires_at BIGINT NOT NULL,
    created_at BIGINT NOT NULL,
    KEY idx_user (user_id)
  ) ${T}`);
  await pool.query(`CREATE TABLE IF NOT EXISTS assignments (
    chat_id VARCHAR(80) PRIMARY KEY,
    user_id INT NOT NULL,
    assigned_at BIGINT NOT NULL,
    KEY idx_user (user_id)
  ) ${T}`);
  try { await pool.query('ALTER TABLE messages ADD COLUMN sent_by INT NULL'); } catch (_) { /* column already exists */ }

  // Login is by WhatsApp number (email is no longer needed)
  try { await pool.query('ALTER TABLE users MODIFY email VARCHAR(190) NULL'); } catch (_) { /* already nullable */ }
  try { await pool.query('ALTER TABLE users ADD UNIQUE KEY uniq_phone (phone)'); } catch (_) { /* already exists */ }
  await pool.query(`CREATE TABLE IF NOT EXISTS login_codes (
    phone VARCHAR(20) PRIMARY KEY,
    code_hash CHAR(64) NOT NULL,
    expires_at BIGINT NOT NULL,
    attempts INT NOT NULL DEFAULT 0,
    last_sent BIGINT NOT NULL
  ) ${T}`);
  const adminPhone = normPhone(process.env.ADMIN_PHONE);
  if (adminPhone.length < 10) throw new Error('ADMIN_PHONE is missing in .env (with country code, e.g. 919876543210)');
  await pool.query("UPDATE users SET role='agent', active=0 WHERE role='admin' AND (phone IS NULL OR phone <> ?)", [adminPhone]);
  await pool.query(
    "INSERT INTO users (name, phone, role, active) VALUES (?,?,'admin',1) ON DUPLICATE KEY UPDATE role='admin', active=1, name=VALUES(name)",
    [process.env.ADMIN_NAME || 'Admin', adminPhone]
  );
  await loadCaches();
  console.log('MySQL ready');
}

const toNum = (v) => {
  if (v == null) return 0;
  if (typeof v === 'number') return v;
  if (typeof v.toNumber === 'function') return v.toNumber();
  if (typeof v.low === 'number') return v.low;
  return Number(v) || 0;
};

const numberFromJid = (jid) => String(jid).split('@')[0].split(':')[0];

async function upsertChat(id, f = {}) {
  await pool.query('INSERT IGNORE INTO chats (id) VALUES (?)', [id]);
  const sets = [];
  const vals = [];
  const map = { name: 'name', unreadCount: 'unread_count', pinned: 'pinned', archived: 'archived' };
  for (const [k, col] of Object.entries(map)) {
    if (f[k] !== undefined && f[k] !== null) {
      sets.push(`${col}=?`);
      vals.push(typeof f[k] === 'boolean' ? +f[k] : f[k]);
    }
  }
  if (f.lastMessageTime) { sets.push('last_message_time=GREATEST(last_message_time,?)'); vals.push(f.lastMessageTime); }
  if (f.unreadDelta) { sets.push('unread_count=unread_count+?'); vals.push(f.unreadDelta); }
  if (sets.length) await pool.query(`UPDATE chats SET ${sets.join(',')} WHERE id=?`, [...vals, id]);
}

async function upsertContact(id, f = {}) {
  await pool.query('INSERT IGNORE INTO contacts (id) VALUES (?)', [id]);
  const sets = [];
  const vals = [];
  if (f.name) { sets.push('name=?'); vals.push(f.name); }
  if (f.notify) { sets.push('notify=?'); vals.push(f.notify); }
  if (sets.length) await pool.query(`UPDATE contacts SET ${sets.join(',')} WHERE id=?`, [...vals, id]);
}

async function getRaw(chatId, id) {
  const [rows] = await pool.query('SELECT raw FROM messages WHERE chat_id=? AND id=?', [chatId, id]);
  return rows[0] ? JSON.parse(rows[0].raw, BufferJSON.reviver) : null;
}

async function getReactions(ids) {
  const out = {};
  if (!ids.length) return out;
  const [rows] = await pool.query('SELECT message_id, reactor, emoji FROM reactions WHERE message_id IN (?)', [ids]);
  for (const r of rows) (out[r.message_id] ||= {})[r.reactor] = r.emoji;
  return out;
}

function rowToMsg(r, reactions = {}) {
  const m = { ...JSON.parse(r.data), status: r.status || null, deleted: !!r.deleted, reactions, sentBy: r.sent_by ? usersCache.get(r.sent_by)?.name || null : null };
  if (r.deleted) {
    m.type = 'deleted';
    m.text = '🚫 This message was deleted';
    delete m.mediaUrl;
  }
  return m;
}

async function getMessage(chatId, id) {
  const [rows] = await pool.query('SELECT * FROM messages WHERE chat_id=? AND id=?', [chatId, id]);
  if (!rows[0]) return null;
  const reacts = await getReactions([id]);
  return rowToMsg(rows[0], reacts[id] || {});
}

const PREVIEW = { image: '📷 Photo', video: '🎥 Video', document: '📄 Document', sticker: 'Sticker', location: '📍 Location', contact: '👤 Contact' };

function chatRowToJson(r) {
  let last = null;
  if (r.last_data) {
    const d = JSON.parse(r.last_data);
    const deleted = !!r.last_deleted;
    last = {
      type: deleted ? 'deleted' : d.type,
      fromMe: d.fromMe,
      status: r.last_status || null,
      timestamp: d.timestamp,
      text: deleted
        ? '🚫 This message was deleted'
        : d.text || (d.type === 'audio' ? (d.ptt ? '🎤 Voice message' : '🎵 Audio') : d.type === 'document' ? '📄 ' + (d.fileName || 'Document') : PREVIEW[d.type] || '')
    };
  }
  return {
    id: r.id,
    name: r.ct_name || r.name || r.ct_notify || (r.id.endsWith('@g.us') ? 'Group' : '+' + numberFromJid(r.id)),
    isGroup: r.id.endsWith('@g.us'),
    unreadCount: Math.max(0, r.unread_count || 0),
    lastMessageTime: r.last_message_time || 0,
    pinned: !!r.pinned,
    archived: !!r.archived,
    assignedTo: assignedInfo(r.id),
    lastMessage: last
  };
}

async function getChats(onlyJid) {
  const [rows] = await pool.query(
    `SELECT c.id, c.name, c.unread_count, c.last_message_time, c.pinned, c.archived,
            ct.name AS ct_name, ct.notify AS ct_notify,
            m.data AS last_data, m.status AS last_status, m.deleted AS last_deleted
       FROM chats c
       JOIN messages m ON m.chat_id = c.id AND m.ts = (SELECT MAX(ts) FROM messages WHERE chat_id = c.id)
       LEFT JOIN contacts ct ON ct.id = c.id
      WHERE c.id <> 'status@broadcast' ${onlyJid ? 'AND c.id = ?' : ''}`,
    onlyJid ? [onlyJid] : []
  );
  const seen = new Set();
  const out = [];
  for (const r of rows) {
    if (seen.has(r.id)) continue;
    seen.add(r.id);
    out.push(chatRowToJson(r));
  }
  out.sort((a, b) => Number(b.pinned) - Number(a.pinned) || b.lastMessageTime - a.lastMessageTime);
  return out;
}

async function emitChat(jid) {
  const [c] = await getChats(jid);
  if (c) emitToChat(jid, 'chat-update', c);
}

/* ───────────────── WhatsApp message → clean JSON ───────────────── */

const MEDIA_TYPES = ['image', 'video', 'audio', 'document', 'sticker'];

function simplify(raw) {
  if (!raw || !raw.key) return null;
  const base = {
    id: raw.key.id,
    chatId: raw.key.remoteJid,
    fromMe: !!raw.key.fromMe,
    sender: raw.key.participant || raw.participant || raw.key.remoteJid,
    pushName: raw.pushName || null,
    timestamp: toNum(raw.messageTimestamp)
  };

  if (raw.messageStubType === WAMessageStubType.REVOKE) {
    return { ...base, type: 'deleted', text: '🚫 This message was deleted', deleted: true };
  }

  const content = normalizeMessageContent(raw.message);
  if (!content) return null;
  const ctype = getContentType(content);
  const body = content[ctype];
  const ctx = body && typeof body === 'object' ? body.contextInfo : null;
  const out = { ...base, type: 'text', text: '', deleted: false };

  switch (ctype) {
    case 'conversation': out.text = body; break;
    case 'extendedTextMessage': out.text = body.text || ''; break;
    case 'imageMessage': out.type = 'image'; out.text = body.caption || ''; out.mimetype = body.mimetype; break;
    case 'videoMessage': out.type = 'video'; out.text = body.caption || ''; out.mimetype = body.mimetype; out.seconds = body.seconds; out.gif = !!body.gifPlayback; break;
    case 'audioMessage': out.type = 'audio'; out.mimetype = body.mimetype; out.seconds = body.seconds; out.ptt = !!body.ptt; break;
    case 'documentMessage': out.type = 'document'; out.text = body.caption || ''; out.mimetype = body.mimetype; out.fileName = body.fileName || 'file'; break;
    case 'stickerMessage': out.type = 'sticker'; out.mimetype = body.mimetype || 'image/webp'; break;
    case 'locationMessage': out.type = 'location'; out.lat = body.degreesLatitude; out.lng = body.degreesLongitude; out.text = body.name || body.address || ''; break;
    case 'contactMessage': out.type = 'contact'; out.text = body.displayName || ''; out.vcard = body.vcard; break;
    case 'reactionMessage':
    case 'protocolMessage':
    case 'senderKeyDistributionMessage':
      return null;
    default:
      out.type = 'unsupported';
      out.text = '[Unsupported message type: ' + ctype + ']';
  }

  if (MEDIA_TYPES.includes(out.type)) {
    out.mediaUrl = `/media/${encodeURIComponent(out.chatId)}/${encodeURIComponent(out.id)}`;
  }
  if (ctx?.stanzaId) {
    const q = ctx.quotedMessage || {};
    out.quotedId = ctx.stanzaId;
    out.quotedText =
      q.conversation || q.extendedTextMessage?.text || q.imageMessage?.caption || q.videoMessage?.caption ||
      (q.audioMessage ? '🎤 Voice message' : q.documentMessage ? '📄 Document' : '[media]');
  }
  return out;
}

async function addMessage(raw) {
  const jid = raw?.key?.remoteJid;
  if (!jid || jid === 'status@broadcast' || !raw.message) return null;
  raw.messageTimestamp = toNum(raw.messageTimestamp) || Math.floor(Date.now() / 1000);

  const m = simplify(raw);
  if (!m) return null;

  await upsertChat(jid, { lastMessageTime: m.timestamp });
  await pool.query(
    `INSERT INTO messages (chat_id, id, ts, from_me, status, deleted, body, data, raw)
     VALUES (?,?,?,?,?,?,?,?,?)
     ON DUPLICATE KEY UPDATE status = GREATEST(status, VALUES(status)), data = VALUES(data), raw = VALUES(raw)`,
    [jid, m.id, m.timestamp, +m.fromMe, toNum(raw.status), +m.deleted, m.text, JSON.stringify(m), JSON.stringify(raw, BufferJSON.replacer)]
  );

  if (!m.fromMe) {
    if (m.pushName) await upsertContact(m.sender, { notify: m.pushName });
    if (jid.endsWith('@g.us')) fillGroupName(jid);
  }
  return getMessage(jid, m.id);
}

const groupNameTried = new Set();
async function fillGroupName(jid) {
  if (groupNameTried.has(jid) || !sock) return;
  groupNameTried.add(jid);
  try {
    const meta = await sock.groupMetadata(jid);
    await upsertChat(jid, { name: meta.subject });
    emitChat(jid);
  } catch (_) { /* ignore */ }
}

/* ───────────────────────── media on disk ───────────────────────── */

const EXT = {
  'image/jpeg': 'jpg', 'image/png': 'png', 'image/webp': 'webp', 'image/gif': 'gif',
  'video/mp4': 'mp4', 'audio/ogg': 'ogg', 'audio/mpeg': 'mp3', 'audio/mp4': 'm4a', 'audio/aac': 'aac',
  'application/pdf': 'pdf'
};
const extFor = (m) => {
  const fromName = m.fileName && m.fileName.includes('.') ? m.fileName.split('.').pop().toLowerCase().replace(/[^a-z0-9]/g, '') : null;
  return fromName || EXT[(m.mimetype || '').split(';')[0]] || 'bin';
};

async function writeMedia(m, buffer) {
  const rel = m.id.replace(/[^\w-]/g, '_') + '.' + extFor(m);
  fs.writeFileSync(path.join(MEDIA_DIR, rel), buffer);
  await pool.query('UPDATE messages SET media_path=? WHERE chat_id=? AND id=?', [rel, m.chatId, m.id]);
  return path.join(MEDIA_DIR, rel);
}

async function ensureMediaFile(raw, m) {
  const [rows] = await pool.query('SELECT media_path FROM messages WHERE chat_id=? AND id=?', [m.chatId, m.id]);
  const rel = rows[0]?.media_path;
  if (rel && fs.existsSync(path.join(MEDIA_DIR, rel))) return path.join(MEDIA_DIR, rel);
  const buffer = await downloadMediaMessage(raw, 'buffer', {}, { logger, reuploadRequest: sock.updateMediaMessage });
  return writeMedia(m, buffer);
}

/* ───────────────────────── helpers ───────────────────────── */

function toJid(phoneNumber) {
  let number = String(phoneNumber).replace(/\D/g, '');
  if (number.length === 10) number = '91' + number; // default India code if missing
  return `${number}@s.whatsapp.net`;
}

async function resolveTarget(input, user) {
  if (!input) throw Object.assign(new Error('chatId / phoneNumber is required'), { status: 400 });
  const deny = () => Object.assign(new Error('Not allowed: this chat is not assigned to you'), { status: 403 });
  if (String(input).includes('@')) {
    if (user && !canAccess(user, String(input))) throw deny();
    return String(input);
  }
  const jid = toJid(input);
  if (user && !canAccess(user, jid)) throw deny();
  const [check] = await sock.onWhatsApp(jid);
  if (!check?.exists) throw Object.assign(new Error('This number is not registered on WhatsApp'), { status: 400 });
  const final = check.jid || jid;
  if (user && !canAccess(user, final)) throw deny();
  return final;
}

// media = { buffer } optional: saves the file we just sent straight to disk
async function sendAndStore(jid, content, quotedId, media, userId) {
  const opts = quotedId ? { quoted: (await getRaw(jid, quotedId)) || undefined } : {};
  const sent = await sock.sendMessage(jid, content, opts);
  let msg = await addMessage(sent);
  if (msg && media?.buffer && MEDIA_TYPES.includes(msg.type)) await writeMedia(msg, media.buffer);
  if (msg && userId) {
    await pool.query('UPDATE messages SET sent_by=? WHERE chat_id=? AND id=?', [userId, jid, msg.id]);
    msg = await getMessage(jid, msg.id);
  }
  if (msg) emitToChat(jid, 'message', msg);
  emitChat(jid);
  return msg;
}

// Uses the bundled binary from `npm i ffmpeg-static` if present, otherwise a system-wide `ffmpeg`.
const FFMPEG = (() => { try { return require('ffmpeg-static') || 'ffmpeg'; } catch (_) { return 'ffmpeg'; } })();

// Browsers record voice as webm/opus; WhatsApp voice notes need ogg/opus.
function toOggOpus(buffer) {
  return new Promise((resolve, reject) => {
    const ff = spawn(FFMPEG, ['-i', 'pipe:0', '-vn', '-c:a', 'libopus', '-b:a', '32k', '-ar', '48000', '-ac', '1', '-f', 'ogg', 'pipe:1']);
    const chunks = [];
    ff.stdout.on('data', (d) => chunks.push(d));
    ff.on('error', () => reject(new Error('ffmpeg not found — install ffmpeg to send browser-recorded voice notes')));
    ff.on('close', (code) => (code === 0 ? resolve(Buffer.concat(chunks)) : reject(new Error('ffmpeg conversion failed'))));
    ff.stdin.on('error', () => {});
    ff.stdin.end(buffer);
  });
}

const wrap = (fn) => async (req, res) => {
  try {
    await fn(req, res);
  } catch (err) {
    console.error(req.method, req.path, err.message);
    res.status(err.status || 500).json({ success: false, message: err.message });
  }
};

const safe = (fn) => async (...args) => {
  try { await fn(...args); } catch (e) { console.error('event handler error:', e.message); }
};

const requireReady = (req, res, next) =>
  isReady ? next() : res.status(503).json({ success: false, message: 'WhatsApp not connected yet' });

/* ───────────────────────── auth, roles & assignments ───────────────────────── */

const digits = (v) => String(v || '').replace(/\D/g, '');
const normPhone = (v) => { let n = digits(v); if (n.length === 10) n = '91' + n; return n; };
const sha = (v) => crypto.createHash('sha256').update(String(v)).digest('hex');
const safeEq = (a, b) => {
  const x = Buffer.from(String(a));
  const y = Buffer.from(String(b));
  return x.length === y.length && crypto.timingSafeEqual(x, y);
};

const OTP_TTL = 5 * 60 * 1000;
const SESSION_TTL = 7 * 24 * 3600 * 1000;
const assignMap = new Map();   // chat jid -> coworker user id
const usersCache = new Map();  // user id -> { id, name, email, phone, role, active }
const otpMsgIds = new Set();   // OTP messages we sent over WhatsApp (not stored as chats)

async function loadCaches() {
  const [users] = await pool.query('SELECT id, name, email, phone, role, active FROM users');
  usersCache.clear();
  users.forEach((u) => usersCache.set(u.id, u));
  const [rows] = await pool.query('SELECT chat_id, user_id FROM assignments');
  assignMap.clear();
  rows.forEach((a) => assignMap.set(a.chat_id, a.user_id));
}

const canAccess = (user, chatId) => user.role === 'admin' || assignMap.get(chatId) === user.id;
const guard = (req, chatId) => {
  if (!canAccess(req.user, chatId)) throw Object.assign(new Error('Not allowed: this chat is not assigned to you'), { status: 403 });
};
const assignedInfo = (chatId) => {
  const u = usersCache.get(assignMap.get(chatId));
  return u ? { id: u.id, name: u.name } : null;
};

// Events about a chat go only to admins and to the coworker it is assigned to
function emitToChat(chatId, event, payload) {
  let room = io.to('admin');
  const uid = assignMap.get(chatId);
  if (uid) room = room.to('user:' + uid);
  room.emit(event, payload);
}

async function userFromToken(token) {
  if (!token) return null;
  const [rows] = await pool.query(
    `SELECT u.id, u.name, u.email, u.phone, u.role FROM sessions s JOIN users u ON u.id = s.user_id
      WHERE s.token_hash = ? AND s.expires_at > ? AND u.active = 1`,
    [sha(token), Date.now()]
  );
  return rows[0] || null;
}

const tokenOf = (req) => (req.headers.authorization || '').replace(/^Bearer\s+/i, '') || req.query.token || '';
const LEGACY = new Set(['/send-text', '/send-invoice', '/send-image']); // your billing system: uses x-api-key
const keyOk = (req) => !!process.env.SERVICE_API_KEY && safeEq(req.headers['x-api-key'] || '', process.env.SERVICE_API_KEY);

const requireAuth = async (req, res, next) => {
  try {
    if (LEGACY.has(req.path)) {
      return keyOk(req) ? next() : res.status(401).json({ success: false, message: 'x-api-key header required' });
    }
    const user = await userFromToken(tokenOf(req));
    if (!user) return res.status(401).json({ success: false, message: 'Please log in' });
    req.user = user;
    next();
  } catch (e) {
    res.status(500).json({ success: false, message: e.message });
  }
};
const requireAdmin = (req, res, next) =>
  req.user?.role === 'admin' ? next() : res.status(403).json({ success: false, message: 'Admin only' });

// OTP delivery: always through the linked WhatsApp.
// Only before WhatsApp is linked (first admin login) the admin's code is printed in the server log.
async function sendOtp(user, code) {
  const text = `Your login code is ${code}. It expires in 5 minutes. Do not share it with anyone.`;
  if (isReady && sock) {
    const m = await sock.sendMessage(toJid(user.phone), { text });
    if (m?.key?.id) otpMsgIds.add(m.key.id);
    return 'whatsapp';
  }
  if (user.role === 'admin') console.log(`⚠️  WhatsApp is not linked yet. Admin login code for +${user.phone}: ${code}`);
  return 'none';
}

const hits = new Map();
const limited = (key, max, windowMs) => {
  const now = Date.now();
  const list = (hits.get(key) || []).filter((t) => now - t < windowMs);
  list.push(now);
  hits.set(key, list);
  return list.length > max;
};

/* ───────────────────────── WhatsApp socket ───────────────────────── */

async function startSock() {
  if (isStarting) {
    console.log('startSock() already in progress — skipping duplicate call');
    return;
  }
  isStarting = true;
  try {
    const { state, saveCreds } = await useMultiFileAuthState(AUTH_FOLDER);
    const { version } = await fetchLatestBaileysVersion();
    console.log('Using Baileys/WA version:', version);

    sock = makeWASocket({
      auth: state,
      version,
      logger,
      printQRInTerminal: false,
      markOnlineOnConnect: false,
      getMessage: async (key) => (await getRaw(key.remoteJid, key.id))?.message || undefined
    });

    sock.ev.on('creds.update', saveCreds);

    sock.ev.on('connection.update', async (update) => {
      const { connection, lastDisconnect, qr } = update;
      if (qr) {
        latestQr = await qrcode.toDataURL(qr);
        isReady = false;
        io.to('admin').emit('qr', latestQr);
        console.log('New QR generated — waiting for scan via UI');
      }
      if (connection === 'open') {
        const linked = numberFromJid(sock.user?.id || '');
        const allowed = normPhone(process.env.WHATSAPP_NUMBER);
        if (allowed && linked && linked !== allowed) {
          console.log(`❌ Linked number +${linked} does not match WHATSAPP_NUMBER (+${allowed}). Unlinking.`);
          try { await sock.logout(); } catch (_) { /* ignore */ }
          return;
        }
        isReady = true;
        latestQr = null;
        io.emit('ready', true);
        console.log('✅ WhatsApp connected');
      }
      if (connection === 'close') {
        isReady = false;
        io.emit('ready', false);
        const statusCode = lastDisconnect?.error?.output?.statusCode;
        const shouldReconnect = statusCode !== DisconnectReason.loggedOut;
        console.log('Connection closed. Status code:', statusCode, 'Reconnecting:', shouldReconnect);
        isStarting = false;
        if (shouldReconnect) startSock();
        else {
          await fs.promises.rm(AUTH_FOLDER, { recursive: true, force: true });
          startSock();
        }
      }
    });

    // History WhatsApp sends right after you link the device
    sock.ev.on('messaging-history.set', safe(async ({ chats = [], contacts = [], messages = [] }) => {
      for (const c of contacts) await upsertContact(c.id, { name: c.name, notify: c.notify });
      for (const c of chats) {
        await upsertChat(c.id, {
          name: c.name,
          unreadCount: c.unreadCount,
          archived: c.archived != null ? !!c.archived : undefined,
          pinned: c.pinned != null ? toNum(c.pinned) > 0 : undefined,
          lastMessageTime: toNum(c.conversationTimestamp)
        });
      }
      for (const m of messages) await addMessage(m);
      io.to('admin').emit('history-synced', { chats: chats.length, messages: messages.length });
    }));

    sock.ev.on('contacts.upsert', safe(async (list) => { for (const c of list) await upsertContact(c.id, { name: c.name, notify: c.notify }); }));
    sock.ev.on('contacts.update', safe(async (list) => { for (const c of list) if (c.id) await upsertContact(c.id, { name: c.name, notify: c.notify }); }));

    sock.ev.on('chats.upsert', safe(async (list) => {
      for (const c of list) {
        await upsertChat(c.id, {
          name: c.name,
          unreadCount: c.unreadCount,
          archived: c.archived != null ? !!c.archived : undefined,
          pinned: c.pinned != null ? toNum(c.pinned) > 0 : undefined
        });
        emitChat(c.id);
      }
    }));
    sock.ev.on('chats.update', safe(async (list) => {
      for (const u of list) {
        if (!u.id) continue;
        // Baileys sends unreadCount as a delta when > 0, absolute otherwise
        const f = {
          name: u.name,
          archived: u.archived != null ? !!u.archived : undefined,
          pinned: u.pinned != null ? toNum(u.pinned) > 0 : undefined
        };
        if (u.unreadCount > 0) f.unreadDelta = u.unreadCount;
        else if (u.unreadCount === 0) f.unreadCount = 0;
        await upsertChat(u.id, f);
        emitChat(u.id);
      }
    }));
    sock.ev.on('chats.delete', safe(async (ids) => {
      for (const id of ids) {
        await pool.query('DELETE FROM messages WHERE chat_id=?', [id]);
        await pool.query('DELETE FROM chats WHERE id=?', [id]);
        emitToChat(id, 'chat-deleted', id);
      }
    }));

    // New incoming / outgoing messages
    sock.ev.on('messages.upsert', safe(async ({ messages, type }) => {
      for (const raw of messages) {
        if (otpMsgIds.has(raw.key?.id)) continue;
        const msg = await addMessage(raw);
        if (!msg) continue;
        emitToChat(msg.chatId, 'message', msg);
        emitChat(msg.chatId);
        // Save incoming media right away, because WhatsApp media links expire
        if (type === 'notify' && !msg.fromMe && MEDIA_TYPES.includes(msg.type)) {
          ensureMediaFile(raw, msg).catch((e) => console.warn('media download failed:', e.message));
        }
      }
    }));

    // Delivery ticks (sent → delivered → read) and deletes
    sock.ev.on('messages.update', safe(async (updates) => {
      for (const { key, update } of updates) {
        if (update.status != null) {
          await pool.query('UPDATE messages SET status = GREATEST(status, ?) WHERE chat_id=? AND id=?', [update.status, key.remoteJid, key.id]);
        }
        if (update.messageStubType === WAMessageStubType.REVOKE) {
          await pool.query('UPDATE messages SET deleted=1 WHERE chat_id=? AND id=?', [key.remoteJid, key.id]);
        }
        const msg = await getMessage(key.remoteJid, key.id);
        if (msg) emitToChat(msg.chatId, 'message-update', msg);
      }
    }));

    sock.ev.on('messages.reaction', safe(async (list) => {
      for (const { key, reaction } of list) {
        const reactor = reaction.key?.fromMe ? 'me' : reaction.key?.participant || reaction.key?.remoteJid;
        if (reaction.text) {
          await pool.query('INSERT INTO reactions (message_id, reactor, emoji) VALUES (?,?,?) ON DUPLICATE KEY UPDATE emoji=VALUES(emoji)', [key.id, reactor, reaction.text]);
        } else {
          await pool.query('DELETE FROM reactions WHERE message_id=? AND reactor=?', [key.id, reactor]);
        }
        const r = await getReactions([key.id]);
        emitToChat(key.remoteJid, 'message-update', { id: key.id, chatId: key.remoteJid, reactions: r[key.id] || {} });
      }
    }));

    sock.ev.on('presence.update', ({ id, presences }) => emitToChat(id, 'presence', { chatId: id, presences }));
  } catch (err) {
    console.error('startSock() failed:', err);
    isStarting = false;
  } finally {
    setTimeout(() => { isStarting = false; }, 30000);
  }
}

io.use(async (socket, next) => {
  try {
    const user = await userFromToken(socket.handshake.auth?.token);
    if (!user) return next(new Error('unauthorized'));
    socket.user = user;
    next();
  } catch (e) { next(e); }
});

io.on('connection', (socket) => {
  socket.join('user:' + socket.user.id);
  if (socket.user.role === 'admin') socket.join('admin');
  socket.emit('status', { ready: isReady, qr: isReady || socket.user.role !== 'admin' ? null : latestQr });
});

/* ───────────────────────── connection routes ───────────────────────── */

app.get('/health', (req, res) => res.json({ status: 'ok', ready: isReady }));

// Public, no login: shows the QR while WhatsApp is not linked, so anyone can link it
app.get('/link/status', (req, res) => res.json({ ready: isReady, qr: isReady ? null : latestQr }));
// ── login with a code sent over WhatsApp ──
app.post('/auth/request-otp', wrap(async (req, res) => {
  const phone = normPhone(req.body.phone);
  if (phone.length < 10) return res.status(400).json({ success: false, message: 'Enter your WhatsApp number with country code' });
  if (limited('otp:' + req.ip, 10, 10 * 60 * 1000)) return res.status(429).json({ success: false, message: 'Too many attempts. Try again later.' });
  const [rows] = await pool.query('SELECT id, name, phone, role FROM users WHERE phone=? AND active=1', [phone]);
  if (rows[0]) {
    const [o] = await pool.query('SELECT last_sent FROM login_codes WHERE phone=?', [phone]);
    if (!o[0] || Date.now() - o[0].last_sent > 30000) {
      const code = String(crypto.randomInt(0, 1000000)).padStart(6, '0');
      await pool.query('REPLACE INTO login_codes (phone, code_hash, expires_at, attempts, last_sent) VALUES (?,?,?,0,?)', [phone, sha(code + phone), Date.now() + OTP_TTL, Date.now()]);
      sendOtp(rows[0], code).catch((e) => console.error('OTP send failed:', e.message));
    }
  }
  // Same answer whether or not the number is registered
  res.json({ success: true, message: 'If this number is registered, a login code has been sent on WhatsApp.' });
}));

app.post('/auth/verify-otp', wrap(async (req, res) => {
  const phone = normPhone(req.body.phone);
  const code = String(req.body.code || '').trim();
  if (limited('ver:' + req.ip, 20, 10 * 60 * 1000)) return res.status(429).json({ success: false, message: 'Too many attempts. Try again later.' });
  const bad = () => res.status(401).json({ success: false, message: 'Invalid or expired code' });
  const [o] = await pool.query('SELECT * FROM login_codes WHERE phone=?', [phone]);
  if (!o[0] || o[0].expires_at < Date.now() || o[0].attempts >= 5) return bad();
  if (!safeEq(sha(code + phone), o[0].code_hash)) {
    await pool.query('UPDATE login_codes SET attempts = attempts + 1 WHERE phone=?', [phone]);
    return bad();
  }
  await pool.query('DELETE FROM login_codes WHERE phone=?', [phone]);
  const [u] = await pool.query('SELECT id, name, phone, role FROM users WHERE phone=? AND active=1', [phone]);
  if (!u[0]) return bad();
  const token = crypto.randomBytes(32).toString('hex');
  await pool.query('DELETE FROM sessions WHERE expires_at < ?', [Date.now()]);
  await pool.query('INSERT INTO sessions (token_hash, user_id, expires_at, created_at) VALUES (?,?,?,?)', [sha(token), u[0].id, Date.now() + SESSION_TTL, Date.now()]);
  res.json({ success: true, token, user: u[0] });
}));

// Everything below needs a logged-in user (your old /send-* routes need the x-api-key header instead)
app.use(requireAuth);

app.get('/auth/me', (req, res) => res.json({ success: true, user: req.user, ready: isReady }));
app.post('/auth/logout', wrap(async (req, res) => {
  await pool.query('DELETE FROM sessions WHERE token_hash=?', [sha(tokenOf(req))]);
  res.json({ success: true });
}));

app.get('/qr-status', requireAdmin, (req, res) => res.json({ ready: isReady, qr: isReady ? null : latestQr }));

// ── admin: coworkers & assignments ──
const dropAccess = async (id) => {
  await pool.query('DELETE FROM sessions WHERE user_id=?', [id]);
  io.in('user:' + id).disconnectSockets(true);
};

app.get('/admin/users', requireAdmin, wrap(async (req, res) => {
  const [rows] = await pool.query(
    `SELECT u.id, u.name, u.email, u.phone, u.role, u.active,
            (SELECT COUNT(*) FROM assignments a WHERE a.user_id = u.id) AS chats
       FROM users u ORDER BY u.role, u.name`
  );
  res.json({ success: true, users: rows });
}));

app.post('/admin/users', requireAdmin, wrap(async (req, res) => {
  const name = String(req.body.name || '').trim();
  const phone = normPhone(req.body.phone);
  if (!name || phone.length < 10) return res.status(400).json({ success: false, message: 'A name and a WhatsApp number (with country code) are required' });
  try {
    await pool.query("INSERT INTO users (name, phone, role, active) VALUES (?,?,'agent',1)", [name, phone]);
  } catch (e) {
    if (e.code === 'ER_DUP_ENTRY') return res.status(409).json({ success: false, message: 'That number already exists' });
    throw e;
  }
  await loadCaches();
  res.json({ success: true });
}));

app.patch('/admin/users/:id', requireAdmin, wrap(async (req, res) => {
  const id = Number(req.params.id);
  const u = usersCache.get(id);
  if (!u || u.role === 'admin') return res.status(404).json({ success: false, message: 'Coworker not found' });
  const sets = [];
  const vals = [];
  const b = req.body;
  if (b.name) { sets.push('name=?'); vals.push(String(b.name).trim()); }
  if (b.phone !== undefined) { sets.push('phone=?'); vals.push(normPhone(b.phone) || null); }
  if (b.active !== undefined) { sets.push('active=?'); vals.push(b.active ? 1 : 0); }
  if (sets.length) await pool.query(`UPDATE users SET ${sets.join(',')} WHERE id=?`, [...vals, id]);
  if (b.active !== undefined && !b.active) await dropAccess(id);
  await loadCaches();
  res.json({ success: true });
}));

app.delete('/admin/users/:id', requireAdmin, wrap(async (req, res) => {
  const id = Number(req.params.id);
  const u = usersCache.get(id);
  if (!u || u.role === 'admin') return res.status(404).json({ success: false, message: 'Coworker not found' });
  await dropAccess(id);
  await pool.query('DELETE FROM assignments WHERE user_id=?', [id]);
  await pool.query('DELETE FROM users WHERE id=?', [id]);
  await loadCaches();
  res.json({ success: true });
}));

// Body: { chatId | phoneNumber, userId }  (userId null = unassign)
app.post('/admin/assign', requireAdmin, wrap(async (req, res) => {
  const { chatId, phoneNumber } = req.body;
  const userId = req.body.userId == null || req.body.userId === '' ? null : Number(req.body.userId);
  const jid = chatId || (phoneNumber ? toJid(phoneNumber) : null);
  if (!jid) return res.status(400).json({ success: false, message: 'chatId or phoneNumber is required' });
  if (userId != null) {
    const u = usersCache.get(userId);
    if (!u || u.role === 'admin' || !u.active) return res.status(400).json({ success: false, message: 'Choose an active coworker' });
  }
  const old = assignMap.get(jid);
  if (userId == null) await pool.query('DELETE FROM assignments WHERE chat_id=?', [jid]);
  else await pool.query('REPLACE INTO assignments (chat_id, user_id, assigned_at) VALUES (?,?,?)', [jid, userId, Date.now()]);
  await loadCaches();
  if (old && old !== userId) io.to('user:' + old).emit('chat-deleted', jid);
  await emitChat(jid);
  res.json({ success: true, chatId: jid });
}));

app.get('/admin/assignments', requireAdmin, wrap(async (req, res) => {
  const [rows] = await pool.query(
    `SELECT a.chat_id, a.user_id, COALESCE(ct.name, c.name, ct.notify) AS name
       FROM assignments a LEFT JOIN chats c ON c.id = a.chat_id LEFT JOIN contacts ct ON ct.id = a.chat_id
      ORDER BY a.assigned_at DESC`
  );
  res.json({ success: true, assignments: rows.map((r) => ({ chatId: r.chat_id, userId: r.user_id, name: r.name || '+' + numberFromJid(r.chat_id) })) });
}));


app.post('/whatsapp/logout', requireAdmin, wrap(async (req, res) => {
  try { await sock.logout(); } catch (e) { console.warn('sock.logout() error (continuing):', e.message); }
  isReady = false;
  await fs.promises.rm(AUTH_FOLDER, { recursive: true, force: true });
  await fs.promises.rm(MEDIA_DIR, { recursive: true, force: true });
  fs.mkdirSync(MEDIA_DIR, { recursive: true });
  for (const t of ['reactions', 'messages', 'contacts', 'chats']) await pool.query(`DELETE FROM ${t}`);
  res.json({ success: true, message: 'WhatsApp disconnected and local data cleared. Scan a new QR code to reconnect.' });
  startSock();
}));

/* ───────────────────────── reading ───────────────────────── */

app.get('/chats', wrap(async (req, res) => {
  res.json({ success: true, chats: (await getChats()).filter((c) => canAccess(req.user, c.id)) });
}));

// ?limit=50&before=<unix timestamp> for scrolling up
app.get('/messages/:chatId', wrap(async (req, res) => {
  guard(req, req.params.chatId);
  const limit = Math.min(parseInt(req.query.limit) || 50, 200);
  const before = parseInt(req.query.before) || 9999999999999;
  const [rows] = await pool.query(
    'SELECT * FROM messages WHERE chat_id=? AND ts<? ORDER BY ts DESC LIMIT ?',
    [req.params.chatId, before, limit + 1]
  );
  const hasMore = rows.length > limit;
  const page = rows.slice(0, limit).reverse();
  const reacts = await getReactions(page.map((r) => r.id));
  res.json({ success: true, messages: page.map((r) => rowToMsg(r, reacts[r.id] || {})), hasMore });
}));

// Media: served from disk (downloaded on demand if missing). ?download=1 forces download
app.get('/media/:chatId/:id', wrap(async (req, res) => {
  guard(req, req.params.chatId);
  const raw = await getRaw(req.params.chatId, req.params.id);
  if (!raw) return res.status(404).json({ success: false, message: 'Message not found' });
  const msg = simplify(raw);
  if (!msg || !MEDIA_TYPES.includes(msg.type)) return res.status(400).json({ success: false, message: 'Message has no media' });

  const [rows] = await pool.query('SELECT media_path FROM messages WHERE chat_id=? AND id=?', [msg.chatId, msg.id]);
  const rel = rows[0]?.media_path;
  let file = rel && fs.existsSync(path.join(MEDIA_DIR, rel)) ? path.join(MEDIA_DIR, rel) : null;
  if (!file) {
    if (!isReady) return res.status(503).json({ success: false, message: 'WhatsApp not connected yet' });
    file = await ensureMediaFile(raw, msg);
  }
  res.set('Content-Type', msg.mimetype || 'application/octet-stream');
  res.set('Cache-Control', 'private, max-age=86400');
  if (req.query.download) res.attachment(msg.fileName || path.basename(file));
  res.sendFile(file); // supports Range requests so audio/video can seek
}));

const picCache = {};
app.get('/profile-picture/:jid', requireReady, wrap(async (req, res) => {
  const jid = req.params.jid;
  guard(req, jid);
  if (!(jid in picCache)) picCache[jid] = await sock.profilePictureUrl(jid, 'image').catch(() => null);
  res.json({ success: true, url: picCache[jid] });
}));

app.get('/contacts', requireAdmin, wrap(async (req, res) => {
  const [rows] = await pool.query("SELECT id, name, notify FROM contacts WHERE id LIKE '%@s.whatsapp.net'");
  res.json({
    success: true,
    contacts: rows.map((c) => ({ id: c.id, name: c.name || c.notify || '+' + numberFromJid(c.id), number: numberFromJid(c.id) }))
  });
}));

/* ───────────────────────── sending ───────────────────────── */

app.post('/send/text', requireReady, wrap(async (req, res) => {
  const { chatId, phoneNumber, text, quotedId } = req.body;
  if (!text) return res.status(400).json({ success: false, message: 'text is required' });
  const jid = await resolveTarget(chatId || phoneNumber, req.user);
  res.json({ success: true, message: await sendAndStore(jid, { text }, quotedId, null, req.user.id) });
}));

// multipart/form-data: file, chatId|phoneNumber, caption?, quotedId?, ptt? ("true" = voice note), gif?
app.post('/send/media', requireReady, upload.single('file'), wrap(async (req, res) => {
  const { chatId, phoneNumber, caption, quotedId, ptt, gif } = req.body;
  const file = req.file;
  if (!file) return res.status(400).json({ success: false, message: 'file is required' });
  const jid = await resolveTarget(chatId || phoneNumber, req.user);

  let content;
  let saved = file.buffer;
  const mime = file.mimetype || '';
  if (ptt === 'true') {
    saved = /ogg/i.test(mime) ? file.buffer : await toOggOpus(file.buffer);
    content = { audio: saved, mimetype: 'audio/ogg; codecs=opus', ptt: true };
  } else if (mime.startsWith('image/')) {
    content = { image: file.buffer, caption: caption || undefined };
  } else if (mime.startsWith('video/')) {
    content = { video: file.buffer, caption: caption || undefined, gifPlayback: gif === 'true' };
  } else if (mime.startsWith('audio/')) {
    content = { audio: file.buffer, mimetype: mime };
  } else {
    content = { document: file.buffer, mimetype: mime || 'application/octet-stream', fileName: file.originalname, caption: caption || undefined };
  }
  res.json({ success: true, message: await sendAndStore(jid, content, quotedId, { buffer: saved }, req.user.id) });
}));

app.post('/send/location', requireReady, wrap(async (req, res) => {
  const { chatId, phoneNumber, lat, lng, name } = req.body;
  const jid = await resolveTarget(chatId || phoneNumber, req.user);
  res.json({ success: true, message: await sendAndStore(jid, { location: { degreesLatitude: lat, degreesLongitude: lng, name } }, null, null, req.user.id) });
}));

app.post('/react', requireReady, wrap(async (req, res) => {
  const { chatId, messageId, emoji } = req.body;
  guard(req, chatId);
  const raw = await getRaw(chatId, messageId);
  if (!raw) return res.status(404).json({ success: false, message: 'Message not found' });
  await sock.sendMessage(chatId, { react: { text: emoji || '', key: raw.key } });
  if (emoji) {
    await pool.query('INSERT INTO reactions (message_id, reactor, emoji) VALUES (?,?,?) ON DUPLICATE KEY UPDATE emoji=VALUES(emoji)', [messageId, 'me', emoji]);
  } else {
    await pool.query('DELETE FROM reactions WHERE message_id=? AND reactor=?', [messageId, 'me']);
  }
  const r = await getReactions([messageId]);
  emitToChat(chatId, 'message-update', { id: messageId, chatId, reactions: r[messageId] || {} });
  res.json({ success: true });
}));

app.post('/forward', requireReady, wrap(async (req, res) => {
  const { fromChatId, messageId, toChatId } = req.body;
  guard(req, fromChatId);
  const raw = await getRaw(fromChatId, messageId);
  if (!raw) return res.status(404).json({ success: false, message: 'Message not found' });
  const jid = await resolveTarget(toChatId, req.user);
  const sent = await sock.sendMessage(jid, { forward: raw });
  const msg = await addMessage(sent);
  if (msg) emitToChat(jid, 'message', msg);
  emitChat(jid);
  res.json({ success: true, message: msg });
}));

app.post('/delete', requireReady, wrap(async (req, res) => {
  const { chatId, messageId, forEveryone } = req.body;
  guard(req, chatId);
  const raw = await getRaw(chatId, messageId);
  if (!raw) return res.status(404).json({ success: false, message: 'Message not found' });
  if (forEveryone) {
    await sock.sendMessage(chatId, { delete: raw.key });
  } else {
    await pool.query('DELETE FROM messages WHERE chat_id=? AND id=?', [chatId, messageId]);
    await pool.query('DELETE FROM reactions WHERE message_id=?', [messageId]);
    emitToChat(chatId, 'message-removed', { chatId, id: messageId });
    emitChat(chatId);
  }
  res.json({ success: true });
}));

/* ───────────────────────── read receipts & presence ───────────────────────── */

app.post('/read', requireReady, wrap(async (req, res) => {
  const { chatId } = req.body;
  guard(req, chatId);
  const [rows] = await pool.query('SELECT raw FROM messages WHERE chat_id=? AND from_me=0 ORDER BY ts DESC LIMIT 100', [chatId]);
  const keys = rows.map((r) => JSON.parse(r.raw, BufferJSON.reviver).key);
  if (keys.length) await sock.readMessages(keys);
  await upsertChat(chatId, { unreadCount: 0 });
  emitChat(chatId);
  res.json({ success: true });
}));

// state: "composing" | "recording" | "paused" | "available" | "unavailable"
app.post('/presence', requireReady, wrap(async (req, res) => {
  guard(req, req.body.chatId);
  await sock.sendPresenceUpdate(req.body.state || 'composing', req.body.chatId);
  res.json({ success: true });
}));

app.post('/presence/subscribe', requireReady, wrap(async (req, res) => {
  guard(req, req.body.chatId);
  await sock.presenceSubscribe(req.body.chatId);
  res.json({ success: true });
}));

/* ───────────────────────── your original routes ───────────────────────── */

app.post('/send-text', requireReady, wrap(async (req, res) => {
  const { phoneNumber, message } = req.body;
  if (!phoneNumber || !message) return res.status(400).json({ success: false, message: 'phoneNumber and message are required' });
  await sendAndStore(await resolveTarget(phoneNumber), { text: message });
  res.json({ success: true, message: 'Text sent successfully' });
}));

app.post('/send-invoice', requireReady, upload.single('invoicePdf'), wrap(async (req, res) => {
  const { phoneNumber, invoiceNumber } = req.body;
  const file = req.file;
  if (!phoneNumber || !file) return res.status(400).json({ success: false, message: 'phoneNumber and invoicePdf file are required' });
  const jid = await resolveTarget(phoneNumber);
  await sendAndStore(jid, {
    document: file.buffer,
    mimetype: 'application/pdf',
    fileName: `Invoice_${invoiceNumber || 'bill'}.pdf`,
    caption: `Hi Customer, here's your invoice #${invoiceNumber || ''}. Thank you for your purchase!.Shop again at GripStyle.`
  }, null, { buffer: file.buffer });
  res.json({ success: true, message: 'Invoice file sent successfully' });
}));

app.post('/send-image', requireReady, wrap(async (req, res) => {
  const { phoneNumber, imageUrl, caption } = req.body;
  if (!phoneNumber || !imageUrl) return res.status(400).json({ success: false, message: 'phoneNumber and imageUrl are required' });
  if (!/^https?:\/\//i.test(String(imageUrl))) return res.status(400).json({ success: false, message: 'imageUrl must start with http:// or https://' });
  await sendAndStore(await resolveTarget(phoneNumber), { image: { url: String(imageUrl) }, caption: caption ? String(caption) : undefined });
  res.json({ success: true, message: 'Image sent successfully' });
}));

/* ───────────────────────── start ───────────────────────── */

(async () => {
  try {
    await initDb();
  } catch (e) {
    console.error('❌ Startup failed — check DB_* values and ADMIN_PHONE in .env:', e.message);
    process.exit(1);
  }
  startSock();
  server.listen(PORT, () => console.log(`WhatsApp service (Baileys + MySQL) running on port ${PORT}`));
})();