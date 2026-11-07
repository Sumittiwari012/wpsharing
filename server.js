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
  // Speeds up "chats with unread messages" lookups (inbox, stats)
  try { await pool.query('ALTER TABLE chats ADD KEY idx_unread (unread_count)'); } catch (_) { /* already exists */ }
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

  // One row per time a staff member handled a chat. This is both the "who owns it now" table
  // (status = 'active') and the history that feeds the admin dashboard.
  //   status: active | cleared (order done) | cancelled | transferred | released (sent back to inbox)
  // active_chat is set to chat_id only while active and is UNIQUE, so two people can never claim the same chat.
  await pool.query(`CREATE TABLE IF NOT EXISTS handlings (
    id INT AUTO_INCREMENT PRIMARY KEY,
    chat_id VARCHAR(80) NOT NULL,
    user_id INT NOT NULL,
    status VARCHAR(12) NOT NULL DEFAULT 'active',
    active_chat VARCHAR(80) NULL,
    started_at BIGINT NOT NULL,
    closed_at BIGINT NULL,
    note VARCHAR(255) NULL,
    transferred_from INT NULL,
    UNIQUE KEY uniq_active (active_chat),
    KEY idx_chat (chat_id),
    KEY idx_user_status (user_id, status)
  ) ${T}`);
  // "I will take care of this number": who gets future messages of a number, even after the chat was closed.
  // Set when someone claims / is transferred a chat, removed when it is released back to the inbox.
  await pool.query(`CREATE TABLE IF NOT EXISTS preferred_owners (
    chat_id VARCHAR(80) PRIMARY KEY,
    user_id INT NOT NULL,
    set_at BIGINT NOT NULL,
    KEY idx_user (user_id)
  ) ${T}`);
  await pool.query("INSERT IGNORE INTO preferred_owners (chat_id, user_id, set_at) SELECT chat_id, user_id, started_at FROM handlings WHERE status='active'");
  // One-time migration from the old admin-driven "assignments" table (ignored if it does not exist)
  try {
    await pool.query(`INSERT IGNORE INTO handlings (chat_id, user_id, status, active_chat, started_at)
                      SELECT chat_id, user_id, 'active', chat_id, assigned_at FROM assignments`);
    await pool.query('DROP TABLE assignments');
  } catch (_) { /* nothing to migrate */ }

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

  // WhatsApp "LID" ids (1234@lid) -> real phone-number ids (91xxxxxxxxxx@s.whatsapp.net). Filled automatically.
  await pool.query(`CREATE TABLE IF NOT EXISTS lid_map (
    lid VARCHAR(80) PRIMARY KEY,
    pn VARCHAR(80) NOT NULL
  ) ${T}`);

  // Small key/value table for one-time housekeeping jobs
  await pool.query(`CREATE TABLE IF NOT EXISTS app_meta (
    k VARCHAR(60) PRIMARY KEY,
    v VARCHAR(100) NOT NULL
  ) ${T}`);
  // One time only: chats that were already unread before this version are cleared, so the inbox starts with NEW messages only.
  const [resetDone] = await pool.query("SELECT 1 FROM app_meta WHERE k='unread_reset_v2'");
  if (!resetDone[0]) {
    await pool.query('UPDATE chats SET unread_count = 0');
    await pool.query("INSERT INTO app_meta (k, v) VALUES ('unread_reset_v2', '1')");
    console.log('Old unread counts cleared (one time). The inbox now lists only new incoming messages.');
  }

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

/* ───────────── LID (WhatsApp internal id) → real phone number ─────────────
   WhatsApp sometimes identifies a customer as 1234@lid instead of 91xxxxxxxxxx@s.whatsapp.net.
   We always store and use the phone-number id (the "canonical" id) so the number shows correctly
   and every event (messages, unread counts, ticks, reactions) lands on the same chat. */

const lidMap = new Map(); // 1234@lid -> 91xxxxxxxxxx@s.whatsapp.net
const bareJid = (j) => {
  const [u, s] = String(j).split('@');
  return u.split(':')[0] + '@' + s;
};
// Any id from WhatsApp or from the UI -> the id we store. Unknown LIDs stay as they are.
const canonId = (j) => (j && String(j).endsWith('@lid') ? lidMap.get(bareJid(j)) || String(j) : j);
// Number to show to the people using the inbox
const displayNumber = (jid) => numberFromJid(canonId(jid));

let mergeQueue = Promise.resolve();
const queued = (fn) => (mergeQueue = mergeQueue.then(fn).catch((e) => console.warn('lid task failed:', e.message)));

function canonicalChatJid(key) {
  const remote = String(key?.remoteJid || '');
  const alt = String(key?.remoteJidAlt || '');
  if (remote.endsWith('@lid') && alt.endsWith('@s.whatsapp.net')) {
    const lid = bareJid(remote);
    const pn = bareJid(alt);
    if (lidMap.get(lid) !== pn) learnLid(lid, pn).catch((e) => console.warn('learnLid failed:', e.message));
    return pn;
  }
  return canonId(remote); // uses earlier mappings when this message has no Alt
}

// Remember a LID → phone-number pair and merge any chat that was already stored under the LID
async function learnLid(lid, pn) {
  if (!lid || !pn) return;
  const l = bareJid(lid);
  const p = bareJid(pn);
  if (!l.endsWith('@lid') || !p.endsWith('@s.whatsapp.net')) return;
  if (lidMap.get(l) !== p) {
    lidMap.set(l, p);
    await pool.query('REPLACE INTO lid_map (lid, pn) VALUES (?,?)', [l, p]);
  }
  await queued(() => mergeChat(l, p));
}

// Move everything from the LID chat into the phone-number chat, then remove the LID chat.
async function mergeChat(from, to) {
  if (!from || !to || from === to) return;
  const [srcRows] = await pool.query('SELECT * FROM chats WHERE id=?', [from]);
  if (!srcRows[0]) return;
  const src = srcRows[0];

  await pool.query('INSERT IGNORE INTO chats (id) VALUES (?)', [to]);
  await pool.query(
    'UPDATE chats SET unread_count = unread_count + ?, last_message_time = GREATEST(last_message_time, ?), pinned = GREATEST(pinned, ?) WHERE id=?',
    [src.unread_count || 0, src.last_message_time || 0, src.pinned || 0, to]
  );

  // Messages (the chatId and mediaUrl stored inside each message are rewritten too)
  const [msgs] = await pool.query('SELECT id, data FROM messages WHERE chat_id=?', [from]);
  for (const m of msgs) {
    let data;
    try {
      data = JSON.parse(m.data);
      data.chatId = to;
      if (data.mediaUrl) data.mediaUrl = `/media/${encodeURIComponent(to)}/${encodeURIComponent(m.id)}`;
    } catch (_) { data = null; }
    try {
      if (data) await pool.query('UPDATE messages SET chat_id=?, data=? WHERE chat_id=? AND id=?', [to, JSON.stringify(data), from, m.id]);
      else await pool.query('UPDATE messages SET chat_id=? WHERE chat_id=? AND id=?', [to, from, m.id]);
    } catch (e) {
      if (e.code === 'ER_DUP_ENTRY') await pool.query('DELETE FROM messages WHERE chat_id=? AND id=?', [from, m.id]);
      else throw e;
    }
  }

  // Who is handling it
  if (assignMap.has(from)) {
    if (assignMap.has(to)) {
      await endHandling(from, 'released');
    } else {
      await pool.query('UPDATE handlings SET active_chat=? WHERE active_chat=?', [to, from]);
      assignMap.set(to, assignMap.get(from));
      assignMap.delete(from);
    }
  }
  await pool.query('UPDATE handlings SET chat_id=? WHERE chat_id=?', [to, from]);
  if (prefMap.has(from)) {
    if (!prefMap.has(to)) await setPreferred(to, prefMap.get(from));
    await clearPreferred(from);
  }

  await pool.query('DELETE FROM chats WHERE id=?', [from]);
  console.log(`Merged chat ${from} into ${to}`);
  emitToChat(from, 'chat-deleted', from);
  await emitChat(to);
}

// Run after WhatsApp connects: finds the phone number of every chat still stored under a LID and merges it.
async function backfillLids() {
  const [rows] = await pool.query("SELECT id FROM chats WHERE id LIKE '%@lid'");
  for (const c of rows) {
    let pn = lidMap.get(c.id) || null;
    if (!pn) {
      const [ms] = await pool.query('SELECT raw FROM messages WHERE chat_id=? ORDER BY ts DESC LIMIT 30', [c.id]);
      for (const m of ms) {
        try {
          const k = JSON.parse(m.raw, BufferJSON.reviver).key;
          if (k?.remoteJidAlt && String(k.remoteJidAlt).endsWith('@s.whatsapp.net')) { pn = bareJid(k.remoteJidAlt); break; }
        } catch (_) { /* skip */ }
      }
    }
    if (!pn) {
      try {
        const r = await sock?.signalRepository?.lidMapping?.getPNForLID(c.id);
        if (r) pn = bareJid(r);
      } catch (_) { /* mapping not available */ }
    }
    if (pn) await learnLid(c.id, pn);
  }
}

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
  m.pushName = null; // also hides profile names of messages stored before this change
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
    // Customers are shown by phone number only (never a contact / profile name). Groups have no number, so they keep the group name.
    name: r.id.endsWith('@g.us') ? (r.name || 'Group') : '+' + displayNumber(r.id),
    isGroup: r.id.endsWith('@g.us'),
    unreadCount: Math.max(0, r.unread_count || 0),
    lastMessageTime: r.last_message_time || 0,
    pinned: !!r.pinned,
    archived: !!r.archived,
    assignedTo: assignedInfo(r.id), // who is handling it right now (null = nobody, sits in the common inbox)
    lastMessage: last
  };
}

// onlyJid: a single chat.
// view:
//   'inbox' = NEW incoming messages only: unread AND not claimed by anybody
//   'mine'  = chats claimed by userId (they stay in the list even when read, so the conversation continues normally)
//   'all'   = every chat (admin overview, and used by emitChat for live updates)
async function getChats(onlyJid, view = 'all', userId = 0) {
  const where = ["c.id <> 'status@broadcast'"];
  const params = [];
  if (onlyJid) { where.push('c.id = ?'); params.push(onlyJid); }
  if (view === 'inbox') {
    where.push('c.unread_count > 0');
    where.push('NOT EXISTS (SELECT 1 FROM handlings h WHERE h.active_chat = c.id)');
  } else if (view === 'mine') {
    where.push('EXISTS (SELECT 1 FROM handlings h WHERE h.active_chat = c.id AND h.user_id = ?)');
    params.push(userId);
  }
  const [rows] = await pool.query(
    `SELECT c.id, c.name, c.unread_count, c.last_message_time, c.pinned, c.archived,
            ct.name AS ct_name, ct.notify AS ct_notify,
            m.data AS last_data, m.status AS last_status, m.deleted AS last_deleted
       FROM chats c
       JOIN messages m ON m.chat_id = c.id AND m.ts = (SELECT MAX(ts) FROM messages WHERE chat_id = c.id)
       LEFT JOIN contacts ct ON ct.id = c.id
      WHERE ${where.join(' AND ')}`,
    params
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

function simplify(raw, canonicalChatId = canonicalChatJid(raw?.key)) {
  if (!raw || !raw.key) return null;
  const base = {
    id: raw.key.id,
    chatId: canonicalChatId,
    fromMe: !!raw.key.fromMe,
    sender: raw.key.participant || raw.participant || raw.key.remoteJid,
    pushName: null, // we only show numbers, never WhatsApp profile names
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

// silent = true is used for bulk history imports: it stores the message but skips the extra
// read-back query (getMessage), which nobody needs while importing thousands of old messages.
async function addMessage(raw, silent = false) {
  const jid = canonicalChatJid(raw?.key);
  if (!jid || jid === 'status@broadcast' || !raw.message) return null;
  raw.messageTimestamp = toNum(raw.messageTimestamp) || Math.floor(Date.now() / 1000);

  const m = simplify(raw, jid);
  if (!m) return null;

  await upsertChat(jid, { lastMessageTime: m.timestamp });
  await pool.query(
    `INSERT INTO messages (chat_id, id, ts, from_me, status, deleted, body, data, raw)
     VALUES (?,?,?,?,?,?,?,?,?)
     ON DUPLICATE KEY UPDATE status = GREATEST(status, VALUES(status)), data = VALUES(data), raw = VALUES(raw)`,
    [jid, m.id, m.timestamp, +m.fromMe, toNum(raw.status), +m.deleted, m.text, JSON.stringify(m), JSON.stringify(raw, BufferJSON.replacer)]
  );

  if (!m.fromMe && jid.endsWith('@g.us')) fillGroupName(jid);
  if (silent) return m;
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
  // Async write: a large file no longer freezes every other request while it is being saved
  await fs.promises.writeFile(path.join(MEDIA_DIR, rel), buffer);
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
  let number = String(phoneNumber).replace(/\D/g, '').replace(/^0+/, '');
  if (number.length === 10) number = '91' + number; // default India code if missing
  return `${number}@s.whatsapp.net`;
}

const deny = (chatId) => {
  const o = assignedInfo(chatId);
  return Object.assign(new Error(o ? `Not allowed: ${o.name} is handling this chat` : 'Claim this chat first'), { status: 403 });
};

// Who may send into a chat?  The coworker who claimed it, or the admin.
// Typing a brand-new phone number in "My chats" claims it automatically if nobody has it yet.
async function resolveTarget(input, user) {
  if (!input) {
    throw Object.assign(new Error('chatId / phoneNumber is required'), { status: 400 });
  }

  const check = async (jid, autoClaim) => {
    if (!user || canSend(user, jid)) return;
    if (autoClaim && !assignMap.has(jid) && (await claimChat(jid, user.id))) return;
    throw deny(jid);
  };

  // The input is already a WhatsApp id (an old LID id from the UI is converted to the phone-number id)
  if (String(input).includes('@')) {
    const directJid = canonId(String(input));
    console.log('📤 Recipient (id given):', input, '->', directJid);
    await check(directJid, false);
    return directJid;
  }

  // A phone number was typed
  const jid = toJid(input);
  if (user && assignMap.has(jid)) await check(jid, false);

  const [found] = await sock.onWhatsApp(jid);
  console.log('📤 Recipient (number given):', input, '| registered:', found?.exists, '| Baileys jid:', found?.jid || '(none)');
  if (!found?.exists) {
    throw Object.assign(new Error('This number is not registered on WhatsApp'), { status: 400 });
  }

  const final = canonId(found.jid || jid);
  await check(final, true);
  return final;
}

// media = { buffer } optional: saves the file we just sent straight to disk
async function sendAndStore(jid, content, quotedId, media, userId) {
  const opts = quotedId ? { quoted: (await getRaw(jid, quotedId)) || undefined } : {};
  const sent = await sock.sendMessage(jid, content, opts);
  let msg = await addMessage(sent);
  if (msg && media?.buffer && MEDIA_TYPES.includes(msg.type)) await writeMedia(msg, media.buffer);
  if (msg && userId) {
    await pool.query('UPDATE messages SET sent_by=? WHERE chat_id=? AND id=?', [userId, msg.chatId, msg.id]);
    msg = await getMessage(msg.chatId, msg.id);
  }
  if (msg) emitToChat(msg.chatId, 'message', msg);
  emitChat(msg ? msg.chatId : jid);
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

/* ───────────────────────── auth, roles & chat ownership ───────────────────────── */

const digits = (v) => String(v || '').replace(/\D/g, '');
const normPhone = (v) => { let n = digits(v).replace(/^0+/, ''); if (n.length === 10) n = '91' + n; return n; }; // 10 digits -> 91 is added
const sha = (v) => crypto.createHash('sha256').update(String(v)).digest('hex');
const safeEq = (a, b) => {
  const x = Buffer.from(String(a));
  const y = Buffer.from(String(b));
  return x.length === y.length && crypto.timingSafeEqual(x, y);
};

const OTP_TTL = 5 * 60 * 1000;
const SESSION_TTL = 10 * 365 * 24 * 3600 * 1000; // ~10 years
const AUTH_CACHE_TTL = 60 * 1000; // a login is re-checked against the database at most once a minute
const assignMap = new Map();   // chat jid -> user id of the coworker handling it right now
const prefMap = new Map();     // chat jid -> user id who takes care of this number (gets its future messages)
const usersCache = new Map();  // user id -> { id, name, email, phone, role, active }
const authCache = new Map();   // token hash -> { user, exp }
const otpMsgIds = new Set();   // OTP messages we sent over WhatsApp (not stored as chats)

async function loadCaches() {
  const [users] = await pool.query('SELECT id, name, email, phone, role, active FROM users');
  usersCache.clear();
  users.forEach((u) => usersCache.set(u.id, u));
  authCache.clear(); // user details / roles may have changed
  const [rows] = await pool.query("SELECT chat_id, user_id FROM handlings WHERE status='active'");
  assignMap.clear();
  rows.forEach((a) => assignMap.set(a.chat_id, a.user_id));
  const [prefs] = await pool.query('SELECT chat_id, user_id FROM preferred_owners');
  prefMap.clear();
  prefs.forEach((a) => prefMap.set(a.chat_id, a.user_id));
  const [lids] = await pool.query('SELECT lid, pn FROM lid_map');
  lidMap.clear();
  lids.forEach((r) => lidMap.set(r.lid, r.pn));
}

async function setPreferred(chatId, userId) {
  await pool.query('REPLACE INTO preferred_owners (chat_id, user_id, set_at) VALUES (?,?,?)', [chatId, userId, Date.now()]);
  prefMap.set(chatId, userId);
}
async function clearPreferred(chatId) {
  await pool.query('DELETE FROM preferred_owners WHERE chat_id=?', [chatId]);
  prefMap.delete(chatId);
}
async function clearPreferredOf(userId) {
  await pool.query('DELETE FROM preferred_owners WHERE user_id=?', [userId]);
  for (const [c, u] of prefMap) if (u === userId) prefMap.delete(c);
}

// Anyone logged in can READ any chat they open.
// A coworker can SEND / change only the chats they handle. The admin can act on every chat
// (continue the conversation, close it, or hand it to a coworker).
const canSend = (user, chatId) => {
  if (user.role === 'admin') return true;
  return assignMap.get(chatId) === user.id;
};
const guardSend = (req, chatId) => {
  if (!canSend(req.user, chatId)) throw deny(chatId);
};
const assignedInfo = (chatId) => {
  const u = usersCache.get(assignMap.get(chatId));
  return u ? { id: u.id, name: u.name } : null;
};

// Take a chat. Atomic: the UNIQUE key on active_chat means only one person can win.
async function claimChat(chatId, userId) {
  try {
    await pool.query("INSERT INTO handlings (chat_id, user_id, status, active_chat, started_at) VALUES (?,?,'active',?,?)", [chatId, userId, chatId, Date.now()]);
  } catch (e) {
    if (e.code === 'ER_DUP_ENTRY') return false;
    throw e;
  }
  assignMap.set(chatId, userId);
  await setPreferred(chatId, userId); // from now on this number's messages come to this person
  return true;
}

// Finish the current handling with a status (cleared / cancelled / released). Returns rows changed.
async function endHandling(chatId, status, note) {
  const [r] = await pool.query(
    'UPDATE handlings SET status=?, active_chat=NULL, closed_at=?, note=? WHERE active_chat=?',
    [status, Date.now(), note ? String(note).slice(0, 255) : null, chatId]
  );
  assignMap.delete(chatId);
  return r.affectedRows;
}

// Send back to the common inbox. We bump unread to 1 so it shows up there again (the inbox lists unread, unclaimed chats).
async function releaseChat(chatId) {
  const n = await endHandling(chatId, 'released');
  await clearPreferred(chatId); // giving it back means future messages go to the common inbox again
  if (n) await pool.query('UPDATE chats SET unread_count = GREATEST(unread_count, 1) WHERE id=?', [chatId]);
  return n;
}

async function releaseAllOf(userId) {
  const [rows] = await pool.query("SELECT chat_id FROM handlings WHERE user_id=? AND status='active'", [userId]);
  for (const r of rows) {
    await releaseChat(r.chat_id);
    await emitChat(r.chat_id);
  }
}

async function transferChat(chatId, toUserId) {
  const conn = await pool.getConnection();
  try {
    await conn.beginTransaction();
    const [cur] = await conn.query('SELECT id, user_id FROM handlings WHERE active_chat=? FOR UPDATE', [chatId]);
    if (!cur[0]) { await conn.rollback(); return false; }
    const now = Date.now();
    await conn.query("UPDATE handlings SET status='transferred', active_chat=NULL, closed_at=? WHERE id=?", [now, cur[0].id]);
    await conn.query(
      "INSERT INTO handlings (chat_id, user_id, status, active_chat, started_at, transferred_from) VALUES (?,?,'active',?,?,?)",
      [chatId, toUserId, chatId, now, cur[0].user_id]
    );
    await conn.commit();
    assignMap.set(chatId, toUserId);
    await setPreferred(chatId, toUserId);
    return true;
  } catch (e) {
    await conn.rollback();
    throw e;
  } finally {
    conn.release();
  }
}

// Marks a chat read. Only as many recent incoming messages are loaded as the chat has unread
// (at least 1, at most 100) instead of always reading and parsing 100 stored messages.
async function markRead(chatId) {
  const [c] = await pool.query('SELECT unread_count FROM chats WHERE id=?', [chatId]);
  const n = Math.min(Math.max(c[0]?.unread_count || 0, 1), 100);
  const [rows] = await pool.query('SELECT raw FROM messages WHERE chat_id=? AND from_me=0 ORDER BY ts DESC LIMIT ?', [chatId, n]);
  const keys = rows.map((r) => JSON.parse(r.raw, BufferJSON.reviver).key);
  if (keys.length && sock && isReady) await sock.readMessages(keys);
  await upsertChat(chatId, { unreadCount: 0 });
}

// Every logged-in person sees the same live updates (inbox, "handled by" tags, new messages)
function emitToChat(chatId, event, payload) {
  io.emit(event, payload);
}

// Cached for AUTH_CACHE_TTL so a chat full of images does not run one login query per image.
// Logout, disabling or deleting a user, and any user change clear the cache (see loadCaches / dropAccess / logout).
async function userFromToken(token) {
  if (!token) return null;
  const h = sha(token);
  const hit = authCache.get(h);
  if (hit && hit.exp > Date.now()) return hit.user;
  const [rows] = await pool.query(
    `SELECT u.id, u.name, u.email, u.phone, u.role FROM sessions s JOIN users u ON u.id = s.user_id
      WHERE s.token_hash = ? AND s.expires_at > ? AND u.active = 1`,
    [h, Date.now()]
  );
  const user = rows[0] || null;
  if (user) authCache.set(h, { user, exp: Date.now() + AUTH_CACHE_TTL });
  else authCache.delete(h);
  return user;
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
    if (m?.key?.id) {
      otpMsgIds.add(m.key.id);
      setTimeout(() => otpMsgIds.delete(m.key.id), 60 * 1000); // only needed for a moment; keeps the set from growing forever
    }
    console.log(`OTP sent to +${user.phone} over WhatsApp`);
    return 'whatsapp';
  }
  console.log(`OTP NOT sent to +${user.phone}: WhatsApp is not connected on the server`);
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
      getMessage: async (key) => (await getRaw(canonicalChatJid(key), key.id))?.message || undefined
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
        // Fix chats that were saved under a LID id: find their phone number and merge them
        backfillLids().catch((e) => console.warn('lid backfill failed:', e.message));
      }
      if (connection === 'close') {
        isReady = false;
        io.emit('ready', false);
        const statusCode = lastDisconnect?.error?.output?.statusCode;
        const shouldReconnect = statusCode !== DisconnectReason.loggedOut;
        console.log('Connection closed. Status code:', statusCode, 'Reconnecting:', shouldReconnect);
        isStarting = false;
        if (shouldReconnect) {
          // Wait a few seconds so a flapping connection (e.g. the same login open on two servers)
          // cannot make the server reconnect in a tight loop
          setTimeout(() => startSock(), 5000);
        } else {
          await fs.promises.rm(AUTH_FOLDER, { recursive: true, force: true });
          setTimeout(() => startSock(), 2000);
        }
      }
    });

    // WhatsApp tells us which LID belongs to which phone number
    sock.ev.on('lid-mapping.update', safe(async ({ lid, pn }) => { await learnLid(lid, pn); }));

    // History WhatsApp sends right after you link the device
    sock.ev.on('messaging-history.set', safe(async ({ chats = [], contacts = [], messages = [], lidPnMappings = [] }) => {
      for (const m of lidPnMappings) await learnLid(m.lid, m.pn);
      for (const c of contacts) await upsertContact(c.id, { name: c.name, notify: c.notify });
      for (const c of chats) {
        await upsertChat(canonId(c.id), {
          name: c.name,
          // unreadCount is NOT imported: only new incoming messages count as unread
          archived: c.archived != null ? !!c.archived : undefined,
          pinned: c.pinned != null ? toNum(c.pinned) > 0 : undefined,
          lastMessageTime: toNum(c.conversationTimestamp)
        });
      }
      for (const m of messages) await addMessage(m, true); // silent: no read-back query per old message
      io.to('admin').emit('history-synced', { chats: chats.length, messages: messages.length });
    }));

    sock.ev.on('contacts.upsert', safe(async (list) => { for (const c of list) await upsertContact(c.id, { name: c.name, notify: c.notify }); }));
    sock.ev.on('contacts.update', safe(async (list) => { for (const c of list) if (c.id) await upsertContact(c.id, { name: c.name, notify: c.notify }); }));

    sock.ev.on('chats.upsert', safe(async (list) => {
      for (const c of list) {
        const id = canonId(c.id);
        await upsertChat(id, {
          name: c.name,
          // unreadCount is NOT imported: only new incoming messages count as unread
          archived: c.archived != null ? !!c.archived : undefined,
          pinned: c.pinned != null ? toNum(c.pinned) > 0 : undefined
        });
        emitChat(id);
      }
    }));
    sock.ev.on('chats.update', safe(async (list) => {
      for (const u of list) {
        if (!u.id) continue;
        const id = canonId(u.id);
        const f = {
          name: u.name,
          archived: u.archived != null ? !!u.archived : undefined,
          pinned: u.pinned != null ? toNum(u.pinned) > 0 : undefined
        };
        // Unread is counted by us from new incoming messages (see messages.upsert), so WhatsApp's increments are ignored.
        // A reset to 0 (chat read on the phone) still clears it.
        if (u.unreadCount === 0) f.unreadCount = 0;
        await upsertChat(id, f);
        emitChat(id);
      }
    }));
    sock.ev.on('chats.delete', safe(async (ids) => {
      for (const rawId of ids) {
        const id = canonId(rawId);
        await pool.query('DELETE FROM messages WHERE chat_id=?', [id]);
        await pool.query('DELETE FROM chats WHERE id=?', [id]);
        await endHandling(id, 'released');
        await clearPreferred(id);
        emitToChat(id, 'chat-deleted', id);
      }
    }));

    // New incoming / outgoing messages
    sock.ev.on('messages.upsert', safe(async ({ messages, type }) => {
      for (const raw of messages) {
        if (otpMsgIds.has(raw.key?.id)) continue;
        const msg = await addMessage(raw);
        if (!msg) continue;
        // A number somebody takes care of: a new message from it goes straight to them (not to the common inbox)
        if (type === 'notify' && !msg.fromMe && !assignMap.has(msg.chatId)) {
          const owner = usersCache.get(prefMap.get(msg.chatId));
          if (owner && owner.active && owner.role === 'agent') {
            await claimChat(msg.chatId, owner.id).catch((e) => console.warn('auto-assign failed:', e.message));
          }
        }
        // New incoming message = +1 unread. Chats that were already unread before are never added to the inbox.
        if (type === 'notify' && !msg.fromMe) await upsertChat(msg.chatId, { unreadDelta: 1 });
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
        const chatId = canonicalChatJid(key);
        if (update.status != null) {
          await pool.query('UPDATE messages SET status = GREATEST(status, ?) WHERE chat_id=? AND id=?', [update.status, chatId, key.id]);
        }
        if (update.messageStubType === WAMessageStubType.REVOKE) {
          await pool.query('UPDATE messages SET deleted=1 WHERE chat_id=? AND id=?', [chatId, key.id]);
        }
        const msg = await getMessage(chatId, key.id);
        if (msg) emitToChat(msg.chatId, 'message-update', msg);
      }
    }));

    sock.ev.on('messages.reaction', safe(async (list) => {
      for (const { key, reaction } of list) {
        const chatId = canonicalChatJid(key);
        const reactor = reaction.key?.fromMe ? 'me' : reaction.key?.participant || reaction.key?.remoteJid;
        if (reaction.text) {
          await pool.query('INSERT INTO reactions (message_id, reactor, emoji) VALUES (?,?,?) ON DUPLICATE KEY UPDATE emoji=VALUES(emoji)', [key.id, reactor, reaction.text]);
        } else {
          await pool.query('DELETE FROM reactions WHERE message_id=? AND reactor=?', [key.id, reactor]);
        }
        const r = await getReactions([key.id]);
        emitToChat(chatId, 'message-update', { id: key.id, chatId, reactions: r[key.id] || {} });
      }
    }));

    sock.ev.on('presence.update', ({ id, presences }) => {
      const chatId = canonId(id);
      emitToChat(chatId, 'presence', { chatId, presences });
    });
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

// Public, no login: used by the separate "WhatsApp Connection Setup" page to show the QR while WhatsApp is not linked.
// Safety: set WHATSAPP_NUMBER in .env. Any other number that scans this QR is unlinked again automatically.
app.get('/link/status', (req, res) => res.json({ ready: isReady, qr: isReady ? null : latestQr }));

// ── login with a code sent over WhatsApp ──
// Only numbers that exist in `users` (the admin from ADMIN_PHONE, and coworkers the admin added) can get a code.
// Any other number gets the same generic reply, but no code is created or sent.
app.post('/auth/request-otp', wrap(async (req, res) => {
  const phone = normPhone(req.body.phone);
  if (phone.length < 10) return res.status(400).json({ success: false, message: 'Enter your WhatsApp number with country code' });
  if (limited('otp:' + req.ip, 10, 10 * 60 * 1000)) return res.status(429).json({ success: false, message: 'Too many attempts. Try again later.' });
  let [rows] = await pool.query('SELECT id, name, phone, role, active FROM users WHERE phone=?', [phone]);
  if (rows[0] && !rows[0].active) rows = []; // a disabled person stays blocked
  if (!rows[0]) console.log(`OTP requested for +${phone}: not sent (number was not added by the admin, or this user is disabled)`);
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
// Everything under /admin is admin-only, including any route added later
app.use('/admin', requireAdmin);

app.get('/auth/me', (req, res) => res.json({ success: true, user: req.user, ready: isReady }));
app.post('/auth/logout', wrap(async (req, res) => {
  const h = sha(tokenOf(req));
  authCache.delete(h);
  await pool.query('DELETE FROM sessions WHERE token_hash=?', [h]);
  res.json({ success: true });
}));

app.get('/qr-status', requireAdmin, (req, res) => res.json({ ready: isReady, qr: isReady ? null : latestQr }));

// Active coworkers: the "predefined list" everybody can pick from when transferring a chat
app.get('/team', wrap(async (req, res) => {
  const [rows] = await pool.query("SELECT id, name, role, active FROM users WHERE role='agent' AND active=1 ORDER BY name");
  res.json({ success: true, users: rows });
}));

/* ───────────────────────── handling a chat: claim / close / transfer / release ───────────────────────── */

// Take a chat from the common inbox. Whoever is first wins; everybody else sees "handled by <name>".
app.post('/chats/claim', wrap(async (req, res) => {
  const chatId = canonId(req.body.chatId);
  if (!chatId) return res.status(400).json({ success: false, message: 'chatId is required' });
  const [ex] = await pool.query('SELECT 1 FROM chats WHERE id=?', [chatId]);
  if (!ex[0]) return res.status(404).json({ success: false, message: 'Chat not found' });
  if (assignMap.get(chatId) === req.user.id) return res.json({ success: true });
  if (!(await claimChat(chatId, req.user.id))) {
    const o = assignedInfo(chatId);
    return res.status(409).json({ success: false, message: o ? `${o.name} is already handling this chat` : 'Could not claim this chat' });
  }
  await markRead(chatId).catch((e) => console.warn('mark read failed:', e.message));
  await emitChat(chatId);
  res.json({ success: true });
}));

// Order finished: outcome = "cleared" (order done) or "cancelled". The chat leaves your list.
app.post('/chats/close', wrap(async (req, res) => {
  const { outcome, note } = req.body;
  const chatId = canonId(req.body.chatId);
  if (!['cleared', 'cancelled'].includes(outcome)) return res.status(400).json({ success: false, message: 'outcome must be "cleared" or "cancelled"' });
  guardSend(req, chatId);
  if (!(await endHandling(chatId, outcome, note))) return res.status(404).json({ success: false, message: 'Nobody is handling this chat' });
  await emitChat(chatId);
  res.json({ success: true });
}));

// Hand over to another coworker: the chat moves from your list to theirs.
app.post('/chats/transfer', wrap(async (req, res) => {
  const chatId = canonId(req.body.chatId);
  const to = Number(req.body.userId);
  guardSend(req, chatId);
  const t = usersCache.get(to);
  if (!t || t.role === 'admin' || !t.active) return res.status(400).json({ success: false, message: 'Choose an active coworker' });
  const current = assignMap.get(chatId);
  if (current === to) return res.status(400).json({ success: false, message: 'That coworker already has this chat' });
  if (current) {
    if (!(await transferChat(chatId, to))) return res.status(404).json({ success: false, message: 'Nobody is handling this chat' });
  } else if (!(await claimChat(chatId, to))) { // nobody had it yet: assign it straight to the coworker
    return res.status(409).json({ success: false, message: 'Could not assign this chat' });
  }
  // (No unread bump needed any more: "My chats" lists every chat the coworker handles, read or unread.)
  await emitChat(chatId);
  res.json({ success: true });
}));

// Put back into the common inbox without a result tag
app.post('/chats/release', wrap(async (req, res) => {
  const chatId = canonId(req.body.chatId);
  guardSend(req, chatId);
  if (!(await releaseChat(chatId))) return res.status(404).json({ success: false, message: 'Nobody is handling this chat' });
  await emitChat(chatId);
  res.json({ success: true });
}));

/* ───────────────────────── admin: team & dashboard ───────────────────────── */

const dropAccess = async (id) => {
  await pool.query('DELETE FROM sessions WHERE user_id=?', [id]);
  authCache.clear(); // their cached logins must stop working immediately
  io.in('user:' + id).disconnectSockets(true);
};

app.get('/admin/users', requireAdmin, wrap(async (req, res) => {
  const [rows] = await pool.query(
    `SELECT u.id, u.name, u.email, u.phone, u.role, u.active,
            (SELECT COUNT(*) FROM handlings h WHERE h.user_id = u.id AND h.status = 'active') AS chats
       FROM users u ORDER BY u.role, u.name`
  );
  res.json({ success: true, users: rows });
}));

// Who is handling which numbers right now (read-only overview for the admin).
// ?userId=N shows only that coworker's numbers. To look inside a chat, open it normally:
// GET /messages/:chatId works for the admin, but sending / closing / transferring stays with the handler.
app.get('/admin/handlers', requireAdmin, wrap(async (req, res) => {
  const uid = Number(req.query.userId) || 0;
  const [rows] = await pool.query(
    `SELECT h.chat_id, h.user_id, h.started_at, u.name AS user_name, u.phone AS user_phone,
            c.name AS chat_name, c.unread_count, c.last_message_time
       FROM handlings h
       JOIN users u ON u.id = h.user_id
       LEFT JOIN chats c ON c.id = h.chat_id
      WHERE h.status = 'active' ${uid ? 'AND h.user_id = ?' : ''}
      ORDER BY u.name, c.last_message_time DESC`,
    uid ? [uid] : []
  );
  const chats = rows.map((r) => ({
    chatId: r.chat_id,
    name: r.chat_id.endsWith('@g.us') ? (r.chat_name || 'Group') : '+' + displayNumber(r.chat_id),
    isGroup: r.chat_id.endsWith('@g.us'),
    handledBy: { id: r.user_id, name: r.user_name, phone: r.user_phone },
    since: r.started_at,
    unreadCount: Math.max(0, r.unread_count || 0),
    lastMessageTime: r.last_message_time || 0
  }));
  const byUser = {};
  for (const c of chats) {
    const g = (byUser[c.handledBy.id] ||= { id: c.handledBy.id, name: c.handledBy.name, phone: c.handledBy.phone, chats: [] });
    g.chats.push({ chatId: c.chatId, name: c.name, since: c.since, unreadCount: c.unreadCount, lastMessageTime: c.lastMessageTime });
  }
  res.json({ success: true, total: chats.length, chats, byUser: Object.values(byUser) });
}));

app.post('/admin/users', requireAdmin, wrap(async (req, res) => {
  const name = String(req.body.name || '').trim();
  const phone = normPhone(req.body.phone);
  if (!name || phone.length < 10) return res.status(400).json({ success: false, message: 'A name and a WhatsApp number (with country code) are required' });
  // If this number already exists, this just updates their name and re-enables them
  const [ex] = await pool.query('SELECT id, role FROM users WHERE phone=?', [phone]);
  if (ex[0]) {
    if (ex[0].role === 'admin') return res.status(409).json({ success: false, message: 'That is the admin number' });
    await pool.query('UPDATE users SET name=?, active=1 WHERE id=?', [name, ex[0].id]);
  } else {
    await pool.query("INSERT INTO users (name, phone, role, active) VALUES (?,?,'agent',1)", [name, phone]);
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
  if (b.active !== undefined && !b.active) {
    await dropAccess(id);
    await releaseAllOf(id); // their chats go back to the common inbox
    await clearPreferredOf(id);
  }
  await loadCaches();
  res.json({ success: true });
}));

app.delete('/admin/users/:id', requireAdmin, wrap(async (req, res) => {
  const id = Number(req.params.id);
  const u = usersCache.get(id);
  if (!u || u.role === 'admin') return res.status(404).json({ success: false, message: 'Coworker not found' });
  await dropAccess(id);
  await releaseAllOf(id);
  await clearPreferredOf(id);
  await pool.query('DELETE FROM users WHERE id=?', [id]); // handling history stays for the dashboard
  await loadCaches();
  res.json({ success: true });
}));

// Dashboard: per coworker how many chats they follow right now and how many ended as order cleared / cancelled.
// ?days=N limits the closed counts to the last N days (0 = all time).
app.get('/admin/stats', requireAdmin, wrap(async (req, res) => {
  const days = Math.max(0, Number(req.query.days) || 0);
  const since = days ? Date.now() - days * 864e5 : 0;
  const [rows] = await pool.query(
    `SELECT u.id, u.name, u.phone, u.active,
            (SELECT COUNT(*) FROM handlings a WHERE a.user_id = u.id AND a.status = 'active') AS following,
            COALESCE(SUM(h.status = 'cleared'), 0) AS cleared,
            COALESCE(SUM(h.status = 'cancelled'), 0) AS cancelled,
            COALESCE(SUM(h.status = 'transferred'), 0) AS transferred
       FROM users u
       LEFT JOIN handlings h ON h.user_id = u.id AND h.status <> 'active' AND h.closed_at >= ?
      WHERE u.role = 'agent'
      GROUP BY u.id
      ORDER BY u.name`,
    [since]
  );
  const [recent] = await pool.query(
    `SELECT h.id, h.chat_id, h.status, h.started_at, h.closed_at,
            u.name AS user_name, c.name AS name
       FROM handlings h
       LEFT JOIN users u ON u.id = h.user_id
       LEFT JOIN chats c ON c.id = h.chat_id
      ORDER BY COALESCE(h.closed_at, h.started_at) DESC
      LIMIT 40`
  );
  // Counted in SQL (was: load every chat with its last message, then count in JavaScript)
  const [[{ n: unclaimed }]] = await pool.query(
    `SELECT COUNT(*) AS n FROM chats c
      WHERE c.unread_count > 0 AND c.id <> 'status@broadcast'
        AND NOT EXISTS (SELECT 1 FROM handlings h WHERE h.active_chat = c.id)`
  );
  res.json({
    success: true,
    unclaimed: Number(unclaimed),
    agents: rows.map((r) => ({
      id: r.id, name: r.name, phone: r.phone, active: !!r.active,
      following: Number(r.following), cleared: Number(r.cleared), cancelled: Number(r.cancelled), transferred: Number(r.transferred)
    })),
    recent: recent.map((r) => ({
      id: r.id, chatId: r.chat_id, status: r.status, startedAt: r.started_at, closedAt: r.closed_at,
      user: r.user_name || 'Removed user',
      name: r.chat_id.endsWith('@g.us') ? (r.name || 'Group') : '+' + displayNumber(r.chat_id)
    }))
  });
}));

app.post('/whatsapp/logout', requireAdmin, wrap(async (req, res) => {
  try { await sock.logout(); } catch (e) { console.warn('sock.logout() error (continuing):', e.message); }
  isReady = false;
  await fs.promises.rm(AUTH_FOLDER, { recursive: true, force: true });
  await fs.promises.rm(MEDIA_DIR, { recursive: true, force: true });
  fs.mkdirSync(MEDIA_DIR, { recursive: true });
  for (const t of ['reactions', 'messages', 'contacts', 'chats', 'lid_map']) await pool.query(`DELETE FROM ${t}`);
  lidMap.clear();
  await pool.query("UPDATE handlings SET status='released', active_chat=NULL, closed_at=? WHERE status='active'", [Date.now()]);
  assignMap.clear();
  await pool.query('DELETE FROM preferred_owners');
  prefMap.clear();
  res.json({ success: true, message: 'WhatsApp disconnected and local data cleared. Scan a new QR code to reconnect.' });
  startSock();
}));

/* ───────────────────────── reading ───────────────────────── */

// GET /chats?view=inbox -> only NEW incoming chats: unread AND unclaimed
// GET /chats?view=mine  -> only chats I am handling (they stay even when read / unread = 0)
// The admin without ?view gets every chat (each one carries `assignedTo` = which coworker is talking to that client).
app.get('/chats', wrap(async (req, res) => {
  const view = req.query.view;
  let chats;
  if (view === 'inbox') chats = await getChats(null, 'inbox');
  else if (view === 'mine') chats = await getChats(null, 'mine', req.user.id);
  else if (req.user.role === 'admin') chats = await getChats(null, 'all');
  else return res.status(400).json({ success: false, message: 'view must be "inbox" or "mine"' });
  res.json({ success: true, chats });
}));

// ?limit=50&before=<unix timestamp> for scrolling up
app.get('/messages/:chatId', wrap(async (req, res) => {
  const chatId = canonId(req.params.chatId);
  const limit = Math.min(parseInt(req.query.limit) || 50, 200);
  const before = parseInt(req.query.before) || 9999999999999;
  const [rows] = await pool.query(
    'SELECT * FROM messages WHERE chat_id=? AND ts<? ORDER BY ts DESC LIMIT ?',
    [chatId, before, limit + 1]
  );
  const hasMore = rows.length > limit;
  const page = rows.slice(0, limit).reverse();
  const reacts = await getReactions(page.map((r) => r.id));
  res.json({ success: true, messages: page.map((r) => rowToMsg(r, reacts[r.id] || {})), hasMore });
}));

// Media: served from disk (downloaded on demand if missing). ?download=1 forces download
app.get('/media/:chatId/:id', wrap(async (req, res) => {
  const chatId = canonId(req.params.chatId);
  const raw = await getRaw(chatId, req.params.id);
  if (!raw) return res.status(404).json({ success: false, message: 'Message not found' });
  const msg = simplify(raw, chatId);
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
  if (!(jid in picCache)) picCache[jid] = await sock.profilePictureUrl(jid, 'image').catch(() => null);
  res.json({ success: true, url: picCache[jid] });
}));

app.get('/contacts', requireAdmin, wrap(async (req, res) => {
  const [rows] = await pool.query("SELECT id FROM contacts WHERE id LIKE '%@s.whatsapp.net'");
  res.json({
    success: true,
    contacts: rows.map((c) => ({ id: c.id, name: '+' + numberFromJid(c.id), number: numberFromJid(c.id) }))
  });
}));

/* ───────────────────────── sending (only the coworker handling the chat, or admin) ───────────────────────── */

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
  const { messageId, emoji } = req.body;
  const chatId = canonId(req.body.chatId);
  guardSend(req, chatId);
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
  const { messageId } = req.body;
  const fromChatId = canonId(req.body.fromChatId);
  const raw = await getRaw(fromChatId, messageId);
  if (!raw) return res.status(404).json({ success: false, message: 'Message not found' });
  const jid = await resolveTarget(req.body.toChatId, req.user);
  const sent = await sock.sendMessage(jid, { forward: raw });
  const msg = await addMessage(sent);
  if (msg) emitToChat(msg.chatId, 'message', msg);
  emitChat(msg ? msg.chatId : jid);
  res.json({ success: true, message: msg });
}));

app.post('/delete', requireReady, wrap(async (req, res) => {
  const { messageId, forEveryone } = req.body;
  const chatId = canonId(req.body.chatId);
  guardSend(req, chatId);
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

// Only the person handling the chat marks it read (previewing from the inbox does NOT)
app.post('/read', requireReady, wrap(async (req, res) => {
  const chatId = canonId(req.body.chatId);
  guardSend(req, chatId);
  await markRead(chatId);
  emitChat(chatId);
  res.json({ success: true });
}));

// state: "composing" | "recording" | "paused" | "available" | "unavailable"
app.post('/presence', requireReady, wrap(async (req, res) => {
  const chatId = canonId(req.body.chatId);
  guardSend(req, chatId);
  await sock.sendPresenceUpdate(req.body.state || 'composing', chatId);
  res.json({ success: true });
}));

app.post('/presence/subscribe', requireReady, wrap(async (req, res) => {
  await sock.presenceSubscribe(canonId(req.body.chatId));
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

/* ───────────────────────── housekeeping ───────────────────────── */

// Every 10 minutes: drop old rate-limit entries and cap the caches that would otherwise only ever grow.
setInterval(() => {
  const now = Date.now();
  for (const [k, list] of hits) {
    if (!list.length || now - list[list.length - 1] > 10 * 60 * 1000) hits.delete(k);
  }
  for (const [k, v] of authCache) if (v.exp <= now) authCache.delete(k);
  if (Object.keys(picCache).length > 1000) for (const k of Object.keys(picCache)) delete picCache[k];
  if (groupNameTried.size > 5000) groupNameTried.clear();
}, 10 * 60 * 1000).unref();

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