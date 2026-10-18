

/* ============================================================
 * GLOBAL_COMMAND_CRASH_PROTECTION_V2
 * ============================================================ */

process.on(
  "uncaughtException",
  error => {

    console.error(
      "[Error comando]",
      error?.stack ||
      error
    );

    /*
     * NO hacemos process.exit().
     *
     * El proceso permanece activo.
     */

  }
);

process.on(
  "unhandledRejection",
  error => {

    console.error(
      "[Error comando]",
      error?.stack ||
      error
    );

  }
);



/* ============================================================
 * GLOBAL_COMMAND_CRASH_PROTECTION_V1
 * ============================================================ */

globalThis.__lastCommandContext = null;

function __formatFatalError(error) {

  const raw =
    error?.stack ||
    error?.message ||
    String(error);

  return String(raw)
    .split("\n")
    .map(x => x.trim())
    .filter(Boolean)
    .slice(0, 3)
    .join("\n");
}

async function __reportFatalCommand(error) {

  const ctx =
    globalThis.__lastCommandContext;

  console.error(
    "❌ ERROR PROTEGIDO:",
    error?.stack || error
  );

  if (
    !ctx ||
    !ctx.sock ||
    !ctx.jid
  ) {
    return;
  }

  try {

    await ctx.sock.sendMessage(
      ctx.jid,
      {
        text:
          "[Error comando]\n*" +
          __formatFatalError(error) +
          "*"
      }
    );

  } catch (sendError) {

    console.error(
      "⚠️ ERROR ENVIANDO ERROR:",
      sendError?.message || sendError
    );

  }

}

/*
 * IMPORTANTE:
 * No hacemos process.exit().
 *
 * Una excepción no controlada ya no debe matar
 * todo el bot.
 */

process.on(
  "uncaughtException",
  error => {

    __reportFatalCommand(error)
      .catch(() => {});

  }
);

process.on(
  "unhandledRejection",
  error => {

    __reportFatalCommand(error)
      .catch(() => {});

  }
);

import http from 'http';
import { createSubBot, loadSubBots } from "./subbot-system/manager.js";
import { getSessionFolder } from "./subbot-system/session.js";

import NodeCache from '@cacheable/node-cache';
import youtubeDl from 'youtube-dl-exec';
import ffmpegInstaller from '@ffmpeg-installer/ffmpeg';
import makeWASocket, {
  makeCacheableSignalKeyStore,
  useMultiFileAuthState,
  fetchLatestBaileysVersion,
  DisconnectReason,
  downloadMediaMessage,
  Browsers
} from '@whiskeysockets/baileys';
import { Sticker, StickerTypes } from 'wa-sticker-formatter'
import P from 'pino';
import qrcode from 'qrcode-terminal';
import fs from 'fs';
import { createSongGame } from './song-game.js';
import { createCarRaceGame } from './car-race-game.js';
import {
  appendPendingAlbumImages,
  claimCar,
  createKeyedLock,
  formatCooldown,
  getCooldownRemainingMs,
  getGroupOwnedCars,
  paginateCars,
  selectQuotedAlbumImages,
  tryStartCooldown
} from './car-system-utils.js';
import {
  hasAnyPremium,
  hasXPremium,
  purchasePremium
} from './premium-utils.js';
const MAX_BOTS = 5;
const rwResultMessageIds = new Set();

const SESSIONS_FILE = './botSessions.json'

const missionLidToJid = new Map();


  if (!fs.existsSync(SESSIONS_FILE)) {
    fs.writeFileSync(SESSIONS_FILE, '[]');
}

const botSessions =
    JSON.parse(fs.readFileSync(SESSIONS_FILE));

import readline from 'readline';
import { spawn } from 'child_process';
import path from 'path';
import crypto from 'crypto';
import os from 'os';
import { execSync } from 'child_process';
import axios from 'axios';
import { imageSize } from 'image-size';
import sharp from 'sharp';
import { Worker } from 'node:worker_threads';

const YT_DLP_PATH = youtubeDl.constants.YOUTUBE_DL_PATH;
const FFMPEG_PATH = ffmpegInstaller.path;
const FFMPEG_DIRECTORY = path.dirname(FFMPEG_PATH);
const DENO_PATH = path.join(
  process.cwd(),
  'node_modules',
  '@deno',
  'win32-x64',
  'deno.exe'
);

function enhanceImageInWorker(inputBuffer, maxDimension) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(
      new URL('./hd-worker.js', import.meta.url),
      {
        workerData: { maxDimension },
        execArgv: process.execArgv.filter(
          argument => !argument.startsWith('--input-type')
        )
      }
    );
    const transferableInput = Uint8Array.from(inputBuffer);
    let settled = false;

    worker.once('message', result => {
      settled = true;
      if (result.error) {
        reject(new Error(result.error));
        return;
      }

      resolve({
        buffer: Buffer.from(result.image),
        originalWidth: result.originalWidth,
        originalHeight: result.originalHeight,
        finalWidth: result.finalWidth,
        finalHeight: result.finalHeight
      });
    });
    worker.once('error', error => {
      settled = true;
      reject(error);
    });
    worker.once('exit', code => {
      if (!settled && code !== 0) {
        reject(new Error(`El worker de mejora terminó con código ${code}.`));
      } else if (!settled) {
        reject(new Error('El worker de mejora terminó sin devolver una imagen.'));
      }
    });
    worker.postMessage(
      { inputBuffer: transferableInput.buffer },
      [transferableInput.buffer]
    );
  });
}


async function prepareHdImage(
  inputBuffer,
  maxDimension
) {
  return enhanceImageInWorker(inputBuffer, maxDimension);
}


async function prepareHd8Image(
  inputBuffer
) {
  return enhanceImageInWorker(inputBuffer, 7680);
}


function unwrapImageMessage(message) {
  let content = message;

  while (content) {
    if (content.imageMessage) return content;
    content =
      content.ephemeralMessage?.message ||
      content.viewOnceMessage?.message ||
      content.viewOnceMessageV2?.message ||
      content.documentWithCaptionMessage?.message;
  }

  return null;
}

function unwrapAlbumMessage(message) {
  let content = message;
  while (content) {
    if (content.albumMessage) return content.albumMessage;
    content =
      content.ephemeralMessage?.message ||
      content.viewOnceMessage?.message ||
      content.viewOnceMessageV2?.message ||
      content.documentWithCaptionMessage?.message;
  }
  return null;
}

function unwrapVideoMessage(message) {
  let content = message;
  while (content) {
    if (content.videoMessage) return content;
    content =
      content.ephemeralMessage?.message ||
      content.viewOnceMessage?.message ||
      content.viewOnceMessageV2?.message ||
      content.documentWithCaptionMessage?.message;
  }
  return null;
}

function getQuotedImageMessage(
  msg,
  jid,
  sender
) {
  const directImage = unwrapImageMessage(msg.message);
  if (directImage) {
    return { ...msg, message: directImage };
  }

  const contextInfo =
    msg.message?.extendedTextMessage?.contextInfo ||
    msg.message?.imageMessage?.contextInfo ||
    msg.message?.videoMessage?.contextInfo;
  const quotedImage = unwrapImageMessage(contextInfo?.quotedMessage);

  if (quotedImage) {
    return {
      key: {
        remoteJid: jid,
        id: contextInfo.stanzaId,
        participant: contextInfo.participant
      },
      message: quotedImage
    };
  }

  const senderAliases = new Set([sender]);
  const mappedPhoneJid = missionLidToJid.get(sender);
  if (mappedPhoneJid) {
    senderAliases.add(mappedPhoneJid);
  } else {
    for (const [lid, phoneJid] of missionLidToJid) {
      if (phoneJid === sender) {
        senderAliases.add(lid);
      }
    }
  }

  const cachedImages = [...senderAliases]
    .flatMap(alias => pendingAlbums[alias] || []);
  const recentImage = cachedImages
    .reverse()
    .find(image =>
      Date.now() - image.time < 300000 &&
      image.msg?.key?.remoteJid === jid &&
      Boolean(unwrapImageMessage(image.msg?.message))
    );

  if (recentImage) {
    return {
      ...recentImage.msg,
      message: unwrapImageMessage(recentImage.msg.message)
    };
  }

  return null;
}


async function downloadQuotedImage(
  msg,
  jid,
  sender
) {

  const quotedMsg =
    getQuotedImageMessage(
      msg,
      jid,
      sender
    );

  if (!quotedMsg) {
    throw new Error(
    'NO_IMAGE_AVAILABLE'
    );
  }

  const imageBuffer =
    await downloadMediaMessage(
      quotedMsg,
      'buffer',
      {}
    );

  if (
    !imageBuffer ||
    !Buffer.isBuffer(imageBuffer)
  ) {
    throw new Error(
      'IMAGE_DOWNLOAD_FAILED'
    );
  }

  return imageBuffer;
}


function buildHdCaption(
  originalWidth,
  originalHeight,
  finalWidth,
  finalHeight
) {

  return (
`（＾ω＾）𝒇𝒐𝒕𝒐 𝒎𝒆𝒋𝒐𝒓𝒂𝒅𝒐 𝒄𝒐𝒏 𝒆𝒙𝒊𝒕𝒐

𝒄𝒂𝒍𝒊𝒅𝒂𝒅 𝒂𝒄𝒕𝒖𝒂𝒍 ➢ \`${finalWidth}𝐱${finalHeight}\`
𝒄𝒂𝒍𝒊𝒅𝒂𝒅 𝒂𝒏𝒕𝒆𝒓𝒊𝒐𝒓 ➢ \`${originalWidth}𝐱${originalHeight}\``
  );
}

function getHdErrorMessage(error) {
  if (error instanceof Error && error.message === 'NO_IMAGE_AVAILABLE') {
    return 'Envía una imagen antes del comando o responde directamente a la foto con /hd, /hd2 o /hd8.';
  }

  return `No se pudo mejorar la imagen: ${
    error instanceof Error ? error.message : String(error)
  }`;
}
import {
  searchPinImages,
  downloadPinImages
} from './lib/pin-search.js';
//import { startSecondary } from "./secondary";
import {
  carsCache,
  carMap,
  loadCars,
  saveCars,
  handleCleanImgV,
  getRandomCar,
  getRandomCarImage,
  CAR_IMAGES,
  CARS_FILE,
  CAR_SERIES
} from "./vehicle-system.js";
import {
  iniciarBackupAutomatico,
  crearCopia,
  listarCopias,
  restaurarMayor
} from "./gacha-backup-system.mjs";

import {
  getGelbooruImage,
  getDanbooruImage,
  downloadDanbooruImage,
  getGelbooruApiImage,
  getGelbooruApiImageCandidates,
  downloadImage,
  downloadGelbooruImage,
  searchDanbooruTags
} from './lib/gelbooru.js';

import {
  createManualTag,
  deleteManualTag,
  getManualTag,
  normalizeManualTag,
  addManualTagImages,
  captureManualTagImage,
  getManualTagPendingImages,
  consumeManualTagImages
} from "./lib/manual-tags.js";

const ACTIONS_PATH = "./actions";

const gelbooruCooldowns = new Map();

function booruDisplayName(tag) {
  return String(tag || '')
    .trim()
    .replace(/_/g, ' ')
    .replace(/\s+/g, ' ')
    .replace(/\b\w/g, char => char.toUpperCase());
}

function booruFormatSize(bytes) {
  const value = Number(bytes);

  if (!Number.isFinite(value) || value < 0) {
    return 'Desconocido';
  }

  const units = ['B', 'KB', 'MB', 'GB'];
  let size = value;
  let unit = 0;

  while (size >= 1024 && unit < units.length - 1) {
    size /= 1024;
    unit++;
  }

  return `${size.toFixed(2)} ${units[unit]}`;
}

function booruGetDimensions(buffer) {
  try {
    const result = imageSize(buffer);

    if (
      result &&
      Number.isFinite(result.width) &&
      Number.isFinite(result.height)
    ) {
      return `${result.width}x${result.height}`;
    }
  } catch (error) {
    console.warn(
      'BOORU DIMENSIONS ERROR:',
      error?.message || error
    );
  }

  return 'Desconocida';
}

function booruSourceFromPost(post) {
  if (!post || typeof post !== 'object') {
    return '';
  }

  const copyright =
    post.tag_string_copyright ||
    post.copyright ||
    post.source_name ||
    '';

  if (Array.isArray(copyright)) {
    return copyright
      .map(value => String(value || '').trim())
      .filter(Boolean)
      .join(', ');
  }

  return String(copyright || '')
    .trim()
    .replace(/_/g, ' ');
}

function booruCaption(tag, buffer, source = '') {
  const lines = [
    `❀ *𝙽𝚘𝚖𝚋𝚛𝚎* » \`${booruDisplayName(tag)}\``,
    `☆ *𝚃𝚊𝚐* » \`${String(tag || '').trim()}\``
  ];

  const cleanSource = String(source || '').trim();

  if (cleanSource) {
    lines.push(`❖ 𝙵𝚞𝚎𝚗𝚝𝚎 » ${cleanSource}`);
  }

  lines.push(
    `⍟ *𝙲𝚊𝚕𝚒𝚍𝚊𝚍* » \`${booruGetDimensions(buffer)}\``,
    `⌬ *𝙿𝚎𝚜𝚘* » \`${booruFormatSize(buffer.length)}\``
  );

  return lines.join('\n');
}


function getAction(action) {

    const file = path.join(
        ACTIONS_PATH,
        `${action}.json`
    );

    if (!fs.existsSync(file)) return null;

    return JSON.parse(
        fs.readFileSync(file, "utf8")
    );

}

function randomGif(action) {

    return action.gifs[
        Math.floor(
            Math.random() * action.gifs.length
        )
    ];

}

// ━━━━━━━ CONFIGURACIÓN DE RUTAS ━━━━━━━
const SESSION_PATH = './auth-main';
const TEMP_DIR = path.join(process.cwd(), 'temp-video');
const CACHE_DIR = './cache';
const AUDIO_CACHE = path.join(CACHE_DIR, 'audio');
const VIDEO_CACHE = path.join(CACHE_DIR, 'video');
const DB_FILE = './database.json';

// ━━━━━━━ PROTECCIÓN AUTOMÁTICA DE DATABASE ━━━━━━━
// DATABASE_BACKUP_SYSTEM_V1

const DB_BACKUP_FILE = './database.backup.json';
const DB_BACKUP_TMP = './database.backup.tmp.json';


// Cuenta datos de forma recursiva.
// Se excluye runtimeMeta porque cambia automáticamente al iniciar.
function contarDatosDatabase(valor, ruta = '') {
  if (ruta === 'runtimeMeta') {
    return 0;
  }

  if (Array.isArray(valor)) {
    return valor.reduce(
      (total, item, index) =>
        total + contarDatosDatabase(item, `${ruta}[${index}]`),
      0
    );
  }

  if (valor && typeof valor === 'object') {
    return Object.entries(valor).reduce(
      (total, [clave, contenido]) =>
        total + contarDatosDatabase(
          contenido,
          ruta ? `${ruta}.${clave}` : clave
        ),
      0
    );
  }

  return valor === undefined ? 0 : 1;
}

function leerDatabaseSegura(archivo) {
  try {
    if (!fs.existsSync(archivo)) {
      return null;
    }

    const contenido = fs.readFileSync(archivo, 'utf8');

    if (!contenido.trim()) {
      return null;
    }

    const datos = JSON.parse(contenido);

    if (!datos || typeof datos !== 'object') {
      return null;
    }

    return datos;
  } catch {
    return null;
  }
}

function sincronizarBackupDatabase() {
  try {
    const databaseActual =
      leerDatabaseSegura(DB_FILE);

    const backupActual =
      leerDatabaseSegura(DB_BACKUP_FILE);

    if (!databaseActual) {
      console.log(
        '[DATABASE BACKUP] Database inválida. No se actualizó el backup.'
      );
      return false;
    }

    const datosActuales =
      contarDatosDatabase(databaseActual);

    if (!backupActual) {
      console.log(
        `[DATABASE BACKUP] Creando backup: ${datosActuales} datos.`
      );

      return crearBackupDatabase();
    }

    const datosBackup =
      contarDatosDatabase(backupActual);

    if (datosActuales < datosBackup) {
      console.log(
        `[DATABASE PROTECTION] Pérdida detectada: Database ${datosActuales} | Backup ${datosBackup}`
      );

      fs.copyFileSync(
        DB_BACKUP_FILE,
        DB_FILE
      );

      console.log(
        '[DATABASE PROTECTION] Database restaurada desde el backup.'
      );

      return true;
    }

    if (datosActuales > datosBackup) {
      console.log(
        `[DATABASE BACKUP] Nuevo dato detectado: ${datosBackup} → ${datosActuales}`
      );

      return crearBackupDatabase();
    }

    return true;
  } catch (error) {
    console.error(
      '[DATABASE BACKUP] ERROR al sincronizar:',
      error
    );

    return false;
  }
}

function crearBackupDatabase() {
  try {
    const databaseActual = leerDatabaseSegura(DB_FILE);

    if (!databaseActual) {
      console.log(
        '[DATABASE BACKUP] No se creó backup: database.json no es válido.'
      );
      return false;
    }

    const datosActuales =
      contarDatosDatabase(databaseActual);

    const backupAnterior =
      leerDatabaseSegura(DB_BACKUP_FILE);

    const datosBackup =
      backupAnterior
        ? contarDatosDatabase(backupAnterior)
        : 0;

    // Si el backup ya representa exactamente la misma cantidad,
    // no escribimos nada innecesariamente.
    if (
      backupAnterior &&
      datosActuales === datosBackup
    ) {
      return true;
    }

    const contenidoBackup =
      JSON.stringify(databaseActual, null, 2);

    // Primero escribimos un archivo temporal.
    fs.writeFileSync(
      DB_BACKUP_TMP,
      contenidoBackup,
      'utf8'
    );

    // Verificamos que el temporal sea un JSON válido.
    const verificacion =
      leerDatabaseSegura(DB_BACKUP_TMP);

    if (!verificacion) {
      try {
        fs.unlinkSync(DB_BACKUP_TMP);
      } catch {}

      console.log(
        '[DATABASE BACKUP] ERROR: el backup temporal no es válido.'
      );

      return false;
    }

    // Solo ahora reemplazamos el backup anterior.
    fs.renameSync(
      DB_BACKUP_TMP,
      DB_BACKUP_FILE
    );

    console.log(
      `[DATABASE BACKUP] Backup actualizado: ${datosActuales} datos.`
    );

    return true;
  } catch (error) {
    console.error(
      '[DATABASE BACKUP] ERROR:',
      error
    );

    try {
      if (fs.existsSync(DB_BACKUP_TMP)) {
        fs.unlinkSync(DB_BACKUP_TMP);
      }
    } catch {}

    return false;
  }
}

function protegerDatabaseAlIniciar() {
  try {
    const databaseActual =
      leerDatabaseSegura(DB_FILE);

    const backup =
      leerDatabaseSegura(DB_BACKUP_FILE);

    // No existe database.json válida.
    // Si tenemos un backup válido, lo restauramos.
    if (!databaseActual) {
      if (backup) {
        fs.copyFileSync(
          DB_BACKUP_FILE,
          DB_FILE
        );

        console.log(
          '[DATABASE PROTECTION] database.json inválida o perdida.'
        );
        console.log(
          '[DATABASE PROTECTION] Database restaurada desde el backup.'
        );

        return true;
      }

      console.log(
        '[DATABASE PROTECTION] No existe un backup válido para restaurar.'
      );

      return false;
    }

    const datosActuales =
      contarDatosDatabase(databaseActual);

    // Primera ejecución: todavía no existe backup.
    if (!backup) {
      console.log(
        `[DATABASE PROTECTION] Creando backup inicial: ${datosActuales} datos.`
      );

      return crearBackupDatabase();
    }

    const datosBackup =
      contarDatosDatabase(backup);

    console.log(
      `[DATABASE PROTECTION] Database: ${datosActuales} | Backup: ${datosBackup}`
    );

    // La database activa perdió datos.
    if (datosActuales < datosBackup) {
      fs.copyFileSync(
        DB_BACKUP_FILE,
        DB_FILE
      );

      console.log(
        '[DATABASE PROTECTION] Pérdida de datos detectada.'
      );
      console.log(
        '[DATABASE PROTECTION] Database restaurada desde el backup.'
      );

      return true;
    }

    // La database actual tiene datos nuevos.
    if (datosActuales > datosBackup) {
      console.log(
        '[DATABASE PROTECTION] Hay datos nuevos. Actualizando backup.'
      );

      return crearBackupDatabase();
    }

    console.log(
      '[DATABASE PROTECTION] Database y backup están sincronizados.'
    );

    return true;
  } catch (error) {
    console.error(
      '[DATABASE PROTECTION] ERROR durante la comprobación inicial:',
      error
    );

    return false;
  }
}

// Restauración/comprobación ANTES de cargar database.json.
protegerDatabaseAlIniciar();




function formatearPesoDatabase(bytes) {
  if (!Number.isFinite(bytes) || bytes <= 0) {
    return '0B';
  }

  if (bytes < 1024) {
    return `${bytes}B`;
  }

  if (bytes < 1024 * 1024) {
    return `${(bytes / 1024).toFixed(2)}KB`;
  }

  if (bytes < 1024 * 1024 * 1024) {
    return `${(bytes / (1024 * 1024)).toFixed(2)}MB`;
  }

  return `${(bytes / (1024 * 1024 * 1024)).toFixed(2)}GB`;
}

function contarDatosEstructuraDatabase(valor) {
  if (Array.isArray(valor)) {
    return valor.length;
  }

  if (valor && typeof valor === 'object') {
    return Object.keys(valor).length;
  }

  return 1;
}

function obtenerPesoEstructuraDatabase(valor) {
  try {
    return Buffer.byteLength(
      JSON.stringify(valor),
      'utf8'
    );
  } catch {
    return 0;
  }
}

function obtenerInfoArchivoDatabase(archivo) {
  try {
    if (!fs.existsSync(archivo)) {
      return null;
    }

    const contenido = fs.readFileSync(
      archivo,
      'utf8'
    );

    if (!contenido.trim()) {
      return null;
    }

    const datos = JSON.parse(contenido);

    return {
      datos: contarDatosDatabase(datos),
      peso: fs.statSync(archivo).size,
      estructura: datos
    };
  } catch {
    return null;
  }
}

async function handleInfoData(sock, msg, sender) {
  const database = obtenerInfoArchivoDatabase(DB_FILE);
  const backup = obtenerInfoArchivoDatabase(DB_BACKUP_FILE);

  if (!database) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`(☆^ー^☆) 𝚒𝚗𝚏𝚘𝚛𝚖𝚊𝚌𝚒𝚘𝚗 𝚜𝚘𝚋𝚛𝚎 𝚍𝚊𝚝𝚊𝚋𝚊𝚜𝚎.

> 𝚍𝚊𝚝𝚊𝚋𝚊𝚜𝚎.𝚓𝚜𝚘𝚗 𝚗𝚘 𝚍𝚒𝚜𝚙𝚘𝚗𝚒𝚋𝚕𝚎.`
      }
    );
  }

  let texto =
`(☆^ー^☆) 𝚒𝚗𝚏𝚘𝚛𝚖𝚊𝚌𝚒𝚘𝚗 𝚜𝚘𝚋𝚛𝚎 𝚍𝚊𝚝𝚊𝚋𝚊𝚜𝚎.
> 𝚍𝚊𝚝𝚊𝚋𝚊𝚜𝚎.𝚓𝚜𝚘𝚗 ${database.datos.toLocaleString('en-US')} 𝚍𝚊𝚝𝚘𝚜 | peso ${formatearPesoDatabase(database.peso)}
> 𝚍𝚊𝚝𝚊𝚋𝚊𝚜𝚎.𝚋𝚊𝚌𝚔𝚞𝚙.𝚓𝚜𝚘𝚗 `;

  if (backup) {
    texto +=
      `${backup.datos.toLocaleString('en-US')} 𝚍𝚊𝚝𝚘𝚜 | peso ${formatearPesoDatabase(backup.peso)}`;
  } else {
    texto += '𝚗𝚘 𝚎𝚡𝚒𝚜𝚝𝚎';
  }

  texto += `

𝙴𝚜𝚝𝚛𝚞𝚌𝚝𝚞𝚛𝚊.`;

  for (const [nombre, valor] of Object.entries(database.estructura)) {
    const cantidad =
      contarDatosEstructuraDatabase(valor);

    const peso =
      obtenerPesoEstructuraDatabase(valor);

    texto +=
      `

> 𝚞𝚜𝚎𝚛𝚜: 𝚍𝚊𝚝𝚘𝚜`;

    texto = texto.slice(0, -(`

> 𝚞𝚜𝚎𝚛𝚜: 𝚍𝚊𝚝𝚘𝚜`).length);

    texto +=
      `

> 𝚍${nombre}: ${cantidad.toLocaleString('en-US')} 𝚍𝚊𝚝𝚘𝚜 | peso ${formatearPesoDatabase(peso)}`;
  }

  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text: texto
    }
  );
}

const GACHA_PATH = '.';
const GACHA_IMAGES = path.join(GACHA_PATH, 'images');
const GACHA_VIDEOS = path.join(GACHA_PATH, 'videos');
const IMPORT_PATH = path.join(GACHA_PATH, 'import');
const CHARACTERS_FILE = path.join(GACHA_PATH, 'characters.json');
const VIDEOS_FILE = path.join(GACHA_PATH, 'videos.json');
const HASHES_FILE = "./actions/hashes.json";

if (!fs.existsSync(HASHES_FILE)) {
    fs.writeFileSync(HASHES_FILE, "{}");
}

const actionHashes =
    JSON.parse(
        fs.readFileSync(HASHES_FILE)
    );
const SERIES_DIR = path.join(GACHA_PATH, 'series');
const PENDING_DIR =
  path.join(
    GACHA_PATH,
    'pending'
  );
const activeBots = new Map();
const SUBBOTS_DIR = './subbots';

if (!fs.existsSync(SUBBOTS_DIR)) {
  fs.mkdirSync(SUBBOTS_DIR, { recursive:true });
}

// Crear carpetas necesarias
for (const dir of [
TEMP_DIR,
AUDIO_CACHE,
VIDEO_CACHE,
'./subbots',
GACHA_PATH,
GACHA_IMAGES,
GACHA_VIDEOS,
IMPORT_PATH,
SERIES_DIR,
PENDING_DIR
]) {
if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

// ━━━━━━━ BASE DE DATOS ━━━━━━━
let db = {
  users: {},
  banners: {},
  subbots: {},
  lastRob: 0,
  groups: {},
  prefix: '/',
  globalOff: false,
  stats: { totalCommands: 0 },
  globalCooldowns: { vote: {} }
};

if (fs.existsSync(DB_FILE)) {
  try {
    db = { ...db, ...JSON.parse(fs.readFileSync(DB_FILE, 'utf-8')) };
  } catch {}
}

db.maintenanceCommands ??= {};

db.rwpPrice ??= 5000000;
db.rwpMultiplier ??= 2;
db.staffPrefixes ??= {};
db.staffCommands ??= [];
db.secondaryOwners ??= [
  '256439998255240@lid'
];
db.staffNames ??= {};
db.eventsGroup ??= null;
db.missionLidToJid ??= {};
for (const [lid, jid] of Object.entries(db.missionLidToJid)) {
  if (lid.endsWith('@lid') && typeof jid === 'string' && jid) {
    missionLidToJid.set(lid, jid);
  }
}
db.primaryOwner ??= null;
db.suggestLogs ??= null;
db.menuCommands ??= {};
db.menuCommands.carrera ??= {
  description: 'Participa en una carrera de autos por grupo.',
  category: 'juegos'
};
db.menuCommands.select ??= {
  description: 'Elige un auto reclamado para la carrera.',
  category: 'juegos'
};
db.menuCommands.yac ??= {
  description: 'Confirma tu auto y queda listo para correr.',
  category: 'juegos'
};
db.menuCommands.setcarcv ??= {
  description: 'Registra la aceleración de un auto. Solo owner.',
  category: 'bot'
};
db.menuCommands.garaje ??= {
  description: 'Muestra tus autos reclamados en este grupo.',
  category: 'juegos'
};
db.menuCommands.setcaracceleration ??= {
  description: 'Registra la aceleración numérica de un auto. Solo owner.',
  category: 'bot'
};
db.menuCommands.setcarcv.description =
  'Alias antiguo para registrar la aceleración numérica de un auto. Solo owner.';
db.seriesOwners ??= {};
db.commandDesigns ??= {};

db.creatingLogs ??= null;
db.runtimeMeta ??= {
  startedAt: 0,
  starts: 0
};
db.runtimeMeta.startedAt = Date.now();
db.runtimeMeta.starts =
  Number(db.runtimeMeta.starts || 0) + 1;


db.addpQueue ??= {};

/*
 * ============================================================
 * ADDP - LIMPIEZA DE LOCKS HUÉRFANOS AL INICIAR
 * ============================================================
 *
 * Un proceso anterior puede haber quedado con:
 *
 *   addpTransition = true
 *   addpBusy = true
 *
 * pero ese scheduler ya no existe después de reiniciar.
 *
 * No tocar:
 *   - index
 *   - personajes
 *   - retries
 *   - esperando=true
 *
 * Solo liberar una transición que quedó persistida
 * sin estar esperando una respuesta.
 */

for (const [queueJid, addpData] of Object.entries(db.addpQueue || {})) {
  if (!addpData) continue;

  if (
    addpData.addpTransition === true &&
    addpData.esperando !== true
  ) {
    console.log(
      " ADDP: limpiando transición huérfana:",
      queueJid
    );

    addpData.addpTransition = false;
    addpData.addpTransitionOwner = null;
    addpData.addpBusy = false;

    if (addpData.timer) {
      clearTimeout(addpData.timer);
      addpData.timer = null;
    }
  }
}



/*
 * ============================================================
 * ADDP - LIMPIEZA DE LOCKS HUÉRFANOS AL INICIAR
 * ============================================================
 *
 * Un proceso anterior puede haber quedado con:
 *
 *   addpTransition = true
 *   addpBusy = true
 *
 * pero ese scheduler ya no existe después de reiniciar.
 *
 * No tocar:
 *   - index
 *   - personajes
 *   - retries
 *   - esperando=true
 *
 * Solo liberar una transición que quedó persistida
 * sin estar esperando una respuesta.
 */

for (const [queueJid, addpData] of Object.entries(db.addpQueue || {})) {
  if (!addpData) continue;

  if (
    addpData.addpTransition === true &&
    addpData.esperando !== true
  ) {
    console.log(
      " ADDP: limpiando transición huérfana:",
      queueJid
    );

    addpData.addpTransition = false;
    addpData.addpTransitionOwner = null;
    addpData.addpBusy = false;

    if (addpData.timer) {
      clearTimeout(addpData.timer);
      addpData.timer = null;
    }
  }
}



db.inviteLogs ??= null;
db.pendingInvites ??= {};
db.suggestStats ??= {};
db.pendingCharacters ??= [];
db.pendingCharacterId ??= 1;
db.seriesAliases ??= {};
db.seriesInfoCache ??= {};
db.pendingSeriesChecks ??= {};
db.pendingMergeSeries ??= {};
db.pendingDeleteSeries ??= {};
db.staffStats ??= {};
db.waifus ??= {};
db.subBots ??= {};
db.registeredUsers ??= null;
db.registeredGroups ??= null;
db.primaryBots ??= {};
db.characterAudios ??= {};
db.rwpCooldown = db.rwpCooldown || 10;
db.rwpCooldownType = db.rwpCooldownType || "m";

db.rwpChances = db.rwpChances || {
  "10": 200000,
  "20": 5000000
};


if (!db.modWarns) db.modWarns = {};
if (!db.luckShop) {

  db.luckShop = {

    discount: {
      percent: 0,
      expires: 0
    },

    multiplier: {
      value: 1,
      expires: 0
    }

  };

}
if (!db.modWarnLimit) db.modWarnLimit = 5;
if (!db.bannedUsers) db.bannedUsers = {};
if (!db.xpBoost) {
  db.xpBoost = {
    multiplier: 1,
    expires: 0
  };
}

let saveQueue = Promise.resolve();

let xpGain = 10;

function saveNow() {
  saveDB();
}

function getFileHash(buffer) {

    return crypto
        .createHash("sha256")
        .update(buffer)
        .digest("hex");

}

function backupDB() {
  const dir = './backups';

  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir);
  }

  const fecha =
    new Date()
      .toISOString()
      .replace(/:/g,'-');

  fs.copyFileSync(
    './db.json',
    `${dir}/db-${fecha}.json`
  );
}

// ================================
// SISTEMA DE ACCIONES LOCALES
// ================================

const ACTIONS_DIR = "./actions";

if (!fs.existsSync(ACTIONS_DIR)) {
    fs.mkdirSync(ACTIONS_DIR, { recursive: true });
}

function getActionFolder(action) {
    return path.join(ACTIONS_DIR, action.toLowerCase());
}

function ensureActionFolder(action) {

    const folder = getActionFolder(action);

    if (!fs.existsSync(folder)) {
        fs.mkdirSync(folder, { recursive: true });
    }

    const dataFile = path.join(folder, "data.json");

    if (!fs.existsSync(dataFile)) {

        fs.writeFileSync(
            dataFile,
            JSON.stringify({
                message: ""
            }, null, 4)
        );

    }

    return folder;

}

function getRandomActionGif(action) {

    const folder = getActionFolder(action);

    if (!fs.existsSync(folder))
        return null;

    const gifs = fs.readdirSync(folder).filter(file =>
        file.endsWith(".gif") ||
        file.endsWith(".mp4") ||
        file.endsWith(".webp")
    );

    if (!gifs.length)
        return null;

    return path.join(
        folder,
        gifs[
            Math.floor(
                Math.random() * gifs.length
            )
        ]
    );

}

function getActionMessage(action) {

    const dataFile =
        path.join(
            getActionFolder(action),
            "data.json"
        );

    if (!fs.existsSync(dataFile))
        return "";

    try {

        return JSON.parse(
            fs.readFileSync(dataFile, "utf8")
        ).message || "";

    } catch {

        return "";

    }

}

function updateLuckShop() {

  const now = Date.now();

  // DESCUENTO

  if (now >= db.luckShop.discount.expires) {

    const r = Math.random();

    let percent = 0;

    if (r < 0.02)
      percent = 30;

    else if (r < 0.10)
      percent = 20;

    else if (r < 0.25)
      percent = 15;

    else if (r < 0.50)
      percent = 8;

    db.luckShop.discount.percent = percent;

    db.luckShop.discount.expires =
      now + (25 * 60 * 1000);

  }

  // MULTIPLICADOR

  if (now >= db.luckShop.multiplier.expires) {

    const r = Math.random();

    let value = 1;

    if (r < 0.05)
      value = 3;

    else if (r < 0.30)
      value = 2;

    db.luckShop.multiplier.value = value;

    db.luckShop.multiplier.expires =
      now + (35 * 60 * 1000);

  }

}

const profilePhotoCache = new Map();

async function getBestProfilePhoto(jid, preferredSock = sock) {

    const cache = profilePhotoCache.get(jid);

    if (
        cache &&
        (Date.now() - cache.time) < 10 * 60 * 1000
    ) {
        return cache.url;
    }

    let url = null;

    try {
        url =
            await preferredSock.profilePictureUrl(
                jid,
                "image"
            );
    } catch (error) {
        console.log(
            '[PROFILE-PHOTO-ERROR]',
            {
                jid,
                message: error?.message,
                statusCode: error?.statusCode,
                data: error?.data
            }
        );
    }

    if (url) {
        profilePhotoCache.set(jid, {
            url,
            time: Date.now()
        });
    }

    return url;
}

function xpForLevel(level) {
  const n = Math.max(1, Math.floor(Number(level) || 1));
  return 30000 * (n - 1) + 5 * (n - 1) * (n - 2);
}

// Funciones auxiliares para formateo de tiempo y numeros
function formatTimeRemaining(ms) {
  if (ms <= 0) return 'Ahora.';
  
  const seconds = Math.floor(ms / 1000);
  const minutes = Math.floor(seconds / 60);
  const hours = Math.floor(minutes / 60);
  const days = Math.floor(hours / 24);
  
  if (days > 0) {
    return days + ' dias ' + (hours % 24) + ' horas ' + (minutes % 60) + ' minutos';
  } else if (hours > 0) {
    return hours + ' horas ' + (minutes % 60) + ' minutos ' + (seconds % 60) + ' segundos';
  } else if (minutes > 0) {
    return minutes + ' minutos ' + (seconds % 60) + ' segundos';
  } else {
    return seconds + ' segundos';
  }
}

function formatNumber(num) {
  return num.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ",");
}

function getRemainingTime(lastTime, cooldown, hasPremium) {
  const now = Date.now();
  const elapsed = now - lastTime;
  const actualCooldown = hasPremium ? cooldown * 0.7 : cooldown;
  const remaining = actualCooldown - elapsed;
  return remaining > 0 ? remaining : 0;
}

let saveDBQueue = Promise.resolve();

function saveDB() {
  saveDBQueue = saveDBQueue
    .then(() =>
      fs.promises.writeFile(
        DB_FILE,
        JSON.stringify(
          db,
          (key, value) => {
            if (key === "timer") return null;
            return value;
          },
          2
        )
      )
    )
    .then(() => {
      sincronizarBackupDatabase();
    })
    .catch(console.error);

  return saveDBQueue;
}


console.log(
  '[STARTUP] Bot iniciado:',
  new Date(db.runtimeMeta.startedAt).toISOString(),
  '| arranques registrados:',
  db.runtimeMeta.starts
);

saveDB();
setInterval(saveDB, 10000);

const songGame = createSongGame({
  db,
  saveDB,
  initUser,
  isMainOwnerId,
  downloadMediaMessage,
  storageDirectory: path.join(process.cwd(), 'song-game'),
  toBoldUnicode
});

const carRaceGame = createCarRaceGame({
  db,
  getCars: () => {
    loadCars();
    return carsCache;
  },
  saveCars,
  saveDB,
  initUser
});

// ━━━━━━━ PROTECCIÓN DE USUARIOS ━━━━━━━
// USER_PROTECTION_SYSTEM_V1

const USER_PROTECTED_FILE = './users-protected.json';
const USER_PROTECTED_TMP = './users-protected.tmp.json';

function esUsuarioInvalidoProteccion(id, user) {
  const nombre = String(user?.name || '').trim().toLowerCase();

  return (
    !id ||
    id === 'undefined' ||
    id === 'null' ||
    id.endsWith('@g.us') ||
    nombre === 'usuario' ||
    !nombre
  );
}

function limpiarUsuariosInvalidos() {
  if (!db.users || typeof db.users !== 'object') {
    db.users = {};
    return;
  }

  let eliminados = 0;

  for (const [id, user] of Object.entries(db.users)) {
    // Los baneados tampoco deben permanecer en db.users.
    if (
      esUsuarioInvalidoProteccion(id, user) ||
      (db.bannedUsers || {})[id]
    ) {
      delete db.users[id];
      eliminados++;
    }
  }

  if (eliminados > 0) {
    console.log(
      '[USERS] Eliminados registros inválidos:',
      eliminados
    );
  }
}

function guardarUsuariosProtegidos() {
  try {
    limpiarUsuariosInvalidos();

    const snapshot = JSON.stringify(
      {
        version: 1,
        savedAt: Date.now(),
        users: Object.fromEntries(
          Object.entries(db.users || {}).filter(
            ([id]) => !(db.bannedUsers || {})[id]
          )
        )
      },
      null,
      2
    );

    fs.writeFileSync(
      USER_PROTECTED_TMP,
      snapshot,
      'utf8'
    );

    fs.renameSync(
      USER_PROTECTED_TMP,
      USER_PROTECTED_FILE
    );

    console.log(
      '[USERS] Copia protegida actualizada:',
      Object.keys(db.users || {}).length,
      'usuarios'
    );

  } catch (e) {
    console.error(
      '[USERS PROTECTED ERROR]',
      e
    );
  }
}


// ============================================================
// ELIMINAR USUARIO DE LA COPIA PROTEGIDA
// ============================================================

function eliminarUsuarioDeProteccion(id) {
  try {
    if (!id) return;

    if (!fs.existsSync(USER_PROTECTED_FILE)) {
      return;
    }

    const backup = JSON.parse(
      fs.readFileSync(
        USER_PROTECTED_FILE,
        'utf8'
      )
    );

    backup.users ??= {};

    if (!backup.users[id]) {
      return;
    }

    delete backup.users[id];

    backup.savedAt = Date.now();

    fs.writeFileSync(
      USER_PROTECTED_TMP,
      JSON.stringify(
        backup,
        null,
        2
      ),
      'utf8'
    );

    fs.renameSync(
      USER_PROTECTED_TMP,
      USER_PROTECTED_FILE
    );

    console.log(
      '[USERS] Usuario eliminado de copia protegida:',
      id
    );

  } catch (e) {
    console.error(
      '[USERS PROTECTED DELETE ERROR]',
      e
    );
  }
}

function cargarUsuariosProtegidos() {
  try {
    if (!fs.existsSync(USER_PROTECTED_FILE)) {
      console.log(
        '[USERS] No existe copia protegida todavía.'
      );
      return;
    }

    const backup = JSON.parse(
      fs.readFileSync(
        USER_PROTECTED_FILE,
        'utf8'
      )
    );

    const protectedUsers =
      backup?.users || {};

    db.users ??= {};

    let recuperados = 0;

    for (const [id, protectedUser] of Object.entries(protectedUsers)) {

      if (esUsuarioInvalidoProteccion(id, protectedUser)) {
        continue;
      }

      // ========================================================
      // USUARIOS BANEADOS NUNCA SE RESTAURAN
      // ========================================================
      db.bannedUsers ??= {};

      if (db.bannedUsers[id]) {
        console.log(
          '[USERS] Restauración bloqueada para usuario baneado:',
          id
        );
        continue;
      }

      /*
       * MUY IMPORTANTE:
       *
       * Si el usuario ya existe en database.json,
       * NO lo reemplazamos.
       *
       * Solamente recuperamos usuarios que hayan
       * desaparecido completamente.
       */

      if (!db.users[id]) {

        db.users[id] =
          JSON.parse(
            JSON.stringify(protectedUser)
          );

        recuperados++;
      }
    }

    if (recuperados > 0) {
      console.log(
        '[USERS] Usuarios recuperados:',
        recuperados
      );
    } else {
      console.log(
        '[USERS] No fue necesario recuperar usuarios.'
      );
    }

    limpiarUsuariosInvalidos();

  } catch (e) {
    console.error(
      '[USERS RESTORE ERROR]',
      e
    );
  }
}

function protegerUsuariosAntesDeReinicio() {
  try {

    console.log(
      '[SAFE RESTART] Protegiendo usuarios...'
    );

    limpiarUsuariosInvalidos();

    guardarUsuariosProtegidos();

    /*
     * Guardado normal de database.json.
     * saveDB() usa su propia cola.
     */

    saveDB();

    console.log(
      '[SAFE RESTART] Usuarios protegidos correctamente.'
    );

  } catch (e) {
    console.error(
      '[SAFE RESTART ERROR]',
      e
    );
  }
}

// Limpieza + recuperación al iniciar.
cargarUsuariosProtegidos();

// Copia protegida periódica.
// Cada 30 segundos.
setInterval(
  guardarUsuariosProtegidos,
  30000
);



 function rebuildHarems() {

  if (!charactersCache.length) {
    console.log(' rebuildHarems cancelado: charactersCache vacío');
    return;
  }

  // Verificar si ya existen harems guardados
  let totalHarems = 0;

  for (const groupId in db.groups) {
    db.groups[groupId].harems ??= {};
    totalHarems += Object.keys(
      db.groups[groupId].harems
    ).length;
  }

  // Si ya hay harems, NO reconstruir
  if (totalHarems > 0) {
    console.log(
      '✓ Harems existentes encontrados. Reconstrucción omitida.'
    );
    return;
  }

  console.log('Reconstruyendo harems...');

  for (const char of charactersCache) {

    if (!char.claimedBy) continue;

    for (const [groupId, claim] of Object.entries(char.claimedBy)) {

      if (!db.groups[groupId]) continue;

      db.groups[groupId].harems ??= {};
      db.groups[groupId].harems[claim.user] ??= [];

      // Evitar duplicados
      const existe =
        db.groups[groupId]
          .harems[claim.user]
          .some(
            c => c.key === char.key
          );

      if (existe) continue;

      db.groups[groupId]
        .harems[claim.user]
        .push({
          id: char.id,
          key: char.key,
          name: char.name,
          anime: char.anime,
          gender: char.gender,
          value: char.value,
          rarity: char.rarity,
          image: char.image || null,
          claimed: false,
          claimedBy: null,
          timestamp: claim.time,
          invoker: claim.user
        });

      // Copia de seguridad en db.users
      const user =
        initUser(claim.user);

      user.harem ??= [];

      if (!user.harem.includes(char.key)) {
        user.harem.push(char.key);
      }
    }
  }

  saveDB();

  console.log('✓ Harems reconstruidos.');
}

function createBackup() {
  try {
    const fecha = new Date()
      .toISOString()
      .replace(/[:.]/g,'-');

    const carpeta = './backups';

    if (!fs.existsSync(carpeta)) {
      fs.mkdirSync(carpeta);
    }

    const archivos = [
      './db.json',
      './characters.json'
    ];

    for (const file of archivos) {
      if (!fs.existsSync(file)) continue;

      const nombre =
        path.basename(file);

      fs.copyFileSync(
        file,
        `${carpeta}/${fecha}_${nombre}`
      );
    }

    console.log(
      '[BACKUP] Copia creada.'
    );

  } catch (e) {
    console.error(
      '[BACKUP ERROR]',
      e
    );
  }
}

function initUser(sender, pushName) {

  // ==================================================
  // VALIDACION ESTRICTA DE IDENTIDAD
  // ==================================================

  if (!sender) {
    return null;
  }

  sender = String(sender).trim();

  // Nunca registrar grupos como usuarios
  if (sender.endsWith('@g.us')) {
    return null;
  }

  // Nunca registrar identificadores invalidos
  if (
    sender === 'undefined' ||
    sender === 'null' ||
    sender === '[object Object]' ||
    sender.length < 5
  ) {
    return null;
  }

  // ==================================================
  // NOMBRE VALIDO
  // ==================================================

  const cleanName =
    typeof pushName === 'string'
      ? pushName.trim()
      : '';

  // ==================================================
  // CREAR USUARIO
  // ==================================================

  if (!db.users[sender]) {

    // Sin nombre real no creamos un usuario fantasma.
    if (!cleanName || cleanName.toLowerCase() === 'usuario') {
      return null;
    }

    db.users[sender] = {
      name: cleanName,
      totalCommands: 0,
      favCommands: {},
      xp: 0,
      level: 1,
      messages: 0,
      dailyStreak: 0,
      lastDailyGlobal: 0,
      lastRwp: 0,
      lastRwr: 0,
      lastCoinCollect: Date.now(),

      atk: 10,
      def: 10,
      vel: 10,
      pres: 10,

      training: null,
      gender: null,
      birthday: null,
      marriedTo: null,
      marryRequest: null,
      claimMsg: null,

      harem: [],

      luck: {
        total: 0,
        mod: 0,
        mythic: 0,
        legendary: 0,
        epic: 0,
        rare: 0,
        common: 0
      },

      diamonds: 0,
      gems: 0,
      coinsgMultiplier: 1,
      cooldownReduction: 0,
      harem100Reward: false,
      bpremiumUntil: 0,
      xpremium: false,

      waifu: {
        current: null,
        totalLove: 0,
        maxLove: 0,
        ligues: {},
        lastLigue: 0
      }
    };

  } else {

    // ==================================================
    // ACTUALIZAR IDENTIDAD
    // ==================================================

    if (
      cleanName &&
      cleanName.toLowerCase() !== 'usuario'
    ) {
      db.users[sender].name = cleanName;
    }

    // ==================================================
    // REPARACION DE CAMPOS ANTIGUOS
    // ==================================================

    if (
      typeof db.users[sender].lastCoinCollect !== 'number'
    ) {
      db.users[sender].lastCoinCollect = Date.now();
    }

    if (!('claimMsg' in db.users[sender]))
      db.users[sender].claimMsg = null;

    if (!Array.isArray(db.users[sender].harem))
      db.users[sender].harem = [];

    if (!db.users[sender].luck) {
      db.users[sender].luck = {
        total: 0,
        mod: 0,
        mythic: 0,
        legendary: 0,
        epic: 0,
        rare: 0,
        common: 0
      };
    }

    const gemBalance = Number(db.users[sender].gems);
    db.users[sender].gems =
      Number.isSafeInteger(gemBalance) && gemBalance >= 0
        ? gemBalance
        : 0;

    if (typeof db.users[sender].coinsgMultiplier !== 'number')
      db.users[sender].coinsgMultiplier = 1;

    if (typeof db.users[sender].cooldownReduction !== 'number')
      db.users[sender].cooldownReduction = 0;

    if (typeof db.users[sender].harem100Reward !== 'boolean')
      db.users[sender].harem100Reward = false;

if (typeof db.users[sender].coinsgMultiplier !== 'number')
  db.users[sender].coinsgMultiplier = 1;

if (typeof db.users[sender].harem100Reward !== 'boolean')
  db.users[sender].harem100Reward = false;

    const bpremiumUntil = Number(db.users[sender].bpremiumUntil);
    db.users[sender].bpremiumUntil =
      Number.isFinite(bpremiumUntil) && bpremiumUntil >= 0
        ? bpremiumUntil
        : 0;

    if (typeof db.users[sender].xpremium !== 'boolean')
      db.users[sender].xpremium = false;

    if (!('gender' in db.users[sender]))
      db.users[sender].gender = null;

    if (!('birthday' in db.users[sender]))
      db.users[sender].birthday = null;

    if (!('marriedTo' in db.users[sender]))
      db.users[sender].marriedTo = null;

    if (!('marryRequest' in db.users[sender]))
      db.users[sender].marryRequest = null;

    if (!db.users[sender].waifu) {
      db.users[sender].waifu = {
        current: null,
        totalLove: 0,
        maxLove: 0,
        ligues: {},
        lastLigue: 0
      };
    }

    if (typeof db.users[sender].atk !== 'number')
      db.users[sender].atk = 10;

    if (typeof db.users[sender].def !== 'number')
      db.users[sender].def = 10;

    if (typeof db.users[sender].vel !== 'number')
      db.users[sender].vel = 10;

    if (typeof db.users[sender].pres !== 'number')
      db.users[sender].pres = 10;

    if (!('training' in db.users[sender]))
      db.users[sender].training = null;

    if (typeof db.users[sender].lastRwp !== 'number')
      db.users[sender].lastRwp = 0;

    if (typeof db.users[sender].lastRwr !== 'number')
      db.users[sender].lastRwr = 0;

    if (typeof db.users[sender].dailyStreak !== 'number')
      db.users[sender].dailyStreak = 0;

    if (typeof db.users[sender].lastDailyGlobal !== 'number')
      db.users[sender].lastDailyGlobal = 0;

    if (typeof db.users[sender].dailyTimezone !== 'string')
      db.users[sender].dailyTimezone = '';

    if (typeof db.users[sender].dailyCountryCode !== 'string')
      db.users[sender].dailyCountryCode = '';

    if (!db.users[sender].favCommands)
      db.users[sender].favCommands = {};

    if (typeof db.users[sender].xp !== 'number')
      db.users[sender].xp = 0;

    if (typeof db.users[sender].level !== 'number')
      db.users[sender].level = 1;

    if (typeof db.users[sender].messages !== 'number')
      db.users[sender].messages = 0;
  }

  return db.users[sender];
}

function getTrainingRank(level){

  if (level < 30)
    return 'Novato';

  if (level < 50)
    return 'Soldado';

  if (level < 100)
    return 'Emperador';

  if (level < 150)
    return 'Leyenda';

  if (level < 200)
    return 'Conquistador';

  if (level < 250)
    return 'Imparable';

  if (level < 300)
    return 'Magia oscura';

  if (level < 350)
    return 'Luz';

  if (level < 400)
    return 'Ego';

  if (level < 450)
    return 'Dueño de tierras';

  if (level < 500)
    return 'Invisible';

  return 'Dios';

}

function getTrainingCost(level){

  const base =
    20000 +
    (
      (level - 1)
      * 12000
    );

  const random =
    Math.floor(
      Math.random() *
      9000
    );

  return base + random;

}

function generateTrainingStats(user){

  return {

    atk:
      Math.floor(
        Math.random() * 12
      ) + 5,

    def:
      Math.floor(
        Math.random() * 12
      ) + 5,

    vel:
      Math.floor(
        Math.random() * 12
      ) + 5,

    pres:
      Math.floor(
        Math.random() * 12
      ) + 5

  };

}

function collectPassiveCoins(
  groupId,
  sender
){

    const user =
    initUser(sender);

  const economy =
    getGroupEconomy(
      groupId,
      sender
    );

  const harem =
    db.groups[groupId]
    ?.harems?.[sender] || [];

  let totalGen = 0;

  for (const char of harem) {

    const original =
      characterKeyMap.get(
        char.key
      );

    totalGen +=
      original?.coinGen || 0;
  }

  const hoursElapsed =
    (Date.now() -
    user.lastCoinCollect) / 3600000;

  if (
    hoursElapsed <= 0 ||
    totalGen <= 0
  ) return;

  const multiplier =
  (hasPremium(user) ? 2 : 1) *
  (user.coinsgMultiplier || 1);

  const earned =
    Math.floor(
      totalGen *
      hoursElapsed *
      multiplier
    );

  if (earned <= 0) return;

  economy.coins += earned;

  user.lastCoinCollect =
    Date.now();
}



function hasPremium(user) {
  return hasAnyPremium(user);
}

function getPremiumCooldown(user) {

  const baseCooldown = hasPremium(user)
    ? 300000
    : 900000;

  const reduction =
    Number(user?.cooldownReduction || 0);

  return Math.max(
    30000,
    baseCooldown - reduction
  );
}

export async function handleBpremium(
  sock,
  msg,
  sender
) {

  const user = initUser(sender, msg.pushName);
  const result = purchasePremium(user, 'bpremium');
  const jid = msg.key.remoteJid;

  if (result.status === 'invalid') {
    return sock.sendMessage(jid, {
      text: '❌ No se pudo cargar tu cuenta para comprar BPremium.'
    }, { quoted: msg });
  }
  if (result.status === 'has-xpremium') {
    return sock.sendMessage(jid, {
      text: '☆ Ya tienes XPremium.'
    }, { quoted: msg });
  }
  if (result.status === 'has-bpremium') {
    return sock.sendMessage(jid, {
      text: '☆ Ya tienes BPremium activo.'
    }, { quoted: msg });
  }
  if (result.status === 'insufficient-gems') {
    return sock.sendMessage(jid, {
      text:
        `◇ BPremium cuesta ${result.price.toLocaleString()} gemas.\n` +
        `◇ Tu saldo actual: ${result.balance.toLocaleString()} gemas.\n` +
        '■ Gemas insuficientes.'
    }, { quoted: msg });
  }

  saveDB();

  return sock.sendMessage(
    jid,
    {
      text:
      "☆ BPremium comprado\n\n" +
      "◇ Duraci¿n: 24 horas\n" +
      "◇ Coinsg: x2\n" +
      "◇ /rw y /rwp: 5 min"
    },
    {
      quoted: msg
    }
  );

}

export async function handleXpremium(
  sock,
  msg,
  sender
) {

  const user = initUser(sender, msg.pushName);
  const result = purchasePremium(user, 'xpremium');
  const jid = msg.key.remoteJid;

  if (result.status === 'invalid') {
    return sock.sendMessage(jid, {
      text: '❌ No se pudo cargar tu cuenta para comprar XPremium.'
    }, { quoted: msg });
  }
  if (result.status === 'has-xpremium') {
    return sock.sendMessage(jid, {
      text: '☆ Ya tienes XPremium.'
    }, { quoted: msg });
  }
  if (result.status === 'insufficient-gems') {
    return sock.sendMessage(jid, {
      text:
        `◇ XPremium cuesta ${result.price.toLocaleString()} gemas.\n` +
        `◇ Tu saldo actual: ${result.balance.toLocaleString()} gemas.\n` +
        '■ Gemas insuficientes.'
    }, { quoted: msg });
  }

  saveDB();

  return sock.sendMessage(
    jid,
    {
      text:
      "☆ XPremium comprado\n\n" +
      "◇ Duraci¿n: Permanente\n" +
      "◇ Coinsg: x2\n" +
      "◇ /rw y /rwp: 5 min"
    },
    {
      quoted: msg
    }
  );

}

export async function handleAddIs(
  sock,
  msg,
  args,
  sender,
  isOwner = false
) {

  const jid =
    msg.key.remoteJid;


  /*
   * Los usuarios normales simplemente son ignorados.
   */
 if (!isOwner) {
  return;
}

  const input =
    args.join(' ').trim();

  if (!input) {
    return sock.sendMessage(
      jid,
      {
        text:
          'Uso: /addis insulto\n\n' +
          'También puedes agregar varios:\n' +
          '/addis idiota,tonto'
      },
      { quoted: msg }
    );
  }

  initAntiIsn();

  const nuevos =
    input
      .split(',')
      .map(x => x.trim())
      .filter(Boolean);

  if (!nuevos.length) {
    return;
  }

  const agregados = [];
  const repetidos = [];

  for (const insulto of nuevos) {

    const limpio =
      insulto.trim();

    if (!limpio) {
      continue;
    }

    const normalizado =
      normalizeAntiIsnText(limpio);

    const existe =
      db.antiIsn.insults.some(
        existente =>
          normalizeAntiIsnText(existente) === normalizado
      );

    if (existe) {
      repetidos.push(limpio);
      continue;
    }

    db.antiIsn.insults.push(limpio);
    agregados.push(limpio);
  }

  saveDB();

  let texto =
    '● *Anti-isn*\n\n';

  if (agregados.length) {
    texto +=
      `✧ Agregados: ${agregados.length}\n`;

    texto +=
      agregados
        .map(x => `» ${x}`)
        .join('\n');
  }

  if (repetidos.length) {
    texto +=
      `\n\n✧ Repetidos: ${repetidos.length}\n`;

    texto +=
      repetidos
        .map(x => `» ${x}`)
        .join('\n');
  }

  texto +=
    `\n\n✧ Total de insultos: ${db.antiIsn.insults.length}`;

  return sock.sendMessage(
    jid,
    {
      text: texto
    },
    { quoted: msg }
  );
}

// ============================================================
// ANTI-ISN
// ============================================================

function initAntiIsn() {
  db.antiIsn ??= {
    insults: []
  };

  if (!Array.isArray(db.antiIsn.insults)) {
    db.antiIsn.insults = [];
  }
}

initAntiIsn();

function normalizeAntiIsnText(text) {
  return String(text || '')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .toLowerCase()
    .replace(/[4@]/g, 'a')
    .replace(/[3]/g, 'e')
    .replace(/[1!|]/g, 'i')
    .replace(/[0]/g, 'o')
    .replace(/[5$]/g, 's')
    .replace(/[7]/g, 't')
    .replace(/[8]/g, 'b')
    .replace(/[^a-z0-9\u0600-\u06ff\u0750-\u077f\u0900-\u097f\u4e00-\u9fff\u3040-\u30ff]+/gi, '');
}

function antiIsnMatches(text, insult) {
  const original = String(text || '');
  const target = String(insult || '').trim();

  if (!original || !target) return false;

  const normalizedText = normalizeAntiIsnText(original);
  const normalizedInsult = normalizeAntiIsnText(target);

  if (!normalizedInsult) return false;

  // Coincidencia directa normalizada.
  if (normalizedText.includes(normalizedInsult)) {
    return true;
  }

  /*
   * Permite separaciones artificiales:
   *
   * i d i o t a
   * i.d.i.o.t.a
   * i-d-i-o-t-a
   *
   * Se eliminan los separadores antes de comparar.
   */
  const compactText = original
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .toLowerCase()
    .replace(/[4@]/g, 'a')
    .replace(/[3]/g, 'e')
    .replace(/[1!|]/g, 'i')
    .replace(/[0]/g, 'o')
    .replace(/[5$]/g, 's')
    .replace(/[7]/g, 't')
    .replace(/[8]/g, 'b')
    .replace(/[^\p{L}\p{N}]+/gu, '');

  if (compactText.includes(normalizedInsult)) {
    return true;
  }

  /*
   * Permite caracteres repetidos:
   *
   * idiiooota
   * tontoool
   */
  const compressed = normalizedText
    .replace(/(.)\1+/g, '$1');

  if (compressed.includes(normalizedInsult)) {
    return true;
  }

  return false;
}

function detectarInsultoAntiIsn(text) {
  initAntiIsn();

  for (const insult of db.antiIsn.insults) {
    if (antiIsnMatches(text, insult)) {
      return insult;
    }
  }

  return null;
}

function contarInsultosAntiIsn() {
  initAntiIsn();
  return db.antiIsn.insults.length;
}

export async function handleAntiIsn(sock, msg, args, groupId, sender) {

  const jid = msg.key.remoteJid;

  if (!jid || !jid.endsWith('@g.us')) {
    return;
  }

  const accion =
    String(args[0] || '').toLowerCase();

  if (!['on', 'off'].includes(accion)) {
    return sock.sendMessage(
      jid,
      {
        text:
          'Uso:\n' +
          '/anti-isn on\n' +
          '/anti-isn off'
      },
      { quoted: msg }
    );
  }


  const group =
    initGroup(jid);

  if (accion === 'on') {

    group.antiIsn = true;

    saveDB();

    return sock.sendMessage(
      jid,
      {
        text:
          `● *Anti-isn* Activado.\n` +
          `> eliminara los insultos (${contarInsultosAntiIsn()})`
      },
      { quoted: msg }
    );
  }

  group.antiIsn = false;

  saveDB();

  return sock.sendMessage(
    jid,
    {
      text:
        `● *Anti-isn* Desactivado.\n` +
        `> la protección contra insultos está apagada.`
    },
    { quoted: msg }
  );
}

async function procesarAntiIsn(sock, msg, jid, sender, body) {

  if (!jid?.endsWith('@g.us')) {
    return false;
  }

  const group =
    initGroup(jid);

  if (group.antiIsn !== true) {
    return false;
  }

  if (!body?.trim()) {
    return false;
  }

  /*
   * Los owners están protegidos.
   */
 const isMainOwner =
   isMainOwnerId(sender);

 const isStaffOwner =
   isSecondaryOwnerId(sender);

  if (isMainOwner || isStaffOwner) {
    return false;
  }

  const insult =
    detectarInsultoAntiIsn(body);

  if (!insult) {
    return false;
  }

  /*
   * Intentamos borrar el mensaje.
   */
  try {

    await sock.sendMessage(
      jid,
      {
        delete: msg.key
      }
    );

  } catch (err) {

    console.log(
      'ANTI-ISN: No se pudo eliminar el mensaje:',
      err.message
    );

    return false;
  }

  console.log(
    'ANTI-ISN: Mensaje eliminado.',
    'Usuario:',
    sender,
    'Coincidencia:',
    insult
  );

  return true;
}

function initGroup(jid) {
  if (!db.groups[jid]) db.groups[jid] = {};
  const g = db.groups[jid];
  if (!g.muted) g.muted = [];
  if (typeof g.antilink !== 'boolean') g.antilink = false;
  if (!g.totalMessages) g.totalMessages = 0;
  if (!g.members) g.members = {};
  if (typeof g.off !== 'boolean') g.off = false;
  if (!g.economy) g.economy = {};
  if (!g.cooldowns) g.cooldowns = {};
  if (!g.harems) g.harems = {};
  return g;
}

function getBotCurrency(sock) {
  const normalizeNumber = value =>
    String(value || "")
      .split(":")[0]
      .split("@")[0]
      .replace(/\D/g, "");

  /*
   * El bot principal no pertenece a db.subBots.
   * Su moneda se guarda directamente en db.primaryCurrency.
   */
  const isMainBot =
    sock === globalThis.MAIN_BOT_SOCK ||
    !sock?.__subBotPhone;

  if (isMainBot) {
    return (
      String(db.primaryCurrency || "oños").trim() ||
      "oños"
    );
  }

  const botPhone = normalizeNumber(
    sock?.user?.id || sock?.__subBotPhone
  );

  if (!botPhone) return "oños";

  for (
    const [key, value]
    of Object.entries(db.subBots || {})
  ) {
    const keyNumber =
      normalizeNumber(key);

    const valueNumbers = [
      value?.phone,
      value?.number,
      value?.jid,
      value?.id,
      value?.user?.id
    ]
      .filter(Boolean)
      .map(normalizeNumber);

    if (
      keyNumber === botPhone ||
      valueNumbers.includes(botPhone)
    ) {
      return (
        String(value?.currency || "oños").trim() ||
        "oños"
      );
    }
  }

  return "oños";
}

function getGroupEconomy(groupId, sender) {
  const g = initGroup(groupId);
  if (!g.economy[sender]) {
  g.economy[sender] = {
  coins: 10000,
  bank: 0,
  lastWork: 0,
  lastSlut: 0,
  lastCrime: 0,
  lastDaily: 0,
  lastMine: 0,
  dailyStreak: 0,
  timeReduction: 0
};

if (typeof g.economy[sender].dailyStreak !== 'number')
  g.economy[sender].dailyStreak = 0;

  }
 if (typeof g.economy[sender].dailyStreak !== 'number') {
  g.economy[sender].dailyStreak = 0;
} 
  
 return g.economy[sender];
}

function getGroupCooldowns(groupId, sender) {
  const g = initGroup(groupId);
  if (!g.cooldowns[sender]) {
    g.cooldowns[sender] = { rw: 0, claim: 0, work: 0, slut: 0, crime: 0, daily: 0, cn: 0 };
  }
  g.cooldowns[sender].cn ??= 0;
  return g.cooldowns[sender];
}

function toBoldUnicode(value) {
  return String(value).replace(/[A-Za-z0-9]/g, character => {
    const code = character.charCodeAt(0);
    if (code >= 65 && code <= 90) return String.fromCodePoint(0x1D400 + code - 65);
    if (code >= 97 && code <= 122) return String.fromCodePoint(0x1D41A + code - 97);
    return String.fromCodePoint(0x1D7CE + code - 48);
  });
}

function getGroupEventState(groupId, now = Date.now()) {
  const event = db.groups?.[String(groupId)]?.event;
  if (!event || typeof event !== 'object') {
    return { status: 'none', event: null };
  }

  const startsAt =
    event.startsAt == null
      ? 0
      : Number(event.startsAt);
  const expiresAt = Number(event.expires);
  if (
    !Number.isFinite(startsAt) ||
    !Number.isFinite(expiresAt) ||
    expiresAt <= now
  ) {
    return { status: 'none', event: null };
  }

  return startsAt > now
    ? { status: 'scheduled', event, startsAt, expiresAt }
    : { status: 'active', event, startsAt, expiresAt };
}

function getGroupEvent(groupId) {
  const state = getGroupEventState(groupId);
  return state.status === 'active' ? state.event : null;
}

function getGroupScheduled(groupId) {
  const state = getGroupEventState(groupId);
  return state.status === 'scheduled' ? state.event : null;
}

function getGroupLuck(groupId) {
  const event = getGroupEvent(groupId);
  return event && Number(event.luck) > 1 ? Number(event.luck) : 1;
}

function eventTimeout(promise, ms) {
  return Promise.race([
    promise,
    new Promise((_, reject) => setTimeout(() => reject(new Error('timeout')), ms))
  ]);
}

function getAllBotSockets() {
  const bots = [];
  const seen = new Set();
  const add = (key, sock, label) => {
    if (!sock || typeof sock.groupFetchAllParticipating !== 'function' || seen.has(sock)) return;
    seen.add(sock);
    bots.push({ key, sock, label });
  };

  add('main', globalThis.MAIN_BOT_SOCK, 'Principal');
  for (const [key, sock] of activeBots.entries()) {
    add('active:' + key, sock, 'Principal');
  }
  const subSockets = globalThis.SUBBOT_SOCKETS;
  const subEntries = subSockets instanceof Map
    ? [...subSockets.entries()]
    : Object.entries(subSockets || {});
  for (const [key, sock] of subEntries) {
    add('sub:' + key, sock, 'Sub ' + key);
  }
  return bots;
}

async function resolveSockForGroup(groupId) {
  for (const bot of getAllBotSockets()) {
    try {
      const metadata = await eventTimeout(bot.sock.groupMetadata(groupId), 8000);
      if (metadata?.id) return bot.sock;
    } catch (error) {
      console.log('[EVENT GROUP LOOKUP]', bot.label, error?.message || error);
    }
  }
  return null;
}

async function buildGroupIndex() {
  const bots = getAllBotSockets();
  const groupsById = {};
  const errors = [];
  const normalize = value => String(value).split('@')[0].split(':')[0];

  for (const bot of bots) {
    let groups;
    try {
      groups = await eventTimeout(bot.sock.groupFetchAllParticipating(), 30000);
    } catch (error) {
      errors.push(bot.label + ': ' + (error?.message || error));
      continue;
    }

    const ownIds = [bot.sock.user?.id, bot.sock.user?.lid]
      .filter(Boolean)
      .map(normalize);

    for (const group of Object.values(groups || {})) {
      const isAdmin = (group.participants || []).some(participant =>
        participant.admin &&
        [participant.id, participant.lid, participant.phoneNumber]
          .filter(Boolean)
          .map(normalize)
          .some(id => ownIds.includes(id))
      );
      if (!groupsById[group.id]) {
        groupsById[group.id] = {
          id: group.id,
          name: group.subject || 'Sin nombre',
          bots: [],
          adminBots: []
        };
      }
      groupsById[group.id].bots.push(bot.label);
      if (isAdmin) groupsById[group.id].adminBots.push(bot);
    }
  }

  db.groupNums ??= {};
  db.groupNames ??= {};
  db.groupNumNext ??= 1;

  const groups = Object.values(groupsById);
  for (const group of groups) {
    if (!db.groupNums[group.id]) db.groupNums[group.id] = db.groupNumNext++;
    db.groupNames[group.id] = group.name;
    group.num = db.groupNums[group.id];
  }
  groups.sort((left, right) => left.num - right.num);

  for (let i = 0; i < groups.length; i += 8) {
    await Promise.all(groups.slice(i, i + 8).map(async group => {
      for (const bot of group.adminBots) {
        try {
          const code = await eventTimeout(bot.sock.groupInviteCode(group.id), 10000);
          if (code) {
            group.link = 'https://chat.whatsapp.com/' + code;
            break;
          }
        } catch (error) {
          console.log('[EVENT GROUP INVITE]', group.id, error?.message || error);
        }
      }
    }));
  }

  saveDB();
  return { list: groups, errors };
}

async function announceXpEvent(sock, groupId, multiplier, luck, minutes) {
  const text =
    '¡ ' + toBoldUnicode('Hay un evento en este grupo, tienen un x' + multiplier + ' de xp y x' + luck + ' de suerte en ') +
    '/' + toBoldUnicode('rw') + ' ⵑ\n> ' +
    toBoldUnicode('duracion ' + minutes + ' minutos') + ' ↻';
  try {
    const sent = await sock.sendMessage(groupId, { text: '↻' });
    const frames = ['⟳', '↻'];
    for (let i = 0; i < 10; i++) {
      await new Promise(resolve => setTimeout(resolve, 1000));
      await sock.sendMessage(groupId, { text: frames[i % 2], edit: sent.key });
    }
    await sock.sendMessage(groupId, { text, edit: sent.key });
  } catch (error) {
    console.log('[EVENT ANNOUNCE]', groupId, error?.message || error);
  }
}

if (!global.__eventExpiryTimer) {
  global.__eventExpiryTimer = setInterval(async () => {
    try {
      for (const groupId of Object.keys(db.groups || {})) {
        const group = db.groups[groupId];
        const event = group?.event;
        if (!event) continue;
        const now = Date.now();

        if (now >= Number(event.expires)) {
          const notify = group.events2 && (event.startsAt === undefined || event.announced);
          delete group.event;
          saveDB();
          if (notify) {
            const sock = await resolveSockForGroup(groupId);
            if (sock) {
              await sock.sendMessage(groupId, {
                text: 'El evento de XP y suerte ha finalizado.'
              }).catch(error => console.log('[EVENT EXPIRE NOTICE]', error?.message || error));
            }
          }
          continue;
        }

        if (event.startsAt !== undefined && !event.announced && now >= Number(event.startsAt)) {
          event.announced = true;
          saveDB();
          const sock = await resolveSockForGroup(groupId);
          if (sock) {
            void announceXpEvent(
              sock,
              groupId,
              event.multiplier,
              event.luck,
              Math.max(1, Math.round((Number(event.expires) - now) / 60000))
            );
          }
        }
      }
    } catch (error) {
      console.log('[EVENT TIMER]', error?.message || error);
    }
  }, 5000);
}

async function sendAnimatedEdit(sock, jid, msg, finalText) {
  const sent = await sock.sendMessage(jid, { text: 'Aᥴtᥙᥲᥣιzᥲᥒdo...' }, { quoted: msg });
  await new Promise(resolve => setTimeout(resolve, 1));
  try {
    await sock.sendMessage(jid, { text: finalText, edit: sent.key });
  } catch (error) {
    await sock.sendMessage(jid, { text: finalText }, { quoted: msg });
  }
}

// ━━━━━━━ GACHA LOCAL (CACHÉ Y NUEVO SISTEMA) ━━━━━━━
let charactersCache = [];

let characterMap = new Map();
let characterKeyMap = new Map();
let imageCache = new Map();

loadCharactersCache();
loadCars();
rebuildHarems();

const recentImages = {};
const pendingAlbums = {};
const carCommandLock = createKeyedLock();
global.ownerIndex = {}; // groupId -> { userId: Set<characterKey> }

function loadCharactersCache() {
  try {
    charactersCache = JSON.parse(
      fs.readFileSync(CHARACTERS_FILE, 'utf8')
    );

    characterMap.clear();
    characterKeyMap.clear();

    for (const c of charactersCache) {
      characterMap.set(c.name.toLowerCase(), c);
      characterKeyMap.set(c.key, c);

      if (!c.claimedBy) c.claimedBy = {};
      if (typeof c.claimedBy !== 'object') c.claimedBy = {};

      if (!Number.isFinite(Number(c.coinGen)) || Number(c.coinGen) <= 0) {
        const v = Number(c.value) || 0;
        if (v > 0) {
          c.coinGen = Math.floor(55 * v);
        }
      }
    }

    buildOwnerIndex();

    rebuildHarems(); // → AQU¿

  } catch {
    charactersCache = [];
  }
}

if (!charactersCache.length) {
  console.log(' characters.json vacío');
}

function smartSearch(list, query, getName){

  query =
    query
      .toLowerCase()
      .trim();

  if (!query)
    return null;

  const normalize = str =>
    str
      .toLowerCase()
      .replace(/[^a-z0-9 ]/g,' ')
      .replace(/\s+/g,' ')
      .trim();

  const q =
    normalize(query);

  let best = null;
  let score = -1;

  for (const item of list){

    const name =
      normalize(
        getName(item)
      );

    let s = 0;

    if (name === q)
      s = 1000;

    else if (
      name.startsWith(q + ' ')
    )
      s = 900;

    else if (
      name.startsWith(q)
    )
      s = 800;

    else if (
      name.includes(' ' + q + ' ')
    )
      s = 700;

    else if (
      name.includes(q)
    )
      s = 600;

    else{

      const words =
        q.split(' ');

      let ok = true;

      for (const w of words){

        if (!name.includes(w)){
          ok = false;
          break;
        }

      }

      if (ok)
        s = 500;

    }

    if (s > score){

      score = s;
      best = item;

    }

  }

  return best;

}

let saveCharactersQueue =
  Promise.resolve();



function calcularRarezaAddP(valor){

 valor = Number(valor);

 if(valor >= 17700)
  return {
   rarity:"Mod",
   chance:"5%"
  };

 if(valor >= 17000)
  return {
   rarity:"Mitico",
   chance:"10%"
  };

 if(valor >= 16000)
  return {
   rarity:"Legendario",
   chance:"20%"
  };

 if(valor >= 15000)
  return {
   rarity:"Epico",
   chance:"30%"
  };

 if(valor >= 10000)
  return {
   rarity:"Raro",
   chance:"40%"
  };

 return {
  rarity:"Comun",
  chance:"75%"
 };

}









/*
 * ============================================================
 * ADDP - REINTENTO AUTOMÁTICO DE #winfo
 * ============================================================
 *
 * Si #winfo no recibe una respuesta válida:
 *
 * 5 segundos
 *   ↓
 * reenviar el mismo #winfo
 *   ↓
 * esperar 5 segundos
 *   ↓
 * repetir hasta 3 reintentos
 *
 * El índice de la cola NO cambia durante los reintentos.
 */


/* ============================================================
 * ADDP - REINTENTO AUTOMÁTICO DE #winfo
 * ============================================================
 */



async function reintentarWinfoAddP(sock, queueJid) {

  const data = db.addpQueue?.[queueJid];


    if (
        data.iniciadoPorAddp !== true ||
        data.origenAddp !== "/addp" ||
        data.addpEstado !== "activa"
    ) {
        console.log(
            " ADDP RETRY BLOQUEADO: cola no válida.",
            queueJid
        );
        return;
    }

  if (!data) {
    console.log(
      "❌ ADDP RETRY: cola inexistente:",
      queueJid
    );
    return;
  }

  /*
   * Si ya llegó una respuesta válida,
   * no reenviar.
   */
  if (!data.esperando) {
    console.log(
      "✓ ADDP RETRY: ya no espera respuesta."
    );
    return;
  }

  const personaje =
    data.personajes?.[data.index];

  if (!personaje) {
    console.log(
      "⚠️ ADDP RETRY: no existe personaje actual."
    );

    data.esperando = false;

    clearTimeout(data.timer);

    data.timer = null;

    saveDB();

    return;
  }

  /*
   * ==========================================================
   * ADDP ETA REAL V4
   * El cronómetro comienza únicamente cuando existe
   * un personaje válido para procesar.
   * ==========================================================
   */
  iniciarCronometroAddP(data);

  const nombre =
    String(
      personaje.nombre || ""
    ).trim();

  if (!nombre) {
    console.log(
      "⚠️ ADDP RETRY: personaje sin nombre."
    );
    return;
  }

  /*
   * Contador de reintentos.
   *
   * 0 = envío original
   * 1 = primer reenvío
   * 2 = segundo reenvío
   * 3 = tercer reenvío
   */
  data.addpRetries =
    Number(data.addpRetries || 0);

  /*
   * ==========================================================
   * RETRY SIN LÍMITE
   * ==========================================================
   *
   * No existe máximo de reintentos.
   *
   * Mientras esperando=true:
   *
   *   esperar 5 segundos
   *        ↓
   *   enviar #winfo
   *        ↓
   *   esperar 5 segundos
   *        ↓
   *   repetir
   *
   * El ciclo solamente termina cuando
   * detectarRespuestaAddP() recibe una respuesta válida
   * y establece esperando=false.
   */

  /*
   * Registrar este reenvío.
   */
  data.addpRetries++;

  console.log(
    "🔁 ADDP: REENVIANDO #winfo",
    nombre,
    "| intento",
    data.addpRetries,
    "(sin límite)"
  );

  /*
   * El destino debe ser el grupo de /creatinglogs.
   */
  const destino =
    typeof db.creatingLogs === "string" &&
    db.creatingLogs.endsWith("@g.us")
      ? db.creatingLogs
      : data.targetJid;

  if (!destino) {

    console.log(
      "❌ ADDP RETRY: no existe destino."
    );

    data.esperando = false;

    clearTimeout(data.timer);

    data.timer = null;

    saveDB();

    return;
  }

  data.targetJid = destino;

  /*
   * Estamos entrando en una nueva espera.
   */
  data.addpBusy = false;
  data.addpTransition = false;

  /*
   * Antes de enviar, mantenemos esperando=true.
   */
  data.esperando = true;

  try {

    const enviado =
      await sock.sendMessage(
        destino,
        {
          text:
            "#winfo " + nombre
        }
      );

    data.messageId =
      enviado?.key?.id || null;

    data.esperando = true;

    saveDB();

    console.log(
      "✓ ADDP RETRY: #winfo reenviado:",
      nombre
    );

    console.log(
      "🆔 Nuevo mensaje:",
      data.messageId
    );

  } catch (error) {

    console.error(
      "❌ ADDP RETRY: error enviando #winfo:",
      error
    );

    /*
     * No destruir la cola.
     *
     * Dejamos esperando=false para que
     * enviarSiguienteAddP pueda volver a
     * intentar si corresponde.
     */
    data.esperando = false;
    data.messageId = null;

    clearTimeout(data.timer);
    data.timer = null;

    saveDB();

    return;
  }

  /*
   * Esperar otros 5 segundos.
   */
  clearTimeout(data.timer);

  data.timer =
    setTimeout(
      async () => {

        const actual =
          db.addpQueue?.[queueJid];

        if (!actual) {
          return;
        }

        /*
         * Si detectarRespuestaAddP()
         * recibiï¿½ un winfo válido,
         * cambia esperando=false.
         */
        if (!actual.esperando) {

          console.log(
            " ADDP: respuesta válida recibida."
          );

          return;
        }

        console.log(
          "⌛ ADDP: 5 segundos sin respuesta:",
          nombre
        );

        await reintentarWinfoAddP(
          sock,
          queueJid
        );

      },
      5000
    );

  saveDB();
}

/*
 * ============================================================
 * ADDP WATCHDOG
 * ============================================================
 *
 * Comprueba periódicamente las colas ADDP.
 *
 * Si una cola:
 *
 *   iniciadoPorAddp = true
 *   esperando = false
 *   tiene personaje actual
 *
 * intenta iniciar nuevamente enviarSiguienteAddP().
 *
 * Esto permite recuperar una cola cuyo temporizador se perdió.
 */

let addpWatchdogRunning = false;

/*
 * ============================================================
 * ADDP WATCHDOG - RECUPERACIÓN AUTOMÁTICA
 * ============================================================
 *
 * El watchdog NO envía #winfo directamente.
 *
 * Su función es recuperar el temporizador cuando:
 *
 *   - el bot se reinició
 *   - el timer anterior se perdió
 *   - la cola quedó esperando respuesta
 *
 * Cada cola tendrá UN solo timer.
 *
 * Flujo:
 *
 *   #winfo
 *      ↓
 *   5 segundos
 *      ↓
 *   reintentarWinfoAddP()
 *      ↓
 *   #winfo
 *      ↓
 *   5 segundos
 *      ↓
 *   repetir
 *
 * El ciclo termina cuando esperando=false.
 */



async function detectarRespuestaAddP(sock, msg) {
if (!msg) {
    console.log(" ADDP msg vacío");
    return false;
  }

  const respuestaJid = msg.key?.remoteJid;

  /*
   * ADDP puede recibir la respuesta de #winfo
   * desde el mismo bot que envió la consulta.
   *
   * Por eso NO descartamos inmediatamente fromMe.
   * Primero verificamos si existe una cola ADDP activa
   * esperando una respuesta en este mismo grupo.
   */
  if (msg.key?.fromMe) {
    const hayColaADDP = Object.values(db.addpQueue || {}).some(data =>
      data &&
      data.iniciadoPorAddp === true &&
      data.esperando === true &&
      data.targetJid === respuestaJid
    );

    if (!hayColaADDP) {
      console.log("⏩ ADDP ignorando mensaje propio sin cola activa");
      return false;
    }

    console.log(
      "✓ ADDP: mensaje propio permitido porque corresponde a una cola activa:",
      respuestaJid
    );
  }
const body =
    msg.message?.conversation ||
    msg.message?.extendedTextMessage?.text ||
    msg.message?.imageMessage?.caption ||
    msg.message?.videoMessage?.caption ||
    "";
if (!body) {
    console.log("⏩ ADDP: mensaje sin texto");
    return false;
  }

  /*
   * Recorremos únicamente colas ADDP activas.
   */
  for (const queueJid of Object.keys(db.addpQueue || {})) {

    
const data = db.addpQueue[queueJid];

    if (
      !data ||
      data.iniciadoPorAddp !== true ||
      data.origenAddp !== "/addp"
    ) {
      return false;
    }


    if (!data) {
      continue;
    }

    if (data.iniciadoPorAddp !== true) {
      continue;
    }

    if (!data.esperando) {
      continue;
    }

    /*
     * La respuesta debe venir del grupo donde ADDP
     * envió #winfo.
     */
    if (
      data.targetJid &&
      respuestaJid !== data.targetJid
    ) {
      console.log(
        "⏩ ADDP: respuesta ignorada por JID.",
        "Esperado:",
        data.targetJid,
        "Recibido:",
        respuestaJid
      );

      continue;
    }

    const pj = data.personajes?.[data.index];

    if (!pj) {
      console.log(
        "⚠️ ADDP: no existe personaje en index:",
        data.index
      );

      continue;
    }

    const nombreEsperado =
      String(pj.nombre || "").trim();

    if (!nombreEsperado) {
      console.log(
        "⚠️ ADDP: personaje sin nombre."
      );

      continue;
    }

    /*
     * Normalizamos para evitar problemas de mayúsculas.
     */
    const bodyNormalizado =
      body.toLowerCase();

    const nombreNormalizado =
      nombreEsperado.toLowerCase();

    /*
     * La respuesta debe contener información de personaje.
     * Permitimos varias variantes de "Nombre".
     */
    const tieneNombre =
      bodyNormalizado.includes("❬ nombre") ||
      bodyNormalizado.includes("nombre »") ||
      bodyNormalizado.includes("nombre:");

    if (!tieneNombre) {
      console.log(
        "⏩ ADDP: no parece respuesta de #winfo."
      );

      continue;
    }

    const nombreRespuestaMatch =
      body.match(/❬\s*Nombre\s*[»:]?\s*\*?([^*\n]+)\*?/i);

    const nombreRespuesta =
      nombreRespuestaMatch
        ? nombreRespuestaMatch[1].trim()
        : "";

    const nombresCoinciden =
      nombresEquivalentesAddP(
        nombreEsperado,
        nombreRespuesta
      );

    if (!nombresCoinciden) {
      console.log(
        "⏩ ADDP: respuesta no corresponde al personaje:",
        nombreEsperado
      );

      continue;
    }

    console.log(
      "🎯 ADDP: RESPUESTA CONFIRMADA:",
      nombreEsperado
    );

    /*
     * BLOQUEAR inmediatamente la cola.
     *
     * Esto evita que el watchdog o cualquier otra llamada
     * pueda enviar otro #winfo mientras se procesa este.
     */
    data.addpBusy = true;
    data.addpTransition = true;

    /*
     * Detener timeout antes de procesar.
     */
    data.esperando = false;

    clearTimeout(data.timer);
    data.timer = null;

    const valorMatch =
      body.match(/✰\s*Valor\s*[»:]?\s*\*?(\d+)/i);

    const valor =
      valorMatch
        ? Number(valorMatch[1])
        : 100;

    const genero = (() => {
      const normalize = value =>
        String(value).normalize('NFKD').replace(/[\u0300-\u036f]/g, '');
      for (const line of String(body).split('\n')) {
        const match = line.match(/^(.*?)[»:](.*)$/);
        if (!match) continue;
        const label = normalize(match[1]).replace(/[■⚥★♧◇*_~\s\u0060]/g, '');
        if (!/^g.{1,5}ro$/i.test(label)) continue;
        const value = match[2].replace(/[*_~\u0060]/g, '').trim();
        if (value) return value;
      }
      return 'Desconocido';
    })();

    const rango =
      calcularRarezaAddP(valor);

    // ============================================================
    // ADDP: COMPROBAR SI EL PERSONAJE YA EXISTE
    // ============================================================

    // ============================================================
    // ADDP: COMPROBACIÓN SEGURA DE DUPLICADOS
    // Busca por:
    // 1. Tag
    // 2. Nombre solicitado
    // 3. Nombre devuelto por /winfo
    // 4. Equivalencias ADDP
    // ============================================================

    const nombreParaBuscar =
      nombreRespuesta || nombreEsperado;

    const tagBuscado =
      normalizarNombreAddP(pj.tag);

    const nombreEsperadoNorm =
      normalizarNombreAddP(nombreEsperado);

    const nombreRespuestaNorm =
      normalizarNombreAddP(nombreRespuesta);

    let personajeExistente = null;

    // ------------------------------------------------------------
    // 1. Buscar primero por TAG
    // ------------------------------------------------------------
    if (tagBuscado) {
      personajeExistente =
        charactersCache.find(c =>
          normalizarNombreAddP(c.tag) === tagBuscado
        );
    }

    // ------------------------------------------------------------
    // 2. Buscar por nombre solicitado / recibido
    // ------------------------------------------------------------
    if (!personajeExistente) {
      personajeExistente =
        charactersCache.find(c => {

          const nombreExistente =
            normalizarNombreAddP(c.name);

          if (!nombreExistente) {
            return false;
          }

          if (
            nombreExistente === nombreEsperadoNorm ||
            nombreExistente === nombreRespuestaNorm
          ) {
            return true;
          }

          // Comprobar equivalencias en ambos sentidos
          if (
            nombresEquivalentesAddP(
              nombreEsperado,
              c.name
            )
          ) {
            return true;
          }

          if (
            nombresEquivalentesAddP(
              nombreRespuesta,
              c.name
            )
          ) {
            return true;
          }

          return false;
        });
    }

    if (personajeExistente) {

      console.log(
        "⚠️ ADDP: personaje ya existe:",
        personajeExistente.name,
        "| ID:",
        personajeExistente.id
      );

      /*
       * ============================================================
       * ADDP DUPLICADO -> DESCARTAR Y CONTINUAR AUTOMÁTICAMENTE
       * ============================================================
       *
       * El personaje ya existe globalmente.
       *
       * NO crear otro personaje.
       * NO mandar otro #winfo para este personaje.
       *
       * Después de descartarlo:
       *
       *   index++
       *       ↓
       *   liberar locks
       *       ↓
       *   guardar DB
       *       ↓
       *   scheduler
       *       ↓
       *   siguiente #winfo
       */

      registrarResultadoAddP(
        data,
        pj.nombre,
        "Ya existe",
        pj.tag
      );

      console.log(
        "📋 ADDP resultado:",
        pj.nombre,
        "-> Ya existe"
      );

      /*
       * Avanzar inmediatamente.
       */

      data.index =
        Number(data.index || 0) + 1;

      /*
       * ============================================================
       * LIBERAR COMPLETAMENTE LA COLA
       * ============================================================
       */

      data.esperando = false;

      data.addpBusy = false;

      data.addpTransition = false;

      data.addpTransitionOwner = null;

      /*
       * Compatibilidad con el sistema anterior.
       */

      data.transition = false;

      /*
       * El watchdog del personaje anterior
       * ya no debe controlar la cola.
       */

      if (data.timer) {

        clearTimeout(
          data.timer
        );

        data.timer = null;
      }

      saveDB();

      /*
       * ============================================================
       * ¿QUEDAN PERSONAJES?
       * ============================================================
       */

      if (
        data.index <
        data.personajes.length
      ) {

        const siguiente =
          data.personajes[data.index];

        console.log(
          "⏭️ ADDP DUPLICADO: descartado:",
          pj.nombre,
          "| siguiente:",
          siguiente?.nombre || "desconocido"
        );

        /*
         * ========================================================
         * CONTINUAR AUTOMÁTICAMENTE
         * ========================================================
         *
         * Usamos setTimeout para salir completamente
         * del procesamiento de la respuesta actual.
         *
         * Esto evita que el scheduler choque con el
         * handler que acaba de procesar el duplicado.
         */

        setTimeout(
          () => {

            const actual =
              db.addpQueue?.[queueJid];

            if (!actual) {

              console.log(
                "⚠️ ADDP DUPLICADO: cola desapareció antes de continuar:",
                queueJid
              );

              return;
            }

            /*
             * Verificación final.
             *
             * Si alguien ya inició la siguiente operación,
             * no duplicar el #winfo.
             */

            if (
              actual.esperando === true ||
              actual.addpBusy === true ||
              actual.addpTransition === true
            ) {

              console.log(
                " ADDP DUPLICADO: siguiente ya está siendo procesado:",
                queueJid
              );

              return;
            }

            console.log(
              "🚀 ADDP DUPLICADO: iniciando autom¿ticamente:",
              queueJid,
              "| index:",
              actual.index,
              "| personaje:",
              actual.personajes?.[
                actual.index
              ]?.nombre
            );

            programarSiguienteAddP(
              sock,
              queueJid
            ).catch(
              error => {

                console.error(
                  " ADDP: error continuando después de duplicado:",
                  error
                );
              }
            );

          },
          250
        );

        return true;
      }

      /*
       * ============================================================
       * FIN DE COLA
       * ============================================================
       */

      console.log(
        "🏁 ADDP: último personaje era duplicado:",
        queueJid
      );

      await enviarResumenAddP(
        sock,
        queueJid,
        data
      );

      delete db.addpQueue[queueJid];

      saveDB();

      return true;
    }

    // ============================================================
    // ADDP: PERSONAJE NUEVO
    // ============================================================

    const nuevoID =
      charactersCache.length
        ? Math.max(
            ...charactersCache.map(
              c => Number(c.id) || 0
            )
          ) + 1
        : 1;

    const personajeKeyAddP =
      nombreEsperado
        .toLowerCase()
        .trim()
        .replace(/[^\w]+/g, '_')
        .replace(/^_+|_+$/g, '');

    const personaje = {
      id: nuevoID,
      name: nombreEsperado,
      key: personajeKeyAddP,
      anime: data.serie?.name || "Desconocido",
      tag: pj.tag,
      gender: genero,
      estado: "Libre",
      value: valor,
      rarity: rango.rarity,
      chance: rango.chance,
      creator: data.user,
      coinGen: Math.floor(55 * Number(valor)),
      images: []
    };

    charactersCache.push(personaje);

/*
 * ============================================================
 * ADDP -> ASOCIAR PERSONAJE A SU SERIE
 * ============================================================
 *
 * El personaje debe quedar registrado inmediatamente
 * tanto en characters.json como en la serie seleccionada
 * por /addp.
 *
 * Esto evita que el personaje exista globalmente pero
 * aparezca como "0 personajes" dentro de la serie.
 */

try {

  const animeAddP =
    String(
      data.serie?.name ||
      personaje.anime ||
      ''
    ).trim();

  if (!animeAddP) {

    console.error(
      '❌ ADDP: no se pudo determinar la serie del personaje:',
      personaje.name
    );

  } else {

    const serieKeyAddP =
      animeAddP
        .toLowerCase()
        .trim();

    let serieAddP =
      seriesCache.get(
        serieKeyAddP
      );

    if (!serieAddP) {

      /*
       * ID permanente para series creadas
       * durante ADDP.
       */
      const idsSeriesAddP =
        [...seriesCache.values()]
          .map(s => Number(s.id))
          .filter(
            n =>
              Number.isInteger(n) &&
              n > 0
          );

      const nuevoIdSerieAddP =
        idsSeriesAddP.length
          ? Math.max(...idsSeriesAddP) + 1
          : 1;

      serieAddP = {
        id: nuevoIdSerieAddP,
        name: animeAddP,
        characters: new Set()
      };

      seriesCache.set(
        serieKeyAddP,
        serieAddP
      );

      console.log(
        '🆕 ADDP: serie creada en cache:',
        animeAddP
      );

    }

    if (
      !serieAddP.characters ||
      typeof serieAddP.characters.add !== 'function'
    ) {

      serieAddP.characters =
        new Set(
          Array.isArray(
            serieAddP.characters
          )
            ? serieAddP.characters
            : []
        );

    }

    /*
     * Usamos el mismo formato de key utilizado
     * por el sistema de series.
     */
    const serieCharacterKey =
      personaje.key ||
      personaje.name
        .toLowerCase()
        .trim()
        .replace(/[^\w]+/g, '_')
        .replace(/^_+|_+$/g, '');

    serieAddP.characters.add(
      serieCharacterKey
    );

    const serieFileName =
      serieKeyAddP
        .replace(/[^\w]/g, '_');

    const serieFile =
      path.join(
        SERIES_DIR,
        serieFileName + '.json'
      );

    if (
      !fs.existsSync(
        SERIES_DIR
      )
    ) {

      fs.mkdirSync(
        SERIES_DIR,
        {
          recursive: true
        }
      );

    }

    fs.writeFileSync(
      serieFile,
      JSON.stringify(
        {
          id:
            Number(serieAddP.id),

          name:
            serieAddP.name,

          characters:
            [...serieAddP.characters]
        },
        null,
        2
      )
    );

    console.log(
      '✓ ADDP: personaje agregado a serie:',
      personaje.name
    );

    console.log(
      '   Serie:',
      serieAddP.name
    );

    console.log(
      '   Key:',
      serieCharacterKey
    );

    console.log(
      '   Total personajes:',
      serieAddP.characters.size
    );

    console.log(
      '   Archivo:',
      serieFile
    );

  }

} catch (error) {

  console.error(
    '❌ ADDP: error asociando personaje a serie:',
    error
  );

}

saveCharacters();



    console.log(
      "✓ ADDP personaje guardado:",
      personaje
    );

    /*
     * Espera de seguridad después de crear el personaje.
     */
    await new Promise(
      resolve => setTimeout(resolve, 3000)
    );

    /*
     * ADDP: acumular resultado.
     * No enviar mensaje individual.
     */
    registrarResultadoAddP(
      data,
      nombreEsperado,
      "Creado",
      pj.tag
    );

    /*
     * ========================================================
     * ADDP ETA REAL V3
     * Registrar cuï¿½nto tardï¿½ realmente este personaje.
     * ========================================================
     */
    registrarTiempoAddP(data);

    console.log(
      "• ADDP resultado acumulado:",
      nombreEsperado,
      "-> Creado"
    );

    data.index++;

    /*
     * ========================================================
     * ADDP ETA REAL V3
     * Actualizar progreso después de terminar el personaje.
     * ========================================================
     */
    data.progresoProcesados = data.index;

    /*
     * ========================================================
     * ADDP PROGRESO REAL V4
     * Confirmar que la referencia al mensaje sigue disponible.
     * ========================================================
     */
    console.log(
      "• ADDP V4: actualizando mensaje:",
      data.progresoMessageId || "SIN ID",
      "| progreso:",
      data.index + "/" + data.personajes.length
    );

    await actualizarProgresoAddP(
      sock,
      data,
      data.index,
      false
    );

    if (
      data.index >=
      data.personajes.length
    ) {

      console.log(
        "🏁 ADDP: cola terminada:",
        queueJid
      );

      await enviarResumenAddP(
        sock,
        queueJid,
        data
      );

      delete db.addpQueue[queueJid];

      saveDB();

      return true;
    }

    /*
     * ============================================================
     * ADDP CONTINUIDAD AUTOMÁTICA
     * ============================================================
     *
     * El personaje ya fue guardado correctamente.
     *
     * Antes de llamar al scheduler debemos liberar la transición
     * iniciada durante el procesamiento de la respuesta.
     *
     * Si addpTransition permanece en true, el scheduler interpreta
     * que ya existe otra transición activa y se detiene.
     */

    data.addpTransition = false;
    data.addpTransitionOwner = null;
    data.addpBusy = false;

    console.log(
      "◇ ADDP CONTINUIDAD: transición liberada:",
      queueJid,
      "| siguiente index:",
      data.index
    );

    saveDB();

    await programarSiguienteAddP(
      sock,
      queueJid
    );

    return true;
  }

  return false;
}


/* ============================================================
 * ADDP - MENSAJE DE PROGRESO
 * ============================================================
 *
 * Mantiene un único mensaje que se va editando conforme
 * termina cada personaje.
 * ============================================================
 */

async function crearMensajeProgresoAddP(
  sock,
  jid,
  serieNombre,
  total,
  quotedMsg
) {

  try {

    const texto =
      "◇ Serie: " +
      String(serieNombre || "Desconocida") +

      "\n\n" +

      "□ Personajes en cola: " +
      Number(total || 0) +

      "\n\n" +

      "⌛ Progreso: 0/" +
      Number(total || 0);

    const enviado = await sock.sendMessage(
      jid,
      {
        text: texto
      },
      quotedMsg
        ? { quoted: quotedMsg }
        : undefined
    );

    if (!enviado?.key?.id) {

      console.log(
        "⚠️ ADDP: no se pudo obtener ID del mensaje de progreso."
      );

      return null;
    }

    return {
      messageId: enviado.key.id,
      chatJid: jid,
      total: Number(total || 0),
      serieNombre: String(serieNombre || "Desconocida")
    };

  } catch (error) {

    console.error(
      "❌ ADDP: error creando mensaje de progreso:",
      error?.message || error
    );

    return null;
  }
}


/* ============================================================
 * EDITAR PROGRESO ADDP
 * ============================================================
 */

async function actualizarProgresoAddP(
  sock,
  data,
  procesados,
  finalizado = false
) {

  try {

    if (!data) {
      return false;
    }

    if (!data.progresoMessageId) {
      console.log(
        "⚠️ ADDP: la cola no tiene mensaje de progreso."
      );

      return false;
    }

    /*
     * Compatibilidad con colas creadas antes de V6.
     * Si no existe la clave completa, reconstruirla.
     */
    if (!data.progresoMessageKey) {
      data.progresoMessageKey = {
        remoteJid:
          data.progresoChatJid,

        fromMe:
          true,

        id:
          data.progresoMessageId
      };
    }

    if (!data.progresoChatJid) {
      console.log(
        "⚠️ ADDP: la cola no tiene progresoChatJid."
      );

      return false;
    }

    const total =
      Number(
        data.progresoTotal ??
        data.personajes?.length ??
        0
      );

    const actual =
      Math.max(
        0,
        Math.min(
          Number(procesados || 0),
          total
        )
      );

    let texto;

    if (finalizado || actual >= total) {

      texto =
        "◇ Serie: " +
        String(
          data.serieNombre ||
          data.serie?.name ||
          data.serie ||
          "Desconocida"
        ) +

        "\n\n" +

        "□ Personajes procesados: " +
        actual +
        "/" +
        total +

        "\n\n" +

        "✓ Proceso terminado.";

    } else {

      texto =
        "◇ Serie: " +
        String(
          data.serieNombre ||
          data.serie?.name ||
          data.serie ||
          "Desconocida"
        ) +

        "\n\n" +

        "□ Personajes en cola: " +
        total +

        "\n\n" +

        "⌛ Progreso: " +
        actual +
        "/" +
        total +

        "\n\n⌛ " +
        obtenerTextoETAAddP(data, actual);
    }

    console.log(
      "•••••••• ADDP EDIT DEBUG ••••••••"
    );

    console.log(
      "CHAT:",
      data.progresoChatJid
    );

    console.log(
      "ID:",
      data.progresoMessageId
    );

    console.log(
      "KEY:",
      JSON.stringify(
        data.progresoMessageKey,
        null,
        2
      )
    );

    console.log(
      "TEXTO:",
      texto
    );

    console.log(
      "••••••••••••••••••••••••••••••••"
    );

    await sock.sendMessage(
      data.progresoChatJid,
      {
        text: texto,

        edit:
          data.progresoMessageKey || {
            remoteJid:
              data.progresoChatJid,

            fromMe:
              true,

            id:
              data.progresoMessageId
          }
      }
    );

    console.log(
      "• ADDP PROGRESO:",
      actual + "/" + total
    );

    return true;

  } catch (error) {

    console.error(
      "⚠️ ADDP: error editando progreso:",
      error?.message || error
    );

    return false;
  }
}


/* ============================================================
 * FINALIZAR PROGRESO ADDP
 * ============================================================
 */

async function finalizarProgresoAddP(
  sock,
  data
) {

  const total =
    Number(
      data?.progresoTotal ??
      data?.personajes?.length ??
      0
    );

  return actualizarProgresoAddP(
    sock,
    data,
    total,
    true
  );
}


function iniciarWatchdogAddP(sock) {

  if (addpWatchdogRunning) {
    return;
  }

  addpWatchdogRunning = true;

  console.log(
    "👁️ ADDP WATCHDOG iniciado en modo RECUPERACIÓN."
  );

  setInterval(() => {

    try {

      const queues =
        db.addpQueue || {};

      for (const queueJid of Object.keys(queues)) {

        const data =
          queues[queueJid];

        if (!data) {
          continue;
        }

        /*
         * Solo colas ADDP activas.
         */
        if (data.iniciadoPorAddp !== true) {
          continue;
        }

        /*
         * Debe estar esperando una respuesta.
         */
        if (data.esperando !== true) {
          continue;
        }

        /*
         * Si ya existe un timer,
         * no crear otro.
         */
        if (data.timer) {
          continue;
        }

        const personaje =
          data.personajes?.[
            Number(data.index || 0)
          ];

        if (!personaje) {
          continue;
        }

        const nombre =
          String(
            personaje.nombre || ""
          ).trim();

        if (!nombre) {
          continue;
        }

        /*
         * Asegurar SIEMPRE el grupo de /creatinglogs.
         */
        const destino =
          typeof db.creatingLogs === "string" &&
          db.creatingLogs.endsWith("@g.us")
            ? db.creatingLogs
            : null;

        if (!destino) {

          console.log(
            "❌ ADDP WATCHDOG: no existe grupo /creatinglogs."
          );

          continue;
        }

        data.targetJid = destino;

        console.log(
          "👁️ ADDP WATCHDOG: recuperando timer:",
          queueJid,
          "| personaje:",
          nombre,
          "| destino:",
          destino
        );

        /*
         * Recuperar el timer perdido.
         */
        data.timer =
          setTimeout(
            async () => {

              const actual =
                db.addpQueue?.[queueJid];

              if (!actual) {
                return;
              }

              /*
               * Si ya llegó una respuesta,
               * detener el ciclo.
               */
              if (actual.esperando !== true) {

                actual.timer = null;

                saveDB();

                console.log(
                  "✓ ADDP WATCHDOG: respuesta recibida:",
                  nombre
                );

                return;
              }

              console.log(
                "⌛ ADDP WATCHDOG: 5 segundos sin respuesta:",
                nombre
              );

              /*
               * Liberar el timer ANTES del retry.
               */
              actual.timer = null;

              saveDB();

              /*
               * reintentarWinfoAddP() envía #winfo
               * y vuelve a crear otro timer de 5 segundos.
               */
              try {

                await reintentarWinfoAddP(
                  sock,
                  queueJid
                );

              } catch (error) {

                console.error(
                  "❌ ADDP WATCHDOG RETRY ERROR:",
                  error
                );

              }

            },
            5000
          );

        saveDB();

      }

    } catch (error) {

      console.error(
        "❌ ADDP WATCHDOG ERROR:",
        error
      );

    }

  }, 1000);
}

/*
 * ============================================================
 * ADDP - TRANSICIÓN SERIAL
 * ============================================================
 *
 * Una cola ADDP solamente puede tener una transición activa.
 *
 * Flujo:
 *
 * respuesta válida
 *      ↓
 * procesamiento
 *      ↓
 * programarSiguienteAddP()
 *      ↓
 * esperar 2 segundos
 *      ↓
 * liberar transición
 *      ↓
 * enviarSiguienteAddP()
 *
 * Esto evita que watchdog, retry o respuesta válida
 * puedan lanzar dos #winfo simultáneamente.
 */



/*
 * ============================================================
 * ADDP - VALIDAR TAG DANBOORU
 * ============================================================
 *
 * Valida que el tag recibido exista en Danbooru.
 *
 * Retorna siempre un objeto con esta estructura:
 *
 * {
 *   valido: true/false,
 *   error: false/true,
 *   tag: "...",
 *   mensaje: "..."
 * }
 *
 * Si Danbooru está temporalmente caído o responde con error,
 * se marca como error temporal para que ADDP no clasifique
 * incorrectamente el personaje.
 */

async function validarTagDanbooruAddP(tag) {

  console.log(
    '[ADDP] Validando tag Danbooru:',
    tag
  );

  if (!tag || typeof tag !== 'string') {

    return {
      valido: false,
      existe: false,
      error: false,
      permanente: true,
      motivo: 'tag vacío'
    };

  }

  const cleanTag =
    tag
      .trim()
      .replace(/\s+/g, '_');

  const url =
    'https://danbooru.donmai.us/tags.json?search%5Bname_matches%5D=' +
    encodeURIComponent(cleanTag + '*') +
    '&search%5Bhide_empty%5D=yes&limit=10';

  try {

    const controller =
      new AbortController();

    const timeout =
      setTimeout(
        () => controller.abort(),
        10000
      );

    let response;

    try {

      response =
        await fetch(
          url,
          {
            method: 'GET',
            headers: {
              'User-Agent':
                'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/151 Safari/537.36',
              'Accept':
                'application/json'
            },
            signal: controller.signal
          }
        );

    } finally {

      clearTimeout(timeout);

    }

    /*
     * ==========================================
     * DANBOORU NO DISPONIBLE
     * ==========================================
     */

    if (
      response.status === 403 ||
      response.status === 429 ||
      response.status >= 500
    ) {

      console.log(
        '[ADDP] Danbooru temporalmente no disponible:',
        response.status
      );

      return {
        valido: false,
        existe: false,
        error: true,
        temporal: true,
        permanente: false,
        status: response.status,
        motivo:
          'Danbooru temporalmente no disponible'
      };

    }

    /*
     * ==========================================
     * TAG NO ENCONTRADO
     * ==========================================
     */

    if (response.status === 404) {

      console.log(
        '[ADDP] Tag no encontrado:',
        cleanTag
      );

      return {
        valido: false,
        existe: false,
        error: false,
        temporal: false,
        permanente: true,
        status: 404,
        motivo: 'Tag no encontrado'
      };

    }

    if (!response.ok) {

      console.log(
        '[ADDP] Error HTTP Danbooru:',
        response.status
      );

      return {
        valido: false,
        existe: false,
        error: true,
        temporal: true,
        permanente: false,
        status: response.status,
        motivo:
          'Error HTTP temporal de Danbooru'
      };

    }

    const resultados =
      await response.json();

    if (
      !Array.isArray(resultados) ||
      resultados.length === 0
    ) {

      console.log(
        '[ADDP] Tag no encontrado:',
        cleanTag
      );

      return {
        valido: false,
        existe: false,
        error: false,
        temporal: false,
        permanente: true,
        motivo: 'Tag no encontrado'
      };

    }

    /*
     * Buscar coincidencia exacta.
     */

    const exacto =
      resultados.find(
        x =>
          String(x.name || '').toLowerCase() ===
          cleanTag.toLowerCase()
      );

    if (!exacto) {

      console.log(
        '[ADDP] Tag no coincide exactamente:',
        cleanTag
      );

      return {
        valido: false,
        existe: false,
        error: false,
        temporal: false,
        permanente: true,
        motivo:
          'No existe coincidencia exacta'
      };

    }

    console.log(
      '[ADDP] Tag válido:',
      cleanTag
    );

    return {
      valido: true,
      existe: true,
      error: false,
      temporal: false,
      permanente: false,
      tag: exacto.name
    };

  } catch (error) {

    console.log(
      '[ADDP] Error consultando Danbooru:',
      error?.message || error
    );

    /*
     * Timeout / red / DNS / fetch:
     * NO es un tag inválido.
     */

    return {
      valido: false,
      existe: false,
      error: true,
      temporal: true,
      permanente: false,
      motivo:
        'Error de conexión con Danbooru',
      detalle:
        error?.message || String(error)
    };

  }

}

async function programarSiguienteAddP(sock, queueJid) {
    /*
     * ========================================================
     * GUARDIA DANBOORU
     * ========================================================
     *
     * Si Danbooru está temporalmente bloqueado/no disponible,
     * el scheduler NO debe volver a lanzar
     * enviarSiguienteAddP().
     */

    const __addpDanbooruPaused =
      db.addpQueue?.[queueJid]?.addpPausadaDanbooru === true;

    if (__addpDanbooruPaused) {

      console.log(
        "⏸️ ADDP SCHEDULER BLOQUEADO POR DANBOORU:",
        queueJid
      );

      return;
    }



  const __addpQueueGuard = db.addpQueue?.[queueJid];
  if (
    !__addpQueueGuard ||
    __addpQueueGuard.iniciadoPorAddp !== true ||
    __addpQueueGuard.origenAddp !== "/addp"
  ) {
    console.log("⏩ ADDP SCHEDULER BLOQUEADO: cola no originada por /addp.");
    return;
  }
  const data = db.addpQueue?.[queueJid];

  if (!data) {
    console.log(
      "⚠️ ADDP SCHEDULER: cola inexistente:",
      queueJid
    );
    return;
  }

  /*
   * ==========================================================
   * EVITAR DOS SCHEDULERS SIMULTÁNEOS
   * ==========================================================
   */

  if (data.addpTransition === true) {
    console.log(
      "⏭️ ADDP SCHEDULER: transición ya activa:",
      queueJid
    );
    return;
  }

  /*
   * ==========================================================
   * CREAR UNA ÚNICA TRANSICIÓN
   * ==========================================================
   */

  data.addpTransition = true;
  data.addpTransitionOwner = "scheduler";
  data.addpBusy = true;
  data.esperando = false;

  clearTimeout(data.timer);
  data.timer = null;

  saveDB();

  console.log(
    "🔒 ADDP SCHEDULER: transición iniciada:",
    queueJid
  );

  try {

    /*
     * ========================================================
     * CICLO SERIAL
     *
     * Un solo scheduler puede avanzar varios duplicados.
     *
     * Ejemplo:
     *
     * Chifuyu -> duplicado
     * Manjirou -> duplicado
     * Senju -> duplicado
     * Keisuke -> nuevo
     *
     * No se crean schedulers anidados.
     * ========================================================
     */

    while (true) {

      const actual =
        db.addpQueue?.[queueJid];

      if (!actual) {
        console.log(
          "ℹ️ ADDP SCHEDULER: cola eliminada:",
          queueJid
        );
        return;
      }

      /*
       * Si algún personaje ya dejó esperando un /winfo,
       * el ciclo termina.
       */

      if (actual.esperando === true) {

        console.log(
          "⏳ ADDP SCHEDULER: esperando respuesta:",
          queueJid,
          "| index:",
          actual.index
        );

        return;
      }

      /*
       * Fin de cola.
       */

      if (
        !Array.isArray(actual.personajes) ||
        actual.index >= actual.personajes.length
      ) {

        console.log(
          "🏁 ADDP SCHEDULER: cola terminada:",
          queueJid
        );

        await enviarResumenAddP(
          sock,
          queueJid,
          actual
        );

        delete db.addpQueue[queueJid];

        saveDB();

        return;
      }

      /*
       * Esperar 2 segundos entre personajes.
       *
       * Esto también evita enviar demasiados mensajes
       * consecutivos a WhatsApp.
       */

      await new Promise(
        resolve => setTimeout(resolve, 2000)
      );

      const antesDeEnviar =
        db.addpQueue?.[queueJid];

      if (!antesDeEnviar) {
        return;
      }

      if (antesDeEnviar.esperando === true) {
        return;
      }

      console.log(
        "➡️ ADDP SCHEDULER: enviando siguiente:",
        queueJid,
        "| index:",
        antesDeEnviar.index,
        "| personaje:",
        antesDeEnviar.personajes?.[
          antesDeEnviar.index
        ]?.nombre
      );

      /*
       * enviarSiguienteAddP solamente procesa UN personaje.
       *
       * Si es nuevo:
       *   deja esperando=true
       *   y el while termina.
       *
       * Si es duplicado:
       *   incrementa index
       *   deja esperando=false
       *   y el while continúa con el siguiente.
       */

      await enviarSiguienteAddP(
        sock,
        queueJid
      );

      const despues =
        db.addpQueue?.[queueJid];

      if (!despues) {
        return;
      }

      /*
       * Personaje nuevo:
       * hay un /winfo pendiente.
       */

      if (despues.esperando === true) {

        console.log(
          "⏳ ADDP SCHEDULER: #winfo enviado, esperando:",
          queueJid,
          "| personaje:",
          despues.personajes?.[
            despues.index
          ]?.nombre
        );

        return;
      }

      /*
       * Si no está esperando, significa que el personaje
       * fue descartado, normalmente porque ya existe.
       *
       * El while continï¿½a automï¿½ticamente.
       */

      console.log(
        "⏭️ ADDP SCHEDULER: personaje descartado, continuando:",
        queueJid,
        "| siguiente index:",
        despues.index
      );
    }

  } catch (error) {

    console.error(
      "❌ ADDP SCHEDULER ERROR:",
      error
    );

    const actual =
      db.addpQueue?.[queueJid];

    if (actual) {
      actual.esperando = false;
      actual.addpBusy = false;
      actual.addpTransition = false;
      actual.addpTransitionOwner = null;
      actual.transition = false;

      saveDB();
    }

    throw error;

  } finally {

    const finalData =
      db.addpQueue?.[queueJid];

    if (finalData) {

      /*
       * Si hay una respuesta pendiente, la cola sigue activa
       * pero ya no debe mantener el lock de transición.
       */

      finalData.addpTransition = false;
      finalData.addpTransitionOwner = null;

      if (finalData.esperando === true) {
        finalData.addpBusy = false;
      } else {
        finalData.addpBusy = false;
      }

      finalData.transition = false;

      saveDB();

      console.log(
        "◇ ADDP SCHEDULER: transición liberada:",
        queueJid
      );
    }
  }
}

async function enviarSiguienteAddP(
  sock,
  queueJid
) {

  console.log(
    "→ ENTR¿ enviarSiguienteAddP:",
    queueJid
  );

  const data =
    db.addpQueue?.[queueJid];

  if (!data) {

    console.log(
      "❌ ADDP: no existe la cola:",
      queueJid
    );

    return;
  }

  /*
   * ==========================================================
   * LOCK DE SEGURIDAD
   * ==========================================================
   *
   * enviarSiguienteAddP NO debe enviar nada si otra operación
   * ya está procesando la cola.
   */

  if (data.esperando === true) {

    console.log(
      "⏳ ADDP: ya espera respuesta:",
      queueJid
    );

    return;
  }

  /*
   * addpTransition significa que esta función fue llamada
   * como parte de una transición controlada.
   *
   * Si es una llamada externa mientras otra transición está
   * activa, se rechaza.
   */

  if (
    data.addpTransition === true &&
    data.addpTransitionOwner !== "scheduler"
  ) {

    console.log(
      "🔒 ADDP: transición activa, ignorando llamada duplicada:",
      queueJid
    );

    return;
  }

  if (
    data.addpBusy === true &&
    data.addpTransition !== true
  ) {

    console.log(
      "🔒 ADDP: cola ocupada, ignorando llamada duplicada:",
      queueJid
    );

    return;
  }

  if (!Array.isArray(data.personajes)) {

    console.log(
      "❌ ADDP: personajes no es un arreglo."
    );

    return;
  }

  const posicion =
    Number(data.index || 0);

  const personaje =
    data.personajes[posicion];

  /*
   * ==========================================================
   * FIN DE COLA
   * ==========================================================
   */

  if (!personaje) {

    console.log(
      "🏁 ADDP: cola terminada:",
      queueJid
    );

    /*
     * Enviar un único resumen antes de eliminar
     * la cola.
     */

    await enviarResumenAddP(
      sock,
      queueJid,
      data
    );

    delete db.addpQueue[queueJid];

    saveDB();

    return;
  }

  const nombre =
    String(
      personaje.nombre || ""
    ).trim();

  /*
   * Personaje inválido:
   * avanzar usando transición serial.
   */

  if (!nombre) {

    console.log(
      "⚠️ ADDP: personaje sin nombre."
    );

    data.index =
      posicion + 1;

    data.addpBusy = false;
    data.addpTransition = false;

    saveDB();

    return programarSiguienteAddP(
      sock,
      queueJid
    );
  }

  const grupoCreatingLogs =
    typeof db.creatingLogs === "string" &&
    db.creatingLogs.endsWith("@g.us")
      ? db.creatingLogs
      : null;

  if (!grupoCreatingLogs) {

    console.log(
      "❌ ADDP: no hay grupo configurado en /creatinglogs."
    );

    console.log(
      "Valor actual:",
      db.creatingLogs
    );

    return;
  }

  /*
   * ==========================================================
   * PREPARAR ESPERA
   * ==========================================================
   */

  data.addpBusy = true;
  data.esperando = true;

  /*
   * Una vez que estamos enviando el nuevo #winfo,
   * la transición deja de estar activa.
   */
  data.addpTransition = false;

  data.addpTransitionOwner = null;

  data.messageId = null;

  data.targetJid =
    grupoCreatingLogs;

  /*
   * El contador de retries solamente se reinicia
   * cuando comenzamos un personaje nuevo.
   */
  data.addpRetries = 0;

  clearTimeout(data.timer);
  data.timer = null;

  saveDB();

  console.log(
    "• ADDP PERSONAJE:",
    nombre
  );

  /*
   * ==========================================================
   * VALIDACIÓN INTERNA DEL TAG EN DANBOORU
   * ==========================================================
   *
   * El tag debe existir en Danbooru y pertenecer
   * a la categoría de personajes.
   *
   * Si es incorrecto:
   * - NO se envía #winfo
   * - NO se crea el personaje
   * - se registra el resultado
   * - ADDP continúa con el siguiente
   */

  const validacionTag =
    await validarTagDanbooruAddP(
      personaje.tag
    );

  /*
   * Error temporal de Danbooru:
   * dejamos la cola detenida para que el watchdog/
   * operador pueda reintentarlo sin clasificar
   * incorrectamente el tag.
   */
  if (validacionTag.error) {

      /*
       * ======================================================
       * ADDP - ERROR DE VALIDACIÓN DANBOORU
       * ======================================================
       *
       * Separamos:
       *
       * 1. Error temporal de Danbooru
       *    -> PAUSAR
       *
       * 2. Tag inexistente / inválido
       *    -> OMITIR PERSONAJE
       *    -> AVANZAR INDEX
       *
       * Nunca se crea un personaje cuyo tag sea inválido.
       */

      const __tagErrorStatus =
        Number(
          validacionTag.status ||
          validacionTag.statusCode ||
          validacionTag.httpStatus ||
          0
        );

      const __tagErrorMessage =
        String(
          validacionTag.message ||
          validacionTag.errorMessage ||
          validacionTag.reason ||
          ''
        ).toLowerCase();

      /*
       * ------------------------------------------------------
       * ERRORES TEMPORALES
       * ------------------------------------------------------
       *
       * 403 = bloqueo / acceso denegado
       * 429 = rate limit
       * 5xx = error servidor
       */

      const __danbooruTemporal =
        __tagErrorStatus === 403 ||
        __tagErrorStatus === 429 ||
        (__tagErrorStatus >= 500 && __tagErrorStatus <= 599) ||
        __tagErrorMessage.includes('403') ||
        __tagErrorMessage.includes('429') ||
        __tagErrorMessage.includes('rate limit') ||
        __tagErrorMessage.includes('temporarily') ||
        __tagErrorMessage.includes('temporalmente') ||
        __tagErrorMessage.includes('forbidden');

      if (__danbooruTemporal) {

        console.log(
          "⏸️ ADDP: Danbooru temporalmente no disponible:",
          __tagErrorStatus || __tagErrorMessage
        );

        /*
         * NO avanzar index.
         *
         * El personaje queda pendiente para /reanudaraddp.
         */

        data.esperando = false;
        data.addpBusy = false;
        data.addpTransition = false;

        data.addpEstado = "pausada-danbooru";
        data.addpPausadaDanbooru = true;
        data.addpDanbooruError = true;
        data.addpDanbooruTag = personaje.tag;
        data.addpDanbooruPauseAt = Date.now();

        if (data.timer) {
          clearTimeout(data.timer);
          data.timer = null;
        }

        saveDB();

        console.log(
          "⏸️ ADDP: cola pausada. Personaje conservado:",
          personaje.nombre,
          "| index:",
          data.index
        );

        return;
      }

      /*
       * ------------------------------------------------------
       * TAG INVÁLIDO / NO ENCONTRADO
       * ------------------------------------------------------
       *
       * Danbooru respondió pero el tag no es válido.
       *
       * NO crear personaje.
       * SÍ avanzar al siguiente.
       */

      console.log(
        " ADDP: tag inválido/no encontrado:",
        personaje.tag
      );

      console.log(
        "⏭️ ADDP: personaje omitido:",
        personaje.nombre
      );

      data.esperando = false;
      data.addpBusy = false;
      data.addpTransition = false;

      /*
       * Avanzamos exactamente UN personaje.
       */

      data.index = Number(data.index || 0) + 1;

      /*
       * Limpiar estados de pausa anteriores.
       */

      data.addpPausadaDanbooru = false;
      data.addpDanbooruError = false;
      data.addpDanbooruTag = null;
      data.addpDanbooruPauseAt = null;

      if (data.timer) {
        clearTimeout(data.timer);
        data.timer = null;
      }

      saveDB();

      console.log(
        "➡️ ADDP: siguiente index:",
        data.index
      );

      /*
       * Continuar automáticamente.
       */

      setTimeout(() => {

        try {

          programarSiguienteAddP(
            sock,
            queueJid
          ).catch(error => {

            console.error(
              " ADDP: error continuando después de tag inválido:",
              error
            );

          });

        } catch (error) {

          console.error(
            "❌ ADDP: error iniciando siguiente personaje:",
            error
          );

        }

      }, 250);

      return;
    }


  /*
   * ============================================================
   * ADDP -> TAG SIN BLOQUEO
   * ============================================================
   *
   * El tag ya fue proporcionado manualmente o encontrado
   * mediante el buscador automático.
   *
   * NO detener ADDP aunque la validación externa diga
   * que el tag no es válido.
   *
   * El #winfo será quien determine finalmente si el
   * personaje puede procesarse.
   */

  console.log(
    "ℹ️ ADDP: omitiendo bloqueo de validaci¿n Danbooru:",
    personaje.tag
  );

  console.log(
    "✓ ADDP: TAG DANBOORU VÁLIDO:",
    validacionTag.tag
  );

  console.log(
    "📍 ADDP DESTINO:",
    grupoCreatingLogs
  );

  console.log(
    "📤 ADDP ENVIANDO:",
    "#winfo " + nombre
  );

  /*
   * ==========================================================
   * ENVIAR #winfo
   * ==========================================================
   */

  try {

    const enviado =
      await sock.sendMessage(
        grupoCreatingLogs,
        {
          text:
            "#winfo " + nombre
        }
      );

    /*
     * Confirmar que la cola sigue existiendo.
     */
    const actual =
      db.addpQueue?.[queueJid];

    if (!actual) {
      return;
    }

    actual.messageId =
      enviado?.key?.id || null;

    actual.targetJid =
      grupoCreatingLogs;

    actual.esperando = true;
    actual.addpBusy = true;

    saveDB();

    console.log(
      "✓ ADDP: #winfo enviado:",
      nombre
    );

    console.log(
      "🆔 Mensaje:",
      actual.messageId
    );

    /*
     * ==========================================================
     * TIMER INICIAL ADDP
     * ==========================================================
     *
     * El #winfo original también debe tener un temporizador.
     *
     * Si en 5 segundos no llega una respuesta válida,
     * reintentarWinfoAddP() reenviará #winfo al grupo
     * configurado mediante /creatinglogs.
     */

    clearTimeout(actual.timer);

    actual.timer = setTimeout(
      async () => {

        const cola =
          db.addpQueue?.[queueJid];

        if (!cola) {
          return;
        }

        /*
         * Si ya llegó una respuesta válida,
         * no reenviar.
         */
        if (cola.esperando !== true) {

          console.log(
            "✓ ADDP: respuesta recibida antes del primer retry:",
            queueJid
          );

          return;
        }

        console.log(
          "⌛ ADDP: 5 segundos sin respuesta:",
          nombre
        );

        await reintentarWinfoAddP(
          sock,
          queueJid
        );

      },
      5000
    );

    saveDB();

  } catch (error) {

    console.error(
      "❌ ADDP: error enviando #winfo:",
      error
    );

    const actual =
      db.addpQueue?.[queueJid];

    if (!actual) {
      return;
    }

    actual.esperando = false;
    actual.addpBusy = false;
    actual.addpTransition = false;
    actual.messageId = null;
    actual.timer = null;

    saveDB();

    try {

      await sock.sendMessage(
        queueJid,
        {
          text:
            "❌ ERROR ADDP\n\n" +
            "No se pudo enviar #winfo.\n\n" +
            "Personaje: " + nombre + "\n\n" +
            "Error:\n" +
            (error.message || error)
        }
      );

    } catch (sendError) {

      console.error(
        "❌ ADDP: error enviando aviso:",
        sendError
      );
    }

    return;
  }
}


async function recibirPersonajeAddP(sock,msg){

    /*
     * SEGURIDAD ADDP
     *
     * Solo una cola creada explícitamente por /addp
     * puede ser procesada aquí.
     */

    const jid = msg.key.remoteJid;
    
    // Buscar la cola tanto por sourceJid como por targetJid
    let data = db.addpQueue?.[jid];
    
    // Si no se encuentra por JID directo, buscar por targetJid
    if (!data) {
        for (const [queueJid, queueData] of Object.entries(db.addpQueue || {})) {
            if (queueData && queueData.targetJid === jid) {
                data = queueData;
                break;
            }
        }
    }

    if (
        !data ||
        data.iniciadoPorAddp !== true ||
        data.origenAddp !== "/addp" ||
        data.addpEstado !== "activa"
    ) {
        console.log(
            " ADDP IGNORADO: cola no válida para recibirPersonajeAddP():",
            jid
        );
        return false;
    }

    /*
     * Si ya existe un #winfo pendiente,
     * no procesar otra respuesta.
     */

    if (data.esperando === true) {
        return false;
    }

const body =
 msg.message?.conversation ||
 msg.message?.extendedTextMessage?.text ||
 "";


 if(!body.includes(">"))
  return false;


 const lineas =
 body.split("\n")
 .filter(x=>x.includes(">"));

 for(const linea of lineas){

 const partes =
 linea.split(">");


 const nombre =
 partes[0]
 .replace(/^\/addp\s+\d+\s*/i,"")
 .trim();

 const tag =
 partes[1]?.trim();


 if(!nombre || !tag)
  return false;


 data.personajes.push({
  nombre,
  tag
 });


 await sock.sendMessage(
  jid,
  {
   text:
   "✓ Agregado: "+nombre+
   "\n🏷️ Tag: "+tag+
   "\n\nEscribe otro o espera."
  },
  {quoted:msg}
 );


 /*
  * ==========================================================
  * ADDP - INICIO AUTOMÁTICO DESPUÉS DE AGREGAR PERSONAJE
  * ==========================================================
  *
  * Después de agregar un personaje debemos asegurarnos de que
  * la cola realmente entre al flujo:
  *
  *   programarSiguienteAddP()
  *        ↓
  *   enviarSiguienteAddP()
  *        ↓
  *   #winfo nombre
  *
  * No dependemos de que personajes.length === 1.
  * El scheduler y sus locks se encargan de evitar duplicados.
  */

 data.addpEstado = "activa";

 const posicionActual =
  Number(data.index || 0);

 const personajeActual =
  data.personajes?.[posicionActual];

 console.log(
  "◆ ADDP POST-AGREGADO:",
  jid
 );

 console.log(
  "   personajes:",
  data.personajes.length
 );

 console.log(
  "   index:",
  posicionActual
 );

 console.log(
  "   actual:",
  personajeActual?.nombre || "ninguno"
 );

 console.log(
  "   esperando:",
  data.esperando
 );

 console.log(
  "   busy:",
  data.addpBusy
 );

 console.log(
  "   transition:",
  data.addpTransition
 );

 /*
  * Si ya está procesando un #winfo,
  * no lanzar otro.
  */
 if (
  data.esperando !== true &&
  data.addpBusy !== true &&
  personajeActual
 ) {
  /*
   * POST-AGREGADO SOLO PERTENECE A /addp.
   * /ainfo/#ainfo/#addanime no pueden activar este flujo.
   */
  const __postAddpData =
    db.addpQueue?.[jid];

  if (
    !__postAddpData ||
    __postAddpData.iniciadoPorAddp !== true ||
    __postAddpData.origenAddp !== "/addp"
  ) {
    console.log(
      "⏩ ADDP POST-AGREGADO BLOQUEADO: no procede de /addp."
    );
    return;
  }


  console.log(
   "🚀 ADDP POST-AGREGADO: iniciando scheduler:",
   jid
  );

  await programarSiguienteAddP(
   sock,
   jid
  );

 } else {

  console.log(
   "⏭️ ADDP POST-AGREGADO: scheduler no iniciado:",
   jid
  );

 }


 }

 return true;

}






/*
 * ============================================================
 * ADDP - RESULTADOS ACUMULADOS
 * ============================================================
 */

function registrarResultadoAddP(
  data,
  nombre,
  estado,
  tag = ""
) {

  if (!data) {
    return;
  }

  if (!Array.isArray(data.resultados)) {
    data.resultados = [];
  }

  data.resultados.push({
    nombre:
      String(nombre || "").trim(),

    estado:
      String(estado || "").trim(),

    tag:
      String(tag || "").trim()
  });

}


/*
 * Envía UN SOLO mensaje con todos los resultados
 * cuando termina la cola ADDP.
 */

async function enviarResumenAddP(
  sock,
  queueJid,
  data
) {

  if (!data) {
    return;
  }

  if (data.addpResumenEnviado === true) {
    return;
  }

  const resultados =
    Array.isArray(data.resultados)
      ? data.resultados
      : [];

  if (!resultados.length) {
    return;
  }

  let texto =
    "◇ RESULTADO ADDP\n\n";

  texto += resultados
    .map(resultado => {

      const nombre =
        resultado.nombre ||
        "Desconocido";

      const estado =
        resultado.estado ||
        "Sin resultado";

      const tag =
        resultado.tag || "";

      return (
        nombre +
        " — " +
        estado +
        (
          tag
            ? " [" + tag + "]"
            : ""
        )
      );

    })
    .join("\n");

  try {

    await sock.sendMessage(
      queueJid,
      {
        text: texto
      }
    );

    data.addpResumenEnviado = true;

    saveDB();

    console.log(
      "📋 ADDP: resumen final enviado:",
      queueJid
    );

  } catch (error) {

    console.error(
      "❌ ADDP: error enviando resumen:",
      error
    );

  }

}



function normalizarNombreAddP(nombre) {
  return String(nombre || "")
    .trim()
    .replace(/^\d+\s+/u, "")
    .toLowerCase()
    .normalize("NFD")
    .replace(/[\u0300-\u036f]/g, "")
    .replace(/[^a-z0-9]/g, "");
}

function nombresEquivalentesAddP(esperado, recibido) {
  const aliases = {
    "keisukebajo": "keisukebaji",
    "manjirou": "sano_manjirou",
    "senjuakashi": "akashi_seijuurou",
    "kenryuuguuji": "ryuuguuji_ken",
    "hinatatachibana": "tachibana_hinata_(tokyo_revengers)",
    "takemichihanagaki": "hanagaki_takemichi",
    "emmasano": "sano_emma",
    "izanakurokawa": "kurokawa_izana",
    "hajimekokonoi": "kokonoi_hajime",
    "ranhaitani": "haitani_ran",
    "kazutorahanemiya": "hanemiya_kazutora",
    "souyakawata": "kawata_souya",
    "shinichirousano": "sano_shinichirou",
    "taijushiba": "shiba_taiju",
    "rindouhaitani": "haitani_rindou",
    "takashimitsuya": "mitsuya_takashi",
    "akaneinui": "inui_akane",
    "yuzuhashiba": "shiba_yuzuha",
    "wakasaimaushi": "imaushi_wakasa",
    "seishuuinui": "inui_seishu",
    "hakkaishiba": "shiba_hakkai",
    "kakuchohitto": "hitto_kakuchou",
    "nahoyakawata": "kawata_nahoya",
    "tettakisaki": "kisaki_tetta",
    "takeomiakashi": "akashi_takeomi",
    "atsushisendou": "sendou_atsushi",
    "harukihayashida": "hayashida_haruki",
    "naototachibana": "tachibana_naoto"
  };

  const a = normalizarNombreAddP(esperado);
  const b = normalizarNombreAddP(recibido);

  if (a === b) return true;

  return aliases[a] === b;
}




function saveCharacters() {
  saveCharactersQueue =
    saveCharactersQueue
      .then(() =>
        fs.promises.writeFile(
          CHARACTERS_FILE,
          JSON.stringify(
            charactersCache,
            null,
            2
          )
        )
      )
      .catch(console.error);
}

function findCharacter(query){

  query =
    query
      .toLowerCase()
      .trim();

  let char =
    characterMap.get(query);

  if(char)
    return char;

  char =
    charactersCache.find(
      c =>
        c.name
         .toLowerCase()
         .startsWith(query)
    );

  if(char)
    return char;

  char =
    charactersCache.find(
      c =>
        c.name
         .toLowerCase()
         .includes(query)
    );

  return char || null;

}

function findSeries(query){

  query =
    query
      .toLowerCase()
      .trim();

  for(const serie of seriesCache.values()){

    if(
      serie.name
        .toLowerCase()
        .startsWith(query)
    ){
      return serie;
    }

    if(
      serie.name
        .toLowerCase()
        .includes(query)
    ){
      return serie;
    }

  }

  for(const official in db.seriesAliases){

    const aliases =
      db.seriesAliases[official];

    if(
      official
        .toLowerCase()
        .startsWith(query)
    ){

      return seriesCache.get(
        official.toLowerCase()
      );

    }

    if(
      aliases.some(
        a =>
          a.includes(query)
      )
    ){

      return seriesCache.get(
        official.toLowerCase()
      );

    }

  }

  return null;

}

function nextPendingCharacterId(){

  const id =
    db.pendingCharacterId;

  db.pendingCharacterId++;

  saveDB();

  return id;

}

function addPendingCharacter(data){

  const id =
    nextPendingCharacterId();

  const pending = {

    id,

    ...data,

    createdAt:
      Date.now(),

    status:
      'pending'

  };

  db.pendingCharacters.push(
    pending
  );

  saveDB();

  return pending;

}

function getPendingCharacter(id){

  return db.pendingCharacters.find(

    p =>

      p.id === Number(id)

  );

}

function removePendingCharacter(id){

  db.pendingCharacters =
    db.pendingCharacters.filter(

      p =>

        p.id !== Number(id)

    );

  saveDB();

}

function buildOwnerIndex() {
  global.ownerIndex = {};
  for (const c of charactersCache) {
    if (!c.claimedBy) continue;
    for (const [groupId, claimData] of Object.entries(c.claimedBy)) {
      if (!claimData || !claimData.user) continue;
      if (!global.ownerIndex[groupId]) global.ownerIndex[groupId] = {};
      if (!global.ownerIndex[groupId][claimData.user]) global.ownerIndex[groupId][claimData.user] = new Set();
      global.ownerIndex[groupId][claimData.user].add(c.key);
    }
  }
}

function getCharacterImages(key) {
  if (!fs.existsSync(GACHA_IMAGES)) return [];
  return fs.readdirSync(GACHA_IMAGES).filter(f => f.startsWith(key + '_'));
}
function getCharacterImage(char) {
    const sources = [];

    // Imágenes locales
    const imgs = getCharacterImages(char.key);
    for (const img of imgs) {
        sources.push({
            type: 'local',
            value: path.join(GACHA_IMAGES, img)
        });
    }

    // Imagen de Danbooru
    if (char.image) {
        sources.push({
            type: 'url',
            value: char.image
        });
    }

    if (!sources.length) return null;

    return sources[Math.floor(Math.random() * sources.length)];
}

function preloadImages() {
  if (!fs.existsSync(GACHA_IMAGES)) return;
  for (const file of fs.readdirSync(GACHA_IMAGES)) {
    const fp = path.join(GACHA_IMAGES, file);
    try { imageCache.set(fp, fs.readFileSync(fp)); } catch {}
  }
}
preloadImages();

// ━━━━━━━ SISTEMA DE SERIES ━━━━━━━
const seriesCache = new Map(); // serieName -> { name, characters: Set<key> }

// ============================================================
// PROTECCION DE SERIES EN DATABASE.JSON
// - Copia todas las series en db.seriesBackup
// - Restaura series que perdieron su archivo JSON
// ============================================================
function sincronizarSeriesDatabase() {
  try {
    db.seriesBackup ??= {};

    for (const [key, serie] of seriesCache.entries()) {
      db.seriesBackup[key] = {
        id: Number(serie.id) || 0,
        name: String(serie.name || ''),
        characters: Array.from(serie.characters || []),
        owner: serie.owner || null,
        updatedAt: Date.now()
      };
    }

    if (typeof saveDB === 'function') saveDB();
  } catch (e) {
    console.error('[SERIES BACKUP]', e);
  }
}

function restaurarSeriesDesdeBackup() {
  if (!db.seriesBackup || typeof db.seriesBackup !== 'object') {
    return;
  }

  fs.mkdirSync(SERIES_DIR, { recursive: true });

  let restauradas = 0;

  for (const [key, backup] of Object.entries(db.seriesBackup)) {
    if (!backup || !backup.name) continue;
    if (seriesCache.has(key)) continue;

    const characters = new Set();
    for (const rawKey of (backup.characters || [])) {
      const charKey = String(rawKey || '').trim();
      if (charKey && characterKeyMap.has(charKey)) {
        characters.add(charKey);
      }
    }

    const serie = {
      id: Number(backup.id) || 0,
      name: String(backup.name || '').trim(),
      characters,
      owner: backup.owner || null
    };

    seriesCache.set(key, serie);

    try {
      const fileName = key.replace(/[^\w]/g, '_');
      fs.writeFileSync(
        path.join(SERIES_DIR, fileName + '.json'),
        JSON.stringify(
          {
            id: serie.id,
            name: serie.name,
            owner: serie.owner,
            characters: [...serie.characters]
          },
          null,
          2
        )
      );
    } catch (e) {
      console.error('[SERIES RESTORE]', e);
    }

    restauradas++;
  }

  if (restauradas > 0) {
    console.log('[SERIES BACKUP] Series restauradas:', restauradas);
  }
}
function loadSeries() {

  console.log('📚 Cargando sistema de series...');

  seriesCache.clear();

  /*
   * ============================================================
   * LOAD SERIES DEFINITIVO
   * ============================================================
   *
   * Las series almacenan únicamente las keys.
   * Los personajes reales se obtienen desde characterKeyMap.
   *
   * No se eliminan keys del JSON.
   * Solo se ignoran temporalmente las que realmente no existan
   * en characters.json.
   */

  if (!fs.existsSync(SERIES_DIR)) {

    console.log(
      '⚠️ SERIES_DIR no existe:',
      SERIES_DIR
    );

    return;

  }

  /*
   * Asegurar que characters.json esté cargado.
   */

  if (
    !Array.isArray(charactersCache) ||
    !charactersCache.length
  ) {

    loadCharactersCache();

  }

  /*
   * Reconstruir mapa por seguridad.
   */

  characterKeyMap.clear();

  for (const character of charactersCache) {

    if (
      character &&
      character.key
    ) {

      characterKeyMap.set(
        String(character.key),
        character
      );

    }

  }

  const files =
    fs.readdirSync(SERIES_DIR)
      .filter(
        file =>
          file.endsWith('.json')
      );

  console.log(
    '📁 Archivos de series:',
    files.length
  );

  let cargadas = 0;
  let personajesAsociados = 0;

  for (const file of files) {

    try {

      const filePath =
        path.join(
          SERIES_DIR,
          file
        );

      const data =
        JSON.parse(
          fs.readFileSync(
            filePath,
            'utf8'
          )
        );

      if (
        !data ||
        !data.name ||
        !Array.isArray(
          data.characters
        )
      ) {

        console.log(
          '⚠️ Serie ignorada:',
          file
        );

        continue;

      }

      /*
       * ID permanente.
       */

      const id =
        Number(data.id);

      /*
       * Mantener solamente IDs válidos.
       * Si falta el ID, se conserva 0 temporalmente
       * para no alterar los archivos desde aquí.
       */

      const serieId =
        Number.isInteger(id) &&
        id > 0
          ? id
          : 0;

      /*
       * Construir Set usando las keys del JSON.
       */

      const characters =
        new Set();

      for (
        const rawKey
        of data.characters
      ) {

        const key =
          String(
            rawKey || ''
          ).trim();

        if (!key) {
          continue;
        }

        /*
         * La key debe existir realmente
         * en characters.json.
         */

        if (
          characterKeyMap.has(key)
        ) {

          characters.add(key);

          personajesAsociados++;

        }

      }

      const serie = {

        id: serieId,

        name:
          String(
            data.name
          ).trim(),

        characters

      };

      seriesCache.set(
        serie.name.toLowerCase(),
        serie
      );

      cargadas++;

      console.log(
        '✓ Serie:',
        serie.id,
        '->',
        serie.name,
        '| Personajes:',
        serie.characters.size
      );

    } catch (err) {

      console.error(
        '❌ Error cargando:',
        file,
        err.message
      );

    }

  }

  console.log('');
  console.log(
    '✓ Series cargadas:',
    cargadas
  );

  console.log(
    '• Asociaciones cargadas:',
    personajesAsociados
  );

}

loadSeries();

restaurarSeriesDesdeBackup();
setInterval(sincronizarSeriesDatabase, 30000);

// ━━━━━━━ VIDEOS LOCALES ━━━━━━━
function getCharacterVideos(key) {
  if (!fs.existsSync(GACHA_VIDEOS)) return [];
  return fs.readdirSync(GACHA_VIDEOS).filter(f => f.startsWith(key + '_'));
}
function getCharacterVideo(key) {
  const vids = getCharacterVideos(key);
  if (!vids.length) return null;
  return path.join(GACHA_VIDEOS, vids[Math.floor(Math.random() * vids.length)]);
}

// ━━━━━━━ HELPERS ━━━━━━━
const OWNER_NUMBER = '39604497432739@lid';
const OWNER_CONTACT_NUMBER = '56956461451';

// Owner principal dinámico desde base de datos
const getMainOwner = () => db.primaryOwner || OWNER_NUMBER;

const SECONDARY_OWNERS = [
  '199149496602667@lid',
  '221290086547601@lid',
  '250942222033020@lid',
  '256439998255240@lid',
  '180728096628981@lid',
];

function normalizeOwnerId(value) {
  return String(value || '')
    .trim()
    .replace(/:.*(?=@)/, '')
    .replace(/@c\.us$/i, '@s.whatsapp.net')
    .toLowerCase();
}

function isMainOwnerId(value) {
  const normalized =
    normalizeOwnerId(value);

  return [
    OWNER_NUMBER,
    db.primaryOwner
  ]
    .filter(Boolean)
    .some(owner =>
      normalizeOwnerId(owner) === normalized
    );
}

function isSecondaryOwnerId(value) {
  const normalized =
    normalizeOwnerId(value);

  return [
    ...SECONDARY_OWNERS,
    ...(Array.isArray(db.secondaryOwners)
      ? db.secondaryOwners
      : [])
  ]
    .filter(Boolean)
    .some(owner =>
      normalizeOwnerId(owner) === normalized
    );
}

function getCharacterCreatorName(character) {
  const seriesOwner =
    db.seriesOwners?.[String(character?.anime || "").trim().toLowerCase()];
  const creator =
    seriesOwner ||
    character?.creator;

  return (
    db.users?.[creator]?.name ||
    String(creator || "").split("@")[0] ||
    "Desconocido"
  );
}

function md5(s) { return crypto.createHash('md5').update(s).digest('hex'); }
function resetSession() { try { fs.rmSync(SESSION_PATH, { recursive: true, force: true }); } catch {} }
function formatBirthday(day, month) {

const meses = [
'enero','febrero','marzo',
'abril','mayo','junio',
'julio','agosto','septiembre',
'octubre','noviembre','diciembre'
];

const dias = [
'domingo',
'lunes',
'martes',
'miércoles',
'jueves',
'viernes',
'sábado'
];

const d = new Date(2025, month - 1, day);


return `${dias[d.getDay()]}, ${day} de ${meses[month-1]}`;
}

function askConsole(question) {
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  return new Promise(resolve => rl.question(question, answer => {
    rl.close();
    resolve(answer.trim());
  }));
}

async function askLinkingMethod() {
  while (true) {
    console.log('\n¿Cómo quieres vincular el bot?');
    console.log('1. Número de teléfono con código de vinculación');
    console.log('2. Código QR');

    const option = await askConsole('Elige una opción (1/2): ');
    if (option === '1' || option === '2') {
      return option;
    }

    console.log('Opción no válida. Elige 1 o 2.');
  }
}

async function askNumber() {
  while (true) {
    const number = (await askConsole('Número con código de país, solo dígitos (ej. 569XXXXXXXX): '))
      .replace(/[^0-9]/g, '');

    if (number.length >= 8 && number.length <= 15) {
      return number;
    }

    console.log('Número no válido. Ingresa entre 8 y 15 dígitos, incluido el código de país.');
  }
}

// ━━━━━━━ YT‐DLP ━━━━━━━
function ytDlpExec(args, client = null) {
  const run = extraArgs => new Promise((resolve, reject) => {
    const proc = spawn(
      YT_DLP_PATH,
      [
        '--js-runtimes', `deno:${DENO_PATH}`,
        '--remote-components', 'ejs:github',
        '--ffmpeg-location', FFMPEG_DIRECTORY,
        ...extraArgs,
        ...args
      ],
      { stdio: ['ignore', 'pipe', 'pipe'], windowsHide: true }
    );
    let out = '', err = '';
    proc.stdout.on('data', d => out += d);
    proc.stderr.on('data', d => err += d);
    proc.on('close', code => {
      if (code === 0) return resolve(out.trim());
      reject(new Error(err.trim() || `yt-dlp terminó con código ${code}`));
    });
    proc.on('error', reject);
  });

  return run([
    '--retries', '3',
    '--fragment-retries', '3',
    '--force-ipv4',
    ...(client ? ['--extractor-args', `youtube:player_client=${client}`] : [])
  ]).catch(async error => {
    const message = String(error?.message || error);
    if (!/403|forbidden/i.test(message)) throw error;

    return run([
      '--retries', '3',
      '--fragment-retries', '3',
      '--force-ipv4',
      '--extractor-args', 'youtube:player_client=web_safari'
    ]);
  });
}
async function ytDlpGetInfo(q) {
  if (/^https?:\/\//i.test(q)) {
    const raw = await ytDlpExec(['-j', '--no-playlist', q], 'ios');
    return JSON.parse(raw);
  }

  const raw = await ytDlpExec(
    ['--flat-playlist', '--dump-single-json', `ytsearch1:${q}`],
    'ios'
  );
  const result = JSON.parse(raw);
  const entry = result.entries?.find(item => item?.id);
  if (!entry) {
    throw new Error('No se encontraron videos para esa búsqueda.');
  }

  const webpageUrl =
    entry.webpage_url ||
    (/^https?:\/\//i.test(entry.url || '')
      ? entry.url
      : `https://www.youtube.com/watch?v=${encodeURIComponent(entry.id)}`);

  return {
    ...entry,
    webpage_url: webpageUrl,
    thumbnail: entry.thumbnail || entry.thumbnails?.[0]?.url,
    uploader: entry.uploader || entry.channel
  };
}
async function ytDlpDownloadToFile(url, dest, opts = {}) {
  const args = [
    '-o',
    dest,
    '--no-playlist',
    ...(!opts.audio ? ['--merge-output-format', 'mp4'] : [])
  ];

  if (opts.audio) {
    args.push(
      '-f',
      'bestaudio',
      '--extract-audio',
      '--audio-format',
      'mp3',
      '--audio-quality',
      '192K'
    );
  } else {
    args.push(
      '-f',
      '18/b[height<=720]/bv*[height<=720]+ba/b[height<=720]/best[height<=720]/best'
    );
  }

  args.push(url);

  let lastError;
  for (const client of ['ios', 'web_safari', 'web_embedded', 'android_vr']) {
    try {
      await ytDlpExec(args, client);
      lastError = null;
      break;
    } catch (error) {
      lastError = error;
    }
  }
  if (lastError) throw lastError;

  const dir = path.dirname(dest);
  const base = path.basename(dest, path.extname(dest));

  const files = fs.readdirSync(dir)
    .filter(f =>
      f.startsWith(base) &&
      !f.endsWith('.part') &&
      !f.endsWith('.ytdl')
    )
    .map(f => path.join(dir, f))
    .filter(f => fs.existsSync(f) && fs.statSync(f).size > 10000);

  if (!files.length) {
    throw new Error('Archivo descargado vacío o inexistente');
  }

  return files[0];
}

async function isWhatsAppCompatibleMp4(filePath) {
  return new Promise(resolve => {
    const proc = spawn('ffprobe', [
      '-v', 'error',
      '-show_entries', 'stream=codec_type,codec_name',
      '-of', 'default=noprint_wrappers=1:nokey=1',
      filePath
    ], { stdio: ['ignore', 'pipe', 'ignore'] });
    let output = '';
    proc.stdout.on('data', data => output += data);
    proc.on('close', code => resolve(
      code === 0 &&
      /video\nh264|h264\nvideo/.test(output) &&
      /audio\naac|aac\naudio/.test(output)
    ));
    proc.on('error', () => resolve(false));
  });
}

// ━━━━━━━ MEDIA DOWNLOADERS ━━━━━━━
export async function handleTomp3(sock, msg) {
  const jid = msg.key.remoteJid;
  const contextInfo =
    msg.message?.extendedTextMessage?.contextInfo ||
    msg.message?.imageMessage?.contextInfo ||
    msg.message?.videoMessage?.contextInfo;
  const quoted = contextInfo?.quotedMessage;
  const videoMessage = unwrapVideoMessage(quoted);

  if (!contextInfo?.stanzaId || !videoMessage) {
    return sock.sendMessage(
      jid,
      { text: '◇ Debes citar un video usando /tomp3' },
      { quoted: msg }
    );
  }

  const quotedVideo = {
    key: {
      remoteJid: jid,
      id: contextInfo.stanzaId,
      participant: contextInfo.participant
    },
    message: videoMessage
  };
  const fileId = `${Date.now()}_${crypto.randomBytes(4).toString('hex')}`;
  const input = path.join(TEMP_DIR, `vid_${fileId}.mp4`);
  const output = path.join(TEMP_DIR, `aud_${fileId}.mp3`);

  try {
    await sock.sendMessage(jid, { text: 'creando...' }, { quoted: msg });
    fs.mkdirSync(TEMP_DIR, { recursive: true });
    const videoBuffer = await downloadMediaMessage(quotedVideo, 'buffer', {});
    if (!Buffer.isBuffer(videoBuffer) || videoBuffer.length === 0) {
      throw new Error('El video citado llegó vacío.');
    }
    fs.writeFileSync(input, videoBuffer);
    await new Promise((resolve, reject) => {
      const proc = spawn(
        FFMPEG_PATH,
        ['-y', '-i', input, '-vn', '-codec:a', 'libmp3lame', '-q:a', '2', '-f', 'mp3', output],
        { stdio: ['ignore', 'ignore', 'pipe'], windowsHide: true }
      );
      let stderr = '';
      proc.stderr.on('data', data => { stderr += data.toString(); });
      proc.on('close', code => code === 0
        ? resolve()
        : reject(new Error(stderr.trim() || `ffmpeg terminó con código ${code}`)));
      proc.on('error', reject);
    });
    if (!fs.existsSync(output) || fs.statSync(output).size === 0) {
      throw new Error('ffmpeg no generó el MP3.');
    }
    await sock.sendMessage(
      jid,
      { audio: fs.readFileSync(output), mimetype: 'audio/mpeg', fileName: 'audio.mp3', ptt: false },
      { quoted: msg }
    );
  } catch (error) {
    console.error('[TOMP3] Error al convertir video citado:', error);
    await sock.sendMessage(
      jid,
      { text: `❌ Error al convertir el video: ${error.message || 'error desconocido'}` },
      { quoted: msg }
    );
  } finally {
    for (const file of [input, output]) {
      if (fs.existsSync(file)) {
        try {
          fs.unlinkSync(file);
        } catch (cleanupError) {
          console.warn('[TOMP3] No se pudo limpiar temporal:', cleanupError.message);
        }
      }
    }
  }
}

export async function handleTt(sock, msg, url) {
  const jid = msg.key.remoteJid;

  const estiloNumero = (n) =>
    String(n).split('').map(d => {
      const code = 0x1D7CE + Number(d);
      return String.fromCodePoint(code);
    }).join('');

  const barra = (porcentaje) => {
    const llenos = Math.floor(porcentaje / 10);
    const vacios = 10 - llenos;
    return '[' + '■'.repeat(llenos) + '□'.repeat(vacios) + ']';
  };

  let cargando;
  try {
    cargando = await sock.sendMessage(
      jid,
      { text: barra(0) + ' ' + estiloNumero(0) + '%' },
      { quoted: msg }
    );
  } catch (e) { return; }

  let animacionActiva = true;
  const animar = async () => {
    let progreso = 0;
    while (animacionActiva && progreso < 100) {
      progreso = Math.min(progreso + Math.floor(Math.random() * 5) + 1, 100);
      try {
        await sock.sendMessage(
          jid,
          {
            text: barra(progreso) + ' ' + estiloNumero(progreso) + '%',
            edit: cargando.key
          }
        );
      } catch (e) {}
      await new Promise(r => setTimeout(r, 250));
    }
  };
  const promesaAnimacion = animar();

  try {
    const json = await fetch('https://www.tikwm.com/api/?url=' + encodeURIComponent(url)).then(r => r.json());

    if (json && json.code === 0 && json.data && json.data.play) {
      const data = json.data;
      const vUrl = data.play || data.hdplay;
      const buffer = Buffer.from(await (await fetch(vUrl)).arrayBuffer());

      animacionActiva = false;
      try { await promesaAnimacion; } catch (e) {}

      try {
        await sock.sendMessage(
          jid,
          { text: barra(100) + ' ' + estiloNumero(100) + '%', edit: cargando.key }
        );
      } catch (e) {}

      try { await sock.sendMessage(jid, { delete: cargando.key }); } catch (e) {}

      const creator = data.author || {};
      const nickname = creator.nickname || creator.unique_id || 'Desconocido';
      const uniqueId = creator.unique_id || '';

      const likes = Number(data.digg_count || 0).toLocaleString('en-US');
      const comments = Number(data.comment_count || 0).toLocaleString('en-US');

      const fecha = data.create_time ? new Date(data.create_time * 1000) : new Date();
      const meses = ['ene','feb','mar','abr','may','jun','jul','ago','sep','oct','nov','dic'];
      const dia = fecha.getDate();
      const mes = meses[fecha.getMonth()];
      const anio = fecha.getFullYear();
      const horas = String(fecha.getHours()).padStart(2,'0');
      const minutos = String(fecha.getMinutes()).padStart(2,'0');
      const fechaFormateada = dia + ' ' + mes + ' ' + anio + ', ' + horas + ':' + minutos;

      let resolucion = 'Desconocida';
      if (data.video && data.video.width && data.video.height) {
        resolucion = data.video.width + 'x' + data.video.height;
      } else if (data.hdplay) {
        resolucion = 'HD';
      }

      const descripcion = data.title || 'Sin descripción';
      const hashtagsMatch = descripcion.match(/#[^\s#]+/g);
      const hashtags = hashtagsMatch ? hashtagsMatch.join(' ') : '';

      const caption = '(˵^ᗜ^˵ ) 𝐕𝐢𝐝𝐞𝐨 𝐝𝐞𝐬𝐜𝐚𝐫𝐠𝐚𝐝𝐨\n\n' +
        '🜲 𝐂ɾ𝐞ɑ𝐝𝐨ɾ ➢ \`' + nickname + ' ୭ (@' + uniqueId + ')\`\n' +
        '♡ 𝐌𝐞 𝐠𝐮𝐬𝐭ɑ ➢ \`' + likes + '\`\n' +
        '⟣ 𝐂𝐨𝐦𝐞𝐧𝐭ɑɾ𝐢𝐨𝐬 ➢ \`' + comments + '\`\n' +
        '⛨ 𝐅𝐞𝐜𝐡ɑ ➢ \`' + fechaFormateada + '\`\n' +
        '▣ 𝐑𝐞𝐬𝐨𝐥𝐮𝐜𝐢𝐨́𝐧 → \`' + resolucion + '\`\n\n' +
        '✎ 𝐃𝐞𝐬𝐜ɾ𝐢𝐩𝐜𝐢𝐨́𝐧 ✎\n\n' +
        '\`' + descripcion + '\`\n\n' +
        '\`' + hashtags + '\`\n\n' +
        '⚯ 𝐄𝐧𝐥ɑ𝐜𝐞 ⚯ \`𝑪𝒓𝒆𝒂𝒕𝒆𝒅 𝒃𝒚 𝑴𝒊𝒐 𝑯𝒂𝒊𝒎𝒊𝒚𝒂\`\n\n' +
        '【 ' + url + ' 】';

      await sock.sendMessage(
        jid,
        { video: buffer, caption: caption, mimetype: 'video/mp4' },
        { quoted: msg }
      );
      return;
    }
    throw new Error('API caída');
  } catch (e) {
    animacionActiva = false;
    try { await promesaAnimacion; } catch (err) {}
    try { await sock.sendMessage(jid, { delete: cargando.key }); } catch (err) {}
    await sock.sendMessage(jid, { text: '● Error al descargar el video de TikTok' }, { quoted: msg });
  }
}

function formatSocialCount(value) {
  const number = Number(value);
  return Number.isFinite(number) ? number.toLocaleString('es-ES') : '0';
}

async function searchTikTokUrls(query) {
  const urls = [];
  const searches = [
    `site:tiktok.com/@ ${query}`,
    `site:tiktok.com ${query} video`
  ];

  for (const search of searches) {
    const endpoints = [
      `https://www.bing.com/search?format=rss&q=${encodeURIComponent(search)}`,
      `https://html.duckduckgo.com/html/?q=${encodeURIComponent(search)}`,
      `https://www.google.com/search?num=10&q=${encodeURIComponent(search)}`
    ];

    for (const endpoint of endpoints) {
      const response = await fetch(endpoint, {
        headers: { 'user-agent': 'Mozilla/5.0' }
      });
      if (!response.ok) continue;
      const html = await response.text();

      const candidates = [
        ...html.matchAll(/<link>(.*?)<\/link>/gis),
        ...html.matchAll(/href=["']([^"']+)["']/gis)
      ];

      for (const match of candidates) {
        let value = match[1]
          .replace(/&amp;/g, '&')
          .replace(/&quot;/g, '"')
          .trim();

        if (value.startsWith('/l/')) {
          value = `https://html.duckduckgo.com${value}`;
        }
        if (value.startsWith('/url?')) {
          value = `https://www.google.com${value}`;
        }

        if (value.includes('uddg=')) {
          try {
            value = decodeURIComponent(new URL(value).searchParams.get('uddg') || '');
          } catch {
            continue;
          }
        }

        let parsed;
        try {
          parsed = new URL(value);
        } catch {
          continue;
        }

        if (
          parsed.hostname === 'www.tiktok.com' ||
          parsed.hostname === 'tiktok.com' ||
          parsed.hostname.endsWith('.tiktok.com')
        ) {
          const isVideo = /^\/@[^/]+\/video\/\d+/.test(parsed.pathname);
          if (isVideo && !urls.includes(value)) urls.push(value);
        }
      }
    }
  }

  return urls;
}

export async function handleTtSearch(sock, msg, query) {
  const jid = msg.key.remoteJid;
  await sock.sendMessage(jid, { text: '⏳ Buscando videos de TikTok...' }, { quoted: msg });

  try {
    let urls;
    if (/^https?:\/\/(?:www\.)?(?:vm|vt|m\.)?tiktok\.com\//i.test(query)) {
      urls = [query];
    } else {
      urls = await searchTikTokUrls(query);
    }
    if (!urls.length) {
      throw new Error('No se encontraron videos de TikTok para esa búsqueda.');
    }

    let selected = null;
    for (const url of urls.slice(0, 5)) {
      const response = await fetch(
        `https://www.tikwm.com/api/?url=${encodeURIComponent(url)}`,
        { headers: { 'user-agent': 'Mozilla/5.0' } }
      );
      if (!response.ok) continue;
      const json = await response.json();
      if (json?.code === 0 && json.data?.play) {
        selected = { url, data: json.data };
        break;
      }
    }

    if (!selected) throw new Error('No se pudo obtener un video reproducible.');

    const { data } = selected;
    const videoResponse = await fetch(data.hdplay || data.play, {
      headers: { 'user-agent': 'Mozilla/5.0' }
    });
    if (!videoResponse.ok) throw new Error('No se pudo descargar el video.');

    const buffer = Buffer.from(await videoResponse.arrayBuffer());
    if (!buffer.length) throw new Error('El video descargado está vacío.');

    const thumbnailUrl = data.cover || data.origin_cover;
    if (thumbnailUrl) {
      const thumbnailResponse = await fetch(thumbnailUrl, {
        headers: { 'user-agent': 'Mozilla/5.0' }
      });
      if (thumbnailResponse.ok) {
        const thumbnail = Buffer.from(await thumbnailResponse.arrayBuffer());
        if (thumbnail.length) {
          await sock.sendMessage(
            jid,
            {
              image: thumbnail,
              caption: `「☆」Buscando *<${data.title || query}>*\n> TikTok: *${data.author?.nickname || data.author?.unique_id || 'Desconocido'}*`
            },
            { quoted: msg }
          );
        }
      }
    }

    const caption =
      `「☆」${data.title || query}\n` +
      `> Autor: *${data.author?.nickname || data.author?.unique_id || 'Desconocido'}*\n` +
      `> Vistas: *${formatSocialCount(data.play_count)}*\n` +
      `> Likes: *${formatSocialCount(data.digg_count)}*\n` +
      `> Comentarios: *${formatSocialCount(data.comment_count)}*`;

    await sock.sendMessage(
      jid,
      { video: buffer, caption, mimetype: 'video/mp4' },
      { quoted: msg }
    );
  } catch (error) {
    console.error('❌ ERROR TTSEARCH:', error);
    await sock.sendMessage(
      jid,
      { text: `❌ ${error.message || 'No se pudo buscar el video de TikTok.'}` },
      { quoted: msg }
    );
  }
}

export async function handleMp4(sock, msg, input) {
  await sock.sendMessage(msg.key.remoteJid, { text: '⏳ Buscando video...' }, { quoted: msg });
  let originalPath = null;
  let finalPath = null;
  try {
    fs.mkdirSync(TEMP_DIR, { recursive: true });
    fs.mkdirSync(VIDEO_CACHE, { recursive: true });

    let urlToDownload = input, title = '', thumbnail = '', uploader = '';
    if (!input.startsWith('http://') && !input.startsWith('https://')) {
      const info = await ytDlpGetInfo(input);
      if (!info) throw new Error('No encontrado');
      urlToDownload = info.webpage_url; title = info.title;
      thumbnail = info.thumbnail; uploader = info.uploader;
    } else {
      const info = await ytDlpGetInfo(urlToDownload);
      title = info.title; thumbnail = info.thumbnail; uploader = info.uploader;
    }
    const cacheKey = md5(urlToDownload);
    const cachePath = path.join(VIDEO_CACHE, `${cacheKey}.mp4`);
      const cacheInfoPath = path.join(VIDEO_CACHE, `${cacheKey}.json`);

      if (fs.existsSync(cachePath)) {
        if (fs.existsSync(cacheInfoPath)) {
          try {
            const saved = JSON.parse(fs.readFileSync(cacheInfoPath, 'utf8'));
            title = saved.title || title;
            thumbnail = saved.thumbnail || thumbnail;
            uploader = saved.uploader || uploader;
          } catch {}
        }
      if (thumbnail) {
        try {
          const thumbBuffer = Buffer.from(await (await fetch(thumbnail)).arrayBuffer());
          await sock.sendMessage(msg.key.remoteJid, { image: thumbBuffer, caption: `「☆」Descargando *<${title}>*\n> ✐ Canal » *${uploader || 'Desconocido'}*\n> Calidad: 720p (cach¿)`, mimetype: 'image/jpeg' }, { quoted: msg });
        } catch {}
      }
      await sock.sendMessage(msg.key.remoteJid, { video: fs.readFileSync(cachePath), caption: ` Título ï¿½ ${title}\n> Calidad: 720p (cachï¿½)`, mimetype: 'video/mp4' }, { quoted: msg });
      return;
    }
    if (thumbnail) {
      try {
        const thumbBuffer = Buffer.from(await (await fetch(thumbnail)).arrayBuffer());
        await sock.sendMessage(msg.key.remoteJid, { image: thumbBuffer, caption: `「☆」Descargando *<${title}>*\n> ✐ Canal » *${uploader || 'Desconocido'}*\n> Calidad: 720p`, mimetype: 'image/jpeg' }, { quoted: msg });
      } catch {}
    }
    const tempDownload = path.join(
      TEMP_DIR,
      `raw_${Date.now()}.%(ext)s`
    );
    originalPath = await ytDlpDownloadToFile(urlToDownload, tempDownload);

    finalPath = path.join(TEMP_DIR, `whatsapp_${Date.now()}.mp4`);

    if (await isWhatsAppCompatibleMp4(originalPath)) {
      fs.renameSync(originalPath, finalPath);
      originalPath = null;
    } else {
      await new Promise((resolve, reject) => {
        const proc = spawn(FFMPEG_PATH, [
          '-i', originalPath,
          '-c:v', 'libx264',
          '-pix_fmt', 'yuv420p',
          '-preset', 'ultrafast',
          '-crf', '28',
          '-c:a', 'aac',
          '-b:a', '128k',
          '-movflags', '+faststart',
          '-f', 'mp4',
          finalPath
        ], { stdio: 'ignore' });

        proc.on('close', code => code === 0 ? resolve() : reject(new Error('ffmpeg error')));
        proc.on('error', reject);
      });
    }

    if (!fs.existsSync(finalPath) || fs.statSync(finalPath).size < 10000) {
      throw new Error('MP4 convertido inválido');
    }

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        video: { stream: fs.createReadStream(finalPath) },
        caption: ` Título ï¿½ ${title}\n> Calidad: 720p`,
        mimetype: 'video/mp4'
      },
      { quoted: msg }
    );

    fs.renameSync(finalPath, cachePath);

    fs.writeFileSync(
      path.join(VIDEO_CACHE, `${cacheKey}.json`),
      JSON.stringify({
        title,
        thumbnail,
        uploader
      }, null, 2)
    );

  } catch (e) {
  console.error("❌ ERROR MP4:", e);
  await sock.sendMessage(
    msg.key.remoteJid,
    { text: `● Error al descargar el video.\\n\\n${e.message || e}` },
    { quoted: msg }
  );
  } finally {
    for (const filePath of [originalPath, finalPath]) {
      if (filePath && fs.existsSync(filePath)) {
        try {
          fs.unlinkSync(filePath);
        } catch (cleanupError) {
          console.warn('⚠️ No se pudo limpiar temporal MP4:', cleanupError.message);
        }
      }
    }
  }
}


export async function handleYtAudio(sock, msg, query) {
  const jid = msg.key.remoteJid;

  console.log(
    '[YTAUDIO] SOCKET:',
    sock.user?.id || null,
    '| LID:',
    sock.user?.lid || null,
    '| ES MAIN:',
    sock === globalThis.MAIN_BOT_SOCK,
    '| ES SUBBOT:',
    Boolean(sock.__subBotPhone)
  );

  try {
    await sock.sendMessage(
      jid,
      { text: '> ʙᴜsǫᴜᴇᴅᴀ ʀᴇᴄɪʙɪᴅᴀ, ᴇsᴘᴇʀᴇ ᴜɴ ᴍᴏᴍᴇɴᴛᴏ...' },
      { quoted: msg }
    );
  } catch {}

  try {
    const cleanQuery = String(query || '').trim();

    if (!cleanQuery) {
      throw new Error('No se recibió una búsqueda.');
    }

    console.log('[YTAUDIO] Buscando:', cleanQuery);

    let info = null;

    if (typeof ytDlpGetInfo === 'function') {
      info = await ytDlpGetInfo(cleanQuery);
    }

    if (!info || !info.webpage_url) {
      throw new Error('No se encontró el audio.');
    }

    const audioUrl = info.webpage_url;
    const title = info.title || 'Audio';
    const uploader = info.uploader || 'Desconocido';

    console.log('[YTAUDIO] Encontrado:', title);
    console.log('[YTAUDIO] URL:', audioUrl);

    /* ===============================
       CACHE REAL
       =============================== */

    const cacheDir = path.join(
      process.cwd(),
      'cache',
      'audio'
    );

    fs.mkdirSync(cacheDir, { recursive: true });

    let videoId = null;

    try {
      const parsed = new URL(audioUrl);

      if (parsed.hostname.includes('youtube.com')) {
        videoId = parsed.searchParams.get('v');
      }

      if (!videoId && parsed.hostname === 'youtu.be') {
        videoId = parsed.pathname.replace(/^\//, '').split('/')[0];
      }
    } catch {}

    if (!videoId) {
      const match = audioUrl.match(/(?:v=|youtu\.be\/)([A-Za-z0-9_-]{6,})/);

      if (match) {
        videoId = match[1];
      }
    }

    if (!videoId) {
      videoId = crypto
        .createHash('md5')
        .update(audioUrl)
        .digest('hex');
    }

    let audioPath = null;

    for (const extension of ['.mp3', '.m4a']) {
      const candidate = path.join(cacheDir, videoId + extension);
      if (fs.existsSync(candidate)) {
        try {
          if (fs.statSync(candidate).size > 10000) {
            audioPath = candidate;
            break;
          }
        } catch {}
      }
    }

    if (audioPath) {
      console.log('[YTAUDIO] CACHE HIT:', audioPath);
    } else {
      console.log('[YTAUDIO] CACHE MISS:', videoId);

      const tempDir = path.join(
        process.cwd(),
        'temp-ytaudio'
      );

      fs.mkdirSync(tempDir, { recursive: true });

      const tempBase = path.join(
        tempDir,
        videoId + '-' + Date.now()
      );

      const downloaded = await ytDlpDownloadToFile(
        audioUrl,
        `${tempBase}.%(ext)s`,
        { audio: true }
      );
      const ext = path.extname(downloaded).toLowerCase();
      if (ext !== '.mp3') {
        throw new Error(`Formato de audio descargado no compatible: ${ext || 'desconocido'}`);
      }
      const destination = path.join(cacheDir, `${videoId}${ext}`);

      fs.copyFileSync(downloaded, destination);
      audioPath = destination;

      console.log('[YTAUDIO] Guardado en CACHE:', audioPath);

      try {
        fs.unlinkSync(downloaded);
      } catch (cleanupError) {
        console.warn('[YTAUDIO] No se pudo limpiar temporal:', cleanupError.message);
      }
    }

    if (!audioPath || !fs.existsSync(audioPath)) {
      throw new Error('No se pudo obtener el audio.');
    }

    const audioSize = fs.statSync(audioPath).size;

    console.log('[YTAUDIO] Archivo listo:', audioPath);
    console.log('[YTAUDIO] Tamaño:', audioSize, 'bytes');

    let youtubeThumbBuffer = null;
    let botProfileBuffer = null;

    try {
      const thumbnailUrl =
        info.thumbnail;

      if (thumbnailUrl) {
        const response =
          await fetch(thumbnailUrl);

        if (response.ok) {
          youtubeThumbBuffer =
            Buffer.from(
              await response.arrayBuffer()
            );
        }
      }
    } catch (error) {
      console.log(
        '[YTAUDIO] Error obteniendo portada de YouTube:',
        error.message
      );
    }

    try {
      const botId =
        sock.user?.id ||
        sock.user?.lid;

      if (botId) {
        const profileUrl =
          await sock.profilePictureUrl(
            botId,
            'image'
          );

        if (profileUrl) {
          const response =
            await fetch(profileUrl);

          if (response.ok) {
            botProfileBuffer =
              Buffer.from(
                await response.arrayBuffer()
              );
          }
        }
      }
    } catch (error) {
      console.log(
        '[YTAUDIO] Error obteniendo foto del bot:',
        error.message
      );
    }

    const durationSeconds =
      Number(info.duration) || 0;

    const duration =
      durationSeconds > 0
        ? Math.floor(durationSeconds / 60) +
          'm ' +
          String(
            Math.floor(durationSeconds % 60)
          ).padStart(2, '0') +
          's'
        : 'Desconocida';

    const views =
      Number(info.view_count) || 0;

    const viewsText =
      views > 0
        ? views.toLocaleString('en-US')
        : 'Desconocidas';

    const bitrate =
      Math.round(
        Number(
          info.abr ||
          info.tbr ||
          0
        )
      );

    const qualityText =
      bitrate > 0
        ? bitrate + 'ᴋʙ'
        : 'Desconocida';

    const sizeMB =
      (audioSize / (1024 * 1024))
        .toFixed(2);

    const caption =
`₊˚⊹ ⬧ (¬‿¬) ʏᴏᴜᴛᴜʙᴇ ⬧ ⊹˚₊

⪩ 《☆》*${title}*

> ⟡ *ᴠɪsᴛᴀs* › \`${viewsText}\`
> ⟡ ᴄᴀʟɪᴅᴀᴅ › \`${qualityText}\`
> ⟡ ᴄᴀɴᴀʟ › \`${uploader}\`
> ⟡ ᴅᴜʀᴀᴄɪóɴ › \`${duration}\`
> ⟡ ᴛᴀᴍᴀñᴏ › \`${sizeMB} ᴍʙ\`
> ⟡ *ʟɪɴᴋ* › \`${audioUrl}\`

✧ ｡ﾟ•┈୨ ♡ ୧┈•ﾟ｡ ✧`;

    const audioBuffer = fs.readFileSync(audioPath);
    const audioExtension = path.extname(audioPath).toLowerCase();
    const audioMimeType = audioExtension === '.m4a'
      ? 'audio/mp4'
      : audioExtension === '.mp3'
        ? 'audio/mpeg'
        : null;

    if (!audioBuffer || !audioBuffer.length) {
      throw new Error('El archivo de audio está vacío.');
    }
    if (!audioMimeType) {
      throw new Error(`Formato de audio no compatible: ${audioExtension || 'desconocido'}`);
    }

    console.log(
      '[YTAUDIO] Preparando audio:',
      audioPath
    );

    console.log(
      '[YTAUDIO] Buffer:',
      audioBuffer.length,
      'bytes'
    );

    if (youtubeThumbBuffer) {
      await sock.sendMessage(
        jid,
        {
          image: youtubeThumbBuffer,
          mimetype: 'image/jpeg',
          caption
        },
        { quoted: msg }
      );
    } else {
      await sock.sendMessage(
        jid,
        {
          text: caption
        },
        { quoted: msg }
      );
    }

    await sock.sendMessage(
      jid,
      {
        audio: audioBuffer,
        mimetype: audioMimeType,
        fileName: `${title}${audioExtension}`,
        ptt: false,
        ...(botProfileBuffer
          ? { jpegThumbnail: botProfileBuffer }
          : {})
      },
      { quoted: msg }
    );

    console.log('[YTAUDIO] Audio enviado correctamente.');
    console.log('[YTAUDIO] CACHE:', audioPath);

  } catch (error) {
    console.error('\n[YTAUDIO] ERROR REAL:');
    console.error(error);

    try {
      await sock.sendMessage(
        jid,
        {
          text: '● No se pudo descargar el audio.\n\nError: ' + (error.message || 'desconocido')
        },
        { quoted: msg }
      );
    } catch {}
  }
}
export async function handleIg(sock, msg, url) {
  await sock.sendMessage(msg.key.remoteJid, { text: '⏳ Descargando Instagram...' }, { quoted: msg });
  try {
    if (!url.includes('instagram.com')) throw new Error('No es un enlace de Instagram');
    const temp = path.join(TEMP_DIR, `ig_${Date.now()}.mp4`);
    const final = await ytDlpDownloadToFile(url, temp);
    try {
      await sock.sendMessage(msg.key.remoteJid, { video: fs.createReadStream(final), caption: '• Video de Instagram (HD)', mimetype: 'video/mp4' }, { quoted: msg });
    } catch {
      const rebuilt = path.join(TEMP_DIR, `ig_rebuilt_${Date.now()}.mp4`);
      await new Promise((resolve, reject) => {
        const proc = spawn(FFMPEG_PATH, ['-i', final, '-c:v', 'libx264', '-preset', 'ultrafast', '-crf', '28', '-c:a', 'aac', '-b:a', '128k', '-movflags', '+faststart', rebuilt], { stdio: 'pipe' });
        proc.on('close', code => code === 0 ? resolve() : reject(new Error('ffmpeg error')));
        proc.on('error', reject);
      });
      await sock.sendMessage(msg.key.remoteJid, { video: fs.createReadStream(rebuilt), caption: '• Video de Instagram (comprimido)', mimetype: 'video/mp4' }, { quoted: msg });
      fs.unlinkSync(rebuilt);
    }
    fs.unlinkSync(final);
  } catch (e) { await sock.sendMessage(msg.key.remoteJid, { text: '❌ No se pudo descargar el video de Instagram.' }, { quoted: msg }); }
}

// ━━━━━━━ NUEVO SISTEMA GACHA ━━━━━━━
const CLAIM_CD = 5 * 60 * 1000;  // 5 minutos
const VOTE_CD = 20 * 60 * 1000;  // 20 minutos

function formatTimeAgo(ts) {
  if (!ts || ts === 0) return 'nunca';
  const diff = Date.now() - ts;
  if (diff < 0) return 'ahora';
  const s = Math.floor(diff / 1000), m = Math.floor(s / 60), h = Math.floor(m / 60), d = Math.floor(h / 24);
  if (s < 60) return `hace ${s}s`;
  if (m < 60) return `hace ${m}m ${s % 60}s`;
  if (h < 24) return `hace ${h}h ${m % 60}m ${s % 60}s`;
  return `hace ${d}d ${h % 24}h`;
}
function getRandomCharacter(sender, groupId) {
  const user = initUser(sender);
  const groupLuck = getGroupLuck(groupId);
  let totalWeight = 0;
  let selected = null;

  for (const char of charactersCache) {
    if (char.pendienteTag && !(char.tag && String(char.tag).trim())) continue;

    let chance =
      parseFloat(
        String(char.chance || "1")
          .replace("%", "")
      );

    if (isNaN(chance))
      chance = 1;

    const rarity =
      String(char.rarity || "")
        .toLowerCase();

    if (rarity === "mod") {
      const baseChance = chance;
      const modLuck = Number(user.luck.mod) || 0;
      chance += groupLuck > 1
        ? (baseChance + modLuck) * groupLuck - baseChance
        : modLuck;
    }

    else if (rarity === "mitico")
      chance += user.luck.mythic;

    else if (rarity === "legendario")
      chance += user.luck.legendary;

    else if (rarity === "epico")
      chance += user.luck.epic;

    else if (rarity === "raro")
      chance += user.luck.rare;

    else
      chance += user.luck.common;

    chance = Math.max(1, Math.floor(chance));

    totalWeight += chance;
    if (Math.random() * totalWeight < chance) {
      selected = char;
    }
  }

  return selected;
}
  


// ==========================================================================
// =========================================================================const TEMP_IMAGES = path.join(__dirname, "temp-images");
const TEMP_IMAGES = path.join(process.cwd(), "temp-images");
// CAR_IMAGES ya está declarado anteriormente.

if (!fs.existsSync(TEMP_IMAGES)) {
fs.mkdirSync(TEMP_IMAGES, { recursive: true });
}

if (!fs.existsSync(CAR_IMAGES)) {
fs.mkdirSync(CAR_IMAGES, { recursive: true });
}

// ==========================================================================
// ESTADO: imágenes pendientes por usuario
// =========================================================================// Estructura:
// pendientesImg[userId] = [
//   "temp-images/<userId>/168xxxxx.jpg",
//   ...
// ]
const pendientesImg = {};

function carpetaTempUsuario(userId) {
return path.join(TEMP_IMAGES, userId.replace(/[^\w]/g, "_"));
}

function inicializarPendiente(userId) {
if (!pendientesImg[userId]) {
pendientesImg[userId] = [];
}
}

// ==========================================================================
// 1) CAPTURA DE IMÁGENES ENTRANTES
// =========================================================================// Llama a esta función desde tu handler de messages.upsert cuando el mensaje
// tenga una imagen y no sea un comando.
//
// Ejemplo:
//
// if (msg.message?.imageMessage) {
//   await handleImagenEntrante(sock, msg);
//   return;
// }

async function handleImagenEntrante(sock, msg) {
try {
const userId = msg.key.participant || msg.key.remoteJid;

const buffer = await downloadMediaMessage(
  msg,
  "buffer",
  {},
  {
    reuploadRequest: sock.updateMediaMessage
  }
);

const folder = carpetaTempUsuario(userId);

if (!fs.existsSync(folder)) {
  fs.mkdirSync(folder, { recursive: true });
}

const nombreArchivo =
  `${Date.now()}_${Math.floor(Math.random() * 1000)}.jpg`;

const rutaFinal = path.join(folder, nombreArchivo);

fs.writeFileSync(rutaFinal, buffer);

inicializarPendiente(userId);
pendientesImg[userId].push(rutaFinal);

console.log(
  `• Imagen guardada en pendientes de ${userId}: ` +
  `${rutaFinal} ` +
  `(total: ${pendientesImg[userId].length})`
);

// Confirmación opcional:
//
// await sock.sendMessage(
//   msg.key.remoteJid,
//   {
//     text:
//       `• Imagen ${pendientesImg[userId].length} ` +
//       `guardada en pendientes.`
//   },
//   {
//     quoted: msg
//   }
// );

} catch (error) {
console.log(
"❌ Error guardando imagen entrante:",
error.message
);
}
}

// ==========================================================================
// 2) LIMPIAR PENDIENTES SIN CREAR VEHÍCULO
// =========================================================================// Comando sugerido:
// /limpiarpendientes

async function handleLimpiarPendientes(sock, msg) {
const userId = msg.key.participant || msg.key.remoteJid;

const folder = carpetaTempUsuario(userId);

if (fs.existsSync(folder)) {
fs.rmSync(folder, {
recursive: true,
force: true
});
}

delete pendientesImg[userId];

await sock.sendMessage(
msg.key.remoteJid,
{
text: "◆ Pendientes de im¿genes eliminados."
},
{
quoted: msg
}
);
}

// ==========================================================================
// 3) cleanimgv
// =========================================================================// Toma todas las imágenes pendientes del usuario, crea o completa el
// vehículo y limpia los archivos temporales.
//
// Uso:
//
// cleanimgv Personaje | Nombre del carro

async function handleCleanImgV2(sock, msg, query) {
try {
const userId = msg.key.participant || msg.key.remoteJid;

if (
  !pendientesImg[userId] ||
  pendientesImg[userId].length === 0
) {
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
        " No tienes imágenes pendientes. " +
        "Envía las fotos primero y luego ejecuta cleanimgv."
    },
    {
      quoted: msg
    }
  );
}

if (!query) {
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:

`Uso:

cleanimgv Personaje | Nombre del carro`
},
{
quoted: msg
}
);
}

const parts = query
  .split("|")
  .map(x => x.trim());

if (parts.length < 2) {
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:

`Uso:

cleanimgv Personaje | Nombre del carro`
},
{
quoted: msg
}
);
}

loadCars();

const personaje = parts[0].toLowerCase();

const nombreOriginal = parts[1];

const key = nombreOriginal
  .toLowerCase()
  .replace(/[^\w]/g, "_");

const folderDestino = path.join(
  CAR_IMAGES,
  personaje,
  key
);

if (!fs.existsSync(folderDestino)) {
  fs.mkdirSync(
    folderDestino,
    {
      recursive: true
    }
  );
}

// Mover las imágenes pendientes a la carpeta definitiva.
const rutasFinales = [];

pendientesImg[userId].forEach(
  (rutaTemp, i) => {
    if (!fs.existsSync(rutaTemp)) {
      return;
    }

    const destino = path.join(
      folderDestino,
      `img_${i + 1}.jpg`
    );

    fs.renameSync(
      rutaTemp,
      destino
    );

    rutasFinales.push(destino);
  }
);

if (rutasFinales.length === 0) {
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
        " Las imágenes pendientes ya no existen " +
        "en disco. Vuelve a enviarlas."
    },
    {
      quoted: msg
    }
  );
}

// Buscar un vehículo existente.
let car = carsCache.find(
  c =>
    c.personaje.toLowerCase() === personaje &&
    c.key === key
);

if (car) {
  car.images = [
    ...(car.images || []),
    ...rutasFinales
  ];
} else {
  const siguienteId =
    carsCache.length > 0
      ? Math.max(
          ...carsCache.map(
            c => c.id
          )
        ) + 1
      : 1;

  car = {
    id: siguienteId,
    personaje: parts[0],
    carName: nombreOriginal,
    key,
    images: rutasFinales
  };

  carsCache.push(car);

  carMap.set(
    car.key,
    car
  );
}

saveCars();

// Limpiar los pendientes.
const folderTempUsuario =
  carpetaTempUsuario(userId);

if (
  fs.existsSync(
    folderTempUsuario
  )
) {
  fs.rmSync(
    folderTempUsuario,
    {
      recursive: true,
      force: true
    }
  );
}

delete pendientesImg[userId];

const texto =

` Vehículo guardado

■ ${car.carName}
• ${car.personaje}
🆔 ${car.id}
🖼️ ${rutasFinales.length} imagen(es)`;

await sock.sendMessage(
  msg.key.remoteJid,
  {
    text: texto
  },
  {
    quoted: msg
  }
);

for (
  const ruta of rutasFinales
) {
  if (
    fs.existsSync(ruta)
  ) {
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        image:
          fs.readFileSync(
            ruta
          )
      }
    );
  }
}

} catch (error) {
console.log(
"❌ Error en handleCleanImgV:",
error
);

await sock.sendMessage(
  msg.key.remoteJid,
  {
    text:
      " Ocurriï¿½ un error guardando las imágenes. " +
      "Revisa la consola."
  },
  {
    quoted: msg
  }
).catch(
  () => {}
);

}
}

export async function handlePay(sock, msg, args, sender) {
  const groupId = msg.key.remoteJid;

  if (!groupId.endsWith('@g.us')) {
    return sock.sendMessage(groupId, {
      text: '〒▽〒 ᴇsᴛᴇ ᴄᴏᴍᴀɴᴅᴏ sᴏʟᴏ ғᴜɴᴄɪᴏɴᴀ ᴇɴ ɢʀᴜᴘᴏs.'
    });
  }

  // /pay sin cantidad ni usuario
  if (!args.length) {
    return sock.sendMessage(groupId, {
      text:
`ᴜsᴀ /ᴘᴀʏ ᴄᴀɴᴛɪᴅᴀᴅ @ᴍᴇɴᴄɪᴏɴ ᴘᴀʀᴀ ᴛʀᴀsɴғᴇʀɪʀ *ᴄᴏɪɴs* ᴀ ᴏᴛʀᴏ ᴜsᴜᴀʀɪᴏ.`
    });
  }

  const amount = Number(args[0]);

  if (!Number.isInteger(amount) || amount <= 0) {
    return sock.sendMessage(groupId, {
      text:
`〒▽〒 ʟᴀ ᴄᴀɴᴛɪᴅᴀᴅ ᴅᴇʙᴇ sᴇʀ ᴜɴ ɴᴜᴍᴇʀᴏ ᴇɴᴛᴇʀᴏ ᴍᴀʏᴏʀ ǫᴜᴇ 0.`
    });
  }

  // Detectar destinatario por mención
  let target = null;

  const mentioned =
    msg.message?.extendedTextMessage?.contextInfo?.mentionedJid ||
    msg.message?.conversation?.contextInfo?.mentionedJid ||
    [];

  if (mentioned.length > 0) {
    target = mentioned[0];
  }

  // Detectar destinatario mediante respuesta/citación
  if (!target) {
    const quoted =
      msg.message?.extendedTextMessage?.contextInfo?.participant;

    if (quoted) {
      target = quoted;
    }
  }

  if (!target) {
    return sock.sendMessage(groupId, {
      text:
`ᴜsᴀ /ᴘᴀʏ ᴄᴀɴᴛɪᴅᴀᴅ @ᴍᴇɴᴄɪᴏɴ ᴘᴀʀᴀ ᴛʀᴀsɴғᴇʀɪʀ *ᴄᴏɪɴs* ᴀ ᴏᴛʀᴏ ᴜsᴜᴀʀɪᴏ.`
    });
  }

  // Evitar pagarse a sí mismo
  if (target === sender) {
    return sock.sendMessage(groupId, {
      text:
`〒▽〒 ɴᴏ ᴘᴜᴇᴅᴇs ᴛʀᴀɴsғᴇʀɪʀᴛᴇ *ᴄᴏɪɴs* ᴀ ᴛɪ ᴍɪsᴍᴏ.`
    });
  }

  const senderEco = getGroupEconomy(groupId, sender);
  const targetEco = getGroupEconomy(groupId, target);

  const senderBank = Number(senderEco.bank || 0);

  // Comprobar banco
  if (senderBank < amount) {
    return sock.sendMessage(groupId, {
      text:
`〒▽〒 ɴᴏ ᴛɪᴇɴᴇs sᴜғɪᴄɪᴇɴᴛᴇs \`ᴄᴏɪɴs\` ᴇɴ ᴛᴜ ʙᴀɴᴄᴏ.
> ᴅᴇᴘᴏsɪᴛᴀ ᴛᴜ ᴅɪɴᴇʀᴏ ᴄᴏɴ \`/ᴅ ᴀʟʟ\``
    });
  }

  // Transferencia
  senderEco.bank = senderBank - amount;
  targetEco.bank = Number(targetEco.bank || 0) + amount;

  saveDB(); 

  const user =
  db.users[target];

const username =
  user?.name ||
  user?.pushName ||
  target.split('@')[0];

const formattedAmount =
  amount.toLocaleString('en-US');

  return sock.sendMessage(groupId, {
    text:
`(≧▽≦) ¡ ʟᴇ ᴛʀᴀɴsғᴇʀɪsᴛᴇ ᴄᴏʀʀᴇᴄᴛᴀᴍᴇɴᴛᴇ \`${formattedAmount}\` ᴀ *${username}* !`
  });
}

// ==========================================================================
// 4) /delcar
// =========================================================================// Elimina el vehículo y todas las imágenes del álbum.

export async function handleDelCar(
sock,
msg,
query
) {
try {
loadCars();

if (!query) {
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:

`Uso:

/delcar ID

o

/delcar Personaje | Nombre del carro`
},
{
quoted: msg
}
);
}

let car = null;

if (
  /^\d+$/.test(
    query.trim()
  )
) {
  car = carsCache.find(
    c =>
      c.id ===
      Number(
        query.trim()
      )
  );

} else {
  const parts = query
    .split("|")
    .map(
      x => x.trim()
    );

  if (
    parts.length < 2
  ) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:

`Uso:

/delcar Personaje | Nombre del carro`
},
{
quoted: msg
}
);
}

  const personaje =
    parts[0]
      .toLowerCase();

  const nombre =
    parts[1]
      .toLowerCase()
      .replace(
        /[^\w]/g,
        "_"
      );

  car = carsCache.find(
    c =>
      c.personaje.toLowerCase() === personaje &&
      c.key === nombre
  );


if (!car) {
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
        " Vehículo no encontrado."
    },
    {
      quoted: msg
    }
  );
}

// Obtener todas las imágenes existentes.
const rutasValidas =
  Array.isArray(
    car.images
  )
    ? car.images.filter(
        p =>
          typeof p ===
            "string" &&
          fs.existsSync(p)
      )
    : [];

const buffersAlbum = [];

for (
  const ruta of rutasValidas
) {
  try {
    buffersAlbum.push(
      fs.readFileSync(
        ruta
      )
    );

  } catch (e) {
    console.log(
      "⚠️ No se pudo leer imagen del veh¿culo:",
      ruta,
      e.message
    );
  }
}

const folder = path.join(
  CAR_IMAGES,
  car.personaje
    .toLowerCase(),
  car.key
);

if (
  fs.existsSync(
    folder
  )
) {
  try {
    fs.rmSync(
      folder,
      {
        recursive: true,
        force: true
      }
    );

  } catch (e) {
    console.log(
      "⚠️ Error borrando la carpeta del veh¿culo:",
      e.message
    );
  }
}

// Eliminar el vehículo de los garajes.
for (
  const uid in db.users
) {
  if (
    Array.isArray(
      db.users[uid].garage
    )
  ) {
    db.users[uid].garage =
      db.users[
        uid
      ].garage.filter(
        x =>
          x !==
          car.key
      );
  }
}


carMap.delete(
  car.key
);

carsCache.splice(
  0,
  carsCache.length,
  ...carsCache.filter(
    x =>
      x.key !== car.key
  )
);

saveCars();
saveDB();

const texto =

` Vehículo eliminado

■ ${car.carName}

• ${car.personaje}
🆔 ${car.id}`;

if (
  buffersAlbum.length === 1
) {
  await sock.sendMessage(
    msg.key.remoteJid,
    {
      image:
        buffersAlbum[0],
      caption:
        texto
    },
    {
      quoted: msg
    }
  );

} else if (
  buffersAlbum.length > 1
) {
  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
        texto
    },
    {
      quoted: msg
    }
  );

  for (
    const buffer of buffersAlbum
  ) {
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        image:
          buffer
      }
    );
  }

} else {
  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
        texto
    },
    {
      quoted: msg
    }
  );
}
}
} catch (error) {
console.log(
"❌ Error en handleDelCar:",
error
);

await sock.sendMessage(
  msg.key.remoteJid,
  {
    text:
      " Ocurriï¿½ un error al eliminar el vehículo. " +
      "Revisa la consola para más detalles."
  },
  {
    quoted: msg
  }
).catch(
  () => {}
);

}
}


export async function handlePjAudio(
  sock,
  msg,
  args,
  sender
){
  

  const text =
    args.join(' ');

  if (!text) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'Uso:\n/pjaudio Nombre del personaje'
      },
      { quoted: msg }
    );
  }

  const ctx =
    msg.message?.extendedTextMessage
      ?.contextInfo;

  const quoted =
    ctx?.quotedMessage;

  if (
    !quoted?.audioMessage
  ){
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'Debes responder un audio.'
      },
      { quoted: msg }
    );
  }

  const char =
    findCharacter(text);

  if (!char){
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'Personaje no encontrado.'
      },
      { quoted: msg }
    );
  }

  const buffer =
    await downloadMediaMessage(
      {
        message: quoted,
        key:{
          remoteJid:
            msg.key.remoteJid
        }
      },
      'buffer',
      {}
    );

  const dir =
    './audios';

  if (!fs.existsSync(dir))
    fs.mkdirSync(dir);

  const file =
    `${dir}/${char.key}.mp3`;

  fs.writeFileSync(
    file,
    buffer
  );

  db.characterAudios[
    char.key
  ] = file;

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`✓ Audio guardado para ${char.name}`
    },
    { quoted: msg }
  );
}

const ACTION_TEXTS = {

    pat: {
        self: [
            "se da cariño propio.",
            "se acaricia la cabeza.",
            "se da mimos.",
            "se consiente un poco."
        ],
        target: [
            "le da cariño a",
            "acaricia suavemente a",
            "pasa la mano por la cabeza de",
            "le da mimos a"
        ]
    },

    hug: {
        self: [
            "se abraza a sí mismo.",
            "se da un abrazo.",
            "se envuelve entre sus brazos.",
            "se abraza con cariño."
        ],
        target: [
            "abraza con fuerza a",
            "le da un gran abrazo a",
            "abraza cariñosamente a",
            "envuelve entre sus brazos a"
        ]
    },

    kiss: {
        self: [
            "se da un beso frente al espejo.",
            "se besa a sí mismo.",
            "se manda un beso.",
            "se da un besito."
        ],
        target: [
            "besa a",
            "le roba un beso a",
            "le da un beso en la mejilla a",
            "le da un beso a"
        ]
    },

    cuddle: {
        self: [
            "se acurruca solo.",
            "se abraza mientras descansa.",
            "se acomoda cómodamente.",
            "se acurruca consigo mismo."
        ],
        target: [
            "se acurruca junto a",
            "abraza tiernamente a",
            "descansa junto a",
            "se acuesta junto a"
        ]
    },

    slap: {
        self: [
            "se da una cachetada.",
            "se golpea la cara.",
            "se castiga.",
            "se pega a sí mismo."
        ],
        target: [
            "golpea a",
            "le da una cachetada a",
            "abofetea a",
            "castiga a"
        ]
    },

    bite: {
        self: [
            "se muerde.",
            "se da un mordisco.",
            "se muerde el brazo.",
            "se muerde a sí mismo."
        ],
        target: [
            "muerde a",
            "le da un mordisco a",
            "clava los dientes en",
            "mordisquea a"
        ]
    },

    poke: {
        self: [
            "se pincha solo.",
            "se toca con el dedo.",
            "se molesta a sí mismo.",
            "se da pequeños toques."
        ],
        target: [
            "pincha a",
            "molesta a",
            "le da pequeños toques a",
            "toca a"
        ]
    },

    lick: {
        self: [
            "se lame.",
            "se limpia solo.",
            "se lame la mano.",
            "se da un lengüetazo."
        ],
        target: [
            "lama a",
            "le da un lengüetazo a",
            "limpia a",
            "lame cariñosamente a"
        ]
    },

    wave: {
        self: [
            "saluda al aire.",
            "saluda felizmente.",
            "levanta la mano.",
            "saluda con una sonrisa."
        ],
        target: [
            "saluda a",
            "mueve la mano hacia",
            "dice hola a",
            "saluda alegremente a"
        ]
    },

    cry: {
        self: [
            "llora desconsoladamente.",
            "rompe en llanto.",
            "no puede dejar de llorar.",
            "llora en silencio."
        ],
        target: [
            "sufre y llora por",
            "llora abrazando a",
            "no deja de llorar por",
            "se pone a llorar junto a"
        ]
    },

    smile: {
        self: [
            "sonríe felizmente.",
            "muestra una gran sonrisa.",
            "sonríe con ternura.",
            "está muy feliz."
        ],
         target: [
            "sonríe a",
            "le dedica una sonrisa a",
            "sonríe feliz junto a",
            "mira sonriendo a"
        ]
    },

    shy: {
        self: [
            "se pone muy tímido.",
            "esconde la cara de vergüenza.",
            "se sonroja.",
            "no sabe dónde mirar."
        ],
        target: [
            "se sonroja frente a",
            "se pone tímido por",
            "se avergüenza al ver a",
            "se esconde de"
        ]
    },

    dance: {
        self: [
            "empieza a bailar.",
            "baila alegremente.",
            "se mueve al ritmo de la música.",
            "se pone a bailar feliz."
        ],
        target: [
            "baila con",
            "invita a bailar a",
            "empieza a bailar junto a",
            "disfruta bailando con"
        ]
    }

};

export async function handleAction(sock, msg, actionName) {

    const folder = path.join(ACTIONS_PATH, actionName);

    if (!fs.existsSync(folder)) {
        return await sock.sendMessage(
            msg.key.remoteJid,
            {
                text: `❌ No hay GIFs para ${actionName}.`
            },
            { quoted: msg }
        );
    }

    const gifs = fs.readdirSync(folder).filter(file =>
        file.endsWith(".mp4") || file.endsWith(".gif")
    );

    if (!gifs.length) {
        return await sock.sendMessage(
            msg.key.remoteJid,
            {
                text: `❌ No hay GIFs guardados para ${actionName}.`
            },
            { quoted: msg }
        );
    }

    const targetData = ACTION_TEXTS[actionName];

    if (!targetData) {
        return await sock.sendMessage(
            msg.key.remoteJid,
            {
                text: "❌ Acción no configurada."
            },
            { quoted: msg }
        );
    }

    let targetName = null;
let targetJid = null;

const mentioned =
    msg.message?.extendedTextMessage?.contextInfo?.mentionedJid || [];

if (mentioned.length) {

    targetJid = mentioned[0];

} else {

    const quoted =
        msg.message?.extendedTextMessage?.contextInfo;

    if (quoted?.participant) {

        targetJid = quoted.participant;

    }

}

if (targetJid) {

    const user =
        db.users[targetJid];

    targetName =
        user?.name ||
        user?.pushName ||
        targetJid.split("@")[0];

}

    let text;

    if (targetName) {

        const action =
            targetData.target[
                Math.floor(Math.random() * targetData.target.length)
            ];

        text =
            `*${msg.pushName || "Usuario"}* ${action} *${targetName}*`;

    } else {

        const action =
            targetData.self[
                Math.floor(Math.random() * targetData.self.length)
            ];

        text =
            `*${msg.pushName || "Usuario"}* ${action}`;

    }

    const random =
        gifs[Math.floor(Math.random() * gifs.length)];

    const file =
        path.join(folder, random);

    await sock.sendMessage(
        msg.key.remoteJid,
        {
            video: fs.readFileSync(file),
            gifPlayback: true,
            caption: text
        },
        { quoted: msg }
    );

}

export async function handleSetLigue(
  sock,
  msg,
  args,
  sender
){

  if (
    !isMainOwnerId(sender) &&
    !isSecondaryOwnerId(sender)
  ){
    return;
  }

  const query =
    args.join(' ').trim();

  if (!query){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/setligue Nombre del personaje

Ejemplo

/setligue Nazuna Nanakusa`
      },
      {
        quoted: msg
      }
    );

  }

  const queryNormalized =
    query
      .trim()
      .toLowerCase();

  const character =
    charactersCache.find(
      c =>
        String(c.name || '')
          .trim()
          .toLowerCase() === queryNormalized
    ) ||
    charactersCache.find(
      c =>
        String(c.key || '')
          .trim()
          .toLowerCase() === queryNormalized
    ) ||
    charactersCache.find(
      c =>
        String(c.name || '')
          .toLowerCase()
          .includes(queryNormalized)
    );

  if (!character){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  db.waifus ??= {};

  if (
    db.waifus[
      character.key
    ]
  ){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
` ${character.name} ya está registrada como waifu.`
      },
      {
        quoted: msg
      }
    );

  }

  db.waifus[
    character.key
  ] = {

    key: character.key,

    id: character.id,

    name: character.name,

    anime: character.anime,

    creator: sender,

    createdAt: Date.now(),

    enabled: true

  };

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`♡ Waifu registrada

◇ Nombre »
${character.name}

☆ Anime »
${character.anime}

□ ID »
${character.id}

> Disponible para /ligue`
    },
    {
      quoted: msg
    }
  );

}

export async function handleTin(
  sock,
  msg,
  groupId,
  sender
){

  const user =
    initUser(sender);

  const economy =
    getGroupEconomy(
      groupId,
      sender
    );

  if (
    user.training
  ){

    const left =
      user.training.finish -
      Date.now();

    if (left > 0){

      const h =
        Math.floor(
          left / 3600000
        );

      const m =
        Math.floor(
          (left % 3600000)
          / 60000
        );

      const s =
        Math.floor(
          (left % 60000)
          / 1000
        );

      return sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
` Ya estás entrenando.

ⴵ Tiempo restante

${h}h ${m}m ${s}s`
        },
        {
          quoted: msg
        }
      );

    }

    user.level++;

    user.atk +=
      user.training.atk;

    user.def +=
      user.training.def;

    user.vel +=
      user.training.vel;

    user.pres +=
      user.training.pres;

    const oldRank =
      getTrainingRank(
        user.level - 1
      );

    const newRank =
      getTrainingRank(
        user.level
      );

    user.training = null;

    saveDB();

    if (
      oldRank !== newRank
    ){

      await sock.sendMessage(
        msg.key.remoteJid,
        {        
          text:
`AVISO: @${sender.split('@')[0]}

haz subido de rango

Rango:
\`${oldRank}\` ➜ \`${newRank}\``,
          mentions:[
            sender
          ]
        },
        {
          quoted: msg
        }
      );

    }

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`✓ Entrenamiento completado

✰ Nivel »
\`${user.level}\`

† Atk »
\`${user.atk}\`

‡ Dfa »
\`${user.def}\`

⥉ Vel »
\`${user.vel}\`

⊗ Pres »
\`${user.pres}\``
      },
      {
        quoted: msg
      }
    );

  }

  const cost =
    getTrainingCost(
      user.level
    );

  if (
    economy.coins < cost
  ){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Necesitas

¥${cost.toLocaleString()}

para entrenar.`
      },
      {
        quoted: msg
      }
    );

  }

  economy.coins -= cost;

  const stats =
    generateTrainingStats(
      user
    );

  user.training = {

    finish:
      Date.now() +
      3600000,

    cost,

    nextLevel:
      user.level + 1,

    atk:
      stats.atk,

    def:
      stats.def,

    vel:
      stats.vel,

    pres:
      stats.pres

  };

  saveDB();

  // La etapa B continuará aquí.

let pfp;

try{

  pfp =
    await sock.profilePictureUrl(
      sender,
      'image'
    );

}catch{

  pfp =
'https://files.catbox.moe/6m8m6i.jpg';

}

const rank =
  getTrainingRank(
    user.level
  );

const atkBefore =
  user.atk;

const defBefore =
  user.def;

const velBefore =
  user.vel;

const presBefore =
  user.pres;

const atkAfter =
  atkBefore +
  stats.atk;

const defAfter =
  defBefore +
  stats.def;

const velAfter =
  velBefore +
  stats.vel;

const presAfter =
  presBefore +
  stats.pres;

const caption =
`Entrenamiento iniciado

♠︎ *Usuario* : \`${user.name}\`
✢ *Rango* : \`${rank}\`
✰ *Nivel* : \`${user.level} ➪ ${user.level + 1}\`
✎ *Modo* : \`Todos los stats\`
⛀ *Costo dinero* : \`${cost.toLocaleString()}\` coins
ⴵ *Duraci¿n* : \`1h\`

✎ *Subida de stats*

• *† Atk*: \`${atkBefore} → ${atkAfter} (+${stats.atk})\`
• *‡ Dfa*: \`${defBefore} → ${defAfter} (+${stats.def})\`
• *⥉ Vel*: \`${velBefore} → ${velAfter} (+${stats.vel})\`
• *⊗ Pres*: \`${presBefore} → ${presAfter} (+${stats.pres})\`

> Cuando termine usa */tin* para aplicar.`;

await sock.sendMessage(
  msg.key.remoteJid,
  {
    image:{
      url: pfp
    },
    caption
  },
  {
    quoted: msg
  }
);

}

// ==================================================
// TOP GLOBAL DE USUARIOS POR COMANDOS
// ==================================================

export async function handleTopCmd(sock, msg, args) {

  const jid = msg.key.remoteJid;

  // Página solicitada
  let page = parseInt(args[0], 10);

  if (!Number.isInteger(page) || page < 1) {
    page = 1;
  }

  const perPage = 10;

  // Obtener usuarios con comandos registrados
  const users = Object.entries(db.users || {})
    .map(([userJid, user]) => ({
      jid: userJid,
      name: user?.name || 'Usuario',
      commands: Number(user?.totalCommands || 0)
    }))
    .filter(user => user.commands > 0)
    .sort((a, b) => {
      // Mayor cantidad primero
      if (b.commands !== a.commands) {
        return b.commands - a.commands;
      }

      // Si empatan, ordenar por nombre
      return a.name.localeCompare(b.name);
    });

  // Si no hay usuarios
  if (!users.length) {
    return sock.sendMessage(
      jid,
      {
        text: '♧ No hay usuarios con comandos registrados ♧'
      },
      {
        quoted: msg
      }
    );
  }

  const totalPages =
    Math.ceil(users.length / perPage);

  // Página fuera de rango
  if (page > totalPages) {
    return sock.sendMessage(
      jid,
      {
        text:
          ` Top de usuarios con más comandos \n\n` +
          `ï¿½ La página *${page}* no existe.\n` +
          `ï¿½ Hay *${totalPages}* páginas disponibles.`
      },
      {
        quoted: msg
      }
    );
  }

  const start =
    (page - 1) * perPage;

  const pageUsers =
    users.slice(start, start + perPage);

  let text =
    ` Top de usuarios con más comandos \n\n`;

  for (let i = 0; i < pageUsers.length; i++) {

    const user = pageUsers[i];

    const position =
      start + i + 1;

    // Corona especial solamente para el #1
    const crown =
      position === 1
        ? '♔ '
        : '';

    text +=
      `✧ ${crown}${position} » *${user.name}* » \`${user.commands.toLocaleString()}\`\n`;

    if (i < pageUsers.length - 1) {
      text += `\n`;
    }
  }

  text +=
    `\n\nï¿½ Página *${page}* de *${totalPages}*`;

  // Mostrar siguiente página solamente si existe
  if (page < totalPages) {
    text +=
      `\nï¿½ Para ver la siguiente página usa: */topcmd ${page + 1}*`;
  }

  // Mostrar página anterior si corresponde
  if (page > 1) {
    text +=
      `\nï¿½ Página anterior: */topcmd ${page - 1}*`;
  }

  await sock.sendMessage(
    jid,
    {
      text
    },
    {
      quoted: msg
    }
  );
}



export async function handleDelSerie(
  sock,
  msg,
  args,
  sender
){


  const query =
    args.join(' ').trim();

  if (!query){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/delserie Nombre de la serie`
      },
      {
        quoted: msg
      }
    );

  }
  const serie =
    findSeries(query);

  if (
    !isMainOwnerId(sender) &&
    serie &&
    serie.owner &&
    serie.owner !== sender
  ) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          '◇ Acceso denegado.\\n\\n' +
          '□ Esta serie pertenece al Secondary Owner que la creo.\\n' +
          '◇ Solo su creador puede eliminarla.'
      },
      {
        quoted: msg
      }
    );

  }
  if (!serie){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Serie no encontrada.'
      },
      {
        quoted: msg
      }
    );

  }

  const chars = [];

  for (
    const key of serie.characters
  ){

    const c =
      characterKeyMap.get(key);

    if (c)
      chars.push(c);

  }

  const confirm =
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`⚠ Confirmación @${sender.split('@')[0]}

ï¿½Estï¿½ seguro de eliminar la serie?

◇ Serie »
${serie.name}

□ Personajes »
${chars.length}

 Esta acciï¿½n eliminarï¿½:

• Todos los personajes
• Sus im¿genes
• Sus videos
• Sus reclamaciones
• Los alias de la serie

Responde citando este mensaje:

\`si\``,
        mentions:[
          sender
        ]
      },
      {
        quoted: msg
      }
    );

  db.pendingDeleteSeries ??= {};

  db.pendingDeleteSeries[
    confirm.key.id
  ] = {

    owner: sender,

    group:
      msg.key.remoteJid,

    series:
      serie.name,

    created:
      Date.now()

  };

  saveDB();

}

async function handleDeleteSerieReply(
  sock,
  msg,
  sender
){

  const quoted =
    msg.message?.extendedTextMessage
    ?.contextInfo?.stanzaId;

  if (!quoted)
    return false;

  db.pendingDeleteSeries ??= {};

  const pending =
    db.pendingDeleteSeries[
      quoted
    ];

  if (!pending)
    return false;

  if (
    pending.owner !== sender
  ){
    return true;
  }

  const text =
    (
      msg.message?.conversation ||
      msg.message?.extendedTextMessage?.text ||
      ''
    )
    .trim()
    .toLowerCase();

  if (
    text !== 'si' &&
    text !== 'sí' &&
    text !== 'no'
  ){
    return true;
  }

  delete db.pendingDeleteSeries[
    quoted
  ];

  if (
    text === 'no'
  ){

    saveDB();

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Eliminación cancelada.'
      },
      {
        quoted: msg
      }
    );

    return true;

  }
  const serie =
    findSeries(
      pending.series
    );

  if (
    !isMainOwnerId(sender) &&
    serie &&
    serie.owner &&
    serie.owner !== sender
  ) {

    saveDB();

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          '◇ Eliminacion denegada.\\n\\n' +
          '□ Esta serie pertenece a otro Secondary Owner.\\n' +
          '◇ Solo su creador puede eliminarla.'
      },
      {
        quoted: msg
      }
    );

    return true;
  }
  if (!serie){

    saveDB();

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ La serie ya no existe.'
      },
      {
        quoted: msg
      }
    );

    return true;

  }

  const removed = [];

  for (
    const key of serie.characters
  ){

    const char =
      characterKeyMap.get(
        key
      );

    if (!char)
      continue;

    removed.push(
      char.name
    );

    charactersCache =
      charactersCache.filter(
        c =>
          c.key !== key
      );

    characterMap.delete(
      char.name.toLowerCase()
    );

    characterKeyMap.delete(
      key
    );

    for (
      const file of
      getCharacterImages(key)
    ){

      try{

        fs.unlinkSync(
          path.join(
            GACHA_IMAGES,
            file
          )
        );

      }catch{}

    }

    for (
      const file of
      getCharacterVideos(key)
    ){

      try{

        fs.unlinkSync(
          path.join(
            GACHA_VIDEOS,
            file
          )
        );

      }catch{}

    }

  }

  seriesCache.delete(
    serie.name.toLowerCase()
  );

  try{

    fs.unlinkSync(
      path.join(
        SERIES_DIR,
        `${serie.name
          .toLowerCase()
          .replace(/[^\w]/g,'_')}.json`
      )
    );

  }catch{}

  if (
    db.seriesAliases
  ){

    for (
      const alias of
      Object.keys(
        db.seriesAliases
      )
    ){

      if (
        db.seriesAliases[
          alias
        ].toLowerCase()
        ===
        serie.name.toLowerCase()
      ){

        delete db.seriesAliases[
          alias
        ];

      }

    }

  }

  buildOwnerIndex();

  rebuildHarems();

  saveCharacters();

  /* ========================================================
   * CHARACTER_UNDEFINED_GUARD_V1
   * ======================================================== */

  if (
    typeof character !== "undefined" &&
    character
  ) {

    await checkMissionProgress(
      sock,
      msg,
      character
    );

  }

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`✓ Serie eliminada

◇ Serie »
${serie.name}

□ Personajes eliminados »
${removed.length}`
    },
    {
      quoted: msg
    }
  );

  return true;

}

export async function handleAzz(sock, msg, jid) {

  const text =
    db.azzText ||
    'No hay actualizaciones registradas.';

  await sock.sendMessage(jid,{
    text:
`Actualizaciones:

> ${text}`
  },{ quoted: msg });

}

export async function handleBulguru(
  sock,
  msg,
  args
) {
  const personaje =
    args.join(' ').trim();

  const jid =
    msg.key.remoteJid;

  if (!personaje) {
    return sock.sendMessage(
      jid,
      {
        text:
          '◇ Uso:\n/bulguru nombre o tag'
      },
      {
        quoted: msg
      }
    );
  }

  const manualTag =
    getManualTag(personaje);

  if (!manualTag) {
    return sock.sendMessage(
      jid,
      {
        text:
          `》*El tag "${personaje}" no existe.*\n` +
          `◇ Crea primero el tag con /addtag.`
      },
      {
        quoted: msg
      }
    );
  }

  const images =
    Array.isArray(manualTag.images)
      ? manualTag.images
      : [];

  if (!images.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          `》*El tag "${personaje}" existe, pero todavía no tiene imágenes.*`
      },
      {
        quoted: msg
      }
    );
  }

  const validImages =
    images.filter(image => {
      if (!image?.file) return false;

      const filePath =
        path.join(
          process.cwd(),
          'manual-tags',
          'images',
          normalizeManualTag(personaje),
          image.file
        );

      return fs.existsSync(filePath);
    });

  if (!validImages.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          `》*El tag "${personaje}" no tiene imágenes locales disponibles.*`
      },
      {
        quoted: msg
      }
    );
  }

  const selected =
    validImages[
      Math.floor(
        Math.random() * validImages.length
      )
    ];

  const imagePath =
    path.join(
      process.cwd(),
      'manual-tags',
      'images',
      normalizeManualTag(personaje),
      selected.file
    );

  try {
    const imageBuffer =
      fs.readFileSync(imagePath);

    await sock.sendMessage(
      jid,
      {
        image: imageBuffer,
        caption:
          `◇ ${personaje}`
      },
      {
        quoted: msg
      }
    );
  } catch (error) {
    console.log(
      '[BULGURU] Error enviando imagen:',
      error?.message || error
    );

    return sock.sendMessage(
      jid,
      {
        text:
          '◇ No se pudo enviar la imagen local.'
      },
      {
        quoted: msg
      }
    );
  }
}

export async function handleDanbooru(
  sock,
  msg,
  args
) {
  const personaje =
    args.join(' ').trim();

  if (!personaje) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: '◇ Uso:\n/danbooru Ellen Joe'
      },
      {
        quoted: msg
      }
    );
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text: `🔍 Buscando: ${personaje}`
    },
    {
      quoted: msg
    }
  );

  const imgUrl =
    await getDanbooruImage(personaje);

  if (!imgUrl) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`》*El tag no existe, puedes encontrarlo en la pagina oficial.*
✿ *Pagina* \`https://danbooru.donmai.us/\``
      },
      {
        quoted: msg
      }
    );
  }

  const image =
    await downloadDanbooruImage(imgUrl);

  if (!image) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: '• Danbooru devolvió una imagen no compatible'
      },
      {
        quoted: msg
      }
    );
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      image: image.buffer,
      mimetype: image.mimetype,
      caption: booruCaption(personaje, image.buffer)
    },
    {
      quoted: msg
    }
  );
}

export async function handleGelbooru(
  sock,
  msg,
  args,
  sender
) {
  const query =
    args.join(' ').trim();

  const jid =
    msg.key.remoteJid;

  if (!query) {
    return sock.sendMessage(
      jid,
      {
        text: '◇ Uso:\n/gelbooru nombre o tag'
      },
      {
        quoted: msg
      }
    );
  }

  const lastUse =
    gelbooruCooldowns.get(sender) || 0;

  const remaining =
    10000 - (Date.now() - lastUse);

  if (remaining > 0) {
    return sock.sendMessage(
      jid,
      {
        text:
          `⏳ Espera ${Math.ceil(remaining / 1000)} segundos para usar /gelbooru nuevamente.`
      },
      {
        quoted: msg
      }
    );
  }

  gelbooruCooldowns.set(
    sender,
    Date.now()
  );

  const imageUrls =
    await getGelbooruApiImageCandidates(query);

  if (!imageUrls?.length) {
    return sock.sendMessage(
      jid,
      {
        text:
`》*El tag no existe, puedes encontrarlo en la pagina oficial.*
✿ *Pagina* \`https://gelbooru.com/\``
      },
      {
        quoted: msg
      }
    );
  }

  let image = null;

  for (const imageUrl of imageUrls) {
    image =
      await downloadGelbooruImage(imageUrl);

    if (image) break;
  }

  if (!image) {
    return sock.sendMessage(
      jid,
      {
        text:
          '❌ Gelbooru devolvió un archivo de imagen no compatible.'
      },
      {
        quoted: msg
      }
    );
  }

  await sock.sendMessage(
    jid,
    {
      image: image.buffer,
      mimetype: image.mimetype,
      caption: booruCaption(
        query,
        image.buffer
      )
    },
    {
      quoted: msg
    }
  );
}

export async function handleSetRwpCooldown(
  sock,
  msg,
  args,
  sender
){

  if (sender !== OWNER_NUMBER)
  return;

  const value =
    args[0]?.toLowerCase();

  if (!value) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso:\n/setrwpsg 5m\n/setrwpsg 30sg'
      },
      { quoted: msg }
    );

  }

  let amount = 0;
  let type = '';

  if (value.endsWith('m')) {

    amount =
      parseInt(
        value.replace('m','')
      );

    type = 'm';

  }

  else if (
    value.endsWith('sg')
  ) {

    amount =
      parseInt(
        value.replace('sg','')
      );

    type = 'sg';

  }

  else {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Usa m o sg.'
      },
      { quoted: msg }
    );

  }

  db.rwpCooldown = amount;
  db.rwpCooldownType = type;

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Cooldown actualizado

Tiempo » ${amount}${type}`
    },
    {
      quoted: msg
    }
  );

}

export async function handleLigues(
  sock,
  msg,
  args,
  sender
){

  const chatId =
    msg.key.remoteJid;

  const user =
    initUser(sender);

  user.waifu ??= {
    current:null,
    totalLove:0,
    maxLove:0,
    ligues:{},
    groupLigues:{},
    lastLigue:0
  };

  user.waifu.groupLigues ??= {};

  const groupLigues =
    user.waifu.groupLigues[chatId] || {};

  const ligueEntries =
    Object.entries(groupLigues);

  if (!ligueEntries.length){

    return sock.sendMessage(
      chatId,
      {
        text:
`✧₊˚⊹♡ ᴛᴜs ʟɪɢᴜᴇs ♡⊹˚₊✧

　　❀ ɴᴏ ᴛɪᴇɴᴇs ʟɪɢᴜᴇs ᴇɴ ᴇsᴛᴇ ɢʀᴜᴘᴏ ❀`
      },
      { quoted: msg }
    );
  }

  const sorted =
    ligueEntries
      .sort(
        ([,a],[,b]) =>
          (Number(b?.love) || 0) -
          (Number(a?.love) || 0)
      );

  const perPage = 10;

  const totalPages =
    Math.ceil(
      sorted.length /
      perPage
    );

  let page =
    Number(args[0]) || 1;

  if (page < 1)
    page = 1;

  if (page > totalPages)
    page = totalPages;

  const start =
    (page - 1) *
    perPage;

  const pageEntries =
    sorted.slice(
      start,
      start + perPage
    );

  const username =
    msg.pushName ||
    sender.split('@')[0];

  let text =
`✧₊˚⊹♡ ᴛᴜs ʟɪɢᴜᴇs ${username} ♡⊹˚₊✧

`;

  pageEntries.forEach(
  ([characterKey, ligue], index) => {

    const position =
      start + index + 1;

    const character =
      charactersCache.find(
        c =>
          String(c.key || '')
            .trim()
            .toLowerCase() ===
          String(characterKey || '')
            .trim()
            .toLowerCase()
      );

    const characterName =
      character?.name ||
      characterKey ||
      'Desconocido';

    const love =
      Number(ligue?.love) || 0;

    text +=
`❀ ${position} ❀ *${characterName}*
　　› \`ᴀᴍᴏʀ ${love}%\`

`;
  }
);

  const nextPage =
    page < totalPages
      ? `${page + 1}°`
      : '1°';

  text +=
`> ✧ ᴘáɢɪɴᴀ ${page} ᴅᴇ ${totalPages} \`ᴜsᴀ /ligues ${nextPage}\` ✧`;

  return sock.sendMessage(
    chatId,
    {
      text
    },
    { quoted: msg }
  );
}

export async function handleTopWaifu(
  sock,
  msg,
  args
){

  const page =
    Math.max(
      1,
      Number(args[0]) || 1
    );

  const perPage = 10;

  const chatId =
    msg.key.remoteJid;

  const ranking = [];

  for (
    const [id,user]
    of Object.entries(db.users)
  ){

    if (
      !user.waifu
    ) continue;

    const groupLigues =
      user.waifu.groupLigues?.[chatId] || {};

    const ligueEntries =
      Object.values(
        groupLigues
      );

    const ligues =
      ligueEntries.length;

    if (
      ligues <= 0
    ) continue;

    const total =
      ligueEntries.reduce(
        (sum, ligue) =>
          sum + (Number(ligue?.love) || 0),
        0
      );

    const max =
      Math.max(
        ...ligueEntries.map(
          ligue =>
            Number(
              ligue?.love || 0
            )
        )
      );

    ranking.push({

      id,

      name:
        user.name ||
        id.split('@')[0],

      total,

      max,

      ligues

    });

  }

  ranking.sort(
    (a,b)=>{

      if (
        b.total !== a.total
      )
        return b.total-a.total;

      return b.ligues-a.ligues;

    }
  );

  if (!ranking.length){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`♯ ɴᴏ ʜᴀʏ ʟɪɢᴜᴇs ᴇɴ ᴇsᴛᴇ ɢʀᴜᴘᴏ
　⁀➷ ᴜsᴀ ʟɪɢᴜᴇ \`Personaje\``
      },
      {
        quoted: msg
      }
    );

  }

  const pages =
    Math.max(
      1,
      Math.ceil(
        ranking.length /
        perPage
      )
    );

  const safePage =
    Math.min(
      page,
      pages
    );

  const slice =
    ranking.slice(
      (safePage-1)*perPage,
      safePage*perPage
    );

  let text =
`✧₊˚⊹♡ 㬏 ᴡᴀɪғᴜ ᴛᴏᴘ — ʀᴀɴᴋɪɴɢ ᴅᴇ ʟɪɢᴜᴇs ♡⊹˚₊✧

　　✧ ᴘáɢɪɴᴀ ${safePage}/${pages} ✧

`;

  let pos =
    (safePage-1)*
    perPage+1;

  for (
    const user of slice
  ){

    let medal='🏅';

    if (pos===1)
      medal='🥇';

    else if(pos===2)
      medal='🥈';

    else if(pos===3)
      medal='🥉';

    const percent =
      Math.min(
        100,
        user.max
      );

    const filled =
      Math.max(
        0,
        Math.min(
          10,
          Math.round(
            percent/10
          )
        )
      );

    const bar =
      '█'.repeat(filled)+
      '░'.repeat(
        10-filled
      );

    text +=
`♯ ${pos}. ${medal} ${user.name}
　⁀➷ ᴛᴏᴛᴀʟ: ${user.total}% ⋆ ʟɪɢᴜᴇs: ${user.ligues} ⋆ ᴍáx: ${user.max}%
　　[${bar}]

`;

    pos++;

  }

  text +=
`　　✧ ᴘáɢɪɴᴀ ${safePage}/${pages} ⋆ ᴜsᴀ /topwaifu ${Math.min(safePage+1,pages)} ✧`;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text
    },
    {
      quoted: msg
    }
  );

}

export async function handleLigue(
  sock,
  msg,
  args,
  sender
){

  const query =
    args.join(' ').trim();

  if (!query){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`❍ Uso

/ligue <nombre waifu>`
      },
      {
        quoted: msg
      }
    );

  }

  const queryNormalized =
    query
      .trim()
      .toLowerCase();

  const character =
    charactersCache.find(
      c =>
        String(c.name || '')
          .trim()
          .toLowerCase() === queryNormalized
    ) ||
    charactersCache.find(
      c =>
        String(c.key || '')
          .trim()
          .toLowerCase() === queryNormalized
    ) ||
    charactersCache.find(
      c =>
        String(c.name || '')
          .toLowerCase()
          .includes(queryNormalized)
    );

  if (!character){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  const gender =
    String(
      character.gender || ''
    )
      .trim()
      .toLowerCase();

  if (
    gender !== 'mujer'
  ){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ No puedes ligar con ${character.name}.

 Género ï¿½
${character.gender || 'Desconocido'}

> Solo los personajes con género Mujer pueden usarse en /ligue.`
      },
      {
        quoted: msg
      }
    );

  }

  const chatId =
    msg.key.remoteJid;

  const user =
    initUser(sender);

  user.waifu ??= {
    current:null,
    totalLove:0,
    maxLove:0,
    ligues:{},
    groupLigues:{},
    lastLigue:0
  };

  user.waifu.groupLigues ??= {};
  user.waifu.groupLigues[chatId] ??= {};

  if (
    user.waifu.groupLigues[chatId]?.[character.key]
  ){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`♯ ʏᴀ ᴇsᴛᴀs ʟɪɢᴀᴅᴏ ᴄᴏɴ \`${character.name}\`
> ⁀➷ ᴘᴜᴇᴅᴇs ʀᴏᴍᴘᴇʀ ᴄᴏɴ \`/romper ${character.name}\``
      },
      {
        quoted: msg
      }
    );

  }

  const existingLigueOwner =
    Object.entries(db.users || {}).find(
      ([ownerId, ownerData]) =>
        ownerId !== sender &&
        ownerData?.waifu?.groupLigues?.[chatId]?.[character.key]
    );

  if (existingLigueOwner){

    const [ownerId, ownerData] =
      existingLigueOwner;

    const ownerName =
      ownerData?.name ||
      ownerId.split('@')[0];

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`✧ ꒰ ɴᴏ ᴘᴜᴇᴅᴇs ʟɪɢᴀʀ ᴄᴏɴ \`${character.name}\` ʏᴀ ᴇsᴛᴀ ᴄᴏɴ \`${ownerName}\`꒱ ✧`
      },
      {
        quoted: msg
      }
    );

  }

  const CD =
    20 * 60 * 1000;

  user.waifu.lastLigueByChat ??= {};

  const lastLigue =
    Number(
      user.waifu.lastLigueByChat[chatId] || 0
    );

  if (
    Date.now() -
    lastLigue
    < CD
  ){

    const leftSeconds =
      Math.ceil(
        (
          CD -
          (
            Date.now() -
            lastLigue
          )
        ) / 1000
      );

    const leftMinutes =
      Math.floor(
        leftSeconds / 60
      );

    const seconds =
      leftSeconds % 60;

    return sock.sendMessage(
      chatId,
      {
        text:
`✧ ꒰ ᴇsᴘᴇʀᴀ \`${leftMinutes} ᴍɪɴᴜᴛᴏs ${seconds} sᴇɢᴜɴᴅᴏs\` ᴘᴀʀᴀ ᴠᴏʟᴠᴇʀ ᴀ ʟɪɢᴀʀ ꒱ ✧`
      },
      {
        quoted: msg
      }
    );

  }

  user.waifu.lastLigueByChat[chatId] =
    Date.now();

  user.waifu.lastLigue =
    Date.now();

  const accepted =
    Math.random() < 0.50;

  const imagePath =
    getCharacterImage(character);

  const imgUrl =
    await getGelbooruImage(
      character.tag ||
      character.name
    );

  if (!accepted){

    saveDB();

    const payload = {

      text:
`✧･ﾟ: * \`Propuesta rechazada\`* :･ﾟ✧
⊹⊱ *${character.name}* aún no siente suficiente confianza.
⊹⊱ Inténtalo nuevamente en 20 minutos.
⊹⊱ \`Probabilidad: 50%\` `

    };


    return sock.sendMessage(
      msg.key.remoteJid,
      payload,
      {
        quoted: msg
      }
    );

  }

  const love =
    Math.floor(
      Math.random()*11
    ) + 10;

  user.waifu.current =
    character.key;

  const ligueData = {

    love,

    owner: sender,

    level:'Conocidos',

    gifts:0,

    kisses:0,

    hugs:0,

    started:
      Date.now(),

    chatId

  };

  user.waifu.groupLigues[chatId][
    character.key
  ] = ligueData;

  user.waifu.ligues[
    character.key
  ] = ligueData;

  user.waifu.totalLove += love;

  if (
    love >
    user.waifu.maxLove
  ){
    user.waifu.maxLove =
      love;
  }

  saveDB();

  const payload = {

    caption:
`ᩥ *¡Aceptado!*

💕 *${character.name}* ha aceptado tu propuesta.

➩ _"Quiz¿s podr¿a funcionar entre nosotros..."_

» Afinidad inicial : \`${love}%\`
» Nivel : \`Conocidos\`

> Regálale algo con */giftshop* y */giftgive*

> Consulta el estado con */wainfo ${character.name}*`

  };

  if (imagePath){

    payload.image =
      fs.readFileSync(
        imagePath
      );

  }else if(imgUrl){

    payload.image = {
      url: imgUrl
    };

  }else{

    delete payload.caption;

    payload.text =
`ᩥ ¡Aceptado!

💕 ${character.name} ha aceptado tu propuesta.

Afinidad inicial: ${love}%`;

  }

  await sock.sendMessage(
    msg.key.remoteJid,
    payload,
    {
      quoted: msg
    }
  );

}

export async function handleRomper(
  sock,
  msg,
  args,
  jid,
  sender
){

  const query =
    args.join(' ').trim();

  if (!query){

    return sock.sendMessage(
      jid,
      {
        text:
`❍ Uso

/romper <nombre personaje>`
      },
      {
        quoted: msg
      }
    );

  }

  const queryNormalized =
    query
      .trim()
      .toLowerCase();

  const character =
    charactersCache.find(
      c =>
        String(c.name || '')
          .trim()
          .toLowerCase() === queryNormalized
    ) ||
    charactersCache.find(
      c =>
        String(c.key || '')
          .trim()
          .toLowerCase() === queryNormalized
    ) ||
    charactersCache.find(
      c =>
        String(c.name || '')
          .toLowerCase()
          .includes(queryNormalized)
    );

  if (!character){

    return sock.sendMessage(
      jid,
      {
        text:
'◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  const chatId =
    msg.key.remoteJid;

  const user =
    initUser(sender);

  user.waifu ??= {
    current:null,
    totalLove:0,
    maxLove:0,
    ligues:{},
    groupLigues:{},
    lastLigue:0
  };

  user.waifu.groupLigues ??= {};
  user.waifu.groupLigues[chatId] ??= {};

  const ligue =
    user.waifu.groupLigues[chatId]?.[character.key];

  if (!ligue){

    return sock.sendMessage(
      jid,
      {
        text:
`♯ ɴᴏ ᴇsᴛᴀs ʟɪɢᴀᴅᴏ ᴄᴏɴ \`${character.name}\``
      },
      {
        quoted: msg
      }
    );

  }

  delete user.waifu.groupLigues[chatId][
    character.key
  ];

  delete user.waifu.ligues[
    character.key
  ];

  if (
    user.waifu.current ===
    character.key
  ){

    user.waifu.current =
      null;

  }

  user.waifu.totalLove =
    Math.max(
      0,
      (user.waifu.totalLove || 0) -
      (Number(ligue.love) || 0)
    );

  const remainingLigues =
    Object.values(
      user.waifu.ligues || {}
    );

  user.waifu.maxLove =
    remainingLigues.length
      ? Math.max(
          ...remainingLigues.map(
            ligueData =>
              Number(
                ligueData?.love || 0
              )
          )
        )
      : 0;

  saveDB();

  return sock.sendMessage(
    jid,
    {
      text:
`♯ ʜᴀs ʀᴏᴍᴘɪᴅᴏ ᴛᴜ ʟɪɢᴜᴇ ᴄᴏɴ \`${character.name}\`
> ⁀➷ ʏᴀ ɴᴏ ᴇsᴛᴀs ʟɪɢᴀᴅᴏ ᴄᴏɴ ᴇʟʟᴀ`
    },
    {
      quoted: msg
    }
  );

}

export async function handleAzzText(
  sock,
  msg,
  jid,
  sender,
  args
){

  if (sender !== OWNER_NUMBER) {
    return sock.sendMessage(jid,{
      text:'Solo el owner principal puede usar este comando.'
    },{ quoted: msg });
  }

  const text =
    args.join(' ').trim();

  if (!text) {
    return sock.sendMessage(jid,{
      text:'Uso: /azztext [texto]'
    },{ quoted: msg });
  }

  db.azzText = text;

  saveDB();

  await sock.sendMessage(jid,{
    text:'✰ Actualizaciones modificadas.'
  },{ quoted: msg });

}

export async function handleAzzDelText(
  sock,
  msg,
  jid,
  sender
){

  if (sender !== OWNER_NUMBER) {
    return sock.sendMessage(jid,{
      text:'Solo el owner principal puede usar este comando.'
    },{ quoted: msg });
  }

  db.azzText = '';

  saveDB();

  await sock.sendMessage(jid,{
    text:'✰ Actualizaciones eliminadas.'
  },{ quoted: msg });

}


function getStaffProfile(staffId) {

  db.staffProfiles ??= {};

  db.staffProfiles[
    staffId
  ] ??= {
    status: 0,
    completedSeries: []
  };

  const profile =
    db.staffProfiles[
      staffId
    ];

  profile.status =
    Number(
      profile.status
    ) || 0;

  if (
    !Array.isArray(
      profile.completedSeries
    )
  ) {

    profile.completedSeries = [];

  }

  return profile;

}

async function resolvePhoneToLid(sock, phone) {
  const normalizedPhone =
    String(phone || '').replace(/\D/g, '');

  if (
    !normalizedPhone ||
    normalizedPhone.length < 7 ||
    normalizedPhone.length > 15
  ) {
    return null;
  }

  const result =
    (await sock.onWhatsApp(
      `${normalizedPhone}@s.whatsapp.net`
    ))?.find(item => item?.exists);

  if (!result?.lid) {
    return null;
  }

  db.missionLidToJid ??= {};
  db.missionLidToJid[result.lid] =
    result.jid ||
    `${normalizedPhone}@s.whatsapp.net`;
  missionLidToJid.set(
    result.lid,
    db.missionLidToJid[result.lid]
  );
  saveDB();

  return {
    phone: normalizedPhone,
    jid: result.jid || `${normalizedPhone}@s.whatsapp.net`,
    lid: result.lid
  };
}

async function handleLid(sock, msg, args) {
  const jid =
    msg.key.remoteJid;
  const phone =
    args[0] || '';

  if (!/^\+?\d{7,15}$/.test(phone)) {
    return sock.sendMessage(
      jid,
      {
        text: '◇ Uso: /lid número telefónico'
      },
      { quoted: msg }
    );
  }

  try {
    const resolved =
      await resolvePhoneToLid(sock, phone);

    if (!resolved) {
      return sock.sendMessage(
        jid,
        {
          text:
            '❌ No pude resolver ese número a un LID. ' +
            'Verifica que la cuenta exista en WhatsApp.'
        },
        { quoted: msg }
      );
    }

    return sock.sendMessage(
      jid,
      {
        text:
          `✓ Número: ${resolved.phone}\n` +
          `JID: ${resolved.jid}\n` +
          `LID: ${resolved.lid}`
      },
      { quoted: msg }
    );
  } catch (error) {
    console.error(
      'ERROR RESOLVIENDO LID:',
      error?.message || error
    );

    return sock.sendMessage(
      jid,
      {
        text: '❌ No se pudo consultar ese número en WhatsApp.'
      },
      { quoted: msg }
    );
  }
}

async function handleDelStatus(
  sock,
  msg,
  args,
  mentioned = [],
  quotedJid = null,
  sender
) {
  const jid = msg.key.remoteJid;

  if (!isMainOwnerId(sender)) {
    return sock.sendMessage(
      jid,
      {
        text: '❌ Solo el owner principal puede usar este comando.'
      },
      { quoted: msg }
    );
  }

  const amount = Number(
    String(args[0] || '').replace(/[^\d]/g, '')
  );

  const inputParts =
    args
      .slice(1)
      .join(' ')
      .split('/')
      .map(part => part.trim())
      .filter(Boolean);

  let target =
    mentioned?.[0] ||
    quotedJid ||
    null;

  const targetInput =
    inputParts[0] || '';
  const numericTarget =
    /^\+?\d{7,15}$/.test(
      targetInput.replace(/\s/g, '')
    );
  const lidTarget =
    /^\d{7,20}@lid$/i.test(targetInput);

  if (
    !target &&
    lidTarget &&
    isSecondaryOwnerId(targetInput)
  ) {
    target = targetInput;
  }

  if (!target && numericTarget) {
    const requestedNumber =
      targetInput.replace(/\D/g, '');
    const ownerIds = [
      ...SECONDARY_OWNERS,
      ...(Array.isArray(db.secondaryOwners)
        ? db.secondaryOwners
        : [])
    ].filter(Boolean);

    const matchingOwner =
      ownerIds.find(owner =>
        normalizeOwnerId(owner)
          .replace(/\D/g, '') === requestedNumber
      ) ||
      Object.entries(db.missionLidToJid || {})
        .find(([lid, linkedJid]) =>
          normalizeOwnerId(linkedJid)
            .replace(/\D/g, '') === requestedNumber &&
          ownerIds.some(owner =>
            normalizeOwnerId(owner) === normalizeOwnerId(lid)
          )
        )?.[0];

    if (matchingOwner) {
      target = matchingOwner;
    } else {
      try {
        const resolved =
          await resolvePhoneToLid(
            sock,
            requestedNumber
          );

        if (
          resolved &&
          ownerIds.some(owner =>
            normalizeOwnerId(owner)
              .replace(/\D/g, '') ===
            normalizeOwnerId(resolved.lid)
              .replace(/\D/g, '')
          ) ||
          resolved &&
          ownerIds.some(owner =>
            normalizeOwnerId(owner)
              .replace(/\D/g, '') ===
            normalizeOwnerId(resolved.jid)
              .replace(/\D/g, '')
          )
        ) {
          target = resolved.lid;
        }
      } catch (error) {
        console.warn(
          '⚠️ No se pudo convertir el número a JID:',
          error?.message || error
        );
      }
    }
  }

  const reasonParts =
    inputParts;
  const reason =
    reasonParts[reasonParts.length - 1] || '';

  if (
    !Number.isSafeInteger(amount) ||
    amount <= 0 ||
    !target ||
    !reason
  ) {
    const targetError =
      numericTarget && !target
        ? '\n◇ Ese número no está registrado como secondary owner o aún no tiene un LID asociado.'
        : lidTarget && !target
          ? '\n◇ Ese LID no pertenece a un secondary owner configurado.'
        : '';

    return sock.sendMessage(
      jid,
      {
        text:
          '◇ Uso:\n/delstatus cantidad / @mención / motivo\n' +
          '/delstatus cantidad / motivo (respondiendo al mensaje del usuario)' +
          targetError
      },
      { quoted: msg }
    );
  }

  const profile =
    getStaffProfile(target);
  const currentStatus =
    Number(profile.status) || 0;

  if (amount > currentStatus) {
    return sock.sendMessage(
      jid,
      {
        text:
          `❌ ${getStaffDisplayName(target, target)} no tiene suficiente status.\n` +
          `Status actual: ${currentStatus.toLocaleString()}`
      },
      {
        quoted: msg,
        mentions: [target]
      }
    );
  }

  profile.status =
    currentStatus - amount;

  saveDB();

  const targetName =
    getStaffDisplayName(target, target);

  if (db.suggestLogs) {
    const secondaryOwners = [
      ...SECONDARY_OWNERS,
      ...(Array.isArray(db.secondaryOwners)
        ? db.secondaryOwners
        : [])
    ].filter((owner, index, owners) =>
      owner &&
      owners.findIndex(candidate =>
        normalizeOwnerId(candidate) === normalizeOwnerId(owner)
      ) === index
    );

    try {
      await sock.sendMessage(
        db.suggestLogs,
        {
          text:
            `⚠️ Se retiraron ${amount.toLocaleString()} status a ` +
            `${targetName}.\n` +
            `Motivo: ${reason}\n` +
            `Status actual: ${profile.status.toLocaleString()}\n\n` +
            secondaryOwners.map(owner =>
              `@${String(owner).split('@')[0]}`
            ).join(' '),
          mentions: [target, ...secondaryOwners]
        }
      );
    } catch (error) {
      console.error(
        '⚠️ No se pudo enviar el aviso de Del Status:',
        error?.message || error
      );
    }
  }

  return sock.sendMessage(
    jid,
    {
      text:
        `✓ Se retiraron ${amount.toLocaleString()} status a ` +
        `${targetName}.\n` +
        `Motivo: ${reason}\n` +
        `Status actual: ${profile.status.toLocaleString()}`,
      mentions: [target]
    },
    { quoted: msg }
  );
}

async function handleAddStatus(
  sock,
  msg,
  args,
  mentioned = [],
  quotedJid = null,
  sender
) {
  const jid = msg.key.remoteJid;

  if (!isMainOwnerId(sender)) {
    return sock.sendMessage(
      jid,
      {
        text: '❌ Solo el owner principal puede usar este comando.'
      },
      { quoted: msg }
    );
  }

  const parts =
    args
      .join(' ')
      .split('/')
      .map(part => part.trim())
      .filter(Boolean);

  let target =
    mentioned?.[0] ||
    quotedJid ||
    null;

  const isAmountPart = value =>
    /^\d+$/.test(String(value || '').trim());

  let amountText = '';
  let targetInput = '';

  if (target || parts.length === 1) {
    amountText =
      parts.find(isAmountPart) ||
      (isAmountPart(parts[0]) ? parts[0] : '');
    targetInput =
      parts.find(part => !isAmountPart(part)) || '';
  } else if (isAmountPart(parts[0])) {
    // También acepta /addstatus cantidad / objetivo.
    amountText = parts[0];
    targetInput = parts[1] || '';
  } else {
    // Formato preferido: /addstatus objetivo / cantidad.
    targetInput = parts[0] || '';
    amountText = parts[1] || '';
  }

  if (!target && /^\d{7,20}@lid$/i.test(targetInput)) {
    target = targetInput;
  }

  if (!target && /^\+?\d{7,15}$/.test(targetInput)) {
    const resolved =
      await resolvePhoneToLid(sock, targetInput);
    target = resolved?.lid || null;
  }

  const amount =
    isAmountPart(amountText)
      ? Number(amountText)
      : NaN;

  if (
    !target ||
    !Number.isSafeInteger(amount) ||
    amount <= 0
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          '◇ Uso:\n' +
          '/addstatus LID / cantidad\n' +
          '/addstatus cantidad (respondiendo al mensaje del usuario)\n' +
          '/addstatus @mención / cantidad'
      },
      { quoted: msg }
    );
  }

  const profile =
    getStaffProfile(target);
  profile.status =
    (Number(profile.status) || 0) + amount;

  saveDB();

  return sock.sendMessage(
    jid,
    {
      text:
        `✓ Se otorgaron ${amount.toLocaleString()} status a ` +
        `${getStaffDisplayName(target, target)}.\n` +
        `Status actual: ${profile.status.toLocaleString()}`,
      mentions: [target]
    },
    { quoted: msg }
  );
}

const INVALID_MEDIA_REPAIR_REWARD = 5_000;

function canRepairCharacterMedia(character, sender) {
  const isCreator = String(character.creator || '') === String(sender || '');
  const isMainOwner =
    isMainOwnerId(sender);
  const isSecondaryOwner =
    isSecondaryOwnerId(sender);
  const isStaff = Array.isArray(db.staff) && db.staff.includes(sender);

  return isCreator || isMainOwner || isSecondaryOwner || isStaff;
}

function rewardInvalidMediaRepair(character, repairer) {
  // Una recompensa por personaje evita cobrar repetidamente por el mismo arreglo.
  if (character.invalidMediaRepairRewardedAt) return null;

  const profile = getStaffProfile(repairer);
  profile.status = (Number(profile.status) || 0) + INVALID_MEDIA_REPAIR_REWARD;
  character.invalidMediaRepairRewardedAt = Date.now();
  character.invalidMediaRepairRewardedBy = repairer;

  saveDB();
  saveCharacters();

  return profile.status;
}

async function notifyEvents(sock, text, mentions = []) {
  if (!db.eventsGroup) return;
  await sock.sendMessage(db.eventsGroup, {
    text,
    mentions: mentions.filter(Boolean)
  });
}

async function handleEvents(sock, msg, jid, sender, args) {
  if (!isMainOwnerId(sender)) {
    return sock.sendMessage(jid, {
      text: '❌ Solo el owner principal puede usar este comando.'
    }, { quoted: msg });
  }

  const action = String(args[0] || '').toLowerCase();
  if (!['on', 'off'].includes(action)) {
    return sock.sendMessage(jid, {
      text: '◇ Uso: /events on o /events off'
    }, { quoted: msg });
  }

  if (action === 'on') {
    if (!jid.endsWith('@g.us')) {
      return sock.sendMessage(jid, {
        text: '◇ Debes activar /events on dentro de un grupo.'
      }, { quoted: msg });
    }
    db.eventsGroup = jid;
    saveDB();
    return sock.sendMessage(jid, {
      text: '✓ Eventos activados en este grupo.'
    }, { quoted: msg });
  }

  db.eventsGroup = null;
  saveDB();
  return sock.sendMessage(jid, {
    text: '✓ Eventos desactivados.'
  }, { quoted: msg });
}

function getStaffRank(status) {

  const ranks = db.staffRanks || [

    {
  name:
    "Staff Maestro",
  min: 6000
},

{
  name:
    "Staff Avanzado",
  min: 10000
},

{
  name:
    "Staff Superior",
  min: 16000
},

{
  name:
    "Staff Profesional",
  min: 25000
},

{
  name:
    "Staff Experto Plus",
  min: 40000
},

{
  name:
    "Staff Veterano",
  min: 60000
},

{
  name:
    "Staff Élite",
  min: 90000
},

{
  name:
    "Staff Diamante",
  min: 130000
},

{
  name:
    "Staff Legendario",
  min: 180000
},

{
  name:
    "Staff Supremo",
  min: 250000
},

{
  name:
    "Staff Campeón",
  min: 350000
},

{
  name:
    "Staff Máximo",
  min: 500000
}

  ].map(rank => ({
    name: String(rank.name),
    min: Number(rank.min)
  })).sort((a, b) => a.min - b.min);

  let current =
    ranks[0];

  for (
    const rank of ranks
  ) {

    if (
      status >=
      rank.min
    ) {

      current = rank;

    }

  }

  return current;

}

function getStaffRanks() {
  db.staffRanks ??= [
    { name: "Staff Maestro", min: 6000 },
    { name: "Staff Avanzado", min: 10000 },
    { name: "Staff Superior", min: 16000 },
    { name: "Staff Profesional", min: 25000 },
    { name: "Staff Experto Plus", min: 40000 },
    { name: "Staff Veterano", min: 60000 },
    { name: "Staff Élite", min: 90000 },
    { name: "Staff Diamante", min: 130000 },
    { name: "Staff Legendario", min: 180000 },
    { name: "Staff Supremo", min: 250000 },
    { name: "Staff Campeón", min: 350000 },
    { name: "Staff Máximo", min: 500000 }
  ];

  return db.staffRanks
    .map(rank => ({
      name: String(rank.name),
      min: Number(rank.min)
    }))
    .filter(rank => rank.name && Number.isFinite(rank.min) && rank.min >= 0)
    .sort((a, b) => a.min - b.min);
}

async function handleStaffRanks(sock, msg) {
  const ranks = getStaffRanks();
  const text = ranks.length
    ? "☆ RANGOS DEL STAFF\n\n" +
      ranks.map((rank, index) =>
        `${index + 1}. *${rank.name}*\n> Necesitas: \`${rank.min.toLocaleString()}\` status`
      ).join("\n\n")
    : "◇ No hay rangos configurados.";

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}

async function handleTopStatus(sock, msg, args = []) {
  const requestedPage = Number.parseInt(args[0] || "1", 10);
  const page = Number.isInteger(requestedPage) && requestedPage > 0
    ? requestedPage
    : 1;
  const perPage = 10;

  const ranking = Object.entries(db.staffProfiles || {})
    .map(([id, profile]) => ({
      id,
      name:
        db.users?.[id]?.name ||
        id.split("@")[0] ||
        "Usuario",
      status: Number(profile?.status) || 0
    }))
    .filter(staff => staff.status > 0)
    .sort((a, b) => {
      if (b.status !== a.status) {
        return b.status - a.status;
      }

      return a.name.localeCompare(b.name);
    });

  const totalPages = Math.max(1, Math.ceil(ranking.length / perPage));

  if (!ranking.length) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: '♧ No hay usuarios con status registrado ♧'
      },
      { quoted: msg }
    );
  }

  if (page > totalPages) {
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          ` Top de usuarios con más status \n\n` +
          `✧ La página *${page}* no existe.\n` +
          `✧ Hay *${totalPages}* páginas disponibles.`
      },
      { quoted: msg }
    );
    return;
  }

  const start = (page - 1) * perPage;
  const visible = ranking.slice(start, start + perPage);

  let text =
    ` Top de usuarios con más status \n\n`;

  for (let i = 0; i < visible.length; i++) {
    const staff = visible[i];
    const position = start + i + 1;
    const crown = position === 1 ? '♔ ' : '';
    const rank = getStaffRank(staff.status);

    text +=
      `✧ ${crown}${position} » *${staff.name}* » \`${staff.status.toLocaleString()}\`\n` +
      `   > Rango: ${rank.name}`;

    if (i < visible.length - 1) {
      text += "\n\n";
    }
  }

  text +=
    `\n\n✧ Página *${page}* de *${totalPages}*`;

  if (page < totalPages) {
    text +=
      `\n✧ Para ver la siguiente página usa: */topstatus ${page + 1}*`;
  }

  if (page > 1) {
    text +=
      `\n✧ Página anterior: */topstatus ${page - 1}*`;
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}

function getStaffRanking() {

  db.staffStats ??= {};

  const ranking = [];

  const creators =
    new Set(
      charactersCache
        .filter(
          char =>
            char.creator
        )
        .map(
          char =>
            char.creator
        )
    );

  for (
    const creator
    of creators
  ) {

    const total =
      charactersCache
        .filter(
          char =>
            char.creator ===
            creator
        )
        .length;

    const fans =
      Number(
        db.staffStats?.[
          creator
        ]?.fans
      ) || 0;

    ranking.push({

      id:
        creator,

      total,

      fans

    });

  }

  ranking.sort(
    (a, b) => {

      if (
        b.fans !==
        a.fans
      ) {

        return (
          b.fans -
          a.fans
        );

      }

      return (
        b.total -
        a.total
      );

    }
  );

  return ranking;

}

export async function handleStaffInfo(
  sock,
  msg,
  args,
  sender
) {

  const target =
    sender;

  const profile =
    getStaffProfile(
      target
    );

  const ranking =
    getStaffRanking();

  const position =
    ranking.findIndex(
      staff =>
        staff.id ===
        target
    ) + 1;

  // -----------------------------------------------
  // PERSONAJES CREADOS
  // -----------------------------------------------

  const totalCharacters =
    charactersCache
      .filter(
        char =>
          char.creator ===
          target
      )
      .length;

  // -----------------------------------------------
  // FANS
  // -----------------------------------------------

  const fans =
    Number(
      db.staffStats?.[
        target
      ]?.fans
    ) || 0;

  // -----------------------------------------------
  // RANGO
  // -----------------------------------------------

  const rank =
    getStaffRank(
      profile.status
    );

  // -----------------------------------------------
  // NOMBRE
  // -----------------------------------------------

  const name =
    db.users?.[
      target
    ]?.name ||
    target
      .split("@")[0];

  // -----------------------------------------------
  // DUEï¿½'O DE SERIE
  //
  // Una serie cuenta como "Dueño de serie"
  // cuando todos sus personajes pertenecen
  // al mismo staff.
  // -----------------------------------------------

  let ownedSeries = 0;

  try {

    for (
      const serie of seriesCache.values()
    ) {

      if (
        !serie ||
        !serie.characters ||
        typeof serie.characters[Symbol.iterator] !==
          "function"
      ) {
        continue;
      }

      const characterKeys =
        Array.from(
          serie.characters
        );

      if (
        !characterKeys.length
      ) {
        continue;
      }

      const characters =
        characterKeys
          .map(
            key =>
              charactersCache.find(
                char =>
                  char.key === key ||
                  char.id === key ||
                  char.name === key
              )
          )
          .filter(Boolean);

      if (
        !characters.length
      ) {
        continue;
      }

      const allOwned =
        characters.every(
          char =>
            char.creator ===
            target
        );

      if (
        allOwned
      ) {
        ownedSeries++;
      }

    }

  } catch (error) {

    console.error(
      "⚠️ Error calculando Dueño de serie:",
      error
    );

  }

  // -----------------------------------------------
  // MISIONES COMPLETADAS
  // -----------------------------------------------

  let completedMissions = 0;

  try {

    const store =
      getMissionStore();

    const missions =
      Array.isArray(
        store?.list
      )
        ? store.list
        : [];

    const targetId =
      String(
        target || ""
      )
        .replace(/\D/g, "");

    completedMissions =
      missions.filter(
        mission => {

          if (
            mission?.status !==
            "completed"
          ) {
            return false;
          }

          const missionStaff =
            String(
              mission.staff || ""
            )
              .replace(/\D/g, "");

          return (
            missionStaff ===
            targetId
          );

        }
      ).length;

  } catch (error) {

    console.error(
      "⚠️ Error calculando misiones:",
      error
    );

  }

  // -----------------------------------------------
  // TEXTO
  // -----------------------------------------------

  const text = [

    "♤ STAFF INFO",

    "",

    "♡ Staff » " +
    name,

    "",

    "▪︎ *Personajes totales* » \`" +
    totalCharacters +
    "\`",

    "☆ *Series completadas* » \`" +
    profile
      .completedSeries
      .length +
    "\`",

    "♠︎ *Dueño de serie* » \`" +
    ownedSeries +
    "\`",

    "♡ *Fans totales* » \`" +
    fans
      .toLocaleString() +
    "\`",

    "",

    "• *Status* » \`" +
    profile
      .status
      .toLocaleString() +
    "\`",

    "♛ *Rango* » \`" +
    rank.name +
    "\`",

    "♤ *Puesto* » \`" +
    (
      position ||
      "Sin puesto"
    ) +
    "\`",

    "¤ *Misiones completadas* » \`" +
    completedMissions +
    "\`",

    "",

    "> Usa /rangs para ver los rangos."

  ].join(
    "\n"
  );

  // -----------------------------------------------
  // FOTO DE PERFIL
  // -----------------------------------------------

  let profilePictureUrl = null;

  try {

    profilePictureUrl =
      await sock.profilePictureUrl(
        target,
        "image"
      );

  } catch (error) {

    profilePictureUrl = null;

  }

  // -----------------------------------------------
  // ENVIAR FOTO + TEXTO
  // -----------------------------------------------

  if (
    profilePictureUrl
  ) {

    try {

      await sock.sendMessage(
        msg.key.remoteJid,
        {
          image: {
            url:
              profilePictureUrl
          },
          caption:
            text
        },
        {
          quoted:
            msg
        }
      );

      return;

    } catch (error) {

      console.error(
        "⚠️ No se pudo enviar la foto de perfil:",
        error
      );

    }

  }

  // -----------------------------------------------
  // FALLBACK: SOLO TEXTO
  // -----------------------------------------------

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text
    },
    {
      quoted:
        msg
    }
  );

}

export async function handleSerieC(
  sock,
  msg,
  args,
  sender
) {

  const isStaff =
    isMainOwnerId(sender) ||
    isSecondaryOwnerId(sender);

  if (
    !isStaff
  ) {

    return;

  }

  const anime =
    args
      .join(
        " "
      )
      .trim();

  if (
    !anime
  ) {

    return sock.sendMessage(

      msg.key.remoteJid,

      {

        text:

          "♤ Uso\n\n" +

          "/seriec Nombre de la serie"

      },

      {

        quoted:
          msg

      }

    );

  }

  const characters =

    charactersCache
      .filter(

        char =>

          String(

            char.anime ||

            ""

          )

          .toLowerCase()

          .trim()

          ===

          anime

          .toLowerCase()

          .trim()

      );

  if (
    !characters.length
  ) {

    return sock.sendMessage(

      msg.key.remoteJid,

      {

        text:

          "♤ Serie no encontrada\n\n" +

          "▪︎ No hay personajes registrados de:\n\n" +

          anime

      },

      {

        quoted:
          msg

      }

    );

  }

  // SERIEC_SERIESKEY_FIX_V2
const seriesKey =

    anime

      .toLowerCase()

      .normalize(
        "NFD"
      )

      .replace(

        /[\u0300-\u036f]/g,

        ""

      )

      .trim();

  const cachedInfo =
    db.seriesInfoCache?.[
      seriesKey
    ];

  if (
    !cachedInfo ||
    !Number.isInteger(Number(cachedInfo.total)) ||
    Number(cachedInfo.total) < 1
  ) {
    db.pendingSeriesChecks ??= {};
    const verification = await sock.sendMessage(
      msg.key.remoteJid,
      {
        text: `#ainfo ${anime}`
      },
      { quoted: msg }
    );

    if (verification?.key?.id) {
      db.pendingSeriesChecks[verification.key.id] = {
        seriesKey,
        anime,
        jid: msg.key.remoteJid,
        sender,
        createdAt: Date.now()
      };
      saveDB();
    }

    return;
  }

 const uniqueCharacters = new Map();

const registeredTotal = (() => {
  for (const char of characters) {
    const uniqueKey =
      char.key ||
      char.name?.toLowerCase();

    if (!uniqueCharacters.has(uniqueKey)) {
      uniqueCharacters.set(uniqueKey, char);
    }
  }

  return uniqueCharacters.size;
})();

const expectedTotal = Number(cachedInfo.total);

  if (
    !Number.isInteger(
      expectedTotal
    ) ||
    expectedTotal < 1
  ) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          " El total guardado de esta serie no es válido."
      },
      {
        quoted:
          msg
        }
    );

  }

  if (
    registeredTotal <
    expectedTotal
  ) {

    const missing =
      expectedTotal -
      registeredTotal;

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          "❌ SERIE INCOMPLETA\n\n" +
          "♤ Serie » " +
          anime +
          "\n\n" +
          "▪︎ Registrados » " +
          registeredTotal +
          "\n" +
          "▪︎ Total » " +
          expectedTotal +
          "\n" +
          "▪︎ Faltan » " +
          missing +
          "\n\n" +
          " La serie todavï¿½a no puede firmarse."
      },
      {
        quoted:
          msg
      }
    );

  }

  if (
    registeredTotal >
    expectedTotal
  ) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          "⚠️ DATOS NO COINCIDEN\n\n" +
          "▪︎ Registrados » " +
          registeredTotal +
          "\n" +
          "▪︎ Total externo » " +
          expectedTotal +
          "\n\n" +
          "♧ La firma fue bloqueada para evitar errores."
      },
      {
        quoted:
          msg
      }
    );

  }

  const creators = [
    ...new Set(
      characters.map(
        char => char.creator
      )
      .filter(Boolean)
    )
  ];

  if (
    creators.length !== 1
  ) {

    const creatorsDisplay =
      creators
        .map(
          creator =>
            db.users?.[creator]?.name ||
            creator?.split("@")[0] ||
            "Desconocido"
        )
        .filter(
          (name, index, array) =>
            array.indexOf(name) === index
        );

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          "》 La serie tiene creadores distintos\n" +
          creatorsDisplay
            .map(name => `✿ ${name}`)
            .join("\n") +
          "\n> Consulta con la owner May."
      },
      {
        quoted:
          msg
      }
    );

  }

  const creator =
    creators[0];

  const profile =
    getStaffProfile(
      creator
    );



  if (

    profile

      .completedSeries

      .includes(

        seriesKey

      )

  ) {

    return sock.sendMessage(

      msg.key.remoteJid,

      {

        text:

          "♤ Esta serie ya fue completada.\n\n" +

          "▪︎ No se puede obtener Status dos veces."

      },

      {

        quoted:
          msg

      }

    );

  }

  const reward =
    registeredTotal * 1000;

  profile.status +=

    reward;

  profile

    .completedSeries

    .push(

      seriesKey

    );

  saveDB();

  const rank =

    getStaffRank(

      profile.status

    );

  const text = [

    "☆ SERIE COMPLETADA",

    "",

    "♤ Serie » " +
    anime,

    "▪︎ Personajes verificados » " +
    registeredTotal +
    "/" +
    expectedTotal,

    "♡ Recompensa » +" +

    reward +

    " Status",

    "• Status total » " +

    profile.status,

    "◇ Rango actual » " +

    rank.name,

    "",

    "♧ Serie firmada correctamente."

  ].join(
    "\n"
  );

  await sock.sendMessage(

    msg.key.remoteJid,

    {

      text

    },

    {

      quoted:
        msg

    }

  );

}


export async function handleTopStaffGacha(
  sock,
  msg,
  args
){

  db.staffStats ??= {};

  const page =
    Math.max(
      1,
      Number(args[0]) || 1
    );

  const perPage = 10;

  const staffMap = new Map();

  for (const char of charactersCache) {

    if (!char.creator)
      continue;

    if (!staffMap.has(char.creator)) {

      staffMap.set(
        char.creator,
        {
          id: char.creator,
          name:
            db.users?.[char.creator]?.name ||
            char.creator.split('@')[0],
          fans:
            db.staffStats?.[
              char.creator
            ]?.fans || 0,
          total: 0
        }
      );

    }

    staffMap.get(
      char.creator
    ).total++;

  }

  const ranking =
    [...staffMap.values()]
      .sort((a,b)=>{

        if (b.fans !== a.fans)
          return b.fans - a.fans;

        return b.total - a.total;

      });

  if (!ranking.length){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'No hay estadísticas.'
      },
      {
        quoted: msg
      }
    );

  }

  const totalPages =
    Math.max(
      1,
      Math.ceil(
        ranking.length / perPage
      )
    );

  const start =
    (page-1) * perPage;

  const end =
    start + perPage;

  let text =
`Top staff con más Reclamaciones\n\n`;

  let pos = start + 1;

  for (
    const staff of
    ranking.slice(start,end)
  ){

    text +=
`☆ ${pos} » ${staff.name}
    ☆ Fans \`${Number(
      staff.fans
    ).toLocaleString()}\` ➭ PJ totales \`${Number(
      staff.total
    ).toLocaleString()}\`\n\n`;

    pos++;

  }

  text +=
` Página \`${page}/${totalPages}\`  usa \`/topstaffgacha ${Math.min(page+1,totalPages)}\` para avanzar`;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text
    },
    {
      quoted: msg
    }
  );

}

export async function handleTopCoinsChar(
  sock,
  msg,
  args
){

  const page =
    parseInt(args[0]) || 1;

  const perPage = 10;

  const chars =
    [...charactersCache]
    .filter(c =>
      Number(c.coinGen || 0) > 0
    )
    .sort(
      (a,b) =>
        Number(b.coinGen || 0)
        -
        Number(a.coinGen || 0)
    );

  const pages =
    Math.max(
      1,
      Math.ceil(
        chars.length / perPage
      )
    );

  const slice =
    chars.slice(
      (page - 1) * perPage,
      page * perPage
    );

  let text =
` Personajes con más dinero pasivo

`;

  let pos =
    (page - 1) * perPage + 1;

  for (const char of slice) {

    text +=
`✰ ${pos} » *${char.name}*
→ coins: *${Number(
  char.coinGen || 0
).toLocaleString()}/h*

`;

    pos++;

  }

  text +=
`> ï¿½ Página *${page}* de *${pages}*`;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );

}

export async function handleSetClaimMsg(sock, msg, args, jid, sender) {

  const text = args.join(' ').trim();

  if (!text) {
    return sock.sendMessage(jid,{
      text:
`《✧》Debes incluir las variables *$user* y *$character* en el mensaje.

> Ejemplos de mensajes:
> *#setclaimmsg $user ha reclamado el personaje $character!*
> *#setclaimmsg $character ha sido reclamado por $user*
> *#setclaimmsg Ahora $user es el dueño de $character!*`
    },{ quoted: msg });
  }

  if (
    !text.includes('$user') ||
    !text.includes('$character')
  ) {

    return sock.sendMessage(jid,{
      text:
`《✧》Debes incluir las variables *$user* y *$character* en el mensaje.`
    },{ quoted: msg });
  }

if (/\d/.test(text)) {
  return sock.sendMessage(jid,{
    text:'《✧》No puedes incluir números en el mensaje de reclamación.'
  },{ quoted: msg });
}

  if (text.length > 70) {
    return sock.sendMessage(jid,{
      text:'《✧》El mensaje no puede superar los *70 caracteres*.'
    },{ quoted: msg });
  }

 const user = initUser(sender);

try {

  collectPassiveCoins(
    jid,
    sender
  );

} catch (error) {

  console.error(
    '[ERROR PASSIVE COINS]',
    error?.stack || error?.message || error
  );

}

  user.claimMsg = text;

  saveDB();

  await sock.sendMessage(jid,{
    text:'✰ Mensaje de reclamación modificado.'
  },{ quoted: msg });
}

export async function handleDelClaimMsg(sock, msg, jid, sender) {

  const user = initUser(sender);

  user.claimMsg = null;

  saveDB();

  await sock.sendMessage(jid,{
    text:'✰ Mensaje de reclamación restablecido.'
  },{ quoted: msg });
}

function getManualTagEntryForCharacter(tag) {
  const value = String(tag || '').trim();
  if (!value) return null;

  const direct = getManualTag(value);
  if (direct) {
    return {
      key: normalizeManualTag(value),
      entry: direct
    };
  }

  const match = value.match(/^(.+)_\(([^()]*)\)$/);
  if (!match) return null;

  const entry = getManualTag(match[1]);
  if (
    !entry ||
    normalizeManualTag(entry.source) !== normalizeManualTag(match[2])
  ) {
    return null;
  }

  return {
    key: normalizeManualTag(match[1]),
    entry
  };
}

async function getManualCharacterImage(tag) {
  const manual = getManualTagEntryForCharacter(tag);
  if (!manual || !Array.isArray(manual.entry.images)) return null;

  const imageDirectory = path.join(
    process.cwd(),
    'manual-tags',
    'images',
    manual.key
  );
  const available = manual.entry.images.filter(image =>
    image?.file &&
    path.basename(image.file) === image.file &&
    fs.existsSync(path.join(imageDirectory, image.file))
  );
  if (!available.length) return null;

  const selected = available[Math.floor(Math.random() * available.length)];
  const imagePath = path.join(imageDirectory, selected.file);
  try {
    const image = await fs.promises.readFile(imagePath);
    if (!image.length) return null;
    const extension = path.extname(selected.file).toLowerCase();
    const mimetype = extension === '.png'
      ? 'image/png'
      : extension === '.webp'
        ? 'image/webp'
        : extension === '.gif'
          ? 'image/gif'
          : 'image/jpeg';
    return { image, mimetype };
  } catch (error) {
    console.error('[MANUAL-TAGS] No se pudo leer imagen del tag:', error?.message || error);
    return null;
  }
}

async function mioTagHasOnlineImage(tag) {
  const query = String(tag || '').trim();
  if (!query) return false;

  try {
    const gelbooruCandidates =
      await getGelbooruApiImageCandidates(query);

    for (const imageUrl of (gelbooruCandidates || []).slice(0, 5)) {
      const image = await downloadGelbooruImage(imageUrl);
      if (image?.buffer?.length) return true;
    }

    const danbooruImageUrl =
      await getDanbooruImage(query);
    if (!danbooruImageUrl) return false;

    const image =
      await downloadDanbooruImage(danbooruImageUrl);
    return Boolean(image?.buffer?.length);
  } catch (error) {
    console.error('[PENDIENTES2] No se pudo comprobar el tag Mio:', error?.message || error);
    return false;
  }
}

async function getCharacterMedia(character){
  const manualImage = await getManualCharacterImage(character.tag);
  if (manualImage) return manualImage;

  const localImages =
    getCharacterImages(character.key)
      .map(imageName => path.join(GACHA_IMAGES, imageName))
      .filter(imagePath => {
        try {
          return fs.existsSync(imagePath);
        } catch {
          return false;
        }
      });

  const hasLocal =
    localImages.length > 0;

  const hasTag =
    !!(
      character.tag &&
      character.tag.trim()
    );

  if (hasLocal){
    const img =
      localImages[
        Math.floor(
          Math.random() *
          localImages.length
        )
      ];

    const buffer =
      imageCache.get(img) ||
      fs.readFileSync(img);

    imageCache.set(img, buffer);

    return {
    image: buffer
    };
  }

  if (hasTag){

    const url =
      await getGelbooruImage(
        character.tag
      );

    if (url){
      const downloaded =
        await downloadImage(url);

      if (downloaded) {
        return {
          image: downloaded.buffer,
          mimetype: downloaded.mimetype
        };
      }
    }
  }

  return null;
}


export async function handleSetv(sock, msg, args, sender) {
  const permitido =
    isMainOwnerId(sender) ||
    isSecondaryOwnerId(sender);

  if (!permitido) return;

  const raw = args.join(" ").trim();
  const partes = raw.split("/").map(x => x.trim());

  if (partes.length < 3) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          "◇ Uso:\n\n" +
          "/setv 1 en 382023 / Nombre del personaje / Nombre de la serie\n\n" +
          "◇ Ejemplo:\n\n" +
          "/setv 1 en 382023 / Miko (Dandadan) / Dandadan"
      },
      { quoted: msg }
    );
  }

  const oddsPart = partes[0];
  const characterName = partes[1];
  const seriesName = partes.slice(2).join(" / ").trim();

  const match = oddsPart.match(/^1\s+(?:en|in)\s+([0-9]+(?:[,.][0-9]{3})*)$/i);

  if (!match) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          " Formato inválido.\n\n" +
          "Usa:\n\n" +
          "/setv 1 en 382023 / Nombre / Serie"
      },
      { quoted: msg }
    );
  }

  const odds = Number(
    match[1].replace(/[.,]/g, "")
  );

  if (!Number.isSafeInteger(odds) || odds < 1) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          "◇ El valor de 1 en debe ser un número entero mayor que 0."
      },
      { quoted: msg }
    );
  }

  if (!characterName || !seriesName) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: "◇ Debes indicar el personaje y la serie."
      },
      { quoted: msg }
    );
  }

  if (!charactersCache.length) {
    loadCharactersCache();
    loadSeries();
  }

  const normalizar = value =>
    String(value || "")
      .normalize("NFD")
      .replace(/[\\u0300-\\u036f]/g, "")
      .toLowerCase()
      .trim();

  const nombreBuscado = normalizar(characterName);
  const serieBuscada = normalizar(seriesName);

  let encontrados = charactersCache.filter(char => {
    const nombre = normalizar(char.name);
    const anime = normalizar(char.anime);

    return nombre === nombreBuscado && anime === serieBuscada;
  });

  if (!encontrados.length) {
    encontrados = charactersCache.filter(char => {
      const nombre = normalizar(char.name);
      const anime = normalizar(char.anime);

      return (
        (nombre.includes(nombreBuscado) ||
          nombreBuscado.includes(nombre)) &&
        (anime === serieBuscada ||
          anime.includes(serieBuscada) ||
          serieBuscada.includes(anime))
      );
    });
  }

  if (!encontrados.length) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          "◇ Personaje no encontrado.\n\n" +
          "◇ Personaje » " + characterName + "\n" +
          "◇ Serie » " + seriesName
      },
      { quoted: msg }
    );
  }

    if (encontrados.length > 1) {
    const activos = encontrados.filter(char =>
      Number(char.coinGen || 0) > 0
    );

    if (activos.length === 1) {
      encontrados = activos;
    } else {
      return sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
            "◇ Se encontraron varios personajes compatibles.\n\n" +
            "Usa el nombre exacto del personaje y de la serie.\n\n" +
            "◇ Personaje » " + characterName + "\n" +
            "◇ Serie » " + seriesName + "\n\n" +
            "◇ No se realiz¿ ningún cambio."
        },
        { quoted: msg }
      );
    }
  }

  const character = encontrados[0];

  character.displayOdds = odds;

  saveCharacters();

  const oddsFormatted =
    odds.toLocaleString("en-US");

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
        "◇ Probabilidad visual actualizada.\n\n" +
        "◇ Nombre » " + character.name + "\n" +
        "☆ Anime » " + character.anime + "\n\n" +
        "`1` *en* `" + oddsFormatted + "`"
    },
    { quoted: msg }
  );
}
// ==== RW: diseno estilizado compartido por /rw y /rwp ====
const RW_STYLE_MAP = {
  a: "\u1972", e: "\u1971", i: "\u03B9", l: "\u1963", n: "\u1952", u: "\u1959", c: "\u1974", p: "\u03C1",
  "\u00E1": "\u1972\u0301", "\u00E9": "\u1971\u0301", "\u00ED": "\u03B9\u0301", "\u00FA": "\u1959\u0301"
};

function estilizarRW(texto) {
  return Array.from(String(texto ?? ""))
    .map(ch => RW_STYLE_MAP[ch] ?? ch)
    .join("");
}

function buildRwCaption(character, estadoTxt, creatorName) {
  const displayOdds = Number(character.displayOdds);
  const displayOddsText =
    Number.isSafeInteger(displayOdds) && displayOdds > 0
      ? "\x601\x60 *en* \x60" + displayOdds.toLocaleString("en-US") + "\x60"
      : "";

  const valor =
    typeof character.value === "number"
      ? character.value.toLocaleString()
      : String(character.value ?? 0);

  return (
    "\u25C7 *Nombr\u1971* \u00BB \x60" + estilizarRW(character.name) + "\x60\n" +
    "\u2606 *A\u1952\u03B9m\u1971* \u00BB \x60" + estilizarRW(character.anime) + "\x60\n" +
    "\u25A0 *G\u1971\u0301\u1952\u1971ro* \u00BB \x60" + estilizarRW(character.gender || "Desconocido") + "\x60\n" +
    "\u2661 *Est\u1972do* \u00BB \x60" + estilizarRW(estadoTxt) + "\x60\n\n" +
    "\u2661 *R\u1972r\u1971z\u1972* \u00BB \x60" + estilizarRW(character.rarity || "Comun") + "\x60\n" +
    "\u2606 *V\u1972\u1963or* \u00BB \x60" + valor + "\x60\n" +
    "\u2667 *Ch\u1972\u1952\u1974\u1971* \u00BB \x60" + (character.chance || "100%") + "\x60\n\n" +
    "\u2605 *Cr\u1971\u1972dor* \u00BB \x60" + creatorName + "\x60\n\n" +
    displayOddsText
  );
}

export async function handleRw(sock, msg, groupId, sender) {
  const user =
    initUser(sender);

  const groupCooldowns =
    getGroupCooldowns(
      groupId,
      sender
    );

  groupCooldowns.rw ??= 0;

  const BASE_CD =
    getPremiumCooldown(user);

  const economy =
    getGroupEconomy(
      groupId,
      sender
    );

  const reduction =
    Number(user.cooldownReduction || 0);

  const finalCD =
    Math.max(
      30000,
      BASE_CD - reduction
    );
  const now = Date.now();

  if (now - groupCooldowns.rw < finalCD) {
    const w = Math.ceil(
      (finalCD - (now - groupCooldowns.rw)) / 1000
    );

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`⧗ ᴇsᴘᴇʀᴀ \`${Math.floor(w / 60)} ᴍɪɴᴜᴛᴏs ʏ ${w % 60} sᴇɢᴜɴᴅᴏs\` ᴘᴀʀᴀ ᴜsᴀʀ \`ʀᴡ\`.`
      },
      { quoted: msg }
    );
  }

  try {
    if (!charactersCache.length) { loadCharactersCache(); loadSeries(); }
    if (!charactersCache.length) return sock.sendMessage(msg.key.remoteJid, { text: '● No hay personajes en la base local.' }, { quoted: msg });

    const user =
initUser(sender);

const character = getRandomCharacter(sender, groupId);

const imageData =
  await getCharacterMedia(character);

if (!imageData) {
  await notifyEvents(
    sock,
    `❌ Error de imagen\n\nPersonaje: ${character.name}\nID: ${character.id}\nSolicitado por: @${String(sender).split('@')[0]}`,
    [sender]
  );
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`Error > Personaje \`ID ${character.id}\`

Si el problema persiste
avísanos con */report*`
    },
    { quoted: msg }
  );
}

    const claimEntry = character.claimedBy?.[groupId];
    const alreadyClaimed = claimEntry ? claimEntry.user : null;
    let estado = 'Libre';

if (alreadyClaimed) {

  const ownerName =
    db.users?.[alreadyClaimed]?.name ||
    alreadyClaimed.split('@')[0];

  estado =
    `Reclamado por ${ownerName}`;
}
    groupCooldowns.rw = now;
    economy.lastClaim = {
      id: character.id,
      key: character.key,
      name: character.name,
      anime: character.anime,
      gender: character.gender,
      value: character.value,
      rarity: character.rarity,
      claimed: !!alreadyClaimed,
      claimedBy: alreadyClaimed,
      timestamp: now,
      invoker: sender
    };
    saveDB();

    const creatorName =
  getCharacterCreatorName(character);

const estadoTxt =
  alreadyClaimed
    ? (
        db.users?.[alreadyClaimed]?.name ||
        alreadyClaimed.split('@')[0]
      )
    : 'Libre';

const displayOdds =
  Number(character.displayOdds);

const displayOddsText =
  Number.isSafeInteger(displayOdds) && displayOdds > 0
    ? "`1` *en* `" + displayOdds.toLocaleString("en-US") + "`"
    : "";

const cap = buildRwCaption(character, estadoTxt, creatorName);

    const rwResult =
      await sock.sendMessage(
  msg.key.remoteJid,
  {
    ...imageData,
    caption: cap
  },
  {
    quoted: msg
  }
);
    rememberRwResultMessage(
      msg.key.remoteJid,
      rwResult
    );

const audio =
  db.characterAudios?.[
    character.key
  ];

if (
  audio &&
  fs.existsSync(audio)
){
  const notice =
    await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
'✨ Conseguiste un personaje único e inolvidable.'
    },
    { quoted: msg }
  );
  rememberRwResultMessage(
    msg.key.remoteJid,
    notice
  );

  const audioMessage =
    await sock.sendMessage(
    msg.key.remoteJid,
    {
      audio:
        fs.readFileSync(audio),
      mimetype:'audio/mpeg',
      ptt:false
    },
    { quoted: msg }
  );
  rememberRwResultMessage(
    msg.key.remoteJid,
    audioMessage
  );
}

  } catch (e) {
    console.error(e.stack);
    await sock.sendMessage(msg.key.remoteJid, { text: '● Error al buscar personaje.' }, { quoted: msg });
  }
}

function rememberRwResultMessage(jid, result) {
  const messageId = result?.key?.id;
  if (!jid || !messageId) return;

  const key = `${jid}:${messageId}`;
  rwResultMessageIds.add(key);

  if (rwResultMessageIds.size > 5000) {
    rwResultMessageIds.delete(
      rwResultMessageIds.values().next().value
    );
  }
}

async function handleDel(sock, msg) {
  const jid = msg?.key?.remoteJid || "";
  const contextInfo =
    msg?.message?.extendedTextMessage?.contextInfo;
  const quotedId = contextInfo?.stanzaId;

  if (!jid.endsWith("@g.us")) {
    return sock.sendMessage(
      jid,
      { text: "❌ Este comando solo puede usarse en grupos." },
      { quoted: msg }
    );
  }

  if (!quotedId || !contextInfo?.quotedMessage) {
    return sock.sendMessage(
      jid,
      { text: "◇ Responde al mensaje que quieres borrar con /del." },
      { quoted: msg }
    );
  }

  if (rwResultMessageIds.has(`${jid}:${quotedId}`)) {
    return sock.sendMessage(
      jid,
      { text: "❌ No se puede borrar el resultado del comando /rw con /del." },
      { quoted: msg }
    );
  }

  const normalizeJid = value =>
    String(value || "")
      .trim()
      .replace(/:.*(?=@)/, "")
      .replace(/@c\.us$/i, "@s.whatsapp.net")
      .toLowerCase();
  const normalizeNumber = value =>
    normalizeJid(value)
      .replace(/@.*$/, "")
      .replace(/\D/g, "");
  const resolveLid = value => {
    const normalized = normalizeJid(value);
    if (!normalized.endsWith("@lid")) return normalized;
    return normalizeJid(
      db.missionLidToJid?.[normalized] ||
      missionLidToJid.get(normalized) ||
      normalized
    );
  };
  const sameUser = (a, b) => {
    const first = resolveLid(a);
    const second = resolveLid(b);
    if (!first || !second) return false;
    if (first === second) return true;
    const firstNumber = normalizeNumber(first);
    const secondNumber = normalizeNumber(second);
    return !!firstNumber && firstNumber === secondNumber;
  };

  const quotedParticipant =
    contextInfo.participant ||
    contextInfo.remoteJid ||
    "";
  const botJid = sock?.user?.id || "";
  const isBotMessage =
    !!quotedParticipant &&
    sameUser(quotedParticipant, botJid);
  const messageKey = {
    remoteJid: jid,
    id: quotedId,
    ...(quotedParticipant
      ? { participant: quotedParticipant }
      : {}),
    fromMe: isBotMessage
  };

  if (!isBotMessage) {
    let metadata;
    try {
      metadata = await sock.groupMetadata(jid);
    } catch (error) {
      console.error("[DEL] No se pudo consultar la metadata del grupo:", error);
      return sock.sendMessage(
        jid,
        { text: "❌ No pude verificar si el bot es administrador del grupo." },
        { quoted: msg }
      );
    }

    const botNumber = normalizeNumber(botJid);
    const botParticipant = metadata.participants.find(participant =>
      sameUser(participant.id, botJid) ||
      (botNumber &&
        normalizeNumber(participant.phoneNumber) === botNumber)
    );
    const botIsAdmin =
      botParticipant?.admin === "admin" ||
      botParticipant?.admin === "superadmin" ||
      botParticipant?.admin === true;

    if (!botIsAdmin) {
      return sock.sendMessage(
        jid,
        { text: "❌ El bot debe ser administrador para borrar mensajes de otros usuarios." },
        { quoted: msg }
      );
    }
  }

  try {
    await sock.sendMessage(jid, { delete: messageKey });
  } catch (error) {
    console.error("[DEL] No se pudo borrar el mensaje:", error);
    return sock.sendMessage(
      jid,
      { text: "❌ No se pudo borrar el mensaje. Comprueba que el bot tenga permisos." },
      { quoted: msg }
    );
  }
}

const LUCK_SHOP = {
  mod:        { cost: 1000000, gain: 1 },
  mythic:     { cost: 870000,  gain: 2 },
  legendary:  { cost: 680000,  gain: 5 },
  epic:       { cost: 530000,  gain: 10 },
  rare:       { cost: 424000,  gain: 15 },
  common:     { cost: 320000,  gain: 20 }
};

export async function handleCinfo(
  sock,
  msg,
  args
) {

    const sender = msg.key.participant || msg.key.remoteJid;


// CONFIRMACION DELSERIE
try {
  const deleteHandled =
    await handleDeleteSerieReply(
      sock,
      msg,
      sender
    );

  if(deleteHandled) return;

} catch(e){
  console.log("ERROR DELSERIE CONFIRM:",e);
}


  const permitido =
    isMainOwnerId(sender) ||
    isSecondaryOwnerId(sender) ||
    isStaffOwner;

if (!permitido) {
    return;
}

  const query =
    args.join(' ').trim();

  if (!query) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`「☆」𝐈𝐧𝐟𝐨𝐫𝐦𝐚𝐜𝐢𝐨́𝐧 𝐝𝐞𝐥 𝐕𝐞𝐡𝐢́𝐜𝐮𝐥𝐨

◇ Uso ╋ \`/cinfo ID\`

♡ Ejemplo ╋ \`/cinfo 1\``
      },
      {
        quoted: msg
      }
    );

  }

  loadCars();

  const numericId =
    Number(query);

  const car =
    carsCache.find(
      c =>
        String(c.id) === query ||
        c.key?.toLowerCase() ===
        query.toLowerCase()
    );

  if (!car) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
` No se encontrï¿½ ningï¿½n vehículo.

◇ ID buscado ╋ \`${query}\``
      },
      {
        quoted: msg
      }
    );

  }

  const creatorName =
    db.users?.[car.creator]?.name ||
    car.creator?.split('@')[0] ||
    'Desconocido';

  const date =
    car.createdAt
      ? new Date(
          car.createdAt
        ).toLocaleDateString(
          'es-CL'
        )
      : 'No registrada';

const cantidadImagenes = car.images?.length || 0;

  const claimedCount =
    Object.keys(
      car.claimedBy || {}
    ).length;

  const text =
`「☆」𝐈𝐧𝐟𝐨𝐫𝐦𝐚𝐜𝐢𝐨́𝐧 𝐝𝐞𝐥 𝐕𝐞𝐡𝐢́𝐜𝐮𝐥𝐨

◇ ID ╋ \`${car.id}\`
♡ Nombre ╋ \`${car.carName || 'Sin nombre'}\`
♧ Creador ╋ \`${creatorName}\`
? Fecha ╋ \`${date}\`
♧ Im¿genes ╋ \`${cantidadImagenes}\`

☆ Precio ╋ \`¥${Number(
  car.price || 0
).toLocaleString()}\`
❀ Aceleración ╋ \`${Number.isFinite(Number(car.acceleration)) && Number(car.acceleration) > 0 ? car.acceleration : 'Pendiente'}\`
♤ Reclamado por ╋ \`${claimedCount} ${
  claimedCount === 1
    ? 'persona'
    : 'personas'
}\`
♢ Personaje asociado ╋ {car.personaje || 'No asociado'}`;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text
    },
    {
      quoted: msg
    }
  );

} 

export async function handleCn(sock, msg, groupId, sender) {
  return carCommandLock(groupId, async () => {
    const cooldowns = getGroupCooldowns(groupId, sender);
    const now = Date.now();
    const existingCooldown =
      getCooldownRemainingMs(cooldowns.cn, now);
    if (existingCooldown > 0) {
      return sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
            `𖤛 Dᥱbᥱs ᥱsρᥱrᥲr \`${formatCooldown(existingCooldown)}\` ` +
            `ρᥲrᥲ voᥣvᥱr ᥲ ᥙsᥲr \`${db.prefix || '/'}cn\` .`
        },
        { quoted: msg }
      );
    }

    const car = getRandomCar(candidate =>
      Array.isArray(candidate.images) &&
      candidate.images.some(image =>
        typeof image === 'string' && fs.existsSync(image)
      )
    );

    if (!car) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: 'No hay vehículos con imágenes disponibles.' },
        { quoted: msg }
      );
    }

    const images = car.images.filter(
      image => typeof image === 'string' && fs.existsSync(image)
    );
    const randomImage = getRandomCarImage(images);
    if (!randomImage) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: `El vehículo ${car.carName} no tiene imágenes disponibles.` },
        { quoted: msg }
      );
    }

    const img = fs.readFileSync(randomImage);
    const user = initUser(sender);
    if (!user) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: 'No pude validar tu cuenta para guardar el vehículo.' },
        { quoted: msg }
      );
    }

    const cooldown = tryStartCooldown(cooldowns, now);
    if (!cooldown.allowed) {
      return sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
            `𖤛 Dᥱbᥱs ᥱsρᥱrᥲr \`${formatCooldown(cooldown.remainingMs)}\` ` +
            `ρᥲrᥲ voᥣvᥱr ᥲ ᥙsᥲr \`${db.prefix || '/'}cn\` .`
        },
        { quoted: msg }
      );
    }

    const owner = car.claimedBy?.[groupId];
    const state = owner ? 'Rᥱᥴᥣᥲmᥲdo' : 'Dιsρoᥒιbᥣᥱ';
    const prefix =
      typeof db.prefix === 'string' && db.prefix.length > 0
        ? db.prefix
        : '/';

    user.lastVehicleByGroup ??= {};
    user.lastVehicleByGroup[groupId] = {
      id: car.id,
      key: car.key,
      timestamp: now
    };
    await saveDB();

    const caption =
`■ Cᥲrro : *${car.carName}*

☆ Rᥲᥒgo : *${car.rarity || 'Sin rango'}*
⛀ Prᥱᥴιo : \`${Number(car.price || 0).toLocaleString('es-CL')}\`
𖤛 Vᥱᥣoᥴιdᥲd : \`${car.speed || 0} KM/H\`
❀ Aᥴᥱᥣᥱrᥲᥴιoᥒ : \`${Number.isFinite(Number(car.acceleration)) && Number(car.acceleration) > 0 ? car.acceleration : 'Pendiente'}\`
♧ Estᥲdo : *${state}*
♡ Asoᥴιᥲdo : *${car.personaje || 'No asociado'}*

> Rᥱᥴᥣᥲ́mᥲᥣo ᥴoᥒ *${prefix}cv* ᥴιtᥲᥒdo ᥱstᥱ mᥱᥒsᥲjᥱ`;

    await sock.sendMessage(
      msg.key.remoteJid,
      { image: img, caption },
      { quoted: msg }
    );
  });
}

export async function handleCv(sock, msg, groupId, sender) {
  return carCommandLock(groupId, async () => {
    const user = initUser(sender);
    if (!user) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: 'No pude validar tu cuenta para reclamar el vehículo.' },
        { quoted: msg }
      );
    }

    const lastVehicle = user.lastVehicleByGroup?.[groupId];
    if (!lastVehicle) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: `❌ Primero usa ${db.prefix || '/'}cn en este grupo.` },
        { quoted: msg }
      );
    }

    const car = carsCache.find(
      candidate => Number(candidate.id) === Number(lastVehicle.id)
    );
    if (!car) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: 'El vehículo mostrado ya no existe.' },
        { quoted: msg }
      );
    }

    const price = Number(car.price);
    if (!Number.isSafeInteger(price) || price < 0) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: 'No se puede comprar este vehículo: su precio no es válido.' },
        { quoted: msg }
      );
    }

    const economy = getGroupEconomy(groupId, sender);
    const previousCoins = Number(economy.coins);
    const previousBank = Number(economy.bank);
    const claimResult = claimCar(car, groupId, sender, economy);
    if (claimResult.status === 'already-claimed') {
      const owner =
        db.users?.[claimResult.owner]?.name ||
        String(claimResult.owner || '').split('@')[0] ||
        'otro usuario';
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: `Ese vehículo ya fue reclamado por *${owner}* en este grupo.` },
        { quoted: msg }
      );
    }
    if (claimResult.status === 'insufficient-funds') {
      const available =
        (Number(economy.coins) || 0) + (Number(economy.bank) || 0);
      return sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
            `No tienes fondos suficientes para comprarlo. Precio: ${price.toLocaleString()}; ` +
            `disponible entre wallet y banco: ${available.toLocaleString()}.`
        },
        { quoted: msg }
      );
    }

    if (claimResult.status !== 'claimed') {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: 'No se pudo validar el vehículo para la compra.' },
        { quoted: msg }
      );
    }
    const payment = claimResult.payment;
    delete user.lastVehicleByGroup[groupId];

    try {
      saveCars();
      await saveDB();
    } catch (error) {
      delete car.claimedBy[groupId];
      economy.coins = previousCoins;
      economy.bank = previousBank;
      user.lastVehicleByGroup[groupId] = lastVehicle;
      saveCars();
      await saveDB();
      throw error;
    }

    const name = db.users?.[sender]?.name || sender.split('@')[0];
    const currency = getBotCurrency(sock);
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          `■ *${name}* reclamó *${car.carName}* en este grupo.\n` +
          `Precio pagado: ${price.toLocaleString()} ${currency} ` +
          `(wallet ${payment.fromCoins.toLocaleString()}, banco ${payment.fromBank.toLocaleString()}).`
      },
      { quoted: msg }
    );
  });
}

export async function handleGarage(sock, msg, args, groupId, sender) {
  loadCars();
  const prefix =
    typeof db.prefix === 'string' && db.prefix.length > 0
      ? db.prefix
      : '/';
  const input = String(args[0] || '1').trim();
  if (args.length > 1 || !/^[1-9]\d*$/.test(input)) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: `Uso: ${prefix}garaje [número de página positivo].` },
      { quoted: msg }
    );
  }

  const requestedPage = Number(input);
  if (!Number.isSafeInteger(requestedPage)) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: 'El número de página debe ser un entero positivo válido.' },
      { quoted: msg }
    );
  }

  const getSpeed = car => {
    const speed = Number(car.speed);
    return Number.isFinite(speed) ? speed : 0;
  };

  const ownedCars = getGroupOwnedCars(carsCache, groupId, sender)
    .sort((first, second) =>
      getSpeed(second) - getSpeed(first) ||
      String(first.carName || '').localeCompare(String(second.carName || ''), 'es') ||
      Number(first.id || 0) - Number(second.id || 0)
    );

  if (!ownedCars.length) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          `❀ Aᥙtos Rᥱᥴᥣᥲmᥲdos ❀\n` +
          `⌦ Usᥙᥲrιo: \`${db.users?.[sender]?.name || sender.split('@')[0]}\`\n` +
          '♡ Aᥙtos: `(0)`\n\n' +
          '> No tienes autos reclamados en este grupo.'
      },
      { quoted: msg }
    );
  }

  const page = paginateCars(ownedCars, requestedPage);
  if (!page.valid) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: `Página inválida. Las páginas disponibles van de 1 a ${page.pageCount}.`
      },
      { quoted: msg }
    );
  }

  const rows = page.cars.map(car =>
    `» \`${car.carName || 'Auto sin nombre'}\` 𖤛 \`${getSpeed(car)}km\` ✶ \`${Number.isFinite(Number(car.acceleration)) && Number(car.acceleration) > 0 ? car.acceleration : 'Pendiente'}\``
  );
  const text =
    `❀ Aᥙtos Rᥱᥴᥣᥲmᥲdos ❀\n` +
    `⌦ Usᥙᥲrιo: \`${db.users?.[sender]?.name || sender.split('@')[0]}\`\n` +
    `♡ Aᥙtos: \`(${ownedCars.length})\`\n\n` +
    `${rows.join('\n')}\n\n` +
    `> ⌦ *Pᥲ́gιᥒᥲ *${page.page}* dᥱ *${page.pageCount}**`;

  return sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}

export async function handleBuyLuck(sock, msg, args, sender) {

    const type = (args[0] || "").toLowerCase();

    if (!LUCK_SHOP[type]) {
        return sock.sendMessage(msg.key.remoteJid,{
            text:
`◇ Uso:

/buyluck common
/buyluck rare
/buyluck epic
/buyluck legendary
/buyluck mythic
/buyluck mod`
        },{ quoted: msg });
    }

    const user = initUser(sender);

    const item = LUCK_SHOP[type];

    if (user.gems < item.cost) {
        return sock.sendMessage(msg.key.remoteJid,{
            text:
`◇ Necesitas ${item.cost.toLocaleString()} gemas.`
        },{ quoted: msg });
    }

    user.gems -= item.cost;

    user.luck[type] += item.gain;

    user.luck.total =
        user.luck.mod +
        user.luck.mythic +
        user.luck.legendary +
        user.luck.epic +
        user.luck.rare +
        user.luck.common;

    saveDB();

    await sock.sendMessage(msg.key.remoteJid,{
        text:
`✿ Compraste +${item.gain}% de suerte para ${type}.

💎 Gemas restantes:
${user.gems.toLocaleString()}

✨ Suerte total:
${user.luck.total}%`
    },{ quoted: msg });

}

export async function handleLuckShop(sock,msg){

  updateLuckShop();

  const d =
    db.luckShop.discount.percent;

  const m =
    db.luckShop.multiplier.value;

  const discount = x =>
    Math.floor(
      x * (100-d)/100
    );

  const prices = {

    mod:1000000,

    mythic:870000,

    legendary:680000,

    epic:530000,

    rare:424000,

    common:320000

  };

  const discTime =
    Math.max(
      0,
      db.luckShop.discount.expires-Date.now()
    );

  const multTime =
    Math.max(
      0,
      db.luckShop.multiplier.expires-Date.now()
    );

  const dm =
    Math.floor(discTime/60000);

  const ds =
    Math.floor((discTime%60000)/1000);

  const mm =
    Math.floor(multTime/60000);

  const ms =
    Math.floor((multTime%60000)/1000);

  let text =
`✿ *》》Tienda de Suerte《《* ✿

> Mejora tu suerte para pjs buenos.

ⴵ *Mod* » \`${discount(prices.mod).toLocaleString()}\` > \`1%\`
ⴵ *Mitico* » \`${discount(prices.mythic).toLocaleString()}\` > \`2%\`
ⴵ *Legendario* » \`${discount(prices.legendary).toLocaleString()}\` > \`5%\`
ⴵ *Epico* » \`${discount(prices.epic).toLocaleString()}\` > \`10%\`
ⴵ *Raro* » \`${discount(prices.rare).toLocaleString()}\` > \`15%\`
ⴵ *Comun* » \`${discount(prices.common).toLocaleString()}\` > \`20%\`

━━━━━━━━━━━━━━

⛁ Evento de descuento »
*${d}%*

Finaliza:
${dm}m ${ds}s

⚡ Multiplicador »
*x${m}*

Finaliza:
${mm}m ${ms}s`;

  await sock.sendMessage(
    msg.key.remoteJid,
    {text},
    {quoted:msg}
  );

}

export async function handleLuck(sock, msg, sender) {

  const user = initUser(sender);

  const luck = user.luck;

  const total =
    luck.mod +
    luck.mythic +
    luck.legendary +
    luck.epic +
    luck.rare +
    luck.common;

  user.luck.total = total;

  const diamonds = user.diamonds || 0;
  const diamondsStr = formatNumber(diamonds);

  let text = 'Suerte de ' + user.name + '\n\n> Mejora tu suerte para pjs buenos.\n\nMod >> ' + luck.mod + '%\nMitico >> ' + luck.mythic + '%\nLegendario >> ' + luck.legendary + '%\nEpico >> ' + luck.epic + '%\nRaro >> ' + luck.rare + '%\nComun >> ' + luck.common + '%\n\nTotal Suerte >> ' + total + '%\n\nDiamantes >> ' + diamondsStr + '\n\nGemas >> ' + (user.gems || 0).toLocaleString();

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );

  saveNow();

}

// Reintenta obtener la imagen de un personaje (fallos temporales de red/booru)
async function rwMediaRetry(character, intentos = 3) {
  for (let i = 1; i <= intentos; i++) {
    try {
      const media = await getCharacterMedia(character);
      if (media) return media;
    } catch (e) {
      console.error("[RWP] Error de imagen (intento " + i + "/" + intentos + ") ID " + (character && character.id) + ": " + (e && e.message ? e.message : e));
    }
    if (i < intentos) await new Promise(r => setTimeout(r, 1500));
  }
  return null;
}

export async function handleRwp(
  sock,
  msg,
  args,
  groupId,
  sender
){
  const jid = msg.key.remoteJid;
  const user = initUser(sender);

  // Solo XPremium
  if (!hasXPremium(user)) {
    return sock.sendMessage(
      jid,
      {
        text:
"so\u1963o \u1963os \u1959s\u1959\u1972r\u03B9os \u1974o\u1952 \u1971\u1963 \u03C1\u1972s\u1971 \x60x\u03C1r\u1971m\u03B9\u1959m\x60 \u03C1\u1959\u1971d\u1971\u1952 \u1959t\u03B9\u1963\u03B9z\u1972r \u1971st\u1971 \u1974om\u1972\u1952do.\n" +
"> \u2605 Com\u03C1r\u1972\u1963o \u1974o\u1952 /x\u03C1r\u1971m\u03B9\u1959m"
      },
      { quoted: msg }
    );
  }

  // Probabilidad fija (ya no se usan porcentajes)
  const RWP_CHANCE = 60;

  // Compatibilidad: si escriben "/rwp 10 Nombre" se ignora el numero
  const nameArgs =
    (args.length > 1 && /^\d+%?$/.test(String(args[0])))
      ? args.slice(1)
      : args;

  const charName = nameArgs.join(" ").trim();

  if (!charName) {
    return sock.sendMessage(
      jid,
      {
        text:
"\u25C7 Uso:\n\n/rwp Nazuna Nanakusa\n\n\u25C7 Probabilidad fija: " + RWP_CHANCE + "%"
      },
      { quoted: msg }
    );
  }

  if (!charactersCache.length) { loadCharactersCache(); loadSeries(); }

  const needle = charName.toLowerCase();

  const target =
    charactersCache.find(c => String(c.name || "").toLowerCase() === needle) ||
    charactersCache.find(c => String(c.name || "").toLowerCase().includes(needle));

  if (!target) {
    return sock.sendMessage(
      jid,
      { text: "\u25C7 Personaje no encontrado." },
      { quoted: msg }
    );
  }

  const wait = getPremiumCooldown(user);

  if (Date.now() - user.lastRwp < wait) {
    const left =
      Math.ceil(
        (wait - (Date.now() - user.lastRwp)) / 60000
      );

    return sock.sendMessage(
      jid,
      { text: "\u23F3 Espera " + left + " minuto(s)." },
      { quoted: msg }
    );
  }

  // Sorteo (el tiempo de espera NO se aplica hasta tener imagen)
  let character =
    (Math.random() * 100 < RWP_CHANCE)
      ? target
      : getRandomCharacter(sender, groupId);

  let imageData = await rwMediaRetry(character, 3);

  // Si falla un personaje sorteado al azar, probar con otros
  if (!imageData && character.key !== target.key) {
    for (let i = 0; i < 3 && !imageData; i++) {
      character = getRandomCharacter(sender, groupId);
      imageData = await rwMediaRetry(character, 2);
    }
  }

  if (!imageData) {
    try {
      await notifyEvents(
        sock,
        "\u274C Error de imagen (/rwp)\n\nPersonaje: " + character.name + "\nID: " + character.id + "\nSolicitado por: @" + String(sender).split("@")[0],
        [sender]
      );
    } catch (e) {}

    return sock.sendMessage(
      jid,
      {
        text:
"Error > Personaje \x60ID " + character.id + "\x60\n\nNo se aplic\u00F3 tiempo de espera, int\u00E9ntalo de nuevo.\n\nSi el problema persiste\nav\u00EDsanos con */report*"
      },
      { quoted: msg }
    );
  }

  // Ahora si: aplicar el tiempo de espera
  user.lastRwp = Date.now();
  saveDB();

  const claimEntry = character.claimedBy?.[groupId];
  const alreadyClaimed = claimEntry ? claimEntry.user : null;

  const economy = getGroupEconomy(groupId, sender);

  economy.lastClaim = {
    id: character.id,
    key: character.key,
    name: character.name,
    anime: character.anime,
    gender: character.gender,
    value: character.value,
    rarity: character.rarity,
    claimed: !!alreadyClaimed,
    claimedBy: alreadyClaimed,
    timestamp: Date.now(),
    invoker: sender
  };

  saveDB();

  const creatorName = getCharacterCreatorName(character);

  const estadoTxt =
    alreadyClaimed
      ? (db.users?.[alreadyClaimed]?.name || alreadyClaimed.split("@")[0])
      : "Libre";

  const rwpResult =
    await sock.sendMessage(
      jid,
      {
        ...imageData,
        caption: buildRwCaption(character, estadoTxt, creatorName)
      },
      { quoted: msg }
    );

  rememberRwResultMessage(jid, rwpResult);
}


export async function handleRwr(sock, msg, args, groupId, sender) {
  const isMainOwner =
    isMainOwnerId(sender);
  const isSecondaryOwner =
    isSecondaryOwnerId(sender);

  if (!isMainOwner && !isSecondaryOwner) return;

  const charName = args.join(' ').trim();
  if (!charName) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: '◇ Uso:\n/rwr Nombre del personaje' },
      { quoted: msg }
    );
  }

  const user = initUser(sender);
  if (!user) return;

  const COOLDOWN_MS = 5_000;
  const now = Date.now();
  const elapsed = now - (Number(user.lastRwr) || 0);
  if (elapsed < COOLDOWN_MS) {
    const remaining = Math.ceil((COOLDOWN_MS - elapsed) / 1_000);
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: `⏳ Espera ${remaining} segundo(s) para volver a usar /rwr.` },
      { quoted: msg }
    );
  }

  const target = charactersCache.find(
    character => character.name.toLowerCase().includes(charName.toLowerCase())
  );
  if (!target) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: '◇ Personaje no encontrado.' },
      { quoted: msg }
    );
  }

  // Guardarlo antes de cargar la imagen evita dos invocaciones simultáneas.
  user.lastRwr = now;
  saveDB();

  const imageData = await getCharacterMedia(target);
  if (!imageData) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: `Error > Personaje \`ID ${target.id}\`\n\nSi el problema persiste avísanos con */report*` },
      { quoted: msg }
    );
  }

  const claimEntry = target.claimedBy?.[groupId];
  const alreadyClaimed = claimEntry ? claimEntry.user : null;
  const economy = getGroupEconomy(groupId, sender);
  economy.lastClaim = {
    id: target.id,
    key: target.key,
    name: target.name,
    anime: target.anime,
    gender: target.gender,
    value: target.value,
    rarity: target.rarity,
    claimed: !!alreadyClaimed,
    claimedBy: alreadyClaimed,
    timestamp: now,
    invoker: sender
  };
  saveDB();

  const cap =
`☆ INVOCACIÓN DE OWNER

❬ Nombre » ${target.name}
☆ Rareza » ${target.rarity || 'Comun'}
◇ Suerte usada » 1000%
✰ Valor » ${target.value}`;

  await sock.sendMessage(
    msg.key.remoteJid,
    { ...imageData, caption: cap },
    { quoted: msg }
  );
}

export async function handleRwpx(
  sock,
  msg,
  args,
  sender
){

  if (sender !== OWNER_NUMBER)
  return;

  const raw =
  args.join(' ');

const data =
  raw
  .split('/')
  .map(x => x.trim());

  if (data.length < 2) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso:\n/rwpx 30% / 10000000'
      },
      { quoted: msg }
    );

  }

  const chance =
    data[0]
    .replace('%','')
    .trim();

  const cost =
    Number(
      data[1]
      .trim()
      .replace(/\./g,'')
    );

  if (
  !chance ||
  isNaN(cost)
){
  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text: ' Datos inválidos.'
    },
    {
      quoted: msg
    }
  );
}

  db.rwpChances[chance] =
    cost;

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Chance agregada

Chance » ${chance}%
Costo » ¥${cost.toLocaleString()}`
    },
    {
      quoted: msg
    }
  );

}

export async function handleDelX(
  sock,
  msg,
  args,
  sender
){

  const chance =
    args[0]
    ?.replace('%','');

  if (!chance)
    return;

  delete db.rwpChances[chance];

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Eliminado ${chance}%`
    },
    {
      quoted: msg
    }
  );

}

export async function handleResetGacha({ sock, jid, msg, sender }) {

  if (sender !== OWNER_NUMBER) {
    return sock.sendMessage(jid, {
      text: '◇ Solo el owner puede usar esto.'
    }, { quoted: msg });
  }

  const groups = db.groups || {};

  for (const groupId in groups) {

    groups[groupId].claimedCharacters = {};

    groups[groupId].harems = {};

    groups[groupId].training = {};

  }

  saveDB();

  await sock.sendMessage(jid, {
    text: ' Gacha reiniciado correctamente.\nTodos los personajes ahora están libres.'
  }, { quoted: msg });

for (const char of characterMap.values()) {
  delete char.claimedBy;
  delete char.owner;
}
}

export async function handleResetHarem(sock, msg, jid, sender) {

  if (sender !== OWNER_NUMBER) {
    return sock.sendMessage(
      jid,
      {
        text: '◇ Solo el owner puede usar esto.'
      },
      { quoted: msg }
    );
  }

  const groups = db.groups || {};

  let revisados = 0;
  let reparados = 0;
  let yaCorrectos = 0;

  for (const [groupId, group] of Object.entries(groups)) {

    if (!group) continue;

    group.harems ??= {};

    for (const character of characterMap.values()) {

      const claimedBy = character?.claimedBy?.[groupId];

      if (!claimedBy?.user) {
        continue;
      }

      revisados++;

      const owner = claimedBy.user;

      group.harems[owner] ??= [];

      const harem = group.harems[owner];

      const existsInHarem = harem.some(
        item => item?.key === character.key
      );

      if (existsInHarem) {
        yaCorrectos++;
      } else {

        harem.push({
          id: character.id,
          key: character.key,
          name: character.name,
          anime: character.anime,
          gender: character.gender,
          value: character.value,
          rarity: character.rarity,
          image: character.image || null,
          claimed: false,
          claimedBy: null,
          timestamp: claimedBy.time,
          invoker: owner
        });

        reparados++;
      }

      const user = db.users?.[owner];

      if (user && typeof user === 'object') {
        user.harem ??= [];

        if (!user.harem.includes(character.key)) {
          user.harem.push(character.key);
        }
      }
    }
  }

  buildOwnerIndex();

  saveCharacters();
  saveDB();

  await sock.sendMessage(
    jid,
    {
      text:
`◇ Reparación de harems completada.

□ Reclamaciones revisadas » ${revisados}
◇ Personajes reparados » ${reparados}
◇ Ya estaban correctos » ${yaCorrectos}

◇ Las reclamaciones no fueron liberadas.
◇ Los personajes huérfanos fueron devueltos a sus harems.`
    },
    { quoted: msg }
  );
}

export async function handleClaim(sock, msg, groupId, sender) {
  const group = db.groups[groupId];
  const economy = getGroupEconomy(groupId, sender);
  const lc = economy.lastClaim;
  if (!lc) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No hay personaje pendiente.' }, { quoted: msg });
  if (lc.claimed) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Ya fue reclamado.' }, { quoted: msg });

  const cooldowns = getGroupCooldowns(groupId, sender);
  const now = Date.now();
  if (now - cooldowns.claim < CLAIM_CD) {
    const w = Math.ceil((CLAIM_CD - (now - cooldowns.claim)) / 1000);
    return sock.sendMessage(msg.key.remoteJid, { text: `⏳ Debes esperar ${Math.floor(w/60)}m ${w%60}s para reclamar de nuevo.` }, { quoted: msg });
  }

  const elapsed = now - lc.timestamp;
  if (elapsed < 20000 && sender !== lc.invoker) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Solo el invocador puede reclamar en los primeros 20s.' }, { quoted: msg });
  if (elapsed > 30000) { economy.lastClaim = null; saveDB(); return sock.sendMessage(msg.key.remoteJid, { text: '◇ El tiempo expir¿.' }, { quoted: msg }); }

  const character = characterKeyMap.get(lc.key);
  if (!character) return;
  if (!character.claimedBy) character.claimedBy = {};
  // Verificar que no esté ya reclamado en el grupo
  if (character.claimedBy[groupId] && character.claimedBy[groupId].user !== sender) {
    return sock.sendMessage(msg.key.remoteJid, { text: '◇ Este personaje ya fue reclamado por otro usuario.' }, { quoted: msg });
  }
  character.claimedBy[groupId] = {
  user: sender,
  time: now
};

if (character.creator) {

  db.staffStats ??= {};

  db.staffStats[character.creator] ??= {
    fans: 0,
    claimed: {}
  };

  const claimed =
    db.staffStats[
      character.creator
    ].claimed;

  claimed[character.id] ??= [];

  if (
    !claimed[
      character.id
    ].includes(sender)
  ){

    claimed[
      character.id
    ].push(sender);

    db.staffStats[
      character.creator
    ].fans++;

  }

}
  if (!global.ownerIndex[groupId]) global.ownerIndex[groupId] = {};
  if (!global.ownerIndex[groupId][sender]) global.ownerIndex[groupId][sender] = new Set();
  global.ownerIndex[groupId][sender].add(lc.key);
  saveCharacters();

  if (!group.harems[sender]) {
  group.harems[sender] = [];
}

if (!group.harems[sender].some(c => c.key === lc.key)) {
  group.harems[sender].push(lc);
}

await checkHarem100Reward(sock, msg, groupId, sender);

const owner = initUser(sender);

owner.harem ??= [];

if (!owner.harem.includes(lc.key)) {
  owner.harem.push(lc.key);
}

cooldowns.claim = now;
economy.lastClaim = null;

saveCharacters();
saveDB();

let claimText =
owner.claimMsg ||
'$user ha reclamado el personaje $character!';

claimText = claimText
.replace(/\$user/g, owner.name || 'Usuario')
.replace(/\$character/g, character.name);

await sock.sendMessage(
  msg.key.remoteJid,
  { text: claimText },
  { quoted: msg }
);

}

export async function handleVote(sock, msg, args, groupId, sender) {
  const name =
  args.join(' ')
      .toLowerCase()
      .trim();
  if (!name) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Uso: /vote [nombre]' }, { quoted: msg });
  if (!charactersCache.length) loadCharactersCache();
  const char = charactersCache.find(c => c.name.toLowerCase() === name);
  if (!char) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Personaje no encontrado.' }, { quoted: msg });

  const now = Date.now();
  const globalCD = db.globalCooldowns.vote[sender] || 0;
  if (now - globalCD < VOTE_CD) {
    const rem = VOTE_CD - (now - globalCD);
    const mins = Math.floor(rem / 60000);
    const secs = Math.floor((rem % 60000) / 1000);
    return sock.sendMessage(msg.key.remoteJid, { text: `《✧》Ya votaste recientemente. Espera ${mins}m ${secs}s.` }, { quoted: msg });
  }

  char.value += 100;
  char.votes = (char.votes || 0) + 1;
  char.lastVote = now;
  if (char.creator) {

  db.staffStats ??= {};

  db.staffStats[char.creator] ??= {
    fans: 0,
    claimed: {}
  };

  const claimed =
    db.staffStats[
      char.creator
    ].claimed;

  claimed[char.id] ??= [];

  if (
    !claimed[
      char.id
    ].includes(sender)
  ){

    claimed[
      char.id
    ].push(sender);

    db.staffStats[
      char.creator
    ].fans++;

  }

}
  db.globalCooldowns.vote[sender] = now;
  saveCharacters();
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `✰ Valor de *${char.name}* aument¿ a ${char.value}.` }, { quoted: msg });
}

// ━━━━━━━ COMANDOS DE SERIES ━━━━━━━
export async function handleSlist(sock, msg, args) {
  const jid = msg.key.remoteJid;
  const page = Math.max(1, parseInt(args[0], 10) || 1);
  const perPage = 10;

  const estilizar = (texto) => {
    const mapa = {
      'a': '\u1972',
      'e': '\u1971',
      'i': '\u03B9',
      'l': '\u1963',
      'n': '\u1952',
      'u': '\u1959',
      'c': '\u1974',
      'p': '\u03C1',
      'y': '\u10E7'
    };
    return String(texto).replace(/[aeiulncpy]/g, ch => mapa[ch] || ch);
  };

  const allSeries = Array.from(seriesCache.values());

  if (!allSeries.length) {
    return sock.sendMessage(
      jid,
      { text: '\u25C7 No hay series disponibles.' },
      { quoted: msg }
    );
  }

  // Orden: mayor cantidad de personajes -> menor
  const sorted = [...allSeries].sort((a, b) => {
    const na = Number(a.characters?.size || 0);
    const nb = Number(b.characters?.size || 0);
    if (nb !== na) return nb - na;
    return String(a.name).localeCompare(String(b.name));
  });

  const total = sorted.length;
  const pages = Math.max(1, Math.ceil(total / perPage));
  const safePage = Math.min(page, pages);
  const slice = sorted.slice((safePage - 1) * perPage, safePage * perPage);

  let text =
    '\u274F ' +
    estilizar('Lista de series') +
    ' `' + total + '`:\n\n';

  for (const s of slice) {
    const count = s.characters?.size || 0;
    text +=
      '\u00BB `' +
      estilizar(s.name) +
      ' (' + count + ')`\n';
  }

  text +=
    '\n> ' +
    estilizar('Pagina') +
    ' `' + safePage + '/' + pages + '`';

  await sock.sendMessage(
    jid,
    { text },
    { quoted: msg }
  );
}
export async function handleMergeSerie(
  sock,
  msg,
  args,
  sender
){

  const raw =
    args.join(' ');

  const parts =
    raw.split('/')
       .map(v => v.trim())
       .filter(Boolean);

  if (parts.length < 2){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/mergeserie Serie origen / Serie destino

Ejemplo

/mergeserie Oshi no Ko / [Oshi No Ko]`
      },
      {
        quoted: msg
      }
    );

  }

  const from =
    findSeries(parts[0]);

  const to =
    findSeries(parts[1]);

  if (!from){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ No encontr¿ la serie:

${parts[0]}`
      },
      {
        quoted: msg
      }
    );

  }

  if (!to){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ No encontr¿ la serie:

${parts[1]}`
      },
      {
        quoted: msg
      }
    );

  }

  if (
    from.name.toLowerCase() ===
    to.name.toLowerCase()
  ){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ No puedes fusionar la misma serie.'
      },
      {
        quoted: msg
      }
    );

  }

  const totalOrigen =
    from.characters.size;

  const totalDestino =
    to.characters.size;

  const confirm =
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`⚠ Confirmación @${sender.split('@')[0]}

ï¿½Estï¿½ seguro de fusionar las series?

◇ Serie origen »
${from.name}

□ Personajes »
${totalOrigen}

⬇

◇ Serie destino »
${to.name}

□ Personajes »
${totalDestino}

⚠ Esta acción mover¿:

• Todos los personajes
• Todos los alias
• Todas las reclamaciones
• Todas las im¿genes
• Todos los videos

La serie origen será eliminada.

Responde citando este mensaje:

\`si\`

o

\`no\``,
        mentions:[sender]
      },
      {
        quoted: msg
      }
    );

  db.pendingMergeSeries[
    confirm.key.id
  ] = {

    from:
      from.name,

    to:
      to.name,

    sender,

    chat:
      msg.key.remoteJid,

    created:
      Date.now()

  };

  saveDB();

}

async function handleMergeSerieReply(
  sock,
  msg,
  sender
){

  const quoted =
    msg.message?.extendedTextMessage
    ?.contextInfo;

  if (!quoted) return false;

  const pending =
    db.pendingMergeSeries?.[
      quoted.stanzaId
    ];

  if (!pending)
    return false;

  delete db.pendingMergeSeries[
    quoted.stanzaId
  ];

  saveDB();

  if (sender !== pending.sender)
    return true;

  const answer =
    (
      msg.message?.conversation ||
      msg.message?.extendedTextMessage?.text ||
      ''
    )
    .trim()
    .toLowerCase();

  if (answer === 'no'){

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Fusión cancelada.'
      },
      {
        quoted: msg
      }
    );

    return true;

  }

  if (answer !== 'si')
    return true;

  const from =
    seriesCache.get(
      pending.from.toLowerCase()
    );

  const to =
    seriesCache.get(
      pending.to.toLowerCase()
    );

  if (!from || !to){

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Una de las series ya no existe.'
      },
      {
        quoted: msg
      }
    );

    return true;

  }

  let moved = 0;

  for (const key of from.characters){

    const char =
      characterKeyMap.get(key);

    if (!char)
      continue;

    char.anime =
      to.name;

    to.characters.add(key);

    moved++;

  }

  from.characters.clear();

  seriesCache.delete(
    from.name.toLowerCase()
  );

  const oldFile =
    path.join(
      SERIES_DIR,
      `${from.name
        .toLowerCase()
        .replace(/[^\w]/g,'_')}.json`
    );

  if (
    fs.existsSync(oldFile)
  ){
    fs.unlinkSync(oldFile);
  }

  const newFile =
    path.join(
      SERIES_DIR,
      `${to.name
        .toLowerCase()
        .replace(/[^\w]/g,'_')}.json`
    );

  fs.writeFileSync(
    newFile,
    JSON.stringify({
      name:to.name,
      characters:[
        ...to.characters
      ]
    },null,2)
  );

  saveCharacters();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`✓ Series fusionadas

◇ Serie eliminada »
${from.name}

◇ Serie destino »
${to.name}

□ Personajes movidos »
${moved}`
    },
    {
      quoted: msg
    }
  );

  return true;

}

export async function handleAinfo(sock, msg, args, groupId) {
  const queryRaw = args.join(' ').trim();

  if (!queryRaw) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: '\u25C7 Uso: /ainfo <serie>' },
      { quoted: msg }
    );
  }

  const query = queryRaw.toLowerCase();

  const normalize = v =>
    String(v || '')
      .toLowerCase()
      .normalize('NFD')
      .replace(/[\u0300-\u036f]/g, '')
      .replace(/\s+/g, ' ')
      .trim();

  const queryNorm = normalize(queryRaw);

  // 1) Coincidencia exacta por key del cache
  let serie = seriesCache.get(query);

  // 2) Coincidencia exacta por nombre normalizado
  if (!serie) {
    for (const s of seriesCache.values()) {
      if (normalize(s.name) === queryNorm) {
        serie = s;
        break;
      }
    }
  }

  // 3) Coincidencia por alias (db.seriesAliases)
  if (!serie && db.seriesAliases) {
    for (const [official, aliases] of Object.entries(db.seriesAliases)) {
      if (!Array.isArray(aliases)) continue;
      if (aliases.some(a => normalize(a) === queryNorm)) {
        for (const s of seriesCache.values()) {
          if (normalize(s.name) === normalize(official)) {
            serie = s;
            break;
          }
        }
        if (serie) break;
      }
    }
  }

  // 4) Fallback: smart search
  if (!serie) {
    serie = smartSearch(
      [...seriesCache.values()],
      queryRaw,
      s => s.name
    );
  }

  if (!serie) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          'La serie *' + queryRaw + '* no existe.\n' +
          '> Usa `/suggest` para sugerirla.'
      },
      { quoted: msg }
    );
  }

  const chars = [];
  for (const key of serie.characters) {
    const c = characterKeyMap.get(key);
    if (c) chars.push(c);
  }

  chars.sort((a, b) => (Number(b.value) || 0) - (Number(a.value) || 0));

  const total = chars.length;
  const claimed = chars.filter(c => c.claimedBy?.[groupId]).length;
  const percent = total ? ((claimed / total) * 100).toFixed(1) : '0';

  let text =
    '\u276C Nombre: "<' + serie.name + '>"\n\n' +
    '\u274F Personajes \u00BB ' + total + '\n' +
    '\u2661 Reclamados \u00BB ' + claimed + '/' + total + ' (' + percent + '%)\n\n' +
    '\u274F Lista de personajes:\n\n';

  for (const c of chars) {
    const owner = c.claimedBy?.[groupId];
    const ownerData = owner ? db.users?.[owner.user] : null;
    const ownerName =
      ownerData?.name ||
      (owner?.user ? String(owner.user).split('@')[0] : 'Usuario');
    const estado = owner ? 'Reclamado por ' + ownerName : 'Libre';
    text += '\u00BB ' + c.name + ' (' + (c.value || 0) + ') \u2022 ' + estado + '\n';
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}
export async function handleSetSerie(
  sock,
  msg,
  args,
  sender
){

  if(
    !isMainOwnerId(sender) &&
    !isSecondaryOwnerId(sender)
  ) return;

  const raw =
    args.join(' ');

  const parts =
    raw
      .split('/')
      .map(x=>x.trim())
      .filter(Boolean);

  if(parts.length < 2){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/setserie Nombre oficial / Alias 1 / Alias 2

Ejemplo

/setserie Zenless Zone Zero / zzz / zenless`
      },
      { quoted: msg }
    );

  }

  const official =
    parts.shift();

  db.seriesAliases[official] =
    parts.map(x=>x.toLowerCase());

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`✓ Alias guardados

◇ Serie »
${official}

□ Alias

${parts.map(x=>"• "+x).join("\n")}`
    },
    { quoted: msg }
  );

}

export async function handleDelNameSerie(
  sock,
  msg,
  args,
  sender
){

  if(
    !isMainOwnerId(sender) &&
    !isSecondaryOwnerId(sender)
  ) return;

  const alias =
    args
      .slice(1)
      .join(' ')
      .toLowerCase()
      .trim();

  if(!alias){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso:\n/delnameserie alias'
      },
      { quoted: msg }
    );

  }

  let found = false;

  for(const serie in db.seriesAliases){

    const list =
      db.seriesAliases[serie];

    const index =
      list.indexOf(alias);

    if(index !== -1){

      list.splice(index,1);

      found = true;

      if(!list.length)
        delete db.seriesAliases[serie];

      break;

    }

  }

  if(!found){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Alias no encontrado.'
      },
      { quoted: msg }
    );

  }

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Alias eliminado

${alias}`
    },
    { quoted: msg }
  );

}

export async function handleIdSerie(
  sock,
  msg,
  args,
  sender
){
  const nombreBuscado =
    args.join(' ')
      .trim()
      .toLowerCase();
  if (!nombreBuscado) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso: /idserie nombre de la serie'
      },
      { quoted: msg }
    );
  }
  const serie =
    seriesCache.get(
      nombreBuscado
    );
  if (!serie) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Serie no encontrada » ${args.join(' ').trim()}`
      },
      { quoted: msg }
    );
  }
  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Serie » ${serie.name}
◇ ID » ${serie.id}`
    },
    { quoted: msg }
  );
}
export async function handleInfoSerie(
  sock,
  msg,
  args,
  sender
){

  if(
    !isMainOwnerId(sender) &&
    !isSecondaryOwnerId(sender)
  ) return;

  const name =
    args.join(' ').trim();

  if(!name){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso:\n/infoserie nombre'
      },
      { quoted: msg }
    );

  }

  const aliases =
    db.seriesAliases[name];

  if(!aliases){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Serie sin alias.'
      },
      { quoted: msg }
    );

  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`❬ Serie

◇ Nombre »
${name}

□ Alias

${aliases.map(a=>"• "+a).join("\n")}`
    },
    { quoted: msg }
  );

}

// ━━━━━━━ GINFO ACTUALIZADO ━━━━━━━
export async function handleGinfo(sock, msg, groupId, sender) {
  const jid = msg.key.remoteJid;
  const backtick = '`';
  const sent = await sock.sendMessage(jid, { text: 'Cargando...' }, { quoted: msg });

  const cooldowns = getGroupCooldowns(groupId, sender);
  const now = Date.now();
  const user = initUser(sender);
  const baseCooldown = getPremiumCooldown(user);
  const reduction = Number(user.cooldownReduction || 0);
  const finalCooldown = Math.max(30000, baseCooldown - reduction);
  const rwCD = Math.max(0, finalCooldown - (now - (cooldowns.rw || 0)));
  const claimCD = Math.max(0, CLAIM_CD - (now - (cooldowns.claim || 0)));
  const voteTimestamp = db.globalCooldowns?.vote?.[sender] || 0;
  const voteCD = Math.max(0, VOTE_CD - (now - voteTimestamp));
  const rwpCD = Math.max(0, baseCooldown - (now - Number(user.lastRwp || 0)));

  const formatTime = ms =>
    Math.floor(ms / 60000) + 'm ' + Math.floor((ms % 60000) / 1000) + 's';
  const formatCooldown = ms => ms <= 0 ? 'Ahora.' : formatTime(ms);
  const eventState = getGroupEventState(groupId, now);
  let eventLabel = 'Evento';
  let eventText = 'No hay evento';
  if (eventState.status === 'scheduled') {
    eventLabel = 'Evento en';
    eventText =
      formatTime(Math.max(0, eventState.startsAt - now)) +
      ` (XP x${Number(eventState.event.multiplier) || 1}, /rw x${Number(eventState.event.luck) || 1})`;
  } else if (eventState.status === 'active') {
    eventLabel = 'Evento activo';
    eventText =
      formatTime(Math.max(0, eventState.expiresAt - now)) +
      ` (XP x${Number(eventState.event.multiplier) || 1}, /rw x${Number(eventState.event.luck) || 1})`;
  }

  const group = db.groups[groupId];
  const harem = group?.harems?.[sender] || [];
  const totalValue = harem.reduce((sum, character) => sum + (Number(character.value) || 0), 0);
  const name = db.users[sender]?.name || 'Usuario';
  const text =
    '*【 Jugador ' + name + ' 】*\n\n' +
    'ⴵ ' + eventLabel + ' » ' + backtick + eventText + backtick + '\n' +
    'ⴵ Rwp » ' + backtick + formatCooldown(rwpCD) + backtick + '\n' +
    'ⴵ RollWaifu » ' + backtick + formatCooldown(rwCD) + backtick + '\n' +
    'ⴵ Claim » ' + backtick + formatCooldown(claimCD) + backtick + '\n' +
    'ⴵ Vote » ' + backtick + formatCooldown(voteCD) + backtick + '\n\n' +
    '✫ Personajes reclamados » ' + backtick + harem.length + backtick + '\n' +
    '✰ Valor total » ' + backtick + totalValue + backtick + '\n' +
    '❏ Personajes totales » ' + backtick + charactersCache.length + backtick + '\n' +
    '❏ Series totales » ' + backtick + seriesCache.size + backtick;

  await new Promise(resolve => setTimeout(resolve, 1));
  try {
    await sock.sendMessage(jid, { text, edit: sent.key });
  } catch {
    await sock.sendMessage(jid, { text }, { quoted: msg });
  }
}

// ━━━━━━━ TRADE NUEVO ━━━━━━━
const pendingTrades = new Map();
const pendingLevelTrades = {};

export async function handleTrade(sock, msg, args, groupId, sender) {
  const text = args.join(' ').trim();
  const input = args.join(' ');
  const parts = input.split('/').map(s => s.trim());
  if (parts.length !== 2 || !parts[0] || !parts[1]) {
    return sock.sendMessage(msg.key.remoteJid, { text: '◇ Uso: /trade <personaje A> / <personaje B>' }, { quoted: msg });
  }
  const nameA = parts[0].toLowerCase();
  const nameB = parts[1].toLowerCase();

  const group = db.groups[groupId];
  if (!group || !group.harems) return;
  let charA, ownerA, charB, ownerB;
  for (const [uid, harem] of Object.entries(group.harems)) {
    if (!charA) {
      charA = harem.find(c => c.name.toLowerCase() === nameA);
      if (charA) ownerA = uid;
    }
    if (!charB) {
      charB = harem.find(c => c.name.toLowerCase() === nameB);
      if (charB) ownerB = uid;
    }
  }
  if (!charA || !charB) return sock.sendMessage(msg.key.remoteJid, { text: ' Uno o ambos personajes no están en el grupo.' }, { quoted: msg });
  if (ownerA === ownerB) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Ambos personajes pertenecen al mismo usuario.' }, { quoted: msg });

  const tradeId = `${sender}_${Date.now()}`;
  pendingTrades.set(tradeId, { from: sender, to: (sender === ownerA) ? ownerB : ownerA, giveKey: charA.key, receiveKey: charB.key, groupId, timestamp: Date.now() });

  await sock.sendMessage(msg.key.remoteJid, {
    text: `❬ Solicitud de intercambio\n\n` +
      `@${sender.split('@')[0]} quiere intercambiar:\n\n` +
      `♡ ${charA.name}\n→•\n♡ ${charB.name}\n\n` +
      `@${((sender === ownerA) ? ownerB : ownerA).split('@')[0]} responde:\n` +
      `"aceptar" citando este mensaje`,
    mentions: [sender, (sender === ownerA) ? ownerB : ownerA]
  }, { quoted: msg });

  setTimeout(() => { pendingTrades.delete(tradeId); }, 120000);
}

async function checkTradeAccept(sock, msg, sender) {
  const text = msg.message?.conversation || msg.message?.extendedTextMessage?.text || '';
  if (text.toLowerCase() !== 'aceptar') return false;
  const quotedMsg = msg.message?.extendedTextMessage?.contextInfo?.quotedMessage;
  if (!quotedMsg) return false;
  for (const [id, trade] of pendingTrades) {
    if (trade.to === sender && Date.now() - trade.timestamp < 120000) {
      const group = db.groups[trade.groupId];
      if (!group || !group.harems) continue;
      const haremFrom = group.harems[trade.from] || [];
      const haremTo = group.harems[trade.to] || [];
      const charA = haremFrom.find(c => c.key === trade.giveKey);
      const charB = haremTo.find(c => c.key === trade.receiveKey);
      if (!charA || !charB) {
        await sock.sendMessage(msg.key.remoteJid, { text: ' Alguno de los personajes ya no está disponible.' }, { quoted: msg });
        pendingTrades.delete(id);
        return true;
      }
      haremFrom.splice(haremFrom.indexOf(charA), 1);
      haremTo.splice(haremTo.indexOf(charB), 1);
      haremFrom.push(charB);
      haremTo.push(charA);
      if (global.ownerIndex[trade.groupId]) {
        global.ownerIndex[trade.groupId][trade.from]?.delete(trade.giveKey);
        global.ownerIndex[trade.groupId][trade.to]?.delete(trade.receiveKey);
        if (!global.ownerIndex[trade.groupId][trade.from]) global.ownerIndex[trade.groupId][trade.from] = new Set();
        if (!global.ownerIndex[trade.groupId][trade.to]) global.ownerIndex[trade.groupId][trade.to] = new Set();
        global.ownerIndex[trade.groupId][trade.from].add(trade.receiveKey);
        global.ownerIndex[trade.groupId][trade.to].add(trade.giveKey);
      }
      const cA = characterKeyMap.get(trade.giveKey);
      const cB = characterKeyMap.get(trade.receiveKey);
      if (cA?.claimedBy?.[trade.groupId]?.user === trade.from) cA.claimedBy[trade.groupId].user = trade.to;
      if (cB?.claimedBy?.[trade.groupId]?.user === trade.to) cB.claimedBy[trade.groupId].user = trade.from;
      saveCharacters();
      saveDB();
      pendingTrades.delete(id);
      await sock.sendMessage(msg.key.remoteJid, { text: `? ¡Intercambio realizado! ${charA.name} →” ${charB.name}`, mentions: [trade.from, trade.to] }, { quoted: msg });
      return true;
    }
  }
  return false;
}

async function checkHarem100Reward(sock, msg, groupId, sender) {
  const user = initUser(sender);

  if (!user) return;

  const harem = db.groups[groupId]?.harems?.[sender] || [];

  // Ya recibió la recompensa
  if (user.harem100Reward === true) return;

  // Todavía no tiene 100 personajes
  if (harem.length < 100) return;

  // ==========================================
  // RECOMPENSA POR 100 PERSONAJES
  // ==========================================

  user.harem100Reward = true;

  // 25.000.000 de gemas
  user.gems = (Number(user.gems) || 0) + 25000000;

  // x2 permanente de Coinsg
  user.coinsgMultiplier = 2;

  // -14 minutos para /rw y /rwp
  const reduction = 14 * 60 * 1000;

  const economy = getGroupEconomy(groupId, sender);

  economy.timeReduction =
    (Number(economy.timeReduction) || 0) + reduction;

  saveDB();

  const mention = `@${sender.split('@')[0]}`;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`${mention} haz desbloqueado: \`Ten 100 personajes en tu harem\`

*Recompesa:*

*Pase Vip: 25.000.000 Gemas obtuviste*
> *Obtuviste un x2 permanente de coinsg*
> *Obtuviste -14 minutos para /rw y /rwp*`,
      mentions: [sender]
    }
  );
}


export async function handleGiveAllHarem(
  sock,
  msg,
  args,
  jid,
  sender
) {

  /*
   * GIVEALLHAREM USA EL MISMO HAREM QUE /HAREM.
   *
   * /harem utiliza:
   *
   * db.groups[groupId].harems[user]
   *
   * Por lo tanto NO debemos utilizar:
   *
   * db.users[user].harem
   */

  const groupId = jid;

  db.groups ??= {};
  db.groups[groupId] ??= {};
  db.groups[groupId].harems ??= {};

  const contextInfo =
    msg?.message?.extendedTextMessage?.contextInfo || {};

  const mentioned =
    Array.isArray(contextInfo.mentionedJid)
      ? contextInfo.mentionedJid
      : [];

  const target = mentioned[0];

  console.log(
    '[PFP-TARGET-DIAG]',
    JSON.stringify(target)
  );


  if (!target) {

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ Debes mencionar a quien quieras regalarle tu harem."
      },
      {
        quoted: msg
      }
    );

  }

  if (String(target) === String(sender)) {

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No puedes regalarte tu propio harem."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * OBTENER EL HAREM REAL DEL GRUPO
   */

  db.groups[groupId].harems[sender] ??= [];
  db.groups[groupId].harems[target] ??= [];

  const harem =
    db.groups[groupId].harems[sender];

  if (!Array.isArray(harem)) {

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No se pudo leer tu harem."
      },
      {
        quoted: msg
      }
    );

  }

  if (harem.length === 0) {

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No tienes personajes en tu harem para regalar."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * COPIA DEL HAREM.
   *
   * No modificamos el original hasta confirmar.
   */

  const personajes =
    harem.map(c => {

      if (typeof c === "string") {
        return c;
      }

      return c?.key || c?.id || null;

    }).filter(Boolean);

  if (personajes.length === 0) {

    return sock.sendMessage(
      jid,
      {
        text:
          " Tu harem no contiene personajes válidos."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * CALCULAR VALOR REAL
   */

  let valorTotal = 0;

  for (const key of personajes) {

    const character =
      characterKeyMap?.get?.(key);

    if (!character) continue;

    const value = Number(
      character.value ??
      character.valor ??
      character.price ??
      character.precio ??
      0
    );

    if (Number.isFinite(value)) {
      valorTotal += value;
    }

  }

  const nombreTarget =
    db.users?.[target]?.name ||
    target.split("@")[0];

  const nombreSender =
    db.users?.[sender]?.name ||
    sender.split("@")[0];

  /*
   * CREAR SOLICITUD
   */

  global.giveAllHaremPending ??= new Map();

  const solicitudId =
    String(groupId) +
    ":" +
    String(sender) +
    ":" +
    String(Date.now());

  const solicitud = {

    id: solicitudId,

    groupId: groupId,

    jid: jid,

    sender: sender,

    target: target,

    characters: personajes,

    harem: personajes,

    cantidad: personajes.length,

    totalValue: valorTotal,

    valorTotal: valorTotal,

    timestamp: Date.now(),

    expiresAt:
      Date.now() + 30000

  };

  global.giveAllHaremPending.set(
    solicitudId,
    solicitud
  );

  /*
   * EXPIRACIÓN
   */

  solicitud.timeout = setTimeout(
    async () => {

      const actual =
        global.giveAllHaremPending.get(
          solicitudId
        );

      if (!actual) return;

      global.giveAllHaremPending.delete(
        solicitudId
      );

      try {

        await sock.sendMessage(
          jid,
          {
            text:
              "◇ La solicitud de intercambio ha expirado."
          }
        );

      } catch (e) {

        console.log(
          "⚠️ Error expirando GIVEALLHAREM:",
          e.message
        );

      }

    },
    30000
  );

  /*
   * MENSAJE DE CONFIRMACIÓN
   */

  const texto = [

    "「♡」 @" +
      sender.split("@")[0] +
      ", Estás seguro que deseas regalar todos tus personajes a *@"
      + nombreTarget +
      "*☆",

    "",

    "☆ Personajes a regalar: *" +
      personajes.length +
      "*",

    "☆ Valor total: *" +
      valorTotal.toLocaleString("en-US") +
      "*",

    "",

    '> Para confirmar responde a este mensaje con "Aceptar".'

  ].join("\n");

  return sock.sendMessage(
    jid,
    {
      text: texto,

      mentions: [
        sender,
        target
      ]
    },
    {
      quoted: msg
    }
  );

}


export async function handleGiveAllHaremConfirm(
  sock,
  msg,
  jid,
  sender,
  body
) {
  global.giveAllHaremPending ??= new Map();

  const texto = String(body ?? "")
    .trim()
    .toLowerCase();

  if (texto !== "aceptar") {
    return false;
  }

  const contextInfo =
    msg?.message?.extendedTextMessage?.contextInfo || {};

  const quotedParticipant =
    contextInfo.participant || null;

  let solicitud = null;
  let solicitudId = null;

  for (const [id, data] of global.giveAllHaremPending.entries()) {

    if (!data) continue;

    if (String(data.sender) !== String(sender)) {
      continue;
    }

    if (
      quotedParticipant &&
      String(quotedParticipant) !== String(data.sender)
    ) {
      continue;
    }

    solicitud = data;
    solicitudId = id;
    break;
  }

  if (!solicitud) {
    return false;
  }

  global.giveAllHaremPending.delete(solicitudId);

  if (solicitud.timeout) {
    clearTimeout(solicitud.timeout);
  }

  const groupId =
    solicitud.groupId ||
    solicitud.jid ||
    jid;

  db.groups ??= {};

  const group = db.groups[groupId];

  if (!group) {

    await sock.sendMessage(
      jid,
      {
        text: "☆ No se pudo completar la transferencia.\n\n◇ El grupo no fue encontrado."
      },
      { quoted: msg }
    );

    return true;
  }

  group.harems ??= {};

  const haremOrigen =
    Array.isArray(group.harems[sender])
      ? group.harems[sender]
      : [];

  const haremDestino =
    Array.isArray(group.harems[solicitud.target])
      ? group.harems[solicitud.target]
      : [];

  const solicitados =
    Array.isArray(solicitud.harem)
      ? solicitud.harem
      : [];

  if (!solicitados.length) {

    await sock.sendMessage(
      jid,
      {
        text: "❌ No hay personajes para transferir."
      },
      { quoted: msg }
    );

    return true;
  }

  const keys = new Set();

  for (const item of solicitados) {

    if (typeof item === "string") {
      keys.add(item);
      continue;
    }

    if (item && typeof item === "object" && item.key) {
      keys.add(item.key);
    }
  }

  const transferidos = [];

  for (const personaje of haremOrigen) {

    const key =
      typeof personaje === "string"
        ? personaje
        : personaje?.key;

    if (key && keys.has(key)) {
      transferidos.push(personaje);
    }
  }

  if (!transferidos.length) {

    await sock.sendMessage(
      jid,
      {
        text: "☆ No se encontraron los personajes en tu harem.\n\n◇ La transferencia fue cancelada."
      },
      { quoted: msg }
    );

    return true;
  }

  const destinoKeys = new Set(
    haremDestino
      .map(p => typeof p === "string" ? p : p?.key)
      .filter(Boolean)
  );

  for (const personaje of transferidos) {

    const key =
      typeof personaje === "string"
        ? personaje
        : personaje?.key;

    if (!key) continue;

    if (!destinoKeys.has(key)) {
      haremDestino.push(personaje);
      destinoKeys.add(key);
    }
  }

  const transferKeys = new Set(
    transferidos
      .map(p => typeof p === "string" ? p : p?.key)
      .filter(Boolean)
  );

  group.harems[sender] =
    haremOrigen.filter(personaje => {

      const key =
        typeof personaje === "string"
          ? personaje
          : personaje?.key;

      return !transferKeys.has(key);
    });

  global.ownerIndex ??= {};
  global.ownerIndex[groupId] ??= {};

  global.ownerIndex[groupId][sender] ??= new Set();
  global.ownerIndex[groupId][solicitud.target] ??= new Set();

  for (const key of transferKeys) {

    global.ownerIndex[groupId][sender].delete(key);
    global.ownerIndex[groupId][solicitud.target].add(key);

    const character =
      characterKeyMap?.get(key);

    if (character) {
      character.claimedBy ??= {};
      character.claimedBy[groupId] = {
        user: solicitud.target
      };
    }
  }

  try {
    if (typeof saveCharacters === "function") {
      saveCharacters();
    }
  } catch (e) {
    console.log("⚠️ Error saveCharacters:", e.message);
  }

  try {
    if (typeof saveDB === "function") {
      saveDB();
    }
  } catch (e) {
    console.log("⚠️ Error saveDB:", e.message);
  }

  let valorTotal = 0;

  for (const personaje of transferidos) {

    const key =
      typeof personaje === "string"
        ? personaje
        : personaje?.key;

    const character =
      characterKeyMap?.get(key);

    valorTotal += Number(
      character?.value ??
      personaje?.value ??
      0
    );
  }

  const nombreTarget =
    db.users?.[solicitud.target]?.name ||
    solicitud.target.split("@")[0];

  const mensaje =
    " Has regalado con ï¿½xito todos tus personajes a *@" +
    nombreTarget +
    "*\n\n" +
    "> ♤ \\`Personajes regalados:\\` *" +
    transferidos.length +
    "*\n" +
    "> ₩ \\`Valor total:\\` *" +
    valorTotal.toLocaleString("en-US") +
    "*";

  await sock.sendMessage(
    jid,
    {
      text: mensaje,
      mentions: [
        sender,
        solicitud.target
      ]
    },
    { quoted: msg }
  );

  return true;
}

// ━━━━━━━ HAREM, DELWAIFU, WINFO, WTOP, WIMAGE, WAIFUVIDEO ━━━━━━━
export async function handleHarem(sock, msg, groupId, sender, args, mentioned) {
  let target = mentioned.length ? mentioned[0] : sender;
  const harem = db.groups[groupId]?.harems?.[target] || [];
  if (!harem.length) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Sin personajes reclamados.' }, { quoted: msg });
  const page = parseInt((args || []).find(a => /^\d+$/.test(a))) || 1;
  const perPage = 10;
  const sorted = [...harem].sort((a, b) => b.value - a.value);
  const total = sorted.length;
  const pages = Math.ceil(total / perPage);
  const slice = sorted.slice((page-1)*perPage, page*perPage);
  let totalCoinsGen = 0;

for (const char of harem) {

    const original =
  characterKeyMap.get(char.key);

totalCoinsGen +=
  Number(original?.coinGen || 0);

}

const username =
  db.users[target]?.name ||
  'Usuario';

  let txt =
`◇ Harem de ${username}

□ Personajes » ${harem.length}
◇ Ganancia » ${totalCoinsGen.toLocaleString()}/h coins

`;
  slice.forEach(c => {
  txt += `» *${c.name}* (${c.value})\n`;
});
  txt += `\n> ⌦ _Pagina *${page}* de *${pages}*_`;
  await sock.sendMessage(
  msg.key.remoteJid,
  { text: txt },
  { quoted: msg }
);

}

export async function handleDelwaifu(sock, msg, args, groupId, sender) {
  const name = args.join(' ').toLowerCase();
  if (!name) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Uso: /delwaifu [nombre]' }, { quoted: msg });
  const harem = db.groups[groupId]?.harems?.[sender] || [];
  const idx = harem.findIndex(c => c.name.toLowerCase().includes(name));
  if (idx === -1) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No tienes ese personaje.' }, { quoted: msg });
  const removed = harem.splice(idx, 1)[0];
  const char = characterKeyMap.get(removed.key);
  if (char?.claimedBy?.[groupId]?.user === sender) {
    delete char.claimedBy[groupId];
    if (global.ownerIndex[groupId]?.[sender]) global.ownerIndex[groupId][sender].delete(removed.key);
    saveCharacters();
  }
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `☆ *${removed.name}* ha sido eliminado de tu lista.` }, { quoted: msg });
}

export async function handleWinfo(
  sock,
  msg,
  query,
  groupId
) {
  if (!query) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso: /winfo nombre'
      },
      {
        quoted: msg
      }
    );
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
'Buscando personaje...'
    },
    {
      quoted: msg
    }
  );

  const q =
    query.toLowerCase().trim();

  const char =
    findCharacter(q);

  if (!char) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'● Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );
  }

  const owner =
    char.claimedBy?.[groupId]
      ?.user || null;

  const estado =
    owner
      ? (
          db.users?.[owner]?.name ||
          owner.split('@')[0]
        )
      : 'Libre';

  const creatorName =
    getCharacterCreatorName(char);

  const coinsg =
    char.coinGen || 0;

    const oddsLine =
    char.displayOdds
      ? `\n◇ *Probabilidad* » \`1 en ${Number(char.displayOdds).toLocaleString('en-US')}\``
      : '';

  const cap =
`◇ *Nombre* » \`${char.name}\`
☆ *Anime* » \`${char.anime}\`
■ *Género* » *${char.gender || 'Desconocido'}*
♡ *Estado* » *${estado}*
$ *Coinsg* » *\`${coinsg}\` */hora*

♡ *Rareza* » \`${char.rarity || 'Comun'}\`
? *Valor* » \`¥${Number(char.value).toLocaleString()}\`
▪︎  *Chance* » \`${char.chance || '100%'}\`
★ *Creador* » \`${creatorName}\`${oddsLine}`;

  try {

    const imageData =
  await getCharacterMedia(char);

    if (imageData) {

      return sock.sendMessage(
        msg.key.remoteJid,
        {
          ...imageData,
          caption: cap
        },
        {
          quoted: msg
        }
      );

    }

  } catch (e) {
    console.log(
      'WINFO IMG ERROR:',
      e
    );
  }

  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text: cap
    },
    {
      quoted: msg
    }
  );
}

export async function handleWtop(sock, msg, args) {
  const page = parseInt(args[0]) || 1;
  const perPage = 10;
  const chars = [...charactersCache].sort((a, b) => b.value - a.value);
  if (!chars.length) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No hay personajes.' }, { quoted: msg });
  const pages = Math.ceil(chars.length / perPage);
  const slice = chars.slice((page - 1) * perPage, page * perPage);
  let text = `❬ Personajes con mas valor:\n\n`;
  slice.forEach((c, i) => text += `✰ ${(page - 1) * perPage + i + 1} » *${c.name}*\n→ Valor: *${c.value || 0}*\n\n`);
  text += `\n> ï¿½ Página *${page}* de *${pages}*`;
  const first = slice[0];

if (first) {
    try {
        const imageData = await getCharacterMedia(first);

        if (imageData) {
            return await sock.sendMessage(
                msg.key.remoteJid,
                {
                    ...imageData,
                    caption: text
                },
                { quoted: msg }
            );
        }
    } catch (e) {
        console.log("WTOP IMG ERROR:", e);
    }
}

await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
);
}

export async function handleProfile(
  sock,
  msg,
  groupId,
  target
) {
  const design = db.commandDesigns.profile || {};
  const title = design.title || '𝐏𝐞𝐫𝐟𝐢𝐥';
  const separator = design.separator || '';

  const user = initUser(target);

  const eco =
    getGroupEconomy(
      groupId,
      target
    );

  const harem =
    db.groups[groupId]?.harems?.[target] || [];

  const haremValue =
    harem.reduce(
      (a,c)=>
        a + (c.value || 0),
      0
    );

  const users =
    Object.entries(db.users)
      .sort(
        (a,b)=>
          (b[1].xp||0) -
          (a[1].xp||0)
      );

  const rank =
    users.findIndex(
      x => x[0] === target
    ) + 1;

  let birthday =
    'No definido';

  if (
    user.birthday &&
    user.birthday.day &&
    user.birthday.month
  ) {

    birthday =
      formatBirthday(
        user.birthday.day,
        user.birthday.month
      );
  }

  const xp =
  user.xp || 0;

const level =
  user.level || 1;

const currentLevelXp =
  xpForLevel(level);

const nextLevelXp =
  xpForLevel(level + 1);

const xpInLevel =
  Math.max(
    0,
    xp - currentLevelXp
  );

const xpNeeded =
  nextLevelXp -
  currentLevelXp;

const progress =
  Math.max(
    0,
    Math.floor(
      (xpInLevel / xpNeeded) * 100
    )
  );

const marriageText =
  user.marriedTo
    ? `\n✿ Pareja ⁝ <${db.users[user.marriedTo]?.name || 'Usuario'}>`
    : '';

const text =
`⋆｡°✩ ──「 𝐏𝐞𝐫𝐟𝐢𝐥 」── ✩°｡⋆
♡ 𝑴𝒂𝒚 ♡

₊˚๑ 𝐈𝐧𝐟𝐨𝐫𝐦𝐚𝐜𝐢𝐨́𝐧 ๑˚₊
✿ Cumpleaños ⁝ *${birthday}*
✿ Género ⁝ *${user.gender || 'No definido'}*${marriageText}

₊˚๑ 𝐄𝐬𝐭𝐚𝐝𝐨 ๑˚₊
❀ Nivel ⁝ *${level}*
❀ Experiencia ⁝ *${xp.toLocaleString()}*
❀ Progreso ⁝ *${xp} → ${nextLevelXp}* _(${progress}%)_
❀ Puesto ⁝ *#${rank}*

₊˚๑ 𝐂𝐨𝐥𝐞𝐜𝐜𝐢𝐨́𝐧 ๑˚₊
❁ Harem ⁝ *${harem.length}*
❁ Valor total ⁝ *${haremValue.toLocaleString()}*

₊˚๑ 𝐀𝐜𝐭𝐢𝐯𝐢𝐝𝐚𝐝 ๑˚₊
✧ Coins ⁝ *${(eco.coins || 0).toLocaleString()} ${getBotCurrency(sock)}*
✧ Comandos ⁝ *${(user.totalCommands || 0).toLocaleString()}*`;

  let pp = null;

  const profileNormalizeJid = value => {
    if (!value) return '';
    return String(value).trim();
  };

  let photoTarget =
    profileNormalizeJid(target);

  try {
    if (
      photoTarget &&
      photoTarget.toLowerCase().endsWith("@lid") &&
      groupId &&
      groupId.endsWith("@g.us")
    ) {
      const metadata =
        await sock.groupMetadata(groupId);

      console.log(
        '[PROFILE-PHOTO-DIAG] target:',
        photoTarget
      );

      console.log(
        '[PROFILE-PHOTO-DIAG] participantes:',
        metadata?.participants?.length || 0
      );

      const participant =
        metadata?.participants?.find(p => {
          const ids = [
            p?.id,
            p?.jid,
            p?.phoneNumber,
            p?.lid
          ]
            .filter(Boolean)
            .map(profileNormalizeJid);

          return ids.includes(photoTarget);
        });

      console.log(
        '[PROFILE-PHOTO-DIAG] participant:',
        participant
          ? JSON.stringify(participant)
          : 'NO ENCONTRADO'
      );

      if (participant) {
        const possibleValues = [
          participant.phoneNumber,
          participant.jid,
          participant.id
        ];

        for (const value of possibleValues) {
          if (!value) continue;

          const normalized =
            profileNormalizeJid(value);

          if (
            normalized &&
            !normalized.toLowerCase().endsWith("@lid")
          ) {
            photoTarget = normalized;
            break;
          }
        }
      }
    }

    console.log(
      '[PROFILE-PHOTO-DIAG] LID original:',
      target
    );

    console.log(
      '[PROFILE-PHOTO-DIAG] JID resuelto:',
      photoTarget
    );

    pp =
      await getBestProfilePhoto(
        target,
        sock
      );

    console.log(
      '[PROFILE-PHOTO-DIAG] foto con LID:',
      !!pp,
      pp || null
    );

    if (!pp && photoTarget !== target) {
      pp =
        await getBestProfilePhoto(
          photoTarget,
          sock
        );

      console.log(
        '[PROFILE-PHOTO-DIAG] foto con JID:',
        !!pp,
        pp || null
      );
    }
  } catch (error) {
    console.log(
      '[PROFILE-PHOTO-DIAG] error general:',
      error?.message
    );
  }

  if (pp) {

    await sock.sendMessage(
        msg.key.remoteJid,
        {
            image: { url: pp },
            caption: text
        },
        { quoted: msg }
    );

} else {

    await sock.sendMessage(
        msg.key.remoteJid,
        {
            text
        },
        { quoted: msg }
    );

}
}

export async function handleTopCoinsG(
  sock,
  msg,
  args,
  groupId
) {

  const page =
    Math.max(
      1,
      parseInt(args[0]) || 1
    );

  const users = [];

  const groupData =
    db.groups?.[groupId];

  if (!groupData) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ No hay datos.'
      },
      { quoted: msg }
    );

  }

  for (
    const [userId, chars]
    of Object.entries(
      groupData.harems || {}
    )
  ) {

    let total = 0;

    for (const char of chars) {

  const original =
    characterKeyMap.get(char.key);

  total += Number(
    original?.coinGen || 0
  );

}

    users.push({

      id: userId,

      total,

      chars:
        chars.length

    });

  }

  users.sort(
    (a,b) =>
      b.total - a.total
  );

  const perPage = 10;

  const totalPages =
    Math.max(
      1,
      Math.ceil(
        users.length /
        perPage
      )
    );

  const start =
    (page - 1) *
    perPage;

  const slice =
    users.slice(
      start,
      start + perPage
    );

  let txt =
`◇ Top Generaci¿n

 Página ï¿½ ${page}/${totalPages}

`;

  let pos = start + 1;

for (const user of slice) {

  const username =
    db.users?.[user.id]?.name ||
    user.id.split('@')[0];

  txt +=
`${pos}° ${username}

◇ ${user.total.toLocaleString()}/h
□ ${user.chars} personajes

`;

  pos++;
}

  await sock.sendMessage(
    msg.key.remoteJid,
    { text: txt },
    { quoted: msg }
  );

}

export async function handleTopRachas(sock, msg, args) {

  const page = Math.max(
    1,
    parseInt(args[0]) || 1
  );

  const perPage = 10;
  const now = Date.now();
  let changed = false;

  const users = Object.entries(db.users || {})
    .filter(([_, u]) => {

      if (
        u.lastDailyGlobal &&
        !isDailyStreakAlive(u, now) &&
        (u.dailyStreak || 0) > 0
      ) {
        u.dailyStreak = 0;
        changed = true;
      }

      return (u.dailyStreak || 0) > 0;
    })
    .sort(
      (a, b) =>
        (b[1].dailyStreak || 0) -
        (a[1].dailyStreak || 0)
    );

  if (changed) {
    saveDB();
  }

  if (!users.length) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`✧₊˚⊹♡  ᴛᴏᴘ ʀᴀᴄʜᴀs ᴅᴀɪʟʏ (ɢʟᴏʙᴀʟ) ♡⊹˚₊✧

> ✧  ɴᴏ ʜᴀʏ ʀᴀᴄʜᴀs ʀᴇɢɪsᴛʀᴀᴅᴀs ✧`
      },
      { quoted: msg }
    );
  }

  const pages =
    Math.ceil(
      users.length / perPage
    );

  const currentPage =
    Math.min(page, pages);

  const slice =
    users.slice(
      (currentPage - 1) * perPage,
      currentPage * perPage
    );

  let text =
`✧₊˚⊹♡  ᴛᴏᴘ ʀᴀᴄʜᴀs ᴅᴀɪʟʏ (ɢʟᴏʙᴀʟ) ♡⊹˚₊✧

`;

  let pos =
    (currentPage - 1) * perPage + 1;

  const numberStyles = [
    '➊',
    '➋',
    '➌',
    '➍',
    '➎',
    '➏',
    '➐',
    '➑',
    '➒',
    '➓'
  ];

  for (const [uid, user] of slice) {

    const coins =
      Object.values(db.groups || {})
        .reduce(
          (sum, g) =>
            sum +
            (g.economy?.[uid]?.coins || 0),
          0
        );

    const rank =
      numberStyles[
        (pos - 1) % 10
      ];

    text +=
`♯ ${rank} *${user.name || 'Usuario'}*
　⁀➷ ʀᴀᴄʜᴀ ${user.dailyStreak || 0} ᴅɪᴀs ⋆ ᴄᴏɪɴs ${coins.toLocaleString()}

`;

    pos++;
  }

  const nextPage =
    currentPage < pages
      ? `ᴜsᴀ /toprachas ${currentPage + 1}`
      : 'ᴜʟᴛɪᴍᴀ ᴘáɢɪɴᴀ';

  text +=
`> ✧  ᴘáɢɪɴᴀ ${currentPage}/${pages} ${nextPage} ✧`;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}

export async function handleTestTag(
  sock,
  msg,
  args
){

  const query =
    args.join(' ').trim();

  if (!query){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso:\n/testtag nombre\n/testtag id'
      },
      {
        quoted: msg
      }
    );

  }

  // Primero buscar por ID exacto; después por nombre exacto.
  // args ya contiene solo el texto posterior a /testtag.
  const char =
    charactersCache.find(
      c => String(c.id) === query
    ) ||
    charactersCache.find(
      c =>
        String(c.name || '').toLowerCase() ===
        query.toLowerCase()
    );

  if (!char){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  const creatorName =
    getCharacterCreatorName(char);

  const fecha =
    char.createdAt
    ? new Date(char.createdAt)
    : new Date();

  const fechaTxt =
    fecha.toLocaleDateString(
      'es-CL'
    );

  const manualImage =
    await getManualCharacterImage(char.tag);
  const imgUrl = manualImage
    ? null
    : await getGelbooruImage(char.tag);

  const caption =
`❬ Información del Personaje

□ *ID* » \`${char.id}\`
◇ *Nombre* » \`${char.name}\`
☆ *Anime* » \`${char.anime}\`
♧ *Tag* » \`${char.tag || 'Sin tag'}\`

♡ *Rareza* » \`${char.rarity}\`
? *Valor* » \`¥${Number(char.value || 0).toLocaleString()}\`
▪︎ *Chance* » \`${char.chance || '100%'}\`

□ *Creado por* »
@${creatorName}

◇ *Fecha* »
\`${fechaTxt}\``;

  if (manualImage) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        ...manualImage,
        caption
      },
      {
        quoted: msg
      }
    );
  }

  if (imgUrl){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        image: {
          url: imgUrl
        },
        caption
      },
      {
        quoted: msg
      }
    );

  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text: caption
    },
    {
      quoted: msg
    }
  );

}

function formatWimageSize(bytes) {
  if (!Number.isFinite(bytes) || bytes < 0)
    return 'Desconocido';

  if (bytes < 1024)
    return `${bytes} B`;

  if (bytes < 1024 ** 2)
    return `${(bytes / 1024).toFixed(2).replace(/\.00$/, '')} KB`;

  if (bytes < 1024 ** 3)
    return `${(bytes / 1024 ** 2).toFixed(2).replace(/\.00$/, '')} MB`;

  return `${(bytes / 1024 ** 3).toFixed(2).replace(/\.00$/, '')} GB`;
}

function getWimageResolution(buffer) {
  if (!Buffer.isBuffer(buffer) || buffer.length < 10)
    return 'Desconocida';

  // PNG
  if (
    buffer.length >= 24 &&
    buffer.toString('ascii', 1, 4) === 'PNG'
  ) {
    return `${buffer.readUInt32BE(16)}x${buffer.readUInt32BE(20)}`;
  }

  // GIF
  if (
    buffer.length >= 10 &&
    (
      buffer.toString('ascii', 0, 6) === 'GIF87a' ||
      buffer.toString('ascii', 0, 6) === 'GIF89a'
    )
  ) {
    return `${buffer.readUInt16LE(6)}x${buffer.readUInt16LE(8)}`;
  }

  // WebP
  if (
    buffer.length >= 30 &&
    buffer.toString('ascii', 0, 4) === 'RIFF' &&
    buffer.toString('ascii', 8, 12) === 'WEBP'
  ) {
    const type = buffer.toString('ascii', 12, 16);

    if (type === 'VP8X' && buffer.length >= 30) {
      const width =
        1 +
        buffer[24] +
        (buffer[25] << 8) +
        (buffer[26] << 16);

      const height =
        1 +
        buffer[27] +
        (buffer[28] << 8) +
        (buffer[29] << 16);

      return `${width}x${height}`;
    }
  }

  // JPEG
  if (
    buffer.length >= 2 &&
    buffer[0] === 0xff &&
    buffer[1] === 0xd8
  ) {
    let offset = 2;

    while (offset + 9 < buffer.length) {
      if (buffer[offset] !== 0xff) {
        offset++;
        continue;
      }

      while (
        offset < buffer.length &&
        buffer[offset] === 0xff
      ) {
        offset++;
      }

      const marker = buffer[offset++];

      if (
        marker === 0xd8 ||
        marker === 0xd9
      ) {
        continue;
      }

      if (offset + 1 >= buffer.length)
        break;

      const segmentLength =
        buffer.readUInt16BE(offset);

      if (segmentLength < 2)
        break;

      const isSOF =
        (marker >= 0xc0 && marker <= 0xc3) ||
        (marker >= 0xc5 && marker <= 0xc7) ||
        (marker >= 0xc9 && marker <= 0xcb) ||
        (marker >= 0xcd && marker <= 0xcf);

      if (
        isSOF &&
        offset + 7 < buffer.length
      ) {
        const height =
          buffer.readUInt16BE(offset + 3);

        const width =
          buffer.readUInt16BE(offset + 5);

        return `${width}x${height}`;
      }

      offset += segmentLength;
    }
  }

  return 'Desconocida';
}

export async function handleWimage(
  sock,
  msg,
  query
){

  if (!query)
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ Uso: /wimage [nombre]'
      },
      {
        quoted: msg
      }
    );

  const q =
    query
      .toLowerCase()
      .trim();

  const char =
    findCharacter(q);

  if (!char)
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  let imageBuffer = null;
  let mimeType = null;

  const manualImage =
    await getManualCharacterImage(char.tag);
  if (manualImage) {
    imageBuffer = manualImage.image;
    mimeType = manualImage.mimetype;
  }

  // Gelbooru y Danbooru: orden aleatorio.
  const onlineSources =
    ['gelbooru', 'danbooru']
      .sort(() => Math.random() - 0.5);

  for (const source of imageBuffer ? [] : onlineSources) {
    try {
      let imgUrl = null;

      if (source === 'gelbooru') {
        const candidates =
          await getGelbooruApiImageCandidates(
            char.tag ||
            char.name
          );

        if (
          Array.isArray(candidates) &&
          candidates.length
        ) {
          imgUrl =
            candidates[
              Math.floor(
                Math.random() *
                candidates.length
              )
            ];
        }
      }

      if (source === 'danbooru') {
        imgUrl =
          await getDanbooruImage(
            char.tag ||
            char.name
          );
      }

      if (!imgUrl)
        continue;

      const downloaded =
        source === 'danbooru'
          ? await downloadDanbooruImage(imgUrl)
          : await downloadGelbooruImage(imgUrl);

      if (
        downloaded?.buffer &&
        Buffer.isBuffer(downloaded.buffer) &&
        downloaded.buffer.length
      ) {
        imageBuffer =
          downloaded.buffer;

        mimeType =
          downloaded.mimetype ||
          null;

        break;
      }

    } catch (error) {
      console.log(
        '[WIMAGE]',
        `${source} fallo:`,
        error?.message || error
      );
    }
  }

  // Respaldo: imágenes locales.
  if (!imageBuffer) {
    const localImages =
      getCharacterImages(char.key);

    if (localImages.length) {
      const shuffled =
        [...localImages]
          .sort(() => Math.random() - 0.5);

      for (const img of shuffled) {
        try {
          const localPath =
            path.join(
              GACHA_IMAGES,
              img
            );

          const localBuffer =
            await fs.promises.readFile(
              localPath
            );

          if (
            localBuffer &&
            localBuffer.length
          ) {
            imageBuffer =
              localBuffer;

            const lower =
              img.toLowerCase();

            if (lower.endsWith('.png'))
              mimeType = 'image/png';
            else if (lower.endsWith('.webp'))
              mimeType = 'image/webp';
            else if (lower.endsWith('.gif'))
              mimeType = 'image/gif';
            else
              mimeType = 'image/jpeg';

            break;
          }

        } catch (error) {
          console.log(
            '[WIMAGE] local fallo:',
            error?.message || error
          );
        }
      }
    }
  }

  if (!imageBuffer)
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ Sin imagen.'
      },
      {
        quoted: msg
      }
    );

  const resolution =
    getWimageResolution(
      imageBuffer
    );

  const size =
    formatWimageSize(
      imageBuffer.length
    );

  const caption =
    `❀ *𝙽𝚘𝚖𝚋𝚛𝚎* » \`${char.name || 'Desconocido'}\`
⚥ *𝙶é𝚗𝚎𝚛𝚘* » \`${char.gender || 'Desconocido'}\`
❖ *𝙵𝚞𝚎𝚗𝚝𝚎* » \`${char.anime || 'Desconocido'}\`
⍟ *𝙲𝚊𝚕𝚒𝚍𝚊𝚍* » \`${resolution}\`
⌬ *𝙿𝚎𝚜𝚘*  » \`${size}\``;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      image: imageBuffer,
      mimetype:
        mimeType || 'image/jpeg',
      caption
    },
    {
      quoted: msg
    }
  );
}

export async function handlePinLegacy(
  sock,
  msg,
  query
){

  const jid =
    msg.key.remoteJid;

  if (
    !query ||
    !query.trim()
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          '◇ Uso: /pin [búsqueda]'
      },
      {
        quoted: msg
      }
    );
  }

  const search =
    query.trim();

  await sock.sendMessage(
    jid,
    {
      text:
        `🔎 Buscando en Pinterest: ${search}`
    },
    {
      quoted: msg
    }
  );

  try {

    const response =
      await axios.get(
        `https://www.bing.com/images/search?q=${encodeURIComponent(`pinterest ${search}`)}&form=HDRSC2`,
        {
          timeout: 15000,
          headers: {
            'User-Agent':
              'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/131 Safari/537.36',
            'Accept-Language':
              'es-ES,es;q=0.9,en;q=0.8'
          }
        }
      );

    const html =
      String(response.data);

    const candidates =
      [
        ...html.matchAll(
          /class="iusc"[^>]+m="([^"]+)"/gi
        )
      ]
        .map(match => {

          try {
            return JSON.parse(
              match[1]
                .replace(/&quot;/g, '"')
                .replace(/&amp;/g, '&')
            );
          } catch (error) {
            return null;
          }

        })
        .filter(result =>
          result &&
          (
            String(result.purl || '')
              .includes('pinterest.com/pin') ||
            String(result.murl || '')
              .includes('i.pinimg.com')
          )
        )
        .map(result => result.murl)
        .filter(url =>
          /^https?:\/\/.+\.(?:jpg|jpeg|png|webp)(?:\?.*)?$/i.test(url)
        );

    const imageUrls =
      [
        ...new Set(candidates)
      ].slice(0, 20);

    let sent =
      0;

    for (
      const imageUrl of imageUrls
    ) {

      if (
        sent >= 7
      ) {
        break;
      }

      try {

        const image =
          await axios.get(
            imageUrl,
            {
              responseType:
                'arraybuffer',
              timeout: 15000,
              maxContentLength:
                10 * 1024 * 1024,
              headers: {
                'User-Agent':
                  'Mozilla/5.0'
              }
            }
          );

        const contentType =
          String(
            image.headers['content-type'] ||
            ''
          ).split(';')[0].toLowerCase();

        if (
          !contentType.startsWith('image/')
        ) {
          continue;
        }

        await sock.sendMessage(
          jid,
          {
            image:
              Buffer.from(image.data),
            caption:
              sent === 0
                ? `📌 Pinterest: ${search}`
                : undefined,
            mimetype:
              contentType
          },
          {
            quoted:
              msg
          }
        );

        sent++;

      } catch (error) {

        console.warn(
          '⚠️ No se pudo descargar una imagen de Pinterest:',
          error?.message || error
        );

      }

    }

    if (
      !sent
    ) {
      return sock.sendMessage(
        jid,
        {
          text:
            '❌ No encontré imágenes disponibles para esa búsqueda.'
        },
        {
          quoted: msg
        }
      );
    }

    console.log(
      `📌 Pinterest: enviadas ${sent} imagen(es) para "${search}"`
    );

  } catch (error) {

    console.error(
      '❌ Error buscando imágenes en Pinterest:',
      error
    );

    await sock.sendMessage(
      jid,
      {
        text:
          '❌ No se pudo realizar la búsqueda en Pinterest. Intenta nuevamente.'
      },
      {
        quoted: msg
      }
    );

  }

}

export async function handlePin(
  sock,
  msg,
  query
){

  const jid =
    msg.key.remoteJid;

  if (!query || !query.trim()) {
    return sock.sendMessage(
      jid,
      {
        text: '◇ Uso: /pin [búsqueda]'
      },
      { quoted: msg }
    );
  }

  const result =
    await searchPinImages(query);

  if (!result.urls.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          '❌ No encontré imágenes seguras para esa búsqueda.'
      },
      { quoted: msg }
    );
  }

  const images =
    await downloadPinImages(
      result.urls.slice(0, 1)
    );

  if (!images.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          '❌ Los proveedores no devolvieron imágenes disponibles.'
      },
      { quoted: msg }
    );
  }

  await sock.sendMessage(
    jid,
    {
      image: images[0].buffer,
      caption:
        `📌 Resultado para: ${result.query}`
    },
    { quoted: msg }
  );

}

export async function handleSetTag(
  sock,
  msg,
  args,
  sender
){

  const raw =
  args.join(' ');

const parts =
  raw.split('/').map(
    x => x.trim()
  );

  if (parts.length < 2){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/settag Nombre / tag

Ejemplo
/settag Nazuna Nanakusa / nazuna_nanakusa`
      },
      {
        quoted: msg
      }
    );

  }

  const name =
    parts[0].trim();

  const tag =
    parts[1].trim();

  const char =
  findCharacter(name);

  if (!char){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  if (!canRepairCharacterMedia(char, sender)) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: '◇ Solo el creador, staff u owner puede corregir este personaje.' },
      { quoted: msg }
    );
  }

  const wasInvalid =
    getCharacterImages(char.key).length === 0 &&
    !(await getCharacterMedia(char));

  char.tag = tag;

  saveCharacters();

  const nowReturnsImage =
    wasInvalid &&
    !!(await getCharacterMedia(char));
  const statusAfter =
    nowReturnsImage
      ? rewardInvalidMediaRepair(char, sender)
      : null;

  if (statusAfter !== null) {
    await notifyEvents(
      sock,
      `${getStaffDisplayName(sender)} ha arreglado el personaje ${char.name} y obtuvo 5.000 de status.`,
      [sender]
    );
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Tag actualizado

❬ Nombre » ${char.name}
☆ Tag » ${tag}` +
        (statusAfter !== null
          ? `\n\n**RECOMPENSA POR ARREGLO**\n**+5.000 Status**\n**Status actual:** ${statusAfter}`
          : '')
    },
    {
      quoted: msg
    }
  );

}

export async function handleFixTag(
  sock,
  msg,
  args,
  sender
){

  if (
    !isMainOwnerId(sender) &&
    !isSecondaryOwnerId(sender)
  ){
    return;
  }

  const query =
    args.join(' ').trim();

  if (!query){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/fixtag ID
/fixtag Nombre

Ejemplo:
/fixtag 292
/fixtag Makima`
      },
      {
        quoted: msg
      }
    );

  }

  let char;

  if (/^\d+$/.test(query)){

    char =
      charactersCache.find(
        c => String(c.id) === query
      );

  } else {

    char =
      charactersCache.find(
        c =>
          c.name.toLowerCase() ===
          query.toLowerCase()
      );

  }

  if (!char){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
        '◇ Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  const search =
    (char.tag || char.name)
      .split('(')[0]
      .replace(/_/g,' ')
      .trim();

  const tags =
    await searchDanbooruTags(search);

  if (!tags.length){

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`❌ No se encontraron coincidencias.

Tag actual:
\`${char.tag || 'Sin tag'}\``
      },
      {
        quoted: msg
      }
    );

  }

  const list =
    tags
    .slice(0,3)
    .map(
      (t,i) =>
      `${i+1} » ${t.name}`
    )
    .join('\n');

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`❬ An¿lisis de tag

ID » ${char.id}
Nombre » ${char.name}

Tag actual:
\`${char.tag || 'Sin tag'}\`

Coincidencias encontradas:

${list}

Recomendado:
\`${tags[0].name}\``
    },
    {
      quoted: msg
    }
  );

}


async function saveActionGif(sock, msg, action) {

    if (!msg.message?.extendedTextMessage?.contextInfo?.quotedMessage) {

        return await sock.sendMessage(
            msg.key.remoteJid,
            {
                text: "❌ Responde a un GIF o video GIF."
            },
            { quoted: msg }
        );

    }

    const quoted = {
        key: {
            remoteJid: msg.key.remoteJid,
            id: msg.message.extendedTextMessage.contextInfo.stanzaId,
            participant: msg.message.extendedTextMessage.contextInfo.participant
        },
        message: msg.message.extendedTextMessage.contextInfo.quotedMessage
    };

    const folder = ensureActionFolder(action);

    const ext =
        quoted.message.videoMessage
            ? ".mp4"
            : quoted.message.imageMessage
            ? ".gif"
            : ".bin";

    const filename =
        `${Date.now()}${ext}`;

    const filepath =
        path.join(folder, filename);

    const stream = await downloadMediaMessage(
    quoted,
    "buffer",
    {},
    {}
);

const hash = getFileHash(stream);

actionHashes[action] ??= [];

if (actionHashes[action].includes(hash)) {

    return await sock.sendMessage(
        msg.key.remoteJid,
        {
            text: " Ese GIF ya está registrado."
        },
        { quoted: msg }
    );

}

// Recién aquí se guarda

fs.writeFileSync(
    filepath,
    stream
);

actionHashes[action].push(hash);

fs.writeFileSync(
    HASHES_FILE,
    JSON.stringify(actionHashes, null, 2)
);

    await sock.sendMessage(
        msg.key.remoteJid,
        {
            text: `✓ GIF guardado en ${action}/${filename}`
        },
        { quoted: msg }
    );

}

export async function handleWaifuVideo({ sock, msg, args, jid }) {
  const query = args.join(' ');

  if (!query) {
    return sock.sendMessage(jid, {
      text: '◇ Uso: /waifuvideo [nombre]'
    }, { quoted: msg });
  }

  const q = query.toLowerCase().trim();
  const char =
findCharacter(query);

  if (!char) {
    return sock.sendMessage(jid, {
      text: '● Personaje no encontrado.'
    }, { quoted: msg });
  }

  const key = char.key || char.name.toLowerCase().replace(/\s+/g, '_');
  const videoPath = getCharacterVideo(key);

  if (!videoPath) {
    return sock.sendMessage(jid, {
      text: '◇ El personaje no tiene videos aún.'
    }, { quoted: msg });
  }

  const cap =
    `❬ ${char.name}\n` +
    `❖ ${char.anime}\n` +
    `✰ ${char.value.toLocaleString()}`;

  await sock.sendMessage(jid, {
    video: fs.readFileSync(videoPath),
    caption: cap,
    mimetype: 'video/mp4'
  }, { quoted: msg });
}

export async function handleWaifuEdit({ sock, msg, args, jid }) {

  const query = args.join(' ').toLowerCase().trim();

  if (!query) {
    return sock.sendMessage(jid, {
      text: '◇ Uso: /waifuedit [nombre]'
    }, { quoted: msg });
  }

  if (!fs.existsSync(GACHA_VIDEOS)) {
    return sock.sendMessage(jid, {
      text: '◇ Carpeta de videos no encontrada.'
    }, { quoted: msg });
  }

  const videos = fs.readdirSync(GACHA_VIDEOS)
    .filter(v =>
      v.toLowerCase().startsWith(query) &&
      v.endsWith('.mp4')
    );

  if (!videos.length) {
    return sock.sendMessage(jid, {
      text: '◇ No se encontraron videos.'
    }, { quoted: msg });
  }

  const randomVideo =
    videos[Math.floor(Math.random() * videos.length)];

  const videoPath = path.join(GACHA_VIDEOS, randomVideo);

  await sock.sendMessage(jid, {
    video: fs.readFileSync(videoPath),
    caption: `☆ ${query}`,
    mimetype: 'video/mp4'
  }, { quoted: msg });
}

// ━━━━━━━ TOP GACHA, TOPGACHAGP, GIVECHAR, DELPJ ━━━━━━━
export async function handleTop(sock, jid, msg, args = []) {

    const page = parseInt(args[0]) || 1;
    const perPage = 10;

    const users = Object.entries(db.users)
        .sort((a, b) => {
            const levelA = a[1].level || 0;
            const levelB = b[1].level || 0;

            if (levelB !== levelA) {
                return levelB - levelA;
            }

            return (b[1].xp || 0) - (a[1].xp || 0);
        });

    const totalPages = Math.ceil(users.length / perPage);

    const start = (page - 1) * perPage;
    const end = start + perPage;

    const topUsers = users.slice(start, end);

    let text = ` Top de usuarios con más experiencia \n\n`;

    topUsers.forEach((u, i) => {

        const pos = start + i + 1;

        const name = u[1].name || 'Usuario';
        const xp = u[1].xp || 0;
        const lvl = u[1].level || 1;

        text +=
`✧ ${pos} » *${name}*
\t\t☆ XP » *${xp}*  ❖ LVL » *${lvl}*

`;
    });

    text += `\nï¿½ Página *${page}* de *${totalPages}*`;

    if (page < totalPages) {
        text += `\nï¿½ Para ver la siguiente página usa: */top ${page + 1}*`;
    }

    await sock.sendMessage(jid, {
        text
    }, { quoted: msg });
}

export async function handleLvl(sock, jid, msg, sender) {

  const user = initUser(
    sender,
    msg.pushName
  );

  const xp = user.xp || 0;
const level = user.level || 1;

const currentLevelXp = xpForLevel(level);
const nextLevelXp = xpForLevel(level + 1);

 const xpInLevel = Math.max(
  0,
  xp - currentLevelXp
);

const xpNeeded =
  nextLevelXp - currentLevelXp;

const progress = Math.max(
  0,
  Math.floor(
    (xpInLevel / xpNeeded) * 100
  )
);

const needed =
  nextLevelXp - currentLevelXp;

const percent =
  Math.min(
    100,
    Math.floor((progress / needed) * 100)
  );

  const topUsers =
    Object.entries(db.users)
      .sort((a, b) =>
        (b[1].xp || 0) -
        (a[1].xp || 0)
      );

  const rank =
    topUsers.findIndex(
      ([id]) => id === sender
    ) + 1;

  const topOrden = Object.entries(db.users).sort((a, b) => {
    const la = a[1].level || 0;
    const lb = b[1].level || 0;
    if (lb !== la) return lb - la;
    return (b[1].xp || 0) - (a[1].xp || 0);
  });
  const rankLvl = topOrden.findIndex(([id]) => id === sender) + 1;
  const topPageLvl = Math.max(1, Math.ceil(rankLvl / 10));
  const nf = n => Number(n || 0).toLocaleString('en-US');
  const estiloNombre = s => [...String(s || 'Usuario')].map(c => {
    const n = c.charCodeAt(0);
    if (n >= 65 && n <= 90) return String.fromCodePoint(0x1D468 + n - 65);
    if (n >= 97 && n <= 122) return String.fromCodePoint(0x1D482 + n - 97);
    return c;
  }).join('');
  const text =
    "➩ `" + estiloNombre(user.name) + " ও`\n\n" +
    "✶ ᥒιvᥱᥣ ➛ `" + level + "`\n" +
    "∞ ᥱxρᥱrιᥱᥒᥴια ➛ `" + nf(xp) + "`\n" +
    "✧ ρrogrᥱѕo ➛ `" + nf(xpInLevel) + " ↹ " + nf(xpNeeded) + " (" + progress + "%)`\n" +
    "≛ ρᥙᥱѕтo ➛ `" + rankLvl + " /top " + topPageLvl + "`\n\n" +
    "⚘ ᥴoຕᥲᥒᑯo⳽ totᥲꙆᥱ⳽ `" + nf(user.totalCommands) + "`";

  await sock.sendMessage(
    jid,
    { text },
    { quoted: msg }
  );

}

async function checkLevelTradeAccept(
  sock,
  msg,
  sender
) {

  const text =
    msg.message?.conversation ||
    msg.message?.extendedTextMessage?.text ||
    '';

  if (text.toLowerCase() !== 'aceptar')
    return false;

  const quoted =
    msg.message?.extendedTextMessage
      ?.contextInfo
      ?.stanzaId;

  if (!quoted)
    return false;

  for (const [id, trade] of Object.entries(pendingLevelTrades)) {

    if (
      trade.messageId !== quoted
    ) continue;

    if (Date.now() > trade.expires) {

      delete pendingLevelTrades[id];
      return true;
    }

    if (sender !== trade.to) {

      await sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
`⟪✧⟫ Solo @${trade.to.split('@')[0]} puede aceptar la solicitud.`,
          mentions:[trade.to]
        },
        { quoted: msg }
      );

      return true;
    }

    const userA =
      initUser(trade.from);

    const userB =
      initUser(trade.to);

    const oldA = userA.level;
    const oldB = userB.level;

    userA.level = oldB;
    userB.level = oldA;

    saveDB();

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`•­─【 TRADE LVL 〕─◆

✓ Intercambio completado

☆ @${trade.from.split('@')[0]}
${oldA} → ${oldB}

☆ @${trade.to.split('@')[0]}
${oldB} → ${oldA}

•°────────◆`,
        mentions:[
          trade.from,
          trade.to
        ]
      },
      { quoted: msg }
    );

    delete pendingLevelTrades[id];

    return true;
  }

  return false;
}


export async function handleTopGachaGlobal(sock, msg, args, jid) {
  const users = Object.entries(db.users || {})
    .filter(([userId, user]) => {
      return user && Array.isArray(user.harem) && user.harem.length > 0;
    })
    .map(([userId, user]) => {
      const harem = Array.isArray(user.harem) ? user.harem : [];

      let totalValue = 0;

      for (const key of harem) {
        const character = characterKeyMap.get(key);

        if (character) {
          totalValue += Number(character.value || 0);
        }
      }

      return {
        jid: userId,
        name: user.name || 'Usuario',
        count: harem.length,
        value: totalValue
      };
    })
    .sort((a, b) => {
      if (b.count !== a.count) {
        return b.count - a.count;
      }

      return b.value - a.value;
    });

  const page = Math.max(1, parseInt(args?.[0], 10) || 1);
  const perPage = 10;
  const pages = Math.max(1, Math.ceil(users.length / perPage));

  if (page > pages) {
    return sock.sendMessage(
      jid,
      {
        text: " Página inválida.\n\n Página mï¿½xima: `" + pages + "`"
      },
      { quoted: msg }
    );
  }

  const slice = users.slice(
    (page - 1) * perPage,
    page * perPage
  );

  if (!slice.length) {
    return sock.sendMessage(
      jid,
      { text: '◇ No hay datos.' },
      { quoted: msg }
    );
  }

  let text = '❬ Top Gacha Global\n\n';

  slice.forEach((user, i) => {
    const position = (page - 1) * perPage + i + 1;

    text +=
      "☆ " + position + " » " + user.name + "\n" +
      "    ✤ Personajes `" + user.count + "` ☆ Valor: `" + user.value + "`\n";
  });

  text += "\n Página `" + page + "/" + pages + "`";

  await sock.sendMessage(
    jid,
    { text },
    { quoted: msg }
  );
}



export async function handleDelAddp(
  sock,
  msg,
  args,
  jid,
  sender,
  isOwner
) {
  console.log("◆ DELADDP DEFINITIVO");
const entradas = Object.entries(db.addpQueue || {});

  /*
   * IMPORTANTE:
   *
   * /deladdp NO debe exigir iniciadoPorAddp === true
   * para poder limpiar una cola rota.
   *
   * Una cola antigua/corrupta puede no tener esa propiedad,
   * pero sus timers siguen funcionando.
   */

  const addpActivo = entradas.find(([queueJid, cola]) => {
    if (!cola || typeof cola !== 'object') {
      return false;
    }

    const personajes = Array.isArray(cola.personajes)
      ? cola.personajes
      : [];

    const index = Number(cola.index || 0);

    /*
     * Consideramos activa cualquier cola que:
     * - tenga personajes pendientes
     * - no esté finalizada/cancelada
     *
     * Esto permite matar también colas antiguas o corruptas.
     */
    const estado = String(cola.addpEstado || '').toLowerCase();

    if (
      estado === 'cancelada' ||
      estado === 'finalizada' ||
      estado === 'terminada' ||
      estado === 'completada'
    ) {
      return false;
    }

    /*
     * También detectamos colas con timer/retry aunque el índice
     * esté fuera de rango.
     */
    const tieneTimer =
      cola.timer ||
      cola.retryTimer ||
      cola.watchdogTimer ||
      cola.timeout ||
      cola.interval;

    return (
      index < personajes.length ||
      !!tieneTimer ||
      cola.addpBusy === true ||
      cola.addpTransition === true ||
      cola.addpEstado === 'activa'
    );
  });

  if (!addpActivo) {
    return sock.sendMessage(
      jid,
      {
        text: '◇ No hay ningún /addp activo.'
      },
      {
        quoted: msg
      }
    );
  }

  const [addpJid, cola] = addpActivo;

  console.log('🛑 DELADDP: cola encontrada:', addpJid);
  console.log('🛑 DELADDP: iniciadoPorAddp:', cola.iniciadoPorAddp);
  console.log('🛑 DELADDP: estado:', cola.addpEstado);
  console.log('🛑 DELADDP: index:', cola.index);
  console.log(
    '🛑 DELADDP: personajes:',
    Array.isArray(cola.personajes)
      ? cola.personajes.length
      : 0
  );

  const creador =
    cola.user ||
    cola.sender ||
    cola.iniciadoPor ||
    cola.createdBy ||
    null;

  const esOwnerPrincipal =
    isOwner === true;

  const esOwnerSecundario =
    Array.isArray(db.secondaryOwners) &&
    db.secondaryOwners.some(
      id => String(id) === String(sender)
    );

  const esCreador =
    creador &&
    String(creador) === String(sender);

  console.log('DELADDP PERMISOS:', {
    esOwnerPrincipal,
    esOwnerSecundario,
    esCreador,
    creador,
    sender
  });

  if (
    !esOwnerPrincipal &&
    !esOwnerSecundario &&
    !esCreador
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          '❌ No tienes permiso para cancelar esta cola /addp.\n\n' +
          '• El usuario que inici¿ el /addp\n' +
          '• Owner principal\n' +
          '• Owner secundario'
      },
      {
        quoted: msg
      }
    );
  }

  /*
   * ==========================================================
   * MATAR TODOS LOS TIMERS CONOCIDOS
   * ==========================================================
   */

  const timers = [
    'timer',
    'retryTimer',
    'watchdogTimer',
    'timeout',
    'interval'
  ];

  for (const propiedad of timers) {
    const valor = cola[propiedad];

    if (!valor) continue;

    try {
      clearTimeout(valor);
    } catch {}

    try {
      clearInterval(valor);
    } catch {}

    cola[propiedad] = null;

    console.log(
      '🛑 DELADDP: timer eliminado:',
      propiedad
    );
  }

  /*
   * Algunas versiones pueden guardar timers adicionales.
   */
  if (Array.isArray(cola.timers)) {
    for (const timer of cola.timers) {
      try {
        clearTimeout(timer);
      } catch {}

      try {
        clearInterval(timer);
      } catch {}
    }

    cola.timers = [];
  }

  /*
   * ==========================================================
   * MARCAR CANCELADA
   * ==========================================================
   */

  cola.addpEstado = 'cancelada';
  cola.addpBusy = false;
  cola.addpTransition = false;
  cola.addpTransitionOwner = null;

  cola.cancelada = true;
  cola.cancelled = true;
  cola.canceladoPor = sender;
  cola.cancelledBy = sender;
  cola.canceladoAt = Date.now();

  /*
   * Evita que una llamada pendiente vuelva a ejecutar ADDP.
   */
  cola.detener = true;
  cola.stop = true;
  cola.abort = true;

  /*
   * ==========================================================
   * ELIMINAR DE LA DB
   * ==========================================================
   */

  delete db.addpQueue[addpJid];

  console.log(
    '🗑️ DELADDP: cola eliminada de db.addpQueue:',
    addpJid
  );

  try {
    saveDB();
    console.log('💾 DELADDP: DB guardada.');
  } catch (err) {
    console.error(
      '❌ DELADDP: error guardando DB:',
      err
    );
  }

  await sock.sendMessage(
    jid,
    {
      text:
        '🛑 /ADDP CANCELADO\n\n' +
        '◇ La cola ADDP fue detenida.\n' +
        '◇ Se eliminaron sus timers.\n' +
        '◇ El watchdog ya no podr¿ recuperarla.'
    },
    {
      quoted: msg
    }
  );

  return true;
}


export async function handleTopGachagp(sock, msg, args, groupId) {
  const group = db.groups[groupId];
  if (!group) return;
  const members = Object.entries(group.harems || {}).filter(([jid, h]) => h.length > 0)
    .sort((a, b) => b[1].length - a[1].length);
  const page = parseInt(args[0]) || 1;
  const perPage = 10;
  const pages = Math.ceil(members.length / perPage);
  const slice = members.slice((page-1)*perPage, page*perPage);
  if (!slice.length) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No hay datos.' }, { quoted: msg });
  let text = `❬ Top Gacha del grupo\n\n`;
  slice.forEach(([jid, h], i) => {
    const sum = h.reduce((s, c) => s + (c.value || 0), 0);
    text += `☆ ${(page-1)*perPage + i + 1} » ${db.users[jid]?.name || 'Usuario'}\n    ✤ Personajes \`${h.length}\` ? Valor: \`${sum}\`\n`;
  });
  text += `\n Página \`${page}/${pages}\``;
  await sock.sendMessage(msg.key.remoteJid, { text }, { quoted: msg });
}

export async function handleGivechar(sock, msg, args, groupId, sender, mentioned) {
  if (!mentioned.length) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Menciona a qui¿n regalar.' }, { quoted: msg });
  const target = mentioned[0];
  const name = args.join(' ').replace(/@\u2068[^\u2069]*\u2069/g, ' ').replace(/@\S+/g, ' ').replace(/\s+/g, ' ').trim().toLowerCase();
  if (!name) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Uso: /givechar [nombre] @usuario' }, { quoted: msg });
  const myHarem = db.groups[groupId]?.harems?.[sender] || [];
  console.log('BUSCANDO:', name);

for (const c of myHarem) {
  console.log('PJ:', JSON.stringify(c.name));
}
   console.log(
  myHarem.map(x => `"${x.name}"`)
);
  const idx = myHarem.findIndex(c => c.name.toLowerCase().includes(name));
  if (idx === -1) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No tienes ese personaje.' }, { quoted: msg });
  const character = myHarem.splice(idx, 1)[0];
  if (!db.groups[groupId].harems[target]) db.groups[groupId].harems[target] = [];
  db.groups[groupId].harems[target].push(character);
  // Actualizar claimedBy y ownerIndex
  const char = characterKeyMap.get(character.key);
  if (char?.claimedBy?.[groupId]?.user === sender) {
    char.claimedBy[groupId].user = target;
    if (global.ownerIndex[groupId]?.[sender]) global.ownerIndex[groupId][sender].delete(character.key);
    if (!global.ownerIndex[groupId]) global.ownerIndex[groupId] = {};
    if (!global.ownerIndex[groupId][target]) global.ownerIndex[groupId][target] = new Set();
    global.ownerIndex[groupId][target].add(character.key);
    saveCharacters();
  }
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `✰ *${character.name}* ha sido regalado a *${db.users[target]?.name || 'Usuario'}*!`, mentions: [target] }, { quoted: msg });
}

// ━━━━━━━ COMANDO DELPJ CORREGIDO ━━━━━━━
async function handleDelPj(sock, msg, args, jid, sender) {
  const name = args.slice(1).join(' ').toLowerCase();
  
  if (!name) {
    return sock.sendMessage(jid, {
      text: '◇ Uso: /delpj [nombre]'
    }, { quoted: msg });
  }

  // Solo owner puede usar este comando
  if (!isOwner) {
  return sock.sendMessage(jid,{
    text:'Solo el owner puede usar este comando.'
  },{ quoted: msg });
}

  const before = charactersCache.length;
  let deletedImages = 0;

  charactersCache = charactersCache.filter(char => {
    const sameName = char.name.toLowerCase() === name;
    
    if (sameName) {
      // Eliminar imágenes asociadas
      const images = getCharacterImages(char.key);
      for (const img of images) {
        const imgPath = path.join(GACHA_IMAGES, img);
        if (fs.existsSync(imgPath)) {
          try {
            fs.unlinkSync(imgPath);
            deletedImages++;
          } catch (e) {}
        }
      }
      return false;
    }
    return true;
  });

  saveCharacters();
  loadCharactersCache();

  const deleted = before - charactersCache.length;

  await sock.sendMessage(jid, {
    text: `☆ Eliminación de personaje\n\n` +
      `❬ Nombre: ${name}\n` +
      `⌗ Eliminados: ${deleted} personaje(s)\n` +
      `⌗ Im¿genes eliminadas: ${deletedImages}\n` +
      `⌗ Restantes: ${charactersCache.length} personajes`
  }, { quoted: msg });
}

// ━━━━━━━ ECONOM¿A (POR GRUPO) ━━━━━━━
export async function handleBal(sock, msg, groupId, sender, mentioned) {
  let target = mentioned.length ? mentioned[0] : sender;
  const eco = getGroupEconomy(groupId, target);
  const total = (eco.coins || 0) + (eco.bank || 0);
  const text = `✿ 》》Econom¿a @${db.users[target]?.name || 'Usuario'}《《 ✿\n\n` +
    `⛀ Dinero » ${(eco.coins || 0).toLocaleString()} ${getBotCurrency(sock)} ⋆.೒'.\n` +
    `⚿ Banco » ${(eco.bank || 0).toLocaleString()} ${getBotCurrency(sock)} ⋆.೒'.\n` +
    `⛁ Total » ${total.toLocaleString()} ${getBotCurrency(sock)} ⋆.೒'.\n\n` +
    `«Protege tu dinero con /deposit»`;
  await sock.sendMessage(msg.key.remoteJid, { text }, { quoted: msg });
}
// Handler para comando einfo
export async function handleEinfo(sock, msg, jid, sender) {
  try {
    const user = db.users[sender];

    if (!user) {
      await sock.sendMessage(
        jid,
        {
          text: 'No tienes cuenta registrada.'
        },
        { quoted: msg }
      );
      return;
    }

    const groupId = msg.key.remoteJid;

    const eco =
      getGroupEconomy(
        groupId,
        sender
      );

    const cooldowns =
      getGroupCooldowns(
        groupId,
        sender
      );

    const now =
      Date.now();

    // =========================================================
    // COOLDOWNS REALES
    // Deben coincidir con handleMine, handleWork,
    // handleSlut, handleCrime y handleDaily.
    // =========================================================

    // /mine = 20 minutos
    // Mine sí utiliza la reducción de Premium mediante
    // getRemainingTime(), exactamente igual que handleMine().
    const hasPremium =
      user.premium &&
      user.premium.expires > now;

    const mineRemaining =
      getRemainingTime(
        eco.lastMine || 0,
        20 * 60 * 1000,
        hasPremium
      );

    // /work = 15 segundos
    // Usa cooldowns.work y NO Premium.
    const workRemaining =
      Math.max(
        0,
        15000 -
        (now - (cooldowns.work || 0))
      );

    // /slut = 4 minutos
    // Usa cooldowns.slut y NO Premium.
    const slutRemaining =
      Math.max(
        0,
        240000 -
        (now - (cooldowns.slut || 0))
      );

    // /crime = 5 minutos
    // Usa cooldowns.crime y NO Premium.
    const crimeRemaining =
      Math.max(
        0,
        300000 -
        (now - (cooldowns.crime || 0))
      );

    // /daily = 24 horas
    // Daily utiliza lastDailyGlobal a nivel global del usuario.
    const dailyRemaining =
      getDailyRemainingMs(user, now);

    // =========================================================
    // FORMATEO
    // =========================================================

    const mineTime =
      formatTimeRemaining(
        mineRemaining
      );

    const workTime =
      formatTimeRemaining(
        workRemaining
      );

    const slutTime =
      formatTimeRemaining(
        slutRemaining
      );

    const crimeTime =
      formatTimeRemaining(
        crimeRemaining
      );

    const dailyTime =
      formatTimeRemaining(
        dailyRemaining
      );

    // =========================================================
    // COINS
    // =========================================================

    const total =
      formatNumber(
        (eco.coins || 0) +
        (eco.bank || 0)
      );

    // =========================================================
    // MENSAJE
    // =========================================================

    const mention =
      `@${sender.split('@')[0]}`;

    const mensaje =
`✿ *》》Economía ${mention}《《* ✿

ⴵ *Mine* » \`${mineTime}\`
ⴵ *Work* » \`${workTime}\`
ⴵ *Slut* » \`${slutTime}\`
ⴵ *Crime* » \`${crimeTime}\`
ⴵ *Daily* » \`${dailyTime}\`

⛁ Coins totales » ${total} ${getBotCurrency(sock)} 𝙧፝֟𓂃𓈒☆̲⌁. ⌝`;

    await sock.sendMessage(
      jid,
      {
        text: mensaje,
        mentions: [sender]
      },
      { quoted: msg }
    );

  } catch (error) {
    console.error(
      '[EINFO ERROR]',
      error
    );

    await sock.sendMessage(
      jid,
      {
        text:
          'Error al mostrar informacion economica.'
      },
      { quoted: msg }
    );
  }
}

// Handler para comando mine
export async function handleMine(sock, msg, jid, sender) {
  try {
    const user = db.users[sender];
    if (!user) {
      await sock.sendMessage(jid, { text: 'No tienes cuenta registrada.' }, { quoted: msg });
      return;
    }

    const groupId = msg.key.remoteJid;
    const eco = getGroupEconomy(groupId, sender);
    const now = Date.now();
    const hasPremium = user.premium && user.premium.expires > now;
    const cooldown = 20 * 60 * 1000;
    
    const remaining = getRemainingTime(eco.lastMine || 0, cooldown, hasPremium);
    
    if (remaining > 0) {
      const timeStr = formatTimeRemaining(remaining);
      let mensaje = 'Tienes que esperar ' + timeStr + ' para volver usar Mine.';
      if (hasPremium) {
        mensaje += '\nPuedes disminuir el tiempo de espera con xpremium.';
      }
      await sock.sendMessage(jid, { text: mensaje }, { quoted: msg });
      return;
    }

    await sock.sendMessage(jid, { text: 'Llendo a la mina...' }, { quoted: msg });

    await new Promise(resolve => setTimeout(resolve, 2000));

    const random = Math.random() * 100;
    let piedras;
    
    if (random < 60) {
      piedras = Math.floor(Math.random() * 1000) + 1;
    } else if (random < 90) {
      piedras = Math.floor(Math.random() * 9000) + 1000;
    } else {
      piedras = Math.floor(Math.random() * 90000) + 10000;
    }

    const diamantes = piedras * 1500;
    
    eco.lastMine = now;
    eco.coins = (eco.coins || 0) + diamantes;
    
    user.diamonds = (user.diamonds || 0) + diamantes;
    
    saveDB();

    const piedrasStr = formatNumber(piedras);
    const diamantesStr = formatNumber(diamantes);

    const mensaje = `\u2740 Exito encontraste ${piedrasStr} piedras de diamantes y ganaste *${diamantesStr} \u25C6\u25C6\u25C6*.`;

    await sock.sendMessage(jid, { text: mensaje }, { quoted: msg });
    
  } catch (error) {
    console.error('[MINE ERROR]', error);
    await sock.sendMessage(jid, { text: 'Error al usar el comando mine.' }, { quoted: msg });
  }
}

// Handler para comando owner?
export async function handleOwnerCheck(sock, msg, jid, sender, mentioned) {
  try {
    const target = mentioned.length ? mentioned[0] : sender;
    const isSecondaryOwner = typeof isSecondaryOwnerId === 'function' ? isSecondaryOwnerId(target) : (Array.isArray(db.secondaryOwners) && db.secondaryOwners.includes(target));
    
    const user = db.users[target];
    const name = user ? user.name : target;
    
    if (isSecondaryOwner) {
      await sock.sendMessage(jid, { text: `${name} es secondary owner del bot.` }, { quoted: msg });
    } else {
      await sock.sendMessage(jid, { text: `${name} no es secondary owner del bot.` }, { quoted: msg });
    }
    
  } catch (error) {
    console.error('[OWNER CHECK ERROR]', error);
    await sock.sendMessage(jid, { text: 'Error al verificar owner.' }, { quoted: msg });
  }
}

// Handler para comando owner - establecer nuevo owner principal
export async function handleSetOwner(sock, msg, jid, sender) {
  try {
    // Verificar si el usuario es owner actual o secondary owner
    const isCurrentOwner = isMainOwnerId(sender);
    const isSecondaryOwner = isSecondaryOwnerId(sender);
    
    if (!isCurrentOwner && !isSecondaryOwner) {
      return;
    }
    
    // Tu número de WhatsApp en formato @lid
    const newOwner = `${OWNER_CONTACT_NUMBER}@lid`;
    
    // Establecer nuevo owner principal en la base de datos
    db.primaryOwner = newOwner;
    saveDB();
    
    await sock.sendMessage(
      jid,
      {
        contacts: {
          displayName: 'Owner',
          contacts: [
            {
              displayName: 'Owner',
              vcard:
                'BEGIN:VCARD\n' +
                'VERSION:3.0\n' +
                'FN:Owner\n' +
                `TEL;type=CELL;type=VOICE;waid=${OWNER_CONTACT_NUMBER}:+${OWNER_CONTACT_NUMBER}\n` +
                'END:VCARD'
            }
          ]
        }
      },
      { quoted: msg }
    );
    
  } catch (error) {
    console.error('[SET OWNER ERROR]', error);
    await sock.sendMessage(jid, { text: 'Error al establecer owner principal.' }, { quoted: msg });
  }
}

export async function handleKick(sock, msg, jid, sender, mentioned, args) {
  if (!jid?.endsWith('@g.us')) {
    return sock.sendMessage(
      jid,
      { text: '◇ Este comando solo funciona en grupos.' },
      { quoted: msg }
    );
  }

  let metadata;

  try {
    metadata =
      await sock.groupMetadata(jid);
  } catch (error) {
    console.error('[KICK METADATA ERROR]', error);
    return sock.sendMessage(
      jid,
      { text: '❌ No se pudo comprobar el grupo.' },
      { quoted: msg }
    );
  }

  const senderParticipant =
    metadata.participants.find(
      participant =>
        participant.id === sender ||
        participant.jid === sender
    );

  const senderIsAdmin =
    senderParticipant?.admin === 'admin' ||
    senderParticipant?.admin === 'superadmin' ||
    senderParticipant?.admin === true;

  if (!isMainOwnerId(sender) &&
      !isSecondaryOwnerId(sender) &&
      !senderIsAdmin) {
    return sock.sendMessage(
      jid,
      { text: '❌ Solo los administradores y owners pueden usar /kick.' },
      { quoted: msg }
    );
  }

  const contextInfo =
    msg.message?.extendedTextMessage?.contextInfo;
  const target =
    mentioned?.[0] ||
    contextInfo?.participant ||
    (args[0]
      ? `${args[0].replace(/\D/g, '')}@lid`
      : null);

  if (!target) {
    return sock.sendMessage(
      jid,
      { text: '◇ Uso: /kick @usuario o responde a su mensaje.' },
      { quoted: msg }
    );
  }

  if (isMainOwnerId(target) || isSecondaryOwnerId(target)) {
    return sock.sendMessage(
      jid,
      { text: '❌ No puedes expulsar a un owner.' },
      { quoted: msg }
    );
  }

  const targetParticipant =
    metadata.participants.find(
      participant =>
        participant.id === target ||
        participant.jid === target ||
        participant.lid === target
    );

  const targetJid =
    targetParticipant?.id ||
    targetParticipant?.jid ||
    target;

  try {
    const targetIsAdmin =
      targetParticipant?.admin === 'admin' ||
      targetParticipant?.admin === 'superadmin' ||
      targetParticipant?.admin === true;

    if (targetIsAdmin) {
      await sock.groupParticipantsUpdate(
        jid,
        [targetJid],
        'demote'
      );
    }

    await sock.groupParticipantsUpdate(
      jid,
      [targetJid],
      'remove'
    );
  } catch (error) {
    console.error('[KICK ERROR]', error);
    return sock.sendMessage(
      jid,
      { text: '❌ No se pudo quitar al usuario. Verifica que el bot sea administrador.' },
      { quoted: msg }
    );
  }
}

export async function handleDeposit(sock, msg, args, groupId, sender) {
  const amount = parseInt(args[0]);
  if (!amount || amount <= 0) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Uso: /deposit <cantidad>' }, { quoted: msg });
  const eco = getGroupEconomy(groupId, sender);
  if (amount > (eco.coins || 0)) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No tienes suficiente dinero en la wallet.' }, { quoted: msg });
  eco.coins -= amount;
  eco.bank = (eco.bank || 0) + amount;
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `☆ Depositado ${amount.toLocaleString()} ${getBotCurrency(sock)} al banco.` }, { quoted: msg });
}

export async function handleD(
  sock,
  msg,
  args,
  groupId,
  sender
) {
  const input =
    String(args[0] || '').trim();

  const jid =
    msg.key.remoteJid;

  const invalidMessage =
`❃ 《✧》 *ᴅᴇʙᴇs ᴅᴇᴘᴏsɪᴛᴀʀ ᴜɴᴀ ᴄᴀɴᴛɪᴅᴀᴅ ᴠáʟɪᴅᴀ*
> ⟡ ᴇᴊᴇᴍᴘʟᴏ 1 › #d 25000
> ⟡ ᴇᴊᴇᴍᴘʟᴏ 2 › #d all
✧ ｡ﾟ•┈୨ ♡ ୧┈•ﾟ｡ ✧`;

  if (!input) {
    return sock.sendMessage(
      jid,
      {
        text: invalidMessage
      },
      {
        quoted: msg
      }
    );
  }

  const eco =
    getGroupEconomy(
      groupId,
      sender
    );

  const wallet =
    Number(eco.coins || 0);

  let amount;

  if (
    input.toLowerCase() === 'all'
  ) {
    amount = wallet;
  } else {
    if (!/^\d+$/.test(input)) {
      return sock.sendMessage(
        jid,
        {
          text: invalidMessage
        },
        {
          quoted: msg
        }
      );
    }

    amount =
      Number(input);
  }

  if (
    !Number.isSafeInteger(amount) ||
    amount <= 0
  ) {
    return sock.sendMessage(
      jid,
      {
        text: invalidMessage
      },
      {
        quoted: msg
      }
    );
  }

  if (
    amount > wallet
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          '◇ No tienes suficientes Coins para depositar esa cantidad.'
      },
      {
        quoted: msg
      }
    );
  }

  eco.coins =
    wallet - amount;

  eco.bank =
    Number(eco.bank || 0) +
    amount;

  saveDB();

  await sock.sendMessage(
    jid,
    {
      text:
`₊˚⊹ ✧ *ᴅᴇᴘᴏsɪᴛᴀsᴛᴇ \`${amount.toLocaleString()}\` ʏᴀ ɴᴏ ᴘᴏᴅʀáɴ ʀᴏʙáʀᴛᴇʟᴏ* ⊹˚₊`
    },
    {
      quoted: msg
    }
  );
}

export async function handleWithdraw(sock, msg, args, groupId, sender) {
  const amount = parseInt(args[0]);
  if (!amount || amount <= 0) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Uso: /withdraw <cantidad>' }, { quoted: msg });
  const eco = getGroupEconomy(groupId, sender);
  if (amount > (eco.bank || 0)) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No tienes suficiente dinero en el banco.' }, { quoted: msg });
  eco.bank -= amount;
  eco.coins = (eco.coins || 0) + amount;
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `☆ Retirado ${amount.toLocaleString()} ${getBotCurrency(sock)} del banco.` }, { quoted: msg });
}

export async function handleWork(sock, msg, groupId, sender) {
  const cooldowns = getGroupCooldowns(groupId, sender);
  const eco = getGroupEconomy(groupId, sender);
  const now = Date.now();
  if (now - cooldowns.work < 15000) {
    const w = Math.ceil((15000 - (now - cooldowns.work)) / 1000);
    return sock.sendMessage(msg.key.remoteJid, { text: `⏳ Espera ${w}s para trabajar.` }, { quoted: msg });
  }

  const earned = Math.floor(Math.random() * 10000) + 1000;
  eco.coins = (eco.coins || 0) + earned;
  cooldowns.work = now;
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `☆ Hoყ trᥲbᥲjᥲstᥱ dᥙrᥲᥒtᥱ vᥲrιᥲs horᥲs ყ fιᥒᥲᥣmᥱᥒtᥱ ᥣᥣᥱgó tᥙ mᥱrᥱᥴιdo ρᥲgo. Gᥲᥒᥲstᥱ ${earned.toLocaleString()} ⫸ᴍᴀʏs.` }, { quoted: msg });
}

export async function handleSlut(sock, msg, groupId, sender) {
  const cooldowns = getGroupCooldowns(groupId, sender);
  const eco = getGroupEconomy(groupId, sender);
  const now = Date.now();
  if (now - cooldowns.slut < 240000) {
    const w = Math.ceil((240000 - (now - cooldowns.slut)) / 1000);
    return sock.sendMessage(msg.key.remoteJid, { text: `⏳ Espera ${Math.floor(w/60)}m ${w%60}s para /slut` }, { quoted: msg });
  }
  const earned = Math.floor(Math.random() * 5000) + 10000;
  eco.coins = (eco.coins || 0) + earned;
  cooldowns.slut = now;
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `☆ Hoყ tᥙvιstᥱ ᥙᥒ dίᥲ bᥲstᥲᥒtᥱ ᥲgιtᥲdo, ρᥱro tᥙvιstᥱ sᥙᥱrtᥱ ყ tᥱrmιᥒᥲstᥱ ᥴoᥒ ᥙᥒ bᥙᥱᥒ ρrᥱmιo. Gᥲᥒᥲstᥱ ${earned.toLocaleString()} ⫸ᴍᴀʏs.` }, { quoted: msg });
}

export async function handleCrime(sock, msg, groupId, sender) {
  const cooldowns = getGroupCooldowns(groupId, sender);
  const eco = getGroupEconomy(groupId, sender);
  const now = Date.now();
  if (now - cooldowns.crime < 300000) {
    const w = Math.ceil((300000 - (now - cooldowns.crime)) / 1000);
    return sock.sendMessage(msg.key.remoteJid, { text: `⏳ Espera ${Math.floor(w/60)}m ${w%60}s para /crime` }, { quoted: msg });
  }
  const earned = Math.floor(Math.random() * 50000) + 50000;
  eco.coins = (eco.coins || 0) + earned;
  cooldowns.crime = now;
  saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `☆ Hoყ ᥱᥒᥴoᥒtrᥲstᥱ ᥙᥒᥲ oρortᥙᥒιdᥲd ყ dᥱᥴιdιstᥱ ᥲrrιᥱsgᥲrtᥱ. Robᥲstᥱ ${earned.toLocaleString()} ⫸ᴍᴀʏs ᥱxιtosᥲmᥱᥒtᥱ.` }, { quoted: msg });
}

export async function handleSuggest(sock, msg, sender, text) {

  if (!text.trim()) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: '《✧》Por favor, escribe la sugerencia que deseas solicitar.'
      },
      { quoted: msg }
    );
  }

  db.suggestStats ??= {};

  const data =
    db.suggestStats[sender] || {
      total: 0,
      last: 0
    };

  const now = Date.now();

  if (now - data.last < 120000) {

    const remain =
      Math.ceil(
        (120000 - (now - data.last))
        / 1000
      );

    const min =
      Math.floor(remain / 60);

    const sec =
      remain % 60;

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`《✧》Debes esperar ${min} minuto${min !== 1 ? 's' : ''} ${sec} segundos para enviar otra sugerencia.`
      },
      { quoted: msg }
    );
  }

  data.total++;
  data.last = now;

  db.suggestStats[sender] = data;

  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`✐ La solicitud ha sido inviada a los administradores del bot, gracias por tu sugerencia ♡`
    },
    { quoted: msg }
  );

  if (!db.suggestLogs) return;

  try {

    await sock.sendMessage(
      db.suggestLogs,
      {
        text:
`•­─【 NUEVA SUGERENCIA 〕─◆

• Usuario:
@${sender.split('@')[0]}

✎ Sugerencia:
${text}

• Sugerencias totales:
${data.total}

•°────────◆`,
        mentions: [sender]
      }
    );

  } catch {}
}

const DAILY_WAIT_MS = 24 * 60 * 60 * 1000;
const DAILY_GRACE_MS = 60 * 60 * 1000;
const DAILY_EXPIRE_MS = DAILY_WAIT_MS + DAILY_GRACE_MS;

// ==== DAILY: dias calendario en hora de Chile (America/Santiago) ====
const chileDayFmt = new Intl.DateTimeFormat("en-CA", {
  timeZone: "America/Santiago", year: "numeric", month: "2-digit", day: "2-digit"
});
const chileTimeFmt = new Intl.DateTimeFormat("en-GB", {
  timeZone: "America/Santiago", hourCycle: "h23", hour: "2-digit", minute: "2-digit", second: "2-digit"
});

function getChileDayKey(ms = Date.now()) {
  return chileDayFmt.format(new Date(ms)); // YYYY-MM-DD
}

function shiftDayKey(key, days) {
  const [y, m, d] = key.split("-").map(Number);
  const t = new Date(Date.UTC(y, m - 1, d + days));
  return t.getUTCFullYear() + "-" + String(t.getUTCMonth() + 1).padStart(2, "0") + "-" + String(t.getUTCDate()).padStart(2, "0");
}

function getUserLastDailyDay(user) {
  if (user.lastDailyDay) return user.lastDailyDay;
  if (user.lastDailyGlobal) return getChileDayKey(user.lastDailyGlobal);
  return "";
}

function isDailyStreakAlive(user, now = Date.now()) {
  const last = getUserLastDailyDay(user);
  if (!last) return false;
  const today = getChileDayKey(now);
  return last === today || last === shiftDayKey(today, -1);
}

function getMsUntilChileMidnight(now = Date.now()) {
  const p = chileTimeFmt.format(new Date(now)).split(":").map(Number);
  const passed = (p[0] % 24) * 3600 + p[1] * 60 + p[2];
  return Math.max(1000, (86400 - passed) * 1000);
}

function getDailyRemainingMs(user, now = Date.now()) {
  const last = getUserLastDailyDay(user);
  if (!last) return 0;
  return last === getChileDayKey(now) ? getMsUntilChileMidnight(now) : 0;
}


async function getDailyTimezone(sender) {

  let normalizedSender =
    String(sender || '').trim();

  let phone = '';

  if (
    normalizedSender
      .toLowerCase()
      .endsWith('@lid')
  ) {

    const mappedJid =
      db.missionLidToJid?.[normalizedSender] ||
      missionLidToJid.get(normalizedSender);

    if (mappedJid) {
      phone =
        String(mappedJid)
          .split('@')[0]
          .replace(/\D/g, '');
    }

  } else {

    phone =
      normalizedSender
        .split('@')[0]
        .replace(/\D/g, '');

  }

  const timezones = [
    ['56', 'CL', 'America/Santiago'],
    ['54', 'AR', 'America/Argentina/Buenos_Aires'],
    ['55', 'BR', 'America/Sao_Paulo'],
    ['51', 'PE', 'America/Lima'],
    ['52', 'MX', 'America/Mexico_City'],
    ['57', 'CO', 'America/Bogota'],
    ['58', 'VE', 'America/Caracas'],
    ['591', 'BO', 'America/La_Paz'],
    ['593', 'EC', 'America/Guayaquil'],
    ['595', 'PY', 'America/Asuncion'],
    ['598', 'UY', 'America/Montevideo'],
    ['502', 'GT', 'America/Guatemala'],
    ['503', 'SV', 'America/El_Salvador'],
    ['504', 'HN', 'America/Tegucigalpa'],
    ['505', 'NI', 'America/Managua'],
    ['506', 'CR', 'America/Costa_Rica'],
    ['507', 'PA', 'America/Panama'],
    ['509', 'HT', 'America/Port-au-Prince'],
    ['34', 'ES', 'Europe/Madrid'],
    ['33', 'FR', 'Europe/Paris'],
    ['49', 'DE', 'Europe/Berlin'],
    ['39', 'IT', 'Europe/Rome'],
    ['44', 'GB', 'Europe/London'],
    ['351', 'PT', 'Europe/Lisbon'],
    ['7', 'RU', 'Europe/Moscow'],
    ['81', 'JP', 'Asia/Tokyo'],
    ['82', 'KR', 'Asia/Seoul'],
    ['86', 'CN', 'Asia/Shanghai'],
    ['91', 'IN', 'Asia/Kolkata'],
    ['61', 'AU', 'Australia/Sydney'],
    ['64', 'NZ', 'Pacific/Auckland'],
    ['971', 'AE', 'Asia/Dubai'],
    ['972', 'IL', 'Asia/Jerusalem'],
    ['27', 'ZA', 'Africa/Johannesburg'],
    ['20', 'EG', 'Africa/Cairo'],
    ['90', 'TR', 'Europe/Istanbul'],
    ['30', 'GR', 'Europe/Athens'],
    ['31', 'NL', 'Europe/Amsterdam'],
    ['32', 'BE', 'Europe/Brussels'],
    ['41', 'CH', 'Europe/Zurich'],
    ['43', 'AT', 'Europe/Vienna'],
    ['45', 'DK', 'Europe/Copenhagen'],
    ['46', 'SE', 'Europe/Stockholm'],
    ['47', 'NO', 'Europe/Oslo'],
    ['48', 'PL', 'Europe/Warsaw'],
    ['40', 'RO', 'Europe/Bucharest'],
    ['380', 'UA', 'Europe/Kyiv'],
    ['65', 'SG', 'Asia/Singapore'],
    ['66', 'TH', 'Asia/Bangkok'],
    ['84', 'VN', 'Asia/Ho_Chi_Minh'],
    ['62', 'ID', 'Asia/Jakarta'],
    ['63', 'PH', 'Asia/Manila'],
    ['60', 'MY', 'Asia/Kuala_Lumpur'],
    ['92', 'PK', 'Asia/Karachi'],
    ['880', 'BD', 'Asia/Dhaka'],
    ['94', 'LK', 'Asia/Colombo'],
    ['98', 'IR', 'Asia/Tehran'],
    ['966', 'SA', 'Asia/Riyadh'],
    ['974', 'QA', 'Asia/Qatar'],
    ['973', 'BH', 'Asia/Bahrain'],
    ['965', 'KW', 'Asia/Kuwait'],
    ['968', 'OM', 'Asia/Muscat']
  ];

  const match =
    timezones.find(([prefix]) =>
      phone.startsWith(prefix)
    );

  if (match) {
    return {
      countryCode: match[1],
      timezone: match[2]
    };
  }

  return {
    countryCode: '',
    timezone: 'UTC'
  };
}

export async function handleDaily(sock, msg, groupId, sender) {

  const user = initUser(sender);
  const eco = getGroupEconomy(groupId, sender);
  const now = Date.now();

  const today = getChileDayKey(now);
  const lastDay = getUserLastDailyDay(user);

  // Ya reclamo hoy (hora de Chile): se reinicia a las 00:00 de Chile
  if (lastDay === today) {

    const w = Math.ceil(getMsUntilChileMidnight(now) / 1000);
    const h = Math.floor(w / 3600);
    const m = Math.floor((w % 3600) / 60);
    const s = w % 60;

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: "\u23F3 Espera " + h + "h " + m + "m " + s + "s para tu daily.\n\n> Se reinicia a las 00:00 (hora de Chile)."
      },
      { quoted: msg }
    );
  }

  // Racha: continua si reclamo ayer (hora de Chile); si no, vuelve a empezar
  if (lastDay !== shiftDayKey(today, -1)) {
    user.dailyStreak = 0;
  }

  user.dailyStreak = Math.min((user.dailyStreak || 0) + 1, 364);

  const earned = user.dailyStreak * 100000;

  eco.coins = (eco.coins || 0) + earned;

  user.lastDailyGlobal = now;
  user.lastDailyDay = today;

  saveDB();

  const nextDay = Math.min(user.dailyStreak + 1, 364);
  const nextReward = nextDay * 100000;

  let text =
    "Has reclamado tu recompensa diaria de *\u00A5" + earned.toLocaleString() + " Coins*! (D\u00EDa *" + user.dailyStreak + "*)\n\n" +
    "> D\u00EDa *" + nextDay + "* \u00BB *+\u00A5" + nextReward.toLocaleString() + "*";

  if (user.dailyStreak >= 364) {
    text += "\n\n> \u2605 Alcanzaste el l\u00EDmite de d\u00EDas, \u00A1sigue as\u00ED!";
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );

}

export async function handleSell(sock, msg, args, groupId, sender) {

  const name =
    args.join(' ').toLowerCase();

  if (!name)
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: '◇ Uso: /sell [nombre]'
      },
      { quoted: msg }
    );

  const harem =
    db.groups[groupId]?.harems?.[sender] || [];

  const idx =
    harem.findIndex(c =>
      c.name.toLowerCase().includes(name)
    );

  if (idx === -1)
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: '◇ No tienes ese personaje.'
      },
      { quoted: msg }
    );

  const character =
    harem.splice(idx,1)[0];

  const eco =
    getGroupEconomy(groupId,sender);

  const sellValue =
    Math.floor(character.value * 1.5);

  eco.coins =
    (eco.coins || 0) +
    sellValue;

  const user =
    initUser(sender);

  // ===== GEMAS =====

  const characterValue =
    Math.max(
      0,
      Number(character.value) || 0
    );

  let baseGems = 0;

  if (characterValue < 15000) {

    baseGems =
      Math.floor(
        characterValue / 2000
      ) * 100000;

  } else if (characterValue <= 15000) {

    baseGems = 500000;

  } else if (characterValue <= 16000) {

    baseGems = 800000;

  } else if (characterValue <= 18000) {

    baseGems = 1000000;

  } else if (characterValue <= 19000) {

    baseGems = 2000000;

  } else if (characterValue <= 21000) {

    baseGems = 3000000;

  } else if (characterValue <= 23000) {

    baseGems = 4000000;

  } else if (characterValue <= 25000) {

    baseGems = 5000000;

  } else if (characterValue <= 27000) {

    baseGems = 6000000;

  } else if (characterValue <= 29000) {

    baseGems = 7000000;

  } else if (characterValue <= 31000) {

    baseGems = 8000000;

  } else if (characterValue <= 33000) {

    baseGems = 9000000;

  } else if (characterValue <= 35000) {

    baseGems = 10000000;

  } else {

    baseGems =
      10000000 +
      Math.floor(
        (characterValue - 34000) / 2000
      ) * 1000000;

  }

  let rarityMultiplier = 1;

  switch (
    (character.rarity || "")
      .toLowerCase()
  ) {
 
    case "mod":
      rarityMultiplier = 3;
      break;

    case "mitico":
    case "mítico":
      rarityMultiplier = 2;
      break;

    case "legendario":
      rarityMultiplier = 1;
      break;

  }

  const gems =
    baseGems * rarityMultiplier;

  // =================

user.gems = (user.gems || 0) + gems;

  const char =
    characterKeyMap.get(character.key);

  if (
    char?.claimedBy?.[groupId]?.user === sender
  ) {

    delete char.claimedBy[groupId];

    if (
      global.ownerIndex[groupId]?.[sender]
    ) {

      global.ownerIndex[groupId][sender]
      .delete(character.key);

    }

    saveCharacters();

  }

  saveDB();

  await sock.sendMessage(
  msg.key.remoteJid,
  {
    text:
`☆ Vendiste *${character.name}*

?? *Coins* » ¥${sellValue.toLocaleString()}
?? *Gemas* » ${gems.toLocaleString()}`
  },
  { quoted: msg }
);

}

// ━━━━━━━ TOP / BALTOP / BALTOPGP ━━━━━━━
export async function handleBaltop(sock, msg, args) {

  const page =
    parseInt(args[0]) || 1;

  const perPage = 10;

  const ranking = [];

  for (const [id, u] of Object.entries(db.users)) {

    let total = 0;

    for (const groupId in db.groups) {

      const eco =
        db.groups[groupId]
        ?.economy?.[id];

      if (!eco) continue;

      total +=
        (eco.coins || 0) +
        (eco.bank || 0);

    }

    ranking.push({
      id,
      name: u.name || 'Usuario',
      total
    });

  }

  ranking.sort(
    (a, b) => b.total - a.total
  );

  const pages =
    Math.max(
      1,
      Math.ceil(
        ranking.length / perPage
      )
    );

  const slice =
    ranking.slice(
      (page - 1) * perPage,
      page * perPage
    );

  if (!slice.length) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text: ' Página vacï¿½a.'
      },
      {
        quoted: msg
      }
    );

  }

  let text =
`Top Usuarios con más Coins (global)

`;

  slice.forEach((u, i) => {

    text +=
`☆ ${(page - 1) * perPage + i + 1} » ${u.name}
✤ Coins \`${u.total.toLocaleString()}\`

`;

  });

  text +=
` Página \`${page}/${pages}\``;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );

}

export async function handleBaltopgp(sock, msg, args) {

  const groupId = msg.key.remoteJid;

  const group =
    db.groups[groupId];

  if (!group) return;

  const users = [];

  for (const userId of Object.keys(group.harems || {})) {

    const eco =
      getGroupEconomy(
        groupId,
        userId
      );

    let gen = 0;

    const harem =
      group.harems[userId] || [];

    for (const char of harem) {

      const original =
        characterKeyMap.get(char.key);

      gen += Number(
        original?.coinGen || 0
      );

    }

    users.push({
      id: userId,
      name:
        db.users[userId]?.name ||
        'Usuario',
      coins:
        (eco.coins || 0) +
        (eco.bank || 0),
      gen
    });

  }

  users.sort(
    (a,b) => b.coins - a.coins
  );

  const page =
    parseInt(args[0]) || 1;

  const perPage = 10;

  const pages =
    Math.max(
      1,
      Math.ceil(
        users.length / perPage
      )
    );

  const slice =
    users.slice(
      (page-1)*perPage,
      page*perPage
    );

  let text =
`Top Usuarios con más Coins (grupo)

`;

slice.forEach((u,i)=>{

  text +=
`☆ ${(page-1)*perPage+i+1} » ${u.name}
✤ Coins \`${u.coins.toLocaleString()}\`
`;

});

text +=
`\n Página \`${page}/${pages}\``;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );

}

// ━━━━━━━ STATUS / BOTS / CODE ━━━━━━━
export async function handleStatus(sock, msg) {

  const exec = (cmd) => {
    try {
      return execSync(cmd, {
        encoding: "utf8",
        timeout: 3000
      }).trim();
    } catch {
      return "";
    }
  };

  const hostname =
    exec("hostname") || "Desconocido";

  let ramTotal = 0;
  let ramAvailable = 0;

  try {
    const meminfo =
      fs.readFileSync("/proc/meminfo", "utf8");

    const totalMatch =
      meminfo.match(/^MemTotal:\s+(\d+)\s+kB$/m);

    const availableMatch =
      meminfo.match(/^MemAvailable:\s+(\d+)\s+kB$/m);

    ramTotal =
      totalMatch
        ? Number(totalMatch[1]) / 1024
        : 0;

    ramAvailable =
      availableMatch
        ? Number(availableMatch[1]) / 1024
        : 0;
  } catch {}

  const ramUsed =
    Math.max(0, ramTotal - ramAvailable);

  const ramUsedText =
    ramUsed >= 1024
      ? `${(ramUsed / 1024).toFixed(1)} GB`
      : `${ramUsed.toFixed(0)} MB`;

  const ramTotalText =
    ramTotal >= 1024
      ? `${(ramTotal / 1024).toFixed(1)} GB`
      : `${ramTotal.toFixed(0)} MB`;

  let diskUsed = "0 GB";
  let diskTotal = "0 GB";
  let diskPercent = "0%";

  try {
    const disk =
      exec("df -BG / | tail -1");

    const parts =
      disk.split(/\s+/);

    if (parts.length >= 5) {
      diskTotal = parts[1];
      diskUsed = parts[2];
      diskPercent = parts[4];
    }
  } catch {}

  const readCPU = () => {
    try {
      const line =
        fs.readFileSync("/proc/stat", "utf8")
          .split("\n")
          .find(x => x.startsWith("cpu "));

      if (!line)
        return null;

      const values =
        line.trim()
          .split(/\s+/)
          .slice(1)
          .map(Number);

      const idle =
        values[3] + (values[4] || 0);

      const total =
        values.reduce((a, b) => a + b, 0);

      return { idle, total };
    } catch {
      return null;
    }
  };

  const cpu1 = readCPU();

  await new Promise(resolve =>
    setTimeout(resolve, 500)
  );

  const cpu2 = readCPU();

  let cpuPercent = "0%";

  if (cpu1 && cpu2) {
    const totalDiff =
      cpu2.total - cpu1.total;

    const idleDiff =
      cpu2.idle - cpu1.idle;

    if (totalDiff > 0) {
      cpuPercent =
        `${Math.round(
          (1 - idleDiff / totalDiff) * 100
        )}%`;
    }
  }

  const procesos =
    exec("ps -e --no-headers | wc -l") || "0";

  let uptimeSeconds = 0;

  try {
    uptimeSeconds =
      Number(
        fs.readFileSync(
          "/proc/uptime",
          "utf8"
        ).split(/\s+/)[0]
      );
  } catch {}

  const totalMinutes =
    Math.floor(uptimeSeconds / 60);

  const minutes =
    totalMinutes % 60;

  const totalHours =
    Math.floor(totalMinutes / 60);

  const hours =
    totalHours % 24;

  const days =
    Math.floor(totalHours / 24);

  let uptime = "";

  if (days > 0) {
    uptime =
      `${days} día${days === 1 ? "" : "s"}`;

    if (hours > 0)
      uptime +=
        ` ${hours} hora${hours === 1 ? "" : "s"}`;

    if (minutes > 0)
      uptime +=
        ` ${minutes} minuto${minutes === 1 ? "" : "s"}`;

  } else if (hours > 0) {
    uptime =
      `${hours} hora${hours === 1 ? "" : "s"}`;

    if (minutes > 0)
      uptime +=
        ` ${minutes} minuto${minutes === 1 ? "" : "s"}`;

  } else {
    uptime =
      `${minutes} minuto${minutes === 1 ? "" : "s"}`;
  }

  const txt =
`◤ Servidor:
\`${hostname}\`

*Ram usada:* \`${ramUsedText}\` *Espacio ocupado:* \`${diskUsed}\` > \`${diskPercent}\`
*Ram Total:* \`${ramTotalText}\` *Espacio Total:* \`${diskTotal}\`
❒ *Dispositivo:* \`Lapto Acer Intel inside & Galaxy A06\`
❒ *Tiempo activo:* \`${uptime}\`
❒ *Procesos ejecutando:* \`${procesos}\`
❒ *CPU:* \`${cpuPercent}\``;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text: txt },
    { quoted: msg }
  );
}

// Cargar subs activos
function getActiveSubs(){

    try{

        const file =
        "./subbot-system/active.json";

        if(!fs.existsSync(file))
            return [];

        const data =
        JSON.parse(
            fs.readFileSync(file,"utf8")
        );

        return Object.values(data)
        .filter(x=>x.online)
        .map(x=>({
            nombre:x.name || "Subbot",
            jid:x.jid,
            owner:x.owner
        }));

    }catch{
        return [];
    }

}

export async function handleBots(sock, msg) {

  db.subBots ??= {};
  db.primaryBots ??= {};

  const normalizeBotNumber = value =>
    String(value || '')
      .replace(/:.*(?=@)/, '')
      .replace(/@.*$/, '')
      .replace(/\D/g, '');

  const sessionIsPresent = phone => {
    const folder = getSessionFolder(phone);
    return (
      fs.existsSync(folder) &&
      fs.existsSync(path.join(folder, 'creds.json'))
    );
  };

  const socketIsConnected = phone =>
    globalThis.SUBBOT_SOCKETS?.get(String(phone))?.user;

  const removeStaleSubBot = phone => {
    const botNumber = normalizeBotNumber(phone);

    for (const [groupJid, primary] of Object.entries(db.primaryBots)) {
      if (normalizeBotNumber(primary) === botNumber) {
        delete db.primaryBots[groupJid];
      }
    }

    delete db.subBots[phone];
  };

  let active = {};

  try {
    const activeFile = "./subbot-system/active.json";

    if (fs.existsSync(activeFile)) {
      active = JSON.parse(fs.readFileSync(activeFile, "utf8"));
    }

    for (const phone of Object.keys(active)) {
      if (!sessionIsPresent(phone) || !socketIsConnected(phone)) {
        delete active[phone];
        removeStaleSubBot(phone);
      }
    }

    for (const phone of Object.keys(db.subBots)) {
      if (!sessionIsPresent(phone)) {
        removeStaleSubBot(phone);
      }
    }

    fs.writeFileSync(
      activeFile,
      JSON.stringify(active, null, 2)
    );
    saveDB();
  } catch (error) {
    console.error(
      "ERROR LIMPIANDO SUBBOTS DESCONECTADOS:",
      error?.message || error
    );
  }

  let principales = activeBots.size;
  let subs = 0;

  let grupoSubs = [];

  let mods = 0;

  try{

    if (!Object.keys(active).length) {
      active = {};
    }

  }catch{}


  const jidGrupo = msg.key.remoteJid;


  for(const phone of Object.keys(active)){

    const sub = active[phone];

    if(sub.online){

      const role =
        String(
          sub.role ||
          sub.type ||
          "Sub"
        )
        .trim()
        .toLowerCase();

      if(
        role === "mod" ||
        role === "moderador"
      ){

        mods++;

      } else {

        subs++;

      }

      if(jidGrupo.endsWith("@g.us")){

        try{

          const metadata =
          await sock.groupMetadata(jidGrupo);


          const phoneDigits =
            String(phone || '')
              .replace(/\\D/g, '');

          const subJidDigits =
            String(sub.jid || '')
              .replace(/\\D/g, '');

          const encontrado =
            metadata.participants.find(
              p => {

                const posibles = [
                  p.id,
                  p.jid,
                  p.lid,
                  p.phoneNumber,
                  p.notify
                ]
                  .filter(Boolean)
                  .map(
                    x =>
                      String(x)
                        .replace(/\\D/g, '')
                  );

                return posibles.some(
                  value => {

                    if (!value) {
                      return false;
                    }

                    return (
                      value === phoneDigits ||
                      value === subJidDigits ||
                      value.includes(phoneDigits) ||
                      phoneDigits.includes(value)
                    );

                  }
                );

              }
            );


          if(encontrado){

            grupoSubs.push({
              nombre:
              sub.name || "Mavis",

              role:
              (
                String(
                  sub.role ||
                  sub.type ||
                  "Sub"
                )
                .trim()
                .toLowerCase() === "mod" ||
                String(
                  sub.role ||
                  sub.type ||
                  "Sub"
                )
                .trim()
                .toLowerCase() === "moderador"
              )
                ? "Mod"
                : "Sub",

              jid:
              encontrado.id
            });

          }


        }catch{}

      }

    }

  }


  let txt =
`「☆」Lista de bots activos (*${principales + mods + subs} sesiones*)

❖ Principales » *${principales}* sesiones
✰ Mods » *${mods}* sesiones
✿ Subs » *${subs}* sesiones

❏ En este grupo: *${grupoSubs.length}*`;


  for(const sub of grupoSubs){

    const displayRole =
      (
        sub.role === "Mod" ||
        sub.role === "Principal" ||
        sub.role === "Sub"
      )
        ? sub.role
        : "Sub";

    txt +=
      "\n\n• [" +
      displayRole +
      " *" +
      (sub.nombre || "Mavis") +
      "*] » @" +
      sub.jid.split("@")[0];

  }


  await sock.sendMessage(
    jidGrupo,
    {
      text:txt,
      mentions:
      grupoSubs.map(
        x=>x.jid
      )
    },
    {
      quoted:msg
    }
  );

}

export async function handleCode(
  sock,
  msg,
  sender,
  args,
  pairingMethod = "code"
){

  const jid =
    msg.key.remoteJid;

  const mappedPhone =
    db.missionLidToJid?.[sender] ||
    missionLidToJid.get(sender);
  const senderPhoneJid = [
    msg.key?.participantPn,
    msg.key?.senderPn,
    msg.senderPn,
    sender,
    mappedPhone
  ].find(value =>
    typeof value === "string" &&
    /@(s\.whatsapp\.net|c\.us)$/.test(value)
  );
  const phone =
    String(senderPhoneJid || "")
      .split("@")[0]
      .split(":")[0]
      .replace(/\D/g, "");

  // ==================================================
  // /code [Sub|Mod|Principal]
  // /codeqr [Sub|Mod|Principal]
  // ==================================================

  const requestedType =
    String(args[0] || args[1] || '')
      .trim()
      .toLowerCase();

  let botType = 'Sub';

  if (
    requestedType === 'mod' ||
    requestedType === 'moderador' ||
    requestedType === 'moderation'
  ) {
    botType = 'Mod';
  }

  else if (
    requestedType === 'principal' ||
    requestedType === 'main' ||
    requestedType === 'mainbot'
  ) {
    botType = 'Principal';
  }

  console.log('========================================');
  console.log(pairingMethod === "qr" ? 'CODE QR BOT' : 'CODE BOT');
  console.log('NUMERO DETECTADO:', phone || 'no disponible');
  console.log('TIPO:', botType);
  console.log('========================================');


  if (
    phone.length < 8 ||
    phone.length > 15
  ){

    return sock.sendMessage(
      jid,
      {
        text:
        'No pude detectar automáticamente tu número de WhatsApp. Ejecuta el comando desde una cuenta cuyo número esté disponible en el mensaje del grupo.'
      },
      {
        quoted:msg
      }
    );

  }

  const accountIds = new Set();
  const addAccountId = value => {
    if (typeof value !== "string" || !value.trim()) {
      return;
    }

    const normalized = value.trim().toLowerCase()
      .replace(/:\d+(?=@)/, "");
    accountIds.add(normalized);

    if (/@(s\.whatsapp\.net|c\.us)$/.test(normalized)) {
      accountIds.add(
        `phone:${normalized.split("@")[0].replace(/\D/g, "")}`
      );
    }
  };

  addAccountId(sender);
  addAccountId(msg.key?.participantPn);
  addAccountId(msg.key?.senderPn);
  addAccountId(msg.senderPn);
  addAccountId(mappedPhone);

  for (const [lid, phoneJid] of missionLidToJid) {
    if (accountIds.has(String(phoneJid).toLowerCase())) {
      addAccountId(lid);
    }
  }

  const linkedSubBot = Object.entries(db.subBots || {}).find(
    ([subPhone, subBot]) => {
      const subSocket =
        globalThis.SUBBOT_SOCKETS?.get(String(subPhone)) ||
        [...(globalThis.SUBBOT_SOCKETS?.entries?.() || [])]
          .find(([socketPhone]) =>
            String(socketPhone).replace(/\D/g, "") ===
            String(subPhone).replace(/\D/g, "")
          )?.[1];

      if (!subSocket?.user) {
        return false;
      }

      const ownerIds = new Set();
      const owner = subBot?.ownerUser;
      if (typeof owner === "string") {
        const normalized = owner.trim().toLowerCase()
          .replace(/:\d+(?=@)/, "");
        ownerIds.add(normalized);
        if (/@(s\.whatsapp\.net|c\.us)$/.test(normalized)) {
          ownerIds.add(
            `phone:${normalized.split("@")[0].replace(/\D/g, "")}`
          );
        }
      }

      return [...ownerIds].some(accountId => accountIds.has(accountId));
    }
  );

  if (linkedSubBot) {
    return sock.sendMessage(
      jid,
      {
        text:
          `@${sender.split("@")[0]} ya tienes un sub bot conectado en tu cuenta. ` +
          "No puedes vincular otra sesión.",
        mentions: [sender]
      },
      { quoted: msg }
    );
  }


  // BOT_CONNECTION_PASSWORD_INIT_V3

  db.subBots ??= {};

  const makeConnectionPassword = () => {

    const letters =
      "abcdefghijklmnopqrstuvwxyz";

    const letter =
      letters[
        Math.floor(
          Math.random() *
          letters.length
        )
      ];

    const number =
      Math.floor(
        Math.random() * 90 + 10
      );

    const hex =
      Math.floor(
        Math.random() * 0x10000
      )
      .toString(16)
      .padStart(4,"0");

    return (
      "Mavis-" +
      letter +
      number +
      "-" +
      hex
    );

  };

  const generatedConnectionPassword =
    makeConnectionPassword();

  await createSubBot({
    sock,
    jid,
    phone,
    sender,
    pairingMethod,
    ownerUser: sender,
    role: botType,
    db,
    saveDB
  });

  const createdKey =
    Object.keys(
      db.subBots || {}
    ).find(
      key =>
        String(key)
          .replace(/\D/g,"") ===
        String(phone)
          .replace(/\D/g,"")
    );

  if(createdKey){

    db.subBots[createdKey].ownerUser ??=
      sender;

    db.subBots[createdKey].role ??=
      botType;

    db.subBots[createdKey].pairingMethod =
      pairingMethod;

    db.subBots[createdKey].connectionPassword ??=
      generatedConnectionPassword;

    db.subBots[createdKey].password ??=
      db.subBots[createdKey].connectionPassword;

    db.botHosts ??= [];

    let assignedHost =
      db.subBots[createdKey].host ||
      null;

    if(!assignedHost){

      let selected = null;

      for(
        const h
        of db.botHosts
      ){

        if(
          Number(h.sessions || 0) <
          24
        ){

          selected = h;
          break;

        }

      }

      if(!selected){

        const next =
          db.botHosts.length + 1;

        selected = {
          id: next,
          name:
            "menbo" +
            next +
            "-8",
          sessions: 0
        };

        db.botHosts.push(
          selected
        );

      }

      selected.sessions =
        Number(
          selected.sessions || 0
        ) + 1;

      assignedHost =
        selected.name;

      db.subBots[createdKey].host =
        assignedHost;

    }

    saveDB();

  }

}

export async function handleMute(sock, msg, mentioned, groupData) {
  if (!mentioned.length) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Menciona a un usuario.' }, { quoted: msg, mentions: [] });
  const target = mentioned[0];
  if (target === OWNER_NUMBER) return sock.sendMessage(msg.key.remoteJid, { text: '◇ No puedes silenciar al owner del bot.' }, { quoted: msg });
  if (!groupData.muted.includes(target)) { groupData.muted.push(target); saveDB(); }
  await sock.sendMessage(msg.key.remoteJid, { text: `🔇 @${target.split('@')[0]} ha sido silenciado.`, mentions: [target] }, { quoted: msg });
}

export async function handleUnmute(sock, msg, mentioned, groupData) {
  if (!mentioned.length) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Menciona a un usuario.' }, { quoted: msg, mentions: [] });
  const target = mentioned[0];
  groupData.muted = groupData.muted.filter(jid => jid !== target); saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `🔊 @${target.split('@')[0]} puede hablar nuevamente.`, mentions: [target] }, { quoted: msg });
}

export async function handleAntilink(sock, msg, args, groupData) {
  const opt = args[1]?.toLowerCase();
  if (opt === 'on') { groupData.antilink = true; saveDB(); await sock.sendMessage(msg.key.remoteJid, { text: '✓ Antilink activado.' }, { quoted: msg }); }
  else if (opt === 'off') { groupData.antilink = false; saveDB(); await sock.sendMessage(msg.key.remoteJid, { text: '❌ Antilink desactivado.' }, { quoted: msg }); }
  else await sock.sendMessage(msg.key.remoteJid, { text: `◇ Uso: /antilink on/off (actual: ${groupData.antilink ? 'on' : 'off'})` }, { quoted: msg });
}

async function checkModeration(sock, msg, groupData, sender) {
  if (!groupData) return false;
  if (groupData.muted.includes(sender)) {
    try { await sock.sendMessage(msg.key.remoteJid, { delete: msg.key }); } catch {}
    return true;
  }
  if (groupData.antilink) {
    const text = msg.message?.conversation || msg.message?.extendedTextMessage?.text || '';
    if (/https?:\/\/[^\s]+/.test(text)) {
      try {
        const meta = await sock.groupMetadata(msg.key.remoteJid);
        const admins = meta.participants.filter(p => p.admin).map(p => p.id);
        if (!admins.includes(sender) && sender !== OWNER_NUMBER) {
          await sock.sendMessage(msg.key.remoteJid, { delete: msg.key });
          await sock.sendMessage(msg.key.remoteJid, { text: `⚠️ @${sender.split('@')[0]} eliminado por enlaces.`, mentions: [sender] });
          await sock.groupParticipantsUpdate(msg.key.remoteJid, [sender], 'remove');
          return true;
        }
      } catch {}
    }
  }
  return false;
}

// ━━━━━━━ HELP / BANNER / PREFIX / INFO ━━━━━━━
async function handleHelp(sock, msg) {

  const jid = msg.key.remoteJid;

  const banner =
    db.banners?.global;

  if (
    banner &&
    fs.existsSync(banner)
  ) {

    let buffer =
      imageCache.get(banner);

    if (!buffer) {

      buffer =
        fs.readFileSync(banner);

      imageCache.set(
        banner,
        buffer
      );

    }

    return sock.sendMessage(
      jid,
      {
        image: buffer,
        caption:
          db.helpMenu ||
          'Menú no configurado.'
      },
      {
        quoted: msg
      }
    );

  }

  await sock.sendMessage(
    jid,
    {
      text:
        db.helpMenu ||
        'Menú no configurado.'
    },
    {
      quoted: msg
    }
  );

}

export async function handleBotInfo(
  sock,
  msg
){

  const jid =
    msg.key.remoteJid;

  const normalizeNumber =
    value =>
      String(value || "")
        .split(":")[0]
        .split("@")[0]
        .replace(/\D/g,"");

  const botJid =
    String(sock.user?.id || "");

  const botNumber =
    normalizeNumber(
      sock.__subBotPhone ||
      botJid
    );

  if(!botNumber){

    return sock.sendMessage(
      jid,
      {
        text:
          "\u25c7 No se pudo identificar este bot."
      },
      { quoted: msg }
    );

  }

  db.subBots ??= {};
  db.banners ??= {};

  const activeFile =
    path.join(
      process.cwd(),
      "subbot-system",
      "active.json"
    );

  let active = {};

  try{

    if(fs.existsSync(activeFile)){

      active =
        JSON.parse(
          fs.readFileSync(
            activeFile,
            "utf8"
          )
        ) || {};

    }

  }catch(e){

    console.log(
      "BOTINFO ACTIVE ERROR:",
      e?.message || e
    );

  }

  let activeData = null;

  for(
    const [key,value]
    of Object.entries(active)
  ){

    const keyNumber =
      normalizeNumber(key);

    const jidNumber =
      normalizeNumber(value?.jid);

    if(
      keyNumber === botNumber ||
      jidNumber === botNumber
    ){

      activeData = value;
      break;

    }

  }

  let dbData = null;
  const directSubBotData =
    db.subBots?.[botNumber] ||
    db.subBots?.[`${botNumber}@s.whatsapp.net`];

  if (directSubBotData && typeof directSubBotData === 'object') {
    dbData = directSubBotData;
  }

  for(
    const [key,value]
    of Object.entries(db.subBots || {})
  ){
    if (dbData) break;

    const keyNumber =
      normalizeNumber(key);

    const valueNumber =
      normalizeNumber(
        value?.jid ||
        value?.phone ||
        value?.number
      );

    if(
      keyNumber === botNumber ||
      valueNumber === botNumber
    ){

      dbData = value;
      break;

    }

  }

  const botData = {
    ...(dbData || {}),
    ...(activeData || {})
  };

  if (!dbData && activeData) {
    db.subBots[botNumber] = {
      ownerUser: activeData.ownerUser || '',
      owner: activeData.owner || '',
      name: activeData.name || 'Mavis',
      role: activeData.role || 'Sub',
      jid: activeData.jid || `${botNumber}@s.whatsapp.net`,
      status: activeData.online ? 'online' : 'offline',
      lastConnection: Date.now()
    };
    dbData = db.subBots[botNumber];
  }

  if (
    dbData &&
    !dbData.connectionPassword &&
    !dbData.password
  ) {
    const generatedPassword =
      `Mavis-${Math.random().toString(36).slice(2, 4)}-${Math.random()
        .toString(16)
        .slice(2, 6)}`;
    dbData.connectionPassword = generatedPassword;
    dbData.password = generatedPassword;
    botData.connectionPassword = generatedPassword;
    saveDB();
  }

  const realName =
    botData.name ||
    dbData?.name ||
    sock.user?.name ||
    "Mavis";

  const role =
    botData.role ||
    dbData?.role ||
    "Sub";

  const connection =
    dbData?.connectionPassword ||
    dbData?.password ||
    botData.connectionPassword ||
    botData.password ||
    "No generada";

  const host =
    botData.host ||
    dbData?.host ||
    "menbo2-8";

  const mention =
    "@" + botNumber;

  let coins = 0;

  try{

    const candidates = [
      botJid,
      botNumber + "@s.whatsapp.net"
    ];

    for(
      const candidate
      of candidates
    ){

      const user =
        db.users?.[candidate];

      if(user){

        coins =
          Number(
            user.coins ??
            user.coin ??
            user.balance ??
            user.saldo ??
            0
          ) || 0;

        break;

      }

    }

  }catch{}

  const text =
`✧ *𝑵𝒐𝒎𝒃𝒓𝒆* »  ${realName}
✧ *𝑵𝒐𝒎𝒃𝒓𝒆 𝑳𝒂𝒓𝒈𝒐*  »  ${mention}
✧ *𝑴𝒐𝒏𝒆𝒅𝒂*  »  𐙚 ${coins.toLocaleString()} 𝒄𝒐𝒊𝒏𝒔

> *нσѕт*  »  \`${host}\`
> *𝚌𝚘𝚗𝚎𝚡𝚒𝚘𝚗*  » \`${connection}\`
> *ᴛɪᴘᴏ* »  \`${role}\`

⌁ *𝑫𝒖𝒆ñ𝒐*  »  \`Oculto por seguridad\`
    *𝑪𝒂𝒏𝒂𝒍* † \`https://whatsapp.com/channel/0029VbCvqoz6hENs6fDbor2q\``;
  const bannerKey =
    botNumber ||
    normalizeNumber(botJid);
  const bannerPath =
    db.banners?.[bannerKey] ||
    path.join(
      typeof GACHA_PATH !== "undefined"
        ? GACHA_PATH
        : process.cwd(),
      "banner.jpg"
    );

  try{

    if(
      bannerPath &&
      fs.existsSync(bannerPath)
    ){

      const buffer =
  imageCache?.get?.(bannerPath) ||
  fs.readFileSync(bannerPath);

const isGif =
  path.extname(bannerPath).toLowerCase() === '.gif';

if (isGif) {

  return sock.sendMessage(
    jid,
    {
      video: buffer,
      gifPlayback: true,
      caption: text,
      mentions: [
        botNumber + "@s.whatsapp.net"
      ]
    },
    { quoted: msg }
  );

}

return sock.sendMessage(
  jid,
  {
    image: buffer,
    caption: text,
    mentions: [
      botNumber + "@s.whatsapp.net"
    ]
  },
  { quoted: msg }
);

    }

  }catch(e){

    console.log(
      "BOTINFO BANNER ERROR:",
      e?.message || e
    );

  }

  return sock.sendMessage(
    jid,
    {
      text,
      mentions: [
        botNumber + "@s.whatsapp.net"
      ]
    },
    { quoted: msg }
  );

}


 export async function handleSetBanner(sock, msg) {
  const jid =
    msg?.key?.remoteJid || "";

  if (!jid.endsWith("@g.us")) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este comando solo puede usarse en grupos."
      },
      { quoted: msg }
    );
  }

  const normalizeJid = value => {
    if (!value) return "";

    return String(value)
      .trim()
      .replace(/:.*(?=@)/, "")
      .replace(
        /@c\.us$/i,
        "@s.whatsapp.net"
      );
  };

  const normalizeNumber = value => {
    return normalizeJid(value)
      .replace(/@.*$/, "")
      .replace(/[^0-9]/g, "");
  };

  const sameUser = (a, b) => {
    if (!a || !b) return false;

    const A = normalizeJid(a);
    const B = normalizeJid(b);

    if (A === B) return true;

    const AN = normalizeNumber(A);
    const BN = normalizeNumber(B);

    return (
      AN &&
      BN &&
      AN === BN
    );
  };

  const realSender =
    normalizeJid(
      msg?.key?.participant ||
      msg?.participant ||
      msg?.key?.remoteJid
    );
  const linkedSender =
    realSender.endsWith("@lid")
      ? db.missionLidToJid?.[realSender] ||
        missionLidToJid.get(realSender) ||
        realSender
      : realSender;
  const isMainOwner =
    isMainOwnerId(linkedSender) ||
    normalizeNumber(linkedSender) ===
      OWNER_CONTACT_NUMBER;

  /*
   * ============================================================
   * EL BOT DEBE SER PRIMARY EN ESTE GRUPO
   * ============================================================
   */

  db.primaryBots ??= {};

  const primaryRaw =
    db.primaryBots[jid];

  if (!primaryRaw) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este grupo no tiene un bot primary."
      },
      { quoted: msg }
    );
  }

  const primaryNumber =
    normalizeNumber(primaryRaw);

  const socketNumber =
    normalizeNumber(
      sock?.user?.id
    );

  if (
    !primaryNumber ||
    !socketNumber ||
    primaryNumber !== socketNumber
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este bot no es el primary de este grupo."
      },
      { quoted: msg }
    );
  }

  /*
   * ============================================================
   * IDENTIFICAR LA SESIÓN Y SU OWNER ACTUAL
   * ============================================================
   */

  let registeredOwner = null;

  const botPhone =
    socketNumber;

  const isSubBot =
    !!sock.__subBotPhone;

  if (isSubBot) {
    let active = {};

    try {
      if (fs.existsSync(ACTIVE)) {
        active =
          JSON.parse(
            fs.readFileSync(
              ACTIVE,
              "utf8"
            )
          ) || {};
      }
    } catch {}

    let activeBot = null;

    for (const [key, value] of Object.entries(active)) {
      const candidateNumbers = [
        key,
        value?.jid,
        value?.phone,
        value?.number,
        value?.id,
        value?.user?.id
      ]
        .filter(Boolean)
        .map(normalizeNumber);

      if (
        candidateNumbers.includes(botPhone)
      ) {
        activeBot = value;
        break;
      }
    }

    db.subBots ??= {};

    let dbBot = null;

    for (const [key, value] of Object.entries(db.subBots)) {
      const candidateNumbers = [
        key,
        value?.jid,
        value?.phone,
        value?.number,
        value?.id,
        value?.user?.id
      ]
        .filter(Boolean)
        .map(normalizeNumber);

      if (
        candidateNumbers.includes(botPhone)
      ) {
        dbBot = value;
        break;
      }
    }

    registeredOwner =
      activeBot?.ownerUser ||
      dbBot?.ownerUser ||
      null;
  } else {
    registeredOwner =
      typeof getMainOwner === "function"
        ? getMainOwner()
        : db.primaryOwner ||
          OWNER_NUMBER;
  }

  if (!registeredOwner && !isMainOwner) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Esta sesión no tiene un dueño registrado."
      },
      { quoted: msg }
    );
  }

  /*
   * ============================================================
   * SOLO EL OWNER ACTUAL DE ESTA SESIÓN
   * ============================================================
   */

  if (
    !isMainOwner &&
    !sameUser(
      realSender,
      registeredOwner
    )
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ No tienes permiso para usar este comando.\n\n" +
          "Solo el dueño actual de esta sesión puede cambiar su banner."
      },
      { quoted: msg }
    );
  }

  /*
   * ============================================================
   * IMAGEN / GIF CITADO
   * ============================================================
   */

  const qm =
    msg.message
      ?.extendedTextMessage
      ?.contextInfo
      ?.quotedMessage;

  const isImage =
    !!qm?.imageMessage;

  const isGif =
    !!qm?.videoMessage?.gifPlayback;

  if (!isImage && !isGif) {
    return sock.sendMessage(
      jid,
      {
        text:
          "◇ Cita una imagen o un GIF."
      },
      { quoted: msg }
    );
  }

  try {
    const buffer =
      await downloadMediaMessage(
        {
          key: {
            ...msg.key,
            id:
              msg.message
                .extendedTextMessage
                .contextInfo
                .stanzaId
          },
          message: qm
        },
        "buffer",
        {}
      );

    const extension =
      isGif
        ? "gif"
        : "jpg";

    if (!botPhone) {
      throw new Error(
        "No se pudo identificar la sesión del bot."
      );
    }

    db.banners ??= {};

    const bannerPath =
      path.join(
        GACHA_PATH,
        `banner_${botPhone}.${extension}`
      );

    fs.writeFileSync(
      bannerPath,
      buffer
    );

    db.banners[botPhone] =
      bannerPath;

    imageCache.set(
      bannerPath,
      buffer
    );

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
          isGif
            ? "◇ GIF establecido como banner."
            : "◇ Imagen establecida como banner."
      },
      { quoted: msg }
    );
  } catch (e) {
    console.error(
      "[SETBANNER ERROR]",
      e
    );

    await sock.sendMessage(
      jid,
      {
        text:
          "❌ No se pudo establecer el banner."
      },
      { quoted: msg }
    );
  }
}

export async function handleSetPrefix(sock, msg, args) {
  const p = args[0];
  if (!p || p.length !== 1) return sock.sendMessage(msg.key.remoteJid, { text: `◇ Uso: ${db.prefix || '/'}setbotprefix <carácter>` }, { quoted: msg });
  db.prefix = p; saveDB();
  await sock.sendMessage(msg.key.remoteJid, { text: `◇ Prefijo cambiado a *${p}*` }, { quoted: msg });
}

export async function handleInfousuario(sock, msg, mentioned, quotedUser, groupId) {
  const target = mentioned.length ? mentioned[0] : quotedUser;
  if (!target) return sock.sendMessage(msg.key.remoteJid, { text: '◇ Menciona o cita a un usuario.' }, { quoted: msg });
  const u = db.users[target];
  const g = db.groups[groupId];
  const stats = g?.members?.[target] || {};
  const txt = `•­【 Stats 〕•®\n` +
    `│▪︎ Usuario: @${target.split('@')[0]}\n` +
    `│▪︎ Mensajes: \`${stats.messages || 0}\`\n` +
    `│▪︎ Msg/seg: \`${((stats.messages || 0) / Math.max(1, (Date.now() - (stats.firstMessage || Date.now())) / 1000)).toFixed(2)}\`\n` +
    `│▪︎ Menciones: \`${stats.mentions || 0}\`\n` +
    `│▪︎ Comandos: \`${u?.totalCommands || 0}\`\n` +
    `•°【● Datos ●〕•¯`;
  await sock.sendMessage(msg.key.remoteJid, { text: txt, mentions: [target] }, { quoted: msg });
}

export async function handleGp(sock, msg, groupId) {

  const meta =
    await sock.groupMetadata(groupId);

  const totalChars =
    charactersCache.length;

  let claimed = 0;

  for (const char of charactersCache) {
    if (char.claimedBy?.[groupId]) {
      claimed++;
    }
  }

  const percent =
    totalChars > 0
      ? ((claimed / totalChars) * 100)
          .toFixed(2)
      : "0.00";

  const botName =
    sock.user?.name ||
    "Bot";

  const text =
`「✿」Grupo ◢ ${meta.subject}

◈ Usuarios » ${meta.participants.length}
✰ Registrados » ${Object.keys(db.users).length}
❖ Bot principal » ${botName}

♡ Claims » ${claimed} (${percent}%)
❬ Personajes » ${totalChars}

☆ ${botName} ✓ Activado
☆ Anti-Links » ${db.groups[groupId]?.antilink ? '✓ Activado' : '✘ Desactivado'}
`;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}

export async function handlePfp(sock, msg, mentioned) {

  if (!mentioned.length) {
    return sock.sendMessage(
      msg.key.remoteJid,
      { text: '◇ Menciona a un usuario.' },
      { quoted: msg }
    );
  }

  const target = mentioned[0];

  try {

    const url =
      await sock.profilePictureUrl(
        target,
        'image'
      ).catch(() => null);

    if (!url) {
      return sock.sendMessage(
        msg.key.remoteJid,
        { text: '◇ Sin foto.' },
        { quoted: msg }
      );
    }

    const buffer =
      Buffer.from(
        await (
          await fetch(url)
        ).arrayBuffer()
      );

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        image: buffer,
        caption:
          `Foto de @${target.split('@')[0]}`,
        mentions: [target]
      },
      { quoted: msg }
    );

  } catch {

    await sock.sendMessage(
      msg.key.remoteJid,
      { text: '❌ Error.' },
      { quoted: msg }
    );

  }
}

export async function handleCleanImg(
  sock,
  msg,
  nombre,
  valor,
  genero,
  anime,
  rareza,
  chance,
  tag
){ 
      msg.key.participant || jid;

    const sender =
  msg.key.participant ||
  msg.participant ||
  msg.key.remoteJid;

recentImages[sender] ??= [];

recentImages[sender].push({
  msg,
  time: Date.now()
});

const isStaff =
  isMainOwnerId(sender) ||
  isSecondaryOwnerId(sender);

  const jid = msg.key.remoteJid;

  let images = [];

if (
  !tag ||
  !tag.trim()
){

  images =
    pendingAlbums[sender]
      ? [...pendingAlbums[sender]]
      : [];

}
else{

  if (
    recentImages[sender]
  ){

    images =
      [...recentImages[sender]];

  }

}


if (!images.length){

  return sock.sendMessage(
    jid,
    {
      text:
`◇ Debes responder una imagen o un ¿lbum usando /cleanimg cuando no utilices un tag.`
    },
    {
      quoted:msg
    }
  );

}

const normalizar = t =>
  t
    .toLowerCase()
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g,'')
    .trim();

const existente =
  charactersCache.find(
    c =>
      normalizar(c.name) ===
      normalizar(nombre)
  );

if (
  existente &&
  sender !== OWNER_NUMBER
){

  const sugerencia =
    `${nombre} (${anime})`;

  /*
 * ============================================================
 * ADDP -> PERSONAJE YA EXISTENTE
 * ============================================================
 *
 * El personaje ya existe globalmente.
 * NO se detiene la cola.
 * Se registra y se continúa con el siguiente.
 */

if (
  typeof db.addpQueue !== 'undefined' &&
  db.addpQueue[jid]
) {

  const colaAddP =
    db.addpQueue[jid];

  if (
    colaAddP.resultados &&
    Array.isArray(colaAddP.resultados)
  ) {

    colaAddP.resultados.push({
      name:
        typeof nombre !== 'undefined'
          ? nombre
          : (
              typeof personaje !== 'undefined'
                ? personaje.name
                : 'Desconocido'
            ),

      status:
        'Ya existe',

      existingId:
        typeof existente !== 'undefined'
          ? existente.id
          : null
    });

  }

  if (
    typeof colaAddP.index === 'number'
  ) {

    colaAddP.index++;

  }

  /*
   * Continuar ADDP en el siguiente tick.
   * Esto evita problemas por respuestas encadenadas.
   */

  setTimeout(() => {

    try {

      enviarSiguienteAddP(jid);

    } catch (err) {

      console.error(
        ' ADDP error continuando después de personaje existente:',
        err
      );

    }

  }, 100);

}
return sock.sendMessage(
    jid,
    {
      text:
` El nombre *${existente.name}* está ocupado por *${existente.anime}*.

Usa:
*${sugerencia}*`
    },
    {
      quoted: msg
    }
  );
}

  const key = nombre
    .toLowerCase()
    .replace(/[^\w]/g, '_');

const rarities = [
  'Comun',
  'Raro',
  'Epico',
  'Legendario',
  'Mitico',
  'Mod'
];

if (!rarities.includes(rareza)) {
  return sock.sendMessage(jid,{
    text:
`Rareza inválida.

Disponibles:
• Comun
• Raro
• Epico
• Legendario
• Mitico
• Mod`
  },{ quoted: msg });
}

const chanceNum =
  parseFloat(
    String(chance).replace('%','')
  );

if (
  isNaN(chanceNum) ||
  chanceNum <= 0 ||
  chanceNum > 100
) {
  return sock.sendMessage(jid,{
    text:'La probabilidad debe estar entre 1% y 100%.'
  },{ quoted: msg });
}

let testImage = null;

const manualTagEntry =
  tag &&
  tag.trim().length > 0
    ? getManualTag(tag)
    : null;

const useManualTag =
  Boolean(manualTagEntry);

const useDanbooru =
  Boolean(
    tag &&
    tag.trim().length > 0 &&
    !useManualTag
  );

if (useManualTag){

  const manualImages =
    Array.isArray(manualTagEntry.images)
      ? manualTagEntry.images
      : [];

  const validManualImages =
    manualImages.filter(image => {

      if (!image?.file) {
        return false;
      }

      const filePath =
        path.join(
          process.cwd(),
          'manual-tags',
          'images',
          normalizeManualTag(tag),
          image.file
        );

      return fs.existsSync(filePath);
    });

  if (!validManualImages.length){
    return sock.sendMessage(
      jid,
      {
        text:
          `》*El tag "${tag}" existe, pero no tiene imágenes disponibles.*`
      },
      {
        quoted: msg
      }
    );
  }

  const selectedManualImage =
    validManualImages[
      Math.floor(
        Math.random() *
        validManualImages.length
      )
    ];

  const manualImagePath =
    path.join(
      process.cwd(),
      'manual-tags',
      'images',
      normalizeManualTag(tag),
      selectedManualImage.file
    );

  try{
    testImage =
      fs.readFileSync(
        manualImagePath
      );
  }catch(error){
    console.log(
      '[CLEANIMG] Error leyendo imagen de Bulguru:',
      error?.message || error
    );

    return sock.sendMessage(
      jid,
      {
        text:
          '◇ No se pudo leer la imagen local del tag.'
      },
      {
        quoted: msg
      }
    );
  }

}else if (useDanbooru){

  testImage =
    await getGelbooruImage(tag);

  if (!testImage){
    testImage =
      await getGelbooruApiImage(tag);
  }

  if (!testImage){
    const tags =
      await searchDanbooruTags(
        tag.split('(')[0]
      );

    const sugerencias =
      tags
        .slice(0,3)
        .map(
          (t,i)=>
            `${i+1}. \`${t.name}\``
        )
        .join('\n');

    return sock.sendMessage(
      jid,
      {
        text:
`》*El tag no existe, puedes encontrarlo en las paginas oficiales*                                   ✿ *Pagina Gelbooru* \`https://gelbooru.com/\`                                                        ✿ *Pagina Danbooru* \`https://danbooru.donmai.us/\``
      },
      {
        quoted: msg
      }
    );
  }
}

const character = {
   id:
      charactersCache.length
      ? Math.max(...charactersCache.map(c => c.id || 0)) + 1
      : 1,

   key,

   name: nombre,
   anime: anime,
   gender: genero,
   value: Number(valor),
   rarity: rareza,
   chance: chance,
 
   tag:
    (useDanbooru || useManualTag)
      ? tag
      : null,
creator: sender,
createdAt: Date.now(),
  
   coinGen: Math.floor(55 * Number(valor)),
   votes: 0,
   images,
   claimedBy: {}
};

for (const char of charactersCache) {

  if (typeof char.coinGen !== 'number')
    char.coinGen = 0;

  if (!char.rarity)
    char.rarity = 'Comun';

  if (!char.chance)
    char.chance = '100%';
}


  charactersCache.push(character);

delete pendingAlbums[sender];
delete recentImages[sender];

  characterMap.set(
    nombre.toLowerCase(),
    character
  );

  characterKeyMap.set(
    key,
    character
  );

  let num = 1;

  for (const imgData of images) {

    try {

      const buffer =
        await downloadMediaMessage(
          imgData.msg,
          'buffer',
          {}
        );

      const file =
  path.join(
    GACHA_IMAGES,
    `${key}_${num}.jpg`
  );

fs.writeFileSync(file, buffer);

imageCache.set(file, buffer);

num++;

    } catch {}
  }


  saveCharacters();

  if (
    isStaff
  ) {

    const profile =

      getStaffProfile(
        sender
      );

    profile.status += 5000;

    saveDB();

  }

  const serieKey =
    anime.toLowerCase();

  let serie =
    seriesCache.get(serieKey);

  if (!serie) {

    /*
     * ID permanente de la serie.
     */
    const idsSeries =
      [...seriesCache.values()]
        .map(s => Number(s.id))
        .filter(
          n =>
            Number.isInteger(n) &&
            n > 0
        );

    const nuevoIdSerie =
      idsSeries.length
        ? Math.max(...idsSeries) + 1
        : 1;

    serie = {
      id: nuevoIdSerie,
      name: anime,
      characters: new Set()
    };

    seriesCache.set(
      serieKey,
      serie
    );
  }

  serie.characters.add(key);

  fs.writeFileSync(
    path.join(
      SERIES_DIR,
      `${serieKey.replace(/[^\w]/g,'_')}.json`
    ),
    JSON.stringify({
      id: Number(serie.id),
      name: anime,
      characters:
        [...serie.characters]
    }, null, 2)
  );

  recentImages[jid] = [];

  const creatorName =
  db.users?.[sender]?.name ||
  sender.split('@')[0];

const caption =
`✓ Personaje creado

◇ *Nombre* » \`${nombre}\`
☆ *Anime* » \`${anime}\`
♧ *Tag* » \`${tag || 'Sin Tag'}\`
○ *Im¿genes locales* » \`${useDanbooru ? 'No' : 'S¿'}\`

□ *ID* » \`${character.id}\`
♡ *Rareza* » \`${rareza}\`
? *Valor* » \`¥${Number(valor).toLocaleString()}\`
▪︎ *Chance* » \`${chance}\`
★ *Creador* » \`${creatorName}\``;

if (useManualTag) {

  await sock.sendMessage(
    jid,
    {
      image: testImage,
      caption
    },
    {
      quoted: msg
    }
  );

} else if (useDanbooru) {

  await sock.sendMessage(
    jid,
    {
      image: {
        url: testImage
      },
      caption
    },
    {
      quoted: msg
    }
  );

} else {

  const primera =
    path.join(
      GACHA_IMAGES,
      `${key}_1.jpg`
    );

  await sock.sendMessage(
    jid,
    {
      image:
        fs.readFileSync(primera),
      caption
    },
    {
      quoted: msg
    }
  );

}
}

// MISIONS_SYSTEM_V1

function normalizarMision(texto) {

  return String(
    texto || ""
  )
    .toLowerCase()
    .normalize("NFD")
    .replace(
      /[\u0300-\u036f]/g,
      ""
    )
    .replace(
      /\s+/g,
      " "
    )
    .trim();

}

function formatMissionTime(
  milliseconds
) {

  let total =
    Math.max(
      0,
      Math.floor(
        milliseconds / 1000
      )
    );

  const dias =
    Math.floor(
      total / 86400
    );

  total %= 86400;

  const horas =
    Math.floor(
      total / 3600
    );

  total %= 3600;

  const minutos =
    Math.floor(
      total / 60
    );

  const segundos =
    total % 60;

  const partes = [];

  if (dias) {
    partes.push(
      dias +
      " día" +
      (
        dias === 1
          ? ""
          : "s"
      )
    );
  }

  if (horas) {
    partes.push(
      horas +
      " hora" +
      (
        horas === 1
          ? ""
          : "s"
      )
    );
  }

  if (minutos) {
    partes.push(
      minutos +
      " minuto" +
      (
        minutos === 1
          ? ""
          : "s"
      )
    );
  }

  if (
    !partes.length ||
    (
      !dias &&
      !horas &&
      !minutos
    )
  ) {
    partes.push(
      segundos +
      " segundo" +
      (
        segundos === 1
          ? ""
          : "s"
      )
    );
  }

  return partes
    .slice(
      0,
      3
    )
    .join(", ");

}

function getMissionStore() {

  db.misions ??= {
    lastId: 0,
    list: []
  };

  if (
    !Array.isArray(
      db.misions.list
    )
  ) {
    db.misions.list = [];
  }

  if (
    typeof db.misions.lastId !==
    "number"
  ) {
    db.misions.lastId = 0;
  }

  return db.misions;

}

function formatMissionMention(jid) {
  const value = String(jid || '').trim();
  return value ? `@${value.split('@')[0]}` : '@usuario';
}

function normalizeStaffId(value) {
  const raw = String(value || '').trim();
  if (!raw) return '';
  if (raw.includes('@')) return raw.toLowerCase();
  return `${raw}@lid`;
}

function getStaffDisplayName(staffJid, fallbackJid = staffJid) {
  const key = normalizeStaffId(staffJid);
  const name = db.staffNames?.[key];
  return name ? `@${name}` : formatMissionMention(fallbackJid);
}

async function handleNameStaff(sock, msg, args, jid, sender) {
  if (!isMainOwnerId(sender)) {
    return sock.sendMessage(jid, {
      text: '❌ Solo el owner principal puede usar este comando.'
    }, { quoted: msg });
  }

  const input = args.join(' ').trim();
  const separator = input.indexOf('/');
  if (separator <= 0) {
    return sock.sendMessage(jid, {
      text: '◇ Uso: /namestaff LID / nombre de usuario'
    }, { quoted: msg });
  }

  const staffId = normalizeStaffId(input.slice(0, separator));
  const displayName = input.slice(separator + 1).trim().replace(/^@+/, '');
  if (!staffId.endsWith('@lid') || !displayName) {
    return sock.sendMessage(jid, {
      text: '◇ Debes indicar un LID y un nombre después de /.'
    }, { quoted: msg });
  }

  db.staffNames[staffId] = displayName;
  saveDB();

  await sock.sendMessage(jid, {
    text: `✓ Nombre de staff actualizado.\n\nLID: ${staffId}\nNombre: @${displayName}`
  }, { quoted: msg });
}

async function resolveMissionMentionTarget(sock, groupJid, participantJid) {
  const stored = String(participantJid || '').trim();
  if (!stored.endsWith('@lid')) {
    return stored;
  }

  const cached = missionLidToJid.get(stored);
  if (cached) {
    return cached;
  }

  try {
    if (groupJid?.endsWith('@g.us')) {
      const metadata = await sock.groupMetadata(groupJid);
      const participant = metadata.participants?.find(item =>
        item.id === stored || item.lid === stored
      );
      const resolved = participant?.jid || participant?.id;
      if (resolved && !resolved.endsWith('@lid')) {
        missionLidToJid.set(stored, resolved);
        return resolved;
      }
    }
  } catch (error) {
    console.warn('⚠️ No se pudo resolver LID de misión:', error.message);
  }

  return stored;
}

export async function handleCreateMission(
  sock,
  msg,
  args,
  jid,
  sender
) {

  if (!isMainOwnerId(sender)) {

    return sock.sendMessage(
      jid,
      {
        text:
`❌ Solo el owner principal puede crear misiones.`
      },
      {
        quoted: msg
      }
    );

  }

  const text =
    args
      .join(" ")
      .trim();

  const missionParts = text
    .replace(/^\+/, "")
    .split("/")
    .map(part => part.trim())
    .filter(Boolean);

  const partes = missionParts[0]?.split(/\s+/) || [];

  const staffNumber =
    Number(
      partes[0]
    );

  const accion =
    String(
      partes[1] || ""
    )
      .toLowerCase();

  const missionAmount =
    Number(
      partes[2]
    );

  const palabra =
    String(
      partes[3] || ""
    )
      .toLowerCase();

  const de =
    String(
      partes[4] || ""
    )
      .toLowerCase();

  const missionAnime =
    partes.slice(5).join(" ").trim();

  const rewardStatus =
    Number(missionParts[1]);

  const match =
    Number.isInteger(
      staffNumber
    ) &&
    staffNumber > 0 &&
    [
      "haz",
      "crea",
      "crear"
    ].includes(
      accion
    ) &&
    Number.isInteger(
      missionAmount
    ) &&
    missionAmount > 0 &&
    (
      palabra ===
      "personaje" ||
      palabra ===
      "personajes"
    ) &&
    de ===
    "de" &&
    missionAnime
      &&
    Number.isInteger(rewardStatus) &&
    rewardStatus > 0
      ? [
          null,
          String(
            staffNumber
          ),
          String(
            missionAmount
          ),
          missionAnime,
          String(rewardStatus)
        ]
      : null;

  if (!match) {
    const staffMentionTargets = await Promise.all(
      SECONDARY_OWNERS.map(staff =>
        resolveMissionMentionTarget(sock, jid, staff)
      )
    );

    return sock.sendMessage(
      jid,
      {
        text:
`☆ USO DE MISIÓN

♤ Formato »

/mision +número haz cantidad personajes de Anime / status

♡ Ejemplo »

/mision +1 haz 20 personajes de Zenless Zone Zero / 829339

▪︎ Staff disponibles »

${SECONDARY_OWNERS
  .map(
    (
      staff,
      index
    ) =>
      `+${index + 1} » ${getStaffDisplayName(staff, staffMentionTargets[index])}`
  )
  .join("\n")}`
      },
      {
        quoted: msg,
        mentions:
          staffMentionTargets
      }
    );

  }

  const staffIndex =
    Number(
      match[1]
    ) - 1;

  const amount =
    Number(
      match[2]
    );

  const anime =
    match[3]
      .trim();
  const missionReward =
    Number(match[4]);

  const staff =
    SECONDARY_OWNERS[
      staffIndex
    ];
  const staffMentionTarget =
    await resolveMissionMentionTarget(sock, jid, staff);

  if (!staff) {

    return sock.sendMessage(
      jid,
      {
        text:
`❌ El staff +${staffIndex + 1} no existe.`
      },
      {
        quoted: msg
      }
    );

  }

  if (
    !Number.isInteger(
      amount
    ) ||
    amount < 1
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ La cantidad debe ser un número mayor a 0."
      },
      {
        quoted: msg
      }
    );

  }

  fs.appendFileSync("debug-misions.log", "sender=" + sender + "\n");

  const store =
    getMissionStore();

  const activeMission =
    store.list.find(
      mission =>
        mission.status ===
          "active" &&
        mission.staff ===
          staff
    );

  if (activeMission) {

    return sock.sendMessage(
      jid,
      {
        text:
`❌ Ese staff ya tiene una misión activa.

♤ Staff »
${getStaffDisplayName(staff, staffMentionTarget)}

♡ Objetivo »
Crear ${activeMission.amount} personajes de ${activeMission.anime}

◇ Recompensa »
${Number(activeMission.rewardStatus || 0).toLocaleString()} status

▪︎ Progreso »
${activeMission.progress}/${activeMission.amount}`
      },
      {
        quoted: msg,
        mentions: [
          staffMentionTarget
        ]
      }
    );

  }

  store.lastId++;

  const mission = {

    id:
      store.lastId,

    staff,

    amount,

    anime,
    rewardStatus: missionReward,
    rewardClaimed: false,

    progress: 0,

    status:
      "active",

    createdAt:
      Date.now(),

    completedAt:
      null

  };

  store.list.push(
    mission
  );

  saveDB();

  // MISSION_SUGGESTLOGS_NOTICE_V1
  // Envía el aviso al grupo configurado con /suggestlogs on.
  // Si falla el aviso, la misiï¿½n seguirï¿½ creada normalmente.
  if (db.suggestLogs) {

    try {

      await sock.sendMessage(
        db.suggestLogs,
        {
          text:
`${getStaffDisplayName(staff, staffMentionTarget)} Tienes una nueva misiï¿½n, revï¿½sala con */misions*.`,

          mentions: [
            staffMentionTarget
          ]
        }
      );

    } catch (error) {

      console.error(
        "⚠️ No se pudo enviar el aviso de misi¿n a Suggest Logs:",
        error?.message || error
      );

    }

  }

  await sock.sendMessage(
    jid,
    {
      text:
`☆ MISIÓN ASIGNADA

♤ Staff »
${getStaffDisplayName(staff, staffMentionTarget)}

♡ Objetivo »
Crear ${amount} personajes de ${anime}

◇ Recompensa »
${missionReward.toLocaleString()} status

▪︎ Progreso »
0/${amount}

• Estado »
En progreso

 La misiï¿½n se firmarï¿½ automï¿½ticamente al completarse.`,

      mentions: [
        staffMentionTarget
      ]

    },
    {
      quoted: msg
    }
  );

}



export async function handleDelMision(
  sock,
  msg,
  jid,
  sender,
  args
) {

  if (
    sender !== OWNER_NUMBER
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Solo el owner principal puede usar este comando."
      },
      {
        quoted: msg
      }
    );

  }

  const idText =
    (args[0] || "")
      .replace("+", "")
      .trim();

  const id =
    Number(idText);

  if (
    !id ||
    isNaN(id)
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
`❌ Uso correcto:

/delmision +ID

Ejemplo:
/delmision +1`
      },
      {
        quoted: msg
      }
    );

  }

  const store =
    getMissionStore();

  const index =
    store.list.findIndex(
      mission =>
        mission.id === id
    );

  if (
    index === -1
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ No existe una misión con ese ID."
      },
      {
        quoted: msg
      }
    );

  }

  const mission =
    store.list[index];
  const missionMentionTarget =
    await resolveMissionMentionTarget(sock, jid, mission.staff);

  store.list.splice(
    index,
    1
  );

  saveDB();

  await sock.sendMessage(
    jid,
    {
      text:
`✓ Misión eliminada.

ID:
${mission.id}

Staff:
${getStaffDisplayName(mission.staff, missionMentionTarget)}

Objetivo:
Crear ${mission.amount} personajes de ${mission.anime}`,
      mentions: [
        missionMentionTarget
      ]
    },
    {
      quoted: msg
    }
  );

}

export async function handleMisions(
  sock,
  msg,
  jid,
  sender
) {

  const store =
    getMissionStore();

  let missions =
    store.list;

  if (
    sender !== OWNER_NUMBER
  ) {

    missions =
      missions.filter(
        mission => {
          const missionStaff =
            String(mission.staff || "")
              .replace(/\\D/g, "");

          const senderId =
            String(sender || "")
              .replace(/\\D/g, "");

          return missionStaff === senderId;
        }
      );

  }

  for (
    const mission of missions
  ) {

    if (
      mission.status !==
      "active"
    ) continue;

    const count =
      charactersCache.filter(
        char =>
          char.creator?.split("@")[0] ===
            mission.staff.split("@")[0] &&
          normalizarMision(
            char.anime
          ) ===
          normalizarMision(
            mission.anime
          )
      ).length;

    if (
      count >
      mission.progress
    ) {

      mission.progress =
        Math.min(
          count,
          mission.amount
        );

      if (
        mission.progress >=
        mission.amount
      ) {

        mission.status =
          "completed";

        mission.completedAt =
          Date.now();

        if (!mission.rewardClaimed) {
          const profile = getStaffProfile(mission.staff);
          profile.status += Number(mission.rewardStatus) || 0;
          mission.rewardClaimed = true;
        }

      }

    }

  }

  saveDB();

  const active =
    missions.filter(
      mission =>
        mission.status ===
        "active"
    );

  if (!active.length) {

    return sock.sendMessage(
      jid,
      {
        text:
          "☆ No hay misiones activas."
      },
      {
        quoted: msg
      }
    );

  }

  const activeMentionTargets = await Promise.all(
    active.map(mission =>
      resolveMissionMentionTarget(sock, jid, mission.staff)
    )
  );

  const text =
    active
      .map(
        (
          mission,
          index
        ) =>
`☆ MISIÓN ${index + 1}

♤ Staff »
${getStaffDisplayName(mission.staff, activeMentionTargets[index])}

♡ Objetivo »
Crear ${mission.amount} personajes de ${mission.anime}

◇ Recompensa »
${Number(mission.rewardStatus || 0).toLocaleString()} status

▪︎ Progreso »
${mission.progress}/${mission.amount}

• Estado »
En progreso`
      )
      .join(
        "\\n\\n"
      );

  await sock.sendMessage(
    jid,
    {
      text,

      mentions:
        [
          ...new Set(
            activeMentionTargets.filter(Boolean)
          )
        ]

    },
    {
      quoted: msg
    }
  );

}

async function checkMissionProgress(
  sock,
  msg,
  character
) {

  const sender =
    msg.key.participant ||
    msg.participant;

  const store =
    getMissionStore();

  const mission =
    store.list.find(
      item =>
        item.status ===
          "active" &&
        item.staff ===
          sender &&
        normalizarMision(
          item.anime
        ) ===
        normalizarMision(
          character.anime
        )
    );

  if (!mission) {
    return;
  }

  mission.progress++;

  const jid =
    msg.key.remoteJid;

  if (
    mission.progress <
    mission.amount
  ) {

    saveDB();

    return sock.sendMessage(
      jid,
      {
        text:
`☆ MISIÓN AVANZANDO

♤ Staff »
${getStaffDisplayName(sender)}

♡ Objetivo »
Crear ${mission.amount} personajes de ${mission.anime}

◇ Recompensa »
${Number(mission.rewardStatus || 0).toLocaleString()} status

▪︎ Progreso »
${mission.progress}/${mission.amount}

• Restantes »
${mission.amount - mission.progress}`,

        mentions: [
          sender
        ]

      },
      {
        quoted: msg
      }
    );

  }

  mission.progress =
    mission.amount;

  mission.status =
    "completed";

  mission.completedAt =
    Date.now();

  if (!mission.rewardClaimed) {
    const profile = getStaffProfile(mission.staff);
    profile.status += Number(mission.rewardStatus) || 0;
    mission.rewardClaimed = true;
  }

  saveDB();

  const tiempo =
    formatMissionTime(
      mission.completedAt -
      mission.createdAt
    );

  const staffTag =
    getStaffDisplayName(sender);

  const privateText =
`☆ MISIÓN COMPLETADA

♤ Staff »
${staffTag}

♡ Objetivo »
Crear ${mission.amount} personajes de ${mission.anime}

◇ Recompensa »
${Number(mission.rewardStatus || 0).toLocaleString()} status

▪︎ Resultado »
${mission.progress}/${mission.amount}

• Tiempo »
${tiempo}

 Misiï¿½n firmada automï¿½ticamente.`;

  const groupText =
`☆ MISIÓN FINALIZADA

♤ ${staffTag} cumpli¿ su misi¿n.

♡ Objetivo »
Crear ${mission.amount} personajes de ${mission.anime}

▪︎ Resultado »
${mission.progress}/${mission.amount}

• Tiempo »
${tiempo}

☆ Misión completada.`;

  try {

    await sock.sendMessage(
      OWNER_NUMBER,
      {
        text:
          privateText,

        mentions: [
          sender
        ]

      }
    );

  } catch (
    error
  ) {

    console.log(
      "⚠️ No se pudo enviar el aviso privado de misi¿n:",
      error.message
    );

  }

  await sock.sendMessage(
    jid,
    {
      text:
        groupText,

      mentions: [
        sender
      ]

    },
    {
      quoted: msg
    }
  );

}

export async function handleSetCoinsG(
  sock,
  msg,
  args,
  jid,
  sender
){

  const text =
    args.join(' ');

  const parts =
    text.split('/').map(x => x.trim());

  if (parts.length < 3) {
    return sock.sendMessage(jid,{
      text:
`Uso:

/setcoinsg nombre / anime / coins

Ejemplo:
/setcoinsg Nazuna Nanakusa / Yofukashi no Uta / 5230`
    },{ quoted: msg });
  }

  const nombre = parts[0];
  const anime = parts[1];
  const coins = Number(parts[2]);

  if (isNaN(coins) || coins < 0) {
    return sock.sendMessage(jid,{
      text:'Cantidad inválida.'
    },{ quoted: msg });
  }

  const char =
findCharacter(nombre);

  if (!char) {
    return sock.sendMessage(jid,{
      text:'Personaje no encontrado.'
    },{ quoted: msg });
  }

  char.coinGen = coins;

  saveCharacters();

  await sock.sendMessage(jid,{
    text:
`✰ Generaci¿n modificada.

❬ Personaje » ${char.name}
❖ Fuente » ${char.anime}
◇ Coins/min » ${coins}`
  },{ quoted: msg });
}

export async function handleAinfoCoinsG(
  sock,
  msg,
  args,
  sender
){

  if (sender != OWNER_NUMBER)
  return;

  const anime =
    args
    .join(' ')
    .trim();

  if (!anime) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Uso: /ainfocoinsg [anime]'
      },
      {
        quoted: msg
      }
    );

  }

  const chars =
    charactersCache.filter(
      c =>
        c.anime
        .toLowerCase()
        .includes(
          anime.toLowerCase()
        )
    );

  if (!chars.length) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'◇ Serie no encontrada.'
      },
      {
        quoted: msg
      }
    );

  }

  let text =
`❬ ${anime}

□ Personajes » ${chars.length}

Lista:

`;

  for (
  const char of chars.filter(
    c =>
      Number(
        c.coinGen || 0
      ) <= 0
  )
) {

    text +=
`*${char.name}* = \`${Number(
  char.coinsGen || 0
).toLocaleString()}/m\`\n`;

  }

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );

}

export async function handleCoinsG(
  sock,
  msg,
  groupId,
  sender
){

  const harem =
    db.groups[groupId]
    ?.harems?.[sender] || [];

  let total = 0;

  let text =
`◇ Generaci¿n pasiva\n\n`;

  for (const char of harem) {

    const original =
      characterKeyMap.get(char.key);

    const gen =
      original?.coinGen || 0;

    if (gen <= 0)
      continue;

    total += gen;

    text +=
`${char.name} » ${gen}/hora\n`;
  }

  text +=
`\nTotal » ${total.toLocaleString()}/hora`;

  await sock.sendMessage(
    msg.key.remoteJid,
    { text },
    { quoted: msg }
  );
}


async function createSubBot_OLD(
 sock,
 jid,
 number
){

const phone = String(number).replace(/\\D/g,'');

if(Object.keys(db.subBots||{}).length >= 5){

return sock.sendMessage(
jid,
{
text:
" Lï¿½mite máximo de 5 subbots alcanzado."
}
);

}


const folder =
path.join(
 SUBBOTS_DIR,
 "sub_"+phone
);


if(!fs.existsSync(folder)){
 fs.mkdirSync(folder,{
 recursive:true
 });
}


const {state,saveCreds}=await useMultiFileAuthState(folder);


const {version}=await fetchLatestBaileysVersion();


const subSock=makeWASocket({

version,

auth:state,

logger:P({
level:"silent"
}),

browser:
Browsers.windows("Chrome"),

printQRInTerminal:false,

syncFullHistory:false,

markOnlineOnConnect:false

});


subSock.ev.on(
"creds.update",
saveCreds
);



let opened=false;


subSock.ev.on(
"connection.update",
async(update)=>{


const {
connection,
lastDisconnect
}=update;



console.log(
"SUBBOT:",
connection
);



if(connection==="open"){

opened=true;


db.subBots[phone]={
owner:jid,
folder,
created:Date.now()
};

saveDB();



const ownerJid = db.subBots[phone]?.ownerUser || jid;

await sock.sendMessage(
jid,
{
text:
`✓ @${ownerJid.split("@")[0]} ha registrado un nuevo sub bot.
> Usa botinfo para ver tu bot.`
},
{
quoted:null,
mentions:[ownerJid]
}
);


}



if(connection==="close"){


const status=
lastDisconnect
?.error
?.output
?.statusCode;



console.log(
"SUBBOT CLOSE:",
status
);



if(status===401){


console.log(
" Sesiï¿½n inválida, eliminando..."
);


if(fs.existsSync(folder)){
fs.rmSync(
folder,
{
recursive:true,
force:true
}
);
}


delete db.subBots[phone];

saveDB();


}



}


}

);



if(!state.creds.registered){


await new Promise(
r=>setTimeout(r,3000)
);


const pair =
await subSock.requestPairingCode(phone);



await sock.sendMessage(
jid,
{
text:
"🔐 C¿digo de vinculaci¿n:\n\n"+pair+
"\n\nIntroduce este código en WhatsApp."
},
{
quoted:null
}
);


}



return subSock;

}



async function loadSubBots_OLD(){

  if (
    !fs.existsSync(SUBBOTS_DIR)
  ) return;


  for (
    const dir of fs.readdirSync(
      SUBBOTS_DIR
    )
  ){

    const full =
      path.join(
        SUBBOTS_DIR,
        dir
      );


    if (
      fs.statSync(full).isDirectory()
    ){

      try {

        
console.log("DEBUG STARTSUBBOT:", typeof startSubBot, full);

if (typeof startSubBot !== "function") {
  console.log("❌ startSubBot NO EXISTE");
  return;
}


try {
  if (typeof startSubBot !== "function") {
    throw new Error("startSubBot is not defined");
  }

  await startSubBot(full);

} catch (e) {
  console.log("❌ ERROR STARTSUBBOT:", e);

  try {
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`❌ Error iniciando ADDP

Subbot:
${full?.name || "desconocido"}

Error:
${e.message}

Revisa la consola del bot.`
      }
    );
  } catch (sendErr) {
    console.log("❌ No se pudo enviar error ADDP:", sendErr);
  }
}



      } catch(e){

        console.log(
          'Error cargando subbot',
          dir
        );

      }

    }

  }

}

// ━━━━━━━ INICIO DEL BOT CORREGIDO ━━━━━━━
global.startupTime = Date.now();
let restarting = false;
let pairingRequested = false;
let waitingForPairing = false;
let selectedLinkingMethod = '';
let selectedPairingNumber = '';
let sock;
let isStarting = false;
async function start() {

if (isStarting) {
    console.log(' Start ya está ejecutándose.');
    return;
}

isStarting = true;

  //  AÑADE ESTO: Crear la carpeta si no existe
  if (!fs.existsSync(SESSION_PATH)) {
    fs.mkdirSync(SESSION_PATH, { recursive: true });
  }

  const { state, saveCreds } = await useMultiFileAuthState(SESSION_PATH);
  const hasSavedAccount = Boolean(state.creds.me?.id);

  if (!hasSavedAccount && !state.creds.registered && !selectedLinkingMethod) {
    selectedLinkingMethod = await askLinkingMethod();
    if (selectedLinkingMethod === '1') {
      selectedPairingNumber = await askNumber();
      if (!selectedPairingNumber) {
        throw new Error('Debes ingresar un número de teléfono válido para solicitar el código.');
      }
    }
  }

  // Cache externa para controlar reintentos de descifrado de mensajes.
  // Debe sobrevivir a recreaciones del socket.
  const msgRetryCounterCache = new NodeCache({
    stdTTL: 60 * 60,
    useClones: false
  });

  const { version } = await fetchLatestBaileysVersion();
  sock = makeWASocket({
    version,
    logger: P({ level: 'silent' }),
    auth: {
      creds: state.creds,
      keys: makeCacheableSignalKeyStore(state.keys, P({ level: 'silent' }))
    },
    msgRetryCounterCache,
    maxMsgRetryCount: 5,
    printQRInTerminal: false,
    browser: Browsers.macOS('Safari'),
    shouldIgnoreJid: jid => jid?.endsWith('@broadcast'),
    markOnlineOnConnect: false,
    syncFullHistory: false,
    retryRequestDelayMs: 300,
    maxMsgsInMemory: 100
  });

  /*
   * Marca temporal de inicio de esta sesión.
   * WhatsApp puede entregar mensajes antiguos durante la sincronización
   * inicial aunque syncFullHistory esté desactivado.
   */
  sock.__messageCutoff = Math.floor(Date.now() / 1000);

  // ━━━━━━━ FIX SIGNAL: sender-key-memory para grupos ━━━━━━━
  // Baileys puede conservar sender-key-memory obsoleto para un grupo,
  // provocando que otros participantes vean "Esperando este mensaje".
  // Se limpia únicamente antes de enviar a un grupo.
  const originalSendMessage = sock.sendMessage.bind(sock);

  sock.sendMessage = async (jid, content, options) => {
    if (jid?.endsWith('@g.us')) {
      try {
        await state.keys.set({
          'sender-key-memory': {
            [jid]: null
          }
        });

        console.log('[SIGNAL] sender-key-memory reiniciado para:', jid);
      } catch (e) {
        console.log(
          '[SIGNAL] No se pudo reiniciar sender-key-memory:',
          e?.message || e
        );
      }
    }

    return originalSendMessage(jid, content, options);
  };
  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  /*
   * ============================================================
   * ADDP WATCHDOG
   * ============================================================
   *
   * Inicia el vigilante después de crear el sock.
   *
   * Su función es recuperar una cola ADDP que haya quedado:
   *
   * esperando = false
   *
   * mientras todavía tenga un personaje pendiente.
   */

  iniciarWatchdogAddP(sock);

let BOT_ID = '';

sock.ev.on('creds.update', saveCreds);
sock.ev.on('chats.phoneNumberShare', ({ lid, jid }) => {
  if (lid && jid) {
    missionLidToJid.set(lid, jid);
    db.missionLidToJid[lid] = jid;
    saveDB();
  }
});

sock.ev.on('connection.update', async ({ connection, lastDisconnect, qr }) => {
    console.log('📡 Estado de conexi¿n:', connection);

    if (selectedLinkingMethod === '2' && qr) {
      console.log('\nEscanea este código QR desde WhatsApp → Dispositivos vinculados:\n');
      qrcode.generate(qr, { small: true });
    }
    
    
if (connection === 'open') {

    // RESTAURACIÓN AUTOMÁTICA DESACTIVADA
    // characters.json se mantiene intacto al iniciar.
    // La restauraciï¿½n se ejecutará ï¿½nicamente de forma manual.
    console.log(
      " Restauraciï¿½n automï¿½tica desactivada."
    );

    iniciarBackupAutomatico(sock, db, OWNER_NUMBER);


pairingRequested = false;
waitingForPairing = false;
selectedLinkingMethod = '';
selectedPairingNumber = '';

    if (!sock.user?.id) {
    console.log(" sock.user todavï¿½a no está disponible, esperando...");
    await new Promise(r => setTimeout(r, 3000));
}

if (sock.user?.id) {
    BOT_ID = sock.user.id.split(':')[0] + '@s.whatsapp.net';
    console.log("✓ BOT_ID:", BOT_ID);
} else {
    console.log("❌ No se pudo obtener BOT_ID");
}

    console.log('◆ BOT ID:', BOT_ID);

    if (BOT_ID) {
    
    // ==================================================
    // REFERENCIA GLOBAL DEL BOT PRINCIPAL
    // ==================================================
    // El socket de index.js es la sesión principal.
    // Los subbots NO modifican esta referencia.
    // ==================================================

    globalThis.MAIN_BOT_SOCK = sock;

    console.log(
      '⭐ BOT PRINCIPAL REGISTRADO GLOBALMENTE:',
      sock?.user?.id || 'sin identidad todavía'
    );

activeBots.set(BOT_ID, sock);
}

    console.log(`📡 Bots activos: ${activeBots.size}`);

    console.log(
      `✓ Bot conectado exitosamente como: ${BOT_ID.split('@')[0]}`
    );

    await loadSubBots({
      sock,
      db,
      saveDB
    });
}
    
    if (connection === 'close') {

    isStarting = false;
    pairingRequested = false;

    const statusCode =
        lastDisconnect?.error?.output?.statusCode;

    console.log("❌ Conexión cerrada. Código:", statusCode);

    if (BOT_ID) {
        activeBots.delete(BOT_ID);
    }

    if (statusCode === 440) {
        console.log("⚠️ Sesi¿n reemplazada. No reiniciar autom¿ticamente.");
        return;
    }

    const shouldReconnect =
        statusCode !== 401 &&
        statusCode !== DisconnectReason.loggedOut;

    if (shouldReconnect && !restarting) {

        restarting = true;

        console.log("🔄 Reiniciando en 5 segundos...");

        await new Promise(r =>
            setTimeout(r, 5000)
        );

        restarting = false;

        start();
    }
}

if (connection === 'open') {
    isStarting = false;
}

if (connection === 'connecting') {
        console.log('🔄 Conectando a WhatsApp...');
    }
});

  if (!hasSavedAccount && !state.creds.registered) {

    if (selectedLinkingMethod === '2') {
      console.log('📱 Esperando que escanees el código QR para vincular el bot...');
    } else {
      if (pairingRequested) {
          console.log('⚠️ C¿digo de vinculaci¿n ya solicitado.');
          return;
      }

      pairingRequested = true;
      const num = selectedPairingNumber;
      console.log('🔐 Solicitando c¿digo para:', num);
      
      try {
        await new Promise(resolve => setTimeout(resolve, 5000));
        
        if (!sock.ws || !sock.ws.isOpen) {
          throw new Error('Socket no está listo para solicitar código');
        }
        
        const code = await sock.requestPairingCode(num);

console.log(`📱 C¿digo de vinculaci¿n: ${code}`);
console.log('⏳ Esperando que WhatsApp complete la vinculación...');
      waitingForPairing = true;
      
      // Esperar máximo 5 minutos para que se complete la vinculaciï¿½n
      await new Promise(resolve => setTimeout(resolve, 300000));
      waitingForPairing = false;
      
      console.log('\n========================================');
      console.log('🔐 INSTRUCCIONES DE VINCULACI¿N:');
      console.log('========================================');
      console.log(`1. Abre WhatsApp en el número: ${num}`);
      console.log(`2. Ve a Ajustes → Dispositivos vinculados`);
      console.log(`3. Toca "Vincular un dispositivo"`);
      console.log(`4. Ingresa el código: ${code}`);
      console.log('5. Espera a que se complete la vinculación');
      console.log('========================================\n');
      
      console.log(' Esperando vinculaciï¿½n... El bot se mantendrï¿½ conectado.');
      
    } catch (err) {
      pairingRequested = false;
      console.error('❌ Error solicitando código:', err.message);
      console.log('🔄 Reintentando en 5 segundos...');
      setTimeout(() => start(), 5000);
      }
    }
  } else {
    console.log('✓ Sesión existente encontrada, conectando...');
}


  sock.ev.on('messages.upsert', async ({ messages, type }) => {
  try {

    const messageCutoff =
      Number(sock.__messageCutoff || 0);

    const freshMessages =
      (Array.isArray(messages) ? messages : []).filter(message => {

        const messageTimestamp =
          Number(message?.messageTimestamp || 0);

        if (
          messageCutoff &&
          messageTimestamp &&
          messageTimestamp < messageCutoff
        ) {
          return false;
        }

        return true;
      });

    if (!freshMessages.length) {
      return;
    }

    messages = freshMessages;

if (type !== 'notify') {

  if (

    type === 'append' &&

    Array.isArray(messages)

  ) {

    appendPendingAlbumImages(
      pendingAlbums,
      messages,
      {
        isImage: message => Boolean(unwrapImageMessage(message)),
        isBanned: imageSender => Boolean(db.bannedUsers?.[imageSender])
      }
    );

    for (const imageMsg of messages) {

      if (

        !imageMsg?.message?.imageMessage ||

        imageMsg.key?.fromMe

      ) {

        continue;

      }


      try {

        const imageJid =

          imageMsg.key?.remoteJid;


        const imageSender =

          imageMsg.key?.participant ||

          imageMsg.participant ||

          "";


        if (

          imageJid?.endsWith("@g.us") &&

          imageSender

        ) {

          await captureManualTagImage(

            imageMsg,

            imageJid,

            imageSender,

            downloadMediaMessage

          );

        }

      } catch (error) {

        console.log(

          "[MANUAL-TAGS] Error capturando imagen append:",

          error?.message || error

        );

      }

    }

  }


  return;

}

for (const observedMsg of messages) {
  try {
    await mioObserve(sock, observedMsg);
  } catch (error) {
    console.error('[MIO] error observando respuesta:', error?.message || error);
  }
}

const addedAlbumImages = appendPendingAlbumImages(
  pendingAlbums,
  messages,
  {
    isImage: message => Boolean(unwrapImageMessage(message)),
    isBanned: imageSender => Boolean(db.bannedUsers?.[imageSender])
  }
);

for (const { sender: imageSender, msg: imageMsg } of addedAlbumImages) {
  try {
    const imageJid = imageMsg.key?.remoteJid;
    if (
      imageJid?.endsWith('@g.us') &&
      !imageMsg.key?.fromMe
    ) {
      await captureManualTagImage(
        imageMsg,
        imageJid,
        imageSender,
        downloadMediaMessage
      );
    }
  } catch (error) {
    console.error(
      '[MANUAL-TAGS] Error capturando imagen desde messages.upsert:',
      error?.message || error
    );
  }
}

const msg = messages[0];


if (!msg.message) return;

if(await recibirPersonajeAddP(
 sock,
 msg
)) return;

if(await detectarRespuestaAddP(
 sock,
 msg
)) return;


const body =
    msg.message?.conversation ||

    msg.message?.extendedTextMessage?.text ||
    msg.message?.imageMessage?.caption ||
    msg.message?.videoMessage?.caption ||
    '';

const messageContent =
  msg.message || {};

const quotedInfo =
  messageContent
    ?.extendedTextMessage
    ?.contextInfo ||

  messageContent
    ?.imageMessage
    ?.contextInfo ||

  messageContent
    ?.videoMessage
    ?.contextInfo ||

  messageContent
    ?.documentMessage
    ?.contextInfo ||

  messageContent
    ?.buttonsResponseMessage
    ?.contextInfo ||

  messageContent
    ?.listResponseMessage
    ?.contextInfo ||

  messageContent
    ?.templateButtonReplyMessage
    ?.contextInfo ||

  null;

const quotedId =
  quotedInfo
    ?.stanzaId;

const pendingSeriesEntry =
  quotedId &&
  db.pendingSeriesChecks?.[quotedId]
    ? [quotedId, db.pendingSeriesChecks[quotedId]]
    : null;

if (pendingSeriesEntry) {

  const pendingId = pendingSeriesEntry[0];
  const pending =
    pendingSeriesEntry[1];

  const totalMatch =
    body.match(
      /personajes\s*(?:totales)?\s*[»>:=-]*\s*(?:\*?\`?\*?\s*)?(\d+)/i
    );

  if (
    totalMatch
  ) {

    const total =
      Number(
        totalMatch[1]
      );

    if (
      Number.isInteger(
        total
      ) &&
      total > 0
    ) {

      db.seriesInfoCache[
        pending.seriesKey
      ] = {

        name:
          pending.anime,

        total,

        updatedAt:
          Date.now()

      };

      delete db.pendingSeriesChecks[pendingId];

      saveDB();

      console.log(
  "✓ Total guardado:",
  pending.anime,
  total
);

try {
  await handleSerieC(
    sock,
    {
      ...msg,
      key: {
        ...msg.key,
        remoteJid:
          pending.jid ||
          msg.key.remoteJid
      }
    },
    pending.anime.split(/\s+/),
    pending.sender ||
      msg.key.participant ||
      msg.participant ||
      ""
  );
} catch (error) {
  console.error(
    " Error al completar /seriec automï¿½ticamente:",
    error
  );
}

    }

  }

}

const jid = msg.key.remoteJid;

if (!jid) return;

const isPrivateChat =
  !jid.endsWith('@g.us');

const sender =
  msg.key.participant ||
  msg.participant ||
  jid;

// ============================================================
// ANTI-ISN — FILTRO DE INSULTOS
// ============================================================

if (
  await procesarAntiIsn(
    sock,
    msg,
    jid,
    sender,
    body
  )
) {
  return;
}

const defaultPrefix =
  typeof db.prefix === 'string' && db.prefix.length
    ? db.prefix
    : '/';

const privatePrefix =
  db.staffPrefixes?.[sender];

const usedPrefix =
  privatePrefix &&
  body.startsWith(privatePrefix)
    ? privatePrefix
    : defaultPrefix;

const prefix = usedPrefix;

const isCmd =
  body.startsWith(defaultPrefix) ||
  (
    privatePrefix &&
    body.startsWith(privatePrefix)
  );

const args =
  body.trim().split(/ +/).slice(1);




const command =
  body
    .slice(prefix.length)
    .trim()
    .split(/ +/)
    .shift()
    ?.toLowerCase();
console.log(
  '[CMD-DIAG]',
  'body=', JSON.stringify(body),
  'isCmd=', isCmd,
  'command=', command,
  'sender=', sender
);

const isMainOwner =
  isMainOwnerId(sender);

const isStaffOwner =
  isSecondaryOwnerId(sender);

const isOwner =
  isMainOwner || isStaffOwner;

if (
  db.staffCommands?.includes(command) &&
  !isMainOwner &&
  !isStaffOwner
) {
  return;
}

if (
  db.xpBoost.multiplier > 1 &&
  Date.now() >= db.xpBoost.expires
) {

  db.xpBoost.multiplier = 1;
  db.xpBoost.expires = 0;

  saveDB();

  for (const grupo of Object.keys(db.groups)) {
    try {
      await sock.sendMessage(grupo,{
        text:'El evento de XP multiplicada ha finalizado.'
      });
    } catch {}
  }
}

console.log('SENDER:', sender);
console.log('SENDER:', sender);

    const user = initUser(sender, msg.pushName);

    if (!user) {
      console.warn(
        '⏩ MENSAJE SIN USUARIO VÁLIDO:',
        sender,
        '| grupo:',
        jid
      );
      return;
    }

collectPassiveCoins(
  jid,
  sender
);

    user.messages += 1;

user.lastMessageAt = Date.now();

    if (isCmd) {
      const oldLevel = Number(user.level) || 1;
      let xpGain = 70;

      if (Date.now() < db.xpBoost.expires) {
        xpGain *= db.xpBoost.multiplier;
      }
      xpGain = songGame.applyXpMultiplier(user, xpGain);
      const groupEvent = getGroupEvent(jid);
      if (groupEvent) {
        xpGain *= Number(groupEvent.multiplier) || 1;
      }

      user.xp += xpGain;

      let newLevel = 1;

      while (
        user.xp >= xpForLevel(newLevel + 1)
      ) {
        newLevel++;
      }

      user.level = newLevel;

      if (newLevel > oldLevel) {
        try {
          user.gems = (Number(user.gems) || 0) + 5000000;
          saveDB();
          await sock.sendMessage(
            jid,
            {
              text:
                '(˶˃ ᵕ ˂˶) ¡ Sᥙbιstᥱ dᥱ ᥒιvᥱᥣ ' + oldLevel + ' ➣ ' + newLevel + ' tomᥲ ᥙᥒᥲ rᥱᥴomρᥱᥒsᥲ !\n' +
                '5.000.000 Gᥱmᥲs.'
            },
            { quoted: msg }
          );
        } catch (e) {
          console.error('[LEVEL-UP REWARD]', e && e.message ? e.message : e);
        }
      }
    }

    const groupData = initGroup(jid);

    if (groupData.off && !isOwner)
  return;

    if (await songGame.handleGuess(sock, msg, { body, jid, sender, isCmd }))
      return;

    groupData.totalMessages =
      (groupData.totalMessages || 0) + 1;

    if (!groupData.members[sender]) {

      groupData.members[sender] = {
        messages: 0,
        mentions: 0,
        firstMessage: Date.now()
      };

    }

    groupData.members[sender].messages++;

    const mentioned =
      msg.message?.extendedTextMessage?.contextInfo?.mentionedJid || [];

    for (const m of mentioned) {

      if (!groupData.members[m]) {

        groupData.members[m] = {
          messages: 0,
          mentions: 0,
          firstMessage: Date.now()
        };

      }

      groupData.members[m].mentions =
        (groupData.members[m].mentions || 0) + 1;

    }

    if (await checkModeration(sock, msg, groupData, sender))
      return;

    if (await checkTradeAccept(sock, msg, sender))
      return;

    if (await checkLevelTradeAccept(sock,msg,sender))
  return;

if (!body) return;

const ctx = msg.message.extendedTextMessage?.contextInfo;

const quotedJid = ctx?.participant;

try {

  if (
    await handleMergeSerieReply(
      sock,
      msg,
      sender
    )
  ){
    return;
  }

} catch (error) {

  console.error(
    '[ERROR REPLY MERGE]',
    error?.stack || error?.message || error
  );

  try {

    await sock.sendMessage(
      jid,
      {
        text:
          '[Error comando]\n*' +
          String(
            error?.stack ||
            error?.message ||
            error
          )
            .split('\n')
            .map(x => x.trim())
            .filter(Boolean)
            .slice(0, 3)
            .join('\n') +
          '*'
      },
      {
        quoted: msg
      }
    );

  } catch {}

}

try {

  if (
    await handleDeleteSerieReply(
      sock,
      msg,
      sender
    )
  ){
    return;
  }

} catch (error) {

  console.error(
    '[ERROR REPLY DELETE SERIE]',
    error?.stack || error?.message || error
  );

  try {

    await sock.sendMessage(
      jid,
      {
        text:
          '[Error comando]\n*' +
          String(
            error?.stack ||
            error?.message ||
            error
          )
            .split('\n')
            .map(x => x.trim())
            .filter(Boolean)
            .slice(0, 3)
            .join('\n') +
          '*'
      },
      {
        quoted: msg
      }
    );

  } catch {}

}


let primary =
  db.primaryBots?.[jid];

const normalizePrimaryNumber = value =>
  String(value || '')
    .trim()
    .replace(/:.*(?=@)/, '')
    .replace(/@.*$/, '')
    .replace(/\D/g, '');

const primaryNumber =
  normalizePrimaryNumber(primary);

const primarySocketOnline =
  primaryNumber &&
  (
    normalizePrimaryNumber(globalThis.MAIN_BOT_SOCK?.user?.id) === primaryNumber ||
    normalizePrimaryNumber(globalThis.MAIN_BOT_SOCK?.user?.lid) === primaryNumber ||
    [...(globalThis.SUBBOT_SOCKETS?.entries?.() || [])].some(
      ([phone, subSock]) =>
        normalizePrimaryNumber(phone) === primaryNumber &&
        Boolean(subSock?.user)
    )
  );

if (
  primary &&
  !primarySocketOnline
) {
  const activeSubBots = (() => {
    try {
      const activeFile =
        path.join(
          process.cwd(),
          'subbot-system',
          'active.json'
        );

      if (!fs.existsSync(activeFile)) return [];

      return Object.entries(
        JSON.parse(fs.readFileSync(activeFile, 'utf8'))
      );
    } catch (error) {
      console.error(
        'ERROR LEYENDO SUBBOTS PARA FAILOVER:',
        error?.message || error
      );
      return [];
    }
  })();

  const replacementSubBot =
    activeSubBots.find(([phone, data]) =>
      data?.online &&
      Array.isArray(data.groups) &&
      data.groups.includes(jid) &&
      globalThis.SUBBOT_SOCKETS?.get(String(phone))?.user
    );

  const mainBotJid =
    globalThis.MAIN_BOT_SOCK?.user?.id ||
    globalThis.MAIN_BOT_SOCK?.user?.lid;

  const replacement =
    replacementSubBot?.[1]?.jid ||
    replacementSubBot?.[0] && `${replacementSubBot[0]}@s.whatsapp.net` ||
    mainBotJid;

  if (replacement) {
    db.primaryBots[jid] =
      String(replacement)
        .trim()
        .replace(/:.*(?=@)/, '')
        .replace(/@c\.us$/i, '@s.whatsapp.net');
    primary = db.primaryBots[jid];

    saveDB();

    console.log(
      '🔁 FAILOVER PRIMARY:',
      jid,
      '→',
      db.primaryBots[jid]
    );
  }
}

/*
 * Si todavía no hay un primary configurado para el grupo, el bot
 * principal conserva el comportamiento anterior y puede responder.
 * Los subbots siguen bloqueados hasta que se elija uno con /setprimary.
 */
if (
  !primary &&
  command !== 'setprimary' &&
  sock.__subBotPhone
) {
  return;
}

if (primary) {
  const normalizePrimaryJid = (value) => {
    if (!value) return '';

    return String(value)
      .trim()
      .replace(/:.*(?=@)/, '')
      .replace(/@c\.us$/i, '@s.whatsapp.net');
  };

  const currentBot =
    normalizePrimaryJid(sock.user?.id);

  const primaryBot =
    normalizePrimaryJid(primary);

  const getBotNumber = value =>
    value.replace(/@.*$/, '').replace(/\D/g, '');
  const currentIdentities = [
    currentBot,
    normalizePrimaryJid(sock.user?.lid),
    sock.__subBotPhone
      ? normalizePrimaryJid(`${sock.__subBotPhone}@s.whatsapp.net`)
      : '',
    sock === globalThis.MAIN_BOT_SOCK
      ? normalizePrimaryJid(globalThis.MAIN_BOT_SOCK?.user?.id)
      : ''
  ].filter(Boolean);
  const sameBot =
    currentIdentities.includes(primaryBot) ||
    currentIdentities.some(identity =>
      getBotNumber(identity) &&
      getBotNumber(identity) === getBotNumber(primaryBot)
    );

  if (!sameBot) return;
}


if (!isCmd) return;

if (
  isPrivateChat &&
  ![
    'status',
    'setbanner',
    'logout',
    'botinfo',
    'menu'
  ].includes(command)
) {
  return;
}

if (db.bannedUsers?.[sender]) {
  return;
}

if (
  db.botOff &&
  !isMainOwnerId(sender) &&
  !isSecondaryOwnerId(sender) &&
  !(Array.isArray(db.staff) && db.staff.includes(sender))
) return;

user.totalCommands =
  (user.totalCommands || 0) + 1;

user.lastCommandAt = Date.now();

if (!user.favCommands)
  user.favCommands = {};

user.favCommands[command] =
  (user.favCommands[command] || 0) + 1;

db.stats.totalCommands =
  (db.stats.totalCommands || 0) + 1;

const target =
  msg.message?.extendedTextMessage?.contextInfo?.participant ||
  mentioned?.[0];


// ━━━━━━━ COMANDOS EN MANTENIMIENTO ━━━━━━━

if (
  command !== 'mc' &&
  db.maintenanceCommands?.[command]
) {

  return sock.sendMessage(
    jid,
    {
      text:
`El comando */${command}* esta en mantenimiento.
> regresa despues para verificar.`
    },
    {
      quoted: msg
    }
  );

}





async function handleMenuCategoria(sock, msg, args) {

const jid = msg.key.remoteJid;

const botName =
  sock.user?.name ||
  "Bot";

const categoria =
  (args[0] || "").toLowerCase();


let texto = "";


if(!categoria){

texto =
"(ᯫ᳐˶ꔷ֊ꔷᯫ᳐) ¡Hola! Soy " + botName + " ♡\n\n" +

"     ㅤ ♛ 𝙱𝚢: 𝙼𝚊𝚟𝚒𝚜\n" +

"•­────── ୨୧ ──────•®\n" +
"┋ ☆ ¡Bienvenido a mi men¿!\n" +
"┋ ♧ Usa /menu categoria\n" +
"•°───────────────•¯\n\n" +

"¡Aqu¿ tienes mis secciones disponibles!\n\n" +

"♡ /menu gacha\n" +
"> Personajes, waifus y colecciones.\n\n" +

"♡ /menu coins\n" +
"> Economía y monedas.\n\n" +

"♡ /menu profile\n" +
"> Perfil y personalización.\n\n" +

"♡ /menu descargas\n" +
"> Videos, audios e imágenes.\n\n" +

"♡ /menu reacciones\n" +
"> Acciones y reacciones.\n\n" +

"♡ /menu admin\n" +
"> Herramientas administrativas.\n\n" +

"♡ /menu bot\n" +
"> Configuración del bot.";

}

else if(categoria === "gacha"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝙼𝙴𝙽𝚄 𝙶𝙰𝙲𝙷𝙰

☆ /rw
☆ /rwp
☆ /w
☆ /winfo
☆ /harem
☆ /sell
☆ /trade
☆ /ginfo
☆ /slist`;

}


else if(categoria === "coins"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝙼𝙴𝙽𝚄 𝙲𝙾𝙸𝙽𝚂

☆ /baltop
☆ /baltopgp
☆ /daily
☆ /deposit
☆ /withdraw
☆ /luck
☆ /luckshop`;

}


else if(categoria === "profile"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝙼𝙴𝙽𝚄 𝙿𝚁𝙾𝙵𝙸𝙻𝙴

☆ /marry
☆ /divorce
☆ /setbirth
☆ /delbirth
☆ /lvl`;

}


else if(categoria === "descargas"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝙼𝙴𝙽𝚄 𝙳𝙴𝚂𝙲𝙰𝚁𝙶𝙰𝚂

☆ /mp4
☆ /tomp3
☆ /tt
☆ /ttsearch
☆ /ytaudio`;

}


else if(categoria === "reacciones"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝚁𝙴𝙰𝙲𝙲𝙸𝙾𝙽𝙴𝚂

☆ /bite
☆ /cry
☆ /hug
☆ /kiss
☆ /pat
☆ /poke
☆ /slap`;

}


else if(categoria === "admin"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝙼𝙴𝙽𝚄 𝙰𝙳𝙼𝙸𝙽

☆ /del (responde al mensaje)

> Para borrar mensajes de otros usuarios, el bot debe ser administrador.`;

}


else if(categoria === "bot"){

texto =
`ദ്ദി˶˒ ᵕ ˂ )✧ 𝙼𝙴𝙽𝚄 𝙱𝙾𝚃

☆ /setname
☆ /setbanner`;

}


else{

texto =
`♧ Categor¿a no encontrada.

Usa:
☆ /menu`;

}



const botKey = String(
  sock.__subBotPhone ||
  sock.user?.id ||
  ""
)
  .split(":")[0]
  .split("@")[0]
  .replace(/\D/g, "");

const banner =
  db.banners?.[botKey];

if (
  banner &&
  fs.existsSync(banner)
) {

  let buffer = imageCache.get(banner);

  if (!buffer) {
    buffer = fs.readFileSync(banner);
    imageCache.set(banner, buffer);
  }

  await sock.sendMessage(
    jid,
    {
      image: buffer,
      caption: texto
    },
    {
      quoted: msg
    }
  );

} else {

  await sock.sendMessage(
    jid,
    {
      text:texto
    },
    {
      quoted:msg
    }
  );

}


}






/*
 * ============================================================
 * GIVEALLHAREM_AUTO_CONFIRM
 * ============================================================
 */

if (
  String(body || "")
    .trim()
    .toLowerCase() === "aceptar"
) {

  const confirmado =
    await processGiveAllHaremConfirmation(
      sock,
      msg,
      jid,
      sender,
      body
    );

  if (confirmado) {
    return;
  }
}




/*
============================================================
/GIVEALLHAREM
============================================================

Transfiere TODO el harem del usuario al usuario mencionado.

La solicitud queda vinculada al sender que ejecutó
/giveallharem.

Solo ese sender puede aceptar.

Tiempo de aceptación: 30 segundos.
*/

global.giveAllHaremPending ??= new Map();



/*
============================================================
CONFIRMAR GIVEALLHAREM
============================================================
*/








/*
============================================================
/GIVEALLHAREM
============================================================
*/

global.giveAllHaremPending ??= new Map();






/* ============================================================
 * CONFIRMACIÓN GIVEALLHAREM
 * ============================================================ */

if (
  typeof body === "string" &&
  body.trim().toLowerCase() === "aceptar"
) {
  
/*
============================================================
CONFIRMACIÓN GIVEALLHAREM
============================================================
*/

if (
  String(body ?? "")
    .trim()
    .toLowerCase() === "aceptar"
) {

  const handled =
    await handleGiveAllHaremConfirm(
      sock,
      msg,
      jid,
      sender,
      body
    );

  if (handled) {
    return;
  }
}

}



// === LOGROS / ACHIEVEMENTS ===


/* COMMAND_PROTECTION_V7 */

  try {

    await handleCommand({
        sock,
        msg,
        jid,
        sender,
        args,
        command,
        prefix,
        mentioned,
        quotedJid,
        target,
        db,
        saveDB,
        isOwner,
        isMainOwner,
        isStaffOwner,
        body
      });

  } catch (error) {

    console.error(
      '❌ ERROR PROCESANDO COMANDO:',
      error?.stack || error?.message || error
    );

    try {

      const errorText =
        String(
          error?.stack ||
          error?.message ||
          error
        )
          .split('\n')
          .map(x => x.trim())
          .filter(Boolean)
          .slice(0, 3)
          .join('\n');

      await sock.sendMessage(
        jid,
        {
          text:
            '[Error comando]\\n*' +
            errorText +
            '*'
        },
        {
          quoted: msg
        }
      );

    } catch (sendError) {

      console.error(
        '❌ ERROR ENVIANDO REPORTE:',
        sendError?.message || sendError
      );

    }

  }


  return;














   
  
  } catch (__errGlobalUpsert) {
    console.error('❌ ERROR NO CAPTURADO EN messages.upsert:', __errGlobalUpsert?.stack || __errGlobalUpsert);
  }
});
}

start();
/* ==== Handlers de apagado reubicados por repair-index.mjs (antes muertos dentro de messages.upsert) ==== */
let shuttingDown = false;

async function apagadoSeguro(signal) {
  if (shuttingDown) {
    console.log('[SAFE SHUTDOWN] Apagado ya en proceso.');
    return;
  }

  shuttingDown = true;

  console.log('');
  console.log('========================================');
  console.log('[SAFE SHUTDOWN] Iniciando apagado seguro...');
  console.log('========================================');

  try {
    // 1. Limpiar usuarios inválidos y baneados.
    if (typeof limpiarUsuariosInvalidos === 'function') {
      limpiarUsuariosInvalidos();
    }

    // 2. Crear la copia protegida de usuarios.
    //    Esta funciï¿½n usa escritura sï¿½ncrona,
    //    por lo que termina completamente antes de continuar.
    if (typeof guardarUsuariosProtegidos === 'function') {
      guardarUsuariosProtegidos();
      console.log('[SAFE SHUTDOWN] users-protected.json terminado.');
    }

    // 3. Solicitar guardado de database.json.
    saveDB();

    // 4. Esperar TODA la cola de escrituras de saveDB.
    await saveDBQueue;

    console.log('[SAFE SHUTDOWN] database.json terminado.');
    console.log('[SAFE SHUTDOWN] Todas las escrituras finalizaron.');

  } catch (error) {
    console.error('[SAFE SHUTDOWN ERROR]', error);
  } finally {
    console.log('[SAFE SHUTDOWN] Cerrando Node...');
    console.log('========================================');

    process.exit(0);
  }
}

process.on('SIGINT', () => {
  apagadoSeguro('SIGINT');
});

process.on('SIGTERM', () => {
  apagadoSeguro('SIGTERM');
});

process.on('uncaughtException', err => {
  console.error(err);
  saveDB();
});

process.on('unhandledRejection', err => {
  console.error(err);
  saveDB();
});

//startSecondary();

/* ============================================================
 * WEB AVATAR SERVER
 * Mini servidor para que la web obtenga fotos de perfil
 * ============================================================ */
const AVATAR_PORT = 3001;

http.createServer(async (req, res) => {
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Content-Type', 'application/json');

  try {
    const url = new URL(req.url, 'http://localhost:' + AVATAR_PORT);

   // Ruta para enviar codigo por WhatsApp
if (url.pathname === '/send-wa-code') {
  const number = (url.searchParams.get('number') || '').replace(/\D/g, '');
  const code = url.searchParams.get('code') || '';

  if (!number || !code) {
    res.statusCode = 400;
    return res.end(JSON.stringify({ error: 'Falta number o code' }));
  }

  const botSock = globalThis.MAIN_BOT_SOCK;
  if (!botSock) {
    res.statusCode = 503;
    return res.end(JSON.stringify({ error: 'Bot no conectado' }));
  }

  const jid = number + '@s.whatsapp.net';

  try {
    await botSock.sendMessage(jid, {
      text:
        '🔐 *Tu codigo de acceso es:*\n\n' +
        '*' + code + '*\n\n' +
        '⏱️ Valido por 60 segundos.\n\n' +
        '> Si no solicitaste este codigo, ignora este mensaje.'
    });
    console.log('[WA-CODE] Codigo enviado a', number);
    return res.end(JSON.stringify({ ok: true }));
  } catch (e) {
    console.error('[WA-CODE] Error:', e.message);
    res.statusCode = 500;
    return res.end(JSON.stringify({ error: e.message }));
  }
}

      // Resolver numero telefonico a LID/JID usando WhatsApp
      if (url.pathname === '/resolve-number') {
        const phone = (url.searchParams.get('phone') || '').replace(/\D/g, '');

        if (!phone || phone.length < 7 || phone.length > 15) {
          res.statusCode = 400;
          return res.end(JSON.stringify({ error: 'Numero invalido' }));
        }

        const botSock = globalThis.MAIN_BOT_SOCK;
        if (!botSock) {
          res.statusCode = 503;
          return res.end(JSON.stringify({ error: 'Bot no conectado' }));
        }

        try {
          const result = (await botSock.onWhatsApp(phone + '@s.whatsapp.net'))?.find(item => item?.exists);

          if (!result) {
            return res.end(JSON.stringify({ ok: false, error: 'Numero no existe en WhatsApp' }));
          }

          // Guardar el mapeo igual que /lid
          try {
            if (typeof db !== 'undefined' && db && result.lid) {
              db.missionLidToJid ??= {};
              db.missionLidToJid[result.lid] = result.jid || (phone + '@s.whatsapp.net');
              if (typeof missionLidToJid !== 'undefined' && missionLidToJid) {
                missionLidToJid.set(result.lid, db.missionLidToJid[result.lid]);
              }
              if (typeof saveDB === 'function') saveDB();
            }
          } catch (e) {
            console.log('[RESOLVE-NUMBER] Error guardando LID:', e.message);
          }

          console.log('[RESOLVE-NUMBER]', phone, '-> LID:', result.lid, '| JID:', result.jid);

          return res.end(JSON.stringify({
            ok: true,
            phone,
            jid: result.jid || (phone + '@s.whatsapp.net'),
            lid: result.lid || null
          }));

        } catch (e) {
          console.error('[RESOLVE-NUMBER] Error:', e.message);
          res.statusCode = 500;
          return res.end(JSON.stringify({ error: e.message }));
        }
      }


// Ruta existente: avatar

      // ============================================================

      // ============================================================
      // RACE CARS - Devolver autos con imagenes para la web
      // ============================================================
      if (url.pathname === '/race/cars') {
        try {
          if (typeof loadCars === 'function') loadCars();
        } catch (e) {}

        const lista = [];
        try {
          for (const c of carsCache) {
            if (!Array.isArray(c.images) || !c.images.length) continue;

            const imagenes = c.images
              .filter(p => typeof p === 'string' && fs.existsSync(p))
              .map(p => {
                try {
                  const rel = path.relative(CAR_IMAGES, p).replace(/\\/g, '/');
                  return '/cars/' + rel;
                } catch (e) { return null; }
              })
              .filter(Boolean);

            if (!imagenes.length) continue;

            lista.push({
              id: c.id,
              nombre: c.carName || 'Auto sin nombre',
              personaje: c.personaje || '',
              key: c.key || '',
              rareza: c.rarity || 'Comun',
              velocidad: Number(c.speed) || 150,
              aceleracion: Number(c.acceleration) || 8,
              imagen: imagenes[0],
              imagenes
            });
          }
        } catch (e) {
          console.error('[RACE] Error:', e.message);
        }

        return res.end(JSON.stringify({ ok: true, total: lista.length, cars: lista }));
      }

      // GROUP-PREVIEW: obtiene info de un grupo desde su link de invitacion
      // ============================================================
      
      // ============================================================
      // STAFF ENDPOINTS
      // ============================================================

      // Verificar si un usuario es staff
      if (url.pathname === '/staff/check') {
        const phone = (url.searchParams.get('phone') || '').replace(/\D/g, '');
        const lid = url.searchParams.get('lid') || '';

        let isPrincipal = false;
        let isSecondary = false;

        // Principal
        if (phone && phone === '56956461451') isPrincipal = true;

        const primaryLid = (typeof db !== 'undefined' && db.primaryOwner) || null;
        if (primaryLid && lid && lid === primaryLid) isPrincipal = true;

        if (phone && !isPrincipal && typeof db !== 'undefined' && db.missionLidToJid && primaryLid) {
          const jidP = db.missionLidToJid[primaryLid];
          if (jidP) {
            const pPhone = jidP.split('@')[0].replace(/\D/g, '');
            if (pPhone === phone) isPrincipal = true;
          }
        }

        // Secundarios
        const SEC = (typeof SECONDARY_OWNERS !== 'undefined' && Array.isArray(SECONDARY_OWNERS)) ? SECONDARY_OWNERS : [];
        const dbSec = (typeof db !== 'undefined' && Array.isArray(db.secondaryOwners)) ? db.secondaryOwners : [];
        const allSec = [...SEC, ...dbSec];

        for (const sLid of allSec) {
          if (!sLid) continue;
          if (lid && sLid === lid) { isSecondary = true; break; }
          if (phone && typeof db !== 'undefined' && db.missionLidToJid) {
            const sJid = db.missionLidToJid[sLid];
            if (sJid) {
              const sPhone = sJid.split('@')[0].replace(/\D/g, '');
              if (sPhone === phone) { isSecondary = true; break; }
            }
          }
        }

        return res.end(JSON.stringify({
          isStaff: isPrincipal || isSecondary,
          role: isPrincipal ? 'principal' : (isSecondary ? 'secundario' : null)
        }));
      }

      // Buscar personajes
      if (url.pathname === '/staff/search') {
        const q = (url.searchParams.get('q') || '').trim();
        if (!q) return res.end(JSON.stringify({ ok: true, results: [] }));

        // Detectar si es un ID numerico
        const esId = /^\d+$/.test(q);

        if (esId) {
          // Buscar por ID
          const idNum = Number(q);
          const c = charactersCache.find(ch => Number(ch.id) === idNum);

          if (!c) return res.end(JSON.stringify({ ok: true, results: [] }));

          let imageCount = 0;
          try {
            if (fs.existsSync(GACHA_IMAGES)) {
              imageCount = fs.readdirSync(GACHA_IMAGES).filter(f => f.startsWith(c.key + '_')).length;
            }
          } catch {}

          return res.end(JSON.stringify({
            ok: true,
            results: [{
              id: c.id,
              name: c.name,
              key: c.key,
              anime: c.anime || 'Desconocido',
              tag: c.tag || '',
              rarity: c.rarity || 'Comun',
              value: c.value || 0,
              chance: c.chance || '100%',
              gender: c.gender || 'Desconocido',
              creator: c.creator || '',
              imageCount
            }]
          }));
        }

        // Busqueda por nombre (normal)
        const ql = q.toLowerCase();
        const found = [];

        for (const c of charactersCache) {
          const name = String(c.name || '').toLowerCase();
          const key = String(c.key || '').toLowerCase();
          const anime = String(c.anime || '').toLowerCase();

          let score = 0;
          if (name === ql || key === ql) score = 1000;
          else if (name.startsWith(ql + ' ')) score = 900;
          else if (name.startsWith(ql)) score = 800;
          else if (name.includes(' ' + ql + ' ')) score = 700;
          else if (name.includes(ql)) score = 600;
          else if (key.includes(ql)) score = 500;
          else if (anime.includes(ql)) score = 300;

          if (score > 0) found.push({ c, score });
        }

        found.sort((a, b) => b.score - a.score);

        const out = found.slice(0, 30).map(r => {
          const c = r.c;
          let imageCount = 0;
          try {
            if (fs.existsSync(GACHA_IMAGES)) {
              imageCount = fs.readdirSync(GACHA_IMAGES).filter(f => f.startsWith(c.key + '_')).length;
            }
          } catch {}
          return {
            id: c.id,
            name: c.name,
            key: c.key,
            anime: c.anime || 'Desconocido',
            tag: c.tag || '',
            rarity: c.rarity || 'Comun',
            value: c.value || 0,
            chance: c.chance || '100%',
            gender: c.gender || 'Desconocido',
            creator: c.creator || '',
            imageCount
          };
        });

        return res.end(JSON.stringify({ ok: true, results: out }));
      }

      // Info del personaje + imagenes
      if (url.pathname === '/staff/character') {
        const key = (url.searchParams.get('key') || '').trim();
        if (!key) { res.statusCode = 400; return res.end(JSON.stringify({ ok: false, error: 'Falta key' })); }

        const char = charactersCache.find(c => c.key === key);
        if (!char) { res.statusCode = 404; return res.end(JSON.stringify({ ok: false, error: 'Personaje no encontrado' })); }

        let imagenes = [];
        try {
          if (fs.existsSync(GACHA_IMAGES)) {
            imagenes = fs.readdirSync(GACHA_IMAGES).filter(f => f.startsWith(key + '_')).sort();
          }
        } catch {}

        // ============================================================
        // BUSCAR IMAGEN ONLINE (Gelbooru primero, Danbooru despues)
        // Se descarga en el SERVIDOR para evitar hotlink protection
        // ============================================================
        let imagenOnline = null;

        if (char.tag && String(char.tag).trim()) {
          const tagLimpio = String(char.tag).trim();
          console.log('[STAFF] Buscando imagen para tag:', tagLimpio);

          // Lista de URLs candidatas para probar
          const urlsParaProbar = [];

          // 1. Gelbooru API (busca candidatos)
          try {
            if (typeof getGelbooruApiImageCandidates === 'function') {
              const candidatos = await getGelbooruApiImageCandidates(tagLimpio);
              if (Array.isArray(candidatos) && candidatos.length) {
                console.log('[STAFF] Gelbooru candidatos:', candidatos.length);
                urlsParaProbar.push(...candidatos.slice(0, 5));
              }
            }
          } catch (e) {
            console.log('[STAFF] Gelbooru candidates error:', e.message);
          }

          // 2. Gelbooru imagen directa
          if (!urlsParaProbar.length) {
            try {
              if (typeof getGelbooruImage === 'function') {
                const gUrl = await getGelbooruImage(tagLimpio);
                if (gUrl) {
                  console.log('[STAFF] Gelbooru URL directa:', gUrl.slice(0, 80));
                  urlsParaProbar.push(gUrl);
                }
              }
            } catch (e) {
              console.log('[STAFF] Gelbooru directo error:', e.message);
            }
          }

          // 3. Gelbooru API alternativo
          if (!urlsParaProbar.length) {
            try {
              if (typeof getGelbooruApiImage === 'function') {
                const gApiUrl = await getGelbooruApiImage(tagLimpio);
                if (gApiUrl) {
                  console.log('[STAFF] Gelbooru API URL:', gApiUrl.slice(0, 80));
                  urlsParaProbar.push(gApiUrl);
                }
              }
            } catch (e) {
              console.log('[STAFF] Gelbooru API error:', e.message);
            }
          }

          // 4. Danbooru
          try {
            if (typeof getDanbooruImage === 'function') {
              const dUrl = await getDanbooruImage(tagLimpio);
              if (dUrl) {
                console.log('[STAFF] Danbooru URL:', dUrl.slice(0, 80));
                urlsParaProbar.push(dUrl);
              }
            }
          } catch (e) {
            console.log('[STAFF] Danbooru error:', e.message);
          }

          console.log('[STAFF] Total URLs a probar:', urlsParaProbar.length);

          // ============================================================
          // DESCARGAR la primera URL que funcione
          // ============================================================
          for (const url of urlsParaProbar) {
            try {
              console.log('[STAFF] Descargando:', url.slice(0, 100));

              const res = await fetch(url, {
                headers: {
                  'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/131 Safari/537.36',
                  'Referer': 'https://gelbooru.com/',
                  'Accept': 'image/*,*/*;q=0.8'
                },
                redirect: 'follow'
              });

              if (!res.ok) {
                console.log('[STAFF] HTTP', res.status, 'para', url.slice(0, 60));
                continue;
              }

              const arrayBuf = await res.arrayBuffer();
              const buffer = Buffer.from(arrayBuf);

              if (!buffer.length) {
                console.log('[STAFF] Buffer vacio');
                continue;
              }

              if (buffer.length > 8 * 1024 * 1024) {
                console.log('[STAFF] Imagen muy grande:', buffer.length);
                continue;
              }

              const contentType = res.headers.get('content-type') || 'image/jpeg';

              // Verificar que sea una imagen
              if (!contentType.startsWith('image/')) {
                console.log('[STAFF] No es imagen:', contentType);
                continue;
              }

              imagenOnline = 'data:' + contentType + ';base64,' + buffer.toString('base64');

              console.log('[STAFF] ✓ Imagen descargada:', buffer.length, 'bytes | Tipo:', contentType);
              break;

            } catch (e) {
              console.log('[STAFF] Error descargando:', e.message);
            }
          }

          if (!imagenOnline) {
            console.log('[STAFF] ✗ No se pudo obtener imagen online para:', tagLimpio);
          }
        } else {
          console.log('[STAFF] Personaje sin tag:', char.name);
        }
        return res.end(JSON.stringify({
          ok: true,
          character: {
            id: char.id, name: char.name, key: char.key, anime: char.anime,
            tag: char.tag, rarity: char.rarity, value: char.value,
            chance: char.chance, gender: char.gender, creator: char.creator
          },
          imagenes,
          imagenOnline
        }));
      }

      // Subir imagen
      if (url.pathname === '/staff/upload' && req.method === 'POST') {
        let body = '';
        req.on('data', chunk => { body += chunk; });
        req.on('end', () => {
          try {
            const data = JSON.parse(body);
            const key = String(data.key || '').trim();
            const base64 = data.base64 || '';

            if (!key || !base64) { res.statusCode = 400; return res.end(JSON.stringify({ ok: false, error: 'Faltan datos' })); }

            const char = charactersCache.find(c => c.key === key);
            if (!char) { res.statusCode = 404; return res.end(JSON.stringify({ ok: false, error: 'Personaje no encontrado' })); }

            let existentes = [];
            if (fs.existsSync(GACHA_IMAGES)) {
              existentes = fs.readdirSync(GACHA_IMAGES).filter(f => f.startsWith(key + '_'));
            }

            if (existentes.length >= 30) {
              return res.end(JSON.stringify({ ok: false, error: 'Limite de 30 imagenes alcanzado' }));
            }

            const match = base64.match(/^data:(image\/(?:jpeg|jpg|png|webp|gif));base64,(.+)$/);
            if (!match) return res.end(JSON.stringify({ ok: false, error: 'Formato invalido' }));

            const mime = match[1];
            const buffer = Buffer.from(match[2], 'base64');

            if (buffer.length > 8 * 1024 * 1024) {
              return res.end(JSON.stringify({ ok: false, error: 'Imagen supera 8 MB' }));
            }

            let maxNum = 0;
            for (const f of existentes) {
              const m = f.match(/_(\d+)\./);
              if (m) maxNum = Math.max(maxNum, parseInt(m[1]));
            }
            const nextNum = maxNum + 1;

            const ext = mime.split('/')[1] === 'jpeg' ? 'jpg' : mime.split('/')[1];
            const fileName = key + '_' + nextNum + '.' + ext;
            const filePath = path.join(GACHA_IMAGES, fileName);

            if (!fs.existsSync(GACHA_IMAGES)) fs.mkdirSync(GACHA_IMAGES, { recursive: true });

            fs.writeFileSync(filePath, buffer);
            try { imageCache.set(filePath, buffer); } catch {}

            console.log('[STAFF] Imagen guardada:', fileName, '(' + buffer.length + ' bytes)');

            return res.end(JSON.stringify({ ok: true, fileName, total: existentes.length + 1 }));
          } catch (e) {
            console.error('[STAFF] Error upload:', e.message);
            res.statusCode = 500;
            return res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }

      // Eliminar imagen
      if (url.pathname === '/staff/delete-image' && req.method === 'POST') {
        let body = '';
        req.on('data', chunk => { body += chunk; });
        req.on('end', () => {
          try {
            const data = JSON.parse(body);
            const key = String(data.key || '').trim();
            const file = String(data.file || '').trim();

            if (!key || !file) { res.statusCode = 400; return res.end(JSON.stringify({ ok: false, error: 'Faltan datos' })); }
            if (!file.startsWith(key + '_')) return res.end(JSON.stringify({ ok: false, error: 'Archivo no pertenece al personaje' }));
            if (file.includes('/') || file.includes('\\') || file.includes('..')) return res.end(JSON.stringify({ ok: false, error: 'Nombre invalido' }));

            const filePath = path.join(GACHA_IMAGES, file);
            if (!fs.existsSync(filePath)) return res.end(JSON.stringify({ ok: false, error: 'Archivo no existe' }));

            fs.unlinkSync(filePath);
            try { imageCache.delete(filePath); } catch {}

            console.log('[STAFF] Imagen eliminada:', file);
            return res.end(JSON.stringify({ ok: true }));
          } catch (e) {
            res.statusCode = 500;
            return res.end(JSON.stringify({ ok: false, error: e.message }));
          }
        });
        return;
      }
if (url.pathname === '/group-preview') {
        const link = url.searchParams.get('link') || '';
        const match = link.match(/chat\.whatsapp\.com\/([A-Za-z0-9_-]+)/);

        if (!match) {
          res.statusCode = 400;
          return res.end(JSON.stringify({ ok: false, error: 'Link de invitacion invalido' }));
        }

        const code = match[1];
        const botSock = globalThis.MAIN_BOT_SOCK;

        if (!botSock) {
          res.statusCode = 503;
          return res.end(JSON.stringify({ ok: false, error: 'Bot no conectado' }));
        }

        try {
          const info = await botSock.groupGetInviteInfo(code);

          if (!info || !info.id) {
            res.statusCode = 404;
            return res.end(JSON.stringify({ ok: false, error: 'Grupo no encontrado o link invalido' }));
          }

          let banner = null;
          try {
            const picUrl = await botSock.profilePictureUrl(info.id, 'image');
            if (picUrl) {
              const r = await fetch(picUrl);
              const buf = Buffer.from(await r.arrayBuffer());
              banner = 'data:image/jpeg;base64,' + buf.toString('base64');
            }
          } catch (e) {
            console.log('[GROUP-PREVIEW] Sin banner:', e.message);
          }

          console.log('[GROUP-PREVIEW] OK:', info.subject, '| ID:', info.id);

          return res.end(JSON.stringify({
            ok: true,
            grupoId: info.id,
            nombre: info.subject || 'Sin nombre',
            descripcion: info.desc || '',
            miembros: info.size || 0,
            banner: banner
          }));

        } catch (e) {
          console.error('[GROUP-PREVIEW] Error:', e.message);
          res.statusCode = 500;
          return res.end(JSON.stringify({ ok: false, error: 'No se pudo obtener info del grupo: ' + e.message }));
        }
      }
      // ============================================================
      // /character/image  -  Imagen online para la pagina web
      // ============================================================
      if (url.pathname === '/character/image') {
        const name = (url.searchParams.get('name') || '').trim();
        const tagParam = (url.searchParams.get('tag') || '').trim();
        const keyParam = (url.searchParams.get('key') || '').trim();

        let characterTag = tagParam;
        let characterKey = keyParam;

        if (!characterTag && name && typeof charactersCache !== 'undefined') {
          const char = charactersCache.find(c =>
            String(c.name || '').toLowerCase() === name.toLowerCase()
          );
          if (char) {
            characterTag = char.tag || '';
            characterKey = char.key;
          }
        }

        let imageData = null;
        let source = null;

        // 1) Tag manual (bulguru)
        if (characterTag) {
          try {
            const manualImage = await getManualCharacterImage(characterTag);
            if (manualImage) {
              imageData = manualImage;
              source = 'manual-tag';
            }
          } catch (e) {}
        }

        // 2) Online: Gelbooru primero, Danbooru despues
        if (!imageData && characterTag) {
          try {
            const candidates = await getGelbooruApiImageCandidates(characterTag);
            for (const u of (candidates || []).slice(0, 5)) {
              const img = await downloadGelbooruImage(u);
              if (img && img.buffer && img.buffer.length) {
                imageData = img;
                source = 'gelbooru';
                break;
              }
            }
            if (!imageData) {
              const dUrl = await getDanbooruImage(characterTag);
              if (dUrl) {
                const img = await downloadDanbooruImage(dUrl);
                if (img && img.buffer && img.buffer.length) {
                  imageData = img;
                  source = 'danbooru';
                }
              }
            }
          } catch (e) {
            console.log('[CHAR-IMAGE] Error online:', e.message);
          }
        }

        // 3) Fallback: imagenes locales
        if (!imageData && characterKey) {
          try {
            const locals = getCharacterImages(characterKey);
            if (locals.length) {
              const p = path.join(GACHA_IMAGES, locals[0]);
              const buf = fs.readFileSync(p);
              imageData = { image: buf, mimetype: 'image/jpeg' };
              source = 'local';
            }
          } catch (e) {}
        }

        if (!imageData || !imageData.image) {
          return res.end(JSON.stringify({
            ok: false,
            error: 'Sin imagen disponible',
            tag: characterTag,
            key: characterKey
          }));
        }

        const mime = imageData.mimetype || 'image/jpeg';
        const b64 = 'data:' + mime + ';base64,' + imageData.image.toString('base64');

        return res.end(JSON.stringify({
          ok: true,
          image: b64,
          tag: characterTag,
          key: characterKey,
          source
        }));
      }
if (url.pathname !== '/avatar') {
  res.statusCode = 404;
  return res.end(JSON.stringify({ error: 'Ruta no encontrada' }));
}

    const number = (url.searchParams.get('number') || '').replace(/\D/g, '');
    const key = url.searchParams.get('key') || '';

    if (!number && !key) {
      res.statusCode = 400;
      return res.end(JSON.stringify({ error: 'Falta number o key' }));
    }

    const botSock = globalThis.MAIN_BOT_SOCK;
    if (!botSock) {
      res.statusCode = 503;
      return res.end(JSON.stringify({ error: 'Bot no conectado aún' }));
    }

    const candidatos = [];
    if (key) candidatos.push(key);
    if (number) {
      candidatos.push(number + '@s.whatsapp.net');
      candidatos.push(number + '@lid');

      try {
        if (typeof db !== 'undefined' && db && db.missionLidToJid) {
          for (const [lid, jid] of Object.entries(db.missionLidToJid)) {
            const jidNum = String(jid).split('@')[0].replace(/\D/g, '');
            const lidNum = String(lid).split('@')[0].replace(/\D/g, '');
            if (jidNum === number || lidNum === number) {
              candidatos.push(lid);
              candidatos.push(jid);
            }
          }
        }
      } catch {}
    }

    let picUrl = null;
    for (const c of candidatos) {
      if (!c || !c.includes('@')) continue;
      try {
        const u = await botSock.profilePictureUrl(c, 'image');
        if (u) { picUrl = u; break; }
      } catch {}
    }

    if (!picUrl) {
      return res.end(JSON.stringify({ ok: false, avatar: null }));
    }

    const imgRes = await fetch(picUrl);
    const buffer = Buffer.from(await imgRes.arrayBuffer());
    const base64 = buffer.toString('base64');
    const contentType = imgRes.headers.get('content-type') || 'image/jpeg';

    res.end(JSON.stringify({
      ok: true,
      avatar: 'data:' + contentType + ';base64,' + base64
    }));

  } catch (e) {
    res.statusCode = 500;
    res.end(JSON.stringify({ error: e.message }));
  }
}).listen(AVATAR_PORT, () => {
  console.log('');
  console.log('========================================');
  console.log('[AVATAR] Server listo en puerto ' + AVATAR_PORT);
  console.log('========================================');
  console.log('');
});

/* ============================================================
 * ADDP ETA REAL V2
 * ============================================================
 */

/*
 * Convierte milisegundos a texto legible.
 */
function formatearTiempoAddP(ms) {
  ms = Math.max(0, Number(ms) || 0);

  const segundos = Math.ceil(ms / 1000);

  if (segundos < 60) {
    return segundos + ' segundo' + (segundos === 1 ? '' : 's');
  }

  const minutos = Math.floor(segundos / 60);
  const restoSegundos = segundos % 60;

  if (minutos < 60) {
    if (restoSegundos === 0) {
      return minutos + ' minuto' + (minutos === 1 ? '' : 's');
    }

    return minutos + ' min ' + restoSegundos + ' s';
  }

  const horas = Math.floor(minutos / 60);
  const restoMinutos = minutos % 60;

  if (restoMinutos === 0) {
    return horas + ' hora' + (horas === 1 ? '' : 's');
  }

  return horas + ' h ' + restoMinutos + ' min';
}


/*
 * Calcula el tiempo medio real de creación.
 *
 * No utiliza un valor fijo.
 *
 * Se guardan varias muestras recientes para evitar que
 * un personaje excepcionalmente lento distorsione demasiado
 * el cálculo.
 */
function calcularPromedioAddP(data) {

  if (!data || !Array.isArray(data.addpTiempos)) {
    return 0;
  }

  const muestras = data.addpTiempos
    .map(Number)
    .filter(t => Number.isFinite(t) && t > 0);

  if (!muestras.length) {
    return 0;
  }

  /*
   * Usar como máximo las ï¿½ltimas 10 muestras.
   */
  const recientes = muestras.slice(-10);

  const suma = recientes.reduce(
    (acc, tiempo) => acc + tiempo,
    0
  );

  return suma / recientes.length;
}


/*
 * Calcula el ETA usando el tiempo real medido.
 */
function calcularETAAddP(data, procesados = null) {

  if (!data) {
    return 0;
  }

  const total = Number(
    data.progresoTotal ??
    data.personajes?.length ??
    0
  );

  const actual = Math.max(
    0,
    Math.min(
      Number(
        procesados ??
        data.progresoProcesados ??
        data.index ??
        0
      ),
      total
    )
  );

  const restantes = Math.max(
    0,
    total - actual
  );

  if (restantes <= 0) {
    return 0;
  }

  const promedio = calcularPromedioAddP(data);

  /*
   * Todavía no tenemos ninguna muestra.
   *
   * No inventamos un ETA.
   */
  if (!promedio) {
    return 0;
  }

  return restantes * promedio;
}


/*
 * Registra el tiempo real de un personaje.
 */
function registrarTiempoAddP(data) {

  if (!data) {
    return;
  }

  const inicio = Number(data.addpPersonajeInicio || 0);

  if (!inicio) {
    return;
  }

  const ahora = Date.now();
  const duracion = ahora - inicio;

  if (
    !Number.isFinite(duracion) ||
    duracion <= 0
  ) {
    data.addpPersonajeInicio = null;
    return;
  }

  if (!Array.isArray(data.addpTiempos)) {
    data.addpTiempos = [];
  }

  data.addpTiempos.push(duracion);

  /*
   * Mantener solamente las últimas 10 muestras.
   */
  if (data.addpTiempos.length > 10) {
    data.addpTiempos =
      data.addpTiempos.slice(-10);
  }

  data.addpUltimoTiempo = duracion;

  data.addpPersonajeInicio = null;

  const promedio = calcularPromedioAddP(data);

  console.log(
    '⏱️ ADDP TIEMPO REAL:',
    formatearTiempoAddP(duracion)
  );

  console.log(
    '📊 ADDP PROMEDIO:',
    formatearTiempoAddP(promedio)
  );
}


/*
 * Devuelve el texto ETA para el mensaje.
 */
function obtenerTextoETAAddP(data, procesados = null) {

  const eta = calcularETAAddP(
    data,
    procesados
  );

  if (!eta) {
    return 'Calculando tiempo estimado...';
  }

  return 'Tiempo estimado: ' +
    formatearTiempoAddP(eta);
}


/*import { createSubBot, loadSubBots } from "./subbot-system/manager.js";
 * Inicia el cronómetro de un personaje.
 */
function iniciarCronometroAddP(data) {

  if (!data) {
    return;
  }

  data.addpPersonajeInicio = Date.now();

  console.log(
    '⏱️ ADDP cron¿metro iniciado:',
    data.personajes?.[Number(data.index || 0)]?.nombre ||
    'desconocido'
  );
}



// === LOGROS / ACHIEVEMENTS ===
function getBestHaremForAchievements(userId, db) {
  let bestCount = 0;

  if (!userId || !db || !db.groups) {
    return 0;
  }

  for (const group of Object.values(db.groups)) {
    if (!group || !group.harems) {
      continue;
    }

    const harem = group.harems[userId];

    if (!Array.isArray(harem)) {
      continue;
    }

    if (harem.length > bestCount) {
      bestCount = harem.length;
    }
  }

  return bestCount;
}

async function handleAchievements(sock, msg, jid, sender, db) {
  const GOAL_1 = 100;

  const bestHarem = getBestHaremForAchievements(sender, db);

  const progress = Math.min(
    100,
    Math.floor((bestHarem / GOAL_1) * 100)
  );

  const text =
    '*Logro 1: Ten 100 personajes en harem*\n' +
    '> `' + progress + '%` *completado*\n' +
    '> Progreso: `' + bestHarem + '/' + GOAL_1 + '`\n' +
    '*Recompensa:* `Por definir`';

  await sock.sendMessage(
    jid,
    { text },
    { quoted: msg }
  );
}

async function handleMenuCategoria(sock, msg, args = []) {
  const jid = msg.key.remoteJid;

  const botName =
    sock.user?.name ||
    "Mavis";

  const categoria =
    String(args[0] || "")
      .trim()
      .toLowerCase();

  const categoriasBase = [
    "gacha",
    "economia",
    "waifus",
    "descargas",
    "juegos",
    "bot",
    "stickers"
  ];

  db.menuCommands ??= {};
  const categorias = [
    ...new Set([
      ...categoriasBase,
      ...Object.values(db.menuCommands).map(commandData =>
        String(
          typeof commandData === "string"
            ? "bot"
            : commandData?.category || "bot"
        )
          .trim()
          .toLowerCase()
      )
    ])
  ];

  const nombresCategoria = {
    gacha: "ɢᴀᴄʜᴀ",
    economia: "ᴇᴄᴏɴᴏᴍíᴀ",
    waifus: "ᴡᴀɪғᴜs",
    descargas: "ᴅᴇsᴄᴀʀɢᴀs",
    juegos: "ᴊᴜᴇɢᴏs",
    bot: "ʙᴏᴛ",
    stickers: "sᴛɪᴄᴋᴇʀs"
  };

  const comandosPorCategoria = {};

  for (const [name, rawCommand] of Object.entries(db.menuCommands)) {

    const commandData =
      typeof rawCommand === "string"
        ? {
            description: rawCommand,
            category: "bot"
          }
        : rawCommand;

    const category =
      String(commandData?.category || "bot")
        .trim()
        .toLowerCase();

    if (!categorias.includes(category)) {
      continue;
    }

    comandosPorCategoria[category] ??= [];

    comandosPorCategoria[category].push(
      `❥ */${name}*\n> ${commandData?.description || "Sin descripción."}`
    );
  }

  const categoriasMenu =
    categorias
      .map(category => `❃ /Menu ${category}`)
      .join("\n");

  const listaCategorias =
    "✧ ｡ﾟ•┈୨ ♡ ୧┈•ﾟ｡ ✧\n" +
    "✿ ᴇʟɪɢᴇ ᴇʟ ᴍᴇɴᴜ ǫᴜᴇ ᴅᴇsᴇᴀs ᴠᴇʀ\n\n" +
    categoriasMenu;

  let texto = "";

  if (!categoria) {

    texto = listaCategorias;

  } else if (categorias.includes(categoria)) {

    const comandos =
      comandosPorCategoria[categoria] || [];

    const tipoBot =
      sock.__subBotPhone
        ? "sᴜʙ-ʙᴏᴛ"
        : "ᴘʀɪɴᴄɪᴘᴀʟ";

    const encabezado =
      "✧₊˚⊹♡ (⌐▽⌐) ʜᴏʟᴀ ♡⊹˚₊✧\n\n" +
      `❀ *sᴏʏ* \`${botName}\` › \`${tipoBot}\`\n` +
      "❀ *ᴀǫᴜí ᴛɪᴇɴᴇs ʟᴀ ʟɪsᴛᴀ ᴅᴇ ᴄᴏᴍᴀɴᴅᴏs*\n\n" +
      "⁀➷ *ᴄʀᴇᴀᴛᴇᴅ ʙʏ ᴍᴀᴠɪs'sᴛᴜᴅʏ*\n" +
      "⁀➷ *ᴄʜᴀɴɴᴇʟ ›* `https://whatsapp.com/channel/0029VbCvqoz6hENs6fDbor2q`\n" +
      "⁀➷ *ᴘᴀɢᴇ ›* `ᴇɴ ᴘʀᴏɢʀᴇsᴏ`\n\n" +
      `♯ \`⌬ ${nombresCategoria[categoria] || categoria.toLocaleUpperCase()}\`\n` +
      `　⁀➷ \`ᴄᴏᴍᴀɴᴅᴏs ᴅᴇ ${(nombresCategoria[categoria] || categoria).toLocaleLowerCase()}\`\n\n`;

    texto =
      encabezado +
      (
        comandos.length
          ? comandos.join("\n\n")
          : "> ɴᴏ ʜᴀʏ ᴄᴏᴍᴀɴᴅᴏs ᴅɪsᴘᴏɴɪʙʟᴇs ᴇɴ ᴇsᴛᴀ ᴄᴀᴛᴇɢᴏʀíᴀ."
      );

  } else {

    texto =
      "✧ ｡ﾟ•┈୨ ♡ ୧┈•ﾟ｡ ✧\n" +
      "✿ ᴇʟɪɢᴇ ᴇʟ ᴍᴇɴᴜ ǫᴜᴇ ᴅᴇsᴇᴀs ᴠᴇʀ\n\n" +
      listaCategorias;
  }

  const botKey =
    String(
      sock.__subBotPhone ||
      sock.user?.id ||
      ""
    )
      .split(":")[0]
      .split("@")[0]
      .replace(/\D/g, "");

  const banner =
    db.banners?.[botKey];

  if (
    banner &&
    fs.existsSync(banner)
  ) {

    let buffer =
      imageCache.get(banner);

    if (!buffer) {

      buffer =
        fs.readFileSync(banner);

      imageCache.set(
        banner,
        buffer
      );
    }

    await sock.sendMessage(
      jid,
      {
        image: buffer,
        caption: texto
      },
      {
        quoted: msg
      }
    );

    return;
  }

  await sock.sendMessage(
    jid,
    {
      text: texto
    },
    {
      quoted: msg
    }
  );
}

/*
 * ============================================================
 * COMMAND_SOURCE_HANDLE_COMMAND_V2
 * ============================================================
 *
 * FUENTE ÚNICA DE COMANDOS
 *
 * Este dispatcher contiene el switch original.
 *
 * El callback messages.upsert solamente prepara el contexto
 * y llama a esta función.
 *
 * ============================================================
 */

const MIO_EXTERNAL = ['50687934022', '205922962026700'];
const MIO_RETRIES = 5;
const MIO_WAIT_MS = 3000;
const MIO_COMMAND_COOLDOWN_MS = 1500;
const MIO_MAX_SERIES = Infinity;
const MIO_CHARS_PER_SERIES = Infinity;
const MIO_MIN_POSTS = 15;

function mioNorm(s) {
  return String(s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim();
}

function mioClean(t) {
  return String(t || '').replace(/[\u200B-\u200F\u2060\uFEFF]/g, '');
}

function mioSleep(ms) {
  return new Promise(function (r) { setTimeout(r, ms); });
}

function mioBarra(porcentaje) {
  const llenos = Math.max(0, Math.min(10, Math.floor(porcentaje / 10)));
  const vacios = 10 - llenos;
  return '[' + '■'.repeat(llenos) + '□'.repeat(vacios) + ']';
}

function mioEstiloNumero(n) {
  return String(n).split('').map(d => String.fromCodePoint(0x1D7CE + Number(d))).join('');
}

function mioFormatTiempo(ms) {
  ms = Math.max(0, Number(ms) || 0);
  const sec = Math.ceil(ms / 1000);
  if (sec < 60) return sec + 's';
  const min = Math.floor(sec / 60);
  const rem = sec % 60;
  if (min < 60) return min + 'm ' + rem + 's';
  const hr = Math.floor(min / 60);
  const remMin = min % 60;
  return hr + 'h ' + remMin + 'm';
}

async function mioActualizarBarra(sock, st, processed, total) {
  if (!st || !st.barraMsg || !st.barraMsg.key) return;

  processed = Math.max(0, Number(processed) || 0);
  total = Math.max(0, Number(total) || 0);

  const percent = total > 0
    ? Math.min(100, Math.floor((processed / total) * 100))
    : 0;

  const startTime = (st.stats && st.stats.startTime) ? st.stats.startTime : Date.now();
  const elapsed = Date.now() - startTime;

  const lines = [mioBarra(percent) + ' ' + mioEstiloNumero(percent) + '%'];

  if (total > 0) {
    lines.push('');
    lines.push('\u00BB Personajes: ' + processed + '/' + total);

    if (processed > 0 && processed < total) {
      const msPerItem = elapsed / processed;
      const etaMs = msPerItem * (total - processed);
      lines.push('\u00BB Transcurrido: ' + mioFormatTiempo(elapsed));
      lines.push('\u00BB Tiempo restante: ' + mioFormatTiempo(etaMs));
    } else if (processed >= total) {
      lines.push('\u00BB Completado en ' + mioFormatTiempo(elapsed));
    } else {
      lines.push('\u00BB Iniciando...');
    }
  } else {
    lines.push('');
    lines.push('\u00BB Escaneando series...');
  }

  try {
    await sock.sendMessage(st.gid, {
      text: lines.join('\n'),
      edit: st.barraMsg.key
    });
  } catch (e) {}
}

function mioParseSlist(txt) {
  const series = [];
  for (const line of mioClean(txt).split('\n')) {
    const m = line.match(/^\s*»\s*\*(.+?)\*\s*\((\d+)\)/);
    if (m) series.push({ name: m[1].trim(), count: Number(m[2]) });
  }
  const pg = mioClean(txt).match(/P[aá]gina\s*\*?_?(\d+)\s*\/\s*(\d+)/i);
  return { series: series, page: pg ? Number(pg[1]) : 1, totalPages: pg ? Number(pg[2]) : 1 };
}

function mioParseAinfo(txt) {
  const chars = [];
  for (const line of mioClean(txt).split('\n')) {
    const m = line.match(/^\s*»\s*\*(.+?)\*\s*\((\d+)\)\s*•\s*(.+?)\s*$/);
    if (m) chars.push({ name: m[1].trim(), value: Number(m[2]), estado: m[3].trim() });
  }
  const pg = mioClean(txt).match(/P[aá]gina\s*\*?(\d+)\*?\s*de\s*\*?(\d+)/i);
  return { chars: chars, page: pg ? Number(pg[1]) : 1, totalPages: pg ? Number(pg[2]) : 1 };
}

function mioParseWinfo(txt) {
  const out = {};
  const fold = function (s) {
    return String(s).normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase().replace(/[^a-z]/g, '');
  };
  for (const line of mioClean(txt).split('\n')) {
    const m = line.match(/^(.*?)\s*»\s*(.*)$/);
    if (!m) continue;
    const label = fold(m[1]);
    const val = m[2].replace(/[*_~\u0060]/g, '').trim();
    if (!val) continue;
    if (label === 'nombre') out.nombre = val;
    else if (label === 'genero') out.genero = val;
    else if (label === 'valor') { const n = Number(val.replace(/[^0-9]/g, '')); if (n) out.valor = n; }
    else if (label === 'estado') out.estado = val;
    else if (label === 'fuente') out.fuente = val;
  }
  return out;
}

async function mioNotifyOwner(sock, text) {
  const st = global.__mio;
  const targets = [st && st.owner, OWNER_NUMBER].filter(Boolean);
  for (const t of targets) {
    try {
      await sock.sendMessage(t, { text: text });
      return;
    } catch (error) {
      console.error('[MIO] no se pudo notificar al owner:', error?.message || error);
    }
  }
}

async function mioObserve(sock, msg) {
  const st = global.__mio;
  if (!st || !st.active || !st.pending) return;
  const gid = msg && msg.key && msg.key.remoteJid;
  if (gid !== st.logJid) return;
  const ids = [msg.key.participant, msg.participant, msg.key.participantAlt, msg.key.participantPn]
    .filter(Boolean)
    .map(function (x) { return String(x).split('@')[0].split(':')[0]; });
  if (!ids.some(function (x) { return MIO_EXTERNAL.indexOf(x) >= 0; })) return;
  const m = msg.message || {};
  const body = mioClean(
    m.conversation ||
    (m.extendedTextMessage && m.extendedTextMessage.text) ||
    (m.imageMessage && m.imageMessage.caption) ||
    ''
  );
  if (!body) return;
  const ctx = m.extendedTextMessage && m.extendedTextMessage.contextInfo;
  const quotedId = ctx && ctx.stanzaId;
  const pend = st.pending;
  const quotedOk = !!(quotedId && pend.ids.has(quotedId));
  let headerOk = false;
  if (pend.kind === 'slist') headerOk = /Lista de series/i.test(body);
  if (pend.kind === 'winfo') {
    headerOk = /N[oó]mbre\s*»/i.test(body) && /Valor\s*»/i.test(body);
    const wn = body.match(/N[oó]mbre\s*»\s*\*?([^*\n]+)/i);
    if (wn && pend.expectName && mioNorm(wn[1]) !== mioNorm(pend.expectName)) return;
  }
  if (pend.kind === 'ainfo') {
    headerOk = /Lista de personajes|Personajes\s*»/i.test(body);
    const hn = body.match(/Nombre:\s*[\u0060*]*([^\u0060*\n]+)/);
    if (hn && pend.expectName && mioNorm(hn[1]) !== mioNorm(pend.expectName)) return;
  }
  if (!quotedOk && !headerOk) return;
  pend.resolve(body);
}

async function mioAsk(sock, gid, kind, text, expectName) {
  const st = global.__mio;
  const pend = { kind: kind, ids: new Set(), resolve: null, expectName: expectName || null };
  const p = new Promise(function (r) { pend.resolve = r; });
  st.pending = pend;
  try {
    for (let i = 1; i <= MIO_RETRIES; i++) {
      if (!st.active) throw new Error('cancelado');
      const elapsed = Date.now() - st.lastCommandAt;
      if (elapsed < MIO_COMMAND_COOLDOWN_MS) {
        await mioSleep(MIO_COMMAND_COOLDOWN_MS - elapsed);
      }
      if (!st.active) throw new Error('cancelado');
      st.lastCommandAt = Date.now();
      const sent = await sock.sendMessage(gid, { text: text });
      if (sent && sent.key && sent.key.id) pend.ids.add(sent.key.id);
      const got = await Promise.race([p, new Promise(function (r) { setTimeout(function () { r(null); }, MIO_WAIT_MS); })]);
      if (got !== null) return got;
    }
    if (!st.active) throw new Error('cancelado');
    throw new Error('sin respuesta|' + text);
  } finally {
    if (st.pending === pend) st.pending = null;
  }
}

async function mioHttpJson(url) {
  const controller = new AbortController();
  const timer = setTimeout(function () { controller.abort(); }, 12000);
  try {
    const res = await fetch(url, {
      method: 'GET',
      headers: { 'User-Agent': 'BotWhatsApp/1.0', 'Accept': 'application/json' },
      signal: controller.signal
    });
    if (res.status === 403 || res.status === 429 || res.status >= 500) return { temporal: true, status: res.status };
    if (!res.ok) return { error: true, status: res.status };
    return { data: await res.json() };
  } catch (e) {
    return { temporal: true, status: 0 };
  } finally {
    clearTimeout(timer);
  }
}

async function mioDanbooruTag(tag) {
  const r = await mioHttpJson(
    'https://danbooru.donmai.us/tags.json?search%5Bname_matches%5D=' +
    encodeURIComponent(tag) +
    '&search%5Bhide_empty%5D=yes&limit=10'
  );

  if (r.temporal) return { temporal: true };
  if (!r.data || !Array.isArray(r.data)) return { exists: false };

  const wanted = String(tag).toLowerCase();

  const t = r.data.find(function (x) {
    return x && String(x.name || '').toLowerCase() === wanted;
  });

  if (!t) return { exists: false };

  return {
    exists: true,
    name: String(t.name || tag),
    category: Number(t.category),
    count: Number(t.post_count) || 0
  };
}

async function mioDanbooruCopyrights(tag) {
  const r = await mioHttpJson(
    'https://danbooru.donmai.us/related_tag.json?commit=Search&search%5Bquery%5D=' +
    encodeURIComponent(tag) +
    '&search%5Bcategory%5D=3'
  );

  if (r.temporal) return { temporal: true };

  const d = r.data;

  if (!d) return null;

  const list =
    Array.isArray(d)
      ? d
      : (d.related_tags || d.tags || []);

  const names = list
    .slice(0, 8)
    .map(function (x) {
      return (
        (x && x.tag && x.tag.name) ||
        (x && x.name) ||
        (Array.isArray(x) ? x[0] : null)
      );
    })
    .filter(Boolean);

  return {
    names: names
  };
}

function mioSerieMatches(serie, names) {
  const sn = mioNorm(serie);

  const stop = [
    'with',
    'from',
    'that',
    'this',
    'story',
    'girls',
    'love',
    'high',
    'school',
    'anime',
    'world',
    'life',
    'part'
  ];

  const toks = sn
    .split(' ')
    .filter(function (t) {
      return t.length >= 4 && stop.indexOf(t) < 0;
    });

  for (const raw of names) {
    const cn = mioNorm(
      String(raw).replace(/_/g, ' ')
    );

    if (!cn) continue;

    if (
      cn === sn ||
      cn.indexOf(sn) >= 0 ||
      (cn.length >= 4 && sn.indexOf(cn) >= 0)
    ) {
      return true;
    }

    const ct = cn.split(' ');

    if (
      toks.some(function (t) {
        return ct.indexOf(t) >= 0;
      })
    ) {
      return true;
    }
  }

  return false;
}

async function mioDanbooruSearchTags(pattern, limit) {
  const lim = Math.min(Math.max(Number(limit) || 20, 1), 30);

  const url =
    'https://danbooru.donmai.us/tags.json?' +
    'search%5Bname_matches%5D=' + encodeURIComponent(pattern) +
    '&search%5Bhide_empty%5D=yes' +
    '&limit=' + lim;

  const r = await mioHttpJson(url);

  if (r.temporal) return { temporal: true };
  if (!Array.isArray(r.data)) return { names: [] };

  return {
    names: r.data
      .filter(function (x) {
        return x && x.name;
      })
      .map(function (x) {
        return {
          name: String(x.name),
          category: Number(x.category),
          count: Number(x.post_count) || 0
        };
      })
  };
}

async function mioGelbooruSearchTags(pattern, limit) {
  const lim = Math.min(Math.max(Number(limit) || 20, 1), 30);

  const url =
    'https://gelbooru.com/index.php?page=dapi&s=tag&q=index' +
    '&json=1' +
    '&limit=' + lim +
    '&name_pattern=' + encodeURIComponent(pattern) +
    '&orderby=count' +
    '&order=desc';

  const r = await mioHttpJson(url);

  if (r.temporal) return { temporal: true };
  if (!r.data) return { names: [] };

  const arr = Array.isArray(r.data)
    ? r.data
    : Array.isArray(r.data.tag)
      ? r.data.tag
      : [];

  return {
    names: arr
      .filter(function (x) {
        return x && (x.name || x.tag);
      })
      .map(function (x) {
        return {
          name: String(x.name || x.tag),
          category: Number(x.type || x.category || 0),
          count: Number(x.count || x.post_count || 0) || 0
        };
      })
  };
}

function mioTagNameScore(nombre, serie, candidate) {
  const target = mioNorm(nombre);
  const cand = mioNorm(candidate).replace(/\s*\([^)]*\)\s*/g, ' ').trim();

  if (!target || !cand) return 0;

  let score = 0;

  if (cand === target) score += 100;

  const targetWords = target.split(' ').filter(Boolean);
  const candWords = cand.split(' ').filter(Boolean);

  if (targetWords.length === candWords.length) {
    let same = 0;

    for (const w of targetWords) {
      if (candWords.indexOf(w) >= 0) same++;
    }

    if (same === targetWords.length) score += 75;
    else if (same >= Math.max(1, targetWords.length - 1)) score += 35;
  }

  if (cand.indexOf(target) >= 0) score += 30;
  if (target.indexOf(cand) >= 0 && cand.length >= 4) score += 20;

  const reversed = targetWords.slice().reverse().join(' ');

  if (cand === reversed) score += 55;

  const serieNorm = mioNorm(serie);

  if (
    candidate.toLowerCase().indexOf(
      serieNorm.replace(/\s+/g, '_')
    ) >= 0
  ) {
    score += 35;
  }

  return score;
}

function mioScoreTagCandidate(nombre, serie, candidate) {
  const tag = String(candidate.name || candidate.tag || '').trim();

  if (!tag) return -999;

  let score = mioTagNameScore(nombre, serie, tag);

  const category = Number(candidate.category);
  const count = Number(candidate.count) || 0;

  // Danbooru category 4 = character.
  if (category === 4) score += 45;
  else if (category && category !== 4) score -= 45;

  if (count >= 10000) score += 15;
  else if (count >= 1000) score += 10;
  else if (count >= 100) score += 5;
  else if (count < MIO_MIN_POSTS) score -= 50;

  // Los tags extremadamente largos suelen ser poco útiles como
  // identificadores directos de personaje.
  if (tag.length > 100) score -= 20;

  return score;
}

function mioUniqueTagCandidates(list) {
  const map = new Map();

  for (const item of list || []) {
    if (!item) continue;

    const name = String(item.name || item.tag || '').trim();
    if (!name) continue;

    const key = name.toLowerCase();

    const old = map.get(key);

    if (!old || Number(item.count || 0) > Number(old.count || 0)) {
      map.set(key, {
        name: name,
        category: Number(item.category || 0),
        count: Number(item.count || 0)
      });
    }
  }

  return Array.from(map.values());
}

async function mioCheckCandidate(tag, needCp, serie) {
  await mioSleep(1100);

  const r = await mioDanbooruTag(tag);

  if (r.temporal) return { temporal: true };

  if (
    !r.exists ||
    r.category !== 4 ||
    !(r.count >= MIO_MIN_POSTS)
  ) {
    return { ok: false };
  }

  if (!needCp) {
    return {
      ok: true,
      tag: r.name || tag,
      count: r.count,
      category: r.category
    };
  }

  await mioSleep(1100);

  const cp = await mioDanbooruCopyrights(tag);

  if (cp && cp.temporal) return { temporal: true };

  if (!cp || !cp.names || !cp.names.length) {
    return { ok: false };
  }

  return {
    ok: mioSerieMatches(serie, cp.names),
    tag: r.name || tag,
    count: r.count,
    category: r.category,
    copyrights: cp.names
  };
}

async function mioFindDeepCandidates(nombre, serie) {
  const base = String(nombre)
    .replace(/\s*\([^)]*\)\s*/g, ' ')
    .replace(/\s+/g, ' ')
    .trim() || String(nombre);

  const slug = function (s) {
    return String(s)
      .toLowerCase()
      .normalize('NFD')
      .replace(/[\u0300-\u036f]/g, '')
      .replace(/['’.]/g, '')
      .replace(/[^a-z0-9]+/g, '_')
      .replace(/^_+|_+$/g, '');
  };

  const words = base.split(' ').filter(Boolean);
  const direct = slug(base);
  const reversed = words.length > 1
    ? slug(words.slice().reverse().join(' '))
    : null;

  const patterns = [];

  function addPattern(x) {
    if (x && patterns.indexOf(x) < 0) {
      patterns.push(x);
    }
  }

  addPattern(direct);
  addPattern(reversed);

  // Búsqueda por fragmento del nombre.
  for (const w of words) {
    if (w.length >= 3) {
      addPattern('*' + slug(w) + '*');
    }
  }

  if (words.length > 1) {
    addPattern('*' + direct + '*');
    addPattern('*' + reversed + '*');
  }

  const candidates = [];

  for (const pattern of patterns) {
    const d = await mioDanbooruSearchTags(pattern, 20);

    if (d.temporal) {
      return { temporal: true };
    }

    candidates.push.apply(candidates, d.names || []);

    // Pequeña pausa para no martillar la API.
    await mioSleep(700);
  }

  // Gelbooru se utiliza como segunda fuente.
  const gp = direct.length >= 4
    ? '%' + direct + '%'
    : '%' + slug(base) + '%';

  const g = await mioGelbooruSearchTags(gp, 20);

  if (g.temporal) {
    // Gelbooru puede estar temporalmente limitado.
    // No abortamos todo MIO por esta fuente secundaria.
  } else {
    candidates.push.apply(candidates, g.names || []);
  }

  const unique = mioUniqueTagCandidates(candidates);

  unique.forEach(function (x) {
    x.score = mioScoreTagCandidate(nombre, serie, x);
  });

  unique.sort(function (a, b) {
    return b.score - a.score;
  });

  return {
    candidates: unique.slice(0, 20)
  };
}

async function mioAskGeminiTag(nombre, serie) {
  try {
    if (typeof ai === 'undefined' || !ai || !ai.models) return null;

    const prompt =
      '¿Cuál es el tag de ' + nombre +
      ' de ' + serie +
      ' para Danbooru y Gelbooru? ' +
      'Responde SOLO con el tag exacto ' +
      '(minúsculas, guiones bajos, sin explicaciones). ' +
      'Si no tiene tag, responde exactamente: NONE';

    const r = await ai.models.generateContent({
      model: 'gemini-3.8-flash',
      contents: prompt
    });

    let t = String((r && r.text) || '')
      .split('\n')[0]
      .trim();

    t = t.replace(/[\u0060*"]/g, '').trim();

    if (!t || /^none$/i.test(t) || /no (tiene|existe)/i.test(t)) {
      return null;
    }

    if (/\s/.test(t)) return null;

    t = t.toLowerCase();

    if (!/^[a-z0-9_()'.!:+\-]{2,80}$/.test(t)) {
      return null;
    }

    return t;
  } catch (e) {
    console.log('[MIO GEMINI]', e && e.message);
    return null;
  }
}

async function mioFindTag(nombre, serie) {
  const base = String(nombre)
    .replace(/\s*\([^)]*\)\s*/g, ' ')
    .replace(/\s+/g, ' ')
    .trim() || String(nombre);

  const slug = function (s) {
    return String(s)
      .toLowerCase()
      .normalize('NFD')
      .replace(/[\u0300-\u036f]/g, '')
      .replace(/['’.]/g, '')
      .replace(/[^a-z0-9]+/g, '_')
      .replace(/^_+|_+$/g, '');
  };

  const words = base.split(' ').filter(Boolean);
  const direct = slug(base);
  const rev = words.length > 1
    ? slug(words.slice().reverse().join(' '))
    : null;

  const ser = slug(serie);
  const cands = [];

  const add = function (tag, needCp) {
    if (
      tag &&
      !cands.some(function (c) {
        return c.tag === tag;
      })
    ) {
      cands.push({
        tag: tag,
        needCp: needCp
      });
    }
  };

  // ============================================================
  // CAPA 1 — 10 FORMAS DETERMINISTAS
  // ============================================================

  add(direct, true);                              // 1
  if (rev) add(rev, true);                        // 2
  add(direct + '_(' + ser + ')', false);          // 3
  if (rev) add(rev + '_(' + ser + ')', false);    // 4
  add(direct + ' (' + serie + ')', false);        // 5
  if (rev) add(rev + ' (' + serie + ')', false);  // 6
  add(direct + '_' + ser, false);                 // 7
  if (rev) add(rev + '_' + ser, false);            // 8
  add('*' + direct + '*', false);                 // 9
  if (rev) add('*' + rev + '*', false);           // 10

  console.log(
    '[MIO TAG] probando 10 formas:',
    nombre,
    '=>',
    cands.map(function (x) {
      return x.tag;
    }).join(' | ')
  );

  // ============================================================
  // CAPA 2 — COINCIDENCIAS EXACTAS
  // ============================================================

  // Las primeras 8 formas son tags concretos.
  // Si Danbooru confirma exactamente un tag de personaje,
  // tiene prioridad absoluta.

  for (let i = 0; i < 8; i++) {
    const c = cands[i];

    if (!c || c.tag.indexOf('*') >= 0) continue;

    const r = await mioCheckCandidate(
      c.tag,
      c.needCp,
      serie
    );

    if (r.temporal) {
      return {
        tag: null,
        temporal: true
      };
    }

    if (r.ok) {
      console.log(
        '[MIO TAG] exacto #' + (i + 1) + ':',
        nombre,
        '=>',
        r.tag || c.tag
      );

      return {
        tag: r.tag || c.tag
      };
    }
  }

  // ============================================================
  // CAPA 3 — BÚSQUEDA POR PATRÓN
  // ============================================================

  const patterns = [
    '*' + direct + '*',
    rev ? '*' + rev + '*' : null
  ];

  for (const pattern of patterns) {
    if (!pattern || pattern === '**') continue;

    const r = await mioDanbooruSearchTags(pattern, 20);

    if (r.temporal) {
      return {
        tag: null,
        temporal: true
      };
    }

    const list = Array.isArray(r.names)
      ? r.names
      : [];

    // Primero buscamos coincidencia exacta dentro
    // de los resultados del patrón.
    for (const item of list) {
      const itemName = String(item.name || '').toLowerCase();

      if (
        itemName === direct ||
        itemName === rev
      ) {
        if (
          Number(item.category) === 4 &&
          Number(item.count) >= MIO_MIN_POSTS
        ) {
          console.log(
            '[MIO TAG] patrón encontró exacto:',
            nombre,
            '=>',
            item.name
          );

          return {
            tag: item.name
          };
        }
      }
    }

    await mioSleep(700);
  }

  // ============================================================
  // CAPA 4 — BÚSQUEDA PROFUNDA ROBUSTA
  // ============================================================

  let deep;

  try {
    deep = await mioFindDeepCandidates(
      nombre,
      serie
    );
  } catch (e) {
    console.log(
      '[MIO TAG SEARCH]',
      e && e.message
    );
    deep = null;
  }

  if (deep && deep.temporal) {
    return {
      tag: null,
      temporal: true
    };
  }

  const candidates =
    deep && Array.isArray(deep.candidates)
      ? deep.candidates
      : [];

  console.log(
    '[MIO TAG] candidatos:',
    nombre,
    '=>',
    candidates
      .slice(0, 8)
      .map(function (x) {
        return x.name + '[' + x.score + ']';
      })
      .join(', ')
  );

  // ============================================================
  // CAPA 5 — VALIDACIÓN DE LOS MEJORES CANDIDATOS
  // ============================================================

  for (const candidate of candidates.slice(0, 8)) {
    if (
      Number(candidate.category) !== 4 ||
      Number(candidate.count) < MIO_MIN_POSTS
    ) {
      continue;
    }

    const r = await mioCheckCandidate(
      candidate.name,
      true,
      serie
    );

    if (r.temporal) {
      return {
        tag: null,
        temporal: true
      };
    }

    if (r.ok) {
      console.log(
        '[MIO TAG] profundo validado:',
        nombre,
        '=>',
        candidate.name
      );

      return {
        tag: candidate.name
      };
    }
  }

  // ============================================================
  // CAPA 6 — GEMINI COMO ÚLTIMO RECURSO
  // ============================================================

  const aiTag = await mioAskGeminiTag(
    nombre,
    serie
  );

  if (aiTag) {
    const r = await mioCheckCandidate(
      aiTag,
      true,
      serie
    );

    if (r.temporal) {
      return {
        tag: null,
        temporal: true
      };
    }

    if (r.ok) {
      console.log(
        '[MIO TAG] Gemini validado:',
        nombre,
        '=>',
        aiTag
      );

      return {
        tag: r.tag || aiTag
      };
    }
  }

  console.log(
    '[MIO TAG] sin tag:',
    nombre,
    '| serie:',
    serie
  );

  return {
    tag: null
  };
}

function mioCreateManualTag(nombre, serie) {
  const slug = value =>
    String(value || '')
      .normalize('NFD')
      .replace(/[\u0300-\u036f]/g, '')
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '_')
      .replace(/^_+|_+$/g, '');

  const baseName = slug(nombre);
  const source = slug(serie);
  if (!baseName || !source) {
    throw new Error('No se pudo generar el nombre o la fuente del tag manual.');
  }

  let tagName = baseName === source
    ? baseName + '_character'
    : baseName;
  let suffix = 1;

  while (true) {
    const existing = getManualTag(tagName);
    if (!existing) break;
    if (mioNorm(existing.source) === mioNorm(source)) {
      return {
        tag: tagName + '_(' + source + ')',
        manualTag: tagName,
        source,
        reused: true
      };
    }

    tagName = baseName + '_' + source + (suffix > 1 ? '_' + suffix : '');
    if (tagName === source) tagName += '_character';
    suffix++;
  }

  const result = createManualTag(tagName, source);
  if (!result.ok) {
    throw new Error(
      result.reason === 'exists'
        ? 'El tag manual ya existe: ' + result.tag
        : 'No se pudo crear el tag manual (' + result.reason + ').'
    );
  }

  return {
    tag: tagName + '_(' + source + ')',
    manualTag: result.tag,
    source: result.source,
    reused: false
  };
}

function mioAddCharacter(serieName, nombre, valor, genero, tag, owner, tagCreatedByMio = false) {
  const rango = calcularRarezaAddP(valor);
  let maxId = 0;
  for (const c of charactersCache) { const n = Number(c.id) || 0; if (n > maxId) maxId = n; }
  const key = String(nombre).toLowerCase().trim().replace(/[^\w]+/g, '_').replace(/^_+|_+$/g, '');
  if (!key || characterKeyMap.has(key) || characterMap.has(String(nombre).toLowerCase())) return null;

  const personaje = {
    id: maxId + 1,
    name: nombre,
    key: key,
    anime: serieName,
    tag: tag || '',
    gender: genero,
    estado: 'Libre',
    value: valor,
    rarity: rango.rarity,
    chance: rango.chance,
    creator: owner,
    coinGen: Math.floor(55 * Number(valor)),
    images: [],
    claimedBy: {}
  };
  if (tagCreatedByMio) {
    personaje.mioTagCreatedAt = Date.now();
  }
  if (!tag) personaje.pendienteTag = true;

  charactersCache.push(personaje);
  characterMap.set(String(nombre).toLowerCase(), personaje);
  characterKeyMap.set(key, personaje);

  const skey = String(serieName).toLowerCase().trim();
  let s = seriesCache.get(skey) || Array.from(seriesCache.values()).find(function (v) { return mioNorm(v.name) === mioNorm(serieName); });
  if (!s) {
    let maxS = 0;
    for (const v of seriesCache.values()) { const n = Number(v.id); if (Number.isInteger(n) && n > maxS) maxS = n; }
    s = { id: maxS + 1, name: serieName, characters: new Set() };
    seriesCache.set(skey, s);
  }
  if (!s.characters || typeof s.characters.add !== 'function') {
    s.characters = new Set(Array.isArray(s.characters) ? s.characters : []);
  }
  s.characters.add(key);

  fs.mkdirSync(SERIES_DIR, { recursive: true });
  const fileKey = String(s.name).toLowerCase().trim().replace(/[^\w]/g, '_');
  fs.writeFileSync(
    path.join(SERIES_DIR, fileKey + '.json'),
    JSON.stringify({ id: Number(s.id), name: s.name, characters: Array.from(s.characters) }, null, 2)
  );
  saveCharacters();
  return personaje;
}

async function mioProcessSeries(sock, st, pick) {
  const gid = st.gid;
  const logJid = db.creatingLogs;
  const chars = [];
  let p = 1;
  let tp = 1;
  while (st.active && p <= tp) {
    const cmd = p === 1 ? '#ainfo ' + pick.name : '#ainfo ' + pick.name + ' page=' + p;
    const txt = await mioAsk(sock, st.logJid, 'ainfo', cmd, pick.name);
    const r = mioParseAinfo(txt);
    if (!r.chars.length) throw new Error('Respuesta inesperada de #ainfo: ' + mioClean(txt).slice(0, 80));
    chars.push.apply(chars, r.chars);
    tp = r.totalPages || 1;
    p++;
  }

  const res = { serie: pick.name, total: chars.length, existentes: 0, creados: 0, pendientes: 0, fallos: 0, truncado: false };
  if (!st.active) return res;

  const have = new Set(
    charactersCache
      .filter(function (c) { return mioNorm(c.anime) === mioNorm(pick.name); })
      .map(function (c) { return mioNorm(c.name); })
  );
  const missing = chars.filter(function (c) {
    return !have.has(mioNorm(c.name)) && !characterMap.has(String(c.name).toLowerCase());
  });
  res.existentes = chars.length - missing.length;
  const todo = missing.slice(0, MIO_CHARS_PER_SERIES);
  res.truncado = missing.length > todo.length;

  if (st.stats) {
    st.stats.total += todo.length;
  }

  try {
    await sock.sendMessage(st.logJid, {
      text:
        'ყᥲ vᥱo, ᥣᥲ sᥱrιᥱ `' +
        pick.name +
        '` tιᥱᥒᥱ `' +
        chars.length +
        '` ρᥱrsoᥒᥲjᥱs, ᥣo hᥲrᥱ.'
    });
  } catch (e) {}

  let consecutive = 0;
  for (const c of todo) {
    if (!st.active) break;

    try {

    let info;
    try {
      const txt = await mioAsk(sock, st.logJid, 'winfo', '#winfo ' + c.name, c.name);
      info = mioParseWinfo(txt);
      consecutive = 0;
    } catch (e) {
      const em = e && e.message ? e.message : '';
      if (em.indexOf('sin respuesta|') === 0) {
        res.fallos++;
        consecutive++;
        if (consecutive >= 3) throw e;
        continue;
      }
      throw e;
    }

    if (!info.nombre) { res.fallos++; continue; }

    const valor = info.valor || c.value || 100;
    const genero = info.genero || 'Desconocido';

    let tagRes = { tag: null };
    try {
      tagRes = await mioFindTag(c.name, pick.name);
    } catch (e) {
      console.log('[MIO TAG]', c.name, e && e.message);
    }
    if (!tagRes.tag && !tagRes.temporal) {
      try {
        const manualTag = mioCreateManualTag(c.name, pick.name);
        tagRes = {
          tag: manualTag.tag,
          manualTag: manualTag.manualTag,
          source: manualTag.source,
          createdManually: !manualTag.reused
        };
      } catch (e) {
        console.log('[MIO manualTag]', e && e.message);
      }
    }

    const pj = mioAddCharacter(
      pick.name,
      c.name,
      valor,
      genero,
      tagRes.tag,
      st.owner,
      tagRes.createdManually === true
    );
    if (!pj) { res.existentes++; continue; }

    res.creados++;

    if (!tagRes.tag) {
      res.pendientes++;
      try {
        await sock.sendMessage(st.logJid, {
          text:
            'Creé el personaje `' +
            pj.name +
            '`, pero no pude comprobar su tag porque el servicio está temporalmente limitado.'
        });
      } catch (e) {}
    } else if (tagRes.createdManually) {
      try {
        await sock.sendMessage(st.logJid, {
          text:
            'Bien, creé el personaje `' +
            pj.name +
            '`. No encontré su tag, pero creé el tag `' +
            tagRes.tag +
            '`.'
        });
      } catch (e) {}
    } else if (tagRes.manualTag) {
      try {
        await sock.sendMessage(st.logJid, {
          text:
            'Bien, creé el personaje `' +
            pj.name +
            '`. No encontré su tag, pero reutilicé el tag `' +
            tagRes.tag +
            '`.'
        });
      } catch (e) {}
    } else {
      try {
        await sock.sendMessage(st.logJid, {
          text:
            'ρᥱrfᥱᥴto, ᥴrᥱᥱ ᥱᥣ ρᥱrsoᥒᥲjᥱ `' +
            pj.name +
            '` ᥴorrᥱᥴtᥲmᥱᥒtᥱ ᥴoᥒ tᥲg.'
        });
      } catch (e) {}
    }

    const currentIndex = todo.indexOf(c);

    if (currentIndex !== todo.length - 1 && st.active) {
      const siguiente = todo[currentIndex + 1];
      try {
        await sock.sendMessage(st.logJid, {
          text:
            'ρᥲsᥲrᥱ ᥲᥣ sιgᥙιᥱᥒtᥱ ρᥱrsoᥒᥲjᥱ `' +
            siguiente.name +
            '`.'
        });
      } catch (e) {}
    }

    console.log(
      '[MIO] creado:',
      pj.name,
      '| serie:',
      pick.name,
      '| tag:',
      tagRes.tag || '(pendiente)'
    );

    } finally {
      if (st.stats) {
        st.stats.processed++;
        try {
          await mioActualizarBarra(sock, st, st.stats.processed, st.stats.total);
        } catch (e) {}
      }
    }
  }
  return res;
}
async function mioRunCycle(sock) {
  const st = global.__mio;
  st.stats = { processed: 0, total: 0, startTime: Date.now() };
  const gid = st.gid;
  const report = [];
  const used = new Set();
  let pool = [];
  let page = 0;
  let totalPages = 1;

  try {
    if (typeof CHARACTERS_FILE !== 'undefined' && fs.existsSync(CHARACTERS_FILE)) {
      fs.copyFileSync(CHARACTERS_FILE, CHARACTERS_FILE + '.mio_' + Date.now());
    }
  } catch (error) {
    console.error('[MIO] no se pudo crear la copia de seguridad:', error?.message || error);
  }

  const needsWork = function (s) {
    const local = charactersCache.filter(function (c) { return mioNorm(c.anime) === mioNorm(s.name); }).length;
    return local < s.count;
  };

  if (Array.isArray(st.series) && st.series.length) {
    for (let n = 0; n < st.series.length && st.active; n++) {
      const requested = st.series[n];
      const pick = { name: requested, count: 0 };
      const r = await mioProcessSeries(sock, st, pick);
      report.push(r);
    }
  } else {
    for (let n = 0; n < MIO_MAX_SERIES && st.active; n++) {
      pool = pool.filter(function (s) { return !used.has(mioNorm(s.name)) && needsWork(s); });
      while (st.active && !pool.length && page < totalPages) {
        page++;
        const txt = await mioAsk(sock, st.logJid, 'slist', page === 1 ? '#slist' : '#slist ' + page);
        const parsed = mioParseSlist(txt);
        if (!parsed.series.length) throw new Error('Respuesta inesperada de #slist: ' + mioClean(txt).slice(0, 80));
        totalPages = parsed.totalPages || 1;
        pool = parsed.series.filter(function (s) { return !used.has(mioNorm(s.name)) && needsWork(s); });
      }
      if (!st.active) return report;
      if (!pool.length) break;
      const pick = pool.splice(Math.floor(Math.random() * pool.length), 1)[0];
      used.add(mioNorm(pick.name));
      const r = await mioProcessSeries(sock, st, pick);
      report.push(r);
    }
  }

  return report;
}
async function mioRun(sock) {
  const st = global.__mio;

  if (!db.creatingLogs || typeof db.creatingLogs !== 'string' || !db.creatingLogs.endsWith('@g.us')) {
    st.active = false;
    try {
      await sock.sendMessage(st.gid, { text: '❌ Debes activar /creatinglogs on en un grupo antes de usar /mio haimiya.' });
    } catch (e) {}
    return;
  }

  st.logJid = db.creatingLogs;

  try {
    st.barraMsg = await sock.sendMessage(st.gid, {
      text: mioBarra(0) + ' ' + mioEstiloNumero(0) + '%\n\n\u00BB Escaneando series...'
    });
  } catch (e) {
    console.error('[MIO] no se pudo crear barra:', e && e.message);
  }

  const barraTimer = null;

  try {
    const report = await mioRunCycle(sock);
    st.active = false;
    if (st.stats) {
      try {
        await mioActualizarBarra(sock, st, st.stats.total, st.stats.total);
      } catch (e) {}
    }

    await mioSleep(800);

    if (Array.isArray(report) && report.length) {
      const serieNames = report.map(r => '`' + r.serie + '`').join(' > ');
      let texto = 'tᥱrmιᥒᥱ ᥣᥲ sᥱrιᥱs ' + serieNames + ' ᥴorrᥱᥴtᥲmᥱᥒtᥱ.\nRᥱsᥙᥣtᥲdos:\n\n';

      for (const r of report) {
        texto += '`' + r.serie + '` ρjs ᥴrᥱᥲdos » `' + r.creados + '` fᥲᥣᥣos `' + r.fallos + '`\n';
      }

      texto += '\n> ρᥙᥱdᥱs vᥱr ᥣos fᥲᥣᥣos ᥴoᥒ /ᥱrror. `ᥲᥙᥒ ᥒo dιsρoᥒιbᥣᥱ`.';

      try {
        await sock.sendMessage(st.gid, {
          text: '@' + String(st.owner).split('@')[0] + ' ' + texto,
          mentions: [st.owner]
        });
      } catch (e) {}
    }
  } catch (error) {
    if (error?.message === 'cancelado') {
      clearTimeout(barraTimer);
      return;
    }
    console.error('[MIO] ciclo interrumpido:', error?.stack || error);
    if (st) {
      st.active = false;
      if (st.pending) st.pending.resolve(null);
      const detail = String(error?.message || error).split('\n')[0];
      try {
        await sock.sendMessage(st.gid, { text: 'Mio Haimiya se detuvo por un error: ' + detail });
      } catch (sendError) {}
      await mioNotifyOwner(sock, '[MIO] ciclo detenido: ' + detail);
    }
  } finally {
    clearTimeout(barraTimer);
    if (st && st.barraMsg && st.barraMsg.key) {
      try {
        await sock.sendMessage(st.gid, { delete: st.barraMsg.key });
      } catch (e) {}
    }
  }
}
/* ============================================================
 * GUARDS_SYSTEM_V1_MARKER
 * /bodyguard - /guards - /robwaifu
 * ============================================================ */

const GUARD_PRICE = 10000000;
const GUARD_MAX_DEFAULT = 5;
const GUARD_MAX_XPREMIUM = 10;
const ROBWAIFU_COOLDOWN_MS = 60 * 60 * 1000;

function formatGemsCompact(value) {
  const v = Number(value) || 0;
  if (v >= 1e9) return (v / 1e9).toLocaleString('en-US', { maximumFractionDigits: 3 }) + ' M';
  if (v >= 1e6) return (v / 1e6).toLocaleString('en-US', { maximumFractionDigits: 3 }) + ' M';
  if (v >= 1e3) return (v / 1e3).toLocaleString('en-US', { maximumFractionDigits: 3 }) + ' K';
  return v.toLocaleString('en-US');
}

function ensureGuardData(user) {
  if (!user || typeof user !== 'object') return;
  if (typeof user.guards !== 'number') user.guards = 0;
  if (!user.guardStats || typeof user.guardStats !== 'object') {
    user.guardStats = { stolen: 0, protected: 0, robbed: 0, failed: 0 };
  }
  if (typeof user.guardStats.stolen !== 'number') user.guardStats.stolen = 0;
  if (typeof user.guardStats.protected !== 'number') user.guardStats.protected = 0;
  if (typeof user.guardStats.robbed !== 'number') user.guardStats.robbed = 0;
  if (typeof user.guardStats.failed !== 'number') user.guardStats.failed = 0;
  if (typeof user.lastRobWaifu !== 'number') user.lastRobWaifu = 0;
}

async function handleBodyguard(sock, msg, sender) {
  const jid = msg.key.remoteJid;
  const user = initUser(sender, msg.pushName);
  if (!user) return;
  ensureGuardData(user);

  const maxGuards = hasXPremium(user) ? GUARD_MAX_XPREMIUM : GUARD_MAX_DEFAULT;

  if (user.guards >= maxGuards) {
    return sock.sendMessage(jid, {
      text: '\u2605 Ya tienes el m\u00E1ximo de guardianes activos permitidos (`' + maxGuards + '`).'
    }, { quoted: msg });
  }

  const gems = Number(user.gems) || 0;
  if (gems < GUARD_PRICE) {
    return sock.sendMessage(jid, {
      text:
        'No tienes suficientes gemas, el precio es de `10 millones de gemas`.\n' +
        '> Gemas actuales \u00BB `' + formatGemsCompact(gems) + '`'
    }, { quoted: msg });
  }

  user.gems = gems - GUARD_PRICE;
  user.guards = (Number(user.guards) || 0) + 1;
  saveDB();

  return sock.sendMessage(jid, {
    text: '\u2605 Compraste `1` guardi\u00E1n para tu `harem`.'
  }, { quoted: msg });
}

async function handleGuards(sock, msg, sender, mentioned, quotedJid) {
  const jid = msg.key.remoteJid;

  let target = sender;
  if (mentioned && mentioned.length) target = mentioned[0];
  else if (quotedJid) target = quotedJid;

  const selfUser = initUser(sender, msg.pushName);
  if (selfUser) ensureGuardData(selfUser);

  const user = db.users?.[target];
  if (user) ensureGuardData(user);

  const guards = Number(user?.guards) || 0;
  const stats = user?.guardStats || { stolen: 0, protected: 0, robbed: 0, failed: 0 };
  const name = user?.name || String(target).split('@')[0] || 'usuario';

  const text =
    '`Guardianes ' + name + '`\n' +
    'Tienes \u00BB `' + guards + '`\n' +
    'Te han robado \u00BB `' + (stats.stolen || 0) + '`\n' +
    'Te han protegido \u00BB `' + (stats.protected || 0) + '`\n' +
    'Has robado \u00BB `' + (stats.robbed || 0) + '`';

  return sock.sendMessage(jid, { text }, { quoted: msg });
}

async function handleRobWaifu(sock, msg, args, groupId, sender) {
  const jid = msg.key.remoteJid;
  const user = initUser(sender, msg.pushName);
  if (!user) return;
  ensureGuardData(user);

  const nameQuery = args.join(' ').trim();

  if (!nameQuery) {
    return sock.sendMessage(jid, {
      text:
        '\u2730 Para robar una waifu haz `/robwaifu name`. \u2730\n' +
        '> Ejemplo 1 \u00BB `/robwaifu Mio Haimiya`\n' +
        '> Ejemplo 2 \u00BB `/robwaifu Nazuna Nanakusa`'
    }, { quoted: msg });
  }

  if (!hasXPremium(user)) {
    return sock.sendMessage(jid, {
      text: '\uD83D\uDED2 Para poder robar a una `waifu` necesitas el pase `xpremium`.'
    }, { quoted: msg });
  }

  const now = Date.now();
  const elapsed = now - (Number(user.lastRobWaifu) || 0);
  if (elapsed < ROBWAIFU_COOLDOWN_MS) {
    const remaining = ROBWAIFU_COOLDOWN_MS - elapsed;
    const mins = Math.floor(remaining / 60000);
    const secs = Math.floor((remaining % 60000) / 1000);
    return sock.sendMessage(jid, {
      text: '\u23F3 Debes esperar `' + mins + 'm ' + secs + 's` para volver a robar.'
    }, { quoted: msg });
  }

  const group = db.groups?.[groupId];
  if (!group || !group.harems) {
    return sock.sendMessage(jid, { text: '\u25C7 No hay datos en este grupo.' }, { quoted: msg });
  }

  const normalizedQuery = nameQuery.toLowerCase().trim();
  let targetOwner = null;
  let targetChar = null;
  let targetHarem = null;

  for (const [uid, harem] of Object.entries(group.harems)) {
    if (!Array.isArray(harem)) continue;
    const found =
      harem.find(c => String(c?.name || '').toLowerCase().trim() === normalizedQuery) ||
      harem.find(c => String(c?.name || '').toLowerCase().includes(normalizedQuery));
    if (found) {
      if (uid === sender) {
        return sock.sendMessage(jid, {
          text: '\u25C7 No puedes robarte tu propio personaje.'
        }, { quoted: msg });
      }
      targetOwner = uid;
      targetChar = found;
      targetHarem = harem;
      break;
    }
  }

  if (!targetChar) {
    return sock.sendMessage(jid, {
      text: '\u25C7 No se encontr\u00F3 el personaje `' + nameQuery + '` en este grupo.'
    }, { quoted: msg });
  }

  const targetUser = db.users?.[targetOwner];
  if (targetUser) ensureGuardData(targetUser);

  const targetGuards = Number(targetUser?.guards) || 0;

  if (targetGuards > 0) {
    targetUser.guards = targetGuards - 1;
    targetUser.guardStats.protected = (targetUser.guardStats.protected || 0) + 1;
    user.guardStats.failed = (user.guardStats.failed || 0) + 1;
    user.lastRobWaifu = now;
    saveDB();

    const mention = db.users?.[targetOwner]?.name || String(targetOwner).split('@')[0];
    return sock.sendMessage(jid, {
      text:
        'El robo fallo, los guardianes de `' + mention + '` te atraparon.\n' +
        '> Intentalo en 1 hora.',
      mentions: [targetOwner]
    }, { quoted: msg });
  }

  const idx = targetHarem.indexOf(targetChar);
  if (idx >= 0) targetHarem.splice(idx, 1);

  group.harems[sender] ??= [];
  if (!group.harems[sender].some(c => c.key === targetChar.key)) {
    group.harems[sender].push(targetChar);
  }

  const char = characterKeyMap.get(targetChar.key);
  if (char) {
    char.claimedBy ??= {};
    char.claimedBy[groupId] = { user: sender, time: Date.now() };
  }

  global.ownerIndex ??= {};
  global.ownerIndex[groupId] ??= {};
  if (global.ownerIndex[groupId][targetOwner]) {
    global.ownerIndex[groupId][targetOwner].delete(targetChar.key);
  }
  global.ownerIndex[groupId][sender] ??= new Set();
  global.ownerIndex[groupId][sender].add(targetChar.key);

  user.guardStats.robbed = (user.guardStats.robbed || 0) + 1;
  user.lastRobWaifu = now;
  if (targetUser) {
    targetUser.guardStats.stolen = (targetUser.guardStats.stolen || 0) + 1;
    if (Array.isArray(targetUser.harem)) {
      targetUser.harem = targetUser.harem.filter(k => k !== targetChar.key);
    }
  }
  user.harem ??= [];
  if (!user.harem.includes(targetChar.key)) {
    user.harem.push(targetChar.key);
  }

  saveCharacters();
  saveDB();

  return sock.sendMessage(jid, {
    text:
      '\u00A1 Le robaste a `' + (db.users?.[targetOwner]?.name || String(targetOwner).split('@')[0]) + '` la waifu `' + targetChar.name + '` exitosamente. !\n' +
      '> Cooldown 1 hora.'
  }, { quoted: msg });
}
export async function handleCommand(commandContext) {

  const {
    sock,
    msg,
    jid,
    sender,
    args,
    command,
    prefix,
    mentioned,
    quotedJid,
    target,
    db,
    saveDB,
    isOwner,
    isMainOwner,
    isStaffOwner,
    body
  } = commandContext;
  const isCmd =
    typeof body === 'string' &&
    typeof prefix === 'string' &&
    body.startsWith(prefix);
  const user = db.users?.[sender];

// ━━━━━━━ SISTEMA ROLTAG / INFOTAGS ━━━━━━━

/* ============================================================
 * ROLTAG / INFOTAGS
 * PROTECCION CONTRA RATE LIMIT DE DANBOORU
 * ============================================================ */

/* ============================================================
 * SISTEMA ROLTAG / INFOTAGS
 * CACHE + COLA GLOBAL + ANTI 429
 * ============================================================ */

const ROLTAG_CACHE = new Map();

const ROLTAG_INFLIGHT = new Map();

const ROLTAG_QUEUE = [];

let ROLTAG_PROCESSING = false;

let ROLTAG_COOLDOWN_UNTIL = 0;

const ROLTAG_REQUEST_DELAY = 1800;

const ROLTAG_429_COOLDOWN = 30000;

function rolTagSleep(ms) {
  return new Promise(resolve =>
    setTimeout(resolve, ms)
  );
}

function normalizarRolTag(tag) {

  return String(tag || '')
    .trim()
    .toLowerCase()
    .replace(/\s+/g, '_');

}

async function procesarColaRolTag() {

  if (ROLTAG_PROCESSING) {
    return;
  }

  ROLTAG_PROCESSING = true;

  try {

    while (ROLTAG_QUEUE.length > 0) {

      const ahora = Date.now();

      if (
        ahora <
        ROLTAG_COOLDOWN_UNTIL
      ) {

        await rolTagSleep(
          ROLTAG_COOLDOWN_UNTIL - ahora
        );

      }

      const trabajo =
        ROLTAG_QUEUE.shift();

      if (!trabajo) {
        continue;
      }

      const key =
        trabajo.key;

      try {

        const cacheado =
          ROLTAG_CACHE.get(key);

        if (cacheado) {

          trabajo.resolve(
            cacheado
          );

          continue;
        }

        const axios =
          (await import('axios')).default;

        const url =
          'https://danbooru.donmai.us/tags.json' +
          '?search[category]=4' +
          '&search[name_matches]=' +
          encodeURIComponent(
            trabajo.tag
          ) +
          '&limit=1';

        const res =
          await axios.get(
            url,
            {
              timeout: 10000,
              headers: {
                'User-Agent':
                  'BotWhatsApp/1.0 tag-validator'
              }
            }
          );

        const tags =
          Array.isArray(res.data)
            ? res.data
            : [];

        const encontrado =
          tags.find(
            t =>
              normalizarRolTag(t.name) ===
              key
          );

        let resultado;

        if (!encontrado) {

          resultado = {
            valido: false,
            temporal: false,
            razon: 'tag_no_existe'
          };

        } else {

          resultado = {
            valido: true,
            temporal: false,
            tag: encontrado.name,
            danbooru: encontrado
          };

        }

        ROLTAG_CACHE.set(
          key,
          resultado
        );

        trabajo.resolve(
          resultado
        );

      } catch (e) {

        const status =
          e?.response?.status;

        if (status === 429) {

          console.warn(
            '[ROLTAG] Danbooru 429. Cooldown de 30 segundos.'
          );

          ROLTAG_COOLDOWN_UNTIL =
            Date.now() +
            ROLTAG_429_COOLDOWN;

          trabajo.resolve({
            valido: false,
            temporal: true,
            razon: 'rate_limited'
          });

        } else {

          console.error(
            '[ROLTAG] Error consultando Danbooru:',
            e?.message || e
          );

          trabajo.resolve({
            valido: false,
            temporal: true,
            razon: 'error_danbooru'
          });

        }

      } finally {

        ROLTAG_INFLIGHT.delete(
          key
        );

        await rolTagSleep(
          ROLTAG_REQUEST_DELAY
        );

      }

    }

  } finally {

    ROLTAG_PROCESSING = false;

  }

}

function consultarDanbooruRolTag(tag) {

  const limpio =
    normalizarRolTag(tag);

  if (!limpio) {

    return Promise.resolve({
      valido: false,
      temporal: false,
      razon: 'sin_tag'
    });

  }

  const cacheado =
    ROLTAG_CACHE.get(limpio);

  if (cacheado) {

    return Promise.resolve(
      cacheado
    );

  }

  const inflight =
    ROLTAG_INFLIGHT.get(
      limpio
    );

  if (inflight) {

    return inflight;

  }

  const promise =
    new Promise(resolve => {

      ROLTAG_QUEUE.push({

        key: limpio,

        tag: limpio,

        resolve

      });

    });

  ROLTAG_INFLIGHT.set(
    limpio,
    promise
  );

  procesarColaRolTag();

  return promise;

}

async function comprobarTagCompleto(tag) {

  if (
    !tag ||
    !String(tag).trim()
  ) {

    return {
      estado: 'XB',
      razon: 'sin_tag'
    };

  }

  let danbooru;

  try {

    danbooru =
      await consultarDanbooruRolTag(
        tag
      );

  } catch (e) {

    console.error(
      '[ROLTAG] Error interno:',
      e?.message || e
    );

    return {
      estado: 'TEMP',
      razon: 'error_danbooru'
    };

  }

  if (!danbooru) {

    console.error(
      '[ROLTAG] Danbooru devolvio undefined.'
    );

    return {
      estado: 'TEMP',
      razon: 'error_danbooru'
    };

  }

  if (
    danbooru.temporal
  ) {

    return {
      estado: 'TEMP',
      razon:
        danbooru.razon ||
        'error_danbooru'
    };

  }

  if (
    !danbooru.valido
  ) {

    return {
      estado: 'XB',
      razon:
        danbooru.razon ||
        'tag_no_existe'
    };

  }

  try {

    const imagen =
      await getGelbooruImage(
        tag
      );

    if (!imagen) {

      return {
        estado: 'XB',
        razon: 'sin_imagen',
        danbooru: true
      };

    }

    return {
      estado: 'TQ',
      razon: 'ok',
      imagen,
      danbooru: true
    };

  } catch (e) {

    console.error(
      '[ROLTAG] Error obteniendo imagen:',
      e?.message || e
    );

    return {
      estado: 'XB',
      razon: 'sin_imagen',
      danbooru: true
    };

  }

}

function limpiarCacheRolTag() {

  ROLTAG_CACHE.clear();

  console.log(
    '[ROLTAG] Cache limpiada.'
  );

}

async function handleRoltag(
  sock,
  msg,
  args
) {

  const nombre =
    args.join(' ').trim();

  if (!nombre) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'\u2726 ROLTAG\n\n' +
'\u25c7 Uso \u00bb /roltag Nombre\n\n' +
'\u25c7 Ejemplo \u00bb /roltag Mavis'
      },
      {
        quoted: msg
      }
    );

  }

  const normalizar =
    texto =>
      String(texto || '')
        .normalize('NFD')
        .replace(/[\\u0300-\\u036f]/g, '')
        .toLowerCase()
        .trim();

  const objetivo =
    normalizar(nombre);

  const personaje =
    charactersCache.find(
      char =>
        normalizar(char.name) ===
        objetivo
    );

  if (!personaje) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
'\u2726 ROLTAG\n\n' +
'\u25c7 Personaje \u00bb ' + nombre + '\n\n' +
'\u25c6 Estado \u00bb XB\n\n' +
'\u25c7 Motivo \u00bb Personaje no encontrado.'
      },
      {
        quoted: msg
      }
    );

  }

  const resultado =
    await comprobarTagCompleto(
      personaje.tag
    );

  // Un personaje es inválido solo cuando no tiene imagen local ni su tag
  // devuelve una imagen. Este caso se informa de forma directa para poder
  // localizarlo y corregirlo con su ID.
  const localImageCount =
    getCharacterImages(personaje.key).length;
  const hasUsableImage =
    localImageCount > 0 ||
    resultado.estado === 'TQ';

  if (!hasUsableImage) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`**error:** el personaje no tiene imagenes disponibles

**nombre:** ${personaje.name}
**id:** ${personaje.id}
**tag:** ${personaje.tag || 'sin tag'}`
      },
      { quoted: msg }
    );
  }

  let motivo = '';

  if (resultado.razon === 'sin_tag') {

    motivo = 'sin tag';

  } else if (
    resultado.razon === 'tag_no_existe'
  ) {

    motivo = 'el tag no existe en danbooru';

  } else if (
    resultado.razon === 'sin_imagen'
  ) {

    motivo = 'el personaje no tiene una imagen disponible por su tag de danbooru';

  } else if (
    resultado.razon === 'error_danbooru'
  ) {

    motivo = 'no se pudo comprobar danbooru';

  }

  // ========================================================
  // PENALIZACION
  //
  // SOLAMENTE cuando comprobarTagCompleto devuelve
  // razon === "sin_imagen".
  //
  // Se descuentan 100000 Status.
  // Nunca se permite quedar por debajo de 0.
  // ========================================================

  let penalizacion = 0;
  let statusActual = null;

  if (
    resultado.razon === 'sin_imagen'
  ) {

    const profile =
      getStaffProfile(
        personaje.creator
      );

    const statusAntes =
      Number(
        profile.status
      ) || 0;

    penalizacion =
      Math.min(
        100000,
        Math.max(
          0,
          statusAntes
        )
      );

    profile.status =
      Math.max(
        0,
        statusAntes - penalizacion
      );

    statusActual =
      profile.status;

    saveDB();

  }

  let texto =
'**roltag**\n\n' +
'**nombre:** ' +
personaje.name +
'\n' +
'**id:** ' +
personaje.id +
'\n' +
'**anime:** ' +
(personaje.anime || 'desconocido') +
'\n' +
'**tag:** ' +
(personaje.tag || 'sin tag') +
'\n\n' +
'**estado:** ' +
String(resultado.estado || '').toLowerCase();

  if (motivo) {

    texto +=
      '\n**motivo:** ' +
      motivo;

  }

  if (penalizacion > 0) {

    texto +=
      '\n\n**penalización:** -' +
      penalizacion +
      ' status';

    texto +=
      '\n**status actual:** ' +
      statusActual;

  }

  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text: texto
    },
    {
      quoted: msg
    }
  );

}


// ━━━━━━━ /infotags ━━━━━━━

async function handleInfotags(
  sock,
  msg,
  sender,
  targetSender = null
) {

  const objetivo =
    targetSender || sender;

  if (objetivo !== sender) {

    const esSecondaryOwner =
      Array.isArray(SECONDARY_OWNERS) &&
      SECONDARY_OWNERS.includes(objetivo);

    const esStaff =
      typeof isStaff === 'function'
        ? await isStaff(objetivo)
        : (
            Array.isArray(db.staff) &&
            db.staff.includes(objetivo)
          );

    if (!esSecondaryOwner && !esStaff) {

      return sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
`☆† INFORME DE TAGS

•‡ No puedes consultar los tags de este usuario.

•‡ Solo se permite consultar a usuarios que sean *Secondary Owner* o *Staff*.`
        },
        {
          quoted: msg
        }
      );
    }
  }

  const personajes =
    charactersCache.filter(
      char =>
        char.creator === objetivo
    );

  const nombreObjetivo =
    db.users?.[objetivo]?.name ||
    objetivo?.split('@')[0] ||
    'Desconocido';

  if (!personajes.length) {

    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`☆† INFORME DE TAGS

•‡ Usuario » @${nombreObjetivo}

•‡ Total » 0
•‡ TQ » 0
•‡ XB » 0
•‡ TEMP » 0

•‡ No tiene personajes creados.`,
        mentions: [objetivo]
      },
      {
        quoted: msg
      }
    );
  }

  let tq = 0;
  let xb = 0;
  let temp = 0;

  const afectados = [];
  const temporales = [];

  for (const personaje of personajes) {

    const resultado =
      await comprobarTagCompleto(
        personaje.tag
      );

    if (resultado.estado === 'TQ') {

      tq++;

    } else if (resultado.estado === 'TEMP') {

      /*
       * TEMP no es XB.
       */
      temp++;

      let motivo = 'Danbooru temporalmente limitado';

      if (
        resultado.razon === 'rate_limited'
      ) {
        motivo = 'rate limit de Danbooru';
      } else if (
        resultado.razon === 'error_danbooru'
      ) {
        motivo = 'error temporal de Danbooru';
      }

      temporales.push(
        `▪ª ${personaje.name} ⬝ ${motivo}`
      );

    } else {

      xb++;

      let motivo = '';

      if (
        resultado.razon === 'sin_tag'
      ) {

        motivo = 'sin tag';

      } else if (
        resultado.razon === 'tag_no_existe'
      ) {

        motivo = 'tag inexistente';

      } else if (
        resultado.razon === 'sin_imagen'
      ) {

        motivo = 'sin imagen';

      } else {

        motivo = 'error Danbooru';
      }

      afectados.push(
        `▪ª ${personaje.name} ⬝ ${motivo}`
      );
    }
  }

  let texto =
`☆† INFORME DE TAGS

•‡ Usuario » @${nombreObjetivo}

•‡ Total » ${personajes.length}
•‡ TQ » ${tq}
•‡ XB » ${xb}
•‡ TEMP » ${temp}`;

  if (afectados.length) {

    texto +=
`\n\n•† TAGS XB

${afectados.join('\n')}`;

  }

  if (temporales.length) {

    texto +=
`\n\n•† TAGS TEMPORALES

${temporales.join('\n')}`;

  }

  return sock.sendMessage(
    msg.key.remoteJid,
    {
      text: texto,
      mentions: [objetivo]
    },
    {
      quoted: msg
    }
  );
}
function getInfotagsTarget(
  msg,
  sender
) {

  /*
   * 1. Primero revisamos una mención:
   *
   * /infotags @usuario
   */

  const mentioned =
    msg.message?.extendedTextMessage
      ?.contextInfo?.mentionedJid ||
    msg.message?.conversation
      ?.contextInfo?.mentionedJid ||
    [];


  if (
    Array.isArray(mentioned) &&
    mentioned.length > 0
  ) {

    return mentioned[0];

  }


  /*
   * 2. Si no hay mención, revisamos
   *    si el comando responde a un mensaje.
   */

  const contextInfo =
    msg.message?.extendedTextMessage
      ?.contextInfo;


  const quotedParticipant =
    contextInfo?.participant ||
    contextInfo?.quotedMessage
      ?.extendedTextMessage
      ?.contextInfo
      ?.participant ||
    contextInfo?.quotedMessage
      ?.conversation
      ?.contextInfo
      ?.participant;


  if (quotedParticipant) {

    return quotedParticipant;

  }


  /*
   * 3. Sin mención ni respuesta:
   *    consulta al propio usuario.
   */

  return sender;

}async function startSubBot(full) {
  console.log(" startSubBot vacío ejecutado:", full);
  return null;
}

  if (isCmd && ['luck', 'buyluck', 'luckshop'].includes(command)) {
    if (!hasPremium(user)) {
      return sock.sendMessage(jid, {
        text: '◇ /luck, /buyluck y /luckshop son exclusivos. Compra XPremium o BPremium con /xpremium o /bpremium para usarlos.'
      }, { quoted: msg });
    }
  }

  if (isCmd && command === 'song' && !hasXPremium(user)) {
    return sock.sendMessage(jid, {
      text: '◇ /song es exclusivo de XPremium. Compra XPremium con /xpremium para jugar.'
    }, { quoted: msg });
  }

  switch (command) {

  case 'mio': {

    if (!isOwner) {
      break;
    }

    const subcommand = String(args[0] || '').toLowerCase();
    const option = String(args[1] || '').toLowerCase();

    if (subcommand !== 'haimiya') {
      await sock.sendMessage(
        jid,
        {
          text: 'Uso: /mio haimiya on | /mio haimiya off | /mio haimiya nombre / nombre'
        },
        { quoted: msg }
      );
      break;
    }

    if (option === 'off') {
      const state = global.__mio;
      if (!state || !state.active) {
        await sock.sendMessage(
          jid,
          { text: 'Mio Haimiya no estaba activo.' },
          { quoted: msg }
        );
        break;
      }

      state.active = false;
      if (state.pending) state.pending.resolve(null);
      await sock.sendMessage(
        jid,
        { text: 'Mio Haimiya detenido.' },
        { quoted: msg }
      );
      break;
    }

    if (!String(jid).endsWith('@g.us')) {
      await sock.sendMessage(
        jid,
        { text: 'Actívalo dentro del grupo donde está el bot externo.' },
        { quoted: msg }
      );
      break;
    }

    if (global.__mio && global.__mio.active) {
      await sock.sendMessage(
        jid,
        {
          text:
            'Mio Haimiya ya está activo' +
            (global.__mio.gid === jid
              ? ' en este grupo.'
              : ' en otro grupo. Usa /mio haimiya off primero.')
        },
        { quoted: msg }
      );
      break;
    }

    const rawSeries = args.slice(1).join(' ').trim();
    let requestedSeries = null;

    if (rawSeries && option !== 'on') {
      const seenSeries = new Set();
      requestedSeries = rawSeries
        .split('/')
        .map(series => series.trim())
        .filter(Boolean)
        .filter(series => {
          const key = mioNorm(series);
          if (seenSeries.has(key)) return false;
          seenSeries.add(key);
          return true;
        });

      if (!requestedSeries.length) {
        await sock.sendMessage(
          jid,
          { text: 'Debes indicar al menos una serie.' },
          { quoted: msg }
        );
        break;
      }

      const names = requestedSeries.length === 1
        ? '`' + requestedSeries[0] + '`'
        : requestedSeries.map(series => '`' + series + '`').join(' - ');
      const verb = requestedSeries.length === 1
        ? 'hᥲrᥱ ᥣᥲ sᥱrιᥱ '
        : 'hᥲrᥱ ᥣᥲs sᥱrιᥱs ';

      await sock.sendMessage(
        jid,
        {
          text:
            'ᥱᥒtᥱᥒdιdo, ' +
            verb +
            names +
            ' vᥱrιfιᥴᥲrᥱ sᥙs ρᥱrsoᥒᥲjᥱs.'
        },
        { quoted: msg }
      );
    }

    const state = {
      active: true,
      gid: jid,
      owner: sender,
      pending: null,
      lastCommandAt: 0,
      series: requestedSeries
    };

    global.__mio = state;
    void mioRun(sock);
    break;
  }

  case 'pendientes': {
    if (!isOwner) {
      await sock.sendMessage(
        jid,
        { text: 'Solo los owners pueden usar este comando.' },
        { quoted: msg }
      );
      break;
    }

    const pendingCharacters = charactersCache.filter(character =>
      character.pendienteTag && !(character.tag && String(character.tag).trim())
    );
    if (!pendingCharacters.length) {
      await sock.sendMessage(
        jid,
        { text: 'No hay personajes pendientes de tag.' },
        { quoted: msg }
      );
      break;
    }

    let text = '•­─【 PENDIENTES 〕─◆\nTotal: ' + pendingCharacters.length + '\n\n';
    for (const character of pendingCharacters) {
      const line = '» ' + character.name + ' (' + (character.anime || 'Sin serie') + ')\n';
      if ((text + line).length > 3000) {
        await sock.sendMessage(jid, { text });
        text = '';
      }
      text += line;
    }
    if (text) await sock.sendMessage(jid, { text });
    break;
  }

  case 'pendientes2': {
    if (!isOwner) {
      await sock.sendMessage(
        jid,
        { text: 'Solo los owners pueden usar este comando.' },
        { quoted: msg }
      );
      break;
    }

    const charactersWithoutImages = charactersCache.filter(character =>
      Number.isFinite(Number(character.mioTagCreatedAt)) &&
      Number(character.mioTagCreatedAt) > 0 &&
      String(character.tag || '').trim()
    );
    const missingImages = [];
    for (const character of charactersWithoutImages) {
      try {
        if (!await mioTagHasOnlineImage(character.tag)) missingImages.push(character);
      } catch (error) {
        console.error(
          '[PENDIENTES2] No se pudo comprobar la imagen de',
          character.name,
          error?.message || error
        );
        missingImages.push(character);
      }
    }

    if (!missingImages.length) {
      await sock.sendMessage(
        jid,
        {
          text: charactersWithoutImages.length
            ? 'Todos los tags creados por Mio Haimiya devuelven una imagen.'
            : 'No hay tags creados por Mio Haimiya para comprobar.'
        },
        { quoted: msg }
      );
      break;
    }

    let text =
      '•­─【 PENDIENTES DE IMAGEN 〕─◆\nTotal: ' +
      missingImages.length +
      '\n\n';

    for (const character of missingImages) {
      const line =
        '» ' + character.name +
        ' (' + (character.anime || 'Sin serie') +
        ') — tag: ' + character.tag + '\n';
      if ((text + line).length > 3000) {
        await sock.sendMessage(jid, { text });
        text = '';
      }
      text += line;
    }
    if (text) await sock.sendMessage(jid, { text });
    break;
  }

  case 'roltag': {

    await handleRoltag(
      sock,
      msg,
      args
    );

    break;
  }

  case 'infotags': {

    const objetivoInfotags =
      getInfotagsTarget(
        msg,
        sender
      );

    await handleInfotags(
      sock,
      msg,
      sender,
      objetivoInfotags
    );

    break;
  }



case 'adds': {

  /*
   * ==========================================================
   * /ADDS
   * Crear solamente una serie.
   *
   * Permitido:
   * - Owner principal
   * - Secondary owners
   *
   * Usuarios normales:
   * - Ignorados completamente.
   * ==========================================================
   */

  const senderAddS =
    sender;

  const esOwnerPrincipalAddS =
    typeof isOwner === "boolean"
      ? isOwner
      : false;

  const esSecondaryAddS =
    Array.isArray(db.secondaryOwners) &&
    db.secondaryOwners.includes(
      senderAddS
    );

  if (
    !esOwnerPrincipalAddS &&
    !esSecondaryAddS
  ) {

    /*
     * Usuario normal:
     * no responder absolutamente nada.
     */
    break;
  }

  const textoSerieAddS =
    String(body || '')
      .trim()
.replace(/^\/adds(?:\s+|$)/i, '')
      .trim();

  if (!textoSerieAddS) {

    await sock.sendMessage(
      jid,
      {
        text:
          "◇ Falta el nombre de la serie.\\n" +
          "└─ Uso: /adds [serie]"
      },
      {
        quoted: msg
      }
    );

    break;
  }

  /*
   * Nombre exacto proporcionado por el owner.
   */
  const nombreSerieAddS =
    textoSerieAddS
      .replace(/\s+/g, " ")
      .trim();

  const serieKeyAddS =
    nombreSerieAddS
      .toLowerCase()
      .trim();

  /*
   * Verificar si ya existe en cache.
   */
  let serieAddS =
    seriesCache.get(
      serieKeyAddS
    );

  if (serieAddS) {

    await sock.sendMessage(
      jid,
      {
        text:
          "⚠️ La serie ya existe.\\n\\n" +
          "◇ Serie: " +
          serieAddS.name +
          "\\n" +
          "◇ ID: " +
          serieAddS.id +
          "\\n" +
          "□ Personajes: " +
          (
            serieAddS.characters
              ? serieAddS.characters.size
              : 0
          )
      },
      {
        quoted: msg
      }
    );

    break;
  }

  /*
   * ==========================================================
   * Generar ID permanente.
   * ==========================================================
   */

  const idsSeriesAddS =
    [...seriesCache.values()]
      .map(
        s =>
          Number(s.id)
      )
      .filter(
        n =>
          Number.isInteger(n) &&
          n > 0
      );

  const nuevoIdSerieAddS =
    idsSeriesAddS.length
      ? Math.max(...idsSeriesAddS) + 1
      : 1;

  /*
   * ==========================================================
   * Crear serie vacía.
   * ==========================================================
   */

  serieAddS = {
    id:
      nuevoIdSerieAddS,

    name:
      nombreSerieAddS,
    characters:
      new Set(),

    owner:
      senderAddS
  };

  /*
   * Registrar en cache.
   */
  seriesCache.set(
    serieKeyAddS,
    serieAddS
  );

  /*
   * ==========================================================
   * Crear directorio de series si no existe.
   * ==========================================================
   */

  if (
    !fs.existsSync(
      SERIES_DIR
    )
  ) {

    fs.mkdirSync(
      SERIES_DIR,
      {
        recursive: true
      }
    );

  }

  /*
   * ==========================================================
   * Nombre del archivo.
   * Mismo formato utilizado por ADDP.
   * ==========================================================
   */

  const serieFileNameAddS =
    serieKeyAddS
      .replace(/[^\w]/g, "_");

  const serieFileAddS =
    path.join(
      SERIES_DIR,
      serieFileNameAddS + ".json"
    );

  /*
   * ==========================================================
   * Guardar serie vacía.
   * ==========================================================
   */

  fs.writeFileSync(
    serieFileAddS,
    JSON.stringify(
      {
        id:
          Number(
            serieAddS.id
          ),

        name:
          serieAddS.name,
        owner:
          serieAddS.owner,
        characters:
          []
      },
      null,
      2
    )
  );

  /*
   * Persistir DB por seguridad.
   */
  saveDB();

  console.log(
    "🆕 ADDS: serie creada:"
  );

  console.log(
    "   Nombre:",
    serieAddS.name
  );

  console.log(
    "   ID:",
    serieAddS.id
  );

  console.log(
    "   Archivo:",
    serieFileAddS
  );

  await sock.sendMessage(
    jid,
    {
      text:
        `•­─【 ADD 〕
│ ♢ ${serieAddS.name}
│ ├ ID: ${serieAddS.id}
│ └ Personajes: 0
•°────────`
    },
    {
      quoted: msg
    }
  );

  break;
}

case 'deladdp':
  await handleDelAddp(sock, msg, args, jid, sender, isOwner);
  break;

case 'addis':
  await handleAddIs(
    sock,
    msg,
    args,
    sender,
    isOwner
  );
  break;

case 'addp':

 console.log("🔥🔥🔥 CASE ADDP DETECTADO 🔥🔥🔥");
 console.log("ARGS ADDP:", args);
 console.log("JID ADDP:", jid);
 console.log("SENDER ADDP:", sender);

 {

 const id =
  Number(args[0]);

 let serie;

 for (
  const s of seriesCache.values()
 ) {

  if (
   Number(s.id) === id
  ) {

   serie = s;
   break;

  }

 }

 if (!serie) {

  return sock.sendMessage(
   jid,
   {
    text:
     " Serie inválida."
   },
   {
    quoted: msg
   }
  );

 }



 /*
  * ============================================================
  * ADDP - BLOQUEO GLOBAL
  * ============================================================
  *
  * Solo puede existir UNA cola ADDP activa en todo el bot.
  *
  * Si cualquier usuario/staff ya tiene un ADDP en proceso,
  * otro /addp será rechazado hasta que la cola termine.
  */


 const addpActivo = Object.entries(
  db.addpQueue || {}
 ).find(
  ([, cola]) => {

   if (
    !cola ||
    cola.iniciadoPorAddp !== true ||
    cola.addpEstado !== "activa"
   ) {
    return false;
   }

   const personajes =
    Array.isArray(cola.personajes)
      ? cola.personajes
      : [];

   const index =
    Number(cola.index || 0);

   if (
    index >= personajes.length
   ) {
    return false;
   }

   return true;
  }
 );


 if (addpActivo) {

  const [addpJid, colaActiva] =
   addpActivo;

  const personajeActivo =
   colaActiva.personajes?.[
    Number(colaActiva.index || 0)
   ];

  const nombreActivo =
   String(
    personajeActivo?.nombre || ""
   ).trim();

  console.log(
   "🛑 ADDP BLOQUEADO: ya existe una cola activa:",
   addpJid,
   "| personaje:",
   nombreActivo || "desconocido",
   "| usuario:",
   colaActiva.user || "desconocido"
  );

  return sock.sendMessage(
   jid,
   {
    text:
     "❌ Ya existe un /addp activo.\n\n" +
     "• Personaje actual: " +
     (nombreActivo || "desconocido") +
     "\n\n" +
     "⏳ Espera a que termine la cola actual."
   },
   {
    quoted: msg
   }
  );
 }

 const textoCompleto =
  body
    .replace(/^\/addp\s+\d+\s*/i, '')
    .trim();



 const personajesIniciales = [];

 /*
  * ============================================================
  * ADDP -> PARSER DOBLE
  * ============================================================
  *
  * FORMATO MANUAL:
  *
  *   nombre > tag
  *   nombre = tag
  *
  * FORMATO AUTOMÁTICO:
  *
  *   nombre
  *
  * Cuando no se proporciona un tag, ADDP consulta Danbooru
  * internamente y obtiene el mejor tag de personaje.
  *
  * El resto del sistema ADDP continúa utilizando exactamente
  * { nombre, tag }, por lo que no se modifica el scheduler,
  * watchdog, #winfo, duplicados ni creación.
  */

 const lineas =
  textoCompleto
    .split(/\r?\n/)
    .map(x => x.trim())
    .filter(Boolean);


 /*
  * ============================================================
  * BUSCADOR INTERNO ADDP
  * ============================================================
  *
  * Misma lógica base utilizada por /searchg.
  *
  * Devuelve solamente el nombre del tag.
  */

 async function buscarTagAutomaticoAddP(
  nombre,
  anime
 ) {

  const normalizar =
   text =>
    String(text || "")
     .toLowerCase()
     .replace(/_/g, " ")
     .replace(/[^a-z0-9 ]/g, "")
     .trim();

  const target =
   normalizar(nombre);

  if (!target) {
   return null;
  }

  let tags = [];

  try {

   const axios =
    (await import("axios")).default;

   /*
    * Primero buscamos por el nombre.
    * Después por el anime, igual que searchg.
    */
   const queries = [
    nombre.replace(/\s+/g, "_"),
    nombre,
    anime
   ];

   for (
    const q of queries
   ) {

    if (!q) continue;

    const url =
     "https://danbooru.donmai.us/tags.json" +
     "?search[category]=4" +
     "&search[name_matches]=*" +
     encodeURIComponent(q) +
     "*" +
     "&limit=100";

    try {

     const res =
      await axios.get(
       url,
       {
        timeout: 15000
       }
      );

     if (
      Array.isArray(
       res.data
      )
     ) {

      tags.push(
       ...res.data
      );

     }

    } catch (error) {

     console.error(
      "⚠️ ADDP SEARCH:",
      q,
      error?.message || error
     );

    }

   }

   /*
    * Eliminar duplicados.
    */
   tags =
    [
     ...new Map(
      tags.map(
       t => [
        t.name,
        t
       ]
      )
     ).values()
    ];

  } catch (error) {

   console.error(
    "❌ ADDP SEARCHG INTERNO:",
    error
   );

   return null;
  }

  if (!tags.length) {

   console.log(
    "❌ ADDP AUTOTAG: sin coincidencias:",
    nombre,
    "| serie:",
    anime
   );

   return null;
  }

  /*
   * ============================================================
   * SCORE
   * ============================================================
   *
   * Mantiene el algoritmo de /searchg:
   *
   * exacto       +20000
   * contiene      +8000
   * comienza      +5000
   * variantes    -10000
   */

  function similarity(
   value
  ) {

   const originalTag =
    String(
     value || ""
    ).toLowerCase();

   const valueNormalized =
    normalizar(
     value
    );

   let score = 0;

   /*
    * Coincidencia exacta.
    */
   if (
    valueNormalized ===
    target
   ) {

    score += 20000;

   }

   /*
    * Nombre contenido.
    */
   if (
    valueNormalized.includes(
     target
    )
   ) {

    score += 8000;

   }

   /*
    * Tag comienza por el nombre.
    */
   if (
    valueNormalized.startsWith(
     target
    )
   ) {

    score += 5000;

   }

   /*
    * Penalizar variantes.
    */
   if (
    /(costume|outfit|alternate|swimsuit|cosplay|3rd|2nd)/i
     .test(
      originalTag
     )
   ) {

    score -= 10000;

   }

   /*
    * Si el nombre del anime aparece en el tag,
    * dar una pequeña prioridad adicional.
    *
    * No se usa como requisito porque muchos tags
    * de personajes de Danbooru no contienen el anime.
    */
   const animeNormalized =
    normalizar(
     anime
    );

   if (
    animeNormalized &&
    valueNormalized.includes(
     animeNormalized
    )
   ) {

    score += 1000;

   }

   return score;
  }

  tags.sort(
   (a, b) =>
    similarity(b.name) -
    similarity(a.name)
  );

  const best =
   tags[0];

  if (!best) {
   return null;
  }

  /*
   * ============================================================
   * SEGURIDAD
   * ============================================================
   *
   * No aceptar resultados que no tengan ninguna relación
   * con el nombre solicitado.
   */
  const bestNormalized =
   normalizar(
    best.name
   );

  const tieneRelacion =
   bestNormalized === target ||
   bestNormalized.includes(target) ||
   bestNormalized.startsWith(target);

  if (!tieneRelacion) {

   console.log(
    "⚠️ ADDP AUTOTAG: resultado rechazado:",
    best.name,
    "| solicitado:",
    nombre
   );

   return null;
  }

  console.log(
   "🔎 ADDP AUTOTAG:",
   nombre,
   "->",
   best.name,
   "| serie:",
   anime
  );

  return best.name;
 }


 /*
  * ============================================================
  * CONSTRUIR COLA
  * ============================================================
  */

 for (
  const linea of lineas
 ) {

  let separador = "";

  /*
   * PRIMERO: modo manual.
   */
  if (
   linea.includes(">")
  ) {

   separador = ">";

  } else if (
   linea.includes("=")
  ) {

   separador = "=";

  }

  /*
   * ============================================================
   * MODO MANUAL
   * ============================================================
   */

  if (separador) {

   const posicion =
    linea.indexOf(
     separador
    );

   const nombre =
    linea
     .slice(
      0,
      posicion
     )
     .trim();

   const tag =
    linea
     .slice(
      posicion + 1
     )
     .trim();

   if (
    !nombre ||
    !tag
   ) {

    console.log(
     " ADDP: lï¿½nea manual inválida:",
     linea
    );

    continue;
   }

   /*
    * ADDP: eliminar ID de serie residual del nombre.
    *
    * Ejemplo:
    *   "124 ¿s N¿dt" -> "¿s N¿dt"
    *
    * Solo elimina números al principio del nombre.
    * No modifica números que formen parte real del nombre.
    */
   const nombreLimpioAddP =
    String(nombre || '')
     .replace(/^\d+\s+/, '')
     .trim();

   if (!nombreLimpioAddP) {
    console.log(
     " ADDP: nombre vacío después de limpiar ID:",
     nombre
    );
    continue;
   }

   personajesIniciales.push({
    nombre: nombreLimpioAddP,
    tag
   });

   console.log(
    "✍️ ADDP MANUAL:",
    nombre,
    "->",
    tag
   );

   continue;
  }


  /*
   * ============================================================
   * MODO AUTOMÁTICO
   * ============================================================
   *
   * No hay > ni =.
   *
   * El texto completo es el nombre del personaje.
   */

  const nombre =
   linea.trim();

  if (!nombre) {
   continue;
  }

  const animeAddP =
   String(
    serie?.name ||
    ""
   ).trim();

  console.log(
   "◆ ADDP AUTOTAG: buscando:",
   nombre,
   "| serie:",
   animeAddP
  );

  const tagAutomatico =
   await buscarTagAutomaticoAddP(
    nombre,
    animeAddP
   );

  if (!tagAutomatico) {

   console.log(
    "❌ ADDP AUTOTAG: no se encontró tag:",
    nombre
   );

   /*
    * No meter un personaje sin tag en la cola.
    */
   continue;
  }

  personajesIniciales.push({
   nombre,
   tag:
    tagAutomatico
  });

  console.log(
   "✓ ADDP AUTOTAG:",
   nombre,
   "->",
   tagAutomatico
  );

 }
 db.addpQueue[jid] = {
  addpEstado:
   "activa",
  iniciadoPorAddp: true,
    origenAddp: "/addp",

  sourceJid:
   jid,

  targetJid:

   (
    typeof db.creatingLogs ===
    "string" &&

    db.creatingLogs.endsWith(
     "@g.us"
    )
   )

   ? db.creatingLogs

   : jid,

  serie: {
   id:
    serie.id,

   name:
    serie.name,

   characters:
    serie.characters
  },

  personajes:
   personajesIniciales,

    /*
     * ADDP ETA REAL V2
     */
    addpTiempos: [],
    addpUltimoTiempo: 0,
    addpPersonajeInicio: null,

  /*
   * Resultados acumulados de ADDP.
   *
   * No se envía un mensaje por personaje.
   * Todos los resultados se muestran al finalizar.
   */
  resultados:
   [],

  index:
   0,

  user:
   sender,

  esperando:
   false,

  timer:
   null,

  messageId:
   null,

  /*
   * ========================================================
   * ADDP PROGRESO REAL V4
   * Referencia al mensaje ï¿½nico que serï¿½ editado.
   * ========================================================
   */
  progresoMessageId:
   null,

  progresoMessageKey:
   null,

  progresoChatJid:
   jid,

  progresoTotal:
   personajesIniciales.length,

  progresoProcesados:
   0

 };


 if (
  personajesIniciales.length > 0
 ) {

  /*
   * ========================================================
   * ADDP PROGRESO REAL V4
   * Crear el mensaje UNA SOLA VEZ y guardar su ID.
   * ========================================================
   */
  const progresoInicialAddP =
   await sock.sendMessage(
    jid,
    {
     text:

      "◇ Serie: " +
      serie.name +

      "\n\n□ Personajes en cola: " +
      personajesIniciales.length +

      "\n\n⌛ Progreso: 0/" +
      personajesIniciales.length +

      "\n\n⌛ Calculando tiempo estimado..."
    },
    {
     quoted: msg
    }
   );

  console.log(
   "🔎 ADDP V5 DEBUG sendMessage:",
   progresoInicialAddP
  );

  console.log(
   "🔎 ADDP V5 DEBUG key:",
   progresoInicialAddP?.key
  );

  console.log(
   "🔎 ADDP V5 DEBUG id:",
   progresoInicialAddP?.key?.id
  );

  /*
   * Guardar la referencia del mensaje para poder editarlo.
   */
  if (
   progresoInicialAddP &&
   progresoInicialAddP.key &&
   progresoInicialAddP.key.id
  ) {

   const colaProgreso =
    db.addpQueue?.[jid];

   if (colaProgreso) {

    colaProgreso.progresoMessageId =
     progresoInicialAddP.key.id;

    colaProgreso.progresoMessageKey = {
     remoteJid:
      progresoInicialAddP.key.remoteJid || jid,

     fromMe:
      progresoInicialAddP.key.fromMe === true,

     id:
      progresoInicialAddP.key.id
    };

    colaProgreso.progresoChatJid =
     jid;

    colaProgreso.progresoTotal =
     personajesIniciales.length;

    colaProgreso.progresoProcesados =
     0;

    saveDB();

    console.log(
     "• ADDP PROGRESO V4: mensaje guardado:",
     progresoInicialAddP.key.id
    );

   }

  } else {

   console.log(
    "⚠️ ADDP PROGRESO V4: no se pudo obtener ID del mensaje inicial."
   );

  }


  console.log(
  "→ ADDP iniciando cola:",
  jid
);


console.log("========================================");
console.log("→ ADDP INICIO DIRECTO");
console.log("📍 Cola:", jid);
console.log("📍 Destino:", db.addpQueue?.[jid]?.targetJid);
console.log(
  "👤 Personaje:",
  db.addpQueue?.[jid]?.personajes?.[
    Number(db.addpQueue?.[jid]?.index || 0)
  ]?.nombre
);
console.log("→ LLAMANDO enviarSiguienteAddP()");
console.log("========================================");

try {

  await enviarSiguienteAddP(
    sock,
    jid
  );

  console.log(
    "✓ ADDP: enviarSiguienteAddP() terminó:",
    jid
  );

} catch (error) {

  console.error(
    "❌ ADDP: error en enviarSiguienteAddP():",
    error
  );

}


 } else {

  await sock.sendMessage(
   jid,
   {
    text:

     "◇ Serie: " +
     serie.name +

     "\n\nEnvía:" +

     "\nNombre > tag" +

     "\n\nPuedes agregar varios usando" +

     "\nsaltos de línea."
   },
   {
    quoted: msg
   }
  );

 }


 break;

}



case 'reanudaraddp': {

  console.log(
    "→ REANUDAR ADDP solicitado por:",
    sender
  );

  /*
   * Buscar todas las colas activas.
   */

  const entradas =
    Object.entries(
      db.addpQueue || {}
    );

  if (!entradas.length) {

    await sock.sendMessage(
      jid,
      {
        text:
          "❌ No hay ninguna cola /addp activa."
      },
      {
        quoted: msg
      }
    );

    break;
  }

  /*
   * Buscar la primera cola válida.
   */

  let encontrado = null;

  for (
    const [queueJid, cola] of entradas
  ) {

    if (
      cola &&
      Array.isArray(cola.personajes) &&
      cola.index < cola.personajes.length
    ) {

      encontrado = {
        queueJid,
        cola
      };

      break;
    }
  }

  if (!encontrado) {

    await sock.sendMessage(
      jid,
      {
        text:
          "❌ Se encontraron colas, pero ninguna tiene personajes pendientes."
      },
      {
        quoted: msg
      }
    );

    break;
  }

  const queueJid =
    encontrado.queueJid;

  const data =
    encontrado.cola;

  const actual =
    data.personajes?.[
      Number(data.index || 0)
    ];

  console.log(
    "📍 ADDP REANUDAR:",
    queueJid
  );

  console.log(
    "📍 INDEX:",
    data.index
  );

  console.log(
    "📍 PERSONAJE:",
    actual?.nombre
  );

  /*
   * ==========================================================
   * LIMPIAR SOLAMENTE LOCKS
   * ==========================================================
   *
   * NO modificar:
   *
   * - personajes
   * - index
   * - resultados
   * - serie
   * - usuario
   */

  data.esperando = false;
  data.addpBusy = false;
  data.addpTransition = false;
  data.addpTransitionOwner = null;

  /*
   * Compatibilidad con la implementación anterior.
   */

  data.transition = false;

  if (data.timer) {
    clearTimeout(data.timer);
    data.timer = null;
  }

  saveDB();

  console.log(
    "◇ ADDP REANUDAR: locks liberados."
  );

  /*
   * Confirmación al usuario.
   */

  await sock.sendMessage(
    jid,
    {
      text:
        "▶️ Reanudando /addp...\n\n" +
        "👤 Personaje: " +
        (actual?.nombre || "desconocido") +
        "\n" +
        "📍 Posici¿n: " +
        (Number(data.index || 0) + 1) +
        "/" +
        data.personajes.length
    },
    {
      quoted: msg
    }
  );

  /*
   * ==========================================================
   * INICIAR EL SCHEDULER
   * ==========================================================
   */

  await programarSiguienteAddP(
    sock,
    queueJid
  );

  break;
}

case 'mc': {

  // Solo el owner principal puede administrar
  // los comandos en mantenimiento.

  if (!isMainOwner) {

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ Solo el owner principal puede usar este comando.'
      },
      {
        quoted: msg
      }
    );

  }


  db.maintenanceCommands ??= {};


  const action =
    (args[0] || '')
      .toLowerCase()
      .trim();


  // /mc
  // Muestra los comandos actualmente
  // en mantenimiento.

  if (!action) {

    const commands =
      Object.keys(
        db.maintenanceCommands
      );


    if (!commands.length) {

      return sock.sendMessage(
        jid,
        {
          text:
`🔧 *COMANDOS EN MANTENIMIENTO*

Actualmente no hay comandos en mantenimiento.

> Usa '/mc nombre' para activar uno.`
        },
        {
          quoted: msg
        }
      );

    }


    const list =
      commands
        .sort()
        .map(
          cmd => `• /${cmd}`
        )
        .join('\n');


    return sock.sendMessage(
      jid,
      {
        text:
`🔧 *COMANDOS EN MANTENIMIENTO*

${list}

> Usa '/mc off nombre' para quitar uno.`
      },
      {
        quoted: msg
      }
    );

  }


  // /mc off cleanimg
  // Desactiva el mantenimiento.

  if (
    action === 'off' ||
    action === 'remove' ||
    action === 'del'
  ) {

    const commandName =
      (args[1] || '')
        .toLowerCase()
        .replace(/^\//, '')
        .trim();


    if (!commandName) {

      return sock.sendMessage(
        jid,
        {
          text:
            '❌ Uso: /mc off nombre'
        },
        {
          quoted: msg
        }
      );

    }


    if (
      !db.maintenanceCommands[
        commandName
      ]
    ) {

      return sock.sendMessage(
        jid,
        {
          text:
`ℹ️ El comando */${commandName}* no estaba en mantenimiento.`
        },
        {
          quoted: msg
        }
      );

    }


    delete db.maintenanceCommands[
      commandName
    ];


    saveDB();


    return sock.sendMessage(
      jid,
      {
        text:
` El comando */${commandName}* ya no está en mantenimiento.`
      },
      {
        quoted: msg
      }
    );

  }


  // /mc cleanimg
  // Activa el mantenimiento.

  const commandName =
    action
      .replace(/^\//, '')
      .trim();


  if (
    commandName === 'mc'
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ No puedes poner /mc en mantenimiento.'
      },
      {
        quoted: msg
      }
    );

  }


  db.maintenanceCommands[
    commandName
  ] = true;


  saveDB();


  return sock.sendMessage(
    jid,
    {
      text:
` El comando */${commandName}* ahora está en mantenimiento.

> Los usuarios y staff no podrán usarlo.`
    },
    {
      quoted: msg
    }
  );

}





case 'searchg': {

  const input =
    args.join(' ').trim();

  const split =
    input.split('>');

  const name =
    (split[0] || '').trim();

  const anime =
    (split[1] || '').trim();


  if (!name || !anime) {

    return sock.sendMessage(
      jid,
      {
        text:
          '☆ Uso: /searchg nombre > anime'
      },
      {
        quoted: msg
      }
    );

  }


  const normalize =
    text =>
      String(text || '')
        .toLowerCase()
        .replace(/_/g,' ')
        .replace(/[^a-z0-9 ]/g,'')
        .trim();


  const target =
    normalize(name);


  let tags = [];


  try {

    const axios =
      (await import('axios')).default;


    const queries = [
      name.replace(/\\s+/g,'_'),
      name,
      anime
    ];

    for (const q of queries) {

      const url =
        'https://danbooru.donmai.us/tags.json' +
        '?search[category]=4' +
        '&search[name_matches]=*' +
        encodeURIComponent(q) +
        '*' +
        '&limit=100';


      const res =
        await axios.get(url);


      if(Array.isArray(res.data)){
        tags.push(...res.data);
      }

    }

    tags =
      [
        ...new Map(
          tags.map(
            t => [t.name,t]
          )
        ).values()
      ];


  } catch(e) {

    console.error(
      'SEARCHG:',
      e
    );

  }


  if (!tags.length) {

    return sock.sendMessage(
      jid,
      {
        text:
          '□ SIN COINCIDENCIAS'
      },
      {
        quoted: msg
      }
    );

  }


  function similarity(value){

    const original =
      String(value || '')
        .toLowerCase();


    value =
      normalize(value);


    let score = 0;


    // exacto gana siempre
    if(
      value === target
    )
      score += 20000;


    // nombre dentro del tag
    if(
      value.includes(target)
    )
      score += 8000;


    // mismo nombre con anime
    if(
      value.startsWith(target)
    )
      score += 5000;


    // penalizar variantes
    if(
      /(costume|outfit|alternate|swimsuit|cosplay|3rd|2nd)/i.test(original)
    )
      score -= 10000;


    return score;

  }


  tags.sort(
    (a,b) =>
      similarity(b.name) -
      similarity(a.name)
  );


  const best =
    tags[0];


  if(best){

    return sock.sendMessage(
      jid,
      {
        text:
          '☆ TAG RECOMENDADO\\n\\n' +
          '● \`' +
          best.name +
          '\`'
      },
      {
        quoted: msg
      }
    );

  }


  break;

}

case 'creatingcopia': {

  // Solo los owners autorizados pueden crear
  // copias manuales
  if (
    !isMainOwnerId(sender) &&
    !isSecondaryOwnerId(sender)
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este comando solo puede ser utilizado por los owners autorizados."
      },
      {
        quoted: msg
      }
    );
  }

  try {

    await sock.sendMessage(
      jid,
      {
        text:
          "⏳ Creando copia de seguridad...\n\n" +
          "◇ Espera un momento."
      },
      {
        quoted: msg
      }
    );

    const resultado =
      await crearCopia(
        sock,
        db,
        OWNER_NUMBER
      );

    if (!resultado) {
      return sock.sendMessage(
        jid,
        {
          text:
            "❌ No se pudo crear la copia.\n\n" +
            " La base de personajes está vacï¿½a " +
            "o no se pudo leer."
        },
        {
          quoted: msg
        }
      );
    }

    const copias =
      listarCopias();

    const copiaNueva =
      copias.find(
        copia =>
          copia.nombre ===
          resultado.split("/").pop()
      );

    const cantidad =
      copiaNueva
        ? copiaNueva.cantidad
        : "Desconocida";

    const peso =
      copiaNueva
        ? (
            copiaNueva.peso /
            1024 /
            1024
          ).toFixed(2)
        : "Desconocido";

    await sock.sendMessage(
      jid,
      {
        text:
          "✓ COPIA MANUAL CREADA\n\n" +
          "◇ Personajes: " +
          cantidad +
          "\n" +
          "° Peso: " +
          peso +
          " MB\n" +
          "• Estado: Guardada correctamente\n\n" +
          "◇ La copia aparecer¿ como " +
          "Copia 1 en /copias."
      },
      {
        quoted: msg
      }
    );

    console.log(
      "☆ Copia manual creada por el owner: " +
      resultado
    );

  } catch (error) {

    console.error(
      "❌ Error creando copia manual:",
      error
    );

    await sock.sendMessage(
      jid,
      {
        text:
          "❌ No se pudo crear la copia manual.\n\n" +
          "◇ Error:\n" +
          error.message
      },
      {
        quoted: msg
      }
    );

  }

  break;

}


case 'restcopia': {
  // SOLO OWNER PRINCIPAL
  if (sender !== OWNER_NUMBER) {
    break;
  }

  const numeroTexto = args[0];
  const numero = Number(numeroTexto);

  if (
    !numeroTexto ||
    !Number.isInteger(numero) ||
    numero < 1
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Uso incorrecto.\n\n" +
          "◇ Usa:\n" +
          "/restcopia [número]\n\n" +
          "◇ Ejemplo:\n" +
          "/restcopia 1"
      },
      { quoted: msg }
    );
  }

  try {
    const copias = listarCopias();

    if (!copias.length) {
      return sock.sendMessage(
        jid,
        {
          text:
            "◇ No existen copias disponibles para restaurar."
        },
        { quoted: msg }
      );
    }

    if (numero > copias.length) {
      return sock.sendMessage(
        jid,
        {
          text:
            "❌ Esa copia no existe.\n\n" +
            "◇ Copias disponibles: " + copias.length
        },
        { quoted: msg }
      );
    }

    const copia = copias[numero - 1];

    await sock.sendMessage(
      jid,
      {
        text:
          "⏳ RESTAURANDO COPIA...\n\n" +
          "◇ Copia: " + numero + "\n" +
          "◇ Archivo: " + copia.nombre + "\n" +
          "◇ Personajes: " + copia.cantidad + "\n" +
          "° Peso: " +
          (Number(copia.peso) / 1024 / 1024).toFixed(2) +
          " MB\n\n" +
          "◇ Espera un momento."
      },
      { quoted: msg }
    );

    const rutaCopia =
      "/storage/emulated/0/gacha/backups/" + copia.nombre;

    if (!fs.existsSync(rutaCopia)) {
      return sock.sendMessage(
        jid,
        {
          text:
            " La copia seleccionada no existe fï¿½sicamente.\n\n" +
            "◇ Archivo: " + copia.nombre
        },
        { quoted: msg }
      );
    }

    const data = JSON.parse(
      fs.readFileSync(rutaCopia, "utf8")
    );

    if (!Array.isArray(data)) {
      throw new Error(
        "La copia no contiene una lista válida de personajes."
      );
    }

    const charactersPath =
      "/storage/emulated/0/gacha/characters.json";

    const restauracionBackup =
      charactersPath +
      ".before-restcopia-" +
      Date.now() +
      ".bak";

    // Guardar el characters.json actual antes de restaurar.
    if (fs.existsSync(charactersPath)) {
      fs.copyFileSync(
        charactersPath,
        restauracionBackup
      );
    }

    // Restaurar la copia elegida.
    fs.copyFileSync(
      rutaCopia,
      charactersPath
    );

    const verificacion = JSON.parse(
      fs.readFileSync(charactersPath, "utf8")
    );

    if (!Array.isArray(verificacion)) {
      throw new Error(
        "La restauraciï¿½n no produjo un characters.json válido."
      );
    }

    await sock.sendMessage(
      jid,
      {
        text:
          "✓ COPIA RESTAURADA CORRECTAMENTE\n\n" +
          "◇ Copia: " + numero + "\n" +
          "◇ Archivo: " + copia.nombre + "\n" +
          "◇ Personajes restaurados: " +
          verificacion.length + "\n" +
          "° Peso: " +
          (Number(copia.peso) / 1024 / 1024).toFixed(2) +
          " MB\n\n" +
          "◇ Restauraci¿n completada."
      },
      { quoted: msg }
    );

    console.log(
      "☆ /restcopia ejecutado por:",
      sender,
      "| Copia:",
      copia.nombre,
      "| Personajes:",
      verificacion.length
    );

  } catch (error) {
    console.error(
      "❌ Error en /restcopia:",
      error
    );

    await sock.sendMessage(
      jid,
      {
        text:
          "❌ No se pudo restaurar la copia.\n\n" +
          "◇ Error:\n" +
          error.message
      },
      { quoted: msg }
    );
  }

  break;
}

case 'delcopias': {

  // Owner principal y owners secundarios
  const esOwnerAutorizado =
    isMainOwnerId(sender) ||
    isSecondaryOwnerId(sender);

  if (!esOwnerAutorizado) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este comando solo puede ser utilizado por los owners."
      },
      {
        quoted: msg
      }
    );
  }

  const copias = listarCopias();

  if (!copias.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No existen copias para eliminar."
      },
      {
        quoted: msg
      }
    );
  }

  let eliminadas = 0;
  let noEncontradas = 0;
  let errores = 0;
  let espacioLiberado = 0;

  for (const copia of copias) {

    const rutaCopia =
      "/storage/emulated/0/gacha/backups/" +
      copia.nombre;

    try {

      if (!fs.existsSync(rutaCopia)) {
        noEncontradas++;
        continue;
      }

      const peso =
        Number(copia.peso) || 0;

      fs.unlinkSync(rutaCopia);

      eliminadas++;
      espacioLiberado += peso;

      console.log(
        "☆ Copia eliminada:",
        copia.nombre
      );

    } catch (error) {

      errores++;

      console.error(
        "❌ Error eliminando:",
        copia.nombre,
        error
      );

    }
  }

  await sock.sendMessage(
    jid,
    {
      text:
        "🗑️ COPIAS ELIMINADAS\n\n" +
        "◇ Eliminadas: " +
        eliminadas +
        "\n" +
        "◇ No encontradas: " +
        noEncontradas +
        "\n" +
        "◇ Errores: " +
        errores +
        "\n" +
        "◇ Espacio liberado: " +
        (
          espacioLiberado /
          1024 /
          1024
        ).toFixed(2) +
        " MB\n\n" +
        "◇ Se eliminaron todas las copias disponibles."
    },
    {
      quoted: msg
    }
  );

  console.log(
    "☆ /delcopias ejecutado por:",
    sender,
    "| Eliminadas:",
    eliminadas
  );

  break;

}

case 'delcopia': {

  // Solo el owner principal puede eliminar copias
  if (sender !== OWNER_NUMBER) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este comando solo puede ser utilizado por el owner principal."
      },
      {
        quoted: msg
      }
    );
  }

  const numeroTexto = args[0];
  const numero = Number(numeroTexto);

  if (
    !numeroTexto ||
    !Number.isInteger(numero) ||
    numero < 1
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Uso incorrecto.\n\n" +
          "◇ Ejemplo:\n" +
          "/delcopia 1"
      },
      {
        quoted: msg
      }
    );
  }

  const copias = listarCopias();

  if (!copias.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No existen copias para eliminar."
      },
      {
        quoted: msg
      }
    );
  }

  if (numero > copias.length) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ La copia " +
          numero +
          " no existe.\n\n" +
          "◇ Copias disponibles: " +
          copias.length
      },
      {
        quoted: msg
      }
    );
  }

  const copia = copias[numero - 1];

  const rutaCopia =
    "/storage/emulated/0/gacha/backups/" +
    copia.nombre;

  try {

    if (!fs.existsSync(rutaCopia)) {
      return sock.sendMessage(
        jid,
        {
          text:
            "❌ No se encontró el archivo de la Copia " +
            numero +
            "."
        },
        {
          quoted: msg
        }
      );
    }

    fs.unlinkSync(rutaCopia);

    await sock.sendMessage(
      jid,
      {
        text:
          "✓ COPIA ELIMINADA\n\n" +
          "□ Copia: " +
          numero +
          "\n" +
          "◇ Personajes: " +
          copia.cantidad +
          "\n" +
          "° Peso: " +
          (
            copia.peso /
            1024 /
            1024
          ).toFixed(2) +
          " MB\n" +
          "• Archivo: " +
          copia.nombre +
          "\n\n" +
          "◇ La copia fue eliminada correctamente."
      },
      {
        quoted: msg
      }
    );

    console.log(
      "☆ Copia eliminada por owner: " +
      copia.nombre
    );

  } catch (error) {

    console.error(
      "❌ Error eliminando copia:",
      error
    );

    await sock.sendMessage(
      jid,
      {
        text:
          "❌ No se pudo eliminar la Copia " +
          numero +
          ".\n\n" +
          "◇ Error:\n" +
          error.message
      },
      {
        quoted: msg
      }
    );

  }

  break;

}

case 'copias': {

 if (
   !isMainOwnerId(sender) &&
   !isSecondaryOwnerId(sender)
 ) {
   return;
 }


 const copias =
   listarCopias();


 if (!copias.length) {
   return sock.sendMessage(
    jid,
    {text:"◇ No existen copias."},
    {quoted:msg}
   );
 }


 let texto =
"?¤ COPIAS DE SEGURIDAD ¤?\n\n";


 copias.forEach((c,i)=>{

 texto +=
`□ Copia ${i+1}
◇ Personajes: ${c.cantidad}
° Peso: ${(c.peso/1024/1024).toFixed(2)} MB
• Fecha: ${new Date(c.fecha).toLocaleString()}

`;

 });


 await sock.sendMessage(
  jid,
  {
   text:texto
  },
  {
   quoted:msg
  }
 );

break;

}

      case 'tomp3': await handleTomp3(sock, msg); break;
      case 'tt': { const url = args[0]; if (!url?.includes('tiktok.com')) return sock.sendMessage(jid, { text: `◇ Uso: ${prefix}tt [link]` }); await handleTt(sock, msg, url); break; }
      case 'ttsearch': {
        const query = args.join(' ').trim();
        if (!query) {
          return sock.sendMessage(
            jid,
            { text: `◇ Uso: ${prefix}ttsearch [nombre o tema]` },
            { quoted: msg }
          );
        }
        await handleTtSearch(sock, msg, query);
        break;
      }
      case 'mp4': { const input = args.slice(0).join(' '); if (!input) return sock.sendMessage(jid, { text: `◇ Uso: ${prefix}mp4 [enlace/nombre]` }); await handleMp4(sock, msg, input); break; }
      case 'ytaudio': {
          const query = args.slice(0).join(' ');

          if (!query) {
            return sock.sendMessage(
              jid,
              {
                text: `◇ Uso: ${prefix}ytaudio [nombre]`
              }
            );
          }

          await handleYtAudio(sock, msg, query);
          break;
        }
      case 'ig': { const url = args[0]; if (!url?.includes('instagram.com')) return sock.sendMessage(jid, { text: `◇ Uso: ${prefix}ig [link]` }); await handleIg(sock, msg, url); break; }
      case 'helpedit': {

  if (!isMainOwner) return;

  const texto = body
    .slice('/helpedit'.length)
    .trim();

  if (!texto) {
    return sock.sendMessage(jid,{
      text:'Uso: /helpedit texto'
    },{ quoted: msg });
  }

  db.helpMenu = texto;

  saveDB();

  await sock.sendMessage(jid,{
    text:'✓ Menú actualizado.'
  },{ quoted: msg });

  break;
}
      case 'recalcCoinsg':
      case 'recalccoinsg':
      case 'recalccoinsG':
      case 'recalcCoinsG': {

  if (!isMainOwner && !isStaffOwner) {
    return sock.sendMessage(
      jid,
      { text: '❌ Solo los owners pueden usar este comando.' },
      { quoted: msg }
    );
  }

  let total = 0;
  let actualizados = 0;
  let sinCambios = 0;
  let sinValor = 0;

  for (const c of charactersCache) {
    total++;

    const v = Number(c.value) || 0;

    if (v <= 0) {
      sinValor++;
      continue;
    }

    const nuevo = Math.floor(55 * v);

    if (Number(c.coinGen) !== nuevo) {
      c.coinGen = nuevo;
      actualizados++;
    } else {
      sinCambios++;
    }
  }

  saveCharacters();

  return sock.sendMessage(
    jid,
    {
      text:
        '✓ Recalculo de Coinsg finalizado.\n\n' +
        '◇ Total personajes » ' + total + '\n' +
        '◇ Actualizados » ' + actualizados + '\n' +
        '◇ Ya correctos » ' + sinCambios + '\n' +
        '◇ Sin valor válido » ' + sinValor + '\n\n' +
        '> Fórmula aplicada: 55 × valor'
    },
    { quoted: msg }
  );
}

      case 'setcoinsg':
  await handleSetCoinsG(
    sock,
    msg,
    args,
    jid,
    sender
  );
break;

case 'coinsg':
  await handleCoinsG(
    sock,
    msg,
    jid,
    sender
  );
break;
     case 'delx':
await handleDelX(
  sock,
  msg,
  args,
  sender
);
break; 
     case 'rwpx':
await handleRwpx(
  sock,
  msg,
  args,
  sender
);
break;
     case 'setrwpsg':
await handleSetRwpCooldown(
  sock,
  msg,
  args,
  sender
);
break;
     case 'rwp':
  await handleRwp(
    sock,
    msg,
    args,
    jid,
    sender
  );
break;
     case 'rwr':
  await handleRwr(
    sock,
    msg,
    args,
    jid,
    sender
  );
break;
      case 'bulguru':
        await handleBulguru(
          sock,
          msg,
          args
        );
        break;

      case 'danbooru':

  await handleDanbooru(
    sock,
    msg,
    args
  );

break;
      case 'gelbooru':

  await handleGelbooru(
    sock,
    msg,
    args,
    sender
  );

break;
      case 'pjaudio':
  await handlePjAudio(
    sock,
    msg,
    args,
    sender
  );
  break;
      case 'bpremium':

        await handleBpremium(
          sock,
          msg,
          sender
        );

      break;

      case 'xpremium':

        await handleXpremium(
          sock,
          msg,
          sender
        );

      break;

      case 'rw':

        await handleRw(
          sock,
          msg,
          jid,
          sender
        );

      break;
      case 'del':
        await handleDel(
          sock,
          msg
        );
        break;
      case 'setv':
        await handleSetv(
          sock,
          msg,
          args,
          sender
        );
      break;
      case "delcar": {

  const isStaff =
    isMainOwnerId(sender) ||
    isSecondaryOwnerId(sender);

  if (!isStaff)
    return;

  const query =
    body
      .slice("/delcar".length)
      .trim();

  await handleDelCar(
    sock,
    msg,
    query
  );

  break;
}
       case 'cinfo':

  await handleCinfo(
    sock,
    msg,
    args
  );

break;
      case 'carrera':
await carRaceGame.handleJoin(sock, msg, {
  groupId: jid,
  sender,
  pushName: msg.pushName
});
break;
      case 'select':
await carRaceGame.handleSelect(sock, msg, {
  groupId: jid,
  sender,
  query: args.join(' ')
});
break;
      case 'yac':
await carRaceGame.handleReady(sock, msg, {
  groupId: jid,
  sender
});
break;
      case 'setcarcv':
      case 'setcaracceleration':
await carRaceGame.handleSetCarAcceleration(sock, msg, {
  groupId: jid,
  args,
  isOwner
});
break;
      case 'garaje':
await handleGarage(sock, msg, args, jid, sender);
break;
       case "cn": {

await handleCn(
  sock,
  msg,
  jid,
  sender
);

break;

}
      case "luckshop":
await handleLuckShop(
sock,
msg
);
break;
      case "buyluck":
    await handleBuyLuck(sock,msg,args,sender);
break;
      case 'luck':
  await handleLuck(
    sock,
    msg,
    sender
  );
break;
      case 'setclaimmsg':
await handleSetClaimMsg(
  sock,
  msg,
  args,
  jid,
  sender
);
break;

      case 'delclaimmsg':
await handleDelClaimMsg(
  sock,
  msg,
  jid,
  sender
);
break;
      case 'c': await handleClaim(sock, msg, jid, sender); break;
      case "cv": {

  await handleCv(
    sock,
    msg,
    jid,
    sender
  );

  break;

}
      case 'p':
case 'ping': {

  globalThis.__pInfoMeasurements ??= [];

  const inicio = Date.now();

  const sent = await sock.sendMessage(
    msg.key.remoteJid,
    {
      text: '\u2606 \u00a1Pong!'
    },
    { quoted: msg }
  );

  const tiempo = Date.now() - inicio;

  globalThis.__pInfoMeasurements.push(tiempo);

  if (globalThis.__pInfoMeasurements.length > 20) {
    globalThis.__pInfoMeasurements.shift();
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text: `\u2606 \u00a1Pong!\n> Respuesta \u2d35 ${tiempo}ms`,
      edit: sent.key
    }
  );

  break;
}

case 'pinfo': {

  const mediciones =
    globalThis.__pInfoMeasurements ?? [];

  // ----------------------------------------------------------
  // CARACTERES UNICODE CORRECTOS
  // ----------------------------------------------------------

  const titulo =
    String.fromCodePoint(
      0x1D474, // 𝑴
      0x1D468, // 𝑨
      0x1D47D, // 𝑽
      0x1D470, // 𝑰
      0x1D47A  // 𝑺
    ) +
    '`' +
    String.fromCodePoint(
      0x1D47A, // 𝑺
      0x1D47B, // 𝑻
      0x1D47C, // 𝑼
      0x1D46B, // 𝑫
      0x1D480  // 𝒀
    );

  const ms =
    String.fromCodePoint(
      0x1D696, // 𝚖
      0x1D69C  // 𝚜
    );

  const estadoLabel =
    String.fromCodePoint(
      0x1D404, // 𝐄
      0x1D42C, // 𝐬
      0x1D42D, // 𝐭
      0x1D41A, // 𝐚
      0x1D41D, // 𝐝
      0x1D428  // 𝐨
    );

  const rapido =
    String.fromCodePoint(
      0x1D479, // 𝑹
      0x1D482, // 𝒂
      0x1D491, // 𝒑
      0x1D48A, // 𝒊
      0x1D485, // 𝒅
      0x1D490  // 𝒐
    );

  const estable =
    String.fromCodePoint(
      0x1D46C, // 𝑬
      0x1D494, // 𝒔
      0x1D495, // 𝒕
      0x1D482, // 𝒂
      0x1D483, // 𝒃
      0x1D48D, // 𝒍
      0x1D486  // 𝒆
    );

  const lento =
    String.fromCodePoint(
      0x1D473, // 𝑳
      0x1D486, // 𝒆
      0x1D48F, // 𝒏
      0x1D495, // 𝒕
      0x1D490  // 𝒐
    );

  // ----------------------------------------------------------
  // SIN MEDICIONES
  // ----------------------------------------------------------

  if (mediciones.length === 0) {

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`> ${titulo}

*Actual:* \`- ${ms}\`
*Promedio:* \`- ${ms}\`
*Mínimo:* \`- ${ms}\`
*Máximo:* \`- ${ms}\`
*Jitter:* \`- ${ms}\`

${estadoLabel}: \`Sin datos\``
      },
      { quoted: msg }
    );

    break;
  }

  // ----------------------------------------------------------
  // CALCULOS
  // ----------------------------------------------------------

  const actual =
    mediciones[mediciones.length - 1];

  const promedio =
    Math.round(
      mediciones.reduce(
        (sum, valor) => sum + valor,
        0
      ) / mediciones.length
    );

  const minimo =
    Math.min(...mediciones);

  const maximo =
    Math.max(...mediciones);

  let jitter = 0;

  if (mediciones.length > 1) {

    let diferenciaTotal = 0;

    for (
      let i = 1;
      i < mediciones.length;
      i++
    ) {

      diferenciaTotal +=
        Math.abs(
          mediciones[i] -
          mediciones[i - 1]
        );
    }

    jitter = Math.round(
      diferenciaTotal /
      (mediciones.length - 1)
    );
  }

  // ----------------------------------------------------------
  // ESTADO
  //
  // 100-199  = Rapido
  // 200-449  = Estable
  // 450+     = Lento
  // ----------------------------------------------------------

  let estado;

  if (actual >= 100 && actual < 200) {

    estado = rapido;

  } else if (actual >= 200 && actual < 450) {

    estado = estable;

  } else if (actual >= 450) {

    estado = lento;

  } else {

    estado = rapido;
  }

  // ----------------------------------------------------------
  // MENSAJE FINAL
  // ----------------------------------------------------------

  const texto =
`> ${titulo}

*Actual:* \`${actual} ${ms}\`
*Promedio:* \`${promedio} ${ms}\`
*Mínimo:* \`${minimo} ${ms}\`
*Máximo:* \`${maximo} ${ms}\`
*Jitter:* \`${jitter} ${ms}\`

${estadoLabel}: \`${estado}\``;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text: texto
    },
    { quoted: msg }
  );

  break;
}

case 'pinfo': {

  const mediciones =
    globalThis.__pInfoMeasurements ?? [];

  if (mediciones.length === 0) {

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`> 𝑴𝑨𝑽𝑰𝑺\`𝑺𝑻𝑼𝑫𝒀

*Actual:* \`ï¿½ 𝚖𝚜\`
*Promedio:* \`ï¿½ 𝚖𝚜\`
*Mï¿½nimo:* \` \`
*Mï¿½ximo:* \`ï¿½ 𝚖𝚜\`
*Jitter:* \`ï¿½ 𝚖𝚜\`

𝐄𝐬𝐭𝐚𝐝𝐨: \`Sin datos\``
      },
      { quoted: msg }
    );

    break;
  }

  const actual =
    mediciones[mediciones.length - 1];

  const promedio =
    Math.round(
      mediciones.reduce(
        (sum, value) => sum + value,
        0
      ) / mediciones.length
    );

  const minimo =
    Math.min(...mediciones);

  const maximo =
    Math.max(...mediciones);

  let jitter = 0;

  if (mediciones.length > 1) {

    let diferenciaTotal = 0;

    for (
      let i = 1;
      i < mediciones.length;
      i++
    ) {

      diferenciaTotal += Math.abs(
        mediciones[i] -
        mediciones[i - 1]
      );
    }

    jitter =
      Math.round(
        diferenciaTotal /
        (mediciones.length - 1)
      );
  }

  let estado;

  if (actual >= 100 && actual < 200) {
    estado = '𝚁𝚊𝚙𝚒𝚍𝚘';
  } else if (actual >= 200 && actual < 450) {
    estado = '𝑬𝒔𝒕𝒂𝒃𝒍𝒆';
  } else if (actual >= 450) {
    estado = '𝐋𝐞𝐧𝐭𝐨';
  } else {
    estado = '𝚁𝚊𝚙𝚒𝚍𝚘';
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`> 𝑴𝑨𝑽𝑰𝑺\`𝑺𝑻𝑼𝑫𝒀

*Actual:* \`${actual} 𝚖𝚜\`
*Promedio:* \`${promedio} 𝚖𝚜\`
*Mï¿½nimo:* \`${minimo} \`
*Mï¿½ximo:* \`${maximo} 𝚖𝚜\`
*Jitter:* \`${jitter} 𝚖𝚜\`

𝐄𝐬𝐭𝐚𝐝𝐨: \`${estado}\``
    },
    { quoted: msg }
  );

  break;
}

case 'pinfo': {

  // ==========================================================
  // PINFO_LATENCY
  // ==========================================================

  const mediciones =
    globalThis.__pInfoMeasurements ?? [];

  if (mediciones.length === 0) {

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`> 𝑴𝑨𝑽𝑰𝑺\`𝑺𝑻𝑼𝑫𝒀

*Actual:* \`ï¿½ 𝚖𝚜\`
*Promedio:* \`ï¿½ 𝚖𝚜\`
*Mï¿½nimo:* \` \`
*Mï¿½ximo:* \`ï¿½ 𝚖𝚜\`
*Jitter:* \`ï¿½ 𝚖𝚜\`

𝐄𝐬𝐭𝐚𝐝𝐨: \`Sin datos\``
      },
      { quoted: msg }
    );

    break;
  }

  const actual =
    mediciones[mediciones.length - 1];

  const promedio =
    Math.round(
      mediciones.reduce(
        (sum, value) => sum + value,
        0
      ) / mediciones.length
    );

  const minimo =
    Math.min(...mediciones);

  const maximo =
    Math.max(...mediciones);

  let jitter = 0;

  if (mediciones.length > 1) {

    let diferenciaTotal = 0;

    for (
      let i = 1;
      i < mediciones.length;
      i++
    ) {

      diferenciaTotal += Math.abs(
        mediciones[i] -
        mediciones[i - 1]
      );
    }

    jitter =
      Math.round(
        diferenciaTotal /
        (mediciones.length - 1)
      );
  }

  // ==========================================================
  // ESTADO SEGUN LA LATENCIA ACTUAL
  // ==========================================================

  let estado;

  if (actual >= 100 && actual < 200) {

    estado = '𝚁𝚊𝚙𝚒𝚍𝚘';

  } else if (actual >= 200 && actual < 450) {

    estado = '𝑬𝒔𝒕𝒂𝒃𝒍𝒆';

  } else if (actual >= 450) {

    estado = '𝐋𝐞𝐧𝐭𝐨';

  } else {

    estado = '𝚁𝚊𝚙𝚒𝚍𝚘';
  }

  const textoPInfo =
`> 𝑴𝑨𝑽𝑰𝑺\`𝑺𝑻𝑼𝑫𝒀

*Actual:* \`${actual} 𝚖𝚜\`
*Promedio:* \`${promedio} 𝚖𝚜\`
*Mï¿½nimo:* \`${minimo} \`
*Mï¿½ximo:* \`${maximo} 𝚖𝚜\`
*Jitter:* \`${jitter} 𝚖𝚜\`

𝐄𝐬𝐭𝐚𝐝𝐨: \`${estado}\``;

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text: textoPInfo
    },
    { quoted: msg }
  );

  break;
}
      case 'topwaifu': {

  await handleTopWaifu(
    sock,
    msg,
    args
  );

  break;
}
      case 'ligue': {

  await handleLigue(
    sock,
    msg,
    args,
    sender
  );

  break;
}

case 'ligues': {

  await handleLigues(
    sock,
    msg,
    args,
    sender
  );

  break;
}
      case 'romper':
      case 'terminar':
      case 'break': {

  await handleRomper(
    sock,
    msg,
    args,
    jid,
    sender
  );

  break;
}
      case 'setligue': {

  await handleSetLigue(
    sock,
    msg,
    args,
    sender
  );

  break;
}
      case 'azz':
  await handleAzz(
    sock,
    msg,
    jid
  );
  break;

case 'azztext':
  await handleAzzText(
    sock,
    msg,
    jid,
    sender,
    args
  );
  break;

case 'azzdeltext':
  await handleAzzDelText(
    sock,
    msg,
    jid,
    sender
  );
  break;
      case 'winfo': { const query = args.slice(0).join(' '); if (!query) return sock.sendMessage(jid, { text: `◇ Uso: ${prefix}winfo [nombre]` }); await handleWinfo(sock, msg, query, jid); break; }
      case 'wtop':
  await handleWtop(sock, msg, args);
  break;
  case 'modwarn': {

  if (!isOwner) {
  return sock.sendMessage(jid,{
    text:'Solo el owner puede usar este comando.'
  },{ quoted: msg });
}

  if (!target) {
    return sock.sendMessage(jid,{
      text:'Uso: /modwarn [razón]\n\nResponde a un mensaje o menciona a un usuario.'
    },{ quoted: msg });
  }

  const reason =
    args.join(' ').trim() || 'Sin razón';

  if (!db.modWarns[target])
    db.modWarns[target] = [];

  db.modWarns[target].push({
    reason,
    date: Date.now(),
    by: sender
  });

  const warns =
    db.modWarns[target].length;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`Advertencia añadida a @${target.split('@')[0]}

Advertencias: ${warns}

Motivo: ${reason}`,
    mentions:[target]
  },{ quoted: msg });

  break;
}
      case 'kick': {
        await handleKick(
          sock,
          msg,
          jid,
          sender,
          mentioned,
          args
        );
        break;
      }
      case 'ban': {

  let targetUser =
    mentioned?.[0];

  if (!targetUser && args[0]) {

    const numero =
      args[0].replace(/\D/g,'');

    if (numero.length < 8) {
      return sock.sendMessage(
        jid,
        {
          text:'Nï¿½mero inválido.'
        },
        { quoted: msg }
      );
    }

    // Buscar en usuarios registrados
    targetUser =
      Object.keys(db.users || {})
        .find(
          id =>
            id === numero ||
            id.includes(numero)
        );

    // Buscar en personajes reclamados
    if (!targetUser) {

      for (const char of charactersCache) {

        if (!char.claimedBy)
          continue;

        for (
          const data of
          Object.values(char.claimedBy)
        ) {

          const uid =
            data?.user;

          if (
            uid &&
            uid.includes(numero)
          ) {
            targetUser = uid;
            break;
          }
        }

        if (targetUser)
          break;
      }
    }

    // Probar formatos comunes
    if (!targetUser) {

      const posibles = [
        numero + '@lid',
        numero + '@s.whatsapp.net'
      ];

      for (const id of posibles) {

        if (
          db.users?.[id]
        ) {
          targetUser = id;
          break;
        }
      }
    }

    // Último recurso
    if (!targetUser) {
      targetUser =
        numero + '@lid';
    }
  }

  if (!targetUser) {
    return sock.sendMessage(
      jid,
      {
        text:
'Uso:\n/ban @usuario\n/ban 51999999999'
      },
      {
        quoted: msg
      }
    );
  }

  if (
    targetUser === OWNER_NUMBER ||
    SECONDARY_OWNERS.includes(
      targetUser
    )
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
'No puedes banear a un owner.'
      },
      {
        quoted: msg
      }
    );
  }

  // Quitar personajes
  for (const char of charactersCache) {

    if (!char.claimedBy)
      continue;

    for (
      const groupId of
      Object.keys(char.claimedBy)
    ) {

      if (
        char.claimedBy[groupId]
          ?.user === targetUser
      ) {
        delete char.claimedBy[
          groupId
        ];
      }
    }
  }

  // Ban permanente
  db.bannedUsers ??= {};

  db.bannedUsers[targetUser] = {
    reason: 'Ban global',
    by: sender,
    date: Date.now()
  };

  // Eliminar datos
  delete db.users[targetUser];

  // El usuario baneado tampoco puede quedar
  // dentro de la copia protegida.
  eliminarUsuarioDeProteccion(targetUser);

  delete db.modWarns[targetUser];

  // Eliminar economía
  if (db.groupEconomy) {

    for (
      const groupId of
      Object.keys(
        db.groupEconomy
      )
    ) {
      delete db.groupEconomy[
        groupId
      ]?.[targetUser];
    }
  }

  saveCharacters();
  saveDB();

  await sock.sendMessage(
    jid,
    {
      text:
`•­─【 BAN GLOBAL 〕─◆

• Usuario:
@${targetUser.split('@')[0]}

🗑️ Nivel eliminado.
🗑️ Monedas eliminadas.
🗑️ Personajes eliminados.
🗑️ Harem eliminado.

🚫 Usuario baneado permanentemente.

•°────────◆`,
      mentions: [targetUser]
    },
    {
      quoted: msg
    }
  );

  break;
}
      case 'unban': {

  const target =
    mentioned?.[0];

  if (!target) {
    return sock.sendMessage(jid,{
      text:'Uso: /unban @usuario'
    },{ quoted: msg });
  }

  delete db.bannedUsers[target];

  saveDB();

  await sock.sendMessage(jid,{
    text:
`✓ Usuario desbaneado.

@${target.split('@')[0]}`,
    mentions:[target]
  },{ quoted: msg });

  break;
}
      case 'userid': {

  if (!isOwner) {
    return sock.sendMessage(jid,{
      text:'Solo los owners pueden usar este comando.'
    },{ quoted: msg });
  }

  const query =
    args.join(' ').trim().toLowerCase();

  if (!query) {
    return sock.sendMessage(jid,{
      text:
`Uso:
/userid Antonio

o

/userid 39604497432739@lid`
    },{ quoted: msg });
  }

  const found =
  Object.entries(db.users).filter(
    ([id,user]) =>
      id.toLowerCase() === query ||
      user.name?.toLowerCase().includes(query)
  );

  if (!found.length) {
  return sock.sendMessage(jid,{
    text:'Usuario no encontrado.'
  },{ quoted: msg });
}

if (found.length > 1) {

  let text =
`•­─【 COINCIDENCIAS 〕─◆

Se encontraron ${found.length} usuarios:

`;

  found.slice(0,15).forEach(([id,user],i)=>{

    text +=
`${i+1}. ${user.name || 'Sin nombre'}
🆔 ${id}

`;

  });

  text +=
`Usa:

/userid [ID COMPLETO]

•°────────◆`;

  return sock.sendMessage(jid,{
    text
  },{ quoted: msg });
}

const [userId,userData] = found[0];

  let totalChars = 0;

  for (const char of charactersCache) {

    if (!char.claimedBy) continue;

    for (const groupId of Object.keys(char.claimedBy)) {

      if (
        char.claimedBy[groupId]?.user === userId
      ) {
        totalChars++;
      }

    }

  }

await sock.sendMessage(jid,{
    text:
`•­─【 USER INFO 〕─◆

 Nombre:
${userData.name || 'Desconocido'}

 ID:
${userId}

☆ Nivel:
${userData.level || 1}

◇ XP:
${userData.xp || 0}

¿ Mensajes:
${userData.messages || 0}

~ Personajes:
${totalChars}

•°────────◆`
  },{ quoted: msg });

  break;
}
      case 'modwarns': {

  if (!target) {
    return sock.sendMessage(jid,{
      text:'Uso: /modwarns\n\nResponde a un mensaje o menciona a un usuario.'
    },{ quoted: msg });
  }

  const warns =
    db.modWarns[target] || [];

  if (!warns.length) {
    return sock.sendMessage(jid,{
      text:'El usuario no tiene advertencias.'
    },{ quoted: msg });
  }

  let text =
`Advertencias de @${target.split('@')[0]}

Total: ${warns.length}

`;

  warns.forEach((w,i)=>{

    const fecha =
      new Date(w.date)
        .toLocaleString('es-ES');

    text +=
`#${i+1} » ${w.reason}
Fecha: ${fecha}

`;

  });

  await sock.sendMessage(jid,{
    text,
    mentions:[target]
  },{ quoted: msg });

  break;
}
      case 'modwarnlimit': {

  if (sender !== OWNER_NUMBER) {
  return sock.sendMessage(jid,{
    text:'Solo el owner principal puede usar este comando.'
  },{ quoted: msg });
}

  if (!args[0]) {
    return sock.sendMessage(jid,{
      text:
`Límite actual de advertencias

Actual: ${db.modWarnLimit}`
    },{ quoted: msg });
  }

  const limit = Number(args[0]);

  if (
    isNaN(limit) ||
    limit < 1 ||
    limit > 20
  ) {
    return sock.sendMessage(jid,{
      text:
`El límite debe estar entre 1 y 20.

Ejemplo:
/modwarnlimit 5`
    },{ quoted: msg });
  }

  db.modWarnLimit = limit;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`Límite actualizado

Nuevo límite: ${limit}`
  },{ quoted: msg });

  break;
}
      case 'wimage': { const query = args.slice(0).join(' '); if (!query) return sock.sendMessage(jid, { text: `◇ Uso: ${prefix}wimage [nombre]` }); await handleWimage(sock, msg, query); break; }
      case 'pin': {
        const query =
          args
            .join(' ')
            .trim();

        await handlePin(
          sock,
          msg,
          query
        );

        break;
      }
      case 'mision':
      case 'mission': {

  await handleCreateMission(
    sock,
    msg,
    args,
    jid,
    sender
  );

  break;

}
  case 'namestaff':
    await handleNameStaff(sock, msg, args, jid, sender);
    break;
  case 'events':
    await handleEvents(sock, msg, jid, sender, args);
    break;

  case 'delmision':

  await handleDelMision(
    sock,
    msg,
    jid,
    sender,
    args
  );

break;

      case 'misions':
      case 'misiones': {

  await handleMisions(
    sock,
    msg,
    jid,
    sender
  );

  break;

}

      case 'cleanimg': {

  const data = body
    .slice('/cleanimg'.length)
    .trim()
    .split('|')
    .map(x => x.trim());

  if (data.length < 7) {

    return sock.sendMessage(
      jid,
      {
        text:
`•­─【 CLEANIMG 〕─◆
│ Crea un personaje nuevo
•°────────◆

◇ Uso:

/cleanimg Nombre | Valor | Género | Anime | Rareza | Chance | Tag

◇ Ejemplo:

/cleanimg Nazuna Nanakusa | 150000 | Femenino | Yofukashi no Uta | Mod | 0.23% | nanakusa_nazuna_(yofukashi_no_uta)`
      },
      { quoted: msg }
    );

  }

  const nombre  = data[0];
  const valor   = data[1];
  const genero  = data[2];
  const anime   = data[3];
  const rareza  = data[4];
  const chance  = data[5];
  const tag     = data[6];

  await handleCleanImg(
    sock,
    msg,
    nombre,
    valor,
    genero,
    anime,
    rareza,
    chance,
    tag
  );

  break;
}
      case 'cleanimgv': {

const data = body
  .slice(prefix.length + 'cleanimgv'.length)
  .trim()
  .split('|')
  .map(x => x.trim());

if (data.length < 6) {

  return sock.sendMessage(
    jid,
    {
      text:
`•­─【 CLEANIMGV 〕─◆
│ Crear veh¿culo
•°────────◆

Uso:

${prefix}cleanimgv Personaje | Rareza | Precio | Velocidad | Nombre del carro | Aceleración

Ejemplo:

${prefix}cleanimgv Miku | Epico | 350000 | 180 | Pegasso Sport Pro 250 | 273`
    },
    { quoted: msg }
  );

}

const personaje = data[0];
const rareza = data[1];
const precio = data[2];
const velocidad = data[3];
const nombreCarro = data[4];
const accelerationText = data[5];
const acceleration =
  /^\d+(?:\.\d+)?$/.test(String(accelerationText || '').trim())
    ? Number(accelerationText)
    : NaN;

if (
  !Number.isFinite(acceleration) ||
  acceleration <= 0
) {
  return sock.sendMessage(
    jid,
    { text: `La aceleración en ${prefix}cleanimgv debe ser un número mayor que 0, sin unidades ni símbolos.` },
    { quoted: msg }
  );
}

const sender =
  msg.key.participant ||
  msg.participant ||
  msg.key.remoteJid;

let images = [];

// Primero intenta obtener el álbum
const activeAlbumImages =
  (pendingAlbums[sender] || []).filter(
    entry => Date.now() - entry.time < 300000
  );

if (activeAlbumImages.length) {
  pendingAlbums[sender] = activeAlbumImages;
}

if (
  activeAlbumImages.length
) {

  images = [...activeAlbumImages];

}
// Si no hay álbum usa las imágenes recientes
else if (
  recentImages[sender] &&
  recentImages[sender].length
) {

  images = recentImages[sender].filter(
    entry => Date.now() - entry.time < 300000
  );

}

if (!images.length) {

  return sock.sendMessage(
    jid,
    {
      text:
` Responde una imagen o un ï¿½lbum antes de usar ${prefix}cleanimgv.`
    },
    {
      quoted: msg
    }
  );

}

const buffers = [];

for (let index = 0; index < images.length; index++) {
  const imageEntry = images[index];
  let imageBuffer;
  try {
    imageBuffer = await downloadMediaMessage(
      imageEntry.msg,
      'buffer',
      {}
    );
  } catch (error) {
    console.error(
      `[CLEANIMGV] No se pudo descargar la imagen ${index + 1}/${images.length}:`,
      error?.message || error
    );
    await sock.sendMessage(
      jid,
      {
        text:
          `No pude descargar la imagen ${index + 1} de ${images.length}. ` +
          'No guardé el vehículo ni eliminé el álbum; vuelve a intentarlo.'
      },
      { quoted: msg }
    );
    return;
  }

  if (!Buffer.isBuffer(imageBuffer) || imageBuffer.length === 0) {
    await sock.sendMessage(
      jid,
      {
        text:
          `La imagen ${index + 1} de ${images.length} llegó vacía. ` +
          'No guardé el vehículo ni eliminé el álbum.'
      },
      { quoted: msg }
    );
    return;
  }
  buffers.push(imageBuffer);
}

await handleCleanImgV(
  sock,
  msg,
  personaje,
  rareza,
  precio,
  velocidad,
  nombreCarro,
  acceleration,
  buffers,
  sender
);

// Limpiar para no mezclar con el siguiente vehículo
delete recentImages[sender];
delete pendingAlbums[sender];

break;
}
      case 'deltag': {
  const data =
    body
      .slice('/deltag'.length)
      .trim()
      .split('|')
      .map(x => x.trim());

  const tag =
    data[0];

  const source =
    data[1];

  if (!tag || !source) {
    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`◇ Uso

/deltag nombre | fuente`
      },
      {
        quoted: msg
      }
    );

    break;
  }

  const result =
    deleteManualTag(
      tag,
      source
    );

  if (!result.ok) {

    if (result.reason === 'not_found') {
      await sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
            `》*El tag "${tag}" no existe.*`
        },
        {
          quoted: msg
        }
      );

      break;
    }

    if (result.reason === 'source_mismatch') {
      await sock.sendMessage(
        msg.key.remoteJid,
        {
          text:
`》*La fuente no coincide con la registrada para "${tag}".*`
        },
        {
          quoted: msg
        }
      );

      break;
    }

    await sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
          '◇ No se pudo eliminar el tag y sus imágenes.'
      },
      {
        quoted: msg
      }
    );

    break;
  }

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`◇ Tag eliminado correctamente.

□ Tag » ${result.tag}
◇ Fuente » ${result.source}
○ Imágenes locales » Eliminadas`
    },
    {
      quoted: msg
    }
  );

  break;
}

case 'addtag': {
        const raw =
          args.join(' ').trim();

        const separator =
          raw.indexOf('/');

        if (separator === -1) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ Uso: ${prefix}addtag nombre / fuente`
            },
            { quoted: msg }
          );
        }

        const tag =
          raw
            .slice(0, separator)
            .trim();

        const source =
          raw
            .slice(separator + 1)
            .trim();

        if (!tag || !source) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ Uso: ${prefix}addtag nombre / fuente`
            },
            { quoted: msg }
          );
        }

        const result =
          createManualTag(
            tag,
            source
          );

        if (!result.ok) {
          if (result.reason === 'exists') {
            return sock.sendMessage(
              jid,
              {
                text:
                  `◇ El tag "${result.tag}" ya existe.`
              },
              { quoted: msg }
            );
          }

          return sock.sendMessage(
            jid,
            {
              text:
                '◇ No se pudo crear el tag.'
            },
            { quoted: msg }
          );
        }

        await sock.sendMessage(
          jid,
          {
            text:
              `◇ Tag creado correctamente.\n\n` +
              `□ Tag » ${result.tag}\n` +
              `◇ Fuente » ${result.source}\n` +
              `□ Imágenes » 0/30`
          },
          { quoted: msg }
        );

        break;
      }

      case 'addfttag': {
        const raw =
          args.join(' ').trim();

        const separator =
          raw.indexOf('/');

        if (separator === -1) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ Uso: ${prefix}addfttag nombre / fuente\n` +
                `◇ Debes responder a una imagen o álbum.`
            },
            { quoted: msg }
          );
        }

        const tag =
          raw
            .slice(0, separator)
            .trim();

        const source =
          raw
            .slice(separator + 1)
            .trim();

        if (!tag || !source) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ Uso: ${prefix}addfttag nombre / fuente`
            },
            { quoted: msg }
          );
        }

        const manualTag =
          getManualTag(tag);

        if (!manualTag) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ El tag "${tag}" no existe.\n` +
                `◇ Primero usa ${prefix}addtag ${tag} / ${source}`
            },
            { quoted: msg }
          );
        }

        if (
          String(manualTag.source)
            .trim()
            .toLowerCase() !==
          source
            .trim()
            .toLowerCase()
        ) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ La fuente no coincide con la registrada para "${tag}".\n\n` +
                `◇ Fuente registrada » ${manualTag.source}`
            },
            { quoted: msg }
          );
        }

        let pending =
          getManualTagPendingImages(
            msg,
            jid,
            sender
          );

        if (!pending.ok && pending.reason === 'image_not_pending') {
          const quote =
            msg.message?.extendedTextMessage?.contextInfo ||
            msg.message?.imageMessage?.contextInfo ||
            msg.message?.videoMessage?.contextInfo;
          const quotedMessage = quote?.quotedMessage;
          const quotedImage =
            quotedMessage?.imageMessage ||
            quotedMessage?.ephemeralMessage?.message?.imageMessage ||
            quotedMessage?.viewOnceMessage?.message?.imageMessage ||
            quotedMessage?.viewOnceMessageV2?.message?.imageMessage;

          if (quote?.stanzaId && quotedImage) {
            const quotedImageMsg = {
              key: {
                remoteJid: quote.remoteJid || jid,
                id: quote.stanzaId,
                participant: quote.participant
              },
              message: {
                imageMessage: quotedImage
              }
            };

            await captureManualTagImage(
              quotedImageMsg,
              jid,
              sender,
              downloadMediaMessage
            );
            pending = getManualTagPendingImages(msg, jid, sender);
          }
        }

        if (!pending.ok) {
          let text =
            '◇ No se encontró una imagen válida para este tag.';

          if (pending.reason === 'no_quote') {
            text =
              '◇ Responde directamente a una imagen o álbum antes de usar /addfttag.';
          }

          if (
            pending.reason ===
            'image_not_pending'
          ) {
            text =
              '◇ No pude recuperar esa imagen. Responde directamente a una imagen original (no a un mensaje reenviado sin vista previa) y vuelve a probar.';
          }

          return sock.sendMessage(
            jid,
            { text },
            { quoted: msg }
          );
        }

        const currentCount =
          Array.isArray(manualTag.images)
            ? manualTag.images.length
            : 0;

        const available =
          Math.max(
            0,
            30 - currentCount
          );

        if (!available) {
          return sock.sendMessage(
            jid,
            {
              text:
                `◇ El tag "${tag}" ya tiene 30/30 imágenes.`
            },
            { quoted: msg }
          );
        }

        const selected =
          pending.images.slice(
            0,
            available
          );

        const buffers = [];

        for (const image of selected) {
          try {
            buffers.push(
              fs.readFileSync(
                image.filePath
              )
            );
          } catch (error) {
            console.log(
              '[MANUAL-TAGS] Error leyendo temporal:',
              error?.message || error
            );
          }
        }

        if (!buffers.length) {
          return sock.sendMessage(
            jid,
            {
              text:
                '◇ No se pudieron leer las imágenes temporales.'
            },
            { quoted: msg }
          );
        }

        const result =
          await addManualTagImages(
            tag,
            buffers
          );

        if (!result.ok) {
          return sock.sendMessage(
            jid,
            {
              text:
                '◇ No se pudieron guardar las imágenes.'
            },
            { quoted: msg }
          );
        }

        consumeManualTagImages(
          selected
        );

        let text =
          `◇ Imágenes agregadas a "${tag}".\n\n` +
          `□ Agregadas » ${result.added}\n` +
          `◇ Total » ${result.total}/30`;

        if (
          selected.length >
          result.added
        ) {
          text +=
            `\n□ Límite alcanzado » ` +
            `${result.total}/30`;
        }

        if (result.duplicated) {
          text +=
            `\n◇ Duplicadas » ${result.duplicated}`;
        }

        await sock.sendMessage(
          jid,
          {
            text
          },
          { quoted: msg }
        );

        break;
      }

      case 'testtag':

  await handleTestTag(
    sock,
    msg,
    args
  );

break;
      case 'aggimgpj': {

  const data = body
    .slice('/aggimgpj'.length)
    .trim()
    .split('|')
    .map(x => x.trim());

  if (data.length < 2) {
    return sock.sendMessage(jid,{
      text:
`•­─【 AGGIMGPJ 〕─◆

Uso:
/aggimgpj Nombre | Anime

Ejemplo:
/aggimgpj Jane Doe | Zenless Zone Zero

•°────────◆`
    },{ quoted: msg });
  }

  const nombre = data[0];
  const anime = data[1];

  const personaje = charactersCache.find(
    c =>
      c.name?.toLowerCase() === nombre.toLowerCase() &&
      c.anime?.toLowerCase() === anime.toLowerCase()
  );

  if (!personaje) {
    return sock.sendMessage(jid,{
      text:
`❌ Personaje no encontrado.

Nombre: ${nombre}
Anime: ${anime}`
    },{ quoted: msg });
  }

  if (!canRepairCharacterMedia(personaje, sender)) {
    return sock.sendMessage(jid, {
      text: '◇ Solo el creador, staff u owner puede corregir este personaje.'
    }, { quoted: msg });
  }

  const wasInvalid =
    getCharacterImages(personaje.key).length === 0 &&
    !(await getCharacterMedia(personaje));
  const quoteContext =
    msg.message?.extendedTextMessage?.contextInfo ||
    msg.message?.imageMessage?.contextInfo ||
    msg.message?.videoMessage?.contextInfo;
  const quotedId = quoteContext?.stanzaId;
  const quotedMessage = quoteContext?.quotedMessage;
  const quotedImage = unwrapImageMessage(quotedMessage);
  const quotedAlbum = unwrapAlbumMessage(quotedMessage);

  if (!quotedId || (!quotedImage && !quotedAlbum)) {
    return sock.sendMessage(jid, {
      text: '◇ Responde directamente a una imagen o álbum con /aggimgpj. No se aceptan imágenes recientes sin citar.'
    }, { quoted: msg });
  }

  const cachedAlbumImages = selectQuotedAlbumImages(
    pendingAlbums,
    {
      quotedId,
      groupId: jid,
      participant: quoteContext.participant,
      albumQuote: Boolean(quotedAlbum)
    }
  ).filter(entry => Boolean(unwrapImageMessage(entry.msg?.message)));
  let images = cachedAlbumImages;
  let expectedAlbumImages = null;
  const albumId = quotedAlbum
    ? quotedId
    : cachedAlbumImages[0]?.albumId;

  if (albumId) {
    expectedAlbumImages =
      quotedAlbum?.expectedImageCount ||
      cachedAlbumImages.find(entry => entry.albumExpectedImageCount)?.albumExpectedImageCount ||
      null;
    if (
      expectedAlbumImages &&
      images.length !== Number(expectedAlbumImages)
    ) {
      return sock.sendMessage(jid, {
        text: `◇ No pude recuperar el álbum completo (${images.length}/${expectedAlbumImages} imágenes). Cita nuevamente el álbum e inténtalo otra vez.`
      }, { quoted: msg });
    }
  } else if (quotedImage) {
    images = [{
      msg: {
        key: {
          remoteJid: jid,
          id: quotedId,
          participant: quoteContext.participant
        },
        message: quotedImage
      },
      time: Date.now()
    }];
  } else {
    images = [];
  }

  const seenImageIds = new Set();
  images = images.filter(entry => {
    const id = entry?.msg?.key?.id;
    if (!id || seenImageIds.has(id)) return false;
    seenImageIds.add(id);
    return true;
  });

  console.log(
    '[AGGIMGPJ] Cache encontrado:',
    images.length
  );

  if (!images.length) {
    return sock.sendMessage(jid,{
      text:
` No hay imágenes recientes.

Responde a la imagen o al álbum con:

/aggimgpj ${personaje.name} | ${personaje.anime}`
    },{ quoted: msg });
  }

  let agregadas = 0;

  const existentes =
    getCharacterImages(personaje.key).length;

  const imageBuffers = [];
  try {
    for (const image of images) {
      const buffer = await downloadMediaMessage(image.msg, 'buffer', {});
      if (!Buffer.isBuffer(buffer) || buffer.length === 0) {
        throw new Error('Una de las imágenes citadas llegó vacía.');
      }
      imageBuffers.push(buffer);
    }
  } catch (error) {
    console.error('[AGGIMGPJ] No se pudo descargar la imagen citada:', error);
    return sock.sendMessage(jid, {
      text: `❌ No pude descargar la imagen o el álbum citado: ${error.message || 'error desconocido'}. No se guardaron imágenes.`
    }, { quoted: msg });
  }

  fs.mkdirSync(GACHA_IMAGES, { recursive: true });
  for (const media of imageBuffers) {
    const fileName = `${personaje.key}_${existentes + agregadas + 1}.jpg`;
    fs.writeFileSync(path.join(GACHA_IMAGES, fileName), media);
    console.log('[AGGIMGPJ] Guardada:', fileName);
    agregadas++;
  }

  const nowReturnsImage =
    agregadas > 0 &&
    wasInvalid &&
    !!(await getCharacterMedia(personaje));
  const statusAfter =
    nowReturnsImage
      ? rewardInvalidMediaRepair(personaje, sender)
      : null;

  if (statusAfter !== null) {
    await notifyEvents(
      sock,
      `${getStaffDisplayName(sender)} ha arreglado el personaje ${personaje.name} y obtuvo 5.000 de status.`,
      [sender]
    );
  }

  await sock.sendMessage(jid,{
    text:
`•­─【 ¿LBUM ACTUALIZADO 〕─◆

• ${personaje.name}
📺 ${personaje.anime}

🖼️ Im¿genes agregadas:
${agregadas}

 Total ï¿½lbum:
${getCharacterImages(personaje.key).length}

🔑 Key:
${personaje.key}` +
        (statusAfter !== null
          ? `\n\n**RECOMPENSA POR ARREGLO**\n**+5.000 Status**\n**Status actual:** ${statusAfter}`
          : '') + `

•°────────◆`
  },{ quoted: msg });

  break;
}
      case 'waifuvideo': { const query = args.slice(0).join(' '); if (!query) return sock.sendMessage(jid, { text: `◇ Uso: ${prefix}waifuvideo [nombre]` }); await handleWaifuVideo({ sock, msg, args, jid }); break; }
      case "giflinkpat":
    await saveActionGif(sock, msg, "pat");
    break;
      case "giflinkshy":
    await saveActionGif(sock, msg, "shy");
    break;
      case "giflinkfuck":
    await saveActionGif(sock, msg, "fuck");
    break;
      case "giflinkkiss":
    await saveActionGif(sock, msg, "kiss");
    break;
      case "giflinkhug":
    await saveActionGif(sock, msg, "hug");
    break;
      case "pat":
case "hug":
case "kiss":
case "cuddle":
case "slap":
case "bite":
case "poke":
case "lick":
case "wave":
case "cry":
case "smile":
case "shy":
case "dance":

    return await handleAction(
        sock,
        msg,
        command
    );
      case 'waifuedit': await handleWaifuEdit({ sock, msg, args, jid }); break;
      case 'vote': await handleVote(sock, msg, args, jid, sender); break;
      case 'resetharem': await handleResetHarem(sock, msg, jid, sender); break;
      case 'harem': await handleHarem(sock, msg, jid, sender, args, mentioned); break;
      case 'delwaifu': await handleDelwaifu(sock, msg, args, jid, sender); break;
      case 'topgacha': await handleTopGachaGlobal(sock, msg, args, jid); break;
      case 'topgachagp': await handleTopGachagp(sock, msg, args, jid); break;
      case 'givechar': await handleGivechar(sock, msg, args, jid, sender, mentioned); break;
case 's':
case 'stickers': {
  try {
    // ============================================================
    // /s y /stickers
    // Convierte UNA imagen citada en sticker
    // ============================================================

    const contextInfo =
      msg.message?.extendedTextMessage?.contextInfo;

    const quoted = contextInfo?.quotedMessage;

    if (!quoted) {
      return await sock.sendMessage(
        jid,
        {
          text: '◇ Debes responder a una imagen usando /s o /stickers'
        },
        { quoted: msg }
      );
    }

    // ------------------------------------------------------------
    // Comprobar que lo citado sea una imagen
    // ------------------------------------------------------------

    if (!quoted.imageMessage) {
      return await sock.sendMessage(
        jid,
        {
          text: '◇ El mensaje citado debe contener una imagen.'
        },
        { quoted: msg }
      );
    }

    // ------------------------------------------------------------
    // Crear el mensaje citado correctamente para Baileys
    // ------------------------------------------------------------

    const quotedMsg = {
      key: {
        remoteJid: jid,
        id: contextInfo.stanzaId,
        participant: contextInfo.participant
      },
      message: quoted
    };

    // ------------------------------------------------------------
    // Descargar la imagen
    // ------------------------------------------------------------

    const imageBuffer = await downloadMediaMessage(
      quotedMsg,
      'buffer',
      {}
    );

    if (!imageBuffer || !Buffer.isBuffer(imageBuffer)) {
      return await sock.sendMessage(
        jid,
        {
          text: '◇ No pude descargar la imagen citada.'
        },
        { quoted: msg }
      );
    }

    // ------------------------------------------------------------
    // Obtener nombre del usuario que ejecutó /s
    // ------------------------------------------------------------

    let stickerAuthor =
      msg.pushName ||
      sender?.split('@')[0] ||
      'Usuario';

    stickerAuthor = String(stickerAuthor).trim();

    if (!stickerAuthor) {
      stickerAuthor = 'Usuario';
    }

    // ------------------------------------------------------------
    // Crear sticker
    // ------------------------------------------------------------

    const sticker = new Sticker(imageBuffer, {
      pack: 'SB',
      author: stickerAuthor,
      type: StickerTypes.FULL,
      quality: 90
    });

    const stickerBuffer = await sticker.toBuffer();

    // ------------------------------------------------------------
    // Enviar sticker citando el mensaje que utilizó /s
    // ------------------------------------------------------------

    await sock.sendMessage(
      jid,
      {
        sticker: stickerBuffer
      },
      {
        quoted: msg
      }
    );

    console.log(
      `[STICKER] ${command} | ${stickerAuthor} | ${jid}`
    );

  } catch (error) {
    console.error('[STICKER ERROR]', error);

    try {
      await sock.sendMessage(
        jid,
        {
          text: '◇ Ocurrió un error al crear el sticker.'
        },
        { quoted: msg }
      );
    } catch {}
  }

  break;
}

      case 'hd': {

  let inputBuffer = null;
  let outputBuffer = null;

  try {

    inputBuffer =
      await downloadQuotedImage(
        msg,
        jid,
        sender
      );

    await sock.sendMessage(
      jid,
      { text: '⏳ Mejorando la imagen en HD; puede tardar unos segundos...' },
      { quoted: msg }
    );

    const result =
      await prepareHdImage(
        inputBuffer,
        1600
      );

    outputBuffer =
      result.buffer;

    await sock.sendMessage(
      jid,
      {
        image: outputBuffer,
        caption: buildHdCaption(
          result.originalWidth,
          result.originalHeight,
          result.finalWidth,
          result.finalHeight
        )
      },
      {
        quoted: msg
      }
    );

  } catch (error) {

    console.error(
      '[HD ERROR]',
      error
    );

    await sock.sendMessage(
      jid,
      {
        text: getHdErrorMessage(error)
      },
      {
        quoted: msg
      }
    );

  } finally {

    inputBuffer = null;
    outputBuffer = null;
  }

  break;
}


case 'hd2': {

  let inputBuffer = null;
  let outputBuffer = null;

  try {

    inputBuffer =
      await downloadQuotedImage(
        msg,
        jid,
        sender
      );

    await sock.sendMessage(
      jid,
      { text: '⏳ Procesando la imagen en HD2; puede tardar un poco...' },
      { quoted: msg }
    );

    const result =
      await prepareHdImage(
        inputBuffer,
        4096
      );

    outputBuffer =
      result.buffer;

    await sock.sendMessage(
      jid,
      {
        image: outputBuffer,
        caption: buildHdCaption(
          result.originalWidth,
          result.originalHeight,
          result.finalWidth,
          result.finalHeight
        )
      },
      {
        quoted: msg
      }
    );

  } catch (error) {

    console.error(
      '[HD2 ERROR]',
      error
    );

    await sock.sendMessage(
      jid,
      {
        text: getHdErrorMessage(error)
      },
      {
        quoted: msg
      }
    );

  } finally {

    inputBuffer = null;
    outputBuffer = null;
  }

  break;
}


case 'hd8': {

  let inputBuffer = null;
  let outputBuffer = null;

  try {

    inputBuffer =
      await downloadQuotedImage(
        msg,
        jid,
        sender
      );

    await sock.sendMessage(
      jid,
      { text: '⏳ Generando el archivo HD8. La mejora y el guardado en alta calidad pueden tardar...' },
      { quoted: msg }
    );

    const result =
      await prepareHd8Image(
        inputBuffer
      );

    outputBuffer =
      result.buffer;

    await sock.sendMessage(
      jid,
      {
        document: outputBuffer,
        mimetype: 'image/jpeg',
        fileName: 'imagen-8k.jpg',
        caption: buildHdCaption(
          result.originalWidth,
          result.originalHeight,
          result.finalWidth,
          result.finalHeight
        )
      },
      {
        quoted: msg
      }
    );

  } catch (error) {

    console.error(
      '[HD8 ERROR]',
      error
    );

    await sock.sendMessage(
      jid,
      {
        text: getHdErrorMessage(error)
      },
      {
        quoted: msg
      }
    );

  } finally {

    inputBuffer = null;
    outputBuffer = null;
  }

  break;
}
      case 'trade': await handleTrade(sock, msg, args, jid, sender); break;
    case 'bodyguard': {
      await handleBodyguard(sock, msg, sender);
      break;
    }
    case 'guards': {
      await handleGuards(sock, msg, sender, mentioned, quotedJid);
      break;
    }
    case 'robwaifu': {
      await handleRobWaifu(sock, msg, args, jid, sender);
      break;
    }
      case 'rob': {

  const target =
    mentioned?.[0];

  if (!target) {
    return sock.sendMessage(jid,{
      text:'Uso: /rob 20% @usuario'
    },{ quoted: msg });
  }

  if (target === sender) {
    return sock.sendMessage(jid,{
      text:'No puedes robarte a ti mismo.'
    },{ quoted: msg });
  }

  const porcentaje =
    parseInt(
      args[0]?.replace('%','')
    );

  if (![10,20,50,100].includes(porcentaje)) {
    return sock.sendMessage(jid,{
      text:
`Porcentajes permitidos:

10%
20%
50%
100%`
    },{ quoted: msg });
  }

  const eco =
    getGroupEconomy(
      jid,
      sender
    );

  const targetEco =
    getGroupEconomy(
      jid,
      target
    );

  const cd =
    20 * 60 * 1000;

  const left =
    cd -
    (
      Date.now() -
      (eco.lastRob || 0)
    );

  if (left > 0) {
    return sock.sendMessage(jid,{
      text:
`Debes esperar ${formatTime(left)} para volver a robar.`
    },{ quoted: msg });
  }

  eco.lastRob = Date.now();

  const success =
    porcentaje === 100
      ? 1
      : 30;

  const rnd =
    Math.random() * 100;

  if (rnd > success) {

    return sock.sendMessage(jid,{
      text:
`❌ El robo falló.

La policï¿½a te descubriï¿½ y escapaste con las manos vacï¿½as.`
    },{ quoted: msg });
  }

  const stolen =
    Math.floor(
      targetEco.coins *
      (porcentaje / 100)
    );

  if (stolen <= 0) {
    return sock.sendMessage(jid,{
      text:'El usuario no tiene coins.'
    },{ quoted: msg });
  }

  targetEco.coins -= stolen;
  eco.coins += stolen;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`?? ¡Robo exitoso!

Robaste ${stolen.toLocaleString()} Coins.

Porcentaje robado:
${porcentaje}%`,
    mentions:[target]
  },{ quoted: msg });

  break;
}
      case 'bal': await handleBal(sock, msg, jid, sender, mentioned); break;
      case 'einfo': await handleEinfo(sock, msg, jid, sender); break;
      case 'deposit': await handleDeposit(sock, msg, args, jid, sender); break;
      case 'd': await handleD(sock, msg, args, jid, sender); break;
      case 'withdraw': await handleWithdraw(sock, msg, args, jid, sender); break;
      case 'w': await handleWork(sock, msg, jid, sender); break;
      case 'mine': await handleMine(sock, msg, jid, sender); break;
      case 'owner?': await handleOwnerCheck(sock, msg, jid, sender, mentioned); break;
      case 'owner': await handleSetOwner(sock, msg, jid, sender); break;

case 'setbotowner': {
  await handleSetBotOwner(
    sock,
    msg,
    sender,
    args
  );
  break;
}
case 'setbotcurrency': {
    await handleSetBotCurrency(
        sock,
        msg,
        sender,
        args
    );
    break;
}
case 'logout': {
        await handleLogout(sock, msg, sender, args);
        break;
      }

case 'topcmd':
  await handleTopCmd(sock, msg, args);
  break;

      case 'setprimary': {

  // ==================================================
  // /SETPRIMARY V9
  // ==================================================
  // Permite establecer como bot primario:
  //
  // 1. Bot principal actual
  // 2. Bot presente en activeBots
  // 3. Subbot registrado en db.subBots
  // 4. Mención
  // 5. Respuesta
  //
  // ==================================================

  // --------------------------------------------------
  // SOLO GRUPOS
  // --------------------------------------------------

  if (!jid.endsWith('@g.us')) {

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ Este comando solo puede usarse en grupos.'
      },
      { quoted: msg }
    );

  }

  // ==================================================
  // PERMISOS
  // ==================================================

  let isGroupAdmin = false;

  try {

    const metadata =
      await sock.groupMetadata(jid);

    const participant =
      metadata.participants.find(
        p =>
          p?.id === sender ||
          p?.jid === sender
      );

    isGroupAdmin =
      participant?.admin === 'admin' ||
      participant?.admin === 'superadmin' ||
      participant?.admin === true;

  } catch (e) {

    console.log(
      'ERROR ADMIN /SETPRIMARY:',
      e.message
    );

  }

  const hasSecondaryPermission =
    Array.isArray(globalThis.SECONDARY_OWNERS)
      ? globalThis.SECONDARY_OWNERS.includes(sender)
      : (
          typeof SECONDARY_OWNERS !== 'undefined' &&
          Array.isArray(SECONDARY_OWNERS) &&
          SECONDARY_OWNERS.includes(sender)
        );

  if (
    !isOwner &&
    !hasSecondaryPermission &&
    !isGroupAdmin
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ Solo los administradores del grupo, el owner principal o los secondary owners pueden usar /setprimary.'
      },
      { quoted: msg }
    );

  }

  // ==================================================
  // NORMALIZADORES
  // ==================================================

  const normalizeJid = value => {

    if (!value) return '';

    return String(value)
      .trim()
      .replace(/:.*(?=@)/, '')
      .replace(/@c\.us$/i, '@s.whatsapp.net');

  };

  const getNumber = value => {

    return normalizeJid(value)
      .replace(/@.*$/, '')
      .replace(/[^0-9]/g, '');

  };

  // ==================================================
  // ARGUMENTOS
  // ==================================================

  const rawArgs =
    typeof args !== 'undefined'
      ? (
          Array.isArray(args)
            ? args
            : String(args || '')
                .trim()
                .split(/\s+/)
        )
      : [];

  const firstArg =
    String(rawArgs[0] || '')
      .trim()
      .toLowerCase();

  const requestedMain =
    firstArg === 'principal' ||
    firstArg === 'main' ||
    firstArg === 'mainbot' ||
    firstArg === 'botprincipal';

  // ==================================================
  // OBTENER MENCIÓN / RESPUESTA
  // ==================================================

  const contextInfo =
    msg.message?.extendedTextMessage?.contextInfo;

  const mentionedJids =
    contextInfo?.mentionedJid || [];

  const repliedParticipant =
    contextInfo?.participant || null;

  const target =
    repliedParticipant ||
    mentionedJids[0] ||
    null;

  console.log('========================================');
  console.log('SETPRIMARY V9');
  console.log('========================================');
  console.log('ARGS:', rawArgs);
  console.log('FIRST ARG:', firstArg);
  console.log('REQUESTED MAIN:', requestedMain);
  console.log('TARGET:', target);
  console.log('GRUPO:', jid);
  console.log('========================================');

  // ==================================================
  // IDENTIDAD DEL BOT ACTUAL
  // ==================================================

  const runningBotJid =
    normalizeJid(sock.user?.id);

  const runningBotNumber =
    getNumber(runningBotJid);

  const runningBotLid =
    normalizeJid(sock.user?.lid);

  const runningBotLidNumber =
    getNumber(runningBotLid);

  console.log(
    '◆ BOT EJECUTANDO:',
    runningBotJid
  );

  console.log(
    '◆ BOT NUMBER:',
    runningBotNumber
  );

  console.log(
    '◆ BOT LID:',
    runningBotLid
  );

  // ==================================================
  // SI SE ESCRIBIÓ /setprimary principal
// ==================================================
// /setprimary principal 1
//
// El principal se obtiene automáticamente desde
// globalThis.MAIN_BOT_SOCK.
//
// NO utiliza:
// - número escrito manualmente
// - mención
// - cita
// - identidad del subbot que ejecuta el comando
// ==================================================

if (
  requestedMain &&
  String(rawArgs[1] || '').trim() === '1'
) {

  console.log('========================================');
  console.log('SETPRIMARY PRINCIPAL AUTO');
  console.log('========================================');

  const mainSock =
    globalThis.MAIN_BOT_SOCK;

  // ------------------------------------------------
  // COMPROBAR QUE INDEX.JS PRINCIPAL ESTÁ ACTIVO
  // ------------------------------------------------

  if (
    !mainSock ||
    !mainSock.user ||
    !mainSock.user.id
  ) {

    console.log(
      '❌ BOT PRINCIPAL NO ACTIVO'
    );

    return sock.sendMessage(
      jid,
      {
        text:
          ' El bot principal no está activo.\\n\\n' +
          'Inicia el index.js principal y vuelve a usar:\\n' +
          '/setprimary principal 1'
      },
      { quoted: msg }
    );
  }

  const mainBotJid =
    String(mainSock.user.id)
      .trim()
      .replace(/:.*(?=@)/, '')
      .replace(/@c\\.us$/i, '@s.whatsapp.net');

  const mainBotNumber =
    mainBotJid
      .replace(/@.*$/, '')
      .replace(/[^0-9]/g, '');

  console.log(
    '◆ MAIN BOT JID:',
    mainBotJid
  );

  console.log(
    '◆ MAIN BOT NUMBER:',
    mainBotNumber
  );

  // ------------------------------------------------
  // COMPROBAR QUE EL PRINCIPAL ESTÁ EN EL GRUPO
  // ------------------------------------------------

  let metadata;

  try {

    metadata =
      await mainSock.groupMetadata(jid);

  } catch (e) {

    console.log(
      '❌ ERROR OBTENIENDO METADATA:',
      e.message
    );

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ No pude comprobar la presencia del bot principal en este grupo.'
      },
      { quoted: msg }
    );
  }

  const principalInGroup =
    metadata?.participants?.some(participant => {

      const values = [
        participant?.id,
        participant?.jid,
        participant?.phoneNumber,
        participant?.lid
      ].filter(Boolean);

      return values.some(value => {

        const number =
          String(value)
            .trim()
            .replace(/:.*(?=@)/, '')
            .replace(/@.*$/, '')
            .replace(/[^0-9]/g, '');

        return (
          number &&
          mainBotNumber &&
          number === mainBotNumber
        );
      });

    });

  if (!principalInGroup) {

    console.log(
      '❌ BOT PRINCIPAL NO ESTÁ EN EL GRUPO'
    );

    return sock.sendMessage(
      jid,
      {
        text:
          ' El bot principal no está en este grupo.\\n\\n' +
          'El index.js principal debe estar dentro del grupo para establecerlo como primary.'
      },
      { quoted: msg }
    );
  }

  // ------------------------------------------------
  // GUARDAR PRINCIPAL
  // ------------------------------------------------

  db.primaryBots ??= {};

  db.primaryBots[jid] =
    mainBotJid;

  saveDB();

  console.log(
    '⭐ PRIMARY GUARDADO:',
    mainBotJid
  );

  console.log(
    '⭐ GRUPO:',
    jid
  );

  console.log('========================================');

  return sock.sendMessage(
    jid,
    {
      text:
        '✐ Bot principal establecido correctamente.\\n' +
        '> Principal » ' +
        mainBotJid
    },
    { quoted: msg }
  );
}

// ==================================================
// /setprimary principal SIN 1
// ==================================================

if (
  requestedMain &&
  !target &&
  String(rawArgs[1] || '').trim() !== '1'
) {

  return sock.sendMessage(
    jid,
    {
      text:
        '❌ Formato incorrecto.\\n\\n' +
        'Usa:\\n' +
        '/setprimary principal 1'
    },
    { quoted: msg }
  );
}

// SI NO HAY TARGET
  // ==================================================

  if (!target) {

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ Responde al mensaje del bot o menciona al bot que deseas establecer como primary.'
      },
      { quoted: msg }
    );

  }

  // ==================================================
  // TARGET
  // ==================================================

  let targetNormalized =
    normalizeJid(target);

  let targetNumber =
    getNumber(targetNormalized);

  console.log(
    '◆ TARGET ORIGINAL:',
    target
  );

  console.log(
    '◆ TARGET NORMALIZADO:',
    targetNormalized
  );

  console.log(
    '◆ TARGET NUMBER INICIAL:',
    targetNumber
  );

  // ==================================================
  // METADATA DEL GRUPO
  // ==================================================

  let metadata = null;

  try {

    metadata =
      await sock.groupMetadata(jid);

  } catch (e) {

    console.log(
      'ERROR METADATA /SETPRIMARY:',
      e.message
    );

  }

  // ==================================================
  // RESOLVER @LID
  // ==================================================

  if (
    targetNormalized
      .toLowerCase()
      .endsWith('@lid') &&
    metadata?.participants
  ) {

    const participant =
      metadata.participants.find(p => {

        const ids = [
          p?.id,
          p?.jid,
          p?.phoneNumber,
          p?.lid
        ]
          .filter(Boolean)
          .map(normalizeJid);

        return ids.includes(
          targetNormalized
        );

      });

    if (participant) {

      console.log(
        '• PARTICIPANTE @LID:',
        JSON.stringify(participant)
      );

      const possibleValues = [
        participant.phoneNumber,
        participant.jid,
        participant.id
      ];

      for (const value of possibleValues) {

        if (!value) continue;

        const normalized =
          normalizeJid(value);

        if (
          !normalized ||
          normalized
            .toLowerCase()
            .endsWith('@lid')
        ) {
          continue;
        }

        const number =
          getNumber(normalized);

        if (number) {

          targetNumber = number;

          targetNormalized =
            normalized;

          console.log(
            '◆ @LID RESUELTO:',
            normalized
          );

          console.log(
            '◆ TARGET NUMBER RESUELTO:',
            targetNumber
          );

          break;

        }

      }

    }

  }

  // ==================================================
  // BUSCAR BOT
  // ==================================================

  let selectedJid = null;
  let selectedSource = null;

  const findBotByNumber = number => {

    if (!number) return null;

    const wanted =
      String(number)
        .replace(/[^0-9]/g, '');

    if (!wanted) return null;

    // ------------------------------------------------
    // 1. BOT PRINCIPAL ACTUAL
    // ------------------------------------------------

    if (
      runningBotNumber &&
      runningBotNumber === wanted
    ) {

      return {
        jid: runningBotJid,
        source: 'BOT PRINCIPAL ACTUAL'
      };

    }

    // ------------------------------------------------
    // 2. ACTIVE BOTS
    // ------------------------------------------------

    if (
      typeof activeBots !== 'undefined' &&
      activeBots
    ) {

      try {

        if (
          typeof activeBots.entries === 'function'
        ) {

          for (
            const [botJid, botSock]
            of activeBots.entries()
          ) {

            const possibleJid =
              normalizeJid(
                botSock?.user?.id ||
                botJid
              );

            const botNumber =
              getNumber(possibleJid);

            if (
              botNumber &&
              botNumber === wanted
            ) {

              console.log(
                '✓ BOT ENCONTRADO EN activeBots:',
                possibleJid
              );

              return {
                jid: possibleJid,
                source: 'ACTIVE BOTS'
              };

            }

          }

        } else if (
          typeof activeBots === 'object'
        ) {

          for (
            const [botJid, botSock]
            of Object.entries(activeBots)
          ) {

            const possibleJid =
              normalizeJid(
                botSock?.user?.id ||
                botJid
              );

            const botNumber =
              getNumber(possibleJid);

            if (
              botNumber &&
              botNumber === wanted
            ) {

              console.log(
                '✓ BOT ENCONTRADO EN activeBots:',
                possibleJid
              );

              return {
                jid: possibleJid,
                source: 'ACTIVE BOTS'
              };

            }

          }

        }

      } catch (e) {

        console.log(
          '⚠️ ERROR BUSCANDO activeBots:',
          e.message
        );

      }

    }
 
       // ------------------------------------------------
    // 3. SUBBOTS EN active.json
    // ------------------------------------------------

    try {

      const activeFile =
        path.join(
          process.cwd(),
          'subbot-system',
          'active.json'
        );

      if (fs.existsSync(activeFile)) {

        const activeData =
          JSON.parse(
            fs.readFileSync(
              activeFile,
              'utf8'
            )
          );

        for (
          const [phone, subBot]
          of Object.entries(activeData || {})
        ) {

          const values = [
            phone,
            subBot?.phone,
            subBot?.number,
            subBot?.jid,
            subBot?.id,
            subBot?.user?.id
          ];

          for (const value of values) {

            if (!value) continue;

            const normalized =
              normalizeJid(value);

            const botNumber =
              getNumber(normalized);

            if (
              botNumber &&
              botNumber === wanted
            ) {

              /*
               * IMPORTANTE:
               * Usar el JID REAL guardado en active.json.
               *
               * Ejemplo:
               * 50688526491:11@s.whatsapp.net
               *
               * NO convertirlo simplemente a:
               * 50688526491@s.whatsapp.net
               */

              let realJid =
                normalizeJid(
                  subBot?.jid ||
                  value
                );

              if (
                !realJid.includes('@')
              ) {

                realJid =
                  realJid +
                  '@s.whatsapp.net';

              }

              realJid =
                normalizeJid(realJid);

              console.log(
                '✓ SUBBOT ENCONTRADO EN active.json:',
                realJid
              );

              console.log(
                '   PHONE:',
                phone
              );

              console.log(
                '   NOMBRE:',
                subBot?.name ||
                'desconocido'
              );

              console.log(
                '   ROL:',
                subBot?.role ||
                'desconocido'
              );

              console.log(
                '   OWNER:',
                subBot?.owner ||
                'desconocido'
              );

              return {
                jid: realJid,
                realJid,
                source: 'ACTIVE.JSON',
                data: subBot
              };

            }

          }

        }

      }

    } catch (e) {

      console.log(
        '⚠️ ERROR BUSCANDO active.json:',
        e.message
      );

    }

    // ------------------------------------------------
    // 3. DB.SUBBOTS
    // ------------------------------------------------

    if (
      db &&
      db.subBots &&
      typeof db.subBots === 'object'
    ) {

      try {

        for (
          const [phone, subBot]
          of Object.entries(db.subBots)
        ) {

          const values = [
            phone,
            subBot?.phone,
            subBot?.number,
            subBot?.jid,
            subBot?.id,
            subBot?.user?.id
          ];

          for (const value of values) {

            if (!value) continue;

            const normalized =
              normalizeJid(value);

            const botNumber =
              getNumber(normalized);

            if (
              botNumber &&
              botNumber === wanted
            ) {

              let finalJid =
                normalized;

              if (
                !finalJid.includes('@')
              ) {

                finalJid =
                  finalJid +
                  '@s.whatsapp.net';

              }

              finalJid =
                normalizeJid(finalJid);

              console.log(
                '✓ SUBBOT ENCONTRADO EN db.subBots:',
                finalJid
              );

              return {
                jid: finalJid,
                source: 'DB.SUBBOTS'
              };

            }

          }

        }

      } catch (e) {

        console.log(
          '⚠️ ERROR BUSCANDO db.subBots:',
          e.message
        );

      }

    }

    return null;

  };

  // ==================================================
  // RESOLVER BOT
  // ==================================================

  const found =
    findBotByNumber(targetNumber);

  if (found) {

    selectedJid =
      normalizeJid(found.jid);

    selectedSource =
      found.source;

  }

  // ==================================================
  // FALLBACK DIRECTO PARA SUBBOT
  // ==================================================

  if (
    !selectedJid &&
    targetNumber &&
    db?.subBots
  ) {

    const possibleKey =
      Object.keys(db.subBots)
        .find(key =>
          getNumber(key) === targetNumber
        );

    if (possibleKey) {

      selectedJid =
        normalizeJid(
          possibleKey.includes('@')
            ? possibleKey
            : possibleKey +
              '@s.whatsapp.net'
        );

      selectedSource =
        'DB.SUBBOTS KEY';

      console.log(
        '✓ SUBBOT ENCONTRADO POR KEY:',
        selectedJid
      );

    }

  }

  // ==================================================
  // SI NO SE ENCONTRÓ
  // ==================================================

  if (!selectedJid) {

    console.log(
      '❌ BOT NO ENCONTRADO:',
      targetNumber
    );

    return sock.sendMessage(
      jid,
      {
        text:
          '❌ No pude identificar el bot seleccionado.\n' +
          '◇ N¿mero detectado » ' +
          targetNumber +
          '\n\n' +
          'Responde directamente al mensaje del bot e inténtalo nuevamente.'
      },
      { quoted: msg }
    );

  }

  // ==================================================
  // GUARDAR PRIMARY
  // ==================================================

  db.primaryBots ??= {};

  const previousPrimary =
    normalizeJid(
      db.primaryBots[jid] || ''
    );

  db.primaryBots[jid] =
    selectedJid;

  saveDB();

  const changed =
    previousPrimary !== selectedJid;

  console.log(
    '========================================'
  );

  console.log(
    '⭐ SETPRIMARY GUARDADO'
  );

  console.log(
    '◇ TARGET:',
    target
  );

  console.log(
    '◇ NUMBER:',
    targetNumber
  );

  console.log(
    '◇ JID:',
    selectedJid
  );

  console.log(
    '◇ ORIGEN:',
    selectedSource
  );

  console.log(
    '◇ PRIMARY ANTERIOR:',
    previousPrimary || 'NINGUNO'
  );

  console.log(
    '◇ CAMBIO REAL:',
    changed
  );

  console.log(
    '========================================'
  );

  const mention =
    '@' + targetNumber;

  return sock.sendMessage(
    jid,
    {
      text:
        '✐ Se ha establecido a ' +
        mention +
        ' como bot primario de este grupo.\n' +
        '> Todos los comandos del grupo serán ejecutados por este bot.',
      mentions: [
        selectedJid
      ]
    },
    { quoted: msg }
  );

}

  break;



      case 'slut': await handleSlut(sock, msg, jid, sender); break;
      case 'crime': await handleCrime(sock, msg, jid, sender); break;
      case 'daily': await handleDaily(sock, msg, jid, sender); break;
      case 'sell': await handleSell(sock, msg, args, jid, sender); break;
      case 'time': await handleTime(sock, msg, args, jid, sender); break;
      case 'cf': await handleCf(sock, msg, args, jid, sender); break;
      case 'reg': {

  if (!isOwner) {
    return sock.sendMessage(jid,{
      text:'Solo los owners pueden usar este comando.'
    },{ quoted: msg });
  }

  const num =
    parseInt(args[0]);

  if (isNaN(num) || num < 0) {
    return sock.sendMessage(jid,{
      text:'Uso: /reg 828'
    },{ quoted: msg });
  }

  db.registeredUsers = num;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`✓ Usuarios registrados actualizados.

Nuevo valor:
${num}`
  },{ quoted: msg });

  break;
}
      case 'reggp': {

  if (!isOwner) {
    return sock.sendMessage(jid,{
      text:'Solo los owners pueden usar este comando.'
    },{ quoted: msg });
  }

  const num =
    parseInt(args[0]);

  if (isNaN(num) || num < 0) {
    return sock.sendMessage(jid,{
      text:'Uso: /reggp 25'
    },{ quoted: msg });
  }

  db.registeredGroups = num;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`✓ Grupos registrados actualizados.

Nuevo valor:
${num}`
  },{ quoted: msg });

  break;
}
      case 'status': await handleStatus(sock, msg); break;
      case 'lid':
        await handleLid(sock, msg, args);
        break;
      case 'addstatus':
        await handleAddStatus(
          sock,
          msg,
          args,
          mentioned,
          quotedJid,
          sender
        );
        break;
      case 'delstatus':
        await handleDelStatus(
          sock,
          msg,
          args,
          mentioned,
          quotedJid,
          sender
        );
        break;
      case 'bots': await handleBots(sock, msg); break;
      case 'code':
  await handleCode(sock, msg, sender, args, "code");
  break;
      case 'codeqr':
  await handleCode(sock, msg, sender, args, "qr");
  break;
      case 'delpj': {

if (!isOwner) {
  return sock.sendMessage(jid,{
    text:'Solo el owner puede usar este comando.'
  },{ quoted: msg });
}

const nombre = args.join(' ').trim();

if (!nombre) {
  return sock.sendMessage(jid, {
    text: '◇ Uso: /delpj [nombre]'
  }, { quoted: msg });
}

const index = charactersCache.findIndex(
  c => c.name.toLowerCase() === nombre.toLowerCase()
);

if (index === -1) {
  return sock.sendMessage(jid, {
    text: '❌ Personaje no encontrado.'
  }, { quoted: msg });
}

const personaje = charactersCache[index];

charactersCache.splice(index, 1);

characterMap.delete(
  personaje.name.toLowerCase()
);

characterKeyMap.delete(
  personaje.key
);

saveCharacters();

await sock.sendMessage(jid, {
  text:
`✓ Personaje eliminado

• ${personaje.name}
📺 ${personaje.anime}`
}, { quoted: msg });

break;
}
      case 'staffcomand': {

  const cmd =
    args[0]?.toLowerCase();

  if (!cmd) {
    return sock.sendMessage(jid,{
      text:
`Comandos staff:

${(db.staffCommands || []).join('\n') || 'Ninguno'}`
    },{ quoted: msg });
  }

  db.staffCommands ??= [];

  if (!db.staffCommands.includes(cmd)) {
    db.staffCommands.push(cmd);
  }

  saveDB();

  await sock.sendMessage(jid,{
    text:`✓ ${cmd} agregado a staff.`
  },{ quoted: msg });

  break;
}     case 'staffdenied': {

  if (!isMainOwner) return;

  const cmd =
    args[0]?.toLowerCase();

  if (!cmd) {
    return sock.sendMessage(jid,{
      text:'Uso: /staffdenied comando'
    },{ quoted: msg });
  }

  db.staffCommands =
    (db.staffCommands || [])
      .filter(x => x !== cmd);

  saveDB();

  await sock.sendMessage(jid,{
    text:`✓ ${cmd} volvió a ser público.`
  },{ quoted: msg });

  break;
}
      case 'staffprefix': {

  if (!isMainOwner) return;

  let target =
    msg.message?.extendedTextMessage?.contextInfo?.participant ||
    mentioned?.[0];

  if (
    !target &&
    isMainOwner
  ){
    target = sender;
  }

  const pref =
    args[args.length - 1];

  if (!target || !pref) {
    return sock.sendMessage(jid,{
      text:
`Uso:
/staffprefix @usuario ☆

También puedes responder
a un mensaje del usuario.`
    },{ quoted: msg });
  }

  db.staffPrefixes ??= {};

  db.staffPrefixes[target] = pref;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`*Dueño:* @${target.split('@')[0]}
*Prefijo:* ${pref}
> Cancela tu prefijo con /delprefix`,
    mentions:[target]
  },{ quoted: msg });

  break;
}

      case 'delprefix': {

  db.staffPrefixes ??= {};

  const currentPrefix =
    db.staffPrefixes[sender];

  if (!currentPrefix) {

    return sock.sendMessage(jid,{
      text:
        '♤ No tienes un prefijo personalizado.\n\n' +
        '▪︎ Tu prefijo actual » `/`'
    },{ quoted: msg });

  }

  delete db.staffPrefixes[sender];

  saveDB();

  await sock.sendMessage(jid,{
    text:
      '♤ Prefijo eliminado.\n\n' +
      '▪︎ Prefijo actual » `/`\n' +
      '> Ahora puedes usar nuevamente los comandos con /.'
  },{ quoted: msg });

  break;
}
      case 'botinfo':
  await handleBotInfo(
    sock,
    msg
  );
  break;
case 'setbanner': await handleSetBanner(sock, msg); break;
      case 'gp':
  await handleGp(sock, msg, jid);
break;
      case 'setbotprefix': await handleSetPrefix(sock, msg, args); break;
      case 'addsong':
        await songGame.handleAddSong(sock, msg, args, sender, prefix);
        break;
      case 'addsongaudio':
        await songGame.handleAddSongAudio(sock, msg, args, prefix);
        break;
      case 'song':
        await songGame.handleSong(sock, msg, jid, sender);
        break;
      case 'infousuario': await handleInfousuario(sock, msg, mentioned, quotedJid, jid); break;
      case 'gp': await handleGp(sock, msg, jid); break;
      case 'pfp': await handlePfp(sock, msg, mentioned); break;
      case 'slist': await handleSlist(sock, msg, args); break;
      case 'mergeserie':
  await handleMergeSerie(
    sock,
    msg,
    args,
    sender
  );
  break;
      case 'ainfo': await handleAinfo(sock, msg, args, jid); break;
      case 'delserie':
await handleDelSerie(
  sock,
  msg,
  args,
  sender
);
break;
      case 'setserie':
await handleSetSerie(
  sock,
  msg,
  args,
  sender
);
break;

      case 'addalias':
await handleAddAlias(
  sock,
  msg,
  args,
  sender
);
break;

case 'delnameserie':
await handleDelNameSerie(
  sock,
  msg,
  args,
  sender
);
break;

case 'infoserie':
await handleInfoSerie(
  sock,
  msg,
  args,
  sender
);
break;
case 'idserie':
await handleIdSerie(
  sock,
  msg,
  args,
  sender
);
break;
      case 'creatinglogs': {

  if (!isOwner) {
    return;
  }

  const mode =
    (args[0] || '')
      .toLowerCase()
      .trim();

  if (mode === 'on') {

    db.creatingLogs = jid;

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
' Creating Logs activado en este grupo.\n\n> Los personajes creados serï¿½n registrados aquï¿½.'
      },
      {
        quoted: msg
      }
    );

  } else if (mode === 'off') {

    db.creatingLogs = null;

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
'✓ Creating Logs desactivado.'
      },
      {
        quoted: msg
      }
    );

  } else {

    await sock.sendMessage(
      jid,
      {
        text:
'Uso: /creatinglogs on | off'
      },
      {
        quoted: msg
      }
    );

  }

  break;

}

case 'suggestlogs': {

  if (!isOwner) return;

  const mode =
    (args[0] || '').toLowerCase();

  if (mode === 'on') {

    db.suggestLogs = jid;

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
'✓ Suggest Logs activado en este grupo.'
      },
      { quoted: msg }
    );

  } else if (mode === 'off') {

    db.suggestLogs = null;

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
'✓ Suggest Logs desactivado.'
      },
      { quoted: msg }
    );

  } else {

    await sock.sendMessage(
      jid,
      {
        text:
'Uso: /suggestlogs on | off'
      },
      { quoted: msg }
    );

  }

  break;
}

case 'invitelogs': {

  if (!OWNER_NUMBER.includes(sender)) return;

  const mode =
    (args[0] || '').toLowerCase();

  if (mode === 'on') {

    db.inviteLogs = jid;

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
`☆ Invite Logs activado ☆`
      },
      { quoted: msg }
    );

  } else if (mode === 'off') {

    db.inviteLogs = null;

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
`☆ Invite Logs desactivado ☆`
      },
      { quoted: msg }
    );

  } else {

    await sock.sendMessage(
      jid,
      {
        text:
`○ Uso:
 /invitelogs on
 /invitelogs off`
      },
      { quoted: msg }
    );

  }

  break;
}

case 'invite': {

  const link = args[0];

  if (!link || !link.includes('chat.whatsapp.com/')) {
    return sock.sendMessage(
      jid,
      {
        text:
` Envia un enlace válido.`
      },
      { quoted: msg }
    );
  }

  if (!db.inviteLogs) {
    return sock.sendMessage(
      jid,
      {
        text:
` Las solicitudes están desactivadas.`
      },
      { quoted: msg }
    );
  }

  let code = '';

  try {
    const match = link.match(
      /chat\.whatsapp\.com\/([A-Za-z0-9_-]+)/i
    );

    code = match?.[1]?.trim() || '';
  } catch {
    code = '';
  }

  if (!code) {
    return sock.sendMessage(
      jid,
      {
        text: '□ No se pudo extraer el c¿digo de invitaci¿n.'
      },
      { quoted: msg }
    );
  }

  db.pendingInvites[code] = {
    code,
    user: sender,
    time: Date.now()
  };

  saveDB();

  await sock.sendMessage(
    db.inviteLogs,
    {
      text:
`☆ NUEVA INVITACIÓN ☆

○ Usuario:
@${sender.split('@')[0]}

□ Grupo:
${link}

¤ /acept
¤ /denied`,
      mentions:[sender]
    }
  );

  break;
}

case 'acept': {

  if (!isOwner) return;

  const keys =
    Object.keys(db.pendingInvites || {});

  const code =
    keys[keys.length - 1];

  if (!code) {
    return sock.sendMessage(
      jid,
      {
        text:
        `○ No hay invitaciones pendientes.`
      },
      { quoted: msg }
    );
  }

  try {

    await sock.groupAcceptInvite(code);

    delete db.pendingInvites[code];

    saveDB();

    await sock.sendMessage(
      jid,
      {
        text:
        `☆ Invitación aceptada ☆`
      },
      { quoted: msg }
    );

  } catch (e) {

    console.log("ERROR ACEPT INVITE:", e);

    await sock.sendMessage(
      jid,
      {
        text:
        `□ No se pudo aceptar la invitaci¿n.\\n\\n${e.message || e}`
      },
      { quoted: msg }
    );

  }

  break;
}

case 'denied': {

  if (!isOwner) return;

  const keys =
    Object.keys(db.pendingInvites || {});

  const code =
    keys[keys.length - 1];

  if (code) {
    delete db.pendingInvites[code];
    saveDB();
  }

  await sock.sendMessage(
    jid,
    {
      text:
      `☆ Invitación rechazada ☆`
    },
    { quoted: msg }
  );

  break;
}

      case 'suggest': {

  const text =
    args.join(' ').trim();

  await handleSuggest(
    sock,
    msg,
    sender,
    text
  );

  break;
}
      case 'report':

  await handleSuggest(
    sock,
    msg,
    args,
    sender
  );

break;
      case 'ginfo': await handleGinfo(sock, msg, jid, sender); break;
      case 'toprachas':
case 'topdaily': {

  await handleTopRachas(
    sock,
    msg,
    args
  );

  break;
}
      case 'topcoinsg':
await handleTopCoinsG(
  sock,
  msg,
  args,
  jid
);
break;
      case 'ainfocoinsg':
await handleAinfoCoinsG(
  sock,
  msg,
  args,
  sender
);
break;
      case 'settag':
  await handleSetTag(
    sock,
    msg,
    args,
    sender
  );
break;
      case 'fixtag':
await handleFixTag(
  sock,
  msg,
  args,
  sender
);
break;
      case 'topcoinschar':
await handleTopCoinsChar(
  sock,
  msg,
  args
);
break;

      case 'stainfo':
      case 'staffinfo':

        await handleStaffInfo(
          sock,
          msg,
          args,
          sender
        );

      break;

      case 'seriec':

        await handleSerieC(
          sock,
          msg,
          args,
          sender
        );

      break;

      case 'topstaffgacha':
  await handleTopStaffGacha(
    sock,
    msg,
    args
  );
break;
      case 'top':
    await handleTop(sock, jid, msg, args);
break;     
      case 'delbirth': {

const user = initUser(sender);

user.birthday = null;

saveDB();

await sock.sendMessage(jid,{
text:
'「✐」Se ha eliminado tu cumplea¿os correctamente.'
},{quoted:msg});

break;
}
      case 'setbirth': {

const input = args.join(' ').trim().toLowerCase();
const monthsEs = ['enero','febrero','marzo','abril','mayo','junio','julio','agosto','septiembre','octubre','noviembre','diciembre'];
const monthsEn = ['january','february','march','april','may','june','july','august','september','october','november','december'];
const weekdays = ['domingo','lunes','martes','miércoles','jueves','viernes','sábado'];
const daysInMonth = [31,29,31,30,31,30,31,31,30,31,30,31];
let day = 0;
let month = 0;

let match = input.match(/^(\d{1,2})\s*[\/\-.]\s*(\d{1,2})(?:\s*[\/\-.]\s*\d{2,4})?$/);
if (match) {
  day = Number(match[1]);
  month = Number(match[2]);
} else {
  match = input.match(/^(\d{1,2})\s*(?:de\s+)?([a-záéíóú]+)$/);
  if (match) {
    day = Number(match[1]);
    const monthName = match[2];
    month = monthsEs.indexOf(monthName) + 1 || monthsEn.indexOf(monthName) + 1;
  }
}

if (!month || month < 1 || month > 12 || day < 1 || day > daysInMonth[month - 1]) {
  await sock.sendMessage(jid,{
    text:
      'Debes ingresar una fecha válida para tu cumpleaños.\n\n' +
      'Ejemplos: /setbirth 24/02, /setbirth 24 de febrero o /setbirth 1 january'
  },{quoted:msg});
  break;
}

const user = initUser(sender);
user.birthday = { day, month };
saveDB();

const today = new Date();
today.setHours(0, 0, 0, 0);
let nextBirthday = null;
for (let yearOffset = 0; yearOffset < 9; yearOffset++) {
  const candidate = new Date(today.getFullYear() + yearOffset, month - 1, day);
  if (
    candidate.getMonth() === month - 1 &&
    candidate.getDate() === day &&
    candidate >= today
  ) {
    nextBirthday = candidate;
    break;
  }
}
const dateLabel =
  (nextBirthday ? weekdays[nextBirthday.getDay()] + ', ' : '') +
  day + ' de ' + monthsEs[month - 1];

await sendAnimatedEdit(
  sock,
  jid,
  msg,
  '「✐」Se ha establecido tu cumpleaños en *' + dateLabel + '*'
);

break;
}
      case 'delgenre': {

const user = initUser(sender);

user.gender = null;

saveDB();

await sock.sendMessage(jid,{
text:'✐ Se ha eliminado tu g¿nero'
},{quoted:msg});

break;
}
      case 'setgenre': {

const gender =
(args.join(' ') || '')
.toLowerCase()
.trim();

const valid = [
'mujer',
'hombre',
'femboy',
'tomboy',
'no binario'
];

if (!valid.includes(gender)) {

return sock.sendMessage(jid,{
text:
`《✧》Debes ingresar un g¿nero valido.

> Ejemplo » *#setgenre hombre*`
},{quoted:msg});

}

const user = initUser(sender);

user.gender = gender;

saveDB();

await sendAnimatedEdit(
  sock,
  jid,
  msg,
  '✐ Se ha establecido tu género en *' + gender + '*!'
);

break;
}
     case 'marry': {

const target =
  mentioned?.[0] ||
  msg.message?.extendedTextMessage
    ?.contextInfo
    ?.participant;

const user = initUser(sender);

if (!target) {

return sock.sendMessage(jid,{
text:
'《✧》Debes mencionar o responder a un usuario.'
},{ quoted: msg });

}

const partner =
  initUser(target);

if (user.marriedTo) {

return sock.sendMessage(jid,{
text:'Ya estás casado.'
},{ quoted: msg });

}

if (partner.marriedTo) {

return sock.sendMessage(jid,{
text:'Ese usuario ya está casado.'
},{ quoted: msg });

}

/* ACEPTAR */

if (
user.marryRequest === target
) {

user.marriedTo = target;
partner.marriedTo = sender;

user.marryRequest = null;

saveDB();

await sock.sendMessage(
jid,
{
text:
`✩.･:｡≻───── ⋆♡⋆ ─────.•:｡✩
¡Se han Casado! ฅ^•ﻌ•^ฅ*:･ﾟ✧

•.¸a Esposa @${sender.split('@')[0]} a¸.•

•.¸a Esposa @${target.split('@')[0]} a¸.•

\`Disfruten de su luna de miel\`

✩.･:｡≻───── ⋆♡⋆ ─────.•`,
mentions:[
sender,
target
]
},
{ quoted: msg }
);

break;
}

/* PROPUESTA */

partner.marryRequest =
  sender;

saveDB();

await sock.sendMessage(
jid,
{
text:
`♡ @${target.split('@')[0]}, @${sender.split('@')[0]} te ha propuesto matrimonio, ¿aceptas? •(=^●ω●^=)•

> ✐ Aceptar » *#marry* @${sender.split('@')[0]}`,
mentions:[
sender,
target
]
},
{ quoted: msg }
);

break;
} 
     case 'divorce': {

const user =
  initUser(sender);

if (!user.marriedTo) {

return sock.sendMessage(jid,{
text:'No estás casado.'
},{ quoted: msg });

}

const partner =
  initUser(
    user.marriedTo
  );

const ex =
  user.marriedTo;

user.marriedTo = null;
partner.marriedTo = null;

saveDB();

await sock.sendMessage(
jid,
{
text:
`✐ @${sender.split('@')[0]} y @${ex.split('@')[0]} se han divorciado.`,
mentions:[
sender,
ex
]
},
{ quoted: msg }
);

break;
}
     case 'profile': {

const target =
  mentioned?.[0] ||
  msg.message?.extendedTextMessage
    ?.contextInfo
    ?.participant ||
  sender;

await handleProfile(
  sock,
  msg,
  jid,
  target
);

break;
}
      case 'tin':
  await handleTin(
    sock,
    msg,
    jid,
    sender
  );
  break;
      case 'lvl': case 'level': await handleLvl(sock, jid, msg, sender); break;
      case 'recalclvl': {

  if (!isMainOwner) return;

  for (const id in db.users) {

    const user = db.users[id];

    let level = 1;

    while (
      user.xp >= xpForLevel(level + 1)
    ) {
      level++;
    }

    user.level = level;
  }

  saveDB();

  await sock.sendMessage(jid,{
    text:'✓ Todos los niveles fueron recalculados.'
  },{ quoted: msg });

  break;
}
      case 'resetlvl': {

  if (!isMainOwner) return;

  let target = args[0];

  if (!target) {
    return sock.sendMessage(jid,{
      text:
`Uso:
${prefix}resetlvl 56912345678
${prefix}resetlvl 183938399@lid`
    },{ quoted: msg });
  }

  if (/^\d+$/.test(target)) {
    target = target + '@s.whatsapp.net';
  }

  if (!db.users[target]) {
    return sock.sendMessage(jid,{
      text:'❌ Usuario no encontrado en la base de datos.'
    },{ quoted: msg });
  }

  db.users[target].xp = 0;
  db.users[target].level = 1;

  saveDB();

  await sock.sendMessage(jid,{
    text:
`✓ Nivel reiniciado

• ${target}

☆ XP: 0
☆ Nivel: 1`
  },{ quoted: msg });

  break;
}
      case 'modlvltransf': {
  if (!isOwner) return;

  const oldId = args[0];
  const newId = args[1];

  if (!oldId || !newId) {
    return sock.sendMessage(
      msg.key.remoteJid,
      {
        text:
`Uso:
${prefix}modlvltransf viejo nuevo

Ejemplo:
${prefix}modlvltransf 39604497432739@lid 56956461451@s.whatsapp.net`
      },
      { quoted: msg }
    );
  }

  let transferred = 0;

  // USERS
  if (db.users?.[oldId]) {
    db.users[newId] = JSON.parse(
      JSON.stringify(db.users[oldId])
    );
  }

  // GRUPOS
  for (const groupId of Object.keys(db.groups || {})) {

    const group = db.groups[groupId];

    // ECONOMIA
    if (group.economy?.[oldId]) {
      group.economy[newId] = JSON.parse(
        JSON.stringify(group.economy[oldId])
      );
    }

    // COOLDOWNS
    if (group.cooldowns?.[oldId]) {
      group.cooldowns[newId] = JSON.parse(
        JSON.stringify(group.cooldowns[oldId])
      );
    }

    // HAREM
    if (group.harems?.[oldId]) {
      group.harems[newId] = JSON.parse(
        JSON.stringify(group.harems[oldId])
      );
    }

    transferred++;
  }

  // CHARACTERS.JSON
  let chars = 0;

  for (const char of charactersCache) {

    if (!char.claimedBy) continue;

    for (const gid of Object.keys(char.claimedBy)) {

      const claim = char.claimedBy[gid];

      if (claim?.user === oldId) {
        claim.user = newId;
        chars++;
      }
    }
  }

  saveCharacters();
  saveDB();

  await sock.sendMessage(
    msg.key.remoteJid,
    {
      text:
`✓ Transferencia completada

Viejo:
${oldId}

Nuevo:
${newId}

Grupos revisados: ${transferred}
Personajes transferidos: ${chars}`
    },
    { quoted: msg }
  );

  break;
}
      case 'tradelvl': {

  const target =
    msg.message?.extendedTextMessage?.contextInfo?.participant ||
    mentioned?.[0];

  if (!target) {
    return sock.sendMessage(jid,{
      text:'Uso: /tradelvl @usuario'
    },{ quoted: msg });
  }

  if (target === sender) {
    return sock.sendMessage(jid,{
      text:'No puedes intercambiar tu nivel contigo mismo.'
    },{ quoted: msg });
  }

  const userA = initUser(sender);
  const userB = initUser(target);

  if (userA.level < 100) {
    return sock.sendMessage(jid,{
      text:'Necesitas ser nivel 100 para usar este comando.'
    },{ quoted: msg });
  }

  if (userB.level < 100) {
    return sock.sendMessage(jid,{
      text:'El usuario debe ser nivel 100 o superior.'
    },{ quoted: msg });
  }

  const tradeId = Date.now().toString();

  pendingLevelTrades[tradeId] = {
    from: sender,
    to: target,
    fromLevel: userA.level,
    toLevel: userB.level,
    expires: Date.now() + 60000
  };

setTimeout(() => {

  delete pendingLevelTrades[tradeId];

}, 60000);

  const sent = await sock.sendMessage(jid,{
    text:
`「✎」 @${target.split('@')[0]}, @${sender.split('@')[0]} te ha enviado una solicitud de intercambio de nivel.

☆ [@${sender.split('@')[0]}]
└ Nivel actual: ${userA.level}

☆ [@${target.split('@')[0]}]
└ Nivel actual: ${userB.level}

⚠ Ambos usuarios intercambiar¿n completamente sus niveles.

✎ Para aceptar responde a este mensaje con "Aceptar".

La solicitud expira en 60 segundos.`,
    mentions:[sender,target]
  },{ quoted: msg });

  pendingLevelTrades[tradeId].messageId =
    sent.key.id;

  break;
}
      case 'xpluck': {

if (!isOwner) {
  return sock.sendMessage(jid,{
    text:'Solo los owners pueden usar este comando.'
  },{ quoted: msg });
}

const raw = String(args.join(' ')).toLowerCase().replace(/[\/|,]/g, ' ');
const groupIdMatch = raw.match(/\bid\s*[:#]?\s*(\d+)/);
const multipliers = [...raw.matchAll(/\bx\s*(\d+(?:\.\d+)?)/g)]
  .map(match => Number(match[1]));
const remaining = raw
  .replace(/\bid\s*[:#]?\s*\d+/g, ' ')
  .replace(/\bx\s*\d+(?:\.\d+)?/g, ' ');
const durations = [...remaining.matchAll(/(\d+)\s*(m|h)(?![a-z])/g)]
  .map(match => ({
    ms: Number(match[1]) * (match[2] === 'h' ? 3600000 : 60000),
    label: match[1] + match[2]
  }));
const multiplier = multipliers[0];
const luckMultiplier = multipliers[1] || 1;
const duration = durations[0];
const delay = durations[1];

if (!multiplier || multiplier < 1 || !duration?.ms) {
  return sock.sendMessage(jid,{
    text:'Uso: /xpluck x2 20m x5 [id 282] [20m]\n\nx2 = multiplicador de XP\n20m = duración del evento\nx5 = multiplicador de suerte en /rw\nid 282 = grupo (opcional, ver /gruposbots)\núltimo 20m = en cuánto empieza (opcional)'
  },{ quoted: msg });
}

let targetGroupId = jid;
if (groupIdMatch) {
  const groupNumber = Number(groupIdMatch[1]);
  const found = Object.keys(db.groupNums || {})
    .find(group => db.groupNums[group] === groupNumber);
  if (!found) {
    return sock.sendMessage(jid,{
      text:'No existe el id ' + groupNumber + '. Usa /gruposbots para ver los ids.'
    },{ quoted: msg });
  }
  targetGroupId = found;
} else if (!String(jid).endsWith('@g.us')) {
  return sock.sendMessage(jid,{
    text:'Escríbelo en un grupo o usa id. Ejemplo: /xpluck x2 20m x5 id 282'
  },{ quoted: msg });
}

const eventSock = targetGroupId === jid
  ? sock
  : await resolveSockForGroup(targetGroupId);
if (!eventSock) {
  return sock.sendMessage(jid,{
    text:'Ningún bot conectado está en ese grupo ahora mismo.'
  },{ quoted: msg });
}

const delayMs = delay ? delay.ms : 0;
const startsAt = Date.now() + delayMs;
const durationMinutes = Math.round(duration.ms / 60000);
db.groups[targetGroupId] ??= {};
db.groups[targetGroupId].events2 = true;
db.groups[targetGroupId].event = {
  multiplier,
  luck: luckMultiplier,
  startsAt,
  expires: startsAt + duration.ms,
  minutes: durationMinutes,
  announced: delayMs === 0
};
await saveDB();

await sock.sendMessage(jid,{
  text:
    '•­─【 XP BOOST 〕─◆\n\n' +
    'Grupo: ' + (db.groupNames?.[targetGroupId] || targetGroupId) + '\n' +
    'XP: x' + multiplier + '\n' +
    'Suerte /rw: x' + luckMultiplier + '\n' +
    'Duración: ' + duration.label + '\n' +
    (delay ? 'Empieza en: ' + delay.label + '\n' : 'Empieza: ahora\n') +
    '\nEvento ' + (delay ? 'programado' : 'activado') + ' (events2 ON en ese grupo).\n\n' +
    '•°────────◆'
},{ quoted: msg });

if (delayMs === 0) {
  void announceXpEvent(eventSock, targetGroupId, multiplier, luckMultiplier, durationMinutes);
}

break;
}

case 'events2': {
  if (!isOwner) {
    return sock.sendMessage(jid,{
      text:'Solo el owner puede usar este comando.'
    },{ quoted: msg });
  }
  if (!String(jid).endsWith('@g.us')) {
    return sock.sendMessage(jid,{
      text:'Este comando solo funciona en grupos.'
    },{ quoted: msg });
  }

  const option = String(args[0] || '').toLowerCase();
  if (option !== 'on' && option !== 'off') {
    return sock.sendMessage(jid,{
      text:'Uso: /events2 on | /events2 off'
    },{ quoted: msg });
  }

  db.groups[jid] ??= {};
  db.groups[jid].events2 = option === 'on';
  saveDB();
  await sock.sendMessage(jid,{
    text: option === 'on'
      ? '✅ Avisos de eventos activados en este grupo.'
      : '❌ Avisos de eventos desactivados en este grupo.'
  },{ quoted: msg });
  break;
}

case 'gruposbots': {
  if (!isMainOwner) {
    return sock.sendMessage(jid,{
      text:'Solo el owner principal puede usar este comando.'
    },{ quoted: msg });
  }

  await sock.sendMessage(jid,{ text:'⏳ Consultando grupos de todos los bots...' },{ quoted: msg });
  const result = await buildGroupIndex();
  if (!result.list.length) {
    return sock.sendMessage(jid,{
      text:'No encontré grupos.' + (result.errors.length ? '\n' + result.errors.join('\n') : '')
    },{ quoted: msg });
  }

  await sock.sendMessage(jid,{
    text:'•­─【 GRUPOS 〕─◆\nTotal: ' + result.list.length + '\nUsa: /xpluck x10 20m x2 id NUMERO\n•°────────◆'
  },{ quoted: msg });

  let chunk = '';
  for (const group of result.list) {
    const line =
      '*' + group.num + '* » ' + group.name + '\n' +
      '   🤖 ' + [...new Set(group.bots)].join(', ') + '\n' +
      '   🔗 ' + (group.link || 'sin link (bot no admin)') + '\n\n';
    if ((chunk + line).length > 3000) {
      await sock.sendMessage(jid,{ text:chunk });
      chunk = '';
    }
    chunk += line;
  }
  if (chunk) await sock.sendMessage(jid,{ text:chunk });
  if (result.errors.length) {
    await sock.sendMessage(jid,{ text:'⚠️ Bots con error:\n' + result.errors.join('\n') });
  }
  break;
}

case 'anti-isn':
  await handleAntiIsn(
    sock,
    msg,
    args,
    jid,
    sender
  );
  break;

      case 'baltop': await handleBaltop(sock, msg, args); break;
      case 'baltopgp': await handleBaltopgp(sock, msg, args); break;
      case 'rangs':
        await handleStaffRanks(sock, msg);
        break;
      case 'topstatus':
        await handleTopStatus(sock, msg, args);
        break;
      case 'addrang': {
        if (!isMainOwner) {
          await sock.sendMessage(
            jid,
            { text: '❌ Solo el owner principal puede usar este comando.' },
            { quoted: msg }
          );
          break;
        }

        const rankMatch = String(body || "")
          .trim()
          .match(/^\/addrang\s+(.+?)\s*\/\s*(\d+)\s*$/i);

        if (!rankMatch) {
          await sock.sendMessage(
            jid,
            { text: '◇ Uso: /addrang nombre del rango / status\n\nEjemplo: /addrang Staff Mítico / 750000' },
            { quoted: msg }
          );
          break;
        }

        const rankName = rankMatch[1].trim();
        const minimumStatus = Number(rankMatch[2]);
        const ranks = getStaffRanks();
        const existingRank = ranks.find(
          rank => rank.name.toLowerCase() === rankName.toLowerCase()
        );

        db.staffRanks = ranks.filter(
          rank => rank.name.toLowerCase() !== rankName.toLowerCase()
        );
        db.staffRanks.push({
          name: rankName,
          min: minimumStatus
        });
        db.staffRanks.sort((a, b) => a.min - b.min);
        saveDB();

        await sock.sendMessage(
          jid,
          {
            text:
              `${existingRank ? '✅ Rango actualizado.' : '✅ Rango agregado.'}\n\n` +
              `☆ ${rankName}\n> Requiere: ${minimumStatus.toLocaleString()} status`
          },
          { quoted: msg }
        );
        break;
      }
case 'pay':
  await handlePay(sock, msg, args, sender);
  break;

case 'infodata':
  await handleInfoData(sock, msg, sender);
  break;

case 'menu':
case 'help':
case 'comandos':
  await handleMenuCategoria(sock, msg, args);
  break;
case 'editcomand':
case 'editcommand': {
  if (!isMainOwner) {
    await sock.sendMessage(
      jid,
      { text: '❌ Solo el owner principal puede usar este comando.' },
      { quoted: msg }
    );
    break;
  }

  const editMatch = String(body || '')
    .trim()
    .match(/^\/edit(?:comand|command)\s+([a-z0-9_-]+)(?:\s+\/\s*(.*?))?$/is);

  if (!editMatch || editMatch[1].toLowerCase() !== 'profile') {
    await sock.sendMessage(
      jid,
      {
        text:
          '◇ Uso: /editcomand profile / título / separador\n' +
          '◇ Restablecer: /editcomand profile reset'
      },
      { quoted: msg }
    );
    break;
  }

  const values = (editMatch[2] || '').split('/').map(value => value.trim());
  if (values[0].toLowerCase() === 'reset') {
    delete db.commandDesigns.profile;
    saveDB();
    await sock.sendMessage(jid, { text: '✅ Diseño de /profile restablecido.' }, { quoted: msg });
    break;
  }

  const title = values[0];
  const separator = values.slice(1).join(' / ').trim();
  if (!title || title.length > 80 || separator.length > 200) {
    await sock.sendMessage(
      jid,
      { text: '❌ El título es obligatorio (máximo 80 caracteres) y el separador admite hasta 200.' },
      { quoted: msg }
    );
    break;
  }

  db.commandDesigns.profile = { title, separator };
  saveDB();
  await sock.sendMessage(
    jid,
    { text: `✅ Diseño de /profile actualizado.\n\nTítulo: ${title}\nSeparador: ${separator || '(ninguno)'}` },
    { quoted: msg }
  );
  break;
}
case 'addcomand':
case 'addcommand': {
  if (!isMainOwner) {
    await sock.sendMessage(
      jid,
      { text: '❌ Solo el owner principal puede usar este comando.' },
      { quoted: msg }
    );
    break;
  }

  const escapedPrefix =
    String(prefix || "/")
      .replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const match = String(body || "")
    .trim()
    .match(new RegExp(
      `^${escapedPrefix}(?:addcomand|addcommand)\\s+([^\\s/]+)\\s*\\/\\s*(.*?)\\s*\\/\\s*([^\\s/]+)\\s*$`,
      "is"
    ));

  if (!match) {
    await sock.sendMessage(
      jid,
      {
        text:
          `◇ Uso: ${prefix}addcomand nombre / función o descripción / categoría\n\n` +
          `Ejemplo: ${prefix}addcomand bal / Muestra el saldo del usuario / coins`
      },
      { quoted: msg }
    );
    break;
  }

  const name = match[1].toLowerCase();
  const description = match[2].trim();
  const category = match[3].toLowerCase();

  if (!/^[a-z0-9_-]+$/i.test(name) || !/^[a-z0-9_-]+$/i.test(category)) {
    await sock.sendMessage(
      jid,
      { text: '❌ El nombre y la categoría solo pueden usar letras, números, guion y guion bajo.' },
      { quoted: msg }
    );
    break;
  }

  db.menuCommands ??= {};
  const wasUpdated = Object.prototype.hasOwnProperty.call(
    db.menuCommands,
    name
  );

  db.menuCommands[name] = {
    description,
    category,
    createdAt: wasUpdated
      ? Number(db.menuCommands[name]?.createdAt || Date.now())
      : Date.now()
  };
  saveDB();

  await sock.sendMessage(
    jid,
    {
      text:
        `${wasUpdated ? '✅ Comando actualizado.' : '✅ Comando agregado.'}\n\n` +
        `☆ ${prefix}${name}\n> ${description}\n` +
        `Categoría: ${category}\n\n` +
        'Aparece permanentemente en esa categoría del menú.'
    },
    { quoted: msg }
  );
  break;
}
case 'ownerserie': {
  if (!isMainOwner) {
    await sock.sendMessage(
      jid,
      { text: '❌ Solo el owner principal puede usar este comando.' },
      { quoted: msg }
    );
    break;
  }

  const seriesMatch = String(body || "")
    .trim()
    .match(/^\/ownerserie\s+(.+?)\s*\/\s*@?[0-9]+/is);

  const seriesOwner = mentioned?.[0];

  if (!seriesMatch || !seriesOwner) {
    await sock.sendMessage(
      jid,
      {
        text:
          '◇ Uso: /ownerserie nombre de serie / @mención\n\n' +
          'Ejemplo: /ownerserie One Piece / @usuario'
      },
      { quoted: msg }
    );
    break;
  }

  const seriesName = seriesMatch[1].trim().toLowerCase();
  const seriesExists = seriesCache.has(seriesName);

  if (!seriesExists) {
    await sock.sendMessage(
      jid,
      { text: `❌ No existe la serie: ${seriesMatch[1].trim()}` },
      { quoted: msg }
    );
    break;
  }

  /*
   * ==========================================================
   * OWNER DE SERIE
   * ==========================================================
   *
   * Antes solo se modificaba db.seriesOwners.
   *
   * Ahora también se actualiza char.creator de TODOS los
   * personajes pertenecientes a esta serie.
   */

  db.seriesOwners ??= {};
  db.seriesOwners[seriesName] = seriesOwner;

  let personajesActualizados = 0;

  for (const char of charactersCache) {

    const charAnime =
      String(char.anime || "")
        .toLowerCase()
        .trim();

    if (charAnime === seriesName) {
      if (String(char.creator || "") !== String(seriesOwner)) {
        char.creator = seriesOwner;
        personajesActualizados++;
      }
    }
  }

  saveCharacters();
  saveDB();

  const ownerName =
    db.users?.[seriesOwner]?.name ||
    seriesOwner.split("@")[0] ||
    "Desconocido";

  await sock.sendMessage(
    jid,
    {
      text:
        `》 Owner de la serie actualizado\n\n` +
        `✿ Serie » ${seriesCache.get(seriesName).name}\n` +
        `✿ Usuario » ${ownerName}\n` +
        `✿ Personajes actualizados » ${personajesActualizados}`,
      mentions: [seriesOwner]
    },
    { quoted: msg }
  );

  break;
}
case 'bot': {
  const canControlBot =
    isMainOwnerId(sender) ||
    isSecondaryOwnerId(sender) ||
    (Array.isArray(db.staff) && db.staff.includes(sender));

  if (!canControlBot) {
    return;
  }

  const groupDataLocal = initGroup(jid);
  const action = String(args[0] || '').toLowerCase().trim();

  if (action === 'off') {
    db.botOff = true;
    saveDB();
    await sock.sendMessage(jid, {
      text: '\u25C7 Bot apagado globalmente.'
    }, { quoted: msg });
  }
  else if (action === 'on') {
    db.botOff = false;
    saveDB();
    await sock.sendMessage(jid, {
      text: '\u2606 Bot encendido globalmente.'
    }, { quoted: msg });
  }
  else if (action === 'offgp') {
    groupDataLocal.off = true;
    saveDB();
    await sock.sendMessage(jid, {
      text: '\u25C7 Bot apagado en este grupo.'
    }, { quoted: msg });
  }
  else if (action === 'ongp') {
    groupDataLocal.off = false;
    saveDB();
    await sock.sendMessage(jid, {
      text: '\u2606 Bot encendido en este grupo.'
    }, { quoted: msg });
  }
  else {
    await sock.sendMessage(jid, {
      text: '\u25C7 Uso: /bot off/on/offgp/ongp'
    }, { quoted: msg });
  }

  break;
}
// COMANDO_DESCONOCIDO_V2
      default: {
        const comandoMostrado =
          String(command || "").trim() || "*";

        await sock.sendMessage(
          jid,
          {
            text:
              "•­─☆♤─◇─♡─♧─•®\n" +
              "│ ❖ *" + comandoMostrado + "* no existe.\n" +
              "│ • Usa */help* para ver el men¿.\n" +
              "•°─♧─♡─◇─♤─☆─•¯"
          },
          {
            quoted: msg
          }
        );

        break;
      }

}
}

/* COMMAND_SOURCE_HANDLE_COMMAND_V2_END */



/* =========================================================
 * /LOGOUT
 * ========================================================= */


export async function handleSetBotOwner(
  sock,
  msg,
  sender,
  args
) {

  const jid =
    msg?.key?.remoteJid || "";

  /*
   * ============================================================
   * /SETBOTOWNER V2
   * ============================================================
   *
   * REGLAS:
   *
   * 1. Solo funciona en grupos.
   * 2. El bot que ejecuta el comando debe ser el PRIMARY.
   * 3. El usuario debe ser owner de ESA SESIÓN.
   * 4. El owner inicial es el ownerUser registrado al crear
   *    la sesión mediante /code.
   * 5. Se actualizan active.json y db.subBots.
   *
   * ============================================================
   */

  if (!jid.endsWith("@g.us")) {

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este comando solo puede usarse en grupos."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * ============================================================
   * NORMALIZADORES
   * ============================================================
   */

  const normalizeJid = value => {

    if (!value) return "";

    return String(value)
      .trim()
      .replace(/:.*(?=@)/, "")
      .replace(/@c\\.us$/i, "@s.whatsapp.net");

  };

  const normalizeNumber = value => {

    return normalizeJid(value)
      .replace(/@.*$/, "")
      .replace(/[^0-9]/g, "");

  };

  const sameUser = (a, b) => {

    if (!a || !b) return false;

    const A = normalizeJid(a);
    const B = normalizeJid(b);

    if (A === B) return true;

    const AN = normalizeNumber(A);
    const BN = normalizeNumber(B);

    return (
      AN &&
      BN &&
      AN === BN
    );

  };

  /*
   * ============================================================
   * SENDER REAL
   * ============================================================
   */

  const realSender =
    normalizeJid(
      sender ||
      msg?.key?.participant ||
      msg?.participant ||
      msg?.key?.remoteJid
    );

  console.log("========================================");
  console.log("SETBOTOWNER V2");
  console.log("========================================");
  console.log("GRUPO:", jid);
console.log(
    "SOCKET ID:",
    sock?.user?.id || "sin ID"
  );

  /*
   * ============================================================
   * PRIMARY DEL GRUPO
   * ============================================================
   */

  db.primaryBots ??= {};

  const primaryRaw =
    db.primaryBots[jid];

  if (!primaryRaw) {

    console.log(
      "❌ SETBOTOWNER: el grupo no tiene primary."
    );

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este grupo no tiene un bot primary."
      },
      {
        quoted: msg
      }
    );

  }

  const primaryJid =
    normalizeJid(primaryRaw);

  const socketJid =
    normalizeJid(
      sock?.user?.id
    );

  const primaryNumber =
    normalizeNumber(primaryJid);

  const socketNumber =
    normalizeNumber(socketJid);

  console.log(
    "PRIMARY REGISTRADO:",
    primaryJid
  );

  console.log(
    "SOCKET ACTUAL:",
    socketJid
  );

  /*
   * El socket actual debe ser exactamente el primary.
   */

  if (
    !primaryNumber ||
    !socketNumber ||
    primaryNumber !== socketNumber
  ) {

    console.log(
      "❌ SETBOTOWNER: este socket NO es primary."
    );

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Este bot no es el primary de este grupo."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * ============================================================
   * IDENTIFICAR LA SESIÓN
   * ============================================================
   *
   * Ejemplo:
   *
   * sock.user.id
   * 56964620338:3@s.whatsapp.net
   *
   * phone:
   * 56964620338
   *
   * ============================================================
   */

  const botPhone =
    socketNumber;

  if (!botPhone) {

    console.log(
      "❌ SETBOTOWNER: no se pudo obtener número del socket."
    );

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ No se pudo identificar la sesión de este bot."
      },
      {
        quoted: msg
      }
    );

  }

  console.log(
    "BOT PHONE:",
    botPhone
  );

  /*
   * ============================================================
   * CARGAR active.json
   * ============================================================
   */

  let active = {};

  try {

    if (fs.existsSync(ACTIVE)) {

      active =
        JSON.parse(
          fs.readFileSync(
            ACTIVE,
            "utf8"
          )
        ) || {};

    }

  } catch (e) {

    console.log(
      "⚠️ ERROR LEYENDO active.json:",
      e?.message || e
    );

  }

  /*
   * ============================================================
   * BUSCAR SESIÓN
   * ============================================================
   */

  let activeBot = null;
  let activeKey = null;

  for (
    const [key, value]
    of Object.entries(active || {})
  ) {

    const keyNumber =
      normalizeNumber(key);

    const jidNumber =
      normalizeNumber(value?.jid);

    if (
      keyNumber === botPhone ||
      jidNumber === botPhone
    ) {

      activeBot = value;
      activeKey = key;

      break;

    }

  }

  /*
   * ============================================================
   * BUSCAR EN db.subBots
   * ============================================================
   */

  db.subBots ??= {};

  let dbBot = null;
  let dbKey = null;

  for (
    const [key, value]
    of Object.entries(db.subBots || {})
  ) {

    const keyNumber =
      normalizeNumber(key);

    const valueNumbers = [
      value?.phone,
      value?.number,
      value?.jid,
      value?.id,
      value?.user?.id
    ]
      .filter(Boolean)
      .map(normalizeNumber);

    if (
      keyNumber === botPhone ||
      valueNumbers.includes(botPhone)
    ) {

      dbBot = value;
      dbKey = key;

      break;

    }

  }

  console.log(
    "ACTIVE KEY:",
    activeKey || "NO ENCONTRADO"
  );

  console.log(
    "DB KEY:",
    dbKey || "NO ENCONTRADO"
  );

  /*
   * ============================================================
   * OBTENER OWNER DE LA SESIÓN
   * ============================================================
   *
   * PRIORIDAD:
   *
   * 1. active.json
   * 2. db.subBots
   *
   * Si existe ownerUser, ese es el dueño.
   *
   * NO se utiliza OWNER_NUMBER del bot principal.
   *
   * ============================================================
   */

  const registeredOwner =
    activeBot?.ownerUser ||
    dbBot?.ownerUser ||
    null;

  console.log(
    "OWNER REGISTRADO:",
    registeredOwner || "NINGUNO"
  );

  /*
   * ============================================================
   * SI LA SESIÓN NO TIENE OWNER
   * ============================================================
   *
   * Esto evita que cualquiera pueda apropiarse de una sesión.
   *
   * En una sesión nueva creada con /code, manager.js ya debe
   * guardar ownerUser = sender.
   *
   * ============================================================
   */

  if (!registeredOwner) {

    console.log(
      "❌ SETBOTOWNER: sesión sin ownerUser."
    );

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ Esta sesión no tiene un dueño registrado."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * ============================================================
   * COMPROBAR OWNER
   * ============================================================
   */

  if (
    !sameUser(
      realSender,
      registeredOwner
    )
  ) {

    console.log(
      "❌ SETBOTOWNER: usuario no es owner."
    );

    console.log(
      "SENDER:",
      realSender
    );

    console.log(
      "OWNER:",
      registeredOwner
    );

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ No tienes permiso para usar este comando.\n\n" +
          "Solo el dueño de esta sesión puede cambiar el owner del bot."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * ============================================================
   * OBTENER NUEVO OWNER
   * ============================================================
   */

  const mentioned =
    msg?.message?.extendedTextMessage?.contextInfo?.mentionedJid ||
    [];

  const quotedParticipant =
    msg?.message?.extendedTextMessage?.contextInfo?.participant ||
    null;

  let target =
    mentioned[0] ||
    quotedParticipant ||
    null;

  target =
    normalizeJid(target);

  /*
   * Tambiï¿½n soportamos número escrito como argumento.
   *
   * Ejemplo:
   * /setbotowner 56912345678
   */

  if (!target) {

    const possibleArg =
      Array.isArray(args)
        ? args[1] || args[0]
        : "";

    if (
      possibleArg &&
      /[0-9]{7,15}/.test(
        String(possibleArg)
      )
    ) {

      const digits =
        String(possibleArg)
          .replace(/[^0-9]/g, "");

      target =
        digits +
        "@s.whatsapp.net";

    }

  }

  if (!target) {

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ Menciona o responde al usuario que ser¿ el nuevo due¿o."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * No permitir asignar el bot como owner.
   */

  if (
    sameUser(
      target,
      socketJid
    )
  ) {

    return sock.sendMessage(
      jid,
      {
        text:
          "❌ No puedes asignarle el owner al propio bot."
      },
      {
        quoted: msg
      }
    );

  }

  /*
   * ============================================================
   * NOMBRE DEL BOT
   * ============================================================
   */

  const botName =
    activeBot?.name ||
    dbBot?.name ||
    "Mavis";

  /*
   * ============================================================
   * GUARDAR NUEVO OWNER
   * ============================================================
   */

  const oldOwner =
    normalizeJid(
      registeredOwner
    );

  const newOwner =
    normalizeJid(
      target
    );

  /*
   * DB
   */

  if (dbBot) {

    dbBot.ownerUser =
      newOwner;

  } else {

    /*
     * Si por alguna razón active.json existe pero db.subBots
     * todavï¿½a no tiene la sesiï¿½n, la registramos.
     */

    db.subBots[botPhone] = {

      ownerUser:
        newOwner,

      owner:
        dbBot?.owner ||
        jid,

      folder:
        dbBot?.folder ||
        activeBot?.folder ||
        "",

      name:
        botName,

      role:
        dbBot?.role ||
        activeBot?.role ||
        "Sub",

      status:
        dbBot?.status ||
        "connected",

      lastConnection:
        Date.now()

    };

  }

  /*
   * Si la clave de DB era diferente, también corregimos.
   */

  if (
    dbKey &&
    dbKey !== botPhone &&
    db.subBots[dbKey]
  ) {

    db.subBots[dbKey].ownerUser =
      newOwner;

  }

  saveDB();

  /*
   * ============================================================
   * active.json
   * ============================================================
   */

  try {

    if (activeBot) {

      activeBot.ownerUser =
        newOwner;

      if (activeKey) {

        active[activeKey] =
          activeBot;

      }

    } else {

      /*
       * Si no estaba en active.json pero sï¿½ tenemos informaciï¿½n
       * de DB, creamos su entrada mínima.
       */

      active[botPhone] = {

        ownerUser:
          newOwner,

        name:
          botName,

        role:
          dbBot?.role ||
          "Sub",

        jid:
          socketJid,

        online:
          true,

        owner:
          dbBot?.owner ||
          jid,

        groups:
          []

      };

    }

    fs.mkdirSync(
      path.dirname(ACTIVE),
      {
        recursive: true
      }
    );

    fs.writeFileSync(
      ACTIVE,
      JSON.stringify(
        active,
        null,
        2
      )
    );

    console.log(
      "✓ active.json actualizado."
    );

  } catch (e) {

    console.log(
      "⚠️ ERROR GUARDANDO active.json:",
      e?.message || e
    );

  }

  /*
   * ============================================================
   * RESULTADO
   * ============================================================
   */

  console.log(
    "========================================"
  );

  console.log(
    "✓ SETBOTOWNER COMPLETADO"
  );

  console.log(
    "BOT:",
    botName
  );

  console.log(
    "BOT PHONE:",
    botPhone
  );

  console.log(
    "OWNER ANTERIOR:",
    oldOwner
  );

  console.log(
    "OWNER NUEVO:",
    newOwner
  );

  console.log(
    "========================================"
  );

  return sock.sendMessage(
    jid,
    {
      text:
        "# El dueño del bot " +
        botName +
        " ha sido cambiado de @" +
        oldOwner.split("@")[0] +
        " a @" +
        newOwner.split("@")[0],

      mentions: [
        oldOwner,
        newOwner
      ]

    },
    {
      quoted: msg
    }
  );


  }



export async function handleSetBotCurrency(
  sock,
  msg,
  sender,
  args = []
) {
  const jid = msg.key.remoteJid;

  const normalizeNumber = value =>
    String(value || "")
      .split(":")[0]
      .split("@")[0]
      .replace(/\D/g, "");

  const normalizeJid = value => {
    if (!value) return "";
    return String(value)
      .trim()
      .replace(/:.*(?=@)/, "")
      .replace(/@c\.us$/i, "@s.whatsapp.net");
  };

  const sameUser = (a, b) =>
    normalizeJid(a) === normalizeJid(b);

  /*
   * ============================================================
   * IDENTIFICAR LA SESIÓN ACTUAL
   * ============================================================
   */

  const socketNumber = normalizeNumber(
    sock.user?.id
  );

  const botPhone = socketNumber;

  if (!botPhone) {
    return sock.sendMessage(
      jid,
      {
        text:
          "❌ No se pudo identificar la sesión de este bot."
      },
      {
        quoted: msg
      }
    );
  }

  /*
   * ============================================================
   * CARGAR active.json
   * ============================================================
   */

  const ACTIVE_PATH = "./subbot-system/active.json";

  let active = {};

  try {
    if (fs.existsSync(ACTIVE_PATH)) {
      active =
        JSON.parse(
          fs.readFileSync(
            ACTIVE_PATH,
            "utf8"
          )
        ) || {};
    }
  } catch (e) {
    console.log(
      "⚠️ ERROR LEYENDO active.json:",
      e?.message || e
    );
  }

  /*
   * ============================================================
   * BUSCAR SESIÓN
   * ============================================================
   */

  let activeBot = null;
  let activeKey = null;

  for (
    const [key, value]
    of Object.entries(active || {})
  ) {
    const keyNumber =
      normalizeNumber(key);

    const jidNumber =
      normalizeNumber(value?.jid);

    if (
      keyNumber === botPhone ||
      jidNumber === botPhone
    ) {
      activeBot = value;
      activeKey = key;
      break;
    }
  }

  /*
   * ============================================================
   * BUSCAR EN db.subBots
   * ============================================================
   */

  db.subBots ??= {};

  let dbBot = null;
  let dbKey = null;

  for (
    const [key, value]
    of Object.entries(db.subBots || {})
  ) {
    const keyNumber =
      normalizeNumber(key);

    const valueNumbers = [
      value?.phone,
      value?.number,
      value?.jid,
      value?.id,
      value?.user?.id
    ]
      .filter(Boolean)
      .map(normalizeNumber);

    if (
      keyNumber === botPhone ||
      valueNumbers.includes(botPhone)
    ) {
      dbBot = value;
      dbKey = key;
      break;
    }
  }

  /*
   * ============================================================
   * OBTENER OWNER
   * ============================================================
   */

  const isMainBot =
    sock === globalThis.MAIN_BOT_SOCK ||
    !sock?.__subBotPhone;

  let registeredOwner = null;

  if (isMainBot) {
    /*
     * El bot principal utiliza el sistema de owner principal.
     * No se crea ninguna entrada dentro de db.subBots.
     */
    const senderNumber =
      normalizeNumber(sender);

    const isConfiguredMainOwner =
      isMainOwnerId(sender) ||
      senderNumber === OWNER_CONTACT_NUMBER;

    if (!isConfiguredMainOwner) {
      return sock.sendMessage(
        jid,
        {
          text:
            "❌ No tienes permiso para usar este comando.\n\n" +
            "Solo el dueño del bot principal puede cambiar la moneda."
        },
        {
          quoted: msg
        }
      );
    }
  } else {
    /*
     * Cada subbot utiliza exclusivamente el owner registrado
     * para esa sesión.
     */
    registeredOwner =
      activeBot?.ownerUser ||
      dbBot?.ownerUser ||
      null;

    /*
     * Si todavía no existe owner para esta sesión,
     * el primer usuario que configure la moneda queda
     * registrado como dueño de la sesión.
     */
    if (!registeredOwner) {
      registeredOwner = sender;

      if (activeBot) {
        activeBot.ownerUser = registeredOwner;
      }

      if (dbBot) {
        dbBot.ownerUser = registeredOwner;
      }
    }

    if (!sameUser(sender, registeredOwner)) {
      return sock.sendMessage(
        jid,
        {
          text:
            "❌ No tienes permiso para usar este comando.\n\n" +
            "Solo el dueño de esta sesión puede cambiar la moneda del bot."
        },
        {
          quoted: msg
        }
      );
    }
  }

  /*
   * ============================================================
   * VALIDAR MONEDA
   * ============================================================
   */

  const currency =
    Array.isArray(args)
      ? String(args[0] || "").trim()
      : "";

  if (
    !currency ||
    currency.length < 4 ||
    currency.length > 20
  ) {
    return sock.sendMessage(
      jid,
      {
        text:
`❀《✧》 *ᴅᴇʙᴇs ᴇsᴄʀɪʙɪʀ ᴜɴ ɴᴏᴍʙʀᴇ ᴅᴇ ᴍᴏɴᴇᴅᴀ ᴠáʟɪᴅᴏ › ᴍíɴɪᴍᴏ 4 ⋆ ᴍáxɪᴍᴏ 20 ᴄᴀʀᴀᴄᴛᴇʀᴇs*
> ⟡ ᴇᴊᴇᴍᴘʟᴏ › \`/setbotcurrency 𝙧፝֟𓂃𓈒☆̲⌁. ⌝\``
      },
      {
        quoted: msg
      }
    );
  }

  /*
   * ============================================================
   * MONEDA ANTERIOR
   * ============================================================
   */

  const oldCurrency = isMainBot
    ? (
        String(db.primaryCurrency || "oños").trim() ||
        "oños"
      )
    : (
        dbBot?.currency ||
        activeBot?.currency ||
        "oños"
      );

  /*
   * ============================================================
   * GUARDAR MONEDA
   * ============================================================
   */

  if (isMainBot) {
    /*
     * El bot principal NO es un subbot.
     * Su moneda queda guardada directamente en la base principal.
     */
    db.primaryCurrency = currency;
  } else {
    /*
     * Cada subbot conserva su propia moneda.
     */
    if (dbBot) {
      dbBot.currency = currency;
    } else {
      db.subBots[botPhone] = {
        ownerUser: registeredOwner,
        owner: jid,
        folder: activeBot?.folder || "",
        name: activeBot?.name || "Mavis",
        role: activeBot?.role || "Sub",
        status: activeBot?.status || "connected",
        lastConnection: Date.now(),
        currency
      };
    }

    if (
      dbKey &&
      dbKey !== botPhone &&
      db.subBots[dbKey]
    ) {
      db.subBots[dbKey].currency = currency;
    }

    /*
     * ============================================================
     * GUARDAR active.json
     * ============================================================
     */

    try {
      if (activeBot) {
        activeBot.currency = currency;

        if (activeKey) {
          active[activeKey] = activeBot;
        }
      } else {
        active[botPhone] = {
          ...(active[botPhone] || {}),
          ownerUser: registeredOwner,
          currency
        };
      }

      fs.mkdirSync(
        path.dirname(ACTIVE_PATH),
        {
          recursive: true
        }
      );

      fs.writeFileSync(
        ACTIVE_PATH,
        JSON.stringify(
          active,
          null,
          2
        )
      );
    } catch (e) {
      console.log(
        "⚠️ ERROR GUARDANDO active.json:",
        e?.message || e
      );
    }
  }

  saveDB();

  return sock.sendMessage(
    jid,
    {
      text:
`✐ *ᴍᴏɴᴇᴅᴀ ᴀᴄᴛᴜᴀʟɪᴢᴀᴅᴀ ᴄᴏʀʀᴇᴄᴛᴀᴍᴇɴᴛᴇ*
> ᴀɴᴛᴇʀɪᴏʀ ⇏\`${oldCurrency}\`
> ᴀʜᴏʀᴀ ⇏\`${currency}\``
    },
    {
      quoted: msg
    }
  );
}

export async function handleLogout(
  sock,
  msg,
  sender,
  args = []
){

  const jid =
    msg.key.remoteJid;

  db.subBots ??= {};
  db.primaryBots ??= {};

  const normalizeNumber =
    value =>
      String(value || "")
        .split(":")[0]
        .split("@")[0]
        .replace(/\D/g,"");

  const currentBot =
    normalizeNumber(
      sock.user?.id
    );

  const isPrivate =
    !jid?.endsWith("@g.us");

  const mainOwner =
    String(sender || "") ===
    String(OWNER_NUMBER || "");

  const secondaryOwner =
    Array.isArray(db.secondaryOwners) &&
    db.secondaryOwners.some(
      id =>
        String(id) ===
        String(sender)
    );

  const suppliedPassword =
    String(
      args?.[0] ||
      ""
    ).trim();

  const activeFile =
    path.join(
      process.cwd(),
      "subbot-system",
      "active.json"
    );

  let active = {};
  let activeData = null;
  let activeKey = null;

  try{

    if(fs.existsSync(activeFile)){

      active =
        JSON.parse(
          fs.readFileSync(
            activeFile,
            "utf8"
          )
        ) || {};

    }

  }catch(e){

    console.log(
      "ERROR ACTIVE:",
      e?.message || e
    );

  }

  for(
    const [key,value]
    of Object.entries(active)
  ){

    const keyNumber =
      normalizeNumber(key);

    const jidNumber =
      normalizeNumber(value?.jid);

    if(
      keyNumber === currentBot ||
      jidNumber === currentBot
    ){

      activeKey = key;
      activeData = value;
      break;

    }

  }

  let targetPhone = null;
  let targetData = null;

  for(
    const [phone,data]
    of Object.entries(
      db.subBots || {}
    )
  ){

    const number =
      normalizeNumber(phone);

    const valueNumber =
      normalizeNumber(
        data?.jid ||
        data?.phone ||
        data?.number
      );

    if(
      number === currentBot ||
      valueNumber === currentBot
    ){

      targetPhone = phone;
      targetData = data;
      break;

    }

  }

  if(
    !targetData &&
    activeData
  ){

    targetPhone =
      activeKey;

    targetData =
      activeData;

  }

  if(!targetData){

    return sock.sendMessage(
      jid,
      {
        text:
          " Esta sesiï¿½n no está registrada como subbot."
      },
      { quoted: msg }
    );

  }

  const registeredOwner =
    String(
      targetData?.ownerUser ||
      activeData?.ownerUser ||
      ""
    );

  const storedPassword =
    String(
      targetData?.connectionPassword ||
      targetData?.password ||
      activeData?.connectionPassword ||
      activeData?.password ||
      ""
    );

  const ownerOfThisBot =
    registeredOwner &&
    registeredOwner ===
    String(sender);

  let allowed = false;

  if(mainOwner || secondaryOwner){

    if(
      !suppliedPassword ||
      !storedPassword ||
      suppliedPassword !== storedPassword
    ){

      return sock.sendMessage(
        jid,
        {
          text:
            "◇ Contraseña de conexión incorrecta."
        },
        { quoted: msg }
      );

    }

    allowed = true;

  }
  else if(ownerOfThisBot){

    if(
      suppliedPassword &&
      storedPassword &&
      suppliedPassword !== storedPassword
    ){

      return sock.sendMessage(
        jid,
        {
          text:
            "◇ Contraseña de conexión incorrecta."
        },
        { quoted: msg }
      );

    }

    allowed = true;

  }
  else{

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No tienes permiso para cerrar esta sesión."
      },
      { quoted: msg }
    );

  }

  if(!allowed){

    return sock.sendMessage(
      jid,
      {
        text:
          "◇ No tienes permiso para cerrar esta sesión."
      },
      { quoted: msg }
    );

  }

  const logoutMessage =
    await sock.sendMessage(
      jid,
      {
        text:
          "☆ Cerrando sesión... @" +
          String(sender || "").split("@")[0],
        mentions: [sender]
      },
      { quoted: msg }
    );

  globalThis.SUBBOT_LOGGING_OUT ??= new Set();
  globalThis.SUBBOT_LOGGING_OUT.add(
    String(currentBot)
  );

  sock.__logoutRequested = true;

  try{
    globalThis.SUBBOT_SOCKETS?.delete(
      String(currentBot)
    );
  }catch(e){
    console.log(
      "ERROR ELIMINANDO SOCKET DE LOGOUT:",
      e?.message || e
    );
  }

  if(
    jid?.endsWith("@g.us") &&
    db.primaryBots?.[jid]
  ){

    const primary =
      normalizeNumber(
        db.primaryBots[jid]
      );

    if(
      primary === currentBot
    ){

      let replacementPrimary = "";

      try{
        const replacement =
          Object.entries(active).find(
            ([key, value]) => {

              const keyNumber =
                normalizeNumber(key);

              const valueNumber =
                normalizeNumber(value?.jid);

              return (
                keyNumber &&
                keyNumber !== currentBot &&
                valueNumber !== currentBot &&
                value?.online === true &&
                Array.isArray(value?.groups) &&
                value.groups.includes(jid)
              );
            }
          );

        if(replacement){
          replacementPrimary =
            String(
              replacement[1]?.jid ||
              replacement[0] ||
              ""
            )
              .trim()
              .replace(/:.*(?=@)/, '')
              .replace(/@c\.us$/i, '@s.whatsapp.net');
        }
      }catch(e){
        console.log(
          "ERROR BUSCANDO PRIMARY DE REEMPLAZO:",
          e?.message || e
        );
      }

      if(replacementPrimary){
        db.primaryBots[jid] =
          replacementPrimary;

        console.log(
          "PRIMARY DE REEMPLAZO:",
          jid,
          "→",
          replacementPrimary
        );
      }else{
      delete db.primaryBots[jid];
      }

    }

  }

  try{

    for(
      const [key,value]
      of Object.entries(active)
    ){

      const keyNumber =
        normalizeNumber(key);

      const valueNumber =
        normalizeNumber(value?.jid);

      if(
        keyNumber === currentBot ||
        valueNumber === currentBot
      ){

        delete active[key];

      }

    }

    fs.mkdirSync(
      path.dirname(activeFile),
      { recursive:true }
    );

    fs.writeFileSync(
      activeFile,
      JSON.stringify(
        active,
        null,
        2
      ),
      "utf8"
    );

  }catch(e){

    console.log(
      "ERROR ACTIVE:",
      e?.message || e
    );

  }

  try{

    const sessionFolder =
      targetData?.folder ||
      path.join(
        process.cwd(),
        "subbot-system",
        "sessions",
        "sub_" + currentBot
      );

    if(
      fs.existsSync(sessionFolder)
    ){

      fs.rmSync(
        sessionFolder,
        {
          recursive:true,
          force:true
        }
      );

      console.log(
        "CARPETA ELIMINADA:",
        sessionFolder
      );

    }

  }catch(e){

    console.log(
      "ERROR SESIÓN:",
      e?.message || e
    );

  }

  for(
    const key
    of Object.keys(
      db.subBots || {}
    )
  ){

    if(
      normalizeNumber(key) ===
      currentBot
    ){

      delete db.subBots[key];

    }

  }

  saveDB();

  try{
    if(logoutMessage?.key){
      await sock.sendMessage(
        jid,
        {
          text:
            "☆ Sesion cerrada @" +
            String(sender || "").split("@")[0],
          mentions: [sender]
        },
        {
          edit: logoutMessage.key
        }
      );
    }
  }catch(e){
    console.log(
      "ERROR EDITANDO MENSAJE DE LOGOUT:",
      e?.message || e
    );
  }

  console.log(
    "LOGOUT COMPLETADO:",
    currentBot,
    "POR:",
    sender,
    "PRIVADO:",
    isPrivate
  );

  try{
    if(sock?.ws?.close){
      sock.ws.close();
    }
  }catch(e){
    console.log(
      "ERROR CERRANDO SOCKET DE LOGOUT:",
      e?.message || e
    );
  }

}

/* ============================================================
 * /ADDALIAS - AGREGAR ALIAS A SERIES
 * ============================================================
 */

export async function handleAddAlias(sock, msg, args, sender) {
  const jid = msg.key.remoteJid;

  if (!isMainOwnerId(sender) && !isSecondaryOwnerId(sender)) {
    return sock.sendMessage(jid, {
      text: "◇ Solo los owners pueden usar /addalias."
    }, { quoted: msg });
  }

  const raw = args.join(" ").trim();

  if (!raw) {
    return sock.sendMessage(jid, {
      text: "◇ Uso:\n\n/addalias Serie Oficial / alias1 / alias2\n\nEjemplo:\n\n/addalias Zenless Zone Zero / zzz / zenless"
    }, { quoted: msg });
  }

  const parts = raw.split("/").map(x => x.trim()).filter(Boolean);

  if (parts.length < 2) {
    return sock.sendMessage(jid, {
      text: "◇ Uso: /addalias Serie Oficial / alias1 / alias2"
    }, { quoted: msg });
  }

  const officialInput = parts.shift();
  const officialLower = officialInput.toLowerCase().trim();

  let officialName = null;

  for (const [key, serie] of seriesCache.entries()) {
    if (key === officialLower || String(serie.name || "").toLowerCase() === officialLower) {
      officialName = serie.name;
      break;
    }
  }

  if (!officialName) {
    const found = findSeries(officialInput);
    if (found) officialName = found.name;
  }

  if (!officialName) {
    return sock.sendMessage(jid, {
      text: "◇ La serie \"" + officialInput + "\" no existe en el sistema.\n\n> Verifica con /slist o crea la serie primero."
    }, { quoted: msg });
  }

  db.seriesAliases ??= {};
  db.seriesAliases[officialName] ??= [];

  const added = [];
  const repeated = [];

  for (const alias of parts) {
    const cleanAlias = String(alias || "").toLowerCase().trim();
    if (!cleanAlias) continue;

    if (db.seriesAliases[officialName].includes(cleanAlias)) {
      repeated.push(cleanAlias);
      continue;
    }

    db.seriesAliases[officialName].push(cleanAlias);
    added.push(cleanAlias);
  }

  saveDB();

  let texto = "✓ Alias actualizados\n\n◇ Serie »\n" + officialName + "\n\n□ Alias actuales\n\n" + db.seriesAliases[officialName].map(x => "• " + x).join("\n");

  if (added.length) {
    texto += "\n\n□ Agregados » " + added.length;
  }

  if (repeated.length) {
    texto += "\n◇ Repetidos » " + repeated.length;
  }

  return sock.sendMessage(jid, {
    text: texto
  }, { quoted: msg });
}
