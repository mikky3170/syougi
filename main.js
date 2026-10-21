/* =========================================================
   将棋王 2026 〜 天下統一・戦国決戦 〜
   メインスクリプト（軍略・演出・思考エンジン統合管理）
   ========================================================= */

// AI Web Workerコード（文字列定義：ローカル実行CORS回避のためBlob URL化）
const workerScriptContent = `
const PIECE_CODES = ['OU','HI','KA','KI','GI','KE','KY','FU','RY','UM','NG','NK','NY','TO'];
const VALUES = { OU: 20000, HI: 1050, KA: 880, KI: 580, GI: 480, KE: 380, KY: 280, FU: 100, RY: 1400, UM: 1200, NG: 560, NK: 480, NY: 420, TO: 420 };
const UNPROMOTE_MAP = { RY: 'HI', UM: 'KA', NG: 'GI', NK: 'KE', NY: 'KY', TO: 'FU', HI: 'HI', KA: 'KA', KI: 'KI', GI: 'GI', KE: 'KE', KY: 'KY', FU: 'FU', OU: 'OU' };
const PROMOTE_MAP = { HI: 'RY', KA: 'UM', GI: 'NG', KE: 'NK', KY: 'NY', FU: 'TO' };
const MATE_SCORE = 100000;

let board = [], hands = { PLAYER: {}, AI: {} };
let searchStartTime = 0, searchTimeLimit = 3500, isSearchTimeout = false, nodeCount = 0;
let moveHistory = [], currentLevel = 1;

// レベル別探索設定（Lv.10は真の超深層：静止深さ7・思考時間5000ms）
const LEVEL_CFG = {
  1:  { depth: 1, qDepth: 2, time: 500 },
  2:  { depth: 1, qDepth: 3, time: 700 },
  3:  { depth: 2, qDepth: 3, time: 1000 },
  4:  { depth: 2, qDepth: 4, time: 1400 },
  5:  { depth: 3, qDepth: 4, time: 1900 },
  6:  { depth: 3, qDepth: 5, time: 2400 },
  7:  { depth: 4, qDepth: 5, time: 3000 },
  8:  { depth: 4, qDepth: 6, time: 3500 },
  9:  { depth: 5, qDepth: 6, time: 4000 },
  10: { depth: 5, qDepth: 7, time: 5000 }
};

// 移動可能マス取得（味方のマスは除外）
function getValidBoardMoves(r, c, owner) {
  const item = board[r][c]; if (!item) return [];
  const dir = owner === 'AI' ? 1 : -1, moves = [];
  const canT = (nr, nc) => !board[nr][nc] || board[nr][nc].owner !== owner;
  const ray = dirs => dirs.forEach(([dr, dc]) => {
    let nr = r + dr, nc = c + dc;
    while (nr >= 0 && nr < 9 && nc >= 0 && nc < 9) {
      if (!board[nr][nc]) moves.push({r: nr, c: nc});
      else { if (canT(nr, nc)) moves.push({r: nr, c: nc}); break; }
      nr += dr; nc += dc;
    }
  });
  const step = offs => offs.forEach(([dr, dc]) => {
    const nr = r + dr, nc = c + dc;
    if (nr >= 0 && nr < 9 && nc >= 0 && nc < 9 && canT(nr, nc)) moves.push({r: nr, c: nc});
  });
  const gold = [[dir, -1], [dir, 0], [dir, 1], [0, -1], [0, 1], [-dir, 0]];
  switch(item.code) {
    case 'FU': step([[dir, 0]]); break;
    case 'KY': ray([[dir, 0]]); break;
    case 'KE': step([[dir * 2, -1], [dir * 2, 1]]); break;
    case 'GI': step([[dir, -1], [dir, 0], [dir, 1], [-dir, -1], [-dir, 1]]); break;
    case 'KI': case 'TO': case 'NY': case 'NK': case 'NG': step(gold); break;
    case 'OU': step([[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]); break;
    case 'HI': ray([[-1,0],[1,0],[0,-1],[0,1]]); break;
    case 'KA': ray([[-1,-1],[-1,1],[1,-1],[1,1]]); break;
    case 'RY': ray([[-1,0],[1,0],[0,-1],[0,1]]); step([[-1,-1],[-1,1],[1,-1],[1,1]]); break;
    case 'UM': ray([[-1,-1],[-1,1],[1,-1],[1,1]]); step([[-1,0],[1,0],[0,-1],[0,1]]); break;
  }
  return moves;
}

// 駒の利きマス取得
function getControlSquares(r, c, owner) {
  const item = board[r][c]; if (!item) return [];
  const dir = owner === 'AI' ? 1 : -1, squares = [];
  const ray = dirs => dirs.forEach(([dr, dc]) => {
    let nr = r + dr, nc = c + dc;
    while (nr >= 0 && nr < 9 && nc >= 0 && nc < 9) {
      squares.push({r: nr, c: nc});
      if (board[nr][nc]) break;
      nr += dr; nc += dc;
    }
  });
  const step = offs => offs.forEach(([dr, dc]) => {
    const nr = r + dr, nc = c + dc;
    if (nr >= 0 && nr < 9 && nc >= 0 && nc < 9) squares.push({r: nr, c: nc});
  });
  const gold = [[dir, -1], [dir, 0], [dir, 1], [0, -1], [0, 1], [-dir, 0]];
  switch(item.code) {
    case 'FU': step([[dir, 0]]); break;
    case 'KY': ray([[dir, 0]]); break;
    case 'KE': step([[dir * 2, -1], [dir * 2, 1]]); break;
    case 'GI': step([[dir, -1], [dir, 0], [dir, 1], [-dir, -1], [-dir, 1]]); break;
    case 'KI': case 'TO': case 'NY': case 'NK': case 'NG': step(gold); break;
    case 'OU': step([[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]); break;
    case 'HI': ray([[-1,0],[1,0],[0,-1],[0,1]]); break;
    case 'KA': ray([[-1,-1],[-1,1],[1,-1],[1,1]]); break;
    case 'RY': ray([[-1,0],[1,0],[0,-1],[0,1]]); step([[-1,-1],[-1,1],[1,-1],[1,1]]); break;
    case 'UM': ray([[-1,-1],[-1,1],[1,-1],[1,1]]); step([[-1,0],[1,0],[0,-1],[0,1]]); break;
  }
  return squares;
}

function findKing(owner) {
  for (let r=0; r<9; r++) for (let c=0; c<9; c++) if (board[r][c]?.owner === owner && board[r][c]?.code === 'OU') return {r, c};
  return null;
}

function isCheckState(owner) {
  const kp = findKing(owner);
  if (!kp) return true;
  const kr = kp.r, kc = kp.c, enemy = (owner === 'PLAYER') ? 'AI' : 'PLAYER';
  for (let r=0; r<9; r++) {
    for (let c=0; c<9; c++) {
      if (board[r][c]?.owner === enemy) {
        const moves = getValidBoardMoves(r, c, enemy);
        if (moves.some(m => m.r === kr && m.c === kc)) return true;
      }
    }
  }
  return false;
}

function makeMove(move) {
  const undo = { move };
  const owner = move.owner;
  if (move.type === 'drop') {
    hands[owner][move.code]--;
    board[move.to.r][move.to.c] = { code: move.code, owner };
  } else {
    const item = board[move.from.r][move.from.c], target = board[move.to.r][move.to.c];
    undo.fromCode = item.code;
    if (target) {
      undo.capturedCode = target.code;
      if (target.code !== 'OU') {
        const raw = UNPROMOTE_MAP[target.code];
        hands[owner][raw] = (hands[owner][raw] || 0) + 1;
      }
    }
    if (move.promote) item.code = PROMOTE_MAP[item.code];
    board[move.to.r][move.to.c] = item;
    board[move.from.r][move.from.c] = null;
  }
  return undo;
}

function unmakeMove(undo) {
  const move = undo.move, owner = move.owner;
  if (move.type === 'drop') {
    hands[owner][move.code]++;
    board[move.to.r][move.to.c] = null;
  } else {
    const item = board[move.to.r][move.to.c];
    item.code = undo.fromCode;
    board[move.from.r][move.from.c] = item;
    if (undo.capturedCode) {
      board[move.to.r][move.to.c] = { code: undo.capturedCode, owner: owner === 'AI' ? 'PLAYER' : 'AI' };
      if (undo.capturedCode !== 'OU') hands[owner][UNPROMOTE_MAP[undo.capturedCode]]--;
    } else board[move.to.r][move.to.c] = null;
  }
}

function isUchifuzume(move) {
  if (move.type !== 'drop' || move.code !== 'FU') return false;
  const enemy = move.owner === 'AI' ? 'PLAYER' : 'AI';
  const enemyKing = findKing(enemy);
  if (!enemyKing) return false;
  const fwd = move.owner === 'AI' ? 1 : -1;
  if (move.to.r !== enemyKing.r - fwd || move.to.c !== enemyKing.c) return false;

  const undo = makeMove(move);
  const kingInCheck = isCheckState(enemy);
  if (!kingInCheck) { unmakeMove(undo); return false; }

  const enemyLegals = genLegalMoves(enemy, false, false);
  unmakeMove(undo);
  return enemyLegals.length === 0;
}

// 局面評価関数
function evaluatePosition() {
  let score = 0;
  let pKing = null, aiKing = null;
  const defenseCount = { PLAYER: Array.from({length:9}, () => Array(9).fill(0)), AI: Array.from({length:9}, () => Array(9).fill(0)) };

  for (let r=0; r<9; r++) {
    for (let c=0; c<9; c++) {
      const p = board[r][c]; if (!p) continue;
      const ctrl = getControlSquares(r, c, p.owner);
      ctrl.forEach(m => { defenseCount[p.owner][m.r][m.c]++; });
      if (p.code === 'OU') {
        if (p.owner === 'AI') aiKing = {r, c}; else pKing = {r, c};
      }
    }
  }

  for (let r=0; r<9; r++) {
    for (let c=0; c<9; c++) {
      const p = board[r][c]; if (!p) continue;
      let val = VALUES[p.code] || 0;
      const sign = p.owner === 'AI' ? 1 : -1;
      
      if (p.owner === 'AI') {
        if (currentLevel === 2) {
          if (p.code === 'HI' || p.code === 'KE') val *= 1.15;
          if (p.code === 'HI' && c === 4) score += 45;
        }
        if (currentLevel === 4) {
          if (p.code === 'HI' && c === 2) score += 40;
        }
        if (currentLevel === 6) {
          if (p.code === 'KA' || p.code === 'UM') val *= 1.25;
        }
        if (currentLevel === 8) {
          if (p.code === 'RY' || p.code === 'UM') val *= 1.25;
        }
      }

      score += sign * val;

      if (p.code !== 'OU') {
        const myDefs = defenseCount[p.owner][r][c];
        const opp = p.owner === 'AI' ? 'PLAYER' : 'AI';
        const oppAttacks = defenseCount[opp][r][c];
        if (myDefs > 0) score += sign * 28;
        if (oppAttacks > myDefs) score -= sign * (val * 0.42);
      }

      if (p.code === 'FU' || p.code === 'GI') {
        const advBonus = (currentLevel === 3) ? 18 : 10;
        score += sign * (p.owner === 'AI' ? r * advBonus : (8 - r) * advBonus);
        if (c >= 2 && c <= 6) score += sign * 15;
      }
    }
  }

  const kingGuardBonus = (currentLevel === 10) ? 80 : ((currentLevel === 7) ? 70 : 45);
  if (pKing) {
    let pG = 0;
    for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) {
      const nr = pKing.r + dr, nc = pKing.c + dc;
      if (nr >= 0 && nr < 9 && nc >= 0 && nc < 9) {
        const occ = board[nr][nc];
        if (occ?.owner === 'PLAYER' && ['KI','GI','NG','NK','NY','TO'].includes(occ.code)) pG++;
      }
    }
    score -= pG * kingGuardBonus;
  }
  if (aiKing) {
    let aiG = 0;
    for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) {
      const nr = aiKing.r + dr, nc = aiKing.c + dc;
      if (nr >= 0 && nr < 9 && nc >= 0 && nc < 9) {
        const occ = board[nr][nc];
        if (occ?.owner === 'AI' && ['KI','GI','NG','NK','NY','TO'].includes(occ.code)) aiG++;
      }
    }
    score += aiG * kingGuardBonus;
  }

  const handMul = (currentLevel === 9) ? 1.25 : 1.15;
  for (const c in hands.AI) score += (hands.AI[c] || 0) * (VALUES[c] || 0) * handMul;
  for (const c in hands.PLAYER) score -= (hands.PLAYER[c] || 0) * (VALUES[c] || 0) * 1.15;
  return score;
}

function genLegalMoves(owner, capturesOnly = false, filterUchifuzume = true) {
  const pseudo = [];
  for (let r=0; r<9; r++) {
    for (let c=0; c<9; c++) {
      if (board[r][c]?.owner === owner) {
        const item = board[r][c];
        getValidBoardMoves(r, c, owner).forEach(m => {
          const target = board[m.r][m.c], isCap = (target && target.owner !== owner);
          const inCamp = (owner === 'AI' ? (r >= 6 || m.r >= 6) : (r <= 2 || m.r <= 2));
          const canP = PROMOTE_MAP[item.code] && inCamp;
          const mustP = owner === 'AI' ? ((item.code === 'FU' || item.code === 'KY') && m.r === 8 || (item.code === 'KE' && m.r >= 7))
                                       : ((item.code === 'FU' || item.code === 'KY') && m.r === 0 || (item.code === 'KE' && m.r <= 1));
          if (capturesOnly && !isCap && !canP && !mustP) return;

          if (mustP) pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: true, isCap });
          else if (canP) {
            pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: true, isCap });
            if (!capturesOnly) pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: false, isCap });
          } else pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: false, isCap });
        });
      }
    }
  }

  if (!capturesOnly) {
    for (const code in hands[owner]) if (hands[owner][code] > 0) {
      for (let r=0; r<9; r++) {
        if ((code === 'FU' || code === 'KY') && ((owner === 'AI' && r === 8) || (owner === 'PLAYER' && r === 0))) continue;
        if (code === 'KE' && ((owner === 'AI' && r >= 7) || (owner === 'PLAYER' && r <= 1))) continue;
        for (let c=0; c<9; c++) {
          if (!board[r][c]) {
            if (code === 'FU') {
              let nifu = false;
              for(let kr=0; kr<9; kr++) if (board[kr][c]?.owner === owner && board[kr][c]?.code === 'FU') { nifu = true; break; }
              if (nifu) continue;
            }
            pseudo.push({ type: 'drop', code, to: {r, c}, owner, isCap: false });
          }
        }
      }
    }
  }

  return pseudo.filter(m => {
    if (filterUchifuzume && m.type === 'drop' && m.code === 'FU') {
      if (isUchifuzume(m)) return false;
    }
    const undo = makeMove(m);
    const safe = !isCheckState(owner);
    unmakeMove(undo);
    return safe;
  }).sort((a, b) => (b.isCap ? 1000 : 0) - (a.isCap ? 1000 : 0));
}

function quiescence(alpha, beta, owner, qDepth, maxQ) {
  nodeCount++;
  if ((nodeCount & 511) === 0 && Date.now() - searchStartTime > searchTimeLimit) {
    isSearchTimeout = true; return alpha;
  }

  const inCheck = isCheckState(owner);

  if (!inCheck) {
    const standPat = (owner === 'AI' ? 1 : -1) * evaluatePosition();
    if (qDepth >= maxQ) return standPat;
    if (standPat >= beta) return beta;
    if (alpha < standPat) alpha = standPat;
  }

  const moves = inCheck ? genLegalMoves(owner, false, true) : genLegalMoves(owner, true, true);
  if (inCheck && moves.length === 0) return -MATE_SCORE + qDepth;

  for (let i = 0; i < moves.length; i++) {
    const undo = makeMove(moves[i]);
    const score = -quiescence(-beta, -alpha, owner === 'AI' ? 'PLAYER' : 'AI', qDepth + 1, maxQ);
    unmakeMove(undo);
    if (isSearchTimeout) break;
    if (score >= beta) return beta;
    if (score > alpha) alpha = score;
  }
  return alpha;
}

function negamax(depth, alpha, beta, owner, maxQ) {
  nodeCount++;
  if ((nodeCount & 511) === 0 && Date.now() - searchStartTime > searchTimeLimit) {
    isSearchTimeout = true; return alpha;
  }
  if (depth <= 0) return quiescence(alpha, beta, owner, 0, maxQ);

  const inCheck = isCheckState(owner);
  const moves = genLegalMoves(owner, false, true);
  if (moves.length === 0) return inCheck ? (-MATE_SCORE + (10 - depth)) : 0;

  let bestVal = -Infinity;
  const nextOwner = owner === 'AI' ? 'PLAYER' : 'AI';

  for (let i = 0; i < moves.length; i++) {
    const m = moves[i];
    const undo = makeMove(m);
    let score = -negamax(depth - 1, -beta, -alpha, nextOwner, maxQ);
    unmakeMove(undo);
    if (isSearchTimeout) break;

    if (moveHistory.length >= 2) {
      const last = moveHistory[moveHistory.length - 2];
      if (m.type === 'move' && last.type === 'move' &&
          m.to.r === last.from.r && m.to.c === last.from.c &&
          m.from.r === last.to.r && m.from.c === last.to.c) {
        score -= 220;
      }
    }

    if (score > bestVal) bestVal = score;
    if (score > alpha) alpha = score;
    if (alpha >= beta) break;
  }
  return bestVal;
}

self.onmessage = function(e) {
  const { board: bD, hands: hD, level = 1, isHintRequest = false, isAwakened = false, history = [] } = e.data;
  board = bD; hands = hD; moveHistory = history; currentLevel = level;
  searchStartTime = Date.now(); isSearchTimeout = false; nodeCount = 0;
  const searchOwner = isHintRequest ? 'PLAYER' : 'AI', enemyOwner = isHintRequest ? 'AI' : 'PLAYER';
  const curEval = evaluatePosition();

  let cfg = isHintRequest ? (isAwakened ? { depth: 5, qDepth: 7, time: 5000 } : { depth: 4, qDepth: 5, time: 3000 })
                          : (LEVEL_CFG[level] || LEVEL_CFG[1]);
  searchTimeLimit = cfg.time;

  const legals = genLegalMoves(searchOwner, false, true);
  if (legals.length === 0) {
    self.postMessage({ type: isHintRequest ? 'hintDone' : 'done', bestMove: null, evalScore: curEval });
    return;
  }

  let bestMove = legals[0], maxScore = -Infinity;
  for (let d = 1; d <= cfg.depth; d++) {
    let curBest = null, alpha = -Infinity, beta = Infinity;
    for (let i = 0; i < legals.length; i++) {
      const m = legals[i];
      const undo = makeMove(m);
      let score = -negamax(d - 1, -beta, -alpha, enemyOwner, cfg.qDepth);
      unmakeMove(undo);

      if (moveHistory.length >= 2) {
        const last = moveHistory[moveHistory.length - 2];
        if (m.type === 'move' && last.type === 'move' &&
            m.to.r === last.from.r && m.to.c === last.from.c &&
            m.from.r === last.to.r && m.from.c === last.to.c) {
          score -= 220;
        }
      }

      if (isSearchTimeout) break;
      if (score > alpha) { alpha = score; curBest = m; }
    }
    if (!isSearchTimeout && curBest) {
      bestMove = curBest; maxScore = alpha;
      if (!isHintRequest) self.postMessage({ type: 'progress', depth: d, evalScore: maxScore });
    }
    if (isSearchTimeout || Date.now() - searchStartTime >= searchTimeLimit) break;
  }
  self.postMessage({ type: isHintRequest ? 'hintDone' : 'done', bestMove, evalScore: maxScore, isAwakened });
};
`;

/* =========================================================
   音響エンジン（戦況連動・武将別BGMマネージャー）
   ========================================================= */
let audioCtx = null, soundEnabled = true;
const bgmAudio = document.getElementById('bgm-audio');
if (bgmAudio) bgmAudio.volume = 0.35;

const BGM_TRACKS = {
  normal: 'nobunaga_song.mp3',
  rivalry: 'nobunaga_song.mp3',
  boss: 'nobunaga_song.mp3'
};
let currentBgmTrack = 'normal';

function updateWarlordBGM(level) {
  let targetTrack = 'normal';
  if (level >= 8) targetTrack = 'boss';
  else if (level >= 6) targetTrack = 'rivalry';

  if (currentBgmTrack === targetTrack) return;
  currentBgmTrack = targetTrack;

  if (bgmAudio && soundEnabled) {
    const src = BGM_TRACKS[targetTrack] || 'nobunaga_song.mp3';
    bgmAudio.src = src;
    bgmAudio.play().catch(() => {});
  }
}

let drumInterval = null, drumType = 'normal';
function playTaikoHit(isDon = true) {
  if (!soundEnabled || !audioCtx) return;
  const now = audioCtx.currentTime;
  const osc = audioCtx.createOscillator(), g = audioCtx.createGain();
  osc.type = 'sine';
  osc.frequency.setValueAtTime(isDon ? 120 : 180, now);
  osc.frequency.exponentialRampToValueAtTime(isDon ? 45 : 70, now + 0.18);
  g.gain.setValueAtTime(isDon ? 0.75 : 0.45, now);
  g.gain.exponentialRampToValueAtTime(0.001, now + (isDon ? 0.35 : 0.2));
  osc.connect(g); g.connect(audioCtx.destination);
  osc.start(now); osc.stop(now + (isDon ? 0.35 : 0.2));
}

function updateBattleDrums(status) {
  if (drumType === status && drumInterval) return;
  drumType = status;
  if (drumInterval) { clearInterval(drumInterval); drumInterval = null; }
  if (!soundEnabled) return;

  if (status === 'advantage') {
    drumInterval = setInterval(() => {
      playTaikoHit(true);
      setTimeout(() => playTaikoHit(false), 160);
      setTimeout(() => playTaikoHit(true), 320);
    }, 3200);
  } else if (status === 'pinch') {
    drumInterval = setInterval(() => {
      playTaikoHit(true);
      setTimeout(() => playTaikoHit(false), 120);
    }, 1300);
  }
}

function initAudio() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  if (audioCtx.state === 'suspended') audioCtx.resume();
  startBgm();
}
function startBgm() {
  if (!soundEnabled || !bgmAudio) return;
  bgmAudio.play().catch(() => {});
}
function pauseBgm() {
  if (bgmAudio) bgmAudio.pause();
  if (drumInterval) { clearInterval(drumInterval); drumInterval = null; }
}
function toggleSound() {
  soundEnabled = !soundEnabled;
  document.getElementById('sound-toggle').textContent = `♪ ${soundEnabled ? '音ON' : '音OFF'}`;
  if (soundEnabled) { initAudio(); startBgm(); }
  else { pauseBgm(); }
}
function playPieceSound() {
  if (!soundEnabled) return; initAudio();
  const now = audioCtx.currentTime;
  const osc = audioCtx.createOscillator(), bg = audioCtx.createGain();
  osc.type = 'triangle'; osc.frequency.setValueAtTime(380, now); osc.frequency.exponentialRampToValueAtTime(120, now + 0.07);
  bg.gain.setValueAtTime(0.65, now); bg.gain.exponentialRampToValueAtTime(0.001, now + 0.07);
  osc.connect(bg); bg.connect(audioCtx.destination);
  osc.start(now); osc.stop(now + 0.07);
}
function playCheckSound() {
  if (!soundEnabled) return; initAudio();
  const now = audioCtx.currentTime, osc = audioCtx.createOscillator(), g = audioCtx.createGain();
  osc.type = 'sine'; osc.frequency.setValueAtTime(110, now); osc.frequency.exponentialRampToValueAtTime(38, now + 0.5);
  g.gain.setValueAtTime(0.7, now); g.gain.exponentialRampToValueAtTime(0.001, now + 0.55);
  osc.connect(g); g.connect(audioCtx.destination);
  osc.start(now); osc.stop(now + 0.55);
}
function playVictorySound() {
  if (!soundEnabled) return; initAudio();
  const now = audioCtx.currentTime;
  const melody = [{f:220,t:0.0,d:0.18},{f:261,t:0.16,d:0.18},{f:293,t:0.32,d:0.22},{f:392,t:0.52,d:0.30},{f:440,t:0.78,d:0.75}];
  melody.forEach(m => {
    const osc = audioCtx.createOscillator(), g = audioCtx.createGain();
    osc.type = 'sawtooth'; osc.frequency.setValueAtTime(m.f, now + m.t);
    g.gain.setValueAtTime(0.0, now + m.t); g.gain.linearRampToValueAtTime(0.25, now + m.t + 0.03);
    g.gain.exponentialRampToValueAtTime(0.001, now + m.t + m.d);
    osc.connect(g); g.connect(audioCtx.destination);
    osc.start(now + m.t); osc.stop(now + m.t + m.d);
  });
}

function triggerCutin(text, isSpecial = false, isRivalry = false) {
  playPieceSound();
  const slot = document.getElementById('cutin-slot'), banner = document.getElementById('cutin-banner'), textEl = document.getElementById('cutin-text');
  textEl.textContent = text;
  banner.classList.toggle('rivalry', isRivalry);
  slot.classList.add('cutin-active');
  setTimeout(() => slot.classList.remove('cutin-active'), isSpecial ? 3500 : (isRivalry ? 3000 : 1800));
}

/* 祝勝花火 */
const canvasCelebration = document.getElementById('celebration-canvas');
const ctxCelebration = canvasCelebration.getContext('2d');
let celebrationParticles = [];
function launchFireworksCelebration() {
  canvasCelebration.width = window.innerWidth; canvasCelebration.height = window.innerHeight;
  celebrationParticles = [];
  for (let i = 0; i < 90; i++) {
    celebrationParticles.push({
      x: canvasCelebration.width / 2, y: canvasCelebration.height * 0.4,
      vx: (Math.random() - 0.5) * 10, vy: (Math.random() - 0.5) * 10,
      col: ['#ffd700', '#ff3b30', '#ffffff', '#ff9500'][Math.floor(Math.random() * 4)],
      alpha: 1, size: Math.random() * 3 + 2
    });
  }
  let startTime = Date.now();
  function loop() {
    ctxCelebration.clearRect(0, 0, canvasCelebration.width, canvasCelebration.height);
    celebrationParticles.forEach(p => {
      p.x += p.vx; p.y += p.vy; p.vy += 0.08; p.alpha -= 0.015;
      if (p.alpha > 0) {
        ctxCelebration.fillStyle = p.col; ctxCelebration.globalAlpha = p.alpha;
        ctxCelebration.beginPath(); ctxCelebration.arc(p.x, p.y, p.size, 0, Math.PI * 2); ctxCelebration.fill();
      }
    });
    if (Date.now() - startTime < 3500) requestAnimationFrame(loop);
    else ctxCelebration.clearRect(0, 0, canvasCelebration.width, canvasCelebration.height);
  }
  loop();
}

/* =========================================================
   武将・軍師ポートレート画像ローダー（SVGフォールバック完全対応）
   ========================================================= */

// 武将用画像ローダー（画像がない場合は兜・家紋SVGを中央表示）
function getWarlordPortraitHtml(warlordData) {
  const baseName = warlordData.customImg || `images/${warlordData.id}`;
  const pngPath = `${baseName}.png`;
  const jpgPath = `${baseName}.jpg`;
  const webpPath = `${baseName}.webp`;

  return `
    <div style="width:100%; height:100%; position:relative; overflow:hidden; display:flex; align-items:center; justify-content:center;">
      <img src="${pngPath}" 
           alt="${warlordData.name}" 
           onerror="
             if (!this.dataset.triedJpg) {
               this.dataset.triedJpg = 'true';
               this.src = '${jpgPath}';
             } else if (!this.dataset.triedWebp) {
               this.dataset.triedWebp = 'true';
               this.src = '${webpPath}';
             } else {
               this.style.display = 'none';
               var svg = this.parentElement.querySelector('svg');
               if (svg) svg.style.display = 'block';
             }
           "
           style="width:100%; height:100%; object-fit:cover; object-position:center 10%; display:block;">
      <svg viewBox="0 0 100 100" style="display:none; width:100%; height:100%;">
        ${warlordData.portraitSvg}
      </svg>
    </div>
  `;
}

// 軍師用画像ローダー（画像がない場合は軍師専用SVGを中央表示）
function getStrategistPortraitHtml(warlordData) {
  const baseName = `images/${warlordData.strategistImgId}`;
  const pngPath = `${baseName}.png`;
  const jpgPath = `${baseName}.jpg`;
  const webpPath = `${baseName}.webp`;

  return `
    <div style="width:100%; height:100%; position:relative; overflow:hidden; display:flex; align-items:center; justify-content:center;">
      <img src="${pngPath}" 
           alt="${warlordData.strategistName}" 
           onerror="
             if (!this.dataset.triedJpg) {
               this.dataset.triedJpg = 'true';
               this.src = '${jpgPath}';
             } else if (!this.dataset.triedWebp) {
               this.dataset.triedWebp = 'true';
               this.src = '${webpPath}';
             } else {
               this.style.display = 'none';
               var svg = this.parentElement.querySelector('svg');
               if (svg) svg.style.display = 'block';
             }
           "
           style="width:100%; height:100%; object-fit:cover; object-position:center 10%; display:block;">
      <svg viewBox="0 0 100 100" style="display:none; width:100%; height:100%;">
        ${warlordData.strategistSvg}
      </svg>
    </div>
  `;
}

/* 主役五傑（専属軍師 ＆ 兜・軍師ポートレートアート） */
const PLAYER_WARLORDS = {
  sanada: {
    id: 'sanada', name: '真田幸村', clan: '信濃国 ｜ 真田赤備隊・日本一の兵', themeColor: '#e61919',
    strategistName: '真田昌幸', strategistTitle: '表裏比興の父', strategistShort: '昌幸',
    strategistImgId: 'strategist_masayuki',
    bgGrad: 'radial-gradient(circle at 35% 35%, #6a0b0b 0%, #180202 100%)',
    quotes: {
      default: '「不惜身命！ この一手に命を懸ける！」',
      check: '「真田が突撃！ ここが敵本陣の喉首ぞ！」',
      pinch: '「六文銭を胸に… まだだ、ここからが真田の戦よ！」',
      adv: '「好機至る！ 赤備え、全軍突撃せよ！」'
    },
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#4d0808"/>
      <path d="M 28,32 Q 10,10 18,2 Q 30,16 34,26 Z" fill="#ffd700"/>
      <path d="M 72,32 Q 90,10 82,2 Q 70,16 66,26 Z" fill="#ffd700"/>
      <path d="M 30,48 Q 50,30 70,48 L 74,75 Q 50,82 26,75 Z" fill="#b31212" stroke="#ffd700" stroke-width="1.8"/>
      <g fill="#ffd700" stroke="#330000" stroke-width="1">
        <circle cx="42" cy="42" r="4.5"/><circle cx="50" cy="42" r="4.5"/><circle cx="58" cy="42" r="4.5"/>
        <circle cx="42" cy="52" r="4.5"/><circle cx="50" cy="52" r="4.5"/><circle cx="58" cy="52" r="4.5"/>
      </g>
      <path d="M 24,72 Q 50,96 76,72 L 72,82 Q 50,100 28,82 Z" fill="#ffd700"/>
    `,
    strategistSvg: `
      <rect width="100" height="100" rx="6" fill="#2d1306"/>
      <polygon points="50,12 66,32 50,26 34,32" fill="#ffd700"/>
      <circle cx="50" cy="52" r="22" fill="#170902" stroke="#ffd700" stroke-width="2"/>
      <g fill="#ffd700">
        <circle cx="44" cy="46" r="3.5"/><circle cx="50" cy="46" r="3.5"/><circle cx="56" cy="46" r="3.5"/>
        <circle cx="44" cy="56" r="3.5"/><circle cx="50" cy="56" r="3.5"/><circle cx="56" cy="56" r="3.5"/>
      </g>
      <text x="50" y="88" font-size="11" font-weight="900" fill="#ffd700" text-anchor="middle">謀将昌幸</text>
    `
  },
  keiji: {
    id: 'keiji', name: '前田慶次', clan: '加賀国 ｜ 天下無双の傾奇者', themeColor: '#ffd700',
    strategistName: '奥村助右衛門', strategistTitle: '加賀前田の親友', strategistShort: '助右衛門',
    strategistImgId: 'strategist_sukeemon',
    bgGrad: 'radial-gradient(circle at 35% 35%, #4a2800 0%, #140500 100%)',
    quotes: {
      default: '「大ふへん者とは大武辺者のことよ！ いざ参る！」',
      check: '「よっしゃあ！ これぞ天下無双の傾奇の一手よ！」',
      pinch: '「窮地ほど面白え！ 松風、もう一跳ねするぜ！」',
      adv: '「ハハハ！ 派手に行こうぜ、天下を傾けてみせろ！」'
    },
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#301404"/>
      <path d="M 20,80 L 80,20" stroke="#d41313" stroke-width="6" stroke-linecap="round"/>
      <path d="M 32,45 Q 50,22 68,45 L 72,72 Q 50,80 28,72 Z" fill="#613808" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="45" r="9" fill="#ffd700"/>
      <circle cx="50" cy="26" r="6" fill="#ffd700"/><circle cx="68" cy="38" r="6" fill="#ffd700"/>
      <circle cx="62" cy="62" r="6" fill="#ffd700"/><circle cx="38" cy="62" r="6" fill="#ffd700"/><circle cx="32" cy="38" r="6" fill="#ffd700"/>
    `,
    strategistSvg: `
      <rect width="100" height="100" rx="6" fill="#1b1d28"/>
      <polygon points="50,15 70,38 30,38" fill="#ffd700"/>
      <path d="M 26,44 Q 50,28 74,44 L 76,74 Q 50,82 24,74 Z" fill="#2d354d" stroke="#ffd700" stroke-width="1.8"/>
      <circle cx="50" cy="56" r="12" fill="#ffd700"/>
      <text x="50" y="90" font-size="11" font-weight="900" fill="#ffd700" text-anchor="middle">助右衛門</text>
    `
  },
  masamune: {
    id: 'masamune', name: '伊達政宗', clan: '陸奥国 ｜ 独眼竜の牙', themeColor: '#4fc3f7',
    strategistName: '片倉小十郎', strategistTitle: '竜の右目・天下二大軍師', strategistShort: '小十郎',
    strategistImgId: 'strategist_kojuro',
    bgGrad: 'radial-gradient(circle at 35% 35%, #0d2847 0%, #030a14 100%)',
    quotes: {
      default: '「天下の隙、この独眼竜が見逃さぬ！ 派手に行こうぜ！」',
      check: '「竜の牙が届いたぜ！ 逃げられると思うなよ！」',
      pinch: '「チッ、手痛い一撃だな… だが独眼竜の牙は折れねえ！」',
      adv: '「Partyの始まりだ！ 一気に盤上を制圧するぜ！」'
    },
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#061224"/>
      <path d="M 16,36 Q 66,8 86,58 Q 50,30 16,36 Z" fill="#ffd700"/>
      <path d="M 28,48 Q 50,28 72,48 L 76,76 Q 50,84 24,76 Z" fill="#0d1f36" stroke="#4fc3f7" stroke-width="1.8"/>
      <circle cx="40" cy="60" r="4" fill="#ffd700"/>
      <path d="M 34,58 L 46,62" stroke="#000" stroke-width="2"/>
    `,
    strategistSvg: `
      <rect width="100" height="100" rx="6" fill="#071b26"/>
      <path d="M 20,40 Q 50,15 80,40 L 76,75 Q 50,85 24,75 Z" fill="#13364b" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="46" r="15" fill="#ffd700"/>
      <circle cx="50" cy="46" r="10" fill="#071b26"/>
      <text x="50" y="90" font-size="11" font-weight="900" fill="#ffd700" text-anchor="middle">竜の右目</text>
    `
  },
  kanetsugu: {
    id: 'kanetsugu', name: '直江兼続', clan: '越後国 ｜ 義と愛の軍師', themeColor: '#ba68c8',
    strategistName: '上杉景勝', strategistTitle: '越後の総帥・寡黙の主君', strategistShort: '景勝',
    strategistImgId: 'strategist_kagekatsu',
    bgGrad: 'radial-gradient(circle at 35% 35%, #2a0836 0%, #0b0110 100%)',
    quotes: {
      default: '「義を見てせざるは勇なきなり！ 義の刃を受けてみよ！」',
      check: '「義理を通し、不義を断つ！ これぞ愛の一手！」',
      pinch: '「義の旗印、決して倒れはせぬ！ 陣形を立て直すぞ！」',
      adv: '「大義は我が軍にあり！ 正道を以て制さん！」'
    },
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#1c0524"/>
      <text x="50" y="44" font-size="34" font-weight="900" fill="#ffd700" text-anchor="middle" font-family="Shippori Mincho, serif">愛</text>
      <path d="M 28,48 Q 50,32 72,48 L 75,76 Q 50,84 25,76 Z" fill="#30103b" stroke="#ffd700" stroke-width="1.8"/>
      <path d="M 24,72 Q 50,94 76,72" fill="none" stroke="#ba68c8" stroke-width="3"/>
    `,
    strategistSvg: `
      <rect width="100" height="100" rx="6" fill="#1d1226"/>
      <path d="M 26,45 Q 50,18 74,45 L 76,78 Q 50,86 24,78 Z" fill="#38214a" stroke="#ffd700" stroke-width="1.8"/>
      <circle cx="50" cy="46" r="16" fill="#150a1c"/>
      <text x="50" y="52" font-size="14" font-weight="900" fill="#ffd700" text-anchor="middle">懸</text>
      <text x="50" y="90" font-size="11" font-weight="900" fill="#ffd700" text-anchor="middle">総帥景勝</text>
    `
  },
  tadakatsu: {
    id: 'tadakatsu', name: '本多忠勝', clan: '三河国 ｜ 徳川四天王・蜻蛉切', themeColor: '#ffb74d',
    strategistName: '本多正信', strategistTitle: '徳川の知謀・佐渡守', strategistShort: '正信',
    strategistImgId: 'strategist_masanobu',
    bgGrad: 'radial-gradient(circle at 35% 35%, #3d2406 0%, #0f0701 100%)',
    quotes: {
      default: '「我が蜻蛉切に切れぬものなし！ 迎え撃ってくれよう！」',
      check: '「天下無双の槍撃！ 敵将、そこを動くな！」',
      pinch: '「五十七度の合戦、一度の傷も負わぬ儂が退くものか！」',
      adv: '「我が槍の前に敵なし！ 押し通るぞ！」'
    },
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#1f1103"/>
      <path d="M 22,25 Q 12,46 32,54 Q 18,36 28,26 Z" fill="#ffd700"/>
      <path d="M 78,25 Q 88,46 68,54 Q 82,36 72,26 Z" fill="#ffd700"/>
      <path d="M 30,48 Q 50,30 70,48 L 74,76 Q 50,84 26,76 Z" fill="#241505" stroke="#ffd700" stroke-width="1.8"/>
      <circle cx="50" cy="62" r="14" fill="none" stroke="#ffd700" stroke-width="3.5" stroke-dasharray="3,3"/>
    `,
    strategistSvg: `
      <rect width="100" height="100" rx="6" fill="#261705"/>
      <polygon points="50,16 68,36 50,30 32,36" fill="#ffd700"/>
      <path d="M 28,45 Q 50,28 72,45 L 75,76 Q 50,84 25,76 Z" fill="#4d2f0a" stroke="#ffd700" stroke-width="1.8"/>
      <circle cx="50" cy="58" r="13" fill="#ffd700"/>
      <text x="50" y="90" font-size="11" font-weight="900" fill="#ffd700" text-anchor="middle">佐渡守</text>
    `
  }
};

/* 敵将十傑（兜ポートレート ＆ 動員兵力） */
const WARLORDS_DATA = {
  1: {
    id: 'enemy_1', province: '尾張国', name: '木下藤吉郎', clan: '尾張国｜織田足軽隊 (Lv.1)', power: '動員兵力 3,200',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#140d06"/><path d="M50 20 Q56 28 50 36 Q44 28 50 20 Z M50 36 Q62 50 50 68 Q38 50 50 36 Z M50 68 Q68 85 50 94 Q32 85 50 68 Z" fill="#ffd700"/>`,
    quotes: { default: '「草履取りとて天下を夢見候！ 足軽の意地、見せてくれよう！」', check: '「猿の一撃、侮りめさるな！」', pinch: '「あわわ…！ 信長様にお叱りを受けてしまう！」', adv: '「出世の足音が聞こえてき申した！」' }
  },
  2: {
    id: 'enemy_2', province: '加賀国', name: '前田利家', clan: '加賀国｜槍の又左 (Lv.2)', power: '動員兵力 4,500',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#180707"/><circle cx="50" cy="50" r="10" fill="#ffd700"/><circle cx="50" cy="24" r="8" fill="#ffd700"/><circle cx="75" cy="42" r="8" fill="#ffd700"/><circle cx="65" cy="74" r="8" fill="#ffd700"/><circle cx="35" cy="74" r="8" fill="#ffd700"/><circle cx="25" cy="42" r="8" fill="#ffd700"/>`,
    quotes: { default: '「我が槍に迷いなし！ 槍の又左が一撃、盤上に受けてみよ！」', check: '「槍の又左、一騎当千の突撃ぞ！」', pinch: '「ぬう…！ 前田の槍衾を崩されるとは！」', adv: '「槍を引くな！ この利家が押し通る！」' }
  },
  3: {
    id: 'enemy_3', province: '越前国', name: '柴田勝家', clan: '越前国｜鬼柴田 (Lv.3)', power: '動員兵力 5,600',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#150a04"/><path d="M30 40 Q50 25 70 40 Q50 48 30 40 Z M30 65 Q50 50 70 65 Q50 73 30 65 Z" fill="#ffd700"/>`,
    quotes: { default: '「かかれ柴田の突進力、小細工など粉砕してくれるわ！」', check: '「鬼柴田の剛腕、いざ受けてみよ！」', pinch: '「ぐぬ… 瓶割り柴田、退路を断って迎え撃つ！」', adv: '「かかれ！ かかれ柴田の猛進を止められるか！」' }
  },
  4: {
    id: 'enemy_4', province: '近江国', name: '浅井長政', clan: '近江国｜浅井軍総帥 (Lv.4)', power: '動員兵力 6,800',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#0d1824"/><g fill="none" stroke="#ffd700" stroke-width="3"><polygon points="50,18 64,26 64,42 50,50 36,42 36,26"/><polygon points="36,44 50,52 50,68 36,76 22,68 22,52"/><polygon points="64,44 78,52 78,68 64,76 50,68 50,52"/></g>`,
    quotes: { default: '「信義を重んじ、我が陣を進めん！ 浅井の誇り、見よ！」', check: '「信義の一撃、ここを退くわけにはいかぬ！」', pinch: '「信義を貫く刻… お市、すまぬ…」', adv: '「我が陣容に乱れなし！ 義の勝利を！」' }
  },
  5: {
    id: 'enemy_5', province: '美濃国', name: '明智光秀', clan: '美濃国｜智謀の軍総帥 (Lv.5)', power: '動員兵力 7,600',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#09141c"/><polygon points="50,18 60,38 82,38 65,52 72,74 50,60 28,74 35,52 18,38 40,38" fill="#ffd700"/>`,
    quotes: { default: '「時は今、天が下知る五月哉。我が智謀、見切れるか！」', check: '「敵は本能寺に… いや、貴殿の本陣にあり！」', pinch: '「天運は我を見放すというのか…！ まだだ！」', adv: '「盤上の全て、我が掌の上にて動いておる。」' }
  },
  6: {
    id: 'enemy_6', province: '越後国', name: '上杉謙信', clan: '越後国｜越後の龍・軍神 (Lv.6)', power: '動員兵力 8,400',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#14061a"/>
      <path d="M 26,45 Q 50,18 74,45 L 76,78 Q 50,86 24,78 Z" fill="#e8e8e8" stroke="#ffd700" stroke-width="1.8"/>
      <circle cx="50" cy="46" r="16" fill="#1c0a24"/>
      <text x="50" y="52" font-size="14" font-weight="900" fill="#ffd700" text-anchor="middle">毘</text>
    `,
    quotes: { default: '「毘沙門天の御加護、我が軍にあり！ 車懸りの陣、進めよ！」', check: '「龍の爪牙、敵本陣を裂く！」', pinch: '「運は天にあり、鎧は胸にあり！ 毘沙門天よ！」', adv: '「車懸り、休むこと莫れ！ 義戦を完遂せん！」' }
  },
  7: {
    id: 'enemy_7', province: '甲斐国', name: '武田信玄', clan: '甲斐国｜甲斐の虎 (Lv.7)', power: '動員兵力 8,900',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#1f0303"/>
      <path d="M 22,34 Q 50,10 78,34 Q 90,60 76,76 Q 50,88 24,76 Q 10,60 22,34 Z" fill="#e0d6c3" stroke="#ffd700" stroke-width="1.8"/>
      <polygon points="50,30 60,42 50,54 40,42" fill="#ffd700"/>
      <polygon points="40,44 50,56 40,68 30,56" fill="#ffd700"/><polygon points="60,44 70,56 60,68 50,56" fill="#ffd700"/>
    `,
    quotes: { default: '「疾きこと風の如く、動かざること山の如し！ 蹂躙してくれる！」', check: '「侵略すること火の如し！ 虎の牙、受けてみよ！」', pinch: '「人は城、人は石垣… 崩れるな、耐えよ！」', adv: '「風林火山の旗の下、天下を呑み込まん！」' }
  },
  8: {
    id: 'enemy_8', province: '近江安土', name: '織田信長', clan: '近江安土｜第六天魔王 (Lv.8)', power: '動員兵力 9,500',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#140606"/>
      <path d="M 28,42 Q 50,20 72,42 L 76,76 Q 50,86 24,76 Z" fill="#3b0808" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="27" r="10" fill="#ffd700"/><circle cx="68" cy="40" r="10" fill="#ffd700"/>
      <circle cx="62" cy="62" r="10" fill="#ffd700"/><circle cx="38" cy="62" r="10" fill="#ffd700"/><circle cx="32" cy="40" r="10" fill="#ffd700"/>
      <circle cx="50" cy="48" r="11" fill="#9b111e" stroke="#ffd700" stroke-width="1.5"/>
    `,
    quotes: { default: '「是非に及ばず。この信長に挑む愚かさ、骨身に刻め。」', check: '「三段撃ち！ 鉄砲の前に灰燼と帰すがよい！」', pinch: '「人間五十年、下天の内をくらぶれば… まだ死せぬ！」', adv: '「天下布武！ 我が前にひれ伏せ！」' }
  },
  9: {
    id: 'enemy_9', province: '摂津大坂', name: '豊臣秀吉', clan: '摂津大坂｜天下人・太閤 (Lv.9)', power: '動員兵力 9,800',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#241904"/>
      <g stroke="#ffd700" stroke-width="2">
        <line x1="50" y1="45" x2="50" y2="8"/><line x1="50" y1="45" x2="25" y2="15"/><line x1="50" y1="45" x2="75" y2="15"/>
        <line x1="50" y1="45" x2="10" y2="30"/><line x1="50" y1="45" x2="90" y2="30"/>
      </g>
      <path d="M 30,46 Q 50,30 70,46 L 74,75 Q 50,84 26,75 Z" fill="#694a08" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="56" r="10" fill="#ffd700"/>
    `,
    quotes: { default: '「天下は我が手中にある！ 太閤の前に跪くがよい！」', check: '「黄金の茶室ならぬ、黄金の王手を喰らいなされ！」', pinch: '「露と落ち、露と消えにし我が身かな… なにを！」', adv: '「日輪の如く、全てを照らし尽くして見せよう！」' }
  },
  10: {
    id: 'enemy_10', province: '武蔵江戸', name: '徳川家康', clan: '武蔵江戸｜天下の覇者 (Lv.10)', power: '動員兵力 10,000',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#080f1f"/>
      <path d="M 32,24 Q 50,14 68,24 Q 80,38 74,62 Q 50,78 26,62 Q 20,38 32,24 Z" fill="#1b2a47" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="50" r="18" fill="none" stroke="#ffd700" stroke-width="2.5"/>
      <path d="M50 48 C44 32, 36 24, 50 18 C64 24, 56 32, 50 48 Z" fill="#ffd700"/>
      <path d="M49 52 C33 50, 24 60, 26 74 C38 74, 46 64, 49 52 Z" fill="#ffd700"/>
      <path d="M51 52 C67 50, 76 60, 74 74 C62 74, 54 64, 51 52 Z" fill="#ffd700"/>
    `,
    quotes: {
      default: '「人の一生は重荷を負うて… 焦るでない、勝機は此処にあり。」',
      check: '「忍耐の刻は過ぎた！ 我が天下の礎となられよ！」',
      pinch: '「ぐぬぬ…！ 爪を噛むほどの焦燥よ… だが儂の天下は揺るがぬ！」',
      adv: '「鳴くまで待った甲斐があったわ。天下泰平の刻ぞ！」'
    }
  }
};

const RIVALRIES = {
  'sanada_10': {
    title: '【宿命の対決】大坂の陣！ 日本一の兵 vs 天下の覇者',
    pQuote: '「不惜身命！ 徳川の天下、この幸村が盤上で覆して見せようぞ！」',
    eQuote: '「真田か…！ 目の上の瘤め、大坂の雪辱はさせぬぞ！」'
  },
  'keiji_2': {
    title: '【宿命の対決】前田の血脈！ 傾奇者 vs 槍の又左',
    pQuote: '「叔父貴、ぬるい水風呂の礼をせねばな！ ど派手に傾くぜ！」',
    eQuote: '「慶次！ その放蕩、前田の当主として盤上で成敗いたす！」'
  },
  'kanetsugu_10': {
    title: '【宿命の対決】直江状の義戦！ 義愛の軍師 vs 関東の巨魁',
    pQuote: '「不義の天下に道はなし！ 義の刃、盤上にて受けてみよ！」',
    eQuote: '「直江兼続… 筆鋒鋭き小僧め、盤上で捻り潰してくれる！」'
  },
  'masamune_9': {
    title: '【宿命の対決】天下への野望！ 独眼竜 vs 太閤の威光',
    pQuote: '「太閤殿下！ 白装束の礼は済んだ、盤上は容赦しねえ！」',
    eQuote: '「伊達の若造、その野心ごとのみ込んで見せようぞ！」'
  },
  'tadakatsu_7': {
    title: '【宿命の対決】三方ヶ原の雪辱！ 蜻蛉切 vs 甲斐の虎',
    pQuote: '「信玄公！ 我が蜻蛉切、家康公の盾となり打ち砕かん！」',
    eQuote: '「忠勝、家康に過ぎたるものよ。虎の牙を凌げるか！」'
  }
};

const PIECES = {
  OU: '王将', HI: '飛車', KA: '角行', KI: '金将', GI: '銀将', KE: '桂馬', KY: '香車', FU: '歩兵',
  RY: '竜王', UM: '竜馬', NG: '成銀', NK: '成桂', NY: '成香', TO: 'と金'
};
const PROMOTED_PIECES = ['RY', 'UM', 'NG', 'NK', 'NY', 'TO'];
const KANJI_NUMS = ['一','二','三','四','五','六','七','八','九'];
const UNPROMOTE_MAP = { RY:'HI', UM:'KA', NG:'GI', NK:'KE', NY:'KY', TO:'FU', HI:'HI', KA:'KA', KI:'KI', GI:'GI', KE:'KE', KY:'KY', FU:'FU', OU:'OU' };
const PROMOTE_MAP = { HI:'RY', KA:'UM', GI:'NG', KE:'NK', KY:'NY', FU:'TO' };

let currentMyWarlordId = 'sanada', currentAiLevel = 1, clearedProvinces = [];
let board = [], hands = { PLAYER: {}, AI: {} }, turn = null, isGameOver = true;
let selectedPos = null, currentValidMoves = [], moveObjectsHistory = [], historyStates = [], reviewingIndex = -1, evalScoresHistory = [0];
let hintSourceCell = null, hintTargetCell = null, pendingMove = null, isAiThinking = false, isHintThinking = false;
let boardHashHistory = [], checkHistory = [], lastMove = null;

// 移動可能マス取得
function getValidBoardMoves(r, c, owner) {
  const item = board[r][c]; if (!item) return [];
  const dir = owner === 'AI' ? 1 : -1, moves = [];
  const canT = (nr, nc) => !board[nr][nc] || board[nr][nc].owner !== owner;
  const ray = dirs => dirs.forEach(([dr, dc]) => {
    let nr = r + dr, nc = c + dc;
    while (nr >= 0 && nr < 9 && nc >= 0 && nc < 9) {
      if (!board[nr][nc]) moves.push({r: nr, c: nc});
      else { if (canT(nr, nc)) moves.push({r: nr, c: nc}); break; }
      nr += dr; nc += dc;
    }
  });
  const step = offs => offs.forEach(([dr, dc]) => {
    const nr = r + dr, nc = c + dc;
    if (nr >= 0 && nr < 9 && nc >= 0 && nc < 9 && canT(nr, nc)) moves.push({r: nr, c: nc});
  });
  const gold = [[dir, -1], [dir, 0], [dir, 1], [0, -1], [0, 1], [-dir, 0]];
  switch(item.code) {
    case 'FU': step([[dir, 0]]); break;
    case 'KY': ray([[dir, 0]]); break;
    case 'KE': step([[dir * 2, -1], [dir * 2, 1]]); break;
    case 'GI': step([[dir, -1], [dir, 0], [dir, 1], [-dir, -1], [-dir, 1]]); break;
    case 'KI': case 'TO': case 'NY': case 'NK': case 'NG': step(gold); break;
    case 'OU': step([[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]); break;
    case 'HI': ray([[-1,0],[1,0],[0,-1],[0,1]]); break;
    case 'KA': ray([[-1,-1],[-1,1],[1,-1],[1,1]]); break;
    case 'RY': ray([[-1,0],[1,0],[0,-1],[0,1]]); step([[-1,-1],[-1,1],[1,-1],[1,1]]); break;
    case 'UM': ray([[-1,-1],[-1,1],[1,-1],[1,1]]); step([[-1,0],[1,0],[0,-1],[0,1]]); break;
  }
  return moves;
}

function findKing(owner) {
  for (let r=0; r<9; r++) for (let c=0; c<9; c++) if (board[r][c]?.owner === owner && board[r][c]?.code === 'OU') return {r, c};
  return null;
}

function isCheckState(owner) {
  const kp = findKing(owner);
  if (!kp) return true;
  const kr = kp.r, kc = kp.c, enemy = (owner === 'PLAYER') ? 'AI' : 'PLAYER';
  for (let r=0; r<9; r++) {
    for (let c=0; c<9; c++) {
      if (board[r][c]?.owner === enemy) {
        const moves = getValidBoardMoves(r, c, enemy);
        if (moves.some(m => m.r === kr && m.c === kc)) return true;
      }
    }
  }
  return false;
}

function makeMove(move) {
  const undo = { move };
  const owner = move.owner;
  if (move.type === 'drop') {
    hands[owner][move.code]--;
    board[move.to.r][move.to.c] = { code: move.code, owner };
  } else {
    const item = board[move.from.r][move.from.c], target = board[move.to.r][move.to.c];
    undo.fromCode = item.code;
    if (target) {
      undo.capturedCode = target.code;
      if (target.code !== 'OU') {
        const raw = UNPROMOTE_MAP[target.code];
        hands[owner][raw] = (hands[owner][raw] || 0) + 1;
      }
    }
    if (move.promote) item.code = PROMOTE_MAP[item.code];
    board[move.to.r][move.to.c] = item;
    board[move.from.r][move.from.c] = null;
  }
  return undo;
}

function unmakeMove(undo) {
  const move = undo.move, owner = move.owner;
  if (move.type === 'drop') {
    hands[owner][move.code]++;
    board[move.to.r][move.to.c] = null;
  } else {
    const item = board[move.to.r][move.to.c];
    item.code = undo.fromCode;
    board[move.from.r][move.from.c] = item;
    if (undo.capturedCode) {
      board[move.to.r][move.to.c] = { code: undo.capturedCode, owner: owner === 'AI' ? 'PLAYER' : 'AI' };
      if (undo.capturedCode !== 'OU') hands[owner][UNPROMOTE_MAP[undo.capturedCode]]--;
    } else board[move.to.r][move.to.c] = null;
  }
}

function isUchifuzume(move) {
  if (move.type !== 'drop' || move.code !== 'FU') return false;
  const enemy = move.owner === 'AI' ? 'PLAYER' : 'AI';
  const enemyKing = findKing(enemy);
  if (!enemyKing) return false;
  const fwd = move.owner === 'AI' ? 1 : -1;
  if (move.to.r !== enemyKing.r - fwd || move.to.c !== enemyKing.c) return false;

  const undo = makeMove(move);
  const kingInCheck = isCheckState(enemy);
  if (!kingInCheck) { unmakeMove(undo); return false; }

  const enemyLegals = getLegalMoves(enemy, false, false);
  unmakeMove(undo);
  return enemyLegals.length === 0;
}

function getLegalMoves(owner, capturesOnly = false, filterUchifuzume = true) {
  const pseudo = [];
  for (let r=0; r<9; r++) {
    for (let c=0; c<9; c++) {
      if (board[r][c]?.owner === owner) {
        const item = board[r][c];
        getValidBoardMoves(r, c, owner).forEach(m => {
          const target = board[m.r][m.c], isCap = (target && target.owner !== owner);
          const inCamp = (owner === 'AI' ? (r >= 6 || m.r >= 6) : (r <= 2 || m.r <= 2));
          const canP = PROMOTE_MAP[item.code] && inCamp;
          const mustP = owner === 'AI' ? ((item.code === 'FU' || item.code === 'KY') && m.r === 8 || (item.code === 'KE' && m.r >= 7))
                                       : ((item.code === 'FU' || item.code === 'KY') && m.r === 0 || (item.code === 'KE' && m.r <= 1));
          if (capturesOnly && !isCap && !canP && !mustP) return;

          if (mustP) pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: true, isCap });
          else if (canP) {
            pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: true, isCap });
            if (!capturesOnly) pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: false, isCap });
          } else pseudo.push({ type: 'move', code: item.code, from: {r, c}, to: m, owner, promote: false, isCap });
        });
      }
    }
  }

  if (!capturesOnly) {
    for (const code in hands[owner]) if (hands[owner][code] > 0) {
      for (let r=0; r<9; r++) {
        if ((code === 'FU' || code === 'KY') && ((owner === 'AI' && r === 8) || (owner === 'PLAYER' && r === 0))) continue;
        if (code === 'KE' && ((owner === 'AI' && r >= 7) || (owner === 'PLAYER' && r <= 1))) continue;
        for (let c=0; c<9; c++) {
          if (!board[r][c]) {
            if (code === 'FU') {
              let nifu = false;
              for(let kr=0; kr<9; kr++) if (board[kr][c]?.owner === owner && board[kr][c]?.code === 'FU') { nifu = true; break; }
              if (nifu) continue;
            }
            pseudo.push({ type: 'drop', code, to: {r, c}, owner, isCap: false });
          }
        }
      }
    }
  }

  return pseudo.filter(m => {
    if (filterUchifuzume && m.type === 'drop' && m.code === 'FU') {
      if (isUchifuzume(m)) return false;
    }
    const undo = makeMove(m);
    const safe = !isCheckState(owner);
    unmakeMove(undo);
    return safe;
  });
}

function loadProgress() {
  try {
    const s = localStorage.getItem('shogi_cleared_provinces');
    if (s !== null) {
      clearedProvinces = JSON.parse(s);
    } else {
      const oldMax = localStorage.getItem('shogi_max_cleared_level');
      if (oldMax !== null) {
        const mx = parseInt(oldMax, 10);
        clearedProvinces = [];
        for (let i = 1; i <= mx; i++) clearedProvinces.push(i);
      } else clearedProvinces = [];
    }
    
    const nextLvl = clearedProvinces.length > 0 ? Math.min(10, Math.max(...clearedProvinces) + 1) : 1;
    currentAiLevel = nextLvl;

    const mw = localStorage.getItem('shogi_my_warlord');
    if (mw && PLAYER_WARLORDS[mw]) currentMyWarlordId = mw;
  } catch (e) { clearedProvinces = []; currentAiLevel = 1; }
  updateConquestMapUI();
}

function saveProgress(clearedLvl) {
  try {
    if (!clearedProvinces.includes(clearedLvl)) {
      clearedProvinces.push(clearedLvl);
      localStorage.setItem('shogi_cleared_provinces', JSON.stringify(clearedProvinces));
    }
  } catch (e) {}
  updateConquestMapUI();
}

function cloneBoardState(b) { return b.map(row => row.map(cell => cell ? {...cell} : null)); }
function getBoardHash(b, h, t) {
  let s = t + ':';
  for(let r=0; r<9; r++) for(let c=0; c<9; c++) {
    const p = b[r][c]; if (p) s += `${r}${c}${p.code}${p.owner[0]}|`;
  }
  for (const ow of ['PLAYER','AI']) for (const k in h[ow]) {
    if (h[ow][k] > 0) s += `${ow[0]}${k}${h[ow][k]}`;
  }
  return s;
}

// 千日手＆連続王手千日手判定
function checkSennichite() {
  const curHash = getBoardHash(board, hands, turn);
  boardHashHistory.push(curHash);
  
  const inCheckCurrent = isCheckState(turn);
  checkHistory.push({ turn, inCheck: inCheckCurrent });

  const count = boardHashHistory.filter(h => h === curHash).length;
  if (count >= 4) {
    let playerChecking = 0, aiChecking = 0;
    const len = checkHistory.length;
    for (let i = Math.max(0, len - 12); i < len; i++) {
      if (checkHistory[i].turn === 'AI' && checkHistory[i].inCheck) playerChecking++;
      if (checkHistory[i].turn === 'PLAYER' && checkHistory[i].inCheck) aiChecking++;
    }

    isGameOver = true; playCheckSound();

    if (playerChecking >= 3 && aiChecking === 0) {
      triggerCutin('連続王手の反則！ 敗戦に候！', true);
      setOrderMessage('【反則負け】連続王手の千日手は武士道違反（反則負け）に候！<br>陣を立て直し再戦されよ。', false);
      return true;
    } else if (aiChecking >= 3 && playerChecking === 0) {
      triggerCutin('敵将の反則！ 我が軍の勝利！', true);
      setOrderMessage('【反則勝ち】敵将が連続王手の千日手を犯し候！ 我が軍の勝利なり！', false);
      saveProgress(currentAiLevel); launchFireworksCelebration();
      return true;
    }

    triggerCutin('千日手！ 痛み分けの引き分け！');
    setOrderMessage('【千日手】同一局面四回にて引き分け（痛み分け）に候。<br>「対局開始」にて再戦されよ。', false);
    return true;
  }
  return false;
}

function initBoardState() {
  board = Array.from({length: 9}, () => Array(9).fill(null));
  hands = { PLAYER: {}, AI: {} };
  moveObjectsHistory = []; historyStates = []; boardHashHistory = []; checkHistory = [];
  evalScoresHistory = [0]; reviewingIndex = -1; lastMove = null;
  hintSourceCell = null; hintTargetCell = null; selectedPos = null; currentValidMoves = [];
  isAiThinking = false; isHintThinking = false;

  updateStrategistUI();
  updateWarlordBGM(currentAiLevel);

  // 対局画面ポートレートの完全描画・更新
  renderMainPortraits();

  board[0] = [{code:'KY',owner:'AI'},{code:'KE',owner:'AI'},{code:'GI',owner:'AI'},{code:'KI',owner:'AI'},{code:'OU',owner:'AI'},{code:'KI',owner:'AI'},{code:'GI',owner:'AI'},{code:'KE',owner:'AI'},{code:'KY',owner:'AI'}];
  board[1][1] = {code:'HI',owner:'AI'}; board[1][7] = {code:'KA',owner:'AI'};
  for(let c=0; c<9; c++) board[2][c] = {code:'FU',owner:'AI'};
  for(let c=0; c<9; c++) board[6][c] = {code:'FU',owner:'PLAYER'};
  board[7][1] = {code:'KA',owner:'PLAYER'}; board[7][7] = {code:'HI',owner:'PLAYER'};
  board[8] = [{code:'KY',owner:'PLAYER'},{code:'KE',owner:'PLAYER'},{code:'GI',owner:'PLAYER'},{code:'KI',owner:'PLAYER'},{code:'OU',owner:'PLAYER'},{code:'KI',owner:'PLAYER'},{code:'GI',owner:'PLAYER'},{code:'KE',owner:'PLAYER'},{code:'KY',owner:'PLAYER'}];

  historyStates.push({ board: cloneBoardState(board), hands: JSON.parse(JSON.stringify(hands)), turn, moveObjectsHistory: [] });
  boardHashHistory.push(getBoardHash(board, hands, turn));
  renderBoard(); renderKifu(); updateMoraleAndSituation(0);
}

// 対局画面アバター（自将・敵将）のポートレートを確実に描画
function renderMainPortraits() {
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const w = WARLORDS_DATA[currentAiLevel];
  const pBox = document.getElementById('player-avatar-container');
  const aiBox = document.getElementById('ai-avatar-container');
  if (pBox) pBox.innerHTML = getWarlordPortraitHtml(p);
  if (aiBox) aiBox.innerHTML = getWarlordPortraitHtml(w);
}

function updateStrategistUI() {
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const badge = document.getElementById('player-strategist-badge');
  if (badge) badge.textContent = `軍師:${p.strategistName}`;
  const hintBtn = document.getElementById('btn-master-hint');
  if (hintBtn) {
    hintBtn.classList.remove('awakened');
    hintBtn.textContent = `💡 ${p.strategistShort}進言`;
  }
}

// 伝令メッセージ表示（軍師ポートレート連動）
function setOrderMessage(txt, isMyTurn = false, showStrategistAvatar = false) {
  const el = document.getElementById('order-message-banner');
  const slot = document.getElementById('order-avatar-slot');
  document.getElementById('order-message-text').innerHTML = txt;
  el.classList.toggle('my-turn', isMyTurn);
  document.getElementById('player-panel').classList.toggle('player-active', isMyTurn);

  if (slot) {
    if (showStrategistAvatar) {
      slot.classList.add('has-strategist');
      slot.innerHTML = getStrategistPortraitHtml(PLAYER_WARLORDS[currentMyWarlordId]);
    } else {
      slot.classList.remove('has-strategist');
      slot.innerHTML = `<svg class="order-crest-icon" viewBox="0 0 100 100"><polygon points="50,5 95,95 5,95" fill="#ffd700"/></svg>`;
    }
  }
}

function openFurigomaModal() {
  initAudio(); playPieceSound();
  const m = document.getElementById('furigoma-modal'), r = document.getElementById('furigoma-pieces-row'), t = document.getElementById('furigoma-result-text');
  m.style.display = 'flex'; r.innerHTML = ''; t.textContent = '天運を見届けております…';
  let toCount = 0;
  for (let i = 0; i < 5; i++) {
    const isTo = Math.random() < 0.5; if (isTo) toCount++;
    const b = document.createElement('div'); b.className = 'furigoma-piece-box';
    b.innerHTML = `
      <div class="furigoma-card" id="fg-${i}">
        <div class="furigoma-face furigoma-front">
          <span class="piece-char-top">歩</span><span class="piece-char-bottom">兵</span>
        </div>
        <div class="furigoma-face furigoma-back">
          <span class="piece-char-top">と</span><span class="piece-char-bottom">金</span>
        </div>
      </div>`;
    r.appendChild(b);
    setTimeout(() => { if (isTo) document.getElementById(`fg-${i}`).classList.add('flipped'); playPieceSound(); }, 150 + i * 160);
  }
  setTimeout(() => {
    const isPlayerSente = (5 - toCount) >= 3;
    turn = isPlayerSente ? 'PLAYER' : 'AI';
    t.innerHTML = isPlayerSente ? `<span style="color:#ff5252;">歩が${5 - toCount}枚！ 我が軍の先手！</span>` : `<span style="color:#ffd700;">と金が${toCount}枚！ 敵軍の先手！</span>`;
    setTimeout(() => { m.style.display = 'none'; startBattle(); }, 1200);
  }, 1300);
}

function startBattle() {
  isGameOver = false; initBoardState();
  const rivalKey = `${currentMyWarlordId}_${currentAiLevel}`;
  const rivalry = RIVALRIES[rivalKey];

  if (rivalry) {
    triggerCutin(rivalry.title, true, true);
    document.getElementById('player-quote-disp').textContent = rivalry.pQuote;
    document.getElementById('ai-quote-disp').textContent = rivalry.eQuote;
  } else {
    triggerCutin('合戦開始！ いざ推して参る！');
    document.getElementById('player-quote-disp').textContent = PLAYER_WARLORDS[currentMyWarlordId].quotes.default;
    document.getElementById('ai-quote-disp').textContent = WARLORDS_DATA[currentAiLevel].quotes.default;
  }

  const pName = PLAYER_WARLORDS[currentMyWarlordId].name;
  if (turn === 'PLAYER') {
    setOrderMessage(`【先手・我が軍】${pName}公、一手目をお決め下され！`, true);
  } else {
    setOrderMessage(`【先手・敵軍】${WARLORDS_DATA[currentAiLevel].name}が軍略を巡らせております…`, false);
    setTimeout(aiTurn, 850);
  }
}

/* 盤面描画：着地点1点のみ点灯 */
function renderBoard() {
  const el = document.getElementById('board'); el.innerHTML = '';
  for(let r=0; r<9; r++) {
    for(let c=0; c<9; c++) {
      const cell = document.createElement('div'); cell.className = 'cell';
      
      if (lastMove && lastMove.to.r === r && lastMove.to.c === c) {
        cell.classList.add('last-move-to');
      }

      if (selectedPos?.r === r && selectedPos?.c === c) cell.classList.add('selected');
      if (currentValidMoves.some(m => m.r === r && m.c === c)) cell.classList.add('target-move');
      if (hintSourceCell?.r === r && hintSourceCell?.c === c) cell.classList.add('hint-source');
      if (hintTargetCell?.r === r && hintTargetCell?.c === c) cell.classList.add('hint-target');

      const p = board[r][c];
      if (p) {
        const pDiv = document.createElement('div');
        const isProm = PROMOTED_PIECES.includes(p.code);
        pDiv.className = `piece ${p.owner === 'PLAYER' ? 'player' : 'ai'} ${isProm ? 'promoted' : ''}`;
        
        const name2 = PIECES[p.code];
        pDiv.innerHTML = `<span class="piece-char-top">${name2[0]}</span><span class="piece-char-bottom">${name2[1]}</span>`;
        cell.appendChild(pDiv);
      }
      cell.onclick = () => onCellClick(r, c);
      el.appendChild(cell);
    }
  }
  renderHands();
}

function renderHands() {
  ['PLAYER', 'AI'].forEach(ow => {
    const box = document.getElementById(ow === 'PLAYER' ? 'player-hand' : 'ai-hand');
    box.innerHTML = '';
    for(let code in hands[ow]) {
      const cnt = hands[ow][code];
      if (cnt > 0) {
        const d = document.createElement('div');
        d.className = `hand-piece ${ow === 'PLAYER' ? 'player' : 'ai'} ${selectedPos?.handCode === code ? 'selected' : ''}`;
        const name2 = PIECES[code];
        d.innerHTML = `<span class="piece-char-top">${name2[0]}</span><span class="piece-char-bottom">${name2[1]}</span>`;
        if (cnt > 1) {
          const s = document.createElement('span'); s.className = 'hand-piece-count'; s.textContent = cnt;
          d.appendChild(s);
        }
        if (ow === 'PLAYER') d.onclick = () => onHandClick(code);
        box.appendChild(d);
      }
    }
  });
}

function isReviewingPast() {
  return (reviewingIndex !== -1 && reviewingIndex !== historyStates.length - 1);
}

function onHandClick(code) {
  if (isGameOver || turn !== 'PLAYER' || isAiThinking) return;
  if (isReviewingPast()) {
    setOrderMessage('【合戦記録閲覧中】「⏭」を押して最新の戦況へお戻り下され。', false);
    return;
  }
  initAudio(); playPieceSound();
  hintSourceCell = null; hintTargetCell = null;
  if (selectedPos?.handCode === code) { selectedPos = null; currentValidMoves = []; }
  else {
    selectedPos = { handCode: code };
    currentValidMoves = getLegalMoves('PLAYER').filter(m => m.type === 'drop' && m.code === code).map(m => m.to);
  }
  renderBoard();
}

function onCellClick(r, c) {
  if (isGameOver || turn !== 'PLAYER' || isAiThinking) return;
  if (isReviewingPast()) {
    setOrderMessage('【合戦記録閲覧中】「⏭」を押して最新の戦況へお戻り下され。', false);
    return;
  }
  initAudio(); hintSourceCell = null; hintTargetCell = null;

  if (selectedPos?.handCode && currentValidMoves.some(m => m.r === r && m.c === c)) {
    executeMove({ type:'drop', code:selectedPos.handCode, to:{r,c}, owner:'PLAYER' });
    selectedPos = null; currentValidMoves = []; finishTurn(); return;
  }
  if (selectedPos?.r !== undefined && currentValidMoves.some(m => m.r === r && m.c === c)) {
    const p = board[selectedPos.r][selectedPos.c];
    const canP = PROMOTE_MAP[p.code] && (selectedPos.r <= 2 || r <= 2);
    const mustP = (p.code === 'FU' || p.code === 'KY') && r === 0 || (p.code === 'KE' && r <= 1);
    if (canP && !mustP) {
      pendingMove = { type:'move', code: p.code, from:selectedPos, to:{r,c}, owner:'PLAYER' };
      document.getElementById('promote-modal').style.display = 'flex'; return;
    }
    executeMove({ type:'move', code: p.code, from:selectedPos, to:{r,c}, owner:'PLAYER', promote: canP || mustP });
    selectedPos = null; currentValidMoves = []; finishTurn(); return;
  }
  if (board[r][c]?.owner === 'PLAYER') {
    selectedPos = {r, c};
    currentValidMoves = getLegalMoves('PLAYER').filter(m => m.type === 'move' && m.from.r === r && m.from.c === c).map(m => m.to);
  } else {
    selectedPos = null; currentValidMoves = [];
  }
  renderBoard();
}

document.getElementById('btn-promote-yes').onclick = () => {
  if (pendingMove) { executeMove({...pendingMove, promote:true}); pendingMove = null; document.getElementById('promote-modal').style.display = 'none'; selectedPos = null; currentValidMoves = []; finishTurn(); }
};
document.getElementById('btn-promote-no').onclick = () => {
  if (pendingMove) { executeMove({...pendingMove, promote:false}); pendingMove = null; document.getElementById('promote-modal').style.display = 'none'; selectedPos = null; currentValidMoves = []; finishTurn(); }
};

// 手の実行＆記録
function executeMove(m) {
  playPieceSound();

  if (m.type === 'move' && !m.code && board[m.from.r][m.from.c]) {
    m.code = board[m.from.r][m.from.c].code;
  }

  moveObjectsHistory.push(m);
  lastMove = m;

  if (m.type === 'drop') {
    hands[m.owner][m.code]--;
    board[m.to.r][m.to.c] = { code: m.code, owner: m.owner };
  } else {
    const fp = board[m.from.r][m.from.c], tp = board[m.to.r][m.to.c];
    if (tp && tp.code !== 'OU') {
      const raw = UNPROMOTE_MAP[tp.code];
      hands[m.owner][raw] = (hands[m.owner][raw] || 0) + 1;
      if (m.owner === 'PLAYER' && (tp.code === 'HI' || tp.code === 'KA')) {
        setOrderMessage(`【戦果】敵の${PIECES[tp.code]}を捕獲！ 敵陣へ打ち込み急襲されよ！`, true);
      }
    }
    if (m.promote) {
      fp.code = PROMOTE_MAP[fp.code];
      if (fp.code === 'RY') triggerCutin('竜王顕現！ 敵陣を薙ぎ払え！', true);
      else if (fp.code === 'UM') triggerCutin('竜馬咆哮！ 神速の刃！', true);
    }
    board[m.to.r][m.to.c] = fp;
    board[m.from.r][m.from.c] = null;
  }
  historyStates.push({ board: cloneBoardState(board), hands: JSON.parse(JSON.stringify(hands)), turn: m.owner === 'PLAYER' ? 'AI' : 'PLAYER', moveObjectsHistory: JSON.parse(JSON.stringify(moveObjectsHistory)) });
  reviewingIndex = historyStates.length - 1;
  renderBoard(); renderKifu();
}

function finishTurn() {
  if (checkSennichite()) return;
  if (isCheckState('AI')) {
    playCheckSound(); triggerCutin('敵将へ王手！'); updateBattleDrums('advantage');
    document.getElementById('player-quote-disp').textContent = PLAYER_WARLORDS[currentMyWarlordId].quotes.check;
    document.getElementById('ai-quote-disp').textContent = WARLORDS_DATA[currentAiLevel].quotes.pinch;
  }
  if (checkGameOver('AI')) return;
  turn = 'AI';
  setOrderMessage(`【敵将思案中】${WARLORDS_DATA[currentAiLevel].name}が次の一手を巡らせております…`, false);
  setTimeout(aiTurn, 850);
}

let aiWorker = null;
const workerBlob = new Blob([workerScriptContent], { type: 'application/javascript' });
const workerUrl = URL.createObjectURL(workerBlob);

function createNewWorker() {
  if (aiWorker) aiWorker.terminate();
  aiWorker = new Worker(workerUrl);
  aiWorker.onmessage = handleWorkerMessage;
}
createNewWorker();

function handleWorkerMessage(e) {
  const data = e.data;
  const p = PLAYER_WARLORDS[currentMyWarlordId];

  if (data.type === 'hintDone') {
    isHintThinking = false;
    const bm = data.bestMove;
    if (!bm) { setOrderMessage(`${p.strategistShort}「進言できる妙手がござらぬ…！」`, true, true); return; }
    const pName = bm.type === 'drop' ? PIECES[bm.code] : PIECES[board[bm.from.r][bm.from.c]?.code || bm.code];
    
    if (data.isAwakened) {
      triggerCutin(`軍師覚醒！ ${p.strategistName}の神算鬼謀！`, true);
      setOrderMessage(`【覚醒進言】${p.strategistShort}「これぞ天下を動かす一手！ <b>${9 - bm.to.c}${KANJI_NUMS[bm.to.r]}へ${pName}</b>を進軍されよ！」`, true, true);
    } else {
      setOrderMessage(`【軍師進言】${p.strategistShort}「<b>${9 - bm.to.c}${KANJI_NUMS[bm.to.r]}へ${pName}</b>を進軍されよ！」`, true, true);
    }
    
    hintSourceCell = bm.type === 'move' ? { r: bm.from.r, c: bm.from.c } : null;
    hintTargetCell = { r: bm.to.r, c: bm.to.c };
    renderBoard(); return;
  }

  isAiThinking = false;
  if (data.evalScore !== undefined) {
    evalScoresHistory.push(data.evalScore);
    updateMoraleAndSituation(data.evalScore);
  }
  const bm = data.bestMove;
  if (!bm) { checkGameOver('AI'); return; }
  executeMove(bm);

  const targetCellEl = document.querySelector(`#board .cell:nth-child(${bm.to.r * 9 + bm.to.c + 1})`);
  if (targetCellEl) targetCellEl.classList.add('sparkle');

  if (checkSennichite()) return;

  if (!checkGameOver('PLAYER')) {
    turn = 'PLAYER';
    const pName = PLAYER_WARLORDS[currentMyWarlordId].name;
    if (isCheckState('PLAYER')) {
      playCheckSound(); triggerCutin('敵の奇襲！ 王手！'); updateBattleDrums('pinch');
      setOrderMessage(`【窮地・王手】${pName}公！ 玉を逃がすか、合駒で射線を防がれよ！`, true);
      document.getElementById('ai-quote-disp').textContent = WARLORDS_DATA[currentAiLevel].quotes.check;
      document.getElementById('player-quote-disp').textContent = PLAYER_WARLORDS[currentMyWarlordId].quotes.pinch;
    } else {
      setOrderMessage(`【自軍手番】${pName}公、次なる一手をお決め下され！`, true);
    }
  }
}

function aiTurn() {
  if (isGameOver) return;
  isAiThinking = true;
  aiWorker.postMessage({ board, hands, level: currentAiLevel, history: moveObjectsHistory });
}

function showMasterHint() {
  if (isGameOver || turn !== 'PLAYER' || isHintThinking) return;
  if (isReviewingPast()) {
    setOrderMessage('【合戦記録閲覧中】「⏭」を押して最新局面へお戻り下され。', false);
    return;
  }
  playPieceSound(); isHintThinking = true;
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const hintBtn = document.getElementById('btn-master-hint');
  const isAwakenedNow = hintBtn.classList.contains('awakened');
  
  if (isAwakenedNow) {
    setOrderMessage(`【覚醒軍師思案中】${p.strategistName}、深淵の神算鬼謀を探索中…！`, false, true);
    aiWorker.postMessage({ board, hands, level: 10, isHintRequest: true, isAwakened: true, history: moveObjectsHistory });
  } else {
    setOrderMessage(`【軍師思案中】${p.strategistName}、勝機の一手を探索中…`, false, true);
    aiWorker.postMessage({ board, hands, level: 8, isHintRequest: true, isAwakened: false, history: moveObjectsHistory });
  }
}

// 待った
function undoMove() {
  if (isGameOver || historyStates.length <= 1) return;
  playPieceSound();
  if (isAiThinking || isHintThinking) { createNewWorker(); isAiThinking = false; isHintThinking = false; }
  
  historyStates.pop();
  if (historyStates.length > 1) historyStates.pop();
  
  if (evalScoresHistory.length > 1) { evalScoresHistory.pop(); }
  if (boardHashHistory.length > 2) { boardHashHistory.pop(); boardHashHistory.pop(); }
  if (checkHistory.length > 2) { checkHistory.pop(); checkHistory.pop(); }

  const target = historyStates[historyStates.length - 1];
  board = cloneBoardState(target.board); hands = JSON.parse(JSON.stringify(target.hands));
  moveObjectsHistory = JSON.parse(JSON.stringify(target.moveObjectsHistory));
  lastMove = moveObjectsHistory[moveObjectsHistory.length - 1] || null;
  reviewingIndex = historyStates.length - 1;
  turn = 'PLAYER'; selectedPos = null; currentValidMoves = [];
  renderBoard(); renderKifu(); setOrderMessage('【待った行使】局面を戻し候。', true);
}

function surrenderGame() {
  if (isGameOver) return;
  isGameOver = true; triggerCutin('無念… 降伏いたす…');
  setOrderMessage('【敗戦】再起の陣を敷き、雪辱を期されよ！', false);
}

function checkGameOver(nextOwner) {
  if (getLegalMoves(nextOwner).length === 0) {
    isGameOver = true;
    playVictorySound();
    if (nextOwner === 'AI') {
      saveProgress(currentAiLevel); launchFireworksCelebration(); triggerCutin('敵将討ち取ったり！', true);
      if (currentAiLevel === 10) {
        document.getElementById('ai-quote-disp').textContent = '「見事なり… 乱世を鎮むる器、確かに見届けた…」';
        setOrderMessage('【天下統一！】徳川幕府を平定し、日ノ本の覇者となり候！ 誠に見事！', false);
      } else {
        setOrderMessage('【大勝利！】敵本陣を陥落させ候！ 天下平定！', false);
      }
    } else {
      triggerCutin('本陣陥落… 敗北に候…');
      setOrderMessage('【敗戦】敵将に敗れ候。再起を期されよ！', false);
    }
    return true;
  }
  return false;
}

function updateMoraleAndSituation(scoreAI) {
  const pScore = -scoreAI;
  let pPct = Math.round(100 / (1 + Math.exp(-pScore / 600)));
  pPct = Math.max(5, Math.min(95, pPct));
  document.getElementById('player-morale-bar').style.width = `${pPct}%`;
  document.getElementById('ai-morale-bar').style.width = `${100 - pPct}%`;
  document.getElementById('player-morale-val').textContent = `士気 ${pPct}`;
  document.getElementById('ai-morale-val').textContent = `士気 ${100 - pPct}`;
  
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const hintBtn = document.getElementById('btn-master-hint');
  const isPinchState = (pPct <= 35) || isCheckState('PLAYER');
  const canAwaken = (currentAiLevel >= 8) && isPinchState;

  if (canAwaken && !isGameOver) {
    hintBtn.classList.add('awakened');
    hintBtn.textContent = `🔥 覚醒${p.strategistShort}`;
  } else {
    hintBtn.classList.remove('awakened');
    hintBtn.textContent = `💡 ${p.strategistShort}進言`;
  }

  const sit = document.getElementById('situation-text');
  if (pPct >= 70) {
    sit.textContent = '我が軍圧倒的優勢！ 敵本陣を包囲せり！'; updateBattleDrums('advantage');
    document.getElementById('player-quote-disp').textContent = p.quotes.adv;
  } else if (pPct <= 30) {
    sit.textContent = '我が陣営に乱れあり！ 敵の猛攻を耐え忍ばれよ！'; updateBattleDrums('pinch');
    document.getElementById('player-quote-disp').textContent = p.quotes.pinch;
  } else {
    sit.textContent = '互角の白兵戦。一手一手が天下の行方を左右し候。'; updateBattleDrums('normal');
  }
}

function stepReview(dir) {
  if (historyStates.length <= 1) return;
  playPieceSound();
  if (reviewingIndex === -1) reviewingIndex = historyStates.length - 1;
  const targetIdx = reviewingIndex + dir;
  if (targetIdx < 0 || targetIdx >= historyStates.length) return;
  reviewingIndex = targetIdx;
  const snap = historyStates[reviewingIndex];
  board = cloneBoardState(snap.board);
  hands = JSON.parse(JSON.stringify(snap.hands));
  lastMove = (reviewingIndex > 0) ? snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] : null;
  renderBoard();
  renderKifu();
  setOrderMessage(`【合戦絵巻鑑賞中】${reviewingIndex}手目の布陣を表示中（「⏭」で最新へ）`, false);
}

function resetToLatestReview() {
  if (historyStates.length <= 1 || reviewingIndex === historyStates.length - 1) return;
  playPieceSound();
  reviewingIndex = historyStates.length - 1;
  const snap = historyStates[reviewingIndex];
  board = cloneBoardState(snap.board);
  hands = JSON.parse(JSON.stringify(snap.hands));
  lastMove = snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] || null;
  renderBoard();
  renderKifu();
  setOrderMessage(`【最新局面復帰】${PLAYER_WARLORDS[currentMyWarlordId].name}公、一手をお決め下され！`, turn === 'PLAYER');
}

// 棋譜帯の描画
function renderKifu() {
  const st = document.getElementById('kifu-stream'); st.innerHTML = '';
  moveObjectsHistory.forEach((m, idx) => {
    const s = document.createElement('div');
    s.className = `kifu-item-cell ${reviewingIndex === idx + 1 ? 'active-review' : ''}`;
    
    const rawCode = m.code || 'FU';
    const pName = m.type === 'drop' ? PIECES[m.code] : (m.promote ? (PIECES[PROMOTE_MAP[rawCode]] || PIECES[rawCode]) : PIECES[rawCode]);
    s.textContent = `${idx + 1}.${9 - m.to.c}${KANJI_NUMS[m.to.r]}${pName}`;
    s.onclick = () => {
      reviewingIndex = idx + 1;
      const snap = historyStates[reviewingIndex];
      board = cloneBoardState(snap.board);
      hands = JSON.parse(JSON.stringify(snap.hands));
      lastMove = snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] || null;
      renderBoard();
      renderKifu();
      setOrderMessage(`【合戦絵巻鑑賞中】${reviewingIndex}手目の布陣を表示中（「⏭」で最新へ）`, false);
    };
    st.appendChild(s);
  });
  if (reviewingIndex === -1 || reviewingIndex === historyStates.length - 1) st.scrollLeft = st.scrollWidth;
}

/* 棋譜モーダル表示 */
function openKifuModal() {
  const pName = PLAYER_WARLORDS[currentMyWarlordId].name;
  const eName = WARLORDS_DATA[currentAiLevel].name;

  document.getElementById('chart-player-name-tag').textContent = `▲ 我が軍【${pName}】優勢`;
  document.getElementById('chart-enemy-name-tag').textContent = `▽ 敵軍【${eName}】優勢`;

  const curSitText = document.getElementById('situation-text').textContent;
  document.getElementById('kifu-modal-situation-text').textContent = curSitText;

  const curEvalAI = evalScoresHistory[evalScoresHistory.length - 1] || 0;
  const curPlayerScore = -curEvalAI;
  const badgeEl = document.getElementById('kifu-modal-status-badge');
  if (curPlayerScore >= 1200) { badgeEl.textContent = '我が軍【勝勢】'; badgeEl.style.color = '#ffd700'; }
  else if (curPlayerScore >= 400) { badgeEl.textContent = '我が軍【優勢】'; badgeEl.style.color = '#76ff03'; }
  else if (curPlayerScore <= -1200) { badgeEl.textContent = '我が軍【敗勢】'; badgeEl.style.color = '#ff3d00'; }
  else if (curPlayerScore <= -400) { badgeEl.textContent = '我が軍【劣勢】'; badgeEl.style.color = '#4fc3f7'; }
  else { badgeEl.textContent = '戦況【互角】'; badgeEl.style.color = '#ffeb3b'; }

  const l = document.getElementById('kifu-list'); l.innerHTML = '';
  const pScores = evalScoresHistory.map(s => -s);

  moveObjectsHistory.forEach((m, idx) => {
    const d = document.createElement('div');
    d.className = 'kifu-row-item';

    const rawCode = m.code || 'FU';
    const pPiece = m.type === 'drop' ? PIECES[m.code] : PIECES[rawCode];
    const mark = m.owner === 'PLAYER' ? '▲' : '△';
    const moveStr = `${idx + 1}手目：${mark} ${9 - m.to.c}${KANJI_NUMS[m.to.r]} ${pPiece}${m.promote ? '成' : ''}`;

    const prevS = pScores[idx] !== undefined ? pScores[idx] : 0;
    const curS = pScores[idx + 1] !== undefined ? pScores[idx + 1] : prevS;
    const delta = curS - prevS;

    let badgeHtml = '';
    if (delta >= 400) {
      d.classList.add('kifu-row-critical');
      badgeHtml = `<span class="kifu-badge-critical badge-tennozan">🔥 天王山 (+${delta})</span>`;
    } else if (delta <= -400) {
      d.classList.add('kifu-row-critical');
      badgeHtml = `<span class="kifu-badge-critical badge-shock">⚡ 激震 (${delta})</span>`;
    }

    d.innerHTML = `<span class="kifu-move-txt">${moveStr}</span>${badgeHtml}`;
    d.onclick = () => {
      reviewingIndex = idx + 1;
      const snap = historyStates[reviewingIndex];
      board = cloneBoardState(snap.board);
      hands = JSON.parse(JSON.stringify(snap.hands));
      lastMove = snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] || null;
      renderBoard();
      renderKifu();
      closeKifuModal();
      setOrderMessage(`【合戦絵巻鑑賞中】${reviewingIndex}手目の局面（「⏭」で最新へ）`, false);
    };
    l.appendChild(d);
  });

  document.getElementById('kifu-modal').style.display = 'flex';
  setTimeout(drawEvaluationChart, 50);
}
function closeKifuModal() { document.getElementById('kifu-modal').style.display = 'none'; }

/* 形勢推移チャート描画 */
function drawEvaluationChart() {
  const cvs = document.getElementById('chart-canvas');
  if (!cvs) return;
  const dpr = window.devicePixelRatio || 1;
  const rect = cvs.getBoundingClientRect();
  cvs.width = (rect.width || 450) * dpr;
  cvs.height = (rect.height || 140) * dpr;
  const ctx = cvs.getContext('2d');
  const w = cvs.width, h = cvs.height;
  ctx.clearRect(0, 0, w, h);

  const midY = h / 2;

  const playerBg = ctx.createLinearGradient(0, 0, 0, midY);
  playerBg.addColorStop(0, 'rgba(180, 25, 25, 0.45)');
  playerBg.addColorStop(1, 'rgba(60, 20, 5, 0.15)');
  ctx.fillStyle = playerBg;
  ctx.fillRect(0, 0, w, midY);

  const enemyBg = ctx.createLinearGradient(0, midY, 0, h);
  enemyBg.addColorStop(0, 'rgba(10, 25, 50, 0.15)');
  enemyBg.addColorStop(1, 'rgba(15, 35, 75, 0.55)');
  ctx.fillStyle = enemyBg;
  ctx.fillRect(0, midY, w, midY);

  ctx.strokeStyle = 'rgba(255, 215, 0, 0.15)';
  ctx.lineWidth = 1 * dpr;
  ctx.setLineDash([3 * dpr, 3 * dpr]);
  [midY - h * 0.35, midY - h * 0.18, midY + h * 0.35, midY + h * 0.18].forEach(y => {
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(w, y); ctx.stroke();
  });

  ctx.setLineDash([]);
  ctx.strokeStyle = 'rgba(255, 215, 0, 0.85)';
  ctx.lineWidth = 1.6 * dpr;
  ctx.beginPath(); ctx.moveTo(0, midY); ctx.lineTo(w, midY); ctx.stroke();

  if (evalScoresHistory.length < 2) return;

  const count = evalScoresHistory.length;
  const step = w / Math.max(1, count - 1);
  const maxEval = 2200;

  const pScores = evalScoresHistory.map(s => -s);
  const points = pScores.map((pScore, idx) => {
    const clamped = Math.max(-maxEval, Math.min(maxEval, pScore));
    const y = midY - (clamped / maxEval) * (midY * 0.86);
    const x = idx * step;
    return { x, y, pScore, idx };
  });

  ctx.beginPath();
  ctx.moveTo(points[0].x, midY);
  points.forEach(pt => ctx.lineTo(pt.x, pt.y));
  ctx.lineTo(points[points.length - 1].x, midY);
  ctx.closePath();
  const fillGrad = ctx.createLinearGradient(0, 0, 0, h);
  fillGrad.addColorStop(0, 'rgba(255, 215, 0, 0.65)');
  fillGrad.addColorStop(0.5, 'rgba(255, 215, 0, 0.12)');
  fillGrad.addColorStop(1, 'rgba(68, 138, 255, 0.55)');
  ctx.fillStyle = fillGrad;
  ctx.fill();

  ctx.beginPath();
  ctx.lineWidth = 2.8 * dpr;
  ctx.strokeStyle = '#fff089';
  ctx.shadowColor = '#ffd700';
  ctx.shadowBlur = 6 * dpr;
  points.forEach((pt, idx) => {
    if (idx === 0) ctx.moveTo(pt.x, pt.y); else ctx.lineTo(pt.x, pt.y);
  });
  ctx.stroke();
  ctx.shadowBlur = 0;

  for (let i = 1; i < points.length; i++) {
    const delta = points[i].pScore - points[i - 1].pScore;
    if (Math.abs(delta) >= 400) {
      const pt = points[i];
      ctx.beginPath();
      ctx.arc(pt.x, pt.y, 6.5 * dpr, 0, Math.PI * 2);
      ctx.fillStyle = delta > 0 ? '#ff1744' : '#0277bd';
      ctx.strokeStyle = '#ffd700';
      ctx.lineWidth = 1.8 * dpr;
      ctx.fill();
      ctx.stroke();

      ctx.beginPath();
      ctx.arc(pt.x, pt.y, 2.5 * dpr, 0, Math.PI * 2);
      ctx.fillStyle = '#ffffff';
      ctx.fill();
    }
  }

  const lastPt = points[points.length - 1];
  ctx.beginPath();
  ctx.arc(lastPt.x, lastPt.y, 4.5 * dpr, 0, Math.PI * 2);
  ctx.fillStyle = '#ffffff';
  ctx.strokeStyle = '#ff9100';
  ctx.lineWidth = 2.2 * dpr;
  ctx.fill();
  ctx.stroke();

  document.getElementById('chart-eval-num-top').textContent = lastPt.pScore >= 0 ? `+${lastPt.pScore}` : '';
  document.getElementById('chart-eval-num-bottom').textContent = lastPt.pScore < 0 ? `${lastPt.pScore}` : '';
}

function openGuideModal() { document.getElementById('guide-modal').style.display = 'flex'; }
function closeGuideModal() { document.getElementById('guide-modal').style.display = 'none'; }
function switchGuideTab(tabIdx) {
  playPieceSound();
  const btns = document.querySelectorAll('.guide-tab-btn');
  btns.forEach((b, idx) => b.classList.toggle('active', idx + 1 === tabIdx));
  for (let i = 1; i <= 4; i++) {
    const pane = document.getElementById(`guide-pane-${i}`);
    if (pane) pane.classList.toggle('active', i === tabIdx);
  }
}

function openConquestMapModal() { updateConquestMapUI(); document.getElementById('conquest-modal').style.display = 'flex'; }
function closeConquestMapModal() { document.getElementById('conquest-modal').style.display = 'none'; }

// 自将モーダル
function openPlayerWarlordModal() {
  const l = document.getElementById('player-warlord-list'); l.innerHTML = '';
  for(let k in PLAYER_WARLORDS) {
    const p = PLAYER_WARLORDS[k];
    const d = document.createElement('div');
    d.className = `warlord-select-card btn-3d ${k === currentMyWarlordId ? 'active' : ''}`;
    d.innerHTML = `
      <div class="card-avatar-mini" style="background:${p.bgGrad};">
        ${getWarlordPortraitHtml(p)}
      </div>
      <div class="card-info-col">
        <div class="card-name-title">${p.name}</div>
        <div class="card-clan-tag">${p.clan}</div>
        <div class="card-strategist-tag">軍師: ${p.strategistName} (${p.strategistTitle})</div>
      </div>`;
    d.onclick = () => { setPlayerWarlord(k); closePlayerWarlordModal(); };
    l.appendChild(d);
  }
  document.getElementById('player-warlord-modal').style.display = 'flex';
}
function closePlayerWarlordModal() { document.getElementById('player-warlord-modal').style.display = 'none'; }

// 国盗り絵巻UI
function updateConquestMapUI() {
  const clearedCount = clearedProvinces.length;
  document.getElementById('conquest-pct-disp').textContent = `${clearedCount * 10}%`;
  document.getElementById('conquest-pct-bar').style.width = `${clearedCount * 10}%`;
  document.getElementById('conquest-cleared-count').textContent = `${clearedCount} / 10 国平定`;

  const maxAvailableLevel = clearedCount > 0 ? Math.min(10, Math.max(...clearedProvinces) + 1) : 1;

  for(let i=1; i<=10; i++) {
    const n = document.getElementById(`map-node-${i}`);
    if (n) {
      n.classList.remove('cleared', 'current', 'locked');
      if (clearedProvinces.includes(i)) {
        n.classList.add('cleared');
      } else if (i === currentAiLevel) {
        n.classList.add('current');
      } else if (i > maxAvailableLevel) {
        n.classList.add('locked');
      }
    }
  }

  const l = document.getElementById('conquest-warlord-list'); l.innerHTML = '';
  for(let i=1; i<=10; i++) {
    const w = WARLORDS_DATA[i];
    const isCleared = clearedProvinces.includes(i);
    const isLocked = !isCleared && (i > maxAvailableLevel);
    const isCurrent = (i === currentAiLevel);

    const d = document.createElement('div');
    d.className = `conquest-card-item btn-3d ${isCurrent ? 'selected' : ''} ${isCleared ? 'cleared' : ''} ${isLocked ? 'locked' : ''}`;
    
    let badgeHtml = '';
    if (isCleared) badgeHtml = `<span class="conquest-status-badge badge-conquered">平定済</span>`;
    else if (isLocked) badgeHtml = `<span class="conquest-status-badge badge-locked">未開放</span>`;
    else badgeHtml = `<span class="conquest-status-badge badge-challenge">進軍可</span>`;

    d.innerHTML = `
      <div class="conquest-card-left">
        <div class="conquest-avatar-thumb">${getWarlordPortraitHtml(w)}</div>
        <div>
          <b>Lv.${i} ${w.province} ｜ ${w.name}</b>
          <div style="font-size:9.5px;color:#d6be89;">${w.clan}</div>
        </div>
      </div>
      <div>${badgeHtml}</div>`;

    if (!isLocked) {
      d.onclick = () => { selectConquestProvince(i); closeConquestMapModal(); };
    }
    l.appendChild(d);
  }
}

function selectConquestProvince(lvl) {
  const clearedCount = clearedProvinces.length;
  const maxAvailableLevel = clearedCount > 0 ? Math.min(10, Math.max(...clearedProvinces) + 1) : 1;
  if (!clearedProvinces.includes(lvl) && lvl > maxAvailableLevel) return;

  currentAiLevel = lvl;
  const w = WARLORDS_DATA[lvl];
  document.getElementById('ai-name-disp').textContent = w.name;
  document.getElementById('ai-clan-disp').textContent = w.clan;
  document.getElementById('ai-quote-disp').textContent = w.quotes.default;
  document.getElementById('ai-power-disp').textContent = w.power;
  
  // 対局画面敵将ポートレートの更新
  const aiBox = document.getElementById('ai-avatar-container');
  if (aiBox) aiBox.innerHTML = getWarlordPortraitHtml(w);

  document.getElementById('btn-enemy-change').textContent = `🗺 ${w.province} (Lv.${lvl})`;
  
  updateWarlordBGM(lvl);
  updateConquestMapUI();

  const rivalKey = `${currentMyWarlordId}_${currentAiLevel}`;
  if (RIVALRIES[rivalKey]) {
    setOrderMessage(`【宿命の因縁！】${RIVALRIES[rivalKey].title}<br>「対局開始」を押して雌雄を決されよ！`, true);
  } else {
    setOrderMessage(`【進軍先決定】${w.province}・「${w.name}」との決戦に候！<br>「対局開始」を押されよ。`, false);
  }
}

function setPlayerWarlord(k) {
  currentMyWarlordId = k;
  try { localStorage.setItem('shogi_my_warlord', k); } catch(e){}
  const p = PLAYER_WARLORDS[k];
  document.documentElement.style.setProperty('--player-theme-color', p.themeColor);
  document.getElementById('player-name-disp').textContent = p.name;
  document.getElementById('player-clan-disp').textContent = p.clan;
  document.getElementById('player-quote-disp').textContent = p.quotes.default;
  
  // 対局画面自将ポートレートの更新
  const pBox = document.getElementById('player-avatar-container');
  if (pBox) pBox.innerHTML = getWarlordPortraitHtml(p);

  updateStrategistUI();
  selectConquestProvince(currentAiLevel);
}

// 正式なKIF形式に準拠した保存出力
function downloadKifu() {
  const pName = PLAYER_WARLORDS[currentMyWarlordId].name;
  const eName = WARLORDS_DATA[currentAiLevel].name;
  const now = new Date();
  const dateStr = `${now.getFullYear()}/${(now.getMonth()+1).toString().padStart(2,'0')}/${now.getDate().toString().padStart(2,'0')}`;

  let txt = `#KIF version=2.0 encoding=UTF-8\n`;
  txt += `開始日時：${dateStr}\n`;
  txt += `棋戦：将棋王 2026 〜 天下統一・戦国決戦 〜\n`;
  txt += `手合割：平手\n`;
  txt += `先手：${pName}\n`;
  txt += `後手：${eName}\n`;
  txt += `手数----指手---------消費時間--\n`;

  moveObjectsHistory.forEach((m, i) => {
    const rawCode = m.code || 'FU';
    const pPiece = m.type === 'drop' ? PIECES[m.code] : PIECES[rawCode];
    const promoteStr = m.promote ? '成' : '';
    const toStr = `${9 - m.to.c}${KANJI_NUMS[m.to.r]}`;
    const fromStr = m.type === 'drop' ? '打' : `(${9 - m.from.c}${9 - m.from.r})`;

    const stepNum = (i + 1).toString().padStart(4, ' ');
    txt += `${stepNum} ${toStr}${pPiece}${promoteStr}${fromStr}\n`;
  });

  const b = new Blob([txt], { type: 'text/plain;charset=UTF-8' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(b);
  a.download = `将棋王_戦国合戦棋譜_${pName}対${eName}.kif`;
  a.click();
}

/* 起動イベント */
document.addEventListener('click', () => initAudio(), { once: true });
document.addEventListener('touchstart', () => initAudio(), { once: true });

loadProgress();
setPlayerWarlord(currentMyWarlordId);
initBoardState();


