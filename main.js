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
let moveHistory = [], pastHashes = [], currentLevel = 1;

// レベル別探索設定
const LEVEL_CFG = {
  1:  { depth: 1, qDepth: 1, time: 400 },
  2:  { depth: 1, qDepth: 2, time: 600 },
  3:  { depth: 2, qDepth: 3, time: 900 },
  4:  { depth: 2, qDepth: 4, time: 1300 },
  5:  { depth: 3, qDepth: 4, time: 1800 },
  6:  { depth: 3, qDepth: 5, time: 2400 },
  7:  { depth: 4, qDepth: 5, time: 3000 },
  8:  { depth: 4, qDepth: 6, time: 3500 },
  9:  { depth: 5, qDepth: 6, time: 4000 },
  10: { depth: 5, qDepth: 7, time: 5000 }
};

function getBoardHash(b, h, t) {
  let s = t + ':';
  for(let r=0; r<9; r++) for(let c=0; c<9; c++) {
    const p = b[r][c]; if (p) s += r + '' + c + p.code + p.owner[0] + '|';
  }
  for (const ow of ['PLAYER','AI']) for (const k in h[ow]) {
    if (h[ow][k] > 0) s += ow[0] + k + h[ow][k];
  }
  return s;
}

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
          if (p.code === 'HI' && c === 2) score += 45;
        }
        if (currentLevel === 5) {
          if (p.code === 'FU' && r >= 5) score += 25;
        }
        if (currentLevel === 6) {
          if (p.code === 'KA' || p.code === 'UM') val *= 1.25;
        }
        if (currentLevel === 7) {
          if (['KI','GI'].includes(p.code) && r <= 2) score += 30;
        }
        if (currentLevel === 8) {
          if (p.code === 'RY' || p.code === 'UM') val *= 1.28;
        }
        if (currentLevel === 9) {
          if (['KI','GI'].includes(p.code) && r >= 5) score += 35;
        }
      }

      score += sign * val;

      if (p.code !== 'OU') {
        const myDefs = defenseCount[p.owner][r][c];
        const opp = p.owner === 'AI' ? 'PLAYER' : 'AI';
        const oppAttacks = defenseCount[opp][r][c];
        if (myDefs > 0) score += sign * 28;
        if (oppAttacks > myDefs) {
          const penaltyRate = (currentLevel === 1) ? 0.20 : 0.42;
          score -= sign * (val * penaltyRate);
        }
      }

      if (p.code === 'FU' || p.code === 'GI') {
        const advBonus = (currentLevel === 3) ? 18 : 10;
        score += sign * (p.owner === 'AI' ? r * advBonus : (8 - r) * advBonus);
        if (c >= 2 && c <= 6) score += sign * 15;
      }
    }
  }

  const kingGuardBonus = (currentLevel === 10) ? 80 : ((currentLevel === 7) ? 90 : 45);
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

  const handMul = (currentLevel === 9) ? 1.30 : 1.15;
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
        score -= 500;
      }
    }

    if (score > bestVal) bestVal = score;
    if (score > alpha) alpha = score;
    if (alpha >= beta) break;
  }
  return bestVal;
}

self.onmessage = function(e) {
  const { board: bD, hands: hD, level = 1, isHintRequest = false, isAwakened = false, history = [], hashHistory = [] } = e.data;
  board = bD; hands = hD; moveHistory = history; pastHashes = hashHistory; currentLevel = level;
  searchStartTime = Date.now(); isSearchTimeout = false; nodeCount = 0;
  const searchOwner = isHintRequest ? 'PLAYER' : 'AI', enemyOwner = isHintRequest ? 'AI' : 'PLAYER';
  const curEval = evaluatePosition();

  let cfg = isHintRequest ? (isAwakened ? { depth: 5, qDepth: 7, time: 5000 } : { depth: 4, qDepth: 5, time: 3000 })
                          : (LEVEL_CFG[level] || LEVEL_CFG[1]);
  searchTimeLimit = cfg.time;

  const legals = genLegalMoves(searchOwner, false, true);
  if (legals.length === 0) {
    self.postMessage({ type: isHintRequest ? 'hintDone' : 'done', bestMove: null, candidateMoves: [], evalScore: curEval });
    return;
  }

  const calcPenalty = (m) => {
    let penalty = 0;
    const undo = makeMove(m);
    const nextHash = getBoardHash(board, hands, enemyOwner);
    const hashOccurrences = pastHashes.filter(h => h === nextHash).length;
    if (hashOccurrences >= 2) penalty += 4000;
    else if (hashOccurrences === 1) penalty += 1500;

    if (moveHistory.length >= 2) {
      const lastOwnerMove = moveHistory[moveHistory.length - 2];
      if (m.type === 'move' && lastOwnerMove?.type === 'move') {
        if (m.to.r === lastOwnerMove.from.r && m.to.c === lastOwnerMove.from.c &&
            m.from.r === lastOwnerMove.to.r && m.from.c === lastOwnerMove.to.c) {
          penalty += 2800;
        }
      }
    }
    unmakeMove(undo);
    return penalty;
  };

  let scoredMoves = legals.map(m => ({ move: m, score: 0 }));

  for (let d = 1; d <= cfg.depth; d++) {
    let alpha = -Infinity, beta = Infinity;
    for (let i = 0; i < scoredMoves.length; i++) {
      const m = scoredMoves[i].move;
      const penalty = calcPenalty(m);
      const undo = makeMove(m);
      let s = -negamax(d - 1, -beta, -alpha, enemyOwner, cfg.qDepth) - penalty;
      unmakeMove(undo);

      scoredMoves[i].score = s;
      if (isSearchTimeout) break;
      if (s > alpha) alpha = s;
    }
    scoredMoves.sort((a, b) => b.score - a.score);
    if (!isHintRequest) {
      self.postMessage({ type: 'progress', depth: d, evalScore: scoredMoves[0].score });
    }
    if (isSearchTimeout || Date.now() - searchStartTime >= searchTimeLimit) break;
  }

  let bestMove = scoredMoves[0] ? scoredMoves[0].move : null;
  if (!isHintRequest && currentLevel === 1 && scoredMoves.length > 1) {
    if (Math.random() < 0.40) {
      const subIdx = Math.min(scoredMoves.length - 1, Math.floor(Math.random() * 3) + 1);
      bestMove = scoredMoves[subIdx].move;
    }
  }

  const bestScore = scoredMoves[0] ? scoredMoves[0].score : curEval;

  self.postMessage({
    type: isHintRequest ? 'hintDone' : 'done',
    bestMove,
    allScoredMoves: scoredMoves,
    evalScore: bestScore,
    isAwakened
  });
};
`;

/* =========================================================
   音響エンジン（本格二層木質合成：乾いた「パチッ」駒音）
   ========================================================= */
let audioCtx = null, soundEnabled = true, isPageHidden = false;
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

  if (bgmAudio && soundEnabled && !isPageHidden) {
    const src = BGM_TRACKS[targetTrack] || 'nobunaga_song.mp3';
    bgmAudio.src = src;
    bgmAudio.play().catch(() => {});
  }
}

function initAudio() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  if (audioCtx.state === 'suspended' && !isPageHidden) audioCtx.resume();
  if (!isPageHidden) startBgm();
}
function startBgm() {
  if (!soundEnabled || !bgmAudio || isPageHidden) return;
  bgmAudio.play().catch(() => {});
}
function pauseBgm() {
  if (bgmAudio) bgmAudio.pause();
}
function toggleSound() {
  soundEnabled = !soundEnabled;
  document.getElementById('sound-toggle').textContent = `♪ ${soundEnabled ? '音ON' : '音OFF'}`;
  if (soundEnabled) { initAudio(); startBgm(); }
  else { pauseBgm(); }
}

function handleVisibilityChange() {
  if (document.hidden) {
    isPageHidden = true;
    pauseBgm();
    stopGuideSpeech();
    stopAutoReplay();
    if (audioCtx && audioCtx.state === 'running') {
      audioCtx.suspend().catch(() => {});
    }
  } else {
    isPageHidden = false;
    if (soundEnabled) {
      if (audioCtx && audioCtx.state === 'suspended') {
        audioCtx.resume().catch(() => {});
      }
      startBgm();
    }
  }
}
document.addEventListener('visibilitychange', handleVisibilityChange);
window.addEventListener('pagehide', () => { isPageHidden = true; pauseBgm(); stopGuideSpeech(); stopAutoReplay(); });
window.addEventListener('pageshow', () => { isPageHidden = false; if (soundEnabled) startBgm(); });

function playPieceSound() {
  if (!soundEnabled || isPageHidden) return;
  initAudio();
  const now = audioCtx.currentTime;

  try {
    const bufferSize = Math.floor(audioCtx.sampleRate * 0.018);
    const noiseBuffer = audioCtx.createBuffer(1, bufferSize, audioCtx.sampleRate);
    const output = noiseBuffer.getChannelData(0);
    for (let i = 0; i < bufferSize; i++) {
      output[i] = (Math.random() * 2 - 1) * Math.exp(-i / (bufferSize * 0.22));
    }
    const whiteNoise = audioCtx.createBufferSource();
    whiteNoise.buffer = noiseBuffer;

    const noiseFilter = audioCtx.createBiquadFilter();
    noiseFilter.type = 'bandpass';
    noiseFilter.frequency.setValueAtTime(1800, now);
    noiseFilter.Q.setValueAtTime(1.8, now);

    const noiseGain = audioCtx.createGain();
    noiseGain.gain.setValueAtTime(0.85, now);
    noiseGain.gain.exponentialRampToValueAtTime(0.001, now + 0.018);

    whiteNoise.connect(noiseFilter);
    noiseFilter.connect(noiseGain);
    noiseGain.connect(audioCtx.destination);
    whiteNoise.start(now);
  } catch (e) {}

  const osc = audioCtx.createOscillator();
  const oscGain = audioCtx.createGain();
  osc.type = 'triangle';
  osc.frequency.setValueAtTime(260, now);
  osc.frequency.exponentialRampToValueAtTime(85, now + 0.065);

  oscGain.gain.setValueAtTime(0.55, now);
  oscGain.gain.exponentialRampToValueAtTime(0.001, now + 0.07);

  osc.connect(oscGain);
  oscGain.connect(audioCtx.destination);

  osc.start(now);
  osc.stop(now + 0.075);
}

function playCheckSound() {
  if (!soundEnabled || isPageHidden) return; initAudio();
  const now = audioCtx.currentTime, osc = audioCtx.createOscillator(), g = audioCtx.createGain();
  osc.type = 'sine'; osc.frequency.setValueAtTime(110, now); osc.frequency.exponentialRampToValueAtTime(38, now + 0.5);
  g.gain.setValueAtTime(0.7, now); g.gain.exponentialRampToValueAtTime(0.001, now + 0.55);
  osc.connect(g); g.connect(audioCtx.destination);
  osc.start(now); osc.stop(now + 0.55);
}

function playVictorySound() {
  if (!soundEnabled || isPageHidden) return; initAudio();
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
   Web Speech API
   ========================================================= */
let guideVoiceGender = 'male';
let currentReadingCardId = null;

function setGuideVoiceGender(gender) {
  playPieceSound();
  guideVoiceGender = gender;
  document.getElementById('btn-voice-male').classList.toggle('active', gender === 'male');
  document.getElementById('btn-voice-female').classList.toggle('active', gender === 'female');
  if (currentReadingCardId) {
    const cardId = currentReadingCardId;
    stopGuideSpeech();
    toggleCardSpeech(cardId);
  }
}

function stopGuideSpeech() {
  if ('speechSynthesis' in window) {
    window.speechSynthesis.cancel();
  }
  if (currentReadingCardId) {
    const cardEl = document.getElementById(currentReadingCardId);
    if (cardEl) {
      cardEl.classList.remove('reading-active');
      const btn = cardEl.querySelector('.card-speech-btn');
      if (btn) btn.innerHTML = '🔊 朗読';
    }
    currentReadingCardId = null;
  }
}

function cleanSpeechText(rawText) {
  let text = rawText;
  text = text.replace(/🔊\s*朗読/g, '').replace(/⏹\s*停止/g, '');
  text = text.replace(/[⚜🪭📜🔰🔥🛡⚔👑🏯💡⚖▶◀⏭♪🎞]/g, '');

  text = text.replace(/７六歩/g, 'ななろくふ、');
  text = text.replace(/２六歩/g, 'にいろくふ、');
  text = text.replace(/４八銀/g, 'よんはちぎん、');
  text = text.replace(/６八玉/g, 'ろくはちぎょく、');
  text = text.replace(/２五歩/g, 'にすごふ、');
  text = text.replace(/５筋/g, 'ごすじ');
  text = text.replace(/１筋/g, 'いちすじ');
  text = text.replace(/９筋/g, 'きゅうすじ');
  text = text.replace(/Lv\.(\d+)/gi, 'レベル$1、');
  text = text.replace(/三間飛車/g, 'さんげんびしゃ');
  text = text.replace(/飛車/g, 'ひしゃ');
  text = text.replace(/角行/g, 'かくぎょう');
  text = text.replace(/龍王/g, 'りゅうおう');
  text = text.replace(/龍馬/g, 'りゅうま');
  text = text.replace(/成駒/g, 'なりごま');
  text = text.replace(/金銀/g, 'きんぎん');
  text = text.replace(/詰ます/g, 'つます');
  text = text.replace(/詰めろ/g, 'つめろ');
  text = text.replace(/王手/g, 'おうて');
  text = text.replace(/千日手/g, 'せんにちて');
  text = text.replace(/vs/gi, '、対、');

  text = text.replace(/【/g, '、').replace(/】/g, '、');
  text = text.replace(/・/g, '。');
  text = text.replace(/\s+/g, ' ').trim();
  return text;
}

function toggleCardSpeech(cardId) {
  if (!('speechSynthesis' in window)) {
    alert('ご使用の端末は音声読み上げに対応しておりませぬ。');
    return;
  }

  if (currentReadingCardId === cardId) {
    stopGuideSpeech();
    return;
  }

  stopGuideSpeech();

  const cardEl = document.getElementById(cardId);
  if (!cardEl) return;

  const btn = cardEl.querySelector('.card-speech-btn');
  const rawText = cardEl.innerText;
  const speechText = cleanSpeechText(rawText);

  if (!speechText) return;

  initAudio();
  currentReadingCardId = cardId;
  cardEl.classList.add('reading-active');
  if (btn) btn.innerHTML = '⏹ 停止';

  const uttr = new SpeechSynthesisUtterance(speechText);
  uttr.lang = 'ja-JP';

  const voices = window.speechSynthesis.getVoices();
  const jaVoices = voices.filter(v => v.lang === 'ja' || v.lang === 'ja-JP' || v.lang.startsWith('ja'));

  if (guideVoiceGender === 'female') {
    const fVoice = jaVoices.find(v => /female|kyoko|haruka|ayumi|sayaka|nanami|hikari/i.test(v.name));
    if (fVoice) uttr.voice = fVoice;
    uttr.pitch = 1.15;
    uttr.rate = 0.96;
  } else {
    const mVoice = jaVoices.find(v => /male|otoya|keita|ichiro|hattori|kenji/i.test(v.name));
    if (mVoice) uttr.voice = mVoice;
    uttr.pitch = 0.85;
    uttr.rate = 0.93;
  }

  uttr.onend = () => {
    if (currentReadingCardId === cardId) {
      cardEl.classList.remove('reading-active');
      if (btn) btn.innerHTML = '🔊 朗読';
      currentReadingCardId = null;
    }
  };

  uttr.onerror = () => {
    if (currentReadingCardId === cardId) {
      cardEl.classList.remove('reading-active');
      if (btn) btn.innerHTML = '🔊 朗読';
      currentReadingCardId = null;
    }
  };

  window.speechSynthesis.speak(uttr);
}

if ('speechSynthesis' in window) {
  window.speechSynthesis.onvoiceschanged = () => {
    window.speechSynthesis.getVoices();
  };
}

/* =========================================================
   武将ポートレート・アバター表示管理
   ========================================================= */
let avatarViewMode = { player: 'face', ai: 'face' };

function toggleWarlordAvatarView(side) {
  playPieceSound();
  avatarViewMode[side] = (avatarViewMode[side] === 'face') ? 'crest' : 'face';
  const containerId = (side === 'player') ? 'player-avatar-container' : 'ai-avatar-container';
  const box = document.querySelector(`#${containerId} .portrait-container-box`);
  if (box) {
    box.classList.toggle('show-crest', avatarViewMode[side] === 'crest');
  }
}

function getWarlordPortraitHtml(warlordData, isInteractive = false, side = null) {
  const baseName = warlordData.customImg || `images/${warlordData.id}`;
  const pngPath = `${baseName}.png`;
  const jpgPath = `${baseName}.jpg`;
  const webpPath = `${baseName}.webp`;

  const showCrestClass = (isInteractive && side && avatarViewMode[side] === 'crest') ? 'show-crest' : '';

  return `
    <div class="portrait-container-box ${showCrestClass}">
      <div class="portrait-crest-svg">
        <svg viewBox="0 0 100 100">
          ${warlordData.portraitSvg}
        </svg>
      </div>
      <img src="${pngPath}" 
           alt="${warlordData.name}" 
           class="portrait-face-img"
           onload="
             this.closest('.portrait-container-box').classList.add('portrait-has-image');
           "
           onerror="
             if (!this.dataset.triedJpg) {
               this.dataset.triedJpg = 'true';
               this.src = '${jpgPath}';
             } else if (!this.dataset.triedWebp) {
               this.dataset.triedWebp = 'true';
               this.src = '${webpPath}';
             } else {
               this.remove();
             }
           ">
    </div>
  `;
}

function getStrategistFaceHtml(imgId) {
  const base = `images/${imgId}`;
  return `
    <div style="width:100%; height:100%; position:relative; display:flex; align-items:center; justify-content:center;">
      <svg viewBox="0 0 40 40" style="width:100%; height:100%;">
        <rect width="40" height="40" fill="#2d1205"/>
        <circle cx="20" cy="16" r="10" fill="#ffd700"/>
        <path d="M 8,36 Q 20,22 32,36 Z" fill="#b31212"/>
      </svg>
      <img src="${base}.png" 
           onload="
             this.style.display='block';
             var s=this.parentElement.querySelector('svg');
             if (s) s.style.display='none';
           "
           onerror="
             if (!this.dataset.triedJpg) {
               this.dataset.triedJpg = 'true';
               this.src = '${base}.jpg';
             } else if (!this.dataset.triedWebp) {
               this.dataset.triedWebp = 'true';
               this.src = '${base}.webp';
             } else {
               this.remove();
             }
           "
           style="display:none; width:100%; height:100%; object-fit:cover; object-position:center 10%; position:absolute; inset:0;">
    </div>
  `;
}

/* 主役五傑（初陣基礎動員兵力：3,000兵設定） */
const PLAYER_WARLORDS = {
  sanada: {
    id: 'sanada', name: '真田幸村', clan: '信濃国 ｜ 真田赤備隊・日本一の兵', themeColor: '#e61919',
    baseTroops: 3000,
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
    `
  },
  keiji: {
    id: 'keiji', name: '前田慶次', clan: '加賀国 ｜ 天下無双の傾奇者', themeColor: '#ffd700',
    baseTroops: 3000,
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
    `
  },
  masamune: {
    id: 'masamune', name: '伊達政宗', clan: '陸奥国 ｜ 独眼竜の牙', themeColor: '#4fc3f7',
    baseTroops: 3000,
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
    `
  },
  kanetsugu: {
    id: 'kanetsugu', name: '直江兼続', clan: '越後国 ｜ 義と愛の軍師', themeColor: '#ba68c8',
    baseTroops: 3000,
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
    `
  },
  tadakatsu: {
    id: 'tadakatsu', name: '本多忠勝', clan: '三河国 ｜ 徳川四天王・蜻蛉切', themeColor: '#ffb74d',
    baseTroops: 3000,
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
    `
  }
};

/* 敵将十傑（戦国史実・大軍動員スケール） */
const WARLORDS_DATA = {
  1: {
    id: 'enemy_1', province: '尾張国', name: '木下藤吉郎', clan: '尾張国｜織田足軽隊',
    maxTroops: 3000,
    featureShort: '守りのない駒を見落としがち。銀と歩を前進させる足軽戦法。',
    tacticsHint: '藤吉郎は守りのない駒を見落としがち。味方の駒にヒモ（守り）をつけ、角と飛車の道を開いて敵陣へ突入されよ！',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#140d06"/><path d="M50 20 Q56 28 50 36 Q44 28 50 20 Z M50 36 Q62 50 50 68 Q38 50 50 36 Z M50 68 Q68 85 50 94 Q32 85 50 68 Z" fill="#ffd700"/>`,
    quotes: { 
      default: '「草履取りとて天下を夢見候！ 足軽の意地、見せてくれよう！」', 
      check: '「猿の一撃、侮りめさるな！」', 
      pinch: '「あわわ…！ 信長様にお叱りを受けてしまう！」', 
      adv: '「出世の足音が聞こえてき申した！」' 
    },
    defeatQuote: '「参り申した…！ されど猿は何度でも木を登り候！」',
    victoryQuote: '「勝ったぞ！ 信長様、藤吉郎やりましたぞ！」'
  },
  2: {
    id: 'enemy_2', province: '加賀国', name: '前田利家', clan: '加賀国｜槍の又左',
    maxTroops: 8000,
    featureShort: '中央5筋から飛車で豪快に突進。中央を金銀で固めて防げ！',
    tacticsHint: '利家公は中央（5筋）から飛車で突進して参る。真ん中に金銀を配して防壁を築き、飛車の突撃を跳ね返されよ！',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#180707"/><circle cx="50" cy="50" r="10" fill="#ffd700"/><circle cx="50" cy="24" r="8" fill="#ffd700"/><circle cx="75" cy="42" r="8" fill="#ffd700"/><circle cx="65" cy="74" r="8" fill="#ffd700"/><circle cx="35" cy="74" r="8" fill="#ffd700"/><circle cx="25" cy="42" r="8" fill="#ffd700"/>`,
    quotes: { 
      default: '「我が槍に迷いなし！ 槍の又左が一撃、盤上に受けてみよ！」', 
      check: '「槍の又左、一騎当千の突撃ぞ！」', 
      pinch: '「ぬう…！ 前田の槍衾を崩されるとは！」', 
      adv: '「槍を引くな！ この利家が押し通る！」' 
    },
    defeatQuote: '「見事な槍さばき… 前田の当主として完敗を認めよう！」',
    victoryQuote: '「槍の又左の前に敵なし！ 百万石の礎となれ！」'
  },
  3: {
    id: 'enemy_3', province: '越前国', name: '柴田勝家', clan: '越前国｜鬼柴田',
    maxTroops: 15000,
    featureShort: '歩と銀で力任せに正面突破。角・飛車の遠距離射線で横から突け。',
    tacticsHint: '勝家は歩と銀で正面突破を狙う猪武者。正面から受けて立たず、横から飛車・角の射線で銀の首を狙い撃たれよ！',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#150a04"/><path d="M30 40 Q50 25 70 40 Q50 48 30 40 Z M30 65 Q50 50 70 65 Q50 73 30 65 Z" fill="#ffd700"/>`,
    quotes: { 
      default: '「かかれ柴田の突進力、小細工など粉砕してくれるわ！」', 
      check: '「鬼柴田の剛腕、いざ受けてみよ！」', 
      pinch: '「ぐぬ… 瓶割り柴田、退路を断って迎え撃つ！」', 
      adv: '「かかれ！ かかれ柴田の猛進を止められるか！」' 
    },
    defeatQuote: '「無念…！ 瓶を割れども、貴殿の策を砕けなんだか…！」',
    victoryQuote: '「ガハハ！ 鬼柴田の突進を止められる者などおらぬわ！」'
  },
  4: {
    id: 'enemy_4', province: '近江国', name: '浅井長政', clan: '近江国｜浅井軍総帥',
    maxTroops: 25000,
    featureShort: '手堅い三間飛車の持久戦。自玉を美濃囲いに囲って対抗せよ。',
    tacticsHint: '長政は三間飛車の持久戦陣形。焦って突っ込まず、自玉を美濃囲い等に囲ってからじっくり攻略されよ。',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#0d1824"/><g fill="none" stroke="#ffd700" stroke-width="3"><polygon points="50,18 64,26 64,42 50,50 36,42 36,26"/><polygon points="36,44 50,52 50,68 36,76 22,68 22,52"/><polygon points="64,44 78,52 78,68 64,76 50,68 50,52"/></g>`,
    quotes: { 
      default: '「信義を重んじ、我が陣を進めん！ 浅井の誇り、見よ！」', 
      check: '「信義の一撃、ここを退くわけにはいかぬ！」', 
      pinch: '「信義を貫く刻… お市、すまぬ…」', 
      adv: '「我が陣容に乱れなし！ 義の勝利を！」' 
    },
    defeatQuote: '「浅井の誇り、盤上に散る… お市、許せよ…」',
    victoryQuote: '「信義は勝てり！ 近江の誇りは揺るぎなし！」'
  },
  5: {
    id: 'enemy_5', province: '美濃国', name: '明智光秀', clan: '美濃国｜智謀の軍総帥',
    maxTroops: 40000,
    featureShort: '浮き駒を狙う3手先読みの知謀。駒同士の連携を絶対に緩めるな。',
    tacticsHint: '光秀は3手先を読む知謀の士。守りのない浮き駒を狙ってくるため、自陣の駒同士を常に連結させよ。',
    portraitSvg: `<rect width="100" height="100" rx="6" fill="#09141c"/><polygon points="50,18 60,38 82,38 65,52 72,74 50,60 28,74 35,52 18,38 40,38" fill="#ffd700"/>`,
    quotes: { 
      default: '「時は今、天が下知る五月哉。我が智謀、見切れるか！」', 
      check: '「敵は本能寺に… いや、貴殿の本陣にあり！」', 
      pinch: '「天運は我を見放すというのか…！ まだだ！」', 
      adv: '「盤上の全て、我が掌の上にて動いておる。」' 
    },
    defeatQuote: '「我が天運の尽きる刻… 貴殿の軍略、誠にお見事…」',
    victoryQuote: '「時は今！ 天下を統べるは、この光秀よ！」'
  },
  6: {
    id: 'enemy_6', province: '越後国', name: '上杉謙信', clan: '越後国｜越後の龍・軍神',
    maxTroops: 60000,
    featureShort: '角行と龍馬の長距離射線で急襲。斜めのラインを常に警戒せよ。',
    tacticsHint: '謙信公は角行と龍馬の遠距離砲撃を好む。斜めの射線上に自軍の大事な駒を置かぬよう細心の注意を払われよ。',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#14061a"/>
      <path d="M 26,45 Q 50,18 74,45 L 76,78 Q 50,86 24,78 Z" fill="#e8e8e8" stroke="#ffd700" stroke-width="1.8"/>
      <circle cx="50" cy="46" r="16" fill="#1c0a24"/>
      <text x="50" y="52" font-size="14" font-weight="900" fill="#ffd700" text-anchor="middle">毘</text>
    `,
    quotes: { 
      default: '「毘沙門天の御加護、我が軍にあり！ 車懸りの陣、進めよ！」', 
      check: '「龍の爪牙、敵本陣を裂く！」', 
      pinch: '「運は天にあり、鎧は胸にあり！ 毘沙門天よ！」', 
      adv: '「車懸り、休むこと莫れ！ 義戦を完遂せん！」' 
    },
    defeatQuote: '「極楽も地獄も先は有明の… 義戦を尽くし、悔いはなし！」',
    victoryQuote: '「毘沙門天の御前、悪は滅び義は輝かん！」'
  },
  7: {
    id: 'enemy_7', province: '甲斐国', name: '武田信玄', clan: '甲斐国｜甲斐の虎',
    maxTroops: 80000,
    featureShort: '金銀で玉を固める風林火山の要塞。正面を避け端攻めで崩せ。',
    tacticsHint: '信玄公は金銀3枚で玉を固める風林火山の要塞。正面からぶつからず、端攻め（1筋や9筋）から崩すのが妙手。',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#1f0303"/>
      <path d="M 22,34 Q 50,10 78,34 Q 90,60 76,76 Q 50,88 24,76 Q 10,60 22,34 Z" fill="#e0d6c3" stroke="#ffd700" stroke-width="1.8"/>
      <polygon points="50,30 60,42 50,54 40,42" fill="#ffd700"/>
      <polygon points="40,44 50,56 40,68 30,56" fill="#ffd700"/><polygon points="60,44 70,56 60,68 50,56" fill="#ffd700"/>
    `,
    quotes: { 
      default: '「疾きこと風の如く、動かざること山の如し！ 蹂躙してくれる！」', 
      check: '「侵略すること火の如し！ 虎の牙、受けてみよ！」', 
      pinch: '「人は城、人は石垣… 崩れるな、耐えよ！」', 
      adv: '「風林火山の旗の下、天下を呑み込まん！」' 
    },
    defeatQuote: '「人は城、人は石垣… 儂の石垣が崩れるとは… 見事！」',
    victoryQuote: '「風林火山の旗靡くところ、天下平定の道あり！」'
  },
  8: {
    id: 'enemy_8', province: '近江安土', name: '織田信長', clan: '近江安土｜第六天魔王',
    maxTroops: 110000,
    featureShort: '龍王・龍馬を先陣に突入させる電撃戦。自玉を深く囲って耐えよ。',
    tacticsHint: '信長公は龍王・龍馬を前線に繰り出す電撃戦。自玉を深く囲い、成駒の突入に耐えつつ反撃の刃を研ぐべし。',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#140606"/>
      <path d="M 28,42 Q 50,20 72,42 L 76,76 Q 50,86 24,76 Z" fill="#3b0808" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="27" r="10" fill="#ffd700"/><circle cx="68" cy="40" r="10" fill="#ffd700"/>
      <circle cx="62" cy="62" r="10" fill="#ffd700"/><circle cx="38" cy="62" r="10" fill="#ffd700"/><circle cx="32" cy="40" r="10" fill="#ffd700"/>
      <circle cx="50" cy="48" r="11" fill="#9b111e" stroke="#ffd700" stroke-width="1.5"/>
    `,
    quotes: { 
      default: '「是非に及ばず。この信長に挑む愚かさ、骨身に刻め。」', 
      check: '「三段撃ち！ 鉄砲の前に灰燼と帰すがよい！」', 
      pinch: '「人間五十年、下天の内をくらぶれば… まだ死せぬ！」', 
      adv: '「天下布武！ 我が前にひれ伏せ！」' 
    },
    defeatQuote: '「是非に及ばず…！ 新たなる天下人よ、乱世を束ねよ！」',
    victoryQuote: '「天下布武！ 我が覇道に従わぬ者に明日はない！」'
  },
  9: {
    id: 'enemy_9', province: '摂津大坂', name: '豊臣秀吉', clan: '摂津大坂｜天下人・太閤',
    maxTroops: 150000,
    featureShort: '持ち駒を操る包囲殲滅戦。安易な大駒交換は敵の思う壺。',
    tacticsHint: '太閤秀吉は持ち駒を操る包囲戦が得意。持ち駒を渡さないよう、無駄な駒交換を避けて盤上を制圧せよ。',
    portraitSvg: `
      <rect width="100" height="100" rx="6" fill="#241904"/>
      <g stroke="#ffd700" stroke-width="2">
        <line x1="50" y1="45" x2="50" y2="8"/><line x1="50" y1="45" x2="25" y2="15"/><line x1="50" y1="45" x2="75" y2="15"/>
        <line x1="50" y1="45" x2="10" y2="30"/><line x1="50" y1="45" x2="90" y2="30"/>
      </g>
      <path d="M 30,46 Q 50,30 70,46 L 74,75 Q 50,84 26,75 Z" fill="#694a08" stroke="#ffd700" stroke-width="2"/>
      <circle cx="50" cy="56" r="10" fill="#ffd700"/>
    `,
    quotes: { 
      default: '「天下は我が手中にある！ 太閤の前に跪くがよい！」', 
      check: '「黄金の茶室ならぬ、黄金の王手を喰らいなされ！」', 
      pinch: '「露と落ち、露と消えにし我が身かな… なにを！」', 
      adv: '「日輪の如く、全てを照らし尽くして見せよう！」' 
    },
    defeatQuote: '「露と落ち露と消えにし我が身かな… 天下の夢、託し申す！」',
    victoryQuote: '「天下人はこの秀吉よ！ 日輪の光、誰にも遮れぬ！」'
  },
  10: {
    id: 'enemy_10', province: '武蔵江戸', name: '徳川家康', clan: '武蔵江戸｜天下の覇者',
    maxTroops: 200000,
    featureShort: '最深探索の鉄壁。軍師の【覚醒進言】と連携し打開せよ。',
    tacticsHint: '家康公は最深探索の鉄壁。一分の隙も許さぬため、軍師の【覚醒進言】と連携し神算鬼謀の一撃を狙うべし。',
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
    },
    defeatQuote: '「見事なり… 乱世を鎮むる真の器、確かに見届けた…！」',
    victoryQuote: '「忍耐の末に泰平あり。天下は徳川の掌中にあり！」'
  }
};

/* 宿命の対決録 */
const RIVALRIES = {
  'sanada_10': {
    title: '大坂の陣！ 日本一の兵 vs 天下の覇者',
    pQuote: '「不惜身命！ 徳川の天下、この幸村が盤上で覆して見せようぞ！」',
    eQuote: '「真田か…！ 目の上の瘤め、大坂の雪辱はさせぬぞ！」'
  },
  'keiji_2': {
    title: '前田の血脈！ 傾奇者 vs 槍の又左',
    pQuote: '「叔父貴、ぬるい水風呂の礼をせねばな！ ど派手に傾くぜ！」',
    eQuote: '「慶次！ その放蕩、前田の当主として盤上で成敗いたす！」'
  },
  'kanetsugu_10': {
    title: '直江状の義戦！ 義愛の軍師 vs 関東の巨魁',
    pQuote: '「不義の天下に道はなし！ 義の刃、盤上にて受けてみよ！」',
    eQuote: '「直江兼続… 筆鋒鋭き小僧め、盤上で捻り潰してくれる！」'
  },
  'masamune_9': {
    title: '天下への野望！ 独眼竜 vs 太閤の威光',
    pQuote: '「太閤殿下！ 白装束の礼は済んだ、盤上は容赦しねえ！」',
    eQuote: '「伊達の若造、その野心ごとのみ込んで見せようぞ！」'
  },
  'tadakatsu_7': {
    title: '三方ヶ原の雪辱！ 蜻蛉切 vs 甲斐の虎',
    pQuote: '「信玄公！ 我が蜻蛉切、家康公の盾となり砕かん！」',
    eQuote: '「忠勝、家康に過ぎたるものよ。虎の牙を凌げるか！」'
  }
};

const PIECES = {
  OU: '王将', HI: '飛車', KA: '角行', KI: '金将', GI: '銀将', KE: '桂馬', KY: '香車', FU: '歩兵',
  RY: '龍王', UM: '龍馬', NG: '成銀', NK: '成桂', NY: '成香', TO: 'と金'
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

let hintUsedCount = 0, awakenedHintCount = 0, battleStartTurn = 'PLAYER';

// 軍師三策管理
let tacticsCandidates = [];
let currentTacticIndex = 0;
let isCurrentHintAwakened = false;

// 自動再生（オートリプレイ）管理
let autoReplayTimer = null;
let isAutoReplaying = false;
const REPLAY_SPEEDS = [1500, 750, 350];
const REPLAY_SPEED_LABELS = ['1x', '2x', '4x'];
let replaySpeedIndex = 0;

/* =========================================================
   【確定仕様】兵力・軍勢成長計算エンジン
   （案Cベース：撃破した敵兵力の約4割を500兵単位で吸収加算）
   ========================================================= */
function getPlayerMaxTroops() {
  const base = PLAYER_WARLORDS[currentMyWarlordId]?.baseTroops || 3000;
  let bonus = 0;
  clearedProvinces.forEach(lvl => {
    const enemyTroops = WARLORDS_DATA[lvl]?.maxTroops || 0;
    // 敵兵力の40%を500兵単位に四捨五入して論功行賞
    const rawBonus = enemyTroops * 0.40;
    const roundedBonus = Math.round(rawBonus / 500) * 500;
    bonus += roundedBonus;
  });
  return base + bonus;
}

function getAiMaxTroops() {
  return WARLORDS_DATA[currentAiLevel]?.maxTroops || 3000;
}

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

// 連続王手千日手 ＆ 千日手の判定
function checkSennichite() {
  const curHash = getBoardHash(board, hands, turn);
  boardHashHistory.push(curHash);
  
  const inCheckCurrent = isCheckState(turn);
  checkHistory.push({ turn, inCheck: inCheckCurrent });

  const count = boardHashHistory.filter(h => h === curHash).length;
  if (count >= 4) {
    const firstIdx = boardHashHistory.indexOf(curHash);
    const lastIdx = boardHashHistory.length - 1;

    let playerAlwaysChecking = true;
    let aiAlwaysChecking = true;
    let stepCount = 0;

    for (let i = firstIdx; i < lastIdx; i++) {
      const snap = checkHistory[i];
      if (snap) {
        stepCount++;
        if (snap.turn === 'AI' && !snap.inCheck) playerAlwaysChecking = false;
        if (snap.turn === 'PLAYER' && !snap.inCheck) aiAlwaysChecking = false;
      }
    }

    isGameOver = true; playCheckSound();
    stopAutoReplay();
    updateTurnAvatarGlow(null);

    if (stepCount >= 6 && playerAlwaysChecking && !aiAlwaysChecking) {
      triggerCutin('連続王手の反則！ 敗戦に候！', true);
      setOrderMessage('連続王手の千日手は武士道違反！ 陣を立て直し再戦されよ。', false, 'alert');
      saveBattleRecord('lose', '反則負け');
      return true;
    } else if (stepCount >= 6 && aiAlwaysChecking && !playerAlwaysChecking) {
      triggerCutin('敵将の反則！ 我が軍の勝利！', true);
      setOrderMessage('敵将が連続王手の千日手を犯し候！ 我が軍の勝利なり！', false, 'settle');
      saveProgress(currentAiLevel); launchFireworksCelebration();
      saveBattleRecord('win', '反則勝ち');
      return true;
    }

    triggerCutin('千日手！ 痛み分けの引き分け！');
    setOrderMessage('同一局面四回にて引き分け（痛み分け）に候。<br>「対局開始」にて再戦されよ。', false, 'alert');
    saveBattleRecord('draw', '千日手');
    return true;
  }
  return false;
}

function initBoardState() {
  stopAutoReplay();
  board = Array.from({length: 9}, () => Array(9).fill(null));
  hands = { PLAYER: {}, AI: {} };
  moveObjectsHistory = []; historyStates = []; boardHashHistory = []; checkHistory = [];
  evalScoresHistory = [0]; reviewingIndex = -1; lastMove = null;
  hintSourceCell = null; hintTargetCell = null; selectedPos = null; currentValidMoves = [];
  isAiThinking = false; isHintThinking = false;
  tacticsCandidates = []; currentTacticIndex = 0;

  updateTurnAvatarGlow(null);
  updateStrategistUI();
  updateWarlordBGM(currentAiLevel);
  renderMainPortraits();
  updateRivalryButton();

  board[0] = [{code:'KY',owner:'AI'},{code:'KE',owner:'AI'},{code:'GI',owner:'AI'},{code:'KI',owner:'AI'},{code:'OU',owner:'AI'},{code:'KI',owner:'AI'},{code:'GI',owner:'AI'},{code:'KE',owner:'AI'},{code:'KY',owner:'AI'}];
  board[1][1] = {code:'HI',owner:'AI'}; board[1][7] = {code:'KA',owner:'AI'};
  for(let c=0; c<9; c++) board[2][c] = {code:'FU',owner:'AI'};
  for(let c=0; c<9; c++) board[6][c] = {code:'FU',owner:'PLAYER'};
  board[7][1] = {code:'KA',owner:'PLAYER'}; board[7][7] = {code:'HI',owner:'PLAYER'};
  board[8] = [{code:'KY',owner:'PLAYER'},{code:'KE',owner:'PLAYER'},{code:'GI',owner:'PLAYER'},{code:'KI',owner:'PLAYER'},{code:'OU',owner:'PLAYER'},{code:'KI',owner:'PLAYER'},{code:'GI',owner:'PLAYER'},{code:'KE',owner:'PLAYER'},{code:'KY',owner:'PLAYER'}];

  historyStates.push({ board: cloneBoardState(board), hands: JSON.parse(JSON.stringify(hands)), turn, moveObjectsHistory: [] });
  boardHashHistory.push(getBoardHash(board, hands, turn));
  renderBoard(); renderKifu(); updateTroopsAndSituation(0);
}

function renderMainPortraits() {
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const w = WARLORDS_DATA[currentAiLevel];
  const pBox = document.getElementById('player-avatar-container');
  const aiBox = document.getElementById('ai-avatar-container');
  if (pBox) pBox.innerHTML = getWarlordPortraitHtml(p, true, 'player');
  if (aiBox) aiBox.innerHTML = getWarlordPortraitHtml(w, true, 'ai');
}

function updateTurnAvatarGlow(activeTurn) {
  const pBox = document.getElementById('player-avatar-container');
  const aiBox = document.getElementById('ai-avatar-container');
  if (!pBox || !aiBox) return;

  pBox.classList.remove('turn-thinking-player');
  aiBox.classList.remove('turn-thinking-enemy');

  if (activeTurn === 'PLAYER') {
    pBox.classList.add('turn-thinking-player');
  } else if (activeTurn === 'AI') {
    aiBox.classList.add('turn-thinking-enemy');
  }
}

function updateStrategistUI() {
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const badge = document.getElementById('player-strategist-badge');
  if (badge) badge.textContent = `軍師:${p.strategistName}`;
  const hintBtn = document.getElementById('btn-master-hint');
  if (hintBtn) {
    hintBtn.classList.remove('awakened');
    hintBtn.textContent = '💡 軍師進言';
  }
}

function updateRivalryButton() {
  const btn = document.getElementById('btn-rivalry-story');
  if (!btn) return;
  const rivalKey = `${currentMyWarlordId}_${currentAiLevel}`;
  if (RIVALRIES[rivalKey]) {
    btn.style.display = 'inline-block';
  } else {
    btn.style.display = 'none';
  }
}

/* =========================================================
   合戦軍令札・メッセージ表示制御
   ========================================================= */
function setOrderMessage(txt, isMyTurn = false, category = 'player') {
  const bannerEl = document.getElementById('order-message-banner');
  const textEl = document.getElementById('order-message-text');
  const badgeEl = document.getElementById('order-tag-badge');
  const r1El = document.getElementById('tag-badge-row1');
  const r2El = document.getElementById('tag-badge-row2');
  const faceEl = document.getElementById('order-strategist-face');
  const altBtn = document.getElementById('btn-alt-tactic');

  textEl.innerHTML = txt;
  bannerEl.classList.toggle('my-turn', isMyTurn);
  document.getElementById('player-panel').classList.toggle('player-active', isMyTurn);

  badgeEl.className = 'order-tag-badge';

  switch(category) {
    case 'enemy':
      badgeEl.classList.add('badge-tag-enemy');
      r1El.textContent = '敵軍'; r2El.textContent = '思案';
      break;
    case 'hint':
      badgeEl.classList.add('badge-tag-hint');
      r1El.textContent = '軍師'; r2El.textContent = '進言';
      break;
    case 'hint-awakened':
      badgeEl.classList.add('badge-tag-hint-awakened');
      r1El.textContent = '覚醒'; r2El.textContent = '進言';
      break;
    case 'alert':
      badgeEl.classList.add('badge-tag-alert');
      r1El.textContent = '合戦'; r2El.textContent = '急変';
      break;
    case 'settle':
      badgeEl.classList.add('badge-tag-settle');
      r1El.textContent = '合戦'; r2El.textContent = '決着';
      break;
    case 'player':
    default:
      badgeEl.classList.add('badge-tag-player');
      r1El.textContent = '自軍'; r2El.textContent = '手番';
      break;
  }

  const isHintMode = category.startsWith('hint');
  if (isHintMode) {
    const p = PLAYER_WARLORDS[currentMyWarlordId];
    faceEl.style.display = 'flex';
    document.getElementById('strategist-face-img-box').innerHTML = getStrategistFaceHtml(p.strategistImgId);
    document.getElementById('strategist-face-name-tag').textContent = p.strategistShort;
  } else {
    faceEl.style.display = 'none';
  }

  if (isHintMode && tacticsCandidates.length > 1) {
    altBtn.style.display = 'inline-block';
  } else {
    altBtn.style.display = 'none';
  }

  updateRivalryButton();
}

function openRivalryInGuide(targetKey = null) {
  playPieceSound();
  stopAutoReplay();
  const rivalKey = targetKey || `${currentMyWarlordId}_${currentAiLevel}`;
  
  openGuideModal();
  switchGuideTab(4);

  setTimeout(() => {
    const cardEl = document.getElementById(`rivalry-card-${rivalKey}`);
    if (cardEl) {
      cardEl.scrollIntoView({ behavior: 'smooth', block: 'center' });
      cardEl.classList.remove('highlight-rivalry-card');
      void cardEl.offsetWidth;
      cardEl.classList.add('highlight-rivalry-card');
      setTimeout(() => cardEl.classList.remove('highlight-rivalry-card'), 3800);
    }
  }, 100);
}

function openFurigomaModal() {
  initAudio(); playPieceSound(); stopAutoReplay();
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
    battleStartTurn = turn;
    t.innerHTML = isPlayerSente ? `<span style="color:#ff5252;">歩が${5 - toCount}枚！ 我が軍の先手！</span>` : `<span style="color:#ffd700;">と金が${toCount}枚！ 敵軍の先手！</span>`;
    setTimeout(() => { m.style.display = 'none'; startBattle(); }, 1200);
  }, 1300);
}

function startBattle() {
  isGameOver = false; initBoardState();
  hintUsedCount = 0; awakenedHintCount = 0;
  const rivalKey = `${currentMyWarlordId}_${currentAiLevel}`;
  const rivalry = RIVALRIES[rivalKey];
  const enemy = WARLORDS_DATA[currentAiLevel];
  const p = PLAYER_WARLORDS[currentMyWarlordId];

  if (rivalry) {
    triggerCutin(`【宿命の対決】${rivalry.title}`, true, true);
    document.getElementById('player-quote-disp').textContent = rivalry.pQuote;
    document.getElementById('ai-quote-disp').textContent = rivalry.eQuote;
  } else {
    triggerCutin('合戦開始！ いざ推して参る！');
    document.getElementById('player-quote-disp').textContent = p.quotes.default;
    document.getElementById('ai-quote-disp').textContent = enemy.quotes.default;
  }

  const levelHint = enemy.tacticsHint ? `<br><span style="color:#ffe082; font-size:10px;">【${p.strategistShort}の兵法】${enemy.tacticsHint}</span>` : '';

  if (turn === 'PLAYER') {
    updateTurnAvatarGlow('PLAYER');
    setOrderMessage(`${p.name}公、一手目をお決め下され！${levelHint}`, true, 'player');
  } else {
    updateTurnAvatarGlow('AI');
    setOrderMessage(`${enemy.name}が軍略を巡らせております…${levelHint}`, false, 'enemy');
    setTimeout(aiTurn, 850);
  }
}

/* 盤面描画 */
function renderBoard() {
  const el = document.getElementById('board'); el.innerHTML = '';
  
  const pKingPos = isCheckState('PLAYER') ? findKing('PLAYER') : null;
  const aiKingPos = isCheckState('AI') ? findKing('AI') : null;

  for(let r=0; r<9; r++) {
    for(let c=0; c<9; c++) {
      const cell = document.createElement('div'); cell.className = 'cell';
      const targetP = board[r][c];

      if (lastMove && lastMove.to.r === r && lastMove.to.c === c) {
        cell.classList.add('last-move-to');
      }

      if (selectedPos?.r === r && selectedPos?.c === c) cell.classList.add('selected');

      if (currentValidMoves.some(m => m.r === r && m.c === c)) {
        if (targetP && targetP.owner === 'AI') {
          cell.classList.add('target-capture');
        } else {
          cell.classList.add('target-move');
        }
      }

      if ((pKingPos && pKingPos.r === r && pKingPos.c === c) || (aiKingPos && aiKingPos.r === r && aiKingPos.c === c)) {
        cell.classList.add('in-check-king');
      }

      if (hintSourceCell?.r === r && hintSourceCell?.c === c) cell.classList.add('hint-source');
      if (hintTargetCell?.r === r && hintTargetCell?.c === c) cell.classList.add('hint-target');

      if (targetP) {
        const pDiv = document.createElement('div');
        const isProm = PROMOTED_PIECES.includes(targetP.code);
        pDiv.className = `piece ${targetP.owner === 'PLAYER' ? 'player' : 'ai'} ${isProm ? 'promoted' : ''}`;
        
        const name2 = PIECES[targetP.code];
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
  stopAutoReplay();
  if (isReviewingPast()) {
    setOrderMessage('「⏭」を押して最新の戦況へお戻り下され。', false, 'player');
    return;
  }
  initAudio(); playPieceSound();
  hintSourceCell = null; hintTargetCell = null; tacticsCandidates = [];
  document.getElementById('btn-alt-tactic').style.display = 'none';

  if (selectedPos?.handCode === code) { selectedPos = null; currentValidMoves = []; }
  else {
    selectedPos = { handCode: code };
    currentValidMoves = getLegalMoves('PLAYER').filter(m => m.type === 'drop' && m.code === code).map(m => m.to);
  }
  renderBoard();
}

function onCellClick(r, c) {
  if (isGameOver || turn !== 'PLAYER' || isAiThinking) return;
  stopAutoReplay();
  if (isReviewingPast()) {
    setOrderMessage('「⏭」を押して最新の戦況へお戻り下され。', false, 'player');
    return;
  }
  initAudio(); hintSourceCell = null; hintTargetCell = null; tacticsCandidates = [];
  document.getElementById('btn-alt-tactic').style.display = 'none';

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

function executeMove(m) {
  playPieceSound();

  if (m.type === 'move' && !m.code && board[m.from.r][m.from.c]) {
    m.code = board[m.from.r][m.from.c].code;
  }

  moveObjectsHistory.push(m);
  lastMove = m;

  if (m.type === 'drop') {
    hands[m.owner][m.code]--;
    board[m.to.r][moveObjectsHistory[moveObjectsHistory.length - 1].to.c] = { code: m.code, owner: m.owner };
  } else {
    const fp = board[m.from.r][m.from.c], tp = board[m.to.r][m.to.c];
    if (tp && tp.code !== 'OU') {
      const raw = UNPROMOTE_MAP[tp.code];
      hands[m.owner][raw] = (hands[m.owner][raw] || 0) + 1;
      if (m.owner === 'PLAYER' && (tp.code === 'HI' || tp.code === 'KA')) {
        setOrderMessage(`敵の${PIECES[tp.code]}を討ち捕獲！ 敵部隊に大損害を与えたり！`, true, 'alert');
      }
    }
    if (m.promote) {
      fp.code = PROMOTE_MAP[fp.code];
      if (fp.code === 'RY') triggerCutin('龍王顕現！ 敵陣を薙ぎ払え！', true);
      else if (fp.code === 'UM') triggerCutin('龍馬咆哮！ 神速の刃！', true);
    }
    board[m.to.r][m.to.c] = fp;
    board[m.from.r][m.from.c] = null;
  }
  historyStates.push({ board: cloneBoardState(board), hands: JSON.parse(JSON.stringify(hands)), turn: m.owner === 'PLAYER' ? 'AI' : 'PLAYER', moveObjectsHistory: JSON.parse(JSON.stringify(moveObjectsHistory)) });
  reviewingIndex = historyStates.length - 1;
  renderBoard(); renderKifu();
}

function finishTurn() {
  tacticsCandidates = [];
  document.getElementById('btn-alt-tactic').style.display = 'none';

  if (checkSennichite()) return;
  if (isCheckState('AI')) {
    playCheckSound(); triggerCutin('敵将へ王手！');
    document.getElementById('player-quote-disp').textContent = PLAYER_WARLORDS[currentMyWarlordId].quotes.check;
    document.getElementById('ai-quote-disp').textContent = WARLORDS_DATA[currentAiLevel].quotes.pinch;
  }
  if (checkGameOver('AI')) return;
  
  turn = 'AI';
  updateTurnAvatarGlow('AI');
  setOrderMessage(`${WARLORDS_DATA[currentAiLevel].name}が次の一手を巡らせております…`, false, 'enemy');
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

function analyzeTacticsIntent(bm) {
  const targetPiece = board[bm.to.r][bm.to.c];
  const movingPieceCode = (bm.type === 'move') ? (board[bm.from.r][bm.from.c]?.code || bm.code) : bm.code;
  const isCapture = (targetPiece && targetPiece.owner === 'AI');
  const enemyKing = findKing('AI');
  const distToKing = enemyKing ? Math.max(Math.abs(bm.to.r - enemyKing.r), Math.abs(bm.to.c - enemyKing.c)) : 9;

  if (isCheckState('PLAYER')) {
    return {
      badgeClass: 'badge-tactics-defense',
      badgeText: '本陣防衛',
      reason: '自玉への王手を防ぎ、急場を脱する一手！'
    };
  }

  if (isCapture) {
    const capName = PIECES[targetPiece.code];
    return {
      badgeClass: 'badge-tactics-capture',
      badgeText: '敵駒捕獲',
      reason: `無防備な敵の${capName}を討ち、敵の戦力を削ぐ好手！`
    };
  }

  if (bm.promote) {
    const promName = PIECES[PROMOTE_MAP[movingPieceCode]] || '成駒';
    return {
      badgeClass: 'badge-tactics-promote',
      badgeText: '敵陣突破',
      reason: `敵陣を破り【${promName}】へ覚醒させよ！ 陣形崩壊の好機！`
    };
  }

  if (distToKing <= 2) {
    return {
      badgeClass: 'badge-tactics-attack',
      badgeText: '包囲殲滅',
      reason: '敵玉の退路を断ち、包囲網を狭める一手！'
    };
  }

  if (bm.type === 'move' && movingPieceCode === 'FU') {
    if ((bm.from.r === 6 && bm.from.c === 2) || (bm.from.r === 6 && bm.from.c === 6)) {
      return {
        badgeClass: 'badge-tactics-open',
        badgeText: '射線開通',
        reason: '飛車・角行の射程を開き、敵陣へ大砲を睨ませるべし！'
      };
    }
  }

  if (bm.type === 'move' && ['KI','GI','OU'].includes(movingPieceCode)) {
    return {
      badgeClass: 'badge-tactics-defense',
      badgeText: '陣形整備',
      reason: '駒を連携させて守りを固め、次なる反撃の足場を築くべし！'
    };
  }

  return {
    badgeClass: 'badge-tactics-trap',
    badgeText: '局面打開',
    reason: '千日手を回避し、新たな戦局を切り拓く好機の一手に候！'
  };
}

function filterThreeTacticsPlans(allScoredMoves) {
  if (!allScoredMoves || allScoredMoves.length === 0) return [];
  
  const best = allScoredMoves[0].move;
  let attackMove = null;
  let defenseMove = null;

  for (let i = 1; i < allScoredMoves.length; i++) {
    const m = allScoredMoves[i].move;
    const intent = analyzeTacticsIntent(m);
    
    if (!attackMove && ['敵駒捕獲', '敵陣突破', '包囲殲滅'].includes(intent.badgeText)) {
      attackMove = m;
    } else if (!defenseMove && ['本陣防衛', '陣形整備'].includes(intent.badgeText)) {
      defenseMove = m;
    }
    if (attackMove && defenseMove) break;
  }

  const plans = [
    { move: best, planName: '第一の策（王道）' }
  ];

  if (attackMove && attackMove !== best) {
    plans.push({ move: attackMove, planName: '第二の策（強襲）' });
  } else if (allScoredMoves[1]) {
    plans.push({ move: allScoredMoves[1].move, planName: '第二の策（積極）' });
  }

  if (defenseMove && defenseMove !== best && defenseMove !== attackMove) {
    plans.push({ move: defenseMove, planName: '第三の策（堅陣）' });
  } else if (allScoredMoves[2]) {
    plans.push({ move: allScoredMoves[2].move, planName: '第三の策（整備）' });
  }

  return plans;
}

function renderTacticProposal(idx) {
  if (!tacticsCandidates || tacticsCandidates.length === 0) return;
  const item = tacticsCandidates[idx];
  const bm = item.move;
  const planName = item.planName || `第${idx+1}の策`;

  const planLabel = `<span class="tactics-plan-tag">【${planName}】</span>`;
  const intent = analyzeTacticsIntent(bm);
  const intentHtml = `<span class="tactics-reason-badge ${intent.badgeClass}">【${intent.badgeText}】</span>`;

  let moveDetailHtml = '';
  const toCoordStr = `<span class="hl-to">${9 - bm.to.c}${KANJI_NUMS[bm.to.r]}</span>`;

  if (bm.type === 'drop') {
    const pName = PIECES[bm.code];
    moveDetailHtml = `持ち駒の【${pName}】を ${toCoordStr}へ<span class="hl-act">【打つ】</span>べし！`;
  } else {
    const fromPiece = board[bm.from.r][bm.from.c];
    const pName = PIECES[fromPiece?.code || bm.code];
    const fromCoordStr = `<span class="hl-from">${9 - bm.from.c}${KANJI_NUMS[bm.from.r]}</span>`;
    
    let promoteText = '';
    if (bm.promote) {
      promoteText = `進軍し<span class="hl-prom">【成る】</span>`;
    } else {
      const canP = PROMOTE_MAP[fromPiece?.code] && (bm.from.r <= 2 || bm.to.r <= 2);
      if (canP) promoteText = `進軍し<span class="hl-act">【成らず】</span>`;
      else promoteText = `へ<span class="hl-act">【移動】</span>`;
    }

    moveDetailHtml = `${fromCoordStr}の【${pName}】を ${toCoordStr}へ${promoteText}させよ！`;
  }

  const categoryType = isCurrentHintAwakened ? 'hint-awakened' : 'hint';

  setOrderMessage(`${planLabel}${intentHtml}<b>${moveDetailHtml}</b><br><span style="font-size:10.5px;color:#fff2b2;">（理由：${intent.reason}）</span>`, true, categoryType);

  hintSourceCell = bm.type === 'move' ? { r: bm.from.r, c: bm.from.c } : null;
  hintTargetCell = { r: bm.to.r, c: bm.to.c };
  renderBoard();
}

function cycleNextTacticsHint() {
  if (!tacticsCandidates || tacticsCandidates.length <= 1) return;
  playPieceSound();
  currentTacticIndex = (currentTacticIndex + 1) % tacticsCandidates.length;
  renderTacticProposal(currentTacticIndex);
}

function handleWorkerMessage(e) {
  const data = e.data;
  const p = PLAYER_WARLORDS[currentMyWarlordId];

  if (data.type === 'hintDone') {
    isHintThinking = false;
    tacticsCandidates = filterThreeTacticsPlans(data.allScoredMoves);
    currentTacticIndex = 0;
    isCurrentHintAwakened = !!data.isAwakened;

    if (tacticsCandidates.length === 0) {
      setOrderMessage(`進言できる妙手がござらぬ…！`, true, 'hint');
      return;
    }

    if (data.isAwakened) {
      triggerCutin(`軍師覚醒！ ${p.strategistName}の神算鬼謀！`, true);
    }
    
    renderTacticProposal(0);
    return;
  }

  isAiThinking = false;
  if (data.evalScore !== undefined) {
    const roundedScore = Math.round(data.evalScore);
    evalScoresHistory.push(roundedScore);
    updateTroopsAndSituation(roundedScore);
  }
  const bm = data.bestMove;
  if (!bm) { checkGameOver('AI'); return; }
  executeMove(bm);

  const targetCellEl = document.querySelector(`#board .cell:nth-child(${bm.to.r * 9 + bm.to.c + 1})`);
  if (targetCellEl) targetCellEl.classList.add('sparkle');

  if (checkSennichite()) return;

  if (!checkGameOver('PLAYER')) {
    turn = 'PLAYER';
    updateTurnAvatarGlow('PLAYER');
    const pName = PLAYER_WARLORDS[currentMyWarlordId].name;
    if (isCheckState('PLAYER')) {
      playCheckSound(); triggerCutin('敵の奇襲！ 王手！');
      setOrderMessage(`敵の奇襲！ 王手を合駒か玉の移動で防がれよ！`, true, 'alert');
      document.getElementById('ai-quote-disp').textContent = WARLORDS_DATA[currentAiLevel].quotes.check;
      document.getElementById('player-quote-disp').textContent = PLAYER_WARLORDS[currentMyWarlordId].quotes.pinch;
    } else {
      setOrderMessage(`${pName}公、次なる一手をお決め下され！`, true, 'player');
    }
  }
}

function aiTurn() {
  if (isGameOver) return;
  isAiThinking = true;
  aiWorker.postMessage({ board, hands, level: currentAiLevel, history: moveObjectsHistory, hashHistory: boardHashHistory });
}

function showMasterHint() {
  if (isGameOver || turn !== 'PLAYER' || isHintThinking) return;
  stopAutoReplay();
  if (isReviewingPast()) {
    setOrderMessage('「⏭」を押して最新局面へお戻り下され。', false, 'player');
    return;
  }
  playPieceSound(); isHintThinking = true;
  hintUsedCount++;
  const hintBtn = document.getElementById('btn-master-hint');
  const isAwakenedNow = hintBtn.classList.contains('awakened');
  
  if (isAwakenedNow) {
    awakenedHintCount++;
    setOrderMessage(`深淵の神算鬼謀を探索中…！`, false, 'hint-awakened');
    aiWorker.postMessage({ board, hands, level: 10, isHintRequest: true, isAwakened: true, history: moveObjectsHistory, hashHistory: boardHashHistory });
  } else {
    setOrderMessage(`局面打開の一手を探索中…`, false, 'hint');
    aiWorker.postMessage({ board, hands, level: 8, isHintRequest: true, isAwakened: false, history: moveObjectsHistory, hashHistory: boardHashHistory });
  }
}

function undoMove() {
  if (isGameOver || historyStates.length <= 1) return;
  stopAutoReplay();
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
  tacticsCandidates = [];
  document.getElementById('btn-alt-tactic').style.display = 'none';

  updateTurnAvatarGlow('PLAYER');
  renderBoard(); renderKifu();
  updateTroopsAndSituation(evalScoresHistory[evalScoresHistory.length - 1] || 0);
  setOrderMessage('局面を戻し候。次なる一手をお決め下され。', true, 'player');
}

function surrenderGame() {
  if (isGameOver) return;
  stopAutoReplay();
  isGameOver = true; triggerCutin('無念… 降伏いたす…');
  updateTurnAvatarGlow(null);
  
  const enemy = WARLORDS_DATA[currentAiLevel];
  if (enemy && enemy.victoryQuote) {
    document.getElementById('ai-quote-disp').textContent = enemy.victoryQuote;
  }
  
  setOrderMessage('再起の陣を敷き、雪辱を期されよ！', false, 'settle');
  saveBattleRecord('lose', '降伏(投了)');
}

function checkGameOver(nextOwner) {
  if (getLegalMoves(nextOwner).length === 0) {
    isGameOver = true;
    playVictorySound();
    stopAutoReplay();
    updateTurnAvatarGlow(null);
    const enemy = WARLORDS_DATA[currentAiLevel];

    if (nextOwner === 'AI') {
      saveProgress(currentAiLevel); launchFireworksCelebration(); triggerCutin('敵将討ち取ったり！', true);
      
      if (enemy && enemy.defeatQuote) {
        document.getElementById('ai-quote-disp').textContent = enemy.defeatQuote;
      }

      if (currentAiLevel === 10) {
        setOrderMessage('徳川幕府を平定し、日ノ本の覇者となり候！ 誠に見事！', false, 'settle');
      } else {
        setOrderMessage(`${enemy.name}を討ち取り、${enemy.province}を平定いたし候！`, false, 'settle');
      }
      saveBattleRecord('win', '大勝利');
    } else {
      triggerCutin('本陣陥落… 敗北に候…');
      if (enemy && enemy.victoryQuote) {
        document.getElementById('ai-quote-disp').textContent = enemy.victoryQuote;
      }
      setOrderMessage('敵将に敗れ候。再起の陣を敷き、雪辱を期されよ！', false, 'settle');
      saveBattleRecord('lose', '本陣陥落');
    }
    return true;
  }
  return false;
}

/* =========================================================
   【新設】兵力（HP）＆戦況リアルタイム換算エンジン
   ========================================================= */
function updateTroopsAndSituation(scoreAI) {
  const pScore = -scoreAI;
  // 評価値から勝率比率（0〜100%）を滑らかに算出
  let pPct = Math.round(100 / (1 + Math.exp(-pScore / 600)));
  pPct = Math.max(5, Math.min(95, pPct));

  const pMax = getPlayerMaxTroops();
  const aiMax = getAiMaxTroops();

  // 実効兵力（現在HP）：各々の最大動員力 × 勝率比率（四捨五入整数）
  const pCurrent = Math.round(pMax * (pPct / 100));
  const aiCurrent = Math.round(aiMax * ((100 - pPct) / 100));

  // メイン画面の兵力ゲージ（HPバー）＆数値の更新
  const pBar = document.getElementById('player-troops-bar');
  const aiBar = document.getElementById('ai-troops-bar');
  const pDisp = document.getElementById('player-troops-disp');
  const aiDisp = document.getElementById('ai-troops-disp');

  if (pBar) pBar.style.width = `${pPct}%`;
  if (aiBar) aiBar.style.width = `${100 - pPct}%`;
  if (pDisp) pDisp.textContent = `${pCurrent.toLocaleString()} / ${pMax.toLocaleString()} 兵`;
  if (aiDisp) aiDisp.textContent = `${aiCurrent.toLocaleString()} / ${aiMax.toLocaleString()} 兵`;

  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const hintBtn = document.getElementById('btn-master-hint');
  const isPinchState = (pPct <= 35) || isCheckState('PLAYER');
  const canAwaken = (currentAiLevel >= 8) && isPinchState;

  if (canAwaken && !isGameOver) {
    hintBtn.classList.add('awakened');
    hintBtn.textContent = '🔥 覚醒進言';
  } else {
    hintBtn.classList.remove('awakened');
    hintBtn.textContent = '💡 軍師進言';
  }

  // 軍師評定テロップの動的更新
  const sit = document.getElementById('situation-text');
  const troopsDiff = Math.abs(pCurrent - aiCurrent);

  if (pPct >= 75) {
    sit.textContent = `我が軍圧倒的優勢！ 敵軍残存わずか ${aiCurrent.toLocaleString()} 兵、本陣包囲せり！`;
    document.getElementById('player-quote-disp').textContent = p.quotes.adv;
  } else if (pPct >= 60) {
    sit.textContent = `我が軍前線突破！ +${troopsDiff.toLocaleString()} 兵の優勢を確保し敵陣へ肉薄中！`;
    document.getElementById('player-quote-disp').textContent = p.quotes.adv;
  } else if (pPct <= 25) {
    sit.textContent = `我が本陣危急！ 自軍残存 ${pCurrent.toLocaleString()} 兵、防衛陣列を再編せよ！`;
    document.getElementById('player-quote-disp').textContent = p.quotes.pinch;
  } else if (pPct <= 40) {
    sit.textContent = `敵軍の猛攻を許す！ -${troopsDiff.toLocaleString()} 兵の損害、陣形を立て直されよ！`;
    document.getElementById('player-quote-disp').textContent = p.quotes.pinch;
  } else {
    sit.textContent = `互角の白兵戦（兵力差 ±${troopsDiff.toLocaleString()}）。一手一手が天下の行方を左右し候。`;
  }
}

/* =========================================================
   合戦レビュー ＆ 自動再生（オートリプレイ）制御
   ========================================================= */
function stepReview(dir, isAuto = false) {
  if (historyStates.length <= 1) return;
  if (!isAuto) stopAutoReplay();

  if (!isAuto || replaySpeedIndex === 0) {
    playPieceSound();
  }

  if (reviewingIndex === -1) reviewingIndex = historyStates.length - 1;
  const targetIdx = reviewingIndex + dir;
  if (targetIdx < 0 || targetIdx >= historyStates.length) {
    if (isAuto) stopAutoReplay();
    return;
  }
  reviewingIndex = targetIdx;
  const snap = historyStates[reviewingIndex];
  board = cloneBoardState(snap.board);
  hands = JSON.parse(JSON.stringify(snap.hands));
  lastMove = (reviewingIndex > 0) ? snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] : null;
  renderBoard();
  renderKifu();
  
  const score = evalScoresHistory[reviewingIndex] !== undefined ? evalScoresHistory[reviewingIndex] : (evalScoresHistory[evalScoresHistory.length - 1] || 0);
  updateTroopsAndSituation(score);

  setOrderMessage(`${reviewingIndex}手目の布陣を表示中（「⏭」で最新局面へ）`, false, 'player');
}

function resetToLatestReview() {
  stopAutoReplay();
  if (historyStates.length <= 1 || reviewingIndex === historyStates.length - 1) return;
  playPieceSound();
  reviewingIndex = historyStates.length - 1;
  const snap = historyStates[reviewingIndex];
  board = cloneBoardState(snap.board);
  hands = JSON.parse(JSON.stringify(snap.hands));
  lastMove = snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] || null;
  renderBoard();
  renderKifu();
  updateTurnAvatarGlow(turn);
  updateTroopsAndSituation(evalScoresHistory[evalScoresHistory.length - 1] || 0);
  setOrderMessage(`${PLAYER_WARLORDS[currentMyWarlordId].name}公、一手をお決め下され！`, turn === 'PLAYER', 'player');
}

function toggleAutoReplay() {
  if (isAutoReplaying) {
    stopAutoReplay();
  } else {
    startAutoReplay();
  }
}

function startAutoReplay() {
  if (historyStates.length <= 1) return;
  initAudio();
  isAutoReplaying = true;
  const btn = document.getElementById('btn-auto-replay');
  if (btn) {
    btn.innerHTML = '⏸ 停止';
    btn.classList.add('is-playing');
  }

  if (reviewingIndex === historyStates.length - 1 || reviewingIndex === -1) {
    reviewingIndex = 0;
    const snap = historyStates[0];
    board = cloneBoardState(snap.board);
    hands = JSON.parse(JSON.stringify(snap.hands));
    lastMove = null;
    renderBoard();
    renderKifu();
    updateTroopsAndSituation(evalScoresHistory[0] || 0);
  }

  runAutoReplayStep();
}

function runAutoReplayStep() {
  if (!isAutoReplaying) return;
  const delay = REPLAY_SPEEDS[replaySpeedIndex];

  autoReplayTimer = setTimeout(() => {
    if (!isAutoReplaying) return;
    if (reviewingIndex >= historyStates.length - 1) {
      stopAutoReplay();
      setOrderMessage('合戦の自動再生が終了いたし候。', false, 'settle');
      return;
    }
    stepReview(1, true);
    runAutoReplayStep();
  }, delay);
}

function stopAutoReplay() {
  if (autoReplayTimer) {
    clearTimeout(autoReplayTimer);
    autoReplayTimer = null;
  }
  isAutoReplaying = false;
  const btn = document.getElementById('btn-auto-replay');
  if (btn) {
    btn.innerHTML = '▶ 自動';
    btn.classList.remove('is-playing');
  }
}

function cycleReplaySpeed() {
  playPieceSound();
  replaySpeedIndex = (replaySpeedIndex + 1) % REPLAY_SPEEDS.length;
  const speedBtn = document.getElementById('btn-replay-speed');
  if (speedBtn) {
    speedBtn.textContent = REPLAY_SPEED_LABELS[replaySpeedIndex];
  }
  if (isAutoReplaying) {
    if (autoReplayTimer) clearTimeout(autoReplayTimer);
    runAutoReplayStep();
  }
}

function renderKifu() {
  const st = document.getElementById('kifu-stream'); st.innerHTML = '';
  moveObjectsHistory.forEach((m, idx) => {
    const s = document.createElement('div');
    s.className = `kifu-item-cell ${reviewingIndex === idx + 1 ? 'active-review' : ''}`;
    
    const rawCode = m.code || 'FU';
    const pName = m.type === 'drop' ? PIECES[m.code] : (m.promote ? (PIECES[PROMOTE_MAP[rawCode]] || PIECES[rawCode]) : PIECES[rawCode]);
    s.textContent = `${idx + 1}.${9 - m.to.c}${KANJI_NUMS[m.to.r]}${pName}`;
    s.onclick = () => {
      stopAutoReplay();
      playPieceSound();
      reviewingIndex = idx + 1;
      const snap = historyStates[reviewingIndex];
      board = cloneBoardState(snap.board);
      hands = JSON.parse(JSON.stringify(snap.hands));
      lastMove = snap.moveObjectsHistory[snap.moveObjectsHistory.length - 1] || null;
      renderBoard();
      renderKifu();
      const score = evalScoresHistory[reviewingIndex] !== undefined ? evalScoresHistory[reviewingIndex] : (evalScoresHistory[evalScoresHistory.length - 1] || 0);
      updateTroopsAndSituation(score);
      setOrderMessage(`${reviewingIndex}手目の布陣を表示中（「⏭」で最新局面へ）`, false, 'player');
    };
    st.appendChild(s);
  });
  if (reviewingIndex === -1 || reviewingIndex === historyStates.length - 1) st.scrollLeft = st.scrollWidth;
}

/* =========================================================
   【大幅刷新】棋譜＆陣地争奪モーダル表示制御
   ========================================================= */
function openKifuModal() {
  stopAutoReplay();
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const e = WARLORDS_DATA[currentAiLevel];

  const pMax = getPlayerMaxTroops();
  const aiMax = getAiMaxTroops();

  const curEvalAI = evalScoresHistory[evalScoresHistory.length - 1] || 0;
  const pScore = -curEvalAI;
  let pPct = Math.round(100 / (1 + Math.exp(-pScore / 600)));
  pPct = Math.max(5, Math.min(95, pPct));

  const pCurrent = Math.round(pMax * (pPct / 100));
  const aiCurrent = Math.round(aiMax * ((100 - pPct) / 100));

  // モーダル上部：両軍残存兵力対比カウンターの更新
  document.getElementById('kifu-player-tag').textContent = `▲ ${p.name}`;
  document.getElementById('kifu-enemy-tag').textContent = `▽ ${e.name}`;
  document.getElementById('kifu-player-troops-val').textContent = `${pCurrent.toLocaleString()} 兵`;
  document.getElementById('kifu-enemy-troops-val').textContent = `${aiCurrent.toLocaleString()} 兵`;

  const troopsDiff = pCurrent - aiCurrent;
  const diffBadge = document.getElementById('kifu-troops-diff-badge');
  if (troopsDiff >= 0) {
    diffBadge.textContent = `我が軍 +${troopsDiff.toLocaleString()} 兵優勢`;
    diffBadge.style.color = '#ffd700';
  } else {
    diffBadge.textContent = `敵軍 +${Math.abs(troopsDiff).toLocaleString()} 兵優勢`;
    diffBadge.style.color = '#90caf9';
  }

  // 形勢格付けスタンプ
  const badgeEl = document.getElementById('kifu-modal-status-badge');
  if (pPct >= 80) { badgeEl.textContent = '【天下掌握】勝勢'; badgeEl.style.color = '#ffd700'; }
  else if (pPct >= 65) { badgeEl.textContent = '【敵陣蹂躙】優勢'; badgeEl.style.color = '#76ff03'; }
  else if (pPct <= 20) { badgeEl.textContent = '【本陣陥落寸前】敗勢'; badgeEl.style.color = '#ff3d00'; }
  else if (pPct <= 35) { badgeEl.textContent = '【防戦一方】劣勢'; badgeEl.style.color = '#4fc3f7'; }
  else { badgeEl.textContent = '【天下分水嶺】互角の白兵戦'; badgeEl.style.color = '#ffeb3b'; }

  document.getElementById('chart-player-name-tag').textContent = `▲ 我が軍【${p.name}】進撃ライン`;
  document.getElementById('chart-enemy-name-tag').textContent = `▽ 敵軍【${e.name}】侵攻ライン`;

  const curSitText = document.getElementById('situation-text').textContent;
  document.getElementById('kifu-modal-situation-text').textContent = curSitText;

  // 棋譜木札リストのレンダリング
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
      updateTroopsAndSituation(evalScoresHistory[reviewingIndex] || 0);
      closeKifuModal();
      setOrderMessage(`${reviewingIndex}手目の局面（「⏭」で最新局面へ）`, false, 'player');
    };
    l.appendChild(d);
  });

  document.getElementById('kifu-modal').style.display = 'flex';
  setTimeout(drawEvaluationChart, 50);
}
function closeKifuModal() { document.getElementById('kifu-modal').style.display = 'none'; }

/* =========================================================
   【大幅刷新】陣地争奪グラフ描画エンジン（安土桃山合戦絵図）
   ========================================================= */
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

  // 上段：我が軍の陣地・進撃エリア（金碧・紅蓮の陣）
  const playerBg = ctx.createLinearGradient(0, 0, 0, midY);
  playerBg.addColorStop(0, 'rgba(180, 25, 25, 0.45)');
  playerBg.addColorStop(1, 'rgba(70, 25, 6, 0.15)');
  ctx.fillStyle = playerBg;
  ctx.fillRect(0, 0, w, midY);

  // 下段：敵軍の陣地・侵攻エリア（濃藍・闇夜の敵陣）
  const enemyBg = ctx.createLinearGradient(0, midY, 0, h);
  enemyBg.addColorStop(0, 'rgba(8, 20, 42, 0.15)');
  enemyBg.addColorStop(1, 'rgba(12, 32, 68, 0.55)');
  ctx.fillStyle = enemyBg;
  ctx.fillRect(0, midY, w, midY);

  // 天下分水嶺（兵力拮抗線・金糸点線）
  ctx.strokeStyle = 'rgba(255, 215, 0, 0.2)';
  ctx.lineWidth = 1 * dpr;
  ctx.setLineDash([3 * dpr, 3 * dpr]);
  [midY - h * 0.35, midY - h * 0.18, midY + h * 0.35, midY + h * 0.18].forEach(y => {
    ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(w, y); ctx.stroke();
  });

  ctx.setLineDash([]);
  ctx.strokeStyle = 'rgba(255, 215, 0, 0.85)';
  ctx.lineWidth = 1.8 * dpr;
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

  // 陣地進撃の塗りつぶしグラデーション（波打つ前線）
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

  // 黄金の前線ライン
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

  // 天王山ポイント（激震の一手）の炎マーク
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

  // 最新現在地ピン
  const lastPt = points[points.length - 1];
  ctx.beginPath();
  ctx.arc(lastPt.x, lastPt.y, 4.5 * dpr, 0, Math.PI * 2);
  ctx.fillStyle = '#ffffff';
  ctx.strokeStyle = '#ff9100';
  ctx.lineWidth = 2.2 * dpr;
  ctx.fill();
  ctx.stroke();

  // グラフ上下の兵力差表示（四捨五入整数）
  const curDiffScore = lastPt.pScore;
  const pMax = getPlayerMaxTroops();
  const scaledDiff = Math.round((curDiffScore / 1000) * (pMax * 0.35));

  const topEl = document.getElementById('chart-eval-num-top');
  const btmEl = document.getElementById('chart-eval-num-bottom');

  if (scaledDiff >= 0) {
    topEl.textContent = `+${scaledDiff.toLocaleString()} 兵優勢`;
    btmEl.textContent = '';
  } else {
    topEl.textContent = '';
    btmEl.textContent = `-${Math.abs(scaledDiff).toLocaleString()} 兵劣勢`;
  }
}

function renderDynamicTactics() {
  const container = document.getElementById('dynamic-tactics-content');
  if (!container) return;
  const w = WARLORDS_DATA[currentAiLevel];
  const p = PLAYER_WARLORDS[currentMyWarlordId];

  container.innerHTML = `
    <div class="guide-card-box beginner-highlight-box" id="guide-card-dynamic-1">
      <div class="guide-card-header-row">
        <h4>🔰 【Lv.${currentAiLevel} ${w.province}｜${w.name}】を討ち破る兵法</h4>
        <button class="card-speech-btn btn-3d" onclick="toggleCardSpeech('guide-card-dynamic-1')">🔊 朗読</button>
      </div>
      専属軍師・<b>${p.strategistName}</b>による、対「${w.name}」専用の極意に候！<br><br>
      <b class="kw-gold">一、敵将の癖と弱点を見抜け！</b><br>
      ・${w.tacticsHint}<br><br>
      <b class="kw-crimson">二、大駒（飛車・角行）を敵陣へ突入させて成れ！</b><br>
      ・飛車と角は自軍最強の矛。敵陣（上段3段以内）へ飛び込み、必ず<span class="kw-crimson">「成る」</span>べし！ 龍王・龍馬が敵陣に顕現すれば敵兵力は崩壊いたします。<br><br>
      <b class="kw-blue">三、玉将（大将）の守りを固めよ！</b><br>
      ・大将が初期位置にいると敵の奇襲で即座に本陣陥落となります。金銀を玉の周りに配し、堅牢な陣形を築いてから出撃されよ！
    </div>

    <div class="guide-card-box" id="guide-card-dynamic-2">
      <div class="guide-card-header-row">
        <h4>💡 ${w.name}戦おすすめの「開戦五手」</h4>
        <button class="card-speech-btn btn-3d" onclick="toggleCardSpeech('guide-card-dynamic-2')">🔊 朗読</button>
      </div>
      対局が始まったら、まずはこの手順で盤面を有利に進められよ！<br>
      1. <b>７六歩</b>（角の道を開き射線を睨ませる）<br>
      2. <b>２六歩</b>（飛車の前の歩を前進させる）<br>
      3. <b>４八銀</b> または <b>６八玉</b>（玉を少し避難させ、銀を前線へ）<br>
      4. <b>２五歩</b>（飛車先の歩をさらに進めて拠点を築く）<br>
      5. 敵の隙を突き、飛車を敵陣へ突撃させて<b>【龍王】</b>へ覚醒せよ！
    </div>
  `;
}

function openGuideModal() {
  stopGuideSpeech();
  stopAutoReplay();
  renderDynamicTactics();
  document.getElementById('guide-modal').style.display = 'flex';
}
function closeGuideModal() {
  stopGuideSpeech();
  document.getElementById('guide-modal').style.display = 'none';
}
function switchGuideTab(tabIdx) {
  playPieceSound();
  stopGuideSpeech();
  const btns = document.querySelectorAll('.guide-tab-btn');
  btns.forEach((b, idx) => b.classList.toggle('active', idx === tabIdx));
  for (let i = 0; i <= 4; i++) {
    const pane = document.getElementById(`guide-pane-${i}`);
    if (pane) pane.classList.toggle('active', i === tabIdx);
  }
}

function openConquestMapModal() { stopAutoReplay(); updateConquestMapUI(); document.getElementById('conquest-modal').style.display = 'flex'; }
function closeConquestMapModal() { document.getElementById('conquest-modal').style.display = 'none'; }

function openPlayerWarlordModal() {
  stopAutoReplay();
  const l = document.getElementById('player-warlord-list'); l.innerHTML = '';
  const currentTotalTroops = getPlayerMaxTroops();

  for(let k in PLAYER_WARLORDS) {
    const p = PLAYER_WARLORDS[k];
    const d = document.createElement('div');
    d.className = `warlord-select-card btn-3d ${k === currentMyWarlordId ? 'active' : ''}`;
    d.innerHTML = `
      <div class="card-avatar-mini" style="background:${p.bgGrad};">
        ${getWarlordPortraitHtml(p, false)}
      </div>
      <div class="card-info-col">
        <div class="card-name-title">${p.name}</div>
        <div class="card-clan-tag">${p.clan}（総動員 ${currentTotalTroops.toLocaleString()} 兵）</div>
        <div class="card-strategist-tag">軍師: ${p.strategistName} (${p.strategistTitle})</div>
      </div>`;
    d.onclick = () => { setPlayerWarlord(k); closePlayerWarlordModal(); };
    l.appendChild(d);
  }
  document.getElementById('player-warlord-modal').style.display = 'flex';
}
function closePlayerWarlordModal() { document.getElementById('player-warlord-modal').style.display = 'none'; }

function updateConquestMapUI() {
  const clearedCount = clearedProvinces.length;
  document.getElementById('conquest-pct-disp').textContent = `${clearedCount * 10}%`;
  document.getElementById('conquest-pct-bar').style.width = `${clearedCount * 10}%`;
  document.getElementById('conquest-cleared-count').textContent = `${clearedCount} / 10 国平定`;

  // 自軍総動員兵力＆論功行賞平定ボーナス表示の更新
  const totalTroops = getPlayerMaxTroops();
  const baseTroops = PLAYER_WARLORDS[currentMyWarlordId]?.baseTroops || 3000;
  const bonusTroops = totalTroops - baseTroops;
  const growthDisp = document.getElementById('conquest-total-troops-disp');
  const bonusDisp = document.getElementById('conquest-troops-bonus-disp');
  if (growthDisp) growthDisp.textContent = `${totalTroops.toLocaleString()} 兵`;
  if (bonusDisp) bonusDisp.textContent = `（平定吸収ボーナス：+${bonusTroops.toLocaleString()} 兵）`;

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
        <div class="conquest-avatar-thumb">${getWarlordPortraitHtml(w, false)}</div>
        <div class="conquest-card-info">
          <div class="conquest-card-title">Lv.${i} ${w.province} ｜ ${w.name}</div>
          <div class="conquest-card-clan">${w.clan} （動員 ${w.maxTroops.toLocaleString()} 兵）</div>
          <div class="conquest-card-feature">⚔ ${w.featureShort}</div>
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
  const p = PLAYER_WARLORDS[currentMyWarlordId];
  const pMax = getPlayerMaxTroops();

  document.getElementById('ai-name-disp').textContent = w.name;
  document.getElementById('ai-clan-disp').textContent = `${w.clan} (Lv.${lvl})`;
  document.getElementById('ai-quote-disp').textContent = w.quotes.default;
  
  // 兵力表示の更新
  document.getElementById('ai-troops-disp').textContent = `${w.maxTroops.toLocaleString()} / ${w.maxTroops.toLocaleString()} 兵`;
  document.getElementById('player-troops-disp').textContent = `${pMax.toLocaleString()} / ${pMax.toLocaleString()} 兵`;

  const aiBox = document.getElementById('ai-avatar-container');
  if (aiBox) aiBox.innerHTML = getWarlordPortraitHtml(w, true, 'ai');

  document.getElementById('btn-enemy-change').textContent = `🗺 ${w.province} (Lv.${lvl})`;
  
  updateWarlordBGM(lvl);
  updateConquestMapUI();

  const rivalKey = `${currentMyWarlordId}_${currentAiLevel}`;
  const levelHint = w.tacticsHint ? `<br><span style="color:#ffe082; font-size:10px;">【${p.strategistShort}の兵法】${w.tacticsHint}</span>` : '';

  if (RIVALRIES[rivalKey]) {
    setOrderMessage(`${RIVALRIES[rivalKey].title}${levelHint}<br>「対局開始」を押して雌雄を決されよ！`, true, 'alert');
  } else {
    setOrderMessage(`${w.province}・「${w.name}」との決戦に候！${levelHint}<br>「対局開始」を押されよ。`, false, 'player');
  }
  updateRivalryButton();
}

function setPlayerWarlord(k) {
  currentMyWarlordId = k;
  try { localStorage.setItem('shogi_my_warlord', k); } catch(e){}
  const p = PLAYER_WARLORDS[k];
  const pMax = getPlayerMaxTroops();

  document.documentElement.style.setProperty('--player-theme-color', p.themeColor);
  document.getElementById('player-name-disp').textContent = p.name;
  document.getElementById('player-clan-disp').textContent = p.clan;
  document.getElementById('player-quote-disp').textContent = p.quotes.default;
  document.getElementById('player-troops-disp').textContent = `${pMax.toLocaleString()} / ${pMax.toLocaleString()} 兵`;
  
  const pBox = document.getElementById('player-avatar-container');
  if (pBox) pBox.innerHTML = getWarlordPortraitHtml(p, true, 'player');

  updateStrategistUI();
  selectConquestProvince(currentAiLevel);
}

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

function saveBattleRecord(resultType, resultLabel) {
  if (moveObjectsHistory.length === 0) return;
  const now = new Date();
  const dateStr = `${now.getFullYear()}/${(now.getMonth()+1).toString().padStart(2,'0')}/${now.getDate().toString().padStart(2,'0')} ${now.getHours().toString().padStart(2,'0')}:${now.getMinutes().toString().padStart(2,'0')}`;
  
  const record = {
    id: Date.now(),
    date: dateStr,
    playerWarlordId: currentMyWarlordId,
    playerWarlordName: PLAYER_WARLORDS[currentMyWarlordId].name,
    playerTroops: getPlayerMaxTroops(),
    enemyLevel: currentAiLevel,
    enemyName: WARLORDS_DATA[currentAiLevel].name,
    enemyProvince: WARLORDS_DATA[currentAiLevel].province,
    enemyTroops: WARLORDS_DATA[currentAiLevel].maxTroops,
    result: resultType,
    resultLabel: resultLabel,
    movesCount: moveObjectsHistory.length,
    sente: battleStartTurn === 'PLAYER' ? '先手' : '後手',
    hintUsed: hintUsedCount,
    awakenedHintUsed: awakenedHintCount,
    historyStates: JSON.parse(JSON.stringify(historyStates)),
    moveObjectsHistory: JSON.parse(JSON.stringify(moveObjectsHistory)),
    evalScoresHistory: JSON.parse(JSON.stringify(evalScoresHistory))
  };

  try {
    let records = JSON.parse(localStorage.getItem('shogi_battle_records') || '[]');
    records.unshift(record);
    if (records.length > 100) records = records.slice(0, 100);
    localStorage.setItem('shogi_battle_records', JSON.stringify(records));
  } catch(e) {}
}

function openHistoryModal() {
  stopAutoReplay();
  renderBattleHistoryList();
  document.getElementById('battle-history-modal').style.display = 'flex';
}
function closeHistoryModal() {
  document.getElementById('battle-history-modal').style.display = 'none';
}

/* =========================================================
   【大幅刷新】合戦戦歴帳（勲功絵巻録）レンダリング
   ========================================================= */
function renderBattleHistoryList() {
  let records = [];
  try {
    records = JSON.parse(localStorage.getItem('shogi_battle_records') || '[]');
  } catch(e) { records = []; }

  const total = records.length;
  const wins = records.filter(r => r.result === 'win').length;
  const loses = records.filter(r => r.result === 'lose').length;
  const draws = records.filter(r => r.result === 'draw').length;
  const winRate = total > 0 ? Math.round((wins / (total - draws || 1)) * 100) : 0;
  
  // 武功格付け称号の判定
  let rankTitle = '初陣の若武者';
  let rankDesc = '合戦の道に足を踏み入れたばかりの若き勇士。';
  if (total >= 10 && winRate >= 80) {
    rankTitle = '天下無双';
    rankDesc = '数多の猛将を圧倒し、日ノ本に並ぶ者なき最強の覇王！';
  } else if (total >= 5 && winRate >= 60) {
    rankTitle = '歴戦の覇者';
    rankDesc = '百戦錬磨の采配で敵を粉砕し、諸国に武名轟く名将！';
  } else if (wins >= 3) {
    rankTitle = '一騎当千';
    rankDesc = '数々の合戦を制し、自軍を勝利へ導く剛腕の指揮官。';
  }

  const stampEl = document.getElementById('history-rank-stamp');
  const descEl = document.getElementById('history-rank-desc');
  const summaryEl = document.getElementById('history-total-summary');

  if (stampEl) stampEl.textContent = rankTitle;
  if (descEl) descEl.textContent = rankDesc;
  if (summaryEl) {
    summaryEl.textContent = `通算 ${total}戦 ${wins}勝 ${loses}敗 ${draws}分（勝率 ${winRate}%）`;
  }

  const resF = document.getElementById('filter-result')?.value || 'all';
  const hintF = document.getElementById('filter-hint')?.value || 'all';
  const warF = document.getElementById('filter-warlord')?.value || 'all';
  const lvlF = document.getElementById('filter-level')?.value || 'all';

  const filtered = records.filter(r => {
    if (resF !== 'all' && r.result !== resF) return false;
    if (hintF === 'none' && r.hintUsed > 0) return false;
    if (hintF === 'used' && r.hintUsed === 0) return false;
    if (warF !== 'all' && r.playerWarlordId !== warF) return false;
    if (lvlF !== 'all' && r.enemyLevel !== parseInt(lvlF, 10)) return false;
    return true;
  });

  const listEl = document.getElementById('history-records-list');
  listEl.innerHTML = '';

  if (filtered.length === 0) {
    listEl.innerHTML = `<div style="text-align:center; padding:25px; color:#c4aa76; font-size:11px;">条件に合致する合戦記録はござらぬ。</div>`;
    return;
  }

  filtered.forEach(r => {
    const card = document.createElement('div');
    card.className = 'history-record-card';

    let badgeClass = 'badge-lose';
    if (r.result === 'win') badgeClass = 'badge-win';
    else if (r.result === 'draw') badgeClass = 'badge-draw';

    let hintBadgeHtml = '';
    if (r.hintUsed === 0) {
      hintBadgeHtml = `<span class="badge-hint-none">✨ 軍師助言: なし(自力)</span>`;
    } else {
      const awkStr = r.awakenedHintUsed > 0 ? ` (覚醒${r.awakenedHintUsed})` : '';
      hintBadgeHtml = `<span class="badge-hint-count">💡 軍師助言: ${r.hintUsed}回${awkStr}</span>`;
    }

    const pTroops = r.playerTroops ? r.playerTroops.toLocaleString() : '3,000';
    const eTroops = r.enemyTroops ? r.enemyTroops.toLocaleString() : WARLORDS_DATA[r.enemyLevel]?.maxTroops.toLocaleString() || '3,000';

    card.innerHTML = `
      <div class="history-card-top-row">
        <span class="history-date-txt">📅 ${r.date}</span>
        <span class="history-res-badge ${badgeClass}">【${r.resultLabel}】</span>
      </div>
      <div class="history-matchup-row">
        <div>
          <span>${r.playerWarlordName} (${r.sente})</span>
          <span class="history-matchup-troops">動員 ${pTroops} 兵</span>
        </div>
        <span class="matchup-vs-txt">⚔ 激突 ⚔</span>
        <div style="text-align:right;">
          <span>${r.enemyProvince}・${r.enemyName} (Lv.${r.enemyLevel})</span>
          <span class="history-matchup-troops">動員 ${eTroops} 兵</span>
        </div>
      </div>
      <div class="history-details-bottom-row">
        <span>総手数: <b>${r.movesCount}手</b></span>
        ${hintBadgeHtml}
        <button class="history-replay-btn btn-3d" onclick="replayFromHistory(${r.id})">棋譜再現</button>
      </div>
    `;
    listEl.appendChild(card);
  });
}

function replayFromHistory(recordId) {
  let records = [];
  try {
    records = JSON.parse(localStorage.getItem('shogi_battle_records') || '[]');
  } catch(e) { records = []; }
  
  const rec = records.find(r => r.id === recordId);
  if (!rec) return;

  stopAutoReplay();
  playPieceSound();
  closeHistoryModal();

  currentMyWarlordId = rec.playerWarlordId;
  currentAiLevel = rec.enemyLevel;
  setPlayerWarlord(currentMyWarlordId);
  selectConquestProvince(currentAiLevel);

  historyStates = rec.historyStates;
  moveObjectsHistory = rec.moveObjectsHistory;
  evalScoresHistory = rec.evalScoresHistory;

  reviewingIndex = historyStates.length - 1;
  const lastSnap = historyStates[reviewingIndex];
  board = cloneBoardState(lastSnap.board);
  hands = JSON.parse(JSON.stringify(lastSnap.hands));
  lastMove = (reviewingIndex > 0) ? lastSnap.moveObjectsHistory[lastSnap.moveObjectsHistory.length - 1] : null;
  isGameOver = true;

  updateTurnAvatarGlow(null);
  renderBoard();
  renderKifu();
  updateTroopsAndSituation(evalScoresHistory[evalScoresHistory.length - 1] || 0);
  
  setOrderMessage(`【${rec.playerWarlordName} vs ${rec.enemyName}の再現中】<br>［▶自動］で流し見、または［◀］［▶］で一手ずつ合戦を振り返られよ！`, false, 'player');
}

function clearBattleHistory() {
  if (confirm('これまでの合戦戦歴をすべて消去いたしますか？')) {
    localStorage.removeItem('shogi_battle_records');
    renderBattleHistoryList();
  }
}

/* 起動イベント */
document.addEventListener('click', () => initAudio(), { once: true });
document.addEventListener('touchstart', () => initAudio(), { once: true });

loadProgress();
setPlayerWarlord(currentMyWarlordId);
initBoardState();


