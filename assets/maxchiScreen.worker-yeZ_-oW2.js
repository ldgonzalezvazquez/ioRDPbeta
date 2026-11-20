// src/engine/maxchiScreen.worker.mts
import { parentPort, workerData } from "node:worker_threads";

// src/engine/types.ts
var GAP = 46;
var NUC_A = 66;
var NUC_C = 68;
var NUC_G = 72;
var NUC_T = 85;
var NUC_MAT = (() => {
  const m = new Uint8Array(256);
  m[NUC_A] = 1;
  m[NUC_C] = 2;
  m[NUC_G] = 3;
  m[NUC_T] = 4;
  m[GAP] = 0;
  return m;
})();
var CONV_NUM_SEQ = (() => {
  const m = new Uint8Array(256);
  m[NUC_A] = 1;
  m[NUC_C] = 2;
  m[NUC_G] = 3;
  m[NUC_T] = 4;
  return m;
})();
var CHAR_TO_CODE = (() => {
  const t = new Int16Array(256).fill(GAP);
  const set = (chars, code) => {
    for (const ch of chars) t[ch.charCodeAt(0)] = code;
  };
  set("Aa", NUC_A);
  set("Cc", NUC_C);
  set("Gg", NUC_G);
  set("TtUu", NUC_T);
  return t;
})();
var CODE_TO_CHAR = {
  [NUC_A]: "A",
  [NUC_C]: "C",
  [NUC_G]: "G",
  [NUC_T]: "T",
  [GAP]: "-"
};
var PROGRAM_MAXCHI = 3;
var PROGRAM_CHIMAERA = 4;
function newXOverEvent(program) {
  return {
    outsideFlag: 0,
    missIdentifyFlag: 0,
    programFlag: program,
    sbpFlag: 0,
    accept: 0,
    majorP: -1,
    minorP: -1,
    daughter: -1,
    beginning: 0,
    ending: 0,
    lHolder: 0,
    eventNumber: 0,
    permPVal: 0,
    beginP: 0,
    endP: 0,
    probability: 1,
    dHolder: 0,
    triplet: [0, 0, 0],
    maxY: 0,
    loHiFlag: 0,
    beginWarn: 0,
    endWarn: 0,
    hWindowWidth: 0,
    lenXoverSeq: 0
  };
}

// src/engine/fssTables.ts
var CODES = 125;
function compress3(a, b, c) {
  return a + 5 * b + 25 * c;
}
function siteClass(x, y, z) {
  if (x === 0 || y === 0 || z === 0) return 0;
  if (x === y && x === z) return 0;
  if (x === y) return 1;
  if (x === z) return 2;
  if (y === z) return 3;
  return 0;
}
function siteMc(x, y, z) {
  if (x === 0 || y === 0 || z === 0) return 0;
  if (x !== y) return 1;
  return x !== z ? 1 : 0;
}
function decode3(code) {
  return [code % 5, Math.floor(code / 5) % 5, Math.floor(code / 25) % 5];
}
var cached = null;
function getFssTables() {
  if (cached) return cached;
  const fssRdp = new Uint8Array(CODES * CODES * CODES * 3);
  const fssMc = new Uint8Array(CODES * CODES * CODES * 3);
  const skipTrip = new Uint8Array(CODES * CODES * CODES);
  for (let A = 0; A < CODES; A++) {
    const [a0, a1, a2] = decode3(A);
    for (let B = 0; B < CODES; B++) {
      const [b0, b1, b2] = decode3(B);
      for (let C = 0; C < CODES; C++) {
        const [c0, c1, c2] = decode3(C);
        const base = ((A * CODES + B) * CODES + C) * 3;
        const h0 = siteClass(a0, b0, c0);
        const h1 = siteClass(a1, b1, c1);
        const h2 = siteClass(a2, b2, c2);
        fssRdp[base] = h0;
        fssRdp[base + 1] = h1;
        fssRdp[base + 2] = h2;
        fssMc[base] = siteMc(a0, b0, c0);
        fssMc[base + 1] = siteMc(a1, b1, c1);
        fssMc[base + 2] = siteMc(a2, b2, c2);
        skipTrip[A * CODES * CODES + B * CODES + C] = (h0 > 0 ? 1 : 0) + (h1 > 0 ? 1 : 0) + (h2 > 0 ? 1 : 0);
      }
    }
  }
  cached = { fssRdp, fssMc, skipTrip };
  return cached;
}
function makeCompressSeqNucMat(seqnum, nSeqs, length, nucMat) {
  const packs = Math.ceil(length / 3);
  const stride = packs + 1;
  const cs = new Uint8Array(nSeqs * stride);
  const snStride = length + 1;
  for (let s = 0; s < nSeqs; s++) {
    const so = s * snStride;
    const co = s * stride;
    let pi = 1;
    for (let p = 1; p <= length; p += 3) {
      const a = nucMat[seqnum[p + so] & 255] ?? 0;
      const b = p + 1 <= length ? nucMat[seqnum[p + 1 + so] & 255] ?? 0 : 0;
      const c = p + 2 <= length ? nucMat[seqnum[p + 2 + so] & 255] ?? 0 : 0;
      cs[co + pi] = compress3(a, b, c);
      pi++;
    }
  }
  return { cs, packs, stride };
}
var seqnumGeneration = 0;
function seqnumFingerprint(_seqnum, nSeqs, length) {
  return nSeqs * 131 + length + seqnumGeneration * 997 | 0;
}

// src/engine/chi.ts
var fr = Math.fround;
function vbCLng(x) {
  const f = Math.floor(x);
  const d = x - f;
  if (d < 0.5) return f;
  if (d > 0.5) return f + 1;
  return f % 2 === 0 ? f : f + 1;
}
var cInt = Math.trunc;
function normalZ(Z) {
  const Z_MAX = 6;
  let NormalZx = 0;
  if (Math.abs(Z) < 5.9999999) {
    if (Z !== 0) {
      let Y = 0.5 * Math.abs(Z);
      let X;
      if (Y >= Z_MAX * 0.5) {
        X = 1;
      } else if (Y < 1) {
        const w = Y * Y;
        X = ((((((((124818987e-12 * w - 0.001075204047) * w + 0.005198775019) * w - 0.019198292004) * w + 0.059054035642) * w - 0.151968751364) * w + 0.319152932694) * w - 0.5319230073) * w + 0.797884560593) * Y * 2;
      } else {
        Y = Y - 2;
        X = (((((((((((((-45255659e-12 * Y + 15252929e-11) * Y - 19538132e-12) * Y - 676904986e-12) * Y + 0.001390604284) * Y - 79462082e-11) * Y - 0.002034254874) * Y + 0.006549791214) * Y - 0.010557625006) * Y + 0.011630447319) * Y - 0.009279453341) * Y + 0.005353579108) * Y - 0.002141268741) * Y + 535310849e-12) * Y + 0.999936657524;
      }
      if (X + 1 < 1 - X) NormalZx = X + 1;
      else NormalZx = 1 - X;
    }
  } else {
    const temp = (Math.abs(Z) - 5.999999) * 10;
    const Temp2 = Math.pow(1.6, temp);
    let WinP = Math.pow(10, -9);
    WinP = WinP / Temp2;
    NormalZx = WinP;
  }
  return NormalZx;
}
function chiPVal(X) {
  if (X === 0) return 1;
  let PValHolder = normalZ(-Math.sqrt(X));
  if (PValHolder === 0) {
    PValHolder = Math.pow(10, -9);
    PValHolder = PValHolder / (X - 34);
  }
  return PValHolder;
}
function calcChiValue(A, C, TotalLen) {
  const b = TotalLen - A;
  const D = TotalLen - C;
  let HMChi;
  if (A + C > 0 && b + D > 0) {
    HMChi = Math.pow(A * D - b * C, 2) * TotalLen * 2;
    HMChi = HMChi / (A + b);
    HMChi = HMChi / (C + D);
    HMChi = HMChi / (A + C);
    HMChi = HMChi / (b + D);
  } else {
    HMChi = 0;
  }
  return fr(HMChi);
}
var chiTableCache = /* @__PURE__ */ new Map();
function makeChiTable(maxABWin = 150) {
  const cached2 = chiTableCache.get(maxABWin);
  if (cached2) return cached2;
  const chimap = new Int32Array(maxABWin + 1);
  for (let g = 0; g <= 4 && g <= maxABWin; g++) chimap[g] = -1;
  let size = 0;
  for (let g = 5; g <= maxABWin; g++) size += (g + 1) * (g + 1);
  const chiTable = new Float32Array(size + 1);
  let j = -1;
  for (let g = 5; g <= maxABWin; g++) {
    chimap[g] = j + 1;
    for (let H = 0; H <= g; H++) {
      for (let i = 0; i <= g; i++) {
        j++;
        chiTable[j] = calcChiValue(H, i, g);
      }
    }
  }
  const t = { chiTable, chimap, maxABWin };
  chiTableCache.set(maxABWin, t);
  return t;
}
function getCriticalDiff(HWindowWidth, lowestProb) {
  let lPrb = lowestProb / 6;
  if (lPrb < 1e-4) lPrb = 1e-4;
  const hPrb = lPrb * 1.000000001;
  lPrb = lPrb * 0.999999999;
  let HMChi = 5;
  let TPVal = 10;
  let guard = 0;
  while (TPVal > lPrb && guard++ < 400) {
    HMChi = HMChi * 2;
    TPVal = chiPVal(HMChi);
    if (TPVal === Math.pow(10, -20)) {
      lPrb = TPVal;
      break;
    }
  }
  let LastLoChi = 0;
  let LastHiChi = HMChi * 2;
  let LastTPval = 0;
  let TempChi;
  guard = 0;
  for (; ; ) {
    TPVal = chiPVal(HMChi);
    if (TPVal * 1.000000001 > LastTPval && TPVal * 0.9999999999 < LastTPval) break;
    if (TPVal < lPrb) {
      TempChi = HMChi;
      HMChi = HMChi - (HMChi - LastLoChi) / 2;
      if (HMChi === TempChi) break;
      LastHiChi = TempChi;
    } else if (TPVal > hPrb) {
      TempChi = HMChi;
      HMChi = HMChi + (LastHiChi - HMChi) / 2;
      if (HMChi === TempChi) break;
      LastLoChi = TempChi;
    } else {
      break;
    }
    LastTPval = TPVal;
    if (++guard > 5e3) break;
  }
  const CriticalChi = HMChi;
  LastLoChi = 0;
  LastHiChi = HWindowWidth;
  let CriticalDiff = vbCLng(HWindowWidth / 2);
  guard = 0;
  do {
    if (CriticalDiff < 2) {
      CriticalDiff = 2;
      break;
    }
    const A = 0;
    const b = HWindowWidth;
    const C = CriticalDiff;
    const D = HWindowWidth - C;
    let h = Math.pow(A * D - b * C, 2) * HWindowWidth * 2;
    h = h / (A + b);
    h = h / (C + D);
    h = h / (A + C);
    h = h / (b + D);
    if (h > CriticalChi) {
      TempChi = CriticalDiff;
      CriticalDiff = vbCLng(CriticalDiff - (CriticalDiff - LastLoChi) / 2);
      LastHiChi = TempChi;
    } else if (h < CriticalChi) {
      TempChi = CriticalDiff;
      CriticalDiff = vbCLng(CriticalDiff + (LastHiChi - CriticalDiff) / 2);
      LastLoChi = TempChi;
    } else {
      break;
    }
    if (++guard > 1e3) break;
  } while (LastHiChi !== CriticalDiff && CriticalDiff !== LastLoChi);
  CriticalDiff = CriticalDiff - 1;
  return { criticalDiff: CriticalDiff, criticalChi: CriticalChi };
}
var ChiWorkspace = class {
  /** LenStrainSeq0 */
  L;
  /** Scores(0..L, 0..2) : Byte, stride L+1 */
  scores;
  /** Winscores(0..L+2*HW, 0..2) : Long, stride UBWS+1 (allocated for the worst case HW <= L) */
  winScores;
  /** Chivals(0..L, 0..2), SmoothChi(0..L, 0..2) : Double, stride L+1 */
  chiVals;
  smoothChi;
  /** BanWin(0..L+2*HW) : Long */
  banWin;
  /** MDMap(0..L) : Byte */
  mdMap;
  /** XDiffPos(0..L+200) / XPosDiff(0..L+200) : Long */
  xDiffPos;
  xPosDiff;
  /** XDP / XPD (Chimaera): 3 lists of length L+201 each */
  xdp;
  xpd;
  /** CompressSeq packs bound to current Seqnum (invalidated on buffer/n/fingerprint). */
  cs = null;
  csPacks = 0;
  csStride = 0;
  csSn = null;
  csN = 0;
  csFinger = 0;
  constructor(L) {
    this.L = L;
    const s = L + 1;
    this.scores = new Uint8Array(3 * s + 8);
    this.winScores = new Int32Array(3 * (2 * L + 8) + 8);
    this.chiVals = new Float64Array(3 * s + 8);
    this.smoothChi = new Float64Array(3 * s + 8);
    this.banWin = new Int32Array(3 * L + 16);
    this.mdMap = new Uint8Array(L + 16);
    this.xDiffPos = new Int32Array(L + 205);
    this.xPosDiff = new Int32Array(L + 205);
    this.xdp = new Int32Array((L + 201) * 3);
    this.xpd = new Int32Array((L + 201) * 3);
  }
  /** Rebuild CS when Seqnum buffer, nSeqs, or content fingerprint changes (ModSN in-place). */
  ensureCompressSeq(seqnum, nSeqs) {
    const finger = seqnumFingerprint(seqnum, nSeqs, this.L);
    if (this.cs && this.csSn === seqnum && this.csN === nSeqs && this.csFinger === finger) return;
    const packed = makeCompressSeqNucMat(seqnum, nSeqs, this.L, NUC_MAT);
    this.cs = packed.cs;
    this.csPacks = packed.packs;
    this.csStride = packed.stride;
    this.csSn = seqnum;
    this.csN = nSeqs;
    this.csFinger = finger;
  }
};
function findSubSeqCP(lenseq, seq1, seq2, seq3, seqnum, xdiffpos, xposdiff, packed) {
  const L = lenseq - 1;
  if (L <= 0) return 0;
  const nSeqs = Math.floor(seqnum.length / lenseq);
  const pack = packed ?? makeCompressSeqNucMat(seqnum, nSeqs, L, NUC_MAT);
  const { fssMc } = getFssTables();
  const s1o = seq1 * pack.stride;
  const s2o = seq2 * pack.stride;
  const s3o = seq3 * pack.stride;
  let y = 0;
  let xh = 0;
  for (let xi = 1; xi <= pack.packs; xi++) {
    const A = pack.cs[s1o + xi];
    const B = pack.cs[s2o + xi];
    const C = pack.cs[s3o + xi];
    const osf = (A * 15625 + B * 125 + C) * 3;
    if (fssMc[osf] + fssMc[osf + 1] + fssMc[osf + 2] === 0) {
      for (let z = 0; z < 3; z++) {
        xh++;
        if (xposdiff && xh < lenseq) xposdiff[xh - 1] = y;
      }
      continue;
    }
    for (let z = 0; z < 3; z++) {
      xh++;
      if (xh >= lenseq) break;
      if (xposdiff) xposdiff[xh - 1] = y;
      if (fssMc[osf + z]) {
        y++;
        xdiffpos[y] = xh;
      }
    }
  }
  return y;
}
function makeWindowSizeP(criticalDiffIn, lenXoverSeq, winFract, winSize, lHWindowWidth, proportionFlag) {
  let WindowWidth;
  let HWindowWidth;
  let CriticalDiff = criticalDiffIn;
  if (proportionFlag === 0) {
    WindowWidth = fr(winSize);
    HWindowWidth = cInt(WindowWidth / 2 + 0.51);
  } else {
    const f = cInt(winFract * lenXoverSeq);
    if (f > 20 && f < lenXoverSeq / 1.5) {
      WindowWidth = cInt(winFract * lenXoverSeq / 2) * 2 - 2;
    } else if (f <= 20) {
      if (lenXoverSeq > 15) WindowWidth = 20;
      else return { ok: false, hWindowWidth: lHWindowWidth, criticalDiff: CriticalDiff };
    } else {
      if (lenXoverSeq / 1.5 > 10) WindowWidth = cInt(lenXoverSeq / 1.5 / 2) * 2 - 2;
      else return { ok: false, hWindowWidth: lHWindowWidth, criticalDiff: CriticalDiff };
    }
    HWindowWidth = cInt(WindowWidth / 2 + 0.51);
    CriticalDiff = 2;
  }
  if (HWindowWidth * 2 > lenXoverSeq) HWindowWidth = cInt(lenXoverSeq * 0.75 / 2 + 0.51) - 1;
  if (HWindowWidth <= CriticalDiff) HWindowWidth = cInt(lenXoverSeq / 2 + 0.51) - 1;
  if (HWindowWidth < 6) {
    return { ok: false, hWindowWidth: lHWindowWidth, criticalDiff: CriticalDiff };
  }
  return { ok: true, hWindowWidth: HWindowWidth, criticalDiff: CriticalDiff };
}
function makeTWinP(findAllFlag, HWindowWidth, lenXoverSeq) {
  let TWin;
  if (findAllFlag === 0) {
    TWin = cInt(fr(HWindowWidth) / 4 + 0.51);
    if (TWin < 6) TWin = 6;
    if (TWin > HWindowWidth) TWin = HWindowWidth;
    if (TWin > cInt(fr(lenXoverSeq) / 2)) TWin = cInt(fr(lenXoverSeq) / 2);
  } else {
    TWin = HWindowWidth;
  }
  return TWin;
}
function winScoreCalcP(ubws, _criticalDiff, HWindowWidth, LenXoverSeq, lenSeq, seq1, seq2, seq3, scores, xDiffPos, seqNum, winScores) {
  const TO = lenSeq;
  const TO2 = lenSeq * 2;
  const FO = ubws + 1;
  const SO = FO * 2;
  winScores.fill(0, 0, Math.min(winScores.length, 3 * FO + 4));
  const ls1 = lenSeq * seq1;
  const ls2 = lenSeq * seq2;
  const ls3 = lenSeq * seq3;
  for (let X = 1; X <= LenXoverSeq; X++) {
    const xdp = xDiffPos[X];
    const s1 = seqNum[xdp + ls1];
    const s2 = seqNum[xdp + ls2];
    const s3 = seqNum[xdp + ls3];
    scores[X] = s1 === s2 ? 1 : 0;
    scores[X + TO] = s1 === s3 ? 1 : 0;
    scores[X + TO2] = s2 === s3 ? 1 : 0;
  }
  for (let X = LenXoverSeq - HWindowWidth + 1; X <= LenXoverSeq; X++) {
    winScores[0] += scores[X];
    winScores[FO] += scores[X + TO];
    winScores[SO] += scores[X + TO2];
  }
  for (let X = 1; X <= HWindowWidth; X++) {
    const LO = LenXoverSeq - HWindowWidth + X;
    winScores[X] = winScores[X - 1] - scores[LO] + scores[X];
    winScores[X + FO] = winScores[X + FO - 1] - scores[LO + TO] + scores[X + TO];
    winScores[X + SO] = winScores[X + SO - 1] - scores[LO + TO2] + scores[X + TO2];
  }
  for (let X = HWindowWidth + 1; X <= LenXoverSeq; X++) {
    const LO = X - HWindowWidth;
    winScores[X] = winScores[X - 1] - scores[LO] + scores[X];
    winScores[X + FO] = winScores[X + FO - 1] - scores[LO + TO] + scores[X + TO];
    winScores[X + SO] = winScores[X + SO - 1] - scores[LO + TO2] + scores[X + TO2];
  }
  for (let X = LenXoverSeq + 1; X < LenXoverSeq + HWindowWidth; X++) {
    const LO = X - HWindowWidth;
    const RO = X - LenXoverSeq;
    winScores[X] = winScores[X - 1] - scores[LO] + scores[RO];
    winScores[X + FO] = winScores[X + FO - 1] - scores[LO + TO] + scores[RO + TO];
    winScores[X + SO] = winScores[X + SO - 1] - scores[LO + TO2] + scores[RO + TO2];
  }
  return 1;
}
function calcChiValsP(UBWS, criticalDiff, HWindowWidth, LenXoverSeq, LenSeq, winScores, chiVals) {
  let MChi = 0;
  const FO = UBWS + 1;
  const SO = LenSeq + 1;
  const LO = HWindowWidth;
  for (let X = 0; X < LenXoverSeq; X++) {
    for (let Y = 0; Y <= 2; Y++) {
      const A = winScores[X + FO * Y];
      const C = winScores[X + LO + FO * Y];
      if (A - C > criticalDiff || A - C < -criticalDiff) {
        const B = fr(HWindowWidth - A);
        const D = fr(HWindowWidth - C);
        if (A + C > 0 && B + D > 0) {
          const E = fr(fr(A * D) - fr(B * C));
          const den = fr(fr(HWindowWidth * fr(A + C)) * fr(B + D));
          const ChiH = E * E * 2 / den;
          chiVals[X + SO * Y] = ChiH;
          if (ChiH > MChi) MChi = ChiH;
        } else chiVals[X + SO * Y] = 0;
      } else chiVals[X + SO * Y] = 0;
    }
  }
  return MChi;
}
function calcChiVals4P(UBWS, criticalDiff, HWindowWidth, LenXoverSeq, LenSeq, winScores, chiVals, banWins) {
  let MChi = 0;
  const FO = UBWS + 1;
  const SO = LenSeq + 1;
  const LO = HWindowWidth;
  for (let X = 0; X < LenXoverSeq; X++) {
    let bp1 = X - HWindowWidth;
    if (bp1 < 1) bp1 = bp1 + LenXoverSeq;
    if (banWins[X] === 0 && banWins[bp1] === 0) {
      for (let Y = 0; Y <= 2; Y++) {
        const A = winScores[X + FO * Y];
        const C = winScores[X + LO + FO * Y];
        if (A - C > criticalDiff || A - C < -criticalDiff) {
          const B = fr(HWindowWidth - A);
          const D = fr(HWindowWidth - C);
          if (A + C > 0 && B + D > 0) {
            const E = fr(fr(A * D) - fr(B * C));
            const num = fr(fr(E * E) * 2);
            const den = fr(fr(HWindowWidth * fr(A + C)) * fr(B + D));
            const ChiH = num / den;
            chiVals[X + SO * Y] = ChiH;
            if (ChiH > MChi) MChi = ChiH;
          } else chiVals[X + SO * Y] = 0;
        } else chiVals[X + SO * Y] = 0;
      }
    } else {
      chiVals[X] = 0;
      chiVals[X + SO] = 0;
      chiVals[X + SO * 2] = 0;
    }
  }
  return MChi;
}
function calcChiVals4P3(UBWS, _criticalDiff, HWindowWidth, LenXoverSeq, LenSeq, winScores, chiVals, banWins, chiTable, ctOff) {
  let MChi = 0;
  const FO = UBWS + 1;
  const SO = LenSeq + 1;
  const S1 = SO * 2;
  const F1 = FO * 2;
  const LO = HWindowWidth;
  const os1 = HWindowWidth + 1;
  for (let X = 0; X < LenXoverSeq; X++) {
    let bp1 = X - HWindowWidth;
    if (bp1 < 1) bp1 = bp1 + LenXoverSeq;
    if (banWins[X] === 0 && banWins[bp1] === 0) {
      chiVals[X] = chiTable[ctOff + winScores[X] + winScores[X + LO] * os1];
      chiVals[X + SO] = chiTable[ctOff + winScores[X + FO] + winScores[X + LO + FO] * os1];
      chiVals[X + S1] = chiTable[ctOff + winScores[X + F1] + winScores[X + LO + F1] * os1];
    } else {
      chiVals[X] = 0;
      chiVals[X + SO] = 0;
      chiVals[X + S1] = 0;
    }
  }
  for (let X = 0; X < LenXoverSeq; X++) if (chiVals[X] > MChi) MChi = chiVals[X];
  for (let X = 0; X < LenXoverSeq; X++) if (chiVals[X + SO] > MChi) MChi = chiVals[X + SO];
  for (let X = 0; X < LenXoverSeq; X++) if (chiVals[X + S1] > MChi) MChi = chiVals[X + S1];
  return MChi;
}
function smoothChiValsP(LenXoverSeq, LenSeq, chiVals, smoothChi) {
  const qWindowSize = 5;
  const OS = LenSeq + 1;
  const RO = qWindowSize * 2 + 1;
  for (let Y = 0; Y <= 2; Y++) {
    let RunCount = 0;
    for (let X = 0 - qWindowSize; X <= 1 + qWindowSize; X++) {
      if (X < 1) RunCount += chiVals[LenXoverSeq + X + Y * OS];
      else RunCount += chiVals[X + Y * OS];
    }
    smoothChi[Y * OS] = RunCount / RO;
    for (let X = 1 - qWindowSize; X < LenXoverSeq - qWindowSize; X++) {
      if (X > 0) {
        if (X + RO <= LenXoverSeq) RunCount = RunCount - chiVals[X + Y * OS] + chiVals[X + RO + Y * OS];
        else RunCount = RunCount - chiVals[X + Y * OS] + chiVals[X + RO - LenXoverSeq + Y * OS];
      } else RunCount = RunCount - chiVals[LenXoverSeq + X + Y * OS] + chiVals[X + RO + Y * OS];
      smoothChi[X + qWindowSize + Y * OS] = RunCount / RO;
    }
  }
  return 1;
}
function findMChiP(LenSeq, LenXoverSeq, chiVals) {
  let tMaxX = -1;
  let tMaxY = -1;
  let tMChi = 0;
  const SO = LenSeq + 1;
  for (let X = 0; X < LenXoverSeq; X++) {
    for (let Y = 0; Y <= 2; Y++) {
      const ChiV = chiVals[X + Y * SO];
      if (ChiV > tMChi) {
        tMChi = ChiV;
        tMaxX = X;
        tMaxY = Y;
      }
    }
  }
  return { maxX: tMaxX, maxY: tMaxY, mChi: tMChi };
}
function cleanChiVals(LenXoverSeq, LenSeq, chiVals) {
  const SO = LenSeq + 1;
  const SO2 = SO * 2;
  for (let X = 0; X < LenXoverSeq; X++) chiVals[X] = 0;
  for (let X = 0; X < LenXoverSeq; X++) chiVals[X + SO] = 0;
  for (let X = 0; X < LenXoverSeq; X++) chiVals[X + SO2] = 0;
  return 1;
}
function destroyPeak(MaxY, LS, RO, LO, LenXoverSeq, LOT, SmoothChi, ChiVals) {
  let EraseAll = 0;
  let Circuit1;
  const off = MaxY * (LS + 1);
  if (RO < 1) {
    RO = LenXoverSeq - RO;
    if (RO < 2) return 0;
  }
  Circuit1 = 0;
  if (RO > LenXoverSeq) {
    RO = RO - LenXoverSeq;
    if (RO >= LenXoverSeq) return 0;
    Circuit1 = 1;
  } else Circuit1 = 0;
  const setLOT_R = () => {
    if (RO > LenXoverSeq - 2) {
      if (RO === LenXoverSeq) {
        LOT[0] = SmoothChi[1 + off];
        LOT[1] = SmoothChi[2 + off];
      } else if (RO === LenXoverSeq - 1) {
        LOT[0] = SmoothChi[LenXoverSeq + off];
        LOT[1] = SmoothChi[1 + off];
      }
    } else {
      LOT[0] = SmoothChi[RO + 1 + off];
      LOT[1] = SmoothChi[RO + 2 + off];
    }
  };
  setLOT_R();
  let guard = 0;
  const maxGuard = 4 * LenXoverSeq + 16;
  while (SmoothChi[RO + off] > 0 && (SmoothChi[RO + off] >= LOT[0] || SmoothChi[RO + off] >= LOT[1])) {
    RO++;
    if (RO > LenXoverSeq) {
      RO = 1;
      if (Circuit1 === 1) {
        EraseAll = 1;
        break;
      } else Circuit1 = 1;
    }
    setLOT_R();
    if (++guard > maxGuard) {
      EraseAll = 1;
      break;
    }
  }
  if (EraseAll === 0) {
    if (LO < 1) {
      LO = LenXoverSeq - RO;
      if (LO < 2) return 0;
    }
    Circuit1 = 0;
    if (LO > LenXoverSeq) {
      LO = LO - LenXoverSeq;
      if (LO >= LenXoverSeq) return 0;
      Circuit1 = 1;
    } else Circuit1 = 0;
    const setLOT_L = () => {
      if (LO < 3) {
        if (LO === 1) {
          LOT[0] = SmoothChi[LenXoverSeq + off];
          LOT[1] = SmoothChi[LenXoverSeq - 1 + off];
        } else if (LO === 2) {
          LOT[0] = SmoothChi[1 + off];
          LOT[1] = SmoothChi[LenXoverSeq + off];
        }
      } else {
        LOT[0] = SmoothChi[LO - 1 + off];
        LOT[1] = SmoothChi[LO - 2 + off];
      }
    };
    setLOT_L();
    guard = 0;
    while (SmoothChi[LO + off] > 0 && (SmoothChi[LO + off] >= LOT[0] || SmoothChi[LO + off] >= LOT[1])) {
      LO--;
      if (LO < 1) {
        LO = LenXoverSeq;
        if (Circuit1 === 1) {
          EraseAll = 1;
          break;
        } else Circuit1 = 1;
      }
      setLOT_L();
      if (++guard > maxGuard) {
        EraseAll = 1;
        break;
      }
    }
  }
  if (EraseAll === 1) {
    for (let X = 0; X <= LenXoverSeq; X++) ChiVals[X + off] = 0;
  } else if (LO < RO) {
    for (let X = LO; X <= RO; X++) ChiVals[X + off] = 0;
  } else {
    for (let X = 0; X <= RO; X++) ChiVals[X + off] = 0;
    for (let X = LO; X <= LenXoverSeq; X++) ChiVals[X + off] = 0;
  }
  return 1;
}
function destroyPeaks(MaxY, LenXoverSeq, LS, LO, RO, SmoothChi, ChiVals) {
  const off1 = MaxY * (LS + 1);
  if (LO === 0) LO = 1;
  if (RO === 0) RO = 1;
  let X = 0;
  const SLO = LO;
  let Circuit1 = 0;
  let EraseAll = 0;
  let guard = 0;
  const maxGuard = 8 * LenXoverSeq + 32;
  const S = (i) => SmoothChi[i + off1];
  if (LenXoverSeq > 5) {
    while (S(LO) >= S(LO + 1) || S(LO) >= S(LO + 2)) {
      LO--;
      if (LO === RO) {
        EraseAll = 1;
        break;
      }
      if (LO < 1) {
        Circuit1++;
        if (Circuit1 === 2) {
          EraseAll = 1;
          break;
        }
        LO = LenXoverSeq + LO;
      }
      if (LO === RO) {
        EraseAll = 1;
        break;
      }
      if (LO > LenXoverSeq - 2) LO = LenXoverSeq - 2;
      if (++guard > maxGuard) {
        EraseAll = 1;
        break;
      }
    }
    if (LO === RO) EraseAll = 1;
    if (EraseAll === 0) {
      Circuit1 = 0;
      guard = 0;
      while ((S(LO) <= S(LO + 1) || S(LO) <= S(LO + 2)) && S(LO) > 1) {
        LO--;
        if (LO === RO) {
          EraseAll = 1;
          break;
        }
        if (LO < 1) {
          Circuit1++;
          if (Circuit1 === 2) {
            EraseAll = 1;
            break;
          }
          LO = LenXoverSeq + LO;
        }
        if (LO === RO) {
          EraseAll = 1;
          break;
        }
        if (++guard > maxGuard) {
          EraseAll = 1;
          break;
        }
      }
    }
    if (LO === RO) EraseAll = 1;
    if (EraseAll === 0) {
      if (RO <= 0) RO = LenXoverSeq + RO;
      guard = 0;
      while (X === 0) {
        RO++;
        if (LO === RO || RO === SLO) {
          EraseAll = 1;
          break;
        }
        if (RO > LenXoverSeq - 1) {
          RO = 1;
          if (RO > LO) {
            EraseAll = 1;
            break;
          }
        }
        if (LO === RO || RO === SLO) {
          EraseAll = 1;
          break;
        }
        if (S(RO) < S(RO - 1)) break;
        if (++guard > maxGuard) {
          EraseAll = 1;
          break;
        }
      }
    }
    if (EraseAll === 0) {
      guard = 0;
      while (X === 0) {
        RO++;
        if (LO === RO || RO === SLO) {
          EraseAll = 1;
          break;
        }
        if (RO > LenXoverSeq - 1) {
          RO = 1;
          if (RO > LO) {
            EraseAll = 1;
            break;
          }
        }
        if (S(RO) === 0 || S(RO) > S(RO - 1)) break;
        if (LO === RO || RO === SLO) {
          EraseAll = 1;
          break;
        }
        if (++guard > maxGuard) {
          EraseAll = 1;
          break;
        }
      }
    }
  } else EraseAll = 1;
  if (EraseAll === 1) {
    for (X = 0; X <= LenXoverSeq; X++) ChiVals[X + off1] = 0;
  } else if (LO < RO) {
    for (X = LO; X <= RO; X++) ChiVals[X + off1] = 0;
  } else {
    for (X = 0; X <= RO; X++) ChiVals[X + off1] = 0;
    for (X = LO; X <= LenXoverSeq; X++) ChiVals[X + off1] = 0;
  }
  return 1;
}
function newGrowState() {
  return { mpv: 0, winWin: 0, mChi: 0, topL: 0, topR: 0, topLO: 0, topRO: 0 };
}
function wrapLORO(LO, RO, LenXoverSeq) {
  if (LO < 1) LO = LenXoverSeq;
  if (RO > LenXoverSeq * 2) RO = RO - LenXoverSeq * 2;
  if (RO > LenXoverSeq) RO = RO - LenXoverSeq;
  return [LO, RO];
}
function growMChiWinP2(MaxABWin, LO, RO, LenXoverSeq, HWindowWidth, TWin, MaxY, LS, A, C, MaxFailCount, scores, chiTable, chimap, g) {
  const off1 = MaxY * (LS + 1);
  let FailCount = 0;
  let htpv = g.mChi;
  while (FailCount <= MaxFailCount) {
    A = A + scores[LO + off1];
    C = C + scores[RO + off1];
    const B = TWin - A;
    const D = TWin - C;
    if (B + D > 0) {
      let hMChi;
      if (TWin <= MaxABWin && chimap[TWin] >= 0) {
        hMChi = chiTable[chimap[TWin] + A + C * (TWin + 1)];
      } else {
        const dA = A;
        const dC = C;
        const dB = B;
        const dD = D;
        let E = dA * dD - dB * dC;
        E = E * E;
        E = E * 2;
        hMChi = E / (TWin * (dA + dC) * (dB + dD));
        if (hMChi < 0) hMChi = Math.abs(hMChi);
      }
      if (hMChi >= htpv) {
        htpv = hMChi;
        g.topLO = LO;
        g.topRO = RO;
        g.mChi = hMChi;
        g.winWin = TWin;
        FailCount = 0;
        g.topL = A;
        g.topR = C;
      } else {
        if (TWin === HWindowWidth && g.topL === 0 && g.topR === 0) {
          g.topL = A;
          g.topR = C;
        }
        FailCount++;
        if (FailCount > MaxFailCount) return 1;
      }
    } else {
      FailCount++;
      if (FailCount > MaxFailCount) return 1;
    }
    [LO, RO] = [LO - 1, RO + 1];
    [LO, RO] = wrapLORO(LO, RO, LenXoverSeq);
    TWin++;
  }
  return 1;
}
function growMChiWin2P2(MaxABWin, LO, RO, LenXoverSeq, HWindowWidth, TWin, MaxY, LS, a, c, MaxFailCount, scores, mdmap, chiTable, chimap, g) {
  const off1 = MaxY * (LS + 1);
  let FailCount = 0;
  let A = fr(a);
  let C = fr(c);
  let mchi = g.mChi;
  let htpv = mchi;
  while (FailCount <= MaxFailCount) {
    A = fr(A + scores[LO + off1]);
    C = fr(C + scores[RO + off1]);
    const B = fr(fr(TWin) - A);
    const D = fr(fr(TWin) - C);
    if (B + D > 0) {
      let hMChi;
      if (TWin <= MaxABWin && chimap[TWin] >= 0) {
        const aa = cInt(A);
        const cc = cInt(C);
        hMChi = chiTable[chimap[TWin] + aa + cc * (TWin + 1)];
      } else {
        let E = fr(fr(A * D) - fr(B * C));
        E = fr(E * E);
        E = fr(E * 2);
        const den = fr(fr(TWin * fr(A + C)) * fr(B + D));
        hMChi = E / den;
      }
      if (hMChi >= htpv) {
        htpv = hMChi;
        g.topLO = LO;
        g.topRO = RO;
        mchi = hMChi;
        g.winWin = TWin;
        FailCount = 0;
        g.topL = cInt(A);
        g.topR = cInt(C);
      } else {
        if (TWin === HWindowWidth && g.topL === 0 && g.topR === 0) {
          g.topL = cInt(A);
          g.topR = cInt(C);
        }
        FailCount++;
        if (FailCount > MaxFailCount) {
          g.mChi = mchi;
          return 1;
        }
      }
    } else {
      FailCount++;
      if (FailCount > MaxFailCount) {
        g.mChi = mchi;
        return 1;
      }
    }
    if (mdmap[RO] === 1 || mdmap[LO] === 1) break;
    RO++;
    LO--;
    if (mdmap[RO] === 1 || mdmap[LO] === 1) break;
    [LO, RO] = wrapLORO(LO, RO, LenXoverSeq);
    TWin++;
  }
  g.mChi = mchi;
  return 1;
}
function getACP(LenXoverSeq, LS, MaxY, MaxX, TWin, scores) {
  const os = MaxY * (LS + 1);
  let A = 0;
  let C = 0;
  for (let X = MaxX + 1 - TWin; X <= MaxX; X++) {
    if (X > 0) {
      if (X <= LenXoverSeq) A += scores[X + os];
      else A += scores[X - LenXoverSeq + os];
    } else A += scores[LenXoverSeq + X + os];
  }
  for (let X = MaxX + 1; X <= MaxX + TWin; X++) {
    if (X > 0) {
      if (X <= LenXoverSeq) C += scores[X + os];
      else C += scores[X - LenXoverSeq + os];
    } else C += scores[LenXoverSeq + X + os];
  }
  return { a: A, c: C };
}
function findSide(TopL, TopR, LS, LO, RO, WinWin, LenXoverSeq, MaxY, scores) {
  const off1 = MaxY * (LS + 1);
  let e = 0;
  for (let X = LO - WinWin; X < LO; X++) {
    if (X < 1) e += scores[LenXoverSeq + X + off1];
    else if (X > LenXoverSeq) e += scores[X - LenXoverSeq + off1];
    else e += scores[X + off1];
  }
  let A = TopL;
  let C = e;
  let B = WinWin - A;
  let D = WinWin - C;
  let E;
  let hMChi;
  if (A + C > 0 && B + D > 0) {
    E = A * D - B * C;
    hMChi = E * E * 2 / (WinWin * (A + C) * (B + D));
  } else hMChi = 0;
  const hiLeft = hMChi;
  e = 0;
  for (let X = RO + 1; X <= RO + WinWin; X++) {
    if (X < 1) e += scores[LenXoverSeq + X + off1];
    else if (X > LenXoverSeq) e += scores[X - LenXoverSeq + off1];
    else e += scores[X + off1];
  }
  A = TopR;
  C = e;
  B = WinWin - A;
  D = WinWin - C;
  if (A + C > 0 && B + D > 0) {
    E = A * D - B * C;
    hMChi = E * E * 2 / (WinWin * (A + C) * (B + D));
  } else hMChi = 0;
  return { hiLeft, hiRight: hMChi };
}
function optLeftBPMC(LO, HiLeft, TopL, MaxX, MaxY, WinWin, LenXOverSeq, LS, scores, MDMap) {
  const off = MaxY * (LS + 1);
  let G = 0;
  for (let X = LO - WinWin; X <= LO - 1; X++) {
    if (X < 1) G += scores[LenXOverSeq + X + off];
    else if (X > LenXOverSeq) G += scores[X - LenXOverSeq + off];
    else G += scores[X + off];
  }
  let P = MaxX - 1;
  let M = LO - 1;
  let n = LO - WinWin;
  if (P < 1) P = LenXOverSeq + P;
  if (n < 1) n = LenXOverSeq + n;
  if (M < 1) M = LenXOverSeq + M;
  let A = G;
  let C = TopL;
  let CurWin = cInt(HiLeft * 1e4);
  let CurWinPos = M;
  let Failcount = 0;
  let guard = 0;
  const maxGuard = 4 * LenXOverSeq + 64;
  for (; ; ) {
    A = A - scores[M + off];
    C = C - scores[P + off];
    C = C + scores[M + off];
    P = P - 1;
    n = n - 1;
    M = M - 1;
    if (MDMap[P] === 1 || MDMap[n] === 1 || MDMap[M] === 1) break;
    if (P < 1) P = LenXOverSeq;
    if (n < 1) n = LenXOverSeq;
    if (M < 1) M = LenXOverSeq;
    if (MDMap[P] === 1 || MDMap[n] === 1 || MDMap[M] === 1) break;
    A = A + scores[n + off];
    const B = WinWin - A;
    const D = WinWin - C;
    if (A + C > 0 && B + D > 0) {
      let E = A * D - B * C;
      let thMChi = E * E * 2;
      E = (A + C) * (B + D);
      E = E * WinWin;
      thMChi = thMChi / E;
      if (thMChi < 0) thMChi = Math.abs(thMChi);
      if (cInt(thMChi * 1e4) > CurWin) {
        CurWin = cInt(thMChi * 1e4);
        CurWinPos = M;
        Failcount = 0;
      } else {
        Failcount = Failcount + 1;
        if (Failcount > cInt(WinWin / 10)) break;
      }
    }
    if (++guard > maxGuard) break;
  }
  return CurWinPos + 1;
}
function optRightBPMC(RO, HiRight, TopR, MaxX, MaxY, WinWin, LenXOverSeq, LS, scores, MDMap) {
  const off = MaxY * (LS + 1);
  let G = 0;
  for (let X = RO + 1; X <= RO + WinWin; X++) {
    if (X < 1) G += scores[LenXOverSeq + X + off];
    else if (X > LenXOverSeq) G += scores[X - LenXOverSeq + off];
    else G += scores[X + off];
  }
  let P = RO + WinWin;
  let M = RO + 1;
  let n = MaxX;
  if (P > LenXOverSeq) P = P - LenXOverSeq;
  if (n > LenXOverSeq) n = n - LenXOverSeq;
  if (M > LenXOverSeq) M = M - LenXOverSeq;
  let A = TopR;
  let C = G;
  let CurWin = cInt(HiRight * 1e4);
  let CurWinPos = M;
  let Failcount = 0;
  let guard = 0;
  const maxGuard = 4 * LenXOverSeq + 64;
  for (; ; ) {
    A = A - scores[n + off];
    C = C - scores[M + off];
    A = A + scores[M + off];
    P = P + 1;
    n = n + 1;
    M = M + 1;
    if (MDMap[P] === 1 || MDMap[n] === 1 || MDMap[M] === 1) break;
    if (P > LenXOverSeq) P = 1;
    if (n > LenXOverSeq) n = 1;
    if (M > LenXOverSeq) M = 1;
    if (MDMap[P] === 1 || MDMap[n] === 1 || MDMap[M] === 1) break;
    C = C + scores[P + off];
    const B = WinWin - A;
    const D = WinWin - C;
    if (A + C > 0 && B + D > 0) {
      let E = A * D - B * C;
      let thMChi = E * E * 2;
      E = (A + C) * (B + D);
      E = E * WinWin;
      thMChi = thMChi / E;
      if (thMChi < 0) thMChi = Math.abs(thMChi);
      if (cInt(thMChi * 1e4) > CurWin) {
        CurWin = cInt(thMChi * 1e4);
        CurWinPos = M;
        Failcount = 0;
      } else {
        Failcount = Failcount + 1;
        if (Failcount > cInt(WinWin / 10)) break;
      }
    }
    if (++guard > maxGuard) break;
  }
  return CurWinPos - 1;
}
function makeBanWinP(UBBW, Seq1, Seq2, Seq3, HWindowWidth, LS, LenXoverSeq, BanWin, MDMap, MissingData, XPosDiff, XDiffPos, opts = {}) {
  const s1o = Seq1 * (LS + 1);
  const s2o = Seq2 * (LS + 1);
  const s3o = Seq3 * (LS + 1);
  if (opts.clearBanWin !== false) {
    for (let X = 0; X < UBBW; X++) BanWin[X] = 0;
  }
  if (opts.clearMdMap !== false) {
    for (let X = 0; X < LenXoverSeq + 2; X++) MDMap[X] = 0;
  }
  let lx = 0;
  for (let X = 1; X <= LS; X++) {
    if (lx > X) break;
    lx = X;
    if (MissingData[X + s1o] === 1 || MissingData[X + s2o] === 1 || MissingData[X + s3o] === 1) {
      const xpd = XPosDiff[X];
      MDMap[xpd] = 1;
      if (xpd + HWindowWidth - 1 <= LenXoverSeq) {
        for (let Y = xpd; Y < xpd + HWindowWidth; Y++) BanWin[Y] = 1;
      } else {
        for (let Y = xpd; Y <= LenXoverSeq; Y++) BanWin[Y] = 1;
        for (let Y = 0; Y < xpd + HWindowWidth - 1 - LenXoverSeq; Y++) BanWin[Y] = 1;
      }
      if (xpd < LenXoverSeq) {
        MDMap[xpd + 1] = 1;
        if (xpd + 2 - HWindowWidth > 0) {
          for (let Y = xpd + 2 - HWindowWidth; Y < xpd + 2; Y++) BanWin[Y] = 1;
        } else {
          for (let Y = 0; Y < xpd + 2; Y++) BanWin[Y] = 1;
          for (let Y = xpd + 2 - HWindowWidth + LenXoverSeq; Y <= LenXoverSeq; Y++) BanWin[Y] = 1;
        }
        if (XDiffPos[xpd + 1] > XDiffPos[xpd]) {
          if (X < XDiffPos[xpd + 1]) {
            X = XDiffPos[xpd + 1];
            if (X >= LS) break;
          }
        } else {
          MDMap[1] = 1;
          break;
        }
      } else {
        MDMap[1] = 1;
        break;
      }
    }
  }
  if (MDMap[LenXoverSeq] === 1 || MDMap[1] === 1) {
    for (let X = LenXoverSeq - HWindowWidth + 2; X <= LenXoverSeq; X++) BanWin[X] = 1;
  }
  return 1;
}
function applyMakeBanWinForSEN(SEN, Seq1, Seq2, Seq3, HWindowWidth, LS, LenXoverSeq, BanWin, MDMap, MissingData, XPosDiff, XDiffPos) {
  const fullBan = Math.min(BanWin.length, LS + HWindowWidth * 2 + 1);
  if (SEN <= 1) {
    BanWin.fill(0, 0, fullBan);
    MDMap.fill(0, 0, Math.min(MDMap.length, LS + 2));
    makeBanWinP(fullBan, Seq1, Seq2, Seq3, HWindowWidth, LS, LenXoverSeq, BanWin, MDMap, MissingData, XPosDiff, XDiffPos);
  } else {
    makeBanWinP(LS, Seq1, Seq2, Seq3, HWindowWidth, LS, LenXoverSeq, BanWin, MDMap, MissingData, XPosDiff, XDiffPos, {
      clearBanWin: true,
      // clears only [0..LS) via UBBW=LS
      clearMdMap: true
    });
  }
}
function centreBP2(LS, BEin, ENin, xPosDiff, xDiffPos, circularFlag, LSS, LenXoverSeq) {
  let BE = BEin;
  let EN = ENin;
  let BWarn = 0;
  let EWarn = 0;
  if (xPosDiff[BE] - 1 > 0) BE = BE - Math.round((BE - xDiffPos[xPosDiff[BE] - 1]) / 2 - 0.1);
  else BE = BE - Math.round((BE + LS - xDiffPos[LenXoverSeq]) / 2 - 0.1);
  if (BE === 0) BE = 1;
  else if (BE < 1) {
    if (circularFlag === 0) BE = 1;
    else BE = LS + BE;
  }
  if (circularFlag === 0) {
    if (xPosDiff[BE] < LSS) BWarn = 1;
  }
  xPosDiff[LS] = LenXoverSeq;
  if (xPosDiff[EN] + 1 <= LenXoverSeq) EN = EN + Math.round((xDiffPos[xPosDiff[EN] + 1] - EN) / 2 - 0.1);
  else EN = EN + Math.round((xDiffPos[1] + (LS - EN)) / 2 - 0.1);
  if (EN > LS) {
    if (circularFlag === 0) EN = LS;
    else EN = EN - LS;
  }
  if (circularFlag === 0) {
    if (xPosDiff[EN] > LenXoverSeq - LSS) EWarn = 1;
  }
  return { be: BE, en: EN, bWarn: BWarn, eWarn: EWarn };
}

// src/engine/stepdown.ts
var N_BINS = 101;
function vbLog10(x) {
  if (x > 0) return Math.log(x) / Math.LN10;
  return 1;
}
function pValCatBin(p) {
  let lpv = vbCLng(-vbLog10(p) * 2);
  if (lpv < 0) lpv = 0;
  if (lpv > 100) lpv = 100;
  return lpv;
}
function createPValCatBook(mcCorrection) {
  return {
    counts: new Int32Array(N_BINS),
    maxP: new Float64Array(N_BINS),
    mcCorrection: Math.max(1, mcCorrection),
    finalized: false
  };
}
function recordPValCat(book, rawP) {
  if (!(rawP > 0)) return;
  const bin = pValCatBin(rawP);
  book.counts[bin] = (book.counts[bin] ?? 0) + 1;
}
function stepDown2(book, rawP) {
  if (!(rawP > 0)) return rawP;
  const mc = book?.mcCorrection ?? 1;
  if (!book || !book.finalized) return rawP * mc;
  const lpv = vbCLng(-vbLog10(rawP) * 2);
  if (!(lpv > 0)) return rawP;
  if (lpv >= 100) return rawP * mc;
  const catNext = book.counts[lpv + 1] ?? 0;
  if (catNext > 0) {
    const left = rawP * (book.counts[lpv] ?? 0);
    const right = (book.maxP[lpv + 1] ?? 0) * catNext;
    return left > right ? left : right;
  }
  return rawP * mc;
}
function applyMcFlagCorrection(rawP, mcFlag, mcCorrection, book) {
  if (mcFlag === 0) return rawP * mcCorrection;
  if (mcFlag === 2) {
    if (book?.finalized) return stepDown2(book, rawP);
    return rawP;
  }
  return rawP;
}
function defaultUcThresh(lowestProb, mcFlag, mcCorrection) {
  return mcFlag === 0 ? lowestProb / Math.max(1, mcCorrection) : lowestProb;
}

// src/engine/settings.ts
var PROGRAM_RDP = 0;
var PROGRAM_GENECONV = 1;
var PROGRAM_BOOTSCAN = 2;
var PROGRAM_SISCAN = 5;
var PROGRAM_LARD = 7;
var PROGRAM_3SEQ = 8;
var PROGRAM_TOPAL = 9;

// src/engine/distAccel.ts
var COMPRESS14_STRIDE = 626;
function buildCompress14Tables() {
  const valid = new Uint8Array(COMPRESS14_STRIDE * COMPRESS14_STRIDE);
  const diffs = new Uint8Array(COMPRESS14_STRIDE * COMPRESS14_STRIDE);
  for (let a = 0; a < 625; a++) {
    const a0 = a % 5;
    const a1 = Math.floor(a / 5) % 5;
    const a2 = Math.floor(a / 25) % 5;
    const a3 = Math.floor(a / 125) % 5;
    const aa = [a0, a1, a2, a3];
    for (let b = 0; b < 625; b++) {
      const b0 = b % 5;
      const b1 = Math.floor(b / 5) % 5;
      const b2 = Math.floor(b / 25) % 5;
      const b3 = Math.floor(b / 125) % 5;
      const bb = [b0, b1, b2, b3];
      let v = 0;
      let d = 0;
      for (let i = 0; i < 4; i++) {
        const x = aa[i];
        const y = bb[i];
        if (x === 0 || y === 0) continue;
        v++;
        if (x !== y) d++;
      }
      const idx = a + b * COMPRESS14_STRIDE;
      valid[idx] = v;
      diffs[idx] = d;
    }
  }
  return { valid, diffs };
}
var TABLES = buildCompress14Tables();

// src/engine/rdp.ts
var MAXL = 169;
var BINOM = (() => {
  const w = MAXL + 1;
  const t = new Float64Array(w * w);
  for (let n = 0; n <= MAXL; n++) {
    t[n * w] = 1;
    for (let k = 1; k <= n; k++) t[n * w + k] = t[(n - 1) * w + k - 1] + (k <= n - 1 ? t[(n - 1) * w + k] : 0);
  }
  return t;
})();
var TT = Math.fround(0.7);

// src/engine/events.ts
var FLAG_TO_METHOD = {
  [PROGRAM_RDP]: "rdp",
  [PROGRAM_GENECONV]: "geneconv",
  [PROGRAM_BOOTSCAN]: "bootscan",
  [PROGRAM_MAXCHI]: "maxchi",
  [PROGRAM_CHIMAERA]: "chimaera",
  [PROGRAM_SISCAN]: "siscan",
  [PROGRAM_3SEQ]: "threeSeq",
  [PROGRAM_LARD]: "lard",
  [PROGRAM_TOPAL]: "topal"
};

// src/engine/centrebp.ts
function checkEnds(LS, RL, LSS, ChF, CirF, seq1, seq2, seq3, BPos, EPos, sn, XPD, XDP, missingData) {
  if (!missingData) return 0;
  const stride = LS + 1;
  const md = (pos, seq) => missingData[pos + seq * stride] ?? 0;
  let warn = 0;
  let bPos = BPos;
  let ePos = EPos;
  if (ChF === 0) {
    let Target;
    if (XPD[bPos] - RL > 0) Target = XDP[XPD[bPos] - RL];
    else if (CirF === 1) Target = XPD[bPos] - RL + LSS >= 0 ? XDP[XPD[bPos] - RL + LSS] : 1;
    else Target = 1;
    if (Target < bPos) {
      for (let X = Target; X <= bPos; X++) {
        if (md(X, seq1) === 1 || md(X, seq2) === 1 || md(X, seq3) === 1) {
          warn = 1;
          break;
        }
      }
    } else {
      for (let X = Target; X < LS; X++) {
        if (md(X, seq1) === 1 || md(X, seq2) === 1 || md(X, seq3) === 1) {
          warn = 1;
          break;
        }
      }
      if (warn === 0 && CirF === 0) {
        if (md(LS, seq1) === 1 || md(LS, seq2) === 1 || md(LS, seq3) === 1) warn = 1;
        if (md(1, seq1) === 1 || md(1, seq2) === 1 || md(1, seq3) === 1) warn = 1;
      }
      if (warn === 0) {
        for (let X = 2; X <= bPos; X++) {
          if (md(X, seq1) === 1 || md(X, seq2) === 1 || md(X, seq3) === 1) {
            warn = 1;
            break;
          }
        }
      }
    }
  } else {
    let Target;
    if (XPD[ePos] + RL < LSS) Target = XDP[XPD[ePos] + RL];
    else if (CirF === 1) Target = XDP[XPD[ePos] + RL - LSS];
    else Target = LS;
    if (XPD[ePos] - RL > 0) ePos = XDP[XPD[ePos] - RL];
    else if (CirF === 1) ePos = XPD[ePos] - RL + LSS >= 0 ? XDP[XPD[ePos] - RL + LSS] : 1;
    else ePos = 1;
    if (ePos < 1) ePos = CirF === 1 ? ePos + LS : LS;
    if (Target > ePos) {
      for (let X = ePos; X <= Target; X++) {
        if (md(X, seq1) === 1 || md(X, seq2) === 1 || md(X, seq3) === 1) {
          warn = 1;
          break;
        }
      }
    } else {
      for (let X = ePos; X <= LS - 1; X++) {
        if (md(X, seq1) === 1 || md(X, seq2) === 1 || md(X, seq3) === 1) {
          warn = 1;
          break;
        }
      }
      if (warn === 0 && CirF === 0) {
        if (md(LS, seq1) === 1 || md(LS, seq2) === 1 || md(LS, seq3) === 1) warn = 1;
        if (md(1, seq1) === 1 || md(1, seq2) === 1 || md(1, seq3) === 1) warn = 1;
      }
      if (warn === 0) {
        for (let X = 2; X <= Target; X++) {
          if (md(X, seq1) === 1 || md(X, seq2) === 1 || md(X, seq3) === 1) {
            warn = 1;
            break;
          }
        }
      }
    }
  }
  void sn;
  return warn;
}
function checkEndsVB(RL, LSS, ChF, CirF, seq1, seq2, seq3, BPos, EPos, sn, XPD, XDP, circularFlag, missingData, LS, OBE = 0, oEN = 0) {
  let warn = 0;
  const tBPos = BPos;
  const tEPos = EPos;
  let b = BPos;
  let e = EPos;
  const md = (pos, seq) => {
    if (!missingData) return 0;
    return missingData[pos + seq * (LS + 1)] ?? 0;
  };
  const anyMd = (x) => md(x, seq1) === 1 || md(x, seq2) === 1 || md(x, seq3) === 1;
  if (OBE === 0 && oEN === 0) {
    if (XPD[e] === 0) {
      let cycle = 0;
      while (XPD[e] === 0) {
        e--;
        if (e < 1) {
          e = LS;
          if (cycle === 1) return 1;
          cycle = 1;
        }
      }
    }
    if (XPD[b] === 0) {
      while (XPD[b] === 0) {
        b++;
        if (b > LS) b = 1;
      }
    }
    warn = checkEnds(LS, RL, LSS, ChF, CirF, seq1, seq2, seq3, b, e, sn, XPD, XDP, missingData);
    if (circularFlag === 0) {
      if (ChF === 0) {
        if (XPD[tBPos] < RL) warn = 1;
      } else if (XPD[tEPos] + RL > LSS) warn = 1;
    }
  } else if (missingData) {
    if (ChF === 0) {
      let Target;
      if (OBE - RL > 0) Target = XDP[OBE - RL];
      else if (CirF === 1) Target = OBE - RL + LSS >= 0 ? XDP[OBE - RL + LSS] : 1;
      else Target = 1;
      if (OBE + RL < LSS) b = XDP[OBE + RL];
      else if (CirF === 1) b = XDP[OBE + RL - LSS];
      else b = LS;
      if (Target < b) {
        for (let x = Target; x <= b; x++) if (anyMd(x)) {
          warn = 1;
          break;
        }
      } else {
        for (let x = Target; x <= LS - 1; x++) if (anyMd(x)) {
          warn = 1;
          break;
        }
        if (CirF === 0) {
          if (anyMd(LS) || anyMd(1)) warn = 1;
        }
        if (warn === 0) {
          for (let x = 2; x <= b; x++) if (anyMd(x)) {
            warn = 1;
            break;
          }
        }
      }
    } else {
      let Target;
      if (oEN + RL < LSS) Target = XDP[oEN + RL];
      else if (CirF === 1) Target = XDP[oEN + RL - LSS];
      else Target = LS;
      if (oEN - RL > 0) e = XDP[oEN - RL];
      else if (CirF === 1) e = oEN - RL + LSS >= 0 ? XDP[oEN - RL + LSS] : 1;
      else e = 1;
      if (e < 1) e = CirF === 1 ? e + LS : LS;
      if (Target > e) {
        for (let x = e; x <= Target; x++) if (anyMd(x)) {
          warn = 1;
          break;
        }
      } else {
        for (let x = e; x <= LS - 1; x++) if (anyMd(x)) {
          warn = 1;
          break;
        }
        if (CirF === 0) {
          if (anyMd(LS) || anyMd(1)) warn = 1;
        }
        if (warn === 0) {
          for (let x = 2; x <= Target; x++) if (anyMd(x)) {
            warn = 1;
            break;
          }
        }
      }
    }
    if (circularFlag === 0) {
      if (ChF === 0) {
        if (OBE < RL) warn = 1;
      } else if (oEN + RL > LSS) warn = 1;
    }
  }
  void tBPos;
  void tEPos;
  return warn;
}

// src/engine/maxchiParallel.ts
import { createRequire as createRequire2 } from "node:module";

// src/engine/parallelPool.ts
import { createRequire } from "node:module";
var req = createRequire(import.meta.url);

// src/engine/maxchiParallel.ts
var req2 = createRequire2(import.meta.url);

// src/engine/maxchi.ts
function resolveScanOptions(aln, o, defaultWinSize) {
  const winSize = o.winSize ?? defaultWinSize;
  const lowestProb = o.lowestProb ?? 0.05;
  const n = aln.nSeqs;
  const nTriplets = n * (n - 1) * (n - 2) / 6;
  const lHWindowWidth = vbCLng(winSize / 2);
  const maxABWin = o.maxABWin ?? 150;
  const mcCorrection = o.mcCorrection ?? Math.max(1, nTriplets);
  const mcFlag = o.mcFlag ?? 0;
  const pvalCat = o.pvalCat !== void 0 ? o.pvalCat : mcFlag === 2 ? createPValCatBook(mcCorrection) : null;
  return {
    winSize,
    winFract: o.winFract ?? 0.1,
    proportionFlag: o.proportionFlag ?? 0,
    lowestProb,
    mcCorrection,
    mcFlag,
    circularFlag: o.circularFlag ?? 0,
    longWindedFlag: o.longWindedFlag ?? 1,
    criticalDiff: o.criticalDiff ?? getCriticalDiff(lHWindowWidth, lowestProb).criticalDiff,
    lHWindowWidth,
    maxABWin,
    sEventNumber: o.sEventNumber ?? 0,
    missingData: o.missingData ?? null,
    table: makeChiTable(maxABWin),
    roleTracker: o.roleTracker ?? null,
    pvalCat,
    // EarlyBale=1 only for FastRecCheckMC *screen* (bail without storing events).
    // Events mode (MCXoverFIV) must keep earlyBale=0 or peaks are never recorded.
    earlyBale: o.earlyBale ?? 0,
    ucThresh: o.ucThresh ?? defaultUcThresh(lowestProb, mcFlag, mcCorrection)
  };
}
function pickActiveLongWinded(seq1, seq2, seq3, tracker) {
  const c = tracker.counts;
  const lpv = tracker.storeLPV;
  const c1 = c[seq1] ?? 0;
  const c2 = c[seq2] ?? 0;
  const c3 = c[seq3] ?? 0;
  let daughter;
  let minorP;
  let majorP;
  if (c1 < c2 && c1 < c3) {
    daughter = seq1;
    majorP = seq2;
    minorP = seq3;
  } else if (c2 < c1 && c2 < c3) {
    daughter = seq2;
    majorP = seq1;
    minorP = seq3;
  } else if (c3 < c1 && c3 < c2) {
    daughter = seq3;
    majorP = seq1;
    minorP = seq2;
  } else if ((lpv[seq1] ?? 0) >= (lpv[seq2] ?? 0) && (lpv[seq1] ?? 0) >= (lpv[seq3] ?? 0)) {
    daughter = seq1;
    majorP = seq2;
    minorP = seq3;
  } else if ((lpv[seq2] ?? 0) >= (lpv[seq1] ?? 0) && (lpv[seq2] ?? 0) >= (lpv[seq3] ?? 0)) {
    daughter = seq2;
    majorP = seq1;
    minorP = seq3;
  } else {
    daughter = seq3;
    majorP = seq1;
    minorP = seq2;
  }
  return { daughter, majorP, minorP };
}
function noteStoredRole(tracker, daughter, probability) {
  if (daughter < 0) return;
  while (tracker.counts.length <= daughter) tracker.counts.push(0);
  while (tracker.storeLPV.length <= daughter) tracker.storeLPV.push(1);
  tracker.counts[daughter]++;
  if (tracker.counts[daughter] === 1 || probability > tracker.storeLPV[daughter]) {
    tracker.storeLPV[daughter] = probability;
  }
}
function resolveParents(aln, triplet, beginning, ending, maxY) {
  const L = aln.length;
  const stride = L + 1;
  const sn = aln.seqnum;
  const inside = (p) => beginning <= ending ? p >= beginning && p <= ending : p >= beginning || p <= ending;
  const pairs = [
    [0, 1],
    [0, 2],
    [1, 2]
  ];
  const nIn = [0, 0, 0];
  const diffIn = [0, 0, 0];
  const nOut = [0, 0, 0];
  const idOut = [0, 0, 0];
  for (let p = 1; p <= L; p++) {
    const ins = inside(p);
    for (let k = 0; k < 3; k++) {
      const a = sn[p + triplet[pairs[k][0]] * stride];
      const b = sn[p + triplet[pairs[k][1]] * stride];
      if (a === 46 || b === 46) continue;
      if (ins) {
        nIn[k]++;
        if (a !== b) diffIn[k]++;
      } else {
        nOut[k]++;
        if (a === b) idOut[k]++;
      }
    }
  }
  for (let k = 0; k < 3; k++) {
    if (nIn[k] === 0 || nOut[k] === 0) return { daughter: -1, majorP: -1, minorP: -1 };
  }
  const distIn = [0, 0, 0];
  for (let k = 0; k < 3; k++) distIn[k] = diffIn[k] / nIn[k];
  let kClose = 0;
  for (let k = 1; k < 3; k++) if (distIn[k] < distIn[kClose]) kClose = k;
  if (maxY !== void 0 && maxY >= 0 && maxY <= 2) {
    if (distIn[maxY] <= distIn[kClose] * 1.05 + 1e-6) kClose = maxY;
  }
  const [ia, ib] = pairs[kClose];
  const majorIdx = 3 - ia - ib;
  const majorP = triplet[majorIdx];
  const kA = pairs.findIndex(([x, y]) => x === majorIdx && y === ia || y === majorIdx && x === ia);
  const kB = pairs.findIndex(([x, y]) => x === majorIdx && y === ib || y === majorIdx && x === ib);
  const idA = idOut[kA] / nOut[kA];
  const idB = idOut[kB] / nOut[kB];
  if (idA >= idB) return { daughter: triplet[ia], majorP, minorP: triplet[ib] };
  return { daughter: triplet[ib], majorP, minorP: triplet[ia] };
}
function assignEventRoles(aln, triplet, beginning, ending, opts) {
  const [seq1, seq2, seq3] = triplet;
  let par = resolveParents(aln, triplet, beginning, ending, opts.maxY);
  if (par.daughter < 0) {
    if ((opts.longWindedFlag ?? 1) === 1 && opts.tracker) {
      par = pickActiveLongWinded(seq1, seq2, seq3, opts.tracker);
    } else {
      par = { daughter: seq1, majorP: seq2, minorP: seq3 };
    }
  }
  if (opts.parentOrder === "rdp") {
    return { daughter: par.daughter, majorP: par.minorP, minorP: par.majorP };
  }
  return par;
}
function shrinkFindDaughterPrgF34(beginning, ending, seq1, seq2, seq3, maxY, loHiFlag, seqnum, L, xPosDiff, xDiffPos, mdMap, lenXoverSeq, circularFlag) {
  let RS = beginning;
  let RE = ending;
  if (RS > L) RS = circularFlag === 0 ? L : RS - L;
  if (RE > L) RE = circularFlag === 0 ? L : RE - L;
  if (RS < 1) RS = circularFlag === 0 ? 1 : L + RS;
  if (RE < 1) RE = circularFlag === 0 ? 1 : L + RE;
  let Hi1;
  let Hi2;
  if (maxY === 0) {
    Hi1 = seq1;
    Hi2 = seq2;
  } else if (maxY === 1) {
    Hi1 = seq1;
    Hi2 = seq3;
  } else {
    Hi1 = seq3;
    Hi2 = seq2;
  }
  const stride = L + 1;
  const nt = (pos, seq) => Number(seqnum[pos + seq * stride] ?? 46);
  const pairMatch = (xi) => {
    const p = Number(xDiffPos[xi] ?? 0);
    return nt(p, Hi1) === nt(p, Hi2);
  };
  const inMd = (xi) => xi >= 0 && xi <= mdMap.length - 1;
  let BE = RS;
  let EN = RE;
  let x = Number(xPosDiff[RS] ?? 0);
  if (x === 0) x = 1;
  for (let guard = 0; guard < lenXoverSeq + 8; guard++) {
    const match = pairMatch(x);
    if (loHiFlag === 1 ? !match : match) break;
    x = x - 1;
    if (inMd(x) && mdMap[x] === 1) break;
    if (x < 1) {
      if (circularFlag === 1) {
        if (x === Number(xPosDiff[RE] ?? 0)) {
          x = x + 1;
          break;
        }
        x = lenXoverSeq;
      } else break;
    }
    if (x === Number(xPosDiff[RE] ?? 0)) {
      x = x + 1;
      break;
    }
  }
  RS = Number(xDiffPos[x] ?? RS);
  x = Number(xPosDiff[RS] ?? 0);
  for (let guard = 0; guard < lenXoverSeq + 8; guard++) {
    const match = pairMatch(x);
    if (loHiFlag === 1 ? match : !match) {
      BE = Number(xDiffPos[x] ?? BE);
      break;
    }
    x = x + 1;
    if (inMd(x) && mdMap[x] === 1) break;
    if (x > lenXoverSeq) {
      if (circularFlag === 1) x = 1;
      else break;
    }
    if (x === Number(xPosDiff[RE] ?? 0)) {
      x = x - 1;
      break;
    }
  }
  x = Number(xPosDiff[RE] ?? 0);
  if (x > mdMap.length - 1) x = mdMap.length - 1;
  if ((mdMap[x] ?? 1) === 0) {
    for (let guard = 0; guard < lenXoverSeq + 8; guard++) {
      const match = pairMatch(x);
      if (loHiFlag === 1 ? !match : match) break;
      x = x + 1;
      if (inMd(x) && mdMap[x] === 1) break;
      if (x > lenXoverSeq) {
        if (circularFlag === 1) {
          x = 1;
          if (inMd(x) && mdMap[x] === 1) break;
        } else break;
      }
      if (x === Number(xPosDiff[RS] ?? 0)) {
        x = x - 1;
        break;
      }
    }
  }
  RE = Number(xDiffPos[x] ?? RE);
  x = Number(xPosDiff[RE] ?? 0);
  if (x === 0) x = 1;
  for (let guard = 0; guard < lenXoverSeq + 8; guard++) {
    const match = pairMatch(x);
    if (loHiFlag === 1 ? match : !match) {
      EN = Number(xDiffPos[x] ?? EN);
      break;
    }
    if (x > 0 && inMd(x) && mdMap[x] === 1) break;
    x = x - 1;
    if (inMd(x) && mdMap[x] === 1) break;
    if (x < 1) {
      if (circularFlag === 1) x = lenXoverSeq;
      else break;
    }
    if (x === Number(xPosDiff[RS] ?? 0)) {
      x = x + 1;
      break;
    }
  }
  let outB = beginning;
  let outE = ending;
  const xpBE = Number(xPosDiff[BE] ?? 0);
  const xpEN = Number(xPosDiff[EN] ?? 0);
  const xpBeg = Number(xPosDiff[beginning] ?? 0);
  const xpEnd = Number(xPosDiff[ending] ?? 0);
  if (Math.abs(xpEN - xpEnd) < 5) outE = EN;
  else if (Math.abs(xpEN - (xpEnd - L)) < 5) outE = EN;
  else if (Math.abs(xpEN - L) - xpEnd < 5) outE = EN;
  if (Math.abs(xpBE - xpBeg) < 5) outB = BE;
  else if (Math.abs(xpBE - (xpBeg - L)) < 5) outB = BE;
  else if (Math.abs(xpBE - L) - xpBeg < 5) outB = BE;
  return { beginning: outB, ending: outE };
}
function scanTripletMC(aln, ws, o, seq1, seq2, seq3, mode = "events") {
  const result = { events: [], found: false, bqpv: 1 };
  const L = aln.length;
  const SO = L + 1;
  const dll = mode === "screen";
  const SEN = o.sEventNumber;
  const earlyBale = o.earlyBale || (mode === "screen" ? 1 : 0);
  const ratio = (a, b) => dll ? Math.fround(a / b) : a / b;
  ws.ensureCompressSeq(aln.seqnum, aln.nSeqs);
  const lenX = findSubSeqCP(L + 1, seq1, seq2, seq3, aln.seqnum, ws.xDiffPos, ws.xPosDiff, {
    cs: ws.cs,
    packs: ws.csPacks,
    stride: ws.csStride
  });
  ws.xPosDiff[L] = lenX;
  if (lenX < o.criticalDiff * 2 || lenX < 7) return result;
  const ws0 = makeWindowSizeP(o.criticalDiff, lenX, o.winFract, o.winSize, o.lHWindowWidth, o.proportionFlag);
  if (!ws0.ok) return result;
  const HW = ws0.hWindowWidth;
  const criticalDiff = ws0.criticalDiff;
  const UBWS = L + HW * 2;
  winScoreCalcP(UBWS, criticalDiff, HW, lenX, L + 1, seq1, seq2, seq3, ws.scores, ws.xDiffPos, aln.seqnum, ws.winScores);
  let mChi;
  const banned = o.longWindedFlag === 1 && SEN > 0 || o.circularFlag === 0;
  if (banned) {
    if (SEN > 0 && o.missingData) {
      applyMakeBanWinForSEN(SEN, seq1, seq2, seq3, HW, L, lenX, ws.banWin, ws.mdMap, o.missingData, ws.xPosDiff, ws.xDiffPos);
    } else {
      ws.mdMap.fill(0, 0, Math.min(ws.mdMap.length, L + 2));
      ws.banWin.fill(0, 0, Math.min(ws.banWin.length, L + HW * 2 + 2));
    }
    if (o.circularFlag === 0) {
      ws.mdMap[1] = 1;
      ws.mdMap[lenX] = 1;
      for (let x = lenX - HW + 2; x <= lenX; x++) ws.banWin[x] = 1;
    }
    if (HW > 4 && HW <= o.maxABWin) {
      mChi = calcChiVals4P3(UBWS, criticalDiff, HW, lenX, L, ws.winScores, ws.chiVals, ws.banWin, o.table.chiTable, o.table.chimap[HW]);
    } else {
      mChi = calcChiVals4P(UBWS, criticalDiff, HW, lenX, L, ws.winScores, ws.chiVals, ws.banWin);
    }
  } else {
    if (SEN === 1) {
      ws.mdMap.fill(0, 0, Math.min(ws.mdMap.length, L + 2));
      ws.banWin.fill(0, 0, Math.min(ws.banWin.length, L + HW * 2 + 2));
    }
    mChi = calcChiValsP(UBWS, criticalDiff, HW, lenX, L, ws.winScores, ws.chiVals);
  }
  const clean = (both) => {
    cleanChiVals(lenX, L, ws.chiVals);
    if (both) cleanChiVals(lenX, L, ws.smoothChi);
  };
  if (o.proportionFlag === 0) {
    if (chiPVal(mChi) * ratio(lenX, HW) * 3 > o.lowestProb) {
      clean(false);
      return result;
    }
  } else if (chiPVal(mChi) * ratio(lenX, HW) * 6 * o.mcCorrection > o.lowestProb) {
    clean(false);
    return result;
  }
  smoothChiValsP(lenX, L, ws.chiVals, ws.smoothChi);
  mChi = 0;
  let wasteOfTime = 0;
  let redox = 0;
  const LOT = new Float64Array(2);
  while (redox <= 100) {
    redox++;
    const pk = findMChiP(L, lenX, ws.chiVals);
    let maxX = pk.maxX;
    const maxY = pk.maxY;
    mChi = pk.mChi;
    if (maxX === -1 || maxY === -1 || redox > 100) {
      clean(false);
      return result;
    }
    const mPrb = chiPVal(mChi);
    if (o.proportionFlag === 0) {
      if (mPrb * ratio(lenX, HW) * 3 > o.lowestProb || mPrb === 1) {
        clean(true);
        return result;
      }
    } else if (mPrb * ratio(lenX, HW) * 6 * o.mcCorrection > o.lowestProb || mPrb === 1) {
      clean(true);
      return result;
    }
    if (!(mPrb < o.lowestProb)) break;
    const maxz = maxX;
    if (maxX === 0) maxX = 1;
    let TWin = makeTWinP(0, HW, lenX);
    let maxFail = HW * 2;
    if (maxFail > Math.trunc((lenX - TWin * 2) / 2)) maxFail = Math.trunc((lenX - TWin * 2) / 2);
    if (maxFail === 0) maxFail = 1;
    let winWin = HW;
    const ac = getACP(lenX, L, maxY, maxX, TWin, ws.scores);
    const A = ac.a;
    const C = ac.c;
    const pMaxX = maxX;
    if (maxX < 1) {
      if (o.circularFlag === 1) maxX = lenX + maxX;
      else maxX = 1;
    } else if (maxX > lenX) {
      if (o.circularFlag === 1) maxX = maxX - lenX;
      else maxX = lenX - 1;
    }
    const g = newGrowState();
    if (TWin >= HW) {
      g.topL = A;
      g.topR = C;
    } else {
      g.topL = 0;
      g.topR = 0;
    }
    TWin++;
    g.mpv = mPrb * ratio(lenX, HW);
    g.winWin = winWin;
    g.mChi = mChi;
    g.topLO = maxX - HW + 1;
    g.topRO = maxX + HW;
    let LO = maxX - TWin + 1;
    if (LO < 0) LO = lenX + LO;
    let RO = maxX + TWin;
    if (RO > lenX * 2) RO = RO - lenX * 2;
    if (RO >= lenX) {
      if (ws.mdMap[lenX] === 0) RO = RO - lenX;
      else {
        TWin = TWin - 1;
        RO = lenX;
        LO = maxX - TWin + 1;
        if (LO < 0) LO = lenX + LO;
      }
    }
    const useMdGrow = dll ? o.longWindedFlag === 1 && (o.circularFlag === 0 || SEN > 1) : o.longWindedFlag === 1 && (o.circularFlag === 0 || SEN > 0);
    if (useMdGrow) {
      growMChiWin2P2(o.maxABWin, LO, RO, lenX, HW, TWin, maxY, L, A, C, maxFail, ws.scores, ws.mdMap, o.table.chiTable, o.table.chimap, g);
    } else {
      growMChiWinP2(o.maxABWin, LO, RO, lenX, HW, TWin, maxY, L, A, C, maxFail, ws.scores, o.table.chiTable, o.table.chimap, g);
    }
    winWin = g.winWin;
    const mChiG = g.mChi;
    let mpv;
    if (winWin < HW) mpv = chiPVal(mChiG) * ratio(lenX, winWin);
    else if (mChiG < 2e4) mpv = chiPVal(mChiG) * ratio(lenX, HW);
    else mpv = Math.pow(10, -200);
    let xMPV = mpv * 3;
    if (xMPV < result.bqpv) result.bqpv = xMPV;
    if (earlyBale === 1 && xMPV < o.ucThresh) {
      result.found = true;
      clean(true);
      return result;
    }
    xMPV = applyMcFlagCorrection(xMPV, o.mcFlag, o.mcCorrection, o.pvalCat);
    mpv = xMPV;
    LO = maxX - winWin;
    RO = maxX + winWin - 1;
    if (RO >= lenX * 2) RO = RO - lenX * 2;
    if (RO > lenX) {
      if (ws.mdMap[RO - lenX] === 0) RO = RO - lenX;
      else RO = lenX;
    }
    if (LO < 1) LO = LO + lenX;
    if (mpv < o.lowestProb) {
      if (dll) {
        result.found = true;
        clean(true);
        return result;
      }
      if (LO - winWin + lenX < 0) LO = -lenX + winWin;
      const side = findSide(g.topL, g.topR, L, LO, RO, winWin, lenX, maxY, ws.scores);
      let BE;
      let EN;
      let loHiFlag;
      if (side.hiLeft >= side.hiRight) {
        const cur = optLeftBPMC(LO, side.hiLeft, g.topL, maxX, maxY, winWin, lenX, L, ws.scores, ws.mdMap);
        LO = cur;
        if (LO > lenX) LO = 1;
        loHiFlag = g.topR > g.topL ? 0 : 1;
        if (LO < 1) LO = LO + lenX;
        if (maxX < 1) RO = lenX + maxX;
        else if (maxX > lenX) RO = maxX - lenX;
        else if (maxX === 1) RO = ws.mdMap[1] === 0 && ws.banWin[1] === 0 ? maxX : lenX;
        else RO = maxX;
        if (RO > 0) RO = RO - 1;
        let guard = 0;
        while (ws.mdMap[RO] !== 0) {
          RO = RO - 1;
          if (RO < 1) RO = lenX;
          if (++guard > lenX + 8) break;
        }
        RO = RO + 1;
        if (RO > lenX) RO = lenX;
        BE = LO + 1 > lenX ? ws.xDiffPos[LO] : ws.xDiffPos[LO + 1];
        EN = ws.xDiffPos[RO];
      } else {
        const cur = optRightBPMC(RO, side.hiRight, g.topR, maxX, maxY, winWin, lenX, L, ws.scores, ws.mdMap);
        RO = cur;
        if (RO < 1) RO = lenX;
        loHiFlag = g.topR > g.topL ? 1 : 0;
        if (RO >= lenX * 2) RO = RO - lenX * 2;
        if (RO > lenX) RO = RO - lenX;
        if (maxX < 0) LO = lenX + maxX;
        else if (maxX > lenX) LO = maxX - lenX;
        else LO = maxX;
        if (LO < lenX) LO = LO + 1;
        let guard = 0;
        while (ws.mdMap[LO] !== 0) {
          LO = LO + 1;
          if (LO > lenX) LO = 1;
          if (++guard > lenX + 8) break;
        }
        LO = LO - 1;
        if (LO < 1) LO = 1;
        BE = LO + 1 > lenX ? ws.xDiffPos[LO] : ws.xDiffPos[LO + 1];
        EN = ws.xDiffPos[RO];
      }
      const mcMaxY = maxY;
      maxX = pMaxX;
      if (LO < RO) {
        if (!(maxX >= LO && maxX <= RO)) {
          if (Math.abs(maxX - LO) > Math.abs(maxX - RO)) RO = maxX;
          else LO = maxX;
        }
      } else if (!(maxX > LO || maxX < RO)) {
        if (Math.abs(maxX - LO) > Math.abs(maxX - RO)) RO = maxX;
        else LO = maxX;
      }
      destroyPeaks(maxY, lenX, L, LO, RO, ws.smoothChi, ws.chiVals);
      ws.chiVals[maxz + maxY * SO] = 0;
      const ev = newXOverEvent(PROGRAM_MAXCHI);
      let cb = centreBP2(L, BE, EN, ws.xPosDiff, ws.xDiffPos, o.circularFlag, o.winSize / 2, lenX);
      const shrunk = shrinkFindDaughterPrgF34(
        cb.be,
        cb.en,
        seq1,
        seq2,
        seq3,
        mcMaxY,
        loHiFlag,
        aln.seqnum,
        L,
        ws.xPosDiff,
        ws.xDiffPos,
        ws.mdMap,
        lenX,
        o.circularFlag
      );
      if (shrunk.beginning !== cb.be || shrunk.ending !== cb.en) {
        cb = centreBP2(L, shrunk.beginning, shrunk.ending, ws.xPosDiff, ws.xDiffPos, o.circularFlag, o.winSize / 2, lenX);
      } else {
        cb = { ...cb, be: shrunk.beginning, en: shrunk.ending };
      }
      ev.beginning = cb.be;
      ev.ending = cb.en;
      ev.beginWarn = cb.bWarn;
      ev.endWarn = cb.eWarn;
      ev.probability = mpv;
      ev.lHolder = winWin * 2;
      ev.sbpFlag = 0;
      ev.beginP = 0;
      ev.endP = 0;
      ev.dHolder = 0;
      ev.triplet = [seq1, seq2, seq3];
      ev.maxY = mcMaxY;
      ev.loHiFlag = loHiFlag;
      ev.hWindowWidth = HW;
      ev.lenXoverSeq = lenX;
      if (o.longWindedFlag === 1 && (SEN > 1 || o.circularFlag === 0)) {
        const xpEN = Math.min(ws.xPosDiff[cb.en], lenX);
        const ENX0 = xpEN === lenX ? 1 : xpEN + 1;
        const ENX = ENX0 > lenX ? ENX0 - lenX : ENX0;
        const xpBE = ws.xPosDiff[cb.be];
        let BEX = xpBE === 1 || xpBE === 0 ? lenX : xpBE - 1;
        if (BEX < 1) BEX = lenX + BEX;
        let eWarn = cb.eWarn;
        let bWarn = cb.bWarn;
        if (SEN > 0) {
          const half = o.winSize / 2;
          if (eWarn === 0) {
            eWarn = checkEndsVB(
              half,
              lenX,
              1,
              o.circularFlag,
              seq1,
              seq2,
              seq3,
              cb.be,
              cb.en,
              aln.seqnum,
              ws.xPosDiff,
              ws.xDiffPos,
              o.circularFlag,
              o.missingData,
              L
            );
          }
          if (bWarn === 0) {
            bWarn = checkEndsVB(
              half,
              lenX,
              0,
              o.circularFlag,
              seq1,
              seq2,
              seq3,
              cb.be,
              cb.en,
              aln.seqnum,
              ws.xPosDiff,
              ws.xDiffPos,
              o.circularFlag,
              o.missingData,
              L
            );
          }
          ev.beginWarn = bWarn;
          ev.endWarn = eWarn;
        }
        const md = ws.mdMap;
        const eBad = md[ENX] === 1 || md[xpEN] === 1;
        const bBad = md[BEX] === 1 || md[xpBE] === 1;
        if (eBad && bBad || eWarn === 1 && bWarn === 1) ev.sbpFlag = 3;
        else if (eBad || eWarn === 1) ev.sbpFlag = 2;
        else if (bBad || bWarn === 1) ev.sbpFlag = 1;
      }
      const par = assignEventRoles(aln, [seq1, seq2, seq3], ev.beginning, ev.ending, {
        maxY: mcMaxY,
        longWindedFlag: o.longWindedFlag,
        tracker: o.roleTracker
      });
      ev.daughter = par.daughter;
      ev.majorP = par.majorP;
      ev.minorP = par.minorP;
      if (o.roleTracker) noteStoredRole(o.roleTracker, par.daughter, mpv);
      if (o.mcFlag === 2 && o.pvalCat && !o.pvalCat.finalized) recordPValCat(o.pvalCat, mpv);
      result.events.push(ev);
      result.found = true;
      wasteOfTime = 0;
      continue;
    }
    wasteOfTime++;
    if (wasteOfTime === 3) {
      clean(true);
      return result;
    }
    const dOk = destroyPeak(maxY, L, pMaxX, pMaxX, lenX, LOT, ws.smoothChi, ws.chiVals);
    ws.chiVals[maxz + maxY * SO] = 0;
    if (dOk === 0) {
      clean(true);
      return result;
    }
  }
  clean(true);
  return result;
}
function dedupeEvents(events, L) {
  const len = (e) => e.beginning <= e.ending ? e.ending - e.beginning + 1 : L - e.beginning + 1 + e.ending;
  const overlap = (a, b) => {
    const mark = (e, p) => e.beginning <= e.ending ? p >= e.beginning && p <= e.ending : p >= e.beginning || p <= e.ending;
    let n = 0;
    for (let p = 1; p <= L; p++) if (mark(a, p) && mark(b, p)) n++;
    return n;
  };
  const sorted = events.slice().sort((x, y) => x.probability - y.probability);
  const kept = [];
  for (const e of sorted) {
    let dup = false;
    for (const k of kept) {
      if (k.daughter !== e.daughter) continue;
      if (overlap(e, k) > 0.5 * Math.min(len(e), len(k))) {
        dup = true;
        break;
      }
    }
    if (!dup) kept.push(e);
  }
  return kept;
}

// src/engine/maxchiScreen.worker.mts
function makeAln(seqSab, nSeqs, length) {
  return {
    names: Array.from({ length: nSeqs }, (_, i) => `s${i}`),
    sequences: Array.from({ length: nSeqs }, () => ""),
    length,
    nSeqs,
    seqnum: new Int16Array(seqSab)
  };
}
function missingFrom(wd) {
  if (!wd.missingSab || wd.missingBytes <= 0) return null;
  return new Uint8Array(wd.missingSab, 0, wd.missingBytes);
}
function runScreen(wd) {
  const aln = makeAln(wd.seqSab, wd.nSeqs, wd.length);
  const ws = new ChiWorkspace(wd.length);
  const o = resolveScanOptions(
    aln,
    {
      winSize: wd.winSize,
      winFract: wd.winFract,
      proportionFlag: wd.proportionFlag,
      lowestProb: wd.lowestProb,
      mcCorrection: wd.mcCorrection,
      mcFlag: wd.mcFlag,
      circularFlag: wd.circularFlag,
      longWindedFlag: 0,
      earlyBale: 1,
      sEventNumber: wd.sEventNumber ?? 0,
      missingData: missingFrom(wd),
      ucThresh: defaultUcThresh(wd.lowestProb, wd.mcFlag, wd.mcCorrection)
    },
    70
  );
  const flags = new Uint8Array(wd.flagsSab);
  const bqpv = wd.bqpvSab ? new Float64Array(wd.bqpvSab) : null;
  const state = new Int32Array(wd.stateSab);
  try {
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = wd.flatTrips[t * 3];
      const b = wd.flatTrips[t * 3 + 1];
      const c = wd.flatTrips[t * 3 + 2];
      const r = scanTripletMC(aln, ws, { ...o, earlyBale: 1 }, a, b, c, "screen");
      flags[t] = r.found ? 1 : 0;
      if (bqpv) bqpv[t] = r.bqpv;
    }
  } catch {
    Atomics.store(state, 1, 1);
  }
  Atomics.add(state, 0, 1);
  Atomics.notify(state, 0);
}
function runEvents(wd) {
  const aln = makeAln(wd.seqSab, wd.nSeqs, wd.length);
  const ws = new ChiWorkspace(wd.length);
  const o = resolveScanOptions(
    aln,
    {
      winSize: wd.winSize,
      winFract: wd.winFract,
      proportionFlag: wd.proportionFlag,
      lowestProb: wd.lowestProb,
      mcCorrection: wd.mcCorrection,
      mcFlag: wd.mcFlag,
      circularFlag: wd.circularFlag,
      longWindedFlag: 1,
      earlyBale: 0,
      sEventNumber: wd.sEventNumber ?? 0,
      missingData: missingFrom(wd),
      ucThresh: defaultUcThresh(wd.lowestProb, wd.mcFlag, wd.mcCorrection)
    },
    70
  );
  const flat = new Int32Array(wd.tripsSab);
  const hits = new Float64Array(wd.hitsSab);
  const state = new Int32Array(wd.stateSab);
  const maxHits = wd.maxHits || 8;
  try {
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = flat[t * 3];
      const b = flat[t * 3 + 1];
      const c = flat[t * 3 + 2];
      const r = scanTripletMC(aln, ws, { ...o, earlyBale: 0, roleTracker: null }, a, b, c, "events");
      const evs = dedupeEvents(r.events, wd.length);
      const base = t * wd.hitStride;
      const n = Math.min(maxHits, evs.length);
      hits[base] = n;
      for (let h = 0; h < n; h++) {
        const e = evs[h];
        const off = base + 1 + h * 12;
        hits[off] = e.beginning;
        hits[off + 1] = e.ending;
        hits[off + 2] = e.probability;
        hits[off + 3] = e.maxY;
        hits[off + 4] = e.permPVal;
        hits[off + 5] = e.sbpFlag;
        hits[off + 6] = e.beginWarn;
        hits[off + 7] = e.endWarn;
        hits[off + 8] = e.loHiFlag;
        hits[off + 9] = e.lenXoverSeq;
        hits[off + 10] = e.lHolder;
        hits[off + 11] = e.hWindowWidth;
      }
    }
  } catch {
    Atomics.store(state, 1, 1);
  }
  Atomics.add(state, 0, 1);
  Atomics.notify(state, 0);
}
if (parentPort) {
  parentPort.on("message", (msg) => {
    if (!msg) return;
    if (msg.type === "job") runScreen(msg);
    else if (msg.type === "events") runEvents(msg);
  });
}
var boot = workerData;
if (boot && boot.type === "boot" && boot.readySab) {
  Atomics.add(new Int32Array(boot.readySab), 0, 1);
  Atomics.notify(new Int32Array(boot.readySab), 0);
}
