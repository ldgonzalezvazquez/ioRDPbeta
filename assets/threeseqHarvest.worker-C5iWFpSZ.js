// src/engine/threeseqHarvest.worker.mts
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

// src/engine/distAccel.ts
var COMPRESS14_STRIDE = 626;
function baseCode(seqnum) {
  return NUC_MAT[seqnum & 255] ?? 0;
}
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
function packSeq14(seqnum, nSeqs, length, startPos = 1, endPos = length) {
  const nSites = endPos - startPos + 1;
  const packs = Math.ceil(nSites / 4);
  const packStride = packs;
  const codes = new Int16Array(nSeqs * packs);
  for (let s = 0; s < nSeqs; s++) {
    const so = s * (length + 1);
    const co = s * packs;
    let pi = 0;
    for (let p = startPos; p <= endPos; p += 4) {
      let c0 = 0;
      let c1 = 0;
      let c2 = 0;
      let c3 = 0;
      c0 = baseCode(seqnum[p + so]);
      if (p + 1 <= endPos) c1 = baseCode(seqnum[p + 1 + so]);
      if (p + 2 <= endPos) c2 = baseCode(seqnum[p + 2 + so]);
      if (p + 3 <= endPos) c3 = baseCode(seqnum[p + 3 + so]);
      codes[co + pi] = c0 + c1 * 5 + c2 * 25 + c3 * 125;
      pi++;
    }
  }
  return { codes, packs, packStride };
}
function superDist14Pair(codes, packs, seqA, seqB) {
  const oa = seqA * packs;
  const ob = seqB * packs;
  const validT = TABLES.valid;
  const diffsT = TABLES.diffs;
  let v = 0;
  let d = 0;
  for (let z = 0; z < packs; z++) {
    const idx = codes[oa + z] + codes[ob + z] * COMPRESS14_STRIDE;
    v += validT[idx];
    d += diffsT[idx];
  }
  return { valid: v, diffs: d };
}
var packCacheSn = null;
var packCacheN = 0;
var packCacheL = 0;
var packCacheFinger = 0;
var packCacheCodes = null;
var packCachePacks = 0;
function packFingerprint(seqnum, nSeqs, length) {
  void seqnum;
  return nSeqs * 131 + length | 0;
}
function packSeq14Cached(seqnum, nSeqs, length) {
  const finger = packFingerprint(seqnum, nSeqs, length);
  if (packCacheSn === seqnum && packCacheN === nSeqs && packCacheL === length && packCacheFinger === finger && packCacheCodes) {
    return { codes: packCacheCodes, packs: packCachePacks };
  }
  const packed = packSeq14(seqnum, nSeqs, length, 1, length);
  packCacheSn = seqnum;
  packCacheN = nSeqs;
  packCacheL = length;
  packCacheFinger = finger;
  packCacheCodes = packed.codes;
  packCachePacks = packed.packs;
  return { codes: packed.codes, packs: packed.packs };
}

// src/engine/seqnum.ts
function calcDistances(aln, minSeqSize = 0, startPos = 1, endPos = aln.length) {
  const n = aln.nSeqs;
  const L = aln.length;
  const distance = new Float32Array(n * n);
  const permValid = new Float32Array(n * n);
  const permDiffs = new Float32Array(n * n);
  let maxDiffs = 0;
  const usePack = startPos === 1 && endPos === L && L >= 4;
  if (usePack) {
    const { codes, packs } = packSeq14Cached(aln.seqnum, n, L);
    for (let x = 0; x < n; x++) {
      for (let y = x + 1; y < n; y++) {
        const { valid, diffs } = superDist14Pair(codes, packs, x, y);
        const sim = valid > 0 && valid >= minSeqSize ? (valid - diffs) / valid : 0;
        distance[x + n * y] = sim;
        distance[y + n * x] = sim;
        permValid[x + n * y] = valid;
        permValid[y + n * x] = valid;
        permDiffs[x + n * y] = diffs;
        permDiffs[y + n * x] = diffs;
        if (diffs > maxDiffs) maxDiffs = diffs;
      }
      distance[x + n * x] = 1;
      permValid[x + n * x] = L;
    }
    return { n, distance, permValid, permDiffs, maxDiffs };
  }
  const stride = L + 1;
  const sn = aln.seqnum;
  for (let x = 0; x < n; x++) {
    const ox = x * stride;
    for (let y = x + 1; y < n; y++) {
      const oy = y * stride;
      let valid = 0;
      let diffs = 0;
      for (let p = startPos; p <= endPos; p++) {
        const a = sn[p + ox];
        if (a === GAP) continue;
        const b = sn[p + oy];
        if (b === GAP) continue;
        valid++;
        if (a !== b) diffs++;
      }
      const d = valid > 0 && valid >= minSeqSize ? (valid - diffs) / valid : 0;
      distance[x + n * y] = d;
      distance[y + n * x] = d;
      permValid[x + n * y] = valid;
      permValid[y + n * x] = valid;
      permDiffs[x + n * y] = diffs;
      permDiffs[y + n * x] = diffs;
      if (diffs > maxDiffs) maxDiffs = diffs;
    }
    distance[x + n * x] = 1;
    permValid[x + n * x] = L;
  }
  return { n, distance, permValid, permDiffs, maxDiffs };
}

// src/engine/settings.ts
var PROGRAM_RDP = 0;
var PROGRAM_GENECONV = 1;
var PROGRAM_BOOTSCAN = 2;
var PROGRAM_SISCAN = 5;
var PROGRAM_LARD = 7;
var PROGRAM_3SEQ = 8;
var PROGRAM_TOPAL = 9;
function defaultSettings() {
  return {
    methods: {
      rdp: true,
      geneconv: true,
      bootscan: false,
      maxchi: true,
      chimaera: false,
      siscan: false,
      threeSeq: false,
      lard: false,
      topal: false
    },
    // Module5 SetDef: DoScans(1,2)=1 Bootscan, DoScans(1,5)=1 SiScan; DoScans(1,4)=0 Chimaera
    confirmMethods: { bootscan: true, siscan: true, chimaera: false },
    rdp: {
      lowestProb: 0.05,
      xOverWindowX: 30,
      mcFlag: 0,
      mcCorrection: 0,
      circularFlag: 1,
      minSeqSize: 0,
      minPairDiffs: 2,
      doAllFlag: 0
    },
    threeSeq: {
      lowestProb: 0.05,
      mcFlag: 0,
      mcCorrection: 0,
      minSeqSize: 0,
      tableMax: 0,
      /**
       * Desktop 3seqTable grows with MaxPermDists; browser default 80 (was 60).
       * Lazy Boni recursion memoises YTable; V8 Map overflows around max≳100–120 on large
       * difference counts — prefer IndexedDB `prefillExactTable` for denser caches up to ~100.
       * Beyond tableCap → SiegmundDiscrete.
       */
      tableCap: 80,
      minInformativeSites: 3
    },
    geneconv: {
      indelFlag: 0,
      missmatchPen: 1,
      maxOverlapFrags: 1,
      minFragLen: 1,
      minPolyInFrag: 2,
      minPairScore: 2,
      longWindedFlag: 1
    },
    bootscan: {
      stepWin: 200,
      stepSize: 20,
      bootReps: 100,
      cutOff: 0.7,
      pValFlag: 1,
      rndNumSeed: 3,
      subModelFlag: 0,
      typeFlag: 0,
      ttRatio: 2,
      coeffVar: 1,
      freqFlag: 0,
      freqA: 0.25,
      freqC: 0.25,
      freqG: 0.25,
      freqT: 0.25
    },
    siscan: {
      winLen: 200,
      step: 20,
      numPerms: 1e3,
      numPerms2: 100,
      fastFlag: 1,
      gapFlag: 0,
      varPFlag: 2,
      outlierFlag: 1,
      rndNumSeed: 3
    },
    maxchi: { winSize: 70, winFract: 0.1, proportionFlag: 0 },
    chimaera: { winSize: 60, winFract: 0.1, proportionFlag: 0 },
    // DoRDP (Module3.bas): after the exploratory pass, extract best→worst unique events
    // one at a time (mask / SeqEdits → REDOREDO). Default ON — without this the browser
    // stops after the first merged SuperEvent and looks "incomplete" vs desktop RDP5.
    // ForcePhylE = 1 desktop SetDef — reject candidates without topo change region↔flank.
    redo: { enabled: 1, maxCycles: 50, phylogeneticCheck: 1 },
    // PolishBP / BenHMM only on the unique-event candidate inside DoRDP cycles (redo.ts).
    // hmmCycles 8 ≈ desktop speed sweet-spot for browser; Options still allow 20 (full PolishBP).
    polish: { enabled: 1, repos: 0, hmmCycles: 8 },
    lard: { step: 5, minRegion: 20, model: 0, ttRatio: 2 },
    topal: { winLen: 200, step: 10, smooth: 5, zThresh: 2.5 },
    schema: { schemaDistCO: 4.5, permNo: 200, frame: 0 },
    plots: {
      dpWindow: 200,
      dpStep: 20,
      dpModelFlag: 1,
      matWinSize: 200,
      matPermNo: 1e3,
      recRateWindow: 200,
      recRateStep: 20,
      typeSeqIndex: 0
    },
    general: {
      showPlotFlag: 2,
      allowConflict: 1,
      realignFlag: 1,
      conservativeGroup: 0,
      gPerms: 0,
      permTypeFlag: 0
    },
    matrixDraw: { colourFlag: 1, binaryThreshold: 1 },
    ldhat: { startRho: 30, blockPen: 10 },
    treesOpt: { mlModel: 1, ttRatio: 2, nniRounds: 5, sprMoves: 8, bayesGens: 1e4, bayesChains: 4 },
    phylpro: { winLen: 60, perms: 200, seed: 3, stripGaps: 0, incSelf: 0 }
  };
}
function minSeqSizeFor(alignmentLength) {
  let m = 50;
  if (alignmentLength / 100 > m) m = Math.trunc(alignmentLength / 100);
  return m;
}
function mcCorrectionFor(nSeqs) {
  if (nSeqs < 3) return 1;
  return nSeqs * (nSeqs - 1) * (nSeqs - 2) / 6;
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

// src/engine/chi.ts
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
function buildBreakpointMaps(aln, seq1, seq2, seq3) {
  const L = aln.length;
  const xDiffPos = new Int32Array(L + 205);
  const xPosDiff = new Int32Array(L + 205);
  const lenXoverSeq = findSubSeqCP(L + 1, seq1, seq2, seq3, aln.seqnum, xDiffPos, xPosDiff);
  xPosDiff[L] = lenXoverSeq;
  return { xPosDiff, xDiffPos, lenXoverSeq };
}
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
function goRightP(seq1, seq2, seq3, circularFlag, startPos, LS, missingData, ubmd = LS) {
  const stride = ubmd + 1;
  let Z = startPos;
  let cycleX = 0;
  for (let X = 1; X <= LS; X++) {
    Z = Z + 1;
    if (Z > LS) {
      if (circularFlag === 0) {
        Z = 1;
        break;
      }
      Z = 1;
      cycleX++;
      if (cycleX === 3) break;
    }
    if (missingData[Z + seq1 * stride] === 0 && missingData[Z + seq2 * stride] === 0 && missingData[Z + seq3 * stride] === 0) {
      break;
    }
  }
  return Z;
}
function goLeftP(seq1, seq2, seq3, circularFlag, startPos, LS, missingData, ubmd = LS) {
  const stride = ubmd + 1;
  let Z = startPos;
  let cycleX = 0;
  for (let X = 1; X <= LS; X++) {
    Z = Z - 1;
    if (Z < 1) {
      if (circularFlag === 0) {
        Z = LS;
        break;
      }
      Z = LS;
      cycleX++;
      if (cycleX === 3) break;
    }
    if (missingData[Z + seq1 * stride] === 0 && missingData[Z + seq2 * stride] === 0 && missingData[Z + seq3 * stride] === 0) {
      break;
    }
  }
  return Z;
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
function centreBreakpoints(aln, event, maps, opts = {}) {
  const circularFlag = opts.circularFlag ?? 0;
  const LSS = opts.lss ?? Math.max(1, Math.floor((event.hWindowWidth || 20) / 2) || 10);
  const [s1, s2, s3] = event.triplet;
  const m = maps && maps.lenXoverSeq > 0 ? maps : buildBreakpointMaps(aln, s1, s2, s3);
  if (m.lenXoverSeq < 2) {
    return { beginning: event.beginning, ending: event.ending, beginWarn: event.beginWarn, endWarn: event.endWarn, sbpFlag: event.sbpFlag };
  }
  m.xPosDiff[aln.length] = m.lenXoverSeq;
  const cb = centreBP2(aln.length, event.beginning, event.ending, m.xPosDiff, m.xDiffPos, circularFlag, LSS, m.lenXoverSeq);
  let be = cb.be;
  let en = cb.en;
  let bWarn = cb.bWarn;
  let eWarn = cb.eWarn;
  const md = opts.missingData ?? null;
  const sen = opts.sEventNumber ?? 0;
  if (sen > 0 && md) {
    const stride = aln.length + 1;
    if (md[be + s1 * stride] === 1 || md[be + s2 * stride] === 1 || md[be + s3 * stride] === 1) {
      bWarn = 1;
      be = goRightP(s1, s2, s3, circularFlag, be, aln.length, md);
    }
    if (md[en + s1 * stride] === 1 || md[en + s2 * stride] === 1 || md[en + s3 * stride] === 1) {
      eWarn = 1;
      en = goLeftP(s1, s2, s3, circularFlag, en, aln.length, md);
    }
  }
  if (opts.checkEnds !== false) {
    const obe = opts.obe ?? 0;
    const oen = opts.oen ?? 0;
    if (eWarn === 0) {
      const w = checkEndsVB(LSS, m.lenXoverSeq, 1, circularFlag, s1, s2, s3, be, en, aln.seqnum, m.xPosDiff, m.xDiffPos, circularFlag, md, aln.length, obe, oen);
      if (w) eWarn = 1;
    }
    if (bWarn === 0) {
      const w = checkEndsVB(LSS, m.lenXoverSeq, 0, circularFlag, s1, s2, s3, be, en, aln.seqnum, m.xPosDiff, m.xDiffPos, circularFlag, md, aln.length, obe, oen);
      if (w) bWarn = 1;
    }
  }
  const sbpFlag = (bWarn ? 1 : 0) + (eWarn ? 2 : 0);
  return { beginning: be, ending: en, beginWarn: bWarn, endWarn: eWarn, sbpFlag };
}

// src/engine/maxchiParallel.ts
import { createRequire as createRequire2 } from "node:module";

// src/engine/parallelPool.ts
import { createRequire } from "node:module";
var req = createRequire(import.meta.url);

// src/engine/maxchiParallel.ts
var req2 = createRequire2(import.meta.url);

// src/engine/maxchi.ts
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

// src/engine/threeseq.ts
function createExactTable(maxPermDists, seed) {
  const B = maxPermDists + 3;
  const y = /* @__PURE__ */ new Map();
  const x = /* @__PURE__ */ new Map();
  if (seed && seed.max === maxPermDists) {
    for (const [nM, nN, nK, v] of seed.cells) {
      x.set((nM * B + nN) * B + nK, v);
    }
  }
  const get3SeqPvalC = (m, n, k, j) => {
    const key = ((m * B + n) * B + k) * B + j;
    const cached2 = y.get(key);
    if (cached2 !== void 0) return cached2;
    let d;
    if (j > k) return 0;
    else if (k > n || k < n - m || j > n || j < n - m) return 0;
    else if (n === 0) return k === 0 && j === 0 ? 1 : 0;
    else if (m === 0) return k === n && j === n ? 1 : 0;
    else if (k === 0 && j === 0) return n === 0 ? 1 : 0;
    if (j === 0) {
      d = m / (n + m) * (get3SeqPvalC(m - 1, n, k, 1) + get3SeqPvalC(m - 1, n, k, 0));
    } else if (k === j) {
      d = n / (n + m) * (get3SeqPvalC(m, n - 1, j - 1, j - 1) + get3SeqPvalC(m, n - 1, j, j - 1));
    } else {
      d = m / (n + m) * get3SeqPvalC(m - 1, n, k, j + 1) + n / (n + m) * get3SeqPvalC(m, n - 1, k, j - 1);
    }
    y.set(key, d);
    return d;
  };
  const seq3PVals = (nM, nN, nK) => {
    let dPValue = 0;
    if (nK === 0 && nN > 0) dPValue = 1;
    else if (nK === 0 && nN === 0) dPValue = 1;
    else if (nM === 0 && nK === nN) dPValue = 1;
    else if (nM === 0 && nK !== nN) dPValue = 1;
    else if (nN === 0 && nK > 0) dPValue = 1;
    else if (nM < 0 || nN < 0 || nK < 0) dPValue = 1;
    else {
      for (let K = nK; K <= nN; K++) {
        if (K <= nN && K >= nN - nM) {
          for (let J = 0; J <= K; J++) dPValue += get3SeqPvalC(nM, nN, K, J);
        }
      }
    }
    return dPValue;
  };
  const table = {
    max: maxPermDists,
    xTable(nM, nN, nK) {
      const key = (nM * B + nN) * B + nK;
      const c = x.get(key);
      if (c !== void 0) return c;
      const v = seq3PVals(nM, nN, nK);
      x.set(key, v);
      return v;
    },
    size: () => x.size,
    snapshot() {
      const cells = [];
      for (const [key, v] of x) {
        const nK = key % B;
        const t = key / B | 0;
        const nN = t % B;
        const nM = t / B | 0;
        cells.push([nM, nN, nK, v]);
      }
      return { max: maxPermDists, cells };
    }
  };
  return table;
}
function approxNormPDF(x) {
  const pi = 3.14159265359;
  return 1 / Math.sqrt(2 * pi) * Math.exp(-0.5 * x * x);
}
function approxNormCDF(x) {
  const b1 = 0.31938153;
  const b2 = -0.356563782;
  const b3 = 1.781477937;
  const b4 = -1.821255978;
  const b5 = 1.330274429;
  const P = 0.2316419;
  const C = 0.39894228;
  if (x >= 0) {
    const T = 1 / (1 + P * x);
    return 1 - C * Math.exp(-x * x / 2) * T * (T * (T * (T * (T * b5 + b4) + b3) + b2) + b1);
  }
  return 1 - approxNormCDF(-x);
}
function approxNu(x) {
  if (x > 0) {
    return (approxNormCDF(x / 2) - 0.5) * 2 / x / (approxNormPDF(x / 2) + x * approxNormCDF(x / 2) / 2);
  }
  return 0;
}
function siegmundDiscrete(M, n, k) {
  const MM = M + n;
  if (MM === 0) return -1;
  const b = k - 0.5;
  const xi = n - M;
  let h1 = -2 * b * (b - xi) / MM;
  if (h1 > 700) h1 = 700;
  let P1 = Math.exp(h1);
  if (P1 > 1e200) P1 = 1e200;
  const P2 = P1 * (2 * (2 * b - xi) * (b - xi) / MM + 1);
  const AN = 2 * (2 * b - xi) / MM;
  let NU = 0;
  if (AN !== 0) NU = approxNu(AN);
  let P3 = NU * NU * P2;
  if (P3 < 0 && P3 < -1) P3 = -1;
  return 1 - Math.exp(-P3);
}
function getTSPVal(table, nMi, NNi, nKi) {
  const T = table.max + 1;
  let nM = nMi;
  let NN = NNi;
  let nK = nKi;
  const onM = nMi;
  const onN = NNi;
  let PVM;
  let WF;
  let dPValue;
  if (nM >= T - 1 || NN >= T - 1 || nK >= T - 1) {
    dPValue = siegmundDiscrete(nM, NN, nK);
    WF = 1;
    if (dPValue >= 1 || dPValue <= 0) {
      if (nM >= NN && nM >= nK) PVM = nM / (T - 2);
      else if (NN >= nM && NN >= nK) PVM = NN / (T - 2);
      else PVM = nK / (T - 2);
      nM = Math.floor(nM / PVM);
      NN = Math.floor(NN / PVM);
      nK = Math.floor(nK / PVM);
      if (nM > 0) {
        PVM = onM / nM;
      } else if (NN > 0) {
        PVM = onN / NN;
      }
      WF = 1;
    } else {
      return [dPValue, WF];
    }
  } else {
    WF = 0;
    PVM = 1;
  }
  dPValue = nK >= 0 ? table.xTable(nM, NN, nK) : table.xTable(nM, NN, 0);
  const odPValue = dPValue;
  if (PVM > 1) dPValue = Math.pow(dPValue, PVM);
  if (dPValue === 0 && odPValue > 0) dPValue = 1e-300;
  return [dPValue, WF];
}
function findSubSeqTS(sn, ls, seq1, seq2, seq3, ws) {
  let currentHeight = 0;
  let maxDescentSeen = 0;
  let maxAscentSeen = 0;
  let Y = 0;
  let nM = 0;
  let nN = 0;
  let maxSeen = 0;
  let minSeen = 0;
  const os1 = (ls + 1) * seq1;
  const os2 = (ls + 1) * seq2;
  const os3 = (ls + 1) * seq3;
  let BE = 0;
  let EN = 0;
  let BE2 = 0;
  let EN2 = 0;
  ws.xposdiff.fill(0);
  for (let X = 0; X <= ls; X++) {
    const s1 = sn[X + os1];
    const s2 = sn[X + os2];
    if (s2 !== s1) {
      if (s1 !== GAP) {
        if (s2 !== GAP) {
          const s3 = sn[X + os3];
          if (s3 !== GAP) {
            if (s3 === s1) {
              currentHeight++;
              ws.height[Y] = currentHeight;
              ws.xdiffpos[Y] = X;
              ws.xposdiff[X] = Y;
              if (currentHeight > maxSeen) {
                maxSeen = currentHeight;
                BE = X;
              }
              if (currentHeight - minSeen > maxAscentSeen) {
                maxAscentSeen = currentHeight - minSeen;
                EN2 = X;
              }
              nM++;
              Y++;
            } else if (s3 === s2) {
              currentHeight--;
              ws.height[Y] = currentHeight;
              ws.xdiffpos[Y] = X;
              ws.xposdiff[X] = Y;
              nN++;
              if (maxSeen - currentHeight > maxDescentSeen) {
                maxDescentSeen = maxSeen - currentHeight;
                EN = X;
              }
              if (currentHeight < minSeen) {
                minSeen = currentHeight;
                BE2 = X;
              }
              Y++;
            }
          }
        }
      }
    }
  }
  return { len: Y - 1, be: BE, en: EN, be2: BE2, en2: EN2, nM, nN, nK: maxDescentSeen, nL: maxAscentSeen };
}
function subPVal(table, nM, nN, lenXoverSeq, SP, EP, xPosDiff, height) {
  if (lenXoverSeq === 0) return 10;
  let x = xPosDiff[SP] > 0 ? xPosDiff[SP] - 1 : lenXoverSeq;
  let maxSeen = -1e3;
  let minSeen = 1e3;
  let EPX = xPosDiff[EP] + 1 > lenXoverSeq ? lenXoverSeq : xPosDiff[EP] + 1;
  if (x === EPX) EPX = EPX - 1;
  if (EPX === 0) EPX = lenXoverSeq;
  let ModX = 0;
  if (EPX < 0) EPX = 0;
  if (lenXoverSeq > 0) {
    while (x !== EPX) {
      if (x < 0) x = lenXoverSeq + x;
      if (x > lenXoverSeq) {
        ModX = height[lenXoverSeq];
        x = x - lenXoverSeq - 1;
      }
      if (x < 0) return 0;
      const h = height[x] + ModX;
      if (maxSeen < h) maxSeen = h;
      if (minSeen > h) minSeen = h;
      if (x === EPX) break;
      x = x + 1;
    }
  }
  const nK = maxSeen - minSeen;
  const [dPValue] = getTSPVal(table, nM, nN, nK);
  return dPValue;
}
function checkSplit3Seq(state, nM, nN, lenXoverSeq, seq1, seq2, seq3, ls, missingData, height, xPosDiff, table) {
  const stride = ls + 1;
  const md = (pos, seq) => missingData[pos + seq * stride] ?? 0;
  let tBE = state.be;
  let tEN = state.en;
  let dPValue = state.dPValue;
  let x = state.be - 1;
  while (x !== state.en) {
    if (x > ls) {
      x = 1;
      if (state.en === 0 || state.en === 1) break;
    }
    if (x < 0) x = ls;
    if (md(x, seq1) === 1 || md(x, seq2) === 1 || md(x, seq3) === 1) {
      dPValue = 1;
      const tdPValue = subPVal(table, nM, nN, lenXoverSeq, state.be, x, xPosDiff, height);
      if (tdPValue < dPValue) {
        dPValue = tdPValue;
        tBE = state.be;
        tEN = x - 1;
      }
      break;
    }
    if (x === state.en) break;
    x = x + 1;
    if (x === state.en) break;
  }
  if (x !== state.en) {
    x = state.en + 1;
    while (x !== state.be) {
      if (x < 0) x = ls;
      if (x > ls) x = 1;
      if (md(x, seq1) === 1 || md(x, seq2) === 1 || md(x, seq3) === 1) {
        const tdPValue = subPVal(table, nM, nN, lenXoverSeq, x, state.en, xPosDiff, height);
        if (tdPValue < dPValue) {
          dPValue = tdPValue;
          tBE = x + 1;
          tEN = state.en;
        }
        break;
      }
      if (x === state.be) break;
      x = x - 1;
    }
  }
  state.en = tEN;
  state.be = tBE;
  state.dPValue = dPValue;
}
function checkwrapC(ls, lenXO, negMod, circular, nKin, beIn, enIn, ws) {
  let BE = beIn;
  let EN = enIn;
  let nK = nKin;
  const { xdiffpos: XDiffPos, xposdiff: XPosDiff, height } = ws;
  if (BE === 0) BE = XDiffPos[0];
  let maxSeen = height[XPosDiff[BE]] * negMod;
  const tempAscent = height[lenXO] * negMod;
  if (BE < EN) {
    const TBE = XPosDiff[BE];
    for (let X = 0; X <= TBE; X++) {
      const h1 = tempAscent + height[X] * negMod;
      if (h1 > maxSeen) {
        maxSeen = h1;
        BE = XDiffPos[X];
      }
      if (maxSeen - h1 > nK) {
        nK = maxSeen - h1;
        EN = XDiffPos[X];
      }
    }
  } else {
    const TBE = XPosDiff[EN];
    for (let X = 0; X <= TBE; X++) {
      const h1 = tempAscent + height[X] * negMod;
      if (h1 > maxSeen) {
        maxSeen = h1;
        BE = XDiffPos[X];
      }
      if (maxSeen - h1 > nK) {
        nK = maxSeen - h1;
        EN = XDiffPos[X];
      }
    }
  }
  if (XPosDiff[BE] < lenXO) BE = XDiffPos[XPosDiff[BE] + 1];
  else BE = XDiffPos[0];
  if (circular === 0) {
    if (BE > EN) {
      let TE;
      if (XPosDiff[EN] < lenXO) TE = XDiffPos[XPosDiff[EN] + 1];
      else TE = 1;
      if (XPosDiff[BE] > 0) EN = XDiffPos[XPosDiff[BE] - 1];
      else EN = ls;
      BE = TE;
    }
  }
  return [nK, BE, EN];
}
function tsXOver(c, seq1, seq2, seq3) {
  const out = [];
  const w = findSubSeqTS(c.sn, c.ls, seq1, seq2, seq3, c.ws);
  const lenXO = w.len;
  if (lenXO < c.minSites) return out;
  let { be: BE, en: EN, be2: BE2, en2: EN2, nM, nN: NN, nK, nL: NL } = w;
  let [dPValue, WF] = getTSPVal(c.table, nM, NN, nK);
  let [dPValue2] = getTSPVal(c.table, NN, nM, NL);
  [nK, BE, EN] = checkwrapC(c.ls, lenXO, 1, c.circular, nK, BE, EN, c.ws);
  [NL, BE2, EN2] = checkwrapC(c.ls, lenXO, -1, c.circular, NL, BE2, EN2, c.ws);
  let multNeg = 0;
  if (dPValue2 < dPValue) {
    [BE, BE2] = [BE2, BE];
    [EN, EN2] = [EN2, EN];
    [nM, NN] = [NN, nM];
    [nK, NL] = [NL, nK];
    const t = dPValue;
    dPValue = dPValue2;
    dPValue2 = t;
    multNeg = 1;
  }
  if (NN > 0 && nK === 1) return out;
  if (NN - nM === nK) return out;
  const odPValue = dPValue;
  let xpValue;
  if (c.mcFlag === 0) {
    xpValue = dPValue * c.mc;
    if (dPValue >= 1 || xpValue >= 1) {
      dPValue = 1;
    } else if (dPValue > 1e-15) {
      dPValue = 1 - Math.pow(1 - dPValue, c.mc);
    } else {
      dPValue = xpValue;
    }
  } else {
    xpValue = dPValue;
  }
  const significant = () => (dPValue < 1 && dPValue <= c.lowestProb || dPValue === 1 && xpValue < c.lowestProb) && xpValue > 0;
  if (!significant()) return out;
  if (dPValue === 0) dPValue = xpValue;
  if (!significant()) return out;
  let odSplit = odPValue;
  if (c.sEventNumber > 0 && c.missingData) {
    const height = c.ws.height;
    if (multNeg === 1) {
      for (let i = 0; i <= lenXO; i++) height[i] = -height[i];
    }
    const st = { be: BE, en: EN, dPValue: odSplit };
    checkSplit3Seq(
      st,
      nM,
      NN,
      lenXO,
      seq1,
      seq2,
      seq3,
      c.ls,
      c.missingData,
      height,
      c.ws.xposdiff,
      c.table
    );
    BE = st.be;
    EN = st.en;
    odSplit = st.dPValue;
    if (odSplit > dPValue2 || c.findAll) {
      for (let i = 0; i <= lenXO; i++) height[i] = -height[i];
      const st2 = { be: BE2, en: EN2, dPValue: dPValue2 };
      checkSplit3Seq(
        st2,
        NN,
        nM,
        lenXO,
        seq1,
        seq2,
        seq3,
        c.ls,
        c.missingData,
        height,
        c.ws.xposdiff,
        c.table
      );
      if (!c.findAll && odSplit > st2.dPValue) {
        BE = st2.be;
        EN = st2.en;
        odSplit = st2.dPValue;
        multNeg = 1 - multNeg;
        [nM, NN] = [NN, nM];
      }
    }
  }
  const { xposdiff, xdiffpos } = c.ws;
  const bi = xposdiff[BE];
  const ei = xposdiff[EN];
  let inside1 = 0;
  let inside2 = 0;
  {
    const os1 = (c.ls + 1) * seq1;
    const os2 = (c.ls + 1) * seq2;
    const os3 = (c.ls + 1) * seq3;
    const visit = (idx) => {
      const pos = xdiffpos[idx];
      const s3 = c.sn[pos + os3];
      if (s3 === c.sn[pos + os1]) inside1++;
      else if (s3 === c.sn[pos + os2]) inside2++;
    };
    if (bi <= ei) for (let i = bi; i <= ei; i++) visit(i);
    else {
      for (let i = bi; i <= lenXO; i++) visit(i);
      for (let i = 0; i <= ei; i++) visit(i);
    }
  }
  const sI = [0, 0];
  const sO = [0, 0];
  {
    const os1 = (c.ls + 1) * seq1;
    const os2 = (c.ls + 1) * seq2;
    const os3 = (c.ls + 1) * seq3;
    const tally = (arr, x) => {
      const pos = xdiffpos[x];
      const s3 = c.sn[pos + os3];
      if (s3 === c.sn[pos + os1]) arr[0]++;
      else if (s3 === c.sn[pos + os2]) arr[1]++;
    };
    if (bi < ei) {
      for (let x = 1; x <= bi - 1; x++) tally(sO, x);
      for (let x = bi; x <= ei; x++) tally(sI, x);
      for (let x = ei + 1; x <= lenXO; x++) tally(sO, x);
    } else {
      for (let x = 1; x <= ei; x++) tally(sI, x);
      for (let x = ei + 1; x <= bi - 1; x++) tally(sO, x);
      for (let x = bi; x <= lenXO; x++) tally(sI, x);
    }
  }
  let TCC = 0;
  if (sI[0] > sI[1] && sO[0] > sO[1]) TCC = 1;
  else if (sI[1] > sI[0] && sO[1] > sO[0]) TCC = 1;
  const geomMinor = inside1 >= inside2 ? seq1 : seq2;
  const geomMajor = geomMinor === seq1 ? seq2 : seq1;
  let daughter = seq3;
  let minor = geomMinor;
  let major = geomMajor;
  if (c.longWindedFlag === 1 && c.roleTracker) {
    const par = assignEventRoles(c.aln, [seq1, seq2, seq3], BE, EN, {
      longWindedFlag: 1,
      tracker: c.roleTracker
    });
    daughter = par.daughter;
    minor = par.minorP;
    major = par.majorP;
  }
  const e = newXOverEvent(PROGRAM_3SEQ);
  e.daughter = daughter;
  e.minorP = minor;
  e.majorP = major;
  e.sbpFlag = 0;
  e.outsideFlag = TCC;
  e.beginning = BE;
  e.ending = EN;
  e.probability = dPValue;
  e.permPVal = WF >= 0 ? WF : 0;
  e.beginP = 0;
  e.endP = 0;
  e.dHolder = seq3;
  e.lHolder = 0;
  e.triplet = [seq1, seq2, seq3];
  e.lenXoverSeq = lenXO;
  e.rawP = odSplit;
  e.uncappedCorrectedP = xpValue;
  e.nM = nM;
  e.nN = NN;
  e.nK = nK;
  e.approximated = WF;
  e.swapped = multNeg;
  if (lenXO >= 2) {
    const maps = {
      xPosDiff: c.ws.xposdiff,
      xDiffPos: c.ws.xdiffpos,
      lenXoverSeq: lenXO
    };
    const cb = centreBreakpoints(c.aln, e, maps, {
      circularFlag: c.circular,
      lss: 10,
      missingData: c.missingData,
      sEventNumber: c.sEventNumber
    });
    e.beginning = cb.beginning;
    e.ending = cb.ending;
    e.beginWarn = cb.beginWarn;
    e.endWarn = cb.endWarn;
    e.sbpFlag = cb.sbpFlag;
  }
  if (c.roleTracker) noteStoredRole(c.roleTracker, daughter, dPValue);
  out.push(e);
  if (c.findAll) {
    const r = { ...e, triplet: [seq1, seq2, seq3] };
    r.majorP = e.minorP;
    r.minorP = e.majorP;
    r.beginning = e.ending;
    r.ending = e.beginning;
    out.push(r);
  }
  return out;
}
function runThreeSeq(aln, options = {}) {
  const def = defaultSettings().threeSeq;
  const lowestProb = options.lowestProb ?? def.lowestProb;
  const mcFlag = options.mcFlag ?? def.mcFlag;
  const circularFlag = options.circularFlag ?? 0;
  const minSeqSize = options.minSeqSize && options.minSeqSize > 0 ? options.minSeqSize : minSeqSizeFor(aln.length);
  const n = aln.nSeqs;
  const dist = options.distances ?? calcDistances(aln, minSeqSize);
  const tableCap = options.tableCap ?? def.tableCap;
  const tableMax = options.tableMax && options.tableMax > 0 ? options.tableMax : Math.min(dist.maxDiffs, tableCap);
  const mc = options.mcCorrection && options.mcCorrection > 0 ? options.mcCorrection : options.triplets ? Math.max(1, options.triplets.length) : Math.max(1, mcCorrectionFor(n));
  const ls = aln.length;
  const ctx = {
    aln,
    sn: aln.seqnum,
    ls,
    table: createExactTable(Math.max(tableMax, 3)),
    ws: {
      height: new Int32Array(ls + 2),
      xdiffpos: new Int32Array(ls + 2),
      xposdiff: new Int32Array(ls + 2)
    },
    circular: circularFlag,
    mcFlag,
    mc,
    lowestProb,
    minSites: options.minInformativeSites ?? def.minInformativeSites,
    findAll: options.findAll ?? false,
    longWindedFlag: options.longWindedFlag ?? 1,
    roleTracker: options.roleTracker ?? null,
    missingData: options.missingData ?? null,
    sEventNumber: options.sEventNumber ?? 0
  };
  const events = [];
  let scanned = 0;
  let aborted = false;
  const total = options.triplets ? options.triplets.length : n * (n - 1) * (n - 2) / 6;
  const doTriplet = (t1, t2, t3) => {
    for (const ev of tsXOver(ctx, t1, t2, t3)) events.push(ev);
    for (const ev of tsXOver(ctx, t2, t3, t1)) events.push(ev);
    for (const ev of tsXOver(ctx, t3, t1, t2)) events.push(ev);
    scanned++;
    return !!options.onProgress && scanned % 64 === 0 && options.onProgress(scanned, total) === true;
  };
  if (options.triplets) {
    for (const [a, b, c3] of options.triplets) {
      if (doTriplet(a, b, c3)) {
        aborted = true;
        break;
      }
    }
  } else {
    done: for (let a = 0; a < n - 2; a++)
      for (let b = a + 1; b < n - 1; b++)
        for (let c3 = b + 1; c3 < n; c3++)
          if (doTriplet(a, b, c3)) {
            aborted = true;
            break done;
          }
  }
  options.onProgress?.(total, total);
  return {
    events,
    scannedTriplets: scanned,
    aborted,
    settingsUsed: { lowestProb, mcFlag, mcCorrection: mc, circularFlag, tableMax: ctx.table.max },
    notes: [
      "exact P-value table computed lazily up to tableMax; SiegmundDiscrete / rescaled approximation beyond",
      "CentreBP with FindSubSeqTS maps (LSS=10); CheckSplit3Seq when sEventNumber>0 and missingData set"
    ]
  };
}

// src/engine/threeseqHarvest.worker.mts
function runJob(wd) {
  const aln = {
    names: Array.from({ length: wd.nSeqs }, (_, i) => `s${i}`),
    sequences: Array.from({ length: wd.nSeqs }, () => ""),
    length: wd.length,
    nSeqs: wd.nSeqs,
    seqnum: new Int16Array(wd.seqSab)
  };
  const flat = new Int32Array(wd.tripsSab);
  const hits = new Float64Array(wd.hitsSab);
  const state = new Int32Array(wd.stateSab);
  const maxHits = wd.maxHits || 8;
  try {
    const trips = [];
    for (let t = wd.lo; t < wd.hi; t++) {
      trips.push([flat[t * 3], flat[t * 3 + 1], flat[t * 3 + 2]]);
    }
    const r = runThreeSeq(aln, {
      circularFlag: wd.circularFlag,
      mcCorrection: wd.mcCorrection,
      lowestProb: wd.lowestProb,
      findAll: wd.findAll,
      triplets: trips,
      longWindedFlag: 0,
      roleTracker: null
    });
    const byKey = /* @__PURE__ */ new Map();
    for (const e of r.events) {
      const key = [e.triplet[0], e.triplet[1], e.triplet[2]].sort((a, b) => a - b).join(",");
      let list = byKey.get(key);
      if (!list) byKey.set(key, list = []);
      list.push(e);
    }
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = flat[t * 3];
      const b = flat[t * 3 + 1];
      const c = flat[t * 3 + 2];
      const key = [a, b, c].sort((x, y) => x - y).join(",");
      const evs = byKey.get(key) ?? [];
      const base = t * wd.hitStride;
      const n = Math.min(maxHits, evs.length);
      hits[base] = n;
      for (let h = 0; h < n; h++) {
        const e = evs[h];
        const o = base + 1 + h * 7;
        hits[o] = e.daughter;
        hits[o + 1] = e.majorP;
        hits[o + 2] = e.minorP;
        hits[o + 3] = e.beginning;
        hits[o + 4] = e.ending;
        hits[o + 5] = e.probability;
        hits[o + 6] = e.programFlag;
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
    if (msg && msg.type === "job") runJob(msg);
  });
}
var boot = workerData;
if (boot && boot.type === "boot" && boot.readySab) {
  Atomics.add(new Int32Array(boot.readySab), 0, 1);
  Atomics.notify(new Int32Array(boot.readySab), 0);
}
