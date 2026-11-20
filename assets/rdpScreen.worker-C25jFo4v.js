// src/engine/rdpScreen.worker.mts
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
  const stride = length + 1;
  let h = nSeqs * 131 + length;
  const cols = [1, Math.max(1, length / 2 | 0), length];
  for (const c of cols) {
    for (let s = 0; s < nSeqs; s++) h = h * 33 + (seqnum[c + s * stride] | 0) | 0;
  }
  return h;
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
var csCacheSn = null;
var csCache = null;
function seqnumFingerprint(seqnum, nSeqs, length) {
  const stride = length + 1;
  let h = nSeqs * 131 + length;
  const cols = [1, Math.max(1, length / 2 | 0), length];
  for (const c of cols) {
    for (let s = 0; s < nSeqs; s++) {
      h = h * 33 + (seqnum[c + s * stride] | 0) | 0;
    }
  }
  if (nSeqs > 0) {
    const last = (nSeqs - 1) * stride;
    h = h * 33 + (seqnum[1 + last] | 0) | 0;
    h = h * 33 + (seqnum[length + last] | 0) | 0;
  }
  return h;
}
function makeCompressSeqCached(seqnum, nSeqs, length, nucMat) {
  const finger = seqnumFingerprint(seqnum, nSeqs, length);
  if (csCacheSn === seqnum && csCache && csCache.n === nSeqs && csCache.L === length && csCache.finger === finger) {
    return { cs: csCache.cs, packs: csCache.packs, stride: csCache.stride };
  }
  const built = makeCompressSeqNucMat(seqnum, nSeqs, length, nucMat);
  csCacheSn = seqnum;
  csCache = { ...built, n: nSeqs, L: length, finger };
  return built;
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

// src/engine/util.ts
var f32 = Math.fround;

// src/engine/trees.ts
function mkNode(tip, number, nayme = -1) {
  return { tip, number, nayme, v: 0, next: null, back: null };
}
function hookup(p, q) {
  p.back = q;
  q.back = p;
}
function neighbour(dist, numsp, opt) {
  const n = numsp;
  if (!(n >= 2)) throw new Error("A tree needs at least 2 sequences");
  const njoin = opt.njoin;
  const outgrno = njoin === 1 && opt.outgroup != null && opt.outgroup >= 0 ? opt.outgroup + 1 : 0;
  const x = new Float32Array(n * n);
  for (let j = 0; j < n; j++) {
    for (let i = 0; i < j; i++) {
      const v = f32(Number(dist[i + j * n]));
      x[i + j * n] = v;
      x[j + i * n] = v;
    }
  }
  if (n === 2) {
    const d = x[0 + 1 * n];
    const nodes = [
      { id: 0, tip: 0, parent: 2, children: [], length: f32(d / 2) },
      { id: 1, tip: 1, parent: 2, children: [], length: f32(d / 2) },
      { id: 2, tip: -1, parent: -1, children: [0, 1], length: 0 }
    ];
    return { method: njoin === 1 ? "nj" : "upgma", nTips: 2, nodes, root: 2, outgroup: -1 };
  }
  const numsp2 = n * 2 - 2;
  const nodep = new Array(numsp2 + 1);
  for (let s = 0; s < n; s++) nodep[s] = mkNode(true, s + 1, s);
  for (let i = n + 1; i <= numsp2; i++) {
    let q = null;
    let p;
    for (let j = 1; j <= 3; j++) {
      p = mkNode(false, i);
      p.next = q;
      q = p;
    }
    p.next.next.next = p;
    nodep[i - 1] = p;
  }
  {
    let q = null;
    let p;
    for (let j = 1; j <= 2; j++) {
      p = mkNode(false, numsp2 + 1);
      p.next = q;
      q = p;
    }
    p.next.next = p;
    nodep[numsp2] = p;
  }
  const enterorder = new Array(n);
  for (let i = 1; i <= n; i++) enterorder[i - 1] = i;
  const cluster = new Array(n);
  for (let i = 0; i < n; i++) cluster[i] = nodep[i];
  let fotu2 = f32(n - 2);
  let nextnode = n + 1;
  const av = new Float32Array(n);
  const oc = new Int32Array(n).fill(1);
  const iter = njoin === 1 ? n - 3 : n - 1;
  const coltotals = new Float32Array(n);
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) coltotals[i] = f32(coltotals[i] + x[i + j * n]);
  const firstActivePair = () => {
    let a = -1;
    for (let k = 0; k < n; k++) {
      if (cluster[k] !== null) {
        if (a < 0) a = k;
        else return [a, k];
      }
    }
    return [0, 1];
  };
  if (njoin === 1) {
    for (let nc = 1; nc <= iter; nc++) {
      for (let j = 1; j < n; j++) {
        const off1 = j * n;
        for (let i = 0; i < j; i++) x[j + i * n] = x[i + off1];
      }
      for (let i = 0; i < n; i++) {
        const off1 = i * n;
        if (cluster[i] !== null) {
          let t = 0;
          for (let j = 0; j < n; j++) t = f32(t + x[j + off1]);
          coltotals[i] = t;
        }
      }
      let tmin = f32(99999);
      let [mini, minj] = firstActivePair();
      for (let ja = 2; ja <= n; ja++) {
        const jj = enterorder[ja - 1] - 1;
        if (cluster[jj] !== null) {
          const off1 = jj * n;
          for (let ia = 0; ia <= ja - 2; ia++) {
            const ii = enterorder[ia] - 1;
            if (cluster[ii] !== null) {
              const dij = x[ii + off1];
              const diq = coltotals[ii];
              const djq = coltotals[jj];
              const total = f32(f32(f32(fotu2 * dij) - diq) - djq);
              if (total < tmin) {
                tmin = total;
                mini = ii;
                minj = jj;
              }
            }
          }
        }
      }
      const mini2 = mini;
      const minj2 = minj;
      const mini1 = mini + 1;
      let dio = 0;
      let djo = 0;
      const o1 = mini2 * n;
      const o2 = minj2 * n;
      for (let i = 0; i < n; i++) {
        dio = f32(dio + x[i + o1]);
        djo = f32(djo + x[i + o2]);
      }
      const dmin = x[mini2 + o2];
      dio = f32((dio - dmin) / fotu2);
      djo = f32((djo - dmin) / fotu2);
      let bi = f32((dmin + dio - djo) * 0.5);
      let bj = f32(dmin - bi);
      bi = f32(bi - av[mini2]);
      bj = f32(bj - av[minj2]);
      const nn = nodep[nextnode - 1];
      hookup(nn.next, cluster[mini2]);
      hookup(nn.next.next, cluster[minj2]);
      cluster[mini2].v = bi;
      cluster[minj2].v = bj;
      cluster[mini2].back.v = bi;
      cluster[minj2].back.v = bj;
      cluster[mini2] = nn;
      cluster[minj2] = null;
      nextnode++;
      av[mini2] = f32(dmin * 0.5);
      fotu2 = f32(fotu2 - 1);
      for (let j = 0; j < n; j++) {
        if (cluster[j] !== null) {
          const da = f32((x[mini2 + j * n] + x[minj2 + j * n]) * 0.5);
          if (mini1 - j - 1 < 0) x[mini2 + j * n] = da;
          else if (mini1 - j - 1 > 0) x[j + mini2 * n] = da;
        }
      }
      for (let j = 0; j < n; j++) {
        x[minj2 + j * n] = 0;
        x[j + minj2 * n] = 0;
      }
      oc[mini2] += oc[minj2];
    }
  } else {
    for (let nc = 1; nc <= iter; nc++) {
      for (let j = 2; j <= n; j++) {
        for (let i = 0; i <= j - 2; i++) x[j - 1 + i * n] = x[i + (j - 1) * n];
      }
      let tmin = f32(99999);
      let [mini, minj] = firstActivePair();
      for (let ja = 2; ja <= n; ja++) {
        const jj = enterorder[ja - 1] - 1;
        if (cluster[jj] !== null) {
          const off1 = jj * n;
          for (let ia = 0; ia <= ja - 2; ia++) {
            const ii = enterorder[ia] - 1;
            if (cluster[ii] !== null) {
              if (x[ii + off1] < tmin) {
                tmin = x[ii + off1];
                mini = ii;
                minj = jj;
              }
            }
          }
        }
      }
      const mini2 = mini;
      const minj2 = minj;
      const bi = f32(f32(x[mini2 + minj2 * n] / 2) - av[mini2]);
      const bj = f32(f32(x[mini2 + minj2 * n] / 2) - av[minj2]);
      av[mini2] = f32(av[mini2] + bi);
      const nn = nodep[nextnode - 1];
      hookup(nn.next, cluster[mini2]);
      hookup(nn.next.next, cluster[minj2]);
      cluster[mini2].v = bi;
      cluster[minj2].v = bj;
      cluster[mini2].back.v = bi;
      cluster[minj2].back.v = bj;
      cluster[mini2] = nn;
      cluster[minj2] = null;
      nextnode++;
      fotu2 = f32(fotu2 - 1);
      for (let j = 0; j < n; j++) {
        if (cluster[j] !== null) {
          let da = x[mini2 + j * n] * oc[mini2] + x[minj2 + j * n] * oc[minj2];
          da /= oc[mini2] + oc[minj2];
          x[mini2 + j * n] = f32(da);
          x[j + mini2 * n] = f32(da);
        }
      }
      for (let j = 0; j < n; j++) {
        x[minj2 + j * n] = 0;
        x[j + minj2 * n] = 0;
      }
      oc[mini2] += oc[minj2];
    }
  }
  const el = [];
  for (let i = 1; i <= n; i++) if (cluster[i - 1] !== null) el.push(i);
  let start;
  if (njoin === 0) {
    start = cluster[el[0] - 1];
  } else {
    let bi = f32((x[el[0] - 1 + (el[1] - 1) * n] + x[el[0] - 1 + (el[2] - 1) * n] - x[el[1] - 1 + (el[2] - 1) * n]) * 0.5);
    let bj = f32(x[el[0] - 1 + (el[1] - 1) * n] - bi);
    let bk = f32(x[el[0] - 1 + (el[2] - 1) * n] - bi);
    bi = f32(bi - av[el[0] - 1]);
    bj = f32(bj - av[el[1] - 1]);
    bk = f32(bk - av[el[2] - 1]);
    const nn = nodep[nextnode - 1];
    hookup(nn, cluster[el[0] - 1]);
    hookup(nn.next, cluster[el[1] - 1]);
    hookup(nn.next.next, cluster[el[2] - 1]);
    cluster[el[0] - 1].v = bi;
    cluster[el[1] - 1].v = bj;
    cluster[el[2] - 1].v = bk;
    cluster[el[0] - 1].back.v = bi;
    cluster[el[1] - 1].back.v = bj;
    cluster[el[2] - 1].back.v = bk;
    start = cluster[el[0] - 1].back;
  }
  if (outgrno > 0) start = nodep[outgrno - 1].back;
  return ringToTree(start, njoin, n, outgrno > 0 ? outgrno - 1 : -1);
}
function ringToTree(start, njoin, nTips, outgroup) {
  const nodes = [];
  for (let i = 0; i < nTips; i++) nodes.push({ id: i, tip: i, parent: -1, children: [], length: 0 });
  const build = (p, isStart) => {
    if (p.tip) {
      nodes[p.nayme].length = p.v;
      return p.nayme;
    }
    const id = nodes.length;
    const node = { id, tip: -1, parent: -1, children: [], length: isStart ? 0 : p.v };
    nodes.push(node);
    const kids = [build(p.next.back, false), build(p.next.next.back, false)];
    if (isStart && njoin === 1) kids.push(build(p.back, false));
    node.children = kids;
    for (const k of kids) nodes[k].parent = id;
    return id;
  };
  const root = build(start, true);
  return { method: njoin === 1 ? "nj" : "upgma", nTips, nodes, root, outgroup };
}
function pickOutgroup(dist, n) {
  const tot = new Float32Array(n);
  for (let x = 0; x < n; x++) {
    for (let y = x + 1; y < n; y++) {
      if (dist[x + x * n] < 3 && dist[y + y * n] < 3) {
        tot[x] = f32(tot[x] + dist[x + y * n]);
        tot[y] = f32(tot[y] + dist[x + y * n]);
      }
    }
  }
  let maxSc = 0;
  let outie = -1;
  for (let x = 0; x < n; x++) {
    if (tot[x] > maxSc) {
      outie = x;
      maxSc = tot[x];
    }
  }
  return outie;
}
function buildNJTree(dist, n, opt = {}) {
  let og = null;
  if (opt.outgroup === "auto") og = n > 3 ? pickOutgroup(dist, n) : -1;
  else if (typeof opt.outgroup === "number") og = opt.outgroup;
  return neighbour(dist, n, { njoin: 1, outgroup: og });
}
function buildUPGMATree(dist, n) {
  return neighbour(dist, n, { njoin: 0 });
}
function patristicMatrix(tree, opt = {}) {
  const n = tree.nTips;
  const N = tree.nodes.length;
  const len = (id) => {
    const l = tree.nodes[id].length;
    if (!opt.clamp) return l;
    return l < 0 ? 0 : l > 1 ? 1 : l;
  };
  const adj = Array.from({ length: N }, () => []);
  for (const nd of tree.nodes) {
    if (nd.parent >= 0) {
      const w = len(nd.id);
      adj[nd.id].push([nd.parent, w]);
      adj[nd.parent].push([nd.id, w]);
    }
  }
  const out = new Float32Array(n * n);
  const dist = new Float64Array(N);
  const stack = new Int32Array(N);
  const from = new Int32Array(N);
  for (let s = 0; s < n; s++) {
    dist.fill(0);
    from.fill(-1);
    let sp = 0;
    stack[sp++] = s;
    while (sp > 0) {
      const u = stack[--sp];
      for (const [v, w] of adj[u]) {
        if (v === from[u]) continue;
        from[v] = u;
        dist[v] = dist[u] + w;
        stack[sp++] = v;
      }
    }
    for (let t = 0; t < n; t++) out[s + t * n] = t === s ? 0 : f32(dist[t]);
  }
  return out;
}
function distanceBakFromIdentity(identity, n) {
  const out = new Float32Array(n * n);
  for (let x = 0; x < n; x++) {
    for (let y = x + 1; y < n; y++) {
      const id = identity[x + y * n];
      const d = id > 0 ? f32(1 - id) : f32(0.999);
      out[x + y * n] = d;
      out[y + x * n] = d;
    }
  }
  return out;
}
function buildTreeDistance(identityDistance, n, method = "upgma") {
  if (!(n >= 2)) {
    const out2 = new Float32Array(Math.max(0, n) * Math.max(0, n));
    for (let i = 0; i < n; i++) out2[i + i * n] = 1;
    return out2;
  }
  const bak = distanceBakFromIdentity(identityDistance, n);
  const tree = method === "nj" ? buildNJTree(bak, n, { outgroup: "auto" }) : buildUPGMATree(bak, n);
  const pat = patristicMatrix(tree);
  const out = new Float32Array(n * n);
  for (let i = 0; i < n; i++) {
    out[i + i * n] = 1;
    for (let j = i + 1; j < n; j++) {
      const td = f32(1 - pat[i + j * n] / 2);
      out[i + j * n] = td;
      out[j + i * n] = td;
    }
  }
  return out;
}

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
function probCalc(L, numSame, p, lenXO) {
  let prob = 0;
  const w = MAXL + 1;
  for (let z = numSame; z <= L; z++) {
    prob += BINOM[L * w + z] * Math.pow(p, z) * Math.pow(1 - p, L - z);
  }
  return prob * lenXO / L;
}
function clngHalfEven(x) {
  const f = Math.floor(x);
  const d = x - f;
  if (d < 0.5) return f;
  if (d > 0.5) return f + 1;
  return f % 2 === 0 ? f : f + 1;
}
function probabilityVBForm(xoverLenRaw, nCommonRaw, indProb, lenXoverSeq, mcFlag, mc) {
  let xoLen = xoverLenRaw;
  let numDiff = xoverLenRaw - nCommonRaw;
  let aFact;
  if (xoLen >= 170) {
    aFact = xoLen / 169;
    numDiff = clngHalfEven(numDiff * 169 / xoLen);
    xoLen = 169;
  } else {
    aFact = 1;
  }
  let p = probCalc(xoLen, xoLen - numDiff, indProb, clngHalfEven(lenXoverSeq / aFact));
  if (p > 1) p = 1;
  if (aFact > 200) aFact = 200;
  p = Math.pow(p, aFact);
  if (p < 1e-300) p = 1e-300;
  if (mcFlag === 0) p *= mc;
  return p;
}
function findNextP(c, startPosX, high, med, low, lenXO) {
  const o1 = (med - 1) * c.S;
  const o2 = (high - 1) * c.S;
  const o3 = (low - 1) * c.S;
  const h = c.hom;
  for (let x = startPosX; x <= lenXO; x++) {
    if (h[x + o1] > h[x + o2]) {
      if (h[x + o1] > h[x + o3]) return x;
    }
  }
  return -1;
}
function findFirstCOP(c, x0, med, high, lenXO) {
  const os = c.S;
  const h = c.hom;
  let x = x0;
  while (h[x + (med - 1) * os] > h[x + (high - 1) * os]) {
    x++;
    if (x > lenXO + 2 * c.xow + 1) break;
  }
  if (h[lenXO + (med - 1) * os] <= h[lenXO + (high - 1) * os]) {
    h[lenXO + (med - 1) * os] = h[1 + (med - 1) * os];
    h[lenXO + (high - 1) * os] = h[1 + (high - 1) * os];
  }
  return x;
}
function defineEventP2(c, med, high, low, xx, lenXO, seqD, seqM, st) {
  const S = c.S;
  const xow = c.xow;
  const xos = c.xosw;
  const h = c.hom;
  const off2b = (med - 1) * S;
  const off3b = (high - 1) * S;
  const off6b = (low - 1) * S;
  let tc = 0;
  if (seqD === 0 && seqM === 1 || seqD === 1 && seqM === 0) tc = 0;
  else if (seqD === 0 && seqM === 2 || seqD === 2 && seqM === 0) tc = 1;
  else if (seqD === 2 && seqM === 1 || seqD === 1 && seqM === 2) tc = 2;
  const off4 = xow + tc * S;
  let x = xx;
  if (x > 1) {
    while (x !== 1) {
      x--;
      if (xos[x + off4] === 0) {
        x++;
        break;
      }
    }
  }
  let nc = 0;
  if (xos[x + off4] === 0) {
    while (x <= lenXO + 1) {
      x++;
      if (xos[x + off4]) break;
      if (x === lenXO + 1) {
        if (nc === 1) break;
        x = 0;
        nc++;
        st.endFlag = 1;
      }
    }
  }
  st.be = x;
  while (x <= lenXO) {
    if (xos[x + off4]) st.nCommon++;
    st.xoLen++;
    if (st.xoLen >= lenXO) break;
    x++;
    if (x > lenXO) {
      if (c.circular === 1) {
        x = 0;
        st.endFlag = 1;
      } else {
        x = lenXO + 2 * xow + 1;
        break;
      }
    }
    if (h[x + off2b] < h[x + off3b] || h[x + off2b] < h[x + off6b]) {
      if (xos[x + off4] === 0) break;
    }
  }
  const storex = x;
  x--;
  while (x > 0) {
    if (xos[x + off4] === 0) {
      if (x < lenXO) {
        if (x > 0) {
          x--;
          st.xoLen--;
          if (st.xoLen === 1) break;
        } else {
          x = lenXO + 1;
          break;
        }
      } else break;
    } else break;
  }
  st.en = x;
  return storex + 1;
}
function daughterMinor(high, med, low, out) {
  if (high === 1 && med === 2 && low === 3) {
    out[0] = 0;
    out[1] = 2;
  } else if (high === 1 && med === 3 && low === 2) {
    out[0] = 1;
    out[1] = 2;
  } else if (high === 2 && med === 1 && low === 3) {
    out[0] = 0;
    out[1] = 1;
  } else if (high === 2 && med === 3 && low === 1) {
    out[0] = 2;
    out[1] = 1;
  } else if (high === 3 && med === 1 && low === 2) {
    out[0] = 1;
    out[1] = 0;
  } else if (high === 3 && med === 2 && low === 1) {
    out[0] = 2;
    out[1] = 0;
  }
}
var TT = Math.fround(0.7);
function scanTriplet(c, seq1, seq2, seq3, collectAll) {
  const hits = [];
  const { ls, xow, S, xosw, hom, xdiff } = c;
  const stride = ls + 1;
  const sn = c.seqnum;
  xosw.fill(0);
  hom.fill(0);
  c.xpos.fill(0);
  const ah = [0, 0, 0, 0];
  let y = 0;
  const xpos = c.xpos;
  const { fssRdp, skipTrip } = getFssTables();
  const s1o = seq1 * c.csStride;
  const s2o = seq2 * c.csStride;
  const s3o = seq3 * c.csStride;
  const cs = c.cs;
  let xh = 0;
  for (let xi = 1; xi <= c.csPacks; xi++) {
    const A = cs[s1o + xi];
    const B = cs[s2o + xi];
    const C = cs[s3o + xi];
    const skipIdx = A * 15625 + B * 125 + C;
    if (skipTrip[skipIdx] === 0) {
      for (let z = 0; z < 3; z++) {
        xh++;
        if (xh <= ls) xpos[xh] = y;
      }
      continue;
    }
    const osf = skipIdx * 3;
    for (let z = 0; z < 3; z++) {
      xh++;
      if (xh > ls) break;
      const holder = fssRdp[osf + z];
      if (holder > 0) {
        y++;
        xdiff[y] = xh;
        xpos[xh] = y;
        ah[holder - 1]++;
        xosw[y + xow + (holder - 1) * S] = 1;
      } else {
        xpos[xh] = y;
      }
    }
  }
  c.infoLen = y;
  {
    let wmx = y - xow;
    let wpx = y + xow;
    for (let b = 1; b <= xow; b++) {
      wmx++;
      wpx++;
      for (let l = 0; l < 3; l++) {
        const base = l * S;
        xosw[b + base] = xosw[wmx + xow + base];
        xosw[wpx + base] = xosw[b + xow + base];
      }
    }
  }
  let lenXoverSeq = y;
  if (lenXoverSeq < xow * 2) return hits;
  const third = Math.trunc(xow / 3);
  if (ah[0] < third || ah[1] < third || ah[2] < third) return hits;
  if (ah[0] === 0 || ah[1] === 0 || ah[2] === 0) return hits;
  const avHomol = [0, ah[0] / lenXoverSeq, ah[1] / lenXoverSeq, ah[2] / lenXoverSeq];
  const count = lenXoverSeq;
  lenXoverSeq = lenXoverSeq - 1;
  const dn = c.n;
  const td = c.treeDist;
  const td12 = td[seq1 + seq2 * dn];
  const td13 = td[seq1 + seq3 * dn];
  const td23 = td[seq2 + seq3 * dn];
  let highHomol = 0;
  if (td12 >= td13 && td12 >= td23) highHomol = 1;
  else if (td13 >= td12 && td13 >= td23) highHomol = 2;
  else if (td23 >= td12 && td23 >= td13) highHomol = 3;
  const d12 = c.dist[seq1 + seq2 * dn];
  const d13 = c.dist[seq1 + seq3 * dn];
  const d23 = c.dist[seq2 + seq3 * dn];
  const limit = 2 * xow + 1;
  for (let l = 0; l < 3; l++) {
    const base = l * S;
    let t = 0;
    for (let z = 1; z <= limit; z++) t += xosw[z + base];
    hom[1 + base] = t;
    for (let x2 = 2; x2 <= lenXoverSeq + 1; x2++) {
      t = t - xosw[x2 - 1 + base] + xosw[x2 + 2 * xow + base];
      hom[x2 + base] = t;
    }
  }
  let startPosX = 0;
  {
    const of1 = (highHomol - 1) * S;
    for (let x2 = 1; x2 <= lenXoverSeq + 1; x2++) {
      if (hom[x2 + of1] <= xow) {
        startPosX = x2;
        break;
      }
    }
  }
  if (startPosX === 0) return hits;
  if (avHomol[1] === avHomol[2] && avHomol[1] === avHomol[3]) {
    if (d12 >= d13 && d12 >= d23) {
      if (d13 > d23) {
        avHomol[2] -= 1e-5;
        avHomol[3] -= 2e-5;
      } else {
        avHomol[2] -= 2e-5;
        avHomol[3] -= 1e-5;
      }
    } else if (d13 >= d12 && d13 >= d23) {
      if (d12 > d23) {
        avHomol[1] -= 1e-5;
        avHomol[3] -= 2e-5;
      } else {
        avHomol[1] -= 2e-5;
        avHomol[3] -= 1e-5;
      }
    } else {
      if (d12 > d13) {
        avHomol[1] -= 1e-5;
        avHomol[2] -= 2e-5;
      } else {
        avHomol[1] -= 2e-5;
        avHomol[2] -= 1e-5;
      }
    }
  } else if (avHomol[1] === avHomol[2]) {
    if (d12 > d13) avHomol[2] -= 1e-5;
    else avHomol[1] -= 1e-5;
  } else if (avHomol[1] === avHomol[3]) {
    if (d12 > d23) avHomol[3] -= 1e-5;
    else avHomol[1] -= 1e-5;
  } else if (avHomol[2] === avHomol[3]) {
    if (d13 > d23) avHomol[3] -= 1e-5;
    else avHomol[2] -= 1e-5;
  }
  let med = 0;
  let low = 0;
  let seqD = 0;
  let seqM = 0;
  if (avHomol[1] >= avHomol[2] && avHomol[1] >= avHomol[3]) {
    highHomol = 1;
    if (avHomol[2] >= avHomol[3]) {
      med = 2;
      low = 3;
      seqD = 0;
      seqM = 2;
    } else {
      med = 3;
      low = 2;
      seqD = 1;
      seqM = 2;
    }
  } else if (avHomol[2] >= avHomol[1] && avHomol[2] >= avHomol[3]) {
    highHomol = 2;
    if (avHomol[1] >= avHomol[3]) {
      med = 1;
      low = 3;
      seqD = 0;
      seqM = 1;
    } else {
      med = 3;
      low = 1;
      seqD = 2;
      seqM = 1;
    }
  } else {
    highHomol = 3;
    if (avHomol[1] >= avHomol[2]) {
      med = 1;
      low = 2;
      seqD = 1;
      seqM = 0;
    } else {
      med = 2;
      low = 1;
      seqD = 2;
      seqM = 0;
    }
  }
  const tri = [seq1, seq2, seq3];
  const st = { endFlag: 0, be: 0, en: 0, nCommon: 0, xoLen: 0 };
  const dm = [0, 0];
  let findCycle = 0;
  let oldX = -1;
  let x = -1;
  const mapBegin = (i) => {
    if (c.circular === 1) {
      let k = i;
      if (k < 1) k += count;
      if (k > count) k -= count;
      return xdiff[k];
    }
    if (i <= 1) return 1;
    return xdiff[Math.min(i, count)];
  };
  const mapEnd = (e) => {
    if (c.circular === 1) {
      let k = e;
      if (k < 1) k += count;
      if (k > count) k -= count;
      const v2 = xdiff[k];
      return v2 === 0 ? ls - 1 : v2;
    }
    if (e >= count) return ls;
    const v = xdiff[Math.max(e, 1)];
    return v === 0 ? ls - 1 : v;
  };
  outer: while (findCycle < 4) {
    let nextPosX = 1;
    while (findCycle < 4) {
      x = findNextP(c, nextPosX, highHomol, med, low, lenXoverSeq);
      if (x > -1 && x !== oldX) {
        oldX = x;
        if (c.circular === 1 && hom[x + (med - 1) * S] > hom[x + (highHomol - 1) * S] && x === 1) {
          x = findFirstCOP(c, x, med, highHomol, lenXoverSeq);
        } else {
          st.nCommon = 0;
          st.xoLen = 0;
          x = defineEventP2(c, med, highHomol, low, x, lenXoverSeq, seqD, seqM, st);
          if (st.xoLen > 2 && st.en !== st.be && (st.en > st.be || c.circular === 1)) {
            let numDifferent = st.xoLen - st.nCommon;
            if (st.nCommon > numDifferent * 0.8) {
              const rawLen = st.xoLen;
              const rawCommon = st.nCommon;
              let aFact;
              let xoLen = st.xoLen;
              let numSame;
              if (xoLen >= 170) {
                aFact = xoLen / 169;
                numDifferent = Math.round(numDifferent * 169 / xoLen);
                xoLen = 169;
                numSame = xoLen - numDifferent;
              } else {
                aFact = 1;
                numSame = st.nCommon;
              }
              const indProb = avHomol[med];
              let p = probCalc(xoLen, numSame, indProb, lenXoverSeq);
              if (aFact > 1.000001) {
                if (p > 0) p = Math.pow(p, aFact);
                else p = 0.05;
              }
              if (p < 1e-300) p = 1e-300;
              const rawP = p;
              if (p < c.ucThresh && p > 0) {
                if (c.mcFlag === 0) p = p * c.mc;
                if (p < c.lowestProb && p > 0) {
                  hits.push({
                    daughter: tri[seqD],
                    minor: tri[seqM],
                    major: tri[3 - seqD - seqM],
                    begin: mapBegin(st.be),
                    end: mapEnd(st.en),
                    p,
                    rawP,
                    pVB: probabilityVBForm(rawLen, rawCommon, indProb, lenXoverSeq, c.mcFlag, c.mc),
                    xoLen,
                    nCommon: numSame,
                    indProb,
                    lenXO: lenXoverSeq,
                    winSites: rawLen,
                    triplet: tri,
                    homolIdx: [highHomol, med, low]
                  });
                  if (!collectAll) return hits;
                }
              }
            }
          }
        }
        if (st.endFlag === 1) {
          st.endFlag = 0;
          x = lenXoverSeq;
        }
        if (x < lenXoverSeq + 1 && x > nextPosX) nextPosX = x + 1;
        else break;
      } else break;
    }
    if (findCycle === 0) {
      const t = med;
      med = low;
      low = t;
    } else if (findCycle === 1) {
      if (avHomol[highHomol] < TT || c.doAll === 1) {
        const t = highHomol;
        highHomol = low;
        low = med;
        med = t;
      } else break outer;
    } else break outer;
    daughterMinor(highHomol, med, low, dm);
    seqD = dm[0];
    seqM = dm[1];
    findCycle++;
  }
  return hits;
}
function runRDP(aln, options = {}) {
  const def = defaultSettings().rdp;
  const lowestProb = options.lowestProb ?? def.lowestProb;
  const xOverWindowX = options.xOverWindowX ?? def.xOverWindowX;
  const mcFlag = options.mcFlag ?? def.mcFlag;
  const circularFlag = options.circularFlag ?? 0;
  const minSeqSize = options.minSeqSize && options.minSeqSize > 0 ? options.minSeqSize : minSeqSizeFor(aln.length);
  const minDiffs = options.minPairDiffs ?? def.minPairDiffs;
  const doAll = options.doAllFlag ?? def.doAllFlag;
  const collectAll = options.collectAll ?? true;
  const n = aln.nSeqs;
  const notes = ["ProbEstimate pre-filter not applied (GoOn = 1)"];
  const longWindedFlag = options.longWindedFlag ?? 1;
  const roleTracker = options.roleTracker ?? null;
  const dist = options.distances ?? calcDistances(aln, minSeqSize);
  let treeDist;
  const useDistHH = options.highHomolFromDistance === true || options.highHomolFromDistance !== false && !collectAll;
  if (options.treeDistance && options.treeDistance.length >= n * n) {
    treeDist = options.treeDistance instanceof Float32Array ? options.treeDistance : Float32Array.from(options.treeDistance);
  } else if (useDistHH) {
    const d = dist.distance;
    treeDist = new Float32Array(n * n);
    for (let i = 0; i < n * n; i++) treeDist[i] = 1 - d[i];
    notes.push("HighHomol from Distance (no UPGMA TreeDistance)");
  } else {
    treeDist = buildTreeDistance(dist.distance, n, "upgma");
    notes.push("TreeDistance from UPGMA patristic (1 \u2212 d/2) used for HighHomol");
  }
  const mc = options.mcCorrection && options.mcCorrection > 0 ? options.mcCorrection : options.triplets ? Math.max(1, options.triplets.length) : Math.max(1, mcCorrectionFor(n));
  const xow = Math.trunc(xOverWindowX / 2);
  const S = aln.length + 1 + 2 * xow;
  const packed = makeCompressSeqCached(aln.seqnum, n, aln.length, NUC_MAT);
  const ctx = {
    seqnum: aln.seqnum,
    ls: aln.length,
    n,
    xow,
    S,
    xosw: new Uint8Array(3 * S + 4),
    hom: new Int32Array(3 * S + 4),
    xdiff: new Int32Array(aln.length + 4),
    xpos: new Int32Array(aln.length + 4),
    infoLen: 0,
    dist: dist.distance,
    treeDist,
    circular: circularFlag,
    mcFlag,
    mc,
    lowestProb,
    ucThresh: mcFlag === 0 ? lowestProb / mc : lowestProb,
    doAll,
    cs: packed.cs,
    csPacks: packed.packs,
    csStride: packed.stride
  };
  const events = [];
  let scanned = 0;
  let skipped = 0;
  let flagged = 0;
  let aborted = false;
  const mask = options.maskSeqs;
  const pv = dist.permValid;
  const pd = dist.permDiffs;
  const total = options.triplets ? options.triplets.length : n * (n - 1) * (n - 2) / 6;
  const process2 = (a, b, c3) => {
    const s12 = a + n * b;
    const s13 = a + n * c3;
    const s23 = b + n * c3;
    if (!(pd[s12] > minDiffs && pv[s12] > minSeqSize) || !(pv[s13] > minSeqSize && pv[s23] > minSeqSize) || !(pd[s23] > minDiffs && pd[s13] > minDiffs)) {
      skipped++;
      return false;
    }
    scanned++;
    const hits = scanTriplet(ctx, a, b, c3, collectAll);
    if (hits.length > 0) flagged++;
    for (const h of hits) {
      const ev = toEvent(h, ctx);
      if (ctx.infoLen >= 2) {
        const maps = { xPosDiff: ctx.xpos, xDiffPos: ctx.xdiff, lenXoverSeq: ctx.infoLen };
        const cb = centreBreakpoints(aln, ev, maps, {
          circularFlag,
          lss: ctx.xow
        });
        ev.beginning = cb.beginning;
        ev.ending = cb.ending;
        ev.beginWarn = cb.beginWarn;
        ev.endWarn = cb.endWarn;
        ev.sbpFlag = cb.sbpFlag;
      }
      if (longWindedFlag === 1 && roleTracker) {
        const par = assignEventRoles(aln, h.triplet, ev.beginning, ev.ending, {
          longWindedFlag: 1,
          tracker: roleTracker
        });
        ev.daughter = par.daughter;
        ev.majorP = par.majorP;
        ev.minorP = par.minorP;
        noteStoredRole(roleTracker, par.daughter, ev.probability);
      }
      events.push(ev);
    }
    if (options.onProgress && (scanned + skipped) % 256 === 0) {
      if (options.onProgress(scanned + skipped, total) === true) return true;
    }
    return false;
  };
  if (options.triplets) {
    for (const t of options.triplets) {
      const s = [...t].sort((p, q) => p - q);
      if (mask && (mask[s[0]] || mask[s[1]] || mask[s[2]])) continue;
      if (process2(s[0], s[1], s[2])) {
        aborted = true;
        break;
      }
    }
  } else {
    done: for (let s1 = 0; s1 < n; s1++) {
      if (mask && mask[s1]) continue;
      for (let s2 = s1 + 1; s2 <= n - 2; s2++) {
        if (mask && mask[s2]) continue;
        const s12 = s1 + n * s2;
        if (!(pd[s12] > minDiffs && pv[s12] > minSeqSize)) {
          skipped += n - 1 - s2;
          continue;
        }
        for (let s3 = s2 + 1; s3 < n; s3++) {
          if (mask && mask[s3]) continue;
          if (process2(s1, s2, s3)) {
            aborted = true;
            break done;
          }
        }
      }
    }
  }
  options.onProgress?.(total, total);
  return {
    events,
    scannedTriplets: scanned,
    skippedTriplets: skipped,
    flaggedTriplets: flagged,
    aborted,
    settingsUsed: { lowestProb, xOverWindowX, mcFlag, mcCorrection: mc, circularFlag, minSeqSize },
    notes
  };
}
function toEvent(h, c) {
  const e = newXOverEvent(PROGRAM_RDP);
  e.daughter = h.daughter;
  e.minorP = h.minor;
  e.majorP = h.major;
  e.beginning = h.begin;
  e.ending = h.end;
  e.probability = h.p;
  e.lHolder = h.winSites;
  e.triplet = h.triplet;
  e.hWindowWidth = c.xow;
  e.lenXoverSeq = h.lenXO;
  e.loHiFlag = 1;
  e.maxY = h.homolIdx[1];
  return {
    ...e,
    rawP: h.rawP,
    probabilityVBForm: h.pVB,
    xoverLength: h.xoLen,
    nCommon: h.nCommon,
    indProb: h.indProb
  };
}

// src/engine/rdpScreen.worker.mts
function runJob(wd) {
  const seqnum = new Int16Array(wd.seqSab);
  const aln = {
    names: Array.from({ length: wd.nSeqs }, (_, i) => `s${i}`),
    sequences: Array.from({ length: wd.nSeqs }, () => ""),
    length: wd.length,
    nSeqs: wd.nSeqs,
    seqnum
  };
  let distances;
  if (wd.distSab && wd.pvSab && wd.pdSab) {
    distances = {
      n: wd.nSeqs,
      distance: new Float32Array(wd.distSab),
      permValid: new Float32Array(wd.pvSab),
      permDiffs: new Float32Array(wd.pdSab),
      maxDiffs: 0
    };
  } else {
    distances = calcDistances(aln, wd.minSeqSize);
  }
  const chunkTrips = [];
  for (let t = wd.lo; t < wd.hi; t++) {
    chunkTrips.push([wd.flatTrips[t * 3], wd.flatTrips[t * 3 + 1], wd.flatTrips[t * 3 + 2]]);
  }
  const flags = new Uint8Array(wd.flagsSab);
  const state = new Int32Array(wd.stateSab);
  try {
    const treeDistance = wd.tdSab ? new Float32Array(wd.tdSab) : void 0;
    const screen = runRDP(aln, {
      lowestProb: wd.lowestProb,
      xOverWindowX: wd.xOverWindowX,
      mcFlag: wd.mcFlag,
      mcCorrection: wd.mcCorrection,
      circularFlag: wd.circularFlag,
      minSeqSize: wd.minSeqSize,
      minPairDiffs: wd.minPairDiffs,
      doAllFlag: wd.doAllFlag,
      longWindedFlag: 0,
      collectAll: false,
      triplets: chunkTrips,
      distances,
      ...treeDistance ? { treeDistance, highHomolFromDistance: false } : { highHomolFromDistance: true }
    });
    const flagged = /* @__PURE__ */ new Set();
    for (const e of screen.events) {
      const s = [...e.triplet].sort((a, b) => a - b);
      flagged.add(`${s[0]},${s[1]},${s[2]}`);
    }
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = wd.flatTrips[t * 3];
      const b = wd.flatTrips[t * 3 + 1];
      const c = wd.flatTrips[t * 3 + 2];
      const s = [a, b, c].sort((x, y) => x - y);
      flags[t] = flagged.has(`${s[0]},${s[1]},${s[2]}`) ? 1 : 0;
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
