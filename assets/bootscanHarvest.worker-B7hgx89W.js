// src/engine/bootscanHarvest.worker.mts
import { parentPort, workerData } from "node:worker_threads";

// src/engine/settings.ts
var PROGRAM_RDP = 0;
var PROGRAM_GENECONV = 1;
var PROGRAM_BOOTSCAN = 2;
var PROGRAM_SISCAN = 5;
var PROGRAM_LARD = 7;
var PROGRAM_3SEQ = 8;
var PROGRAM_TOPAL = 9;
function minSeqSizeFor(alignmentLength) {
  let m = 50;
  if (alignmentLength / 100 > m) m = Math.trunc(alignmentLength / 100);
  return m;
}
function mcCorrectionFor(nSeqs) {
  if (nSeqs < 3) return 1;
  return nSeqs * (nSeqs - 1) * (nSeqs - 2) / 6;
}

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
function vbCLng(x) {
  const f = Math.floor(x);
  const d = x - f;
  if (d < 0.5) return f;
  if (d > 0.5) return f + 1;
  return f % 2 === 0 ? f : f + 1;
}
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
function makeFactTable() {
  const fact = new Float64Array(171);
  let y = 1;
  fact[0] = 1;
  for (let x = 1; x <= 170; x++) {
    y *= x;
    fact[x] = y;
  }
  return fact;
}
function probCalcP(fact, xoverlength, numincommon, indprob, lenxoverseq) {
  let probability = 0;
  const td1 = xoverlength;
  const td2 = lenxoverseq;
  const nfactorial = fact[xoverlength];
  for (let z = numincommon; z <= xoverlength; z++) {
    const mfactorial = fact[z];
    const nmfactorial = fact[xoverlength - z];
    const hold = mfactorial * nmfactorial;
    const hold2 = nfactorial / hold;
    probability = probability + Math.pow(indprob, z) * Math.pow(1 - indprob, xoverlength - z) * hold2;
  }
  probability = probability * td2 / td1;
  return probability;
}
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

// src/engine/geneconvParallel.ts
import { createRequire as createRequire2 } from "node:module";

// src/engine/parallelPool.ts
import { createRequire } from "node:module";
var req = createRequire(import.meta.url);

// src/engine/geneconvParallel.ts
var req2 = createRequire2(import.meta.url);

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
import { createRequire as createRequire3 } from "node:module";
var req3 = createRequire3(import.meta.url);

// src/engine/maxchi.ts
function createRoleTracker(nSeqs) {
  return { counts: new Array(nSeqs).fill(0), storeLPV: new Array(nSeqs).fill(1) };
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

// src/engine/shrinkRegionBS.ts
var GAP3 = 46;
function shrinkRegionBS(aln, hi1, hi2, lo, rs, re, opts = {}) {
  const L = aln.length;
  const circularFlag = opts.circularFlag ?? 0;
  const sen = opts.sEventNumber ?? 0;
  const md = opts.missingData ?? null;
  const sn = aln.seqnum;
  const stride = L + 1;
  const at = (pos, seq) => {
    if (pos < 1 || pos > L || seq < 0) return GAP3;
    return sn[pos + seq * stride] ?? GAP3;
  };
  const isMissing = (pos) => {
    if (!md || sen <= 0) return false;
    return (md[pos + hi1 * stride] ?? 0) === 1 || (md[pos + hi2 * stride] ?? 0) === 1 || (md[pos + lo * stride] ?? 0) === 1;
  };
  let be = rs;
  let en = re;
  if (be < 1) be = 1;
  if (en < 1) en = 1;
  if (be > L) be = L;
  if (en > L) en = L;
  let bEx = be;
  let enX = en;
  let x = be - 1;
  if (x > L) x = L;
  for (; ; ) {
    const h1 = at(x, hi1);
    const h2 = at(x, hi2);
    const loV = at(x, lo);
    if (h1 !== GAP3 && h2 !== GAP3 && loV !== GAP3) {
      if (h1 !== h2 && h1 === loV) {
        bEx = x;
        break;
      }
    }
    x--;
    if (x < 1) {
      if (circularFlag === 1) x = L;
      else {
        bEx = 1;
        break;
      }
    } else if (isMissing(x)) {
      bEx = bEx + 1;
      break;
    }
    if (x === be || x === en) return { beginning: bEx, ending: enX, ok: false };
  }
  x = bEx;
  if (x > L) x = L;
  let ncyc = 0;
  for (; ; ) {
    const h1 = at(x, hi1);
    const h2 = at(x, hi2);
    const loV = at(x, lo);
    if (h1 !== GAP3 && h2 !== GAP3 && loV !== GAP3) {
      if (h1 === h2 && h1 !== loV) {
        bEx = x;
        break;
      }
    }
    x++;
    if (x > L) {
      if (circularFlag === 1) {
        x = 1;
        if (sen > 0 && isMissing(x)) {
          bEx = 1;
          break;
        }
        ncyc++;
        if (ncyc === 2) return { beginning: bEx, ending: enX, ok: false };
      } else {
        bEx = 1;
        break;
      }
    } else if (isMissing(x)) {
      let cycle = 0;
      while (isMissing(x)) {
        x++;
        if (x > L) {
          x = 1;
          cycle++;
          if (cycle === 2) {
            x = en;
            break;
          }
        }
      }
      bEx = x;
      break;
    }
    if (x === en) return { beginning: bEx, ending: enX, ok: false };
  }
  if (x === en) return { beginning: bEx, ending: enX, ok: false };
  x = en;
  ncyc = 0;
  for (; ; ) {
    const h1 = at(x, hi1);
    const h2 = at(x, hi2);
    const loV = at(x, lo);
    if (h1 !== GAP3 && h2 !== GAP3 && loV !== GAP3) {
      if (h1 !== h2 && h1 === loV) {
        enX = x;
        break;
      }
    }
    x++;
    if (x > L) {
      if (circularFlag === 1) {
        x = 1;
        if (sen > 0 && isMissing(x)) {
          enX = L;
          break;
        }
        ncyc++;
        if (ncyc === 2) return { beginning: bEx, ending: enX, ok: false };
      } else {
        enX = L;
        break;
      }
    } else if (isMissing(x)) {
      let cycle = 0;
      while (isMissing(x)) {
        x--;
        if (x === en) return { beginning: bEx, ending: enX, ok: false };
        if (x < 1) x = L;
        if (x === en) return { beginning: bEx, ending: enX, ok: false };
      }
      enX = x;
      break;
    }
    if (x === be || x === en) return { beginning: bEx, ending: enX, ok: false };
  }
  x = enX;
  ncyc = 0;
  for (; ; ) {
    const h1 = at(x, hi1);
    const h2 = at(x, hi2);
    const loV = at(x, lo);
    if (h1 !== GAP3 && h2 !== GAP3 && loV !== GAP3) {
      if (h1 === h2 && h1 !== loV) {
        enX = x;
        break;
      }
    }
    x--;
    if (x < 1) {
      if (circularFlag === 1) {
        x = L;
        if (sen > 0 && isMissing(x)) {
          enX = L;
          break;
        }
        ncyc++;
        if (ncyc === 2) return { beginning: bEx, ending: enX, ok: false };
      } else {
        enX = L;
        break;
      }
    } else if (isMissing(x)) {
      let cycle = 0;
      while (isMissing(x)) {
        x--;
        if (x < 1) {
          x = L;
          cycle++;
          if (cycle === 2) return { beginning: bEx, ending: enX, ok: false };
        }
      }
      enX = x;
      break;
    }
    if (x === be || x === bEx) return { beginning: bEx, ending: enX, ok: false };
  }
  return { beginning: bEx, ending: enX, ok: true };
}

// src/engine/bootscan.ts
var fr = Math.fround;
function resolveBsOptions(aln, o, nTriplets) {
  let stepWin = o.stepWin ?? 200;
  let stepSize = o.stepSize ?? 20;
  const L = aln.length;
  if (stepWin > L / 2) {
    stepWin = vbCLng(L / 2);
    if (stepWin < 5) return null;
  }
  if (stepSize > L / 4) {
    stepSize = vbCLng(L / 4);
    if (stepSize < 1) stepSize = 1;
  }
  const mc = o.mcCorrection && o.mcCorrection > 0 ? o.mcCorrection : nTriplets && nTriplets > 0 ? nTriplets : mcCorrectionFor(aln.nSeqs);
  let subModel = o.subModelFlag ?? 0;
  if (subModel !== 0 && subModel !== 1 && subModel !== 2 && subModel !== 3) subModel = 0;
  const typeFlag = o.typeFlag ?? 0;
  return {
    lowestProb: o.lowestProb ?? 0.05,
    mcFlag: o.mcFlag ?? 0,
    mcCorrection: mc,
    circularFlag: o.circularFlag ?? 0,
    stepWin,
    stepSize,
    bootReps: o.bootReps ?? 100,
    cutOff: o.cutOff ?? 0.7,
    pValFlag: o.pValFlag ?? 1,
    rndNumSeed: o.rndNumSeed ?? 3,
    longWindedFlag: o.longWindedFlag ?? 1,
    roleTracker: o.roleTracker ?? null,
    findallFlag: o.findallFlag ?? 0,
    subModelFlag: subModel,
    typeFlag: typeFlag >= 0 && typeFlag <= 4 ? typeFlag : 0,
    ttRatio: o.ttRatio ?? 2,
    coeffVar: o.coeffVar && o.coeffVar > 0 ? o.coeffVar : 1,
    freqFlag: o.freqFlag ?? 0,
    freqA: o.freqA ?? 0.25,
    freqC: o.freqC ?? 0.25,
    freqG: o.freqG ?? 0.25,
    freqT: o.freqT ?? 0.25
  };
}
var MsvcRand = class {
  s;
  static RAND_MAX = 32767;
  constructor(seed) {
    this.s = seed >>> 0;
  }
  rand() {
    this.s = Math.imul(this.s, 214013) + 2531011 >>> 0;
    return this.s >>> 16 & 32767;
  }
};
var seqboot2Cache = /* @__PURE__ */ new Map();
var seqboot2ColSumByW = /* @__PURE__ */ new WeakMap();
function seqboot2ColSum(weights) {
  return seqboot2ColSumByW.get(weights);
}
function seqboot2(seed, reps, win) {
  const key = `${seed >>> 0}:${reps}:${win}`;
  const hit = seqboot2Cache.get(key);
  if (hit) return hit;
  const R = reps + 1;
  const w = new Int32Array(R * win);
  const rng = new MsvcRand(seed);
  const rm = MsvcRand.RAND_MAX;
  rng.rand();
  for (let x = 1; x <= win; x++) w[(x - 1) * R] = 1;
  const bs2 = win - 1;
  rng.rand();
  for (let x = 1; x <= win; x++) {
    for (let y = 1; y <= reps; y++) {
      const rn = rng.rand();
      const rfx = Math.trunc(rn / rm * bs2);
      w[y + rfx * R]++;
    }
  }
  const colSum = new Int32Array(R);
  for (let site = 0; site < win; site++) {
    const off = site * R;
    for (let a = 0; a < R; a++) colSum[a] += w[off + a];
  }
  seqboot2ColSumByW.set(w, colSum);
  if (seqboot2Cache.size > 32) {
    seqboot2Cache.clear();
  }
  seqboot2Cache.set(key, w);
  return w;
}
function makeSubAlign(seqs, lenseq, winnum, stepsize, winsize, out, seqnum) {
  const os = winnum * stepsize - Math.trunc(winsize / 2);
  for (let y = 0; y < 3; y++) {
    const so = seqs[y] * (lenseq + 1);
    const oo = y * (winsize + 1);
    for (let x = 1; x <= winsize; x++) {
      let pos;
      if (os >= 1 && os <= lenseq - winsize) pos = x + os;
      else if (os > 1) pos = x + os <= lenseq ? x + os : x + os - lenseq;
      else pos = x + os > 0 ? x + os : x + os + lenseq;
      out[x + oo] = seqnum[pos + so];
    }
  }
}
function bootDistFill(df, reps, R, valid, diffs, dst, validIsColSum, useJc) {
  for (let p = 0; p < 3; p++) {
    const base = p * R;
    for (let a = df; a <= reps; a++) {
      const idx = base + a;
      const v = validIsColSum ? valid[a] : valid[idx];
      let d;
      if (v > 0) {
        const th1 = fr(diffs[idx]);
        let th2 = fr(v);
        const id = fr(fr(th2 - th1) / th2);
        if (id > 0.25) {
          if (useJc) {
            th2 = fr((4 * id - 1) / 3);
            d = fr(-0.75 * fr(Math.log(th2)));
          } else {
            d = fr(1 - id);
          }
        } else d = 10;
      } else d = 10;
      dst[idx] = d;
    }
  }
}
function fastBootDistIPGapless(df, reps, lenseq, tseq, weightmod, colSum, dst, diffs, useJc = true) {
  const R = reps + 1;
  const R2 = R * 2;
  const nSlot = 3 * R;
  for (let i = 0; i < nSlot; i++) diffs[i] = 0;
  const o1 = lenseq + 1;
  const o2 = 2 * (lenseq + 1);
  for (let z = 1; z <= lenseq; z++) {
    const a0 = tseq[z];
    const a1 = tseq[z + o1];
    const a2 = tseq[z + o2];
    const off3 = R * (z - 1);
    if (a0 !== a1) {
      for (let a = df; a <= reps; a++) diffs[a] += weightmod[a + off3];
    }
    if (a0 !== a2) {
      for (let a = df; a <= reps; a++) diffs[R + a] += weightmod[a + off3];
    }
    if (a1 !== a2) {
      for (let a = df; a <= reps; a++) diffs[R2 + a] += weightmod[a + off3];
    }
  }
  bootDistFill(df, reps, R, colSum, diffs, dst, true, useJc);
}
function fastBootDistIP(df, reps, lenseq, tseq, weightmod, dst, valid, diffs, colSum, useJc = true) {
  const R = reps + 1;
  const R2 = R * 2;
  const o1 = lenseq + 1;
  const o2 = 2 * (lenseq + 1);
  let hasGap = false;
  for (let z = 1; z <= lenseq; z++) {
    if (tseq[z] === GAP || tseq[z + o1] === GAP || tseq[z + o2] === GAP) {
      hasGap = true;
      break;
    }
  }
  if (!hasGap) {
    const cs = colSum ?? seqboot2ColSum(weightmod);
    if (cs) {
      fastBootDistIPGapless(df, reps, lenseq, tseq, weightmod, cs, dst, diffs, useJc);
      return;
    }
  }
  const nSlot = 3 * R;
  for (let i = 0; i < nSlot; i++) {
    valid[i] = 0;
    diffs[i] = 0;
  }
  for (let z = 1; z <= lenseq; z++) {
    const a0 = tseq[z];
    const a1 = tseq[z + o1];
    const a2 = tseq[z + o2];
    const off3 = R * (z - 1);
    if (a0 !== GAP && a1 !== GAP && a2 !== GAP) {
      const m01 = a0 !== a1;
      const m02 = a0 !== a2;
      const m12 = a1 !== a2;
      for (let a = df; a <= reps; a++) {
        const wv = weightmod[a + off3];
        valid[a] += wv;
        valid[R + a] += wv;
        valid[R2 + a] += wv;
        if (m01) diffs[a] += wv;
        if (m02) diffs[R + a] += wv;
        if (m12) diffs[R2 + a] += wv;
      }
      continue;
    }
    if (a0 !== GAP) {
      if (a0 === a1) {
        for (let a = df; a <= reps; a++) valid[a] += weightmod[a + off3];
      } else if (a1 !== GAP) {
        for (let a = df; a <= reps; a++) {
          const wv = weightmod[a + off3];
          valid[a] += wv;
          diffs[a] += wv;
        }
      }
      if (a0 === a2) {
        for (let a = df; a <= reps; a++) valid[R + a] += weightmod[a + off3];
      } else if (a2 !== GAP) {
        for (let a = df; a <= reps; a++) {
          const wv = weightmod[a + off3];
          valid[R + a] += wv;
          diffs[R + a] += wv;
        }
      }
    }
    if (a1 !== GAP) {
      if (a1 === a2) {
        for (let a = df; a <= reps; a++) valid[R2 + a] += weightmod[a + off3];
      } else if (a2 !== GAP) {
        for (let a = df; a <= reps; a++) {
          const wv = weightmod[a + off3];
          valid[R2 + a] += wv;
          diffs[R2 + a] += wv;
        }
      }
    }
  }
  bootDistFill(df, reps, R, valid, diffs, dst, false, useJc);
}
var NT_A = 66;
var NT_C = 68;
var NT_G = 72;
var NT_T = 85;
function ntCode(b) {
  if (b === NT_A) return 0;
  if (b === NT_C) return 1;
  if (b === NT_G) return 2;
  if (b === NT_T) return 3;
  return 4;
}
function bootDistKimura(num1, num2, den, ttratio, cvi = 1, tmodel = 1) {
  if (den === 0 || num1 === 0) return 10;
  let aa = ttratio * 0.25 - 0.25;
  let xi = aa / (aa + 0.5);
  let xv = 1 - xi;
  if (xi < 0) {
    xi = 0.6;
    xv = 0.4;
  }
  const fracchange = xi * 0.5 + xv * 0.75;
  let tt = 1 - num1 / den;
  if (!(tt > 0)) return 10;
  let delta = 0.1;
  tt = delta;
  for (let it = 0; it < 1e3 && Math.abs(delta) > 2e-5; it++) {
    let p1, p2, p3;
    if (tmodel === 1) {
      p1 = Math.exp(-tt);
      p2 = Math.exp(-xv * tt) - Math.exp(-tt);
      p3 = 1 - Math.exp(-xv * tt);
    } else {
      p1 = Math.exp(-cvi * Math.log(1 + tt / cvi));
      p2 = Math.exp(-cvi * Math.log(1 + xv * tt / cvi)) - Math.exp(-cvi * Math.log(1 + tt / cvi));
      p3 = 1 - Math.exp(-cvi * Math.log(1 + xv * tt / cvi));
    }
    const q1 = p1 + p2 / 2 + p3 / 4;
    const q2 = p2 / 2 + p3 / 4;
    const q3 = p3 / 2;
    let slope;
    if (tmodel === 1) {
      const th1 = 0.5 * Math.exp(-tt) * (num2 / q2 - num1 / q1);
      const th2 = 0.25 * xv * Math.exp(-xv * tt);
      const th3 = (den - num1 - num2) * 2 / q3 - num2 / q2 - num1 / q1;
      slope = th1 + th2 * th3;
    } else {
      const th1 = 0.5 * (1 / (1 + tt / cvi)) * Math.exp(-cvi * Math.log(1 + tt / cvi)) * (num2 / q2 - num1 / q1);
      const th2 = 0.25 * (xv / (1 + xv * tt / cvi)) * Math.exp(-cvi * Math.log(1 + xv * tt / cvi));
      const th3 = (den - num1 - num2) * 2 / q3 - num2 / q2 - num1 / q1;
      slope = th1 + th2 * th3;
    }
    delta = slope < 0 ? Math.abs(delta) / -2 : Math.abs(delta);
    tt += delta;
  }
  return fracchange * tt;
}
function logDetDistance(joint) {
  let tot = 0;
  for (let i = 0; i < 16; i++) tot += joint[i];
  if (tot <= 0) return 10;
  const F = new Float64Array(16);
  for (let i = 0; i < 16; i++) F[i] = joint[i] / tot;
  const M = Float64Array.from(F);
  let det = 1;
  for (let i = 0; i < 4; i++) {
    let piv = i;
    for (let r = i + 1; r < 4; r++) if (Math.abs(M[r + 4 * i]) > Math.abs(M[piv + 4 * i])) piv = r;
    if (Math.abs(M[piv + 4 * i]) < 1e-12) return 10;
    if (piv !== i) {
      for (let c = 0; c < 4; c++) {
        const tmp = M[i + 4 * c];
        M[i + 4 * c] = M[piv + 4 * c];
        M[piv + 4 * c] = tmp;
      }
      det = -det;
    }
    const pivV = M[i + 4 * i];
    det *= pivV;
    for (let r = i + 1; r < 4; r++) {
      const f = M[r + 4 * i] / pivV;
      for (let c = i; c < 4; c++) M[r + 4 * c] -= f * M[i + 4 * c];
    }
  }
  if (!(det > 0)) return 10;
  const row = [0, 0, 0, 0];
  const col = [0, 0, 0, 0];
  for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      row[i] += F[i + 4 * j];
      col[j] += F[i + 4 * j];
    }
  }
  let g = 1;
  for (let i = 0; i < 4; i++) {
    if (row[i] <= 0 || col[i] <= 0) return 10;
    g *= row[i] * col[i];
  }
  const d = -0.25 * Math.log(det) + 0.125 * Math.log(g);
  return Number.isFinite(d) && d >= 0 ? d : 10;
}
function f84Distance(sites, freq, ttratio) {
  const [freqa, freqc, freqg, freqt] = freq;
  const freqr = freqa + freqg;
  const freqy = freqc + freqt;
  if (freqr <= 0 || freqy <= 0) return 10;
  const freqar = freqa / freqr;
  const freqcy = freqc / freqy;
  const freqgr = freqg / freqr;
  const freqty = freqt / freqy;
  let aa = ttratio * freqr * freqy - freqa * freqg - freqc * freqt;
  const bb = freqa * freqgr + freqc * freqty;
  let xi = aa / (aa + bb);
  let xv = 1 - xi;
  if (xi < 0) {
    xi = 0.6;
    xv = 0.4;
  }
  const fracchange = xi * (2 * freqa * freqgr + 2 * freqc * freqty) + xv * (1 - freqa * freqa - freqc * freqc - freqg * freqg - freqt * freqt);
  const rat = 1;
  const ratxv = xv;
  const prod = [];
  const prod2 = [];
  const prod3 = [];
  const weights = [];
  for (const s of sites) {
    if (s.h1 >= 4 || s.h2 >= 4) continue;
    const xx1 = [0, 0, 0, 0];
    const xx2 = [0, 0, 0, 0];
    xx1[s.h1] = 1;
    xx2[s.h2] = 1;
    const xx1fa = xx1[0] * freqa;
    const xx1fc = xx1[1] * freqc;
    const xx1fg = xx1[2] * freqg;
    const xx1ft = xx1[3] * freqt;
    const sum1 = xx1fa + xx1fc + xx1fg + xx1ft;
    const sum2 = freqa * xx2[0] + freqc * xx2[1] + freqg * xx2[2] + freqt * xx2[3];
    prod.push(sum1 * sum2);
    prod2.push((xx1fa + xx1fg) * (xx2[0] * freqar + xx2[2] * freqgr) + (xx1fc + xx1ft) * (xx2[1] * freqcy + xx2[3] * freqty));
    prod3.push(xx1fa * xx2[0] + xx1fc * xx2[1] + xx1fg * xx2[2] + xx1ft * xx2[3]);
    weights.push(s.w);
  }
  if (prod.length === 0) return 10;
  let tt = 0.1;
  let delta = 0.1;
  for (let it = 0; it < 1e3 && Math.abs(delta) > 2e-5; it++) {
    let slope = 0;
    if (tt > 0) {
      const lz = -tt;
      const z1 = Math.exp(ratxv * lz);
      const y1 = 1 - z1;
      const z1zz = Math.exp(rat * lz);
      const z1yy = z1 - z1zz;
      const z1xv = z1 * xv;
      for (let i = 0; i < prod.length; i++) {
        const cc = prod[i];
        const bb2 = prod2[i];
        const aa2 = prod3[i];
        const den = aa2 * z1zz + bb2 * z1yy + cc * y1;
        if (den !== 0) slope += weights[i] * (z1zz * (bb2 - aa2) + z1xv * (cc - bb2)) / den;
      }
    }
    delta = slope < 0 ? Math.abs(delta) / -2 : Math.abs(delta);
    tt += delta;
  }
  const vv = tt * fracchange;
  return Number.isFinite(vv) && vv >= 0 ? vv : 10;
}
function bootDistTriplet(reps, lenseq, tseq, weightmod, dst, opts) {
  const R = reps + 1;
  if (opts.subModel === 0) {
    const valid = new Int32Array(3 * R);
    const diffs = new Int32Array(3 * R);
    fastBootDistIP(0, reps, lenseq, tseq, weightmod, dst, valid, diffs);
    return;
  }
  const o0 = 0;
  const o1 = lenseq + 1;
  const o2 = 2 * (lenseq + 1);
  const pairs = [
    [o0, o1],
    [o0, o2],
    [o1, o2]
  ];
  let freq = [opts.freqA, opts.freqC, opts.freqG, opts.freqT];
  if (opts.subModel === 3 && opts.freqFlag === 0) {
    const cnt = [0, 0, 0, 0];
    let n = 0;
    for (const oo of [o0, o1, o2]) {
      for (let z = 1; z <= lenseq; z++) {
        const c = ntCode(tseq[z + oo]);
        if (c < 4) {
          cnt[c]++;
          n++;
        }
      }
    }
    if (n > 0) freq = [cnt[0] / n, cnt[1] / n, cnt[2] / n, cnt[3] / n];
  }
  for (let p = 0; p < 3; p++) {
    const [oa, ob] = pairs[p];
    for (let a = 0; a <= reps; a++) {
      if (opts.subModel === 1) {
        let num1 = 0;
        let num2 = 0;
        let den = 0;
        for (let z = 1; z <= lenseq; z++) {
          const h1 = ntCode(tseq[z + oa]);
          const h2 = ntCode(tseq[z + ob]);
          if (h1 >= 4 || h2 >= 4) continue;
          const w = weightmod[a + (z - 1) * R];
          if (w === 0) continue;
          const same = h1 === h2 ? 1 : 0;
          const ry = (h1 === 0 || h1 === 2) && (h2 === 0 || h2 === 2) || (h1 === 1 || h1 === 3) && (h2 === 1 || h2 === 3) ? 1 : 0;
          num1 += w * same;
          num2 += w * (ry - same);
          den += w;
        }
        dst[p * R + a] = fr(bootDistKimura(num1, num2, den, opts.ttRatio, opts.coeffVar, 1));
      } else if (opts.subModel === 2) {
        const joint = new Float64Array(16);
        for (let z = 1; z <= lenseq; z++) {
          const h1 = ntCode(tseq[z + oa]);
          const h2 = ntCode(tseq[z + ob]);
          if (h1 >= 4 || h2 >= 4) continue;
          const w = weightmod[a + (z - 1) * R];
          if (w === 0) continue;
          joint[h1 + 4 * h2] += w;
        }
        dst[p * R + a] = fr(logDetDistance(joint));
      } else {
        const sites = [];
        for (let z = 1; z <= lenseq; z++) {
          const h1 = ntCode(tseq[z + oa]);
          const h2 = ntCode(tseq[z + ob]);
          const w = weightmod[a + (z - 1) * R];
          if (w === 0) continue;
          sites.push({ h1, h2, w });
        }
        dst[p * R + a] = fr(f84Distance(sites, freq, opts.ttRatio));
      }
    }
  }
}
function applyBsTreeDistances(dst, reps, typeFlag) {
  if (typeFlag <= 0) return;
  const R = reps + 1;
  const useUPGMA = typeFlag === 1;
  for (let a = 0; a < reps; a++) {
    const mat = new Float32Array(16);
    const d01 = dst[a];
    const d02 = dst[R + a];
    const d12 = dst[2 * R + a];
    mat[0 + 1 * 4] = mat[1] = d01;
    mat[0 + 2 * 4] = mat[2] = d02;
    mat[1 + 2 * 4] = mat[2 + 1 * 4] = d12;
    for (let y = 0; y < 3; y++) {
      mat[y + 3 * 4] = 6;
      mat[3 + y * 4] = 6;
    }
    try {
      const tree = useUPGMA ? buildUPGMATree(mat, 4) : buildNJTree(mat, 4, { outgroup: 3 });
      const pat = patristicMatrix(tree, { clamp: false });
      dst[a] = pat[0 + 1 * 4];
      dst[R + a] = pat[0 + 2 * 4];
      dst[2 * R + a] = pat[1 + 2 * 4];
    } catch {
    }
  }
}
function getPltValX(b, reps, dst, pltVal) {
  const R = reps + 1;
  const o0 = b * 3;
  for (let x = 0; x < reps; x++) {
    const d0 = dst[x];
    const d1 = dst[R + x];
    const d2 = dst[2 * R + x];
    if (d0 < 2 && d1 < 2 && d2 < 2) {
      if (d0 < d1 && d0 < d2) pltVal[o0] += 1;
      else if (d1 < d0 && d1 < d2) pltVal[o0 + 1] += 1;
      else if (d2 < d0 && d2 < d1) pltVal[o0 + 2] += 1;
    }
  }
}
function bsOrderArray(d12, d13, d23) {
  if (d12 >= d13 && d12 >= d23) return 0;
  if (d13 >= d12 && d13 >= d23) return 1;
  return 2;
}
function scanPositiveWindow(winnum, cutOff, cocount, bootreps, order, dst, goOn) {
  const R = bootreps + 1;
  let hisLos1Pair;
  let hisLos2Pair;
  let los1Los2Pair;
  if (order === 0) {
    hisLos1Pair = 0;
    hisLos2Pair = 1;
    los1Los2Pair = 2;
  } else if (order === 1) {
    hisLos1Pair = 1;
    hisLos2Pair = 0;
    los1Los2Pair = 2;
  } else {
    hisLos1Pair = 2;
    hisLos2Pair = 0;
    los1Los2Pair = 1;
  }
  const hislos1 = dst[0 + hisLos1Pair * R];
  const hislos2 = dst[0 + hisLos2Pair * R];
  const los1los2 = dst[0 + los1Los2Pair * R];
  if (!(hislos1 > los1los2 || hislos1 > hislos2)) return;
  const co = cutOff * bootreps | 0;
  let fcount = 0;
  let l1 = 1;
  let l2 = 1;
  for (let a = 1; a < bootreps; a++) {
    const h1 = dst[a + hisLos1Pair * R];
    const h2 = dst[a + hisLos2Pair * R];
    const l12 = dst[a + los1Los2Pair * R];
    if (h1 < l12 && h1 < h2) {
      fcount++;
      if (fcount > cocount) break;
    } else if (l12 < h2) l1++;
    else if (l12 > h2) l2++;
  }
  if (fcount <= cocount && (l1 >= co || l2 >= co)) {
    if (goOn.goOnA === 0) goOn.goOnA = winnum;
    goOn.goOnB = winnum;
  }
}
function expandGoOnRange(goOnA, goOnB, numWins, overlapNum, findallFlag) {
  if (findallFlag !== 0) {
    return { goOnA: 1, goOnB: Math.max(1, numWins - 1) };
  }
  if (goOnA <= 0) return null;
  const a = goOnA > overlapNum ? goOnA - overlapNum : 1;
  const b = goOnB + overlapNum < numWins ? goOnB + overlapNum : numWins;
  return { goOnA: a, goOnB: b };
}
function bsSubSeq(lenseq, seq1, seq2, seq3, sn, xposdiff, xdiffpos, scores) {
  let y = 0;
  const os1 = lenseq + 1;
  const os2 = 2 * os1;
  for (let x = 1; x <= lenseq; x++) {
    const s1 = sn[x + seq1 * os1];
    const s2 = sn[x + seq2 * os1];
    const s3 = sn[x + seq3 * os1];
    xposdiff[x] = y;
    if (s1 !== GAP && s2 !== GAP && s3 !== GAP) {
      if (s1 !== s2 || s1 !== s3 || s2 !== s3) {
        y++;
        scores[y] = 0;
        scores[y + os1] = 0;
        scores[y + os2] = 0;
        if (s1 === s2) scores[y] = 1;
        else if (s1 === s3) scores[y + os1] = 1;
        else if (s2 === s3) scores[y + os2] = 1;
        xdiffpos[y] = x;
        xposdiff[x] = y;
      }
    }
  }
  return y;
}
function makeScoresBS(lenXOverSeq, scoreP, LS, be, EN, xposdiff, scores) {
  const os2 = scoreP * (LS + 1);
  let A = 0;
  let C = 0;
  let XOverLen;
  const xb = xposdiff[be] | 0;
  const xe = xposdiff[EN] | 0;
  if (be < EN) {
    XOverLen = xe - xb + 1;
    for (let X = xb; X <= xe; X++) A += scores[X + os2];
    for (let X = 1; X <= xb - 1; X++) C += scores[X + os2];
    for (let X = xe + 1; X <= lenXOverSeq; X++) C += scores[X + os2];
  } else {
    XOverLen = xe + (lenXOverSeq - xb) + 1;
    for (let X = xe + 1; X <= xb - 1; X++) C += scores[X + os2];
    for (let X = 1; X <= xe; X++) A += scores[X + os2];
    for (let X = xb; X <= lenXOverSeq; X++) A += scores[X + os2];
  }
  return { xOverLen: XOverLen, a: A, c: C };
}
function pv(p, pair, win) {
  const v = p[pair + win * 3];
  return v === void 0 ? 0 : v;
}
function findBeginBS(circularFlag, stepSize, stepWin, med, high, low, numwins, cutOff, reps, posCount, overlapNum, yVal, curPos0, plt) {
  let ProbCounter = 0;
  let CurPos = curPos0;
  let TotalProb = 0;
  let Y = 0;
  let LastFull = 0;
  let guard = 0;
  const limit = 20 * (numwins + 5);
  while (CurPos >= 0 && CurPos >= posCount - overlapNum) {
    if (guard++ > limit) break;
    if (pv(plt, med, CurPos) < cutOff * reps) {
      let GoOnFlag = 0;
      for (let Z = 0; Z <= overlapNum; Z++) {
        Y = CurPos - Z;
        if (Y === posCount) {
          return { curPos: CurPos, totalProb: TotalProb, probCounter: ProbCounter, lastFull: LastFull, yVal: yVal + stepWin + stepSize + 1, ok: false };
        }
        if (Y < 1) Y = Y + numwins - 1;
        if (pv(plt, med, Y) <= pv(plt, high, Y) || pv(plt, med, Y) <= pv(plt, low, Y) || pv(plt, med, Y) <= 0.4 * reps) {
          GoOnFlag = 0;
          break;
        } else if (pv(plt, med, Y) >= cutOff * reps) {
          GoOnFlag = 1;
          CurPos = Y;
          break;
        }
        ProbCounter++;
        TotalProb += pv(plt, med, CurPos - 1) / reps;
      }
      if (GoOnFlag === 0) {
        if (Y === CurPos && pv(plt, med, Y) <= 0.4 * reps) CurPos++;
        break;
      }
    } else LastFull = CurPos;
    if (pv(plt, med, CurPos) <= pv(plt, high, CurPos) || pv(plt, med, CurPos) <= pv(plt, low, CurPos) || pv(plt, med, CurPos) <= 0.5 * reps) {
      if (pv(plt, med, Y) <= 0.4 * reps) CurPos++;
      break;
    }
    ProbCounter++;
    TotalProb = TotalProb + pv(plt, med, CurPos - 1) / reps;
    CurPos--;
    if (CurPos === posCount) {
      return { curPos: CurPos, totalProb: TotalProb, probCounter: ProbCounter, lastFull: LastFull, yVal: yVal + stepWin + stepSize + 1, ok: false };
    }
    if (CurPos < 1) {
      if (circularFlag === 1) CurPos = numwins - 1;
      else {
        CurPos = 1;
        break;
      }
    }
  }
  return { curPos: CurPos, totalProb: TotalProb, probCounter: ProbCounter, lastFull: LastFull, yVal, ok: true };
}
function findEndBS(Y, cutOff, reps, numwins, overlapNum, med, high, low, gbcc, lastFull0, probCounter0, curPos0, totalProb0, plt) {
  let TotalProb = totalProb0;
  let LastFull = lastFull0;
  let CurPos = curPos0;
  let ProbCounter = probCounter0;
  let guard = 0;
  const limit = 20 * (numwins + 5);
  while (CurPos <= gbcc - 1) {
    if (guard++ > limit) break;
    if (pv(plt, med, CurPos) < cutOff * reps) {
      let GoOnFlag = 0;
      for (let Z = 1; Z <= overlapNum; Z++) {
        if (CurPos + Z <= numwins) {
          const w = CurPos + Z;
          if (pv(plt, med, w) <= pv(plt, high, w) || pv(plt, med, w) <= pv(plt, low, w) || pv(plt, med, w) <= 0.4 * reps) {
            GoOnFlag = 0;
            break;
          } else if (pv(plt, med, w) >= cutOff * reps) {
            GoOnFlag = 1;
            CurPos++;
            break;
          }
        } else break;
        ProbCounter++;
        TotalProb = TotalProb + pv(plt, med, CurPos - 1) / reps;
      }
      if (GoOnFlag === 0) {
        if (Y === CurPos && pv(plt, med, Y) <= 0.4 * reps) CurPos--;
        break;
      }
    } else LastFull = CurPos;
    ProbCounter++;
    TotalProb = TotalProb + pv(plt, med, CurPos - 1) / reps;
    CurPos++;
  }
  return { curPos: CurPos, lastFull: LastFull, probCounter: ProbCounter, totalProb: TotalProb };
}
var BootscanContext = class {
  aln;
  o;
  dist;
  weights;
  /** Per-rep Σ WeightMod — gapless FastBootDist valid[]. */
  weightColSum;
  fact;
  /** CurrentXOver / StoreLPV for ScanBSPlots ActiveSeq (Module30 ~23742–23787). */
  roleTracker;
  // workspaces
  tseq;
  dst;
  valid;
  diffs;
  xPosDiff;
  xDiffPos;
  scores;
  /** Reused plot buffers (sized lazily to numWins). */
  pltBuf = null;
  pltPosBuf = null;
  /** Per-context plot cache: exact (s1,s2,s3) → plot (harvest repeats parents). */
  plotCache = null;
  constructor(aln, o, dist, roleTracker) {
    this.aln = aln;
    this.o = o;
    this.dist = dist;
    this.roleTracker = roleTracker ?? createRoleTracker(aln.nSeqs);
    this.weights = seqboot2(o.rndNumSeed, o.bootReps, o.stepWin);
    this.weightColSum = seqboot2ColSum(this.weights) ?? null;
    this.fact = makeFactTable();
    this.tseq = new Int16Array(3 * (o.stepWin + 1));
    this.dst = new Float32Array(3 * (o.bootReps + 1));
    this.valid = new Int32Array(3 * (o.bootReps + 1));
    this.diffs = new Int32Array(3 * (o.bootReps + 1));
    this.xPosDiff = new Int32Array(aln.length + 202);
    this.xDiffPos = new Int32Array(aln.length + 202);
    this.scores = new Int8Array((aln.length + 1) * 3 + 4);
  }
};
function bootscanPlot(c, s1, s2, s3) {
  const cacheKey = `${s1},${s2},${s3}`;
  if (c.plotCache) {
    const hit = c.plotCache.get(cacheKey);
    if (hit) return hit;
  }
  const L = c.aln.length;
  const { stepSize, stepWin, bootReps, cutOff, subModelFlag, typeFlag } = c.o;
  const numWins = Math.floor(L / stepSize) + 2;
  const needPos = numWins + 2;
  const needPlt = 3 * (numWins + 1);
  if (!c.pltPosBuf || c.pltPosBuf.length < needPos) c.pltPosBuf = new Int32Array(needPos);
  if (!c.pltBuf || c.pltBuf.length < needPlt) c.pltBuf = new Float64Array(needPlt);
  const pltPos = c.pltPosBuf;
  const plt = c.pltBuf;
  plt.fill(0, 0, needPlt);
  for (let z = 0; z < numWins; z++) pltPos[z] = vbCLng(stepSize * z);
  const n = c.dist.n;
  const D = c.dist.distance;
  const order = bsOrderArray(D[s1 + n * s2], D[s1 + n * s3], D[s2 + n * s3]);
  const cocount = (1 - cutOff) * bootReps;
  const goOn = { goOnA: 0, goOnB: 0 };
  const winCap = Math.min(numWins, 255);
  const distOpts = {
    subModel: subModelFlag,
    ttRatio: c.o.ttRatio,
    coeffVar: c.o.coeffVar,
    freqFlag: c.o.freqFlag,
    freqA: c.o.freqA,
    freqC: c.o.freqC,
    freqG: c.o.freqG,
    freqT: c.o.freqT
  };
  const colSum = c.weightColSum;
  for (let b = 0; b <= numWins; b++) {
    makeSubAlign([s1, s2, s3], L, b, stepSize, stepWin, c.tseq, c.aln.seqnum);
    if (subModelFlag === 0) {
      fastBootDistIP(0, bootReps, stepWin, c.tseq, c.weights, c.dst, c.valid, c.diffs, colSum, true);
    } else {
      bootDistTriplet(bootReps, stepWin, c.tseq, c.weights, c.dst, distOpts);
    }
    if (typeFlag > 0) applyBsTreeDistances(c.dst, bootReps, typeFlag);
    getPltValX(b, bootReps, c.dst, plt);
    if (b <= winCap) scanPositiveWindow(b, cutOff, cocount, bootReps, order, c.dst, goOn);
  }
  const goOnCopy = { goOnA: goOn.goOnA, goOnB: goOn.goOnB };
  if (c.plotCache) {
    if (c.plotCache.size > 4096) c.plotCache.clear();
    const snap = {
      plt: plt.slice(0, needPlt),
      pltPos: pltPos.slice(0, needPos),
      numWins,
      goOn: goOnCopy,
      order
    };
    c.plotCache.set(cacheKey, snap);
    return snap;
  }
  return { plt, pltPos, numWins, goOn: goOnCopy, order };
}
function makeBSEvent(c, lenXoverSeq, plt, pltPos, numWins, overlapNum, yVal0, posCount0, med, high, low) {
  const { stepSize, stepWin, bootReps, cutOff, circularFlag, pValFlag } = c.o;
  const L = c.aln.length;
  const pp = (i) => i >= 0 && i < pltPos.length ? pltPos[i] : 0;
  let bWarn = 0;
  let eWarn = 0;
  const res = { returned: true, BE: 0, EN: 0, PPVal: -1, PVal: 1e8, yVal: yVal0, posCount: posCount0, bWarn: 0, eWarn: 0, xOverLen: 0 };
  let ProbCounter = 1;
  let TotalProb = pv(plt, med, posCount0) / bootReps;
  let CurPos = posCount0;
  const FirstFull = posCount0;
  let LastFull = posCount0;
  const EraseAll = 0;
  const fb = findBeginBS(circularFlag, stepSize, stepWin, med, high, low, numWins, cutOff, bootReps, posCount0, overlapNum, yVal0, CurPos, plt);
  if (!fb.ok) {
    res.PPVal = 1;
    res.PVal = 1e8;
    res.yVal = fb.yVal;
    return res;
  }
  CurPos = fb.curPos;
  TotalProb = fb.totalProb;
  ProbCounter = fb.probCounter;
  LastFull = fb.lastFull;
  res.yVal = fb.yVal;
  if (CurPos < 0) CurPos = 0;
  let Backtrack = vbCLng(stepWin / 2 / stepSize);
  let bCurPos;
  if (FirstFull < Backtrack) {
    if (circularFlag === 1) bCurPos = FirstFull - Backtrack + numWins;
    else bCurPos = 1;
  } else bCurPos = FirstFull - Backtrack;
  let BE;
  if (circularFlag === 0 && pp(bCurPos) < pp(CurPos) && pv(plt, med, bCurPos) >= pv(plt, high, bCurPos) && pv(plt, med, bCurPos) >= pv(plt, low, bCurPos) && pv(plt, med, bCurPos) >= 0.5 * bootReps || circularFlag === 1 && EraseAll === 1) {
    BE = pp(bCurPos);
    if (FirstFull === 0) {
      if (circularFlag === 0) bWarn = 1;
    } else if (pv(plt, 0, FirstFull - 1) === 0 && pv(plt, 1, FirstFull - 1) === 0 && pv(plt, 2, FirstFull - 1) === 0) bWarn = 1;
  } else {
    BE = pp(CurPos);
    if (CurPos === 0) {
      if (circularFlag === 0) bWarn = 1;
    } else if (pv(plt, 0, CurPos - 1) === 0 && pv(plt, 1, CurPos - 1) === 0 && pv(plt, 2, CurPos - 1) === 0) bWarn = 1;
  }
  if (BE < 1) BE = circularFlag === 0 ? 1 : L + BE;
  CurPos = posCount0;
  const fe = findEndBS(0, cutOff, bootReps, numWins, overlapNum, med, high, low, numWins - 1, LastFull, ProbCounter, CurPos, TotalProb, plt);
  CurPos = fe.curPos;
  LastFull = fe.lastFull;
  ProbCounter = fe.probCounter;
  TotalProb = fe.totalProb;
  if (CurPos > numWins) CurPos = numWins;
  Backtrack = vbCLng(stepWin / 2 / stepSize);
  if (LastFull + Backtrack > numWins) {
    if (circularFlag === 1) bCurPos = LastFull + Backtrack - numWins;
    else bCurPos = numWins;
  } else bCurPos = LastFull + Backtrack;
  let EN;
  if (circularFlag === 0 && pp(bCurPos) > pp(CurPos) && pv(plt, med, bCurPos) >= pv(plt, high, bCurPos) && pv(plt, med, bCurPos) >= pv(plt, low, bCurPos) && pv(plt, med, bCurPos) >= 0.5 * bootReps || circularFlag === 1 && EraseAll === 1) {
    EN = pp(bCurPos);
    if (LastFull === numWins) {
      if (circularFlag === 0) eWarn = 1;
    } else if (pv(plt, 0, LastFull + 1) === 0 && pv(plt, 1, LastFull + 1) === 0 && pv(plt, 2, LastFull + 1) === 0) eWarn = 1;
  } else {
    EN = pp(CurPos);
    if (CurPos === numWins) {
      if (circularFlag === 0) eWarn = 1;
    } else if (pv(plt, 0, CurPos + 1) === 0 && pv(plt, 1, CurPos + 1) === 0 && pv(plt, 2, CurPos + 1) === 0) eWarn = 1;
  }
  if (EN > L) EN = circularFlag === 0 ? L : EN - L;
  let PPVal = ProbCounter === 0 ? 1 : 1 - TotalProb / ProbCounter;
  if (PPVal === 0) PPVal = 1 / (bootReps * 10);
  res.BE = BE;
  res.EN = EN;
  res.PPVal = PPVal;
  res.bWarn = bWarn;
  res.eWarn = eWarn;
  if (BE === EN) return res;
  let PVal;
  if (pValFlag > 0) {
    const scoreP = med;
    const sc = makeScoresBS(lenXoverSeq, scoreP, L, BE, EN, c.xPosDiff, c.scores);
    let A = sc.a;
    let C = sc.c;
    let XOverLen = sc.xOverLen;
    let probabilityXOver;
    if (pValFlag === 1) {
      const indProb = lenXoverSeq - XOverLen > 0 ? (C + A) / lenXoverSeq : 1;
      if (XOverLen > 2) {
        let AFact;
        if (XOverLen >= 170) {
          A = vbCLng(A * 169 / XOverLen);
          AFact = XOverLen / 169;
          XOverLen = 169;
        } else AFact = 1;
        probabilityXOver = probCalcP(c.fact, XOverLen, A, indProb, lenXoverSeq);
        if (probabilityXOver > 1) probabilityXOver = 1;
        probabilityXOver = Math.pow(probabilityXOver, AFact);
      } else probabilityXOver = 1;
    } else {
      if (lenXoverSeq > 0) {
        C = vbCLng(C * (XOverLen / lenXoverSeq));
        const b = XOverLen - A;
        const D = XOverLen - C;
        if (A + C > 0 && b + D > 0) {
          let HMChi = Math.pow(A * D - b * C, 2) * XOverLen * 2;
          HMChi = HMChi / (A + b);
          HMChi = HMChi / (C + D);
          HMChi = HMChi / (A + C);
          HMChi = HMChi / (b + D);
          probabilityXOver = HMChi > 0 ? chiPVal(HMChi) : 1;
        } else probabilityXOver = 1;
      } else probabilityXOver = 1;
    }
    if (c.o.mcFlag === 0) probabilityXOver = probabilityXOver * c.o.mcCorrection;
    if (!(probabilityXOver < c.o.lowestProb && probabilityXOver > 0)) {
      BE = EN;
      res.BE = BE;
    }
    PVal = probabilityXOver;
    res.xOverLen = sc.xOverLen;
  } else {
    PVal = PPVal;
  }
  res.PVal = PVal;
  res.yVal = vbCLng(pp(CurPos) + stepWin / 2);
  res.posCount = CurPos > posCount0 ? CurPos : posCount0;
  return res;
}
function fixEndPoint(v, L, circular) {
  if (v > L) v = circular === 0 ? L : v - L;
  if (v < 1) v = circular === 0 ? 1 : v + L;
  return v;
}
function scanBSPlots(c, s1, s2, s3, plt, pltPos, numWins, goOnRaw, findallOverride) {
  const events = [];
  const o = c.o;
  const findallFlag = findallOverride ?? o.findallFlag;
  const L = c.aln.length;
  const seqs = [s1, s2, s3];
  const members = [
    [s1, s2],
    [s1, s3],
    [s2, s3]
  ];
  const lenXoverSeq = bsSubSeq(L, s1, s2, s3, c.aln.seqnum, c.xPosDiff, c.xDiffPos, c.scores);
  const maps = { xPosDiff: c.xPosDiff, xDiffPos: c.xDiffPos, lenXoverSeq };
  const D = c.dist.distance;
  const n = c.dist.n;
  const d12 = D[s1 + n * s2];
  const d13 = D[s1 + n * s3];
  const d23 = D[s2 + n * s3];
  const av = [d12, d13, d23];
  if (av[0] === av[1] && av[0] === av[2]) {
    if (d12 > d13 && d12 > d23) {
      av[0] += 0.01;
      if (d13 > d23) av[2] -= 0.01;
      else av[1] -= 0.01;
    } else if (d13 > d12 && d13 > d23) {
      av[1] += 0.01;
      if (d12 > d23) av[2] -= 0.01;
      else av[0] -= 0.01;
    } else if (d13 > d13 && d23 > d12) {
      av[2] += 0.01;
      if (d12 > d13) av[1] -= 0.01;
      else av[0] -= 0.01;
    }
  } else if (av[0] === av[1]) {
    if (d12 > d13) av[0] += 0.01;
    else av[1] += 0.01;
  } else if (av[0] === av[2]) {
    if (d12 > d23) av[0] += 0.01;
    else av[2] += 0.01;
  } else if (av[1] === av[2]) {
    if (d13 > d23) av[1] += 0.01;
    else av[2] += 0.01;
  }
  let High, Med, Low;
  if (av[0] >= av[1] && av[0] >= av[2]) {
    High = 0;
    if (av[1] > av[2]) {
      Med = 1;
      Low = 2;
    } else {
      Med = 2;
      Low = 1;
    }
  } else if (av[1] >= av[0] && av[1] >= av[2]) {
    High = 1;
    if (av[0] > av[2]) {
      Med = 0;
      Low = 2;
    } else {
      Med = 2;
      Low = 0;
    }
  } else {
    High = 2;
    if (av[0] > av[1]) {
      Med = 0;
      Low = 1;
    } else {
      Med = 1;
      Low = 0;
    }
  }
  const overlapNum = vbCLng(o.stepWin / o.stepSize);
  const raw = goOnRaw ?? { goOnA: 0, goOnB: 0 };
  const range = expandGoOnRange(raw.goOnA, raw.goOnB, numWins, overlapNum, findallFlag);
  if (!range) return events;
  let posCount = range.goOnA;
  const goOnA = range.goOnA;
  const goOnB = range.goOnB;
  const yEnd = o.stepWin + o.stepSize * goOnB;
  const thr = o.cutOff * o.bootReps;
  let guard = 0;
  for (let Y = o.stepWin + o.stepSize * goOnA; Y <= yEnd; Y += o.stepSize) {
    if (guard++ > 20 * (numWins + 5)) break;
    let PVal = 1e8;
    let r = null;
    let tested = -1;
    if (pv(plt, Med, posCount) >= thr) {
      tested = Med;
      r = makeBSEvent(c, lenXoverSeq, plt, pltPos, numWins, overlapNum, Y, posCount, Med, High, Low);
    } else if (pv(plt, Low, posCount) >= thr) {
      tested = Low;
      r = makeBSEvent(c, lenXoverSeq, plt, pltPos, numWins, overlapNum, Y, posCount, Low, High, Med);
    } else if (pv(plt, High, posCount) >= thr) {
      tested = High;
      r = makeBSEvent(c, lenXoverSeq, plt, pltPos, numWins, overlapNum, Y, posCount, High, Med, Low);
    }
    let BE = 0;
    let EN = 0;
    let PPVal = -1;
    let bWarn = 0;
    let eWarn = 0;
    if (r) {
      BE = r.BE;
      EN = r.EN;
      PPVal = r.PPVal;
      PVal = r.PVal;
      bWarn = r.bWarn;
      eWarn = r.eWarn;
      Y = r.yVal;
      posCount = r.posCount;
    }
    if (o.pValFlag === 0 && PVal < 1 - o.cutOff || o.pValFlag > 0 && PVal > 0 && PVal < o.lowestProb) {
      let beginning = fixEndPoint(BE, L, o.circularFlag);
      let ending = fixEndPoint(EN, L, o.circularFlag);
      const tracker = o.roleTracker ?? c.roleTracker;
      const par = pickActiveLongWinded(seqs[0], seqs[1], seqs[2], tracker);
      const daughter = par.daughter;
      const major = par.majorP;
      const minor = par.minorP;
      if (daughter < 0 || major < 0 || minor < 0 || major === minor || major === daughter || minor === daughter) {
        posCount = posCount + 1;
        if (posCount > numWins) break;
        continue;
      }
      const ev = newXOverEvent(PROGRAM_BOOTSCAN);
      ev.daughter = daughter;
      ev.majorP = major;
      ev.minorP = minor;
      ev.beginning = beginning;
      ev.ending = ending;
      ev.probability = PVal;
      ev.permPVal = PPVal >= 0 ? PPVal : 0;
      ev.dHolder = 0;
      ev.triplet = [seqs[0], seqs[1], seqs[2]];
      ev.maxY = tested;
      ev.loHiFlag = 1;
      ev.lenXoverSeq = lenXoverSeq;
      ev.lHolder = r ? r.xOverLen : 0;
      ev.sbpFlag = (bWarn ? 1 : 0) + (eWarn ? 2 : 0);
      ev.beginWarn = bWarn;
      ev.endWarn = eWarn;
      if (lenXoverSeq >= 2) {
        const cb = centreBreakpoints(c.aln, ev, maps, { circularFlag: o.circularFlag, lss: 10 });
        ev.beginning = cb.beginning;
        ev.ending = cb.ending;
        ev.beginWarn = cb.beginWarn;
        ev.endWarn = cb.endWarn;
        ev.sbpFlag = cb.sbpFlag;
      }
      if (ev.beginning <= ev.ending && major >= 0 && minor >= 0 && daughter >= 0) {
        const shrunk = shrinkRegionBS(c.aln, major, minor, daughter, ev.beginning, ev.ending, {
          circularFlag: o.circularFlag,
          sEventNumber: 0
        });
        if (shrunk.ok && shrunk.beginning <= shrunk.ending) {
          const seedLen = ev.ending - ev.beginning + 1;
          const newLen = shrunk.ending - shrunk.beginning + 1;
          if (newLen >= Math.max(50, seedLen * 0.25) && newLen <= seedLen * 2.5) {
            ev.beginning = shrunk.beginning;
            ev.ending = shrunk.ending;
          }
        }
      }
      noteStoredRole(tracker, daughter, PVal);
      events.push(ev);
    }
    posCount = posCount + 1;
    if (posCount > numWins) break;
  }
  return events;
}
function bootscanTripletCheckingThenFindall(c, s1, s2, s3) {
  const { plt, pltPos, numWins, goOn } = bootscanPlot(c, s1, s2, s3);
  const check = scanBSPlots(c, s1, s2, s3, plt, pltPos, numWins, goOn, 0);
  if (check.length) return check;
  return scanBSPlots(c, s1, s2, s3, plt, pltPos, numWins, goOn, 1);
}

// src/engine/bootscanChecking.ts
function toBsOptions(triplet, opts) {
  return {
    circularFlag: opts.circularFlag ?? 1,
    mcCorrection: opts.mcCorrection ?? 2300,
    lowestProb: opts.lowestProb ?? 0.05,
    stepWin: opts.stepWin ?? 200,
    stepSize: opts.stepSize ?? 20,
    bootReps: opts.bootReps ?? 100,
    cutOff: opts.cutOff ?? 0.7,
    pValFlag: opts.pValFlag ?? 1,
    findallFlag: opts.findallFlag ?? 0,
    triplets: [triplet]
  };
}
function significant(hits, lowestProb) {
  return hits.filter((e) => e.probability > 0 && e.probability <= lowestProb);
}
function makeHarvestCtx(aln, opts, stepWin, stepSize, dist) {
  const o = resolveBsOptions(
    aln,
    {
      ...toBsOptions([0, 1, 2], { ...opts, findallFlag: 0, stepWin, stepSize }),
      distances: dist
    },
    1
  );
  if (!o) return null;
  const ctx = new BootscanContext(aln, o, dist);
  ctx.plotCache = /* @__PURE__ */ new Map();
  return ctx;
}
function harvestOneWithCtx(ctx, triplet, lowest, allowHalf, stepWin, stepSize, opts, aln, dist) {
  const [a, b, c] = triplet;
  const full = significant(bootscanTripletCheckingThenFindall(ctx, a, b, c), lowest);
  if (full.length) return full;
  if (!allowHalf) return [];
  const tryBridge = (win, step) => {
    if (win >= stepWin) return [];
    const bridgeCtx = makeHarvestCtx(aln, opts, win, step, dist);
    if (!bridgeCtx) return [];
    return significant(bootscanTripletCheckingThenFindall(bridgeCtx, a, b, c), lowest);
  };
  const threeQuarterWin = Math.max(20, Math.floor(stepWin * 3 / 4));
  const threeQuarterStep = Math.max(1, Math.floor(stepSize * 3 / 4));
  const bridge34 = tryBridge(threeQuarterWin, threeQuarterStep);
  if (bridge34.length) return bridge34;
  const halfWin = Math.max(20, Math.floor(stepWin / 2));
  const halfStep = Math.max(1, Math.floor(stepSize / 2));
  return tryBridge(halfWin, halfStep);
}
function bootscanHarvestTripletsBatch(aln, trips, opts = {}) {
  const lowest = opts.lowestProb ?? 0.05;
  const stepWin = opts.stepWin ?? 200;
  const stepSize = opts.stepSize ?? 20;
  const allowHalf = opts.allowHalfWindow !== false;
  if (!trips.length) return [];
  const dist = opts.distances ?? calcDistances(aln, minSeqSizeFor(aln.length));
  const ctx = makeHarvestCtx(aln, opts, stepWin, stepSize, dist);
  const out = new Array(trips.length);
  if (!ctx) {
    out.fill([]);
    return out;
  }
  for (let i = 0; i < trips.length; i++) {
    const trip = trips[i];
    const [a, b, c] = trip;
    if ((/* @__PURE__ */ new Set([a, b, c])).size !== 3 || [a, b, c].some((s) => s < 0 || s >= aln.nSeqs)) {
      out[i] = [];
      continue;
    }
    ctx.roleTracker.counts.fill(0);
    ctx.roleTracker.storeLPV.fill(1);
    out[i] = harvestOneWithCtx(ctx, trip, lowest, allowHalf, stepWin, stepSize, opts, aln, dist);
  }
  return out;
}

// src/engine/bootscanHarvest.worker.mts
function unpackDist(sab) {
  if (!sab) return void 0;
  const meta = new Float32Array(sab, 0, 2);
  const n = meta[0] | 0;
  const maxDiffs = meta[1] | 0;
  const nn = n * n;
  return {
    n,
    maxDiffs,
    distance: new Float32Array(sab, 8, nn),
    permValid: new Float32Array(sab, 8 + nn * 4, nn),
    permDiffs: new Float32Array(sab, 8 + nn * 8, nn)
  };
}
function runJob(wd) {
  const seqnum = new Int16Array(wd.seqSab);
  const aln = {
    names: Array.from({ length: wd.nSeqs }, (_, i) => `s${i}`),
    sequences: Array.from({ length: wd.nSeqs }, () => ""),
    length: wd.length,
    nSeqs: wd.nSeqs,
    seqnum
  };
  const flatTrips = new Int32Array(wd.tripsSab);
  const hits = new Float64Array(wd.hitsSab);
  const state = new Int32Array(wd.stateSab);
  const maxHits = wd.maxHits || 8;
  const opts = {
    lowestProb: wd.lowestProb,
    mcCorrection: wd.mcCorrection,
    circularFlag: wd.circularFlag,
    stepWin: wd.stepWin,
    stepSize: wd.stepSize,
    bootReps: wd.bootReps,
    cutOff: wd.cutOff,
    pValFlag: wd.pValFlag,
    allowHalfWindow: wd.allowHalfWindow,
    distances: unpackDist(wd.distSab)
  };
  try {
    const chunk = [];
    for (let t = wd.lo; t < wd.hi; t++) {
      chunk.push([
        flatTrips[t * 3],
        flatTrips[t * 3 + 1],
        flatTrips[t * 3 + 2]
      ]);
    }
    const results = bootscanHarvestTripletsBatch(aln, chunk, opts);
    for (let i = 0; i < chunk.length; i++) {
      const t = wd.lo + i;
      const evs = results[i] ?? [];
      const base = t * wd.hitStride;
      const n = Math.min(maxHits, evs.length);
      hits[base] = n;
      for (let h = 0; h < n; h++) {
        const e = evs[h];
        const o = base + 1 + h * 6;
        hits[o] = e.daughter;
        hits[o + 1] = e.majorP;
        hits[o + 2] = e.minorP;
        hits[o + 3] = e.beginning;
        hits[o + 4] = e.ending;
        hits[o + 5] = e.probability;
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
