// src/engine/geneconvScreen.worker.mts
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

// src/engine/settings.ts
var PROGRAM_RDP = 0;
var PROGRAM_GENECONV = 1;
var PROGRAM_BOOTSCAN = 2;
var PROGRAM_SISCAN = 5;
var PROGRAM_LARD = 7;
var PROGRAM_3SEQ = 8;
var PROGRAM_TOPAL = 9;
function mcCorrectionFor(nSeqs) {
  if (nSeqs < 3) return 1;
  return nSeqs * (nSeqs - 1) * (nSeqs - 2) / 6;
}

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

// src/engine/maxchiParallel.ts
import { createRequire as createRequire2 } from "node:module";

// src/engine/parallelPool.ts
import { createRequire } from "node:module";
var req = createRequire(import.meta.url);

// src/engine/maxchiParallel.ts
var req2 = createRequire2(import.meta.url);

// src/engine/geneconvParallel.ts
import { createRequire as createRequire3 } from "node:module";
var req3 = createRequire3(import.meta.url);

// src/engine/geneconv.ts
var fr = Math.fround;
function resolveGcOptions(aln, o, nTriplets) {
  const mc = o.mcCorrection && o.mcCorrection > 0 ? o.mcCorrection : nTriplets && nTriplets > 0 ? nTriplets : mcCorrectionFor(aln.nSeqs);
  return {
    lowestProb: o.lowestProb ?? 0.05,
    mcFlag: o.mcFlag ?? 0,
    mcCorrection: mc,
    circularFlag: o.circularFlag ?? 0,
    gcIndelFlag: o.gcIndelFlag ?? 0,
    gcMissmatchPen: o.gcMissmatchPen ?? 1,
    gcMaxOverlapFrags: o.gcMaxOverlapFrags ?? 1,
    longWindedFlag: o.longWindedFlag ?? 1,
    roleTracker: o.roleTracker ?? null,
    sEventNumber: o.sEventNumber ?? 0,
    missingData: o.missingData ?? null
  };
}
var GcWorkspace = class {
  L;
  cap;
  // largest GCDimSize
  subSeq;
  xPosDiff;
  xDiffPos;
  fragSt;
  fragEn;
  fragScore;
  maxScorePos;
  fragMaxScore;
  pVals;
  deleteArray;
  constructor(L) {
    this.L = L;
    this.cap = L + 12;
    this.subSeq = new Int8Array((L + 1) * 7 + 4);
    this.xPosDiff = new Int32Array(L + 4);
    this.xDiffPos = new Int32Array(L + 4);
    this.fragSt = new Int32Array((this.cap + 1) * 7 + 4);
    this.fragEn = new Int32Array((this.cap + 1) * 7 + 4);
    this.fragScore = new Int32Array((this.cap + 1) * 7 + 4);
    this.maxScorePos = new Int32Array((this.cap + 1) * 6 + 4);
    this.fragMaxScore = new Int32Array((this.cap + 1) * 6 + 4);
    this.pVals = new Float64Array((this.cap + 1) * 6 + 4);
    this.deleteArray = new Int32Array(this.cap + 4);
  }
};
function findSubSeqGCAP(gcIndelFlag, L, seq1, seq2, seq3, sn, sub, xPosDiff, xDiffPos, nDiff) {
  let Y = 0;
  const os1 = seq1 * (L + 1);
  const os2 = seq2 * (L + 1);
  const os3 = seq3 * (L + 1);
  const off1 = L + 1;
  const off2 = (L + 1) * 2;
  const off3 = (L + 1) * 6;
  let X = 0;
  xPosDiff[0] = 0;
  xDiffPos[0] = 0;
  if (gcIndelFlag === 0) {
    for (X = 1; X <= L; X++) {
      xPosDiff[X] = Y;
      const s1 = sn[X + os1];
      const s2 = sn[X + os2];
      const s3 = sn[X + os3];
      if (s1 !== s2 || s1 !== s3) {
        if (s1 !== GAP && s2 !== GAP && s3 !== GAP) {
          Y++;
          xPosDiff[X] = Y;
          xDiffPos[Y] = X;
          sub[Y] = s1 === s2 ? 1 : 0;
          sub[Y + off1] = s1 === s3 ? 1 : 0;
          sub[Y + off2] = s2 === s3 ? 1 : 0;
        }
        sub[Y + off3] = sub[Y] === 0 && sub[Y + off1] === 0 && sub[Y + off2] === 0 ? 1 : 0;
      }
    }
  } else if (gcIndelFlag === 1) {
    for (X = 1; X <= L; X++) {
      let s1 = sn[X + os1];
      let s2 = sn[X + os2];
      let s3 = sn[X + os3];
      let goOn = 0;
      const gapRun = () => {
        xPosDiff[X] = Y;
        const SX = X;
        let s1s, s2s, s3s;
        if (s1 === s2) {
          s1s = 1;
          s2s = 0;
          s3s = 0;
        } else {
          s1s = 0;
          if (s1 === s3) {
            s2s = 1;
            s3s = 0;
          } else {
            s2s = 0;
            s3s = s2 === s3 ? 1 : 0;
          }
        }
        X++;
        if (X <= L) {
          s1 = sn[X + os1];
          s2 = sn[X + os2];
          s3 = sn[X + os3];
          while (s1 === GAP || s2 === GAP || s3 === GAP) {
            if (s1s !== 0 && s1 !== s2) s1s = 0;
            if (s2s !== 0 && s1 !== s3) s2s = 0;
            if (s3s !== 0 && s2 !== s3) s3s = 0;
            X++;
            if (X > L) break;
            s1 = sn[X + os1];
            s2 = sn[X + os2];
            s3 = sn[X + os3];
          }
        }
        X--;
        Y++;
        const mp = Math.trunc(SX + Math.trunc((X - SX) / 2));
        for (let Z2 = SX + 1; Z2 <= X; Z2++) xPosDiff[Z2] = 0;
        xPosDiff[mp] = Y;
        xDiffPos[Y] = mp;
        sub[Y] = s1s;
        sub[Y + off1] = s2s;
        sub[Y + off2] = s3s;
      };
      if (s1 !== s2) {
        if (s1 !== GAP && s2 !== GAP && s3 !== GAP) {
          Y++;
          xPosDiff[X] = Y;
          xDiffPos[Y] = X;
          sub[Y] = 0;
          sub[Y + off1] = s1 === s3 ? 1 : 0;
          sub[Y + off2] = s2 === s3 ? 1 : 0;
        } else goOn = 1;
        if (goOn === 1) gapRun();
        sub[Y + off3] = sub[Y] === 0 && sub[Y + off1] === 0 && sub[Y + off2] === 0 ? 1 : 0;
      } else if (s1 !== s3) {
        if (s1 !== GAP && s2 !== GAP && s3 !== GAP) {
          Y++;
          xPosDiff[X] = Y;
          xDiffPos[Y] = X;
          sub[Y] = 1;
          sub[Y + off1] = 0;
          sub[Y + off2] = s2 === s3 ? 1 : 0;
        } else goOn = 1;
        if (goOn === 1) gapRun();
        sub[Y + off3] = sub[Y] === 0 && sub[Y + off1] === 0 && sub[Y + off2] === 0 ? 1 : 0;
      } else {
        xPosDiff[X] = Y;
      }
    }
  } else if (gcIndelFlag === 2) {
    for (X = 1; X <= L; X++) {
      xPosDiff[X] = Y;
      const s1 = sn[X + os1];
      const s2 = sn[X + os2];
      const s3 = sn[X + os3];
      if (s1 !== s2 || s1 !== s3) {
        Y++;
        xPosDiff[X] = Y;
        xDiffPos[Y] = X;
        sub[Y] = s1 === s2 ? 1 : 0;
        sub[Y + off1] = s1 === s3 ? 1 : 0;
        sub[Y + off2] = s2 === s3 ? 1 : 0;
        sub[Y + off3] = sub[Y] === 0 && sub[Y + off1] === 0 && sub[Y + off2] === 0 ? 1 : 0;
      }
    }
  }
  for (X = 1; X <= Y; X++) {
    nDiff[0] += sub[X];
    nDiff[1] += sub[X + off1];
    nDiff[2] += sub[X + off2];
  }
  xDiffPos[Y + 1] = L;
  const Z = xDiffPos[Y] + 1;
  for (X = Z; X <= L; X++) xPosDiff[X] = Y;
  return Y;
}
function getFragsP(circularFlag, lenXoverSeq, L, maxcount, sub, fragSt, fragEn, fragScore, fragCount) {
  let goOn = 0;
  const RR = lenXoverSeq + 1;
  let FC6 = 0;
  const os4 = L + 1;
  const os5 = maxcount + 1;
  let X = 1;
  let Y = 0;
  let Z = 0;
  for (X = 1; X < RR; X++) {
    for (Y = 0; Y < 3; Y++) {
      if (sub[X + Y * os4] === 1) break;
    }
    if (Y === 3) Y = 6;
    const os2 = Y * os4;
    const os = fragCount[Y] + Y * os5;
    fragSt[os] = X;
    const FS = X;
    const SX = X;
    X++;
    if (circularFlag === 0) {
      while (sub[os2 + X] === 1) {
        X++;
        if (X > lenXoverSeq) break;
      }
    } else {
      while (sub[os2 + X] === 1) {
        X++;
        if (X > lenXoverSeq) {
          X = 1;
          goOn = 1;
          break;
        }
      }
      if (X === 1) {
        while (sub[os2 + X] === 1 && X !== SX) X++;
      }
      if (X === SX) return 0;
    }
    X--;
    fragEn[os] = X;
    const FE = X;
    let FSc;
    if (FE > FS) FSc = FE - FS + 1;
    else if (FE < FS) FSc = FE - FS + RR;
    else FSc = 1;
    fragScore[os] = FSc;
    let os3;
    if (Y !== 0) {
      os3 = fragCount[0];
      fragSt[os3] = FS;
      fragEn[os3] = FE;
      fragScore[os3] = -FSc;
      fragCount[0]++;
    }
    if (Y !== 1) {
      os3 = fragCount[1] + os5;
      fragSt[os3] = FS;
      fragEn[os3] = FE;
      fragScore[os3] = -FSc;
      fragCount[1]++;
    }
    if (Y !== 2) {
      os3 = fragCount[2] + 2 * os5;
      fragSt[os3] = FS;
      fragEn[os3] = FE;
      fragScore[os3] = -FSc;
      fragCount[2]++;
    }
    if (Y === 0) Z = 5;
    else if (Y === 1) Z = 4;
    else if (Y === 2) Z = 3;
    else if (Y === 6) Z = 6;
    if (Z < 6) {
      os3 = fragCount[Z] + Z * os5;
      if (fragCount[Z] > 0) {
        if (fragScore[os3 - 1] > 0) {
          fragEn[os3 - 1] = FE;
          fragScore[os3 - 1] = fragScore[os3 - 1] + FSc;
        } else {
          fragSt[os3] = FS;
          fragEn[os3] = FE;
          fragScore[os3] = FSc;
          fragCount[Z]++;
        }
      } else {
        fragSt[os3] = FS;
        fragEn[os3] = FE;
        fragScore[os3] = FSc;
        fragCount[Z]++;
      }
      for (let A = 3; A < 6; A++) {
        if (A !== Z) {
          os3 = fragCount[A] + A * os5;
          fragSt[os3] = FS;
          fragEn[os3] = FE;
          fragScore[os3] = -FSc;
          fragCount[A]++;
        }
      }
    } else {
      if (fragCount[3] > 0) {
        for (let A = 3; A < 6; A++) {
          os3 = fragCount[A] + A * os5;
          if (fragScore[os3 - 1] > 0) {
            fragEn[os3 - 1] = FE;
            fragScore[os3 - 1] = fragScore[os3 - 1] + FSc;
          } else {
            fragSt[os3] = FS;
            fragEn[os3] = FE;
            fragScore[os3] = FSc;
            fragCount[A]++;
          }
        }
      } else {
        for (let A = 3; A < 6; A++) {
          os3 = fragCount[A] + A * os5;
          fragSt[os3] = FS;
          fragEn[os3] = FE;
          fragScore[os3] = FSc;
          fragCount[A]++;
        }
      }
    }
    if (Y <= 2) fragCount[Y]++;
    for (let A = 0; A < 6; A++) {
      if (fragCount[A] >= maxcount - 1) {
        goOn = 1;
        break;
      }
    }
    FC6++;
    if (goOn === 1 || FC6 >= maxcount - 1) break;
  }
  fragCount[6] = FC6;
  for (X = 0; X <= 6; X++) {
    const os = fragCount[X] + X * os5;
    fragSt[os] = lenXoverSeq;
    fragEn[os] = lenXoverSeq;
  }
  return 1;
}
function getMaxFragScoreP(lseq, gcMissmatchPen, missPen, maxScorePos, fragMaxScore, fragScore, fragCount, hiscore) {
  const os = lseq + 1;
  const os2 = lseq + 1;
  if (gcMissmatchPen > 0) {
    for (let X = 0; X < 6; X++) {
      let hsx = 0;
      const os3 = X * os2;
      const MPen = fr(missPen[X]);
      const fcx = fragCount[X];
      for (let Y = 0; Y <= fcx; Y++) {
        const os5 = Y + os3;
        if (fragScore[os5] > 0) {
          let Polys = fragScore[os5];
          let fms = Polys;
          let Diffs = 0;
          let msp = Y;
          for (let Z = Y + 1; Z <= fcx; Z++) {
            let fs = fragScore[Z + os3];
            if (fs <= 0) {
              fs = -fs;
              Diffs += fs;
            }
            Polys += fs;
            const ts = Math.trunc(fr(Polys - Diffs - fr(Diffs * MPen)));
            if (ts < 0) break;
            else if (ts >= fms) {
              fms = ts;
              msp = Z;
            }
          }
          maxScorePos[os5] = msp;
          fragMaxScore[os5] = fms;
          if (fms > hsx) hsx = fms;
        } else {
          fragMaxScore[os5] = 0;
        }
      }
      hiscore[X] = hsx;
    }
  } else {
    let osv = os;
    for (let X = 0; X <= 5; X++) {
      const os3 = X * os2;
      const os7 = X * osv;
      for (let Y = 0; Y <= fragCount[X]; Y++) {
        osv = Y + os3;
        fragMaxScore[Y + os7] = fragScore[osv];
        maxScorePos[osv] = Y;
      }
    }
  }
}
function calcKMaxP(gcMissmatchPen, XOLen, mcFlag, mcCorrection, lowestProb, hiFragScore, critval, missPen, LL, KMax, nDiff, highenough) {
  const LenXoverSeq = XOLen;
  for (let X = 0; X < 6; X++) {
    LL[X] = 0;
    if (highenough[X] === 1) {
      if (nDiff[X] > 0 && nDiff[X] < LenXoverSeq) {
        const P = nDiff[X] / LenXoverSeq;
        const Q = 1 - P;
        if (gcMissmatchPen === 0) {
          LL[X] = -Math.log(Q);
          KMax[X] = P;
        } else {
          const mP = missPen[X] * P;
          const mx = missPen[X];
          let ll0 = Math.log(mP / Q);
          ll0 = ll0 / (mx + 1);
          let Z = Math.exp(2 * ll0);
          let zdel = 1;
          let Yy = 1;
          let guard = 0;
          while ((Math.abs(zdel) > 1e-6 || Math.abs(Yy) > 1e-6) && guard++ < 1e3) {
            const zm = Math.pow(Z, -mx);
            Yy = Q * Z + P * zm - 1;
            zdel = Yy / (Q - mP * zm / Z);
            Z = Z - zdel;
          }
          LL[X] = Math.log(Z);
          let d1 = Math.exp(LL[X]);
          d1 = d1 - 1;
          const d2 = -(mx + 1) * LL[X];
          const d3 = Math.exp(d2);
          KMax[X] = d1 * (Q - mP * d3);
        }
      }
    }
  }
  const PCO = mcFlag === 0 ? lowestProb / mcCorrection : lowestProb;
  if (PCO > 1) return { goOn: 0, pco: PCO };
  for (let X = 0; X <= 5; X++) {
    if (KMax[X] > 0) {
      let KMTL = KMax[X] * XOLen;
      KMTL = Math.log(KMTL);
      let PVM1 = 1 - PCO;
      if (PVM1 > 0) {
        PVM1 = -Math.log(PVM1);
        if (PVM1 > 0) {
          PVM1 = -Math.log(PVM1);
          critval[X] = (KMTL + PVM1) / LL[X];
          if (critval[X] < 4) critval[X] = 4;
        }
      } else critval[X] = 4;
    } else critval[X] = 4;
  }
  let goOn = 0;
  for (let X = 0; X <= 5; X++) {
    highenough[X] = 0;
    if (hiFragScore[X] > 3 && hiFragScore[X] > critval[X]) {
      highenough[X] = 1;
      goOn = 1;
    }
  }
  return { goOn, pco: PCO };
}
function gcCalcPValP(lseq, LXover, fragMaxScore, pVals, fragCount, KMax, LL, highenough, critval) {
  const os = lseq + 1;
  const LenXoverSeq = LXover;
  let MaxScore = 10;
  for (let X = 0; X <= 5; X++) {
    if (highenough[X] === 1) {
      if (KMax[X] > 0) {
        const LKLen = fr(Math.log(KMax[X] * LenXoverSeq));
        for (let Y = 0; Y <= fragCount[X]; Y++) {
          const os2 = Y + X * os;
          if (fragMaxScore[os2] > critval[X]) {
            let KAScore = fr(LL[X] * fragMaxScore[os2] - LKLen);
            if (KAScore > 0) {
              if (KAScore < 32) {
                const THld = Math.exp(-KAScore);
                pVals[os2] = 1 - Math.exp(-THld);
              } else {
                let warn = 0;
                if (KAScore > 700) {
                  warn = KAScore;
                  KAScore = 701;
                }
                let THld = Math.exp(-KAScore);
                if (warn !== 0) {
                  KAScore = fr(warn - 700);
                  THld = THld / KAScore;
                }
                pVals[os2] = THld;
              }
            } else pVals[os2] = 1;
            if (pVals[os2] < MaxScore) MaxScore = pVals[os2];
          } else pVals[os2] = 1;
        }
      } else highenough[X] = 0;
    }
  }
  return MaxScore;
}
function gcAnalyse(w, o, aln, s1, s2, s3) {
  const L = aln.length;
  const nDiff = new Int32Array(8);
  let cnt = 0;
  {
    const sn = aln.seqnum;
    const a = s1 * (L + 1);
    const b = s2 * (L + 1);
    const c = s3 * (L + 1);
    for (let x = 1; x <= L; x++) {
      const v = sn[x + a];
      if (v !== sn[x + b] || v !== sn[x + c]) cnt++;
    }
  }
  const dim = cnt + 10;
  const os = dim + 1;
  w.subSeq.fill(0);
  w.xPosDiff.fill(0);
  w.xDiffPos.fill(0);
  w.fragSt.fill(0, 0, os * 7 + 2);
  w.fragEn.fill(0, 0, os * 7 + 2);
  w.fragScore.fill(0, 0, os * 7 + 2);
  w.maxScorePos.fill(0, 0, os * 6 + 2);
  w.fragMaxScore.fill(0, 0, os * 6 + 2);
  w.pVals.fill(0, 0, os * 6 + 2);
  const lenXoverSeq = findSubSeqGCAP(o.gcIndelFlag, L, s1, s2, s3, aln.seqnum, w.subSeq, w.xPosDiff, w.xDiffPos, nDiff);
  if (nDiff[0] === lenXoverSeq || nDiff[1] === lenXoverSeq || nDiff[2] === lenXoverSeq) return null;
  const UBSS = L;
  w.subSeq[lenXoverSeq + 1] = 0;
  w.subSeq[lenXoverSeq + 1 + UBSS + 1] = 0;
  w.subSeq[lenXoverSeq + 1 + 2 * (UBSS + 1)] = 0;
  w.subSeq[lenXoverSeq + 1 + 6 * (UBSS + 1)] = 0;
  nDiff[3] = nDiff[0] + nDiff[1];
  nDiff[4] = nDiff[0] + nDiff[2];
  nDiff[5] = nDiff[1] + nDiff[2];
  nDiff[0] = lenXoverSeq - nDiff[0];
  nDiff[1] = lenXoverSeq - nDiff[1];
  nDiff[2] = lenXoverSeq - nDiff[2];
  const LTG = fr(lenXoverSeq * o.gcMissmatchPen);
  const missPen = new Float64Array(8);
  missPen[0] = Math.trunc(fr(LTG / fr(nDiff[0]))) + 1;
  missPen[1] = Math.trunc(fr(LTG / fr(nDiff[1]))) + 1;
  missPen[2] = Math.trunc(fr(LTG / fr(nDiff[2]))) + 1;
  let MaxDiff = 0;
  let MinDiff = L;
  for (let x = 0; x <= 5; x++) {
    if (MinDiff > nDiff[x]) MinDiff = nDiff[x];
    if (MaxDiff < nDiff[x]) MaxDiff = nDiff[x];
  }
  if (MinDiff < 3 && MaxDiff > MinDiff * 10) return null;
  if (nDiff[3] === 0) nDiff[3] = 1;
  if (nDiff[4] === 0) nDiff[4] = 1;
  if (nDiff[5] === 0) nDiff[5] = 1;
  missPen[3] = Math.trunc(LTG / nDiff[3]) + 1;
  missPen[4] = Math.trunc(LTG / nDiff[4]) + 1;
  missPen[5] = Math.trunc(LTG / nDiff[5]) + 1;
  const fragCount = new Int32Array(8);
  const goOn = getFragsP(o.circularFlag, lenXoverSeq, L, dim, w.subSeq, w.fragSt, w.fragEn, w.fragScore, fragCount);
  if (goOn === 0) return null;
  const hiFragScore = new Int32Array(8);
  getMaxFragScoreP(dim, o.gcMissmatchPen, missPen, w.maxScorePos, w.fragMaxScore, w.fragScore, fragCount, hiFragScore);
  const highEnough = new Int32Array(8);
  for (let x = 0; x <= 5; x++) highEnough[x] = hiFragScore[x] > 3 ? 1 : 0;
  const LL = new Float64Array(8);
  const KMax = new Float64Array(8);
  const critval = new Float64Array(8);
  const kk = calcKMaxP(o.gcMissmatchPen, lenXoverSeq, o.mcFlag, o.mcCorrection, o.lowestProb, hiFragScore, critval, missPen, LL, KMax, nDiff, highEnough);
  if (kk.goOn === 0) return null;
  const maxScore = gcCalcPValP(dim, lenXoverSeq, w.fragMaxScore, w.pVals, fragCount, KMax, LL, highEnough, critval);
  return { dim, lenXoverSeq, os, fragCount, highEnough, LL, KMax, critval, missPen, maxScore, pco: kk.pco };
}
function gcXoverDP(w, o, aln, s1, s2, s3) {
  const st = gcAnalyse(w, o, aln, s1, s2, s3);
  return st !== null && st.maxScore <= st.pco;
}

// src/engine/geneconvScreen.worker.mts
function runJob(wd) {
  const aln = {
    names: Array.from({ length: wd.nSeqs }, (_, i) => `s${i}`),
    sequences: Array.from({ length: wd.nSeqs }, () => ""),
    length: wd.length,
    nSeqs: wd.nSeqs,
    seqnum: new Int16Array(wd.seqSab)
  };
  const flat = new Int32Array(wd.tripsSab);
  const flags = new Uint8Array(wd.flagsSab);
  const state = new Int32Array(wd.stateSab);
  const o = resolveGcOptions(
    aln,
    {
      lowestProb: wd.lowestProb,
      mcCorrection: wd.mcCorrection,
      circularFlag: wd.circularFlag,
      gcIndelFlag: wd.gcIndelFlag,
      gcMissmatchPen: wd.gcMissmatchPen,
      gcMaxOverlapFrags: wd.gcMaxOverlapFrags,
      longWindedFlag: 0,
      roleTracker: null,
      prescreenOnly: true
    },
    wd.nSeqs
  );
  const w = new GcWorkspace(wd.length);
  try {
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = flat[t * 3];
      const b = flat[t * 3 + 1];
      const c = flat[t * 3 + 2];
      flags[t] = gcXoverDP(w, o, aln, a, b, c) ? 1 : 0;
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
