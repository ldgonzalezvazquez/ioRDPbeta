/**
 * Worker persistente MaxChi: EarlyBale screen + events-pass (sin RoleTracker;
 * el hilo principal reasigna roles en orden). Propaga sEventNumber/missingData
 * para MakeBanWin en ciclos DoRDP.
 */
import { parentPort, workerData } from "node:worker_threads";
import type { Alignment } from "./types.ts";
import { ChiWorkspace } from "./chi.ts";
import { defaultUcThresh } from "./stepdown.ts";
import { resolveScanOptions, scanTripletMC, dedupeEvents } from "./maxchi.ts";

type Boot = { type: "boot"; readySab: SharedArrayBuffer; slot: number };
type ScreenJob = {
  type: "job";
  seqSab: SharedArrayBuffer;
  nSeqs: number;
  length: number;
  flatTrips: Int32Array;
  lo: number;
  hi: number;
  lowestProb: number;
  mcCorrection: number;
  mcFlag: 0 | 1 | 2;
  circularFlag: number;
  winSize: number;
  winFract: number;
  proportionFlag: number;
  sEventNumber: number;
  missingSab: SharedArrayBuffer | null;
  missingBytes: number;
  flagsSab: SharedArrayBuffer;
  bqpvSab?: SharedArrayBuffer;
  stateSab: SharedArrayBuffer;
};
type EventsJob = {
  type: "events";
  seqSab: SharedArrayBuffer;
  nSeqs: number;
  length: number;
  tripsSab: SharedArrayBuffer;
  lo: number;
  hi: number;
  lowestProb: number;
  mcCorrection: number;
  mcFlag: 0 | 1 | 2;
  circularFlag: number;
  winSize: number;
  winFract: number;
  proportionFlag: number;
  sEventNumber: number;
  missingSab: SharedArrayBuffer | null;
  missingBytes: number;
  hitStride: number;
  maxHits: number;
  hitsSab: SharedArrayBuffer;
  stateSab: SharedArrayBuffer;
};

function makeAln(seqSab: SharedArrayBuffer, nSeqs: number, length: number): Alignment {
  return {
    names: Array.from({ length: nSeqs }, (_, i) => `s${i}`),
    sequences: Array.from({ length: nSeqs }, () => ""),
    length,
    nSeqs,
    seqnum: new Int16Array(seqSab),
  };
}

function missingFrom(wd: { missingSab: SharedArrayBuffer | null; missingBytes: number }): Uint8Array | null {
  if (!wd.missingSab || wd.missingBytes <= 0) return null;
  return new Uint8Array(wd.missingSab, 0, wd.missingBytes);
}

function runScreen(wd: ScreenJob): void {
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
      ucThresh: defaultUcThresh(wd.lowestProb, wd.mcFlag, wd.mcCorrection),
    },
    70,
  );
  const flags = new Uint8Array(wd.flagsSab);
  const bqpv = wd.bqpvSab ? new Float64Array(wd.bqpvSab) : null;
  const state = new Int32Array(wd.stateSab);
  try {
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = wd.flatTrips[t * 3]!;
      const b = wd.flatTrips[t * 3 + 1]!;
      const c = wd.flatTrips[t * 3 + 2]!;
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

function runEvents(wd: EventsJob): void {
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
      ucThresh: defaultUcThresh(wd.lowestProb, wd.mcFlag, wd.mcCorrection),
    },
    70,
  );
  const flat = new Int32Array(wd.tripsSab);
  const hits = new Float64Array(wd.hitsSab);
  const state = new Int32Array(wd.stateSab);
  const maxHits = wd.maxHits || 8;
  try {
    for (let t = wd.lo; t < wd.hi; t++) {
      const a = flat[t * 3]!;
      const b = flat[t * 3 + 1]!;
      const c = flat[t * 3 + 2]!;
      const r = scanTripletMC(aln, ws, { ...o, earlyBale: 0, roleTracker: null }, a, b, c, "events");
      const evs = dedupeEvents(r.events, wd.length);
      const base = t * wd.hitStride;
      const n = Math.min(maxHits, evs.length);
      hits[base] = n;
      for (let h = 0; h < n; h++) {
        const e = evs[h]!;
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
  parentPort.on("message", (msg: ScreenJob | EventsJob) => {
    if (!msg) return;
    if (msg.type === "job") runScreen(msg);
    else if (msg.type === "events") runEvents(msg);
  });
}

const boot = workerData as Boot | null;
if (boot && boot.type === "boot" && boot.readySab) {
  Atomics.add(new Int32Array(boot.readySab), 0, 1);
  Atomics.notify(new Int32Array(boot.readySab), 0);
}
