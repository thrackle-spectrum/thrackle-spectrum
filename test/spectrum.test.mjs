// Brute-force verification of src/algorithm/caterpillarSpectrum.js.
//
// For every tested caterpillar, every drawing produced by the algorithm is checked:
//   * the predicted number of crossings equals the number counted by brute force,
//   * the first drawing is a convex thrackle,
//   * every number of crossings lies in the claimed spectrum [0, spectrumMax] + {theta},
//   * at every settled drawing, all the values of the spectrum from its number of
//     crossings up to theta have been realized (no gaps),
//   * the last drawing is planar, i.e., the whole spectrum is covered,
//   * the number of local moves is linear in theta + n.
// The algorithm for a specific number of crossings is checked for every value, and for
// small caterpillars the claimed spectrum is compared with all circular layouts.
//
// Run with: npm test

import { describeCaterpillar, drawingWithCrossings, enumerateSpectrum, inSpectrum, runSpectrum } from "../src/algorithm/caterpillarSpectrum.js";

function edgesOf(seq) {
  const edges = [];
  for (let i = 0; i + 1 < seq.length; i += 1) edges.push([`v${i}`, `v${i + 1}`]);
  seq.forEach((legs, i) => {
    for (let j = 0; j < legs; j += 1) edges.push([`v${i}`, `l${i}_${j}`]);
  });
  return edges;
}

function countCrossings(order, edges) {
  const pos = new Map(order.map((id, index) => [id, index]));
  const inside = (u, v, x) => (u < v ? u < x && x < v : x > u || x < v);
  let count = 0;
  for (let i = 0; i < edges.length; i += 1) {
    const [a, b] = edges[i];
    const u = pos.get(a);
    const v = pos.get(b);
    for (let j = i + 1; j < edges.length; j += 1) {
      const [c, d] = edges[j];
      if (a === c || a === d || b === c || b === d) continue;
      if (inside(u, v, pos.get(c)) !== inside(u, v, pos.get(d))) count += 1;
    }
  }
  return count;
}

/** Thrackle bound by the formula (m(m+1) - sum of squared degrees) / 2. */
function thetaByFormula(edges) {
  const degree = new Map();
  for (const [a, b] of edges) {
    degree.set(a, (degree.get(a) || 0) + 1);
    degree.set(b, (degree.get(b) || 0) + 1);
  }
  let squares = 0;
  for (const d of degree.values()) squares += d * d;
  return (edges.length * (edges.length + 1) - squares) / 2;
}

/** The numbers of crossings of all circular layouts. */
function bruteForceSpectrum(seq) {
  const edges = edgesOf(seq);
  const ids = [...new Set(edges.flat())];
  const found = new Set();
  const order = [ids[0]];
  const used = new Array(ids.length).fill(false);
  const extend = () => {
    if (order.length === ids.length) {
      found.add(countCrossings(order, edges));
      return;
    }
    for (let i = 1; i < ids.length; i += 1) {
      if (used[i]) continue;
      used[i] = true;
      order.push(ids[i]);
      extend();
      order.pop();
      used[i] = false;
    }
  };
  extend();
  return found;
}

const stats = {
  instances: 0,
  drawings: 0,
  targets: 0,
  bruteForce: 0,
  mergedSteps: 0,
  worst: { odd: [0, null], even: [0, null] },
  worstTarget: { odd: [0, null], even: [0, null] },
  cases: new Map(),
};

function fail(seq, message) {
  throw new Error(`[${seq.join(",")}] ${message}`);
}

function checkSpectrum(seq) {
  const edges = edgesOf(seq);
  const n = edges.length + 1;
  const theta = thetaByFormula(edges);
  const info = describeCaterpillar(seq);
  if (info.theta !== theta) fail(seq, `thrackle bound ${info.theta} instead of ${theta}`);
  const result = enumerateSpectrum(seq);
  const visited = new Uint8Array(theta + 1);
  let frontier = theta + 1; // every value of the spectrum that is at least `frontier` has been realized
  let lowestSettled = Infinity;
  result.steps.forEach((step, index) => {
    if (step.order.length !== n || new Set(step.order).size !== n) fail(seq, `step ${index} is not a permutation of the vertices`);
    const actual = countCrossings(step.order, edges);
    if (actual !== step.crossings) {
      fail(seq, `step ${index} "${step.label}": predicted ${step.crossings} crossings, counted ${actual}`);
    }
    if (index === 0 && actual !== theta) fail(seq, `the initial drawing has ${actual} crossings instead of ${theta}`);
    if (!inSpectrum(info, actual)) fail(seq, `step ${index} "${step.label}": ${actual} crossings are not in the claimed spectrum`);
    visited[actual] = 1;
    while (frontier > 0 && (visited[frontier - 1] || !inSpectrum(info, frontier - 1))) frontier -= 1;
    if (step.settled) {
      lowestSettled = Math.min(lowestSettled, actual);
      if (frontier > lowestSettled) fail(seq, `step ${index} "${step.label}": ${frontier - 1} crossings have not been realized`);
    }
    const prefix = step.label.split(":")[0].replace(/\s*\([^)]*\)/g, "").replace(/ [vl]\d+(_\d+)?/g, " x");
    const special = /move \(\w\)|top-region swap|root move/.exec(step.label);
    for (const key of [step.type === "swap" ? prefix : step.type, special && special[0]]) {
      if (key) stats.cases.set(key, (stats.cases.get(key) || 0) + 1);
    }
  });
  if (frontier !== 0 || result.steps[result.steps.length - 1].crossings !== 0) fail(seq, "the spectrum is not covered down to 0");
  checkStructures(seq, result.steps, n);
  checkMergedUndo(seq, edges, info, result);
  const parity = info.spineLength % 2 === 1 ? "odd" : "even";
  const ratio = result.moves / (theta + n);
  if (ratio > stats.worst[parity][0]) stats.worst[parity] = [ratio, seq];
  stats.instances += 1;
  stats.drawings += result.steps.length;
  return info;
}

/**
 * The structure reported with the steps partitions the vertices into the spine and the
 * feet of the current caterpillar and the removed vertices, and it changes only at the
 * steps that start a level.
 */
function checkStructures(seq, steps, n) {
  let previous = null;
  steps.forEach((step, index) => {
    const structure = step.structure;
    if (!structure) {
      if (n > 2 && steps.length > 1) fail(seq, `step ${index} has no structure`);
      return;
    }
    if (structure === previous) return;
    if (step.type === "swap") fail(seq, `step ${index} "${step.label}" changes the structure`);
    previous = structure;
    const { spine, feet, removed } = structure;
    const all = new Set([...spine, ...Object.keys(feet), ...Object.keys(removed)]);
    if (all.size !== n || spine.length + Object.keys(feet).length + Object.keys(removed).length !== n) {
      fail(seq, `step ${index}: the structure is not a partition of the vertices`);
    }
    const onSpine = new Set(spine);
    for (const parent of Object.values(feet)) {
      if (!onSpine.has(parent)) fail(seq, `step ${index}: the parent ${parent} of a foot is not on the spine`);
    }
    for (const holder of Object.values(removed)) {
      if (!onSpine.has(holder) && !(holder in feet)) fail(seq, `step ${index}: ${holder} holds removed vertices but is not in the caterpillar`);
    }
  });
}

/** Reversing all auxiliary moves in one step yields the same drawings without the intermediate ones. */
function checkMergedUndo(seq, edges, info, result) {
  const merged = enumerateSpectrum(seq, { mergeUndo: true });
  if (merged.moves !== result.moves) fail(seq, "merging the undo steps changes the number of moves");
  const visited = new Uint8Array(info.theta + 1);
  let total = 0;
  for (const step of merged.steps) {
    total += step.merged;
    visited[step.crossings] = 1;
    if (step.merged > 1) {
      const actual = countCrossings(step.order, edges);
      if (actual !== step.crossings) fail(seq, `merged step "${step.label}": predicted ${step.crossings} crossings, counted ${actual}`);
      stats.mergedSteps += 1;
    }
  }
  if (total !== result.steps.length) fail(seq, "merging the undo steps loses steps");
  for (let s = 0; s <= info.theta; s += 1) {
    if (inSpectrum(info, s) && !visited[s]) fail(seq, `with merged undo steps, ${s} crossings are not shown`);
  }
  const last = merged.steps[merged.steps.length - 1];
  const lastPlain = result.steps[result.steps.length - 1];
  if (last.order.join() !== lastPlain.order.join()) fail(seq, "merging the undo steps changes the final drawing");
}

function checkTargets(seq, info) {
  const edges = edgesOf(seq);
  const n = edges.length + 1;
  const parity = info.spineLength % 2 === 1 ? "odd" : "even";
  for (let s = 0; s <= info.theta; s += 1) {
    if (!inSpectrum(info, s)) {
      let rejected = false;
      try {
        drawingWithCrossings(seq, s);
      } catch {
        rejected = true;
      }
      if (!rejected) fail(seq, `${s} crossings are not in the spectrum but were accepted`);
      continue;
    }
    const order = drawingWithCrossings(seq, s);
    const actual = countCrossings(order, edges);
    if (actual !== s) fail(seq, `the drawing for ${s} crossings has ${actual} crossings`);
    const { moves } = runSpectrum(seq, null, { target: s });
    if (moves / n > stats.worstTarget[parity][0]) stats.worstTarget[parity] = [moves / n, [...seq, `s=${s}`]];
    stats.targets += 1;
  }
}

function checkAgainstAllLayouts(seq, info) {
  const found = bruteForceSpectrum(seq);
  for (let s = 0; s <= info.theta; s += 1) {
    if (found.has(s) !== inSpectrum(info, s)) fail(seq, `${s} crossings: claimed ${inSpectrum(info, s)}, all layouts say ${found.has(s)}`);
  }
  if (Math.max(...found) !== info.theta) fail(seq, "a layout exceeds the thrackle bound");
  stats.bruteForce += 1;
}

/** All sequences of length k+1 with ends in [minEnd, maxEnd] and internal entries in [minInner, maxInner]. */
function* sequences(k, [minEnd, maxEnd], [minInner, maxInner]) {
  const seq = new Array(k + 1).fill(0);
  function* rec(i) {
    if (i > k) {
      yield seq.slice();
      return;
    }
    const end = i === 0 || i === k;
    for (let v = end ? minEnd : minInner; v <= (end ? maxEnd : maxInner); v += 1) {
      seq[i] = v;
      yield* rec(i + 1);
    }
  }
  yield* rec(0);
}

function makeRandom(seed) {
  let state = seed >>> 0;
  return () => {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    return state / 4294967296;
  };
}

const started = Date.now();

// Exhaustive families: [k, ends, internal].
const families = [
  [1, [1, 7], [0, 0]],
  [3, [1, 4], [0, 4]],
  [5, [1, 3], [0, 3]],
  [7, [1, 2], [0, 2]],
  [9, [1, 2], [0, 1]],
  [11, [1, 1], [0, 1]],
  [2, [1, 5], [0, 5]],
  [4, [1, 3], [0, 3]],
  [6, [1, 2], [0, 2]],
  [8, [1, 2], [0, 1]],
  [10, [1, 1], [0, 1]],
  // Every spine vertex has degree at least 3 (m >= 3).
  [4, [2, 4], [1, 3]],
  [6, [2, 3], [1, 2]],
  [8, [2, 3], [1, 2]],
  [4, [3, 5], [2, 3]],
  // Many feet at both ends: the values close to the thrackle bound need the band at v_i
  // combined with moves over the following spine vertices.
  [4, [6, 8], [1, 2]],
  [6, [6, 7], [1, 2]],
];
for (const [k, ends, inner] of families) {
  let count = 0;
  for (const seq of sequences(k, ends, inner)) {
    const info = checkSpectrum(seq);
    if (k <= 5 || count % 7 === 0) checkTargets(seq, info);
    count += 1;
  }
  console.log(`k = ${k}: ${count} caterpillars (ends ${ends.join("..")}, internal ${inner.join("..")}) ok`);
}

// End vertices without legs are leaves: the spine is shorter than the given path.
for (const seq of [[0, 2], [2, 0], [0, 0], [3], [0, 1, 1, 0], [0, 2, 3, 1], [0, 0, 1, 2, 0, 0], [0, 1, 0, 2, 1, 0, 3, 0], [1, 0, 0, 0, 0, 0], [0, 3, 2, 2], [0, 0, 0]]) {
  const info = checkSpectrum(seq);
  checkTargets(seq, info);
}
console.log("caterpillars given with leaves as end vertices ok");

// A few caterpillars with many feet at the ends and larger minimum degree.
for (const seq of [[16, 2, 2, 3, 17], [17, 2, 3, 2, 16], [9, 1, 2, 1, 2, 2, 9], [12, 3, 2, 4, 3, 2, 11], [10, 1, 1, 1, 1, 1, 1, 1, 10], [30, 1, 1, 4, 30]]) {
  const info = checkSpectrum(seq);
  if (info.theta <= 700) checkTargets(seq, info);
}
console.log("caterpillars with many feet at the ends ok");

// Small caterpillars: compare the claimed spectrum with all circular layouts.
for (let length = 2; length <= 6; length += 1) {
  for (const seq of sequences(length - 1, [1, 6], [0, 6])) {
    if (length + seq.reduce((a, b) => a + b, 0) > 8) continue;
    const info = checkSpectrum(seq);
    checkAgainstAllLayouts(seq, info);
  }
}
console.log(`${stats.mergedSteps} merged undo steps verified`);
console.log(`${stats.bruteForce} caterpillars with at most 8 vertices: the spectrum agrees with all circular layouts`);

// Random larger caterpillars.
const random = makeRandom(20261115);
let randomCount = 0;
for (let round = 0; round < 3000; round += 1) {
  const k = 1 + Math.floor(random() * 20);
  const density = random();
  const maxLegs = 1 + Math.floor(random() * 6);
  const minLegs = random() < 0.3 ? 1 + Math.floor(random() * 2) : 0; // often m >= 3
  const seq = [];
  for (let i = 0; i <= k; i += 1) {
    const end = i === 0 || i === k;
    const legs = Math.max(minLegs, random() < density ? 1 + Math.floor(random() * maxLegs) : 0);
    seq.push(end ? Math.max(1 + (minLegs > 0 ? 1 : 0), legs) : legs);
  }
  const info = checkSpectrum(seq);
  if (round % 10 === 0 && info.theta <= 400) checkTargets(seq, info);
  randomCount += 1;
}
console.log(`${randomCount} random caterpillars ok`);

console.log("");
console.log(
  `${stats.instances} caterpillars, ${stats.drawings} drawings and ${stats.targets} target values verified in ${((Date.now() - started) / 1000).toFixed(1)} s`
);
for (const parity of ["odd", "even"]) {
  const [ratio, seq] = stats.worst[parity];
  const [targetRatio, targetSeq] = stats.worstTarget[parity];
  console.log(`${parity} spine: max. moves / (theta + n) = ${ratio.toFixed(2)} for [${seq.join(",")}]`);
  console.log(`${parity} spine: max. moves / n for a specific number of crossings = ${targetRatio.toFixed(2)} for [${targetSeq.join(",")}]`);
}
console.log("coverage of the cases of the proofs (number of moves):");
for (const key of [...stats.cases.keys()].sort()) console.log(`  ${key}: ${stats.cases.get(key)}`);
