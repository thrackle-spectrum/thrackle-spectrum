import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { describeCaterpillar, enumerateSpectrum, inSpectrum } from "./algorithm/caterpillarSpectrum.js";

// The colors of the figures in the paper. As in the figures,
// the spine vertex v_i and its feet are filled with the light color of the i-th pair, and
// the legs of v_i are drawn in the dark one.
const PAPER_COLORS = [
  { dark: "#33a02c", light: "#b2df8a" }, // dark green, light green
  { dark: "#1f78b4", light: "#a6cee3" }, // dark blue, light blue
  { dark: "#ff7f00", light: "#fdbf6f" }, // dark orange, light orange
  { dark: "#a65628", light: "#e5d8bd" }, // dark brown, light brown
  { dark: "#6a3d9a", light: "#cab2d6" }, // dark purple, light purple
  { dark: "#f781bf", light: "#fddaec" }, // dark pink, light pink
  { dark: "#1b9e77", light: "#8dd3c7" }, // dark cyan, light cyan
  { dark: "#e31a1c", light: "#fb9a99" }, // mid red, light red
];
const INK = "#000000"; // black
const GRAY = "#bebebe"; // gray
const DARK_GRAY = "#808080"; // dark gray
const ACCENT = "#1f78b4"; // dark blue
const DEFAULT_SEQUENCE_TEXT = "1,1,1,1,1,1";

function paperColor(i) {
  return PAPER_COLORS[((i % PAPER_COLORS.length) + PAPER_COLORS.length) % PAPER_COLORS.length];
}

function arraysEqual(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i += 1) if (a[i] !== b[i]) return false;
  return true;
}

function parseSequence(text) {
  const cleaned = text.trim().replace(/[;\s]+/g, ",").replace(/,+/g, ",").replace(/^,|,$/g, "");
  if (!cleaned) throw new Error("Enter a non-empty sequence such as 1,1,1,1,1,1.");
  const seq = cleaned.split(",").map((part) => {
    if (!/^\d+$/.test(part)) throw new Error("The sequence must contain only non-negative integers.");
    return Number(part);
  });
  if (seq.length < 2) throw new Error("Use at least two spine vertices.");
  return seq;
}

function makeThrackleOrder(seq, leavesBySpine) {
  const top = [];
  const bottom = [];
  for (let i = 0; i < seq.length; i += 1) {
    if (i % 2 === 0) {
      top.push(`v${i}`);
      bottom.push(...leavesBySpine[i]);
    } else {
      top.push(...leavesBySpine[i]);
      bottom.push(`v${i}`);
    }
  }
  return [...top, ...bottom];
}

function countCrossings(order, edges) {
  const pos = new Map(order.map((id, index) => [id, index]));
  const inOpenInterval = (u, v, x) => (u < v ? u < x && x < v : x > u || x < v);
  let count = 0;
  for (let i = 0; i < edges.length; i += 1) {
    const e1 = edges[i];
    const u = pos.get(e1.a);
    const v = pos.get(e1.b);
    for (let j = i + 1; j < edges.length; j += 1) {
      const e2 = edges[j];
      if (e1.a === e2.a || e1.a === e2.b || e1.b === e2.a || e1.b === e2.b) continue;
      const x = pos.get(e2.a);
      const y = pos.get(e2.b);
      if (inOpenInterval(u, v, x) !== inOpenInterval(u, v, y)) count += 1;
    }
  }
  return count;
}

function buildGraph(seq) {
  const vertices = [];
  const edges = [];
  const leavesBySpine = Array.from({ length: seq.length }, () => []);
  for (let i = 0; i < seq.length; i += 1) {
    vertices.push({ id: `v${i}`, kind: "spine", spineIndex: i, shortLabel: `v${i}` });
  }
  for (let i = 0; i < seq.length - 1; i += 1) edges.push({ id: `e-s-${i}`, a: `v${i}`, b: `v${i + 1}`, kind: "spine", spineIndex: i });
  for (let i = 0; i < seq.length; i += 1) {
    for (let j = 0; j < seq[i]; j += 1) {
      const id = `l${i}_${j}`;
      vertices.push({ id, kind: "leaf", spineIndex: i, leafIndex: j, shortLabel: `l${i}_${j}` });
      leavesBySpine[i].push(id);
      edges.push({ id: `e-l-${i}-${j}`, a: `v${i}`, b: id, kind: "leaf", spineIndex: i });
    }
  }
  const vertexMap = Object.fromEntries(vertices.map((vertex) => [vertex.id, vertex]));
  const thrackleOrder = makeThrackleOrder(seq, leavesBySpine);
  return { seq, vertices, edges, vertexMap, leavesBySpine, thrackleOrder, theta: countCrossings(thrackleOrder, edges) };
}

function positionsMap(order) {
  return Object.fromEntries(order.map((id, index) => [id, index]));
}

function neighborIndex(n, index, direction) {
  return direction === "cw" ? (index + 1) % n : (index - 1 + n) % n;
}

function swapPositions(order, a, b) {
  const i = order.indexOf(a);
  const j = order.indexOf(b);
  if (i < 0 || j < 0 || i === j) return order.slice();
  const next = order.slice();
  [next[i], next[j]] = [next[j], next[i]];
  return next;
}

function swapIndices(order, i, j) {
  const next = order.slice();
  [next[i], next[j]] = [next[j], next[i]];
  return next;
}

function getTargetIds(graph, spineIndex, targetPart) {
  if (targetPart === "spine") return [`v${spineIndex}`];
  if (targetPart === "legs") return graph.leavesBySpine[spineIndex].slice();
  return [`v${spineIndex}`, ...graph.leavesBySpine[spineIndex]];
}

function inferDirection(order, sourceLeafIds, targetIds) {
  const targetSet = new Set(targetIds);
  const pos = positionsMap(order);
  let cwCount = 0;
  let ccwCount = 0;
  for (const leafId of sourceLeafIds) {
    if (!(leafId in pos)) continue;
    const index = pos[leafId];
    if (targetSet.has(order[neighborIndex(order.length, index, "cw")])) cwCount += 1;
    if (targetSet.has(order[neighborIndex(order.length, index, "ccw")])) ccwCount += 1;
  }
  if (cwCount === 0 && ccwCount === 0) return null;
  if (cwCount === 0) return "ccw";
  if (ccwCount === 0) return "cw";
  return cwCount >= ccwCount ? "cw" : "ccw";
}

function chooseBoundaryLeaf(order, sourceLeafIds, direction, targetSet) {
  const pos = positionsMap(order);
  const leaves = sourceLeafIds.filter((id) => id in pos);
  const adjacent = leaves.filter((id) => targetSet.has(order[neighborIndex(order.length, pos[id], direction)]));
  const candidates = adjacent.length > 0 ? adjacent : leaves;
  if (candidates.length === 0) return null;
  candidates.sort((a, b) => (direction === "cw" ? pos[b] - pos[a] : pos[a] - pos[b]));
  return candidates[0];
}

function moveOneLeafAcrossTargetSet(order, leafId, targetIds, direction, edges) {
  let nextOrder = order.slice();
  const targetSet = new Set(targetIds);
  const counts = [];
  let swaps = 0;
  while (true) {
    const pos = positionsMap(nextOrder);
    const leafPos = pos[leafId];
    const nextPos = neighborIndex(nextOrder.length, leafPos, direction);
    if (!targetSet.has(nextOrder[nextPos])) break;
    nextOrder = swapIndices(nextOrder, leafPos, nextPos);
    swaps += 1;
    counts.push(countCrossings(nextOrder, edges));
  }
  return { order: nextOrder, counts, swaps };
}

function performSingleLeafMove(graph, order, { sourceIndex, targetIndex, targetPart, direction = "auto" }) {
  const sourceLeafIds = graph.leavesBySpine[sourceIndex] || [];
  const sourceLeafSet = new Set(sourceLeafIds);
  const targetIds = getTargetIds(graph, targetIndex, targetPart).filter((id) => !sourceLeafSet.has(id));
  if (sourceLeafIds.length === 0) return { ok: false, message: `v${sourceIndex} has no legs to move.` };
  if (targetIds.length === 0) return { ok: false, message: `The chosen target part at v${targetIndex} is empty.` };
  const preferred = direction === "auto" ? inferDirection(order, sourceLeafIds, targetIds) : direction;
  const directionChoices = preferred ? [preferred] : [];
  if (!directionChoices.includes("cw")) directionChoices.push("cw");
  if (!directionChoices.includes("ccw")) directionChoices.push("ccw");
  let best = null;
  for (const fixedDirection of directionChoices) {
    const leafId = chooseBoundaryLeaf(order, sourceLeafIds, fixedDirection, new Set(targetIds));
    if (!leafId) continue;
    const step = moveOneLeafAcrossTargetSet(order, leafId, targetIds, fixedDirection, graph.edges);
    if (step.swaps === 0) continue;
    best = { ok: true, order: step.order, counts: step.counts, swaps: step.swaps, direction: fixedDirection, message: `Moved one leg of v${sourceIndex} over ${targetPart} of v${targetIndex}.` };
    break;
  }
  return best ?? { ok: false, message: `No adjacent single-leg move from v${sourceIndex} over ${targetPart} of v${targetIndex} is currently available.` };
}

function performBatchMove(graph, order, config) {
  let currentOrder = order.slice();
  const counts = [];
  let swaps = 0;
  let movedLeaves = 0;
  const limit = Math.max(1, (graph.leavesBySpine[config.sourceIndex] || []).length * (order.length + 2));
  for (let i = 0; i < limit; i += 1) {
    const step = performSingleLeafMove(graph, currentOrder, config);
    if (!step.ok || step.swaps === 0) break;
    currentOrder = step.order;
    counts.push(...step.counts);
    swaps += step.swaps;
    movedLeaves += 1;
    config = { ...config, direction: step.direction };
  }
  if (swaps === 0) return { ok: false, message: `No adjacent batch move from legs of v${config.sourceIndex} is currently available.` };
  return { ok: true, order: currentOrder, counts, swaps, movedLeaves, message: `Moved ${movedLeaves} leg${movedLeaves === 1 ? "" : "s"} of v${config.sourceIndex}.` };
}


// The drawing: the vertices lie on a circle around (cx, cy).
const FRAME = { size: 640, cx: 320, cy: 320, radius: 236 };
// How far a vertex that passes other vertices leaves the circle on its way.
const LIFT = 24;
const REDUCED_MOTION = typeof window !== "undefined" && window.matchMedia?.("(prefers-reduced-motion: reduce)").matches === true;

// The point at `position` (an index, possibly fractional) of n positions on a circle of the given radius.
function pointAt(position, n, radius) {
  const angle = -Math.PI / 2 + (2 * Math.PI * position) / n;
  return { x: FRAME.cx + radius * Math.cos(angle), y: FRAME.cy + radius * Math.sin(angle) };
}

// Runs the algorithm of the paper (Theorems "odd-spine-spectrum" and "even-spine-spectrum",
// see src/algorithm/caterpillarSpectrum.js) and turns its drawings into timeline snapshots.
// Every drawing is re-counted by brute force.
// With `target`, the algorithm for a specific number of crossings (Theorems
// "specific-value-odd-spine" and "specific-value-even-spine") is run instead; it starts
// at the convex thrackle of a smaller caterpillar and stops at `target` crossings.
// With `mergeUndo`, consecutive steps that reverse auxiliary moves are shown as one step.
function runPaperSpectrumAlgorithm(graph, order, visited, target = null, { mergeUndo = false } = {}) {
  let result;
  try {
    result = enumerateSpectrum(graph.seq, target === null ? { mergeUndo } : { target, mergeUndo });
  } catch (err) {
    return { ok: false, snapshots: [], notice: err.message || "The spectrum algorithm failed." };
  }

  // Rotate the drawings so that the first vertex of the algorithm stays where it is now.
  const shift = result.steps.length > 0 ? Math.max(0, order.indexOf(result.steps[0].order[0])) : 0;
  const placed = (ids) => (shift === 0 ? ids : [...ids.slice(ids.length - shift), ...ids.slice(0, ids.length - shift)]);

  let currentCount = countCrossings(order, graph.edges);
  const currentVisited = new Set(visited);
  currentVisited.add(currentCount);
  const stepSnapshots = [];

  for (let i = 0; i < result.steps.length; i += 1) {
    const step = result.steps[i];
    const stepOrder = placed(step.order);
    if (i === 0 && arraysEqual(stepOrder, order)) continue;
    const nextCount = countCrossings(stepOrder, graph.edges);
    if (nextCount !== step.crossings) {
      return {
        ok: false,
        snapshots: stepSnapshots,
        notice: `Step "${step.label}" was expected to yield ${step.crossings} crossings but yields ${nextCount}.`,
      };
    }
    const entry = { label: step.label, from: currentCount, to: nextCount, delta: nextCount - currentCount, swaps: step.merged, kind: step.type };
    currentCount = nextCount;
    currentVisited.add(nextCount);
    stepSnapshots.push(makeSnapshot(entry, stepOrder, currentVisited, step.label, graph.seq, step.structure));
  }

  // The algorithm ends on a smaller caterpillar. A last step shows the result as the
  // whole caterpillar again, drawn as at the beginning.
  const withFinalView = () => {
    const last = stepSnapshots[stepSnapshots.length - 1];
    const reduced = last?.structure && (Object.keys(last.structure.removed).length > 0 || Object.keys(last.structure.feet).some((id) => id.startsWith("v")));
    if (!reduced) return stepSnapshots;
    const label = `Result: the whole caterpillar with ${currentCount} crossing${currentCount === 1 ? "" : "s"}`;
    const entry = { label, from: currentCount, to: currentCount, delta: 0, swaps: 0, kind: "result" };
    return [...stepSnapshots, makeSnapshot(entry, last.order, currentVisited, label, graph.seq, null)];
  };

  if (target !== null) {
    if (currentCount !== target) {
      return {
        ok: false,
        snapshots: stepSnapshots,
        notice: `The algorithm for a specific number of crossings stopped at ${currentCount} instead of ${target} crossings.`,
      };
    }
    return {
      ok: true,
      snapshots: withFinalView(),
      notice: stepSnapshots.length === 0
        ? `The current drawing already has exactly ${target} crossings.`
        : `Constructed a drawing with exactly ${target} crossings: ${result.moves} local move${result.moves === 1 ? "" : "s"} after the convex thrackle of the first step (n = ${order.length} vertices).`,
    };
  }

  const missing = [];
  for (let value = 0; value <= result.theta; value += 1) {
    if (inSpectrum(result, value) && !currentVisited.has(value)) missing.push(value);
  }
  if (missing.length > 0) {
    return {
      ok: false,
      snapshots: stepSnapshots,
      notice: `The spectrum algorithm finished, but these crossing values were not reached: ${missing.join(", ")}.`,
    };
  }

  const gap = result.theta - result.spectrumMax - 1;
  const spectrumText = gap > 0
    ? `every crossing count of the spectrum, that is, ${result.theta} and ${result.spectrumMax} down to 0 (${gap === 1 ? `the value ${result.theta - 1} is` : `the values ${result.spectrumMax + 1} to ${result.theta - 1} are`} not realizable)`
    : `every crossing count from ${result.theta} down to 0`;
  return {
    ok: true,
    snapshots: withFinalView(),
    notice: `Ran the ${result.spineLength % 2 === 1 ? "odd" : "even"}-spine algorithm of the paper: ${result.moves} local moves, starting from ${result.levels} convex thrackle${result.levels === 1 ? "" : "s"}, realize ${spectrumText}.`,
  };
}

const RANDOM_LIMITS = { spine: 16, legs: 8 };

function randomInt(lo, hi) {
  return lo + Math.floor(Math.random() * (hi - lo + 1));
}

// A random caterpillar as its sequence of legs. The end vertices get at least one leg,
// so the path with `spine` vertices is the spine and `parity` refers to its length k.
function randomCaterpillar({ spineMin, spineMax, legsMin, legsMax, parity }) {
  const sizes = [];
  for (let size = spineMin; size <= spineMax; size += 1) {
    const k = size - 1;
    if (parity === "any" || (parity === "odd") === (k % 2 === 1)) sizes.push(size);
  }
  if (sizes.length === 0) {
    throw new Error(`No spine of ${parity} length has between ${spineMin} and ${spineMax} vertices.`);
  }
  const size = sizes[randomInt(0, sizes.length - 1)];
  return Array.from({ length: size }, (_, i) => (
    i === 0 || i === size - 1 ? randomInt(Math.max(1, legsMin), Math.max(1, legsMax)) : randomInt(legsMin, legsMax)
  ));
}

// Compares two circular orders of the same vertices. Returns the maximal runs of consecutive
// vertices that moved by the same number of positions: { ids, shift, from, to }, where `from`
// and `to` are the (possibly fractional) positions of the center of the run before and after.
// Returns no runs if nothing or too much changed (for example, at a restart).
function describeMove(previousOrder, nextOrder, maxRuns = 6) {
  const n = nextOrder.length;
  if (!previousOrder || previousOrder.length !== n || n < 3) return [];
  const oldIndex = new Map(previousOrder.map((id, index) => [id, index]));
  const shifts = [];
  for (let index = 0; index < n; index += 1) {
    const before = oldIndex.get(nextOrder[index]);
    if (before === undefined) return [];
    let shift = (index - before) % n;
    if (shift < 0) shift += n;
    if (shift > n / 2) shift -= n;
    shifts.push(shift);
  }
  const anchor = shifts.indexOf(0);
  if (anchor < 0) return [];
  const runs = [];
  let current = null;
  for (let t = 1; t < n; t += 1) {
    const index = (anchor + t) % n;
    if (shifts[index] === 0) {
      current = null;
    } else if (current && current.shift === shifts[index]) {
      current.last = anchor + t;
      current.ids.push(nextOrder[index]);
    } else {
      current = { shift: shifts[index], first: anchor + t, last: anchor + t, ids: [nextOrder[index]] };
      runs.push(current);
    }
  }
  if (runs.length > maxRuns) return [];
  return runs.map((run) => {
    const to = (run.first + run.last) / 2;
    return { ids: run.ids, shift: run.shift, from: to - run.shift, to };
  });
}

// An arc around the center of the drawing from position `from` to position `to` (of n positions).
function arcArrowPath(n, from, to, radius) {
  const point = (position) => {
    const { x, y } = pointAt(position, n, radius);
    return `${x.toFixed(1)} ${y.toFixed(1)}`;
  };
  const largeArc = Math.abs(to - from) * 2 > n ? 1 : 0;
  return `M ${point(from)} A ${radius} ${radius} 0 ${largeArc} ${to > from ? 1 : 0} ${point(to)}`;
}

// How the vertices and edges are drawn, following the figures of the paper. `structure`
// describes the caterpillar the algorithm currently works on (see `enumerateSpectrum`);
// without it, the whole caterpillar is drawn. Spine edges are thick and black, a foot has
// the color of its parent, a former spine vertex that became a foot is drawn as a foot of
// its new parent, and removed vertices are gray with pale edges.
function drawingStyle(graph, structure) {
  const onSpine = structure ? new Set(structure.spine) : null;
  const role = (id) => {
    if (!structure) return graph.vertexMap[id].kind === "spine" ? "spine" : "foot";
    if (id in structure.removed) return "removed";
    return onSpine.has(id) ? "spine" : "foot";
  };
  // The index of the spine vertex of the current caterpillar from which the vertex hangs.
  const ownerIndex = (id) => {
    const own = graph.vertexMap[id].spineIndex;
    if (!structure) return own;
    let holder = id in structure.removed ? structure.removed[id] : id;
    if (!onSpine.has(holder)) holder = structure.feet[holder] ?? holder;
    return graph.vertexMap[holder]?.spineIndex ?? own;
  };
  const vertices = {};
  for (const vertex of graph.vertices) {
    vertices[vertex.id] = { role: role(vertex.id), color: paperColor(ownerIndex(vertex.id)) };
  }
  const layers = { removed: [], leg: [], spine: [] };
  for (const edge of graph.edges) {
    const a = vertices[edge.a];
    const b = vertices[edge.b];
    if (a.role === "removed" || b.role === "removed") {
      layers.removed.push({ edge, stroke: (b.role === "removed" ? b : a).color.light, width: 1.6 });
    } else if (a.role === "spine" && b.role === "spine") {
      layers.spine.push({ edge, stroke: INK, width: 3.6 });
    } else {
      layers.leg.push({ edge, stroke: (b.role === "foot" ? b : a).color.dark, width: 1.9 });
    }
  }
  return { vertices, edges: [...layers.removed, ...layers.leg, ...layers.spine], hasRemoved: layers.removed.length > 0 };
}

const VERTEX_SHAPES = {
  spine: { radius: 12, strokeWidth: 2.6, labelSize: 17, labelGap: 15 },
  foot: { radius: 8, strokeWidth: 1.6, labelSize: 12, labelGap: 13 },
  removed: { radius: 7, strokeWidth: 1.6, labelSize: 12, labelGap: 13 },
};

const VERTEX_NAME = /^(?:v(\d+)|l(\d+)_(\d+))$/;

// The name of a vertex as in the paper: v with the index of the spine vertex, or the
// letter l with the index of the parent and the number of the foot.
function vertexName(id) {
  const match = VERTEX_NAME.exec(id);
  if (!match) return null;
  return match[1] !== undefined ? { letter: "v", index: match[1] } : { letter: "\u2113", index: `${match[2]},${match[3]}` };
}

// Text in which the names of vertices (v3, l3_1) are typeset as in the paper.
function MathText({ text }) {
  return text.split(/\b(v\d+|l\d+_\d+)\b/).map((part, i) => {
    const name = i % 2 === 1 ? vertexName(part) : null;
    return name ? <span key={i} className="math">{name.letter}<sub>{name.index}</sub></span> : part;
  });
}

function VertexLabel({ id, role, size, x, y }) {
  const name = vertexName(id);
  return (
      <text x={x} y={y} textAnchor="middle" dominantBaseline="central" fontSize={size} className={`v-label v-label-${role}`}>
        <tspan className="letter">{name ? name.letter : id}</tspan>
        {name ? <tspan className="index" dy={size * 0.24} fontSize={size * 0.68}>{name.index}</tspan> : null}
      </text>
  );
}

function makeSnapshot(entry, nextOrder, nextVisited, nextNotice, nextGraphSeq, structure = null) {
  return {
    entry,
    order: nextOrder.slice(),
    visited: Array.from(nextVisited),
    notice: nextNotice,
    graphSeq: nextGraphSeq.slice(),
    structure,
  };
}

function buildExplorerState(text, fallbackNotice = "Reset to zig-zag drawing.") {
  const seq = parseSequence(text);
  const graph = buildGraph(seq);
  const entry = { label: "Initialize at zig-zag drawing", from: graph.theta, to: graph.theta, delta: 0, swaps: 0 };
  const snapshot = { entry, order: graph.thrackleOrder.slice(), visited: [graph.theta], notice: fallbackNotice, graphSeq: graph.seq.slice() };
  return {
    sequenceText: seq.join(","),
    graph,
    order: graph.thrackleOrder.slice(),
    visited: new Set([graph.theta]),
    notice: fallbackNotice,
    timeline: [snapshot],
    timelineCursor: 0,
    batchSource: Math.min(1, graph.seq.length - 1),
    batchTarget: 0,
    batchTargetPart: "block",
    batchDirection: "auto",
  };
}

const INITIAL_STATE = buildExplorerState(DEFAULT_SEQUENCE_TEXT);

const PLAYER_ICONS = {
  start: "M4 6h2v12H4z M13 6v12l-6.5-6z M20 6v12l-6.5-6z",
  back: "M6 6h2v12H6z M18 6v12l-8.5-6z",
  play: "M8 5v14l11-7z",
  pause: "M6 5h4v14H6z M14 5h4v14h-4z",
  forward: "M16 6h2v12h-2z M6 6v12l8.5-6z",
  end: "M18 6h2v12h-2z M11 6v12l6.5-6z M4 6v12l6.5-6z",
};
const PLAYER_SPEEDS = [
  { label: "Slow", delay: 900 },
  { label: "Normal", delay: 450 },
  { label: "Fast", delay: 180 },
  { label: "Very fast", delay: 60 },
];

const easeInOut = (t) => (t < 0.5 ? 2 * t * t : 1 - (2 - 2 * t) ** 2 / 2);

// Where the vertices are while the drawing changes from the positions `anim.from` to the
// order `anim.order`: every vertex moves along the circle the shorter way round, and the
// vertices in `anim.movers` leave the circle on their way, so that they pass the others.
function placeVertices(anim, progress) {
  const n = anim.order.length;
  const t = easeInOut(progress);
  const lift = progress < 1 ? LIFT * Math.sin(Math.PI * progress) : 0;
  const placed = {};
  anim.order.forEach((id, index) => {
    const from = anim.from[id] ?? index;
    let shift = (index - from) % n;
    if (shift > n / 2) shift -= n;
    else if (shift < -n / 2) shift += n;
    placed[id] = { position: progress >= 1 ? index : from + shift * t, lift: anim.movers.has(id) ? lift : 0 };
  });
  return placed;
}

// The circular drawing. When `order` changes, the vertices move to their new places
// within `duration` milliseconds.
function Drawing({ order, style, selectedId, arrows, showArrows, duration, onVertexClick }) {
  const [anim, setAnim] = useState(() => ({ order, from: {}, movers: new Set(), duration: 0 }));
  const [progress, setProgress] = useState(1);

  let active = anim;
  let shownProgress = progress;
  if (anim.order !== order) {
    // A new drawing: start at the places where the vertices are shown right now.
    const shown = placeVertices(anim, progress);
    const from = {};
    for (const id of anim.order) from[id] = shown[id].position;
    const animate = duration > 0 && anim.order.length === order.length && order.every((id) => id in from);
    const runs = animate ? describeMove(anim.order, order) : [];
    // In a swap of two parts, the smaller part passes the larger one.
    const movers = runs.length === 2 ? new Set((runs[0].ids.length <= runs[1].ids.length ? runs[0] : runs[1]).ids) : new Set();
    active = { order, from: animate ? from : {}, movers, duration: animate ? duration : 0 };
    shownProgress = animate ? 0 : 1;
    setAnim(active);
    setProgress(shownProgress);
  }

  useEffect(() => {
    if (anim.duration <= 0) return undefined;
    let frame = 0;
    let startTime = null;
    const step = (now) => {
      if (startTime === null) startTime = now;
      const next = Math.min(1, (now - startTime) / anim.duration);
      setProgress(next);
      if (next < 1) frame = requestAnimationFrame(step);
    };
    frame = requestAnimationFrame(step);
    // Animation frames do not run in a hidden tab; make sure the drawing arrives anyway.
    const fallback = setTimeout(() => setProgress(1), anim.duration + 150);
    return () => {
      cancelAnimationFrame(frame);
      clearTimeout(fallback);
    };
  }, [anim]);

  const n = order.length;
  const placed = placeVertices(active, shownProgress);
  const at = (id, extra = 0) => pointAt(placed[id].position, n, FRAME.radius + placed[id].lift + extra);
  const showFootLabels = n <= 64;
  const settled = shownProgress >= 1;

  return (
      <svg viewBox={`0 0 ${FRAME.size} ${FRAME.size}`} data-settled={settled ? "true" : "false"} className="plate mx-auto block w-full max-w-[74vh]">
        <defs>
          <marker id="swap-arrow" viewBox="0 0 10 10" refX="8.5" refY="5" markerWidth="8" markerHeight="8" markerUnits="userSpaceOnUse" orient="auto-start-reverse">
            <path d="M0 0.8 L10 5 L0 9.2 z" fill={DARK_GRAY} />
          </marker>
        </defs>
        <circle cx={FRAME.cx} cy={FRAME.cy} r={FRAME.radius} fill="none" stroke={DARK_GRAY} strokeWidth="1.2" strokeDasharray="6 6" />
        {style.edges.map(({ edge, stroke, width }) => {
          const a = at(edge.a);
          const b = at(edge.b);
          return <line key={edge.id} x1={a.x} y1={a.y} x2={b.x} y2={b.y} stroke={stroke} strokeWidth={width} strokeLinecap="round" />;
        })}
        {order.map((id) => {
          const point = at(id);
          const look = style.vertices[id];
          const shape = VERTEX_SHAPES[look.role];
          const removed = look.role === "removed";
          const label = look.role === "spine" || showFootLabels ? at(id, shape.radius + shape.labelGap) : null;
          return (
              <g key={id} data-role={look.role} onClick={() => onVertexClick(id)} style={{ pointerEvents: "all", cursor: "pointer" }}>
                <circle cx={point.x} cy={point.y} r={shape.radius} fill={removed ? "#ffffff" : look.color.light} stroke={selectedId === id ? ACCENT : removed ? GRAY : INK} strokeWidth={selectedId === id ? 4.5 : shape.strokeWidth} />
                {label ? <VertexLabel id={id} role={look.role} size={shape.labelSize} x={label.x} y={label.y} /> : null}
              </g>
          );
        })}
        {showArrows && settled ? arrows.map((arrow) => (
            <path key={arrow.key} data-testid="swap-arrow" d={arrow.d} fill="none" stroke={DARK_GRAY} strokeWidth="1.3" strokeLinecap="round" markerStart={arrow.both ? "url(#swap-arrow)" : undefined} markerEnd="url(#swap-arrow)" style={{ pointerEvents: "none" }} />
        )) : null}
      </svg>
  );
}

function PlayerButton({ icon, label, onClick, disabled, primary = false }) {
  return (
      <button type="button" onClick={onClick} disabled={disabled} title={label} aria-label={label} className={primary ? "is-primary" : undefined}>
        <svg viewBox="0 0 24 24" width="18" height="18" fill="currentColor" aria-hidden="true"><path d={PLAYER_ICONS[icon]} /></svg>
      </button>
  );
}

export default function App() {
  const [sequenceText, setSequenceText] = useState(INITIAL_STATE.sequenceText);
  const [error, setError] = useState("");
  const [notice, setNotice] = useState(INITIAL_STATE.notice);
  const [graph, setGraph] = useState(INITIAL_STATE.graph);
  const [order, setOrder] = useState(INITIAL_STATE.order);
  const [selectedId, setSelectedId] = useState(null);
  const [visited, setVisited] = useState(INITIAL_STATE.visited);
  const [timeline, setTimeline] = useState(INITIAL_STATE.timeline);
  const [timelineCursor, setTimelineCursor] = useState(INITIAL_STATE.timelineCursor);
  const [batchSource, setBatchSource] = useState(INITIAL_STATE.batchSource);
  const [batchTarget, setBatchTarget] = useState(INITIAL_STATE.batchTarget);
  const [batchTargetPart, setBatchTargetPart] = useState(INITIAL_STATE.batchTargetPart);
  const [batchDirection, setBatchDirection] = useState(INITIAL_STATE.batchDirection);
  const [targetText, setTargetText] = useState("");
  const [playing, setPlaying] = useState(false);
  const [stepDelay, setStepDelay] = useState(PLAYER_SPEEDS[1].delay);
  const [randomSpec, setRandomSpec] = useState({ spineMin: "4", spineMax: "8", legsMin: "0", legsMax: "3", parity: "any" });
  const [mergeUndo, setMergeUndo] = useState(false);
  const drawingRef = useRef(null);
  const logItemRefs = useRef(new Map());
  const logBoxRef = useRef(null);

  const currentCrossings = useMemo(() => (graph ? countCrossings(order, graph.edges) : 0), [graph, order]);
  const caterpillarInfo = useMemo(() => (graph ? describeCaterpillar(graph.seq) : null), [graph]);
  const structure = timeline[timelineCursor]?.structure ?? null;
  const style = useMemo(() => (graph ? drawingStyle(graph, structure) : null), [graph, structure]);
  const spineEdgeCount = caterpillarInfo ? caterpillarInfo.spineLength : 0;
  const firstCursorByCount = useMemo(() => {
    const map = new Map();
    timeline.forEach((snapshot, index) => {
      if (!map.has(snapshot.entry.to)) map.set(snapshot.entry.to, index);
    });
    return map;
  }, [timeline]);
  // A preview of the next step of the move log. If two parts of the same size swap, one
  // curve with an arrowhead at both ends joins them. If a part passes a larger part, a
  // single arrow leads from it into the gap where it will land. A restart and steps that
  // combine several moves get no arrow.
  const nextArrows = useMemo(() => {
    const next = timeline[timelineCursor + 1];
    const kind = next?.entry.kind;
    if (!next || kind === "restart" || kind === "init" || kind === "continue") return [];
    const runs = describeMove(order, next.order);
    if (runs.length !== 2) return [];
    const n = order.length;
    const radius = FRAME.radius + 44;
    const [a, b] = runs;
    if (a.ids.length === b.ids.length) {
      // Each of the two parts takes the place of the other one.
      let end = b.to;
      if (end - a.to > n / 2) end -= n;
      else if (a.to - end > n / 2) end += n;
      return [{ key: `${a.ids[0]}-${b.ids[0]}`, d: arcArrowPath(n, a.to, end, radius), both: true }];
    }
    const mover = a.ids.length < b.ids.length ? a : b;
    const other = mover === a ? b : a;
    // The two parts move in opposite directions (the shifts are taken the shorter way round).
    let shift = mover.shift;
    if (Math.sign(shift) === Math.sign(other.shift)) shift -= Math.sign(shift) * n;
    const from = mover.to - shift;
    const gap = from + Math.sign(shift) * ((mover.ids.length - 1) / 2 + other.ids.length + 0.5);
    return [{ key: `${mover.ids[0]}-${gap}`, d: arcArrowPath(n, from, gap, radius), both: false }];
  }, [timeline, timelineCursor, order]);

  // Keeps the current step visible in the move log without scrolling the page.
  useEffect(() => {
    const box = logBoxRef.current;
    const activeItem = logItemRefs.current.get(timelineCursor);
    if (!box || !activeItem) return;
    const boxRect = box.getBoundingClientRect();
    const itemRect = activeItem.getBoundingClientRect();
    if (itemRect.top < boxRect.top) box.scrollTop -= boxRect.top - itemRect.top;
    else if (itemRect.bottom > boxRect.bottom) box.scrollTop += itemRect.bottom - boxRect.bottom;
  }, [timelineCursor]);

  const restoreTimelineCursor = useCallback((nextCursor) => {
    if (nextCursor < 0 || nextCursor >= timeline.length) return;
    const snapshot = timeline[nextCursor];
    setGraph(buildGraph(snapshot.graphSeq));
    setOrder(snapshot.order.slice());
    setVisited(new Set(snapshot.visited));
    setNotice(snapshot.notice);
    setTimelineCursor(nextCursor);
    setSelectedId(null);
  }, [timeline]);

  // Playback: shows the next step of the move log after `stepDelay` and stops at the end.
  const lastCursor = timeline.length - 1;
  const isPlaying = playing && timelineCursor < lastCursor;
  useEffect(() => {
    if (!isPlaying) return undefined;
    const timer = setTimeout(() => {
      restoreTimelineCursor(timelineCursor + 1);
      if (timelineCursor + 1 >= lastCursor) setPlaying(false);
    }, stepDelay);
    return () => clearTimeout(timer);
  }, [isPlaying, timelineCursor, lastCursor, stepDelay, restoreTimelineCursor]);

  function pushInitialState(nextGraph, nextNotice) {
    const entry = { label: "Initialize at zig-zag drawing", from: nextGraph.theta, to: nextGraph.theta, delta: 0, swaps: 0 };
    const snapshot = { entry, order: nextGraph.thrackleOrder.slice(), visited: [nextGraph.theta], notice: nextNotice, graphSeq: nextGraph.seq.slice() };
    setGraph(nextGraph);
    setOrder(nextGraph.thrackleOrder.slice());
    setVisited(new Set([nextGraph.theta]));
    setNotice(nextNotice);
    setTimeline([snapshot]);
    setTimelineCursor(0);
    setPlaying(false);
    setSelectedId(null);
    setBatchSource(Math.min(1, nextGraph.seq.length - 1));
    setBatchTarget(0);
    setBatchTargetPart("block");
    setBatchDirection("auto");
  }

  function initialize(text = sequenceText) {
    try {
      const seq = parseSequence(text);
      pushInitialState(buildGraph(seq), "Reset to zig-zag drawing.");
      setSequenceText(seq.join(","));
      setError("");
    } catch (err) {
      setError(err.message || "Could not parse the sequence.");
    }
  }

  function generateRandom() {
    const read = (text, lo, hi, fallback) => {
      const value = Number.parseInt(text, 10);
      return Number.isNaN(value) ? fallback : Math.min(hi, Math.max(lo, value));
    };
    const spine = [read(randomSpec.spineMin, 2, RANDOM_LIMITS.spine, 4), read(randomSpec.spineMax, 2, RANDOM_LIMITS.spine, 8)].sort((a, b) => a - b);
    const legs = [read(randomSpec.legsMin, 0, RANDOM_LIMITS.legs, 0), read(randomSpec.legsMax, 0, RANDOM_LIMITS.legs, 3)].sort((a, b) => a - b);
    setRandomSpec({ spineMin: String(spine[0]), spineMax: String(spine[1]), legsMin: String(legs[0]), legsMax: String(legs[1]), parity: randomSpec.parity });
    try {
      const seq = randomCaterpillar({ spineMin: spine[0], spineMax: spine[1], legsMin: legs[0], legsMax: legs[1], parity: randomSpec.parity });
      const legCount = seq.reduce((sum, value) => sum + value, 0);
      pushInitialState(buildGraph(seq), `Generated a random caterpillar with ${seq.length} spine vertices and ${legCount} leg${legCount === 1 ? "" : "s"}.`);
      setSequenceText(seq.join(","));
      setError("");
    } catch (err) {
      setError(err.message || "Could not generate a caterpillar.");
    }
  }

  // Brings the drawing into view if it is not visible (narrow windows).
  function showDrawing() {
    drawingRef.current?.scrollIntoView({ block: "nearest", behavior: "smooth" });
  }

  // Navigation by the user: stops the playback.
  function goToStep(nextCursor) {
    setPlaying(false);
    restoreTimelineCursor(nextCursor);
  }

  function play() {
    if (timeline.length < 2) return;
    if (timelineCursor >= lastCursor) restoreTimelineCursor(0);
    setPlaying(true);
  }

  function commitStepSequence(stepSnapshots, finalNotice, options = {}) {
    if (stepSnapshots.length === 0) return;
    const nextTimeline = [...timeline.slice(0, timelineCursor + 1), ...stepSnapshots];
    const finalCursor = nextTimeline.length - 1;
    nextTimeline[finalCursor] = { ...nextTimeline[finalCursor], notice: finalNotice };
    setTimeline(nextTimeline);
    setSelectedId(null);
    if (options.play) {
      // Stay at the current drawing and let the player walk through the new steps.
      setNotice(`Playing ${stepSnapshots.length} step${stepSnapshots.length === 1 ? "" : "s"}.`);
      setPlaying(true);
      return;
    }
    const snapshot = nextTimeline[finalCursor];
    setPlaying(false);
    setGraph(buildGraph(snapshot.graphSeq));
    setOrder(snapshot.order.slice());
    setVisited(new Set(snapshot.visited));
    setNotice(finalNotice);
    setTimelineCursor(finalCursor);
  }

  function commitOrderChange(nextOrder, countsVisited, entry, nextNotice = notice) {
    const nextVisited = new Set([...visited, ...countsVisited]);
    const snapshot = { entry, order: nextOrder.slice(), visited: Array.from(nextVisited), notice: nextNotice, graphSeq: graph.seq.slice() };
    const nextTimeline = [...timeline.slice(0, timelineCursor + 1), snapshot];
    setOrder(nextOrder.slice());
    setVisited(nextVisited);
    setNotice(nextNotice);
    setTimeline(nextTimeline);
    setTimelineCursor(nextTimeline.length - 1);
    setPlaying(false);
    setSelectedId(null);
  }

  function jumpToFirstCount(value) {
    const cursor = firstCursorByCount.get(value);
    if (cursor == null) return;
    goToStep(cursor);
  }

  function handleSwapChoice(id) {
    if (!selectedId) return setSelectedId(id);
    if (selectedId === id) return setSelectedId(null);
    const nextOrder = swapPositions(order, selectedId, id);
    const nextCount = countCrossings(nextOrder, graph.edges);
    commitOrderChange(nextOrder, [nextCount], { label: `Swap ${selectedId} and ${id}`, from: currentCrossings, to: nextCount, delta: nextCount - currentCrossings, swaps: 1 });
  }

  function applyManualBatch() {
    const result = performBatchMove(graph, order, { sourceIndex: batchSource, targetIndex: batchTarget, targetPart: batchTargetPart, direction: batchDirection });
    if (!result.ok) return setNotice(result.message);
    const nextCount = result.counts[result.counts.length - 1] ?? currentCrossings;
    commitOrderChange(result.order, result.counts.length > 0 ? result.counts : [nextCount], { label: `Batch: move legs of v${batchSource} over ${batchTargetPart} of v${batchTarget}`, from: currentCrossings, to: nextCount, delta: nextCount - currentCrossings, swaps: result.swaps }, result.message);
  }

  function runFullSpectrum() {
    if (!arraysEqual(order, graph.thrackleOrder)) {
      setNotice("Reset to the zig-zag drawing before running the spectrum algorithm.");
      return;
    }
    const result = runPaperSpectrumAlgorithm(graph, order, visited, null, { mergeUndo });
    if (result.snapshots.length === 0) {
      setNotice(result.notice);
      return;
    }
    commitStepSequence(result.snapshots, result.notice, { play: true });
    showDrawing();
  }

  // Constructs a drawing with exactly `value` crossings and appends its steps to the move log.
  function constructDrawingWithCrossings(value) {
    const result = runPaperSpectrumAlgorithm(graph, order, visited, value, { mergeUndo });
    if (result.snapshots.length === 0) {
      setNotice(result.notice);
      return;
    }
    commitStepSequence(result.snapshots, result.notice);
    showDrawing();
  }

  function submitTarget(event) {
    event.preventDefault();
    const text = targetText.trim();
    if (!/^\d+$/.test(text)) {
      setNotice("Enter the target number of crossings as a non-negative integer.");
      return;
    }
    constructDrawingWithCrossings(Number(text));
  }

  if (!graph) return <div className="p-6">Loading...</div>;

  const setRandom = (key) => (e) => setRandomSpec((spec) => ({ ...spec, [key]: e.target.value }));
  const endsAreLeaves = graph.seq[0] === 0 || graph.seq[graph.seq.length - 1] === 0;
  const fullSpectrum = caterpillarInfo.spectrumMax >= caterpillarInfo.theta - 1;
  const currentEntry = timeline[timelineCursor]?.entry;
  const cellState = (value) => {
    if (value === currentCrossings) return "current";
    if (visited.has(value)) return "visited";
    return inSpectrum(caterpillarInfo, value) ? "open" : "void";
  };

  return (
      <div className="min-h-screen px-5 pb-12 pt-6 md:px-9">
        <div className="mx-auto max-w-[108rem]">
          <header>
            <div className="flex flex-wrap items-end justify-between gap-x-12 gap-y-4">
              <div>
                <div className="eyebrow">Convex thrackle spectrum of caterpillars</div>
                <h1 className="masthead-title mt-1">Caterpillar convex-crossing explorer</h1>
              </div>
              <dl className="masthead-facts">
                <div>
                  <dt className="eyebrow">Spine length</dt>
                  <dd><span className="math">k</span> = {spineEdgeCount} <small>({spineEdgeCount % 2 === 0 ? "even" : "odd"})</small></dd>
                </div>
                <div>
                  <dt className="eyebrow">Min. spine degree</dt>
                  <dd><span className="math">m</span> = {caterpillarInfo.minDegree}</dd>
                </div>
                <div>
                  <dt className="eyebrow">Thrackle bound</dt>
                  <dd><span className="math">θ</span> = {caterpillarInfo.theta}</dd>
                </div>
                <div>
                  <dt className="eyebrow">Spectrum</dt>
                  <dd>{fullSpectrum ? `[0, ${caterpillarInfo.theta}]` : `[0, ${caterpillarInfo.spectrumMax}] ∪ {${caterpillarInfo.theta}}`}</dd>
                </div>
              </dl>
            </div>
            <div className="double-rule mt-3" />
            <div className="mt-2 min-h-[1.5em]">
              {error ? <p className="status status-error">{error}</p> : null}
              {notice ? <p data-testid="notice" className="status"><MathText text={notice} /></p> : null}
            </div>
          </header>

          <main className="mt-5 grid gap-x-8 gap-y-10 lg:grid-cols-[19rem_minmax(0,1fr)] xl:grid-cols-[19rem_minmax(0,1fr)_23rem]">
            <div className="space-y-9">
              <section>
                <div className="section-head"><span className="no">1</span><h2>Caterpillar</h2></div>
                <label htmlFor="sequence" className="eyebrow mb-1 block">Legs per spine vertex</label>
                <form onSubmit={(e) => { e.preventDefault(); initialize(); }} className="flex gap-2">
                  <input id="sequence" value={sequenceText} onChange={(e) => setSequenceText(e.target.value)} aria-label="Legs per spine vertex" className="field flex-1" placeholder="e.g. 2,0,1,3" />
                  <button type="submit" className="btn btn-solid">Build</button>
                </form>

                <div className="subhead eyebrow">Or at random</div>
                <div className="grid grid-cols-[1fr_auto_auto_auto] items-center gap-x-2 gap-y-2 text-[14px]">
                  <span>Spine vertices</span>
                  <input type="number" min={2} max={RANDOM_LIMITS.spine} value={randomSpec.spineMin} onChange={setRandom("spineMin")} aria-label="Minimum number of spine vertices" className="field field-num" />
                  <span className="text-ink-3">–</span>
                  <input type="number" min={2} max={RANDOM_LIMITS.spine} value={randomSpec.spineMax} onChange={setRandom("spineMax")} aria-label="Maximum number of spine vertices" className="field field-num" />
                  <span>Legs per vertex</span>
                  <input type="number" min={0} max={RANDOM_LIMITS.legs} value={randomSpec.legsMin} onChange={setRandom("legsMin")} aria-label="Minimum number of legs per spine vertex" className="field field-num" />
                  <span className="text-ink-3">–</span>
                  <input type="number" min={0} max={RANDOM_LIMITS.legs} value={randomSpec.legsMax} onChange={setRandom("legsMax")} aria-label="Maximum number of legs per spine vertex" className="field field-num" />
                  <span>Spine length <span className="math">k</span></span>
                  <select value={randomSpec.parity} onChange={setRandom("parity")} aria-label="Parity of the spine length" className="field col-span-3">
                    <option value="any">odd or even</option>
                    <option value="odd">odd</option>
                    <option value="even">even</option>
                  </select>
                </div>
                <button type="button" onClick={generateRandom} className="btn mt-3 w-full">Generate random caterpillar</button>
                <p className="hint mt-2">The two end vertices always get at least one leg.</p>
              </section>

              <section>
                <div className="section-head"><span className="no">2</span><h2>Algorithm</h2></div>
                <button type="button" onClick={runFullSpectrum} className="btn btn-solid w-full py-3">Run spectrum algorithm</button>
                <p className="hint mt-2">Starts at the zig-zag drawing and plays every number of crossings of the spectrum, from <span className="math">θ</span> down to 0.</p>
                <label className="mt-3 flex items-start gap-2 text-[14px]">
                  <input type="checkbox" checked={mergeUndo} onChange={(e) => setMergeUndo(e.target.checked)} className="check" />
                  <span>Undo auxiliary moves in one step <span className="hint">(the paper undoes them one at a time)</span></span>
                </label>

                <form onSubmit={submitTarget} className="subhead">
                  <label htmlFor="target-crossings" className="eyebrow mb-1 block">Target number of crossings</label>
                  <div className="flex gap-2">
                    <input id="target-crossings" type="number" min={0} max={graph.theta} step={1} value={targetText} onChange={(e) => setTargetText(e.target.value)} className="field flex-1" placeholder={`0 to ${graph.theta}`} />
                    <button type="submit" className="btn">Construct</button>
                  </div>
                </form>
                {endsAreLeaves ? <p className="hint mt-2">End vertices without legs are treated as leaves of their neighbors.</p> : null}

                <details className="mt-4">
                  <summary className="eyebrow select-none">How it works</summary>
                  <p className="hint mt-2">The routine follows the proofs in the paper. Odd spine: starting at the zig-zag convex thrackle, Phase 1 moves the feet of the internal spine vertices to their target regions, Phase 2 moves the feet of the two end vertices next to their parents, and then it recurses on the shorter caterpillar. Even spine: the feet of one end vertex are moved next to it (for <span className="math">m</span> = 2, one foot at a time on its journey around the circle), which leaves a caterpillar with an odd spine. Auxiliary swaps fill in every intermediate crossing count of the spectrum.</p>
                  <p className="hint mt-2">A target number of crossings is realized by the algorithm for a specific value: it starts at the convex thrackle of a smaller caterpillar (the removed feet stay next to their parents) and needs only <span className="math">O</span>(<span className="math">n</span>) local moves. Clicking a value of the spectrum that has not been visited yet does the same.</p>
                </details>
              </section>

              <section>
                <div className="section-head"><span className="no">3</span><h2>Manual moves</h2></div>
                <p className="hint">Click two vertices in the figure to swap them, or move all legs of a spine vertex at once.</p>
                <div className="mt-3 grid grid-cols-2 gap-x-2 gap-y-3">
                  <label><span className="eyebrow mb-1 block">Source legs</span><select value={batchSource} onChange={(e) => setBatchSource(Number(e.target.value))} className="field w-full">{graph.seq.map((_, i) => <option key={i} value={i}>v{i} ({graph.seq[i]} legs)</option>)}</select></label>
                  <label><span className="eyebrow mb-1 block">Over vertex</span><select value={batchTarget} onChange={(e) => setBatchTarget(Number(e.target.value))} className="field w-full">{graph.seq.map((_, i) => <option key={i} value={i}>v{i}</option>)}</select></label>
                  <label><span className="eyebrow mb-1 block">Target part</span><select value={batchTargetPart} onChange={(e) => setBatchTargetPart(e.target.value)} className="field w-full"><option value="spine">spine vertex only</option><option value="legs">legs only</option><option value="block">whole block</option></select></label>
                  <label><span className="eyebrow mb-1 block">Direction</span><select value={batchDirection} onChange={(e) => setBatchDirection(e.target.value)} className="field w-full"><option value="auto">auto</option><option value="cw">clockwise</option><option value="ccw">counterclockwise</option></select></label>
                </div>
                <button type="button" onClick={applyManualBatch} className="btn mt-3 w-full">Run batch move</button>
              </section>
            </div>

            <div className="min-w-0 space-y-9 xl:border-l xl:border-rule xl:pl-8">
              <figure ref={drawingRef}>
                <Drawing
                    order={order}
                    style={style}
                    selectedId={selectedId}
                    arrows={nextArrows}
                    showArrows={!isPlaying}
                    duration={REDUCED_MOTION ? 0 : Math.round(Math.min(420, stepDelay * 0.6))}
                    onVertexClick={handleSwapChoice}
                />

                <div className="mx-auto mt-4 flex max-w-[74vh] flex-wrap items-center gap-x-4 gap-y-3">
                  <div className="transport">
                    <PlayerButton icon="start" label="Go to start" onClick={() => goToStep(0)} disabled={timelineCursor <= 0} />
                    <PlayerButton icon="back" label="Step back" onClick={() => goToStep(timelineCursor - 1)} disabled={timelineCursor <= 0} />
                    <PlayerButton icon="play" label="Play" onClick={play} disabled={isPlaying || timeline.length < 2} primary />
                    <PlayerButton icon="pause" label="Pause" onClick={() => setPlaying(false)} disabled={!isPlaying} />
                    <PlayerButton icon="forward" label="Step forward" onClick={() => goToStep(timelineCursor + 1)} disabled={timelineCursor >= lastCursor} />
                    <PlayerButton icon="end" label="Go to end" onClick={() => goToStep(lastCursor)} disabled={timelineCursor >= lastCursor} />
                  </div>
                  <input type="range" min={0} max={Math.max(1, lastCursor)} step={1} value={timelineCursor} onChange={(e) => goToStep(Number(e.target.value))} disabled={timeline.length < 2} aria-label="Step" className="scrubber" />
                  <label className="flex items-center gap-2"><span className="eyebrow">Speed</span>
                    <select value={stepDelay} onChange={(e) => setStepDelay(Number(e.target.value))} className="field py-1">
                      {PLAYER_SPEEDS.map((speed) => <option key={speed.delay} value={speed.delay}>{speed.label}</option>)}
                    </select>
                  </label>
                </div>

                <figcaption className="caption mx-auto mt-3 max-w-[74vh]">
                  <b data-testid="step-counter">Step {timelineCursor} / {lastCursor}</b>
                  <span className="mx-2 text-ink-3">·</span>
                  <span data-testid="step-label"><MathText text={currentEntry?.label ?? ""} /></span>
                  {style.hasRemoved ? <span data-testid="removed-legend" className="hint mt-1 block">Gray vertices with pale edges are no longer part of the caterpillar the algorithm works on (induction step); they stay next to their parents.</span> : null}
                </figcaption>
              </figure>

              <section>
                <div className="section-head">
                  <h2>Spectrum</h2>
                  <span className="aside flex flex-wrap items-center gap-x-4 gap-y-1 text-[12.5px] text-ink-2">
                    <span><i className="swatch" style={{ background: "var(--color-blue)", borderColor: "var(--color-blue)" }} />current</span>
                    <span><i className="swatch" style={{ background: "var(--color-green-light)", borderColor: "#8fc763" }} />visited</span>
                    <span><i className="swatch" style={{ background: "var(--color-sheet)" }} />open</span>
                    {fullSpectrum ? null : <span><i className="swatch" style={{ background: "repeating-linear-gradient(135deg, transparent 0 2px, var(--color-ink-3) 2px 3px)" }} />not realizable</span>}
                    <button type="button" onClick={() => setVisited(new Set([currentCrossings]))} className="link-btn">Clear visited</button>
                  </span>
                </div>
                <div className="cells">
                  {Array.from({ length: graph.theta + 1 }, (_, i) => i).map((value) => {
                    const state = cellState(value);
                    return (
                        <button
                            key={value}
                            type="button"
                            data-state={state}
                            onClick={() => (visited.has(value) ? jumpToFirstCount(value) : constructDrawingWithCrossings(value))}
                            disabled={state === "void"}
                            title={state === "open" ? `Construct a drawing with ${value} crossings` : state === "void" ? "Not in the convex thrackle spectrum" : undefined}
                            className="cell"
                        >
                          {value}
                        </button>
                    );
                  })}
                </div>
              </section>
            </div>

            <div className="space-y-9 lg:col-span-2 xl:col-span-1 xl:border-l xl:border-rule xl:pl-8">
              <section>
                <div className="section-head"><h2>Crossings</h2></div>
                <div className="flex items-end gap-3">
                  <div data-testid="current-crossings" className="bignum">{currentCrossings}</div>
                  <div className="pb-1 text-[15px] leading-tight text-ink-2">of at most<br /><span className="math">θ</span> = <span className="text-ink">{graph.theta}</span></div>
                </div>
                <div className="gauge mt-4" aria-hidden="true"><span style={{ width: `${graph.theta > 0 ? (100 * currentCrossings) / graph.theta : 0}%` }} /></div>
                <div className="mt-3 flex items-baseline gap-2">
                  <span className="eyebrow flex-none">Legs</span>
                  <span className="min-w-0 break-words font-mono text-[12.5px]">{graph.seq.join(", ")}</span>
                </div>
              </section>

              <section>
                <div className="section-head">
                  <h2>Move log</h2>
                  <button type="button" onClick={() => pushInitialState(buildGraph(graph.seq), "Reset to zig-zag drawing.")} className="link-btn aside">Reset to zig-zag</button>
                </div>
                <div ref={logBoxRef} className="log">
                  {timeline.map((snapshot, index) => (
                      <button
                          key={index}
                          type="button"
                          ref={(node) => {
                            if (node) logItemRefs.current.set(index, node);
                            else logItemRefs.current.delete(index);
                          }}
                          onClick={() => goToStep(index)}
                          aria-current={index === timelineCursor ? "true" : undefined}
                          className="log-row"
                      >
                        <span className="no">{index}</span>
                        <span><MathText text={snapshot.entry.label} /></span>
                        <span className="count"><b>{snapshot.entry.to}</b>{snapshot.entry.delta !== 0 ? ` ${snapshot.entry.delta > 0 ? "+" : "−"}${Math.abs(snapshot.entry.delta)}` : ""}</span>
                      </button>
                  ))}
                </div>
              </section>
            </div>
          </main>
        </div>
      </div>
  );
}
