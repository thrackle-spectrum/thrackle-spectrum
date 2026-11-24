// Convex thrackle spectrum of caterpillars.
//
// This is an implementation of the constructive proofs of the theorems
// "odd-spine-spectrum", "specific-value-odd-spine", "even-spine-spectrum" and
// "specific-value-even-spine" of the paper in ../../paper/main.tex. Comments such as
// "Phase 1, Case 3" or "move (E)" refer to these proofs and to the appendix.
//
// Conventions
// -----------
// * A caterpillar is given as a sequence seq[0..n-1]: seq[i] is the number of legs of
//   the i-th vertex of a path. Vertex ids are `v{i}` for the path and `l{i}_{j}` for the
//   leaves, as in App.jsx. End vertices without legs are leaves themselves, so the
//   actual spine is obtained by trimming them (see `buildCaterpillar`).
// * The circular order is a doubly linked list of nodes; `next` is the clockwise
//   successor. Every node carries a block of vertices that stay next to it (processed
//   and relinked feet, see the running-time analyses in the paper), so that a local
//   move is a swap of two consecutive nodes and takes O(1) time.
// * "Up to a flip of the spine" is implemented by reversing the array of the spine
//   vertices and the reading direction of the list (`flip`); the drawing is not changed.
//   All the code below addresses the drawing through a view (`view`).
// * The algorithm never counts crossings. It tracks the number of crossings with the
//   changes predicted by the swap rule, Lemma "rebalance-region" and Lemma "swap".
//   test/spectrum.test.mjs checks every single prediction by brute force.

const STOP = Symbol("target reached");

function makeNode(id) {
  return {
    id,
    isSpine: false,
    idx: -1, // index on the current spine (spine nodes only)
    parent: null, // spine node (feet only)
    feet: [], // feet in the current caterpillar that are not processed (spine nodes only)
    pre: [], // block members counterclockwise of the node (nearest first)
    post: [], // block members clockwise of the node (nearest first)
    prev: null,
    next: null,
  };
}

/** Appends the vertex ids of the block of `node` to `out`, in clockwise order. */
export function blockIds(node, out = []) {
  for (let i = node.pre.length - 1; i >= 0; i -= 1) blockIds(node.pre[i], out);
  out.push(node.id);
  for (let i = 0; i < node.post.length; i += 1) blockIds(node.post[i], out);
  return out;
}

/**
 * Builds the nodes of the caterpillar and determines its spine.
 * An end vertex of the given path without legs is a leaf, hence a foot of its neighbor.
 */
function buildCaterpillar(seq) {
  if (!Array.isArray(seq) || seq.length === 0 || seq.some((x) => !Number.isInteger(x) || x < 0)) {
    throw new Error("The caterpillar must be given as a non-empty sequence of non-negative integers.");
  }
  const path = seq.map((_, i) => makeNode(`v${i}`));
  seq.forEach((legs, i) => {
    for (let j = 0; j < legs; j += 1) {
      const foot = makeNode(`l${i}_${j}`);
      foot.parent = path[i];
      path[i].feet.push(foot);
    }
  });
  let lo = 0;
  let hi = seq.length - 1;
  if (hi > lo && path[lo].feet.length === 0) {
    path[lo].parent = path[lo + 1];
    path[lo + 1].feet.unshift(path[lo]);
    lo += 1;
  }
  if (hi > lo && path[hi].feet.length === 0) {
    path[hi].parent = path[hi - 1];
    path[hi - 1].feet.push(path[hi]);
    hi -= 1;
  }
  const spine = path.slice(lo, hi + 1);
  spine.forEach((node, j) => {
    node.isSpine = true;
    node.idx = j;
  });
  return spine;
}

function spineDegree(S, j) {
  const k = S.length - 1;
  return S[j].feet.length + (k === 0 ? 0 : j === 0 || j === k ? 1 : 2);
}

/** Number of edges and thrackle bound of the caterpillar with spine S. */
function measure(S) {
  let edges = S.length - 1;
  let squares = 0;
  for (let j = 0; j < S.length; j += 1) {
    const deg = spineDegree(S, j);
    edges += S[j].feet.length;
    squares += deg * deg + S[j].feet.length;
  }
  return { edges, theta: (edges * (edges + 1) - squares) / 2 };
}

function describe(S) {
  const k = S.length - 1;
  const { theta } = measure(S);
  let minDegree = Infinity;
  for (let j = 0; j <= k; j += 1) minDegree = Math.min(minDegree, spineDegree(S, j));
  // Theorems "odd-spine-spectrum" and "even-spine-spectrum".
  const spectrumMax = k > 0 && k % 2 === 0 ? theta - (minDegree - 1) : theta;
  return { spineLength: k, theta, minDegree, spectrumMax };
}

/**
 * Basic data of the caterpillar given by `seq`: the length of its spine, its thrackle
 * bound theta, the minimum degree of a spine vertex, and spectrumMax such that the
 * convex thrackle spectrum is [0, spectrumMax] together with theta.
 */
export function describeCaterpillar(seq) {
  return describe(buildCaterpillar(seq));
}

export function inSpectrum(info, crossings) {
  return Number.isInteger(crossings) && crossings >= 0 && (crossings <= info.spectrumMax || crossings === info.theta);
}

class SpectrumEngine {
  constructor(seq, onEvent, target) {
    this.onEvent = onEvent || (() => {});
    this.target = target;
    this.S = buildCaterpillar(seq);
    this.k = this.S.length - 1;
    this.info = describe(this.S);
    this.c = 0; // predicted number of crossings of the current drawing
    this.moves = 0;
    this.levels = 0; // number of convex thrackles from which the algorithm (re)started
    this.ctx = "";
    this.aux = [];
    this.hold = 0; // > 0 while the values above the current one are not all realized yet
    this.flip = false;
    this.layoutReady = false; // the drawing is the convex thrackle of the current caterpillar
    this.needSync = false; // the feet arrays do not reflect the order of the feet
    this.undoing = false; // the current swaps reverse auxiliary moves
  }

  // ------------------------------------------------------------------ basics

  /**
   * A view of the current caterpillar. The mirrored view exchanges v_j with v_{k-j} and
   * clockwise with counterclockwise; `fwd` is the clockwise successor in the view.
   */
  view(mirrored) {
    const { S, k } = this;
    const reversed = mirrored !== this.flip;
    return {
      mirrored,
      V: mirrored ? (j) => S[k - j] : (j) => S[j],
      idx: mirrored ? (node) => k - node.idx : (node) => node.idx,
      fwd: reversed ? (n) => n.prev : (n) => n.next,
      bwd: reversed ? (n) => n.next : (n) => n.prev,
    };
  }

  /** Swaps two consecutive nodes; `delta` is the predicted change of the number of crossings. */
  swap(a, b, delta, what) {
    let left;
    let right;
    if (a.next === b) {
      left = a;
      right = b;
    } else if (b.next === a) {
      left = b;
      right = a;
    } else {
      throw new Error(`Internal error: ${a.id} and ${b.id} are not consecutive (${this.ctx}).`);
    }
    const p = left.prev;
    const n = right.next;
    p.next = right;
    right.prev = p;
    right.next = left;
    left.prev = right;
    left.next = n;
    n.prev = left;
    this.c += delta;
    this.moves += 1;
    this.onEvent({
      type: "swap",
      left,
      right,
      delta,
      crossings: this.c,
      settled: this.hold === 0,
      context: this.ctx,
      undo: this.undoing,
      label: `${this.ctx}: ${what} ${a.id} over ${b.id}`,
    });
    if (this.c === this.target) throw STOP;
  }

  /** An auxiliary move that removes exactly one crossing and is reversed by `undoAux`. */
  auxSwap(a, b, what = "auxiliary swap,") {
    this.swap(a, b, -1, what);
    this.aux.push([a, b, what]);
  }

  undoAux() {
    this.undoing = true;
    while (this.aux.length > 0) {
      const [a, b, what] = this.aux.pop();
      this.swap(a, b, +1, `undo ${what}`);
    }
    this.undoing = false;
  }

  /** A move that adds exactly one crossing, applied right after a swap and reversed at once (moves (P), (Q)). */
  blip(a, b, what) {
    this.swap(a, b, +1, what);
    this.swap(a, b, -1, `undo ${what}`);
  }

  /** The foot `x` is next to its parent and from now on belongs to the block of its parent. */
  merge(x, parent) {
    if (parent.prev === x) parent.pre.push(x);
    else if (parent.next === x) parent.post.push(x);
    else throw new Error(`Internal error: ${x.id} is not next to ${parent.id}.`);
    x.prev.next = x.next;
    x.next.prev = x.prev;
    x.prev = null;
    x.next = null;
  }

  setSpine(spine) {
    this.S = spine;
    this.k = spine.length - 1;
    spine.forEach((node, j) => {
      node.idx = j;
    });
  }

  /** A spine vertex without feet at the end of the spine becomes a foot of its neighbor. */
  demoteLast() {
    const { S, k } = this;
    const v = S[k];
    v.isSpine = false;
    v.parent = S[k - 1];
    S[k - 1].feet.push(v);
    this.setSpine(S.slice(0, k));
  }

  /** Reverses the spine without changing the drawing. */
  flipSpine(info) {
    const { k } = this;
    this.setSpine(this.S.slice().reverse());
    this.flip = !this.flip;
    if (info && info.minI >= 0) [info.minI, info.maxI] = [k - info.maxI, k - info.minI];
  }

  /** Rebuilds the feet arrays in the clockwise order of the (unmirrored) view. */
  syncFeet() {
    const W = this.view(false);
    for (const v of this.S) v.feet = [];
    const start = this.S[0];
    for (let node = W.fwd(start); node !== start; node = W.fwd(node)) {
      if (!node.isSpine) node.parent.feet.push(node);
    }
  }

  /**
   * The convex thrackle of the current caterpillar (proof of Theorem "le:claw"):
   * clockwise, v_0, L_1, v_2, L_3, ... and then L_0, v_1, L_2, v_3, ..., where L_j
   * denotes the feet of v_j.
   */
  buildThrackle() {
    const { S, k } = this;
    const right = [];
    const left = [];
    for (let j = 0; j <= k; j += 1) {
      if (j % 2 === 0) {
        right.push(S[j]);
        left.push(...S[j].feet);
      } else {
        right.push(...S[j].feet);
        left.push(S[j]);
      }
    }
    const order = [...right, ...left];
    order.forEach((node, i) => {
      node.next = order[(i + 1) % order.length];
      node.prev = order[(i + order.length - 1) % order.length];
    });
    this.flip = false;
    return order;
  }

  /**
   * The current caterpillar within the given one: the ids of its spine vertices, for each
   * of its feet the id of its parent, and for every removed vertex the id of the vertex
   * of the current caterpillar to whose block it belongs.
   */
  structure() {
    const spine = this.S.map((node) => node.id);
    const feet = {};
    const removed = {};
    const first = this.S[0];
    let node = first;
    do {
      if (!node.isSpine) feet[node.id] = node.parent.id;
      for (const id of blockIds(node)) {
        if (id !== node.id) removed[id] = node.id;
      }
      node = node.next;
    } while (node !== first);
    return { spine, feet, removed };
  }

  /**
   * The drawing is the convex thrackle of the current, smaller caterpillar, and the
   * algorithm continues in place (induction step without a restart).
   */
  announce() {
    this.onEvent({
      type: "continue",
      crossings: this.c,
      settled: this.hold === 0,
      structure: this.structure(),
      label: `Continue with the caterpillar with spine ${this.S.map((node) => node.id).join(",")}; the drawing is its convex thrackle, and the removed feet stay next to their parents`,
    });
  }

  /** Starts (again) from the convex thrackle of the current caterpillar. */
  start() {
    const nodes = this.buildThrackle();
    this.c = measure(this.S).theta;
    const plain = this.levels === 0 && this.S.every((node) => node.pre.length + node.post.length === 0);
    const spine = this.S.map((node) => node.id).join(",");
    this.onEvent({
      type: this.levels === 0 ? "init" : "restart",
      nodes,
      crossings: this.c,
      settled: true,
      structure: this.structure(),
      label: plain
        ? "Convex thrackle"
        : `${this.levels === 0 ? "Convex thrackle" : "Restart from the convex thrackle"} of the caterpillar with spine ${spine}; the removed feet stay next to their parents`,
    });
    this.levels += 1;
    this.layoutReady = true;
    this.needSync = false;
    if (this.c === this.target) throw STOP;
  }

  checkCount() {
    const { theta } = measure(this.S);
    if (this.c !== theta) throw new Error(`Internal error: ${this.c} crossings instead of the thrackle bound ${theta} (${this.ctx}).`);
  }

  // ----------------------------------------------------------------- driver

  run() {
    if (this.k === 0) {
      // A star (or a single edge): every circular layout is planar.
      this.c = 0;
      this.onEvent({ type: "init", nodes: this.buildThrackle(), crossings: 0, settled: true, label: "Star: the only number of crossings is 0" });
      return;
    }
    try {
      if (this.target !== null) this.reduceForTarget(this.target);
      this.start();
      while (this.k % 2 === 0) this.evenStep();
      this.oddLoop();
    } catch (signal) {
      if (signal !== STOP) throw signal;
    }
  }

  /** Theorem "odd-spine-spectrum": Phase 1, Phase 2, and the induction step. */
  oddLoop() {
    for (;;) {
      if (!this.layoutReady) this.start();
      else if (this.needSync) this.syncFeet();
      this.layoutReady = false;
      this.needSync = false;
      // The feet of v_0 are stored in clockwise and the feet of v_k in counterclockwise
      // order, such that for both of them feet[0] is at the boundary between the two
      // groups and the last one is the first to leave the bottom region in Phase 2.
      this.S[this.k].feet.reverse();
      this.checkCount();
      if (this.k === 1) {
        this.doubleStar();
        break;
      }
      this.phase1();
      this.phase2();
      if (this.c === 0) break;
      this.inductionStep();
    }
  }

  /** Base case k = 1: the feet of v_0 move one at a time over all the feet of v_1. */
  doubleStar() {
    const W = this.view(false);
    const [v0, v1] = this.S;
    this.ctx = "Double star";
    for (const x of v0.feet.slice()) {
      for (let i = 0; i < v1.feet.length; i += 1) this.swap(x, W.bwd(x), -1, "move");
    }
  }

  /**
   * Induction step: the feet of v_0 and v_k are next to their parents, so v_0 and v_k
   * become feet of v_1 and v_{k-1}. Then we remove further feet as long as the thrackle
   * bound stays at least the current number of crossings (running-time analysis).
   */
  inductionStep() {
    const { S, k } = this;
    const a = S[0];
    const b = S[k];
    a.isSpine = false;
    a.parent = S[1];
    S[1].feet.unshift(a);
    b.isSpine = false;
    b.parent = S[k - 1];
    S[k - 1].feet.push(b);
    this.setSpine(S.slice(1, k));
    this.reduce(this.c);
  }

  /**
   * Odd spine: removes feet of the end vertices of the spine, one at a time (or the
   * only foot of both of them, which shortens the spine by two), as long as the
   * thrackle bound of the resulting caterpillar is at least `bound`. A removed foot is
   * relinked next to its parent, i.e., it joins the block of its parent.
   */
  reduce(bound) {
    const S = this.S;
    let lo = 0;
    let hi = S.length - 1;
    let { edges, theta } = measure(S);
    for (;;) {
      const a = S[lo];
      const b = S[hi];
      if (a.feet.length > 1 || b.feet.length > 1) {
        const v = a.feet.length > 1 ? a : b;
        const removed = edges - (v.feet.length + 1); // a leg of v crosses all the edges not incident to v
        if (theta - removed < bound) break;
        v.post.push(v.feet.pop());
        theta -= removed;
        edges -= 1;
      } else if (hi - lo >= 3) {
        const removed = edges - 2 + (edges - 1 - 2);
        if (theta - removed < bound) break;
        a.post.push(a.feet.pop());
        b.post.push(b.feet.pop());
        theta -= removed;
        edges -= 2;
        a.isSpine = false;
        a.parent = S[lo + 1];
        S[lo + 1].feet.unshift(a);
        b.isSpine = false;
        b.parent = S[hi - 1];
        S[hi - 1].feet.push(b);
        lo += 1;
        hi -= 1;
      } else {
        break;
      }
    }
    if (lo > 0) this.setSpine(S.slice(lo, hi + 1));
  }

  /**
   * Theorems "specific-value-odd-spine" and "specific-value-even-spine": removes feet
   * as long as `target` stays in the spectrum of the resulting caterpillar.
   */
  reduceForTarget(target) {
    if (this.k % 2 === 1) {
      this.reduce(target);
      return;
    }
    let { edges, theta } = measure(this.S);
    const info = this.evenInfo();
    for (;;) {
      // v is the spine vertex whose feet are the first to be removed by the algorithm.
      const { v } = this.orientEven(info);
      const degree = spineDegree(this.S, v.idx);
      const reduced = theta - (edges - degree);
      const becomesOdd = v === this.S[this.k] && v.feet.length === 1;
      const minDegree = Math.min(info.m, degree - 1);
      if (becomesOdd ? target > reduced : target !== reduced && target > reduced - (minDegree - 1)) return;
      v.post.push(v.feet.pop());
      theta = reduced;
      edges -= 1;
      if (becomesOdd) {
        this.demoteLast();
        this.reduce(target);
        return;
      }
      info.m = minDegree;
      if (degree - 1 === 2) {
        if (info.minI < 0 || v.idx < info.minI) info.minI = v.idx;
        if (v.idx > info.maxI) info.maxI = v.idx;
      }
    }
  }

  // ------------------------------------------------- odd spine: Phase 1

  /** Phase 1: move all the feet of the internal spine vertices to their target regions. */
  phase1(pass = this.passPhase1) {
    const h = (this.k + 1) / 2;
    for (let i = 1; i < h; i += 1) {
      this.processInternal(this.view(false), i, pass); // v_i
      this.processInternal(this.view(true), i, pass); // v_{k-i}
    }
  }

  /**
   * In the view W, the vertex v = V(i) has i < (k+1)/2, that is, it is top-right or
   * bottom-left, and its feet move counterclockwise over V(i-1), V(i-3), ...
   */
  processInternal(W, i, pass) {
    const v = W.V(i);
    const feet = W.mirrored ? v.feet.slice().reverse() : v.feet.slice();
    for (const x of feet) {
      for (let j = i - 1; j >= 0; j -= 2) pass.call(this, W, x, i, W.V(j), j);
    }
  }

  passPhase1(W, x, i, u, j) {
    const v = W.V(i);
    const lu = u.feet.length;
    // Lemma "swap": the leg (v,x) crosses the legs of u and the spine edges of u not incident to v.
    const d = lu + (j === 0 ? 1 : 2) - (j === i - 1 ? 1 : 0);
    const name = `Phase 1 (${v.id})`;
    const yb = W.V(this.k).feet[0]; // the feet of V(k) and V(0) that are consecutive in the bottom region
    const xb = W.V(0).feet[0];
    if (d <= 1) {
      this.ctx = name;
      this.swap(x, u, -d, "move");
      return;
    }
    if (lu === 0) {
      // Case 1: one crossing is compensated by a foot of v_0 and a foot of v_k.
      this.ctx = `${name}, Case 1`;
      this.auxSwap(yb, xb);
      this.undoAux();
      this.swap(x, u, -d, "move");
      return;
    }
    // The feet of u are consecutive in the target region of u.
    let first = u.feet[0];
    while (W.bwd(first).parent === u) first = W.bwd(first);
    let last = u.feet[0];
    while (W.fwd(last).parent === u) last = W.fwd(last);
    const side = !W.bwd(first).isSpine ? "bwd" : !W.fwd(last).isSpine ? "fwd" : null;
    if (side !== null) {
      // Case 2: the target region of u contains a processed foot y of another spine vertex,
      // chosen next to a foot of u. Lemma "rebalance-region" for R = {feet of u, y}: y passes
      // all the feet of u, which yields the values c-1, ..., c-l(u).
      this.ctx = `${name}, Case 2`;
      const y = side === "bwd" ? W.bwd(first) : W.fwd(last);
      for (let r = lu; r > 0; r -= 1) this.auxSwap(y, side === "bwd" ? W.fwd(y) : W.bwd(y));
      if (d === lu + 2) {
        // One more value is needed, c-l(u)-1.
        if (W.fwd(yb) === xb) {
          // A foot of v_0 and a foot of v_k are consecutive.
          this.auxSwap(yb, xb);
        } else {
          // Otherwise, y is the only foot of v_0 or of v_k, and the move of y has brought a
          // foot y' of the other one of them next to a foot of u.
          const other = y === xb ? yb : xb;
          const z = side === "bwd" ? W.fwd(other) : W.bwd(other);
          if ((y !== xb && y !== yb) || z.parent !== u) throw new Error("Internal error: Phase 1, Case 2 expects a foot of v_0 or v_k next to a foot of u.");
          this.auxSwap(other, z);
        }
      }
      this.undoAux();
      this.swap(x, u, -d, "move");
      return;
    }
    // Case 3: u is a bottom vertex and the top region contains only the feet of u.
    this.ctx = `${name}, Case 3`;
    const w = W.V(0);
    const q = w.feet.length + (j === 1 ? 0 : 1); // crossings added by swapping a foot of u with w
    if (d <= q) {
      for (let r = d - 1; r > 0; r -= 1) this.auxSwap(yb, W.fwd(yb));
      this.undoAux();
      this.swap(x, u, -d, "move");
      return;
    }
    this.auxSwap(yb, xb);
    this.undoAux();
    const s = Math.ceil((d - 2) / q);
    const moved = [];
    for (let t = 0; t < s; t += 1) {
      const z = W.bwd(w);
      if (z.parent !== u) throw new Error("Internal error: Phase 1, Case 3 expects a foot of u next to w.");
      this.swap(z, w, +q, "auxiliary move of");
      moved.push(z);
    }
    this.swap(x, u, -d, "move");
    while (moved.length > 0) {
      const z = moved.pop();
      for (let r = q - 1; r > 0; r -= 1) this.auxSwap(yb, W.fwd(yb));
      this.undoAux();
      this.swap(z, w, -q, "move back");
    }
  }

  // ------------------------------------------------- odd spine: Phase 2

  /** Phase 2: move all the feet of v_0 and v_k into the top region, next to their parents. */
  phase2() {
    while (this.S[0].feet.length >= 2) this.journeyCase1(this.view(false));
    while (this.S[this.k].feet.length >= 2) this.journeyCase1(this.view(true));
    this.case2();
  }

  /** Phase 2, Case 1: in the view W, a foot of V(0) moves while another one stays in the bottom region. */
  journeyCase1(W) {
    const { k } = this;
    const h = (k + 1) / 2;
    const v0 = W.V(0);
    const vk = W.V(k);
    const x = v0.feet.pop();
    const xp = v0.feet[0]; // x'
    const y = vk.feet[0];
    this.ctx = `Phase 2, Case 1 (${v0.id})`;
    while (!W.fwd(x).isSpine) this.swap(x, W.fwd(x), -1, "move");
    for (let j = 1; j <= k; j += 2) {
      const u = W.V(j);
      const t = u.feet.length;
      let delta;
      if (j === k) {
        delta = t + 1;
        for (let r = t; r > 0; r -= 1) this.auxSwap(xp, W.bwd(xp));
      } else if (j < h) {
        delta = 2 - (j === 1 ? 1 : 0) - t;
        if (delta === 2) this.auxSwap(y, xp);
      } else {
        delta = t + 2;
        this.auxSwap(y, xp);
        if (t > 0) {
          let last = u.feet[0];
          while (W.fwd(last).parent === u) last = W.fwd(last);
          const a = W.fwd(last);
          for (let r = t; r > 0; r -= 1) this.auxSwap(a, W.bwd(a));
        }
      }
      this.undoAux();
      this.swap(x, u, -delta, "move");
    }
    while (W.fwd(x) !== v0) this.swap(x, W.fwd(x), -1, "move");
    this.merge(x, v0);
  }

  /** Phase 2, Case 2: each of v_0 and v_k has exactly one foot in the bottom region. */
  case2() {
    const { S, k } = this;
    const h = (k + 1) / 2;
    let tL = 0;
    let tR = 0;
    const bottomWithLegs = [];
    for (let j = 1; j < k; j += 1) {
      const legs = S[j].feet.length;
      const top = (j % 2 === 0) === (j < h);
      if (!top) {
        if (legs > 0) bottomWithLegs.push(j);
      } else if (j % 2 === 0) tR += legs;
      else tL += legs;
    }
    const onlyBottom = (j) => bottomWithLegs.length === 1 && bottomWithLegs[0] === j;
    let mirrored;
    let name;
    if (tL + tR === 0) {
      name = "2b";
      mirrored = onlyBottom(k - 1);
    } else if (tR === 0 || tL === 0) {
      name = "2a";
      mirrored = tL === 0;
    } else {
      name = "2c";
      mirrored = tL === 1 && S[2].feet.length === tR && onlyBottom(1);
    }
    const W = this.view(mirrored);
    const stats = mirrored ? { tL: tR, tR: tL } : { tL, tR };
    this.firstJourney(W, stats, name);
    this.secondJourney(W, stats, name);
  }

  /** Two consecutive feet of distinct spine vertices in the top region, if any. */
  topBoundary(W) {
    let f = W.fwd(W.V(this.k));
    while (!f.isSpine && !W.fwd(f).isSpine) {
      if (W.fwd(f).parent !== f.parent) return [f, W.fwd(f)];
      f = W.fwd(f);
    }
    return null;
  }

  /** Case 2: in the view W, the foot x of V(0) moves first, while the foot y of V(k) lies in the bottom region. */
  firstJourney(W, { tL, tR }, name) {
    const { k } = this;
    const h = (k + 1) / 2;
    const v0 = W.V(0);
    const vk = W.V(k);
    const x = v0.feet.pop();
    const y = vk.feet[0];
    this.ctx = `Phase 2, Case ${name}, first journey (${v0.id})`;
    while (!W.fwd(x).isSpine) this.swap(x, W.fwd(x), -1, "move");
    const firstTR = W.fwd(y); // the first top-right foot (if tR > 0)
    const pair = this.topBoundary(W);
    for (let j = 1; j <= k; j += 2) {
      const u = W.V(j);
      const t = u.feet.length;
      const delta = j === k ? 2 : j < h ? 2 - (j === 1 ? 1 : 0) - t : t + 2;
      let moveP = false;
      if (delta >= 2) {
        let r = delta - 1;
        // The leg of y crosses the legs of the top-left feet.
        for (let i = Math.min(r, tL); i > 0; i -= 1, r -= 1) this.auxSwap(y, W.bwd(y));
        if (r > 0 && tR > 0) {
          // Now the last top-left foot and the first top-right foot are consecutive.
          this.auxSwap(firstTR, W.bwd(firstTR));
          r -= 1;
        }
        if (r > 0) {
          const vk1 = W.V(k - 1);
          if (r !== 1 || W.bwd(y) !== vk1) throw new Error(`Internal error in Case ${name}: unexpected configuration in the first journey.`);
          if (vk1.feet.length === 0) this.auxSwap(y, vk1, "move (E),");
          else if (pair) this.auxSwap(pair[0], pair[1], "top-region swap,");
          else if (j !== k) moveP = true;
          else throw new Error(`Internal error in Case ${name}: no auxiliary move for the swap with ${u.id}.`);
        }
        this.undoAux();
      }
      // With move (P), the value skipped by the swap is realized right after it.
      if (moveP) this.hold += 1;
      this.swap(x, u, -delta, "move");
      if (moveP) {
        this.hold -= 1;
        const f = W.fwd(vk);
        if (f.isSpine || f.parent !== W.V(k - 1)) throw new Error("Internal error: move (P) is not applicable.");
        this.blip(f, vk, "move (P),");
      }
    }
    while (W.fwd(x) !== v0) this.swap(x, W.fwd(x), -1, "move");
    this.merge(x, v0);
  }

  /** Case 2: in the view W, the foot y of V(k) moves after the foot of V(0) has been processed. */
  secondJourney(W, { tL, tR }, name) {
    const { k } = this;
    const h = (k + 1) / 2;
    const v0 = W.V(0);
    const vk = W.V(k);
    const y = vk.feet.pop();
    this.ctx = `Phase 2, Case ${name}, second journey (${vk.id})`;
    const firstTR = W.fwd(y); // the first top-right foot (if tR > 0)
    while (!W.bwd(y).isSpine) this.swap(y, W.bwd(y), -1, "move");
    const pair = this.topBoundary(W);
    for (let j = k - 1; j >= 0; j -= 2) {
      const u = W.V(j);
      const t = u.feet.length;
      const delta = j === k - 1 ? 1 - t : j === 0 ? 1 : j >= h ? 2 - t : t + 2;
      let moveQ = false;
      if (delta >= 2) {
        let r = delta - 1;
        if (tL > 0 && tR > 0) {
          // The legs of the top-left feet cross the legs of the top-right feet.
          let f = firstTR;
          while (r > 0 && !f.isSpine) {
            const following = W.fwd(f);
            while (r > 0 && !W.bwd(f).isSpine && W.idx(W.bwd(f).parent) % 2 === 1) {
              this.auxSwap(f, W.bwd(f));
              r -= 1;
            }
            f = following;
          }
        }
        if (r > 0) {
          if (r !== 1) throw new Error(`Internal error in Case ${name}: unexpected configuration in the second journey.`);
          const v1 = W.V(1);
          const v2 = W.V(2);
          if (v2.feet.length === 0) {
            if (k < 5 || W.fwd(v0) !== v2) throw new Error("Internal error: move (U) is not applicable.");
            this.auxSwap(v2, v0, "move (U),");
          } else if (j !== 2) {
            throw new Error(`Internal error in Case ${name}: no auxiliary move for the swap with ${u.id}.`);
          } else if (v1.feet.length === 0) {
            moveQ = true;
          } else if (pair) {
            this.auxSwap(pair[0], pair[1], "top-region swap,");
          } else {
            throw new Error(`Internal error in Case ${name}: no auxiliary move for the swap with ${u.id}.`);
          }
        }
        this.undoAux();
      }
      // With move (Q), the value skipped by the swap is realized right after it.
      if (moveQ) this.hold += 1;
      this.swap(y, u, -delta, "move");
      if (moveQ) {
        this.hold -= 1;
        const v1 = W.V(1);
        const f = W.bwd(v1);
        if (f.isSpine || f.parent !== W.V(2)) throw new Error("Internal error: move (Q) is not applicable.");
        this.blip(f, v1, "move (Q),");
      }
    }
    while (W.bwd(y) !== vk) this.swap(y, W.bwd(y), -1, "move");
    this.merge(y, vk);
  }

  // ------------------------------------------------------------- even spine
  //
  // In the convex thrackle of a caterpillar with a spine of even length k, the feet of
  // v_{j+1} lie in the gap between v_j and v_{j+2} (indices modulo k+1), in clockwise
  // order v_j, L_{j+1}, v_{j+2}.

  /** Minimum degree m of a spine vertex, and the smallest and largest index of a spine vertex of degree 2. */
  evenInfo() {
    const { S, k } = this;
    const info = { m: Infinity, minI: -1, maxI: -1 };
    for (let j = 0; j <= k; j += 1) {
      const degree = spineDegree(S, j);
      if (degree < info.m) info.m = degree;
      if (degree === 2) {
        if (info.minI < 0) info.minI = j;
        info.maxI = j;
      }
    }
    return info;
  }

  /**
   * Chooses the orientation of the spine as in the proof of Theorem "even-spine-spectrum"
   * and returns the spine vertex v whose feet are removed first (for k = 2, also the
   * index i of the vertex over which they move).
   */
  orientEven(info) {
    const k = this.k;
    if (k === 2) {
      if (spineDegree(this.S, 1) === info.m) return { i: 1, v: this.S[2] };
      if (spineDegree(this.S, 0) !== info.m) this.flipSpine(info);
      return { i: 0, v: this.S[1] };
    }
    if (info.m >= 3) {
      if (this.S[0].feet.length < this.S[k].feet.length) this.flipSpine(info);
    } else if (info.minI > k - info.maxI) {
      this.flipSpine(info);
    }
    return { v: this.S[k] };
  }

  /** One step of the algorithm for a spine of even length; the drawing is a convex thrackle. */
  evenStep() {
    const info = this.evenInfo();
    if (this.k === 2) this.evenTwo(info);
    else if (info.m >= 3) this.evenLarge(info);
    else this.evenJourney(info);
    if (this.layoutReady) {
      this.checkCount();
      if (this.c > 0) this.announce();
    }
  }

  /** The case k = 2. */
  evenTwo(info) {
    const { i, v: mover } = this.orientEven(info);
    const W = this.view(false);
    const S = this.S;
    const m = info.m;
    const vi = S[i];
    const other = S[(i + 2) % 3]; // v_{i-1}, whose feet lie between v_{i+1} and v_i
    this.ctx = `Even spine, k = 2 (${mover.id})`;
    const moved = [];
    for (let t = mover.feet.length; t > 0; t -= 1) {
      const x = W.fwd(vi);
      if (x.parent !== mover) throw new Error("Internal error: expected a foot of v_{i+1} next to v_i.");
      if (moved.length > 0) {
        // The first moved foot is next to the feet of v_{i-1}, and its leg crosses their legs.
        for (let r = m - 2; r > 0; r -= 1) this.auxSwap(moved[0], W.bwd(moved[0]));
        this.undoAux();
      }
      this.swap(x, vi, -(m - 1), "move");
      moved.push(x);
    }
    for (const x of moved) {
      for (let r = other.feet.length; r > 0; r -= 1) this.swap(x, W.bwd(x), -1, "move");
    }
    // Now the feet of v_{i+1} are next to v_{i+1}, and their legs cross no edge.
    for (const x of moved) this.merge(x, mover);
    mover.feet = [];
    if (i === 1) {
      // v_2 becomes a foot of v_1; the drawing is the convex thrackle for the spine (v_0, v_1).
      this.demoteLast();
      this.needSync = true;
    }
    // Otherwise, v_1 now has degree 2, and the drawing is the convex thrackle of the new caterpillar.
    this.layoutReady = true;
  }

  /** The case k >= 4 and m >= 3. */
  evenLarge(info) {
    this.orientEven(info); // now l(v_0) >= l(v_k)
    const W = this.view(false);
    const { S, k } = this;
    const m = info.m;
    const theta = this.c;

    // The values close to the thrackle bound: theta - r for m - 1 <= r < l(v_k).
    const lk = S[k].feet.length;
    if (lk > m - 1) {
      let i = k - 1;
      while (spineDegree(S, i) !== m) i -= 1;
      if (this.target === null) {
        for (let r = m - 1; r < lk; r += 1) this.nearThrackle(W, i, m, r);
      } else if (theta - this.target >= m - 1 && theta - this.target < lk) {
        this.nearThrackle(W, i, m, theta - this.target);
      }
    }

    // The path S* = (s_0, v_0, ..., v_k), where s_0 is the foot of v_0 that follows v_k,
    // plays the role of a spine of odd length whose end vertex s_0 has no feet.
    this.syncFeet();
    const s0 = W.fwd(S[k]);
    if (S[0].feet[0] !== s0) throw new Error("Internal error: s_0 is not the first foot of v_0.");
    S[0].feet.shift();
    s0.isSpine = true;
    s0.parent = null;
    this.setSpine([s0, ...S]);
    const K = this.k;
    this.S[K].feet.reverse();
    this.phase1(this.passPhase1Even);
    this.phase2Even();

    // The feet of v_k are next to v_k: v_k becomes a foot of v_{k-1}, and the spine has odd length.
    const path = this.S;
    s0.isSpine = false;
    s0.parent = path[1];
    path[1].feet.push(s0);
    this.setSpine(path.slice(1));
    this.demoteLast();
    this.reduce(this.c);
    this.layoutReady = false;
  }

  /**
   * Realizes theta - r, for m - 1 <= r < l(v_k), from the convex thrackle and returns to
   * it: feet of v_{j+1} move over v_j for j = k-1, ..., i+1, each removing l(v_j) + 1
   * crossings, and the band at v_i removes the rest: feet of v_{i+1} move over v_i, each
   * removing m - 1 crossings, and then over feet of v_{i-1}, each removing one crossing.
   */
  nearThrackle(W, i, m, r) {
    const { S, k } = this;
    this.ctx = `Close to the thrackle bound (${this.c - r})`;
    let rest = r;
    const plan = [];
    for (let j = k - 1; j > i; j -= 1) {
      const removed = S[j].feet.length + 1;
      const count = Math.min(S[j + 1].feet.length, Math.floor((rest - (m - 1)) / removed));
      if (count > 0) {
        plan.push([j, count, removed]);
        rest -= count * removed;
      }
    }
    const lp = S[i - 1].feet.length;
    const over = Math.max(1, Math.ceil(rest / (m - 1 + lp))); // feet moved over v_i
    if (over > S[i + 1].feet.length || over * (m - 1) > rest) throw new Error("Internal error: the band cannot realize the value.");
    let swaps = rest - over * (m - 1);
    const done = [];
    const move = (a, b, removed) => {
      this.swap(a, b, -removed, "auxiliary move of");
      done.push([a, b, removed]);
    };
    this.hold += 1;
    for (const [j, count, removed] of plan) {
      for (let t = 0; t < count; t += 1) {
        const x = W.fwd(S[j]);
        if (x.parent !== S[j + 1]) throw new Error("Internal error: expected a foot of v_{j+1} next to v_j.");
        move(x, S[j], removed);
      }
    }
    for (let t = 0; t < over; t += 1) {
      const x = W.fwd(S[i]);
      if (x.parent !== S[i + 1]) throw new Error("Internal error: expected a foot of v_{i+1} next to v_i.");
      move(x, S[i], m - 1);
      for (let w = Math.min(swaps, lp); w > 0; w -= 1, swaps -= 1) move(x, W.bwd(x), 1);
    }
    this.hold -= 1;
    while (done.length > 0) {
      const [a, b, removed] = done.pop();
      this.swap(a, b, +removed, "undo auxiliary move of");
    }
  }

  /** Phase 1 for the path S*: the auxiliary swaps between feet of the two end vertices are replaced. */
  passPhase1Even(W, x, i, u, j) {
    const { S, k: K } = this;
    const v = W.V(i);
    const lu = u.feet.length;
    const d = lu + (j === 0 ? 1 : 2) - (j === i - 1 ? 1 : 0);
    this.ctx = `Phase 1 (${v.id})`;
    let r = d - 1;
    const s0 = S[0];
    const s1 = S[1];
    const beforeLast = S[K - 1]; // s_{K-1} = v_{k-1}
    if (r > 0 && (u === S[K] || u === beforeLast || u === s1)) {
      // The last foot of v_{k-1} in the top region moves clockwise over the bottom-left
      // feet that follow it and then over s_0; then the next foot of v_{k-1} does the same.
      // The first foot of v_{k-1} moves over v_k without auxiliary swaps: the values in
      // between are those close to the thrackle bound, or they are not in the spectrum.
      const base = this.view(false);
      let index = beforeLast.feet.length - 1;
      while (r > 0 && beforeLast.feet[index] !== x) {
        const z = beforeLast.feet[index];
        if (!z) throw new Error("Internal error: Phase 1 (even) has run out of auxiliary swaps.");
        index -= 1;
        for (;;) {
          const following = base.fwd(z);
          if (r === 0 || (following !== s0 && (following.isSpine || following.parent === beforeLast))) break;
          this.auxSwap(z, following);
          r -= 1;
        }
      }
    } else if (r > 0) {
      // On the side of the feet of u towards the middle of its target region, there are
      // at least two feet of other vertices: the first one passes the feet of u, and then
      // the second one passes one foot of u.
      let first = u.feet[0];
      while (W.bwd(first).parent === u) first = W.bwd(first);
      const y = W.bwd(first);
      const y2 = W.bwd(y);
      if (y.isSpine || y2.isSpine) throw new Error("Internal error: Phase 1 (even) expects two feet next to the feet of u.");
      for (let t = Math.min(r, lu); t > 0; t -= 1, r -= 1) this.auxSwap(y, W.fwd(y));
      if (r > 0) {
        if (r !== 1) throw new Error("Internal error: Phase 1 (even) needs too many auxiliary swaps.");
        this.auxSwap(y2, W.fwd(y2));
      }
    }
    this.undoAux();
    this.swap(x, u, -d, "move");
  }

  /** Phase 2 for the path S*: move all the feet of v_k into the top region, next to v_k. */
  phase2Even() {
    const { S, k: K } = this;
    const h = (K + 1) / 2;
    const W = this.view(true); // V(0) = v_k, and the feet of v_k move clockwise in this view
    const vk = S[K];
    // A foot of v_{k-1} and a foot of s_1 = v_0 that are consecutive in the top region.
    const p = S[K - 1].feet[S[K - 1].feet.length - 1];
    const q = this.view(false).fwd(p);
    if (q.isSpine || q.parent !== S[1]) throw new Error("Internal error: Phase 2 (even) expects a foot of v_{k-1} next to a foot of v_0.");
    this.ctx = `Phase 2 (${vk.id})`;
    while (vk.feet.length > 0) {
      const x = vk.feet.pop();
      while (!W.fwd(x).isSpine) this.swap(x, W.fwd(x), -1, "move");
      for (let j = 1; j <= K; j += 2) {
        const u = W.V(j);
        const t = u.feet.length;
        const delta = j === K ? 1 : j < h ? 2 - (j === 1 ? 1 : 0) - t : t + 2;
        if (delta >= 2) {
          if (j < h) throw new Error("Internal error: Phase 2 (even) expects every bottom vertex to have feet.");
          // u is an internal top vertex: one swap in the top region, and the foot that
          // follows the feet of u in the bottom region passes them.
          this.auxSwap(p, q, "top-region swap,");
          let last = u.feet[0];
          while (W.fwd(last).parent === u) last = W.fwd(last);
          const a = W.fwd(last);
          if (a.isSpine) throw new Error("Internal error: Phase 2 (even) expects a foot next to the feet of u.");
          for (let r = t; r > 0; r -= 1) this.auxSwap(a, W.bwd(a));
          this.undoAux();
        }
        this.swap(x, u, -delta, "move");
      }
      while (W.fwd(x) !== vk) this.swap(x, W.fwd(x), -1, "move");
      this.merge(x, vk);
    }
  }

  /** The case k >= 4 and m = 2: the journey of a foot f of v_k. */
  evenJourney(info) {
    this.orientEven(info); // now min I <= k - max I
    const W = this.view(false);
    const { S, k } = this;
    const vk = S[k];
    const f = W.bwd(S[0]); // the foot of v_k that precedes v_0
    if (f.parent !== vk) throw new Error("Internal error: expected a foot of v_k next to v_0.");
    if (vk.feet[vk.feet.length - 1] !== f) vk.feet.reverse();
    if (vk.feet.pop() !== f) throw new Error("Internal error: the feet of v_k are out of order.");

    // For every index t, the nearest indices before and after t of spine vertices with feet other than f.
    const before = new Array(k + 1);
    const after = new Array(k + 1);
    for (let t = 0, last = -1; t <= k; t += 1) {
      before[t] = last;
      if (S[t].feet.length > 0) last = t;
    }
    for (let t = k, next = k + 1; t >= 0; t -= 1) {
      after[t] = next;
      if (S[t].feet.length > 0) next = t;
    }
    const tables = { iStar: info.minI, before, after };

    const name = `Journey of ${f.id}`;
    for (let s = 0; s <= k - 2; s += 2) {
      const vs = S[s];
      if (W.fwd(f) !== vs) throw new Error("Internal error: the journey has left its route.");
      const degree = spineDegree(S, s);
      this.ctx = `${name}, auxiliary moves`;
      this.reserve(W, s, degree - 1, tables);
      this.ctx = name;
      this.swap(f, vs, -degree, "move");
      while (!W.fwd(f).isSpine) this.swap(f, W.fwd(f), -1, "move");
    }
    this.merge(f, vk);
    // The drawing is a convex thrackle of the caterpillar without f.
    if (vk.feet.length === 0) {
      this.demoteLast();
      this.needSync = true;
    }
    this.layoutReady = true;
  }

  /**
   * Claim "reserve": before f passes v_s, realizes the next `need` smaller values by
   * auxiliary moves that do not involve f, and then reverses these moves.
   */
  reserve(W, s, need, { iStar, before, after }) {
    const { S, k } = this;
    const legs = (t) => S[t].feet.length;

    // The choice of u = v_i and of the range a..b.
    const forZero = () => (iStar >= 1 ? [iStar, 0, iStar] : legs(1) >= 1 ? [0, 0, 1] : [1, 0, 1]);
    let choice;
    if (s === 0) choice = forZero();
    else if (legs(s) === 0) {
      if (iStar < s) choice = forZero();
      else {
        const t = after[s];
        if (t > k) throw new Error("Internal error: no foot for the auxiliary moves.");
        choice = [t - 1, t - 1, t];
      }
    } else if (iStar < s) choice = legs(s - 1) >= 1 ? [iStar, iStar, s] : [s - 1, 0, s];
    else if (iStar >= s + 2) choice = [iStar, s, iStar];
    else choice = [iStar, s, k];
    const [i, a, b] = choice;
    const u = S[i];

    // Root moves: the feet of v_{i+1} move over u and then past the p feet of v_{i-1};
    // finally, the feet of v_{i-1} move over u. Each of them removes one crossing.
    const p = i - 1 >= a ? legs(i - 1) : 0;
    const q = i + 1 <= b ? legs(i + 1) : 0;
    const rootCount = q * (p + 1) + p;
    const rootDone = [];
    let state = { walker: null, walked: 0, over: 0 };
    const rootForward = () => {
      const previous = state;
      let x;
      let y;
      if (state.walker && state.walked < p) {
        x = state.walker;
        y = W.bwd(x);
        state = { ...state, walked: state.walked + 1 };
      } else if (state.over < q) {
        x = W.fwd(u);
        y = u;
        if (x.parent !== S[i + 1]) throw new Error("Internal error: expected a foot of v_{i+1} next to u.");
        state = { walker: x, walked: 0, over: state.over + 1 };
      } else {
        x = W.bwd(u);
        y = u;
        if (x.parent !== S[i - 1]) throw new Error("Internal error: expected a foot of v_{i-1} next to u.");
      }
      this.swap(x, y, -1, "root move of");
      rootDone.push([x, y, previous]);
    };
    const rootBack = () => {
      const [x, y, previous] = rootDone.pop();
      this.swap(x, y, +1, "undo root move of");
      state = previous;
    };

    // Groups: the feet of v_t with |t - i| >= 2 move over the neighbor u_x of v_t towards u.
    const groups = [];
    let total = rootCount;
    let lo = i - 2 >= a ? (legs(i - 2) > 0 ? i - 2 : before[i - 2]) : -1;
    let hi = i + 2 <= b ? (legs(i + 2) > 0 ? i + 2 : after[i + 2]) : k + 1;
    while (total < need) {
      const useLo = lo >= a && (hi > b || i - lo <= hi - i);
      if (!useLo && hi > b) throw new Error("Internal error: not enough auxiliary moves.");
      const t = useLo ? lo : hi;
      const ux = useLo ? S[t + 1] : S[t - 1];
      const group = { t, ux, towardsEnd: useLo, size: legs(t), removed: ux.feet.length + 1, moved: [] };
      groups.push(group);
      total += group.size * group.removed;
      if (useLo) lo = before[t];
      else hi = after[t];
    }
    // Sort the groups by the number of crossings removed by one foot (counting sort).
    const buckets = Array.from({ length: need + 1 }, () => []);
    for (const group of groups) {
      if (group.removed > need) throw new Error("Internal error: a group removes too many crossings.");
      buckets[group.removed].push(group);
    }
    const sorted = buckets.flat();
    const smaller = new Array(need + 1); // smaller[A]: number of groups with removed <= A
    for (let A = 0, count = 0; A <= need; A += 1) {
      count += buckets[A].length;
      smaller[A] = count;
    }
    const groupForward = (group) => {
      const x = group.towardsEnd ? W.bwd(group.ux) : W.fwd(group.ux);
      if (x.parent !== S[group.t]) throw new Error("Internal error: expected a foot of v_t next to u_x.");
      this.swap(x, group.ux, -group.removed, "auxiliary move of");
      group.moved.push(x);
    };
    const groupBack = (group) => {
      this.swap(group.moved.pop(), group.ux, +group.removed, "undo auxiliary move of");
    };

    // Realize c - 1, ..., c - need, in this order. `open` lists the groups (1-based, in
    // sorted order) that still have feet to move; the smallest index is on top.
    const c = this.c;
    const open = [];
    for (let j = sorted.length; j >= 1; j -= 1) open.push(j);
    this.hold += 1;
    for (let step = 1; step <= need; step += 1) {
      if (rootDone.length < rootCount) {
        rootForward();
      } else {
        const j = open[open.length - 1];
        const group = sorted[j - 1];
        if (!group) throw new Error("Internal error: no auxiliary move left.");
        groupForward(group);
        if (group.moved.length === group.size) open.pop();
        // Restore removed - 1 crossings with the groups before j and with root moves.
        let A = group.removed - 1;
        let jj = Math.min(j - 1, smaller[A]);
        while (A > 0 && jj >= 1) {
          const other = sorted[jj - 1];
          const count = Math.min(other.moved.length, Math.floor(A / other.removed));
          if (count > 0) {
            for (let t = 0; t < count; t += 1) groupBack(other);
            open.push(jj);
            A -= count * other.removed;
          }
          jj = Math.min(jj - 1, smaller[A]);
        }
        if (A > rootDone.length) throw new Error("Internal error: cannot restore the crossings.");
        for (; A > 0; A -= 1) rootBack();
      }
      if (this.c !== c - step) throw new Error("Internal error: the auxiliary moves missed a value.");
    }
    this.hold -= 1;
    // Return to the drawing before the auxiliary moves.
    for (const group of sorted) while (group.moved.length > 0) groupBack(group);
    while (rootDone.length > 0) rootBack();
  }
}

// ------------------------------------------------------------------ public API

/**
 * Runs the algorithm and reports every drawing as an event:
 *   { type: "init" | "restart", nodes, crossings, label }   a convex thrackle (nodes in clockwise order)
 *   { type: "swap", left, right, delta, crossings, label }   two consecutive nodes are swapped
 *   { type: "continue", crossings, label }                   the drawing is unchanged; the algorithm
 *                                                            continues with a smaller caterpillar
 * The events "init", "restart", and "continue" carry `structure` = { spine, feet, removed }, which
 * describes the caterpillar the algorithm works on from now on (see `SpectrumEngine.structure`).
 * A swap that reverses an auxiliary move has `undo` set.
 * Use `blockIds(node)` to obtain the vertices of a node. An event has `settled` set if
 * every value of the spectrum from its number of crossings up to the thrackle bound has
 * been realized. If `target` is given, the algorithm for a specific number of crossings
 * is used and stops as soon as the drawing has `target` crossings.
 * Returns { spineLength, theta, minDegree, spectrumMax, moves, levels, crossings }.
 */
export function runSpectrum(seq, onEvent, { target = null } = {}) {
  const engine = new SpectrumEngine(seq, onEvent, target);
  const info = engine.info;
  if (target !== null && !inSpectrum(info, target)) {
    throw new Error(
      info.spectrumMax < info.theta - 1
        ? `The number of crossings must be ${info.theta} or an integer between 0 and ${info.spectrumMax}.`
        : `The number of crossings must be an integer between 0 and ${info.theta}.`
    );
  }
  engine.run();
  return { ...info, moves: engine.moves, levels: engine.levels, crossings: engine.c };
}

/** Maintains the circular order as an array of vertex ids while the events arrive. */
export function makeOrderTracker() {
  let order = [];
  return {
    get order() {
      return order;
    },
    apply(event) {
      if (event.type === "continue") return order;
      if (event.type === "swap") {
        const left = blockIds(event.left);
        const right = blockIds(event.right);
        const n = order.length;
        const start = order.indexOf(left[0]);
        if (order[(start + left.length) % n] !== right[0]) throw new Error("Internal error: the swapped blocks are not consecutive.");
        for (let t = 0; t < right.length; t += 1) order[(start + t) % n] = right[t];
        for (let t = 0; t < left.length; t += 1) order[(start + right.length + t) % n] = left[t];
      } else {
        const next = event.nodes.flatMap((node) => blockIds(node));
        // Keep the first spine vertex where it was, so that a restart looks as similar as possible.
        const anchor = order.indexOf(next[0]);
        order = anchor > 0 ? [...next.slice(next.length - anchor), ...next.slice(0, next.length - anchor)] : next;
      }
      return order;
    },
  };
}

/**
 * Enumerates drawings whose numbers of crossings cover the whole convex thrackle
 * spectrum. Returns the data of `runSpectrum` and `steps`, where every step is
 * { type, order, crossings, delta, settled, label, structure, undo, merged } and `order`
 * lists the vertex ids clockwise. `structure` is the caterpillar the algorithm works on
 * at this step (null for a star). With the option `mergeUndo`, consecutive swaps that
 * reverse auxiliary moves are reported as a single step (`merged` is their number).
 */
export function enumerateSpectrum(seq, options = {}) {
  const { mergeUndo = false, ...runOptions } = options;
  const tracker = makeOrderTracker();
  const steps = [];
  let structure = null;
  const result = runSpectrum(
    seq,
    (event) => {
      const order = tracker.apply(event).slice();
      if (event.structure) structure = event.structure;
      const undo = event.undo === true;
      const last = steps[steps.length - 1];
      if (mergeUndo && undo && last && last.undo) {
        last.order = order;
        last.crossings = event.crossings;
        last.delta += event.delta;
        last.settled = event.settled;
        last.merged += 1;
        last.label = `${event.context}: undo ${last.merged} auxiliary moves`;
        return;
      }
      steps.push({ type: event.type, order, crossings: event.crossings, delta: event.delta ?? 0, settled: event.settled, label: event.label, structure, undo, merged: 1 });
    },
    runOptions
  );
  return { ...result, steps };
}

/** A circular layout (clockwise order of the vertex ids) with exactly `crossings` crossings. */
export function drawingWithCrossings(seq, crossings) {
  const tracker = makeOrderTracker();
  const result = runSpectrum(seq, (event) => tracker.apply(event), { target: crossings });
  if (result.crossings !== crossings) throw new Error(`Internal error: stopped at ${result.crossings} instead of ${crossings} crossings.`);
  return tracker.order.slice();
}
