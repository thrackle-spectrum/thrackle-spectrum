# Caterpillar convex-crossing explorer

An interactive companion to a paper on the convex thrackle spectrum of caterpillars
(anonymous submission, double-blind review).

A caterpillar is drawn with its vertices on a circle. The tool runs the algorithms of
the paper step by step and shows how the drawing changes:

- **Spectrum algorithm:** starting at the convex thrackle (the zig-zag drawing with the
  maximum number of crossings), it realizes every number of crossings of the spectrum,
  down to a planar drawing.
- **Specific number of crossings:** it constructs a drawing with exactly the requested
  number of crossings using a linear number of local moves.

Every step swaps two consecutive parts of the circular order. The number of crossings
that the algorithm predicts for each step is checked against a direct count.

## Using the page

1. Enter the number of legs of each spine vertex (for example `2,0,1,3`) and press
   *Build*, or generate a random caterpillar.
2. Press *Run spectrum algorithm*, or enter a target number of crossings and press
   *Construct*. Clicking a value in the spectrum that has not been visited yet does the
   same.
3. Use the player below the figure to play, pause, and step through the moves. The move
   log on the right lists every step; click a row to jump to it.

Colors and drawing style follow the figures of the paper: spine edges are black, each
spine vertex and its feet share a color, and vertices that are no longer part of the
caterpillar the algorithm works on are drawn in gray.

## Running it locally

Requires Node.js 20 or newer.

```
npm install
npm run dev
```

## Tests

```
npm test
```

The test runs the algorithms on several thousand caterpillars and verifies every
drawing by counting its crossings by brute force. For small caterpillars it also
compares the spectrum with the crossing numbers of all circular layouts.

## Building

```
npm run build        # into dist/
npm run build:pages  # into docs/, which is what the published page serves
```

The build uses relative paths only and loads nothing from other servers.

## Layout of the code

- `src/algorithm/caterpillarSpectrum.js`: the algorithms, independent of the interface
- `src/App.jsx`, `src/index.css`: the interface
- `test/spectrum.test.mjs`: the test
