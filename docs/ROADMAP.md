# Roadmap — blueprint statement to Lean declaration

Every labelled statement of `/home/alvaro/claude/schoenflies/jordan_schoenflies.tex`, with where
it lives in this library and whether it is finished. Work is scheduled off the blueprint's
**Appendix A**, the machine-generated statement-level citation index, rather than off the
milestone list: Appendix A repeatedly reveals substantial statements with no internal
prerequisites that can be built in parallel, far ahead of the critical path.

Status vocabulary:

| | |
|---|---|
| **done** | proved outright; nothing assumed beyond Mathlib |
| **conditional** | proved, but with a named hypothesis that a later module must discharge. Never a `sorry` — see the standing rule in `AGENTS.md` |
| **partial** | some clauses proved, others not stated at all |
| **open** | not started |

Keep this file honest. A "done" that is really a "conditional" costs the next agent a day.

## Live obligations

These are the only statements assumed anywhere in the library. Each is a `def … : Prop` that
some theorem takes as a hypothesis, so the axiom audit (`docs/audit-axioms.py`) stays a real
guarantee and an interface defect surfaces at the consumer rather than at the end.

| Assumed | Declared in | Blocks | Notes |
|---|---|---|---|
| `Schoenflies.SquaresTwoConnected` | `ArcComplement.lean` | `thm:arc-complement`, hence `lem:accessible-dense`, hence **`thm:jordan`** | a subdivided axis-parallel square boundary is 2-connected. The blueprint gets 2-connectivity of each block by iterating `lem:union-two-connected` over the squares, which presupposes it for one square. **This is the only thing between the library and the Jordan curve theorem.** |
| `Schoenflies.IsPolyArcCarrier` | `ArcCollars.lean` | `Schoenflies.HasArcCollars`, hence `lem:crosscut-at-most-two`, hence `thm:general-crosscut` | every simple polygonal arc is the carrier of a `PolyArc`. The arc analogue of the realization theorem, which `Realization.lean` already does for closed curves |

### What the no-`sorry` rule caught

`Graph.CrosscutEncloses` stood on `main` as an assumed hypothesis for a whole wave, and is
**false**. Nothing in its hypotheses stopped the crosscut from being drawn *through* `x`: take
the unit square cycle with cut points `(0,0)` and `(1,1)`, let `R` be the two edges
`(0,0) → (1/2,1/2) → (1,1)`, and let `x = (2/5, 2/5)`. Every field of `IsCycleCrosscut` holds,
`x` is inside the cycle, and `x` lies *on* both spliced curves, so it is inside neither.

The repair was one clause, `x ∈ exterior H drawing`, which the consumer already had. Had the
gap been a `sorry`, it would have been filled in eventually and the falsity discovered only
then, with everything written in the meantime resting on it. The counterexample is recorded in
`OuterChain.lean` where the false version stood.

## Part I — the Jordan curve theorem

### Foundation (Layers 0–6)

| Statement | Status | Where |
|---|---|---|
| `lem:polygonal-connected` | done | `PolygonalCarrier.lean`, `PolyLocal.lean`, `LocallyPolygonal.lean` |
| `lem:finite-polygonal-union` | done | `SimpleArc.lean` |
| `lem:nearest-segment` | done | `Plane.lean` (`notMem_of_mem_segment_of_isMinOn`) |
| `lem:compact-separation` | done | `Plane.lean` (`exists_dist_pos`, `exists_thickening_subset`, `exists_ball_subset_diff`) |
| `lem:diameter-closure` | done | Mathlib `Metric.diam_closure` |
| `lem:nested-compact` | done | `Plane.lean` (`eq_singleton_iInter_of_diam_tendsto_zero`) |
| `lem:clopen-component` | done | `Plane.lean` (`connectedComponentIn_eq_of_frontier_disjoint`), `Topology.lean` |
| `lem:polygonal-collar` (a) | done | `Compose.lean` (`polygonal_collar`), `StripLocal.lean` (`exists_two_sided_collar`) |
| `lem:polygonal-collar` (b) | done for a `PolyArc` | `ArcCollars.lean` |
| `lem:parity-subdivision` | done | `Parity.lean` (`parity_subdivide`) |
| `lem:polygon-parity` | done | `Parity.lean` |
| `lem:polygonal-overlay` | done | `Overlay.lean`, `OverlayGraph.lean` (`polygonal_overlay`) |

### Polygonal separation

| Statement | Status | Where |
|---|---|---|
| `thm:polygonal-jordan` (H7) | done | `PolygonalJordan.lean` (`ClosedPolygon.polygonal_jordan`), `PrePolygonSep.lean` |
| `def:separating`, `lem:absorption`, `lem:crosscut-cells` | done | `CrosscutCells.lean` |
| `lem:parity-splitting` | done | `ParitySplitting.lean` |
| `thm:polygonal-crosscut` | done | `PolygonalCrosscut.lean` (`polygonal_crosscut`) |
| `cor:alternating-crosscuts` | done | `AlternatingCrosscuts.lean` |
| realization theorem | done | `Realization.lean` — every set-level polygonal Jordan curve admits a `ClosedPolygon` presentation, with prescribed arcs. Not a blueprint statement; it is the bridge the blueprint takes for granted |

### Graph theory

| Statement | Status | Where |
|---|---|---|
| `lem:cycle-criterion` | done | `Graph/Cycle.lean` |
| `lem:three-leaf-tree` | done | `Graph/Tree.lean` (`IsTree.three_leaves`) |
| `lem:union-two-connected` | done | `Graph/TwoConnected.lean` (`IsTwoConnected.union`) |
| `lem:subdivision-ear-preserve` | done | `Graph/Ear.lean` |
| `lem:relative-ear` | done | `Graph/RelativeEar.lean` |
| `lem:polygonal-redrawing` | done | `Graph/Redrawing.lean` |
| `lem:k33`, `cor:k33-subdivision` (H8) | done | `Graph/K33Land.lean` (`k33Graph_not_exists_isDrawing`, `IsArcK33.elim`) |
| `lem:face-cycles` | done | `FaceCyclesLand.lean` (`face_cycles'`) |
| `lem:outer-chain` (H9) | **done** | `OuterChain.lean`, closed in `OuterChainClosed.lean` (`outer_chain'`) from `CrosscutExists.lean` + `CrosscutEncloses.lean` |

### The Jordan curve theorem

| Statement | Status | Where |
|---|---|---|
| `lem:jordan-circle` | done | `ModelCurve.lean`, `Subarc.lean`, `TwoArcs.lean` |
| `prop:jordan-disconnected` | done | `JordanSeparates.lean` |
| `thm:arc-complement` | conditional (`SquaresTwoConnected`) | `ArcComplement.lean`, on `ArcComplementPrep.lean` |
| `lem:accessible-dense` | conditional (via `thm:arc-complement`) | `Jordan.lean` |
| `thm:jordan` | conditional (via `thm:arc-complement`) | `Jordan.lean` (`IsJordanCurve.isSeparating`) |
| `lem:crosscut-at-most-two` | conditional (`HasArcCollars`, now reduced to `IsPolyArcCarrier`) | `CrosscutAtMostTwo.lean`, `ArcCollars.lean` |
| `thm:general-crosscut` (H10) | conditional (`thm:jordan`, `HasArcCollars`) | `GeneralCrosscut.lean` |
| `lem:accessible-endpoints` | done | `AccessibleJoin.lean` |

## Part II — the Schönflies extension

Nothing here is finished. The abstract scaffolding exists and was deliberately built first,
because `lem:combinatorial-invariance` has no internal prerequisites and so could be proved
while the Jordan curve theorem was still open.

| Statement | Status | Where |
|---|---|---|
| `def:admissible-graph`, `def:matched-pair`, `def:matched-cellulation` | done | `CombinatorialInvariance.lean` (`CellStructure`, `Realization`, `SkeletonHomeo`) |
| `lem:combinatorial-invariance` | done | `CombinatorialInvariance.lean` |
| `lem:outer-incidence` | done | `CombinatorialInvariance.lean` (`outerEdge_face_corresponds`) |
| `def:strong-accessibility`, `lem:nearest-strong`, `lem:tangent-cone`, `prop:countable-strong-access` | done | `Accessible.lean` |
| `lem:square-point-mover` | done | `SquareMover.lean` |
| `lem:local-skeleton-structure` | partial | `SkeletonLocal.lean` + `SkeletonSectors.lean` — open only at points with fewer than two local directions |
| `prop:anchored-square-mesh` | partial | `SquareMesh.lean` + `SquareMeshConnected.lean` — geometry and diameter bounds done, 2-connectivity not yet connected to the mesh itself |
| `lem:skeleton-crosscuts` | partial | `AccessibleJoin.lean` — the final extraction paragraph only |
| `lem:tangent-dense` | open | needs `thm:jordan` |
| `prop:initial-pair` | conditional (`thm:arc-complement`, `HasArcCollars` for the crosscut) | `InitialPair.lean` — `initialStructure`, `HexData.realization`, `targetHex`, `sourceHex`, `InitialData` with `sourceRealization` / `targetRealization` / `skeletonHomeo`, `exists_initialData`, `initial_pair` |
| `def:generated-structure`, `rem:intermediate-disconnection` | open | the inductive closure of the two elementary operations |
| `lem:cellulation-invariants` | open | **the spine of Part II**: nine assertions by mutual induction over the two constructors, resting on `thm:general-crosscut` |
| `lem:star-intersection`, `lem:refinement-compatibility`, `lem:star-face-mesh`, `rem:inductive-invariants` | open | all rest on `lem:cellulation-invariants` |
| `lem:polygonal-side-accessibility` | open | needs `lem:local-skeleton-structure` in full |
| `thm:finite-transfer` | open | the largest single statement in the manuscript: twelve internal prerequisites |
| `prop:local-grid-attachment`, `lem:grid-star-estimate`, `prop:shrinking-stars`, `lem:anchor-density` | open | quantitative refinement |
| `lem:cell-neighborhood`, `prop:skeleton-agreement`, `prop:F-continuous`, `prop:image-interior`, `prop:F-injective`, `prop:target-skeleton-dense`, `prop:F-surjective`, `lem:exact-cell-correspondence`, `prop:inverse-continuous`, `prop:interior-homeomorphism` | open | the limit homeomorphism |
| `lem:crosscut-side-correspondence`, `prop:boundary-continuity` | open | continuity at the curve |
| `thm:square-extension`, `prop:square-reduction`, `thm:closed-interior-extension` | open | |
| `prop:pointed-extension`, `lem:inversion-sides`, `prop:exterior-extension` | open | the endgame; short once `thm:square-extension` is in hand |
| `thm:main` | open | |

### A note on `prop:skeleton-agreement`

Appendix A lists it as citing nothing, which reads as "buildable now". It is not: it needs
`F`, `T_n` and `g_∞` to be defined, and those come from the whole limit-map construction. The
citation index is a syntactic citation list, not a semantic closure, and this is the one place
where that gap misleads.
