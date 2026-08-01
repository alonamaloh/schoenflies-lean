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

**Part I has none.** `thm:jordan` and `thm:general-crosscut` rest on `propext`,
`Classical.choice` and `Quot.sound` alone; `docs/audit-axioms.py` checks that for every
declaration in the library on every run.

Part II's open statements are listed below as `open` or `partial` rather than as assumed
hypotheses: nothing downstream is built on them yet, so there is no obligation to discharge,
only work to do. The two exceptions are named in the Part II table.

### What the standing rules caught

Two things, both worth the cost of the rules that found them.

**A false hypothesis.** `Graph.CrosscutEncloses` stood on `main` as an assumed hypothesis for a
whole wave, and is **false**. Nothing in its hypotheses stopped the crosscut from being drawn
*through* `x`: take the unit square cycle with cut points `(0,0)` and `(1,1)`, let `R` be the
two edges `(0,0) → (1/2,1/2) → (1,1)`, and let `x = (2/5, 2/5)`. Every field of
`IsCycleCrosscut` holds, `x` is inside the cycle, and `x` lies *on* both spliced curves, so it
is inside neither. The repair was one clause, `x ∈ exterior H drawing`, which the consumer
already had. Had the gap been a `sorry` it would have been filled in eventually and the falsity
found only then, with everything written in the meantime resting on it. The counterexample is
recorded in `OuterChain.lean` where the false version stood.

**A false clause of a blueprint statement, as formalised.** `prop:anchored-square-mesh`
clause 5 — "the skeleton of `T` is 2-connected" — is false for the Lean `squareMesh` when the
fresh-point set is empty: the mesh is then concentric ring frames, pairwise disjoint, hence
disconnected. It is still false with exactly one fresh point, whose single spoke is the only
thing joining the rings, so every interior vertex of that spoke is a cut vertex. See
`Schoenflies.not_isTwoConnected_squareMesh_of_fresh_nil` in `SquareMeshFixed.lean`. The
blueprint's own construction never hits either case, because it chooses enough fresh points to
make every boundary arc have diameter `< δ/4`; what is missing in Lean is that hypothesis on
the parameter, and `Schoenflies.FreshDense` in `SquareMesh.lean` is the shape it should take.

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
| `lem:polygonal-collar` (b) | done | `ArcCollars.lean` for a `PolyArc`, `PolyArcRealize.lean` for a set |
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
| realization theorem, arc case | done | `PolyArcRealize.lean` — every set-level simple polygonal arc admits a `PolyArc` presentation (`isPolyArcCarrier_of_isPolygonal`). Same status: not a blueprint statement, but the bridge Lemma 1.8 (b) takes for granted |

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
| `thm:arc-complement` | **done** | `ArcComplement.lean`; `SquaresTwoConnected` discharged in `SquareCycle.lean`; headline `Schoenflies.arc_complement` in `JordanClosed.lean` |
| `lem:accessible-dense` | **done** | `Jordan.lean` |
| `thm:jordan` | **done** | `Jordan.lean`; headline `Schoenflies.jordan_curve_theorem` in `JordanClosed.lean`, stated as `IsSeparating C` |
| `lem:crosscut-at-most-two` | **done** | `CrosscutAtMostTwo.lean`, `ArcCollars.lean`, closed in `PolyArcRealize.lean` (`crosscut_at_most_two_of_isPolygonal`) |
| `thm:general-crosscut` (H10) | **done** | `GeneralCrosscut.lean` + `PolyArcRealize.lean`; headline `Schoenflies.crosscut_theorem` in `JordanClosed.lean` |
| `lem:accessible-endpoints` | done | `AccessibleJoin.lean` |

## Part II — the Schönflies extension

The abstract scaffolding was deliberately built first, because `lem:combinatorial-invariance`
has no internal prerequisites and so could be proved while the Jordan curve theorem was still
open. With Part I closed, the critical path is assertions (i) and (vii) of
`lem:cellulation-invariants` — the two that need `thm:general-crosscut` at every 2-cell split —
and then `thm:finite-transfer`.

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
| `lem:tangent-dense` | done | `Inversion.lean` |
| `prop:initial-pair` | partial | `InitialPair.lean` — `initialStructure`, both realizations, `InitialData`, `initial_pair`. Its two hypotheses are now both discharged on `main` and should be substituted. Two clauses remain open: the source and target 2-cell labellings are never linked (no lemma says `tgt.arcOf k = u '' src.arcOf k`), and strong accessibility of the two chosen points is not recorded, though the blueprint requires `a, b ∈ 𝒜` |
| `def:generated-structure`, `rem:intermediate-disconnection` | partial | `GeneratedStructure.lean` — both elementary operations as defs and the inductive closure, but carrying no realizations yet |
| `lem:cellulation-invariants` | partial | `GeneratedStructure.lean` — (ii), (iii), (iv compatibility), (v), (vi), (viii), (ix), and (i) for the subdivision constructor. **(i) for the split constructor and (vii) are the remaining work**, and both need `thm:general-crosscut`, now available |
| `lem:star-intersection`, `lem:refinement-compatibility`, `lem:star-face-mesh`, `rem:inductive-invariants` | open | all rest on `lem:cellulation-invariants` |
| `lem:polygonal-side-accessibility` | conditional (`Schoenflies.CellsAbsorb`) | `SkeletonAccess.lean` — both halves, on one clause of `lem:cellulation-invariants` |
| `thm:finite-transfer` | open | the largest single statement in the manuscript: twelve internal prerequisites |
| `prop:local-grid-attachment`, `lem:grid-star-estimate`, `prop:shrinking-stars`, `lem:anchor-density` | open | quantitative refinement |
| `lem:cell-neighborhood`, `prop:skeleton-agreement`, `prop:F-continuous`, `prop:image-interior`, `prop:F-injective`, `prop:target-skeleton-dense`, `prop:F-surjective`, `lem:exact-cell-correspondence`, `prop:inverse-continuous`, `prop:interior-homeomorphism` | open | the limit homeomorphism |
| `lem:crosscut-side-correspondence`, `prop:boundary-continuity` | open | continuity at the curve |
| `thm:square-extension`, `prop:square-reduction`, `thm:closed-interior-extension` | open | |
| `lem:inversion-sides` | done | `Inversion.lean` (`invert_image_outside`, `IsJordanCurve.invert`, `invertHomeo`) |
| `prop:exterior-extension` | conditional (`Schoenflies.PointedInteriorExtension`) | `Inversion.lean` — the last statement before `thm:main`, waiting only on the interior half |
| `prop:pointed-extension` | open | needs `thm:closed-interior-extension`; `lem:square-point-mover` is done |
| `thm:main` | open | |

### A note on `prop:skeleton-agreement`

Appendix A lists it as citing nothing, which reads as "buildable now". It is not: it needs
`F`, `T_n` and `g_∞` to be defined, and those come from the whole limit-map construction. The
citation index is a syntactic citation list, not a semantic closure, and this is the one place
where that gap misleads.
