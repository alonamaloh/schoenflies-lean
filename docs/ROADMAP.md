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
`Classical.choice` and `Quot.sound` alone.

**Part II's consuming chain is complete and every link is proved**; what is missing is the
*construction* that produces the object the chain consumes.

```
Schoenflies.jordan_schoenflies   thm:main            ← SquareExtension
Schoenflies.square_extension     thm:square-extension ← HasLimitHomeomorphism
Schoenflies.CellStructure.LimitTower.isHomeoOn_F      ← the fields of LimitTower
```

| Assumed | Declared in | Blocks | Notes |
|---|---|---|---|
| `Schoenflies.SquareExtension` | `Endgame.lean` | `thm:main` | discharged by `square_extension` below, so not really open |
| `Schoenflies.HasLimitHomeomorphism` | `BoundaryContinuity2.lean` | `thm:square-extension` | four conjuncts: a dense anchor set, the interior homeomorphism, `HasAnchorCrosscuts`, `HasSpokes`. **`LimitTower` supplies the second; the other three need the construction.** |
| the fields of `CellStructure.LimitTower` | `LimitMap.lean` | the interior homeomorphism | ~14 fields, each an obligation on whoever builds the nested sequence: the cell decompositions, the shared parent maps, the two halves of `prop:shrinking-stars`, and the nesting of the skeleton maps. See the module docstring |
| `Schoenflies.CellsAbsorb` | `SkeletonAccess.lean`, `FreshAccess.lean` | `lem:polygonal-side-accessibility` | one clause of `lem:cellulation-invariants`; finite transfer now derives it directly as `IsCellDecomposition.cellsAbsorb` from assertions (i) and (vii) |

### The atom is closed

The gap that everything waited on — *`CellulationInvariants.lean` proves (i)-at-the-split and
(vii) as step theorems, given a realization `R'` of the refined structure, and nothing ever built
such an `R'`* — is closed. Both elementary operations of `def:generated-structure` now have
realization constructors, and the skeleton homeomorphism transports across both:

| | realization | skeleton map |
|---|---|---|
| edge subdivision | `SubdivData.realize`, `isRefinement_realize` (`RealizeSubdiv.lean`) | `SubdivData.realizeHomeo` (`RealizeSubdivHomeo.lean`, on `ArcMonotone.lean`) |
| 2-cell split | `SplitData.realize`, `isCrosscutSplit_realize` (`RealizeSplit.lean`) | `SplitData.splitHomeo` (`MatchedSplit.lean`) |

All four are unconditional: no hypothesis beyond the geometric input each takes, and nothing left
for a later module to discharge. Stage 0 is built (`InitialData.generatedPair`, all nine
`GeneratedPair` fields, zero hypotheses), and `StageTower.lean` turns a sequence of stages into a
`LimitTower` with no free hypotheses at all.

### The boundary-cycle piece is closed

`EarStep` needs `SplitData.path₁` and `path₂`, *the two boundary paths of the split 2-cell
between the ear's endpoints*, together with `sub_face` and `paths_meet`.  These are now exported
by `CellStructure.BoundaryCycles.boundaryPaths`.

The maintained invariant is `CellStructure.FaceCycle` / `BoundaryCycles` in
`BoundaryCycles.lean`.  `FaceCycle.boundaryPaths` applies the existing
`Graph.IsCycleThrough.split_at` theorem and proves that the two path-cell carriers meet exactly
at their endpoints.  `boundaryCycles_initialStructure` is the base case.

**`lem:face-cycles` is not the route, and this is the trap to avoid.** `Graph.face_cycles'`
takes `hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)` — *every* edge polygonal. A source
realization does not satisfy that and never will: its outer edges are subarcs of the wild curve
`C`. (`def:admissible-graph` and `IsWeaklyAdmissible.isPolygonal` both restrict polygonality to
the nonboundary edges, correctly. `IsStageOn.polygonal` had dropped the restriction and was
unsatisfiable in consequence — see below.) So the geometric route gives face cycles on the
*target* side only, and the blueprint never claims otherwise.

The boundary cycle on the source side is **maintained as data, not derived**. That is what
`CellStructure.boundary : γ → List γ` is for — "the cyclic boundary walk of each 2-cell", the
one field of `CellStructure` on which no axiom is imposed. The route is therefore:

* state the invariant: for every 2-cell `F`, `boundary F` is a closed walk of `skel` whose cells
  are exactly the cells strictly below `F`;
* the base case is already proved — `isWalk_initBoundary_false`, `isWalk_initBoundary_true` and
  `mem_faceCells_iff` in `InitialPairFixed.lean`, which were written for exactly this;
* preserve it under the two constructors. The split constructor is where the two paths come
  from and where they go: `SplitData` already carries `path₁`, `path₂` as data, so the new
  2-cells' walks are built from them and the ear. The subdivision constructor needs the repair
  `CellulationInvariants.lean` built and `GeneratedStructure.lean` now consumes —
  `SubdivData.SubstWalk`.

**The boundary-update design point is implemented.** `SubstWalk` is a *relation*, not a
function of the list — which of `[newEdge₁, newEdge₂]` and `[newEdge₂, newEdge₁]` is correct is
determined by the walk, and the list alone does not record it. `SubdivData` therefore carries
`newBoundary : γ → List γ` and `boundary_subst`, which says that every old face boundary is a
closed walk and that the corresponding new list is its orientation-aware `SubstWalk` image.
`subdivideEdge` uses that data directly, and `SubdivData.boundary_isWalk` proves that every
updated face boundary is again closed. The old orientation-blind `flatMap` update and its
machine-checked counterexample have been removed.

The constructor-preservation proof is also closed in `BoundaryCyclesGenerated.lean`:

* `SplitData.boundaryCycles` proves that the two new boundaries are an old boundary arc closed
  by the reversed ear, while untouched faces retain their old cycles;
* `SubdivData.SubstWalk.isPath`, `.pathCells_eq`, and `.exists_isCycleThrough` prove that the
  orientation-aware replacement preserves simplicity and performs the exact carrier update;
* `SubdivData.boundaryCycles` closes the subdivision case;
* `GeneratedStructure.boundaryCycles` closes the induction, and
  `GeneratedPair.boundaryCycles` exposes it to finite transfer.

Two-edge cycles are deliberately allowed: splitting along an ear can create a legitimate
digon, so an invariant demanding a third boundary vertex would not be constructor-stable.

The entire `EarStep` construction is now closed:

* `exists_source_face_of_ear` identifies the source face and its abstract endpoints;
* `GeneratedPair.exists_target_crosscut` constructs the target polygonal crosscut;
* `Graph.relabelEdges` and `Graph.relabelDrawing` preserve paths and drawings under fresh edge
  names;
* `exists_sourceEarStepData` allocates fresh internal vertices, edges and faces, builds the
  abstract `SplitData`, and realizes exactly the ambient source path;
* `MatchedArc.lean` proves that subarcs of a polygonal arc are polygonal and constructs the
  endpoint-preserving parameter-matching homeomorphism between any two arcs;
* `EarCrosscut.exists_matched_target` transports every abstract source edge to its target
  counterpart, proving the resulting drawing and each target edge polygonal;
* `GeneratedPair.split` builds both realized splits and the extended skeleton homeomorphism;
* `EarCrosscut.isWeaklyAdmissible_realize` proves weak admissibility instead of asking the
  caller for it;
* `EarStepData.isPartialTransferOf_pair` composes refinements and proves the exact enlarged
  source carrier;
* `earStepConstruction` and `earStep` assemble the nontrivial and already-present branches.

Everything downstream is now:

1. the stage recursion — both directions of `thm:finite-transfer` are implemented; direction
   (b)'s stage-facing form is `exists_finite_transfer_toward_source_initial_squareMesh`, reduced
   to the three statements saying that the chosen mesh subdivides the current target skeleton.
   This is where `GridAttach.lean`, `SquareMeshClosed.lean` and `Windows.lean` are spent, giving
   `lem:grid-star-estimate` and `prop:shrinking-stars`;
2. `HasAnchorCrosscuts` and `HasSpokes` from the stages, and `thm:main` becomes unconditional.

Everything that *consumes* those is done.

### What the standing rules caught

Five things, all worth the cost of the rules that found them.

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
the parameter. `Schoenflies.FreshDense` in `SquareMesh.lean` was proposed as the repair and
**is not one on its own**: `LocalGrid.lean` proves `freshDense_of_four_sqrt_two_le` (at
`4√2 ≤ δ` the condition is vacuous, the empty list included) and
`freshDense_not_isTwoConnected` (the counterexample, formal). What repairs it is `FreshDense`
*together with a bound on `δ`* — `exists_two_distinct_fresh_of_freshDense` turns `δ < 4` into
two distinct fresh points — and two distinct fresh points is exactly the right amount, because
`not_isTwoConnected_meshGraph_of_fresh_subsingleton` shows fewer is always fatal. The
blueprint's own `δ = ε_n = 2^{-n}` is far below the bound.

**A hypothesis that is false in the generality it was stated in.** `Schoenflies.EarStep` in
`FiniteTransfer.lean` quantified over an arbitrary name type `γ`. Every cell of every structure
is a name drawn from `γ` — `V(skel)`, `E(skel)` and `faces` are three disjoint subsets of it —
and an ear insertion consumes fresh names for the ear's interior vertices, its edges and the two
2-cells the split creates, while the conclusion forces the new structure to realize a
subdivision of the enlarged graph. A `γ` large enough to carry the transfer of `B` and too small
to carry it with one more ear satisfies the hypotheses and refutes the conclusion. The repair is
`[Infinite γ]`, and the consumer instantiates `γ := ℕ`. Unlike the two above this one is
*recorded rather than machine-checked*: pinning it down needs a `GeneratedPair` over an
exactly-exhausted finite `γ`, a page of construction for a defect the type class removes
outright. Had it been a `sorry` it would have been filled in for `γ = ℕ` and the statement left
false.

**A structure too weak for its own step theorem.** `CellStructure.SplitData.paths_disjoint`
forbade the two boundary paths of the split 2-cell a common *edge* and said nothing about a
common interior *vertex*. Two edge-disjoint paths between the same two vertices may share one:
parallel edges `e₁, f₁ : u — a` and `e₂, f₂ : a — v`, with paths `[e₁, e₂]` and `[f₁, f₂]`. Every
other field holds, and the two realized boundary paths then meet in three points, so
`IsCutPair.inter_eq` is false, and with it the `isCutPair` field of `SplitData.IsCrosscutSplit`
and assertion (i) at the split constructor. Found by `RealizeSplit.lean`, the first module that
ever built a realization of a split, which had to carry the missing clause as a hypothesis
rather than `sorry` past it. Repaired at the source — nothing anywhere constructs a `SplitData`
yet, so it was the cheapest possible moment — by replacing the field with `paths_meet`, from
which `paths_disjoint` is recovered as a theorem.

**A structure unsatisfiable for the graphs it was written for.** `Graph.IsStageOn.polygonal`
asked `IsPolygonal` of *every* edge of a stage. The outer edges of a *source* stage are subarcs
of the wild Jordan curve `C`, which is in general nowhere polygonal, so no source stage could
satisfy it — and `lem:skeleton-crosscuts`, the whole point of the structure, is about source
stages. `def:admissible-graph` says it correctly ("its edges *not contained in `C`* are
polygonal arcs") and the Lean statement had dropped the restriction. Nothing was lost by the
repair: both proofs in the module already applied the field only to nonboundary edges. It had
not been hit because nothing had ever constructed an `IsStageOn`.

**And one claimed gap that was not one.** `SquareMeshFixed.lean` carried a hypothesis
`SubdividesToPath` and its docstring — and `SquareMeshConnected.lean`'s — asserted that
discharging it needed "a theorem no module on `main` has". It is
`Schoenflies.exists_incWalk_insideEdges` in `SquareCycle.lean`, whose `insideEdges` predicate is
`Iff.rfl`-equal to the clause in question; the two modules had simply never been in one import
chain. The bridge is four lines. Worth recording because it is the failure mode opposite to the
others: a `conditional` that was really a `done`, and the cost of it was a hypothesis threaded
through a whole module for nothing.

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
open. With Part I closed, assertions (i) and (vii) of `lem:cellulation-invariants` — the two that
need `thm:general-crosscut` at every 2-cell split — are done, as step theorems. The critical
path is now the two **realization constructors** they are stated against, and then
`thm:finite-transfer`.

| Statement | Status | Where |
|---|---|---|
| `def:admissible-graph`, `def:matched-pair`, `def:matched-cellulation` | done | `CombinatorialInvariance.lean` (`CellStructure`, `Realization`, `SkeletonHomeo`) |
| `lem:combinatorial-invariance` | done | `CombinatorialInvariance.lean` |
| `lem:outer-incidence` | done | `LimitMap.lean` (`IsCellDecomposition.closure_cell_meets_outer_iff`, `.star_meets_outer_iff`, `LimitTower.star_meets_bdry_iff`). **Not** `CombinatorialInvariance.outerEdge_face_corresponds`, which this table used to point at — that is assertion (vi), a different statement |
| `def:strong-accessibility`, `lem:nearest-strong`, `lem:tangent-cone`, `prop:countable-strong-access` | done | `Accessible.lean` |
| `lem:square-point-mover` | done | `SquareMover.lean` |
| `lem:local-skeleton-structure` | partial | `SkeletonLocal.lean` + `SkeletonSectors.lean` — open only at points with fewer than two local directions; the two missing cases are closed in `SkeletonAccess.lean` |
| `prop:anchored-square-mesh` | **done** | `SquareMesh.lean`, `SquareMeshConnected.lean`, `SquareMeshFixed.lean`, `LocalGrid.lean` for clauses 1, 2, 3, 4, 6; `SquareMeshClosed.lean` for clause 5 (`squareMesh_isTwoConnected`, on `FreshDense fresh δ` and `δ < 4`, both free at the call site since the blueprint uses `δ = 2⁻ⁿ`) and for the outer cycle as a genuine cycle of the graph, exported as data |
| `lem:skeleton-crosscuts` | partial | `AccessibleJoin.lean` — the final extraction paragraph only |
| `lem:tangent-dense` | done | `Inversion.lean` |
| `prop:initial-pair` | **done**, and packaged as a `GeneratedPair` in `InitialGenerated.lean` | `InitialPair.lean` (`initialStructure`, both realizations, `InitialData`) completed in `InitialPairFixed.lean`: the anchor clause (`AnchorSet`, `AnchoredInitialData`, `stronglyAccessible_initialData_a`), the matched labelling (`tgt_arcOf_eq_image`, `closure_cell_face_link`), the polygonal target edges, the boundary-walk check, and both hypotheses `harc` / `hcollars` discharged — `initial_pair'` is unconditional |
| `def:generated-structure`, `rem:intermediate-disconnection` | **done** | `GeneratedStructure.lean` for the two operations and the inductive closure; `RealizeSubdiv.lean` / `RealizeSplit.lean` for the realization constructors; `RealizeSubdivHomeo.lean` / `MatchedSplit.lean` for the skeleton map across each. All four unconditional |
| `lem:cellulation-invariants` | done | (ii), (iii), (iv), (v), (vi), (viii), (ix) and (i) at the subdivision constructor in `GeneratedStructure.lean`; **(i) at the split constructor and (vii)** in `CellulationInvariants.lean` (`SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan`, `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan`). Both are *step* theorems, stated against a realization of the refined structure — see the row above for what is still missing |
| `lem:refinement-compatibility`, `lem:star-intersection`, `lem:star-face-mesh`, `lem:cell-neighborhood` | done | `RefinementStars.lean`. The carrier is a total function and refinement is abstract, which is what lets the limit section be built against an interface |
| `lem:polygonal-side-accessibility` | conditional (`Schoenflies.CellsAbsorb`) | `SkeletonAccess.lean` — both halves, on one clause of `lem:cellulation-invariants` |
| `thm:finite-transfer` (a) | **done** | `FiniteTransfer.lean` supplies the ear induction and `earStep`; `CommonSubdivision.lean` proves `commonSubdivision` by tracing the old skeleton and iterating matched edge subdivisions, then exposes `finite_transfer_toward_square_unconditional` |
| `thm:finite-transfer` (b) | **done** | `FiniteTransferTarget.lean` constructs the target common subdivision, fully implements the target-path relabelling and matched reverse split, and carries out the relative-ear induction. Local carrier reflection and name-independent boundary-edge uniqueness make each new wild-boundary endpoint outer-only; `OuterEdgesFormCycle`, invariant under both generated constructors and verified for the initial hexagon in `InitialOuterCycle.lean`, forces the selected face to be unique. `Graph.Relabel` now preserves incidence, finiteness, connectedness, 2-connectivity and drawings. `FiniteTransferTargetMesh.lean` transports all square-mesh boundary geometry through a finite injective edge relabelling and assembles `IsSourceExtension` from only the three subdivision clauses. Finally `InitialReverseTransfer.lean` chooses unused `InitialCell` names automatically and exposes `exists_finite_transfer_toward_source_initial_squareMesh`, the stage-facing unconditional theorem |
| `prop:local-grid-attachment` | conditional (`hΓ`, `hcov`) | `LocalGrid.lean` (`localGrid`, the diameter clause) + `GridAttach.lean` (the overlay, the crosscut factory, the component-joining loop, and the construction as `def`s). The blueprint's three cases collapse to one; the joining loop is done by representatives rather than by a decreasing component count. `hΓ` is 2-connectivity of `Γ` with the auxiliary arcs appended — not provable there, because `C` is not drawn by segments so `Γ` is not a `pieceListGraph`; `hcov` is "finitely many representatives meet every component of `|L| ∖ C`", where the blueprint's finiteness lives |
| `lem:grid-star-estimate`, `prop:shrinking-stars`, `lem:anchor-density` | open | quantitative refinement; they consume the stage recursion, which does not exist yet. The metric half is ready: `Windows.lean` has `supRadius` (the ℓ^∞ distance to a compact set, with attainment, positivity and the 1-Lipschitz property), `windowRadius` / `window` / `openWindow` with the blueprint's three inequalities and `W_n(p) ⊆ D`, the arithmetic of `prop:shrinking-stars` (`mem_openWindow_of_supDist_lt`), and the two sequences (`recur`, `tendsto_two_pow_neg`) |
| the passage from stages to `LimitTower` | done | `StageTransition.lean` gives both finite-transfer directions one common composable output (the two refinements, source-skeleton growth, and skeleton-map nesting). `StageTower.lean` records one such transition at each successor stage and builds `StageSequence.limitTower`, with no free hypotheses; `isHomeoOn_F` is `prop:interior-homeomorphism` in exactly the shape `HasLimitHomeomorphism`'s second conjunct asks for, and `F_eq_skelHomeo` is the bridge that will discharge `HasAnchorCrosscuts` |
| arc monotonicity | done | `ArcMonotone.lean` — not a blueprint statement; one of the facts the manuscript uses silently. A homeomorphism between two arcs induces a strictly monotone map of parameters, so it carries subarcs to subarcs |
| `lem:cell-neighborhood`, `prop:skeleton-agreement`, `prop:F-continuous`, `prop:image-interior`, `prop:F-injective`, `prop:target-skeleton-dense`, `prop:F-surjective`, `lem:exact-cell-correspondence`, `prop:inverse-continuous`, `prop:interior-homeomorphism` | open | the limit homeomorphism |
| `lem:crosscut-side-correspondence`, `prop:boundary-continuity` | open | continuity at the curve |
| `thm:square-extension`, `prop:square-reduction`, `thm:closed-interior-extension` | open | |
| `lem:inversion-sides` | done | `Inversion.lean` (`invert_image_outside`, `IsJordanCurve.invert`, `invertHomeo`) |
| `prop:exterior-extension` | conditional (`Schoenflies.PointedInteriorExtension`) | `Inversion.lean` — the last statement before `thm:main`, waiting only on the interior half |
| `prop:pointed-extension` | open | needs `thm:closed-interior-extension`; `lem:square-point-mover` is done |
| `thm:main` | open | |

### The limit section, and why it needed no construction

`jordan_schoenflies.tex` line 2570 says the limit section "forgets how the decompositions were
constructed and uses only their nesting, matching, and shrinking properties". `LimitMap.lean`
takes that literally: `CellStructure.LimitTower` records exactly those properties, and the whole
of tex 2568–2826 is proved against it with **no free hypotheses at all** — every obligation is
a field of the structure, i.e. an obligation on whoever eventually builds the sequence.

| Statement | Lean |
|---|---|
| definition of `F` | `LimitTower.F`, `tgtStar`, `iInter_tgtStar_eq` |
| `prop:skeleton-agreement` | `LimitTower.F_eq_skelHomeo` |
| `prop:F-continuous` | `LimitTower.continuousOn_F` — on the **closed** domain, not just the interior |
| `prop:image-interior` | `LimitTower.F_mem_region'` |
| `prop:F-injective` | `LimitTower.injOn_F` |
| `prop:target-skeleton-dense` | `LimitTower.exists_mem_tgt_skeletonSet` |
| `prop:F-surjective` | `LimitTower.exists_mem_region_F_eq` |
| `lem:exact-cell-correspondence` | `LimitTower.image_cell` |
| `prop:inverse-continuous` | `LimitTower.continuousOn_inv` |
| `prop:interior-homeomorphism` | `LimitTower.isHomeoOn_F`, `.interior_homeomorphism` |

Two departures from the blueprint's route, both simplifications, both worth knowing:

* **Assertion (vii) of `lem:cellulation-invariants` is not needed.** The blueprint routes
  `lem:exact-cell-correspondence` through (vii) → (viii) to get "the only 2-cell above a 2-cell
  is itself"; that is `CombInvariants.face_maximal`, already an inductive invariant.
* **`prop:F-surjective` is proved by a shorter route**, so `prop:target-skeleton-dense` is off
  the critical path. The source stars of the target carriers of `y` are themselves a nested
  sequence of nonempty compacts, and any point of their intersection is already a preimage — no
  skeleton density, no convergent subsequence, no compactness of `C ∪ D`.

### A note on `prop:skeleton-agreement`

Appendix A lists it as citing nothing, which reads as "buildable now". It is not: it needs
`F`, `T_n` and `g_∞` to be defined, and those come from the whole limit-map construction. The
citation index is a syntactic citation list, not a semantic closure, and this is the one place
where that gap misleads.
