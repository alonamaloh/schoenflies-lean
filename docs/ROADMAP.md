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
| `Schoenflies.CommonSubdivision` | `FiniteTransfer.lean` | `thm:finite-transfer`(a) | step 1. The overlay itself is proved (`exists_overlay_of_biUnion_finite`); what is missing is carrying each new subdivision point through the chosen edge parametrization to the *other* realization. `RealizeSubdivHomeo.lean` now supplies exactly that transport for one subdivision (`SubdivData.targetParam`, `realizeHomeo`), so this is assembly, not new mathematics |
| `Schoenflies.EarStep` | `FiniteTransfer.lean` | `thm:finite-transfer`(a) | step 3, one ear. Carries `[Infinite γ]` — see below. **Both `EarCrosscut`s and the `EarHomeo` now exist** (`EarDraw.lean`, `EarSource.lean`, `EarTarget.lean`), so the geometric input of `SplitData.realize` is in hand on both sides, and `GeneratedPair` now carries assertion (vii). What is missing is two more stage invariants the bundle still does not carry — `CellsAbsorb` on the source side and the target-cells-are-components presentation — and then the assembly of the twelve fields. See phase 1d below |
| `Schoenflies.CellsAbsorb` | `SkeletonAccess.lean`, `FiniteTransfer.lean`, `FreshAccess.lean` | `lem:polygonal-side-accessibility`, ear placement | one clause of `lem:cellulation-invariants`; `cellsAbsorb_of_isComponent_in` discharges it when the cells are the components |

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
for a later module to discharge. Stage 0 is built (`InitialData.generatedPair`, all twelve
`GeneratedPair` fields, zero hypotheses), and `StageTower.lean` turns a sequence of stages into a
`LimitTower` with no free hypotheses at all.

### The one piece with real content left

`EarStep` builds a `SplitData` from an ear. Every field is now routine except two:
`SplitData.path₁` and `path₂`, *the two boundary paths of the split 2-cell between the ear's
endpoints*, together with `sub_face` (they carry exactly the cells below the 2-cell) and
`paths_meet` (they share nothing but their two ends).

Producing them means knowing that **the cells below a 2-cell form a cycle**, and that two of its
0-cells cut that cycle into two paths. `CellStructure.CombInvariants` does not carry it;
`BoundaryWalks.lean` now carries half of it (see the plan below).

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
  2-cells' walks are built from them and the ear. **The subdivision constructor is done** — see
  the next paragraph.

**The design point, decided and written in Lean.** `subdivideEdge` used to replace the
subdivided edge in every boundary walk by the fixed list `[newEdge₁, newEdge₂]`, which is
**orientation-blind and wrong**: an interior edge lies on the boundary of two 2-cells whose
walks cross it in opposite directions, and one of them needs `[newEdge₂, newEdge₁]`. The
correction is a *relation*, not a function of the list — which order is right is determined by
the walk, which the list does not record — so it could not be another closed form, and the
corrected walks now **arrive as data**. Of the two shapes on the table, the field won over an
extra argument to `subdivideEdge`, for the reason recorded here: `SubdivData` is already the
bundle of everything one subdivision chooses, and this keeps `subdivideEdge` a function of its
data alone. What the write-up did not foresee is that it takes **three** fields, not one:

* `Schoenflies.IsSubstWalk` had to be restated for a bare graph, because a field's type may name
  only *earlier* fields — `d.SubstWalk` does not exist inside the declaration of `d`.
  `SubdivData.SubstWalk` survives as the specialization.
* `boundaryStart : γ → γ` is a field of its own. A `newBoundary` constrained at *every* vertex
  its boundary list happens to walk from would be **unsatisfiable**: the one-edge walk `[e]`
  walks from both ends of `e`, and demands both orders of `e₁, e₂` at once
  (`Schoenflies.eq_of_isSubstWalk_singleton`). The departure vertex is exactly what the closed
  form could not see, so it is exactly what the data has to carry.
* the constraint is conditional on the old list being a walk at all, since `CellStructure`
  imposes no axiom on `boundary`, and `Schoenflies.substWalk` builds the witness — so the three
  fields cost a constructor nothing.

The payoff a consumer sees is `CellStructure.subdivideEdge_isWalk_boundary`: a boundary walk of
`S` is still a walk, with the same ends, after a subdivision. The record of the defect stays in
`CellulationInvariants.lean` as `SubdivData.flatBoundary` and
`SubdivData.not_isWalk_flatBoundary_of_head`. Done in the window nothing constructed a
`SubdivData` — the same window that made the `SplitData.paths_meet` repair cheap.

### The plan to finish, and where it stands

Four phases. Everything that *consumes* them is done, so each one is the whole of what is left
at its level.

**Phase 1 — face boundary cycles, hence `EarStep`.** The one piece with real content. 1a, 1b
and 1c are done and `sorry`-free; 1d is blocked on one interface change, described below.

* **1a. The boundary-walk invariant — done.** `BoundaryWalks.lean`: for every 2-cell `F`,
  `boundary F` is a closed walk of the skeleton based at `start F`, and the cells it runs
  through are exactly the cells strictly below `F`. Both elementary operations preserve it
  (`BoundaryWalks.subdivideEdge`, `.splitFace`) and `initialBoundaryWalks` is the base case,
  packaging `isWalk_initBoundary_*` and `mem_faceCells_iff`. Two things fell out: **no 2-cell is
  strictly below another** (`eq_of_sub_of_mem_faces`) — which the blueprint asserts of its
  update lists and which is now a theorem — and `mem_boundary_iff_sub`.
* **1b. The invariant is a cycle, not a closed walk — done.** `EarStep` needs
  `SplitData.paths_meet`: the two boundary paths share *nothing but their two ends*. That does
  not follow from a closed walk — one that repeats a vertex cuts into pieces meeting in more
  than two points. `BoundaryWalks.isCycle` says the boundary datum is a cycle, presented through
  its first edge the way `Graph.IsCycleThrough` presents every cycle here, so `Graph.IsPath`
  does the ruling-out. Both preservation proofs were redone for it: the subdivision case rests
  on `SubdivData.SubstWalk.isPath` (the new vertex is fresh, so an old path cannot already have
  visited it) and on `IsSubstWalk.cons_inv`, whose three cases *are* the three constructors;
  the split case on `SplitData.vertexSet_inter`. `isWalk` is now a theorem, not a field.
* **1c. Cut a cycle at two of its 0-cells — done.**
  `BoundaryWalks.exists_boundary_paths`: two distinct 0-cells below a 2-cell give two paths
  between them carrying exactly the cells below it and meeting in nothing but the two — which
  are `SplitData.isPath₁`, `isPath₂`, `sub_face`, `paths_meet`. The graph-level cut was already
  on `main` (`Graph.IsCycleThrough.split_at`, in `FaceCyclesProof.lean`, a module no cell-
  structure file had ever imported); what 1c adds is the bridge from the abstract invariant to
  it. Carries `CombInvariants`, because `sub_face` quantifies over every `σ ≼ F` and nothing
  else says such a `σ` is a cell.
* **1d. The bundle carries the invariant — done; `EarStep` itself is next.** The `SplitData`
  fields were available after 1c but **`EarStep` could not reach them**: its hypothesis is
  `IsPartialTransferOf T P B Hdraw par`, and neither that nor `GeneratedPair` carried a
  `BoundaryWalks`. It cannot be recovered from `generated` either — a derivation may contain
  `SubdivData`s whose `boundaryStart` has nothing to do with any invariant, so there is no
  closure theorem over the raw inductive, only the two step *constructions* a consumer applies
  while building a stage. So `GeneratedPair` grew a `walks : str.BoundaryWalks` field,
  discharged at stage 0 by `Schoenflies.initialBoundaryWalks` (which moved into
  `InitialGenerated.lean`, since it cannot sit above the pair it feeds).

  **No subdivision is needed after all.** The reading flagged below as "worth checking" holds:
  `IsPartialTransferOf.vertexSet_subset` plus `EarStep`'s own `a, b ∈ V(B)` make both ends
  drawn 0-cells already (`IsPartialTransferOf.exists_cell_of_mem_vertexSet`, `EarPaths.lean`),
  so one ear insertion is **one split with no subdivision**. The subdivision constructor is
  needed by `CommonSubdivision` (1e) and not by the ear induction.

* **1d″. The drawn ear, and both `EarCrosscut`s — done.** Three modules, all `sorry`-free.

  * `EarDraw.lean` — the abstract ear and its drawing are built **together**, because the ear
    has to be drawn exactly where `H` draws the path it came from. `Graph.IsEarChart` is the
    correspondence: the ear is `Graph.pathOn z steps` on fresh names, `earPos` places its
    vertices at the concrete path's vertices in order, `name` matches its edges with the
    concrete path's, and `isLink` ties the two. `Graph.exists_isEarChart` builds one by an
    induction along the path from its source; the hypothesis `z = w ↔ a = b` is what keeps that
    recursion uniform, since the last step has to arrive at the *prescribed* old name of the far
    0-cell. Out of it: `Graph.IsEarChart.isDrawing` (the drawn ear is a plane graph — every
    clause of `IsDrawing` is the corresponding clause for `H`) and `.pointSet_eq` (it occupies
    exactly `|H.pathGraphOf a D|`), packaged as `Graph.exists_drawn_ear`.
  * `EarSource.lean` — `Schoenflies.exists_source_earCrosscut`: from exactly what `EarStep` is
    handed, the `SplitData` *and* the source `EarCrosscut`, all seven fields. The two facts
    worth naming are `Graph.disjoint_walkPointSet_diff` (the ear's interior misses `|B|` —
    `EarStep` only says the interior *vertices* are new, and that the interior *points* are is
    the plane-graph condition on `H`) and `Graph.IsDrawing.isPolygonal_walkPointSet` (no ear
    edge can be an outer edge, because the outer curve is inside `|B|` and the ear's interior is
    not, so `edge_dichotomy` gives polygonality). The one ear these miss is a single edge `B`
    already has, and `Schoenflies.isPartialTransferOf_union_of_mem_edgeSet` disposes of it:
    `B ∪ ear = B` there.
  * `EarTarget.lean` — `Schoenflies.exists_target_earCrosscut`: the target ear is the **image**
    of the source one under a homeomorphism of the two arcs (`Schoenflies.exists_arc_homeo`),
    not a cutting of the target crosscut at prescribed parameters. `Graph.IsDrawing.map_of_injOn`
    (a plane graph pushed forward along an injection continuous on its point set is a plane
    graph) gives the drawing, and `SplitData.EarHomeo`'s two matching clauses then hold by
    definition — which is exactly the shape `MatchedSplit.lean` argues for.

  For the integrator: eight general facts were written in these three modules for want of a
  home — `Graph.setOf_mem_cons`, `Graph.union_eq_left_of_le`, `Graph.IsPath.eq_singleton_of_inc`,
  `Graph.pointSet_pathGraphOf`, `Graph.IsDrawing.isPolygonal_walkPointSet`,
  `Graph.edgeArc_map`, `Graph.pointSet_map`, `Graph.IsDrawing.map_of_injOn`. They belong in
  `Schoenflies/Graph/{Walk,PathGraph,Drawing}.lean`. And `EarTarget.lean` imports the whole of
  `InitialPair.lean` for one general topology fact,
  `Schoenflies.continuousOn_invFunOn_image` — *a continuous injection of a compact set has a
  continuous inverse on its image* — which belongs in `Schoenflies/Topology.lean`; hoisting it
  drops the import.

* **1d‴. What `EarStep` still needs, and it is an interface change.** The assembly of the
  `GeneratedPair` fields cannot be written against `GeneratedPair` as it stood, because
  `EarStep` quantifies over *every* partial transfer `T` and three things the split needs are
  properties of `T` that the bundle did not carry and no hypothesis of `EarStep` supplies. The
  first is now closed; the other two are not.

  1. **Assertion (vii) on both realizations — closed.**
     `SplitData.isCellDecomposition_and_isFaceJordan_realize` takes `R.IsFaceJordan`, and
     `SplitData.isCutPair_of_inter` — which produces the `IsCutPair` that `exists_target_ear`
     consumes — takes it on the target. Nothing on `main` ever *constructed* an `IsFaceJordan`:
     the only occurrences in the inventory were the structure, its API, and the two step
     theorems, so it was unavailable at stage 0 too. `GeneratedPair` now has two more fields,
     **`src_isFaceJordan` and `tgt_isFaceJordan`** (eleventh and twelfth), discharged in
     `InitialGenerated.lean` by `InitialData.src_isFaceJordan` / `.tgt_isFaceJordan` — the same
     move that added `walks`. The proof at stage 0 is four lines each:
     `IsCrosscut.isJordanCurve_union` splices the arc of `C` with the crosscut, and
     `IsSeparating.frontier_inside` identifies the frontier of `inside` that curve with the
     curve, so `InitialData.sourceRealization_cell_face` finishes it.
  2. **`Schoenflies.CellsAbsorb` for the source realization.** Already in the table above, but
     note *where* it now has to be discharged: `GeneratedPair.exists_face_and_boundary_paths`
     needs it for the current stage, inside a theorem quantified over `T`, so it cannot be an
     argument of the `EarStep` proof either. Either it becomes a field, or it is derived from
     (i) + (vii) — the 2-cells of a stage are the components of the open domain minus the
     skeleton, which is what `cellsAbsorb_of_isComponent_in` wants.
  3. **The target-side presentation `exists_target_ear` consumes**: an ambient open `Q` with
     `frontier Q ⊆ tgt.skeletonSet` and every target 2-cell a component of `Q ∖ |Γ'|`, plus
     `IsPolygonal (edgeArc tgt.drawing e)` for **every** target edge. The last is not implied by
     weak admissibility: `IsWeaklyAdmissible.isPolygonal` is restricted to *nonboundary* edges,
     correctly (the source outer edges are subarcs of the wild `C`), and on the target side the
     outer edges are the square's sides — polygonal, but nothing records it. A field
     `tgt_isPolygonal_outer`, or a target-side clause saying the 2-cells are the components of
     the open square, is what closes this.

  None of the three is a gap in the mathematics; all three are the bundle being one invariant
  short of its consumer, which is the same failure mode `walks` had and the standing rules keep
  catching.

  The rest of the assembly is routine and unwritten: `generated := T.generated.splitFace d`,
  the two `realize`s, `splitHomeo`, `walks := T.walks.splitFace …`, the ten weak-admissibility
  clauses (`isTwoConnected` is `EarCrosscut.isTwoConnected_splitGraph`, `isPolygonal` for an ear
  edge on the target is `IsArcBetween.isPolygonal_of_subset` inside the polygonal crosscut,
  `outerSet_eq` is `map_eq_of_eqOn` + `pointSet_congr` since the split changes neither the outer
  graph nor its drawing), and the four `IsPartialTransferOf` fields, of which `skeletonSet_eq`
  is `SplitData.skeletonSet_realize` plus `Graph.pointSet_union`.

  What follows is the record of the two blockers that *were* closed.

  > **weak admissibility is not known to be preserved by either elementary operation.**
  > `IsWeaklyAdmissible` occurs in exactly two modules — `FiniteTransfer.lean`, which defines
  > it, and `InitialGenerated.lean`, which discharges it at stage 0. Nothing subdivides or
  > splits it. Its five clauses are unequal: `outerSet_eq`, `isPolygonal`, `cell_subset` and
  > `skeletonSet_subset` should be routine from the realization constructors, but
  > `isTwoConnected` needs *a subdivision of a 2-connected graph is 2-connected*, and
  > `Schoenflies/Graph/TwoConnected.lean` says nothing about subdivisions —
  > `IsTwoConnected.union` needs both sides 2-connected, which an ear is not. That is a
  > self-contained graph-theory lemma and the natural next module.
* **1d′. Weak admissibility across the two operations — the graph half is now closed.**
  `Graph.IsSubdivisionOf.isTwoConnected` (`Graph/Subdivision.lean`) is the subdivision half,
  and the ear half was already on `main` as `Graph.IsTwoConnected.ear` (`Graph/Ear.lean`),
  which `relative_grows_by_ear` uses internally and which applies verbatim to a given ear. Both
  are stated for an arbitrary `Graph α β`, so they apply to the *drawn* graph, which is the one
  `def:admissible-graph` constrains; `SubdivData.isSubdivisionOf_realizeGraph` is the bridge on
  the subdivision side, and the split side needs its analogue (the realized split skeleton is
  the old one union the drawn ear as a path graph).

  Note what `isTwoConnected` needs and what it does not: **`x ≠ y`, because the theorem is false
  for a loop** — a loop subdivides into a pendant pair, and deleting its base vertex strands the
  new vertex, while 2-connectedness on its own permits loops. Consumers get looplessness from
  `Graph.IsDrawing.not_isLoopAt`, which `transfer_of_ears` already passes around.

  The `isPolygonal` clause looked like the next gap and is now closed too:
  `IsArcBetween.isPolygonal_of_subset` (`PolygonalCut.lean`) — an arc inside a polygonal arc is
  polygonal, which is what the two halves of a subdivided edge and each edge arc of a drawn ear
  need. It is *not* list surgery on polylines: `exists_simple_poly_of_isPolygonal` already
  produces some polygonal arc between the two points inside the ambient one, and the content is
  that there is only one such arc (`subarc_subset_of_isPreconnected`, where the parametrisation
  being a closed map does the work).

  What is left of 1d′ is `outerSet_eq`, `cell_subset` and `skeletonSet_subset` for both
  operations — read off the realization constructors, with `skeletonSet_realize` already there
  — and then `GeneratedPair.subdivideEdge` / `.splitFace` themselves.

  **An interface reading, now checked.** The blueprint's step 3 is "at most two edge
  subdivisions followed by one split", the subdivisions being what turns the ear's endpoints
  into 0-cells. In the Lean formulation they are unnecessary, and this is now formal:
  `IsPartialTransferOf.vertexSet_subset` says `V(B) ⊆ V(T.src.graph)`, `EarStep` hypothesises
  `a ∈ V(B)`, `b ∈ V(B)`, and `IsPartialTransferOf.exists_cell_of_mem_vertexSet`
  (`EarPaths.lean`) names the 0-cells they are. So `EarStep` is one split with no subdivision,
  and the subdivision half of everything above is needed only by `CommonSubdivision` (1e).
* **1e. `CommonSubdivision`.** Independent of 1b–1d and pure assembly:
  `exists_overlay_of_biUnion_finite` gives the overlay, `SubdivData.realizeHomeo` transports one
  subdivision to the other realization, and the induction over the overlay's finitely many new
  points is the whole of it.

**Phase 2 — `thm:finite-transfer`.** (a) becomes unconditional the moment 1d and 1e land; (b)
needs one further ingredient, accessibility at a fresh anchor on the wild curve, which
`FreshAccess.lean` already closes.

**Phase 3 — the stage recursion.** Where `GridAttach.lean`, `SquareMeshClosed.lean` and
`Windows.lean` are spent, giving `lem:grid-star-estimate` and `prop:shrinking-stars`. This is
the largest phase by far and the only one whose geometry is not yet assembled anywhere.

**Phase 4 — `thm:main` unconditional.** `HasAnchorCrosscuts` and `HasSpokes` from the stages.
The limit map and everything after it is already built and waiting.

### What the standing rules caught

Five things, all worth the cost of the rules that found them — and one of the same kind that a
rule did not have to catch, because writing the field caught it first.

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

**A field that would have been unsatisfiable, caught while writing it.** The `newBoundary` field
of `SubdivData` was to say "the corrected boundary walk, for whichever vertex the old one walks
from". Quantified that way it cannot be filled: the walk `[e]` consisting of the subdivided edge
alone walks from *both* ends of `e`, and the two corrections are the two orders of `e₁, e₂`, so
the field would demand a single list equal to both. The repair is the extra field
`boundaryStart`, and the obstruction is machine-checked as
`Schoenflies.eq_of_isSubstWalk_singleton`. Not a standing-rules catch — it was found by writing
the field rather than by a review — but the same failure mode as the two above, and the same
window: nothing constructs a `SubdivData`.

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
| `thm:finite-transfer` (a) | conditional (`CommonSubdivision`, `EarStep`) | `FiniteTransfer.lean` — steps 2 and 4 and the last paragraph unconditional, the induction scheme closed, steps 1 and 3 named. See the live-obligations table |
| `thm:finite-transfer` (b) | partial | its one ingredient beyond (a), source accessibility at a fresh anchor on the wild curve, is closed in `FreshAccess.lean` (`polyAccessible_of_stronglyAccessible`). The statement itself is not yet written |
| `prop:local-grid-attachment` | conditional (`hΓ`, `hcov`) | `LocalGrid.lean` (`localGrid`, the diameter clause) + `GridAttach.lean` (the overlay, the crosscut factory, the component-joining loop, and the construction as `def`s). The blueprint's three cases collapse to one; the joining loop is done by representatives rather than by a decreasing component count. `hΓ` is 2-connectivity of `Γ` with the auxiliary arcs appended — not provable there, because `C` is not drawn by segments so `Γ` is not a `pieceListGraph`; `hcov` is "finitely many representatives meet every component of `|L| ∖ C`", where the blueprint's finiteness lives |
| `lem:grid-star-estimate`, `prop:shrinking-stars`, `lem:anchor-density` | open | quantitative refinement; they consume the stage recursion, which does not exist yet. The metric half is ready: `Windows.lean` has `supRadius` (the ℓ^∞ distance to a compact set, with attainment, positivity and the 1-Lipschitz property), `windowRadius` / `window` / `openWindow` with the blueprint's three inequalities and `W_n(p) ⊆ D`, the arithmetic of `prop:shrinking-stars` (`mem_openWindow_of_supDist_lt`), and the two sequences (`recur`, `tendsto_two_pow_neg`) |
| the passage from stages to `LimitTower` | done | `StageTower.lean` — `StageSequence` and `StageSequence.limitTower`, with no free hypotheses; `isHomeoOn_F` is `prop:interior-homeomorphism` in exactly the shape `HasLimitHomeomorphism`'s second conjunct asks for, and `F_eq_skelHomeo` is the bridge that will discharge `HasAnchorCrosscuts` |
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
