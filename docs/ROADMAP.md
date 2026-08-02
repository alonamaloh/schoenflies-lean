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
Schoenflies.stageSequence        the fields of LimitTower ← HasGridSteps, HasMeshSteps
```

| Assumed | Declared in | Blocks | Notes |
|---|---|---|---|
| `Schoenflies.SquareExtension` | `Endgame.lean` | `thm:main` | discharged by `square_extension` below, so not really open |
| `Schoenflies.HasLimitHomeomorphism` | `BoundaryContinuity2.lean` | `thm:square-extension` | four conjuncts: a dense anchor set, the interior homeomorphism, `HasAnchorCrosscuts`, `HasSpokes`. **`stageSequence` + `limitTower` supply the second given the two choosers below; the other three need `lem:anchor-density` and the `SkeletonCrosscuts.lean` handoff.** |
| the fields of `CellStructure.LimitTower` | `LimitMap.lean` | the interior homeomorphism | **supplied**: `Schoenflies.stageSequence` (`StageRecursion.lean`) builds the `StageSequence`, and `StageSequence.limitTower` the tower, conditional only on the two choosers below. `prop:shrinking-stars` is proved inside the recursion, not assumed |
| `Schoenflies.HasGridSteps` | `StageRecursion.lean` | the interior homeomorphism | **discharged** by `Schoenflies.hasGridSteps` (`GridSteps.lean`) from `HasGridExtensions` below — the transfer invocation, the star bound, the `Piece`→`γ` relabelling (`Graph.relabel`, `IsSourceExtensionOver`), the window placement and the `MeetsFinitely` reduction are all proved there |
| `Schoenflies.HasGridExtensions` | `GridSteps.lean` | `HasGridSteps` | at every stage, window and mesh: an `IsSourceExtension` whose point set carries the local grid over the window. The discharger must build **`gridAttachGraph` ∪ the outer part of the stage's own graph** — the grid alone cannot satisfy `skeletonSet_subset`, since `|Γ|` contains the wild `C`; the nonboundary skeleton enters through `gsegs` inside the overlay so crossings become vertices. The `hΓ` 2-connectivity assembly lives here, with `localGrid_subdivide_isTwoConnected` already discharging the `hK` side. See the module docstring's itemized obligations |
| `Schoenflies.HasMeshSteps` | `StageRecursion.lean` | the interior homeomorphism | **discharged** by `Schoenflies.hasMeshSteps` (`MeshSteps.lean`) from `HasMeshTransfers` below — the quantitative half, the fresh-anchor supply and the fourth ambient fact are all proved there |
| `Schoenflies.HasMeshTransfers` | `MeshSteps.lean` | `HasMeshSteps` | **discharged** by `Schoenflies.hasMeshTransfers` (`MeshTransfer.lean`) from `HasMeshOverlays` below, via the repaired `finite_transfer_back'` — the fresh-point supply at density `min ε 3`, the `HasFreshAnchors` derivation, the γ-renaming (`Graph.renameEdges`, `Graph/RenameEdges.lean`) and the ambient facts are all proved there. (The cut at the transfer's conclusion had been forced by the pre-repair deadlock, the ninth entry of "What the standing rules caught"; `IsTransferOfTgt` was untouched by the repair, as the cut anticipated) |
| `Schoenflies.HasMeshOverlays` | `MeshTransfer.lean` | `HasMeshTransfers` | the overlay construction itself: given any valid fresh list, a `MeshOverlayExtension` — the extension clauses over a free edge type for `meshSegments` overlaid with the polygonal target skeleton **plus joining arcs**. The joining arcs are load-bearing: for an arbitrary admissible stage, mesh ∪ skeleton alone can have disconnected complement of `S` (counterexample recorded at the `isConnected` field). Discharger: `polygonal_overlay` + mesh clauses 3–5 + the 2-connectivity toolkit; the risky fields are audited in the module docstring |
| anchor incidence | `SkeletonCrosscuts.lean` | `HasAnchorCrosscuts`, `HasSpokes` | the surviving condition of `lem:skeleton-crosscuts` as assembled: each anchor has an incident nonboundary edge — a clause of `lem:anchor-density`. Its former companion `Realization.HasPolygonalArcs` is **a theorem**: `Realization.hasPolygonalArcs_of_isPolygonal` (`PolygonalSkeletonArcs.lean`), with the hypothesis-free corollary `GeneratedPair.tgt_hasPolygonalArcs` that `exists_anchor_crosscut` takes directly |
| `Schoenflies.CellsAbsorb` | `SkeletonAccess.lean`, `FreshAccess.lean` | `lem:polygonal-side-accessibility` | one clause of `lem:cellulation-invariants`. **Discharged at a stage** by `Realization.cellsAbsorb` (`StageCells.lean`) — assertions (i) and (vii) make the 2-cells a partition of the open domain minus the skeleton into open connected pieces, which is the decomposition into components. It remains a hypothesis only where the realization is *not* a stage of a `GeneratedPair` |

**One live integrator debt.** The two chooser waves independently built an edge-renaming:
`Graph.relabel` / `relabelDraw` (`GridSteps.lean`) and `Graph.renameEdges` / `renameDrawing`
(`Graph/RenameEdges.lean`). No name collides and both are correct; `RenameEdges.lean` is the
general, standalone one and should survive. A housekeeping pass should port `GridSteps.lean`'s
internal uses onto it and delete the local copy.

**Neither direction of `thm:finite-transfer` is on this list any more.** (b)'s ear step is
`Schoenflies.earStepTgt` (`EarStepTgt.lean`) and `Schoenflies.finite_transfer_back'` is (b)
assuming nothing beyond its own statement — `IsSourceExtension` on `H`, `HasFreshAnchors` for its
new boundary points, and the two ambient-domain facts. See "How (b) went" below.

**`thm:finite-transfer`(a) is no longer on this list either.** Both of its named hypotheses are
discharged — step 3 by `Schoenflies.earStep` (`EarStep.lean`) and step 1 by
`Schoenflies.commonSubdivision` (`CommonSubdiv.lean`) — and
`Schoenflies.finite_transfer_toward_square'` is the theorem with neither assumed. What it still
takes as arguments is four facts about the two *ambient domains*, the same at every stage:
`dom ∖ outer` open with frontier inside `outer` on each side, which
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and `frontier_sdiff_outer_of_isSeparating`
supply for a closed Jordan region, the shape both sides have.

### How step 1 went

`Schoenflies.commonSubdivision` (`CommonSubdiv.lean`) proves it. The record of what it took,
because two of the three clauses were not where they looked.

**`K` is forced, and what it is.** Step 1 may only subdivide, and a subdivision does not move
the realized skeleton (`SubdivData.skeletonSet_realize`), so `T₀.src.skeletonSet` is still `|Γ|`
and the clause `skeletonSet_eq` forces `pointSet K Hdraw = |Γ|`. Since every edge of `H` inside
`|Γ|` is needed to cover it, `K` is `Schoenflies.sourcePart P.src H Hdraw` — the vertices of `H`
on `|Γ|` with the edges of `H` drawn inside `|Γ|`. `sourcePart_le` and `pointSet_sourcePart` are
two of the three clauses, the latter spending exactly two hypotheses on the extension: `|Γ| ⊆
|H|`, and `edge_subset`.

**The overlay was not on this path.** `exists_overlay_of_biUnion_finite` was recorded here as
what step 1 needed. It is not used: `IsSourceExtension`'s `edge_subset` clause already says an
edge of `H` meeting an open edge of `Γ` runs inside it, i.e. that `H` does not *cross* `Γ`, so
the blueprint's overlay has, in the Lean formulation, already been performed by the hypothesis.
What step 1 actually needed was to extract `K` from `H` and subdivide `Γ` to match.

**The third clause was a naming problem, not a geometric one.** `K.IsTwoConnected` cannot be
read off the bundle even though 2-connectivity of the realized skeleton is a field of
`IsWeaklyAdmissible` and so free at every stage: that graph carries names drawn from `γ` by the
freshness lemmas, while `K ≤ H` forces `H`'s names, and there is no edge relabelling in Mathlib
or in this repo. Nor can the subdivisions simply use `H`'s names —
`SubdivData.newEdge₁_notMem` wants them fresh, and nothing stops an edge name of `H` from
already being a cell of `P`. Three results close it:

* `GeneratedPair.subdivideEdge` (`SubdivStage.lean`) carries the thirteen-field bundle across
  one subdivision, and `GeneratedPair.exists_subdivide_finite` (`SubdivPoints.lean`) iterates
  it, producing the stage whose 0-cells are **exactly** the old ones together with `V(H) ∩ |Γ|`;
* `Graph.adj_congr_of_pointSet_eq` (`Graph/PlaneEdges.lean`) — two finite plane graphs occupying
  the same points with the same vertices have the same adjacency, because the open edges of a
  plane graph are the connected components of what its vertices leave of it. Finiteness is spent
  once, on "the other arcs are a closed set";
* `Graph.IsTwoConnected.of_adj_congr` (`Graph/AdjCongr.lean`) — 2-connectivity travels along
  that adjacency, across a change of edge *type*.

The middle one is worth its own line, because the first plan for it was wrong: it was recorded
here as an ordering argument along a single drawn edge of `Γ`, using
`subarc_subset_of_isPreconnected` and the `ArcMonotone` parameter comparisons. It is nothing of
the sort — the statement mentions neither `Γ` nor the extension, and the proof is one separation
argument, the same shape as `Realization.cell_isComponent` in `StageCells.lean`.

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
for a later module to discharge. Stage 0 is built (`InitialData.generatedPair`, all thirteen
`GeneratedPair` fields, zero hypotheses), and `StageTower.lean` turns a sequence of stages into a
`LimitTower` with no free hypotheses at all.

### The piece that had the real content, and how it went — historical

**This section is a record, not a plan: `EarStep` is closed** (`Schoenflies.earStep`,
`EarStep.lean`). It is kept because the route it argues for is the one the boundary-walk
invariant still rests on, and because the trap it names is one a reader will otherwise walk
into again.

`EarStep` builds a `SplitData` from an ear. Every field was routine except two:
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

**Phase 1 — face boundary cycles, hence `EarStep`.** The one piece with real content.
**1a–1d are done and `sorry`-free, and `EarStep` with them**; 1e, the common subdivision, is
all that is left of the phase.

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
  * `EarSource.lean` — `Schoenflies.exists_earCrosscut` (then named `exists_source_earCrosscut`):
    from exactly what `EarStep` is
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

  The eight general facts these three modules wrote for want of a home are hoisted; see
  "The integrator debts, discharged" below.

* **1d‴. Closing the bundle — done, and it was the whole of what was left.** The assembly
  could not be written against `GeneratedPair` as it stood: `EarStep` quantifies over *every*
  partial transfer `T`, so anything the split needs about `T` has to be in the bundle, and three
  things were not. All three are now closed, in the order they had to be.

  1. **Assertion (vii) on both realizations — two new fields.**
     `SplitData.isCellDecomposition_and_isFaceJordan_realize` consumes `R.IsFaceJordan` and
     reproduces it; `SplitData.isCutPair_of_inter`, which makes the `IsCutPair` that
     `exists_target_ear` consumes, is stated against it on the target. Nothing on `main` ever
     *constructed* an `IsFaceJordan` — the inventory held the structure, its API and the two
     step theorems, and no realization anywhere satisfied it, stage 0 included. So
     `GeneratedPair` has `src_isFaceJordan` and `tgt_isFaceJordan`, discharged in
     `InitialGenerated.lean` in four lines each: `IsCrosscut.isJordanCurve_union` splices the arc
     of `C` with the crosscut, `IsSeparating.frontier_inside` identifies the frontier of its
     bounded region with the curve, and `sourceRealization_cell_face` finishes it.
  2. **`Schoenflies.CellsAbsorb` — a theorem, not a field.** `StageCells.lean`: assertion (i)
     partitions the closed domain into open cells, (vii) makes every 2-cell open and connected,
     and `disjoint_cell_skeletonSet` keeps them off the skeleton — so the 2-cells partition
     `(dom ∖ outer) ∖ |Γ|` into disjoint nonempty open connected pieces, which *is* its
     decomposition into components (`Realization.cell_isComponent`). `cells_isComponent_in` is
     the same fact in the shape `exists_target_ear` and
     `polygonal_side_accessibility_target` consume, so one theorem retires a live obligation and
     supplies the target-side presentation at once. Only the *shape of the domain* stays a
     hypothesis — `dom ∖ outer` open with frontier inside `outer` — and it is stage-independent,
     so it can be an argument of `earStep`.
  3. **Polygonality of every target edge — one new field, `tgt_isPolygonal`.** Not implied by
     weak admissibility: `IsWeaklyAdmissible.isPolygonal` is restricted to *nonboundary* edges,
     correctly, because the outer edges of a *source* stage are subarcs of the wild `C`. This is
     the one place the two sides of a matched cellulation are genuinely not mirror images, and
     the reflex to mirror them is what would have kept costing. Discharged at stage 0 by
     `InitialData.isPolygonal_tgt_edgeArc`, which `InitialPairFixed.lean` had proved and nothing
     consumed.

  With the bundle closed, `GeneratedPair.splitFace` (`SplitStage.lean`) carries all thirteen
  fields across one split, and `Schoenflies.earStep` (`EarStep.lean`) is the assembly. Two
  things had content beyond bookkeeping:

  * **`IsArcBetween.isPolygonal_of_subset'`** (`PolygonalCut.lean`). The existing lemma asks the
    sub-arc to *start where the ambient one does* — enough for the two halves of a subdivided
    edge, not enough for an interior ear edge, which touches neither end of the crosscut it was
    cut from. Two applications of the special case remove the restriction, and identifying the
    sub-arc needs `subarc_subset_of_isPreconnected` based at an arbitrary parameter rather than
    at `0` — which its proof never used, so it is now stated generally.
  * **The degenerate ear.** `EarStep`'s hypotheses do not say the ear brings a new edge, and the
    disjointness argument needs it. `Graph.IsPath.eq_singleton_of_inc` shows the only ear that
    fails it is a single edge `B` already has, for which `B ∪ ear = B`.

  What follows is the record of the earlier blockers, all closed.

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
* **1e. `CommonSubdivision` — done.** Independent of 1b–1d.
  `GeneratedPair.subdivideEdge` (`SubdivStage.lean`) carries the thirteen-field bundle across one
  subdivision — the mirror of `GeneratedPair.splitFace`, the one clause that does not copy being
  `outerSet_eq`, since a subdivision really does change the outer graph when the subdivided edge
  is outer (`SubdivData.outerSet_realize`). `GeneratedPair.exists_subdivide_finite`
  (`SubdivPoints.lean`) iterates it over a finite set of skeleton points; `sourcePart`,
  `Graph.adj_congr_of_pointSet_eq` and `Graph.IsTwoConnected.of_adj_congr` are the other three
  ingredients, and `Schoenflies.commonSubdivision` assembles them. See "How step 1 went" above
  for the two places the plan recorded here was wrong.

**Phase 2 — `thm:finite-transfer`.** (a) **is unconditional** —
`Schoenflies.finite_transfer_toward_square'`. **(b)'s step 1 is done too**: `IsSourceExtension`
turned out to be direction-agnostic — it is stated for an arbitrary realization, so (b)'s
hypotheses on `H'` are `IsSourceExtension P.tgt tgtOuter tgtDom H' H'draw`, and `sourcePart`,
`pointSet_sourcePart`, `Graph.adj_congr_of_pointSet_eq` and
`Graph.IsTwoConnected.of_adj_congr` apply to the target side unchanged. Only the subdivision
induction needed a twin, because `GeneratedPair.subdivideEdge` cuts the *source* edge at a
given parameter and the target edge at the one the skeleton homeomorphism sends it to;
`exists_subdivide_finite_tgt` drives it from a prescribed target point instead, and needs no
inverse parameter — `SkeletonHomeo.image_cell` supplies the corresponding source point and
`SubdivData.drawing_targetParam` says the target cut lands on the nose. **(b) is now
unconditional too**: `Schoenflies.finite_transfer_back'` (`EarStepTgt.lean`) assumes nothing
beyond its own statement. What follows is the record of what its ear step took, because two of
its pieces were not where they looked.

The ear step's two halves are of very different sizes. An endpoint off `C` is accessible from
the corresponding source face — that is
`CellStructure.Realization.polyAccessible_of_notMem_outer` (`SourceAccess.lean`), **done**. It
is not `polygonal_side_accessibility_target`, which asks every edge polygonal and which a source
realization never satisfies; the general `Graph.polygonal_side_accessibility` applies, because
it already carries a compact wild set to be adjoined, and the whole content is choosing the
graph — `Realization.nonboundaryGraph`, the drawn skeleton with the outer edges deleted, whose
point set together with the outer curve is the whole skeleton. An endpoint *on* `C` is the
anchor `a` of a fresh point `u(a)`, and
`Schoenflies.polyAccessible_of_stronglyAccessible` (`FreshAccess.lean`) is that paragraph,
proved — but carrying `hunique`, *the only current source 2-cell whose closure contains `a` is
the one corresponding to the target face*.

#### `hunique` is closed, and what it took

`hunique` was the blueprint's combinatorial paragraph ("each of the resulting outer subedges is
incident with exactly one source 2-cell … hence exactly one descendant 2-cell remains incident
with `a`"), and it was recorded here as the one piece of direction (b) with real content left.
`AnchorFace.lean` is that paragraph. Three of its sentences turn out to be vacuous once the
representation is fixed, and the module docstring records why; what is *not* vacuous is
`CellStructure.SplitData.uniqueFaceAt`, the induction step.

**The paragraph is `S.UniqueFaceAt z` — at most one 2-cell above a 0-cell — and the anchor is
tracked as a 0-cell, not as a pair of outer subedges.** The subdivision constructor hands a
created cell exactly the supercells of the edge it cut
(`SubdivData.newCells_subRel_iff`), so one subdivision moves
`lem:cellulation-invariants`(vi) from the outer edge to the fresh point and the blueprint's
"the two subedges have the same incident 2-cell" never arises. Both appeals to
`lem:combinatorial-invariance`(c) are free for the same reason the endpoint transfer of
direction (a) is: `sub` is a field of the **one** abstract structure both realizations realize,
so the source 2-cell above `z` and the target 2-cell above `z` are the same name.

**The invariant is now carried, and that was the other half.** `EarStepTgt` quantifies over
every intermediate stage, so — the failure mode this file has recorded three times — nothing
outside the bundle could supply it. `IsPartialTransferOfTgt` has the clause
`anchor_uniqueFaceAt`: a 0-cell whose ancestor in the base pair is an outer edge, *and at which
the current subgraph still has no nonboundary edge*, is incident with at most one 2-cell. Both
conditions are load-bearing. Without the first the clause would be a statement about old 0-cells
of the outer cycle, which is a different theorem; without the second it is **false** from the
moment the ear at `u(a)` is inserted, since an ear ending at a 0-cell leaves both descendants
incident with it. They move together, because the ear at `u(a)` is the unique new nonboundary
edge there — which is exactly the second sentence of `thm:finite-transfer`(b), the fresh-anchor
hypothesis that no other part of (b) spends.

The base case is discharged **unconditionally**: `GeneratedPair.exists_subdivide_at_tgt` and
`.exists_subdivide_finite_tgt` also return `CellStructure.PropagatesUniqueFace` — the invariant
at a cell follows from the invariant at its parent, in the form that survives an unknown number
of subdivisions — and `commonSubdivisionTgt` spends it against (vi) at the base pair. Nothing
else in the chain changed shape: `transfer_of_ears_tgt` and `finite_transfer_back` recompile
untouched.

#### How the ear step went

**Both geometric halves are shared with direction (a), and that was the surprise.** Three
theorems that looked like they would need target-side twins did not:

* `Schoenflies.exists_earCrosscut` (`EarSource.lean`) places an ear from **either** realization.
  The five clauses that named `T.src` are a realization's cell decomposition, its outer set, what
  it occupies, which of its 0-cells are drawn, and the absorption family; nothing in the
  placement argument knows which side it is on, and `IsSourceExtension` was already
  direction-agnostic. `GeneratedPair.exists_face_and_boundary_paths` was generalized the same way
  — only assertion (i) and the two endpoint positions were ever about one realization, since the
  boundary cut is about the abstract structure both realize.
* `lem:accessible-endpoints` is shared: `Schoenflies.exists_crosscut_of_accessible_ends` takes
  the accessibility of the two endpoints as hypotheses, and `exists_target_crosscut` / `_split`
  are now that with `lem:polygonal-side-accessibility` supplied — which is available on the
  target side only, because it wants every edge polygonal.
* `Schoenflies.exists_target_earCrosscut` was already stated for two arbitrary realizations. What
  it needed was `CellStructure.SplitData.EarHomeo.symm`: it matches the ear one is *given* to the
  ear one *builds*, the two directions are given theirs on opposite sides, and
  `GeneratedPair.splitFace` always wants the matching from source to target.

So the genuinely new work was the source crosscut (`SourceEar.lean`) — the two-case split that
direction (a) never meets, `polyAccessible_of_notMem_outer` off `C` and the anchor paragraph on
it — and the assembly.

**Two obligations that looked like new invariants were not.**

* The geometric twin of `anchor_uniqueFaceAt` — the blueprint's "`K` … does not contain `a`" —
  follows from the untouched condition already in the bundle. Take `K` on the target side as
  `closure (|B| ∖ S)`; `Graph.closure_pointSet_diff_subset` says what a finite plane graph leaves
  outside a set is contained in the vertices outside it together with the arcs of the edges not
  inside it, which is closed, so a closure point on `S` lies on a nonboundary edge of `B` through
  the anchor — exactly what the untouched condition forbids. `T.homeo` then transports it to the
  source, where `polyAccessible_of_stronglyAccessible` wants it.
* "The ancestor of the anchor is an outer edge" is derived, not assumed:
  `Realization.Refines.cell_subset` puts the anchor in the open cell of its ancestor, a 0-cell
  ancestor would make it a drawn 0-cell of the base pair and a 2-cell ancestor would put it off
  the skeleton, and `Realization.mem_edgeSet_outerGraph_of_cell_meets_outerSet` makes the
  surviving 1-cell an outer one.

**One was.** `IsPartialTransferOfTgt.homeo_eqOn` — the stage's skeleton map agrees with the base
pair's on the base skeleton — is nowhere derivable from the other clauses, because
`Realization.Refines` says nothing about the two homeomorphisms. Without it the fresh-anchor
accessibility hypothesis, which is about the *base* pair's correspondence, cannot be spent at an
intermediate stage. A subdivision does not change the map at all, so the base case is the
identity; `SplitData.splitHomeo_eqOn` restricted along `Realization.Refines.skeletonSet_subset`
is the step. It was found by writing down what the assembly would pass **before** writing the
assembly, which is the cheap defence this file has recommended four times.

**Phase 3 — the stage recursion.** Where `GridAttach.lean`, `SquareMeshClosed.lean` and
`Windows.lean` are spent, giving `lem:grid-star-estimate` and `prop:shrinking-stars`. This is
the largest phase by far.

**The recursion itself is now written.** `Schoenflies.stageSequence` (`StageRecursion.lean`) is
a `def` producing the `Schoenflies.StageSequence γ S₀ C` (`StageTower.lean`) whose
`limitTower` supplies the second conjunct of `HasLimitHomeomorphism`, and
`stageSequence_of_isJordanCurve` instantiates it at stage 0 = `(initialData hC).generatedPair`.
All fourteen fields have suppliers; `prop:shrinking-stars` itself — the dense-recurrence
argument, `mem_openWindow_of_supDist_lt`, the catch-index bound, and monotonicity of stars
under refinement — is **proved inside it**, not assumed. What it takes is exactly two named
hypotheses, the two enlargement choosers:

* **`Schoenflies.HasGridSteps S₀ C`** — at every strongly admissible stage, for every `ε > 0`
  and window centre, a refined stage one `IsRefinementStep` away whose new source stars have
  diameter `≤ 2ε` inside the open window. This is `prop:local-grid-attachment` +
  `thm:finite-transfer`(a) + `lem:grid-star-estimate` in one bundle.
* **`Schoenflies.HasMeshSteps S₀ C`** — the same minus the centre, with every closed target
  2-cell of diameter `≤ ε`. This is `prop:anchored-square-mesh` (done) + overlay +
  `thm:finite-transfer`(b), whose `HasFreshAnchors` is the mesh's clauses 3–4.

Two findings from writing it, recorded so the dischargers do not trip on them: the choosers
need **strong admissibility of their input stage** — the grid attachment uses connectedness of
`|Γ| ∖ C` — which `StageSequence` does not carry, so the recursion's state is an
`AdmissibleStage` (pair + both admissibilities), replenished each step by the transfer
conclusions; and stage 0 needs its own target-star bound since no mesh step precedes it, hence
`eps 0 = 4` via `diam_tgt_star_le_four`. The choosers quantify over *arbitrary* admissible
stages, not the recursion's own — both intended dischargers need no history (anchor
accessibility is domain-level; mesh freshness avoids only the current finite vertex set), but
if a future discharger does need recursion-specific facts, the hypotheses must be re-cut.

What is left of the phase is discharging the two choosers, and the missing pieces are:

0. **`lem:grid-star-estimate` is done** — `Schoenflies.StagePair.diam_star_le_of_grid`
   (`GridStarEstimate.lean`), whose conclusion is verbatim the `GridStepData.diam_star_le`
   field. One hypothesis, `hgrid`: the local grid cover over the window is inside the stage's
   source skeleton, supplied by `localGrid_subset_gridAttachGraph` composed with
   `IsPartialTransferOf.skeletonSet_eq` after the transfer. **A renaming obligation surfaced
   there**: `gridAttachGraph` names its edges by `Piece = Plane × Plane` while the transfer
   fixes `H : Graph Plane γ`, and this repo deliberately has no edge relabelling — the
   `HasGridSteps` discharger must rebuild the grid graph over `γ` (the `InitialCell.aux` spare-
   constructor route) before invoking `finite_transfer_toward_square'`. The renaming preserves
   the drawn point set, which is all `hgrid` reads. Note also the trapping step deliberately
   bypasses `cells_isComponent_in` (wrong complement — the argument runs against the grid
   cover, not the whole skeleton) and uses its two ingredients `IsFaceJordan.isConnected` and
   `disjoint_cell_skeletonSet` directly.

1. **`hΓ`** of `gridAttachGraph_isTwoConnected` — 2-connectivity of `Γ` with the case's crosscut
   and the loop's joining arcs appended and everything subdivided at the crossings. Not provable
   in `GridAttach.lean`, which never sees `Γ`'s drawing; every ingredient exists
   (`pieceListGraph_subdivide_isTwoConnected`, `Graph.IsTwoConnected.replace_edge_by_path`,
   `Graph.IsTwoConnected.ear`, `pieceListGraph_append_crosscut`) and assembling them is the
   caller's job.
2. **`hcov` — done**, and it exposed a blueprint defect (see "What the standing rules caught").
   The blueprint's *"since there are only finitely many components"* of `|L| ∖ C` is **false**
   as a general plane fact — a segment can meet a wild `C` in a Cantor set. What the blueprint
   silently spends is a drawing invariant, isolated in `GridComponents.lean` as
   `Schoenflies.MeetsFinitely l C` (every piece meets `C` finitely), under which the whole
   coverage fact is a **theorem**: `exists_reps_hcov` returns finite representatives, in the
   cover and off `C`, whose second conjunct is *syntactically* the `hcov` of
   `gridAttachGraph_isConnected_diff`, and
   `gridAttachGraph_isConnected_diff_of_meetsFinitely` composes end-to-end with no `hcov`
   left. No component is ever named — midpoints between consecutive crossing parameters do the
   work. What survives for the assembler is `MeetsFinitely gsegs C`, a fact about `Γ`'s drawing
   with the same owner as `hΓ`.
3. **`lem:grid-star-estimate`**, tying the grid mesh to a star diameter bound. The metric half is
   ready in `Windows.lean`; what is missing is the geometry.
4. **`skelHomeo_succ` on the source side — done.** `IsPartialTransferOf` now carries
   `homeo_eqOn`, the exact mirror of `IsPartialTransferOfTgt.homeo_eqOn`: the stage's skeleton
   map agrees with the base pair's on the base source skeleton. It went exactly as predicted —
   identity at a subdivision (`exists_subdivide_at` / `exists_subdivide_finite` now return the
   conjunct their `_tgt` twins always had), and `SplitData.splitHomeo_eqOn` restricted along
   `Realization.Refines.skeletonSet_subset` at the ear step, chained with the stage's own
   clause. No consumer outside the four construction sites changed.

Item 4 was the fifth instance of the shape this file has now recorded four times: the bundle
that carries a construction is one invariant short of its consumer. It was found by writing out
the fourteen `StageSequence` fields and naming a supplier for each **before** building the
recursion — which is the cheap defence, and it was cheapest at exactly that moment, because
nothing yet constructed a `StageSequence`.

**Phase 4 — `thm:main` unconditional.** `HasAnchorCrosscuts` and `HasSpokes` from the stages.
The limit map and everything after it is already built and waiting.

The bridges are written, and `lem:skeleton-crosscuts` is now assembled at the cell-structure
level. `StageSequence.F_eq_skelHomeo` says `F` agrees with each stage's *finite* skeleton
homeomorphism wherever that stage's skeleton reaches; two anchors are 0-cells at some stage, and
`GeneratedPair.exists_anchor_crosscut_stage` (`SkeletonCrosscuts.lean`) joins them by a crosscut
in that stage's skeleton **and** carries it through the stage homeomorphism to a crosscut of the
square, with the endpoint bookkeeping `HasAnchorCrosscuts` wants — conditional on
`Realization.HasPolygonalArcs` for the target stage (an arc in a polygonal-edged skeleton is
polygonal; honest later-module work) and on the anchor-incidence clause of `lem:anchor-density`
(each anchor has a nonboundary edge attached). What remains for `HasAnchorCrosscuts` itself is
the identification of `u` (the boundary map) with the drawn target 0-cells at the anchors —
clause 2 of `def:matched-pair`, which whoever builds the stage tower must carry — plus
`F_eq_skelHomeo` to replace `g` by `F`. `HasSpokes` uses the same bridge on an initial subarc of
the nonboundary edge `lem:anchor-density` attaches at the anchor. The dense anchor set `𝒜` is
`lem:anchor-density` itself.

`Schoenflies.CellsAbsorb`, the one live obligation outside these two phases, retires itself:
`Realization.cellsAbsorb` discharges it at any stage of a `GeneratedPair`, so it survives only
where no such sequence exists.

### The integrator debts, discharged

Everything this file and the module docstrings recorded as "written here for want of a home" is
hoisted. Nothing was restated and nothing was renamed, so no consumer changed; what changed is
which module a fact can be reached from.

| Fact | Was in | Now in |
|---|---|---|
| `Graph.setOf_mem_cons`, `Graph.IsPath.eq_singleton_of_inc` | `EarDraw.lean`, `EarSource.lean` | `Graph/Walk.lean` |
| `Graph.union_eq_left_of_le` | `EarSource.lean` | `Graph/TwoConnected.lean`, beside `Graph.union` |
| `Graph.edgeArc_map`, `Graph.pointSet_map`, `Graph.IsDrawing.map_of_injOn` | `EarTarget.lean` | `Graph/Drawing.lean` |
| `Graph.closure_pointSet_diff_subset` | `EarSource.lean` | `Graph/Drawing.lean` |
| `Graph.walkPointSet` and its API, `Graph.IsPath.map`, `Graph.IsPathGraph.map`, `Graph.map_union` | `RealizeSplit.lean` | **`Graph/DrawnWalk.lean`**, new |
| `Graph.pointSet_pathGraphOf`, `Graph.IsDrawing.isPolygonal_walkPointSet` | `EarSource.lean` | `Graph/DrawnWalk.lean` |
| `Schoenflies.continuousOn_invFunOn_image` | `InitialPair.lean` | `Topology.lean` |
| `SubdivData.outer_vertexSet_of_mem` | `SubdivStage.lean` | `GeneratedStructure.lean`, beside `outer_edgeSet_of_mem` |
| `Realization.Refines.skeletonSet_subset` | `StageCells.lean` | `RefinementStars.lean`, beside `Refines` |

Three of them were not simple moves, and the reasons are worth keeping.

* **`walkPointSet` had to move for two of the eight to move at all.** `Graph.pointSet_pathGraphOf`
  and `IsDrawing.isPolygonal_walkPointSet` are stated in terms of it, and it lived in
  `RealizeSplit.lean` — four layers of cell-structure machinery above the graph modules the two
  facts belong in. `RealizeSplit.lean`'s own docstring had said "if a second consumer appears
  they belong in `Schoenflies/Graph/`"; the ear steps of both directions were that consumer.
  `Graph/DrawnWalk.lean` is the module, on `Graph.PathGraph` + `Graph.Drawing` + `Concatenate` +
  `Polygonal`, and it carries `IsDrawing.isArcBetween_walkPointSet` — the workhorse that makes a
  drawn path an arc — down with it.
* **`Refines.skeletonSet_subset` was blocked by `cellUnion`, not by its own content.** Its proof
  went through `skeletonSet_subset_cellUnion`, and `Realization.cellUnion` is defined in
  `CellulationInvariants.lean`, which imports `RefinementStars.lean` — so the lemma could not
  follow `Refines` down. The dichotomy it actually uses has nothing to do with `cellUnion`:
  a skeleton point is a drawn vertex, or an endpoint of a drawn arc, or an interior point of one.
  That is now `Realization.exists_cell_of_mem_skeletonSet`, next to its converse
  `cell_subset_skeletonSet` in `CombinatorialInvariance.lean`, and `skeletonSet_subset_cellUnion`
  is a three-line corollary where `cellUnion` exists.
* **`IsPath.eq_nil_of_eq` came along.** `eq_singleton_of_inc` uses it, and it was in
  `FaceCycles.lean` — a module far above `Graph/Walk.lean`, which is where the rest of the
  `IsPath` basics are.

`EarTarget.lean` dropping `import Schoenflies.InitialPair` is the one with a measurable effect:
`InitialPair.lean` is no longer in the import closure of `EarTarget.lean` or of anything above it
up to `EarStepTgt.lean`.

### What the standing rules caught

Nine things, all worth the cost of the rules that found them — and one of the same kind that a
rule did not have to catch, because writing the field caught it first.

**A proved theorem whose hypotheses are jointly unsatisfiable at its intended call site, the
second.** `finite_transfer_back'` was proved, and no mesh overlay could ever satisfy its
hypotheses together. `IsSourceExtension.edge_subset` forced any `H`-edge merely *touching* an
old open 1-cell to run inside that edge's arc — so a spoke reaching the outer curve at a fresh
point (which sits inside an old outer edge's open 1-cell) was forbidden outright; the only
escape, pre-subdividing the outer edge at the fresh point, was forbidden by
`HasFreshAnchors.notMem_vertexSet`, which quantified over *all* of `E(H)` where the blueprint
says the *new* edges `H′ ∖ Γ′`. **Repaired**, along the first of the two candidates the
finding proposed: `edge_subset` now triggers only at a meeting point that is not a vertex of
`H` (the overlay convention — a spoke may end on an open old 1-cell), and every clause of
`HasFreshAnchors` is restricted to the new edges by a `¬ edgeArc ⊆ |Γ′|` clause in
`NonboundaryAt`. The choice fell on this candidate because the strong `edge_subset` had one
consumer (`pointSet_sourcePart`, a two-line case split to re-prove) and the anchor-tracking
machinery survives untouched; what the strong forms gave `earStepTgt` is re-proved
(`IsSourceExtension.edge_subset_of_edgeArc_subset_skeletonSet`: an edge *on* the old skeleton
cannot merely touch an open 1-cell, so old edges still cannot reach fresh points except
inside the outer curve). `MeshSteps.lean` keeps the machine-checked record — the deadlock
re-proved against the pre-repair hypotheses stated as explicit local hypotheses
(`edgeArc_subset_outer_of_strong_hypotheses`, `not_nonboundaryAt_of_strong_hypotheses`),
which the live structures no longer supply, plus the satisfiability half
(`edge_subset_clause_of_inter_subset_vertexSet`: the repaired clause accepts the spoke the
old one forbade). `IsTransferOfTgt` was untouched, so everything cut at the transfer's
conclusion survived the repair verbatim, as predicted. The same `edge_subset` overshoot would
have met direction (a)'s discharger at interior crossing points; the weakening frees those
too, since `IsSourceExtension` is direction-agnostic. Found the same way as the
`FreshAccess` instance: by writing down what the discharger would pass, before writing the
discharger.

**A false finiteness claim in a blueprint proof.** `prop:local-grid-attachment`'s joining loop
terminates "since there are only finitely many components" of `|L| ∖ C`. As a general plane
fact that is false: a straight segment can meet a wild Jordan curve in a Cantor set, so
`segment ∖ C` can have uncountably many components. What the blueprint silently spends is that
every segment actually fed to the loop meets `C` finitely — nonboundary edges of `Γ` meet `C`
only at shared vertices, the auxiliary crosscut's open part lies in a face, the grid is
disjoint from `C`. `GridComponents.lean` isolates that as `Schoenflies.MeetsFinitely`, proves
the coverage fact as a theorem under it (`exists_reps_hcov`), and records the defect in its
docstring. Found by the instruction this file keeps repeating: pin down what a "finiteness"
rests on before formalising it.

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

**An invariant every step theorem consumed and nothing ever constructed.**
`Realization.IsFaceJordan` — assertion (vii) — had a structure, an API, and two *step* theorems
saying each elementary operation preserves it. No module anywhere built one, stage 0 included,
so every one of those theorems was vacuously unusable. It surfaced only when `EarStep` tried to
apply the split step and found the hypothesis unreachable: it is a property of the intermediate
stage, and `EarStep` quantifies over every intermediate stage, so it could not come from
outside. The repair is two fields of `GeneratedPair` and four lines at stage 0. What is worth
recording is the shape, because it is the third time: the bundle that carries a construction was
one invariant short of its consumer, and the shortfall was found at the consumer rather than at
the design. `walks` was the first, (vii) the second, target polygonality the third — and the
cheap defence is to read the hypothesis list of every step theorem and every geometric factory
*before* writing the assembly, which is what closed them all in one wave.

**A proved theorem whose hypotheses were contradictory at its only call site — repaired.**
`Schoenflies.polyAccessible_of_stronglyAccessible` (`FreshAccess.lean`) took one compact set `K`
and asked both `a ∉ K` — the cone is shrunk until it misses `K` — and `CellsAbsorb K cells`, the
absorption clause of `lem:cellulation-invariants`(i). The two cannot hold together in the
intended instantiation, and the theorem's own conclusion is the witness. Let `F ∈ cells` be a
2-cell with `a ∈ closure F` and `Disjoint F K`, which is what a stage supplies. Then `insert a F`
is preconnected (`F` is preconnected and `insert a F ⊆ closure F`), disjoint from `K`, and meets
`F` — so `CellsAbsorb K cells` forces `insert a F ⊆ F`, i.e. `a ∈ F`. But `a` lies on the outer
curve and an open 2-cell does not. So `a ∈ K`, and `ha : a ∉ K` was unsatisfiable.

Nothing was wrong with the *proof*: `accessCone_subset_cell` uses `Disjoint (cone) K` for the
absorption and `x ∉ K` for the covering, and both are true of the whole skeleton, while the
shrinking is true of the smaller compact set the blueprint calls `K`. Conflating them is what
made the statement vacuous. The repair is two sets with `D ∩ K' ⊆ K`, three lines, and is done;
see "How the ear step went" above for the instantiation, and note that the second induction
obligation it looked like it would bring turned out to follow from the anchor clause already
present.

It is the fourth instance of the same shape and the first where the defect is *unsatisfiability*
rather than a missing invariant, so the standing rule that caught it is a different one: a
hypothesis must be a statement one believes **and that a later module can discharge**. This one
was believed and cannot be discharged. Found by writing down what the consumer would pass, before
writing the consumer.

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
open. With Part I closed, assertions (i) and (vii) of `lem:cellulation-invariants` are done, both
realization constructors are built, and both directions of `thm:finite-transfer` are
unconditional — so the critical path is no longer any of those. **It is the stage recursion, and
nothing else.** Everything below `thm:square-extension` in this table is proved against
`Schoenflies.SquareExtension`; `square_extension` proves that from
`Schoenflies.HasLimitHomeomorphism`; and all four conjuncts of *that* come from one term, a
`Schoenflies.StageSequence` — which `Schoenflies.stageSequence` (`StageRecursion.lean`) now
builds from the two chooser hypotheses `HasGridSteps` and `HasMeshSteps`. Phase 3 above is the
list of what discharging those still needs.

| Statement | Status | Where |
|---|---|---|
| `def:admissible-graph`, `def:matched-pair`, `def:matched-cellulation` | done | `CombinatorialInvariance.lean` (`CellStructure`, `Realization`, `SkeletonHomeo`) |
| `lem:combinatorial-invariance` | done | `CombinatorialInvariance.lean` |
| `lem:outer-incidence` | done | `LimitMap.lean` (`IsCellDecomposition.closure_cell_meets_outer_iff`, `.star_meets_outer_iff`, `LimitTower.star_meets_bdry_iff`). **Not** `CombinatorialInvariance.outerEdge_face_corresponds`, which this table used to point at — that is assertion (vi), a different statement |
| `def:strong-accessibility`, `lem:nearest-strong`, `lem:tangent-cone`, `prop:countable-strong-access` | done | `Accessible.lean` |
| `lem:square-point-mover` | done | `SquareMover.lean` |
| `lem:local-skeleton-structure` | partial | `SkeletonLocal.lean` + `SkeletonSectors.lean` — open only at points with fewer than two local directions; the two missing cases are closed in `SkeletonAccess.lean` |
| `prop:anchored-square-mesh` | **done** | `SquareMesh.lean`, `SquareMeshConnected.lean`, `SquareMeshFixed.lean`, `LocalGrid.lean` for clauses 1, 2, 3, 4, 6; `SquareMeshClosed.lean` for clause 5 (`squareMesh_isTwoConnected`, on `FreshDense fresh δ` and `δ < 4`, both free at the call site since the blueprint uses `δ = 2⁻ⁿ`) and for the outer cycle as a genuine cycle of the graph, exported as data |
| `lem:skeleton-crosscuts` | conditional (`Realization.HasPolygonalArcs`, anchor incidence) | the extraction is `AccessibleJoin.lean`; the graph-level clause 1 was already on `main` as `Graph.IsStageOn.exists_crosscut` (`BoundaryContinuity.lean`) — the `AccessibleJoin` docstring used to deny this; the cell-structure assembly and the transport through the stage homeomorphism are `SkeletonCrosscuts.lean` (`IsAdmissible.isStageOn`, `IsAdmissible.exists_crosscut`, `SkeletonHomeo.isCrosscut_image`, `GeneratedPair.exists_anchor_crosscut_stage`). Conditional on `HasPolygonalArcs` (an arc in a polygonal-edged skeleton is polygonal) and on the anchor-incidence clause of `lem:anchor-density` |
| `lem:tangent-dense` | done | `Inversion.lean` |
| `prop:initial-pair` | **done**, and packaged as a `GeneratedPair` in `InitialGenerated.lean` | `InitialPair.lean` (`initialStructure`, both realizations, `InitialData`) completed in `InitialPairFixed.lean`: the anchor clause (`AnchorSet`, `AnchoredInitialData`, `stronglyAccessible_initialData_a`), the matched labelling (`tgt_arcOf_eq_image`, `closure_cell_face_link`), the polygonal target edges, the boundary-walk check, and both hypotheses `harc` / `hcollars` discharged — `initial_pair'` is unconditional |
| `def:generated-structure`, `rem:intermediate-disconnection` | **done** | `GeneratedStructure.lean` for the two operations and the inductive closure; `RealizeSubdiv.lean` / `RealizeSplit.lean` for the realization constructors; `RealizeSubdivHomeo.lean` / `MatchedSplit.lean` for the skeleton map across each. All four unconditional |
| `lem:cellulation-invariants` | done | (ii), (iii), (iv), (v), (vi), (viii), (ix) and (i) at the subdivision constructor in `GeneratedStructure.lean`; **(i) at the split constructor and (vii)** in `CellulationInvariants.lean` (`SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan`, `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan`). Both are *step* theorems, stated against a realization of the refined structure — see the row above for what is still missing |
| `lem:refinement-compatibility`, `lem:star-intersection`, `lem:star-face-mesh`, `lem:cell-neighborhood` | done | `RefinementStars.lean`. The carrier is a total function and refinement is abstract, which is what lets the limit section be built against an interface |
| `lem:polygonal-side-accessibility` | conditional (`Schoenflies.CellsAbsorb`) | `SkeletonAccess.lean` — both halves, on one clause of `lem:cellulation-invariants` |
| `thm:finite-transfer` (a) | **done** | `FiniteTransfer.lean` for steps 2 and 4, the induction scheme and the last paragraph; **step 3** is `Schoenflies.earStep` (`EarStep.lean`, on `EarDraw.lean` / `EarSource.lean` / `EarTarget.lean` / `SplitStage.lean` / `StageCells.lean`); **step 1** is `Schoenflies.commonSubdivision` (`CommonSubdiv.lean`, on `SubdivStage.lean` / `SubdivPoints.lean` / `Graph/PlaneEdges.lean` / `Graph/AdjCongr.lean`). `Schoenflies.finite_transfer_toward_square'` is the headline, assuming nothing but the four ambient-domain facts |
| `thm:finite-transfer` (b) | **done** | `Schoenflies.finite_transfer_back` (`FiniteTransferBack.lean`) is the theorem with only the ear step assumed. **Step 1 is done** — `Schoenflies.commonSubdivisionTgt` (`CommonSubdivTgt.lean`), on `GeneratedPair.exists_subdivide_finite_tgt`; steps 2 and 4 and the final admissibility are `transfer_of_ears_tgt` and `finite_transfer_back`. **The combinatorial paragraph of step 3 is done** — `AnchorFace.lean` (`CellStructure.UniqueFaceAt` and the two elementary operations), carried through the induction as the `anchor_uniqueFaceAt` clause of `IsPartialTransferOfTgt` and discharged at the base by `commonSubdivisionTgt`; **and so are both geometric halves of step 3** — `Schoenflies.exists_earCrosscut` (`EarSource.lean`) places the given target ear, and `GeneratedPair.exists_source_ear` (`SourceEar.lean`) produces the source crosscut. **And step 3 is closed**: `Schoenflies.earStepTgt` (`EarStepTgt.lean`, on `SourceEar.lean`), whose `HasFreshAnchors` is the statement's own second sentence. `Schoenflies.finite_transfer_back'` is the headline, assuming nothing but that and the four ambient-domain facts |
| `prop:local-grid-attachment` | conditional (`hΓ`, `hcov`) | `LocalGrid.lean` (`localGrid`, the diameter clause) + `GridAttach.lean` (the overlay, the crosscut factory, the component-joining loop, and the construction as `def`s). The blueprint's three cases collapse to one; the joining loop is done by representatives rather than by a decreasing component count. `hΓ` is 2-connectivity of `Γ` with the auxiliary arcs appended — not provable there, because `C` is not drawn by segments so `Γ` is not a `pieceListGraph`; `hcov` is "finitely many representatives meet every component of `|L| ∖ C`", where the blueprint's finiteness lives |
| `lem:grid-star-estimate`, `prop:shrinking-stars`, `lem:anchor-density` | `prop:shrinking-stars` **done** conditional on the two choosers; the other two open | the stage recursion now exists (`Schoenflies.stageSequence`, `StageRecursion.lean`) and `prop:shrinking-stars` is proved inside it — the dense recurrence (`recur` on `denseSeq`), `mem_openWindow_of_supDist_lt`, the catch-index bound, and star monotonicity under refinement. `lem:grid-star-estimate` survives as the `diam_star_le` field of `HasGridSteps`, and `lem:anchor-density` is unchanged: open, consumed by `HasAnchorCrosscuts`/`HasSpokes` through `SkeletonCrosscuts.lean`. The metric half stays where it was: `Windows.lean` has `supRadius`, `windowRadius` / `window` / `openWindow` with the blueprint's three inequalities and `W_n(p) ⊆ D`, and the two sequences (`recur`, `tendsto_two_pow_neg`) |
| the passage from stages to `LimitTower` | done | `StageTower.lean` — `StageSequence` and `StageSequence.limitTower`, with no free hypotheses; `isHomeoOn_F` is `prop:interior-homeomorphism` in exactly the shape `HasLimitHomeomorphism`'s second conjunct asks for, and `F_eq_skelHomeo` is the bridge that will discharge `HasAnchorCrosscuts` |
| arc monotonicity | done | `ArcMonotone.lean` — not a blueprint statement; one of the facts the manuscript uses silently. A homeomorphism between two arcs induces a strictly monotone map of parameters, so it carries subarcs to subarcs |
| `prop:skeleton-agreement`, `prop:F-continuous`, `prop:image-interior`, `prop:F-injective`, `prop:target-skeleton-dense`, `prop:F-surjective`, `lem:exact-cell-correspondence`, `prop:inverse-continuous`, `prop:interior-homeomorphism` | **done**, against `CellStructure.LimitTower` | `LimitMap.lean`, with **no free hypotheses at all**: every one takes `L : LimitTower γ` and nothing else, so every obligation is a *field* of the structure. See "The limit section, and why it needed no construction" below for the statement-by-statement map. (`lem:cell-neighborhood` used to be listed here too; it is `RefinementStars.lean`, as the row above says) |
| `lem:crosscut-side-correspondence`, `prop:boundary-continuity` | **done** | `BoundaryContinuity2.lean` — `crosscut_side_correspondence` and `boundary_continuity`. Both take the four conjuncts of `HasLimitHomeomorphism` as explicit arguments and assume nothing else; `isHomeoOn_extendByBoundary` is the two of them assembled into "the extended map is a homeomorphism of the closed domain onto the closed square" |
| `thm:square-extension` | conditional (`Schoenflies.HasLimitHomeomorphism`) | `BoundaryContinuity2.lean` (`square_extension`). **This is the one root obligation of Part II** — every row below reduces to it, and so does `thm:main` |
| `prop:square-reduction`, `thm:closed-interior-extension` | conditional (`Schoenflies.SquareExtension`) | `Endgame.lean` (`square_reduction`, `closed_interior_extension`) — the second is the first, once the target curve is charted to the model square |
| `lem:inversion-sides` | done | `Inversion.lean` (`invert_image_outside`, `IsJordanCurve.invert`, `invertHomeo`) |
| `prop:pointed-extension` | conditional (`Schoenflies.SquareExtension`) | `Endgame.lean` (`pointed_extension`), from `square_reduction` and `lem:square-point-mover` |
| `prop:exterior-extension` | conditional (`Schoenflies.SquareExtension`) | `Inversion.lean` (`exterior_extension`) proves it from `PointedInteriorExtension` and `thm:arc-complement`; `Endgame.lean` (`exterior_extension_of_squareExtension`) discharges both, the second by `Schoenflies.arc_complement` |
| `thm:main` | conditional (`Schoenflies.SquareExtension`) | `Endgame.lean` — `jordan_schoenflies`, with `jordan_schoenflies_homeomorph` and `jordan_schoenflies_of_homeomorph` as the bundled forms. Interior half from `closed_interior_extension`, exterior half from `exterior_extension_of_squareExtension`, pasted along `C` |

These seven rows read **open** until 2026-08-02, which was wrong in the direction this file warns
about least often and should warn about equally: an `open` that is really a `conditional` sends
the next agent to rebuild a proof that is already on `main`. Everything from `thm:square-extension`
down was written against `SquareExtension` as a hypothesis and has been for some time. What is
actually missing is one predicate, `HasLimitHomeomorphism`, and the object that supplies all four
of its conjuncts is a `StageSequence` — see Phase 3.

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
