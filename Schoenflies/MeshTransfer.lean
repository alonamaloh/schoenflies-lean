/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshSteps
import Schoenflies.LocalGrid
import Schoenflies.Graph.RenameEdges

/-!
# The mesh transfer chooser, reduced to the polygonal overlay

`Schoenflies.HasMeshTransfers` (`MeshSteps.lean`) is the target-mesh chooser cut at the
conclusion of `thm:finite-transfer`(b): at every admissible stage `P` and every `ε > 0`, an
`ε`-dense fresh list, an extension `H` containing the anchored mesh of size `ε`, and a
completed direction-(b) transfer of `H`. This module discharges everything about that bundle
except the overlay itself:

* **the fresh points** are chosen by `Schoenflies.exists_fresh_anchor_supply` — `δ`-dense for
  `δ = min ε 3` (so that two distinct fresh points exist,
  `Schoenflies.exists_two_distinct_fresh_of_freshDense`, and so that `ε ≥ 4` needs no special
  case), off the drawn 0-cells of the stage and off any finite bad set the overlay wants
  avoided, with strongly accessible source partners;
* **the transfer** is the repaired `Schoenflies.finite_transfer_back'`, its four ambient facts
  supplied by `Schoenflies.isOpen_sdiff_outer_of_isSeparating`,
  `Schoenflies.frontier_sdiff_outer_of_isSeparating`,
  `Schoenflies.isOpen_closedSquare_sdiff_modelCurve` and
  `Schoenflies.frontier_closedSquare_sdiff_modelCurve`;
* **the anchor clauses** of `Schoenflies.HasFreshAnchors` are assembled from the overlay's
  single combinatorial clause "a new nonboundary edge reaches `S` only at a listed fresh
  point" (`nonboundaryAt_mem_fresh` below) together with the properties of the chosen fresh
  points — so the remaining obligation mentions neither accessibility nor anchor sets.

What remains is `Schoenflies.HasMeshOverlays`: the overlay of the anchored square mesh with
the current polygonal target skeleton, as a bundle `Schoenflies.MeshOverlayExtension` of
exactly the clauses `IsSourceExtension` and `HasFreshAnchors` read, stated over an **arbitrary
edge-name type** `β` — the overlay machinery (`Subdivide.lean`, `Overlay.lean`,
`OverlayGraph.lean`, `SquareMesh*.lean`) names its edges by `Piece = Plane × Plane`, while the
transfer fixes `Graph Plane γ`. The gap between the two is closed here, not left to the
overlay: `Schoenflies.MeshOverlayExtension.rename` rebuilds any finite extension over fresh
`γ`-names via `Graph.renameEdges` (`Graph/RenameEdges.lean`), transporting every clause.

## Interface notes for the integrator

* `Schoenflies.IsSourceExtension` and `Schoenflies.HasFreshAnchors` fix the edge type of `H`
  to the cell-name type `γ` although every one of their clauses is meaningful for
  `H : Graph Plane β`. `Schoenflies.MeshOverlayExtension` is those clauses restated over `β`;
  if the two structures are ever generalized to a free edge type, the restatement and
  `MeshOverlayExtension.rename` collapse into an application of the generalized forms.
* The rename machinery (`Graph/RenameEdges.lean`) is deliberately general: the direction-(a)
  grid discharger (docs/ROADMAP.md Phase 3 item 0) faces the same `Piece`-vs-`γ` mismatch and
  can use `Graph.renameEdges` / `Graph.renameDrawing` / `Graph.exists_injOn_notMem` verbatim.

## Blueprint

* `Schoenflies.FreshDense.mono` — density is monotone in the mesh size.
* `Schoenflies.MeshOverlayExtension` — the overlay's obligations: the clauses of
  `IsSourceExtension` for the mesh-plus-skeleton graph, the `H' ∖ Γ'` boundary-incidence
  clauses of `thm:finite-transfer`(b) reduced to "new nonboundary edges reach `S` in listed
  fresh points, one edge per point", and containment of the anchored mesh
  (`prop:anchored-square-mesh` carried through `lem:polygonal-overlay`).
* `Schoenflies.MeshOverlayExtension.isSourceExtension`,
  `Schoenflies.MeshOverlayExtension.hasFreshAnchors` — at edge type `γ`, the bundle *is* the
  hypotheses of `thm:finite-transfer`(b); the anchor clauses are derived from the fresh-point
  properties.
* `Schoenflies.MeshOverlayExtension.rename` — the bundle transports across an edge renaming;
  with `Graph.exists_injOn_notMem` this is the `Piece`-to-`γ` rebuild.
* `Schoenflies.meshTransfer_of_extension` — one overlay extension yields one
  `Schoenflies.MeshTransfer`, via `Schoenflies.finite_transfer_back'`.
* `Schoenflies.HasMeshOverlays` — **the remaining named hypothesis**: the overlay of
  `lem:polygonal-overlay` applied to the anchored square mesh and the current target skeleton.
* `Schoenflies.hasMeshTransfers` — the discharge of `Schoenflies.HasMeshTransfers` from it.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-- Density of a fresh list is monotone in the mesh size: a `δ`-dense list is `δ'`-dense for
every `δ' ≥ δ`. This is what lets the chooser serve an arbitrary `ε > 0` with points chosen
`min ε 3`-dense. -/
theorem FreshDense.mono {fresh : List Plane} {δ δ' : ℝ} (h : FreshDense fresh δ)
    (hle : δ ≤ δ') : FreshDense fresh δ' := fun A hA hconn x hx y hy =>
  le_trans (h A hA hconn x hx y hy) (by linarith)

/-- **The overlay's obligations, over a free edge-name type.**

A `MeshOverlayExtension P ε fresh β` is what `lem:polygonal-overlay` has to produce from the
anchored square mesh of size `ε` (`Schoenflies.squareMesh`) and the polygonal target skeleton
of the stage `P`, given a fresh list on `S` avoiding the drawn 0-cells: a finite 2-connected
plane graph containing both, subdividing rather than crossing the old skeleton, whose new
edges reach `S` only at listed fresh points, one edge per point.

The first block is clause-for-clause `Schoenflies.IsSourceExtension P.tgt modelCurve
(Plane.closedSquare 0 1) H Hdraw` — restated because that structure fixes the edge type of `H`
to the cell-name type `γ`, while the overlay machinery names edges by `Piece`; see the module
docstring. The second block implies `Schoenflies.HasFreshAnchors P H Hdraw`
(`MeshOverlayExtension.hasFreshAnchors`) once the fresh points are known to avoid the drawn
0-cells and to have strongly accessible partners — which is how
`Schoenflies.exists_fresh_anchor_supply` chooses them, so neither fact is an obligation
here. -/
structure MeshOverlayExtension (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (β : Type*) where
  /-- The overlay graph: the anchored mesh, the old target skeleton, and a vertex at every
  point where the two meet. -/
  H : Graph Plane β
  /-- Its drawing. -/
  Hdraw : β → ℝ → Plane
  /-- The overlay is finite. -/
  finite : H.Finite
  /-- The overlay is a plane graph. -/
  isDrawing : Graph.IsDrawing H Hdraw
  /-- The overlay is 2-connected — `Schoenflies.squareMesh_isTwoConnected` transported through
  the subdivisions and unions of the overlay (`Graph.IsTwoConnected.union`,
  `Graph.IsSubdivisionOf.isTwoConnected`). -/
  isTwoConnected : H.IsTwoConnected
  /-- Every drawn 0-cell of the stage is a vertex of the overlay. -/
  vertexSet_subset : V(P.tgt.graph) ⊆ V(H)
  /-- The old drawn skeleton is part of the overlay. -/
  skeletonSet_subset : P.tgt.skeletonSet ⊆ Graph.pointSet H Hdraw
  /-- The overlay subdivides the old skeleton rather than crossing it: an overlay edge meeting
  an old open 1-cell at a point that is not an overlay vertex runs inside that 1-cell — the
  repaired `IsSourceExtension.edge_subset`, satisfied by making every mesh–skeleton
  intersection a vertex (`rem:polygonal-overlay-convention`,
  `Schoenflies.edge_subset_clause_of_inter_subset_vertexSet`). -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(P.str.skel) → ∀ ⦃f⦄, f ∈ E(H) → ∀ ⦃q⦄,
    q ∈ Graph.edgeArc Hdraw f → q ∈ P.tgt.cell e → q ∉ V(H) →
    Graph.edgeArc Hdraw f ⊆ Graph.edgeArc P.tgt.drawing e
  /-- The overlay is drawn in the closed square. -/
  pointSet_subset : Graph.pointSet H Hdraw ⊆ Plane.closedSquare 0 1
  /-- Each overlay edge is a boundary edge or a polygonal nonboundary edge with interior in
  the open square. -/
  edge_dichotomy : ∀ ⦃f⦄, f ∈ E(H) → Graph.edgeArc Hdraw f ⊆ modelCurve ∨
    (IsPolygonal (Graph.edgeArc Hdraw f) ∧
      Graph.edgeArc Hdraw f \ V(H) ⊆ Plane.closedSquare 0 1 \ modelCurve)
  /-- `|H| ∖ S` is connected — `Schoenflies.squareMesh_isConnected_diff` plus the attachment
  of every overlay component to the mesh. -/
  isConnected : IsConnected (Graph.pointSet H Hdraw \ modelCurve)
  /-- **A new nonboundary edge reaches `S` only at a listed fresh point** — the first half of
  the second sentence of `thm:finite-transfer`(b), with the anchor properties of the fresh
  points factored out. Through the overlay this is
  `Schoenflies.squareMesh_inner_edge_at_fresh`: the only edges off both `S` and the old
  skeleton that touch `S` are (pieces of) mesh spokes, and a spoke touches `S` exactly at its
  fresh point. -/
  nonboundaryAt_mem_fresh : ∀ ⦃p⦄, p ∈ modelCurve →
    NonboundaryAt H Hdraw modelCurve P.tgt.skeletonSet p → p ∈ fresh
  /-- **One new nonboundary edge per fresh boundary point** — the second half, through the
  overlay this is `Schoenflies.squareMesh_unique_inner_edge`. -/
  unique_edge : ∀ ⦃p⦄, p ∈ modelCurve → ∀ ⦃f g⦄, f ∈ E(H) → g ∈ E(H) →
    p ∈ Graph.edgeArc Hdraw f → p ∈ Graph.edgeArc Hdraw g →
    ¬ Graph.edgeArc Hdraw f ⊆ modelCurve → ¬ Graph.edgeArc Hdraw g ⊆ modelCurve →
    ¬ Graph.edgeArc Hdraw f ⊆ P.tgt.skeletonSet →
    ¬ Graph.edgeArc Hdraw g ⊆ P.tgt.skeletonSet → f = g
  /-- The overlay contains the anchored mesh of size `ε`: the overlay only ever adds vertices
  on existing segments, so the mesh cover survives into its point set. -/
  mesh_subset : cover (meshSegments (meshCount ε) fresh) ⊆ Graph.pointSet H Hdraw

namespace MeshOverlayExtension

variable {P : StagePair S₀ C} {ε : ℝ} {fresh : List Plane}

/-- At edge type `γ`, the first block of the bundle is literally
`Schoenflies.IsSourceExtension` for the two square-side regions. -/
theorem isSourceExtension (M : MeshOverlayExtension P ε fresh γ) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1) M.H M.Hdraw where
  finite := M.finite
  isDrawing := M.isDrawing
  isTwoConnected := M.isTwoConnected
  vertexSet_subset := M.vertexSet_subset
  skeletonSet_subset := M.skeletonSet_subset
  edge_subset := M.edge_subset
  pointSet_subset := M.pointSet_subset
  edge_dichotomy := M.edge_dichotomy
  isConnected := M.isConnected

/-- At edge type `γ`, the second block of the bundle together with the properties of the
chosen fresh points is `Schoenflies.HasFreshAnchors`: a point reached by a new nonboundary
edge is a listed fresh point, and the listed fresh points avoid the drawn 0-cells and have
strongly accessible partners. -/
theorem hasFreshAnchors (M : MeshOverlayExtension P ε fresh γ) (hsep : IsSeparating C)
    (hfresh : ∀ z ∈ fresh, z ∉ V(P.tgt.graph) ∧
      StronglyAccessible (inside C) (P.homeo.invFun z)) :
    HasFreshAnchors P M.H M.Hdraw where
  unique_edge := M.unique_edge
  notMem_vertexSet := fun p hp hnb =>
    (hfresh p (M.nonboundaryAt_mem_fresh hp hnb)).1
  stronglyAccessible := fun p hp hnb => by
    rw [sdiff_outer_eq_inside hsep]
    exact (hfresh p (M.nonboundaryAt_mem_fresh hp hnb)).2

/-- **The bundle transports across an edge renaming.** An overlay extension over any
edge-name type yields one over `γ`: `Graph.exists_injOn_notMem` supplies fresh injective
`γ`-names for the finitely many overlay edges, and `Graph.renameEdges` preserves everything
the clauses read — vertex set, adjacency, each edge's arc, the occupied point set. This is
the `Piece`-to-`γ` rebuild of the module docstring. -/
theorem rename [Infinite γ] {β : Type*} [Nonempty β]
    (M : MeshOverlayExtension P ε fresh β) : Nonempty (MeshOverlayExtension P ε fresh γ) := by
  classical
  haveI := M.finite
  obtain ⟨σ, hσ, -⟩ := Graph.exists_injOn_notMem (Graph.finite_edgeSet M.H)
    (Set.finite_empty (α := γ))
  have hpt : Graph.pointSet (M.H.renameEdges σ hσ) (Graph.renameDrawing M.H σ M.Hdraw)
      = Graph.pointSet M.H M.Hdraw := Graph.pointSet_renameEdges hσ
  -- the two directions of the `NonboundaryAt` correspondence
  have hnbdown : ∀ ⦃p : Plane⦄,
      NonboundaryAt (M.H.renameEdges σ hσ) (Graph.renameDrawing M.H σ M.Hdraw)
        modelCurve P.tgt.skeletonSet p →
      NonboundaryAt M.H M.Hdraw modelCurve P.tgt.skeletonSet p := by
    rintro p ⟨f, hf, hp, hnb, hnew⟩
    obtain ⟨f₀, hf₀, rfl, harc⟩ := Graph.exists_rep_of_mem_renameEdges (d := M.Hdraw) hσ hf
    rw [harc] at hp hnb hnew
    exact ⟨f₀, hf₀, hp, hnb, hnew⟩
  refine ⟨⟨M.H.renameEdges σ hσ, Graph.renameDrawing M.H σ M.Hdraw,
    Graph.renameEdges_finite, M.isDrawing.renameEdges hσ,
    M.isTwoConnected.renameEdges hσ, M.vertexSet_subset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hpt]; exact M.skeletonSet_subset
  · -- `edge_subset`
    intro e he f hf q hq hcell hqV
    obtain ⟨f₀, hf₀, rfl, harc⟩ := Graph.exists_rep_of_mem_renameEdges (d := M.Hdraw) hσ hf
    rw [harc] at hq ⊢
    exact M.edge_subset he hf₀ hq hcell hqV
  · rw [hpt]; exact M.pointSet_subset
  · -- `edge_dichotomy`
    intro f hf
    obtain ⟨f₀, hf₀, rfl, harc⟩ := Graph.exists_rep_of_mem_renameEdges (d := M.Hdraw) hσ hf
    rw [harc]
    exact M.edge_dichotomy hf₀
  · rw [hpt]; exact M.isConnected
  · -- `nonboundaryAt_mem_fresh`
    intro p hp hnb
    exact M.nonboundaryAt_mem_fresh hp (hnbdown hnb)
  · -- `unique_edge`
    intro p hp f g hf hg hpf hpg hnbf hnbg hnewf hnewg
    obtain ⟨f₀, hf₀, rfl, harcf⟩ := Graph.exists_rep_of_mem_renameEdges (d := M.Hdraw) hσ hf
    obtain ⟨g₀, hg₀, rfl, harcg⟩ := Graph.exists_rep_of_mem_renameEdges (d := M.Hdraw) hσ hg
    rw [harcf] at hpf hnbf hnewf
    rw [harcg] at hpg hnbg hnewg
    exact congrArg σ (M.unique_edge hp hf₀ hg₀ hpf hpg hnbf hnbg hnewf hnewg)
  · rw [hpt]; exact M.mesh_subset

end MeshOverlayExtension

/-- **One overlay extension is one mesh transfer.** The extension is fed to the repaired
`thm:finite-transfer`(b) (`Schoenflies.finite_transfer_back'`) with the four ambient facts of
the two regions, and the conclusion is exactly the bundle `Schoenflies.MeshTransfer` records;
the `ε`-density of the fresh list arrives by monotonicity from whatever finer density they
were chosen with. -/
theorem meshTransfer_of_extension [Infinite γ] (h₀ : S₀.CombInvariants)
    (hsep : IsSeparating C) {P : StagePair S₀ C} {ε : ℝ} {fresh : List Plane}
    (hdense : FreshDense fresh ε)
    (hfresh : ∀ z ∈ fresh, z ∉ V(P.tgt.graph) ∧
      StronglyAccessible (inside C) (P.homeo.invFun z))
    (M : MeshOverlayExtension P ε fresh γ) : Nonempty (MeshTransfer P ε) := by
  obtain ⟨T, par, hT⟩ := finite_transfer_back' h₀ M.isSourceExtension
    (M.hasFreshAnchors hsep hfresh)
    (isOpen_sdiff_outer_of_isSeparating hsep) (frontier_sdiff_outer_of_isSeparating hsep)
    isOpen_closedSquare_sdiff_modelCurve frontier_closedSquare_sdiff_modelCurve
  exact ⟨⟨fresh, hdense, M.H, M.Hdraw, T, par, hT, M.mesh_subset⟩⟩

/-- **NAMED HYPOTHESIS — the polygonal overlay of the anchored mesh with the target
skeleton.** At every admissible stage and mesh size there is a finite bad set (the overlay's
own degeneracies — in the intended discharger it is empty or a set of mesh vertices on `S`)
such that *every* fresh list on `S` avoiding the drawn 0-cells and the bad set, with at least
two points, extends to a `Schoenflies.MeshOverlayExtension` over the overlay machinery's own
edge names.

Its discharger is `lem:polygonal-overlay` run on `squareMesh ε fresh anchors` and the drawn
target skeleton (polygonal by `GeneratedPair.tgt_isPolygonal`): subdivide every mesh edge and
every old 1-cell at their meeting points — in the *base pair first* where an old 1-cell gains
interior vertices (`GeneratedPair.exists_subdivide_finite_tgt`) — take the union, and read
the clauses off `prop:anchored-square-mesh` (clauses 3–5 are `squareMesh_inner_edge_at_fresh`,
`squareMesh_unique_inner_edge`, `squareMesh_isConnected_diff`) and the 2-connectivity toolkit
(`squareMesh_isTwoConnected` via `exists_two_distinct_fresh_of_freshDense`,
`Graph.IsTwoConnected.union`). The quantification over `fresh` is an input, not an
obligation: the fresh points' density, avoidance and accessibility are supplied by
`Schoenflies.exists_fresh_anchor_supply` at the call site (`Schoenflies.hasMeshTransfers`). -/
def HasMeshOverlays (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ bad : Set Plane, bad.Finite ∧
        ∀ ⦃fresh : List Plane⦄,
          (∀ z ∈ fresh, z ∈ modelCurve ∧ z ∉ V(P.tgt.graph) ∧ z ∉ bad ∧
            StronglyAccessible (inside C) (P.homeo.invFun z)) →
          (∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w) →
          Nonempty (MeshOverlayExtension P ε fresh Piece)

/-- **The discharge of the mesh-transfer chooser from the overlay.** The fresh points are
chosen by `Schoenflies.exists_fresh_anchor_supply` at density `min ε 3` — positive, at most
`ε` (so `FreshDense.mono` recovers the `ε`-density the transfer bundle records) and below `4`
(so `Schoenflies.exists_two_distinct_fresh_of_freshDense` gives the two distinct fresh points
the overlay's 2-connectivity needs) — avoiding the finitely many drawn 0-cells of the stage
and the overlay's bad set; the overlay hypothesis turns them into an extension, and
`Schoenflies.meshTransfer_of_extension` runs the transfer. -/
theorem hasMeshTransfers [Infinite γ] (h₀ : S₀.CombInvariants) (hsep : IsSeparating C)
    (hov : HasMeshOverlays S₀ C) : HasMeshTransfers S₀ C := by
  intro P hsrc htgt ε hε
  obtain ⟨bad, hbad, hext⟩ := hov P hsrc htgt hε
  -- the fresh points, `min ε 3`-dense and off both finite avoid sets
  have hδ : (0 : ℝ) < min ε 3 := lt_min hε (by norm_num)
  have hV : (V(P.tgt.graph) ∪ bad).Finite :=
    (Graph.finite_vertexSet P.tgt.graph).union hbad
  obtain ⟨fresh, hdense, hfresh⟩ :=
    exists_fresh_anchor_supply hsep (anchorSet hsep.isJordanCurve) P hδ hV
  have hfresh' : ∀ z ∈ fresh, z ∈ modelCurve ∧ z ∉ V(P.tgt.graph) ∧ z ∉ bad ∧
      StronglyAccessible (inside C) (P.homeo.invFun z) := by
    intro z hz
    obtain ⟨hzS, hzV, hzA⟩ := hfresh z hz
    exact ⟨hzS, fun h => hzV (Or.inl h), fun h => hzV (Or.inr h), hzA⟩
  obtain ⟨M⟩ := hext hfresh'
    (exists_two_distinct_fresh_of_freshDense hdense
      (lt_of_le_of_lt (min_le_right ε 3) (by norm_num)))
  obtain ⟨M'⟩ := M.rename (γ := γ)
  exact meshTransfer_of_extension h₀ hsep (hdense.mono (min_le_left ε 3))
    (fun z hz => ⟨(hfresh' z hz).2.1, (hfresh' z hz).2.2.2⟩) M'

/-! ### The interface, exercised

Over the concrete base, the Phase 3 deliverable now rests on the source-grid chooser and the
polygonal overlay of the anchored mesh — the transfer, the fresh points and the edge renaming
are no longer obligations. -/

example {C : Set Plane} (hC : IsJordanCurve C) (hg : HasGridSteps initialStructure C)
    (hov : HasMeshOverlays initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC hg
    (hasMeshSteps (hasMeshTransfers combInvariants_initialStructure
      (jordan_curve_theorem hC) hov))⟩

end Schoenflies
