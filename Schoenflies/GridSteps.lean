/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.GridStarEstimate
import Schoenflies.GridComponents
import Schoenflies.MeshSteps

/-!
# The direction-(a) grid step, assembled — the `Schoenflies.HasGridSteps` discharger

`Schoenflies.HasGridSteps` (`StageRecursion.lean`) is the source-grid chooser of the stage
recursion: at every admissible stage `P`, mesh `ε > 0` and window centre `b ∈ inside C`, a
`Schoenflies.GridStepData P ε b`. Its intended discharger is `prop:local-grid-attachment`
building an extension `H` of the source skeleton over the window `W(b)`, then
`thm:finite-transfer`(a) (`Schoenflies.finite_transfer_toward_square'`, unconditional) to
transfer it, then `lem:grid-star-estimate` (`Schoenflies.StagePair.diam_star_le_of_grid`, done)
for the star bound. This module assembles that pipeline end to end.

## The cut, and what remains

The pipeline is cut at the *hypotheses* of the transfer: `Schoenflies.GridExtensionData` is the
proposed extension `H` together with `Schoenflies.IsSourceExtension` — the hypotheses of
`thm:finite-transfer`(a), verbatim — and the one clause about how `H` was made, namely that its
drawn point set contains the local grid cover on `W(b)`. Everything downstream of that bundle is
*proved* here: `Schoenflies.hasGridSteps` invokes the transfer with the four ambient-domain
facts, reads the step relation off the conclusion by
`Schoenflies.IsTransferOf.isRefinementStep`, and lands the star bound by feeding the transfer's
`skeletonSet_eq` into `Schoenflies.StagePair.diam_star_le_of_grid`.

What remains — the one named hypothesis `Schoenflies.HasGridExtensions` — is the *construction*
of the extension, `prop:local-grid-attachment` applied at the stage. Its discharger builds the
graph from the pieces already on `main`, over any convenient edge-name type, and pushes it into
`γ` by the relabelling below; see the docstring of `Schoenflies.HasGridExtensions` for the
itemized obligations (`hΓ`, `MeetsFinitely`, the union with the outer part of `Γ`, and the
window placement).

## The edge relabelling

`Schoenflies.gridAttachGraph` names its edges by `Piece = Plane × Plane` while the transfer
fixes `H : Graph Plane γ`; this repo deliberately has no edge relabelling (`Graph.map` relabels
vertices only — see the note on `InitialCell.aux` in `InitialGenerated.lean`). The rebuild
recorded as Phase 3's renaming debt is `Graph.relabel` below: the same graph presented under an
injection of edge names, with drawing `Graph.relabelDraw`. Everything the transfer's hypotheses
read — finiteness, the drawing, 2-connectivity, the vertex set, every edge arc, the point set —
is preserved, so `Schoenflies.IsSourceExtensionOver` (the transfer's hypotheses over an
*arbitrary* edge-name type) transports to `Schoenflies.IsSourceExtension` over `γ`
(`Schoenflies.IsSourceExtensionOver.relabel`), and
`Schoenflies.nonempty_gridExtensionData_of_over` closes the renaming debt: the discharger of
`HasGridExtensions` may build over `Piece`, or over `γ ⊕ Piece`, or over any nonempty edge type
at all, and the injection into the infinite `γ` is chosen here.

## Blueprint

* `Graph.relabel`, `Graph.relabelDraw` — not a numbered statement; the edge renaming that
  Phase 3 item 0 of `docs/ROADMAP.md` records as the composition obligation of
  `lem:grid-star-estimate`'s `hgrid`.
* `Schoenflies.IsSourceExtensionOver`, `Schoenflies.IsSourceExtensionOver.relabel` — the
  hypotheses of `thm:finite-transfer`(a) on `H`, freed of the edge-name type, and their
  transport into the shape the transfer consumes.
* `Schoenflies.GridExtensionData`, `Schoenflies.HasGridExtensions` — `prop:local-grid-attachment`
  applied at a stage, as one named hypothesis: the extension over the window, satisfying the
  transfer's hypotheses, containing the grid.
* `Schoenflies.GridExtensionData.nonempty_gridStepData`, `Schoenflies.hasGridSteps` — the
  discharge of `Schoenflies.HasGridSteps` from it: `thm:finite-transfer`(a) +
  `lem:grid-star-estimate`, with nothing else assumed.
-/

open Metric Set Schoenflies
open scoped Graph

/-! ## Relabelling the edges of a graph

`Graph.map` relabels vertices and keeps edge names; nothing in Mathlib or in this repo renames
edges. `Graph.relabel` is that missing operation, for an injection of the edge set: the same
vertices, the same links, each edge `e` now called `f e`. It is general graph theory and
belongs beside `Graph.map`; it is here because it was needed here first. -/

namespace Graph

variable {α β β' : Type*} {G : Graph α β} {f : β → β'}

/-- **The graph `G` with each edge `e` renamed `f e`**, for `f` injective on the edge set.
Injectivity is what keeps distinct edges distinct, so the relabelled graph has the same links
with the same multiplicities. -/
def relabel (G : Graph α β) (f : β → β') (hf : Set.InjOn f E(G)) : Graph α β' where
  vertexSet := V(G)
  IsLink e' x y := ∃ e ∈ E(G), f e = e' ∧ G.IsLink e x y
  edgeSet := f '' E(G)
  isLink_symm := fun _ _ => ⟨fun _ _ ⟨e, he, hfe, hl⟩ => ⟨e, he, hfe, hl.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e' x y v w ⟨e, he, rfl, hl⟩ ⟨e₂, he₂, hfe, hl₂⟩
    obtain rfl := hf he₂ he hfe
    exact hl.left_eq_or_eq hl₂
  edge_mem_iff_exists_isLink := by
    rintro e'
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, e, he, rfl, hl⟩
    · rintro ⟨x, y, e, he, rfl, -⟩
      exact ⟨e, he, rfl⟩
  left_mem_of_isLink := by
    rintro e' x y ⟨e, -, -, hl⟩
    exact hl.left_mem

variable {hf : Set.InjOn f E(G)}

@[simp] theorem relabel_vertexSet : V(G.relabel f hf) = V(G) := rfl

@[simp] theorem relabel_edgeSet : E(G.relabel f hf) = f '' E(G) := rfl

theorem relabel_isLink {e' : β'} {x y : α} :
    (G.relabel f hf).IsLink e' x y ↔ ∃ e ∈ E(G), f e = e' ∧ G.IsLink e x y := Iff.rfl

/-- On an edge of `G`, the relabelled link is the old link. -/
theorem relabel_isLink_image {e : β} (he : e ∈ E(G)) {x y : α} :
    (G.relabel f hf).IsLink (f e) x y ↔ G.IsLink e x y := by
  constructor
  · rintro ⟨e₂, he₂, hfe, hl⟩
    obtain rfl := hf he₂ he hfe
    exact hl
  · exact fun hl => ⟨e, he, rfl, hl⟩

/-- Relabelling edges does not change which pairs of vertices are joined. -/
theorem relabel_adj {x y : α} : (G.relabel f hf).Adj x y ↔ G.Adj x y := by
  constructor
  · rintro ⟨e', e, he, rfl, hl⟩
    exact ⟨e, hl⟩
  · rintro ⟨e, hl⟩
    exact ⟨f e, e, hl.edge_mem, rfl, hl⟩

theorem relabel_inc_image {e : β} (he : e ∈ E(G)) {x : α} :
    (G.relabel f hf).Inc (f e) x ↔ G.Inc e x := by
  constructor
  · rintro ⟨y, hl⟩
    exact ⟨y, (relabel_isLink_image he).1 hl⟩
  · rintro ⟨y, hl⟩
    exact ⟨y, (relabel_isLink_image he).2 hl⟩

theorem relabel_finite [G.Finite] : (G.relabel f hf).Finite where
  finite_vertexSet := Graph.finite_vertexSet G
  finite_edgeSet := (Graph.finite_edgeSet G).image f

/-- **2-connectivity survives an edge relabelling** — it only sees adjacency
(`Graph.IsTwoConnected.of_adj_congr`). -/
theorem IsTwoConnected.relabel (h : G.IsTwoConnected) : (G.relabel f hf).IsTwoConnected :=
  h.of_adj_congr relabel_vertexSet.symm fun _ _ => relabel_adj.symm

/-! ### The relabelled drawing -/

variable [Nonempty β] {d : β → ℝ → Plane}

/-- The drawing of a relabelled plane graph: each new name `f e` is drawn by the old drawing of
`e`, recovered by a partial inverse of `f` on the edge set. Off the image the value is junk and
is never read — every clause of `Graph.IsDrawing` quantifies over edges of the graph. -/
noncomputable def relabelDraw (f : β → β') (s : Set β) (d : β → ℝ → Plane) :
    β' → ℝ → Plane :=
  fun e' => d (Function.invFunOn f s e')

theorem relabelDraw_image {G : Graph Plane β} {f : β → β'} (hf : Set.InjOn f E(G)) {e : β}
    (he : e ∈ E(G)) {d : β → ℝ → Plane} : relabelDraw f E(G) d (f e) = d e := by
  rw [relabelDraw, hf.leftInvOn_invFunOn he]

theorem relabel_edgeArc {G : Graph Plane β} {f : β → β'} (hf : Set.InjOn f E(G)) {e : β}
    (he : e ∈ E(G)) {d : β → ℝ → Plane} :
    edgeArc (relabelDraw f E(G) d) (f e) = edgeArc d e := by
  rw [edgeArc, edgeArc, relabelDraw_image hf he]

/-- Relabelling the edges does not move the drawn point set. -/
theorem relabel_pointSet {G : Graph Plane β} {f : β → β'} (hf : Set.InjOn f E(G))
    {d : β → ℝ → Plane} :
    pointSet (G.relabel f hf) (relabelDraw f E(G) d) = pointSet G d := by
  rw [pointSet, pointSet, relabel_vertexSet, relabel_edgeSet, Set.biUnion_image]
  exact congrArg _ (Set.iUnion₂_congr fun e he => relabel_edgeArc hf he)

/-- **A drawing survives an edge relabelling.** Every clause is the old clause read through the
bijection `e ↦ f e` of edge names, under which the arcs are unchanged. -/
theorem IsDrawing.relabel {G : Graph Plane β} {f : β → β'} {hf : Set.InjOn f E(G)}
    {d : β → ℝ → Plane} (hd : IsDrawing G d) :
    IsDrawing (G.relabel f hf) (relabelDraw f E(G) d) where
  edge_param := by
    rintro e' ⟨e, he, rfl⟩
    obtain ⟨hcont, hinj, hl⟩ := hd.edge_param he
    rw [relabelDraw_image hf he]
    exact ⟨hcont, hinj, (relabel_isLink_image he).2 hl⟩
  vertex_mem_edgeArc := by
    rintro e' x y v ⟨e, he, rfl, hl⟩ hv hvarc
    rw [relabel_edgeArc hf he] at hvarc
    exact hd.vertex_mem_edgeArc hl hv hvarc
  edge_inter := by
    rintro e' g' he' hg' hne p hpe hpg
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨g, hg, rfl⟩ := hg'
    have hneg : e ≠ g := fun h => hne (congrArg f h)
    rw [relabel_edgeArc hf he] at hpe
    rw [relabel_edgeArc hf hg] at hpg
    obtain ⟨hpV, hince, hincg⟩ := hd.edge_inter he hg hneg hpe hpg
    exact ⟨hpV, (relabel_inc_image he).2 hince, (relabel_inc_image hg).2 hincg⟩

end Graph

namespace Schoenflies

open Graph CellStructure

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}

/-! ## A supply of names

The relabelling needs an injection of the finite edge set into `γ`; `Infinite γ` supplies one.
This is general set theory and is here only because it was needed here first. -/

/-- A finite set of any type injects into any infinite type. -/
theorem exists_injOn_of_finite {β δ : Type*} [Infinite δ] {s : Set β} (hs : s.Finite) :
    ∃ f : β → δ, Set.InjOn f s := by
  classical
  haveI := hs.fintype
  have hemb : Nonempty (s ↪ δ) :=
    ⟨(Fintype.equivFin s).toEmbedding.trans
      ((Fin.valEmbedding).trans (Infinite.natEmbedding δ))⟩
  obtain ⟨g⟩ := hemb
  refine ⟨fun b => if h : b ∈ s then g ⟨b, h⟩ else Classical.arbitrary δ, ?_⟩
  intro a ha b hb hab
  dsimp only at hab
  rw [dif_pos ha, dif_pos hb] at hab
  exact congrArg Subtype.val (g.injective hab)

/-! ## The transfer's hypotheses, freed of the edge-name type

`Schoenflies.IsSourceExtension` (`FiniteTransfer.lean`) states the hypotheses of
`thm:finite-transfer`(a) for `H : Graph Plane γ` — the edge names drawn from the one cell-name
type. The construction of the extension is more comfortable over a concrete name type (the
grid overlay uses `Piece`; the union with the outer part of `Γ` may want `γ ⊕ Piece`), and no
clause of the hypotheses reads a name: this is the same statement over an arbitrary edge type,
together with the transport into the `γ`-shape along `Graph.relabel`. -/

/-- **The hypotheses of `thm:finite-transfer`(a) on the extension, over an arbitrary edge-name
type.** Field for field `Schoenflies.IsSourceExtension`, with the graph's edge names drawn from
any type `β`; `Schoenflies.IsSourceExtensionOver.relabel` converts to the `γ`-named form the
transfer consumes. -/
structure IsSourceExtensionOver {β : Type*} {S : CellStructure γ} (R : S.Realization)
    (outer dom : Set Plane) (G : Graph Plane β) (d : β → ℝ → Plane) : Prop where
  /-- `H` is finite. -/
  finite : G.Finite
  /-- `H` is a plane graph. -/
  isDrawing : Graph.IsDrawing G d
  /-- `H` is 2-connected. -/
  isTwoConnected : G.IsTwoConnected
  /-- Every 0-cell of `Γ` is a vertex of `H`. -/
  vertexSet_subset : V(R.graph) ⊆ V(G)
  /-- `|Γ| ⊆ |H|`. -/
  skeletonSet_subset : R.skeletonSet ⊆ Graph.pointSet G d
  /-- An edge of `H` meeting an open edge of `Γ` at a point that is not a vertex of `H` runs
  inside it — the repaired subdivision clause; see `Schoenflies.IsSourceExtension.edge_subset`
  for why the trigger exempts vertices of `H`. -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → ∀ ⦃P⦄, P ∈ E(G) → ∀ ⦃q⦄, q ∈ Graph.edgeArc d P →
    q ∈ R.cell e → q ∉ V(G) → Graph.edgeArc d P ⊆ Graph.edgeArc R.drawing e
  /-- `H` is drawn in the closed domain. -/
  pointSet_subset : Graph.pointSet G d ⊆ dom
  /-- Each edge of `H` is an outer edge or a polygonal nonboundary edge with interior in the
  open domain. -/
  edge_dichotomy : ∀ ⦃P⦄, P ∈ E(G) → Graph.edgeArc d P ⊆ outer ∨
    (IsPolygonal (Graph.edgeArc d P) ∧ Graph.edgeArc d P \ V(G) ⊆ dom \ outer)
  /-- `|H| ∖ C` is connected. -/
  isConnected : IsConnected (Graph.pointSet G d \ outer)

omit [Nonempty γ] in
/-- **The transport into the transfer's shape.** The relabelled graph satisfies
`Schoenflies.IsSourceExtension`: every clause of the hypotheses reads the graph through its
vertex set, its adjacency, or its edge arcs, all of which `Graph.relabel` preserves. -/
theorem IsSourceExtensionOver.relabel {β : Type*} [Nonempty β] {S : CellStructure γ}
    {R : S.Realization} {outer dom : Set Plane} {G : Graph Plane β} {d : β → ℝ → Plane}
    (h : IsSourceExtensionOver R outer dom G d) {f : β → γ} (hf : Set.InjOn f E(G)) :
    IsSourceExtension R outer dom (G.relabel f hf) (Graph.relabelDraw f E(G) d) := by
  haveI := h.finite
  refine ⟨Graph.relabel_finite, h.isDrawing.relabel, h.isTwoConnected.relabel,
    h.vertexSet_subset, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Graph.relabel_pointSet hf]
    exact h.skeletonSet_subset
  · rintro e he f' ⟨P, hP, rfl⟩ q hq hqcell hqV
    rw [Graph.relabel_edgeArc hf hP] at hq ⊢
    exact h.edge_subset he hP hq hqcell hqV
  · rw [Graph.relabel_pointSet hf]
    exact h.pointSet_subset
  · rintro f' ⟨P, hP, rfl⟩
    rw [Graph.relabel_edgeArc hf hP]
    exact h.edge_dichotomy hP
  · rw [Graph.relabel_pointSet hf]
    exact h.isConnected

/-! ## The named hypothesis: the extension exists

The bundle `prop:local-grid-attachment` must deliver at a stage, cut at the hypotheses of
`thm:finite-transfer`(a). Everything from here to `Schoenflies.HasGridSteps` is proved below. -/

/-- **The proposed extension at stage `P`, window centre `b`, mesh `ε`** — the input to
`thm:finite-transfer`(a), plus the one clause recording how it was built: the drawn point set
contains the local grid cover on the window `W(b)`.

Its supplier is `prop:local-grid-attachment` (`GridAttach.lean` / `GridComponents.lean` /
`LocalGrid.lean`), whose remaining obligations are itemized on
`Schoenflies.HasGridExtensions`. -/
structure GridExtensionData (P : StagePair S₀ C) (ε : ℝ) (b : Plane) where
  /-- The extension graph, named over the cell-name type as the transfer requires. Builders
  working over another edge type reach this shape through
  `Schoenflies.nonempty_gridExtensionData_of_over`. -/
  H : Graph Plane γ
  /-- Its drawing. -/
  Hdraw : γ → ℝ → Plane
  /-- The hypotheses of `thm:finite-transfer`(a): finite, plane, 2-connected, containing a
  subdivision of `Γ`, outer cycle `C`, polygonal nonboundary edges, `|H| ∖ C` connected. -/
  ext : IsSourceExtension P.src C (C ∪ inside C) H Hdraw
  /-- The extension contains the local grid on `W(b)` — clause 2 of
  `prop:local-grid-attachment`, which is what `lem:grid-star-estimate` reads after the
  transfer's `skeletonSet_eq`. -/
  grid_subset : cover (localGridEdges b (windowRadius C ε b)
    (localGridCount (windowRadius C ε b) ε)) ⊆ Graph.pointSet H Hdraw

omit [Nonempty γ] in
/-- **The reduction of the renaming debt.** An extension built over *any* nonempty edge-name
type — `Piece` for the grid overlay, `γ ⊕ Piece` for a union with the current graph, anything —
yields a `Schoenflies.GridExtensionData`: `Infinite γ` supplies an injection of the finite edge
set into `γ`, and `Graph.relabel` transports every hypothesis. -/
theorem nonempty_gridExtensionData_of_over [Infinite γ] {β : Type*} [Nonempty β]
    {P : StagePair S₀ C} {ε : ℝ} {b : Plane} {G : Graph Plane β} {d : β → ℝ → Plane}
    (hext : IsSourceExtensionOver P.src C (C ∪ inside C) G d)
    (hgrid : cover (localGridEdges b (windowRadius C ε b)
      (localGridCount (windowRadius C ε b) ε)) ⊆ Graph.pointSet G d) :
    Nonempty (GridExtensionData P ε b) := by
  haveI := hext.finite
  obtain ⟨f, hf⟩ := exists_injOn_of_finite (δ := γ) (Graph.finite_edgeSet G)
  refine ⟨⟨G.relabel f hf, Graph.relabelDraw f E(G) d, hext.relabel hf, ?_⟩⟩
  rw [Graph.relabel_pointSet hf]
  exact hgrid

/-- **NAMED HYPOTHESIS — the extension chooser, `prop:local-grid-attachment` at a stage.**

At every admissible stage, mesh `ε > 0` and window centre `b ∈ inside C`, an extension of the
source skeleton satisfying the hypotheses of `thm:finite-transfer`(a) and containing the local
grid on `W(b)`.

Discharged by `prop:local-grid-attachment` assembled at the stage — build over any edge type
and finish with `Schoenflies.nonempty_gridExtensionData_of_over`. The pieces, all on `main`
except the four listed obligations:

* the graph and its clauses — `Schoenflies.gridAttachGraph` (`GridAttach.lean`): the drawing
  (`gridAttachGraph_isDrawing`), the grid containment (`localGrid_subset_gridAttachGraph`,
  which is `grid_subset` up to the relabelling), 2-connectivity
  (`gridAttachGraph_isTwoConnected`) and connectedness of the open nonboundary part
  (`gridAttachGraph_isConnected_diff_of_meetsFinitely`, `GridComponents.lean`);
* **obligation 1, `hΓ`** of `gridAttachGraph_isTwoConnected`: 2-connectivity of `Γ` with the
  case's crosscut and the joining arcs appended and everything subdivided at the crossings,
  from the stage's `IsWeaklyAdmissible.isTwoConnected` via
  `pieceListGraph_subdivide_isTwoConnected`, `Graph.IsTwoConnected.replace_edge_by_path`,
  `Graph.IsTwoConnected.ear` and `pieceListGraph_append_crosscut`;
* **obligation 2, `MeetsFinitely gsegs C`** (`GridComponents.lean`): each drawn nonboundary
  piece meets `C` finitely, from the stage's drawing invariants (nonboundary edges are
  polygonal with interiors in the open domain);
* **obligation 3, the union with the outer part of `Γ`**: `IsSourceExtension` demands
  `|Γ| ⊆ |H|` and `V(Γ) ⊆ V(H)`, and `|Γ|` contains the wild curve `C`, which no family of
  segments covers — so the extension is `gridAttachGraph` (the polygonal part: the subdivided
  nonboundary skeleton, crosscut, joining arcs, grid) *unioned with the outer part of the
  stage's own graph*, drawn by the stage's drawing; the union's `edge_subset` and
  `edge_dichotomy` clauses split along that decomposition;
* **obligation 4, the window placement**: the grid lies in `W(b) ⊆ inside C`
  (`Schoenflies.window_subset_inside`) hence misses `C`, the joining arcs live in the open
  domain (`Schoenflies.exists_simple_poly_of_isPreconnected` aimed at the representatives of
  `Schoenflies.exists_reps_hcov`), and the crosscut's ends lie on the graph
  (`Schoenflies.exists_crosscut`, `frontier_face_subset_pointSet`). -/
def HasGridExtensions (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃b : Plane⦄, b ∈ inside C → Nonempty (GridExtensionData P ε b)

/-! ## The discharge -/

/-- **One extension is one grid step.** `thm:finite-transfer`(a)
(`Schoenflies.finite_transfer_toward_square'`, unconditional) transfers the extension, with the
four ambient-domain facts supplied by `thm:jordan` on the source side and the model-square
lemmas on the target side; the step relation is read off the conclusion by
`Schoenflies.IsTransferOf.isRefinementStep`, and the star bound is `lem:grid-star-estimate`
(`Schoenflies.StagePair.diam_star_le_of_grid`) fed the transferred skeleton through the
conclusion's `skeletonSet_eq`. -/
theorem GridExtensionData.nonempty_gridStepData [Infinite γ] (h₀ : S₀.CombInvariants)
    (hsep : IsSeparating C) {P : StagePair S₀ C} {ε : ℝ} (hε : 0 < ε) {b : Plane}
    (hb : b ∈ inside C) (E : GridExtensionData P ε b) : Nonempty (GridStepData P ε b) := by
  obtain ⟨T, par, hT⟩ := finite_transfer_toward_square' h₀ E.ext
    (isOpen_sdiff_outer_of_isSeparating hsep) (frontier_sdiff_outer_of_isSeparating hsep)
    isOpen_closedSquare_sdiff_modelCurve frontier_closedSquare_sdiff_modelCurve
  refine ⟨⟨T, par, hT.isRefinementStep, ?_⟩⟩
  refine StagePair.diam_star_le_of_grid h₀ hsep T hε hb ?_
  rw [hT.skeletonSet_eq]
  exact E.grid_subset

/-- **The discharge of the source-grid chooser.** Given one extension per admissible stage,
mesh and window centre, `Schoenflies.HasGridSteps` holds — the transfer, the step relation and
the star estimate are all proved, not assumed. -/
theorem hasGridSteps [Infinite γ] (h₀ : S₀.CombInvariants) (hsep : IsSeparating C)
    (hE : HasGridExtensions S₀ C) : HasGridSteps S₀ C :=
  fun P hsrc htgt _ε hε _b hb =>
    (hE P hsrc htgt hε hb).elim fun E => E.nonempty_gridStepData h₀ hsep hε hb

/-! ## The window placement

The quantitative half of obligation 4 of the extension chooser: the local grid on the window
`W(b)` lies inside the closed window, hence inside the open Jordan domain, hence misses `C`.
The disjointness is stated in the exact shape `Schoenflies.exists_reps_hcov` consumes, and
`Schoenflies.MeetsFinitely.of_disjoint` turns it into the grid's joining-loop input. -/

section WindowPlacement

variable {p b : Plane} {s ε : ℝ} {k : ℕ}

/-- A grid coordinate stays within `s` of the centre's coordinate. -/
theorem abs_localGridX_sub_le (hs : 0 < s) (hk : 1 ≤ k) {i : ℕ} (hi : i ≤ k) :
    |localGridX p s k i - p 0| ≤ s := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  have h1 : (0 : ℝ) ≤ i * (2 * s / k) := by positivity
  have h2 : (i : ℝ) * (2 * s / k) ≤ 2 * s := by
    calc (i : ℝ) * (2 * s / k) ≤ k * (2 * s / k) :=
          mul_le_mul_of_nonneg_right hik (by positivity)
      _ = 2 * s := by field_simp
  rw [localGridX, uniformCoord, abs_le]
  constructor <;> nlinarith

/-- A grid coordinate stays within `s` of the centre's coordinate. -/
theorem abs_localGridY_sub_le (hs : 0 < s) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ k) :
    |localGridY p s k j - p 1| ≤ s := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
  have h1 : (0 : ℝ) ≤ j * (2 * s / k) := by positivity
  have h2 : (j : ℝ) * (2 * s / k) ≤ 2 * s := by
    calc (j : ℝ) * (2 * s / k) ≤ k * (2 * s / k) :=
          mul_le_mul_of_nonneg_right hjk (by positivity)
      _ = 2 * s := by field_simp
  rw [localGridY, uniformCoord, abs_le]
  constructor <;> nlinarith

/-- Every vertex of the local grid lies in the closed window. -/
theorem gridPt_mem_closedSquare (hs : 0 < s) (hk : 1 ≤ k) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    gridPt (localGridX p s k) (localGridY p s k) i j ∈ Plane.closedSquare p s := by
  change Plane.supDist _ p ≤ s
  rw [Plane.supDist, Plane.supNorm]
  refine max_le ?_ ?_
  · simpa [gridPt, Plane.sub_apply] using abs_localGridX_sub_le (p := p) hs hk hi
  · simpa [gridPt, Plane.sub_apply] using abs_localGridY_sub_le (p := p) hs hk hj

/-- **The local grid lies in the closed window**: each edge is a segment between two grid
vertices, and the window is convex. -/
theorem cover_localGridEdges_subset (hs : 0 < s) (hk : 1 ≤ k) :
    cover (localGridEdges p s k) ⊆ Plane.closedSquare p s := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  rw [localGridEdges] at hP
  rcases (mem_gridEdges_iff hk hk).1 hP with ⟨i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · exact (Plane.convex_closedSquare p s).segment_subset
      (gridPt_mem_closedSquare hs hk (by omega) hj)
      (gridPt_mem_closedSquare hs hk (by omega) hj) hxP
  · exact (Plane.convex_closedSquare p s).segment_subset
      (gridPt_mem_closedSquare hs hk hi (by omega))
      (gridPt_mem_closedSquare hs hk hi (by omega)) hxP

/-- The local grid on the window `W(b)` lies in the window. -/
theorem cover_localGridEdges_subset_window (hC : IsCompact C) (hCne : C.Nonempty)
    (hbC : b ∉ C) (hk : 1 ≤ k) :
    cover (localGridEdges b (windowRadius C ε b) k) ⊆ window C ε b := by
  rw [window]
  exact cover_localGridEdges_subset (windowRadius_pos hC hCne hbC) hk

/-- **The grid misses the curve** — the disjointness `Schoenflies.exists_reps_hcov` asks of
the grid half of the attachment cover, and via `Schoenflies.MeetsFinitely.of_disjoint` the
grid's input to the joining loop. -/
theorem disjoint_cover_localGridEdges (hsep : IsSeparating C) (hb : b ∈ inside C)
    (hε : 0 < ε) (hk : 1 ≤ k) :
    Disjoint (cover (localGridEdges b (windowRadius C ε b) k)) C := by
  have hC : IsCompact C := hsep.isJordanCurve.isCompact
  have hCne : C.Nonempty := hsep.isJordanCurve.nonempty
  have hbC : b ∉ C := fun h => inside_subset_compl hb h
  have hsub : cover (localGridEdges b (windowRadius C ε b) k) ⊆ inside C :=
    (cover_localGridEdges_subset_window hC hCne hbC hk).trans
      (window_subset_inside hC hCne hsep hb hε)
  exact Set.disjoint_left.2 fun x hx hxC => inside_subset_compl (hsub hx) hxC

end WindowPlacement

/-! ### The interface, exercised

Over the concrete base, the two remaining obligations of Phase 3 are the extension chooser here
and the mesh transfer chooser of `MeshSteps.lean`; together they produce the Phase 3
deliverable. -/

example {C : Set Plane} (hC : IsJordanCurve C) (hE : HasGridExtensions initialStructure C)
    (hm : HasMeshTransfers initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC
    (hasGridSteps combInvariants_initialStructure (jordan_curve_theorem hC) hE)
    (hasMeshSteps hm)⟩

end Schoenflies
