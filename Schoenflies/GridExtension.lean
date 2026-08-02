/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.GridSteps

/-!
# The grid extension at a stage — the reduction of `Schoenflies.HasGridExtensions`

`Schoenflies.HasGridExtensions` (`Schoenflies/GridSteps.lean`) asks, at every admissible stage
`P`, mesh `ε > 0` and window centre `b ∈ inside C`, for an extension `H` of the source skeleton
satisfying the hypotheses of `thm:finite-transfer`(a) and containing the local grid on `W(b)`.
This module builds that extension and discharges every obligation except one, which it isolates
as the single named hypothesis `Schoenflies.HasGridUnionTwoConnected`.

## The design constraint, and the shape of `H`

`Schoenflies.IsSourceExtension.skeletonSet_subset` demands `|Γ| ⊆ |H|`, and `|Γ|` contains the
wild curve `C`, which no finite family of segments covers. So `H` cannot be the attached grid
graph alone: it is the **union** of

* the *outer part* of the stage's own graph — `S.outerGraph.map R.pos`, drawn by the stage's own
  drawing `R.drawing`, occupying exactly `C`; and
* the *polygonal part* — `Schoenflies.gridAttachGraph` over the pieces: the stage's polygonal
  nonboundary skeleton read off as a piece list (`Schoenflies.skeletonSegs`), auxiliary
  segments supplied by the 2-connectivity discharger, the joining arcs of the component loop
  (`Schoenflies.gridJoin`), and the local grid on `W(b)` — drawn by
  `Schoenflies.segmentDrawing`.

The two parts live over different edge-name types (`γ` and `Piece`), so the union is formed over
`γ ⊕ Piece` by `Graph.sumUnion` below, and `Schoenflies.nonempty_gridExtensionData_of_over`
pushes the result into the `γ`-named shape the transfer consumes.

The old nonboundary skeleton enters through the piece list — so grid×skeleton crossings become
vertices by the overlay convention — and **not** as subgraph edges of `Γ`; only the outer edges
of `Γ` survive as `γ`-named edges of `H`.

## Blueprint

* `Graph.IsDrawing.of_le`, `Graph.sumUnion`, `Graph.sumDraw`, `Graph.IsDrawing.sumUnion` — not
  numbered statements; the union of two plane graphs over distinct edge-name types, which is
  how the wild outer part and the polygonal part coexist in one graph.
-/

open Metric Set Schoenflies
open scoped Graph

/-! ## Plane-graph unions over a sum of edge-name types

A drawing restricted to a subgraph is a drawing, and two plane graphs over different edge-name
types union over the sum type. This is general plane-graph theory and belongs beside
`Graph.union` and `Graph.IsDrawing`; it is here because it was needed here first. -/

namespace Graph

variable {β β₁ β₂ : Type*}

/-- **A drawing of a graph restricts to a drawing of any subgraph.** Every clause of
`Graph.IsDrawing` quantifies over the graph's own vertices and edges, all of which the subgraph
has fewer of. -/
theorem IsDrawing.of_le {G H : Graph Plane β} {d : β → ℝ → Plane} (hd : IsDrawing G d)
    (hle : H ≤ G) : IsDrawing H d where
  edge_param := by
    intro e he
    obtain ⟨hc, hi, hl⟩ := hd.edge_param (hle.edgeSet_mono he)
    exact ⟨hc, hi, (hle.isLink_iff he).2 hl⟩
  vertex_mem_edgeArc := fun _ _ _ _ hl hv hvarc =>
    hd.vertex_mem_edgeArc (hl.mono hle) (hle.vertexSet_mono hv) hvarc
  edge_inter := by
    intro e f he hf hef p hpe hpf
    obtain ⟨-, hince, hincf⟩ :=
      hd.edge_inter (hle.edgeSet_mono he) (hle.edgeSet_mono hf) hef hpe hpf
    have hince' : H.Inc e p := (hle.inc_congr he).2 hince
    refine ⟨?_, hince', (hle.inc_congr hf).2 hincf⟩
    obtain ⟨y, hl⟩ := hince'
    exact hl.left_mem

/-- **The union of two graphs over different edge-name types**: the edges of `G₁` renamed
`Sum.inl`, the edges of `G₂` renamed `Sum.inr`, and the union taken over `β₁ ⊕ β₂`. This is how
the outer part of the stage's graph (edges named by `γ`) and the polygonal attached-grid part
(edges named by `Piece`) become one graph. -/
protected def sumUnion (G₁ : Graph Plane β₁) (G₂ : Graph Plane β₂) : Graph Plane (β₁ ⊕ β₂) :=
  (G₁.renameEdges Sum.inl Sum.inl_injective.injOn).union
    (G₂.renameEdges Sum.inr Sum.inr_injective.injOn)

/-- The drawing of the union: each side keeps its own drawing. -/
def sumDraw (d₁ : β₁ → ℝ → Plane) (d₂ : β₂ → ℝ → Plane) : β₁ ⊕ β₂ → ℝ → Plane :=
  Sum.elim d₁ d₂

variable {G₁ : Graph Plane β₁} {G₂ : Graph Plane β₂} {d₁ : β₁ → ℝ → Plane} {d₂ : β₂ → ℝ → Plane}

@[simp] theorem sumUnion_vertexSet : V(G₁.sumUnion G₂) = V(G₁) ∪ V(G₂) := rfl

@[simp] theorem sumUnion_edgeSet :
    E(G₁.sumUnion G₂) = Sum.inl '' E(G₁) ∪ Sum.inr '' E(G₂) := rfl

@[simp] theorem edgeArc_sumDraw_inl (e : β₁) :
    edgeArc (sumDraw d₁ d₂) (Sum.inl e) = edgeArc d₁ e := rfl

@[simp] theorem edgeArc_sumDraw_inr (P : β₂) :
    edgeArc (sumDraw d₁ d₂) (Sum.inr P) = edgeArc d₂ P := rfl

theorem sumUnion_isLink_inl {e : β₁} {x y : Plane} :
    (G₁.sumUnion G₂).IsLink (Sum.inl e) x y ↔ G₁.IsLink e x y := by
  rw [Graph.sumUnion, union_isLink]
  constructor
  · rintro (⟨e', -, he', hl⟩ | ⟨-, e', -, he', -⟩)
    · exact Sum.inl_injective he' ▸ hl
    · exact absurd he' Sum.inr_ne_inl
  · intro hl
    exact Or.inl ⟨e, hl.edge_mem, rfl, hl⟩

theorem sumUnion_isLink_inr {P : β₂} {x y : Plane} :
    (G₁.sumUnion G₂).IsLink (Sum.inr P) x y ↔ G₂.IsLink P x y := by
  rw [Graph.sumUnion, union_isLink]
  constructor
  · rintro (⟨e', -, he', -⟩ | ⟨-, e', -, he', hl⟩)
    · exact absurd he' Sum.inl_ne_inr
    · exact Sum.inr_injective he' ▸ hl
  · intro hl
    refine Or.inr ⟨?_, P, hl.edge_mem, rfl, hl⟩
    rintro ⟨e', -, he'⟩
    exact absurd he' Sum.inl_ne_inr

theorem sumUnion_inc_inl {e : β₁} {x : Plane} :
    (G₁.sumUnion G₂).Inc (Sum.inl e) x ↔ G₁.Inc e x := by
  constructor
  · rintro ⟨y, hl⟩
    exact ⟨y, sumUnion_isLink_inl.1 hl⟩
  · rintro ⟨y, hl⟩
    exact ⟨y, sumUnion_isLink_inl.2 hl⟩

theorem sumUnion_inc_inr {P : β₂} {x : Plane} :
    (G₁.sumUnion G₂).Inc (Sum.inr P) x ↔ G₂.Inc P x := by
  constructor
  · rintro ⟨y, hl⟩
    exact ⟨y, sumUnion_isLink_inr.1 hl⟩
  · rintro ⟨y, hl⟩
    exact ⟨y, sumUnion_isLink_inr.2 hl⟩

/-- The union occupies exactly what its two parts occupy. -/
theorem pointSet_sumUnion :
    pointSet (G₁.sumUnion G₂) (sumDraw d₁ d₂) = pointSet G₁ d₁ ∪ pointSet G₂ d₂ := by
  rw [pointSet, pointSet, pointSet, sumUnion_vertexSet, sumUnion_edgeSet, Set.biUnion_union,
    Set.biUnion_image, Set.biUnion_image]
  simp only [edgeArc_sumDraw_inl, edgeArc_sumDraw_inr]
  ac_rfl

theorem sumUnion_finite [G₁.Finite] [G₂.Finite] : (G₁.sumUnion G₂).Finite where
  finite_vertexSet := by
    rw [sumUnion_vertexSet]
    exact (Graph.finite_vertexSet G₁).union (Graph.finite_vertexSet G₂)
  finite_edgeSet := by
    rw [sumUnion_edgeSet]
    exact ((Graph.finite_edgeSet G₁).image _).union ((Graph.finite_edgeSet G₂).image _)

/-- **The union of two plane graphs is a plane graph**, provided the arcs of the two sides meet
each other only at shared endpoints: a vertex of either side on an arc of the other is an end of
that arc, and a common point of two cross arcs is an endpoint of both. -/
theorem IsDrawing.sumUnion (h₁ : IsDrawing G₁ d₁) (h₂ : IsDrawing G₂ d₂)
    (hv₁ : ∀ ⦃v⦄, v ∈ V(G₂) → ∀ ⦃e x y⦄, G₁.IsLink e x y → v ∈ edgeArc d₁ e → v = x ∨ v = y)
    (hv₂ : ∀ ⦃v⦄, v ∈ V(G₁) → ∀ ⦃P x y⦄, G₂.IsLink P x y → v ∈ edgeArc d₂ P → v = x ∨ v = y)
    (hcross : ∀ ⦃e⦄, e ∈ E(G₁) → ∀ ⦃P⦄, P ∈ E(G₂) → ∀ ⦃q⦄, q ∈ edgeArc d₁ e →
      q ∈ edgeArc d₂ P → G₁.Inc e q ∧ G₂.Inc P q) :
    IsDrawing (G₁.sumUnion G₂) (sumDraw d₁ d₂) where
  edge_param := by
    rintro e' (⟨e, he, rfl⟩ | ⟨P, hP, rfl⟩)
    · obtain ⟨hc, hi, hl⟩ := h₁.edge_param he
      exact ⟨hc, hi, sumUnion_isLink_inl.2 hl⟩
    · obtain ⟨hc, hi, hl⟩ := h₂.edge_param hP
      exact ⟨hc, hi, sumUnion_isLink_inr.2 hl⟩
  vertex_mem_edgeArc := by
    rintro e' x y v hl hv hvarc
    rcases e' with e | P
    · rw [edgeArc_sumDraw_inl] at hvarc
      have hl₁ := sumUnion_isLink_inl.1 hl
      rcases hv with hv | hv
      · exact h₁.vertex_mem_edgeArc hl₁ hv hvarc
      · exact hv₁ hv hl₁ hvarc
    · rw [edgeArc_sumDraw_inr] at hvarc
      have hl₂ := sumUnion_isLink_inr.1 hl
      rcases hv with hv | hv
      · exact hv₂ hv hl₂ hvarc
      · exact h₂.vertex_mem_edgeArc hl₂ hv hvarc
  edge_inter := by
    rintro e' f' he' hf' hne q hqe hqf
    rcases he' with ⟨e, he, rfl⟩ | ⟨P, hP, rfl⟩ <;> rcases hf' with ⟨f, hf, rfl⟩ | ⟨Q, hQ, rfl⟩
    · -- both from the first side
      have hef : e ≠ f := fun h => hne (congrArg Sum.inl h)
      obtain ⟨hV, hie, hif⟩ := h₁.edge_inter he hf hef hqe hqf
      exact ⟨Or.inl hV, sumUnion_inc_inl.2 hie, sumUnion_inc_inl.2 hif⟩
    · -- one from each side
      obtain ⟨hie, hiQ⟩ := hcross he hQ hqe hqf
      refine ⟨Or.inl ?_, sumUnion_inc_inl.2 hie, sumUnion_inc_inr.2 hiQ⟩
      obtain ⟨y, hl⟩ := hie
      exact hl.left_mem
    · -- one from each side, the other order
      obtain ⟨hif, hiP⟩ := hcross hf hP hqf hqe
      refine ⟨Or.inl ?_, sumUnion_inc_inr.2 hiP, sumUnion_inc_inl.2 hif⟩
      obtain ⟨y, hl⟩ := hif
      exact hl.left_mem
    · -- both from the second side
      have hPQ : P ≠ Q := fun h => hne (congrArg Sum.inr h)
      obtain ⟨hV, hiP, hiQ⟩ := h₂.edge_inter hP hQ hPQ hqe hqf
      exact ⟨Or.inr hV, sumUnion_inc_inr.2 hiP, sumUnion_inc_inr.2 hiQ⟩

end Graph

namespace Schoenflies

open Graph CellStructure

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane}

/-! ## The nonboundary skeleton as a piece list

`IsWeaklyAdmissible.isPolygonal` says each nonboundary edge arc is `poly vs` for some vertex
list; `Schoenflies.segsOf` reads such a list as nondegenerate segments covering it. Chaining
the two over the (finite) nonboundary edge set presents the whole polygonal nonboundary
skeleton as one piece list, which is what the overlay of `prop:local-grid-attachment`
consumes. -/

open scoped Classical in
/-- The chosen polyline presentation of a polygonal set — junk when the set is not
polygonal, which no lemma below ever reads. -/
noncomputable def arcChain (A : Set Plane) : List Plane :=
  if h : IsPolygonal A then h.choose else []

theorem poly_arcChain {A : Set Plane} (h : IsPolygonal A) : A = poly (arcChain A) := by
  rw [arcChain, dif_pos h]
  exact h.choose_spec

/-- The nonboundary 1-cells of the structure, as a list. -/
noncomputable def nonboundaryEdgeList (S : CellStructure γ) : List γ :=
  letI := Classical.decPred fun e => e ∉ E(S.outerGraph)
  (S.finite_edgeSet.toFinset.filter fun e => e ∉ E(S.outerGraph)).toList

theorem mem_nonboundaryEdgeList {e : γ} :
    e ∈ nonboundaryEdgeList S ↔ e ∈ E(S.skel) ∧ e ∉ E(S.outerGraph) := by
  letI := Classical.decPred fun e : γ => e ∉ E(S.outerGraph)
  rw [nonboundaryEdgeList, Finset.mem_toList, Finset.mem_filter, Set.Finite.mem_toFinset]

/-- **The polygonal nonboundary skeleton of a stage, as a piece list**: each nonboundary
edge's arc read off as the segment chain of its chosen polyline. -/
noncomputable def skeletonSegs (R : S.Realization) : List Piece :=
  (nonboundaryEdgeList S).flatMap fun e => segsOf (arcChain (edgeArc R.drawing e))

/-- Every listed piece is nondegenerate — `segsOf` skips repeated vertices. -/
theorem skeletonSegs_nondeg : ∀ P ∈ skeletonSegs R, P.Nondeg := by
  intro P hP
  obtain ⟨e, -, hPe⟩ := List.mem_flatMap.1 hP
  exact segsOf_nondeg _ P hPe

/-- A piece of a chain stays on the chain's carrier. -/
theorem seg_subset_poly_of_mem_segsOf {vs : List Plane} {P : Piece} (hP : P ∈ segsOf vs) :
    P.seg ⊆ poly vs := by
  rcases cover_segsOf vs with h | ⟨h1, -⟩
  · exact fun z hz => h ▸ mem_cover hP hz
  · rw [h1] at hP
    exact absurd hP (List.not_mem_nil)

/-- A drawn edge arc holds two distinct points: its two ends, distinct because a plane graph
has no loops. -/
theorem exists_ne_mem_edgeArc (R : S.Realization) {e : γ} (he : e ∈ E(S.skel)) :
    ∃ a b, a ∈ edgeArc R.drawing e ∧ b ∈ edgeArc R.drawing e ∧ a ≠ b := by
  have he' : e ∈ E(R.graph) := by rw [Realization.edgeSet_graph]; exact he
  obtain ⟨-, -, hl⟩ := R.isDrawing.edge_param he'
  refine ⟨R.drawing e 0, R.drawing e 1, ⟨0, zero_mem_I, rfl⟩, ⟨1, one_mem_I, rfl⟩,
    fun hEq => ?_⟩
  exact R.isDrawing.not_isLoopAt e (R.drawing e 1) (hEq ▸ hl)

/-- **The chain of a nonboundary edge occupies exactly its arc.** -/
theorem cover_segsOf_arcChain (R : S.Realization) {e : γ} (he : e ∈ E(S.skel))
    (hpoly : IsPolygonal (edgeArc R.drawing e)) :
    cover (segsOf (arcChain (edgeArc R.drawing e))) = edgeArc R.drawing e := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_ne_mem_edgeArc R he
  have hpa := poly_arcChain hpoly
  exact (cover_segsOf_eq (hpa ▸ ha) (hpa ▸ hb) hab).trans hpa.symm

/-- Reading a listed piece back: it belongs to the chain of one nonboundary edge. -/
theorem exists_edge_of_mem_skeletonSegs {P : Piece} (hP : P ∈ skeletonSegs R) :
    ∃ e, (e ∈ E(S.skel) ∧ e ∉ E(S.outerGraph)) ∧
      P ∈ segsOf (arcChain (edgeArc R.drawing e)) := by
  obtain ⟨e, he, hPe⟩ := List.mem_flatMap.1 hP
  exact ⟨e, mem_nonboundaryEdgeList.1 he, hPe⟩

/-- A nonboundary edge arc lies on the cover of the skeleton pieces. -/
theorem edgeArc_subset_cover_skeletonSegs (hW : R.IsWeaklyAdmissible outer dom) {e : γ}
    (he : e ∈ E(S.skel)) (hne : e ∉ E(S.outerGraph)) :
    edgeArc R.drawing e ⊆ cover (skeletonSegs R) := by
  intro z hz
  rw [← cover_segsOf_arcChain R he (hW.isPolygonal he hne)] at hz
  obtain ⟨P, hP, hzP⟩ := mem_cover_iff.1 hz
  exact mem_cover (List.mem_flatMap.2 ⟨e, mem_nonboundaryEdgeList.2 ⟨he, hne⟩, hP⟩) hzP

/-- **The skeleton pieces occupy exactly the nonboundary edge arcs.** -/
theorem cover_skeletonSegs (hW : R.IsWeaklyAdmissible outer dom) :
    cover (skeletonSegs R) = ⋃ e ∈ E(S.skel) \ E(S.outerGraph), edgeArc R.drawing e := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨P, hP, hzP⟩ := mem_cover_iff.1 hz
    obtain ⟨e, ⟨he, hne⟩, hPe⟩ := exists_edge_of_mem_skeletonSegs hP
    have hsub : P.seg ⊆ edgeArc R.drawing e :=
      (poly_arcChain (hW.isPolygonal he hne)) ▸ seg_subset_poly_of_mem_segsOf hPe
    exact Set.mem_biUnion ⟨he, hne⟩ (hsub hzP)
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
    exact edgeArc_subset_cover_skeletonSegs hW he.1 he.2 hze

/-! ## Where the skeleton pieces sit

`MeetsFinitely` (obligation 2 of the extension chooser) and the window-side placement facts,
all read off the stage's own drawing invariants: away from the drawn 0-cells a skeleton piece
runs in the open nonboundary cell of its edge, inside the open domain, off the outer curve. -/

/-- **A skeleton piece leaves the open domain only at drawn 0-cells.** -/
theorem skeletonSegs_diff_subset (hW : R.IsWeaklyAdmissible outer dom) :
    ∀ P ∈ skeletonSegs R, P.seg \ (R.pos '' V(S.skel)) ⊆ dom \ outer := by
  intro P hP z hz
  obtain ⟨e, ⟨he, hne⟩, hPe⟩ := exists_edge_of_mem_skeletonSegs hP
  have hsub : P.seg ⊆ edgeArc R.drawing e :=
    (poly_arcChain (hW.isPolygonal he hne)) ▸ seg_subset_poly_of_mem_segsOf hPe
  obtain ⟨x, y, hl⟩ := S.skel.exists_isLink_of_mem_edgeSet he
  refine hW.cell_subset he hne ?_
  rw [R.cell_edge hl]
  refine ⟨hsub hz.1, ?_⟩
  rintro (h | h)
  · exact hz.2 (h ▸ ⟨x, hl.left_mem, rfl⟩)
  · exact hz.2 (h ▸ ⟨y, hl.right_mem, rfl⟩)

/-- **Obligation 2 of the extension chooser, discharged**: the skeleton pieces meet `C`
finitely, because away from the finitely many drawn 0-cells they avoid it. -/
theorem meetsFinitely_skeletonSegs {C : Set Plane} (hW : R.IsWeaklyAdmissible C dom) :
    MeetsFinitely (skeletonSegs R) C :=
  MeetsFinitely.of_diff_subset_compl (S.finite_vertexSet.image R.pos)
    fun P hP => (skeletonSegs_diff_subset hW P hP).trans fun _ hz => hz.2

/-- What the skeleton pieces meet of the outer curve is drawn 0-cells. -/
theorem cover_skeletonSegs_inter_subset {C : Set Plane} (hW : R.IsWeaklyAdmissible C dom) :
    cover (skeletonSegs R) ∩ C ⊆ R.pos '' V(S.skel) := by
  rintro z ⟨hz, hzC⟩
  obtain ⟨P, hP, hzP⟩ := mem_cover_iff.1 hz
  by_contra hznot
  exact (skeletonSegs_diff_subset hW P hP ⟨hzP, hznot⟩).2 hzC

/-- The skeleton pieces stay on the realized skeleton. -/
theorem cover_skeletonSegs_subset (hW : R.IsWeaklyAdmissible outer dom) :
    cover (skeletonSegs R) ⊆ R.skeletonSet := by
  intro z hz
  obtain ⟨P, hP, hzP⟩ := mem_cover_iff.1 hz
  obtain ⟨e, ⟨he, hne⟩, hPe⟩ := exists_edge_of_mem_skeletonSegs hP
  have hsub : P.seg ⊆ edgeArc R.drawing e :=
    (poly_arcChain (hW.isPolygonal he hne)) ▸ seg_subset_poly_of_mem_segsOf hPe
  exact edgeArc_subset_pointSet (by rw [Realization.edgeSet_graph]; exact he) (hsub hzP)

/-! ## The drawn 0-cells off the outer cycle lie on the skeleton pieces

The union's vertex clause `V(Γ) ⊆ V(H)` splits: an outer 0-cell is a vertex of the outer part,
and any other 0-cell must be found on the polygonal part. It is, because 2-connectedness
leaves no vertex isolated, an edge at a non-outer vertex is nonboundary, and a drawn edge
ends at its drawn 0-cells. -/

/-- A 0-cell off the outer cycle has a nonboundary edge. -/
theorem exists_nonboundary_isLink_of_notMem_outer (hW : R.IsWeaklyAdmissible outer dom)
    {v : γ} (hv : v ∈ V(S.skel)) (hvout : v ∉ V(S.outerGraph)) :
    ∃ e w, S.skel.IsLink e v w ∧ e ∉ E(S.outerGraph) := by
  have hv' : R.pos v ∈ V(R.graph) := by
    rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩
  -- some other vertex exists, so a path leaves `pos v` by some edge
  obtain ⟨a, ha, b, hb, -, -, hab, -, -⟩ := hW.isTwoConnected.hasThreeVertices
  obtain ⟨w', hw', hne⟩ : ∃ w' ∈ V(R.graph), R.pos v ≠ w' := by
    rcases eq_or_ne a (R.pos v) with rfl | h
    · exact ⟨b, hb, fun h => hab h⟩
    · exact ⟨a, ha, fun h' => h h'.symm⟩
  obtain ⟨W, hWp⟩ := hW.isTwoConnected.connected.exists_isPath hv' hw'
  obtain ⟨g, -, hinc⟩ := hWp.isWalk.exists_inc_source (hWp.ne_nil hne)
  obtain ⟨z, hl⟩ := hinc
  -- read the incidence back on the abstract skeleton
  have hl' : (S.skel.map R.pos).IsLink g (R.pos v) z := hl
  rw [Graph.map_isLink] at hl'
  obtain ⟨p, q, hpq, hpv, -⟩ := hl'
  obtain rfl : p = v := R.injOn_pos hpq.left_mem hv hpv
  refine ⟨g, q, hpq, fun hgout => hvout ?_⟩
  -- an outer edge would put `v` on the outer cycle
  obtain ⟨x', y', hlo⟩ := S.outerGraph.exists_isLink_of_mem_edgeSet hgout
  rcases hpq.left_eq_or_eq (hlo.mono S.outerGraph_le) with rfl | rfl
  · exact hlo.left_mem
  · exact hlo.right_mem

/-- **A non-outer drawn 0-cell lies on the skeleton pieces.** -/
theorem pos_mem_cover_skeletonSegs (hW : R.IsWeaklyAdmissible outer dom) {v : γ}
    (hv : v ∈ V(S.skel)) (hvout : v ∉ V(S.outerGraph)) :
    R.pos v ∈ cover (skeletonSegs R) := by
  obtain ⟨e, w, hl, hne⟩ := exists_nonboundary_isLink_of_notMem_outer hW hv hvout
  have he' : e ∈ E(R.graph) := by rw [Realization.edgeSet_graph]; exact hl.edge_mem
  obtain ⟨-, -, hlp⟩ := R.isDrawing.edge_param he'
  have hlv : R.graph.IsLink e (R.pos v) (R.pos w) := hl.map R.pos
  refine edgeArc_subset_cover_skeletonSegs hW hl.edge_mem hne ?_
  rcases hlv.eq_and_eq_or_eq_and_eq hlp with ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h0 ▸ ⟨0, zero_mem_I, rfl⟩
  · exact h0 ▸ ⟨1, one_mem_I, rfl⟩

/-! ## The joining arcs

`prop:local-grid-attachment`'s component loop joins every representative to a fixed hub by a
simple polygonal arc in the open Jordan domain (`lem:polygonal-connectedness`,
`Schoenflies.exists_simple_poly_of_isPreconnected`). The hub is a corner of the local grid,
and the degenerate join — from the hub to itself — is the grid edge at the hub, which the
overlay deduplicates away. -/

open scoped Classical in
/-- **The joining-arc chooser.** For a point `r` of the open domain other than the hub, the
segment chain of a chosen simple polygonal arc from the hub to `r` inside the domain; at the
hub itself (and off the domain, where it is never read), the fallback piece `E₀`. -/
noncomputable def gridJoin (C : Set Plane) (hub : Plane) (E₀ : Piece) (r : Plane) :
    List Piece :=
  if h : IsSeparating C ∧ hub ∈ inside C ∧ r ∈ inside C ∧ r ≠ hub then
    segsOf (exists_simple_poly_of_isPreconnected h.1.isOpen_inside
      h.1.isConnected_inside.isPreconnected h.2.1 h.2.2.1 (Ne.symm h.2.2.2)).choose
  else [E₀]

variable {C : Set Plane} {hub : Plane} {E₀ : Piece} {r : Plane}

/-- The chosen arc, read back. -/
theorem gridJoin_spec (hsep : IsSeparating C) (hhub : hub ∈ inside C) (hr : r ∈ inside C)
    (hne : r ≠ hub) :
    ∃ vs, ∃ h : vs ≠ [], vs.head h = hub ∧ vs.getLast h = r ∧ poly vs ⊆ inside C ∧
      IsArcBetween (poly vs) hub r ∧ gridJoin C hub E₀ r = segsOf vs := by
  rw [gridJoin, dif_pos ⟨hsep, hhub, hr, hne⟩]
  obtain ⟨hvs, h1, h2, h3, h4⟩ := (exists_simple_poly_of_isPreconnected hsep.isOpen_inside
    hsep.isConnected_inside.isPreconnected hhub hr (Ne.symm hne)).choose_spec
  exact ⟨_, hvs, h1, h2, h3, h4, rfl⟩

theorem gridJoin_self : gridJoin C hub E₀ hub = [E₀] := by
  rw [gridJoin, dif_neg]
  rintro ⟨-, -, -, h⟩
  exact h rfl

/-- Every joining piece is nondegenerate. -/
theorem gridJoin_nondeg (hE₀ : E₀.Nondeg) : ∀ P ∈ gridJoin C hub E₀ r, P.Nondeg := by
  rw [gridJoin]
  split_ifs
  · exact segsOf_nondeg _
  · intro P hP
    rw [List.mem_singleton] at hP
    exact hP ▸ hE₀

/-- **The four properties the joining loop asks of an arc**, plus the domain containment:
connected, through the hub, through its representative, inside the open domain. -/
theorem gridJoin_props (hsep : IsSeparating C) (hhub : hub ∈ inside C)
    (hE₀ : E₀.seg ⊆ inside C) (hE₀hub : hub ∈ E₀.seg) (hr : r ∈ inside C) :
    IsPreconnected (cover (gridJoin C hub E₀ r)) ∧ hub ∈ cover (gridJoin C hub E₀ r) ∧
      r ∈ cover (gridJoin C hub E₀ r) ∧ cover (gridJoin C hub E₀ r) ⊆ inside C := by
  rcases eq_or_ne r hub with rfl | hne
  · rw [gridJoin_self]
    have hcov : cover [E₀] = E₀.seg := by rw [cover_cons, cover_nil, Set.union_empty]
    rw [hcov]
    exact ⟨(convex_segment E₀.1 E₀.2).isPreconnected, hE₀hub, hE₀hub, hE₀⟩
  · obtain ⟨vs, hvs, hhead, hlast, hsub, -, heq⟩ := gridJoin_spec hsep hhub hr hne
    rw [heq, cover_segsOf_eq (hhead ▸ head_mem_poly hvs) (hlast ▸ getLast_mem_poly hvs)
      hne.symm]
    exact ⟨(isConnected_poly hvs).isPreconnected, hhead ▸ head_mem_poly hvs,
      hlast ▸ getLast_mem_poly hvs, hsub⟩

/-! ## Two helpers on the overlay -/

/-- **A prescribed extra point lying on the pieces is a vertex of the overlay** —
`rem:polygonal-overlay-convention` read back off `Schoenflies.attachGraph`. -/
theorem mem_vertexSet_attachGraph_of_mem_extra {pieces : List Piece} {extra : List Plane}
    {z : Plane} (hnd : ∀ P ∈ pieces, P.Nondeg) (hz : z ∈ extra) (hzc : z ∈ cover pieces) :
    z ∈ V(attachGraph pieces extra) := by
  have hend : z ∈ endSet (subdivide pieces (attachPoints pieces extra)) :=
    mem_endSet_subdivide_of_mem_cover hnd (mem_attachPoints_of_mem hz) hzc
  show z ∈ V(overlayGraph pieces (attachPoints pieces extra))
  rw [← (sameLinks_overlayGraph pieces (attachPoints pieces extra)).vertexSet,
    pieceListGraph_vertexSet]
  exact hend

/-- An overlay edge runs on the cover of the source pieces. -/
theorem seg_subset_cover_of_mem_overlayPieces {pieces : List Piece} {points : List Plane}
    {Q : Piece} (hQ : Q ∈ overlayPieces pieces points) : Q.seg ⊆ cover pieces := by
  intro z hz
  rw [← overlayPieces_cover pieces points]
  exact mem_cover hQ hz

/-! ## The extension graph -/

/-- **The proposed extension `H` at a stage**: the outer part of the stage's own graph — drawn
by the stage's own drawing, occupying exactly the outer curve — unioned over `γ ⊕ Piece` with
the polygonal attached-grid part of `prop:local-grid-attachment`. -/
noncomputable def gridExtGraph (R : S.Realization) (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) (extra : List Plane) :
    Graph Plane (γ ⊕ Piece) :=
  (S.outerGraph.map R.pos).sumUnion (gridAttachGraph gsegs reps Jarc p s ε extra)

/-- Its drawing: the stage's drawing on the outer names, straight segments on the pieces. -/
noncomputable def gridExtDraw (R : S.Realization) : γ ⊕ Piece → ℝ → Plane :=
  Graph.sumDraw R.drawing segmentDrawing

/-- The outer part is a subgraph of the stage's drawn graph. -/
theorem outerPart_le (R : S.Realization) : S.outerGraph.map R.pos ≤ R.graph :=
  S.outerGraph_le.map R.pos

instance outerPart_finite (R : S.Realization) : (S.outerGraph.map R.pos).Finite where
  finite_vertexSet := by
    rw [Graph.vertexSet_map]
    exact (S.finite_vertexSet.subset S.outerGraph_le.vertexSet_mono).image R.pos
  finite_edgeSet := by
    rw [Graph.edgeSet_map]
    exact S.finite_edgeSet.subset S.outerGraph_le.edgeSet_mono

end Schoenflies
