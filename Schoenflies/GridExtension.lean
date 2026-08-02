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
