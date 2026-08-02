/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.AdjCongr
import Schoenflies.Graph.Drawing

/-!
# Relabelling the edges of a graph

`Graph.map` relabels vertices only, and neither Mathlib nor this repository had an edge
relabelling — see the note on `InitialCell.aux` in `Schoenflies/InitialGenerated.lean`, where
the *supply* of fresh names was solved by a spare constructor rather than by relabelling. That
solution does not serve the two extension-graph dischargers of `thm:finite-transfer`: the mesh
and grid machinery (`SquareMesh*.lean`, `LocalGrid.lean`, `Overlay.lean`) names its edges by
`Piece = Plane × Plane`, while `Schoenflies.IsSourceExtension` fixes the extension's edge type
to the cell-name type `γ`. What is needed is not a fresh name for a new edge of an existing
graph but a **new graph** with the same vertices, links and drawing whose edge names are drawn
from `γ`.

`Graph.renameEdges` builds it, along any map injective on the edge set; `Graph.renameDrawing`
carries a drawing across; `Graph.exists_injOn_notMem` supplies, for a finite edge set and an
infinite name type, an injection avoiding any finite set of used names. Everything a drawing
can see is preserved on the nose — vertex set, adjacency, each edge's arc, the occupied point
set — so every property stated through those (finiteness, 2-connectivity via
`Graph.IsTwoConnected.of_adj_congr`, `IsDrawing`) transports.

## Blueprint

Not a numbered statement — the blueprint renames edges silently whenever it says "the graph
`H` obtained by overlaying". `rem:polygonal-overlay-convention`'s graphs enter
`thm:finite-transfer` through this module.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

variable {α β γ : Type*} {G : Graph α β} {σ : β → γ} {x y : α} {e f : β} {g : γ}

/-! ### The renamed graph -/

/-- **The graph `G` with its edges relabelled along `σ`** — same vertices, and for each edge
`e` of `G` an edge `σ e` with the same two ends. Injectivity of `σ` on `E(G)` is what keeps
distinct edges distinct, so it is data of the definition. -/
protected def renameEdges (G : Graph α β) (σ : β → γ) (hσ : Set.InjOn σ E(G)) :
    Graph α γ where
  vertexSet := V(G)
  IsLink g x y := ∃ e ∈ E(G), σ e = g ∧ G.IsLink e x y
  edgeSet := σ '' E(G)
  isLink_symm := fun g _hg => ⟨fun x y ⟨e, he, hσe, hl⟩ => ⟨e, he, hσe, hl.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro g x y v w ⟨e, he, rfl, hl⟩ ⟨e', he', hee, hl'⟩
    obtain rfl := hσ he' he hee
    exact hl.left_eq_or_eq hl'
  edge_mem_iff_exists_isLink := by
    intro g
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, e, he, rfl, hl⟩
    · rintro ⟨x, y, e, he, hσe, -⟩
      exact ⟨e, he, hσe⟩
  left_mem_of_isLink := by
    rintro g x y ⟨e, he, rfl, hl⟩
    exact hl.left_mem

variable {hσ : Set.InjOn σ E(G)}

@[simp] theorem renameEdges_vertexSet : V(G.renameEdges σ hσ) = V(G) := rfl

@[simp] theorem renameEdges_edgeSet : E(G.renameEdges σ hσ) = σ '' E(G) := rfl

theorem renameEdges_isLink :
    (G.renameEdges σ hσ).IsLink g x y ↔ ∃ e ∈ E(G), σ e = g ∧ G.IsLink e x y := Iff.rfl

/-- Each link of `G` survives under its new name. -/
theorem IsLink.renameEdges (hl : G.IsLink e x y) (hσ : Set.InjOn σ E(G)) :
    (G.renameEdges σ hσ).IsLink (σ e) x y := ⟨e, hl.edge_mem, rfl, hl⟩

/-- The renamed graph has the same adjacency. -/
@[simp] theorem renameEdges_adj : (G.renameEdges σ hσ).Adj x y ↔ G.Adj x y := by
  constructor
  · rintro ⟨g, e, he, rfl, hl⟩
    exact ⟨e, hl⟩
  · rintro ⟨e, hl⟩
    exact ⟨σ e, hl.renameEdges hσ⟩

theorem renameEdges_finite [G.Finite] : (G.renameEdges σ hσ).Finite where
  finite_vertexSet := G.finite_vertexSet
  finite_edgeSet := G.finite_edgeSet.image σ

/-- 2-connectivity survives the relabelling: it only sees adjacency
(`Graph.IsTwoConnected.of_adj_congr`). -/
theorem IsTwoConnected.renameEdges (h : G.IsTwoConnected) (hσ : Set.InjOn σ E(G)) :
    (G.renameEdges σ hσ).IsTwoConnected := by
  refine IsTwoConnected.of_adj_congr (G := G) (G' := G.renameEdges σ hσ) rfl
    (fun x y => ?_) h
  exact renameEdges_adj.symm

/-! ### The renamed drawing -/

section Drawing

variable [Nonempty β] {G : Graph Plane β} {σ : β → γ} {hσ : Set.InjOn σ E(G)}
  {d : β → ℝ → Plane} {x y : Plane}

/-- The drawing of the renamed graph: each new name draws what its old name drew. Off the
image of the edge set the value is junk, which no clause of `IsDrawing` ever reads. -/
noncomputable def renameDrawing (G : Graph Plane β) (σ : β → γ) (d : β → ℝ → Plane) :
    γ → ℝ → Plane :=
  fun g => d (Function.invFunOn σ E(G) g)

theorem renameDrawing_apply (hσ : Set.InjOn σ E(G)) (he : e ∈ E(G)) :
    renameDrawing G σ d (σ e) = d e := by
  unfold renameDrawing
  rw [hσ.leftInvOn_invFunOn he]

theorem edgeArc_renameDrawing (hσ : Set.InjOn σ E(G)) (he : e ∈ E(G)) :
    edgeArc (renameDrawing G σ d) (σ e) = edgeArc d e := by
  unfold edgeArc
  rw [renameDrawing_apply hσ he]

/-- Every edge of the renamed graph is a renamed edge of `G`, drawn along the same arc — the
form in which a clause quantified over `E(G.renameEdges σ hσ)` is pushed down to `E(G)`. -/
theorem exists_rep_of_mem_renameEdges (hσ : Set.InjOn σ E(G))
    (hg : g ∈ E(G.renameEdges σ hσ)) :
    ∃ e ∈ E(G), σ e = g ∧ edgeArc (renameDrawing G σ d) g = edgeArc d e := by
  obtain ⟨e, he, rfl⟩ := hg
  exact ⟨e, he, rfl, edgeArc_renameDrawing hσ he⟩

/-- A drawing survives the relabelling. -/
theorem IsDrawing.renameEdges (h : IsDrawing G d) (hσ : Set.InjOn σ E(G)) :
    IsDrawing (G.renameEdges σ hσ) (renameDrawing G σ d) where
  edge_param := by
    rintro g ⟨e, he, rfl⟩
    rw [renameDrawing_apply hσ he]
    obtain ⟨hc, hi, hl⟩ := h.edge_param he
    exact ⟨hc, hi, hl.renameEdges hσ⟩
  vertex_mem_edgeArc := by
    rintro g x y v ⟨e, he, rfl, hl⟩ hv hmem
    rw [edgeArc_renameDrawing hσ he] at hmem
    exact h.vertex_mem_edgeArc hl hv hmem
  edge_inter := by
    rintro g g' ⟨e, he, rfl⟩ ⟨e', he', rfl⟩ hne p hp hp'
    rw [edgeArc_renameDrawing hσ he] at hp
    rw [edgeArc_renameDrawing hσ he'] at hp'
    have hee : e ≠ e' := fun h => hne (congrArg σ h)
    obtain ⟨hv, ⟨u, hu⟩, ⟨u', hu'⟩⟩ := h.edge_inter he he' hee hp hp'
    exact ⟨hv, ⟨u, hu.renameEdges hσ⟩, ⟨u', hu'.renameEdges hσ⟩⟩

/-- The renamed graph occupies the same points. -/
theorem pointSet_renameEdges (hσ : Set.InjOn σ E(G)) :
    pointSet (G.renameEdges σ hσ) (renameDrawing G σ d) = pointSet G d := by
  rw [pointSet, pointSet, renameEdges_vertexSet, renameEdges_edgeSet]
  refine congrArg (V(G) ∪ ·) ?_
  rw [Set.biUnion_image]
  exact Set.iUnion₂_congr fun e he => edgeArc_renameDrawing hσ he

end Drawing

/-! ### The supply of fresh names -/

/-- **Fresh injective names always exist**: any finite set of things can be named injectively
from an infinite name type while avoiding any finite set of used names. This is the whole
content of the "choose fresh edge names" step of `rem:polygonal-overlay-convention`. -/
theorem exists_injOn_notMem {β γ : Type*} [Infinite γ] {s : Set β} (hs : s.Finite)
    {avoid : Set γ} (havoid : avoid.Finite) :
    ∃ σ : β → γ, Set.InjOn σ s ∧ ∀ e ∈ s, σ e ∉ avoid := by
  classical
  have hemb : ℕ ↪ ↥avoidᶜ := havoid.infinite_compl.natEmbedding
  haveI := hs.to_subtype
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin ↥s
  refine ⟨fun e => if h : e ∈ s then (hemb ((eqv ⟨e, h⟩ : Fin n) : ℕ) : γ) else
    (hemb 0 : γ), fun a ha b hb hab => ?_, fun e he => ?_⟩
  · simp only [dif_pos ha, dif_pos hb] at hab
    have h1 : eqv ⟨a, ha⟩ = eqv ⟨b, hb⟩ :=
      Fin.val_injective (hemb.injective (Subtype.ext hab))
    simpa using eqv.injective h1
  · simp only [dif_pos he]
    exact (hemb ((eqv ⟨e, he⟩ : Fin n) : ℕ)).2

end Graph
