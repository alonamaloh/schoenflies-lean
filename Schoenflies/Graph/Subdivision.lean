/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.TwoConnected
import Schoenflies.Graph.Cycle

/-!
# Subdividing an edge preserves connectedness and 2-connectedness

`lem:subdivision-ear-preserve`(a) in the form the cell-structure recursion needs: replacing an
edge by two edges through a new vertex changes neither connectedness nor 2-connectedness. Every
elementary operation of `def:generated-structure` has to keep `def:admissible-graph`'s
2-connectivity clause, and the subdivision half of that is here.

## The relation, not the construction

`Schoenflies.subdivGraph` builds the subdivided graph, but only for `Graph γ γ` — vertex names
and edge names of the same type — because that is what an abstract cell structure has. The
graph this file is really about is the *drawn* one, `Graph Plane γ`, whose subdivision is built
by `SubdivData.realizeGraph`. So the hypothesis here is a **characterization**,
`Graph.IsSubdivisionOf`: `G'` has one more vertex than `G`, and its links are `G`'s save that
`e` has been replaced by `e₁` and `e₂` through `v`. Both constructions satisfy it, and neither
has to be mentioned.

## `x ≠ y` is not optional

The theorem is **false** for a loop, and 2-connectedness does not rule loops out: a loop `e` at
`x` subdivides into two edges from `x` to `v`, and deleting `x` strands `v`. So
`IsSubdivisionOf.isTwoConnected` takes `x ≠ y`. Every consumer has it — a drawn edge is an arc
between two distinct points — and `Graph.IsDrawing.not_isLoopAt` is where it comes from.

## Blueprint

* `Graph.IsSubdivisionOf` — "the graph obtained by subdividing an edge", as a relation.
* `Graph.IsSubdivisionOf.connected` — `lem:subdivision-ear-preserve`(a) for connectedness.
* `Graph.IsSubdivisionOf.isTwoConnected` — the same for 2-connectedness, which is the clause
  `def:admissible-graph` imposes.
* `Graph.IsSubdivisionOf.deleteVerts_newVertex` — deleting the new vertex gives back the old
  graph with the subdivided edge deleted. This is the case that needs the edge to lie on a
  cycle, i.e. `Graph.IsTwoConnected.no_bridge`.
-/

open Set

variable {α β : Type*} {G G' : Graph α β} {e e₁ e₂ f : β} {x y v z u w a b : α}

namespace Graph

/-- **`G'` is `G` with the edge `e` subdivided.** `e` runs from `x` to `y` in `G`; in `G'` it
has been replaced by a new vertex `v` and two new edges `e₁ : x — v` and `e₂ : v — y`, and
nothing else has changed.

A characterization rather than a construction, because the two constructions that satisfy it —
`Schoenflies.subdivGraph` on an abstract skeleton and
`Schoenflies.CellStructure.SubdivData.realizeGraph` on a drawn one — live in different graph
types. -/
structure IsSubdivisionOf (G' G : Graph α β) (e x y v e₁ e₂ : _) : Prop where
  /-- The subdivided edge runs from `x` to `y`. -/
  isLink : G.IsLink e x y
  /-- The new vertex is not an old one. -/
  newVertex_notMem : v ∉ V(G)
  /-- The first new edge is not an old one. -/
  newEdge₁_notMem : e₁ ∉ E(G)
  /-- The second new edge is not an old one. -/
  newEdge₂_notMem : e₂ ∉ E(G)
  /-- The two new edges are distinct. -/
  newEdge_ne : e₁ ≠ e₂
  /-- One vertex has been added. -/
  vertexSet_eq : V(G') = insert v V(G)
  /-- The links are the old ones, except that `e` has become `e₁` and `e₂` through `v`. -/
  isLink_iff : ∀ f a b, G'.IsLink f a b ↔
    (G.IsLink f a b ∧ f ≠ e ∧ f ≠ e₁ ∧ f ≠ e₂) ∨
      (f = e₁ ∧ s(a, b) = s(x, v)) ∨ (f = e₂ ∧ s(a, b) = s(v, y))

namespace IsSubdivisionOf

variable (h : IsSubdivisionOf G' G e x y v e₁ e₂)
include h

theorem mem_vertexSet_of_mem (hu : u ∈ V(G)) : u ∈ V(G') := by
  rw [h.vertexSet_eq]; exact mem_insert_of_mem _ hu

theorem newVertex_mem : v ∈ V(G') := by
  rw [h.vertexSet_eq]; exact mem_insert _ _

theorem left_mem : x ∈ V(G') := h.mem_vertexSet_of_mem h.isLink.left_mem

theorem right_mem : y ∈ V(G') := h.mem_vertexSet_of_mem h.isLink.right_mem

theorem isLink_newEdge₁ : G'.IsLink e₁ x v := (h.isLink_iff _ _ _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem isLink_newEdge₂ : G'.IsLink e₂ v y :=
  (h.isLink_iff _ _ _).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- An old edge other than the subdivided one survives with its ends. -/
theorem isLink_of_isLink (hl : G.IsLink f a b) (hf : f ≠ e) : G'.IsLink f a b :=
  (h.isLink_iff _ _ _).2 (Or.inl ⟨hl, hf,
    fun hh => h.newEdge₁_notMem (hh ▸ hl.edge_mem), fun hh => h.newEdge₂_notMem (hh ▸ hl.edge_mem)⟩)

/-- **Reachability survives.** A walk that took the subdivided edge goes through the new vertex
instead; every other step is unchanged. -/
theorem reaches (hr : G.Reaches u w) : G'.Reaches u w := by
  obtain ⟨W, hW⟩ := hr
  induction hW with
  | nil hu => exact Reaches.refl (h.mem_vertexSet_of_mem hu)
  | @cons a c w f W hl _ ih =>
    refine Reaches.trans ?_ ih
    by_cases hf : f = e
    · subst hf
      -- The step crossed the subdivided edge, in one direction or the other.
      rcases h.isLink.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (Reaches.of_isLink h.isLink_newEdge₁).trans (Reaches.of_isLink h.isLink_newEdge₂)
      · exact (Reaches.of_isLink h.isLink_newEdge₂.symm).trans
          (Reaches.of_isLink h.isLink_newEdge₁.symm)
    · exact Reaches.of_isLink (h.isLink_of_isLink hl hf)

/-- **Subdividing an edge keeps a graph connected.** -/
theorem connected (hG : G.Connected) : G'.Connected := by
  refine Connected.of_hub h.left_mem fun u hu => ?_
  rw [h.vertexSet_eq] at hu
  rcases hu with rfl | hu
  · exact Reaches.of_isLink h.isLink_newEdge₁
  · exact h.reaches (hG.reaches h.isLink.left_mem hu)

/-- **Deleting the new vertex gives back the old graph with the subdivided edge deleted.** The
two new edges have nowhere to run once `v` is gone, and no old edge is touched. -/
theorem deleteVerts_newVertex : G'.deleteVerts {v} = G.deleteEdges {e} := by
  refine Graph.ext ?_ fun f a b => ?_
  · rw [vertexSet_deleteVerts, h.vertexSet_eq, vertexSet_deleteEdges]
    ext z
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    exact ⟨fun hz => hz.1.resolve_left hz.2,
      fun hz => ⟨Or.inr hz, fun hh => h.newVertex_notMem (hh ▸ hz)⟩⟩
  · rw [deleteVerts_isLink, deleteEdges_isLink, h.isLink_iff]
    constructor
    · rintro ⟨hl | ⟨rfl, hs⟩ | ⟨rfl, hs⟩, ha, hb⟩
      · exact ⟨hl.1, by simpa using hl.2.1⟩
      · rcases Sym2.eq_iff.1 hs with ⟨-, rfl⟩ | ⟨rfl, -⟩
        exacts [absurd rfl hb, absurd rfl ha]
      · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨-, rfl⟩
        exacts [absurd rfl ha, absurd rfl hb]
    · rintro ⟨hl, hf⟩
      simp only [mem_singleton_iff] at hf
      exact ⟨Or.inl ⟨hl, hf, fun hh => h.newEdge₁_notMem (hh ▸ hl.edge_mem),
          fun hh => h.newEdge₂_notMem (hh ▸ hl.edge_mem)⟩,
        fun hh => h.newVertex_notMem (hh ▸ hl.left_mem),
        fun hh => h.newVertex_notMem (hh ▸ hl.right_mem)⟩

/-- Deleting an old vertex other than the subdivided edge's ends leaves a subdivision again. -/
theorem deleteVerts (hzx : z ≠ x) (hzy : z ≠ y) (hzv : z ≠ v) :
    IsSubdivisionOf (G'.deleteVerts {z}) (G.deleteVerts {z}) e x y v e₁ e₂ where
  isLink := (deleteVerts_isLink _ _).2 ⟨h.isLink, fun hh => hzx hh.symm, fun hh => hzy hh.symm⟩
  newVertex_notMem := by
    intro hv
    rw [vertexSet_deleteVerts] at hv
    exact h.newVertex_notMem hv.1
  newEdge₁_notMem := fun hf => h.newEdge₁_notMem (by
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
    exact ((deleteVerts_isLink _ _).1 hl).1.edge_mem)
  newEdge₂_notMem := fun hf => h.newEdge₂_notMem (by
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
    exact ((deleteVerts_isLink _ _).1 hl).1.edge_mem)
  newEdge_ne := h.newEdge_ne
  vertexSet_eq := by
    rw [vertexSet_deleteVerts, vertexSet_deleteVerts, h.vertexSet_eq]
    ext c
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hc, hcz⟩
      exacts [Or.inl rfl, Or.inr ⟨hc, hcz⟩]
    · rintro (rfl | ⟨hc, hcz⟩)
      exacts [⟨Or.inl rfl, fun hh => hzv hh.symm⟩, ⟨Or.inr hc, hcz⟩]
  isLink_iff := fun f a b => by
    rw [deleteVerts_isLink, h.isLink_iff, deleteVerts_isLink]
    constructor
    · rintro ⟨hl | ⟨rfl, hs⟩ | ⟨rfl, hs⟩, ha, hb⟩
      · exact Or.inl ⟨⟨hl.1, ha, hb⟩, hl.2⟩
      · exact Or.inr (Or.inl ⟨rfl, hs⟩)
      · exact Or.inr (Or.inr ⟨rfl, hs⟩)
    · rintro (⟨⟨hl, ha, hb⟩, hf⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩)
      · exact ⟨Or.inl ⟨hl, hf⟩, ha, hb⟩
      · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [⟨Or.inr (Or.inl ⟨rfl, rfl⟩), fun hh => hzx hh.symm, fun hh => hzv hh.symm⟩,
          ⟨Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩), fun hh => hzv hh.symm, fun hh => hzx hh.symm⟩]
      · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [⟨Or.inr (Or.inr ⟨rfl, rfl⟩), fun hh => hzv hh.symm, fun hh => hzy hh.symm⟩,
          ⟨Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩), fun hh => hzy hh.symm, fun hh => hzv hh.symm⟩]

/-- Deleting an end of the subdivided edge deletes that edge too, so the rest of the old graph
survives unchanged inside the subdivided one. -/
theorem deleteVerts_le_of_mem (hz : z = x ∨ z = y) :
    G.deleteVerts {z} ≤ G'.deleteVerts {z} where
  vertexSet_mono := by
    rw [vertexSet_deleteVerts, vertexSet_deleteVerts, h.vertexSet_eq]
    exact sdiff_subset_sdiff_left (subset_insert _ _)
  isLink_mono := by
    intro f a b hl
    rw [deleteVerts_isLink] at hl ⊢
    refine ⟨h.isLink_of_isLink hl.1 ?_, hl.2.1, hl.2.2⟩
    rintro rfl
    -- The subdivided edge is incident to `z`, so the deleted graph does not carry it.
    rcases h.isLink.eq_and_eq_or_eq_and_eq hl.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hz with rfl | rfl
    exacts [hl.2.1 rfl, hl.2.2 rfl, hl.2.2 rfl, hl.2.1 rfl]

/-- **Subdividing an edge keeps a graph 2-connected.** The hypothesis `x ≠ y` is not
decoration: a loop subdivides into a pendant pair, and deleting its base vertex strands the new
one — see the module docstring. -/
theorem isTwoConnected (hG : G.IsTwoConnected) (hxy : x ≠ y) : G'.IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.mono (by rw [h.vertexSet_eq]; exact subset_insert _ _)
  connected := h.connected hG.connected
  deleteVerts_connected := by
    intro z hz
    by_cases hzv : z = v
    · -- Deleting the new vertex undoes the subdivision, and the edge lies on a cycle.
      subst hzv
      rw [h.deleteVerts_newVertex]
      exact hG.connected.deleteEdges_singleton
        ((liesOnCycle_iff_deleteEdges_reaches h.isLink).2 (hG.no_bridge h.isLink))
    · -- An old vertex: everything reaches whichever end of the subdivided edge survives.
      have hzG : z ∈ V(G) := (h.vertexSet_eq ▸ hz : z ∈ insert v V(G)).resolve_left hzv
      have hconn := hG.deleteVerts_connected hzG
      by_cases hzx : z = x
      · -- `x` is the deleted vertex, so the hub is `y`, which the new vertex reaches by `e₂`.
        have hzy : z ≠ y := fun hh => hxy (hzx.symm.trans hh)
        have hhub : y ∈ V(G'.deleteVerts {z}) :=
          mem_deleteVerts_singleton_of_ne h.right_mem (Ne.symm hzy)
        refine Connected.of_hub hhub fun c hc => ?_
        rw [vertexSet_deleteVerts, h.vertexSet_eq] at hc
        rcases hc.1 with rfl | hc'
        · exact (Reaches.of_isLink ((deleteVerts_isLink _ _).2 ⟨h.isLink_newEdge₂,
            fun hh => hzv (mem_singleton_iff.1 hh).symm,
            fun hh => hzy (mem_singleton_iff.1 hh).symm⟩)).symm
        · refine Reaches.symm (Reaches.mono (h.deleteVerts_le_of_mem (Or.inl hzx)) ?_)
          exact hconn.reaches (mem_deleteVerts_singleton_of_ne hc' hc.2)
            (mem_deleteVerts_singleton_of_ne h.isLink.right_mem (Ne.symm hzy))
      · -- `x` survives and is the hub, which the new vertex reaches by `e₁`.
        have hhub : x ∈ V(G'.deleteVerts {z}) :=
          mem_deleteVerts_singleton_of_ne h.left_mem (Ne.symm hzx)
        refine Connected.of_hub hhub fun c hc => ?_
        rw [vertexSet_deleteVerts, h.vertexSet_eq] at hc
        rcases hc.1 with rfl | hc'
        · exact Reaches.of_isLink ((deleteVerts_isLink _ _).2 ⟨h.isLink_newEdge₁,
            fun hh => hzx (mem_singleton_iff.1 hh).symm,
            fun hh => hzv (mem_singleton_iff.1 hh).symm⟩)
        · have hcz : c ∈ V(G.deleteVerts {z}) := mem_deleteVerts_singleton_of_ne hc' hc.2
          have hxz : x ∈ V(G.deleteVerts {z}) :=
            mem_deleteVerts_singleton_of_ne h.isLink.left_mem (Ne.symm hzx)
          by_cases hzy : z = y
          · -- `y` is deleted, so the subdivided edge goes with it and the rest is unchanged.
            exact Reaches.mono (h.deleteVerts_le_of_mem (Or.inr hzy)) (hconn.reaches hxz hcz)
          · -- Both ends survive, so what is left is again a subdivision.
            exact (h.deleteVerts hzx hzy hzv).reaches (hconn.reaches hxz hcz)

end IsSubdivisionOf

end Graph
