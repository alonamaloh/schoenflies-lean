/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.Drawing
import Schoenflies.Graph.Degree
import Schoenflies.Subarc

/-!
# The open edges of a plane graph are the components of what its vertices leave of it

A finite plane graph is *determined*, as far as adjacency goes, by two sets: the points it
occupies and the points that are its vertices. Nothing about the edges — how many there are,
what they are called, which arcs they run along — is extra information.

The reason is that `pointSet G drawing ∖ V(G)` breaks into the **open edges**
`Graph.openEdge G drawing e = edgeArc drawing e ∖ V(G)`, and that decomposition is the
decomposition into connected components:

* the pieces are pairwise disjoint — `IsDrawing.edge_inter`, a common point of two arcs is a
  vertex;
* each is connected and nonempty — it is an arc minus its two ends
  (`IsArcBetween.isConnected_diff`);
* each is open in the union — the *other* arcs are finitely many compacts, so their union is
  closed and misses this piece. This is the only place finiteness is spent, and it is spent
  essentially: an infinite plane graph can have an edge whose interior is a limit of others.

So two finite plane graphs occupying the same points with the same vertices have the same open
edges, hence the same closed edges (`IsArcBetween.closure_diff_eq`), hence the same pairs of
ends, hence the same adjacency.

## Why this is what step 1 of `thm:finite-transfer`(a) needed

`Schoenflies.commonSubdivision_of_adj_match` had to compare the drawn skeleton of a refined
stage with `Schoenflies.sourcePart` — the part of the extension graph lying on the old skeleton
— and the two are, by construction, two names for the same arcs. The obstruction was never
geometric: it was that a `GeneratedPair` draws its edges with names drawn from `γ` by the
freshness lemmas while `K ≤ H` forces `H`'s names, and there is no edge relabelling in Mathlib
or here. `Graph.IsTwoConnected.of_adj_congr` reduced 2-connectivity to adjacency;
`Graph.adj_congr_of_pointSet_eq` is what supplies the adjacency, and it needs to know nothing
whatever about cell structures, subdivisions or extensions.

## Blueprint

Not a numbered statement — it is one of the facts the manuscript uses silently whenever it says
"the same graph, drawn the same way". `Graph.adj_congr_of_pointSet_eq` is the form step 1
consumes.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β β₁ β₂ : Type*} {G : Graph Plane β} {G₁ : Graph Plane β₁} {G₂ : Graph Plane β₂}
  {drawing : β → ℝ → Plane} {d₁ : β₁ → ℝ → Plane} {d₂ : β₂ → ℝ → Plane}
  {e f : β} {p x y : Plane}

/-! ### The open edges -/

/-- **The open edge of `e`**: its arc without the vertices of the graph, which is its arc without
its own two ends (`openEdge_eq_diff`). Stated with `V(G)` rather than with the ends so that it
makes sense before an edge's ends have been named — which is what the decomposition below needs,
since the two graphs being compared name their ends differently. -/
def openEdge (G : Graph Plane β) (drawing : β → ℝ → Plane) (e : β) : Set Plane :=
  edgeArc drawing e \ V(G)

theorem openEdge_subset : openEdge G drawing e ⊆ edgeArc drawing e := diff_subset

/-- The vertices on an edge's arc are its own two ends, so the two readings agree. -/
theorem openEdge_eq_diff (h : IsDrawing G drawing) (hl : G.IsLink e x y) :
    openEdge G drawing e = edgeArc drawing e \ {x, y} := by
  refine Set.Subset.antisymm (fun p hp => ⟨hp.1, ?_⟩) fun p hp => ⟨hp.1, ?_⟩
  · rintro (rfl | rfl)
    exacts [hp.2 hl.left_mem, hp.2 hl.right_mem]
  · exact fun hv => hp.2 (h.vertex_mem_edgeArc hl hv hp.1)

theorem isConnected_openEdge (h : IsDrawing G drawing) (hl : G.IsLink e x y) :
    IsConnected (openEdge G drawing e) := by
  rw [openEdge_eq_diff h hl]
  exact (h.edge_isArcBetween hl).isConnected_diff

/-- **The closed edge is the closure of the open one**, which is how a shared open edge forces
two graphs to share the whole arc. -/
theorem closure_openEdge (h : IsDrawing G drawing) (hl : G.IsLink e x y) :
    closure (openEdge G drawing e) = edgeArc drawing e := by
  rw [openEdge_eq_diff h hl]
  exact (h.edge_isArcBetween hl).closure_diff_eq

/-- **The two ends are what the open edge is missing.** -/
theorem edgeArc_diff_openEdge (h : IsDrawing G drawing) (hl : G.IsLink e x y) :
    edgeArc drawing e \ openEdge G drawing e = {x, y} := by
  rw [openEdge_eq_diff h hl, sdiff_sdiff_right_self]
  exact Set.inter_eq_right.2 (Set.pair_subset (h.edge_isArcBetween hl).left_mem
    (h.edge_isArcBetween hl).right_mem)

/-- A point of one open edge is on no other edge's arc: a common point of two distinct arcs is a
vertex, and the open edge has none. -/
theorem notMem_edgeArc_of_mem_openEdge (h : IsDrawing G drawing) (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : f ≠ e) (hp : p ∈ openEdge G drawing e) : p ∉ edgeArc drawing f := fun hpf =>
  hp.2 (h.edge_inter he hf (Ne.symm hef) hp.1 hpf).1

/-- **What the vertices leave of a plane graph is exactly its open edges.** -/
theorem biUnion_openEdge (G : Graph Plane β) (drawing : β → ℝ → Plane) :
    ⋃ e ∈ E(G), openEdge G drawing e = pointSet G drawing \ V(G) := by
  ext z
  simp only [openEdge, pointSet, Set.mem_iUnion₂, Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨g, hg, hz, hzV⟩
    exact ⟨Or.inr ⟨g, hg, hz⟩, hzV⟩
  · rintro ⟨hzV' | ⟨g, hg, hzg⟩, hzV⟩
    · exact absurd hzV' hzV
    · exact ⟨g, hg, hzg, hzV⟩

/-! ### The decomposition is the decomposition into components

The two open sets of the separation argument, for a fixed edge `e`: the complement of all the
*other* arcs, and the complement of `e`'s own arc. Both are open because a finite union of edge
arcs is compact. Together they cover, and on `pointSet ∖ V(G)` they meet in nothing. -/

section Finite

variable [G.Finite]

/-- The complement of the union of the arcs other than `e` — open, and it cuts `e`'s open edge
out of `pointSet ∖ V(G)`. -/
theorem isOpen_compl_biUnion_edgeArc (h : IsDrawing G drawing) (e : β) :
    IsOpen ((⋃ f ∈ E(G) \ {e}, edgeArc drawing f)ᶜ) := by
  have hcl : IsClosed (⋃ f ∈ E(G) \ {e}, edgeArc drawing f) :=
    ((G.finite_edgeSet.subset Set.sdiff_subset).isCompact_biUnion
      fun f hf => h.isCompact_edgeArc hf.1).isClosed
  exact hcl.isOpen_compl

omit [G.Finite] in
/-- A point of one open edge misses every other arc, so it is in the complement of their
union — the open set that cuts this open edge out. -/
theorem mem_compl_biUnion_of_mem_openEdge (h : IsDrawing G drawing) (he : e ∈ E(G))
    (hp : p ∈ openEdge G drawing e) : p ∈ (⋃ f ∈ E(G) \ {e}, edgeArc drawing f)ᶜ := by
  intro hmem
  obtain ⟨g, hg, hpg⟩ := Set.mem_iUnion₂.1 hmem
  exact notMem_edgeArc_of_mem_openEdge h he hg.1 hg.2 hp hpg

/-- **A connected subset of `pointSet ∖ V(G)` meeting one open edge lies inside it.** This is
the whole of "the open edges are the connected components", in the form the comparison uses. -/
theorem subset_openEdge_of_isPreconnected (h : IsDrawing G drawing) (he : e ∈ E(G))
    {A : Set Plane} (hA : IsPreconnected A) (hAsub : A ⊆ pointSet G drawing \ V(G))
    (hmeet : (A ∩ openEdge G drawing e).Nonempty) : A ⊆ openEdge G drawing e := by
  set U : Set Plane := (⋃ f ∈ E(G) \ {e}, edgeArc drawing f)ᶜ with hU
  set W : Set Plane := (edgeArc drawing e)ᶜ with hW
  -- A point of `A` on `e`'s arc is on no other arc; one off it is in `W` outright.
  have hcover : A ⊆ U ∪ W := by
    intro q hq
    by_cases hqe : q ∈ edgeArc drawing e
    · exact Or.inl (mem_compl_biUnion_of_mem_openEdge h he ⟨hqe, (hAsub hq).2⟩)
    · exact Or.inr hqe
  -- Off every other arc, a point of `pointSet ∖ V(G)` has nowhere to be but `e`'s own arc.
  have hdisj : ¬ (A ∩ (U ∩ W)).Nonempty := by
    rintro ⟨q, hqA, hqU, hqW⟩
    refine hqW ?_
    obtain ⟨g, hg, hqg⟩ := Set.mem_iUnion₂.1 ((biUnion_openEdge G drawing) ▸ hAsub hqA)
    by_cases hge : g = e
    · exact hge ▸ hqg.1
    · exact absurd (Set.mem_iUnion₂.2 ⟨g, ⟨hg, hge⟩, hqg.1⟩) hqU
  intro q hq
  by_contra hqe
  obtain ⟨r, hrA, hre⟩ := hmeet
  exact hdisj (hA U W (isOpen_compl_biUnion_edgeArc h e)
    ((h.isCompact_edgeArc he).isClosed.isOpen_compl) hcover
    ⟨r, hrA, mem_compl_biUnion_of_mem_openEdge h he hre⟩
    ⟨q, hq, fun hqa => hqe ⟨hqa, (hAsub hq).2⟩⟩)

end Finite

/-! ### Two plane graphs occupying the same points, with the same vertices -/

section Compare

variable [G₁.Finite] [G₂.Finite]

/-- **Each open edge of one graph is an open edge of the other.** Both are connected subsets of
the same set, and each lies inside whichever piece of the other decomposition it meets. -/
theorem exists_openEdge_eq (h₁ : IsDrawing G₁ d₁) (h₂ : IsDrawing G₂ d₂)
    (hpt : pointSet G₁ d₁ = pointSet G₂ d₂) (hV : V(G₁) = V(G₂)) {e : β₁} (he : e ∈ E(G₁)) :
    ∃ f ∈ E(G₂), openEdge G₁ d₁ e = openEdge G₂ d₂ f := by
  obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨p, hp⟩ := (isConnected_openEdge h₁ hl).nonempty
  have hAeq : pointSet G₁ d₁ \ V(G₁) = pointSet G₂ d₂ \ V(G₂) := by rw [hpt, hV]
  have hsub₁ : openEdge G₁ d₁ e ⊆ pointSet G₁ d₁ \ V(G₁) := by
    rw [← biUnion_openEdge]; exact Set.subset_biUnion_of_mem he
  -- The piece of the second decomposition that carries `p`.
  obtain ⟨f, hf, hpf⟩ := Set.mem_iUnion₂.1 ((biUnion_openEdge G₂ d₂) ▸ hAeq ▸ hsub₁ hp)
  obtain ⟨x', y', hl'⟩ := exists_isLink_of_mem_edgeSet hf
  have hsub₂ : openEdge G₂ d₂ f ⊆ pointSet G₂ d₂ \ V(G₂) := by
    rw [← biUnion_openEdge]; exact Set.subset_biUnion_of_mem hf
  exact ⟨f, hf, Set.Subset.antisymm
    (subset_openEdge_of_isPreconnected h₂ hf (isConnected_openEdge h₁ hl).isPreconnected
      (hAeq ▸ hsub₁) ⟨p, hp, hpf⟩)
    (subset_openEdge_of_isPreconnected h₁ he (isConnected_openEdge h₂ hl').isPreconnected
      (hAeq ▸ hsub₂) ⟨p, hpf, hp⟩)⟩

/-- **Adjacency transports, one direction.** Equal open edges have equal closures, hence equal
arcs, hence equal pairs of ends — and a pair of ends is an adjacency. -/
theorem adj_of_adj_of_pointSet_eq (h₁ : IsDrawing G₁ d₁) (h₂ : IsDrawing G₂ d₂)
    (hpt : pointSet G₁ d₁ = pointSet G₂ d₂) (hV : V(G₁) = V(G₂)) {u v : Plane}
    (h : G₁.Adj u v) : G₂.Adj u v := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg', harc⟩ := exists_openEdge_eq h₁ h₂ hpt hV hg.edge_mem
  obtain ⟨u', v', hg''⟩ := exists_isLink_of_mem_edgeSet hg'
  have hends : ({u, v} : Set Plane) = {u', v'} := by
    rw [← edgeArc_diff_openEdge h₁ hg, ← edgeArc_diff_openEdge h₂ hg'',
      ← closure_openEdge h₁ hg, ← closure_openEdge h₂ hg'', harc]
  rcases Set.pair_eq_pair_iff.1 hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [⟨g', hg''⟩, ⟨g', hg''.symm⟩]

/-- **Two finite plane graphs occupying the same points, with the same vertices, have the same
adjacency.** This is what makes the edge names of a plane graph carry no information that
adjacency can see. -/
theorem adj_congr_of_pointSet_eq (h₁ : IsDrawing G₁ d₁) (h₂ : IsDrawing G₂ d₂)
    (hpt : pointSet G₁ d₁ = pointSet G₂ d₂) (hV : V(G₁) = V(G₂)) {u v : Plane} :
    G₁.Adj u v ↔ G₂.Adj u v :=
  ⟨adj_of_adj_of_pointSet_eq h₁ h₂ hpt hV, adj_of_adj_of_pointSet_eq h₂ h₁ hpt.symm hV.symm⟩

end Compare

end Graph
