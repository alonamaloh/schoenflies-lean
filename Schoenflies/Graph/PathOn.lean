/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.PathGraph
import Schoenflies.Graph.TwoConnected

/-!
# A path graph built from names, not carved out of an ambient graph

`Graph.pathGraphOf` cuts a path graph out of a graph that already has it. The ear of
`def:generated-structure`, operation 2, is the opposite situation: it has to be a path graph on
**fresh names**, chosen to be cells of no current structure, and there is no ambient graph
carrying them.

`Graph.pathOn u steps` builds it. A *step* is a pair `(e, w)` — take the edge named `e` and
arrive at the vertex named `w` — so the ear is a start vertex together with a list of steps, and
`Graph.isPathGraph_pathOn` says that on distinct names it is the path graph it looks like.

## Why not the shortcuts

* `Graph.map` relabels **vertices only** — Mathlib has no edge-relabelling and neither does this
  repo (see the note on `InitialCell.aux` in `Schoenflies/InitialGenerated.lean`), so the drawn
  ear cannot simply be pushed onto fresh names: its edge names would come along.
* Reusing the *drawn* ear's edge names is not open either. `Schoenflies.EarStep` quantifies over
  every partial transfer `T`, so nothing stops a current cell of `T` from carrying a name that
  the extension graph `H` also uses for an ear edge, and `SplitData.edge_fresh` would fail.

## Blueprint

* `Graph.pathOn`, `Graph.isPathGraph_pathOn` — the abstract ear of `def:generated-structure`,
  operation 2, on names the caller chooses.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {u w x y : α} {e f : β}

/-! ### One edge -/

/-- The graph with one edge `e` joining `u` to `w`, and nothing else. -/
def edgeGraph (e : β) (u w : α) : Graph α β where
  vertexSet := {u, w}
  edgeSet := {e}
  IsLink f x y := f = e ∧ s(x, y) = s(u, w)
  isLink_symm _ _ := { symm := fun _ _ h => ⟨h.1, Sym2.eq_swap.trans h.2⟩ }
  eq_or_eq_of_isLink_of_isLink := by
    rintro f a b c d ⟨-, hab⟩ ⟨-, hcd⟩
    have := Sym2.eq_iff.1 (hab.trans hcd.symm)
    tauto
  edge_mem_iff_exists_isLink f := by
    constructor
    · rintro rfl; exact ⟨u, w, rfl, rfl⟩
    · rintro ⟨a, b, rfl, -⟩; rfl
  left_mem_of_isLink := by
    rintro f a b ⟨-, hab⟩
    rcases Sym2.eq_iff.1 hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [mem_insert _ _, mem_insert_of_mem _ rfl]

@[simp] theorem edgeGraph_vertexSet : V(edgeGraph e u w) = {u, w} := rfl

@[simp] theorem edgeGraph_edgeSet : E(edgeGraph e u w) = {e} := rfl

theorem edgeGraph_isLink {f : β} {a b : α} :
    (edgeGraph e u w).IsLink f a b ↔ f = e ∧ s(a, b) = s(u, w) := Iff.rfl

theorem edgeGraph_isLink_self : (edgeGraph e u w).IsLink e u w := ⟨rfl, rfl⟩

/-! ### A chain of them -/

/-- **The path graph on chosen names.** `pathOn u steps` starts at `u` and, for each step
`(e, w)`, takes an edge named `e` to a vertex named `w`. -/
def pathOn (u : α) : List (β × α) → Graph α β
  | [] => noEdge {u} β
  | (e, w) :: rest => (edgeGraph e u w).union (pathOn w rest)

@[simp] theorem pathOn_nil : pathOn (β := β) u [] = noEdge {u} β := rfl

@[simp] theorem pathOn_cons {rest : List (β × α)} :
    pathOn u ((e, w) :: rest) = (edgeGraph e u w).union (pathOn w rest) := rfl

/-- The vertices of `pathOn` are its start together with the vertex of every step. -/
theorem vertexSet_pathOn : ∀ {u : α} {steps : List (β × α)},
    V(pathOn u steps) = insert u {z | z ∈ steps.map Prod.snd}
  | u, [] => by simp [pathOn]
  | u, (e, w) :: rest => by
    rw [pathOn_cons, vertexSet_union, edgeGraph_vertexSet, vertexSet_pathOn]
    ext z
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_setOf_eq, List.map_cons,
      List.mem_cons]
    tauto

/-- The edges of `pathOn` are the edge of every step. -/
theorem edgeSet_pathOn : ∀ {u : α} {steps : List (β × α)},
    E(pathOn u steps) = {g | g ∈ steps.map Prod.fst}
  | u, [] => by simp [pathOn]
  | u, (e, w) :: rest => by
    rw [pathOn_cons, edgeSet_union, edgeGraph_edgeSet, edgeSet_pathOn]
    ext g
    simp only [mem_union, mem_singleton_iff, mem_setOf_eq, List.map_cons, List.mem_cons]

/-- The first step of `pathOn` is a link of it. -/
theorem pathOn_isLink_cons {rest : List (β × α)} :
    (pathOn u ((e, w) :: rest)).IsLink e u w := Or.inl edgeGraph_isLink_self

/-- The rest of the chain sits inside the whole of it, as soon as the first edge is not one of
the rest's. -/
theorem pathOn_le_cons {rest : List (β × α)} (he : e ∉ rest.map Prod.fst) :
    pathOn w rest ≤ pathOn u ((e, w) :: rest) := by
  have hcompat : (edgeGraph e u w).Compatible (pathOn w rest) :=
    Compatible.of_disjoint_edgeSet (by
      rw [edgeGraph_edgeSet, edgeSet_pathOn, Set.disjoint_singleton_left]
      exact he)
  exact pathOn_cons ▸ hcompat.right_le_union

/-- A walk of a subgraph visits the same vertices in the ambient graph: its edges have the same
ends there. -/
theorem walkVertices_eq_of_le {H G : Graph α β} (hle : H ≤ G) {u v : α} {W : List β}
    (h : H.IsWalk u W v) : G.walkVertices u W = H.walkVertices u W := by
  ext z
  constructor
  · rintro (rfl | ⟨f, hf, y, hy⟩)
    · exact mem_walkVertices_self
    · exact mem_walkVertices_of_mem_covered ⟨f, hf, y, (hle.isLink_iff (h.edge_mem hf)).2 hy⟩
  · rintro (rfl | ⟨f, hf, y, hy⟩)
    · exact mem_walkVertices_self
    · exact mem_walkVertices_of_mem_covered ⟨f, hf, y, hle.isLink_mono hy⟩

/-- **`pathOn` is the path graph it looks like**, as soon as the names are distinct: the start
and the steps' vertices are pairwise distinct, and so are the steps' edges. -/
theorem isPathGraph_pathOn : ∀ {u : α} {steps : List (β × α)},
    (u :: steps.map Prod.snd).Nodup → (steps.map Prod.fst).Nodup →
    (pathOn u steps).IsPathGraph u (steps.map Prod.fst)
      ((steps.map Prod.snd).getLastD u)
  | u, [], _, _ => by
    refine ⟨.nil (by simp [pathOn]), by simp [pathOn], by simp [pathOn, Graph.walkVertices]⟩
  | u, (e, w) :: rest, hv, he => by
    rw [List.map_cons, List.map_cons, List.getLastD_cons]
    have hvrest : (w :: rest.map Prod.snd).Nodup := (List.nodup_cons.1 hv).2
    have herest : (rest.map Prod.fst).Nodup := (List.nodup_cons.1 (by simpa using he)).2
    have hefresh : e ∉ rest.map Prod.fst := (List.nodup_cons.1 (by simpa using he)).1
    have ih := isPathGraph_pathOn hvrest herest
    have hle : pathOn w rest ≤ pathOn u ((e, w) :: rest) := pathOn_le_cons hefresh
    have hlink : (pathOn u ((e, w) :: rest)).IsLink e u w := pathOn_isLink_cons
    have hveq : (pathOn u ((e, w) :: rest)).walkVertices w (rest.map Prod.fst)
        = (pathOn w rest).walkVertices w (rest.map Prod.fst) :=
      walkVertices_eq_of_le hle ih.isWalk
    have hunotin : u ∉ (pathOn u ((e, w) :: rest)).walkVertices w (rest.map Prod.fst) := by
      rw [hveq, ← ih.vertexSet_eq, vertexSet_pathOn]
      rintro (rfl | hmem)
      · exact (List.nodup_cons.1 hv).1 (by simp)
      · refine (List.nodup_cons.1 hv).1 ?_
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr hmem
    refine ⟨.cons hlink (ih.isPath.mono hle) hunotin, ?_, ?_⟩
    · rw [edgeSet_pathOn]; ext g; simp
    · rw [Graph.walkVertices_cons hlink, hveq, ← ih.vertexSet_eq, vertexSet_pathOn,
        vertexSet_pathOn]
      ext z
      simp only [mem_insert_iff, mem_setOf_eq, List.map_cons, List.mem_cons]

end Graph
