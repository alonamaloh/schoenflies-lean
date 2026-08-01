/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.CycleJordan
import Schoenflies.Subarc

/-!
# The utility graph, and the combinatorics of its nonplanarity

Placeholder docstring.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {x y : Fin 3 → α} {e : Fin 3 → Fin 3 → β}
variable {i j k l s t : Fin 3} {z : α}

/-- A copy of the utility graph `K(3,3)` inside `G`. -/
structure IsK33Config (G : Graph α β) (x y : Fin 3 → α) (e : Fin 3 → Fin 3 → β) : Prop where
  /-- `e i j` joins the `i`-th vertex of one side to the `j`-th vertex of the other. -/
  isLink : ∀ i j, G.IsLink (e i j) (x i) (y j)
  /-- The three vertices of the first side are distinct. -/
  x_injective : Function.Injective x
  /-- The three vertices of the second side are distinct. -/
  y_injective : Function.Injective y
  /-- The two sides are disjoint. -/
  ne : ∀ i j, x i ≠ y j

namespace IsK33Config

theorem x_ne_x (h : IsK33Config G x y e) (hik : i ≠ k) : x i ≠ x k :=
  fun he ↦ hik (h.x_injective he)

theorem y_ne_y (h : IsK33Config G x y e) (hjl : j ≠ l) : y j ≠ y l :=
  fun he ↦ hjl (h.y_injective he)

theorem x_ne_y (h : IsK33Config G x y e) (i j : Fin 3) : x i ≠ y j := h.ne i j

theorem y_ne_x (h : IsK33Config G x y e) (j i : Fin 3) : y j ≠ x i := (h.ne i j).symm

/-- **The nine edges carry nine different names.** This is not an axiom of the configuration:
an edge has only two ends, so two of the nine names being equal would force the two index
pairs to agree. -/
theorem eq_of_e_eq (h : IsK33Config G x y e) (heq : e i j = e k l) : i = k ∧ j = l := by
  have h' : G.IsLink (e i j) (x k) (y l) := by rw [heq]; exact h.isLink k l
  rcases (h.isLink i j).eq_and_eq_or_eq_and_eq h' with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨h.x_injective h1, h.y_injective h2⟩
  · exact absurd h1 (h.ne i l)

theorem e_ne (h : IsK33Config G x y e) (hne : ¬ (i = k ∧ j = l)) : e i j ≠ e k l :=
  fun heq ↦ hne (h.eq_of_e_eq heq)

/-- A vertex on one of the nine edges is one of that edge's two ends. -/
theorem inc_elim (h : IsK33Config G x y e) (hz : G.Inc (e i j) z) : z = x i ∨ z = y j :=
  hz.eq_or_eq_of_isLink (h.isLink i j)

/-- **Freshness, in the form the path constructor asks for.** A vertex which is neither the
source of the rest of the walk nor an end of any of its edges is not among the vertices that
rest visits. -/
theorem notMem_walkVertices (h : IsK33Config G x y e) {W : List β} {w : α} (hzw : z ≠ w)
    (hW : ∀ f ∈ W, ∃ i j, f = e i j ∧ z ≠ x i ∧ z ≠ y j) :
    z ∉ G.walkVertices w W := by
  intro hz
  rcases mem_walkVertices_iff.1 hz with rfl | ⟨f, hf, hinc⟩
  · exact hzw rfl
  obtain ⟨i, j, rfl, hxi, hyj⟩ := hW f hf
  rcases h.inc_elim hinc with hh | hh
  exacts [hxi hh, hyj hh]

end IsK33Config

/-! ### The six-cycle

The blueprint reads `K(3,3)` as the six-cycle `x₀y₀x₁y₁x₂y₂x₀` together with the three
remaining edges. The cycle is presented as `Schoenflies/Graph/Cycle.lean` presents one:
through the edge `e 0 0`, with a detour path running the other way round. -/

/-- The index pairs of the six edges of the six-cycle, in the order the cycle is traversed
starting from `e 0 0`. Kept as index pairs, not as edges, because every question about which
edges the cycle uses is then decidable. -/
def hexPairs : List (Fin 3 × Fin 3) := [(0, 0), (0, 2), (2, 2), (2, 1), (1, 1), (1, 0)]

/-- The five edges of the detour of the six-cycle: the path
`x₀ → y₂ → x₂ → y₁ → x₁ → y₀` that returns to the other end of `e 0 0`. -/
def hexDetour (e : Fin 3 → Fin 3 → β) : List β := [e 0 2, e 2 2, e 2 1, e 1 1, e 1 0]

/-- The six edges of the six-cycle. -/
def hexList (e : Fin 3 → Fin 3 → β) : List β := e 0 0 :: hexDetour e

theorem hexList_eq_map (e : Fin 3 → Fin 3 → β) :
    hexList e = hexPairs.map fun p ↦ e p.1 p.2 := rfl

theorem mem_hexList_iff {f : β} : f ∈ hexList e ↔ ∃ p ∈ hexPairs, f = e p.1 p.2 := by
  rw [hexList_eq_map]
  simp only [List.mem_map, eq_comm]

namespace IsK33Config

/-- The detour of the six-cycle is a path. Each freshness clause says that the vertex a step
departs from is none of the six vertices the rest of the detour meets. -/
theorem hexDetour_isPath (h : IsK33Config G x y e) : G.IsPath (x 0) (hexDetour e) (y 0) := by
  have h5 : G.IsPath (x 1) [e 1 0] (y 0) := .single (h.isLink 1 0) (h.x_ne_y 1 0)
  have h4 : G.IsPath (y 1) [e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 1 1).symm h5 (h.notMem_walkVertices (h.y_ne_x 1 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    exact ⟨1, 0, rfl, h.y_ne_x 1 1, h.y_ne_y (by decide)⟩
  have h3 : G.IsPath (x 2) [e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 1) h4 (h.notMem_walkVertices (h.x_ne_y 2 1) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 2 1⟩
    · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 2 0⟩
  have h2 : G.IsPath (y 2) [e 2 2, e 2 1, e 1 1, e 1 0] (y 0) := by
    refine .cons (h.isLink 2 2).symm h3 (h.notMem_walkVertices (h.y_ne_x 2 2) ?_)
    rintro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨2, 1, rfl, h.y_ne_x 2 2, h.y_ne_y (by decide)⟩
    · exact ⟨1, 1, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
    · exact ⟨1, 0, rfl, h.y_ne_x 2 1, h.y_ne_y (by decide)⟩
  refine .cons (h.isLink 0 2) h2 (h.notMem_walkVertices (h.x_ne_y 0 2) ?_)
  rintro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨2, 2, rfl, h.x_ne_x (by decide), h.x_ne_y 0 2⟩
  · exact ⟨2, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 1, rfl, h.x_ne_x (by decide), h.x_ne_y 0 1⟩
  · exact ⟨1, 0, rfl, h.x_ne_x (by decide), h.x_ne_y 0 0⟩

/-- **The six-cycle is a cycle**, presented through the edge `e 0 0`. -/
theorem hexagon_isCycleThrough (h : IsK33Config G x y e) :
    G.IsCycleThrough (e 0 0) (x 0) (y 0) (hexDetour e) := by
  refine ⟨h.isLink 0 0, h.hexDetour_isPath, ?_⟩
  simp only [hexDetour, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide), h.e_ne (by decide),
    h.e_ne (by decide)⟩

/-! ### The three remaining edges

`e s (s+1)`, for `s : Fin 3`, are the three edges of `K(3,3)` that the six-cycle leaves out. -/

/-- The three remaining edges are not edges of the six-cycle. -/
theorem chord_notMem_hexList (h : IsK33Config G x y e) (s : Fin 3) : e s (s + 1) ∉ hexList e := by
  intro hmem
  obtain ⟨p, hp, heq⟩ := mem_hexList_iff.1 hmem
  have key : ∀ (s : Fin 3) (p : Fin 3 × Fin 3), p ∈ hexPairs → ¬ (s = p.1 ∧ s + 1 = p.2) := by
    decide
  exact key s p hp (h.eq_of_e_eq heq)

/-- Two distinct remaining edges carry distinct names, and share no end. -/
theorem chord_ne (h : IsK33Config G x y e) (hst : s ≠ t) : e s (s + 1) ≠ e t (t + 1) :=
  h.e_ne (fun hc ↦ hst hc.1)

/-- The edges of the six-cycle are edges of the graph. -/
theorem hexList_edge_mem (h : IsK33Config G x y e) {f : β} (hf : f ∈ hexList e) : f ∈ E(G) := by
  obtain ⟨p, -, rfl⟩ := mem_hexList_iff.1 hf
  exact (h.isLink p.1 p.2).edge_mem

end IsK33Config

theorem mem_hexList (e : Fin 3 → Fin 3 → β) {p : Fin 3 × Fin 3} (hp : p ∈ hexPairs) :
    e p.1 p.2 ∈ hexList e :=
  mem_hexList_iff.2 ⟨p, hp, rfl⟩

end Graph

/-! ## The six-cycle drawn in the plane

Everything from here on is about a *drawing* of the configuration. Nothing in this section
uses more geometry than the three clauses of `Graph.IsDrawing`. -/

namespace Graph

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s t : Fin 3}

/-- The point set of the six-cycle of a drawn `K(3,3)`. -/
def hexSet (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) : Set Plane :=
  edgesCover drawing (hexList e)

namespace IsK33Config

/-- **The six-cycle of a drawn `K(3,3)` is a Jordan curve.** This is the blueprint's "the
six-cycle is a polygonal Jordan curve"; polygonality plays no part in it, and is needed only
where the *polygonal* Jordan curve theorem is applied to the result. -/
theorem hexagon_isJordanCurve (h : IsK33Config G x y e) (hd : IsDrawing G drawing) :
    IsJordanCurve (hexSet drawing e) :=
  hd.cycle_isJordanCurve h.hexagon_isCycleThrough

/-- The `i`-th vertex of the first side lies on the six-cycle. -/
theorem x_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (i : Fin 3) :
    x i ∈ hexSet drawing e := by
  have hp : ∀ i : Fin 3, ((i, i) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp i)) (hd.edge_isArcBetween (h.isLink i i)).left_mem

/-- The `j`-th vertex of the second side lies on the six-cycle. -/
theorem y_mem_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (j : Fin 3) :
    y j ∈ hexSet drawing e := by
  have hp : ∀ j : Fin 3, ((j, j) : Fin 3 × Fin 3) ∈ hexPairs := by decide
  exact mem_edgesCover (mem_hexList e (hp j)) (hd.edge_isArcBetween (h.isLink j j)).right_mem

/-- **Each of the three remaining edges is a crosscut of the six-cycle**: its arc meets the
cycle in exactly its own two ends. -/
theorem chord_inter_hexSet (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    edgeArc drawing (e s (s + 1)) ∩ hexSet drawing e = {x s, y (s + 1)} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro p ⟨hpe, hph⟩
    obtain ⟨f, hf, hpf⟩ := mem_edgesCover_iff.1 hph
    have hne : e s (s + 1) ≠ f := fun hc ↦ h.chord_notMem_hexList s (hc ▸ hf)
    obtain ⟨-, hinc, -⟩ :=
      hd.edge_inter (h.isLink s (s + 1)).edge_mem (h.hexList_edge_mem hf) hne hpe hpf
    exact h.inc_elim hinc
  · rintro p (rfl | rfl)
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).left_mem, h.x_mem_hexSet hd s⟩
    · exact ⟨(hd.edge_isArcBetween (h.isLink s (s + 1))).right_mem, h.y_mem_hexSet hd (s + 1)⟩

/-- The interior of a remaining edge, as the blueprint reads it: its arc without its two
ends. -/
theorem chord_openArc_eq (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (s : Fin 3) :
    openArc (drawing (e s (s + 1))) = edgeArc drawing (e s (s + 1)) \ {x s, y (s + 1)} := by
  obtain ⟨-, hi, hlink⟩ := hd.edge_param (h.isLink s (s + 1)).edge_mem
  have hpair : ({drawing (e s (s + 1)) 0, drawing (e s (s + 1)) 1} : Set Plane)
      = {x s, y (s + 1)} := by
    rcases hlink.eq_and_eq_or_eq_and_eq (h.isLink s (s + 1)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  rw [openArc_eq_diff hi, hpair]
  rfl

/-- **A remaining edge lies wholly off the six-cycle except at its ends.** -/
theorem chord_openArc_subset_compl (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : openArc (drawing (e s (s + 1))) ⊆ (hexSet drawing e)ᶜ := by
  rw [h.chord_openArc_eq hd s]
  rintro p ⟨hpe, hpn⟩ hph
  exact hpn ((h.chord_inter_hexSet hd s).subset ⟨hpe, hph⟩)

theorem chord_openArc_isPreconnected (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (s : Fin 3) : IsPreconnected (openArc (drawing (e s (s + 1)))) :=
  isPreconnected_Ioo.image _
    ((hd.edge_param (h.isLink s (s + 1)).edge_mem).1.mono Ioo_subset_I)

theorem chord_openArc_nonempty (s : Fin 3) :
    (openArc (drawing (e s (s + 1)))).Nonempty :=
  ⟨drawing (e s (s + 1)) (1 / 2), 1 / 2, by norm_num, rfl⟩

/-- **Each of the three remaining edges lies wholly on one side of the six-cycle**: its
interior, being connected and disjoint from the cycle, lies in a single connected component of
the complement. -/
theorem chord_openArc_subset_connectedComponentIn (h : IsK33Config G x y e)
    (hd : IsDrawing G drawing) (s : Fin 3) {p : Plane}
    (hp : p ∈ openArc (drawing (e s (s + 1)))) :
    openArc (drawing (e s (s + 1))) ⊆ connectedComponentIn (hexSet drawing e)ᶜ p :=
  (h.chord_openArc_isPreconnected hd s).subset_connectedComponentIn hp
    (h.chord_openArc_subset_compl hd s)

/-- **Two distinct remaining edges are disjoint.** Their four ends are distinct, and two
distinct edges of a plane graph meet only at a shared end. -/
theorem chords_disjoint (h : IsK33Config G x y e) (hd : IsDrawing G drawing) (hst : s ≠ t) :
    edgeArc drawing (e s (s + 1)) ∩ edgeArc drawing (e t (t + 1)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p ⟨hps, hpt⟩ ↦ ?_
  obtain ⟨-, hincs, hinct⟩ := hd.edge_inter (h.isLink s (s + 1)).edge_mem
    (h.isLink t (t + 1)).edge_mem (h.chord_ne hst) hps hpt
  have hne1 : s ≠ t := hst
  have hne2 : s + 1 ≠ t + 1 := fun hc ↦ hst (by simpa using hc)
  rcases h.inc_elim hincs with rfl | rfl <;> rcases h.inc_elim hinct with hh | hh
  · exact (h.x_ne_x hne1) hh
  · exact (h.x_ne_y s (t + 1)) hh
  · exact (h.y_ne_x (s + 1) t) hh
  · exact (h.y_ne_y hne2) hh

end IsK33Config

end Graph
