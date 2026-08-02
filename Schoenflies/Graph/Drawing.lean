/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Curve
import Schoenflies.Topology
import Schoenflies.Bounded
import Schoenflies.Graph.Degree
import Mathlib.Combinatorics.Graph.Maps

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `closure_pointSet_diff_subset` — what a finite plane graph leaves outside a set accumulates
  only on its own vertices and arcs. Not a blueprint statement; it is how
  `thm:finite-transfer`(b) reads the blueprint's `K` off the transfer invariant.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
* `edgeArc_map`, `pointSet_map`, `IsDrawing.map_of_injOn` — a plane graph pushed forward along
  an injection continuous on what it occupies. Not a blueprint statement; it is what lets the
  target ear of `thm:finite-transfer` be *transported* rather than cut at parameters.
-/

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

/-- The point set of a single edge: the image of its parametrization on `[0, 1]`. -/
def edgeArc (drawing : β → ℝ → Plane) (e : β) : Set Plane := drawing e '' I

/-- A drawing of an abstract graph in the plane.

The vertices are already plane points, so a drawing only has to say how the edges run. -/
structure IsDrawing (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  /-- Each edge is drawn by an injective continuous parametrization on `[0, 1]` whose two
  endpoints are the ends of that edge.

  This says more than "the point set `edgeArc drawing e` is an arc between the ends". That
  weaker clause makes two drawings with the same point sets indistinguishable, which is fine
  for the face theory and useless for the redrawing argument: "the last parameter at which
  this edge is inside the square at `v`" is meaningless unless `drawing e` is itself the
  parametrization. `edge_isArcBetween` below recovers the weaker statement.

  Stated orientation-free — `G.IsLink e (drawing e 0) (drawing e 1)` — because `IsLink` is
  symmetric, so pinning `drawing e 0` to a *named* end of a *given* link would force the two
  ends to coincide. -/
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) I ∧ InjOn (drawing e) I ∧ G.IsLink e (drawing e 0) (drawing e 1)

  /-- An edge's arc meets the vertex set only at its own two ends. -/
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  /-- Two distinct edges meet only at vertices incident with both. -/
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p

namespace IsDrawing

/-- The point set of an edge is an arc between its two ends — the weaker reading of
`edge_param`, and the one the face theory uses. -/
theorem edge_isArcBetween (h : IsDrawing G drawing) ⦃e x y⦄ (hl : G.IsLink e x y) :
    IsArcBetween (edgeArc drawing e) x y := by
  obtain ⟨hc, hi, hlink⟩ := h.edge_param hl.edge_mem
  have base : IsArcBetween (edgeArc drawing e) (drawing e 0) (drawing e 1) :=
    ⟨drawing e, hc, hi, rfl, rfl, rfl⟩
  rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact base
  · exact base.reverse

theorem isArc_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsArc (edgeArc drawing e) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact (h.edge_isArcBetween hxy).isArc

theorem isCompact_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsCompact (edgeArc drawing e) := (h.isArc_edgeArc he).isCompact

/-- The blueprint's "distinct edges of a plane graph meet only at shared vertices". -/
theorem arcs_meet_at_vertex (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : e ≠ f) {p : Plane} (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    p ∈ V(G) :=
  (h.edge_inter he hf hef hpe hpf).1

/-- Away from the vertices, a point of the drawing lies on exactly one edge. This is the form
the polygonal overlay wants. -/
theorem unique_edge_at (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    {p : Plane} (hpV : p ∉ V(G)) (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    e = f := by
  by_contra hef
  exact hpV (h.arcs_meet_at_vertex he hf hef hpe hpf)

end IsDrawing

/-! ### What a plane graph occupies -/

/-- The point set of a plane graph: its vertices together with all of its edge arcs. -/
def pointSet (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  V(G) ∪ ⋃ e ∈ E(G), edgeArc drawing e

theorem vertexSet_subset_pointSet : V(G) ⊆ pointSet G drawing := subset_union_left

theorem edgeArc_subset_pointSet {e : β} (he : e ∈ E(G)) :
    edgeArc drawing e ⊆ pointSet G drawing :=
  subset_union_of_subset_right (subset_biUnion_of_mem he) _

/-- A finite plane graph occupies a compact set: finitely many points and finitely many
compact arcs. -/
theorem IsDrawing.isCompact_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsCompact (pointSet G drawing) := by
  refine (Graph.finite_vertexSet (G := G)).isCompact.union ?_
  exact (Graph.finite_edgeSet (G := G)).isCompact_biUnion fun e he => h.isCompact_edgeArc he

theorem IsDrawing.isClosed_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (pointSet G drawing) := h.isCompact_pointSet.isClosed

/-- **What a finite plane graph leaves outside a set accumulates only on its own pieces.**

The part of `|G|` outside `A` is contained in the vertices outside `A` together with the arcs of
the edges that are not inside `A`, and that is a *closed* set — finitely many points and finitely
many arcs — so the closure is contained in it too.

`thm:finite-transfer`(b) spends it on the blueprint's `K`, "the union of all old closed
nonboundary edges and the finitely many source ears already inserted", which is what the access
cone at a fresh anchor is shrunk away from: `a ∉ K` reduces by this to "no nonboundary edge of
the current subgraph passes through `a`", which is the anchor clause of the transfer invariant. -/
theorem closure_pointSet_diff_subset [G.Finite] (h : IsDrawing G drawing) (A : Set Plane) :
    closure (pointSet G drawing \ A) ⊆
      (V(G) \ A) ∪ ⋃ e ∈ {e | e ∈ E(G) ∧ ¬ edgeArc drawing e ⊆ A}, edgeArc drawing e := by
  refine closure_minimal (fun x hx => ?_) ?_
  · rcases hx.1 with hv | hedge
    · exact Or.inl ⟨hv, hx.2⟩
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hedge
    exact Or.inr (Set.mem_iUnion₂.2 ⟨e, ⟨he, fun hsub => hx.2 (hsub hxe)⟩, hxe⟩)
  refine IsClosed.union (Graph.finite_vertexSet G).sdiff.isClosed ?_
  refine Set.Finite.isClosed_biUnion ((Graph.finite_edgeSet G).subset fun e he => he.1)
    fun e he => ?_
  obtain ⟨p, q, hl⟩ := exists_isLink_of_mem_edgeSet he.1
  exact (h.edge_isArcBetween hl).isArc.isClosed

/-! ### A plane graph pushed forward

`Graph.map` relabels the vertices; the drawing that goes with the relabelled graph is the old
drawing composed with the same map. Everything a drawing asks for survives an injection that is
continuous on what the graph occupies. -/

section Map

variable {φ : Plane → Plane}

theorem edgeArc_map (e : β) : edgeArc (fun f => φ ∘ drawing f) e = φ '' edgeArc drawing e := by
  rw [edgeArc, edgeArc, Set.image_comp]

/-- A drawn graph pushed forward occupies the image of what it occupied. -/
theorem pointSet_map : pointSet (G.map φ) (fun f => φ ∘ drawing f) = φ '' pointSet G drawing := by
  rw [pointSet, pointSet, vertexSet_map, edgeSet_map, Set.image_union, Set.image_iUnion₂]
  exact congrArg _ (Set.iUnion₂_congr fun e _ => edgeArc_map e)

/-- **A plane graph pushed forward along an injection continuous on its point set is a plane
graph.** Every clause is the old clause pulled back through the injection: two points of the
image coincide only if their preimages do, which is what turns each of the three conditions
into its own image. -/
theorem IsDrawing.map_of_injOn (h : IsDrawing G drawing)
    (hcont : ContinuousOn φ (pointSet G drawing)) (hinj : InjOn φ (pointSet G drawing)) :
    IsDrawing (G.map φ) (fun f => φ ∘ drawing f) where
  edge_param := by
    intro e he
    rw [edgeSet_map] at he
    obtain ⟨hc, hi, hl⟩ := h.edge_param he
    have hsub : MapsTo (drawing e) I (pointSet G drawing) := fun t ht =>
      edgeArc_subset_pointSet he ⟨t, ht, rfl⟩
    exact ⟨hcont.comp hc hsub, hinj.comp hi hsub, hl.map φ⟩
  vertex_mem_edgeArc := by
    intro e x y vv hlk hv hmem
    obtain ⟨p, q, hpq, rfl, rfl⟩ := hlk
    rw [vertexSet_map] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    rw [edgeArc_map] at hmem
    obtain ⟨u, hu, heq⟩ := hmem
    obtain rfl : v' = u := hinj (vertexSet_subset_pointSet hv')
      (edgeArc_subset_pointSet hpq.edge_mem hu) heq.symm
    rcases h.vertex_mem_edgeArc hpq hv' hu with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [edgeSet_map] at he hf
    rw [edgeArc_map] at hpe hpf
    obtain ⟨x, hx, rfl⟩ := hpe
    obtain ⟨y, hy, heq⟩ := hpf
    have hxf : x ∈ edgeArc drawing f := by
      have hyx : y = x := hinj (edgeArc_subset_pointSet hf hy)
        (edgeArc_subset_pointSet he hx) heq
      rwa [hyx] at hy
    obtain ⟨hxV, hIe, hIf⟩ := h.edge_inter he hf hef hx hxf
    exact ⟨by rw [vertexSet_map]; exact ⟨x, hxV, rfl⟩, hIe.map φ, hIf.map φ⟩

end Map

/-- The exterior of a plane graph: everything the drawing does not occupy. -/
def exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  (pointSet G drawing)ᶜ

theorem IsDrawing.isOpen_exterior [G.Finite] (h : IsDrawing G drawing) :
    IsOpen (exterior G drawing) := h.isClosed_pointSet.isOpen_compl

/-- A face of a plane graph, named by a point of the exterior rather than indexed: no face has
to be produced before it can be spoken about. -/
def face (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) : Set Plane :=
  connectedComponentIn (exterior G drawing) base

theorem face_subset_exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) :
    face G drawing base ⊆ exterior G drawing :=
  connectedComponentIn_subset _ _

theorem mem_face (h : base ∈ exterior G drawing) : base ∈ face G drawing base :=
  mem_connectedComponentIn h

theorem IsDrawing.isOpen_face [G.Finite] (h : IsDrawing G drawing) (base : Plane) :
    IsOpen (face G drawing base) :=
  Schoenflies.Plane.isOpen_connectedComponentIn h.isOpen_exterior

theorem isConnected_face (h : base ∈ exterior G drawing) :
    IsConnected (face G drawing base) :=
  ⟨⟨base, mem_face h⟩, isPreconnected_connectedComponentIn⟩

/-- Faces partition the exterior: two faces either coincide or are disjoint. -/
theorem face_eq_or_disjoint (b c : Plane) :
    face G drawing b = face G drawing c ∨ Disjoint (face G drawing b) (face G drawing c) := by
  by_cases h : (face G drawing b ∩ face G drawing c).Nonempty
  · obtain ⟨z, hzb, hzc⟩ := h
    left
    rw [face, face, connectedComponentIn_eq hzb, connectedComponentIn_eq hzc]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

end Graph
