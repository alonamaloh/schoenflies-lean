/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.PathGraph
import Schoenflies.Graph.TwoConnected
import Schoenflies.Graph.Drawing
import Schoenflies.Concatenate
import Schoenflies.Polygonal

/-!
# What a drawn walk occupies

`Graph.pointSet` reads the vertex set and the edge set of a graph. Along a walk both are read
off the edge *list* instead, and that is the form every induction along a walk runs on. This
module is `Graph.walkPointSet` and the two theorems that make it worth having:

* **the point set of a drawn path is a simple arc between its two ends**
  (`Graph.IsDrawing.isArcBetween_walkPointSet`) — the workhorse. It is what makes a realized ear
  an arc, so `IsCrosscut` applies, and what makes each realized boundary path an arc, so
  `IsCutPair` applies. The induction is on `Graph.IsPath`, and the freshness clause of a path is
  exactly what rules out the returning point that would break `IsArcBetween.concatenate`;
* **a drawn walk with polygonal edges is a polygonal set**
  (`Graph.IsDrawing.isPolygonal_walkPointSet`) — each step glues one more edge arc on at a point
  both pieces contain, which is the hypothesis of `Schoenflies.IsPolygonal.union`.

The relabelling section is here for the same reason: `Graph.IsWalk.map` was already on `main`
(in `Schoenflies/CombinatorialInvariance.lean`), but the *path* version needs injectivity,
because the freshness clause is a non-membership and only an injective map reflects one.

## Blueprint

Nothing here is a blueprint statement. `def:generated-structure` operation 2 and both directions
of `thm:finite-transfer` are what consume it: the ear of a 2-cell split is presented as a path,
and everything geometric asked of the ear is asked of what that path occupies.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

/-! ### Pushing a path forward along a relabelling -/

section Map

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v : α} {W : List β}

theorem coveredVertices_map (f : α → α') :
    (G.map f).coveredVertices W = f '' G.coveredVertices W := by
  ext x
  simp only [mem_coveredVertices_iff, map_inc, Set.mem_image]
  constructor
  · rintro ⟨e, he, v, hv, rfl⟩
    exact ⟨v, ⟨e, he, hv⟩, rfl⟩
  · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
    exact ⟨e, he, v, hv, rfl⟩

theorem walkVertices_map (f : α → α') (u : α) (W : List β) :
    (G.map f).walkVertices (f u) W = f '' G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_map, Set.image_insert_eq]

/-- **A path pushes forward along an injective relabelling.** Unlike `Graph.IsWalk.map` this
needs the injectivity: the freshness clause is a non-membership, and only an injective map
reflects it. -/
theorem IsPath.map (hf : InjOn f V(G)) (h : G.IsPath u W v) : (G.map f).IsPath (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.map f) ih ?_
    rw [walkVertices_map]
    rintro ⟨z, hz, hzf⟩
    have hzV : z ∈ V(G) := walkVertices_subset_vertexSet hW.isWalk.left_mem hz
    exact hfresh (hf hzV hl.left_mem hzf ▸ hz)

/-- Relabelling commutes with the union. Both sides resolve a shared edge name in favour of
the left-hand graph, and `Graph.map` keeps the edge set, so the two resolutions agree. -/
theorem map_union (G H : Graph α β) (f : α → α') :
    (G.union H).map f = (G.map f).union (H.map f) := by
  refine Graph.ext (by simp [Set.image_union]) fun e x y => ?_
  simp only [map_isLink, union_isLink, Relation.map_apply, edgeSet_map]
  constructor
  · rintro ⟨a, b, hab | ⟨he, hab⟩, rfl, rfl⟩
    · exact Or.inl ⟨a, b, hab, rfl, rfl⟩
    · exact Or.inr ⟨he, a, b, hab, rfl, rfl⟩
  · rintro (⟨a, b, hab, rfl, rfl⟩ | ⟨he, a, b, hab, rfl, rfl⟩)
    · exact ⟨a, b, Or.inl hab, rfl, rfl⟩
    · exact ⟨a, b, Or.inr ⟨he, hab⟩, rfl, rfl⟩

theorem IsPathGraph.map {P : Graph α β} (hf : InjOn f V(P)) (h : P.IsPathGraph u W v) :
    (P.map f).IsPathGraph (f u) W (f v) where
  isPath := h.isPath.map hf
  edgeSet_eq := by rw [edgeSet_map]; exact h.edgeSet_eq
  vertexSet_eq := by rw [vertexSet_map, walkVertices_map, h.vertexSet_eq]

end Map

section Drawing

variable {β : Type*} {H K : Graph Plane β} {drw : β → ℝ → Plane}

/-! ### The point set of a drawn walk -/

/-- The point set a walk occupies: the vertices it visits together with the arcs of its
edges. For a path graph this is the whole of `Graph.pointSet` (`walkPointSet_eq_pointSet`). -/
def walkPointSet (H : Graph Plane β) (drw : β → ℝ → Plane) (u : Plane) (W : List β) : Set Plane :=
  H.walkVertices u W ∪ ⋃ e ∈ ({e | e ∈ W} : Set β), edgeArc drw e

theorem walkPointSet_eq_pointSet {u v : Plane} {W : List β} (h : H.IsPathGraph u W v) :
    walkPointSet H drw u W = pointSet H drw := by
  rw [walkPointSet, pointSet, h.vertexSet_eq, h.edgeSet_eq]

/-- The point set a walk occupies is the point set of the subgraph it spans. -/
theorem pointSet_pathGraphOf {u v : Plane} {W : List β} (h : H.IsWalk u W v) :
    pointSet (H.pathGraphOf u W) drw = walkPointSet H drw u W := by
  rw [walkPointSet, pointSet, pathGraphOf_vertexSet, pathGraphOf_edgeSet h]

theorem walkPointSet_nil (u : Plane) : walkPointSet H drw u ([] : List β) = {u} := by
  rw [walkPointSet, walkVertices_nil]
  simp

/-- Peeling the first step off a walk peels its arc off the point set. The vertex the step
departs from is an end of that arc, which is why nothing is left behind. -/
theorem walkPointSet_cons (hD : IsDrawing H drw) {e : β} {u w : Plane} {W : List β}
    (hl : H.IsLink e u w) :
    walkPointSet H drw u (e :: W) = edgeArc drw e ∪ walkPointSet H drw w W := by
  have hu : u ∈ edgeArc drw e := (hD.edge_isArcBetween hl).left_mem
  rw [walkPointSet, walkPointSet, walkVertices_cons hl, setOf_mem_cons, Set.biUnion_insert]
  refine Set.Subset.antisymm ?_ ?_
  · rintro z (hz | hz)
    · rcases hz with rfl | hz
      · exact Or.inl hu
      · exact Or.inr (Or.inl hz)
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
  · rintro z (hz | hz | hz)
    · exact Or.inr (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr (Or.inr hz)

/-- **The point set of a drawn path is a simple arc between its two ends.**

The two pieces glued at each step are the arc of the first edge and the point set of the rest
of the path, and `IsArcBetween.concatenate` asks that they meet only at the vertex between
them. That is precisely the freshness clause of `Graph.IsPath`: the vertex the path departs
from is not among those the rest of it visits, and every point the first arc shares with the
rest of the drawing is a vertex the rest visits — a vertex by `vertex_mem_edgeArc` if it is
one of the rest's vertices, and by `edge_inter` if it lies on one of the rest's arcs. -/
theorem IsDrawing.isArcBetween_walkPointSet (hD : IsDrawing H drw) :
    ∀ {u v : Plane} {W : List β}, H.IsPath u W v → u ≠ v →
      IsArcBetween (walkPointSet H drw u W) u v := by
  intro u v W hp
  induction hp with
  | nil => exact fun h => absurd rfl h
  | @cons u w v e W hl hW hfresh ih =>
    intro _
    rw [walkPointSet_cons hD hl]
    have harc : IsArcBetween (edgeArc drw e) u w := hD.edge_isArcBetween hl
    by_cases hwv : w = v
    · subst hwv
      rw [hW.eq_nil_of_eq, walkPointSet_nil,
        Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.2 harc.right_mem)]
      exact harc
    · refine harc.concatenate (ih hwv) ?_
      intro z hz hz'
      -- every point the first arc shares with the rest is a vertex the rest visits
      have hzw : z ∈ H.walkVertices w W := by
        rcases hz' with hz' | hz'
        · exact hz'
        · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hz'
          have hfe : e ≠ f := by
            rintro rfl
            exact (List.nodup_cons.1 (IsPath.cons hl hW hfresh).nodup).1 hf
          exact mem_walkVertices_of_mem_covered ⟨f, hf,
            (hD.edge_inter hl.edge_mem (hW.isWalk.edge_mem hf) hfe hz hzf).2.2⟩
      have hzV : z ∈ V(H) := walkVertices_subset_vertexSet hW.isWalk.left_mem hzw
      rcases hD.vertex_mem_edgeArc hl hzV hz with rfl | rfl
      · exact absurd hzw hfresh
      · rfl

theorem IsDrawing.isArcBetween_pointSet (hD : IsDrawing H drw) {u v : Plane} {W : List β}
    (h : H.IsPathGraph u W v) (huv : u ≠ v) : IsArcBetween (pointSet H drw) u v := by
  rw [← walkPointSet_eq_pointSet h]
  exact hD.isArcBetween_walkPointSet h.isPath huv

/-- **A drawn walk with polygonal edges is a polygonal set.** Each step glues one more edge arc
on at a point both pieces contain, which is exactly the hypothesis of
`Schoenflies.IsPolygonal.union`. -/
theorem IsDrawing.isPolygonal_walkPointSet (hD : IsDrawing H drw) :
    ∀ {u v : Plane} {W : List β}, H.IsWalk u W v → (∀ e ∈ W, IsPolygonal (edgeArc drw e)) →
      IsPolygonal (walkPointSet H drw u W) := by
  intro u v W h
  induction h with
  | @nil x hx =>
    intro _
    rw [walkPointSet_nil]
    exact ⟨[x], (poly_singleton x).symm⟩
  | @cons u m v e W hl hW ih =>
    intro hpoly
    rw [walkPointSet_cons hD hl]
    refine (hpoly e (List.mem_cons_self ..)).union
      (ih fun f hf => hpoly f (List.mem_cons_of_mem _ hf)) ⟨m, ?_, ?_⟩
    · exact (hD.edge_isArcBetween hl).right_mem
    · exact Or.inl mem_walkVertices_self

end Drawing

end Graph
