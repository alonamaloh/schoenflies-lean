/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CellulationInvariants
import Schoenflies.JordanClosed
import Schoenflies.Graph.PathGraph

/-!
# Realizing a 2-cell split

`Schoenflies/CellulationInvariants.lean` proves the *step* theorems of the second elementary
operation: given a realization `R'` of `S.splitFace d` standing in the relation
`SplitData.IsCrosscutSplit` to a realization `R` of `S`, the two invariants of
`lem:cellulation-invariants` propagate. Nothing built such an `R'`. This module does.

## Blueprint

* `def:generated-structure`, operation 2 — the 2-cell split whose realization is constructed
  here.
* `lem:cellulation-invariants` (i), (vii) — the invariants that
  `SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` derives from the output of
  this module.
* `thm:general-crosscut` (`Schoenflies.crosscut_theorem`) — what turns the constructed ear into
  the two new open 2-cells; it is applied inside `IsCrosscutSplit.isRefinement`, and this module
  supplies its hypotheses.

## What is constructed

* `Schoenflies.CellStructure.SplitData.EarCrosscut` — the geometric input: an assignment of
  points to the ear's vertices and of parametrizations to the ear's edges, drawing the ear as a
  polygonal crosscut of the realized open 2-cell.
* `Schoenflies.CellStructure.SplitData.realize` — the realization of `S.splitFace d` built from
  `R` and such an ear. It is a `def` with lemmas, not an existential: `realize_pos`,
  `realize_drawing`, `realize_cell_of_old`, `realize_cell_face₁`, … name every component.
* `Schoenflies.CellStructure.SplitData.isCrosscutSplit_realize` — the constructed realization
  stands in the relation `IsCrosscutSplit` to `R`. Composed with
  `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the full induction step.

## The general lemmas this needed

Three facts about drawings and paths had no home on `main` and are proved here in the root
`Graph` namespace. If a second consumer appears they belong in `Schoenflies/Graph/`:

* `Graph.IsPath.map`, `Graph.walkVertices_map`, `Graph.IsPathGraph.map` — a path pushes forward
  along an injective relabelling of the vertices. `Graph.IsWalk.map` was already on `main` (in
  `Schoenflies/CombinatorialInvariance.lean`); the path version needs the injectivity, because
  the freshness clause is a *non*-membership.
* `Graph.IsDrawing.isArcBetween_walkPointSet` — **the point set of a drawn path is a simple
  arc between its two ends.** This is the workhorse: it is what makes the realized ear an arc
  (so `IsCrosscut` applies) and what makes each realized boundary path an arc (so `IsCutPair`
  applies). The induction is on `Graph.IsPath`, and the freshness clause of a path is exactly
  what rules out the returning point that would break `IsArcBetween.concatenate`.
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

theorem IsPathGraph.map {P : Graph α β} (hf : InjOn f V(P)) (h : P.IsPathGraph u W v) :
    (P.map f).IsPathGraph (f u) W (f v) where
  isPath := h.isPath.map hf
  edgeSet_eq := by rw [edgeSet_map]; exact h.edgeSet_eq
  vertexSet_eq := by rw [vertexSet_map, walkVertices_map, h.vertexSet_eq]

end Map

section Drawing

variable {β : Type*} {H K : Graph Plane β} {drw : β → ℝ → Plane}

/-! ### The point set of a drawn path

`Graph.pointSet` reads the vertex set and the edge set of a graph. Along a walk both are read
off the list instead, and that is the form the induction below runs on. -/

/-- The point set a walk occupies: the vertices it visits together with the arcs of its
edges. For a path graph this is the whole of `Graph.pointSet` (`walkPointSet_eq_pointSet`). -/
def walkPointSet (H : Graph Plane β) (drw : β → ℝ → Plane) (u : Plane) (W : List β) : Set Plane :=
  H.walkVertices u W ∪ ⋃ e ∈ ({e | e ∈ W} : Set β), edgeArc drw e

theorem walkPointSet_eq_pointSet {u v : Plane} {W : List β} (h : H.IsPathGraph u W v) :
    walkPointSet H drw u W = pointSet H drw := by
  rw [walkPointSet, pointSet, h.vertexSet_eq, h.edgeSet_eq]

theorem walkPointSet_nil (u : Plane) : walkPointSet H drw u ([] : List β) = {u} := by
  rw [walkPointSet, walkVertices_nil]
  simp

/-- Peeling the first step off a walk peels its arc off the point set. The vertex the step
departs from is an end of that arc, which is why nothing is left behind. -/
theorem walkPointSet_cons (hD : IsDrawing H drw) {e : β} {u w : Plane} {W : List β}
    (hl : H.IsLink e u w) :
    walkPointSet H drw u (e :: W) = edgeArc drw e ∪ walkPointSet H drw w W := by
  have hu : u ∈ edgeArc drw e := (hD.edge_isArcBetween hl).left_mem
  have hset : ({f | f ∈ e :: W} : Set β) = insert e {f | f ∈ W} := by
    ext f; simp [List.mem_cons]
  rw [walkPointSet, walkPointSet, walkVertices_cons hl, hset, Set.biUnion_insert]
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

end Drawing

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ## What a realization does to a walk

Two facts about an existing realization, both of the shape "the realized cells of a piece of
the skeleton occupy the point set that piece of the drawing occupies". They are what let the
crosscut theorem, which speaks of point sets, be fed from the cell structure, which speaks of
cells. -/

namespace Realization

variable (R : S.Realization)

theorem walkVertices_graph (u : γ) (W : List γ) :
    R.graph.walkVertices (R.pos u) W = R.pos '' S.skel.walkVertices u W :=
  Graph.walkVertices_map _ _ _

/-- **The realized cells of a path occupy the point set the drawn path occupies.** The two
differ only in the endpoints an open 1-cell drops, and those are the points of the 0-cells the
walk visits. -/
theorem cellUnion_pathCells {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    R.cellUnion (S.pathCells u W) = Graph.walkPointSet R.graph R.drawing (R.pos u) W := by
  have hsub : S.skel.walkVertices u W ⊆ V(S.skel) :=
    Graph.walkVertices_subset_vertexSet h.left_mem
  have hV : R.cellUnion (S.skel.walkVertices u W) = R.pos '' S.skel.walkVertices u W := by
    refine Set.Subset.antisymm (cellUnion_subset fun z hz => ?_) ?_
    · rw [R.cell_vertex (hsub hz)]
      exact Set.singleton_subset_iff.2 ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cell_subset_cellUnion hz (by rw [R.cell_vertex (hsub hz)]; rfl)
  rw [CellStructure.pathCells, cellUnion_union, hV, Graph.walkPointSet, R.walkVertices_graph]
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.union_subset (cellUnion_subset fun f hf => ?_) Set.subset_union_left
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    rw [R.cell_edge hl]
    exact fun x hx => Or.inr (Set.mem_biUnion hf hx.1)
  · refine Set.union_subset Set.subset_union_right (Set.iUnion₂_subset fun f hf x hx => ?_)
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · exact Or.inr ⟨a, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_left⟩, rfl⟩
      · exact Or.inr ⟨b, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_right⟩, rfl⟩
    · exact Or.inl (cell_subset_cellUnion hf (by rw [R.cell_edge hl]; exact ⟨hx, hxab⟩))

/-- The drawn skeleton is covered by the open cells of dimension 0 and 1. -/
theorem skeletonSet_subset_cellUnion :
    R.skeletonSet ⊆ R.cellUnion (V(S.skel) ∪ E(S.skel)) := by
  intro x hx
  rcases hx with hx | hx
  · rw [Realization.vertexSet_graph] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine cell_subset_cellUnion (Set.mem_union_left _ hz) ?_
    rw [R.cell_vertex hz]
    rfl
  · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx
    rw [Realization.edgeSet_graph] at hf
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.left_mem) ?_
        rw [R.cell_vertex hl.left_mem]
        rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.right_mem) ?_
        rw [R.cell_vertex hl.right_mem]
        rfl
    · refine cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
      rw [R.cell_edge hl]
      exact ⟨hxf, hxab⟩

/-- **An open 2-cell misses the drawn skeleton.** Immediate from the disjointness clause of
assertion (i): the skeleton is covered by cells of lower dimension. -/
theorem disjoint_cell_skeletonSet {D : Set Plane} (hcd : R.IsCellDecomposition D) {F : γ}
    (hF : F ∈ S.faces) : Disjoint (R.cell F) R.skeletonSet := by
  refine Set.disjoint_right.2 fun x hx hxF => ?_
  obtain ⟨σ, hσ, hxσ⟩ := mem_cellUnion_iff.1 (R.skeletonSet_subset_cellUnion hx)
  have hne : F ≠ σ := by
    rintro rfl
    rcases hσ with hσ | hσ
    exacts [Set.disjoint_left.1 S.disjoint_faces_vertexSet hF hσ,
      Set.disjoint_left.1 S.disjoint_faces_edgeSet hF hσ]
  have hσc : σ ∈ S.cells := by
    rcases hσ with hσ | hσ
    exacts [S.mem_cells_of_mem_vertexSet hσ, S.mem_cells_of_mem_edgeSet hσ]
  exact Set.disjoint_left.1 (hcd.disjoint (S.mem_cells_of_mem_faces hF) hσc hne) hxF hxσ

end Realization

end CellStructure

end Schoenflies
