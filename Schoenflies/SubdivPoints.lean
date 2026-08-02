/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SubdivStage
import Schoenflies.EarPaths
import Schoenflies.AnchorFace

/-!
# Making finitely many skeleton points into 0-cells

Step 1 of `thm:finite-transfer`(a) has to turn the given extension's vertices that lie on the
old skeleton into 0-cells of the cell structure, by edge subdivisions and nothing else. This
module is that induction, in the generality it is actually needed: **any** finite set of points
of `|Γ|` can be made a set of 0-cells by finitely many subdivisions of a generated pair.

Nothing here is geometric. The whole content is that

* a point of `|Γ|` is either already a 0-cell or an interior point of exactly one drawn edge
  (`Realization.mem_vertexSet_or_exists_cell`), and in the second case comes with a parameter
  strictly inside that edge (`Realization.exists_param_of_mem_cell`) — which is what
  `GeneratedPair.subdivideEdge` takes;
* an edge subdivision moves no point of the skeleton and loses no 0-cell, so the points already
  dealt with stay dealt with and the ones left are still on the skeleton.

`[Infinite γ]` is spent exactly where `EarStep` spends it: three fresh names per subdivision,
drawn by `Schoenflies.exists_fresh_list` from the complement of the current cells.

## Blueprint

* `Schoenflies.CellStructure.exists_subdivData` — one edge subdivision's abstract data, on fresh
  names, with the boundary walks corrected by `Schoenflies.substWalk`.
* `Schoenflies.GeneratedPair.exists_subdivide_at` — one point.
* `Schoenflies.GeneratedPair.exists_subdivide_finite` — `def:generated-structure`, operation 1,
  iterated: the "subdivide at all intersections" half of step 1 of `thm:finite-transfer`(a).
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*}

/-- **Three fresh names.** One subdivision consumes a name for the new 0-cell and two for the
new 1-cells, all outside the current cells and pairwise distinct — the six freshness fields of
`CellStructure.SubdivData`. -/
theorem exists_fresh_triple [Infinite γ] {s : Set γ} (hs : s.Finite) :
    ∃ x y z : γ, x ∉ s ∧ y ∉ s ∧ z ∉ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  classical
  obtain ⟨t, hts, hcard⟩ := hs.infinite_compl.exists_subset_card_eq 3
  obtain ⟨x, y, z, hxy, hxz, hyz, ht⟩ := Finset.card_eq_three.1 hcard
  exact ⟨x, y, z, hts (by simp [ht]), hts (by simp [ht]), hts (by simp [ht]), hxy, hxz, hyz⟩

namespace CellStructure

variable {S : CellStructure γ}

/-- **The abstract data of one edge subdivision, for a given edge and a given family of base
points.** The three names are fresh by `exists_fresh_triple`, and the corrected boundary walks
are `Schoenflies.substWalk`'s — which is the whole reason `newBoundary` can be a field at all.

Existentially packaged because the names are a choice; every property a consumer needs of that
choice is in the conclusion. -/
theorem exists_subdivData [Infinite γ] {e a b : γ} (hl : S.skel.IsLink e a b) (start : γ → γ) :
    ∃ d : S.SubdivData, d.edge = e ∧ d.left = a ∧ d.right = b ∧ d.boundaryStart = start := by
  classical
  obtain ⟨v, e₁, e₂, hv, h₁, h₂, hve₁, hve₂, h₁₂⟩ := exists_fresh_triple S.finite_cells
  exact ⟨{ edge := e, left := a, right := b, newVertex := v, newEdge₁ := e₁, newEdge₂ := e₂
           isLink := hl
           newVertex_notMem := hv
           newEdge₁_notMem := h₁
           newEdge₂_notMem := h₂
           newVertex_ne₁ := hve₁
           newVertex_ne₂ := hve₂
           newEdge_ne := h₁₂
           boundaryStart := start
           newBoundary := fun F => substWalk S.skel e a b e₁ e₂ (start F) (S.boundary F)
           newBoundary_isSubstWalk := fun _ _ hw => isSubstWalk_substWalk hl hw },
    rfl, rfl, rfl, rfl⟩

namespace Realization

variable {R : S.Realization} {p : Plane}

/-- **A point of the drawn skeleton is a 0-cell or an interior point of a 1-cell.** The drawn
skeleton is the vertex positions together with the edge arcs, and an edge arc is its own open
1-cell together with the positions of its two ends. -/
theorem mem_vertexSet_or_exists_cell (hp : p ∈ R.skeletonSet) :
    p ∈ V(R.graph) ∨ ∃ e ∈ E(S.skel), p ∈ R.cell e := by
  rcases hp with hv | he
  · exact Or.inl hv
  · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.1 he
    rw [Realization.edgeSet_graph] at he
    obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    by_cases hpc : p ∈ R.cell e
    · exact Or.inr ⟨e, he, hpc⟩
    · rw [R.cell_edge hl] at hpc
      simp only [mem_sdiff, not_and, not_not, mem_insert_iff, mem_singleton_iff] at hpc
      rw [Realization.vertexSet_graph]
      rcases hpc hpe with rfl | rfl
      exacts [Or.inl ⟨x, hl.left_mem, rfl⟩, Or.inl ⟨y, hl.right_mem, rfl⟩]

/-- **An interior point of a drawn 1-cell comes with a parameter strictly inside the unit
interval.** That parameter is what `SubdivData.realize` cuts the edge at, and the two open
conditions are what `GeneratedPair.subdivideEdge` asks for. -/
theorem exists_param_of_mem_cell {e x y : γ} (hl : S.skel.IsLink e x y) (hp : p ∈ R.cell e) :
    ∃ t ∈ Ioo (0 : ℝ) 1, R.drawing e t = p := by
  rw [R.cell_edge hl] at hp
  obtain ⟨⟨t, htI, hpt⟩, hends⟩ := hp
  -- The two ends of the parametrization are the two ends of the edge, in one order or the other,
  -- so neither `0` nor `1` can be the parameter of an interior point.
  have hlm : R.graph.IsLink e (R.pos x) (R.pos y) := hl.map R.pos
  have hpar : R.graph.IsLink e (R.drawing e 0) (R.drawing e 1) :=
    (R.isDrawing.edge_param (by rw [edgeSet_map]; exact hl.edge_mem)).2.2
  have hmem : ∀ s : ℝ, s = 0 ∨ s = 1 → R.drawing e s ∈ ({R.pos x, R.pos y} : Set Plane) := by
    rintro s (rfl | rfl) <;>
      rcases hlm.eq_and_eq_or_eq_and_eq hpar with ⟨h0, h1⟩ | ⟨h0, h1⟩
    exacts [Or.inl h0.symm, Or.inr h1.symm, Or.inr h1.symm, Or.inl h0.symm]
  refine ⟨t, ⟨lt_of_le_of_ne htI.1 fun h => ?_, lt_of_le_of_ne htI.2 fun h => ?_⟩, hpt⟩
  · exact hends (hpt ▸ hmem t (Or.inl h.symm))
  · exact hends (hpt ▸ hmem t (Or.inr h))

end Realization

end CellStructure

/-! ### The induction -/

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

open CellStructure

/-- **One point of the skeleton made a 0-cell.** Either it already is one, or it is an interior
point of a drawn 1-cell and one subdivision at the corresponding parameter makes it one.

Nothing is lost on the way and nothing extra is gained: the skeleton does not move, no old
0-cell stops being one, the only 0-cell added is the point itself, and both realizations refine
the old ones along the same parent map. The last clause is what lets a consumer conclude that
the 0-cells of the result are exactly the old ones together with the points it asked for. -/
theorem GeneratedPair.exists_subdivide_at [Infinite γ] (h₀ : S₀.CombInvariants)
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {p : Plane}
    (hp : p ∈ T.src.skeletonSet) :
    ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      T'.src.Refines T.src par ∧ T'.tgt.Refines T.tgt par ∧
        T'.src.skeletonSet = T.src.skeletonSet ∧
        V(T.src.graph) ⊆ V(T'.src.graph) ∧ p ∈ V(T'.src.graph) ∧
        V(T'.src.graph) ⊆ insert p V(T.src.graph) := by
  rcases Realization.mem_vertexSet_or_exists_cell hp with hv | ⟨e, he, hpe⟩
  · exact ⟨T, id, .refl _, .refl _, rfl, subset_rfl, hv, subset_insert _ _⟩
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  obtain ⟨t, ht, hpt⟩ := Realization.exists_param_of_mem_cell hl hpe
  obtain ⟨d, hde, -, -, hds⟩ := exists_subdivData hl T.walks.start
  have hgraph : (T.subdivideEdge (T.combInvariants h₀) d hds ht).src.graph
      = d.realizeGraph T.src t := rfl
  refine ⟨T.subdivideEdge (T.combInvariants h₀) d hds ht, d.parent, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (T.refines_subdivideEdge (T.combInvariants h₀) d hds ht).1
  · exact (T.refines_subdivideEdge (T.combInvariants h₀) d hds ht).2
  · exact T.skeletonSet_subdivideEdge (T.combInvariants h₀) d hds ht
  · rw [hgraph, SubdivData.realizeGraph_vertexSet]
    exact subset_insert _ _
  · rw [hgraph, SubdivData.realizeGraph_vertexSet, hde, hpt]
    exact mem_insert _ _
  · rw [hgraph, SubdivData.realizeGraph_vertexSet, hde, hpt]

/-- **Finitely many points of the skeleton made 0-cells.** The "subdivide at all intersections"
half of step 1 of `thm:finite-transfer`(a), for an arbitrary finite set of skeleton points: no
ear is inserted, the skeleton does not move, and the result refines the given pair along one
parent map.

The induction is over the set of points, not over the structure: a subdivision keeps every
0-cell it had, so a point already dealt with stays dealt with. -/
theorem GeneratedPair.exists_subdivide_finite [Infinite γ] (h₀ : S₀.CombInvariants)
    {Q : Set Plane} (hQ : Q.Finite) :
    ∀ T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom, Q ⊆ T.src.skeletonSet →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        T'.src.Refines T.src par ∧ T'.tgt.Refines T.tgt par ∧
          T'.src.skeletonSet = T.src.skeletonSet ∧
          V(T.src.graph) ⊆ V(T'.src.graph) ∧ Q ⊆ V(T'.src.graph) ∧
          V(T'.src.graph) ⊆ V(T.src.graph) ∪ Q := by
  induction Q, hQ using Set.Finite.induction_on with
  | empty =>
    exact fun T _ => ⟨T, id, .refl _, .refl _, rfl, subset_rfl, empty_subset _, subset_union_left⟩
  | @insert a s ha hs ih =>
    intro T hQK
    obtain ⟨T₁, par₁, hr₁, hr₁', hK₁, hV₁, haV, hV₁'⟩ :=
      T.exists_subdivide_at h₀ (hQK (mem_insert a s))
    obtain ⟨T₂, par₂, hr₂, hr₂', hK₂, hV₂, hsV, hV₂'⟩ :=
      ih T₁ (hK₁ ▸ (subset_insert a s).trans hQK)
    refine ⟨T₂, par₁ ∘ par₂, hr₂.trans hr₁, hr₂'.trans hr₁', hK₂.trans hK₁, hV₁.trans hV₂,
      insert_subset (hV₂ haV) hsV, hV₂'.trans (union_subset ?_ ?_)⟩
    · exact hV₁'.trans (insert_subset (mem_union_right _ (mem_insert a s)) subset_union_left)
    · exact subset_union_of_subset_right (subset_insert a s) _

/-! ### The same, driven from the target side

Direction (b) of `thm:finite-transfer` runs the whole argument the other way round: the given
extension refines `Γ'`, so step 1 has to make prescribed *target* points into 0-cells. The
subdivision itself is not symmetric — `GeneratedPair.subdivideEdge` cuts the source edge at a
parameter `t` and the target edge at `SubdivData.targetParam`, the parameter the skeleton
homeomorphism sends `t` to — so the target-driven statement needs its own proof.

It needs no inverse parameter, though, and that is the only thing worth saying about it.
`SkeletonHomeo.image_cell` turns a target point of an open 1-cell into a source point of the
same 1-cell, `Realization.exists_param_of_mem_cell` reads off the source parameter, and
`SubdivData.drawing_targetParam` — *the target edge at `targetParam g t` is where `g` sends the
source edge at `t`* — says the target subdivision point is the prescribed one on the nose. -/

/-- **One point of the target skeleton made a 0-cell.** The mirror of
`GeneratedPair.exists_subdivide_at`, for direction (b).

The last clause is for `thm:finite-transfer`(b) alone: the fresh anchors it inserts into the
outer cycle have to inherit `lem:cellulation-invariants`(vi) from the outer edge they are
inserted into, and `CellStructure.SubdivData.propagatesUniqueFace` is that inheritance in the
form that survives the iteration below. -/
theorem GeneratedPair.exists_subdivide_at_tgt [Infinite γ] (h₀ : S₀.CombInvariants)
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {q : Plane}
    (hq : q ∈ T.tgt.skeletonSet) :
    ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      T'.src.Refines T.src par ∧ T'.tgt.Refines T.tgt par ∧
        T'.tgt.skeletonSet = T.tgt.skeletonSet ∧
        V(T.tgt.graph) ⊆ V(T'.tgt.graph) ∧ q ∈ V(T'.tgt.graph) ∧
        V(T'.tgt.graph) ⊆ insert q V(T.tgt.graph) ∧
        CellStructure.PropagatesUniqueFace T'.str T.str par := by
  rcases Realization.mem_vertexSet_or_exists_cell hq with hv | ⟨e, he, hqe⟩
  · exact ⟨T, id, .refl _, .refl _, rfl, subset_rfl, hv, subset_insert _ _,
      CellStructure.propagatesUniqueFace_id _⟩
  -- The corresponding source point of the same open 1-cell.
  have hqim : q ∈ T.homeo.toFun '' T.src.cell e := by
    rw [T.homeo.image_cell (Set.mem_union_right _ he)]; exact hqe
  obtain ⟨p, hp, hpq⟩ := hqim
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  obtain ⟨t, ht, hpt⟩ := Realization.exists_param_of_mem_cell hl hp
  obtain ⟨d, hde, -, -, hds⟩ := exists_subdivData hl T.walks.start
  -- The target edge at the transferred parameter is exactly the prescribed point.
  have hqt : T.tgt.drawing d.edge (d.targetParam T.homeo t) = q := by
    rw [d.drawing_targetParam T.homeo (Set.Ioo_subset_Icc_self ht), hde, hpt, hpq]
  have hgraph : (T.subdivideEdge (T.combInvariants h₀) d hds ht).tgt.graph
      = d.realizeGraph T.tgt (d.targetParam T.homeo t) := rfl
  refine ⟨T.subdivideEdge (T.combInvariants h₀) d hds ht, d.parent, ?_, ?_, ?_, ?_, ?_, ?_,
    d.propagatesUniqueFace⟩
  · exact (T.refines_subdivideEdge (T.combInvariants h₀) d hds ht).1
  · exact (T.refines_subdivideEdge (T.combInvariants h₀) d hds ht).2
  · exact CellStructure.SubdivData.skeletonSet_realize (d.targetParam_mem_Ioo T.homeo ht)
  · rw [hgraph, SubdivData.realizeGraph_vertexSet]
    exact subset_insert _ _
  · rw [hgraph, SubdivData.realizeGraph_vertexSet, hqt]
    exact mem_insert _ _
  · rw [hgraph, SubdivData.realizeGraph_vertexSet, hqt]

/-- **Finitely many points of the target skeleton made 0-cells.** The "subdivide at all
intersections" half of step 1 of `thm:finite-transfer`(b). -/
theorem GeneratedPair.exists_subdivide_finite_tgt [Infinite γ] (h₀ : S₀.CombInvariants)
    {Q : Set Plane} (hQ : Q.Finite) :
    ∀ T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom, Q ⊆ T.tgt.skeletonSet →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        T'.src.Refines T.src par ∧ T'.tgt.Refines T.tgt par ∧
          T'.tgt.skeletonSet = T.tgt.skeletonSet ∧
          V(T.tgt.graph) ⊆ V(T'.tgt.graph) ∧ Q ⊆ V(T'.tgt.graph) ∧
          V(T'.tgt.graph) ⊆ V(T.tgt.graph) ∪ Q ∧
          CellStructure.PropagatesUniqueFace T'.str T.str par := by
  induction Q, hQ using Set.Finite.induction_on with
  | empty =>
    exact fun T _ => ⟨T, id, .refl _, .refl _, rfl, subset_rfl, empty_subset _, subset_union_left,
      CellStructure.propagatesUniqueFace_id _⟩
  | @insert a s ha hs ih =>
    intro T hQK
    obtain ⟨T₁, par₁, hr₁, hr₁', hK₁, hV₁, haV, hV₁', hp₁⟩ :=
      T.exists_subdivide_at_tgt h₀ (hQK (mem_insert a s))
    obtain ⟨T₂, par₂, hr₂, hr₂', hK₂, hV₂, hsV, hV₂', hp₂⟩ :=
      ih T₁ (hK₁ ▸ (subset_insert a s).trans hQK)
    refine ⟨T₂, par₁ ∘ par₂, hr₂.trans hr₁, hr₂'.trans hr₁', hK₂.trans hK₁, hV₁.trans hV₂,
      insert_subset (hV₂ haV) hsV, hV₂'.trans (union_subset ?_ ?_),
      hp₂.trans hp₁ fun _ hσ => hr₂'.parent_mem_cells hσ⟩
    · exact hV₁'.trans (insert_subset (mem_union_right _ (mem_insert a s)) subset_union_left)
    · exact subset_union_of_subset_right (subset_insert a s) _

end Schoenflies
