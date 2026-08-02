/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.StageCells
import Schoenflies.RealizeSubdivHomeo
import Schoenflies.MatchedSplit
import Schoenflies.PolygonalCut

/-!
# One edge subdivision carries a whole stage

The mirror of `Schoenflies/SplitStage.lean` for the *first* elementary operation of
`def:generated-structure`. `Schoenflies.GeneratedPair` is the induction hypothesis of the
transfer — the abstract structure, its two realizations, the skeleton homeomorphism, and every
invariant a later step reads — and `Schoenflies.GeneratedPair.subdivideEdge` carries all
thirteen fields across one edge subdivision.

## What each field costs

* `src`, `tgt`, `homeo` — `SubdivData.realize` twice and `SubdivData.realizeHomeo`, all on
  `main`. The two sides do **not** subdivide at the same parameter: the target cuts at
  `SubdivData.targetParam`, the parameter the skeleton homeomorphism sends `t` to, which is
  what `def:generated-structure` means by "the corresponding point is inserted".
* assertions (i) and (vii), both sides — `realize_isCellDecomposition_and_isFaceJordan`.
* `walks` — `BoundaryWalks.subdivideEdge`, which is why the data has to have been built with
  `boundaryStart` the invariant's own base points; that is the `hstart` argument.
* `tgt_isPolygonal` and the `isPolygonal` clause of weak admissibility — the old edges keep
  their drawing, and each half of the cut edge is a sub-arc of the whole, which
  `Schoenflies.IsArcBetween.isPolygonal_of_subset` says is polygonal. The *unprimed* form
  suffices here, unlike at the split: each half shares an end with the edge it was cut from.
* `outerSet_eq` — `SubdivData.outerSet_realize`, and this is the one clause that does not copy
  from the split. A split leaves `outerGraph` and its drawing untouched, so there the realized
  outer cycle is the old one by `Graph.map_eq_of_eqOn` and `Graph.pointSet_congr`. A subdivision
  sets `outerGraph := d.outer`, which genuinely differs from `S.outerGraph` when the subdivided
  edge is an outer edge (`SubdivData.outer_eq` covers only the other case). So the argument has
  to be that the two halves occupy exactly the old arc — the same computation
  `SubdivData.pointSet_realize` makes for the whole skeleton, made again for the outer cycle.
* `isTwoConnected` — `Graph.IsSubdivisionOf.isTwoConnected` through
  `SubdivData.isSubdivisionOf_realizeGraph`, whose `x ≠ y` side condition is looplessness of the
  drawn graph.
* `cell_subset`, `skeletonSet_subset` — the two halves sit inside the old open edge
  (`realizeCell_edge_eq`) and the skeleton does not move at all (`skeletonSet_realize`).

## An integrator note

`SubdivData.outer_vertexSet_of_mem` is the outer-cycle twin of `SubdivData.skeleton_vertexSet`
and belongs beside it in `Schoenflies/GeneratedStructure.lean`, next to
`SubdivData.outer_edgeSet_of_mem`, which is already there. It is here only because hoisting it
rebuilds everything below `GeneratedStructure.lean`.

## Blueprint

* `Schoenflies.GeneratedPair.subdivideEdge` — `def:generated-structure`, operation 1, as an
  operation on matched cellulations rather than on abstract structures. With
  `GeneratedPair.splitFace` it is what `Schoenflies.CommonSubdivision` (step 1 of
  `thm:finite-transfer`(a)) inducts with.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} {d : S.SubdivData} {R : S.Realization} {t : ℝ}
  {outer dom : Set Plane}

/-! ### The outer cycle of the subdivided structure

`SubdivData.outer` is `S.outerGraph` when the subdivided edge is not an outer edge and the
subdivided outer cycle when it is. `outer_edgeSet_of_mem` is on `main`; what the geometric
clauses need beside it is the vertex set, and the three ways of reading "this edge is not an
outer edge of the new structure". -/

/-- The subdivided outer cycle gains the new 0-cell, and nothing else. -/
theorem outer_vertexSet_of_mem (he : d.edge ∈ E(S.outerGraph)) :
    V(d.outer) = insert d.newVertex V(S.outerGraph) := by
  ext z
  simp only [SubdivData.outer, subdivGraph_vertexSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.outer_isLink he, and_true]
  tauto

/-- If the first half is a nonboundary edge of the new structure then the edge it was cut from
was a nonboundary edge of the old one — the two halves of an *outer* edge are outer. -/
theorem edge_notMem_outerGraph_of_newEdge₁ (h : d.newEdge₁ ∉ E(d.outer)) :
    d.edge ∉ E(S.outerGraph) := fun he =>
  h (by rw [d.outer_edgeSet_of_mem he]; exact Set.mem_insert _ _)

theorem edge_notMem_outerGraph_of_newEdge₂ (h : d.newEdge₂ ∉ E(d.outer)) :
    d.edge ∉ E(S.outerGraph) := fun he =>
  h (by rw [d.outer_edgeSet_of_mem he]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))

/-- A surviving edge that is nonboundary after the subdivision was nonboundary before it. -/
theorem notMem_outerGraph_of_notMem_outer {f : γ} (hfe : f ≠ d.edge) (h : f ∉ E(d.outer)) :
    f ∉ E(S.outerGraph) := fun hf => by
  by_cases he : d.edge ∈ E(S.outerGraph)
  · exact h (by
      rw [d.outer_edgeSet_of_mem he]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hf, hfe⟩))
  · exact h (by rw [d.outer_eq he]; exact hf)

section

variable (ht : t ∈ Ioo (0 : ℝ) 1)
include ht

/-! ### The subdivision does not move the outer cycle either

`SubdivData.pointSet_realize` says an edge subdivision leaves the realized 1-skeleton where it
was. The same is true of the realized outer cycle, and it needs its own proof: when the
subdivided edge is outer, the subdivided outer cycle is a genuinely different abstract graph,
and the content is that its two new edges occupy between them exactly the old arc. -/

omit ht in
/-- The realized outer cycle gains the new point as a vertex — which it already carried, as an
interior point of the subdivided arc. -/
theorem outerGraph_map_vertexSet_of_mem (he : d.edge ∈ E(S.outerGraph)) :
    V(d.outer.map (d.realizePos R t)) = insert (R.drawing d.edge t)
      V(S.outerGraph.map R.pos) := by
  rw [vertexSet_map, vertexSet_map, d.outer_vertexSet_of_mem he, image_insert_eq,
    realizePos_newVertex]
  exact congrArg _ (image_congr fun z hz =>
    realizePos_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hz))

/-- **An edge subdivision does not move the realized outer cycle.**

Unconditionally, whether or not the subdivided edge is an outer edge. This is what
`def:admissible-graph`'s `outerSet_eq` clause needs across the first elementary operation, and
it is the one clause of weak admissibility whose proof does not copy from the 2-cell split. -/
theorem outerSet_realize : (d.realize R t ht).outerSet = R.outerSet := by
  change pointSet (d.outer.map (d.realizePos R t)) (d.realizeDrawing R t) = R.outerSet
  by_cases he : d.edge ∈ E(S.outerGraph)
  · -- The subdivided edge is outer: the two halves replace it, and cover its arc.
    have hedge : (⋃ f ∈ E(S.outerGraph.map R.pos), edgeArc R.drawing f) =
        edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.outerGraph) \ {d.edge}, edgeArc R.drawing f := by
      rw [edgeSet_map, ← biUnion_insert, insert_sdiff_singleton, insert_eq_of_mem he]
    have hnew : (⋃ f ∈ E(d.outer.map (d.realizePos R t)), edgeArc (d.realizeDrawing R t) f) =
        edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.outerGraph) \ {d.edge}, edgeArc R.drawing f := by
      rw [edgeSet_map, d.outer_edgeSet_of_mem he, biUnion_insert, biUnion_insert,
        iUnion₂_congr (fun f (hf : f ∈ E(S.outerGraph) \ {d.edge}) =>
          edgeArc_of_ne (d := d) (R := R) (t := t)
            (d.ne_newEdge₁_of_mem_cells (S.mem_cells_of_mem_edgeSet
              (S.outerGraph_le.edgeSet_mono hf.1)))
            (d.ne_newEdge₂_of_mem_cells (S.mem_cells_of_mem_edgeSet
              (S.outerGraph_le.edgeSet_mono hf.1)))),
        ← union_assoc, edgeArc_new_union ht]
    have hM : R.drawing d.edge t ∈ edgeArc R.drawing d.edge := ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    rw [Realization.outerSet, pointSet, pointSet, hnew, hedge,
      outerGraph_map_vertexSet_of_mem he, insert_union,
      insert_eq_of_mem (mem_union_right _ (mem_union_left _ hM))]
  · -- The subdivided edge is not outer: neither the graph, nor the positions, nor the arcs of
    -- the outer cycle are touched.
    have hmap : d.outer.map (d.realizePos R t) = S.outerGraph.map R.pos := by
      rw [d.outer_eq he]
      exact map_eq_of_eqOn fun z hz =>
        realizePos_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hz)
    rw [hmap]
    refine pointSet_congr fun f hf => ?_
    rw [edgeSet_map] at hf
    have hfc : f ∈ S.cells :=
      S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hf)
    exact edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc) (d.ne_newEdge₂_of_mem_cells hfc)

/-! ### Polygonality of the two halves -/

omit ht in
/-- The drawn subdivided edge, as an arc between the positions of its two ends. -/
theorem isArcBetween_edge :
    IsArcBetween (edgeArc R.drawing d.edge) (R.pos d.left) (R.pos d.right) :=
  R.isDrawing.edge_isArcBetween (d.isLink_drawn_edge R)

/-- **Each half of a subdivided polygonal edge is polygonal.** Unlike an interior edge of a
drawn ear, a half shares an end with the arc it is cut from, so the unprimed
`IsArcBetween.isPolygonal_of_subset` applies. -/
theorem isPolygonal_edgeArc_newEdge₁ (hpoly : IsPolygonal (edgeArc R.drawing d.edge)) :
    IsPolygonal (edgeArc (d.realizeDrawing R t) d.newEdge₁) :=
  isArcBetween_edge.isPolygonal_of_subset hpoly (isArcBetween_newEdge₁ ht)
    (edgeArc_newEdge₁_subset ht) (d.newPos_ne_pos R ht d.isLink.left_mem).symm

theorem isPolygonal_edgeArc_newEdge₂ (hpoly : IsPolygonal (edgeArc R.drawing d.edge)) :
    IsPolygonal (edgeArc (d.realizeDrawing R t) d.newEdge₂) :=
  isArcBetween_edge.reverse.isPolygonal_of_subset hpoly (isArcBetween_newEdge₂ ht).reverse
    (edgeArc_newEdge₂_subset ht) (d.newPos_ne_pos R ht d.isLink.right_mem).symm

/-! ### The two geometric clauses -/

/-- Each half of the cut edge sits inside the old open 1-cell. -/
theorem realizeCell_newEdge₁_subset : d.realizeCell R t d.newEdge₁ ⊆ R.cell d.edge := by
  rw [realizeCell_edge_eq ht]
  exact subset_union_left.trans subset_union_left

theorem realizeCell_newEdge₂_subset : d.realizeCell R t d.newEdge₂ ⊆ R.cell d.edge := by
  rw [realizeCell_edge_eq ht]
  exact subset_union_right

omit ht in
/-- The drawn subdivided skeleton has no loop at the subdivided edge, which is the side
condition `Graph.IsSubdivisionOf.isTwoConnected` cannot do without. -/
theorem pos_left_ne_pos_right : R.pos d.left ≠ R.pos d.right := by
  intro h
  have hl := d.isLink_drawn_edge R
  rw [← h] at hl
  exact R.isDrawing.not_isLoopAt d.edge (R.pos d.left) hl

/-- **Weak admissibility survives an edge subdivision.** The clause `def:admissible-graph`
imposes on every intermediate stage of `def:generated-structure`, carried across the first
elementary operation. -/
theorem isWeaklyAdmissible_realize (hadm : R.IsWeaklyAdmissible outer dom) :
    (d.realize R t ht).IsWeaklyAdmissible outer dom where
  isTwoConnected :=
    (d.isSubdivisionOf_realizeGraph ht).isTwoConnected hadm.isTwoConnected pos_left_ne_pos_right
  outerSet_eq := by rw [outerSet_realize ht]; exact hadm.outerSet_eq
  isPolygonal := by
    intro e he hout
    have he' : e ∈ insert d.newEdge₁ (insert d.newEdge₂ (E(S.skel) \ {d.edge})) := by
      rwa [subdivideEdge_skel, d.skeleton_edgeSet] at he
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff] at he'
    rw [realize_drawing]
    rcases he' with rfl | rfl | ⟨heS, hee⟩
    · exact isPolygonal_edgeArc_newEdge₁ ht
        (hadm.isPolygonal d.edge_mem_edgeSet (edge_notMem_outerGraph_of_newEdge₁ hout))
    · exact isPolygonal_edgeArc_newEdge₂ ht
        (hadm.isPolygonal d.edge_mem_edgeSet (edge_notMem_outerGraph_of_newEdge₂ hout))
    · rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells (S.mem_cells_of_mem_edgeSet heS))
        (d.ne_newEdge₂_of_mem_cells (S.mem_cells_of_mem_edgeSet heS))]
      exact hadm.isPolygonal heS (notMem_outerGraph_of_notMem_outer hee hout)
  cell_subset := by
    intro e he hout
    have he' : e ∈ insert d.newEdge₁ (insert d.newEdge₂ (E(S.skel) \ {d.edge})) := by
      rwa [subdivideEdge_skel, d.skeleton_edgeSet] at he
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff] at he'
    rw [realize_cell]
    rcases he' with rfl | rfl | ⟨heS, hee⟩
    · exact (realizeCell_newEdge₁_subset ht).trans
        (hadm.cell_subset d.edge_mem_edgeSet (edge_notMem_outerGraph_of_newEdge₁ hout))
    · exact (realizeCell_newEdge₂_subset ht).trans
        (hadm.cell_subset d.edge_mem_edgeSet (edge_notMem_outerGraph_of_newEdge₂ hout))
    · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_edgeSet heS)]
      exact hadm.cell_subset heS (notMem_outerGraph_of_notMem_outer hee hout)
  skeletonSet_subset := by
    rw [skeletonSet_realize ht]; exact hadm.skeletonSet_subset

/-- **Every edge of the subdivided realization is polygonal**, once every edge of the old one
was. This is the target-side clause; on the source side it is false and `IsWeaklyAdmissible`
restricts it, correctly, to the nonboundary edges. -/
theorem isPolygonal_realize
    (hpoly : ∀ ⦃e⦄, e ∈ E(S.skel) → IsPolygonal (edgeArc R.drawing e)) ⦃e : γ⦄
    (he : e ∈ E((S.subdivideEdge d).skel)) :
    IsPolygonal (edgeArc (d.realize R t ht).drawing e) := by
  have he' : e ∈ insert d.newEdge₁ (insert d.newEdge₂ (E(S.skel) \ {d.edge})) := by
    rwa [subdivideEdge_skel, d.skeleton_edgeSet] at he
  simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff] at he'
  rw [realize_drawing]
  rcases he' with rfl | rfl | ⟨heS, hee⟩
  · exact isPolygonal_edgeArc_newEdge₁ ht (hpoly d.edge_mem_edgeSet)
  · exact isPolygonal_edgeArc_newEdge₂ ht (hpoly d.edge_mem_edgeSet)
  · rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells (S.mem_cells_of_mem_edgeSet heS))
      (d.ne_newEdge₂_of_mem_cells (S.mem_cells_of_mem_edgeSet heS))]
    exact hpoly heS

end

end SubdivData

end CellStructure

/-! ### The stage -/

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

open CellStructure

/-- **One edge subdivision, as an operation on matched cellulations.**

Every field of the next stage, from the current one, the abstract subdivision data and a
parameter `t` strictly inside the drawn source edge. Nothing is assumed beyond that and
`hstart`, which says the data was built with the boundary-walk invariant's own base points —
`BoundaryWalks.subdivideEdge` cannot do without it, and no closed form supplies it.

The target side is subdivided at `SubdivData.targetParam`, not at `t`: the two realizations
draw the same edge differently, and the point that corresponds to `R.drawing e t` is the one the
skeleton homeomorphism sends it to. -/
noncomputable def GeneratedPair.subdivideEdge
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (hS : T.str.CombInvariants)
    (d : T.str.SubdivData) (hstart : d.boundaryStart = T.walks.start) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := T.str.subdivideEdge d
  generated := T.generated.subdivideEdge d
  src := d.realize T.src t ht
  tgt := d.realize T.tgt (d.targetParam T.homeo t) (d.targetParam_mem_Ioo T.homeo ht)
  homeo := d.realizeHomeo T.homeo ht
  src_isCellDecomposition :=
    (d.realize_isCellDecomposition_and_isFaceJordan ht hS T.src_isCellDecomposition
      T.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo T.homeo ht) hS
      T.tgt_isCellDecomposition T.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.realize_isCellDecomposition_and_isFaceJordan ht hS T.src_isCellDecomposition
      T.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo T.homeo ht) hS
      T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.1
  tgt_isPolygonal :=
    SubdivData.isPolygonal_realize (d.targetParam_mem_Ioo T.homeo ht) T.tgt_isPolygonal
  src_isWeaklyAdmissible := SubdivData.isWeaklyAdmissible_realize ht T.src_isWeaklyAdmissible
  tgt_isWeaklyAdmissible :=
    SubdivData.isWeaklyAdmissible_realize (d.targetParam_mem_Ioo T.homeo ht)
      T.tgt_isWeaklyAdmissible
  walks := T.walks.subdivideEdge d hstart

@[simp] theorem GeneratedPair.subdivideEdge_str
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (hS : T.str.CombInvariants)
    (d : T.str.SubdivData) (hstart : d.boundaryStart = T.walks.start) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (T.subdivideEdge hS d hstart ht).str = T.str.subdivideEdge d := rfl

@[simp] theorem GeneratedPair.subdivideEdge_src
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (hS : T.str.CombInvariants)
    (d : T.str.SubdivData) (hstart : d.boundaryStart = T.walks.start) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (T.subdivideEdge hS d hstart ht).src = d.realize T.src t ht := rfl

@[simp] theorem GeneratedPair.subdivideEdge_tgt
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (hS : T.str.CombInvariants)
    (d : T.str.SubdivData) (hstart : d.boundaryStart = T.walks.start) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (T.subdivideEdge hS d hstart ht).tgt =
      d.realize T.tgt (d.targetParam T.homeo t) (d.targetParam_mem_Ioo T.homeo ht) := rfl

/-- **The new stage refines the old one along `SubdivData.parent`, on both sides and by the same
map** — `lem:refinement-compatibility`(c) at a subdivision, which is what
`Schoenflies.IsPartialTransferOf` asks of a step. -/
theorem GeneratedPair.refines_subdivideEdge
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (hS : T.str.CombInvariants)
    (d : T.str.SubdivData) (hstart : d.boundaryStart = T.walks.start) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (T.subdivideEdge hS d hstart ht).src.Refines T.src d.parent ∧
      (T.subdivideEdge hS d hstart ht).tgt.Refines T.tgt d.parent :=
  ⟨(d.realize_isCellDecomposition_and_isFaceJordan ht hS T.src_isCellDecomposition
      T.src_isFaceJordan).2.2,
    (d.realize_isCellDecomposition_and_isFaceJordan (d.targetParam_mem_Ioo T.homeo ht) hS
      T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2⟩

/-- **An edge subdivision does not move the source skeleton.** The clause
`Schoenflies.IsPartialTransferOf` carries about the current subgraph therefore survives a
subdivision unchanged, which is what makes step 1 an induction over new points rather than over
subgraphs. -/
theorem GeneratedPair.skeletonSet_subdivideEdge
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (hS : T.str.CombInvariants)
    (d : T.str.SubdivData) (hstart : d.boundaryStart = T.walks.start) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (T.subdivideEdge hS d hstart ht).src.skeletonSet = T.src.skeletonSet :=
  CellStructure.SubdivData.skeletonSet_realize ht

end Schoenflies
