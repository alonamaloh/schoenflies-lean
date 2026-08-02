/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.StageCells
import Schoenflies.MatchedSplit
import Schoenflies.PolygonalCut

/-!
# One 2-cell split carries a whole stage

`Schoenflies.GeneratedPair` is the induction hypothesis of the transfer: the abstract structure,
its two realizations, the skeleton homeomorphism, and every invariant a later step reads. The
realization constructors, the skeleton map and the boundary-walk update each survive a 2-cell
split on their own; this module puts them together and shows **the bundle** survives it.

`Schoenflies.GeneratedPair.splitFace` is that constructor. Given a stage, the abstract split
data, and a drawing of the ear as a polygonal crosscut on *each* side together with the chosen
homeomorphism between the two drawn ears, it produces the next stage — all thirteen fields, no
hypothesis beyond those and the two facts about the ambient domains that no stage can supply
(`srcOuter ⊆ |Γ|` and its target twin, which weak admissibility gives, and which are recorded
as arguments only because they are read off two different fields).

## What each field costs

* `src`, `tgt`, `homeo` — `SplitData.realize` twice and `SplitData.splitHomeo`, all on `main`.
* assertions (i) and (vii), both sides — `isCellDecomposition_and_isFaceJordan_realize`, which
  is why (vii) had to become a field: the step theorem consumes it and reproduces it.
* `walks` — `BoundaryWalks.splitFace`, unconditional.
* `tgt_isPolygonal` and the `isPolygonal` clause of weak admissibility — the old edges keep
  their drawing, and each **ear** edge is a sub-arc of the drawn crosscut, which
  `EarCrosscut.polygonal` says is polygonal. That is
  `Schoenflies.IsArcBetween.isPolygonal_of_subset'`, and the primed form is needed rather than
  the original: an interior ear edge shares neither end with the crosscut.
* `outerSet_eq` — the split changes neither the outer graph nor its drawing, so
  `Graph.map_eq_of_eqOn` and `Graph.pointSet_congr` say the realized outer cycle is the old one.
* `cell_subset`, `skeletonSet_subset` — the new cells all sit inside the old open 2-cell, and
  `Realization.cell_subset_sdiff` puts that inside the open domain.

## Blueprint

* `Schoenflies.GeneratedPair.splitFace` — `def:generated-structure`, operation 2, as an
  operation on matched cellulations rather than on abstract structures: the induction step of
  `thm:finite-transfer`(a) step 3 once the geometry is in hand.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

namespace SplitData

variable {γ : Type*} {S : CellStructure γ} {d : S.SplitData} {R : S.Realization}
  {ep : γ → Plane} {ed : γ → ℝ → Plane} {outer dom : Set Plane}

/-- **Each edge of a drawn ear is polygonal.** It is a sub-arc of the drawn crosscut, which
`EarCrosscut.polygonal` says is polygonal — and it shares neither end with the crosscut when it
is an interior edge, which is exactly why `IsArcBetween.isPolygonal_of_subset'` had to be
proved. -/
theorem isPolygonal_edgeArc_of_mem_ear (hE : d.EarCrosscut R ep ed) ⦃e : γ⦄ (he : e ∈ E(d.ear)) :
    IsPolygonal (Graph.edgeArc ed e) := by
  obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have hlm : (d.earGraph ep).IsLink e (ep a) (ep b) := hl.map ep
  refine hE.isArcBetween_earSet.isPolygonal_of_subset' hE.polygonal
    (hE.isDrawing.edge_isArcBetween hlm) (EarCrosscut.edgeArc_subset_earSet he) fun h => ?_
  exact hE.isDrawing.not_isLoopAt e (ep a) (by rw [h] at hlm ⊢; exact hlm)

/-- **The ear's open cells sit inside the old open 2-cell**, which is where the two geometric
clauses of weak admissibility are read. -/
theorem splitCell_earEdge_subset_cell_face (hE : d.EarCrosscut R ep ed) ⦃e : γ⦄
    (he : e ∈ E(d.ear)) : d.splitCell R ep ed e ⊆ R.cell d.face := by
  rw [splitCell_earEdge he]
  rintro x ⟨hx, hxv⟩
  refine hE.subset_face ⟨EarCrosscut.edgeArc_subset_earSet he hx, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (rfl | rfl)
  · exact hxv ⟨d.source, d.source_mem_ear, hE.pos_source⟩
  · exact hxv ⟨d.target, d.target_mem_ear, hE.pos_target⟩

/-- **The drawn ear lies in the closed domain**: its interior is inside the old open 2-cell and
its two ends are old 0-cells. -/
theorem earSet_subset_dom (hE : d.EarCrosscut R ep ed) (hcd : R.IsCellDecomposition dom)
    (houter : outer ⊆ R.skeletonSet) (hK : R.skeletonSet ⊆ dom) : d.earSet ep ed ⊆ dom := by
  intro x hx
  by_cases hxe : x ∈ ({R.pos d.source, R.pos d.target} : Set Plane)
  · rcases hxe with rfl | rfl
    exacts [hK (R.pos_mem_skeletonSet d.source_mem_skel),
      hK (R.pos_mem_skeletonSet d.target_mem_skel)]
  · exact (Set.diff_subset.trans Set.diff_subset)
      (Realization.cell_subset_sdiff hcd houter d.face_mem (hE.subset_face ⟨hx, hxe⟩))

/-- **Weak admissibility survives a 2-cell split.** The clause `def:admissible-graph` imposes on
every intermediate stage of `def:generated-structure`, carried across the second elementary
operation. -/
theorem isWeaklyAdmissible_realize (hE : d.EarCrosscut R ep ed)
    (hcd : R.IsCellDecomposition dom) (hadm : R.IsWeaklyAdmissible outer dom)
    (houter : outer ⊆ R.skeletonSet) :
    (d.realize R ep ed hE).IsWeaklyAdmissible outer dom where
  isTwoConnected := hE.isTwoConnected_splitGraph hadm.isTwoConnected
  outerSet_eq := by
    have hmap : S.outerGraph.map (d.splitPos R ep) = S.outerGraph.map R.pos :=
      Graph.map_eq_of_eqOn fun z hz => hE.splitPos_eq (S.outerGraph_le.vertexSet_mono hz)
    have hpt : Graph.pointSet (S.outerGraph.map R.pos) (d.splitDrawing R ed)
        = Graph.pointSet (S.outerGraph.map R.pos) R.drawing :=
      Graph.pointSet_congr fun e he => edgeArc_splitDrawing_of_mem_skel
        (S.outerGraph_le.edgeSet_mono (by rwa [Graph.edgeSet_map] at he))
    show Graph.pointSet (S.outerGraph.map (d.splitPos R ep)) (d.splitDrawing R ed) = outer
    rw [hmap, hpt]
    exact hadm.outerSet_eq
  isPolygonal := by
    intro e he hout
    have he' : e ∈ E(S.skel) ∪ E(d.ear) := he
    rcases he' with he' | he'
    · rw [realize_drawing, edgeArc_splitDrawing_of_mem_skel he']
      exact hadm.isPolygonal he' hout
    · rw [realize_drawing, edgeArc_splitDrawing_of_mem_ear he']
      exact isPolygonal_edgeArc_of_mem_ear hE he'
  cell_subset := by
    intro e he hout
    have he' : e ∈ E(S.skel) ∪ E(d.ear) := he
    rcases he' with he' | he'
    · rw [realize_cell, splitCell_of_mem_cells (S.mem_cells_of_mem_edgeSet he')]
      exact hadm.cell_subset he' hout
    · rw [realize_cell]
      exact (splitCell_earEdge_subset_cell_face hE he').trans
        ((Realization.cell_subset_sdiff hcd houter d.face_mem).trans Set.diff_subset)
  skeletonSet_subset := by
    rw [skeletonSet_realize hE]
    exact Set.union_subset hadm.skeletonSet_subset
      (earSet_subset_dom hE hcd houter hadm.skeletonSet_subset)

/-- **Every edge of the split realization is polygonal**, once every edge of the old one was.
This is the target-side clause; on the source side it is false and `IsWeaklyAdmissible`
restricts it, correctly, to the nonboundary edges. -/
theorem isPolygonal_realize (hE : d.EarCrosscut R ep ed)
    (hpoly : ∀ ⦃e⦄, e ∈ E(S.skel) → IsPolygonal (Graph.edgeArc R.drawing e)) ⦃e : γ⦄
    (he : e ∈ E((S.splitFace d).skel)) :
    IsPolygonal (Graph.edgeArc (d.realize R ep ed hE).drawing e) := by
  have he' : e ∈ E(S.skel) ∪ E(d.ear) := he
  rcases he' with he' | he'
  · rw [realize_drawing, edgeArc_splitDrawing_of_mem_skel he']
    exact hpoly he'
  · rw [realize_drawing, edgeArc_splitDrawing_of_mem_ear he']
    exact isPolygonal_edgeArc_of_mem_ear hE he'

end SplitData

end CellStructure

/-! ### The stage -/

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

open CellStructure

/-- **One 2-cell split, as an operation on matched cellulations.**

Every field of the next stage, from the current one and a drawing of the ear as a polygonal
crosscut on each side. Nothing is assumed beyond that: the two `outer ⊆ |Γ|` arguments are
`Realization.outerSet_subset_skeletonSet` composed with `IsWeaklyAdmissible.outerSet_eq`, and
are taken as arguments only because rewriting the domain parameter of a `GeneratedPair` inside
the constructor is not type-correct. -/
noncomputable def GeneratedPair.splitFace (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : T.str.CombInvariants) (d : T.str.SplitData)
    {earPos₁ earPos₂ : γ → Plane} {earDraw₁ earDraw₂ : γ → ℝ → Plane}
    (hE₁ : d.EarCrosscut T.src earPos₁ earDraw₁) (hE₂ : d.EarCrosscut T.tgt earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)
    (hsrc : srcOuter ⊆ T.src.skeletonSet) (htgt : tgtOuter ⊆ T.tgt.skeletonSet) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom where
  str := T.str.splitFace d
  generated := T.generated.splitFace d
  src := d.realize T.src earPos₁ earDraw₁ hE₁
  tgt := d.realize T.tgt earPos₂ earDraw₂ hE₂
  homeo := d.splitHomeo T.homeo hE₁ hE₂ m
  src_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize hE₁ hS T.src_isCellDecomposition
      T.src_isFaceJordan).1
  tgt_isCellDecomposition :=
    (d.isCellDecomposition_and_isFaceJordan_realize hE₂ hS T.tgt_isCellDecomposition
      T.tgt_isFaceJordan).1
  src_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize hE₁ hS T.src_isCellDecomposition
      T.src_isFaceJordan).2.1
  tgt_isFaceJordan :=
    (d.isCellDecomposition_and_isFaceJordan_realize hE₂ hS T.tgt_isCellDecomposition
      T.tgt_isFaceJordan).2.1
  tgt_isPolygonal := SplitData.isPolygonal_realize hE₂ T.tgt_isPolygonal
  src_isWeaklyAdmissible :=
    SplitData.isWeaklyAdmissible_realize hE₁ T.src_isCellDecomposition
      T.src_isWeaklyAdmissible hsrc
  tgt_isWeaklyAdmissible :=
    SplitData.isWeaklyAdmissible_realize hE₂ T.tgt_isCellDecomposition
      T.tgt_isWeaklyAdmissible htgt
  walks := T.walks.splitFace d

@[simp] theorem GeneratedPair.splitFace_str (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : T.str.CombInvariants) (d : T.str.SplitData) {earPos₁ earPos₂ : γ → Plane}
    {earDraw₁ earDraw₂ : γ → ℝ → Plane} (hE₁ : d.EarCrosscut T.src earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut T.tgt earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)
    (hsrc : srcOuter ⊆ T.src.skeletonSet) (htgt : tgtOuter ⊆ T.tgt.skeletonSet) :
    (T.splitFace hS d hE₁ hE₂ m hsrc htgt).str = T.str.splitFace d := rfl

@[simp] theorem GeneratedPair.splitFace_src (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : T.str.CombInvariants) (d : T.str.SplitData) {earPos₁ earPos₂ : γ → Plane}
    {earDraw₁ earDraw₂ : γ → ℝ → Plane} (hE₁ : d.EarCrosscut T.src earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut T.tgt earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)
    (hsrc : srcOuter ⊆ T.src.skeletonSet) (htgt : tgtOuter ⊆ T.tgt.skeletonSet) :
    (T.splitFace hS d hE₁ hE₂ m hsrc htgt).src = d.realize T.src earPos₁ earDraw₁ hE₁ := rfl

@[simp] theorem GeneratedPair.splitFace_tgt (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : T.str.CombInvariants) (d : T.str.SplitData) {earPos₁ earPos₂ : γ → Plane}
    {earDraw₁ earDraw₂ : γ → ℝ → Plane} (hE₁ : d.EarCrosscut T.src earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut T.tgt earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)
    (hsrc : srcOuter ⊆ T.src.skeletonSet) (htgt : tgtOuter ⊆ T.tgt.skeletonSet) :
    (T.splitFace hS d hE₁ hE₂ m hsrc htgt).tgt = d.realize T.tgt earPos₂ earDraw₂ hE₂ := rfl

/-- **The new stage refines the old one along `SplitData.parent`, on both sides and by the same
map** — `lem:refinement-compatibility`(c) at a split, which is what
`Schoenflies.IsPartialTransferOf` asks of a step. -/
theorem GeneratedPair.refines_splitFace (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : T.str.CombInvariants) (d : T.str.SplitData) {earPos₁ earPos₂ : γ → Plane}
    {earDraw₁ earDraw₂ : γ → ℝ → Plane} (hE₁ : d.EarCrosscut T.src earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut T.tgt earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)
    (hsrc : srcOuter ⊆ T.src.skeletonSet) (htgt : tgtOuter ⊆ T.tgt.skeletonSet) :
    (T.splitFace hS d hE₁ hE₂ m hsrc htgt).src.Refines T.src d.parent ∧
      (T.splitFace hS d hE₁ hE₂ m hsrc htgt).tgt.Refines T.tgt d.parent :=
  ⟨(d.isCellDecomposition_and_isFaceJordan_realize hE₁ hS T.src_isCellDecomposition
      T.src_isFaceJordan).2.2,
    (d.isCellDecomposition_and_isFaceJordan_realize hE₂ hS T.tgt_isCellDecomposition
      T.tgt_isFaceJordan).2.2⟩

end Schoenflies
