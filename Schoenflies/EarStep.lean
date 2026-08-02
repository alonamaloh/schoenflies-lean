/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.EarTarget
import Schoenflies.SplitStage

/-!
# Step 3 of `thm:finite-transfer`(a): one ear insertion

`Schoenflies.EarStep` was a named hypothesis of `Schoenflies.transfer_of_ears`. This module
discharges it.

## The proof, in one paragraph

The ear either brings a new edge or it does not. If it does not, some edge of it is already an
edge of `B`, hence has both ends in `V(B)`, hence — by the freshness of the ear's interior —
both ends among the two prescribed ones; a path with an edge joining its own two ends is that
one edge, so `B ∪ ear = B` and there is nothing to do
(`Schoenflies.isPartialTransferOf_union_of_mem_edgeSet`).

Otherwise `Schoenflies.exists_earCrosscut` places the ear: it is drawn where `H` draws
it, its interior misses the current skeleton and so lies in a single current 2-cell, whose
boundary cycle cuts at the ear's two ends into the two boundary paths. That gives the abstract
`CellStructure.SplitData` and the source `SplitData.EarCrosscut`. On the target side,
`Schoenflies.exists_target_ear` produces the polygonal crosscut of the corresponding 2-cell and
`Schoenflies.exists_target_earCrosscut` draws the ear along it, together with the chosen
homeomorphism between the two drawn ears. `Schoenflies.GeneratedPair.splitFace` then produces
the next stage, and the four clauses of `Schoenflies.IsPartialTransferOf` are read off it.

## What is assumed, and why it is not about the stage

Four hypotheses beyond `IsSourceExtension`, and none of them mentions the intermediate stage `T`
that `EarStep` quantifies over: they say the two ambient domains are closed Jordan regions, in
the only form used — `dom ∖ outer` is open with its frontier inside `outer`.
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and
`Schoenflies.frontier_sdiff_outer_of_isSeparating` discharge them from `thm:jordan` for the
shape both sides have, and the consumer has `IsSeparating C` in hand.

That the *stage* invariants are all available is the point of the wave that preceded this
module: assertion (vii) and target polygonality became fields of `Schoenflies.GeneratedPair`,
and `Schoenflies.CellsAbsorb` became a theorem
(`CellStructure.Realization.cellsAbsorb`) rather than an assumption.

## Blueprint

* `Schoenflies.earStep` — `thm:finite-transfer`(a), step 3: "at most two edge subdivisions
  followed by one 2-cell split". In the Lean formulation the subdivisions are unnecessary — the
  ear's two ends are already drawn 0-cells — so it is one split.
-/

open Set
open scoped Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- **One ear insertion.** `Schoenflies.EarStep`, discharged.

The four domain hypotheses are about the two fixed regions, not about the stage; see the module
docstring. -/
theorem earStep [Infinite γ] {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} (h₀ : S₀.CombInvariants)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    (htgtQ : IsOpen (tgtDom \ tgtOuter)) (htgtFr : frontier (tgtDom \ tgtOuter) ⊆ tgtOuter) :
    EarStep P H Hdraw := by
  classical
  intro B a b D hB hBH hpath hab ha hb hint T par hT
  -- The ear that brings no new edge adds nothing.
  by_cases hdeg : ∃ e ∈ D, e ∈ E(B)
  · obtain ⟨e, heD, heB⟩ := hdeg
    exact ⟨T, par, isPartialTransferOf_union_of_mem_edgeSet hT hH.isDrawing hBH hpath hab ha
      hint heD heB⟩
  push Not at hdeg
  have hS : T.str.CombInvariants := T.combInvariants h₀
  -- The realized outer cycles are part of the two realized skeletons.
  have hsrcOut : srcOuter ⊆ T.src.skeletonSet := by
    have h1 : T.src.outerSet ⊆ T.src.skeletonSet := T.src.outerSet_subset_skeletonSet
    rwa [T.src_isWeaklyAdmissible.outerSet_eq] at h1
  have htgtOut : tgtOuter ⊆ T.tgt.skeletonSet := by
    have h1 : T.tgt.outerSet ⊆ T.tgt.skeletonSet := T.tgt.outerSet_subset_skeletonSet
    rwa [T.tgt_isWeaklyAdmissible.outerSet_eq] at h1
  -- The source side: the split data and the drawn ear.
  obtain ⟨d, earPos₁, earDraw₁, hE₁, hearSet, hposa, hposb, himg⟩ :=
    exists_earCrosscut hH hS T.src_isCellDecomposition T.src_isWeaklyAdmissible.outerSet_eq
      hT.skeletonSet_eq hT.vertexSet_subset
      (T.src.cellsAbsorb T.src_isCellDecomposition T.src_isFaceJordan hsrcOut hsrcQ hsrcFr)
      hBH hpath hab ha hb hint hdeg
  -- The target side: the crosscut of the corresponding 2-cell.
  have hposne : T.tgt.pos d.source ≠ T.tgt.pos d.target :=
    SplitData.EarCrosscut.source_ne_target_pos
  have hfrsub : frontier (T.tgt.cell d.face) ⊆ T.tgt.skeletonSet :=
    Realization.frontier_cell_subset_skeletonSet T.tgt_isCellDecomposition T.tgt_isFaceJordan
      d.face_mem
  have hfr := SplitData.frontier_cell_face (d := d) T.tgt_isCellDecomposition T.tgt_isFaceJordan
  have hsubsrc : ∀ {c : γ}, c ∈ V(T.str.skel) → T.str.sub c d.face →
      T.src.pos c ∈ closure (T.src.cell d.face) := fun hc hsub =>
    Realization.IsCellDecomposition.pos_mem_closure_cell_of_sub T.src_isCellDecomposition hc
      d.face_mem hsub
  obtain ⟨Pset, hPpoly, hParc, hPsub, -⟩ :=
    exists_target_ear T.src_isCellDecomposition T.tgt_isCellDecomposition T.tgt_isPolygonal
      htgtQ (htgtFr.trans htgtOut)
      (fun F hF => Realization.cells_isComponent_in T.tgt_isCellDecomposition T.tgt_isFaceJordan
        htgtOut hF)
      d.face_mem hfrsub (T.tgt_isFaceJordan.isJordanCurve d.face_mem)
      (T.tgt_isFaceJordan.cell_eq_inside d.face_mem) d.source_mem_skel d.target_mem_skel hposne
      (by rw [hfr]; exact Or.inl SplitData.pos_source_mem_cellUnion_cells₁)
      (by rw [hfr]; exact Or.inl SplitData.pos_target_mem_cellUnion_cells₁)
      (hsubsrc d.source_mem_skel (d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))))
      (hsubsrc d.target_mem_skel (d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))))
      (SplitData.isCutPair_of_inter T.tgt_isCellDecomposition T.tgt_isFaceJordan)
  -- …and the ear drawn along it, with the chosen homeomorphism between the two drawn ears.
  obtain ⟨earPos₂, earDraw₂, hE₂, -, ⟨m⟩⟩ :=
    exists_target_earCrosscut hE₁ hPpoly hParc hPsub
      (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition d.face_mem)
  -- The next stage.
  refine ⟨T.splitFace hS d hE₁ hE₂ m hsrcOut htgtOut, par ∘ d.parent, ?_, ?_, ?_, ?_⟩
  · exact (T.refines_splitFace hS d hE₁ hE₂ m hsrcOut htgtOut).1.trans hT.refines_src
  · exact (T.refines_splitFace hS d hE₁ hE₂ m hsrcOut htgtOut).2.trans hT.refines_tgt
  · have h1 : (T.splitFace hS d hE₁ hE₂ m hsrcOut htgtOut).src.skeletonSet
        = T.src.skeletonSet ∪ d.earSet earPos₁ earDraw₁ := SplitData.skeletonSet_realize hE₁
    rw [h1, hT.skeletonSet_eq, hearSet, ← Graph.pointSet_pathGraphOf hpath.isWalk,
      Graph.pointSet_union]
  · rw [GeneratedPair.splitFace_src]
    have hVs : V(T.str.skel) ⊆ V((T.str.splitFace d).skel) := fun z hz => Or.inl hz
    have hkey : ∀ ⦃x : Plane⦄, x ∈ V(B) ∪ H.walkVertices a D →
        x ∈ (d.realize T.src earPos₁ earDraw₁ hE₁).pos '' V((T.str.splitFace d).skel) := by
      rintro x (hx | hx)
      · obtain ⟨z, hz, rfl⟩ := (Realization.vertexSet_graph T.src) ▸ hT.vertexSet_subset hx
        exact ⟨z, hVs hz, by rw [SplitData.realize_pos, hE₁.splitPos_eq hz]⟩
      · obtain ⟨z, hz, rfl⟩ := himg ▸ hx
        exact ⟨z, Or.inr hz, by rw [SplitData.realize_pos, SplitData.splitPos_of_mem_ear hz]⟩
    intro x hx
    rw [Realization.vertexSet_graph]
    exact hkey hx

/-- **`thm:finite-transfer`, direction (a), with step 3 discharged.**

`Schoenflies.finite_transfer_toward_square` assumed both steps 1 and 3; this is the same
theorem on step 1 alone. What is left of `thm:finite-transfer`(a) is therefore exactly
`Schoenflies.CommonSubdivision`. -/
theorem finite_transfer_toward_square_of_commonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} (h₀ : S₀.CombInvariants)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    (htgtQ : IsOpen (tgtDom \ tgtOuter)) (htgtFr : frontier (tgtDom \ tgtOuter) ⊆ tgtOuter)
    (hsub : CommonSubdivision P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square hH hsub (earStep h₀ hH hsrcQ hsrcFr htgtQ htgtFr)

end Schoenflies
