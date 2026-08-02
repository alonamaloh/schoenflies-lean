/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.EarStep
import Schoenflies.SourceEar
import Schoenflies.FiniteTransferBack

/-!
# Step 3 of `thm:finite-transfer`(b): one ear insertion

`Schoenflies.EarStepTgt` was the last named hypothesis of `thm:finite-transfer`(b). This module
discharges it.

## Where it differs from direction (a)

The shape is `Schoenflies.earStep`'s and most of the assembly is the same, because
`Schoenflies.exists_earCrosscut` places an ear from either realization and
`Schoenflies.exists_target_earCrosscut` draws one from either. Two things are genuinely
different.

* **Which side is given.** Here the ear is drawn by `Hdraw` in the *target*, so the placement
  runs against `T.tgt` and the crosscut has to be produced in the corresponding *source* 2-cell
  (`GeneratedPair.exists_source_ear`). `CellStructure.SplitData.EarHomeo.symm` turns the matching
  round, since `GeneratedPair.splitFace` always wants it from source to target.
* **The endpoint on the wild curve.** Direction (a) never meets one: its target 2-cells are
  polygonal Jordan regions and every point of their boundaries is accessible. Here an ear
  endpoint may sit on `C`, and that is what the second sentence of `thm:finite-transfer`(b) is
  for. `Schoenflies.HasFreshAnchors` is that sentence, and the three things it says are the three
  the anchor paragraph needs.

## What the fresh-anchor hypotheses buy, one at a time

Let `z` be an ear endpoint whose *source* position lies on `C`; then its target position `p` lies
on `S`, and the ear's own first edge is a nonboundary edge of `H` through `p`.

* `unique_edge` — at most one nonboundary edge of `H` reaches `p` — makes the ear's edge the only
  one, and the ear's edges are not edges of `B` (this is the non-degenerate branch), so **no
  nonboundary edge of `B` reaches `p`**. That is the antecedent of the transfer invariant's
  anchor clause, and it is also, through `Graph.closure_pointSet_diff_subset`, the statement that
  `p` is off the closure of what `B` leaves outside `S` — the blueprint's "`K` … does not contain
  `a`", transported to the source by the skeleton homeomorphism.
* `notMem_vertexSet` — `p` is not a 0-cell of `Γ'` — makes the ancestor `par z` a *1-cell*, and
  `Realization.mem_edgeSet_outerGraph_of_cell_meets_outerSet` makes it an **outer** 1-cell, which
  is the other antecedent of the anchor clause. So `CellStructure.UniqueFaceAt z` follows, which
  is `hunique`.
* `stronglyAccessible` — the source partner of `p` is strongly accessible — is `a ∈ 𝒜`. It is
  stated for the *base* pair's correspondence, and the `homeo_eqOn` clause of
  `IsPartialTransferOfTgt` is what identifies that partner with `T.src.pos z`.

## Blueprint

* `Schoenflies.HasFreshAnchors` — the second sentence of `thm:finite-transfer`(b).
* `Schoenflies.earStepTgt` — `thm:finite-transfer`(b), step 3.
* `Schoenflies.finite_transfer_back'` — `thm:finite-transfer`(b), with nothing assumed beyond
  the hypotheses of its own statement.
-/

open Set
open scoped Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- **A point of the outer curve that a nonboundary edge of the extension reaches.** In
`thm:finite-transfer`(b) these are exactly the fresh points `u(a)`. -/
def NonboundaryAt (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (outer : Set Plane) (p : Plane) :
    Prop := ∃ f ∈ E(H), p ∈ Graph.edgeArc Hdraw f ∧ ¬ Graph.edgeArc Hdraw f ⊆ outer

/-- **The second sentence of `thm:finite-transfer`(b).**

*Assume that every new nonboundary edge of `H' ∖ Γ'` meeting `S` has exactly one endpoint on `S`,
that this endpoint is a fresh point `u(a)` with `a ∈ 𝒜`, and that exactly one new nonboundary
edge is incident with each such fresh boundary point.*

Three clauses, and each is spent exactly once; see the module docstring. None of them mentions an
intermediate stage — they are conditions on `H` and on the base pair — which is what lets the ear
induction quantify over stages freely. -/
structure HasFreshAnchors (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop where
  /-- **Exactly one new nonboundary edge is incident with each fresh boundary point.** -/
  unique_edge : ∀ ⦃p⦄, p ∈ tgtOuter → ∀ ⦃f g⦄, f ∈ E(H) → g ∈ E(H) →
    p ∈ Graph.edgeArc Hdraw f → p ∈ Graph.edgeArc Hdraw g →
    ¬ Graph.edgeArc Hdraw f ⊆ tgtOuter → ¬ Graph.edgeArc Hdraw g ⊆ tgtOuter → f = g
  /-- **The endpoint on `S` is a fresh point**: not a 0-cell of `Γ'`. -/
  notMem_vertexSet : ∀ ⦃p⦄, p ∈ tgtOuter → NonboundaryAt H Hdraw tgtOuter p → p ∉ V(P.tgt.graph)
  /-- **It is `u(a)` with `a ∈ 𝒜`**: its source partner is strongly accessible. -/
  stronglyAccessible : ∀ ⦃p⦄, p ∈ tgtOuter → NonboundaryAt H Hdraw tgtOuter p →
    StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun p)

/-! ### The two bridges the anchor case needs -/

variable {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {B : Graph Plane γ}
  {Hdraw : γ → ℝ → Plane} {par : γ → γ}

/-- **The ancestor of a fresh boundary 0-cell is an outer edge of the base pair.**

`Realization.Refines.cell_subset` puts the 0-cell's position in the open cell of its ancestor. A
0-cell ancestor would make it a drawn 0-cell of the base pair, which `HasFreshAnchors` forbids; a
2-cell ancestor would put it off the base skeleton, which the outer curve is part of. So the
ancestor is a 1-cell, and `Realization.mem_edgeSet_outerGraph_of_cell_meets_outerSet` makes it an
outer one. -/
theorem parent_mem_edgeSet_outerGraph (hT : IsPartialTransferOfTgt T P B Hdraw par) {z : γ}
    (hz : z ∈ V(T.str.skel)) (hp : T.tgt.pos z ∈ tgtOuter)
    (hfresh : T.tgt.pos z ∉ V(P.tgt.graph)) : par z ∈ E(P.str.outerGraph) := by
  have hcell : T.tgt.pos z ∈ P.tgt.cell (par z) := by
    refine hT.refines_tgt.cell_subset (T.str.mem_cells_of_mem_vertexSet hz) ?_
    rw [T.tgt.cell_vertex hz]
    rfl
  have hpar : par z ∈ P.str.cells :=
    hT.refines_tgt.parent_mem_cells (T.str.mem_cells_of_mem_vertexSet hz)
  have houtP : tgtOuter ⊆ P.tgt.skeletonSet := by
    have h1 : P.tgt.outerSet ⊆ P.tgt.skeletonSet := P.tgt.outerSet_subset_skeletonSet
    rwa [P.tgt_isWeaklyAdmissible.outerSet_eq] at h1
  have he : par z ∈ E(P.str.skel) := by
    rcases hpar with hv | hv
    · rcases hv with hv | hv
      · exact absurd (by rw [P.tgt.cell_vertex hv] at hcell
                         rw [Realization.vertexSet_graph]; exact ⟨par z, hv, hcell.symm⟩) hfresh
      · exact hv
    · exact absurd (houtP hp)
        (Set.disjoint_left.1 (P.tgt.disjoint_cell_skeletonSet P.tgt_isCellDecomposition hv) hcell)
  exact Realization.mem_edgeSet_outerGraph_of_cell_meets_outerSet he hcell
    (by rwa [P.tgt_isWeaklyAdmissible.outerSet_eq])

/-- **The source partner of a fresh boundary 0-cell is where the stage draws it.** The
`homeo_eqOn` clause says the stage's skeleton map extends the base pair's, so the two agree at
the source position of the 0-cell — which lies on the outer curve, hence on the base skeleton. -/
theorem invFun_pos_eq (hT : IsPartialTransferOfTgt T P B Hdraw par) {z : γ}
    (hz : z ∈ V(T.str.skel)) (hsrc : T.src.pos z ∈ srcOuter) :
    P.homeo.invFun (T.tgt.pos z) = T.src.pos z := by
  have hsub : T.src.pos z ∈ P.src.skeletonSet := by
    have h1 : P.src.outerSet ⊆ P.src.skeletonSet := P.src.outerSet_subset_skeletonSet
    rw [P.src_isWeaklyAdmissible.outerSet_eq] at h1
    exact h1 hsrc
  rw [← T.homeo.pos_apply hz, hT.homeo_eqOn hsub]
  exact P.homeo.leftInvOn hsub

/-! ### The step -/

/-- **One ear insertion, direction (b).** `Schoenflies.EarStepTgt`, discharged.

The four domain hypotheses are about the two fixed regions, not about the stage — the same ones
`Schoenflies.earStep` takes — and `hA` is the second sentence of `thm:finite-transfer`(b). -/
theorem earStepTgt [Infinite γ] {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} (h₀ : S₀.CombInvariants)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) (hA : HasFreshAnchors P H Hdraw)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    (htgtQ : IsOpen (tgtDom \ tgtOuter)) (htgtFr : frontier (tgtDom \ tgtOuter) ⊆ tgtOuter) :
    EarStepTgt P H Hdraw := by
  classical
  intro B a b D hB hBH hpath hab ha hb hint T par hT
  -- The ear that brings no new edge adds nothing.
  by_cases hdeg : ∃ e ∈ D, e ∈ E(B)
  · obtain ⟨e, heD, heB⟩ := hdeg
    refine ⟨T, par, ?_⟩
    rw [Graph.union_pathGraphOf_eq_left hH.isDrawing hBH hpath hab ha hint heD heB]
    exact hT
  push Not at hdeg
  haveI := hH.finite
  haveI : B.Finite := Graph.Finite.of_le hBH
  have hS : T.str.CombInvariants := T.combInvariants h₀
  have hdrawH : IsDrawing H Hdraw := hH.isDrawing
  have hdrawB : IsDrawing B Hdraw := hdrawH.mono hBH
  -- The realized outer cycles are part of the two realized skeletons.
  have hsrcOut : srcOuter ⊆ T.src.skeletonSet := by
    have h1 : T.src.outerSet ⊆ T.src.skeletonSet := T.src.outerSet_subset_skeletonSet
    rwa [T.src_isWeaklyAdmissible.outerSet_eq] at h1
  have htgtOut : tgtOuter ⊆ T.tgt.skeletonSet := by
    have h1 : T.tgt.outerSet ⊆ T.tgt.skeletonSet := T.tgt.outerSet_subset_skeletonSet
    rwa [T.tgt_isWeaklyAdmissible.outerSet_eq] at h1
  have hBout : tgtOuter ⊆ pointSet B Hdraw := hT.skeletonSet_eq ▸ htgtOut
  have hdisj : Disjoint (walkPointSet H Hdraw a D \ {a, b}) (pointSet B Hdraw) :=
    disjoint_walkPointSet_diff hdrawH hBH hpath hint hdeg
  -- The target side: the split data and the drawn ear, where `H` draws it.
  obtain ⟨d, earPos₂, earDraw₂, hE₂, hearSet, hposa, hposb, himg⟩ :=
    exists_earCrosscut hH hS T.tgt_isCellDecomposition T.tgt_isWeaklyAdmissible.outerSet_eq
      hT.skeletonSet_eq hT.vertexSet_subset
      (T.tgt.cellsAbsorb T.tgt_isCellDecomposition T.tgt_isFaceJordan htgtOut htgtQ htgtFr)
      hBH hpath hab ha hb hint hdeg
  -- **An ear endpoint is accessible from the source 2-cell.** Off `C` this is
  -- `lem:polygonal-side-accessibility`; on `C` it is the anchor paragraph, and the ear's own
  -- edge at that end is what makes the three fresh-anchor clauses apply.
  have haccess : ∀ ⦃z : γ⦄, z ∈ V(T.str.skel) → T.str.sub z d.face →
      (∃ g ∈ D, T.tgt.pos z ∈ edgeArc Hdraw g) →
      PolyAccessible (T.src.cell d.face) (T.src.pos z) := by
    intro z hz hsub hear
    by_cases hoff : T.src.pos z ∈ srcOuter
    · obtain ⟨g, hgD, hgp⟩ := hear
      have hgnb : ¬ edgeArc Hdraw g ⊆ tgtOuter :=
        notSubset_of_mem_ear hdrawH hBH hpath hdisj hBout ha hb hgD
      -- the target position is on `S`, because the skeleton map carries `C` onto it
      have hp : T.tgt.pos z ∈ tgtOuter := by
        have himgo := T.homeo.image_outerSet
        rw [T.src_isWeaklyAdmissible.outerSet_eq, T.tgt_isWeaklyAdmissible.outerSet_eq] at himgo
        have hmem : T.homeo.toFun (T.src.pos z) ∈ T.homeo.toFun '' srcOuter := ⟨_, hoff, rfl⟩
        have hx : T.homeo.toFun (T.src.pos z) ∈ tgtOuter := himgo.subset hmem
        rwa [T.homeo.pos_apply hz] at hx
      have hnb : NonboundaryAt H Hdraw tgtOuter (T.tgt.pos z) :=
        ⟨g, hpath.edge_mem hgD, hgp, hgnb⟩
      -- **no nonboundary edge of `B` reaches the anchor**: the ear's is the only one, and it is
      -- not an edge of `B`
      have huntouched : ∀ ⦃f⦄, f ∈ E(B) → T.tgt.pos z ∈ edgeArc Hdraw f →
          edgeArc Hdraw f ⊆ tgtOuter := by
        intro f hfB hfp
        by_contra hcon
        exact hdeg g hgD (hA.unique_edge hp (hBH.edgeSet_mono hfB) (hpath.edge_mem hgD) hfp hgp
          hcon hgnb ▸ hfB)
      have hu : T.str.UniqueFaceAt z := hT.anchor_uniqueFaceAt hz
        (parent_mem_edgeSet_outerGraph hT hz hp (hA.notMem_vertexSet hp hnb)) huntouched
      have hacc : StronglyAccessible (srcDom \ srcOuter) (T.src.pos z) := by
        rw [← invFun_pos_eq hT hz hoff]; exact hA.stronglyAccessible hp hnb
      -- **the blueprint's `K`**, on the target and transported back
      have hBcpt : IsCompact (pointSet B Hdraw) := hdrawB.isCompact_pointSet
      set Kt : Set Plane := closure (pointSet B Hdraw \ tgtOuter) with hKtdef
      have hKtsub : Kt ⊆ pointSet B Hdraw := closure_minimal Set.diff_subset hBcpt.isClosed
      have hKtskel : Kt ⊆ T.tgt.skeletonSet := hT.skeletonSet_eq ▸ hKtsub
      have hzKt : T.tgt.pos z ∉ Kt := by
        intro hmem
        rcases Graph.closure_pointSet_diff_subset hdrawB tgtOuter hmem with hv | hedge
        · exact hv.2 hp
        · obtain ⟨f, ⟨hfB, hfnb⟩, hfp⟩ := Set.mem_iUnion₂.1 hedge
          exact hfnb (huntouched hfB hfp)
      refine T.polyAccessible_src_of_stronglyAccessible hsrcOut hsrcQ hsrcFr d.face_mem hz hsub hu
        Set.Subset.rfl hacc
        ((hBcpt.of_isClosed_subset isClosed_closure hKtsub).image_of_continuousOn
          (T.homeo.continuousOn_invFun.mono hKtskel)) ?_ ?_
      · rintro ⟨y, hy, hyz⟩
        refine hzKt ?_
        have : T.tgt.pos z = y := by
          rw [← T.homeo.pos_apply hz, ← hyz, T.homeo.rightInvOn (hKtskel hy)]
        exact this ▸ hy
      · intro x hxD hxK
        have hxn : x ∈ T.src.nonboundary := by
          rw [T.src_nonboundary_eq]; exact ⟨hxK, hxD.2⟩
        have hxt : T.homeo.toFun x ∈ Kt := by
          have h1 : T.homeo.toFun x ∈ T.tgt.nonboundary :=
            T.homeo.image_nonboundary ▸ ⟨x, hxn, rfl⟩
          rw [T.tgt_nonboundary_eq, hT.skeletonSet_eq] at h1
          exact subset_closure h1
        exact ⟨_, hxt, T.homeo.leftInvOn hxK⟩
    · exact T.polyAccessible_src_of_notMem_outer hsrcOut hsrcQ hsrcFr d.face_mem hz hsub hoff
  -- The two ear edges at the two ends.
  obtain ⟨g₁, hg₁D, m₁, hl₁⟩ := hpath.isWalk.exists_isLink_left_of_ne hab
  obtain ⟨g₂, hg₂D, m₂, hl₂⟩ := hpath.reverse.isWalk.exists_isLink_left_of_ne hab.symm
  -- The source side: the polygonal crosscut of the corresponding 2-cell.
  obtain ⟨Pset, hPpoly, hParc, hPsub, -⟩ :=
    T.exists_source_ear
      (haccess d.source_mem_skel (d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁)))
        ⟨g₁, hg₁D, by rw [hposa]; exact (hdrawH.edge_isArcBetween hl₁).left_mem⟩)
      (haccess d.target_mem_skel (d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁)))
        ⟨g₂, List.mem_reverse.1 hg₂D, by rw [hposb]; exact (hdrawH.edge_isArcBetween hl₂).left_mem⟩)
  -- …and the source ear drawn along it, with the chosen homeomorphism between the two drawn ears.
  obtain ⟨earPos₁, earDraw₁, hE₁, -, ⟨m⟩⟩ :=
    exists_target_earCrosscut hE₂ hPpoly hParc hPsub
      (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition d.face_mem)
  have hcompat : B.Compatible (H.pathGraphOf a D) :=
    Graph.Compatible.of_disjoint_edgeSet (Set.disjoint_left.2 fun e he he' => by
      rw [Graph.pathGraphOf_edgeSet hpath.isWalk] at he'
      exact hdeg e he' he)
  refine ⟨T.splitFace hS d hE₁ hE₂ m.symm hsrcOut htgtOut, par ∘ d.parent, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (T.refines_splitFace hS d hE₁ hE₂ m.symm hsrcOut htgtOut).1.trans hT.refines_src
  · exact (T.refines_splitFace hS d hE₁ hE₂ m.symm hsrcOut htgtOut).2.trans hT.refines_tgt
  · have h1 : (T.splitFace hS d hE₁ hE₂ m.symm hsrcOut htgtOut).tgt.skeletonSet
        = T.tgt.skeletonSet ∪ d.earSet earPos₂ earDraw₂ := SplitData.skeletonSet_realize hE₂
    rw [h1, hT.skeletonSet_eq, hearSet, ← Graph.pointSet_pathGraphOf hpath.isWalk,
      Graph.pointSet_union]
  · rw [GeneratedPair.splitFace_tgt]
    have hVs : V(T.str.skel) ⊆ V((T.str.splitFace d).skel) := fun z hz => Or.inl hz
    have hkey : ∀ ⦃x : Plane⦄, x ∈ V(B) ∪ H.walkVertices a D →
        x ∈ (d.realize T.tgt earPos₂ earDraw₂ hE₂).pos '' V((T.str.splitFace d).skel) := by
      rintro x (hx | hx)
      · obtain ⟨z, hz, rfl⟩ := (Realization.vertexSet_graph T.tgt) ▸ hT.vertexSet_subset hx
        exact ⟨z, hVs hz, by rw [SplitData.realize_pos, hE₂.splitPos_eq hz]⟩
      · obtain ⟨z, hz, rfl⟩ := himg ▸ hx
        exact ⟨z, Or.inr hz, by rw [SplitData.realize_pos, SplitData.splitPos_of_mem_ear hz]⟩
    intro x hx
    rw [Realization.vertexSet_graph]
    exact hkey hx
  · -- **the anchor clause at the next stage**
    intro z hz hpar huntouched
    have hzsplit : z ∈ V(T.str.skel) := by
      rcases hz with hz | hz
      · exact hz
      -- an interior vertex of the ear has a 2-cell for parent, so its ancestor is not an edge
      by_cases hzc : z ∈ T.str.cells
      · rcases d.mem_cells_of_mem_ear_vertexSet hz hzc with rfl | rfl
        exacts [d.source_mem_skel, d.target_mem_skel]
      · exfalso
        have hpz : d.parent z = d.face :=
          d.parent_of_mem_newCells (Or.inl (Or.inl ⟨hz, by
            rintro (rfl | rfl)
            exacts [hzc d.source_mem_cells, hzc d.target_mem_cells]⟩))
        have : par (d.parent z) ∈ P.str.faces := by
          rw [hpz]; exact hT.refines_tgt.parent_mem_faces d.face_mem
        exact P.str.faces_ne_edgeSet this (P.str.outerGraph_le.edgeSet_mono hpar) rfl
    -- an old 0-cell keeps its position, and the ear's edge at an end destroys `huntouched`
    have hpos : (T.splitFace hS d hE₁ hE₂ m.symm hsrcOut htgtOut).tgt.pos z = T.tgt.pos z := by
      rw [GeneratedPair.splitFace_tgt, SplitData.realize_pos, hE₂.splitPos_eq hzsplit]
    have huntouched' : ∀ ⦃f⦄, f ∈ E(B) → T.tgt.pos z ∈ edgeArc Hdraw f →
        edgeArc Hdraw f ⊆ tgtOuter := fun f hf hfp =>
      huntouched (Graph.left_le_union _ _ |>.edgeSet_mono hf) (hpos ▸ hfp)
    have hne : ∀ {g : γ} {p : Plane}, g ∈ D → T.tgt.pos z = p → p ∈ edgeArc Hdraw g → False := by
      intro g p hgD hzp hgp
      refine notSubset_of_mem_ear hdrawH hBH hpath hdisj hBout ha hb hgD ?_
      refine huntouched ?_ (by rw [hpos, hzp]; exact hgp)
      exact hcompat.right_le_union.edgeSet_mono
        (by rw [Graph.pathGraphOf_edgeSet hpath.isWalk]; exact hgD)
    have hzs : z ≠ d.source := by
      rintro rfl
      exact hne hg₁D hposa (hdrawH.edge_isArcBetween hl₁).left_mem
    have hzt : z ≠ d.target := by
      rintro rfl
      exact hne (List.mem_reverse.1 hg₂D) hposb (hdrawH.edge_isArcBetween hl₂).left_mem
    have hpar' : par z ∈ E(P.str.outerGraph) := by
      have hc : (par ∘ d.parent) z = par z := by
        rw [Function.comp_apply,
          d.parent_of_mem_cells (T.str.mem_cells_of_mem_vertexSet hzsplit)]
      rwa [hc] at hpar
    exact d.uniqueFaceAt (hT.anchor_uniqueFaceAt hzsplit hpar' huntouched')
      (T.str.mem_cells_of_mem_vertexSet hzsplit)
      (fun h => T.str.faces_ne_vertexSet d.face_mem hzsplit h.symm)
      (d.notMem_earCells_of_mem_vertexSet hzsplit hzs hzt)
  · -- **the skeleton map still extends the base pair's**
    refine fun x hx => ?_
    have h1 : (T.splitFace hS d hE₁ hE₂ m.symm hsrcOut htgtOut).homeo.toFun x
        = T.homeo.toFun x :=
      SplitData.splitHomeo_eqOn hE₁ hE₂
        (hT.refines_src.skeletonSet_subset P.src_isCellDecomposition
          T.src_isCellDecomposition hx)
    rw [h1]
    exact hT.homeo_eqOn hx

/-- **`thm:finite-transfer`, direction (b), with nothing assumed.**

`Schoenflies.finite_transfer_back` was the theorem on the ear step alone; this is it with the ear
step discharged. What it takes is the statement's own hypotheses: `H` is an admissible refinement
of `Γ'` (`IsSourceExtension`, which is direction-agnostic), its new boundary points are fresh
anchors (`HasFreshAnchors`), and the two ambient regions are closed Jordan regions in the only
form used — `dom ∖ outer` open with its frontier inside `outer`, which
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and its companion supply. -/
theorem finite_transfer_back' [Infinite γ] (h₀ : S₀.CombInvariants)
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {H : Graph Plane γ}
    {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) (hA : HasFreshAnchors P H Hdraw)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    (htgtQ : IsOpen (tgtDom \ tgtOuter)) (htgtFr : frontier (tgtDom \ tgtOuter) ⊆ tgtOuter) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOfTgt T P H Hdraw par :=
  finite_transfer_back h₀ hH (earStepTgt h₀ hH hA hsrcQ hsrcFr htgtQ htgtFr)

end Schoenflies
