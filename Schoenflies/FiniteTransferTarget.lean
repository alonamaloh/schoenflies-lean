/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CommonSubdivision
import Schoenflies.FreshAccess

/-!
# Finite transfer, direction (b): toward the Jordan domain

Direction (b) starts with an extension of the **target** realization and reproduces it on the
source side.  This module begins its construction with the target analogue of the common
subdivision from direction (a).  The graph-theoretic extension assumptions are exactly
`Schoenflies.IsSourceExtension`, applied to `P.tgt`: only the side on which the realization lives
changes.

The trace of the target extension supported on the old target skeleton is 2-connected.  Its
finitely many vertices are inserted by `GeneratedPair.exists_subdivideTargetSetData`; each target
point is transported backwards through the skeleton homeomorphism, and the resulting source
parameter is then carried forward by `SubdivData.realizeHomeo`.  Thus the same subdivision is
made on both sides and both refinement maps share one parent map.

The reverse ear bookkeeping is also completed here.  The ambient target path is injectively
renamed, realized as a target crosscut, and then matched to a polygonal source crosscut by
reversing `EarHomeo`.  Off the wild curve, endpoint accessibility is derived from
polygonal-side accessibility.  At a fresh anchor, this module constructs the compact carrier of
closed nonboundary edges and discharges compactness, cell absorption, and coverage before
applying `Schoenflies.polyAccessible_of_stronglyAccessible_in`.  Consequently the only remaining
input is `TargetEarFreshInvariant`: the prescribed outer-cycle ear order must say that a
wild-boundary endpoint is a strongly accessible anchor absent from that carrier and incident
with one unique current source face.

## Blueprint

* `Schoenflies.IsTargetPartialTransferOf`, `Schoenflies.TargetCommonSubdivision` — the
  target-to-source analogues of the direction-(a) transfer interfaces.
* `Schoenflies.targetCommonSubdivision` — step 1 of `thm:finite-transfer`(b).
* `Schoenflies.TargetEarStepData`, `Schoenflies.exists_targetSideEarStepData` — the complete
  target-path relabelling and split data for one reverse ear.
* `Schoenflies.TargetEarEndpointAccessibility`,
  `Schoenflies.targetEarStep_of_endpointAccessibility` — the reverse ear construction reduced
  to its exact source-side geometric invariant.
* `Schoenflies.GeneratedPair.sourceNonboundaryGraph`,
  `Schoenflies.GeneratedPair.source_polyAccessible_of_fresh` — the compact source carrier and
  the fresh-anchor accessibility theorem with all cellulation hypotheses discharged.
* `Schoenflies.TargetEarFreshInvariant`,
  `Schoenflies.targetEarEndpointAccessibility_of_freshInvariant` — the remaining prescribed-ear
  combinatorics and its implication for endpoint accessibility.
* `Schoenflies.targetTransferOfEars`,
  `Schoenflies.finite_transfer_toward_source_of_freshInvariant` — the relative-ear induction
  and direction-(b) theorem conditional only on that combinatorial invariant.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- An intermediate target-to-source transfer: the target realization occupies the current
subgraph of the target extension, while both sides refine the original pair along one map. -/
structure IsTargetPartialTransferOf
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the original source realization. -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the original target realization along the same map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The new target skeleton occupies exactly the current target subgraph. -/
  skeletonSet_eq : T.tgt.skeletonSet = pointSet B Hdraw
  /-- Every current target-graph vertex is a 0-cell of the new pair. -/
  vertexSet_subset : V(B) ⊆ V(T.tgt.graph)

/-- The final conclusion of direction (b): a target extension reproduced by an admissible
matched pair on both sides. -/
structure IsTargetTransferOf
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsTargetPartialTransferOf T P H Hdraw par where
  /-- The transferred source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The transferred target realization is admissible. -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

/-- Step 1 of direction (b), as the interface consumed by its relative-ear induction. -/
def TargetCommonSubdivision
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
      (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsTargetPartialTransferOf T₀ P K Hdraw par₀

/-- One target ear insertion, expressed as the step consumed by relative-ear induction. -/
def TargetEarStep [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsTargetPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

/-- Complete constructor data for adjoining one target ear to a partial reverse transfer. -/
structure TargetEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  /-- The common abstract face split. -/
  splitData : T.str.SplitData
  /-- The two realizations of its new ear. -/
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  /-- Each realized ear is a crosscut of the corresponding old face. -/
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  /-- The source-to-target matching consumed by `GeneratedPair.split`. -/
  earHomeo : splitData.EarHomeo srcPos srcDraw tgtPos tgtDraw
  /-- Both realized ears have polygonal edges. -/
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc srcDraw e)
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc tgtDraw e)
  /-- The target ear realizes exactly the ambient target path. -/
  tgtEarSet_eq : splitData.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D
  /-- All vertices of the enlarged target graph occur in the split realization. -/
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.tgt tgtPos tgtDraw tgtCrosscut).graph)

namespace TargetEarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

/-- Assemble the generated pair exposed by one reverse-ear construction. -/
noncomputable def pair (w : TargetEarStepData T B H Hdraw a D) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom :=
  T.split T.str_combInvariants w.splitData w.srcPos w.srcDraw w.tgtPos w.tgtDraw
    w.srcCrosscut w.tgtCrosscut w.earHomeo w.srcEdgePolygonal w.tgtEdgePolygonal

@[simp] theorem pair_src (w : TargetEarStepData T B H Hdraw a D) :
    w.pair.src =
      w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut := rfl

@[simp] theorem pair_tgt (w : TargetEarStepData T B H Hdraw a D) :
    w.pair.tgt =
      w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut := rfl

/-- The assembled pair realizes the enlarged target subgraph and refines the original pair. -/
theorem isTargetPartialTransferOf_pair
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {b : Plane}
    {par : γ → γ} (w : TargetEarStepData T B H Hdraw a D)
    (hdraw : H.IsDrawing Hdraw) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    IsTargetPartialTransferOf w.pair P (B.union (H.pathGraphOf a D)) Hdraw
      (par ∘ w.splitData.parent) where
  refines_src :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.srcCrosscut
      T.str_combInvariants T.src_isCellDecomposition T.src_isFaceJordan).2.2).trans
      hT.refines_src
  refines_tgt :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.tgtCrosscut
      T.str_combInvariants T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2).trans
      hT.refines_tgt
  skeletonSet_eq := by
    change (w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut).skeletonSet = _
    rw [w.splitData.skeletonSet_realize, hT.skeletonSet_eq, w.tgtEarSet_eq,
      Graph.pointSet_union, hdraw.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)]
  vertexSet_subset := by
    change V(B.union (H.pathGraphOf a D)) ⊆
      V((w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut).graph)
    exact w.vertexSet_subset

end TargetEarStepData

/-- The nontrivial reverse-ear constructor, before the already-present-edge branch is folded
back in. -/
def TargetEarStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (_hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      Nonempty (TargetEarStepData T B H Hdraw a D)

/-- Fold the explicit nontrivial reverse-ear constructor into the total `TargetEarStep`
interface. -/
theorem targetEarStep_of_data [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hbuild : TargetEarStepConstruction P H Hdraw hH) :
    TargetEarStep P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint T par hT
  rcases Graph.ear_edges_notMem_or_union_eq hBH hpath hab haB hbB hint with hnew | hsame
  · obtain ⟨w⟩ := hbuild B a b D hB hBH hpath hab haB hbB hint hnew T par hT
    exact ⟨w.pair, par ∘ w.splitData.parent,
      w.isTargetPartialTransferOf_pair hH.isDrawing hpath hab hT⟩
  · refine ⟨T, par, ?_⟩
    rw [hsame]
    exact hT

/-! ### Locating and realizing the target half of a reverse ear -/

/-- A nontrivial target ear lies in one current target face and determines its two abstract
endpoint vertices. -/
theorem exists_target_face_of_ear
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    ∃ u v F, u ∈ V(T.str.skel) ∧ v ∈ V(T.str.skel) ∧ u ≠ v ∧
      T.tgt.pos u = a ∧ T.tgt.pos v = b ∧ F ∈ T.str.faces ∧
      Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F ∧
      T.str.sub u F ∧ T.str.sub v F := by
  have haT := hT.vertexSet_subset haB
  have hbT := hT.vertexSet_subset hbB
  rw [CellStructure.Realization.vertexSet_graph] at haT hbT
  obtain ⟨u, hu, hua⟩ := haT
  obtain ⟨v, hv, hvb⟩ := hbT
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hua, ← hvb, huv]
  have harc : IsArcBetween (Graph.edgesCover Hdraw D) a b :=
    hH.isDrawing.path_isArcBetween hpath (hpath.ne_nil hab)
  let N := Graph.edgesCover Hdraw D \ {a, b}
  have hNconn : IsPreconnected N := harc.isConnected_diff.isPreconnected
  have hNne : N.Nonempty := harc.isConnected_diff.nonempty
  have hND : N ⊆ tgtDom := by
    intro x hx
    exact hH.pointSet_subset
      (Graph.edgesCover_subset_pointSet (fun g hg => hpath.edge_mem hg) hx.1)
  have hNdisj : Disjoint N T.tgt.skeletonSet := by
    rw [hT.skeletonSet_eq]
    refine Set.disjoint_left.2 fun x hx hxB ↦ hx.2 ?_
    exact hH.isDrawing.edgesCover_inter_pointSet hBH hpath hint hnew ⟨hx.1, hxB⟩
  obtain ⟨F, hF, hNF, huF, hvF, -⟩ :=
    T.tgt_isCellDecomposition.exists_face_of_ear
      (T.tgt_isCellDecomposition.cellsAbsorb T.tgt_isFaceJordan)
      hNconn hNne hND hNdisj hu hv
      (hua ▸ harc.left_mem_closure_diff) (hvb ▸ harc.right_mem_closure_diff)
  exact ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hNF, huF, hvF⟩

/-- Every edge of a genuine target ear is polygonal.  An edge in the exceptional outer-curve
branch would lie simultaneously in the old target skeleton and in the open current face. -/
theorem target_ear_edge_polygonal
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F) :
    ∀ e ∈ D, IsPolygonal (Graph.edgeArc Hdraw e) := by
  intro e he
  rcases hH.edge_dichotomy (hpath.edge_mem he) with houter | hpoly
  · exfalso
    have houterSkel : tgtOuter ⊆ T.tgt.skeletonSet := by
      intro z hz
      apply T.tgt.outerSet_subset_skeletonSet
      rw [T.tgt_isWeaklyAdmissible.outerSet_eq]
      exact hz
    have harcPair : edgeArc Hdraw e ⊆ ({a, b} : Set Plane) := by
      intro z hz
      by_contra hzpair
      have hzCell : z ∈ T.tgt.cell F :=
        hinside ⟨Graph.mem_edgesCover he hz, hzpair⟩
      have hzSkel : z ∈ T.tgt.skeletonSet := houterSkel (houter hz)
      exact Set.disjoint_left.1
        (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition hF) hzCell hzSkel
    obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hpath.edge_mem he)
    have harc := hH.isDrawing.edge_isArcBetween hxy
    have hxyne := hH.isDrawing.ne_of_isLink hxy
    rcases harcPair harc.left_mem with rfl | rfl <;>
      rcases harcPair harc.right_mem with rfl | rfl
    · exact hxyne rfl
    · exact harc.not_subset_pair harcPair
    · exact harc.not_subset_pair (by simpa [Set.pair_comm] using harcPair)
    · exact hxyne rfl
  · exact hpoly.1

/-- The one-sided constructor data obtained by realizing the ambient target path. -/
structure TargetSideEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  splitData : T.str.SplitData
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc tgtDraw e)
  tgtEarSet_eq : splitData.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.tgt tgtPos tgtDraw tgtCrosscut).graph)

/-- Injectively rename a nontrivial ambient target ear with fresh abstract cells and realize it
as a crosscut of the target face that contains its open arc. -/
theorem exists_targetSideEarStepData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
      H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      (∀ g ∈ D, g ∉ E(B)) →
      ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        IsTargetPartialTransferOf T P B Hdraw par →
        Nonempty (TargetSideEarStepData T B H Hdraw a D) := by
  classical
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hinside, huF, hvF⟩ :=
    exists_target_face_of_ear hH hBH hpath hab haB hbB hint hnew hT
  let paths := T.str_boundaryCycles.boundaryPaths F hF u v hu hv huF hvF huv
  let Q : Graph Plane γ := H.pathGraphOf a D
  have hQle : Q ≤ H := Graph.pathGraphOf_le hpath.isWalk
  have hQpath : Q.IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  have haQ : a ∈ V(Q) := Graph.mem_vertexSet_pathGraphOf_self
  have hbQ : b ∈ V(Q) := by
    rw [Graph.pathGraphOf_vertexSet]
    exact hpath.target_mem_walkVertices
  have hQfinV : V(Q).Finite := hpath.isWalk.finite_vertexSet_pathGraphOf
  have hQfinE : E(Q).Finite := hpath.isWalk.finite_edgeSet_pathGraphOf
  have huCell : u ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hu
  have hvCell : v ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hv
  obtain ⟨vname, vname_a, vname_b, vname_inj, vname_fresh⟩ :=
    exists_injective_pinned_avoiding T.str.finite_cells huCell hvCell huv hQfinV hab
  let newVertices : Set γ := vname '' (V(Q) \ {a, b})
  have hnewVertices_fin : newVertices.Finite := hQfinV.sdiff.image vname
  have hnewVertices_avoid : Disjoint newVertices T.str.cells := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨hxQ, hxab⟩, rfl⟩ hzCell
    exact vname_fresh x hxQ (fun h => hxab (Or.inl h)) (fun h => hxab (Or.inr h)) hzCell
  let edgeUsed : Set γ := T.str.cells ∪ newVertices
  have hedgeUsed_fin : edgeUsed.Finite := T.str.finite_cells.union hnewVertices_fin
  letI : Finite E(Q) := Set.finite_coe_iff.mpr hQfinE
  obtain ⟨freshEdge, freshEdge_inj, freshEdge_avoid⟩ :=
    exists_injective_avoiding edgeUsed hedgeUsed_fin E(Q)
  let ename : γ → γ := fun e => if he : e ∈ E(Q) then freshEdge ⟨e, he⟩ else u
  have ename_apply {e : γ} (he : e ∈ E(Q)) : ename e = freshEdge ⟨e, he⟩ := by
    simp [ename, he]
  have ename_inj : InjOn ename E(Q) := by
    intro e he f hf hef
    have hsub : (⟨e, he⟩ : E(Q)) = ⟨f, hf⟩ := by
      apply freshEdge_inj
      calc
        freshEdge ⟨e, he⟩ = ename e := (ename_apply he).symm
        _ = ename f := hef
        _ = freshEdge ⟨f, hf⟩ := ename_apply hf
    exact congrArg (fun z : E(Q) => z.1) hsub
  have ename_avoid {e : γ} (he : e ∈ E(Q)) : ename e ∉ edgeUsed := by
    rw [ename_apply he]
    exact freshEdge_avoid ⟨e, he⟩
  let newEdges : Set γ := ename '' E(Q)
  have hnewEdges_fin : newEdges.Finite := hQfinE.image ename
  have hnewEdges_avoid : Disjoint newEdges edgeUsed := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, rfl⟩
    exact ename_avoid he
  let faceUsed : Set γ := edgeUsed ∪ newEdges
  have hfaceUsed_fin : faceUsed.Finite := hedgeUsed_fin.union hnewEdges_fin
  obtain ⟨freshFace, freshFace_inj, freshFace_avoid⟩ :=
    exists_injective_avoiding faceUsed hfaceUsed_fin (Fin 2)
  let face₁ : γ := freshFace 0
  let face₂ : γ := freshFace 1
  let relabelled : Graph Plane γ := Q.relabelEdges ename ename_inj
  let ear : Graph γ γ := relabelled.map vname
  have hVear : V(ear) = vname '' V(Q) := by simp [ear, relabelled]
  have hEear : E(ear) = ename '' E(Q) := by simp [ear, relabelled]
  have hearPath : ear.IsPathGraph u (D.map ename) v := by
    have hrel := hQpath.relabelEdges ename_inj
    have hmap := hrel.map (by simpa [relabelled] using vname_inj)
    simpa [ear, relabelled, vname_a, vname_b] using hmap
  have hear_disjoint : Disjoint V(ear) E(ear) := by
    rw [Set.disjoint_left]
    rintro z hzV hzE
    rw [hVear] at hzV
    rw [hEear] at hzE
    obtain ⟨x, hxQ, rfl⟩ := hzV
    obtain ⟨e, heQ, heq⟩ := hzE
    have hedgeAvoid := ename_avoid heQ
    apply hedgeAvoid
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl (by rw [heq, vname_a]; exact huCell)
    rcases eq_or_ne x b with rfl | hxb
    · exact Or.inl (by rw [heq, vname_b]; exact hvCell)
    · exact Or.inr ⟨x, ⟨hxQ, by simp [hxa, hxb]⟩, heq.symm⟩
  have hvertex_inter : V(ear) ∩ V(T.str.skel) = {u, v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzEar, hzOld⟩
      rw [hVear] at hzEar
      obtain ⟨x, hxQ, rfl⟩ := hzEar
      rcases eq_or_ne x a with rfl | hxa
      · simp [vname_a]
      rcases eq_or_ne x b with rfl | hxb
      · simp [vname_b]
      exfalso
      exact vname_fresh x hxQ hxa hxb (T.str.mem_cells_of_mem_vertexSet hzOld)
    · rintro z (rfl | rfl)
      · exact ⟨hVear ▸ ⟨a, haQ, vname_a⟩, hu⟩
      · exact ⟨hVear ▸ ⟨b, hbQ, vname_b⟩, hv⟩
  have hface₁Avoid : face₁ ∉ faceUsed := freshFace_avoid 0
  have hface₂Avoid : face₂ ∉ faceUsed := freshFace_avoid 1
  let d : T.str.SplitData := {
    face := F
    face₁ := face₁
    face₂ := face₂
    ear := ear
    source := u
    target := v
    earWalk := D.map ename
    path₁ := paths.path₁
    path₂ := paths.path₂
    isPathGraph := hearPath
    isPath₁ := paths.isPath₁
    isPath₂ := paths.isPath₂
    ear_disjoint := hear_disjoint
    source_ne_target := huv
    face_mem := hF
    vertexSet_inter := hvertex_inter
    edge_fresh := by
      intro e he
      rw [hEear] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact fun hmem => ename_avoid hf (Or.inl hmem)
    vertex_fresh := by
      intro z hz hzu hzv
      rw [hVear] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ a := fun h => hzu (h ▸ vname_a)
      have hxb : x ≠ b := fun h => hzv (h ▸ vname_b)
      exact vname_fresh x hx hxa hxb
    face₁_notMem := fun h => hface₁Avoid (Or.inl (Or.inl h))
    face₂_notMem := fun h => hface₂Avoid (Or.inl (Or.inl h))
    face₁_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₁Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₁Avoid (Or.inr hz)
    face₂_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₂Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₂Avoid (Or.inr hz)
    face_ne := fun h => Fin.zero_ne_one (freshFace_inj h)
    sub_face := paths.sub_face
    paths_meet := paths.paths_meet
  }
  let tgtPos : γ → Plane := Function.invFunOn vname V(Q)
  let tgtDraw : γ → ℝ → Plane := Graph.relabelDrawing Q ename Hdraw
  have hQdraw : Graph.IsDrawing Q Hdraw := hH.isDrawing.mono hQle
  have hrelDraw : Graph.IsDrawing relabelled tgtDraw := hQdraw.relabelEdges ename_inj
  have hearGraph : d.earGraph tgtPos = relabelled := by
    change (relabelled.map vname).map tgtPos = relabelled
    simpa [tgtPos, relabelled] using
      (Graph.map_map_invFunOn (G := relabelled) (f := vname)
        (by simpa [relabelled] using vname_inj))
  have htgtSet : d.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D := by
    rw [CellStructure.SplitData.earSet, hearGraph, Graph.pointSet_relabelEdges ename_inj]
    simpa [Q] using hH.isDrawing.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)
  have htgtEdgeOrig := target_ear_edge_polygonal hH hpath hF hinside
  have htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) →
      IsPolygonal (Graph.edgeArc tgtDraw e) := by
    intro e he
    change e ∈ E(ear) at he
    rw [hEear] at he
    obtain ⟨f, hfQ, rfl⟩ := he
    rw [Graph.edgeArc_relabelDrawing ename_inj hfQ]
    apply htgtEdgeOrig f
    rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ
  have htgtPoly : IsPolygonal (d.earSet tgtPos tgtDraw) := by
    rw [htgtSet]
    exact hQdraw.isPolygonal_edgesCover
      (fun f hfQ => htgtEdgeOrig f (by
        rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ))
      hpath.pathGraphOf.isWalk (hpath.ne_nil hab)
  have htgt : d.EarCrosscut T.tgt tgtPos tgtDraw := {
    pos_source := by
      change tgtPos u = T.tgt.pos u
      rw [hua]
      change Function.invFunOn vname V(Q) u = a
      rw [← vname_a, vname_inj.leftInvOn_invFunOn haQ]
    pos_target := by
      change tgtPos v = T.tgt.pos v
      rw [hvb]
      change Function.invFunOn vname V(Q) v = b
      rw [← vname_b, vname_inj.leftInvOn_invFunOn hbQ]
    injOn := by
      change InjOn (Function.invFunOn vname V(Q)) V(ear)
      rw [hVear]
      exact Function.invFunOn_injOn_image vname V(Q)
    isDrawing := by rw [hearGraph]; exact hrelDraw
    subset_face := by
      rw [htgtSet]
      simpa [d, hua, hvb] using hinside
    disjoint_skeleton := T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition hF
    polygonal := htgtPoly
  }
  refine ⟨{
    splitData := d
    tgtPos := tgtPos
    tgtDraw := tgtDraw
    tgtCrosscut := htgt
    tgtEdgePolygonal := htgtEdgePoly
    tgtEarSet_eq := htgtSet
    vertexSet_subset := ?_
  }⟩
  change V(B.union (H.pathGraphOf a D)) ⊆
    V((T.str.splitFace d).skel.map (d.splitPos T.tgt tgtPos))
  rw [htgt.splitGraph_eq]
  intro x hx
  rcases hx with hxB | hxQ
  · exact Or.inl (hT.vertexSet_subset hxB)
  · apply Or.inr
    rw [hearGraph, Graph.vertexSet_relabelEdges]
    exact hxQ

/-! ### The exact geometric obligation on the source side -/

/-- Source vertices incident with a nonboundary edge.  Outer-only vertices are deliberately
excluded: a fresh anchor must not enter the compact set merely because it is already a vertex
of the outer cycle. -/
def GeneratedPair.sourceNonboundaryVertices
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) : Set Plane :=
  {x | ∃ e, e ∈ E(T.src.graph) ∧ e ∉ E(T.str.outerGraph) ∧ T.src.graph.Inc e x}

/-- The current source graph with outer edges and outer-only vertices removed.  Its point set is
the compact union of the closed nonboundary edges used in the fresh-anchor argument. -/
def GeneratedPair.sourceNonboundaryGraph
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) : Graph Plane γ :=
  (T.src.graph.deleteEdges E(T.str.outerGraph)).induce T.sourceNonboundaryVertices

theorem GeneratedPair.sourceNonboundaryGraph_le
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.sourceNonboundaryGraph ≤ T.src.graph := by
  apply (Graph.induce_le ?_).trans Graph.deleteEdges_le
  rintro x ⟨e, -, -, hinc⟩
  exact hinc.vertex_mem

instance GeneratedPair.sourceNonboundaryGraph_finite
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.sourceNonboundaryGraph.Finite :=
  Graph.Finite.of_le T.sourceNonboundaryGraph_le

/-- The source skeleton is the union of its compact nonboundary-edge carrier and its outer
curve. -/
theorem GeneratedPair.skeletonSet_eq_sourceNonboundaryGraph_union
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.src.skeletonSet = pointSet T.sourceNonboundaryGraph T.src.drawing ∪ srcOuter := by
  have hdecomp : T.src.skeletonSet =
      pointSet T.sourceNonboundaryGraph T.src.drawing ∪ T.src.outerSet := by
    apply Set.Subset.antisymm
    · intro x hx
      change x ∈ pointSet T.src.graph T.src.drawing at hx
      rcases hx with hxV | hxE
      · obtain ⟨e, he, hinc⟩ : ∃ e, e ∈ E(T.src.graph) ∧ T.src.graph.Inc e x := by
          obtain ⟨z, hz, hzx, -⟩ :=
            T.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
          obtain ⟨D, hD⟩ :=
            T.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hxV hz
          obtain ⟨e, heD, hinc⟩ :=
            hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
          exact ⟨e, hD.edge_mem heD, hinc⟩
        by_cases heOuter : e ∈ E(T.str.outerGraph)
        · apply Or.inr
          apply Graph.vertexSet_subset_pointSet
          have hOle : T.str.outerGraph.map T.src.pos ≤ T.src.graph :=
            T.str.outerGraph_le.map T.src.pos
          exact ((hOle.inc_congr (by rwa [Graph.edgeSet_map])).2 hinc).vertex_mem
        · apply Or.inl
          apply Graph.vertexSet_subset_pointSet
          exact ⟨e, he, heOuter, hinc⟩
      · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
        by_cases heOuter : e ∈ E(T.str.outerGraph)
        · exact Or.inr (Graph.edgeArc_subset_pointSet (by
            rw [Graph.edgeSet_map]
            exact heOuter) hxe)
        · apply Or.inl
          exact Graph.edgeArc_subset_pointSet (by
            obtain ⟨u, v, huv⟩ := T.src.graph.exists_isLink_of_mem_edgeSet he
            exact ⟨u, v, ⟨⟨huv, heOuter⟩,
              ⟨e, he, heOuter, huv.inc_left⟩, ⟨e, he, heOuter, huv.inc_right⟩⟩⟩) hxe
    · exact Set.union_subset
        (Graph.pointSet_mono T.sourceNonboundaryGraph_le)
        T.src.outerSet_subset_skeletonSet
  exact hdecomp.trans (congrArg (pointSet T.sourceNonboundaryGraph T.src.drawing ∪ ·)
    T.src_isWeaklyAdmissible.outerSet_eq)

theorem GeneratedPair.isCompact_sourceNonboundaryGraph
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    IsCompact (pointSet T.sourceNonboundaryGraph T.src.drawing) :=
  (T.src.isDrawing.mono T.sourceNonboundaryGraph_le).isCompact_pointSet

/-- Inside the open Jordan domain, avoiding the compact nonboundary-edge carrier is equivalent
to avoiding the whole current skeleton; the remaining part of the latter is the outer curve. -/
theorem GeneratedPair.source_cellsAbsorbIn_nonboundary
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    CellsAbsorbIn (srcDom \ srcOuter)
      (pointSet T.sourceNonboundaryGraph T.src.drawing)
      {A | ∃ F ∈ T.str.faces, A = T.src.cell F} := by
  intro N hND hN hNdisj R hR hmeet
  apply (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
    N hN ?_ R hR hmeet
  rw [Set.disjoint_left]
  intro x hxN hxSkel
  rw [T.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSkel
  rcases hxSkel with hxCore | hxOuter
  · exact Set.disjoint_left.1 hNdisj hxN hxCore
  · exact (hND hxN).2 hxOuter

/-- Every point of the open source domain outside the compact nonboundary-edge carrier lies in
one current source face. -/
theorem GeneratedPair.exists_source_face_of_mem_interior_notMem_nonboundary
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {x : Plane}
    (hx : x ∈ srcDom \ srcOuter)
    (hxCore : x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing) :
    ∃ R ∈ {A : Set Plane | ∃ F ∈ T.str.faces, A = T.src.cell F}, x ∈ R := by
  have hxSkel : x ∉ T.src.skeletonSet := by
    rw [T.skeletonSet_eq_sourceNonboundaryGraph_union]
    rintro (hcore | houter)
    · exact hxCore hcore
    · exact hx.2 houter
  have hxDom : x ∈ ⋃ σ ∈ T.str.cells, T.src.cell σ := by
    rw [T.src_isCellDecomposition.iUnion_eq]
    exact hx.1
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hxDom
  have hσFace : σ ∈ T.str.faces := by
    rcases hσ with (hv | he) | hface
    · exact absurd (T.src.cell_subset_skeletonSet (Or.inl hv) hxσ) hxSkel
    · exact absurd (T.src.cell_subset_skeletonSet (Or.inr he) hxσ) hxSkel
    · exact hface
  exact ⟨T.src.cell σ, ⟨σ, hσFace, rfl⟩, hxσ⟩

/-- A fresh strongly accessible boundary anchor is accessible from its unique incident current
source face.  Compactness, absorption, and coverage are all discharged from the generated-pair
invariants; the three hypotheses are exactly the data maintained by the prescribed ear order. -/
theorem GeneratedPair.source_polyAccessible_of_fresh
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} {x : Plane}
    (hstrong : StronglyAccessible (srcDom \ srcOuter) x)
    (hfresh : x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing)
    (hunique : ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
      x ∈ closure R → R = T.src.cell F) :
    PolyAccessible (T.src.cell F) x := by
  exact polyAccessible_of_stronglyAccessible_in hstrong
    T.isCompact_sourceNonboundaryGraph hfresh T.source_cellsAbsorbIn_nonboundary
    (fun _ hy hycore =>
      T.exists_source_face_of_mem_interior_notMem_nonboundary hy hycore) hunique

/-- A point in the closure of a current source face is polygonally accessible whenever it is
off the wild outer curve.  The polygonal graph used by `polygonal_side_accessibility` is the
current skeleton with its outer edges deleted; adjoining the compact outer curve recovers the
whole source skeleton. -/
theorem GeneratedPair.source_polyAccessible_of_notMem_outer
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} {x : Plane} (hF : F ∈ T.str.faces) (hx : x ∈ closure (T.src.cell F))
    (hxOuter : x ∉ srcOuter) : PolyAccessible (T.src.cell F) x := by
  let G := T.src.graph.deleteEdges E(T.str.outerGraph)
  let O := T.str.outerGraph.map T.src.pos
  have hOle : O ≤ T.src.graph := T.str.outerGraph_le.map T.src.pos
  have hGunion : G.union O = T.src.graph := by
    apply Graph.eq_of_le_of_subset_subset (Graph.union_le Graph.deleteEdges_le hOle)
    · intro z hz
      exact Or.inl (by rwa [Graph.vertexSet_deleteEdges])
    · intro e he
      by_cases heOuter : e ∈ E(T.str.outerGraph)
      · exact Or.inr (by rwa [Graph.edgeSet_map])
      · exact Or.inl (Graph.mem_edgeSet_deleteEdges_iff.2 ⟨he, heOuter⟩)
  have hK : T.src.skeletonSet = pointSet G T.src.drawing ∪ srcOuter := by
    change pointSet T.src.graph T.src.drawing = _
    rw [← hGunion, Graph.pointSet_union]
    change pointSet G T.src.drawing ∪ T.src.outerSet = _
    rw [T.src_isWeaklyAdmissible.outerSet_eq]
  letI : G.Finite := Graph.Finite.of_le Graph.deleteEdges_le
  have hGdraw : G.IsDrawing T.src.drawing := T.src.isDrawing.mono Graph.deleteEdges_le
  have hGpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc T.src.drawing e) := by
    intro e he
    rw [Graph.mem_edgeSet_deleteEdges_iff] at he
    exact T.src_isWeaklyAdmissible.isPolygonal he.1 he.2
  let cells : Set (Set Plane) := {A | ∃ Z ∈ T.str.faces, A = T.src.cell Z}
  have hFcells : T.src.cell F ∈ cells := ⟨F, hF, rfl⟩
  have hdisj : Disjoint (T.src.cell F) T.src.skeletonSet :=
    T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF
  letI : O.Finite := Graph.Finite.of_le hOle
  have houterCompact : IsCompact srcOuter := by
    rw [← T.src_isWeaklyAdmissible.outerSet_eq]
    exact T.src.isCompact_skeletonSet.of_isClosed_subset
      (T.src.isDrawing.mono hOle).isClosed_pointSet T.src.outerSet_subset_skeletonSet
  exact Graph.polygonal_side_accessibility hGdraw hGpoly
    houterCompact hK (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
    hFcells hdisj hx hxOuter

/-- The two ways a source endpoint is ready for a reverse ear: it is off the wild curve, or it
is a fresh strongly accessible anchor incident with one prescribed current face. -/
def GeneratedPair.SourceEndpointReady
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (x : Plane) : Prop :=
  x ∉ srcOuter ∨
    StronglyAccessible (srcDom \ srcOuter) x ∧
      x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing ∧
      ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
        x ∈ closure R → R = T.src.cell F

/-- The combinatorial/anchoring invariant still required from the prescribed target ear order:
both source endpoints selected by every nontrivial target ear are ready in the preceding sense. -/
def TargetEarFreshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a D,
        T.SourceEndpointReady w.splitData.face (T.src.pos w.splitData.source) ∧
        T.SourceEndpointReady w.splitData.face (T.src.pos w.splitData.target)

/-- Both source endpoints of every nontrivial target ear are polygonally accessible from the
source face selected by that ear.  This is the geometric invariant direction (b) must maintain:
off the wild curve it follows from polygonal-side accessibility, while a fresh wild-boundary
endpoint is supplied by `polyAccessible_of_stronglyAccessible`. -/
def TargetEarEndpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a D,
        PolyAccessible (T.src.cell w.splitData.face) (T.src.pos w.splitData.source) ∧
        PolyAccessible (T.src.cell w.splitData.face) (T.src.pos w.splitData.target)

/-- The fresh-anchor invariant implies the endpoint-accessibility invariant: the off-curve
branch uses polygonal-side accessibility, and the fresh branch uses the compact carrier and
unique-face theorem above. -/
theorem targetEarEndpointAccessibility_of_freshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    TargetEarEndpointAccessibility P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceReady, htargetReady⟩ :=
    hfresh B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have hsourceClosure : T.src.pos d.source ∈ closure (T.src.cell d.face) := by
    have hsub := T.src_isCellDecomposition.subset_closure
      (T.str.mem_cells_of_mem_vertexSet d.source_mem_skel)
      (T.str.mem_cells_of_mem_faces d.face_mem) hsourceSub
    rw [T.src.cell_vertex d.source_mem_skel] at hsub
    exact hsub (Set.mem_singleton _)
  have htargetClosure : T.src.pos d.target ∈ closure (T.src.cell d.face) := by
    have hsub := T.src_isCellDecomposition.subset_closure
      (T.str.mem_cells_of_mem_vertexSet d.target_mem_skel)
      (T.str.mem_cells_of_mem_faces d.face_mem) htargetSub
    rw [T.src.cell_vertex d.target_mem_skel] at hsub
    exact hsub (Set.mem_singleton _)
  constructor
  · rcases hsourceReady with houter | ⟨hstrong, hnew, hunique⟩
    · exact T.source_polyAccessible_of_notMem_outer d.face_mem hsourceClosure houter
    · exact T.source_polyAccessible_of_fresh hstrong hnew hunique
  · rcases htargetReady with houter | ⟨hstrong, hnew, hunique⟩
    · exact T.source_polyAccessible_of_notMem_outer d.face_mem htargetClosure houter
    · exact T.source_polyAccessible_of_fresh hstrong hnew hunique

/-- Endpoint accessibility supplies the missing source crosscut, after which the already-proved
arc matching and split constructor complete one nontrivial reverse ear. -/
theorem targetEarStepConstruction_of_endpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    TargetEarStepConstruction P H Hdraw hH := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨w⟩ := exists_targetSideEarStepData P H Hdraw hH
    B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨hsource, htarget⟩ :=
    haccess B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  let d := w.splitData
  have hends : T.src.pos d.source ≠ T.src.pos d.target := fun h =>
    d.source_ne_target (T.src.injOn_pos d.source_mem_skel d.target_mem_skel h)
  obtain ⟨A, hApoly, hAarc, hAsub⟩ :=
    exists_simple_arc_of_polyAccessible
      (T.src_isFaceJordan.isOpen d.face_mem)
      (T.src_isFaceJordan.isConnected d.face_mem).isPreconnected
      hends hsource htarget
  obtain ⟨srcPos, srcDraw, reverseHomeo, hsrc, hsrcEdgePoly⟩ :=
    w.tgtCrosscut.exists_matched_target hApoly hAarc hAsub
      (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition d.face_mem)
  exact ⟨{
    splitData := d
    srcPos := srcPos
    srcDraw := srcDraw
    tgtPos := w.tgtPos
    tgtDraw := w.tgtDraw
    srcCrosscut := hsrc
    tgtCrosscut := w.tgtCrosscut
    earHomeo := reverseHomeo.symm
    srcEdgePolygonal := hsrcEdgePoly
    tgtEdgePolygonal := w.tgtEdgePolygonal
    tgtEarSet_eq := w.tgtEarSet_eq
    vertexSet_subset := w.vertexSet_subset
  }⟩

/-- One reverse ear follows from the endpoint-accessibility invariant. -/
theorem targetEarStep_of_endpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    TargetEarStep P H Hdraw :=
  targetEarStep_of_data hH
    (targetEarStepConstruction_of_endpointAccessibility P H Hdraw hH haccess)

/-- One reverse ear follows from the concrete fresh-anchor/unique-face invariant. -/
theorem targetEarStep_of_freshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    TargetEarStep P H Hdraw :=
  targetEarStep_of_endpointAccessibility P H Hdraw hH
    (targetEarEndpointAccessibility_of_freshInvariant P H Hdraw hfresh)

/-- Explicit output data for the target common-subdivision construction. -/
structure TargetCommonSubdivisionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) where
  /-- The part of `H` supported on the old target skeleton. -/
  graph : Graph Plane γ
  /-- The matched pair after inserting every vertex of `graph`. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite parent map from the subdivided pair to `P`. -/
  parent : γ → γ
  /-- The traced graph remains 2-connected. -/
  graph_isTwoConnected : graph.IsTwoConnected
  /-- The traced graph is a subgraph of the given target extension. -/
  graph_le : graph ≤ H
  /-- The refined pair realizes the traced target graph. -/
  isTargetPartialTransferOf : IsTargetPartialTransferOf pair P graph Hdraw parent

/-- Construct the target trace, its matched subdivision, and the composite parent map. -/
noncomputable def targetCommonSubdivisionData [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    TargetCommonSubdivisionData P H Hdraw := by
  classical
  let K := Graph.traceGraph H Hdraw P.tgt.skeletonSet
  have hKle : K ≤ H := Graph.traceGraph_le _
  letI : H.Finite := hH.finite
  letI : K.Finite := Graph.Finite.of_le hKle
  have hK2 : K.IsTwoConnected :=
    trace_isTwoConnected hH P.tgt_isWeaklyAdmissible.isTwoConnected
  have hvertices : V(K) ⊆ P.tgt.skeletonSet := by
    intro x hx
    rw [Graph.traceGraph_vertexSet] at hx
    exact hx.2
  let w := Classical.choice (GeneratedPair.exists_subdivideTargetSetData P
    (Graph.finite_vertexSet K) hvertices)
  exact {
    graph := K
    pair := w.pair
    parent := w.parent
    graph_isTwoConnected := hK2
    graph_le := hKle
    isTargetPartialTransferOf := {
      refines_src := w.refines_src
      refines_tgt := w.refines_tgt
      skeletonSet_eq := w.skeletonSet_eq.trans (trace_pointSet hH).symm
      vertexSet_subset := w.vertexSet_subset
    }
  }

/-- **Step 1 of finite transfer, direction (b): construct the target common subdivision.** -/
theorem targetCommonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    TargetCommonSubdivision P H Hdraw := by
  let w := targetCommonSubdivisionData hH
  exact ⟨w.graph, w.pair, w.parent, w.graph_isTwoConnected, w.graph_le,
    w.isTargetPartialTransferOf⟩

/-- Iterate a target ear step from a common subdivision through the whole extension graph. -/
theorem targetTransferOfEars [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hsub : TargetCommonSubdivision P H Hdraw) (hstep : TargetEarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P H Hdraw par := by
  haveI := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsTargetPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-- Direction (b), conditional only on the target ear step. -/
theorem finite_transfer_toward_source_of_targetEarStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hstep : TargetEarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ :=
    targetTransferOfEars hH (targetCommonSubdivision hH) hstep
  have hconnTgt : IsConnected T.tgt.nonboundary := by
    rw [CellStructure.Realization.nonboundary,
      T.tgt_isWeaklyAdmissible.outerSet_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  have hconnSrc : IsConnected T.src.nonboundary :=
    T.homeo.isConnected_nonboundary_iff.2 hconnTgt
  exact ⟨T, par, hT, T.src_isAdmissible hconnSrc, T.tgt_isAdmissible hconnSrc⟩

/-- Direction (b), reduced to the precise geometric endpoint-accessibility invariant maintained
by the prescribed outer-cycle ear order. -/
theorem finite_transfer_toward_source_of_endpointAccessibility [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_targetEarStep hH
    (targetEarStep_of_endpointAccessibility P H Hdraw hH haccess)

/-- Direction (b), reduced to the prescribed ear order's concrete fresh-anchor and
unique-incident-face invariant.  All geometric accessibility and reverse-split construction is
discharged. -/
theorem finite_transfer_toward_source_of_freshInvariant [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_endpointAccessibility hH
    (targetEarEndpointAccessibility_of_freshInvariant P H Hdraw hfresh)

end Schoenflies
