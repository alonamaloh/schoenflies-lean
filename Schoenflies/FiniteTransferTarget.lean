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

The remaining ear induction differs from direction (a) only when a target ear has a fresh
endpoint on the model curve.  `Schoenflies.polyAccessible_of_stronglyAccessible` supplies the
source access arc at the corresponding wild-boundary anchor; its integration belongs to the next
section of this module.

## Blueprint

* `Schoenflies.IsTargetPartialTransferOf`, `Schoenflies.TargetCommonSubdivision` — the
  target-to-source analogues of the direction-(a) transfer interfaces.
* `Schoenflies.targetCommonSubdivision` — step 1 of `thm:finite-transfer`(b).
* `Schoenflies.TargetEarStep`, `Schoenflies.targetTransferOfEars` — the relative-ear induction
  for direction (b).
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

end Schoenflies
