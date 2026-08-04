/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransferTarget
import Schoenflies.SquareMeshClosed

/-!
# Anchored square meshes supply the boundary anchors for reverse finite transfer

`Schoenflies.TargetBoundaryAnchored` is the fixed geometric input isolated from finite-transfer
direction (b): every nonouter target edge ending on the model curve must end at the image of a
strongly accessible source anchor.

The anchored square mesh was built to have exactly this property.  Its clause 4,
`Schoenflies.squareMesh_inner_edge_at_fresh`, says that every mesh edge which meets the model
curve without lying in it meets the curve at one of the prescribed fresh points.  Thus, if the
fresh list consists of target images of strongly accessible source anchors, the whole boundary
condition follows with no ear-order argument.

## Blueprint

* `Schoenflies.targetBoundaryAnchored_squareMesh` — anchored-square-mesh clause 4 discharges the
  strong-accessibility input of reverse finite transfer.
* `Schoenflies.finite_transfer_toward_source_squareMesh` — direction (b) for an anchored square
  mesh, reduced only to the evolving fresh-incidence combinatorics.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {S₀ : CellStructure Piece} {srcOuter srcDom tgtDom : Set Plane}

/-- An anchored square mesh satisfies the fixed boundary-anchor condition for reverse finite
transfer.  The only hypothesis beyond membership in the model curve is the one the stage
constructor records: every prescribed fresh target point pulls back to a strongly accessible
source anchor. -/
theorem targetBoundaryAnchored_squareMesh
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ) :
    TargetBoundaryAnchored P (squareMesh delta fresh anchors) segmentDrawing := by
  intro f y hf hinc hy hnot
  have hdraw := squareMesh_isDrawing hfresh delta anchors
  obtain ⟨z, hlink⟩ := hinc
  have hyArc : y ∈ edgeArc segmentDrawing f :=
    (hdraw.edge_isArcBetween hlink).left_mem
  have hySeg : y ∈ f.seg := by
    rwa [edgeArc_segmentDrawing] at hyArc
  have hmeet : (f.seg ∩ modelCurve).Nonempty := ⟨y, hySeg, hy⟩
  have hnotSeg : ¬ f.seg ⊆ modelCurve := by
    simpa only [edgeArc_segmentDrawing] using hnot
  obtain ⟨w, hw, hinter, -, -⟩ :=
    squareMesh_inner_edge_at_fresh hfresh delta hf hmeet hnotSeg
  have hyw : y = w := by
    have : y ∈ ({w} : Set Plane) := hinter ▸ ⟨hySeg, hy⟩
    simpa only [Set.mem_singleton_iff] using this
  rw [hyw]
  exact hstrong w hw

/-- Reverse finite transfer for an anchored square mesh.  Strong accessibility is completely
discharged from the mesh's fresh-point clause; only carrier freshness and unique current-face
incidence remain for the prescribed ear order. -/
theorem finite_transfer_toward_source_squareMesh
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (hcomb : TargetEarFreshCombinatorics P
      (squareMesh delta fresh anchors) segmentDrawing) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom) (par : Piece → Piece),
      IsTargetTransferOf T P (squareMesh delta fresh anchors) segmentDrawing par :=
  finite_transfer_toward_source_of_boundaryAnchored hH
    (targetBoundaryAnchored_squareMesh P hfresh hstrong delta) hcomb

end Schoenflies
