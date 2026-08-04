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
* `Schoenflies.targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo` — mesh
  uniqueness and the local two-branch property of the generated outer cycle discharge the
  evolving fresh-incidence input.
* `Schoenflies.targetEarFreshCombinatorics_squareMesh_of_outerCycle` — the preceding local
  property follows from one simple-cycle check on the base structure.
* `Schoenflies.finite_transfer_toward_source_squareMesh` — direction (b) for an anchored square
  mesh, reduced only to the evolving fresh-incidence combinatorics.
* `Schoenflies.finite_transfer_toward_source_squareMesh_of_outerIncidenceAtMostTwo` — the same
  conclusion reduced to propagation of one static outer-cycle invariant.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {S₀ : CellStructure Piece} {srcOuter srcDom tgtDom : Set Plane}

/-- At a point of the model curve, two nonouter square-mesh edges cannot both be incident.
Clause 4 first recognizes the point as fresh from either edge, then its uniqueness half
identifies the two pieces. -/
theorem squareMesh_nonouter_incident_eq
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) {z : Plane} (hz : z ∈ modelCurve) {P Q : Piece}
    (hP : P ∈ E(squareMesh delta fresh anchors))
    (hQ : Q ∈ E(squareMesh delta fresh anchors))
    (hPinc : (squareMesh delta fresh anchors).Inc P z)
    (hQinc : (squareMesh delta fresh anchors).Inc Q z)
    (hPnot : ¬ edgeArc segmentDrawing P ⊆ modelCurve)
    (hQnot : ¬ edgeArc segmentDrawing Q ⊆ modelCurve) :
    P = Q := by
  have hdraw := squareMesh_isDrawing hfresh delta anchors
  have endpoint_data : ∀ {R : Piece}, R ∈ E(squareMesh delta fresh anchors) →
      (squareMesh delta fresh anchors).Inc R z →
      ¬ edgeArc segmentDrawing R ⊆ modelCurve →
      R ∈ E(squareMesh delta fresh anchors) ∧
        (z = R.1 ∨ z = R.2) ∧ ¬ R.seg ⊆ modelCurve ∧ z ∈ fresh := by
    intro R hR hRinc hRnot
    have hzArc : z ∈ edgeArc segmentDrawing R := hdraw.inc_mem_edgeArc hRinc
    have hzSeg : z ∈ R.seg := by
      rwa [edgeArc_segmentDrawing] at hzArc
    have hmeet : (R.seg ∩ modelCurve).Nonempty := ⟨z, hzSeg, hz⟩
    have hRnotSeg : ¬ R.seg ⊆ modelCurve := by
      simpa only [edgeArc_segmentDrawing] using hRnot
    obtain ⟨w, hwFresh, hinter, hwEnd, -⟩ :=
      squareMesh_inner_edge_at_fresh hfresh delta hR hmeet hRnotSeg
    have hzw : z = w := by
      have : z ∈ ({w} : Set Plane) := hinter ▸ ⟨hzSeg, hz⟩
      simpa only [Set.mem_singleton_iff] using this
    exact ⟨hR, hzw ▸ hwEnd, hRnotSeg, hzw ▸ hwFresh⟩
  have hPd := endpoint_data hP hPinc hPnot
  have hQd := endpoint_data hQ hQinc hQnot
  obtain ⟨R, hR, huniq⟩ :=
    squareMesh_unique_inner_edge hfresh delta anchors hPd.2.2.2
  exact (huniq P ⟨hPd.1, hPd.2.1, hPd.2.2.1⟩).trans
    (huniq Q ⟨hQd.1, hQd.2.1, hQd.2.2.1⟩).symm

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

/-- A wild-boundary endpoint of the next square-mesh ear is outer-only in the current
abstract skeleton.  If a current nonouter abstract edge reached it, local carrier reflection
would produce a current ambient nonouter edge there.  Clause 4 identifies that edge with the
new ear edge, contradicting that every edge of the ear is absent from the current graph. -/
theorem targetEarEndpointsOuterOnly_squareMesh
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    {B : Graph Plane Piece} {a b : Plane} {D : List Piece} {par : Piece → Piece}
    (hBH : B ≤ squareMesh delta fresh anchors)
    (hpath : (squareMesh delta fresh anchors).IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    {T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom}
    (hT : IsTargetPartialTransferOf T P B segmentDrawing par)
    (w : TargetSideEarStepData T B (squareMesh delta fresh anchors)
      segmentDrawing a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.source) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.target) := by
  letI : B.Finite := Graph.Finite.of_le hBH
  have hBdraw := hH.isDrawing.mono hBH
  have hinside : Graph.edgesCover segmentDrawing D \ {a, b} ⊆
      T.tgt.cell w.splitData.face := by
    intro x hx
    apply w.tgtCrosscut.subset_face
    refine ⟨?_, ?_⟩
    · rw [w.tgtEarSet_eq]
      exact hx.1
    · simpa only [w.target_pos_source, w.target_pos_target] using hx.2
  have hnotOuter := target_ear_edge_not_outer hH hpath w.splitData.face_mem hinside
  obtain ⟨eₛ, heₛ, hincₛ⟩ :=
    hpath.isWalk.exists_inc_source (hpath.ne_nil hab)
  obtain ⟨eₜ, heₜ, hincₜ⟩ :=
    hpath.reverse.isWalk.exists_inc_source (hpath.reverse.ne_nil (Ne.symm hab))
  have heₜD : eₜ ∈ D := by simpa using heₜ
  have endpoint_outerOnly : ∀ {v : Piece} {y : Plane} {e : Piece},
      v ∈ V(T.str.skel) → T.tgt.pos v = y → y ∈ V(B) →
      e ∈ D → (squareMesh delta fresh anchors).Inc e y →
      ¬ edgeArc segmentDrawing e ⊆ modelCurve →
      T.src.pos v ∈ srcOuter → T.str.OuterOnlyAt v := by
    intro v y e hv hpos hyB heD heinc henot hx
    have hyOuter : y ∈ modelCurve := by
      rw [← hpos]
      exact T.target_pos_mem_outer_of_source_pos_mem_outer hv hx
    intro g hg
    by_contra hgOuter
    have hvB : T.tgt.pos v ∈ V(B) := by rwa [hpos]
    have hvOuter : T.tgt.pos v ∈ modelCurve := by rwa [hpos]
    obtain ⟨f, hfB, hfincB, hfnot⟩ :=
      hT.exists_ambient_nonouter_incident hBdraw hvB hvOuter hg hgOuter
    have hfH : f ∈ E(squareMesh delta fresh anchors) := hBH.edgeSet_mono hfB
    have hfincH : (squareMesh delta fresh anchors).Inc f y := by
      rw [← hpos]
      exact (hBH.inc_congr hfB).1 hfincB
    have hef : e = f :=
      squareMesh_nonouter_incident_eq hfresh delta hyOuter
        (hpath.edge_mem heD) hfH heinc hfincH henot hfnot
    exact hnew e heD (by rwa [hef])
  constructor
  · intro hx
    exact endpoint_outerOnly (v := w.splitData.source) (y := a) (e := eₛ)
      w.splitData.source_mem_skel w.target_pos_source haB
      heₛ hincₛ (hnotOuter eₛ heₛ) hx
  · intro hx
    exact endpoint_outerOnly (v := w.splitData.target) (y := b) (e := eₜ)
      w.splitData.target_mem_skel w.target_pos_target hbB
      heₜD hincₜ (hnotOuter eₜ heₜD) hx

/-- For a square mesh, the reverse-ear fresh-incidence invariant follows from the static fact
that every generated outer graph is locally at most two-branched.  Clause 4 makes each new
wild-boundary endpoint outer-only; the local two-branch bound then makes its selected face the
unique incident face. -/
theorem targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (htwo : ∀ (S : CellStructure Piece), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    TargetEarFreshCombinatorics P (squareMesh delta fresh anchors) segmentDrawing := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceOuterOnly, htargetOuterOnly⟩ :=
    targetEarEndpointsOuterOnly_squareMesh P hfresh delta hH hBH hpath hab
      haB hbB hnew hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have htwoT := htwo T.str T.generated
  constructor
  · intro hx
    have houter : T.str.OuterOnlyAt d.source := hsourceOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.source_mem_skel houter,
      T.unique_source_face_of_outerOnly d.source_mem_skel d.face_mem hsourceSub
        houter (htwoT d.source)⟩
  · intro hx
    have houter : T.str.OuterOnlyAt d.target := htargetOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.target_mem_skel houter,
      T.unique_source_face_of_outerOnly d.target_mem_skel d.face_mem htargetSub
        houter (htwoT d.target)⟩

/-- It is enough to verify once, on the base cell structure, that the distinguished outer
edges form a simple cycle.  The two generated-structure constructors preserve that fact. -/
theorem targetEarFreshCombinatorics_squareMesh_of_outerCycle
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (hcycle : S₀.OuterEdgesFormCycle) :
    TargetEarFreshCombinatorics P (squareMesh delta fresh anchors) segmentDrawing :=
  targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo
    P hfresh delta hH fun _ h => h.outerIncidenceAtMostTwoEverywhere hcycle

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

/-- Reverse finite transfer for an anchored square mesh, reduced to a supplied propagation of
the static local outer-cycle invariant. -/
theorem finite_transfer_toward_source_squareMesh_of_outerIncidenceAtMostTwo
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (htwo : ∀ (S : CellStructure Piece), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom) (par : Piece → Piece),
      IsTargetTransferOf T P (squareMesh delta fresh anchors) segmentDrawing par :=
  finite_transfer_toward_source_squareMesh P hfresh hstrong delta hH
    (targetEarFreshCombinatorics_squareMesh_of_outerIncidenceAtMostTwo
      P hfresh delta hH htwo)

/-- Reverse finite transfer for an anchored square mesh from the natural base invariant: its
distinguished outer edges form a simple cycle. -/
theorem finite_transfer_toward_source_squareMesh_of_outerCycle
    (P : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom)
    {fresh anchors : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hstrong : ∀ z ∈ fresh,
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun z))
    (delta : ℝ)
    (hH : IsSourceExtension P.tgt modelCurve tgtDom
      (squareMesh delta fresh anchors) segmentDrawing)
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom modelCurve tgtDom) (par : Piece → Piece),
      IsTargetTransferOf T P (squareMesh delta fresh anchors) segmentDrawing par :=
  finite_transfer_toward_source_squareMesh P hfresh hstrong delta hH
    (targetEarFreshCombinatorics_squareMesh_of_outerCycle P hfresh delta hH hcycle)

end Schoenflies
