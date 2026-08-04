/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransferTargetMesh
import Schoenflies.SkeletonLocal

/-!
# Overlaying a target skeleton with the anchored square mesh

A fresh square mesh does not generally contain the current target skeleton: already at stage
zero the target has an arbitrary straight chord which need not be radial or lie on a mesh ring.
The ambient graph for reverse finite transfer must therefore be the polygonal overlay of the
two finite segment families.

`TargetSegmentCover` writes the whole current target skeleton as a finite exact segment cover.
It also remembers which old abstract edge supplied each segment; that provenance is what will
prove the subdivision clause after transverse intersections have been made vertices.

`TargetSegmentCover.meshOverlay` is the combined graph.  Its cut list contains both the mesh
anchors and every old target vertex.  The basic carrier, drawing, containment, and edge-source
facts are established here; 2-connectivity, connectedness off the boundary, and the fresh
boundary-incidence property are the remaining assembly facts.

## Blueprint

* `Schoenflies.TargetSegmentCover` — the finite segment presentation of the current polygonal
  target skeleton.
* `Schoenflies.GeneratedPair.exists_targetSegmentCover` — every generated pair supplies that
  presentation.
* `Schoenflies.TargetSegmentCover.meshOverlay` — the current target skeleton overlaid with the
  anchored square mesh.
* `Schoenflies.TargetSegmentCover.meshOverlay_pointSet` — the combined graph occupies exactly
  the union of the two carriers.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- A finite exact segment presentation of the target skeleton, with each segment traced back
to an old abstract edge. -/
structure TargetSegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) where
  /-- The straight segments covering the target skeleton. -/
  pieces : List Piece
  /-- No listed segment is degenerate. -/
  nondeg : ∀ Q ∈ pieces, Q.Nondeg
  /-- The listed segments occupy exactly the target skeleton. -/
  cover_eq : cover pieces = P.tgt.skeletonSet
  /-- Every listed segment came from one old target edge. -/
  source : ∀ Q ∈ pieces, ∃ e ∈ E(P.str.skel), Q.seg ⊆ edgeArc P.tgt.drawing e

namespace GeneratedPair

/-- Every generated pair has a finite segment presentation of its polygonal target skeleton. -/
theorem exists_targetSegmentCover
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    Nonempty (TargetSegmentCover P) := by
  letI : Graph.Finite P.tgt.graph :=
    CellStructure.Realization.finite_graph P.tgt
  have hincident : ∀ z ∈ V(P.tgt.graph), ∃ e, P.tgt.graph.Inc e z := by
    intro z hz
    obtain ⟨w, hw, hwz, -⟩ :=
      P.tgt_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne z z
    obtain ⟨D, hD⟩ :=
      (P.tgt_isWeaklyAdmissible.isTwoConnected.connected.reaches hz hw).exists_isPath
    obtain ⟨e, -, hinc⟩ := hD.isWalk.exists_inc_source
      (hD.ne_nil (Ne.symm hwz))
    exact ⟨e, hinc⟩
  have hpoly : ∀ e ∈ E(P.tgt.graph), IsPolygonal (edgeArc P.tgt.drawing e) := by
    intro e he
    apply P.tgt_isPolygonal
    rwa [P.tgt.edgeSet_graph] at he
  obtain ⟨pieces, hnd, hcover, hsource⟩ :=
    P.tgt.isDrawing.exists_segmentCover (G := P.tgt.graph) hpoly hincident
  refine ⟨⟨pieces, hnd, hcover, ?_⟩⟩
  intro Q hQ
  obtain ⟨e, he, hsub⟩ := hsource Q hQ
  exact ⟨e, by rwa [P.tgt.edgeSet_graph] at he, hsub⟩

end GeneratedPair

namespace TargetSegmentCover

variable {P : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}

/-- The two source families for the combined target overlay. -/
noncomputable def meshPieces (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh : List Plane) : List Piece :=
  Q.pieces ++ meshSegments (meshCount delta) fresh

/-- The target skeleton overlaid with the anchored square mesh.  Old vertices and prescribed
mesh anchors are explicitly included in the cut list. -/
noncomputable def meshOverlay (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : Graph Plane Piece :=
  attachGraph (Q.meshPieces delta fresh)
    (anchors ++ P.tgt.graph.vertexFinset.toList)

instance meshOverlay_finite (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : (Q.meshOverlay delta fresh anchors).Finite :=
  attachGraph_finite _ _

/-- Every source segment of the combined overlay is nondegenerate. -/
theorem meshPieces_nondeg (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (delta : ℝ) :
    ∀ R ∈ Q.meshPieces delta fresh, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact Q.nondeg R hR
  · exact meshSegments_nondeg (two_le_meshCount delta) hfresh R hR

/-- The combined overlay is a finite straight-line plane graph. -/
theorem meshOverlay_isDrawing (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (Q.meshOverlay delta fresh anchors) segmentDrawing :=
  attachGraph_isDrawing (Q.meshPieces_nondeg hfresh delta) _

/-- The combined overlay occupies exactly the current target skeleton together with the square
mesh. -/
theorem meshOverlay_pointSet (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing =
      P.tgt.skeletonSet ∪
        Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  rw [meshOverlay, attachGraph_pointSet, meshPieces, cover_append, Q.cover_eq,
    squareMesh_pointSet]

/-- The current target skeleton is contained in the combined overlay. -/
theorem targetSkeleton_subset_meshOverlay (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    P.tgt.skeletonSet ⊆
      Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  rw [Q.meshOverlay_pointSet]
  exact subset_union_left

/-- The whole anchored square mesh is contained in the combined overlay. -/
theorem squareMesh_subset_meshOverlay (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing ⊆
      Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing := by
  rw [Q.meshOverlay_pointSet]
  exact subset_union_right

/-- Every old target vertex is explicitly retained as a vertex of the combined overlay. -/
theorem targetVertices_subset_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    V(P.tgt.graph) ⊆ V(Q.meshOverlay delta fresh anchors) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh)
    (attachPoints (Q.meshPieces delta fresh)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right anchors (by
      rw [Finset.mem_toList, mem_vertexFinset]
      exact hx)
  · rw [meshPieces, cover_append, Q.cover_eq]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- Every edge of the combined overlay is a subsegment either of an old target segment or of a
square-mesh source segment. -/
theorem meshOverlay_edge_source (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ E(Q.meshOverlay delta fresh anchors)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ meshSegments (meshCount delta) fresh, R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.meshPieces delta fresh)
    (attachPoints (Q.meshPieces delta fresh)
      (anchors ++ P.tgt.graph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · exact Or.inr ⟨A, hA, hsub⟩

/-- Away from the vertices created by the overlay, an overlay edge meeting an old open target
edge is one of its subdivision pieces.  At a transverse crossing the common point is an overlay
vertex, so the hypothesis is intentionally false there. -/
theorem meshOverlay_edge_subset (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    ∀ ⦃e⦄, e ∈ E(P.str.skel) → ∀ ⦃R : Piece⦄,
      R ∈ E(Q.meshOverlay delta fresh anchors) →
      (edgeArc segmentDrawing R ∩
        (P.tgt.cell e \ V(Q.meshOverlay delta fresh anchors))).Nonempty →
      edgeArc segmentDrawing R ⊆ edgeArc P.tgt.drawing e := by
  intro e he R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ edgeArc P.tgt.drawing e := by
    rw [P.tgt.cell_edge hab] at hzCell
    exact hzCell.1
  have hznotOldVertex : z ∉ V(P.tgt.graph) := by
    intro hzV
    rcases P.tgt.isDrawing.vertex_mem_edgeArc (hab.map P.tgt.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.tgt.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.tgt.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have hzSkeleton : z ∈ P.tgt.skeletonSet :=
    P.tgt.cell_subset_skeletonSet (Or.inr he) hzCell
  have hzCover : z ∈ cover Q.pieces := by
    rw [Q.cover_eq]
    exact hzSkeleton
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, hAg⟩ := Q.source A hA
  have hzg : z ∈ edgeArc P.tgt.drawing g := hAg hzA
  have heg : e = g := P.tgt.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ edgeArc P.tgt.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.meshPieces delta fresh)
        (anchors ++ P.tgt.graph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_left _ hA) hzA
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- The combined overlay stays in the closed target square. -/
theorem meshOverlay_pointSet_subset (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing ⊆
      Plane.closedSquare 0 1 := by
  rw [Q.meshOverlay_pointSet]
  exact Set.union_subset P.tgt_isWeaklyAdmissible.skeletonSet_subset
    (squareMesh_pointSet_subset hfresh delta anchors)

/-- Every combined-overlay edge either lies on the model curve or is a polygonal edge whose
nonvertex points lie in the open target square.  A nonouter edge cannot meet the model curve
away from overlay vertices: the outer-ring segment through such a point would give a second
edge of the plane drawing there. -/
theorem meshOverlay_edge_dichotomy (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    ∀ ⦃R⦄, R ∈ E(Q.meshOverlay delta fresh anchors) →
      edgeArc segmentDrawing R ⊆ modelCurve ∨
        (IsPolygonal (edgeArc segmentDrawing R) ∧
          edgeArc segmentDrawing R \ V(Q.meshOverlay delta fresh anchors) ⊆
            Plane.closedSquare 0 1 \ modelCurve) := by
  intro R hR
  by_cases houter : edgeArc segmentDrawing R ⊆ modelCurve
  · exact Or.inl houter
  · refine Or.inr ⟨?_, ?_⟩
    · rw [edgeArc_segmentDrawing]
      exact isPolygonal_segment _ _
    · intro x hx
      refine ⟨Q.meshOverlay_pointSet_subset hfresh delta anchors
        (Graph.edgeArc_subset_pointSet hR hx.1), ?_⟩
      intro hxOuter
      have hxRing : x ∈ cover (ringPieces 1) := by
        rw [cover_ringPieces zero_le_one, ringSet_one]
        exact hxOuter
      obtain ⟨A, hA, hxA⟩ := mem_cover_iff.1 hxRing
      have hAmesh : A ∈ meshSegments (meshCount delta) fresh :=
        outer_ringPieces_mem (two_le_meshCount delta) hA
      obtain ⟨R', hR', hxR', hR'A⟩ :=
        exists_overlayPiece_mem_subset
          (points := attachPoints (Q.meshPieces delta fresh)
            (anchors ++ P.tgt.graph.vertexFinset.toList))
          (P₀ := A) (List.mem_append_right Q.pieces hAmesh) hxA
      have hxR'Arc : x ∈ edgeArc segmentDrawing R' := by
        rwa [edgeArc_segmentDrawing]
      have hRR' : R = R' :=
        (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
          hR hR' hx.2 hx.1 hxR'Arc
      apply houter
      rw [hRR', edgeArc_segmentDrawing]
      exact hR'A.trans (by
        rw [← ringSet_one]
        exact ringPieces_seg_subset zero_le_one hA)

/-- After injective edge relabelling, the combined overlay is a target extension as soon as its
two genuinely global assembly properties—2-connectivity and connectedness off the boundary—are
available.  Every local subdivision and geometric field is discharged above. -/
theorem isSourceExtension_relabelledMeshOverlay
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (htwo : (Q.meshOverlay delta fresh anchors).IsTwoConnected)
    (hconnected : IsConnected
      (Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing \ modelCurve)) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) where
  finite := Graph.Finite.relabelEdges hname
  isDrawing := (Q.meshOverlay_isDrawing hfresh delta anchors).relabelEdges hname
  isTwoConnected := htwo.relabelEdges hname
  vertexSet_subset := by
    rw [Graph.vertexSet_relabelEdges]
    exact Q.targetVertices_subset_meshOverlay hfresh delta anchors
  skeletonSet_subset := by
    rw [Graph.pointSet_relabelEdges hname]
    exact Q.targetSkeleton_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he d hd hmeet
    obtain ⟨R, hR, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hR,
      Graph.vertexSet_relabelEdges] at hmeet
    rw [Graph.edgeArc_relabelDrawing hname hR]
    exact Q.meshOverlay_edge_subset hfresh delta anchors he hR hmeet
  pointSet_subset := by
    rw [Graph.pointSet_relabelEdges hname]
    exact Q.meshOverlay_pointSet_subset hfresh delta anchors
  edge_dichotomy := by
    intro d hd
    obtain ⟨R, hR, rfl⟩ := hd
    rw [Graph.edgeArc_relabelDrawing hname hR,
      Graph.vertexSet_relabelEdges]
    exact Q.meshOverlay_edge_dichotomy hfresh delta anchors hR
  isConnected := by
    rw [Graph.pointSet_relabelEdges hname]
    exact hconnected

/-- Fresh cell names for every edge of the combined target overlay, avoiding all names already
used by the current generated structure. -/
theorem exists_meshOverlay_edgeRelabeling
    [Infinite γ] (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) :
    ∃ name : Piece → γ, InjOn name E(Q.meshOverlay delta fresh anchors) ∧
      ∀ e ∈ E(Q.meshOverlay delta fresh anchors), name e ∉ P.str.cells :=
  exists_finiteGraph_edgeRelabeling_avoiding γ (Q.meshOverlay delta fresh anchors)
    P.str.cells P.str.finite_cells

end TargetSegmentCover

end Schoenflies
