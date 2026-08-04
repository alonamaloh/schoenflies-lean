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

`TargetSegmentCover.meshOverlay` is the combined graph.  It overlays the target cover with the
already-subdivided edges of the anchored mesh, and its cut list contains both the mesh anchors
and every old target vertex.  The basic carrier, drawing, containment, edge-source, and
2-connectivity facts are established here.  Connectedness off the boundary is reduced to the
quantitative statement that the mesh meets every connected piece of the old open skeleton;
that mesh-hitting statement and the fresh boundary-incidence property remain.

## Blueprint

* `Schoenflies.TargetSegmentCover` — the finite segment presentation of the current polygonal
  target skeleton.
* `Schoenflies.GeneratedPair.exists_targetSegmentCover` — every generated pair supplies that
  presentation.
* `Schoenflies.TargetSegmentCover.meshOverlay` — the current target skeleton overlaid with the
  anchored square mesh.
* `Schoenflies.TargetSegmentCover.meshOverlay_pointSet` — the combined graph occupies exactly
  the union of the two carriers.
* `Schoenflies.TargetSegmentCover.meshOverlay_isTwoConnected` — the two subdivision traces glue
  along two fresh boundary vertices to make the combined overlay 2-connected.
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

/-- The already-subdivided edges of the anchored square mesh, listed as straight pieces. -/
noncomputable def squareMeshPieces (delta : ℝ) (fresh anchors : List Plane) : List Piece :=
  (squareMesh delta fresh anchors).edgeFinset.toList

@[simp] theorem mem_squareMeshPieces {delta : ℝ} {fresh anchors : List Plane} {R : Piece} :
    R ∈ squareMeshPieces delta fresh anchors ↔ R ∈ E(squareMesh delta fresh anchors) := by
  simp [squareMeshPieces, Graph.mem_edgeFinset]

/-- Listing the edges loses no carrier: every square-mesh vertex is an end of one of its
edges. -/
theorem cover_squareMeshPieces (delta : ℝ) (fresh anchors : List Plane) :
    cover (squareMeshPieces delta fresh anchors) =
      Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  ext x
  constructor
  · intro hx
    obtain ⟨R, hR, hxR⟩ := mem_cover_iff.1 hx
    exact Or.inr (Set.mem_iUnion₂_of_mem (mem_squareMeshPieces.1 hR) (by
      rwa [edgeArc_segmentDrawing]))
  · intro hx
    rcases hx with hxV | hxE
    · obtain ⟨R, hR, hxR⟩ := meshGraph_mem_vertexSet.1 hxV
      exact mem_cover_iff.2 ⟨R, mem_squareMeshPieces.2 hR, by
        rcases hxR with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩
    · obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.1 hxE
      exact mem_cover_iff.2 ⟨R, mem_squareMeshPieces.2 hR, by
        rwa [← edgeArc_segmentDrawing]⟩

/-- The two source families for the combined target overlay. -/
noncomputable def meshPieces (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : List Piece :=
  Q.pieces ++ squareMeshPieces delta fresh anchors

/-- The target skeleton overlaid with the anchored square mesh.  Old vertices and prescribed
mesh anchors are explicitly included in the cut list. -/
noncomputable def meshOverlay (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : Graph Plane Piece :=
  attachGraph (Q.meshPieces delta fresh anchors)
    (anchors ++ P.tgt.graph.vertexFinset.toList)

instance meshOverlay_finite (Q : TargetSegmentCover P) (delta : ℝ)
    (fresh anchors : List Plane) : (Q.meshOverlay delta fresh anchors).Finite :=
  attachGraph_finite _ _

/-- Every source segment of the combined overlay is nondegenerate. -/
theorem meshPieces_nondeg (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (delta : ℝ)
    (anchors : List Plane) :
    ∀ R ∈ Q.meshPieces delta fresh anchors, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · exact Q.nondeg R hR
  · exact meshGraph_edge_nondeg (two_le_meshCount delta) hfresh
      (mem_squareMeshPieces.1 hR)

/-- The combined overlay is a finite straight-line plane graph. -/
theorem meshOverlay_isDrawing (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    Graph.IsDrawing (Q.meshOverlay delta fresh anchors) segmentDrawing :=
  attachGraph_isDrawing (Q.meshPieces_nondeg hfresh delta anchors) _

/-- The combined overlay occupies exactly the current target skeleton together with the square
mesh. -/
theorem meshOverlay_pointSet (Q : TargetSegmentCover P)
    (delta : ℝ) (fresh anchors : List Plane) :
    Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing =
      P.tgt.skeletonSet ∪
        Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing := by
  rw [meshOverlay, attachGraph_pointSet, meshPieces, cover_append, Q.cover_eq,
    cover_squareMeshPieces]

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
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta anchors)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right anchors (by
      rw [Finset.mem_toList, mem_vertexFinset]
      exact hx)
  · rw [meshPieces, cover_append, Q.cover_eq]
    exact Or.inl (Graph.vertexSet_subset_pointSet hx)

/-- Every square-mesh vertex is an endpoint of a source piece for the combined overlay. -/
theorem squareMeshVertices_subset_meshOverlay (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    V(squareMesh delta fresh anchors) ⊆ V(Q.meshOverlay delta fresh anchors) := by
  intro x hx
  obtain ⟨R, hR, hxR⟩ := meshGraph_mem_vertexSet.1 hx
  change x ∈ V(overlayGraph (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.meshPieces_nondeg hfresh delta anchors)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right Q.pieces (mem_squareMeshPieces.2 hR)) x hxR
  · exact mem_cover_iff.2 ⟨R,
      List.mem_append_right Q.pieces (mem_squareMeshPieces.2 hR), by
        rcases hxR with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩

/-- Every edge of the combined overlay is a subsegment either of an old target segment or of a
square-mesh source segment. -/
theorem meshOverlay_edge_source (Q : TargetSegmentCover P)
    {delta : ℝ} {fresh anchors : List Plane} {R : Piece}
    (hR : R ∈ E(Q.meshOverlay delta fresh anchors)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      ∃ A ∈ meshSegments (meshCount delta) fresh, R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.meshPieces delta fresh anchors)
    (attachPoints (Q.meshPieces delta fresh anchors)
      (anchors ++ P.tgt.graph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hA
  · exact Or.inl ⟨A, hA, hsub⟩
  · obtain ⟨B, hB, hAB⟩ := meshGraph_edge_source (mem_squareMeshPieces.1 hA)
    exact Or.inr ⟨B, hB, hsub.trans hAB⟩

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
      (points := attachPoints (Q.meshPieces delta fresh anchors)
        (anchors ++ P.tgt.graph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_left _ hA) hzA
  have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- The combined overlay locally contains an edge subdivision of the old target drawing. -/
theorem target_isPlaneSubdivisionExtension (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    IsPlaneSubdivisionExtension P.tgt.graph P.tgt.drawing
      (Q.meshOverlay delta fresh anchors) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := P.tgt.isDrawing
  isDrawing := Q.meshOverlay_isDrawing hfresh delta anchors
  vertexSet_subset := Q.targetVertices_subset_meshOverlay hfresh delta anchors
  pointSet_subset := by
    change P.tgt.skeletonSet ⊆ _
    exact Q.targetSkeleton_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he R hR hmeet
    have heS : e ∈ E(P.str.skel) := by
      rwa [P.tgt.edgeSet_graph] at he
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet heS
    apply Q.meshOverlay_edge_subset hfresh delta anchors heS hR
    obtain ⟨z, hzR, hze, hznot⟩ := hmeet
    refine ⟨z, hzR, ?_, hznot⟩
    rw [P.tgt.cell_edge hab]
    refine ⟨hze, ?_⟩
    intro hzEnds
    rcases hzEnds with hza | hzb
    · apply hznot
      rw [hza]
      exact Q.targetVertices_subset_meshOverlay hfresh delta anchors (by
        rw [P.tgt.vertexSet_graph]
        exact ⟨a, hab.left_mem, rfl⟩)
    · apply hznot
      rw [hzb]
      exact Q.targetVertices_subset_meshOverlay hfresh delta anchors (by
        rw [P.tgt.vertexSet_graph]
        exact ⟨b, hab.right_mem, rfl⟩)

/-- The combined overlay also locally contains an edge subdivision of the anchored square
mesh.  Using the mesh's already-subdivided edges as source pieces makes the proof immediate. -/
theorem squareMesh_isPlaneSubdivisionExtension (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    IsPlaneSubdivisionExtension (squareMesh delta fresh anchors) segmentDrawing
      (Q.meshOverlay delta fresh anchors) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := squareMesh_isDrawing hfresh delta anchors
  isDrawing := Q.meshOverlay_isDrawing hfresh delta anchors
  vertexSet_subset := Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
  pointSet_subset := Q.squareMesh_subset_meshOverlay delta fresh anchors
  edge_subset := by
    intro e he R hR hmeet
    obtain ⟨z, hzR, hze, hznot⟩ := hmeet
    obtain ⟨R', hR', hzR', hR'e⟩ :=
      exists_overlayPiece_mem_subset
        (points := attachPoints (Q.meshPieces delta fresh anchors)
          (anchors ++ P.tgt.graph.vertexFinset.toList))
        (P₀ := e) (List.mem_append_right Q.pieces (mem_squareMeshPieces.2 he))
        (by rwa [edgeArc_segmentDrawing] at hze)
    have hzR'Arc : z ∈ edgeArc segmentDrawing R' := by
      rwa [edgeArc_segmentDrawing]
    have hRR' : R = R' :=
      (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
        hR hR' hznot hzR hzR'Arc
    rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
    exact hR'e

/-- The old-target trace inside the combined overlay remains 2-connected. -/
theorem targetTrace_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (delta : ℝ) (anchors : List Plane) :
    (Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
      P.tgt.skeletonSet).IsTwoConnected :=
  (Q.target_isPlaneSubdivisionExtension hfresh delta anchors).trace_isTwoConnected
    P.tgt_isWeaklyAdmissible.isTwoConnected

/-- Under the usual density hypotheses, the square-mesh trace inside the combined overlay
remains 2-connected. -/
theorem squareMeshTrace_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) :
    (Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
      (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)).IsTwoConnected :=
  (Q.squareMesh_isPlaneSubdivisionExtension hfresh delta anchors).trace_isTwoConnected
    (squareMesh_isTwoConnected hfresh hdense hdelta anchors)

/-- The combined target/mesh overlay is 2-connected.  The two subdivision traces are glued at
two distinct fresh boundary vertices, and together they contain every overlay vertex. -/
theorem meshOverlay_isTwoConnected (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) :
    (Q.meshOverlay delta fresh anchors).IsTwoConnected := by
  let T := Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
    P.tgt.skeletonSet
  let M := Graph.traceGraph (Q.meshOverlay delta fresh anchors) segmentDrawing
    (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing)
  have hT2 : T.IsTwoConnected := Q.targetTrace_isTwoConnected hfresh delta anchors
  have hM2 : M.IsTwoConnected :=
    Q.squareMeshTrace_isTwoConnected hfresh hdense hdelta anchors
  obtain ⟨z, hz, w, hw, hzw⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  have hzSquare : z ∈ V(squareMesh delta fresh anchors) :=
    end_mem_vertexSet_meshGraph (spokePiece_mem_meshSegments hz) (Or.inl rfl)
  have hwSquare : w ∈ V(squareMesh delta fresh anchors) :=
    end_mem_vertexSet_meshGraph (spokePiece_mem_meshSegments hw) (Or.inl rfl)
  have hzOverlay : z ∈ V(Q.meshOverlay delta fresh anchors) :=
    Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
      hzSquare
  have hwOverlay : w ∈ V(Q.meshOverlay delta fresh anchors) :=
    Q.squareMeshVertices_subset_meshOverlay hfresh delta anchors
      hwSquare
  have hzTarget : z ∈ P.tgt.skeletonSet := by
    apply P.tgt.outerSet_subset_skeletonSet
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hfresh z hz
  have hwTarget : w ∈ P.tgt.skeletonSet := by
    apply P.tgt.outerSet_subset_skeletonSet
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hfresh w hw
  have hzMesh : z ∈ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hzSquare
  have hwMesh : w ∈ Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hwSquare
  have hzT : z ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hzOverlay, hzTarget⟩
  have hwT : w ∈ V(T) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hwOverlay, hwTarget⟩
  have hzM : z ∈ V(M) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hzOverlay, hzMesh⟩
  have hwM : w ∈ V(M) := by
    rw [Graph.traceGraph_vertexSet]
    exact ⟨hwOverlay, hwMesh⟩
  have hcompat : T.Compatible M :=
    Graph.Compatible.of_le_le (Graph.traceGraph_le _) (Graph.traceGraph_le _)
  have hU2 : (T.union M).IsTwoConnected :=
    hT2.union hcompat hM2 hzw hzT hzM hwT hwM
  apply hU2.of_le_of_vertexSet_subset
    (Graph.union_le (Graph.traceGraph_le _) (Graph.traceGraph_le _))
  intro x hx
  rw [Graph.vertexSet_union]
  have hxPoint : x ∈ Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing :=
    Graph.vertexSet_subset_pointSet hx
  rw [Q.meshOverlay_pointSet] at hxPoint
  rcases hxPoint with hxTarget | hxMesh
  · exact Or.inl (by rw [Graph.traceGraph_vertexSet]; exact ⟨hx, hxTarget⟩)
  · exact Or.inr (by rw [Graph.traceGraph_vertexSet]; exact ⟨hx, hxMesh⟩)

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
      have hxMeshOuter :
          x ∈ ⋃ A ∈ outerEdges (meshCount delta) fresh anchors, A.seg := by
        rw [squareMesh_cover_outerEdges]
        exact hxOuter
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hxMeshOuter
      obtain ⟨R', hR', hxR', hR'A⟩ :=
        exists_overlayPiece_mem_subset
          (points := attachPoints (Q.meshPieces delta fresh anchors)
            (anchors ++ P.tgt.graph.vertexFinset.toList))
          (P₀ := A) (List.mem_append_right Q.pieces
            (mem_squareMeshPieces.2 hA.1)) hxA
      have hxR'Arc : x ∈ edgeArc segmentDrawing R' := by
        rwa [edgeArc_segmentDrawing]
      have hRR' : R = R' :=
        (Q.meshOverlay_isDrawing hfresh delta anchors).unique_edge_at
          hR hR' hx.2 hx.1 hxR'Arc
      apply houter
      rw [hRR', edgeArc_segmentDrawing]
      exact hR'A.trans hA.2

/-- If every connected piece of the old open skeleton meets the connected open part of the
mesh, their union is connected.  This is the set-theoretic core of the remaining quantitative
mesh-hitting argument. -/
theorem meshOverlay_isConnected_diff_of_hits (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh) (delta : ℝ) (anchors : List Plane)
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsConnected
      (Graph.pointSet (Q.meshOverlay delta fresh anchors) segmentDrawing \ modelCurve) := by
  let M := Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \ modelCurve
  have hM : IsConnected M := squareMesh_isConnected_diff hfresh delta anchors hz₀
  obtain ⟨r₀, hr₀⟩ := hM.nonempty
  have hunion : IsConnected ((P.tgt.skeletonSet \ modelCurve) ∪ M) := by
    refine ⟨⟨r₀, Or.inr hr₀⟩, isPreconnected_of_forall r₀ ?_⟩
    intro z hz
    rcases hz with hzOld | hzMesh
    · obtain ⟨A, hA, hAconn, hzA, w, hwA, hwM⟩ := hhit z hzOld
      refine ⟨A ∪ M, Set.union_subset (hA.trans subset_union_left) subset_union_right,
        Or.inr hr₀, Or.inl hzA, ?_⟩
      exact hAconn.union' ⟨w, hwA, hwM⟩ hM.isPreconnected
    · exact ⟨M, subset_union_right, hr₀, hzMesh, hM.isPreconnected⟩
  rw [Q.meshOverlay_pointSet]
  have heq :
      (P.tgt.skeletonSet ∪
          Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing) \ modelCurve =
        (P.tgt.skeletonSet \ modelCurve) ∪ M := by
    ext x
    constructor
    · rintro ⟨hxOld | hxMesh, hxOuter⟩
      · exact Or.inl ⟨hxOld, hxOuter⟩
      · exact Or.inr ⟨hxMesh, hxOuter⟩
    · rintro (⟨hxOld, hxOuter⟩ | ⟨hxMesh, hxOuter⟩)
      · exact ⟨Or.inl hxOld, hxOuter⟩
      · exact ⟨Or.inr hxMesh, hxOuter⟩
  rw [heq]
  exact hunion

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

/-- The mesh-hitting condition is enough to discharge the connectedness field of the target
extension.  Thus only 2-connectivity and the quantitative fact that the mesh meets every
connected piece of the old open skeleton remain. -/
theorem isSourceExtension_relabelledMeshOverlay_of_hits
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh)
    (delta : ℝ) (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (htwo : (Q.meshOverlay delta fresh anchors).IsTwoConnected)
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) :=
  Q.isSourceExtension_relabelledMeshOverlay hfresh delta anchors name hname htwo
    (Q.meshOverlay_isConnected_diff_of_hits hfresh hz₀ delta anchors hhit)

/-- With a dense fresh boundary list, 2-connectivity and the nonempty-fresh requirement are
automatic.  The mesh-hitting condition is then the only remaining assembly hypothesis. -/
theorem isSourceExtension_relabelledMeshOverlay_of_dense_hits
    (Q : TargetSegmentCover P)
    {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    {delta : ℝ} (hdense : FreshDense fresh delta) (hdelta : delta < 4)
    (anchors : List Plane) (name : Piece → γ)
    (hname : InjOn name E(Q.meshOverlay delta fresh anchors))
    (hhit : ∀ z ∈ P.tgt.skeletonSet \ modelCurve,
      ∃ A : Set Plane, A ⊆ P.tgt.skeletonSet \ modelCurve ∧
        IsPreconnected A ∧ z ∈ A ∧
          (A ∩ (Graph.pointSet (squareMesh delta fresh anchors) segmentDrawing \
            modelCurve)).Nonempty) :
    IsSourceExtension P.tgt modelCurve (Plane.closedSquare 0 1)
      ((Q.meshOverlay delta fresh anchors).relabelEdges name hname)
      ((Q.meshOverlay delta fresh anchors).relabelDrawing name segmentDrawing) := by
  obtain ⟨z, hz, -, -, -⟩ := exists_two_distinct_fresh_of_freshDense hdense hdelta
  exact Q.isSourceExtension_relabelledMeshOverlay_of_hits hfresh hz delta anchors name hname
    (Q.meshOverlay_isTwoConnected hfresh hdense hdelta anchors) hhit

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
