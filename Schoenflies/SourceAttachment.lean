/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SourceOverlay

/-!
# Auxiliary-crosscut source overlays

A local window can miss the current skeleton, so the raw source/grid overlay need not have the
two common vertices required for 2-connectivity.  The degenerate cases of
`prop:local-grid-attachment` add one polygonal crosscut of the containing face.  This module
builds the corresponding finite straight-line inner overlay while keeping the original wild
outer curve separate.

## Blueprint

* `Schoenflies.SourceNonboundarySegmentCover.crosscutOverlay` — the old compact nonboundary
  carrier, one auxiliary crosscut, and the local grid in a single exact segment overlay.
* `crosscutOverlay_pointSet` — its exact carrier.
* `crosscutOverlay_isDrawing`, `crosscutOverlay_pointSet_subset`, and
  `crosscutOverlay_edge_dichotomy` — the local plane and domain geometry needed by finite
  transfer.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}

namespace SourceNonboundarySegmentCover

variable (Q : SourceNonboundarySegmentCover P)

/-- The source pieces after adjoining one auxiliary crosscut and one local grid. -/
noncomputable def crosscutPieces (J : Piece) (p : Plane) (s epsilon : ℝ) : List Piece :=
  (Q.pieces ++ [J]) ++ localGridEdges p s (localGridCount s epsilon)

/-- The finite straight-line overlay of the old compact source core, an auxiliary crosscut,
and the local grid.  Old nonboundary vertices and prescribed points are retained. -/
noncomputable def crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : Graph Plane Piece :=
  attachGraph (Q.crosscutPieces J p s epsilon)
    (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)

instance crosscutOverlay_finite (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) : (Q.crosscutOverlay J p s epsilon extra).Finite :=
  attachGraph_finite _ _

/-- Every source piece in the crosscut overlay is nondegenerate. -/
theorem crosscutPieces_nondeg {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) :
    ∀ R ∈ Q.crosscutPieces J p s epsilon, R.Nondeg := by
  intro R hR
  rcases List.mem_append.1 hR with hR | hR
  · rcases List.mem_append.1 hR with hR | hR
    · exact Q.nondeg R hR
    · rw [List.mem_singleton] at hR
      subst R
      exact hJ
  · exact localGridEdges_nondeg hs (one_le_localGridCount s epsilon) R hR

/-- The auxiliary-crosscut overlay is a finite straight-line plane graph. -/
theorem crosscutOverlay_isDrawing {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    Graph.IsDrawing (Q.crosscutOverlay J p s epsilon extra) segmentDrawing :=
  attachGraph_isDrawing (Q.crosscutPieces_nondeg hs hJ) _

/-- The crosscut overlay occupies exactly the old compact source carrier, the auxiliary
segment, and the local grid. -/
theorem crosscutOverlay_pointSet (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing =
      (Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ∪ J.seg) ∪
        cover (localGridEdges p s (localGridCount s epsilon)) := by
  rw [crosscutOverlay, attachGraph_pointSet, crosscutPieces, cover_append,
    cover_append, Q.cover_eq]
  simp only [cover_cons, cover_nil, Set.union_empty]

/-- The old compact source core survives in the auxiliary-crosscut overlay. -/
theorem sourceCore_subset_crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    Graph.pointSet P.sourceNonboundaryGraph P.src.drawing ⊆
      Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing := by
  rw [Q.crosscutOverlay_pointSet]
  exact subset_union_left.trans subset_union_left

/-- The entire auxiliary segment survives in the overlay. -/
theorem crosscut_subset_crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    J.seg ⊆ Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing := by
  rw [Q.crosscutOverlay_pointSet]
  exact subset_union_right.trans subset_union_left

/-- The entire local grid survives in the auxiliary-crosscut overlay. -/
theorem localGrid_subset_crosscutOverlay (J : Piece) (p : Plane) (s epsilon : ℝ)
    (extra : List Plane) :
    cover (localGridEdges p s (localGridCount s epsilon)) ⊆
      Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing := by
  rw [Q.crosscutOverlay_pointSet]
  exact subset_union_right

/-- Every old compact-core vertex is retained by the auxiliary-crosscut overlay. -/
theorem sourceCoreVertices_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    V(P.sourceNonboundaryGraph) ⊆ V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · apply mem_attachPoints_of_mem
    exact List.mem_append_right extra (by
      rw [Finset.mem_toList, Graph.mem_vertexFinset]
      exact hx)
  · rw [crosscutPieces, cover_append, cover_append, Q.cover_eq]
    exact Or.inl (Or.inl (Graph.vertexSet_subset_pointSet hx))

/-- Both endpoints of the auxiliary crosscut are overlay vertices. -/
theorem crosscutEnds_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ({J.1, J.2} : Set Plane) ⊆ V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · exact attachPoints_endsAreCut _ _ J
      (List.mem_append_left _ (List.mem_append_right Q.pieces (List.mem_singleton_self J)))
      x hx
  · exact mem_cover_iff.2 ⟨J,
      List.mem_append_left _ (List.mem_append_right Q.pieces (List.mem_singleton_self J)), by
        rcases hx with rfl | rfl
        · exact left_mem_segment ℝ _ _
        · exact right_mem_segment ℝ _ _⟩

/-- Every raw local-grid vertex is retained by the auxiliary-crosscut overlay. -/
theorem localGridVertices_subset_crosscutOverlay {J : Piece} {p : Plane}
    {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    V(localGrid p s (localGridCount s epsilon)) ⊆
      V(Q.crosscutOverlay J p s epsilon extra) := by
  intro x hx
  rw [localGrid_eq, pieceListGraph_vertexSet] at hx
  simp only [endSet, Set.mem_setOf_eq] at hx
  obtain ⟨R, hR, hxR⟩ := hx
  change x ∈ V(overlayGraph (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)))
  apply overlayGraph_mem_vertexSet_of_mem_cover (Q.crosscutPieces_nondeg hs hJ)
  · exact attachPoints_endsAreCut _ _ R
      (List.mem_append_right (Q.pieces ++ [J]) hR) x hxR
  · exact mem_cover_iff.2 ⟨R, List.mem_append_right (Q.pieces ++ [J]) hR, by
      rcases hxR with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _⟩

/-- Every overlay edge is cut from the old compact cover, the auxiliary crosscut, or the local
grid. -/
theorem crosscutOverlay_edge_source {J : Piece} {p : Plane} {s epsilon : ℝ}
    {extra : List Plane} {R : Piece} (hR : R ∈ E(Q.crosscutOverlay J p s epsilon extra)) :
    (∃ A ∈ Q.pieces, R.seg ⊆ A.seg) ∨
      R.seg ⊆ J.seg ∨
        ∃ A ∈ localGridEdges p s (localGridCount s epsilon), R.seg ⊆ A.seg := by
  change R ∈ overlayPieces (Q.crosscutPieces J p s epsilon)
    (attachPoints (Q.crosscutPieces J p s epsilon)
      (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList)) at hR
  obtain ⟨R₀, hR₀, rfl⟩ := mem_overlayPieces.1 hR
  obtain ⟨A, hA, hsub, -⟩ := subdivide_subset _ _ R₀ hR₀
  rw [orientPiece_seg]
  rcases List.mem_append.1 hA with hA | hGrid
  · rcases List.mem_append.1 hA with hOld | hCrosscut
    · exact Or.inl ⟨A, hOld, hsub⟩
    · rw [List.mem_singleton] at hCrosscut
      exact Or.inr (Or.inl (hCrosscut ▸ hsub))
  · exact Or.inr (Or.inr ⟨A, hGrid, hsub⟩)

/-- If both the crosscut and the window lie in the open source domain, the entire auxiliary
overlay lies in the closed source domain. -/
theorem crosscutOverlay_pointSet_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJopen : J.seg ⊆ srcDom \ srcOuter)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    Graph.pointSet (Q.crosscutOverlay J p s epsilon extra) segmentDrawing ⊆ srcDom := by
  rw [Q.crosscutOverlay_pointSet]
  apply Set.union_subset
  · apply Set.union_subset
    · exact (Graph.pointSet_mono P.sourceNonboundaryGraph_le).trans
        P.src_isWeaklyAdmissible.skeletonSet_subset
    · exact hJopen.trans sdiff_subset
  · exact (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)).trans (hwindow.trans sdiff_subset)

/-- Every auxiliary-overlay edge is polygonal and has all nonvertex points in the open source
domain. -/
theorem crosscutOverlay_edge_dichotomy {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (hJopen : J.seg ⊆ srcDom \ srcOuter)
    (hwindow : Plane.closedSquare p s ⊆ srcDom \ srcOuter) (extra : List Plane) :
    ∀ {R : Piece}, R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      IsPolygonal (_root_.Graph.edgeArc segmentDrawing R) ∧
        _root_.Graph.edgeArc segmentDrawing R \ V(Q.crosscutOverlay J p s epsilon extra) ⊆
          srcDom \ srcOuter := by
  intro R hR
  refine ⟨by rw [edgeArc_segmentDrawing]; exact isPolygonal_segment _ _, ?_⟩
  intro x hx
  have hxSeg : x ∈ R.seg := by
    rw [← edgeArc_segmentDrawing]
    exact hx.1
  rcases Q.crosscutOverlay_edge_source hR with hOld | hCrosscut | hGrid
  · obtain ⟨A, hA, hRA⟩ := hOld
    obtain ⟨e, he, heNotOuter, hAe⟩ := Q.source A hA
    obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
    have hxe : x ∈ _root_.Graph.edgeArc P.src.drawing e := hAe (hRA hxSeg)
    have hxCell : x ∈ P.src.cell e := by
      rw [P.src.cell_edge hab]
      refine ⟨hxe, ?_⟩
      intro hxEnds
      have habSrc := hab.map P.src.pos
      rcases hxEnds with hxa | hxb
      · apply hx.2
        rw [hxa]
        apply Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_left⟩
      · apply hx.2
        rw [hxb]
        apply Q.sourceCoreVertices_subset_crosscutOverlay hs hJ extra
        exact ⟨e, by rwa [P.src.edgeSet_graph], heNotOuter, habSrc.inc_right⟩
    exact P.src_isWeaklyAdmissible.cell_subset he heNotOuter hxCell
  · exact hJopen (hCrosscut hxSeg)
  · obtain ⟨A, hA, hRA⟩ := hGrid
    exact hwindow (cover_localGridEdges_subset_closedSquare hs
      (one_le_localGridCount s epsilon)
      (mem_cover_iff.2 ⟨A, hA, hRA hxSeg⟩))

/-- Away from overlay vertices, an auxiliary-overlay edge meeting an old open nonboundary edge
is one of that edge's subdivision pieces. -/
theorem crosscutOverlay_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {e : γ}, e ∈ E(P.str.skel) → e ∉ E(P.str.outerGraph) → ∀ {R : Piece},
      R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (P.src.cell e \ V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc P.src.drawing e := by
  intro e he heOuter R hR hmeet
  obtain ⟨z, hzR, hzCell, hznotOverlay⟩ := hmeet
  obtain ⟨a, b, hab⟩ := P.str.skel.exists_isLink_of_mem_edgeSet he
  have hzOldArc : z ∈ _root_.Graph.edgeArc P.src.drawing e := by
    rw [P.src.cell_edge hab] at hzCell
    exact hzCell.1
  have hzCore : z ∈ Graph.pointSet P.sourceNonboundaryGraph P.src.drawing :=
    Graph.edgeArc_subset_pointSet
      (sourceNonboundaryGraph_edge_mem (P := P) he heOuter) hzOldArc
  have hzCover : z ∈ cover Q.pieces := by rwa [Q.cover_eq]
  obtain ⟨A, hA, hzA⟩ := ClosedPolygon.exists_of_mem_cover hzCover
  obtain ⟨g, hg, -, hAg⟩ := Q.source A hA
  have hzg : z ∈ _root_.Graph.edgeArc P.src.drawing g := hAg hzA
  have hznotOldVertex : z ∉ V(P.src.graph) := by
    intro hzV
    rcases P.src.isDrawing.vertex_mem_edgeArc (hab.map P.src.pos) hzV hzOldArc with
      hza | hzb
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hza])
    · rw [P.src.cell_edge hab] at hzCell
      exact hzCell.2 (by simp [hzb])
  have heg : e = g := P.src.isDrawing.unique_edge_at
    (by change e ∈ E(P.str.skel); exact he)
    (by change g ∈ E(P.str.skel); exact hg)
    hznotOldVertex hzOldArc hzg
  have hAold : A.seg ⊆ _root_.Graph.edgeArc P.src.drawing e := by rwa [heg]
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A)
      (List.mem_append_left _ (List.mem_append_left [J] hA)) hzA
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing]
  exact hR'A.trans hAold

/-- Away from overlay vertices, an auxiliary-overlay edge meeting a raw local-grid edge is one
of that edge's subdivision pieces. -/
theorem crosscutOverlay_grid_edge_subset {J : Piece} {p : Plane} {s epsilon : ℝ}
    (hs : 0 < s) (hJ : J.Nondeg) (extra : List Plane) :
    ∀ {A : Piece}, A ∈ E(localGrid p s (localGridCount s epsilon)) → ∀ {R : Piece},
      R ∈ E(Q.crosscutOverlay J p s epsilon extra) →
      (_root_.Graph.edgeArc segmentDrawing R ∩
        (_root_.Graph.edgeArc segmentDrawing A \
          V(Q.crosscutOverlay J p s epsilon extra))).Nonempty →
      _root_.Graph.edgeArc segmentDrawing R ⊆
        _root_.Graph.edgeArc segmentDrawing A := by
  intro A hA R hR hmeet
  have hAList : A ∈ localGridEdges p s (localGridCount s epsilon) := by
    simpa only [localGrid_eq, pieceListGraph_mem_edgeSet] using hA
  obtain ⟨z, hzR, hzA, hznotOverlay⟩ := hmeet
  obtain ⟨R', hR', hzR', hR'A⟩ :=
    exists_overlayPiece_mem_subset
      (points := attachPoints (Q.crosscutPieces J p s epsilon)
        (extra ++ P.sourceNonboundaryGraph.vertexFinset.toList))
      (P₀ := A) (List.mem_append_right (Q.pieces ++ [J]) hAList)
      (by rwa [edgeArc_segmentDrawing] at hzA)
  have hzR'Arc : z ∈ _root_.Graph.edgeArc segmentDrawing R' := by
    rwa [edgeArc_segmentDrawing]
  have hRR' : R = R' :=
    (Q.crosscutOverlay_isDrawing hs hJ extra).unique_edge_at
      hR hR' hznotOverlay hzR hzR'Arc
  rw [hRR', edgeArc_segmentDrawing, edgeArc_segmentDrawing]
  exact hR'A

/-- The auxiliary straight-line overlay contains a plane subdivision of the raw local grid. -/
theorem crosscutOverlay_localGrid_isPlaneSubdivisionExtension
    {J : Piece} {p : Plane} {s epsilon : ℝ} (hs : 0 < s) (hJ : J.Nondeg)
    (extra : List Plane) :
    IsPlaneSubdivisionExtension
      (localGrid p s (localGridCount s epsilon)) segmentDrawing
      (Q.crosscutOverlay J p s epsilon extra) segmentDrawing where
  finite := inferInstance
  oldIsDrawing := localGrid_isDrawing hs (one_le_localGridCount s epsilon)
  isDrawing := Q.crosscutOverlay_isDrawing hs hJ extra
  vertexSet_subset := Q.localGridVertices_subset_crosscutOverlay hs hJ extra
  pointSet_subset := by
    rw [localGrid_eq, pieceListGraph_pointSet]
    exact Q.localGrid_subset_crosscutOverlay J p s epsilon extra
  edge_subset := by
    intro A hA R hR hmeet
    exact Q.crosscutOverlay_grid_edge_subset hs hJ extra hA hR hmeet

end SourceNonboundarySegmentCover

end Schoenflies
