/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshTransfer
import Schoenflies.SquareMeshClosed
import Schoenflies.SimpleArc
import Schoenflies.GridComponents

/-!
# The mesh overlay: `Schoenflies.HasMeshOverlays`, reduced to 2-connectivity

`Schoenflies.HasMeshOverlays` (`Schoenflies/MeshTransfer.lean`) is the one remaining named
hypothesis of the direction-(b) chooser: at every admissible stage `P` and mesh size `ε`, every
fresh list on `S` avoiding the drawn 0-cells extends to a
`Schoenflies.MeshOverlayExtension P ε fresh Piece`. This module builds the extension.

## The construction

The overlay is `Schoenflies.overlayGraph` (Lemma 3.7) run on one list of segments:

* the anchored square mesh `Schoenflies.meshSegments (meshCount ε) fresh` — the rings and the
  spokes;
* the old polygonal target skeleton, one straight piece at a time: each old 1-cell's arc is
  polygonal (`GeneratedPair.tgt_isPolygonal`), so it is `poly vs` for some vertex chain, and
  `Schoenflies.segsOf` cuts the chain into nondegenerate segments (`skelPieces`);
* a list of **joining arcs** (`joins`), polygonal chains inside the open square that connect
  every component of the old nonboundary skeleton to the mesh. They are not optional: the
  docstring of `MeshOverlayExtension.isConnected` records the counterexample where
  mesh ∪ skeleton alone has disconnected `|H| ∖ S`.

The cut points are the ones `Schoenflies.exists_cut_points` supplies for the combined list,
*plus* the drawn 0-cells of the stage, which is what makes every old vertex a vertex of the
overlay (the same device as the anchors of `Schoenflies.squareMesh`).

The joining arcs are quantified, not chosen: `JoinsFor P ε joins` records exactly what every
clause of the extension needs of them (nondegenerate, drawn in the open square, and connecting
the nonboundary skeleton to the mesh base point), `Schoenflies.exists_joinsFor` produces such a
list from `Schoenflies.exists_reps_cover_diff` and `Schoenflies.exists_poly_of_isPreconnected`,
and the 2-connectivity hypothesis below quantifies existentially over the list so that its
discharger may pick a better-behaved one.

## What is proved, and what is not

Every field of `Schoenflies.MeshOverlayExtension` is proved for
`Schoenflies.meshOverlayGraph P ε fresh joins` **except 2-connectivity**, which remains as the
named hypothesis `Schoenflies.HasMeshOverlayCores`:

* its route is the blueprint's: the overlay restricted to the old-skeleton pieces is a
  subdivision of `Γ'` (2-connected by admissibility, `Graph.IsSubdivisionOf.isTwoConnected`),
  the overlay restricted to the mesh pieces is a subdivision of
  `Schoenflies.squareMesh` (2-connected by `Schoenflies.squareMesh_isTwoConnected`), the two
  share at least two vertices on `S` (`Graph.IsTwoConnected.union`), and each joining arc goes
  in as an ear (`Graph.IsTwoConnected.ear`);
* the existential over `joins` is what makes the hypothesis honest: for the *specific* joining
  chains `Classical.choice` would extract from `Schoenflies.exists_joinsFor`, a chain that
  doubles back on itself would subdivide to a pendant edge and 2-connectivity would be false.
  The discharger chooses the chains, and `Schoenflies.exists_joinsFor` shows the choice is
  never vacuous.

`Schoenflies.hasMeshOverlays_of` composes the reduction:
`HasMeshOverlayCores S₀ C → HasMeshOverlays S₀ C`.

## Blueprint

* `skelChain`, `skelPieces`, `skelNbPieces` — the polygonal target skeleton as a segment list.
* `meshBase`, `JoinsFor`, `exists_joinsFor` — the joining arcs of `lem:polygonal-overlay` as
  the blueprint's *"join each component to the mesh"*, aimed at the representatives of
  `Schoenflies.exists_reps_cover_diff`.
* `meshOverlayPieces`, `meshOverlayPoints`, `meshOverlayGraph` — the overlay of
  `lem:polygonal-overlay` applied to mesh, skeleton and joining arcs.
* `meshOverlayGraph_isDrawing` … `meshOverlayGraph_unique_edge` — the clauses of
  `Schoenflies.MeshOverlayExtension`, one theorem each.
* `HasMeshOverlayCores` — **the remaining named hypothesis**: 2-connectivity of the overlay,
  with the joining arcs at the discharger's choice.
* `meshOverlayExtension_of_joins`, `hasMeshOverlays_of` — the assembly and the reduction.
-/

open Metric Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {u w : α}

/-- In a connected graph with a second vertex, every vertex has an incident edge. The walk to
the second vertex cannot be empty, and its first step is the edge. (General-purpose; a
candidate for hoisting into `Schoenflies/Graph/Walk.lean`.) -/
theorem Connected.exists_isLink_left (h : G.Connected) (hu : u ∈ V(G)) (hw : w ∈ V(G))
    (hne : u ≠ w) : ∃ e x, G.IsLink e u x := by
  obtain ⟨W, hW⟩ := h.reaches hu hw
  cases hW with
  | nil hx => exact absurd rfl hne
  | cons hl hW' => exact ⟨_, _, hl⟩

end Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-! ### The old skeleton as a list of straight pieces

Each 1-cell's drawn arc is polygonal, so it is the carrier of a vertex chain; `segsOf` cuts
the chain into nondegenerate segments. The chain is extracted by choice once per edge, behind
a `dite` so that the definition carries no hypothesis. -/

open scoped Classical in
/-- A vertex chain carrying the drawn arc of the 1-cell `e` of the stage's target skeleton —
any chain, extracted from `GeneratedPair.tgt_isPolygonal` by choice. -/
noncomputable def skelChain (P : StagePair S₀ C) (e : γ) : List Plane :=
  if h : IsPolygonal (Graph.edgeArc P.tgt.drawing e) then h.choose else []

theorem poly_skelChain (P : StagePair S₀ C) {e : γ} (he : e ∈ E(P.str.skel)) :
    poly (skelChain P e) = Graph.edgeArc P.tgt.drawing e := by
  rw [skelChain, dif_pos (P.tgt_isPolygonal he)]
  exact (P.tgt_isPolygonal he).choose_spec.symm

/-- A drawn 1-cell contains two distinct points: the two ends of its parametrization. -/
theorem edgeArc_two_points (P : StagePair S₀ C) {e : γ} (he : e ∈ E(P.str.skel)) :
    ∃ x ∈ Graph.edgeArc P.tgt.drawing e, ∃ y ∈ Graph.edgeArc P.tgt.drawing e, x ≠ y := by
  have he' : e ∈ E(P.str.skel.map P.tgt.pos) := by rwa [edgeSet_map]
  obtain ⟨-, hinj, -⟩ := P.tgt.isDrawing.edge_param he'
  exact ⟨P.tgt.drawing e 0, ⟨0, zero_mem_I, rfl⟩, P.tgt.drawing e 1, ⟨1, one_mem_I, rfl⟩,
    fun h => zero_ne_one (hinj zero_mem_I one_mem_I h)⟩

/-- The pieces of the chain occupy exactly the drawn 1-cell. -/
theorem cover_skelSegs (P : StagePair S₀ C) {e : γ} (he : e ∈ E(P.str.skel)) :
    cover (segsOf (skelChain P e)) = Graph.edgeArc P.tgt.drawing e := by
  obtain ⟨x, hx, y, hy, hxy⟩ := edgeArc_two_points P he
  rw [← poly_skelChain P he] at hx hy ⊢
  exact cover_segsOf_eq hx hy hxy

/-- The 1-cells of the stage, as a list. -/
noncomputable def skelEdges (P : StagePair S₀ C) : List γ :=
  P.str.finite_edgeSet.toFinset.toList

theorem mem_skelEdges {P : StagePair S₀ C} {e : γ} :
    e ∈ skelEdges P ↔ e ∈ E(P.str.skel) := by
  rw [skelEdges, Finset.mem_toList, Set.Finite.mem_toFinset]

/-- **The old skeleton as a segment list**: the chains of all 1-cells, concatenated. -/
noncomputable def skelPieces (P : StagePair S₀ C) : List Piece :=
  (skelEdges P).flatMap fun e => segsOf (skelChain P e)

theorem mem_skelPieces {P : StagePair S₀ C} {Q : Piece} :
    Q ∈ skelPieces P ↔ ∃ e ∈ E(P.str.skel), Q ∈ segsOf (skelChain P e) := by
  simp only [skelPieces, List.mem_flatMap, mem_skelEdges]

theorem skelPieces_nondeg (P : StagePair S₀ C) : ∀ Q ∈ skelPieces P, Q.Nondeg := by
  intro Q hQ
  obtain ⟨e, -, hQe⟩ := mem_skelPieces.1 hQ
  exact segsOf_nondeg _ Q hQe

/-- A piece of the chain of `e` runs inside the drawn 1-cell of `e`. -/
theorem seg_subset_edgeArc (P : StagePair S₀ C) {e : γ} (he : e ∈ E(P.str.skel)) {Q : Piece}
    (hQ : Q ∈ segsOf (skelChain P e)) : Q.seg ⊆ Graph.edgeArc P.tgt.drawing e := by
  rw [← cover_skelSegs P he]
  exact fun x hx => mem_cover_iff.2 ⟨Q, hQ, hx⟩

theorem cover_skelPieces (P : StagePair S₀ C) :
    cover (skelPieces P) = ⋃ e ∈ E(P.str.skel), Graph.edgeArc P.tgt.drawing e := by
  rw [skelPieces, cover_flatMap']
  ext x
  simp only [mem_iUnion, exists_prop, mem_skelEdges]
  constructor
  · rintro ⟨e, he, hx⟩
    exact ⟨e, he, (cover_skelSegs P he) ▸ hx⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨e, he, (cover_skelSegs P he).symm ▸ hx⟩

open scoped Classical in
/-- The nonboundary 1-cells of the stage: the 1-cells off the outer cycle. -/
noncomputable def skelNbEdges (P : StagePair S₀ C) : List γ :=
  (skelEdges P).filter fun e => decide (e ∉ E(P.str.outerGraph))

theorem mem_skelNbEdges {P : StagePair S₀ C} {e : γ} :
    e ∈ skelNbEdges P ↔ e ∈ E(P.str.skel) ∧ e ∉ E(P.str.outerGraph) := by
  classical
  simp only [skelNbEdges, List.mem_filter, mem_skelEdges, decide_eq_true_eq]

/-- The pieces of the nonboundary 1-cells. These are the pieces the joining arcs have to
reach, and the only skeleton pieces that survive removing `S`. -/
noncomputable def skelNbPieces (P : StagePair S₀ C) : List Piece :=
  (skelNbEdges P).flatMap fun e => segsOf (skelChain P e)

theorem mem_skelNbPieces {P : StagePair S₀ C} {Q : Piece} :
    Q ∈ skelNbPieces P ↔
      ∃ e, (e ∈ E(P.str.skel) ∧ e ∉ E(P.str.outerGraph)) ∧ Q ∈ segsOf (skelChain P e) := by
  simp only [skelNbPieces, List.mem_flatMap, mem_skelNbEdges]

theorem skelNbPieces_subset (P : StagePair S₀ C) : skelNbPieces P ⊆ skelPieces P := by
  intro Q hQ
  obtain ⟨e, ⟨he, -⟩, hQe⟩ := mem_skelNbPieces.1 hQ
  exact mem_skelPieces.2 ⟨e, he, hQe⟩

/-! ### The base point and the joining arcs

`meshBase ε` is a point of the innermost ring, off `S` — the point every joining arc runs to.
`JoinsFor` records exactly what the extension's clauses need of the joining arcs; nothing else
about them is ever used, which is what lets the 2-connectivity hypothesis quantify over
them. -/

/-- The base point on the innermost ring of the mesh of size `ε`. -/
noncomputable def meshBase (ε : ℝ) : Plane := Plane.mk ((meshCount ε : ℝ))⁻¹ 0

theorem supNorm_meshBase (ε : ℝ) : Plane.supNorm (meshBase ε) = ((meshCount ε : ℝ))⁻¹ := by
  have h0 : (0 : ℝ) ≤ ((meshCount ε : ℝ))⁻¹ := (inv_cast_pos (two_le_meshCount ε)).le
  have h1 : (meshBase ε) 0 = ((meshCount ε : ℝ))⁻¹ := Plane.mk_zero _ _
  have h2 : (meshBase ε) 1 = 0 := Plane.mk_one _ _
  rw [Plane.supNorm, h1, h2, abs_of_nonneg h0, abs_zero]
  exact max_eq_left h0

theorem meshBase_mem_ringSet (ε : ℝ) : meshBase ε ∈ ringSet ((meshCount ε : ℝ))⁻¹ :=
  supNorm_meshBase ε

theorem meshBase_notMem_modelCurve (ε : ℝ) : meshBase ε ∉ modelCurve := by
  intro h
  have h1 : Plane.supNorm (meshBase ε) = 1 := h
  rw [supNorm_meshBase] at h1
  exact absurd h1 (ne_of_lt (inv_cast_lt_one (two_le_meshCount ε)))

theorem meshBase_mem_openSquare (ε : ℝ) : meshBase ε ∈ Plane.openSquare 0 1 :=
  mem_openSquare_zero_one.2
    (supNorm_meshBase ε ▸ inv_cast_lt_one (two_le_meshCount ε))

/-- The base point lies on the mesh. -/
theorem meshBase_mem_cover_meshSegments (ε : ℝ) (fresh : List Plane) :
    meshBase ε ∈ cover (meshSegments (meshCount ε) fresh) :=
  ringSet_subset_cover (two_le_meshCount ε) (inv_mem_meshRadii (two_le_meshCount ε))
    (meshBase_mem_ringSet ε)

/-- **What the extension needs of the joining arcs.** Nondegenerate segments drawn in the open
square — off `S` outright — that connect every point of the nonboundary skeleton and of the
arcs themselves to the mesh base point. The connecting set is allowed to use the arcs, the
nonboundary skeleton and the base point, all off `S`. -/
structure JoinsFor (P : StagePair S₀ C) (ε : ℝ) (joins : List Piece) : Prop where
  /-- Every joining piece is nondegenerate. -/
  nondeg : ∀ Q ∈ joins, Q.Nondeg
  /-- The joining arcs are drawn in the open square. -/
  subset : cover joins ⊆ Plane.openSquare 0 1
  /-- Every point of the nonboundary skeleton or of a joining arc, off `S`, is connected to
  the mesh base point inside the union of the two with the base point, off `S`. -/
  connects : ∀ x ∈ (cover (skelNbPieces P) ∪ cover joins) \ modelCurve,
    ∃ A : Set Plane,
      A ⊆ (cover (skelNbPieces P) ∪ cover joins ∪ {meshBase ε}) \ modelCurve ∧
      IsPreconnected A ∧ x ∈ A ∧ meshBase ε ∈ A

/-! ### The overlay -/

/-- **The segment list of the overlay**: mesh, old skeleton, joining arcs. -/
noncomputable def meshOverlayPieces (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) : List Piece :=
  meshSegments (meshCount ε) fresh ++ (skelPieces P ++ joins)

/-- **The cut points of the overlay**: the drawn 0-cells of the stage, plus the cut points
`Schoenflies.exists_cut_points` supplies for the combined segment list. -/
noncomputable def meshOverlayPoints (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) : List Plane :=
  (P.str.finite_vertexSet.toFinset.toList.map P.tgt.pos)
    ++ (exists_cut_points (meshOverlayPieces P ε fresh joins)).choose

/-- **The overlay graph**: `lem:polygonal-overlay` run on mesh, skeleton and joining arcs at
once, with the drawn 0-cells as prescribed vertices. -/
noncomputable def meshOverlayGraph (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) : Graph Plane Piece :=
  overlayGraph (meshOverlayPieces P ε fresh joins) (meshOverlayPoints P ε fresh joins)

variable {P : StagePair S₀ C} {ε : ℝ} {fresh : List Plane} {joins : List Piece}

theorem meshOverlayPieces_nondeg (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hj : ∀ Q ∈ joins, Q.Nondeg) :
    ∀ Q ∈ meshOverlayPieces P ε fresh joins, Q.Nondeg := by
  intro Q hQ
  rcases List.mem_append.1 hQ with h | h
  · exact meshSegments_nondeg (two_le_meshCount ε) hfresh Q h
  · rcases List.mem_append.1 h with h' | h'
    · exact skelPieces_nondeg P Q h'
    · exact hj Q h'

theorem meshOverlayPoints_endsAreCut (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) :
    EndsAreCut (meshOverlayPieces P ε fresh joins) (meshOverlayPoints P ε fresh joins) :=
  (exists_cut_points (meshOverlayPieces P ε fresh joins)).choose_spec.1.mono
    (List.subset_append_right _ _)

theorem meshOverlayPoints_meetsAreCut (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) :
    MeetsAreCut (meshOverlayPieces P ε fresh joins) (meshOverlayPoints P ε fresh joins) :=
  (exists_cut_points (meshOverlayPieces P ε fresh joins)).choose_spec.2.mono
    (List.subset_append_right _ _)

/-- Every drawn 0-cell of the stage is a prescribed cut point. -/
theorem pos_mem_meshOverlayPoints {v : γ} (hv : v ∈ V(P.str.skel)) :
    P.tgt.pos v ∈ meshOverlayPoints P ε fresh joins :=
  List.mem_append_left _ (List.mem_map.2 ⟨v,
    (Finset.mem_toList).2 (P.str.finite_vertexSet.mem_toFinset.2 hv), rfl⟩)

instance meshOverlayGraph_finite (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) : Graph.Finite (meshOverlayGraph P ε fresh joins) :=
  overlayGraph_finite _ _

/-- **The overlay is a plane graph.** -/
theorem meshOverlayGraph_isDrawing (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hj : ∀ Q ∈ joins, Q.Nondeg) :
    Graph.IsDrawing (meshOverlayGraph P ε fresh joins) segmentDrawing :=
  overlayGraph_isDrawing _ _ (meshOverlayPieces_nondeg hfresh hj)
    (meshOverlayPoints_endsAreCut P ε fresh joins)
    (meshOverlayPoints_meetsAreCut P ε fresh joins)

/-- What the overlay occupies: mesh, skeleton, joining arcs. -/
theorem meshOverlayGraph_pointSet (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) :
    Graph.pointSet (meshOverlayGraph P ε fresh joins) segmentDrawing
      = cover (meshOverlayPieces P ε fresh joins) :=
  overlayGraph_pointSet _ _

theorem cover_meshOverlayPieces (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) :
    cover (meshOverlayPieces P ε fresh joins)
      = cover (meshSegments (meshCount ε) fresh) ∪ (cover (skelPieces P) ∪ cover joins) := by
  rw [meshOverlayPieces, cover_append, cover_append]

/-- The mesh is part of the overlay. -/
theorem mesh_cover_subset (P : StagePair S₀ C) (ε : ℝ) (fresh : List Plane)
    (joins : List Piece) :
    cover (meshSegments (meshCount ε) fresh)
      ⊆ Graph.pointSet (meshOverlayGraph P ε fresh joins) segmentDrawing := by
  rw [meshOverlayGraph_pointSet, cover_meshOverlayPieces]
  exact subset_union_left

/-- An edge of the overlay is a subsegment of a listed segment, with matching interior. -/
theorem meshOverlayGraph_edge_source {Q : Piece} (hQ : Q ∈ E(meshOverlayGraph P ε fresh joins)) :
    ∃ R ∈ meshOverlayPieces P ε fresh joins, Q.seg ⊆ R.seg ∧ Q.interior ⊆ R.interior := by
  obtain ⟨Q', hQ', rfl⟩ := mem_overlayPieces.1 hQ
  obtain ⟨R, hR, hsub, hsub'⟩ := subdivide_subset _ _ Q' hQ'
  exact ⟨R, hR, by rwa [orientPiece_seg], by rwa [orientPiece_interior]⟩

theorem meshOverlayGraph_edge_nondeg (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hj : ∀ Q ∈ joins, Q.Nondeg) {Q : Piece}
    (hQ : Q ∈ E(meshOverlayGraph P ε fresh joins)) : Q.Nondeg :=
  overlayPieces_nondeg _ (meshOverlayPieces_nondeg hfresh hj) Q hQ

/-- **A cut point lying on a listed segment is a vertex of the overlay** — the general form of
`Schoenflies.anchor_mem_vertexSet`, for an arbitrary overlay. (General-purpose; a candidate
for hoisting into `Schoenflies/OverlayGraph.lean`.) -/
theorem overlay_mem_vertexSet_of_cut {pieces : List Piece} {points : List Plane} {p : Plane}
    (hp : p ∈ points) {R : Piece} (hR : R ∈ pieces) (hmem : p ∈ R.seg) :
    p ∈ V(overlayGraph pieces points) := by
  obtain ⟨Q, hQ, -, hend⟩ := subdivide_end_of_mem points pieces p hp R hR hmem
  exact ⟨orientPiece Q, mem_overlayPieces.2 ⟨Q, hQ, rfl⟩, (orientPiece_ends Q p).2 hend⟩

/-- A fresh point is a vertex of the overlay: it is an end of its own spoke, hence a cut
point, and it lies on the spoke. -/
theorem fresh_mem_vertexSet_meshOverlayGraph {z : Plane} (hz : z ∈ fresh) :
    z ∈ V(meshOverlayGraph P ε fresh joins) := by
  have hspoke : spokePiece (meshCount ε) z ∈ meshOverlayPieces P ε fresh joins :=
    List.mem_append_left _ (spokePiece_mem_meshSegments hz)
  exact overlay_mem_vertexSet_of_cut
    (meshOverlayPoints_endsAreCut P ε fresh joins _ hspoke z (Or.inl rfl))
    hspoke (left_mem_segment ℝ _ _)

/-! ### The containment clauses

Every drawn 0-cell is a vertex, the old skeleton is part of the overlay, and the overlay stays
in the closed square. The 0-cell clause rests on the stage's 2-connectivity: a 0-cell of a
connected graph with a second vertex is an end of some 1-cell, hence lies on a drawn arc,
hence — being a prescribed cut point — is an end of an overlay piece. -/

/-- The drawn skeleton of the stage. -/
theorem arc_subset_skeletonSet (P : StagePair S₀ C) {e : γ} (he : e ∈ E(P.str.skel)) :
    Graph.edgeArc P.tgt.drawing e ⊆ P.tgt.skeletonSet :=
  Graph.edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph])

/-- Every drawn 0-cell of an admissible stage lies on the drawn arc of one of its 1-cells. -/
theorem pos_mem_edgeArc_of_vertex (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    {v : γ} (hv : v ∈ V(P.str.skel)) :
    ∃ e ∈ E(P.str.skel), P.tgt.pos v ∈ Graph.edgeArc P.tgt.drawing e := by
  have hposv : P.tgt.pos v ∈ V(P.tgt.graph) := by
    rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩
  -- 2-connectivity supplies a second vertex, connectivity a first step towards it
  obtain ⟨a, ha, b, hb, -, -, hab, -, -⟩ := htgt.isTwoConnected.hasThreeVertices
  have hw : ∃ w ∈ V(P.tgt.graph), w ≠ P.tgt.pos v := by
    by_cases h : a = P.tgt.pos v
    · exact ⟨b, hb, fun hbv => hab (h.trans hbv.symm)⟩
    · exact ⟨a, ha, h⟩
  obtain ⟨w, hwV, hwne⟩ := hw
  obtain ⟨e, x, hl⟩ :=
    htgt.isTwoConnected.connected.exists_isLink_left hposv hwV (Ne.symm hwne)
  have he : e ∈ E(P.str.skel) := by
    have := hl.edge_mem
    rwa [Realization.edgeSet_graph] at this
  -- the ends of the parametrization are the ends of the edge, so `pos v` is one of them
  have hlink : (P.tgt.graph).IsLink e (P.tgt.drawing e 0) (P.tgt.drawing e 1) :=
    (P.tgt.isDrawing.edge_param (by rwa [edgeSet_map] : e ∈ E(P.str.skel.map P.tgt.pos))).2.2
  rcases hl.left_eq_or_eq hlink with h0 | h1
  · exact ⟨e, he, h0 ▸ ⟨0, zero_mem_I, rfl⟩⟩
  · exact ⟨e, he, h1 ▸ ⟨1, one_mem_I, rfl⟩⟩

/-- A piece of the chain of a 1-cell is a listed overlay segment. -/
theorem skelSeg_mem_meshOverlayPieces {e : γ} (he : e ∈ E(P.str.skel)) {R : Piece}
    (hR : R ∈ segsOf (skelChain P e)) : R ∈ meshOverlayPieces P ε fresh joins :=
  List.mem_append_right _ (List.mem_append_left _ (mem_skelPieces.2 ⟨e, he, hR⟩))

/-- **Every drawn 0-cell of the stage is a vertex of the overlay.** -/
theorem meshOverlayGraph_vertexSet_subset
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)) :
    V(P.tgt.graph) ⊆ V(meshOverlayGraph P ε fresh joins) := by
  intro x hx
  rw [Realization.vertexSet_graph] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨e, he, hmem⟩ := pos_mem_edgeArc_of_vertex htgt hv
  rw [← cover_skelSegs P he] at hmem
  obtain ⟨R, hR, hmemR⟩ := mem_cover_iff.1 hmem
  exact overlay_mem_vertexSet_of_cut (pos_mem_meshOverlayPoints hv)
    (skelSeg_mem_meshOverlayPieces he hR) hmemR

/-- **The old drawn skeleton is part of the overlay.** -/
theorem meshOverlayGraph_skeletonSet_subset
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)) :
    P.tgt.skeletonSet ⊆ Graph.pointSet (meshOverlayGraph P ε fresh joins) segmentDrawing := by
  intro x hx
  obtain ⟨κ, hκ, hcell⟩ := Realization.exists_cell_of_mem_skeletonSet hx
  rcases hκ with hκ | hκ
  · -- a 0-cell: its position is a vertex of the overlay
    rw [P.tgt.cell_vertex hκ, mem_singleton_iff] at hcell
    subst hcell
    exact Graph.vertexSet_subset_pointSet (meshOverlayGraph_vertexSet_subset htgt
      (by rw [Realization.vertexSet_graph]; exact ⟨κ, hκ, rfl⟩))
  · -- a 1-cell: its open arc lies inside the drawn arc, which the overlay covers
    obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet hκ
    rw [P.tgt.cell_edge hl] at hcell
    rw [meshOverlayGraph_pointSet, cover_meshOverlayPieces]
    refine Or.inr (Or.inl ?_)
    rw [cover_skelPieces]
    exact mem_iUnion₂.2 ⟨κ, hκ, hcell.1⟩

/-- The open square sits inside the closed square off the model curve. -/
theorem openSquare_subset_closedSquare_diff :
    Plane.openSquare 0 1 ⊆ Plane.closedSquare 0 1 \ modelCurve := fun x hx =>
  ⟨mem_closedSquare_zero_one.2 (le_of_lt (mem_openSquare_zero_one.1 hx)),
    fun hS => absurd (show Plane.supNorm x = 1 from hS)
      (ne_of_lt (mem_openSquare_zero_one.1 hx))⟩

/-- **The overlay is drawn in the closed square.** -/
theorem meshOverlayGraph_pointSet_subset
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hjoins : cover joins ⊆ Plane.openSquare 0 1) :
    Graph.pointSet (meshOverlayGraph P ε fresh joins) segmentDrawing
      ⊆ Plane.closedSquare 0 1 := by
  rw [meshOverlayGraph_pointSet, cover_meshOverlayPieces]
  refine union_subset (cover_meshSegments_subset (two_le_meshCount ε) hfresh)
    (union_subset ?_ (hjoins.trans (fun x hx => (openSquare_subset_closedSquare_diff hx).1)))
  rw [cover_skelPieces]
  exact iUnion₂_subset fun e he =>
    (arc_subset_skeletonSet P he).trans htgt.skeletonSet_subset

/-! ### The subdivision clause

An overlay edge meeting an old open 1-cell at a non-vertex runs inside that 1-cell. The point
is interior to the overlay edge (its ends are vertices) and interior to the overlay piece
through it inside the 1-cell (its ends are cut points, hence vertices), so by separation the
two pieces are the same segment. -/

/-- The ends of an overlay edge are vertices. -/
theorem end_mem_vertexSet_meshOverlayGraph {f : Piece}
    (hf : f ∈ E(meshOverlayGraph P ε fresh joins)) {q : Plane} (hq : q = f.1 ∨ q = f.2) :
    q ∈ V(meshOverlayGraph P ε fresh joins) := ⟨f, hf, hq⟩

/-- A point of an overlay edge that is not a vertex is interior to the edge. -/
theorem mem_interior_of_mem_edge_not_vertex {f : Piece}
    (hf : f ∈ E(meshOverlayGraph P ε fresh joins)) {q : Plane} (hq : q ∈ f.seg)
    (hqV : q ∉ V(meshOverlayGraph P ε fresh joins)) : q ∈ f.interior := by
  by_contra hcon
  refine hqV (end_mem_vertexSet_meshOverlayGraph hf ?_)
  by_contra hend
  push Not at hend
  exact hcon (mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hq)

/-- **The overlay subdivides the old skeleton rather than crossing it** — the `edge_subset`
clause of `Schoenflies.MeshOverlayExtension`. -/
theorem meshOverlayGraph_edge_subset (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (hj : ∀ Q ∈ joins, Q.Nondeg) :
    ∀ ⦃e⦄, e ∈ E(P.str.skel) → ∀ ⦃f⦄, f ∈ E(meshOverlayGraph P ε fresh joins) → ∀ ⦃q⦄,
      q ∈ Graph.edgeArc segmentDrawing f → q ∈ P.tgt.cell e →
      q ∉ V(meshOverlayGraph P ε fresh joins) →
      Graph.edgeArc segmentDrawing f ⊆ Graph.edgeArc P.tgt.drawing e := by
  intro e he f hf q hqf hqcell hqV
  rw [edgeArc_segmentDrawing] at hqf ⊢
  have hnd := meshOverlayPieces_nondeg (P := P) (ε := ε) hfresh hj
  have hEnds := meshOverlayPoints_endsAreCut P ε fresh joins
  have hMeets := meshOverlayPoints_meetsAreCut P ε fresh joins
  -- `q` lies on the drawn 1-cell, hence on one of its chain pieces
  obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet he
  have hqarc : q ∈ Graph.edgeArc P.tgt.drawing e := by
    rw [P.tgt.cell_edge hl] at hqcell
    exact hqcell.1
  have hqcov : q ∈ cover (segsOf (skelChain P e)) := by rwa [cover_skelSegs P he]
  obtain ⟨R, hR, hqR⟩ := mem_cover_iff.1 hqcov
  -- the overlay piece through `q` inside that chain piece
  obtain ⟨Q, hQ, hqQ, hQR⟩ := subdivide_covers_source (meshOverlayPoints P ε fresh joins)
    (meshOverlayPieces P ε fresh joins) R (skelSeg_mem_meshOverlayPieces he hR) q hqR
  have hoQ : orientPiece Q ∈ E(meshOverlayGraph P ε fresh joins) :=
    mem_overlayPieces.2 ⟨Q, hQ, rfl⟩
  have hqQ' : q ∈ (orientPiece Q).seg := by rwa [orientPiece_seg]
  -- `q` is interior to both pieces, so they are the same edge
  have hqQi : q ∈ (orientPiece Q).interior := mem_interior_of_mem_edge_not_vertex hoQ hqQ' hqV
  have hqfi : q ∈ f.interior := mem_interior_of_mem_edge_not_vertex hf hqf hqV
  have hfQ : f = orientPiece Q := by
    by_contra hne
    exact overlayPieces_disjoint_interiors hnd hEnds hMeets hf hoQ hne hqfi hqQi
  rw [hfQ, orientPiece_seg]
  exact hQR.trans (seg_subset_edgeArc P he hR)

/-! ### The dichotomy and the boundary clauses

Every overlay edge is a subsegment of a listed segment, and the list is made of exactly four
kinds: outer material (the outer ring and the outer 1-cells), inner rings, spokes, and
material off `S` (nonboundary 1-cells away from their endpoints, joining arcs). The dichotomy
and both fresh-point clauses are case splits over that classification. -/

/-- **Each overlay edge is a boundary edge or a polygonal edge with interior off `S`.** -/
theorem meshOverlayGraph_edge_dichotomy
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hjoins : JoinsFor P ε joins) :
    ∀ ⦃f⦄, f ∈ E(meshOverlayGraph P ε fresh joins) →
      Graph.edgeArc segmentDrawing f ⊆ modelCurve ∨
      (IsPolygonal (Graph.edgeArc segmentDrawing f) ∧
        Graph.edgeArc segmentDrawing f \ V(meshOverlayGraph P ε fresh joins)
          ⊆ Plane.closedSquare 0 1 \ modelCurve) := by
  intro f hf
  rw [edgeArc_segmentDrawing]
  have hN := two_le_meshCount ε
  obtain ⟨R, hR, hsub, -⟩ := meshOverlayGraph_edge_source hf
  rcases List.mem_append.1 hR with hmesh | hrest
  · rcases mem_meshSegments.1 hmesh with ⟨r, hr, hRr⟩ | ⟨z, hz, rfl⟩
    · by_cases h1 : r = 1
      · -- a piece of the outer ring lies on `S`
        subst h1
        exact Or.inl (hsub.trans (ringPieces_seg_subset zero_le_one hRr))
      · -- a piece of an inner ring misses `S` outright
        refine Or.inr ⟨isPolygonal_segment _ _, fun x hx => ?_⟩
        have hxr : x ∈ ringSet r :=
          (hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)) hx.1
        exact ⟨mem_closedSquare_zero_one.2 (le_of_eq_of_le hxr (meshRadii_le_one hN hr)),
          fun hS => h1 (hxr.symm.trans hS)⟩
    · -- a piece of a spoke meets `S` only at its fresh point, which is a vertex
      refine Or.inr ⟨isPolygonal_segment _ _, fun x hx => ?_⟩
      refine ⟨spokePiece_subset_closedSquare hN (hfresh z hz) (hsub hx.1), fun hS => ?_⟩
      have hxz : x ∈ ({z} : Set Plane) := by
        rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
        exact ⟨hsub hx.1, hS⟩
      exact hx.2 (hxz ▸ fresh_mem_vertexSet_meshOverlayGraph hz)
  · rcases List.mem_append.1 hrest with hskel | hjoin
    · obtain ⟨e, he, hRe⟩ := mem_skelPieces.1 hskel
      by_cases hout : e ∈ E(P.str.outerGraph)
      · -- a piece of an outer 1-cell lies on the realized outer cycle, which is `S`
        have houter : Graph.edgeArc P.tgt.drawing e ⊆ P.tgt.outerSet :=
          Graph.edgeArc_subset_pointSet
            (show e ∈ E(P.str.outerGraph.map P.tgt.pos) by rwa [edgeSet_map])
        rw [htgt.outerSet_eq] at houter
        exact Or.inl ((hsub.trans (seg_subset_edgeArc P he hRe)).trans houter)
      · -- a piece of a nonboundary 1-cell, off the vertices, sits in the open 1-cell
        refine Or.inr ⟨isPolygonal_segment _ _, fun x hx => ?_⟩
        obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet he
        have hxarc : x ∈ Graph.edgeArc P.tgt.drawing e :=
          (hsub.trans (seg_subset_edgeArc P he hRe)) hx.1
        have hxab : x ∉ ({P.tgt.pos a, P.tgt.pos b} : Set Plane) := by
          intro hmem
          refine hx.2 (meshOverlayGraph_vertexSet_subset htgt ?_)
          rw [Realization.vertexSet_graph]
          rcases hmem with h | h
          · exact ⟨a, hl.left_mem, h.symm⟩
          · exact ⟨b, hl.right_mem, h.symm⟩
        refine htgt.cell_subset he hout ?_
        rw [P.tgt.cell_edge hl]
        exact ⟨hxarc, hxab⟩
    · -- a joining piece is drawn in the open square, off `S` outright
      exact Or.inr ⟨isPolygonal_segment _ _, fun x hx =>
        openSquare_subset_closedSquare_diff
          (hjoins.subset (mem_cover_iff.2 ⟨R, hjoin, hsub hx.1⟩))⟩

/-- **An overlay edge reaching `S` off both `S` and the old skeleton is a spoke piece at a
fresh point**, the point is that spoke's fresh point, and it is an end of the edge. -/
theorem meshOverlayGraph_spoke_edge_at
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hjoins : JoinsFor P ε joins)
    {p : Plane} (hp : p ∈ modelCurve) {f : Piece}
    (hf : f ∈ E(meshOverlayGraph P ε fresh joins)) (hpf : p ∈ f.seg)
    (hnb : ¬ f.seg ⊆ modelCurve) (hnew : ¬ f.seg ⊆ P.tgt.skeletonSet) :
    p ∈ fresh ∧ f.seg ⊆ (spokePiece (meshCount ε) p).seg ∧ (p = f.1 ∨ p = f.2) := by
  have hN := two_le_meshCount ε
  obtain ⟨R, hR, hsub, -⟩ := meshOverlayGraph_edge_source hf
  rcases List.mem_append.1 hR with hmesh | hrest
  · rcases mem_meshSegments.1 hmesh with ⟨r, hr, hRr⟩ | ⟨z, hz, rfl⟩
    · by_cases h1 : r = 1
      · exact absurd (hsub.trans (by subst h1; exact ringPieces_seg_subset zero_le_one hRr)) hnb
      · exfalso
        have hxr : p ∈ ringSet r :=
          (hsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)) hpf
        exact h1 (hxr.symm.trans hp)
    · -- the spoke case: `p` is the spoke's fresh point, a cut point, so an end of `f`
      have hpz : p ∈ ({z} : Set Plane) := by
        rw [← spokePiece_inter_modelCurve hN (hfresh z hz)]
        exact ⟨hsub hpf, hp⟩
      rw [mem_singleton_iff] at hpz
      subst hpz
      refine ⟨hz, hsub, ?_⟩
      have hpts : p ∈ meshOverlayPoints P ε fresh joins :=
        meshOverlayPoints_endsAreCut P ε fresh joins _
          (List.mem_append_left _ (spokePiece_mem_meshSegments hz)) p (Or.inl rfl)
      by_contra hcon
      push Not at hcon
      exact overlayPieces_avoids (meshOverlayPieces_nondeg hfresh hjoins.nondeg) p hpts f hf
        (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hpf)
  · rcases List.mem_append.1 hrest with hskel | hjoin
    · obtain ⟨e, he, hRe⟩ := mem_skelPieces.1 hskel
      exact absurd (hsub.trans ((seg_subset_edgeArc P he hRe).trans
        (arc_subset_skeletonSet P he))) hnew
    · exact absurd hp (openSquare_subset_closedSquare_diff
        (hjoins.subset (mem_cover_iff.2 ⟨R, hjoin, hsub hpf⟩))).2

/-- **A new nonboundary edge reaches `S` only at a listed fresh point.** -/
theorem meshOverlayGraph_nonboundaryAt_mem_fresh
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hjoins : JoinsFor P ε joins) :
    ∀ ⦃p⦄, p ∈ modelCurve →
      NonboundaryAt (meshOverlayGraph P ε fresh joins) segmentDrawing modelCurve
        P.tgt.skeletonSet p → p ∈ fresh := by
  intro p hp hnb
  obtain ⟨f, hf, hpf, hnbf, hnewf⟩ := hnb
  rw [edgeArc_segmentDrawing] at hpf hnbf hnewf
  exact (meshOverlayGraph_spoke_edge_at hfresh hjoins hp hf hpf hnbf hnewf).1

/-- **One new nonboundary edge per fresh boundary point.** Two such edges are subpieces of the
spoke at the point with the point as an end, so their interiors overlap just inside `S`, and
separation makes them the same edge. -/
theorem meshOverlayGraph_unique_edge
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hjoins : JoinsFor P ε joins) :
    ∀ ⦃p⦄, p ∈ modelCurve → ∀ ⦃f g⦄, f ∈ E(meshOverlayGraph P ε fresh joins) →
      g ∈ E(meshOverlayGraph P ε fresh joins) →
      p ∈ Graph.edgeArc segmentDrawing f → p ∈ Graph.edgeArc segmentDrawing g →
      ¬ Graph.edgeArc segmentDrawing f ⊆ modelCurve →
      ¬ Graph.edgeArc segmentDrawing g ⊆ modelCurve →
      ¬ Graph.edgeArc segmentDrawing f ⊆ P.tgt.skeletonSet →
      ¬ Graph.edgeArc segmentDrawing g ⊆ P.tgt.skeletonSet → f = g := by
  intro p hp f g hf hg hpf hpg hnbf hnbg hnewf hnewg
  rw [edgeArc_segmentDrawing] at hpf hpg hnbf hnbg hnewf hnewg
  have hN := two_le_meshCount ε
  obtain ⟨-, hsubf, hendf⟩ :=
    meshOverlayGraph_spoke_edge_at hfresh hjoins hp hf hpf hnbf hnewf
  obtain ⟨-, hsubg, hendg⟩ :=
    meshOverlayGraph_spoke_edge_at hfresh hjoins hp hg hpg hnbg hnewg
  obtain ⟨tf, hltf, hintf⟩ := spoke_subpiece_interior hN
    (meshOverlayGraph_edge_nondeg hfresh hjoins.nondeg hf) hsubf hendf
  obtain ⟨tg, hltg, hintg⟩ := spoke_subpiece_interior hN
    (meshOverlayGraph_edge_nondeg hfresh hjoins.nondeg hg) hsubg hendg
  by_contra hne
  -- both interiors contain every multiple `s • p` with `max tf tg < s < 1`
  set s : ℝ := (max tf tg + 1) / 2 with hs
  have hmax : max tf tg < 1 := max_lt hltf hltg
  have hs1 : s < 1 := by rw [hs]; linarith
  have hsf : tf < s := by rw [hs]; linarith [le_max_left tf tg]
  have hsg : tg < s := by rw [hs]; linarith [le_max_right tf tg]
  refine overlayPieces_disjoint_interiors (meshOverlayPieces_nondeg hfresh hjoins.nondeg)
    (meshOverlayPoints_endsAreCut P ε fresh joins)
    (meshOverlayPoints_meetsAreCut P ε fresh joins) hf hg hne (x := s • p) ?_ ?_
  · rw [hintf]; exact ⟨s, ⟨hsf, hs1⟩, rfl⟩
  · rw [hintg]; exact ⟨s, ⟨hsg, hs1⟩, rfl⟩

/-! ### Connectivity off `S`

`|H| ∖ S` is connected: the mesh off `S` is connected and contains the base point, the outer
material vanishes off `S`, and `JoinsFor.connects` ties every remaining point to the base
point. The joining arcs are load-bearing here — mesh ∪ skeleton alone can leave a nonboundary
component stranded. -/

/-- A list inclusion pushes covers forward. (General-purpose; a candidate for hoisting into
`Schoenflies/Subdivide.lean`.) -/
theorem cover_mono {l l' : List Piece} (h : l ⊆ l') : cover l ⊆ cover l' := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := mem_cover_iff.1 hx
  exact mem_cover_iff.2 ⟨Q, h hQ, hxQ⟩

/-- The drawn arc of an outer 1-cell lies on `S`. -/
theorem outer_arc_subset_modelCurve
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)) {e : γ}
    (hout : e ∈ E(P.str.outerGraph)) :
    Graph.edgeArc P.tgt.drawing e ⊆ modelCurve := by
  have houter : Graph.edgeArc P.tgt.drawing e ⊆ P.tgt.outerSet :=
    Graph.edgeArc_subset_pointSet
      (show e ∈ E(P.str.outerGraph.map P.tgt.pos) by rwa [edgeSet_map])
  rwa [htgt.outerSet_eq] at houter

/-- **`|H| ∖ S` is connected.** -/
theorem meshOverlayGraph_isConnected
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hjoins : JoinsFor P ε joins)
    {z₀ : Plane} (hz₀ : z₀ ∈ fresh) :
    IsConnected
      (Graph.pointSet (meshOverlayGraph P ε fresh joins) segmentDrawing \ modelCurve) := by
  rw [meshOverlayGraph_pointSet, cover_meshOverlayPieces]
  have hmesh : IsConnected (cover (meshSegments (meshCount ε) fresh) \ modelCurve) :=
    isConnected_cover_diff_modelCurve (two_le_meshCount ε) hfresh hz₀
  have hbase : meshBase ε ∈ cover (meshSegments (meshCount ε) fresh) \ modelCurve :=
    ⟨meshBase_mem_cover_meshSegments ε fresh, meshBase_notMem_modelCurve ε⟩
  have hmesh_sub : cover (meshSegments (meshCount ε) fresh) \ modelCurve
      ⊆ (cover (meshSegments (meshCount ε) fresh)
          ∪ (cover (skelPieces P) ∪ cover joins)) \ modelCurve :=
    fun w hw => ⟨Or.inl hw.1, hw.2⟩
  -- the connecting set delivered by `JoinsFor`, pushed into the full cover
  have hAin : ∀ A : Set Plane,
      A ⊆ (cover (skelNbPieces P) ∪ cover joins ∪ {meshBase ε}) \ modelCurve →
      A ⊆ (cover (meshSegments (meshCount ε) fresh)
          ∪ (cover (skelPieces P) ∪ cover joins)) \ modelCurve := by
    intro A hA w hw
    obtain ⟨hw1, hw2⟩ := hA hw
    refine ⟨?_, hw2⟩
    rcases hw1 with (hw1 | hw1) | hw1
    · exact Or.inr (Or.inl (cover_mono (skelNbPieces_subset P) hw1))
    · exact Or.inr (Or.inr hw1)
    · rw [mem_singleton_iff] at hw1
      exact hw1 ▸ Or.inl (meshBase_mem_cover_meshSegments ε fresh)
  refine ⟨⟨meshBase ε, hmesh_sub hbase⟩, isPreconnected_of_forall (meshBase ε) ?_⟩
  rintro y ⟨hy, hyS⟩
  -- a point off the mesh reaches the base point through its `JoinsFor` connecting set
  have viaJoins : y ∈ (cover (skelNbPieces P) ∪ cover joins) \ modelCurve →
      ∃ t, t ⊆ (cover (meshSegments (meshCount ε) fresh)
          ∪ (cover (skelPieces P) ∪ cover joins)) \ modelCurve ∧
        meshBase ε ∈ t ∧ y ∈ t ∧ IsPreconnected t := by
    intro hynb
    obtain ⟨A, hAsub, hAconn, hyA, hbA⟩ := hjoins.connects y hynb
    exact ⟨A, hAin A hAsub, hbA, hyA, hAconn⟩
  rcases hy with hy | hy
  · -- on the mesh: the mesh off `S` is one connected set through the base point
    exact ⟨cover (meshSegments (meshCount ε) fresh) \ modelCurve, hmesh_sub, hbase,
      ⟨hy, hyS⟩, hmesh.isPreconnected⟩
  rcases hy with hy | hy
  · -- on the skeleton: outer pieces vanish off `S`, nonboundary ones go through the joins
    obtain ⟨R, hRmem, hyR⟩ := mem_cover_iff.1 hy
    obtain ⟨e, he, hRe⟩ := mem_skelPieces.1 hRmem
    by_cases hout : e ∈ E(P.str.outerGraph)
    · exact absurd (outer_arc_subset_modelCurve htgt hout
        (seg_subset_edgeArc P he hRe hyR)) hyS
    · exact viaJoins ⟨Or.inl (mem_cover_iff.2 ⟨R, mem_skelNbPieces.2 ⟨e, ⟨he, hout⟩, hRe⟩,
        hyR⟩), hyS⟩
  · -- on a joining arc
    exact viaJoins ⟨Or.inr hy, hyS⟩

/-! ### The joining arcs exist

`Schoenflies.exists_reps_cover_diff` produces finitely many representatives meeting every
component of the nonboundary skeleton off `S` — each nonboundary piece meets `S` in at most
the two drawn endpoints of its 1-cell, which is the `MeetsFinitely` input — and
`Schoenflies.exists_poly_of_isPreconnected` joins each representative to the mesh base point
inside the open square. -/

/-- Each nonboundary skeleton piece meets `S` finitely: in at most the two drawn endpoints of
its 1-cell. -/
theorem skelNbPieces_meetsFinitely
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)) :
    MeetsFinitely (skelNbPieces P) modelCurve := by
  intro Q hQ
  obtain ⟨e, ⟨he, hout⟩, hQe⟩ := mem_skelNbPieces.1 hQ
  obtain ⟨a, b, hl⟩ := exists_isLink_of_mem_edgeSet he
  have hsub : Q.seg ∩ modelCurve ⊆ {P.tgt.pos a, P.tgt.pos b} := by
    rintro x ⟨hx1, hx2⟩
    by_contra hcon
    have hxcell : x ∈ P.tgt.cell e := by
      rw [P.tgt.cell_edge hl]
      exact ⟨seg_subset_edgeArc P he hQe hx1, hcon⟩
    exact (htgt.cell_subset he hout hxcell).2 hx2
  exact (Set.finite_singleton _ |>.insert _).subset hsub

/-- **Joining arcs exist.** This is what makes the 2-connectivity hypothesis below
non-vacuous: its existential over `joins` always has a witness satisfying `JoinsFor`. -/
theorem exists_joinsFor (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    (ε : ℝ) : ∃ joins : List Piece, JoinsFor P ε joins := by
  obtain ⟨reps, hrmem, hrcov⟩ :=
    exists_reps_cover_diff (skelNbPieces P) (skelNbPieces_meetsFinitely htgt)
  -- every representative sits in the open square
  have hrepΩ : ∀ r ∈ reps, r ∈ Plane.openSquare 0 1 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hrmem r hr
    obtain ⟨Q, hQ, hrQ⟩ := mem_cover_iff.1 hr1
    obtain ⟨e, ⟨he, -⟩, hQe⟩ := mem_skelNbPieces.1 hQ
    have hsq : r ∈ Plane.closedSquare 0 1 := htgt.skeletonSet_subset
      (arc_subset_skeletonSet P he (seg_subset_edgeArc P he hQe hrQ))
    exact mem_openSquare_zero_one.2
      (lt_of_le_of_ne (mem_closedSquare_zero_one.1 hsq) fun h => hr2 h)
  have hΩo : IsOpen (Plane.openSquare 0 1) := Plane.isOpen_openSquare 0 1
  have hΩc : IsPreconnected (Plane.openSquare 0 1) :=
    (Plane.convex_openSquare 0 1).isPreconnected
  have hbΩ : meshBase ε ∈ Plane.openSquare 0 1 := meshBase_mem_openSquare ε
  -- a chain from each representative to the base point, inside the open square
  have key : ∀ rs : List Plane, (∀ r ∈ rs, r ∈ Plane.openSquare 0 1) →
      ∃ js : List Piece, (∀ Q ∈ js, Q.Nondeg) ∧ cover js ⊆ Plane.openSquare 0 1 ∧
        (∀ r ∈ rs, ∃ A : Set Plane, A ⊆ cover js ∪ {meshBase ε} ∧ IsPreconnected A ∧
          r ∈ A ∧ meshBase ε ∈ A) ∧
        (∀ x ∈ cover js, ∃ A : Set Plane, A ⊆ cover js ∪ {meshBase ε} ∧ IsPreconnected A ∧
          x ∈ A ∧ meshBase ε ∈ A) := by
    intro rs
    induction rs with
    | nil => exact fun _ => ⟨[], by simp, by simp, by simp, by simp⟩
    | cons r rs ih =>
      intro hmem
      obtain ⟨js, hnd, hsub, hreps, hpts⟩ := ih fun w hw => hmem w (List.mem_cons_of_mem _ hw)
      obtain ⟨vs, hne, hvsub, hhead, hlast⟩ :=
        exists_poly_of_isPreconnected hΩo hΩc (hmem r List.mem_cons_self) hbΩ
      have hcs : cover (segsOf vs) ⊆ poly vs := by
        rcases cover_segsOf vs with h | ⟨h1, -⟩
        · exact h.le
        · rw [h1, cover_nil]; exact empty_subset _
      -- the chain's carrier connects everything on it — including `r` — to the base point
      have hchain : ∀ x ∈ poly vs, ∃ A : Set Plane,
          A ⊆ cover (segsOf vs ++ js) ∪ {meshBase ε} ∧ IsPreconnected A ∧
            x ∈ A ∧ meshBase ε ∈ A := by
        intro x hx
        rcases cover_segsOf vs with hcov | ⟨-, hsing⟩
        · refine ⟨poly vs, ?_, (isConnected_poly hne).isPreconnected, hx,
            hlast ▸ getLast_mem_poly hne⟩
          rw [cover_append, ← hcov]
          exact fun w hw => Or.inl (Or.inl hw)
        · -- the chain collapsed to the base point
          have hxb : x = meshBase ε :=
            hsing hx (hlast ▸ getLast_mem_poly hne)
          exact ⟨{meshBase ε}, fun w hw => Or.inr hw, isPreconnected_singleton,
            hxb ▸ rfl, rfl⟩
      refine ⟨segsOf vs ++ js, ?_, ?_, ?_, ?_⟩
      · intro Q hQ
        rcases List.mem_append.1 hQ with h | h
        · exact segsOf_nondeg vs Q h
        · exact hnd Q h
      · rw [cover_append]
        exact union_subset (hcs.trans hvsub) hsub
      · intro w hw
        rcases List.mem_cons.1 hw with rfl | hw'
        · exact hchain w (hhead ▸ head_mem_poly hne)
        · obtain ⟨A, hA, hAc, hwA, hbA⟩ := hreps w hw'
          refine ⟨A, hA.trans ?_, hAc, hwA, hbA⟩
          rw [cover_append]
          exact union_subset_union_left _ subset_union_right
      · intro x hx
        rw [cover_append] at hx
        rcases hx with hx | hx
        · exact hchain x (hcs hx)
        · obtain ⟨A, hA, hAc, hxA, hbA⟩ := hpts x hx
          refine ⟨A, hA.trans ?_, hAc, hxA, hbA⟩
          rw [cover_append]
          exact union_subset_union_left _ subset_union_right
  obtain ⟨js, hnd, hsub, hreps, hpts⟩ := key reps hrepΩ
  -- assemble `JoinsFor`: the joining cover misses `S`, so the sets stay off `S`
  have hjS : ∀ w ∈ cover js ∪ ({meshBase ε} : Set Plane), w ∉ modelCurve := by
    rintro w (hw | hw) hwS
    · exact absurd (show Plane.supNorm w = 1 from hwS)
        (ne_of_lt (mem_openSquare_zero_one.1 (hsub hw)))
    · rw [mem_singleton_iff] at hw
      exact meshBase_notMem_modelCurve ε (hw ▸ hwS)
  refine ⟨js, hnd, hsub, ?_⟩
  rintro x ⟨hx, hxS⟩
  rcases hx with hx | hx
  · -- on the nonboundary skeleton: representative first, then its chain
    obtain ⟨r, hr, A₀, hA₀sub, hA₀conn, hxA₀, hrA₀⟩ := hrcov x ⟨hx, hxS⟩
    obtain ⟨A₁, hA₁sub, hA₁conn, hrA₁, hbA₁⟩ := hreps r hr
    refine ⟨A₀ ∪ A₁, ?_, IsPreconnected.union r hrA₀ hrA₁ hA₀conn hA₁conn,
      Or.inl hxA₀, Or.inr hbA₁⟩
    rintro w (hw | hw)
    · obtain ⟨hw1, hw2⟩ := hA₀sub hw
      exact ⟨Or.inl (Or.inl hw1), hw2⟩
    · rcases hA₁sub hw with hw' | hw'
      · exact ⟨Or.inl (Or.inr hw'), hjS w (Or.inl hw')⟩
      · exact ⟨Or.inr hw', hjS w (Or.inr hw')⟩
  · -- on a joining arc
    obtain ⟨A, hA, hAc, hxA, hbA⟩ := hpts x hx
    refine ⟨A, ?_, hAc, hxA, hbA⟩
    intro w hw
    rcases hA hw with hw' | hw'
    · exact ⟨Or.inl (Or.inr hw'), hjS w (Or.inl hw')⟩
    · exact ⟨Or.inr hw', hjS w (Or.inr hw')⟩

/-! ### The assembly, and the reduction -/

/-- **The extension, assembled.** Every clause of `Schoenflies.MeshOverlayExtension` is one of
the theorems above; 2-connectivity is the argument. -/
noncomputable def meshOverlayExtension_of_joins
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (hne : ∃ z, z ∈ fresh)
    (hjoins : JoinsFor P ε joins)
    (h2c : (meshOverlayGraph P ε fresh joins).IsTwoConnected) :
    MeshOverlayExtension P ε fresh Piece where
  H := meshOverlayGraph P ε fresh joins
  Hdraw := segmentDrawing
  finite := meshOverlayGraph_finite P ε fresh joins
  isDrawing := meshOverlayGraph_isDrawing hfresh hjoins.nondeg
  isTwoConnected := h2c
  vertexSet_subset := meshOverlayGraph_vertexSet_subset htgt
  skeletonSet_subset := meshOverlayGraph_skeletonSet_subset htgt
  edge_subset := meshOverlayGraph_edge_subset hfresh hjoins.nondeg
  pointSet_subset := meshOverlayGraph_pointSet_subset htgt hfresh hjoins.subset
  edge_dichotomy := meshOverlayGraph_edge_dichotomy htgt hfresh hjoins
  isConnected := by
    obtain ⟨z₀, hz₀⟩ := hne
    exact meshOverlayGraph_isConnected htgt hfresh hjoins hz₀
  nonboundaryAt_mem_fresh := meshOverlayGraph_nonboundaryAt_mem_fresh hfresh hjoins
  unique_edge := meshOverlayGraph_unique_edge hfresh hjoins
  mesh_subset := mesh_cover_subset P ε fresh joins

/-- **NAMED HYPOTHESIS — 2-connectivity of the mesh overlay.** At every admissible stage,
mesh size and fresh list there are joining arcs satisfying `Schoenflies.JoinsFor` whose
overlay `Schoenflies.meshOverlayGraph` is 2-connected. Every other clause of
`Schoenflies.MeshOverlayExtension` is a theorem of this module, so this is all that separates
`Schoenflies.HasMeshOverlays` from discharge.

The existential over `joins` is at the discharger's disposal, and `Schoenflies.exists_joinsFor`
shows it always has a `JoinsFor` witness — the hypothesis only adds that *some* witness can be
taken 2-connected. The intended route (blueprint `lem:polygonal-overlay` +
`prop:anchored-square-mesh` clause 5):

* the overlay restricted to the pieces of the old skeleton is a **subdivision of `Γ'`**, which
  is 2-connected by admissibility (`IsWeaklyAdmissible.isTwoConnected`,
  `Graph.IsSubdivisionOf.isTwoConnected`);
* the overlay restricted to the mesh pieces is a subdivision of
  `Schoenflies.squareMesh ε fresh anchors`, 2-connected by
  `Schoenflies.squareMesh_isTwoConnected` — the two distinct fresh points are supplied here as
  a hypothesis;
* the two share at least two vertices (any two of the four corners of the outer ring, which
  are vertices of both), so `Graph.IsTwoConnected.union` glues them;
* each joining arc, *chosen simple* — the freedom the existential grants — goes in as an ear
  between two vertices of the union (`Graph.IsTwoConnected.ear` /
  `Graph/RelativeEar.lean`). -/
def HasTwoConnectedMeshOverlays (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃fresh : List Plane⦄,
      (∀ z ∈ fresh, z ∈ modelCurve ∧ z ∉ V(P.tgt.graph)) →
      (∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w) →
      ∃ joins : List Piece, JoinsFor P ε joins ∧
        (meshOverlayGraph P ε fresh joins).IsTwoConnected

/-- **The discharge of `Schoenflies.HasMeshOverlays`, up to 2-connectivity.** The bad set is
empty — the construction handles every fresh position. -/
theorem hasMeshOverlays_of (hcore : HasTwoConnectedMeshOverlays S₀ C) :
    HasMeshOverlays S₀ C := by
  intro P hsrc htgt ε hε
  refine ⟨∅, finite_empty, ?_⟩
  intro fresh hfresh hne
  obtain ⟨joins, hjoins, h2c⟩ := hcore P hsrc htgt hε
    (fun z hz => ⟨(hfresh z hz).1, (hfresh z hz).2.1⟩) hne
  obtain ⟨z, hz, -⟩ := hne
  exact ⟨meshOverlayExtension_of_joins htgt (fun w hw => (hfresh w hw).1) ⟨z, hz⟩ hjoins h2c⟩

/-! ### The interface, exercised

Over the concrete base, Phase 3 now rests on the source-grid chooser and the overlay's
2-connectivity — the extension's other nine clauses are no longer obligations. -/

example {C : Set Plane} (hC : IsJordanCurve C) (hg : HasGridSteps initialStructure C)
    (hcore : HasTwoConnectedMeshOverlays initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC hg
    (hasMeshSteps (hasMeshTransfers combInvariants_initialStructure
      (jordan_curve_theorem hC) (hasMeshOverlays_of hcore)))⟩

end Schoenflies
