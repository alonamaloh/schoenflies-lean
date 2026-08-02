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

end Schoenflies
