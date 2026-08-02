/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.GridExtension

/-!
# 2-connectivity of the grid union, reduced to its anchored skeleton core

`Schoenflies.HasGridUnionTwoConnected` (`Schoenflies/GridExtension.lean`) asks, at every
admissible stage, mesh and window centre, for auxiliary segments and cut points making the
assembled union `Schoenflies.gridExtGraph` — the stage's wild outer cycle, the subdivided
polygonal nonboundary skeleton, the auxiliary segments, the joining arcs and the local grid,
overlaid — 2-connected. This module discharges the *grid half* of that: the local grid's part
of the overlay is 2-connected on its own (`Schoenflies.localGrid_subdivide_isTwoConnected`,
carried across the overlay's orient-and-dedup step and the edge renaming into the sum type),
it contains every vertex of the union lying on the grid, and it glues onto the rest of the
union by `Graph.IsTwoConnected.union` at two anchor points where the auxiliary segments cross
the grid.

What remains is the *skeleton half*, the named hypothesis
`Schoenflies.HasGridAnchoredCores` below: auxiliary segments and cut points — among them two
anchors lying on both the auxiliary segments and the grid — such that the union restricted to
everything **off** the grid (the outer cycle, the skeleton chains, the auxiliary segments and
the joining arcs) is spanned by a 2-connected subgraph. That is `lem:subdivision-ear-preserve`
at the stage: the outer cycle plus the subdivided nonboundary skeleton is a subdivision of the
stage's own 2-connected graph, the auxiliary segments enter as a crosscut ear anchored on the
skeleton, and each joining arc — simple by `Schoenflies.IsJoinFamily` — enters as an ear from
the hub. None of that mentions the grid's interior, which is exactly the part this module
absorbs.

## Why the carve is here

The mesh side made the same cut: `Schoenflies.hasTwoConnectedMeshOverlays_of`
(`Schoenflies/MeshTwoConnected.lean`) absorbs the joining chains and leaves the
mesh-and-skeleton core as `Schoenflies.HasTwoConnectedCores`. On the grid side the joining
family is *universally* quantified — the interface of `Schoenflies.HasGridUnionTwoConnected`
fixes `Schoenflies.IsJoinFamily`, whose chains carry simple **arcs** but need not be simple
**chains** — so the ear-by-ear absorption of the joins belongs with the skeleton core, where
the arc-ordering machinery it needs will live. What can be split off cleanly is the grid: its
2-connectivity after arbitrary subdivision is already proved, and the union argument of
`lem:union-two-connected` needs only two shared cut points, which the hypothesis's anchors
supply.

## Blueprint

* `Graph.renameEdges_mono`, `Graph.renameEdges_inr_le_sumUnion` — not numbered statements;
  transport of subgraphs along the edge renaming into the union's sum type. General-purpose;
  candidates for hoisting into `Schoenflies/Graph/RenameEdges.lean` beside
  `Graph.IsTwoConnected.renameEdges`.
* `Schoenflies.endSet_map_orientPiece`, `Schoenflies.sameLinks_pieceListGraph_orientPiece` —
  the orient-only half of `Schoenflies.sameLinks_overlayGraph`: orienting a piece list changes
  edge names, not links. Candidates for hoisting beside `Graph.SameLinks` in
  `Schoenflies/GridAttach.lean`.
* `Schoenflies.gridPartGraph` and its lemmas — the grid's part of the overlay as a named
  subgraph of the union: 2-connected (`lem:subdivision-ear-preserve` (a) for the grid, via
  `Schoenflies.localGrid_subdivide_isTwoConnected`), and containing every union vertex on the
  grid.
* `Schoenflies.HasGridAnchoredCores` — **the remaining named hypothesis**: the union off the
  grid is spanned by a 2-connected subgraph, with two anchors on the grid.
* `Schoenflies.hasGridUnionTwoConnected_of` — `lem:union-two-connected` at the stage: the
  anchored core and the grid part glue at the two anchors, and the union of the two spans, so
  `Schoenflies.HasGridUnionTwoConnected` follows.
* `Schoenflies.hasGridSteps_of_anchoredCores` and the closing `example` — the composition
  through `Schoenflies.hasGridExtensions_of` and `Schoenflies.hasGridSteps` down to
  `Schoenflies.HasGridSteps`.
-/

open Metric Set Schoenflies
open scoped Graph

/-! ## Subgraph transport along an edge renaming

`Graph.renameEdges` keeps vertices and links and renames edges injectively; a subgraph
relation survives it, and the `Sum.inr`-renamed graph sits inside the sum-union it was built
into. General graph theory; flagged for hoisting into `Schoenflies/Graph/RenameEdges.lean`. -/

namespace Graph

variable {α β β₁ β₂ : Type*} {γ' : Type*}

/-- **Renaming edges is monotone in the graph.** -/
theorem renameEdges_mono {G G' : Graph α β} {σ : β → γ'} (hle : G ≤ G')
    (hσ : Set.InjOn σ E(G)) (hσ' : Set.InjOn σ E(G')) :
    G.renameEdges σ hσ ≤ G'.renameEdges σ hσ' where
  vertexSet_mono := hle.vertexSet_mono
  isLink_mono := by
    rintro g x y hl
    obtain ⟨e, he, rfl, hl'⟩ := renameEdges_isLink.1 hl
    exact renameEdges_isLink.2 ⟨e, hle.edgeSet_mono he, rfl, hle.isLink_mono hl'⟩

/-- The second summand of `Graph.sumUnion`, renamed into the sum type, is a subgraph of the
union. -/
theorem renameEdges_inr_le_sumUnion (G₁ : Graph Plane β₁) (G₂ : Graph Plane β₂) :
    G₂.renameEdges Sum.inr Sum.inr_injective.injOn ≤ G₁.sumUnion G₂ where
  vertexSet_mono := by
    rw [renameEdges_vertexSet, sumUnion_vertexSet]
    exact Set.subset_union_right
  isLink_mono := by
    rintro g x y hl
    obtain ⟨P, -, rfl, hl'⟩ := renameEdges_isLink.1 hl
    exact sumUnion_isLink_inr.2 hl'

end Graph

namespace Schoenflies

open Graph CellStructure

/-! ## Orienting a piece list does not change its links

The overlay's edges are the subdivided pieces *oriented*; `Schoenflies.sameLinks_overlayGraph`
handles orient-and-dedup for the whole subdivision, but the grid part needs the orient-only
step on its own sublist, so that `Schoenflies.pieceListGraph_mono` can place it inside the
overlay. Flagged for hoisting beside `Graph.SameLinks` in `Schoenflies/GridAttach.lean`. -/

/-- Orienting does not change which points are ends of the list. -/
theorem endSet_map_orientPiece (l : List Piece) : endSet (l.map orientPiece) = endSet l := by
  ext v
  constructor
  · rintro ⟨P, hP, hv⟩
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hP
    exact ⟨Q, hQ, (orientPiece_ends Q v).1 hv⟩
  · rintro ⟨Q, hQ, hv⟩
    exact ⟨orientPiece Q, List.mem_map_of_mem hQ, (orientPiece_ends Q v).2 hv⟩

/-- **Orienting a piece list renames its edges without changing its links.** -/
theorem sameLinks_pieceListGraph_orientPiece (l : List Piece) :
    Graph.SameLinks (pieceListGraph l) (pieceListGraph (l.map orientPiece)) := by
  constructor
  · rw [pieceListGraph_vertexSet, pieceListGraph_vertexSet, endSet_map_orientPiece]
  · intro x y
    simp only [pieceListGraph_isLink]
    constructor
    · rintro ⟨P, hP, hxy⟩
      exact ⟨orientPiece P, List.mem_map_of_mem hP, (orientPiece_link_iff P x y).2 hxy⟩
    · rintro ⟨P, hP, hxy⟩
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hP
      exact ⟨Q, hQ, (orientPiece_link_iff Q x y).1 hxy⟩

/-! ## The grid's part of the overlay

The subgraph of `Schoenflies.gridAttachGraph` carried by the subdivided grid pieces: its
edges are the grid's subpieces oriented, which is how they are named in the overlay. It is
2-connected because the raw subdivided grid is, and it holds every overlay vertex lying on
the grid, because such a vertex is a cut point and a cut point on the grid cuts the grid. -/

variable {γ : Type*} {gsegs : List Piece} {reps : List Plane} {Jarc : Plane → List Piece}
  {p : Plane} {s ε : ℝ} {extra : List Plane}

/-- **The grid part of the overlay**: the subdivided local grid, oriented, as a piece-list
graph. Its edge names are exactly the names the overlay gives the grid's subpieces. -/
noncomputable def gridPartGraph (gsegs : List Piece) (reps : List Plane)
    (Jarc : Plane → List Piece) (p : Plane) (s ε : ℝ) (extra : List Plane) :
    Graph Plane Piece :=
  pieceListGraph
    ((subdivide (localGridEdges p s (localGridCount s ε))
      (attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra)).map orientPiece)

/-- **The grid part is 2-connected** — `Schoenflies.localGrid_subdivide_isTwoConnected`
carried across the orientation renaming. -/
theorem gridPartGraph_isTwoConnected (hs : 0 < s) :
    (gridPartGraph gsegs reps Jarc p s ε extra).IsTwoConnected :=
  (localGrid_subdivide_isTwoConnected hs (one_le_localGridCount s ε) _).sameLinks
    (sameLinks_pieceListGraph_orientPiece _)

/-- The grid part sits inside the overlay: its edges are overlay edges by name. -/
theorem gridPartGraph_le :
    gridPartGraph gsegs reps Jarc p s ε extra ≤ gridAttachGraph gsegs reps Jarc p s ε extra := by
  have heq : gridAttachGraph gsegs reps Jarc p s ε extra =
      pieceListGraph (overlayPieces (gridAttachPieces gsegs reps Jarc p s ε)
        (attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra)) :=
    overlayGraph_eq_pieceListGraph _ _
  rw [heq]
  refine pieceListGraph_mono ?_
  intro Q hQ
  obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ
  refine mem_overlayPieces.2 ⟨Q', ?_, rfl⟩
  rw [gridAttachPieces, subdivide_append]
  exact List.mem_append_right _ hQ'

/-- **A cut point on the grid is a vertex of the grid part.** -/
theorem mem_gridPartGraph_of_mem_cover (hs : 0 < s) {x : Plane}
    (hx : x ∈ attachPoints (gridAttachPieces gsegs reps Jarc p s ε) extra)
    (hxc : x ∈ cover (localGridEdges p s (localGridCount s ε))) :
    x ∈ V(gridPartGraph gsegs reps Jarc p s ε extra) := by
  rw [gridPartGraph, pieceListGraph_vertexSet, endSet_map_orientPiece]
  exact mem_endSet_subdivide_of_mem_cover
    (localGridEdges_nondeg hs (one_le_localGridCount s ε)) hx hxc

/-- **Every overlay vertex on the grid lies in the grid part** — an overlay vertex is an end
of an overlay edge, hence a cut point, and a cut point on the grid cuts the grid. -/
theorem vertexSet_inter_grid_subset (hs : 0 < s) {x : Plane}
    (hx : x ∈ V(gridAttachGraph gsegs reps Jarc p s ε extra))
    (hxc : x ∈ cover (localGridEdges p s (localGridCount s ε))) :
    x ∈ V(gridPartGraph gsegs reps Jarc p s ε extra) := by
  rw [gridAttachGraph, attachGraph, overlayGraph_vertexSet] at hx
  obtain ⟨Q, hQ, hxQ⟩ := hx
  exact mem_gridPartGraph_of_mem_cover hs
    (overlayPieces_ends_cut (attachPoints_endsAreCut _ _) Q hQ x hxQ) hxc

/-! ## The named hypothesis, and the reduction -/

section Assemble

variable {S₀ : CellStructure γ}

/-- **NAMED HYPOTHESIS — the anchored skeleton core of the grid union.**

At every admissible stage, mesh and window centre: auxiliary segments `xsegs` and cut points
`xtra` — among them two distinct *anchors* lying on both the auxiliary segments and the local
grid — such that for any representative list on the cover off `C` and any joining family as
`Schoenflies.IsJoinFamily` describes, the assembled union `Schoenflies.gridExtGraph` has a
2-connected subgraph containing every vertex of the union that lies on a drawn 0-cell or on
the pieces off the grid (the skeleton chains, the auxiliary segments and the joining arcs).

This is the skeleton half of `lem:union-two-connected` at the stage, and its discharger's
route is `lem:subdivision-ear-preserve`: the outer cycle together with the subdivided
nonboundary skeleton chains is a subdivision of the stage's own graph, 2-connected by
admissibility (the cross-edge-type transport of `Graph.IsSubdivisionOf.isTwoConnected`, as in
the mesh side's `Schoenflies.HasTwoConnectedSkelCores`); the auxiliary segments — chosen by
the discharger as a crosscut through the window with both ends on the nonboundary skeleton —
enter by `Graph.IsTwoConnected.ear`, and their crossings with the grid supply the two anchors;
each joining arc, whose carrier `Schoenflies.IsJoinFamily` makes a simple polygonal arc from
the hub, enters as a chain of ears between consecutive vertices along the arc, ordered by the
arc's parametrization. The grid's own interior is *not* the core's responsibility — the
vertices it must contain lie on the grid only where the skeleton side crosses it — which is
exactly the part `Schoenflies.hasGridUnionTwoConnected_of` absorbs. -/
def HasGridAnchoredCores (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃b : Plane⦄, b ∈ inside C →
      ∃ (xsegs : List Piece) (xtra : List Plane),
        (∀ Q ∈ xsegs, Q.Nondeg) ∧ cover xsegs ⊆ inside C ∧
        (∃ a₁ a₂ : Plane, a₁ ≠ a₂ ∧ a₁ ∈ xtra ∧ a₂ ∈ xtra ∧
          a₁ ∈ cover xsegs ∧ a₂ ∈ cover xsegs ∧
          a₁ ∈ cover (localGridEdges b (windowRadius C ε b)
            (localGridCount (windowRadius C ε b) ε)) ∧
          a₂ ∈ cover (localGridEdges b (windowRadius C ε b)
            (localGridCount (windowRadius C ε b) ε))) ∧
        ∀ (reps : List Plane) (Jarc : Plane → List Piece),
          (∀ r ∈ reps, r ∈ cover ((skeletonSegs P.src ++ xsegs) ++
            localGridEdges b (windowRadius C ε b) (localGridCount (windowRadius C ε b) ε))
              \ C) →
          IsJoinFamily C
            (gridHub b (windowRadius C ε b) (localGridCount (windowRadius C ε b) ε))
            (gridHubEdge b (windowRadius C ε b) (localGridCount (windowRadius C ε b) ε))
            reps Jarc →
          ∃ K : Graph Plane (γ ⊕ Piece),
            K ≤ gridExtGraph P.src (skeletonSegs P.src ++ xsegs) reps Jarc b
              (windowRadius C ε b) ε (xtra ++ stageVerts P.src) ∧
            K.IsTwoConnected ∧
            ∀ x ∈ V(gridExtGraph P.src (skeletonSegs P.src ++ xsegs) reps Jarc b
              (windowRadius C ε b) ε (xtra ++ stageVerts P.src)),
              x ∈ P.src.pos '' V(P.str.skel) ∨
                x ∈ cover ((skeletonSegs P.src ++ xsegs) ++ reps.flatMap Jarc) → x ∈ V(K)

/-- **The reduction: an anchored skeleton core makes the whole union 2-connected** —
`lem:union-two-connected` at the stage. The grid part of the overlay is 2-connected on its own
(`Schoenflies.gridPartGraph_isTwoConnected`), the core and the grid part share the two
anchors, `Graph.IsTwoConnected.union` glues them, and the union of the two spans every vertex
of `Schoenflies.gridExtGraph`: a drawn 0-cell and a vertex on the skeleton side lie in the
core, a vertex on the grid lies in the grid part. -/
theorem hasGridUnionTwoConnected_of {C : Set Plane} (hsep : IsSeparating C)
    (hcore : HasGridAnchoredCores S₀ C) : HasGridUnionTwoConnected S₀ C := by
  intro P hsrc ε hε b hb
  set s := windowRadius C ε b with hs_def
  set k := localGridCount s ε with hk_def
  have hC : IsCompact C := hsep.isJordanCurve.isCompact
  have hCne : C.Nonempty := hsep.isJordanCurve.nonempty
  have hbC : b ∉ C := fun h => inside_subset_compl hb h
  have hs : 0 < s := windowRadius_pos hC hCne hbC
  have hk1 : 1 ≤ k := one_le_localGridCount s ε
  obtain ⟨xsegs, xtra, hxnd, hxin, ⟨a₁, a₂, ha12, ha₁x, ha₂x, ha₁s, ha₂s, ha₁g, ha₂g⟩, hK⟩ :=
    hcore P hsrc hε hb
  refine ⟨xsegs, xtra, hxnd, hxin, ?_⟩
  intro reps Jarc hrmem hJF
  obtain ⟨K, hKle, hK2, hKspan⟩ := hK reps Jarc hrmem hJF
  set gsegs := skeletonSegs P.src ++ xsegs with hgsegs_def
  set extra := xtra ++ stageVerts P.src with hextra_def
  -- nondegeneracy of every piece in play
  have hg1 : ∀ Q ∈ gsegs, Q.Nondeg := by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    exacts [skeletonSegs_nondeg Q h, hxnd Q h]
  have hE₀nd : (gridHubEdge b s k).Nondeg :=
    localGridEdges_nondeg hs hk1 _ (gridHubEdge_mem hk1)
  have hj1 : ∀ Q ∈ reps.flatMap Jarc, Q.Nondeg := by
    intro Q hQ
    obtain ⟨r, hr, hQr⟩ := List.mem_flatMap.1 hQ
    rcases hJF r hr with ⟨-, hJr⟩ | ⟨-, vs, hvs, -, -, -, -, hJr⟩
    · rw [hJr, List.mem_singleton] at hQr
      exact hQr ▸ hE₀nd
    · rw [hJr] at hQr
      exact segsOf_nondeg _ Q hQr
  have hndall : ∀ Q ∈ gridAttachPieces gsegs reps Jarc b s ε, Q.Nondeg :=
    gridAttachPieces_nondeg hs hg1 hj1
  -- the grid part, renamed into the union
  set Ggrid := (gridPartGraph gsegs reps Jarc b s ε extra).renameEdges Sum.inr
    Sum.inr_injective.injOn with hGgrid_def
  have hGgrid2 : Ggrid.IsTwoConnected :=
    (gridPartGraph_isTwoConnected hs).renameEdges _
  have hGgridle : Ggrid ≤ gridExtGraph P.src gsegs reps Jarc b s ε extra :=
    (Graph.renameEdges_mono gridPartGraph_le _ _).trans
      (Graph.renameEdges_inr_le_sumUnion _ _)
  -- the auxiliary segments lie on the pieces
  have hxsub : cover xsegs ⊆ cover (gridAttachPieces gsegs reps Jarc b s ε) := by
    rw [cover_gridAttachPieces]
    intro z hz
    exact Or.inl (Or.inl (by rw [hgsegs_def, cover_append]; exact Or.inr hz))
  -- a cut point on the auxiliary segments is a vertex of the union
  have haVH : ∀ a, a ∈ xtra → a ∈ cover xsegs →
      a ∈ V(gridExtGraph P.src gsegs reps Jarc b s ε extra) := by
    intro a hax has
    have : a ∈ V(gridAttachGraph gsegs reps Jarc b s ε extra) :=
      mem_vertexSet_attachGraph_of_mem_extra hndall
        (List.mem_append_left _ hax) (hxsub has)
    exact Or.inr this
  -- the two anchors lie in the core
  have hanchK : ∀ a, a ∈ xtra → a ∈ cover xsegs → a ∈ V(K) := by
    intro a hax has
    refine hKspan a (haVH a hax has) (Or.inr ?_)
    rw [cover_append]
    exact Or.inl (by rw [hgsegs_def, cover_append]; exact Or.inr has)
  -- and in the grid part
  have hanchG : ∀ a, a ∈ xtra → a ∈ cover (localGridEdges b s k) → a ∈ V(Ggrid) := by
    intro a hax hag
    exact mem_gridPartGraph_of_mem_cover hs
      (mem_attachPoints_of_mem (List.mem_append_left _ hax)) hag
  -- glue at the anchors
  have hcompat := Graph.Compatible.of_le_le hKle hGgridle
  have hKfull : (K.union Ggrid).IsTwoConnected :=
    hK2.union hcompat hGgrid2 ha12 (hanchK a₁ ha₁x ha₁s) (hanchG a₁ ha₁x ha₁g)
      (hanchK a₂ ha₂x ha₂s) (hanchG a₂ ha₂x ha₂g)
  -- the union of the core and the grid part spans
  refine hKfull.of_le_of_vertexSet_subset (Graph.union_le hKle hGgridle) ?_
  intro x hx
  rw [Graph.vertexSet_union]
  rcases hx with hx | hx
  · -- a vertex of the outer part is a drawn 0-cell, hence in the core
    refine Or.inl (hKspan x (Or.inl hx) (Or.inl ?_))
    rw [Graph.renameEdges_vertexSet, Graph.vertexSet_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, P.str.outerGraph_le.vertexSet_mono hv, rfl⟩
  · -- an overlay vertex lies on the pieces: skeleton side into the core, grid side
    -- into the grid part
    have hxcov : x ∈ cover (gridAttachPieces gsegs reps Jarc b s ε) :=
      vertexSet_gridAttachGraph_subset_cover hx
    rw [cover_gridAttachPieces] at hxcov
    rcases hxcov with hx' | hx'
    · refine Or.inl (hKspan x (Or.inr hx) (Or.inr ?_))
      rw [cover_append, cover_flatMap']
      exact hx'
    · exact Or.inr (vertexSet_inter_grid_subset hs hx hx')

end Assemble

end Schoenflies
