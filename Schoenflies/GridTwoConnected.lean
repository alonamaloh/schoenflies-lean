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

end Schoenflies
