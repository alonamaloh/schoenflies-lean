/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.LocalGrid
import Schoenflies.Graph.Ear
import Schoenflies.Line
import Schoenflies.PolygonalCarrier

/-!
# Attaching a local source grid — `prop:local-grid-attachment`

`Schoenflies/LocalGrid.lean` built the grid `K` itself and its quantitative clause 3. This
module is the *rest* of the proposition: the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases of the union argument, and the component-joining loop.

## Blueprint

* `lem:polygonal-overlay` / `rem:polygonal-overlay-convention` — `Schoenflies.attachPieces`,
  `Schoenflies.attachGraph` and its drawing/point-set lemmas.
* `lem:union-two-connected` — `Schoenflies.attachGraph_isTwoConnected_of_two_common`
  (case "at least two common vertices"), through `Graph.IsTwoConnected.union`.
* `lem:subdivision-ear-preserve` — `Schoenflies.overlayGraph_isTwoConnected`, which is the
  step the blueprint spends without comment ("By `lem:subdivision-ear-preserve`, subdivision
  preserves 2-connectivity") and which needed a missing bridge; see below.
* the crosscut `E` of the two degenerate cases — `Schoenflies.crosscutEnd₀`,
  `Schoenflies.crosscutEnd₁`, `Schoenflies.crosscut_spec`, built on
  `Schoenflies.Plane.exists_openSegment_eq_connectedComponentIn`.
* the component-joining loop — `Schoenflies.isPreconnected_union_joins`, and the graph-level
  `Schoenflies.attachJoin_isTwoConnected`.

## The bridge that was missing: 2-connectivity of an overlay graph

`Schoenflies/SquareMeshFixed.lean` proves `pieceListGraph_subdivide_isTwoConnected`: the graph
of a **raw** subdivided piece list is 2-connected. `Schoenflies/OverlayGraph.lean` builds the
overlay as `overlayGraph pieces points`, whose edges are the subdivided pieces *oriented and
deduplicated*. Nothing on `main` connects the two, so no overlay graph anywhere in the
development was known to be 2-connected — including `Schoenflies.squareMesh`, whose clause 5
is the subject of the first half of `LocalGrid.lean`.

Orienting renames an edge `(a, b)` to `(b, a)` and deduplication drops repeats, so the two
graphs are not equal and are not isomorphic by an identity on edges. But 2-connectivity does
not see edge *names*: it is a statement about which pairs of vertices are joined. That is what
`Graph.SameLinks` isolates — same vertex set, same joined pairs — and it transfers `Connected`,
`deleteVerts`, and hence `IsTwoConnected` in both directions.

## What is a hypothesis here, and why

Two things the blueprint's proof uses are stated as hypotheses rather than proved, and both are
statements about `Γ`, not about the grid:

* `hΓsub` — that the skeleton of `Γ`, subdivided at the crossing points, is still 2-connected.
  For the polygonal part this is `pieceListGraph_subdivide_isTwoConnected`; for the arcs of `C`
  it is `Graph.IsTwoConnected.replace_edge_by_path` iterated. It is not provable *here* because
  this module never sees `Γ`'s drawing — the whole union argument is combinatorial.
* `hears` in `attachJoin_isTwoConnected` — that a joining arc decomposes into ears of the old
  graph. The blueprint asserts it in one sentence ("each component of the arc outside the old
  graph is an open subarc whose closure has two distinct endpoints on the old graph"); turning
  that into a list of `Graph.IsPathGraph`s is a separate piece of work.

Neither is a restatement of a goal of this module, and both are true.
-/

open Metric Set
open scoped Graph

/-! ## Graphs that join the same pairs

2-connectivity is invariant under renaming edges, merging parallel edges, and dropping an edge
that duplicates another — none of which a `Graph` isomorphism captures, since the edge type is
fixed. `SameLinks` is the equivalence that does capture them, and it is exactly what the
overlay's orient-and-dedup step needs.

This is general graph theory and belongs in `Schoenflies/Graph/Walk.lean` beside `IsWalk.mono`;
it is here only because it was needed here first. -/

namespace Graph

variable {α β : Type*} {G H : Graph α β} {u v x y : α} {e : β} {X : Set α}

/-- Two graphs with the same vertices which join the same pairs of vertices. Edge names,
multiplicities and parallel edges are all invisible to it. -/
def SameLinks (G H : Graph α β) : Prop :=
  V(G) = V(H) ∧ ∀ x y, (∃ e, G.IsLink e x y) ↔ (∃ e, H.IsLink e x y)

namespace SameLinks

@[refl] theorem refl (G : Graph α β) : SameLinks G G := ⟨rfl, fun _ _ => Iff.rfl⟩

theorem symm (h : SameLinks G H) : SameLinks H G := ⟨h.1.symm, fun x y => (h.2 x y).symm⟩

theorem vertexSet (h : SameLinks G H) : V(G) = V(H) := h.1

/-- Deleting the same vertices from both sides preserves the relation: the deleted graph's
links are the old links between surviving vertices. -/
theorem deleteVerts (h : SameLinks G H) (X : Set α) :
    SameLinks (G.deleteVerts X) (H.deleteVerts X) := by
  refine ⟨by rw [vertexSet_deleteVerts, vertexSet_deleteVerts, h.1], fun x y => ?_⟩
  constructor
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink _ _] at he
    obtain ⟨f, hf⟩ := (h.2 x y).1 ⟨e, he.1⟩
    exact ⟨f, (deleteVerts_isLink _ _).2 ⟨hf, he.2.1, he.2.2⟩⟩
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink _ _] at he
    obtain ⟨f, hf⟩ := (h.2 x y).2 ⟨e, he.1⟩
    exact ⟨f, (deleteVerts_isLink _ _).2 ⟨hf, he.2.1, he.2.2⟩⟩

end SameLinks

/-- Reachability only sees which pairs are joined. -/
theorem Reaches.sameLinks (h : SameLinks G H) (hr : G.Reaches u v) : H.Reaches u v := by
  obtain ⟨W, hW⟩ := hr
  induction hW with
  | nil hz => exact Reaches.refl (h.1 ▸ hz)
  | @cons p w q g R hl _ ih =>
    obtain ⟨f, hf⟩ := (h.2 p w).1 ⟨g, hl⟩
    exact (Reaches.of_isLink hf).trans ih

theorem Connected.sameLinks (h : SameLinks G H) (hG : G.Connected) : H.Connected := by
  obtain ⟨z, hz⟩ := hG.nonempty
  exact Connected.of_hub (h.1 ▸ hz) fun w hw =>
    (hG.reaches hz (h.1 ▸ hw : w ∈ V(G))).sameLinks h

theorem HasThreeVertices.sameLinks (h : SameLinks G H) (hG : G.HasThreeVertices) :
    H.HasThreeVertices := hG.mono (le_of_eq h.1)

/-- **2-connectivity does not see edge names.** -/
theorem IsTwoConnected.sameLinks (h : SameLinks G H) (hG : G.IsTwoConnected) :
    H.IsTwoConnected where
  hasThreeVertices := hG.hasThreeVertices.sameLinks h
  connected := hG.connected.sameLinks h
  deleteVerts_connected := fun z _ =>
    (hG.deleteVerts_connected' z).sameLinks (h.deleteVerts {z})

end Graph

namespace Schoenflies

/-! ## The overlay graph is a piece-list graph

`overlayGraph pieces points` and `pieceListGraph (overlayPieces pieces points)` are the same
structure with the same fields, so the equation is `rfl`. Saying it once lets every lemma of
`Schoenflies/SquareMeshConnected.lean` about `pieceListGraph` — in particular
`pieceListGraph_union`, which turns "glue on another family of segments" into a list append —
apply to overlays. -/

/-- The overlay graph is the piece-list graph of its own edges. -/
theorem overlayGraph_eq_pieceListGraph (pieces : List Piece) (points : List Plane) :
    overlayGraph pieces points = pieceListGraph (overlayPieces pieces points) := rfl

/-! ### Orienting and deduplicating do not change which pairs are joined -/

/-- The two ends of a piece, as an unordered pair, are what a link records. -/
theorem orientPiece_link_iff (P : Piece) (x y : Plane) :
    ((x = (orientPiece P).1 ∧ y = (orientPiece P).2) ∨
        (x = (orientPiece P).2 ∧ y = (orientPiece P).1)) ↔
      ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := by
  by_cases h : Precedes P.1 P.2
  · rw [orientPiece_of_precedes h]
  · rw [orientPiece_of_not_precedes h]; exact or_comm

/-- **The subdivided list and the overlay's edge list join the same pairs.** This is the bridge
between `pieceListGraph_subdivide_isTwoConnected`, which knows about the raw subdivision, and
`overlayGraph`, which is what every plane consumer holds. -/
theorem sameLinks_overlayGraph (pieces : List Piece) (points : List Plane) :
    Graph.SameLinks (pieceListGraph (subdivide pieces points)) (overlayGraph pieces points) := by
  constructor
  · ext v
    simp only [pieceListGraph_vertexSet, overlayGraph_vertexSet, endSet, mem_setOf_eq]
    constructor
    · rintro ⟨P, hP, hv⟩
      exact ⟨orientPiece P, mem_overlayPieces.2 ⟨P, hP, rfl⟩, (orientPiece_ends P v).2 hv⟩
    · rintro ⟨P, hP, hv⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
      exact ⟨Q, hQ, (orientPiece_ends Q v).1 hv⟩
  · intro x y
    simp only [pieceListGraph_isLink, overlayGraph_isLink]
    constructor
    · rintro ⟨P, hP, hxy⟩
      exact ⟨orientPiece P, mem_overlayPieces.2 ⟨P, hP, rfl⟩,
        (orientPiece_link_iff P x y).2 hxy⟩
    · rintro ⟨P, hP, hxy⟩
      obtain ⟨Q, hQ, rfl⟩ := mem_overlayPieces.1 hP
      exact ⟨Q, hQ, (orientPiece_link_iff Q x y).1 hxy⟩

/-- **`lem:subdivision-ear-preserve` for an overlay.** If the raw subdivision of the piece list
has a 2-connected graph, so does the overlay graph built from it.

Without this the development had no 2-connected overlay at all: every 2-connectivity result
about segment families is stated for `pieceListGraph`, and every plane result — drawing, faces,
outer face — is stated for `overlayGraph`. -/
theorem overlayGraph_isTwoConnected {pieces : List Piece} {points : List Plane}
    (h : (pieceListGraph (subdivide pieces points)).IsTwoConnected) :
    (overlayGraph pieces points).IsTwoConnected :=
  h.sameLinks (sameLinks_overlayGraph pieces points)

/-- The same, from the hypotheses `pieceListGraph_subdivide_isTwoConnected` actually needs. -/
theorem overlayGraph_isTwoConnected_of_cleanCut {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hclean : ∀ q ∈ points, CleanCut pieces q)
    (h : (pieceListGraph pieces).IsTwoConnected) :
    (overlayGraph pieces points).IsTwoConnected :=
  overlayGraph_isTwoConnected (pieceListGraph_subdivide_isTwoConnected points pieces hnd hclean h)

end Schoenflies
