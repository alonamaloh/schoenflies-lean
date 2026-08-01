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

/-! ## Subdividing an append

The blueprint's `Γ ∪ K` is, at the level of segment lists, a list append, and
`pieceListGraph_union` turns the graph union into that append. Subdivision has to commute with
it, which it does because a subdivision is a `flatMap`. -/

theorem splitAllAt_append (q : Plane) (l l' : List Piece) :
    splitAllAt q (l ++ l') = splitAllAt q l ++ splitAllAt q l' := by
  simp [splitAllAt, List.flatMap_append]

theorem subdivide_append (points : List Plane) : ∀ l l' : List Piece,
    subdivide (l ++ l') points = subdivide l points ++ subdivide l' points := by
  induction points with
  | nil => intro l l'; rfl
  | cons q qs ih => intro l l'; rw [subdivide_cons, splitAllAt_append, ih, subdivide_cons,
      subdivide_cons]

theorem endSet_subset_append_left {l l' : List Piece} : endSet l ⊆ endSet (l ++ l') := by
  rintro v ⟨P, hP, hv⟩
  exact ⟨P, List.mem_append_left _ hP, hv⟩

/-! ### A cut point on the drawing is a vertex

`Schoenflies/SimpleArc.lean` proves this for `overlayGraph`; the union argument runs on the raw
subdivision, where the same two facts — `subdivide_cover` and `subdivide_avoids` — give it. -/

/-- **A cut point lying on the pieces is an end of some subpiece.** -/
theorem mem_endSet_subdivide_of_mem_cover {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) {x : Plane} (hxp : x ∈ points) (hx : x ∈ cover pieces) :
    x ∈ endSet (subdivide pieces points) := by
  rw [← subdivide_cover pieces points] at hx
  obtain ⟨P, hP, hxP⟩ := mem_cover_iff.1 hx
  refine ⟨P, hP, ?_⟩
  by_contra hcon
  push Not at hcon
  exact subdivide_avoids points hnd x hxp P hP
    (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hxP)

/-! ## The union: the case "at least two common vertices"

`lem:union-two-connected`, in the form `prop:local-grid-attachment` uses it. The two families of
segments are overlaid together — one list append, one list of cut points — and the two distinct
common points are supplied as points that lie on *both* families and are cut. -/

/-- **`prop:local-grid-attachment`, the main case.** Two families of segments, each of which is
2-connected after subdivision, overlay to a 2-connected graph as soon as two distinct cut points
lie on both families.

This is `lem:union-two-connected` composed with `lem:subdivision-ear-preserve` and with the
orient-and-dedup bridge: the conclusion is about `overlayGraph`, which is what the plane layer
(drawing, faces, outer face) is stated for. -/
theorem overlayGraph_append_isTwoConnected {l l' : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ l, P.Nondeg) (hnd' : ∀ P ∈ l', P.Nondeg)
    (hl : (pieceListGraph (subdivide l points)).IsTwoConnected)
    (hl' : (pieceListGraph (subdivide l' points)).IsTwoConnected)
    {a b : Plane} (hab : a ≠ b) (ha : a ∈ points) (hb : b ∈ points)
    (hal : a ∈ cover l) (hbl : b ∈ cover l) (hal' : a ∈ cover l') (hbl' : b ∈ cover l') :
    (overlayGraph (l ++ l') points).IsTwoConnected := by
  refine overlayGraph_isTwoConnected ?_
  rw [subdivide_append, ← pieceListGraph_union]
  exact hl.union (pieceListGraph_compatible _ _) hl' hab
    (mem_endSet_subdivide_of_mem_cover hnd ha hal)
    (mem_endSet_subdivide_of_mem_cover hnd' ha hal')
    (mem_endSet_subdivide_of_mem_cover hnd hb hbl)
    (mem_endSet_subdivide_of_mem_cover hnd' hb hbl')

/-! ## The crosscut of a face

The two degenerate cases of `prop:local-grid-attachment` — no common vertex, and exactly one —
both build an auxiliary crosscut `E` of a face `F` of `Γ`: *"the component of `ℓ ∩ F` containing
the relative interior of `J` is a bounded open interval in `ℓ`; its closure `E` is a line segment
with two distinct endpoints on `∂F` and interior in `F`. Hence `E` is an ear for `Γ`."*

`Schoenflies.Plane.exists_openSegment_eq_connectedComponentIn` is exactly that component, with
its two endpoints already placed on `frontier F`. What is added here is the clause the blueprint
needs next — *"since `E` contains `J`"* — in the form that makes it usable: **every** connected
piece of `ℓ ∩ F` through the chosen point is swallowed by the crosscut, because a connected
subset of a set lies inside one component of it. -/

variable {F : Set Plane} {a b y : Plane}

/-- **The crosscut of a face along a line.** A face `F` (open, bounded) met by a line `ℓ` at `y`
supplies a segment `[q₀, q₁]` with distinct ends on `∂F`, open part inside `F`, containing `y` —
and containing every connected subset of `ℓ ∩ F` through `y`, which is how the blueprint's chosen
grid edge `J` ends up inside the crosscut. -/
theorem exists_crosscut (hab : a ≠ b) (hFopen : IsOpen F) (hFbdd : Bornology.IsBounded F)
    (hy : y ∈ Plane.line a b ∩ F) :
    ∃ q₀ q₁ : Plane, q₀ ≠ q₁ ∧ q₀ ∈ frontier F ∧ q₁ ∈ frontier F ∧
      openSegment ℝ q₀ q₁ ⊆ F ∧ y ∈ openSegment ℝ q₀ q₁ ∧
      ∀ S : Set Plane, IsPreconnected S → S ⊆ Plane.line a b ∩ F → y ∈ S →
        S ⊆ openSegment ℝ q₀ q₁ := by
  obtain ⟨q₀, q₁, hne, -, -, hcomp, -, h0, h1⟩ :=
    Plane.exists_openSegment_eq_connectedComponentIn hab hFopen hFbdd hy
  refine ⟨q₀, q₁, hne, h0, h1, ?_, ?_, ?_⟩
  · rw [← hcomp]
    exact fun z hz => (connectedComponentIn_subset _ _ hz).2
  · rw [← hcomp]
    exact mem_connectedComponentIn hy
  · intro S hS hSsub hyS
    rw [← hcomp]
    exact hS.subset_connectedComponentIn hyS hSsub

/-- The frontier of a face lies on the graph — which is what makes the crosscut's two endpoints
points of `Γ`, and hence (after subdivision) vertices of it. -/
theorem frontier_face_subset_pointSet {β : Type*} {G : Graph Plane β} [G.Finite]
    {drawing : β → ℝ → Plane} (h : Graph.IsDrawing G drawing) (base : Plane) :
    frontier (Graph.face G drawing base) ⊆ Graph.pointSet G drawing :=
  Plane.frontier_connectedComponentIn_compl_subset h.isClosed_pointSet base

/-! ## Attaching the crosscut as an ear

`lem:subdivision-ear-preserve` (b) with the ear a single straight edge: once the crosscut's two
endpoints are vertices — which they are, being cut points of the overlay lying on `Γ` — the
segment joining them is a path graph of length one. -/

/-- A single nondegenerate segment is a path graph between its two ends. -/
theorem isPathGraph_single {q₀ q₁ : Plane} (hne : q₀ ≠ q₁) :
    (pieceListGraph [(q₀, q₁)]).IsPathGraph q₀ [(q₀, q₁)] q₁ where
  isPath := .single (pieceListGraph_isLink_self (by simp)) hne
  edgeSet_eq := rfl
  vertexSet_eq := by
    have hmem : ((q₀, q₁) : Piece) ∈ [((q₀, q₁) : Piece)] := List.mem_singleton_self _
    ext x
    constructor
    · rintro ⟨P, hP, hx⟩
      rw [List.mem_singleton] at hP
      subst hP
      simp only [Graph.walkVertices, mem_insert_iff, Graph.coveredVertices, mem_setOf_eq]
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(q₀, q₁), hmem, pieceListGraph_inc hmem (Or.inr h)⟩
    · intro hx
      simp only [Graph.walkVertices, mem_insert_iff, Graph.coveredVertices, mem_setOf_eq] at hx
      rcases hx with h | ⟨e, he, hinc⟩
      · exact ⟨(q₀, q₁), hmem, Or.inl h⟩
      · rw [List.mem_singleton] at he
        subst he
        obtain ⟨-, hx'⟩ := pieceListGraph_inc_iff.1 hinc
        exact ⟨(q₀, q₁), hmem, hx'⟩

/-- **A crosscut is an ear.** Adding to a 2-connected family of segments one further segment
whose two ends are already ends of the family keeps it 2-connected. -/
theorem pieceListGraph_append_crosscut {l : List Piece} {q₀ q₁ : Plane}
    (hl : (pieceListGraph l).IsTwoConnected) (hne : q₀ ≠ q₁)
    (h0 : q₀ ∈ endSet l) (h1 : q₁ ∈ endSet l) :
    (pieceListGraph (l ++ [(q₀, q₁)])).IsTwoConnected := by
  rw [← pieceListGraph_union]
  exact hl.ear (pieceListGraph_compatible _ _) (isPathGraph_single hne) hne h0 h1

/-! ## The component-joining loop

*"If `|L| ∖ C` has more than one component, choose points in two of its components and join them
by a simple polygonal arc in `D` … Each round therefore strictly decreases the number of
components. Since there are only finitely many components, finitely many repetitions produce a
2-connected graph `H_n` for which `|H_n| ∖ C` is connected."*

Counting components and decrementing is one way to run that loop; picking one representative per
component and joining each to a fixed one is another, and it is the one that survives
formalisation, because it replaces "strictly decreases" by a single induction-free statement. The
finiteness the blueprint spends is what supplies the finite list `reps`. -/

/-- **The joining loop.** If every point of `A` is joined inside `A` to one of finitely many
representatives, and each representative is joined to a fixed `r₀ ∈ A` by a connected set `T r`,
then `A` together with all the `T r` is connected.

The `T r` are the blueprint's joining arcs; nothing is assumed about how they meet `A` beyond
containing their two ends, so an arc that crosses `A` many times is no harder than one that does
not. -/
theorem isConnected_union_joins {A : Set Plane} {r₀ : Plane} (hr₀ : r₀ ∈ A)
    {reps : List Plane} {T : Plane → Set Plane}
    (hTconn : ∀ r ∈ reps, IsPreconnected (T r))
    (hThub : ∀ r ∈ reps, r₀ ∈ T r) (hTrep : ∀ r ∈ reps, r ∈ T r)
    (hcover : ∀ z ∈ A, ∃ r ∈ reps, ∃ S : Set Plane,
      S ⊆ A ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S) :
    IsConnected (A ∪ ⋃ r ∈ reps, T r) := by
  have hmem : r₀ ∈ A ∪ ⋃ r ∈ reps, T r := Or.inl hr₀
  refine ⟨⟨r₀, hmem⟩, isPreconnected_of_forall r₀ ?_⟩
  rintro z (hz | hz)
  · -- inside `A`: walk to a representative, then along its joining set to the hub
    obtain ⟨r, hr, S, hSA, hSconn, hzS, hrS⟩ := hcover z hz
    refine ⟨S ∪ T r, ?_, Or.inr (hThub r hr), Or.inl hzS,
      hSconn.union' ⟨r, hrS, hTrep r hr⟩ (hTconn r hr)⟩
    exact union_subset (hSA.trans subset_union_left)
      (fun w hw => Or.inr (mem_biUnion hr hw))
  · -- on a joining set: it already contains the hub
    simp only [mem_iUnion, exists_prop] at hz
    obtain ⟨r, hr, hzT⟩ := hz
    exact ⟨T r, fun w hw => Or.inr (mem_biUnion hr hw), hThub r hr, hzT, hTconn r hr⟩

end Schoenflies
