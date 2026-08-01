/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.PrePolygonSep
import Schoenflies.Graph.K33Closed

/-!
# `lem:k33` and `cor:k33-subdivision`, with nothing assumed

`Schoenflies/Graph/K33Planar.lean` proves the nonplanarity of `K(3,3)` from
`Graph.IsHexRealization`; `Schoenflies/Graph/K33Closed.lean` reduces that to `Graph.Bendable` —
"every polygonal drawing can be redrawn so that no two edges leave a vertex along one line". This
module removes the hypothesis altogether. Nothing is bent.

## Where the hypothesis came from, and why it is not needed

`Schoenflies.ClosedPolygon` carries a `corner` field, and
`Schoenflies.ClosedPolygon.isCornerAt_vertex` shows the field is not slack: *every* vertex of
*every* `ClosedPolygon` presentation is a point at which the curve turns. So a crosscut interface
phrased with `ClosedPolygon`s — `Schoenflies.IsPolygonalCrosscut`, and hence
`Schoenflies.alternating_crosscuts` — can only cut the curve at corners, and a drawn `K(3,3)` puts
its branch points wherever it likes.

The blueprint's `cor:alternating-crosscuts` has no such condition: it is stated for a set-level
simple closed polygonal curve and simple polygonal arcs with endpoints anywhere on it. The fix is
to state the crosscut for `Schoenflies.PrePolygon` — `ClosedPolygon` without `corner` — whose
vertices may sit anywhere on the curve. `Schoenflies/PrePolygonSep.lean` already supplies the two
things Theorem 2.8 asks of such a curve: that its carrier separates the plane, and the two values
of the crossing parity. Everything else in the chain is about *edge lists*, and edge lists do not
know about corners.

## The one construction this needed

Three closed polygons enter Theorem 2.8 — the curve `C` and the two curves `Jᵢ` the crosscut
forms with the two arcs — and their **edge lists** must agree: `SameEdges Jᵢ.pieces (Aᵢ ++ K)`.
`Schoenflies/Graph/K33Closed.lean` found three realizations independently and matched them with
`Schoenflies.ClosedPolygon.arcPieces_eq`, whose proof is exactly where `corner` was consumed. For
`PrePolygon` no such matching theorem can exist: two presentations of one arc need not agree.

So the two spliced curves are not found — they are *built*. `Schoenflies.PrePolygon.exists_splice`
lays two chains with common ends end to end and returns a `PrePolygon` whose edge list is their
concatenation, so the three lists agree by construction and nothing has to be matched. The chains
themselves come from `Schoenflies.exists_prePolygon_arcs_oriented`, which needs
`Schoenflies.PrePolygon.insertLast`: a point of the curve that is not yet a vertex is interior to
an edge, and an edge may be cut. That is the inverse of
`Schoenflies.PrePolygon.deleteLast`, and it is what makes "a `PrePolygon` may be presented with
vertices at any prescribed finite set of points of its carrier" a theorem
(`Schoenflies.PrePolygon.exists_prePolygon_vertices`).

## Blueprint

* `Schoenflies.PrePolygon.chain`, `…isArcBetween_chain`, `…arcPieces`, `…arc`, `…arc_union`,
  `…arc_inter`, `…isArcBetween_arc`, `…parity_splitting`, `…parity_ne_iff_mem_farRegion` — §2 for
  a polygon presented with redundant vertices: the arcs of a splitting, their edge lists,
  Lemma 2.7, and Theorem 2.3 read as a separation criterion. Each is the `ClosedPolygon` proof of
  `Schoenflies/PolygonBridge.lean`, `Schoenflies/ParitySplitting.lean` and
  `Schoenflies/PolygonalCrosscut.lean` with the structure changed and `corner` never used.
* `Schoenflies.segment_halves_inter`, `Schoenflies.right_notMem_left_half`,
  `Schoenflies.left_notMem_right_half` — §1: cutting a segment at an interior point, in order.
  General-purpose; they belong beside `Schoenflies.segment_split` in `Schoenflies/SegmentCut.lean`.
* `Schoenflies.PrePolygon.insertLast`, `…carrier_insertLast`,
  `Schoenflies.PrePolygon.exists_prePolygon_insert`, `…exists_prePolygon_vertices` — the inverse
  of the blueprint's "delete redundant vertices" (Lemma 1.8): *insert* one, anywhere on the curve.
* `Schoenflies.PrePolygon.exists_splice` — two arcs with common ends, laid end to end.
* `Schoenflies.PrePolygon.reverse`, `…reverse_arc`, `…sameEdges_reverse_arcPieces` — the polygon
  traversed the other way, which is what pins the direction of a prescribed arc.
* `Schoenflies.exists_prePolygon_points`, `…exists_prePolygon_split`, `…exists_prePolygon_arcs`,
  `…exists_prePolygon_arcs_oriented` — §1, the realization theorem **with the cut points
  anywhere on the curve**. Compare `Schoenflies.exists_closedPolygon_arcs`, which requires them
  to be corners.
* `Schoenflies.IsPrePolygonalCrosscut` and its API up to
  `…alternating_inter_nonempty_of_same_side` — `thm:polygonal-crosscut` and
  `cor:alternating-crosscuts` in the blueprint's own generality: the split points need not be
  corners.
* `Graph.IsPreHexCrosscut`, `Graph.IsK33Config.isPreHexCrosscut` — the six-cycle of a polygonally
  drawn `K(3,3)`, cut at the two ends of one remaining edge, as such a crosscut. **This is what
  `Graph.IsHexRealization` was assuming, and it is proved here.**
* `Graph.IsK33Config.false_of_isPreHexCrosscut`, `…false_of_polygonal`,
  `Graph.IsK33Config.not_exists_isDrawing` — `lem:k33`.
* `Graph.IsArcK33.elim`, `Graph.IsK33Subdivision.elim` — `cor:k33-subdivision`.
* `Graph.k33Graph_not_exists_isDrawing` — `lem:k33` for the concrete graph.

## A note on names, for the integrator

The unconditional statements could not take the names of the conditional ones, which are still
in the import closure:

| conditional, now dead                             | unconditional, here                        |
|---------------------------------------------------|--------------------------------------------|
| `Graph.IsK33Config.not_isDrawing` (K33Planar)      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsK33Config.not_isDrawing_of_bendable`      | `Graph.IsK33Config.not_exists_isDrawing`   |
| `Graph.IsArcK33.false_of_realization`/`_bendable`  | `Graph.IsArcK33.elim`                      |
| `Graph.IsK33Subdivision.false_of_realization`/`…`  | `Graph.IsK33Subdivision.elim`              |
| `Graph.k33Graph_not_isDrawing`                     | `Graph.k33Graph_not_exists_isDrawing`      |

With this module in place `Graph.IsHexRealization`, `Graph.IsHexCrosscut`, `Graph.IsHexGeneric`
and `Graph.Bendable` have no consumers left.
-/

open Bornology Metric Set unitInterval
open scoped Graph

namespace Schoenflies

open Plane

namespace PrePolygon

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-! ## Indices, edges and the elementary simplicity facts

Verbatim the `Schoenflies.ClosedPolygon` facts of `Schoenflies/PolygonBridge.lean` whose proofs
use only `vertex_inj` and `edges_meet`. -/

/-- Distinct indices below the modulus name distinct vertices. -/
theorem vertex_natCast_ne {j l : ℕ} (hj : j < m + 3) (hl : l < m + 3) (hjl : j ≠ l) :
    P.vertex (j : ZMod (m + 3)) ≠ P.vertex (l : ZMod (m + 3)) :=
  fun heq => hjl (ClosedPolygon.natCast_inj hj hl (P.vertex_inj heq))

/-- **An edge meets an earlier edge only at its own initial vertex.** -/
theorem edge_meet_earlier {j l : ℕ} (hjl : j < l) (hl : l + 1 < m + 3) {z : Plane}
    (hzj : z ∈ P.edge (j : ZMod (m + 3))) (hzl : z ∈ P.edge (l : ZMod (m + 3))) :
    z = P.vertex (l : ZMod (m + 3)) := by
  have hjn : j < m + 3 := by omega
  have hln : l < m + 3 := by omega
  have hne : (l : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
    fun heq => (by omega : l ≠ j) (ClosedPolygon.natCast_inj hln hjn heq)
  have hmem := P.edges_meet _ _ hne (Set.mem_inter hzl hzj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hmem
  exfalso
  have hmem2 := P.edges_meet _ _ (Ne.symm hne) (Set.mem_inter hzj hzl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem2
  rw [← ClosedPolygon.natCast_succ] at hmem
  rcases hmem2 with hmem2 | hmem2
  · have : l + 1 = j := ClosedPolygon.natCast_inj hl hjn (P.vertex_inj (hmem ▸ hmem2))
    omega
  · rw [← ClosedPolygon.natCast_succ] at hmem2
    have : l + 1 = j + 1 :=
      ClosedPolygon.natCast_inj hl (by omega) (P.vertex_inj (hmem ▸ hmem2))
    omega

/-! ## The chain of the first `k` edges, and that it is an arc -/

/-- The union of the edges leaving vertices `0, 1, …, k`. -/
def chain (P : PrePolygon m) : ℕ → Set Plane
  | 0 => P.edge 0
  | k + 1 => chain P k ∪ P.edge ((k + 1 : ℕ) : ZMod (m + 3))

theorem mem_chain_iff {z : Plane} : z ∈ P.chain k ↔ ∃ j ≤ k, z ∈ P.edge (j : ZMod (m + 3)) := by
  induction k with
  | zero =>
    constructor
    · intro hz
      exact ⟨0, le_rfl, by simpa [chain] using hz⟩
    · rintro ⟨j, hj, hzj⟩
      obtain rfl : j = 0 := Nat.le_zero.1 hj
      simpa [chain] using hzj
  | succ k ih =>
    simp only [chain, Set.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨j, hj, hzj⟩ := ih.1 hz
        exact ⟨j, le_trans hj (Nat.le_succ k), hzj⟩
      · exact ⟨k + 1, le_rfl, hz⟩
    · rintro ⟨j, hj, hzj⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inl (ih.2 ⟨j, Nat.lt_succ_iff.1 hlt, hzj⟩)
      · obtain rfl : j = k + 1 := le_antisymm hj hge
        exact Or.inr hzj

/-- **The partial chains are arcs.** One edge at a time, glued at the vertex they share. -/
theorem isArcBetween_chain (P : PrePolygon m) :
    ∀ k : ℕ, k + 1 < m + 3 →
      IsArcBetween (P.chain k) (P.vertex 0) (P.vertex ((k + 1 : ℕ) : ZMod (m + 3))) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [ClosedPolygon.natCast_succ]
    exact isArcBetween_segment (vertex_ne_succ 0)
  | succ k ih =>
    intro hk
    have hA := ih (by omega)
    have hB : IsArcBetween (P.edge ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 : ℕ) : ZMod (m + 3)))
        (P.vertex ((k + 1 + 1 : ℕ) : ZMod (m + 3))) := by
      rw [ClosedPolygon.natCast_succ (k + 1)]
      exact isArcBetween_segment (vertex_ne_succ _)
    have hmeet : ∀ z ∈ P.chain k, z ∈ P.edge ((k + 1 : ℕ) : ZMod (m + 3)) →
        z = P.vertex ((k + 1 : ℕ) : ZMod (m + 3)) := by
      intro z hz hze
      obtain ⟨j, hj, hzj⟩ := mem_chain_iff.1 hz
      exact edge_meet_earlier (by omega) (by omega) hzj hze
    exact hA.concatenate hB hmeet

/-! ## The edge list of an arc

`Schoenflies.ClosedPolygon.arcPieces` with the structure changed; every proof below uses only
`vertex_inj` and `edges_meet`, so it is the old proof verbatim. -/

/-- The edge list of the arc of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (P.vertex (a + t), P.vertex (a + t + 1))

/-- Forgetting the `corner` field does not change the edge list of an arc. -/
@[simp] theorem arcPieces_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arcPieces a k = C.arcPieces a k := rfl

@[simp] theorem arcPieces_zero (P : PrePolygon m) (a : ZMod (m + 3)) : P.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_add (P : PrePolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    P.arcPieces a (k + l) = P.arcPieces a k ++ P.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_full (P : PrePolygon m) : P.arcPieces 0 (m + 3) = P.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon. -/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ P.arcPieces a k) : Q ∈ P.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact P.mem_pieces _

theorem arcPieces_nondeg (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ P.arcPieces a k, Q.Nondeg :=
  fun _ hQ => P.pieces_nondeg _ (mem_pieces_of_mem_arcPieces hQ)

theorem arcPieces_hgt_ne (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **An arc is a chain from its first vertex to its last.** -/
theorem isChainFrom_arcPieces (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (P.arcPieces a k) (P.vertex a) (P.vertex (a + k)) := by
  intro f
  have hmap : ((P.arcPieces a k).map fun Q => f Q.1 + f Q.2)
      = (List.range k).map fun j : ℕ =>
          f (P.vertex (a + (j : ZMod (m + 3))))
            + f (P.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (P.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** -/
theorem arcPieces_full_perm (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.arcPieces a (m + 3)).Perm P.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : P.arcPieces a (m + 3)
      = P.arcPieces a (m + 3 - a.val) ++ P.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add P a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : P.pieces = P.arcPieces 0 a.val ++ P.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add P 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** -/
theorem arcPieces_split_perm (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)).Perm P.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm P a

theorem sameEdges_arcPieces_split (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges P.pieces (P.arcPieces a k ++ P.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm P a hk).symm

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (P.arcPieces a k) ∪ cover (P.arcPieces (a + k) (m + 3 - k)) = P.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm P a hk), cover_pieces]

theorem cover_arcPieces_subset (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (P.arcPieces a k) ⊆ P.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

/-- **A curve of the split occupies its arc together with the crosscut.** -/
theorem carrier_eq_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) :
    J.carrier = cover (P.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

/-- A point off `P` and off the crosscut is off `J`. -/
theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : PrePolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (P.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ P.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset P a k hx)
  · exact hxK hx

/-- **Parity splitting** (Lemma 2.7) for a polygon presented with redundant vertices. -/
theorem parity_splitting (P : PrePolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {L₁ L₂ K : List Piece} (h₁ : SameEdges L₁ (P.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (P.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u P.pieces q :=
  parity_split u (sameEdges_arcPieces_split P a hk) h₁ h₂ q

/-! ## The arcs as sets -/

/-- The arc of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (P.arcPieces a k)

@[simp] theorem arc_toPre (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    C.toPre.arc a k = C.arc a k := rfl

theorem arc_subset_carrier (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arc a k ⊆ P.carrier := cover_arcPieces_subset P a k

theorem arc_union (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    P.arc a k ∪ P.arc (a + k) (m + 3 - k) = P.carrier := cover_arcPieces_union P a hk

theorem mem_arc_iff {z : Plane} :
    z ∈ P.arc a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- The first vertex of a nonempty arc lies on it. -/
theorem vertex_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex a ∈ P.arc a k := by
  refine mem_arc_iff.2 ⟨0, hk, ?_⟩
  rw [Nat.cast_zero, add_zero, edge]
  exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arc lies on it. -/
theorem vertex_add_mem_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex (a + k) ∈ P.arc a k := by
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have h : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, h]
  refine mem_arc_iff.2 ⟨k - 1, by omega, ?_⟩
  rw [edge, hlast]
  exact right_mem_segment ℝ _ _

/-- **The two cut vertices lie on both arcs.** -/
theorem endpoints_subset_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc a k := by
  rintro w (rfl | rfl)
  · exact P.vertex_mem_arc a hk
  · exact P.vertex_add_mem_arc a hk

theorem endpoints_subset_arc' (P : PrePolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arc (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := P.vertex_add_mem_arc (a + k) hpos
    rwa [hwrap] at hm
  · exact P.vertex_mem_arc (a + k) hpos

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_inj (P : PrePolygon m) (a : ZMod (m + 3)) {x z : ℕ} (hx : x < m + 3)
    (hz : z < m + 3) (he : P.vertex (a + (x : ZMod (m + 3))) = P.vertex (a + (z : ZMod (m + 3)))) :
    x = z :=
  ClosedPolygon.natCast_inj hx hz (add_left_cancel (P.vertex_inj he))

/-- An arc of `P` is a chain of the polygon read from its first vertex. -/
theorem arc_eq_chain (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.arc a k = (P.rotate a).chain (k - 1) := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  ext z
  rw [mem_arc_iff, mem_chain_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, by omega, by rw [hedge]; exact hz⟩
  · rintro ⟨j, hj, hz⟩
    rw [hedge] at hz
    exact ⟨j, by omega, hz⟩

/-- **An arc of a splitting is an arc between the two cut vertices.** -/
theorem isArcBetween_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : IsArcBetween (P.arc a k) (P.vertex a) (P.vertex (a + k)) := by
  have h := (P.rotate a).isArcBetween_chain (k - 1) (by omega)
  rw [← arc_eq_chain P a hk1, show ((k - 1 + 1 : ℕ) : ZMod (m + 3)) = (k : ZMod (m + 3)) by
    congr 1; omega] at h
  simpa using h

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** -/
theorem arc_inter (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arc a k ∩ P.arc (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arc a hk1)
    (P.endpoints_subset_arc' a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iff.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iff.1 hz2
  have hkt : k + t < m + 3 := by omega
  rw [show a + (k : ZMod (m + 3)) + (t : ZMod (m + 3)) = a + ((k + t : ℕ) : ZMod (m + 3)) by
    push_cast; ring] at hzt
  have hij : a + (s : ZMod (m + 3)) ≠ a + ((k + t : ℕ) : ZMod (m + 3)) := fun he =>
    absurd (ClosedPolygon.natCast_inj (by omega) hkt (add_left_cancel he)) (by omega)
  have hsucc₁ : a + (s : ZMod (m + 3)) + 1 = a + ((s + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hsucc₂ : a + ((k + t : ℕ) : ZMod (m + 3)) + 1 = a + ((k + t + 1 : ℕ) : ZMod (m + 3)) := by
    push_cast; ring
  have hA := P.edges_meet _ _ hij (Set.mem_inter hzs hzt)
  have hB := P.edges_meet _ _ (Ne.symm hij) (Set.mem_inter hzt hzs)
  rw [hsucc₁] at hA
  rw [hsucc₂] at hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB ⊢
  have hzero : k + t + 1 = m + 3 →
      ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_inj a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · have hst : s + 1 = k + t := P.natCast_shift_inj a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_inj a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_inj a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

/-- **The crossing count separates points exactly as the polygon does** (Theorem 2.3, read as a
criterion), for a polygon presented with redundant vertices. -/
theorem parity_ne_iff_mem_farRegion (P : PrePolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) {x y : Plane}
    (hx : x ∉ P.carrier) (hy : y ∉ P.carrier) :
    parity u P.pieces x ≠ parity u P.pieces y ↔ x ∈ farRegion P.carrier y := by
  rw [mem_farRegion_iff_connectedComponentIn_ne hx]
  constructor
  · intro hne heq
    exact hne (P.parity_eq_of_mem_connectedComponentIn_carrier hu hL hy
      (heq ▸ mem_connectedComponentIn hx))
  · intro hne
    rcases P.connectedComponentIn_eq_inside_or_outside hx with hxr | hxr <;>
      rcases P.connectedComponentIn_eq_inside_or_outside hy with hyr | hyr
    · exact absurd (hxr.trans hyr.symm) hne
    · rw [P.parity_eq_one_of_mem_inside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_zero_of_mem_outside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · rw [P.parity_eq_zero_of_mem_outside hu hL (hxr ▸ mem_connectedComponentIn hx),
        P.parity_eq_one_of_mem_inside hu hL (hyr ▸ mem_connectedComponentIn hy)]
      decide
    · exact absurd (hxr.trans hyr.symm) hne

end PrePolygon

/-! ## Cutting a segment at an interior point, in order

The two halves of a cut segment meet only at the cut, and neither reaches the far end of the
other. Both are read off `Schoenflies/SegmentOrder.lean`: along a nondegenerate segment the
distance from one end is a coordinate. -/

/-- **The two halves of a cut segment meet only at the cut.** -/
theorem segment_halves_inter {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    segment ℝ u w ∩ segment ℝ w v ⊆ {w} := by
  rintro x ⟨hx1, hx2⟩
  have hws : w ∈ segment ℝ u v := openSegment_subset_segment ℝ _ _ hw
  have hwd := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    (by simp) hws
  have h1 := dist_le_of_mem_segment huv (left_mem_segment ℝ u v) hws (by simp) hx1
  have h2 := dist_le_of_mem_segment huv hws (right_mem_segment ℝ u v) hwd.2 hx2
  have hxs : x ∈ segment ℝ u v :=
    (convex_segment u v).segment_subset (left_mem_segment ℝ u v) hws hx1
  exact eq_of_dist_left_eq huv hxs hws (le_antisymm h1.2 h2.1)

/-- The far end of a cut segment is not on the near half. -/
theorem right_notMem_left_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    v ∉ segment ℝ u w := by
  intro hv
  have hvw : v = w := segment_halves_inter huv hw ⟨hv, right_mem_segment ℝ w v⟩
  rw [← hvw] at hw
  exact huv (right_mem_openSegment_iff.1 hw)

/-- The near end of a cut segment is not on the far half. -/
theorem left_notMem_right_half {u v w : Plane} (huv : u ≠ v) (hw : w ∈ openSegment ℝ u v) :
    u ∉ segment ℝ w v := by
  intro hu
  have huw : u = w := segment_halves_inter huv hw ⟨left_mem_segment ℝ u w, hu⟩
  rw [← huw] at hw
  exact huv (left_mem_openSegment_iff.1 hw)

namespace PrePolygon

/-! ## Inserting a vertex

`Schoenflies.PrePolygon.deleteLast` removes a redundant vertex; this is the inverse operation,
and it is what makes `PrePolygon` the right presentation for a consumer that must cut the curve
at prescribed points. The vertex is inserted at the end of the list, interior to the last edge;
`Schoenflies.PrePolygon.rotate` brings any edge there. -/

section Insert

variable {m : ℕ} {P : PrePolygon m} {z : Plane}

/-- The index `-1` of a cyclic list of length `m + 3`, as a numeral. -/
theorem val_neg_one : (-1 : ZMod (m + 3)).val = m + 2 := by
  have h : (-1 : ZMod (m + 3)) = ((m + 2 : ℕ) : ZMod (m + 3)) := by
    have h0 : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
    push_cast at h0 ⊢
    linear_combination -h0
  rw [h, ZMod.val_cast_of_lt (by omega)]

/-- The last edge, with its second endpoint written as vertex `0`. -/
theorem edge_neg_one (P : PrePolygon m) :
    P.edge (-1) = segment ℝ (P.vertex (-1)) (P.vertex 0) := by
  rw [edge, show (-1 : ZMod (m + 3)) + 1 = 0 by ring]

/-- **A point interior to an edge is a vertex of no index.** -/
theorem vertex_ne_of_mem_openSegment {i : ZMod (m + 3)} {w : Plane}
    (hw : w ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) (j : ZMod (m + 3)) :
    P.vertex j ≠ w := by
  intro he
  by_cases hji : j = i
  · rw [hji] at he
    rw [← he] at hw
    exact vertex_ne_succ i (left_mem_openSegment_iff.1 hw)
  · have hmem : w ∈ P.edge j := by rw [edge, ← he]; exact left_mem_segment ℝ _ _
    exact notMem_edge_of_mem_openSegment hji hw hmem

/-- The vertex list with `z` appended at the end. -/
def insVertex (P : PrePolygon m) (z : Plane) (j : ZMod (m + 1 + 3)) : Plane :=
  if j.val < m + 3 then P.vertex ((j.val : ℕ) : ZMod (m + 3)) else z

theorem insVertex_emb (P : PrePolygon m) (z : Plane) (j : ZMod (m + 3)) :
    insVertex P z (emb j) = P.vertex j := by
  have hlt : j.val < m + 3 := ZMod.val_lt j
  have hval : (emb j).val = j.val := by
    rw [emb, ZMod.val_cast_of_lt (by omega)]
  rw [insVertex, if_pos (by rw [hval]; exact hlt), hval, ZMod.natCast_rightInverse j]

theorem val_neg_one' : (-1 : ZMod (m + 1 + 3)).val = m + 3 := by
  rw [neg_one_eq_cast, ZMod.val_cast_of_lt (by omega)]

theorem insVertex_neg_one (P : PrePolygon m) (z : Plane) : insVertex P z (-1) = z := by
  rw [insVertex, if_neg (by rw [val_neg_one' (m := m)]; omega)]

/-- Away from the inserted vertex the edges are unchanged. -/
theorem insEdge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (insVertex P z (emb j)) (insVertex P z (emb j + 1)) = P.edge j := by
  rw [← emb_succ_of_lt h, insVertex_emb, insVertex_emb, edge]

/-- The penultimate edge of the lengthened list: the near half of the cut edge. -/
theorem insEdge_pen (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1 - 1)) (insVertex P z (-1 - 1 + 1))
      = segment ℝ (P.vertex (-1)) z := by
  have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
  have h1 : insVertex P z (-1 - 1) = P.vertex (-1) := by rw [← he, insVertex_emb]
  have h2 : insVertex P z (-1 - 1 + 1) = z := by
    rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]
  rw [h1, h2]

/-- The last edge of the lengthened list: the far half of the cut edge. -/
theorem insEdge_last (P : PrePolygon m) (z : Plane) :
    segment ℝ (insVertex P z (-1)) (insVertex P z (-1 + 1)) = segment ℝ z (P.vertex 0) := by
  have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
  have h1 : insVertex P z (-1) = z := insVertex_neg_one P z
  have h2 : insVertex P z (-1 + 1) = P.vertex 0 := by
    rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]
  rw [h1, h2]

theorem vertex_neg_one_ne_zero (P : PrePolygon m) : P.vertex (-1) ≠ P.vertex 0 := by
  have h := vertex_ne_succ (P := P) (-1)
  rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at h

variable (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
include hz

/-- The two new edges cover the edge they replace. -/
theorem insEdge_union : segment ℝ (P.vertex (-1)) z ∪ segment ℝ z (P.vertex 0) = P.edge (-1) := by
  rw [edge_neg_one]
  exact (segment_split (openSegment_subset_segment ℝ _ _ hz)).symm

theorem insEdge_pen_subset : segment ℝ (P.vertex (-1)) z ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_left

theorem insEdge_last_subset : segment ℝ z (P.vertex 0) ⊆ P.edge (-1) := by
  rw [← insEdge_union hz]; exact Set.subset_union_right

/-- **The polygon with one extra vertex, interior to its last edge.** -/
def insertLast (P : PrePolygon m) (hz : z ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) :
    PrePolygon (m + 1) where
  vertex := insVertex P z
  vertex_inj := by
    intro i j hij
    have hzv : ∀ l : ZMod (m + 3), P.vertex l ≠ z := by
      intro l
      refine vertex_ne_of_mem_openSegment (i := -1) ?_ l
      rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring]
    simp only [insVertex] at hij
    have hi := ZMod.val_lt i
    have hj := ZMod.val_lt j
    by_cases hli : i.val < m + 3 <;> by_cases hlj : j.val < m + 3
    · rw [if_pos hli, if_pos hlj] at hij
      exact ZMod.val_injective _
        (ClosedPolygon.natCast_inj hli hlj (P.vertex_inj hij))
    · rw [if_pos hli, if_neg hlj] at hij
      exact absurd hij (hzv _)
    · rw [if_neg hli, if_pos hlj] at hij
      exact absurd hij.symm (hzv _)
    · exact ZMod.val_injective _ (by omega)
  edges_meet := by
    have hne0 : P.vertex (-1) ≠ P.vertex 0 := vertex_neg_one_ne_zero P
    have hhalf := segment_halves_inter hne0 hz
    have hpen := insEdge_pen P z
    have hlast := insEdge_last P z
    -- The shape of the edge at each of the three kinds of index.
    have hshape : ∀ i : ZMod (m + 1 + 3),
        (∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i ∧
            segment ℝ (insVertex P z i) (insVertex P z (i + 1)) = P.edge j ∧
            ({insVertex P z i, insVertex P z (i + 1)} : Set Plane)
              = {P.vertex j, P.vertex (j + 1)}) ∨
          (i = -1 - 1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ (P.vertex (-1)) z) ∨
          (i = -1 ∧ segment ℝ (insVertex P z i) (insVertex P z (i + 1))
              = segment ℝ z (P.vertex 0)) := by
      intro i
      by_cases h1 : i = -1
      · exact Or.inr (Or.inr ⟨h1, by rw [h1]; exact hlast⟩)
      by_cases h2 : i = -1 - 1
      · exact Or.inr (Or.inl ⟨h2, by rw [h2]; exact hpen⟩)
      obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine Or.inl ⟨j, hjv, rfl, insEdge_of_lt hjv, ?_⟩
      rw [insVertex_emb, ← emb_succ_of_lt hjv, insVertex_emb]
    intro i j hij
    have hi := hshape i
    have hj := hshape j
    -- The names of the two ends of the edge at `i`, in each case.
    rcases hi with ⟨ji, hjiv, rfl, hEi, hVi⟩ | ⟨rfl, hEi⟩ | ⟨rfl, hEi⟩
    · have hjine : ji ≠ -1 := by
        intro he
        rw [he, val_neg_one] at hjiv
        omega
      rw [hEi, hVi]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, hEj⟩
      · rw [hEj]
        exact P.edges_meet ji jj fun he => hij (by rw [he])
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_pen_subset hz hx.2⟩
      · rw [hEj]
        exact fun x hx =>
          P.edges_meet ji (-1) hjine ⟨hx.1, insEdge_last_subset hz hx.2⟩
    · rw [hEi]
      have hV : ({insVertex P z (-1 - 1), insVertex P z (-1 - 1 + 1)} : Set Plane)
          = {P.vertex (-1), z} := by
        have he : emb (-1 : ZMod (m + 3)) = -1 - 1 := emb_eq_last (by rw [val_neg_one])
        rw [show insVertex P z (-1 - 1) = P.vertex (-1) by rw [← he, insVertex_emb],
          show insVertex P z (-1 - 1 + 1) = z by
            rw [show (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 by ring, insVertex_neg_one]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hEj⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_pen_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · exact absurd (hmem ▸ hx1) (right_notMem_left_half hne0 hz)
      · exact absurd rfl hij
      · rw [hEj]
        exact fun x hx => Or.inr (hhalf hx)
    · rw [hEi]
      have hV : ({insVertex P z (-1), insVertex P z (-1 + 1)} : Set Plane)
          = {z, P.vertex 0} := by
        have hemb0 : emb (0 : ZMod (m + 3)) = 0 := by rw [emb, ZMod.val_zero, Nat.cast_zero]
        rw [insVertex_neg_one,
          show insVertex P z (-1 + 1) = P.vertex 0 by
            rw [show (-1 : ZMod (m + 1 + 3)) + 1 = 0 by ring, ← hemb0, insVertex_emb]]
      rw [hV]
      rcases hj with ⟨jj, hjjv, rfl, hEj, -⟩ | ⟨rfl, hEj⟩ | ⟨rfl, -⟩
      · have hjjne : jj ≠ -1 := by
          intro he
          rw [he, val_neg_one] at hjjv
          omega
        rw [hEj]
        rintro x ⟨hx1, hx2⟩
        have hmem := P.edges_meet (-1) jj (Ne.symm hjjne)
          ⟨insEdge_last_subset hz hx1, hx2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
        rcases hmem with hmem | hmem
        · exact absurd (hmem ▸ hx1) (left_notMem_right_half hne0 hz)
        · exact Or.inr hmem
      · rw [hEj]
        exact fun x hx => Or.inl (hhalf ⟨hx.2, hx.1⟩)
      · exact absurd rfl hij

@[simp] theorem insertLast_vertex : (insertLast P hz).vertex = insVertex P z := rfl

/-- **Inserting a vertex does not move the curve.** -/
theorem carrier_insertLast : (insertLast P hz).carrier = P.carrier := by
  have hpen := insEdge_pen P z
  have hlast := insEdge_last P z
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) (Set.iUnion_subset fun j => ?_)
  · by_cases h1 : i = -1
    · subst h1
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_last_subset hz) (edge_subset_carrier _))
      exact hlast
    by_cases h2 : i = -1 - 1
    · subst h2
      refine le_trans (le_of_eq ?_) (le_trans (insEdge_pen_subset hz) (edge_subset_carrier _))
      exact hpen
    · obtain ⟨j, hjv, rfl⟩ := exists_emb_eq h1 h2
      refine le_trans (le_of_eq ?_) (edge_subset_carrier j)
      exact insEdge_of_lt hjv
  · by_cases hjlast : j.val + 1 < m + 3
    · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := insertLast P hz) (emb j))
      exact (insEdge_of_lt hjlast (P := P) (z := z)).symm
    · have hjm : j = -1 := by
        have := ZMod.val_lt j
        exact ZMod.val_injective _ (by rw [val_neg_one]; omega)
      subst hjm
      rw [← insEdge_union hz]
      refine Set.union_subset ?_ ?_
      · refine le_trans (le_of_eq hpen.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1 - 1))
      · refine le_trans (le_of_eq hlast.symm)
          (edge_subset_carrier (P := insertLast P hz) (-1))

/-- The inserted vertex is a vertex. -/
theorem insertLast_mem_vertex : ∃ j, (insertLast P hz).vertex j = z :=
  ⟨-1, insVertex_neg_one P z⟩

/-- The old vertices are still vertices. -/
theorem insertLast_old_vertex (i : ZMod (m + 3)) : ∃ j, (insertLast P hz).vertex j = P.vertex i :=
  ⟨emb i, insVertex_emb P z i⟩

end Insert

/-- **A point of the curve can be made a vertex.** Either it already is one, or it is interior to
an edge, and then that edge is brought to the end of the list by `rotate` and cut. -/
theorem exists_prePolygon_insert {m : ℕ} (P : PrePolygon m) {z : Plane} (hz : z ∈ P.carrier) :
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧ (∃ j, P'.vertex j = z) ∧
      ∀ i, ∃ j, P'.vertex j = P.vertex i := by
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.1 hz
  by_cases hend : z = P.vertex i ∨ z = P.vertex (i + 1)
  · exact ⟨m, P, rfl, by rcases hend with rfl | rfl; exacts [⟨i, rfl⟩, ⟨i + 1, rfl⟩],
      fun i => ⟨i, rfl⟩⟩
  · push Not at hend
    have hopen : z ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
      mem_openSegment_of_ne_left_right (Ne.symm hend.1) (Ne.symm hend.2) hzi
    -- Rotate so that the edge in question is the last one.
    set Q : PrePolygon m := P.rotate (i + 1) with hQ
    have hQm : Q.vertex (-1) = P.vertex i := by
      rw [hQ, rotate_vertex, show i + 1 + (-1 : ZMod (m + 3)) = i by ring]
    have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
      rw [hQ, rotate_vertex, add_zero]
    have hopen' : z ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by rw [hQm, hQ0]; exact hopen
    refine ⟨m + 1, insertLast Q hopen', ?_, insertLast_mem_vertex hopen', fun l => ?_⟩
    · rw [carrier_insertLast hopen', hQ, carrier_rotate]
    · obtain ⟨j, hj⟩ := insertLast_old_vertex hopen' (l - (i + 1))
      exact ⟨j, by rw [hj, hQ, rotate_vertex, add_sub_cancel]⟩

/-- **Any finite list of points of the curve can be made vertices.** -/
theorem exists_prePolygon_vertices : ∀ (S : List Plane) {m : ℕ} (P : PrePolygon m),
    (∀ z ∈ S, z ∈ P.carrier) →
      ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
        (∀ z ∈ S, ∃ j, P'.vertex j = z) ∧ (∀ i, ∃ j, P'.vertex j = P.vertex i)
  | [], m, P, _ => ⟨m, P, rfl, by simp, fun i => ⟨i, rfl⟩⟩
  | z :: S, m, P, hS => by
    obtain ⟨m₁, P₁, hcar₁, ⟨j₀, hj₀⟩, hold₁⟩ :=
      exists_prePolygon_insert P (hS z (List.mem_cons_self ..))
    obtain ⟨m₂, P₂, hcar₂, hnew₂, hold₂⟩ := exists_prePolygon_vertices S P₁
      (fun w hw => by rw [hcar₁]; exact hS w (List.mem_cons_of_mem _ hw))
    refine ⟨m₂, P₂, by rw [hcar₂, hcar₁], fun w hw => ?_, fun i => ?_⟩
    · rcases List.mem_cons.1 hw with rfl | hw'
      · obtain ⟨j, hj⟩ := hold₂ j₀
        exact ⟨j, by rw [hj, hj₀]⟩
      · exact hnew₂ w hw'
    · obtain ⟨j₁, hj₁⟩ := hold₁ i
      obtain ⟨j, hj⟩ := hold₂ j₁
      exact ⟨j, by rw [hj, hj₁]⟩

/-- A one-edge arc is that edge. -/
theorem arc_one {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) : P.arc a 1 = P.edge a := by
  ext z
  rw [mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain rfl : t = 0 := by omega
    rwa [Nat.cast_zero, add_zero] at hz
  · intro hz
    exact ⟨0, by omega, by rwa [Nat.cast_zero, add_zero]⟩

/-- **A vertex on an edge is one of that edge's own two ends.** -/
theorem vertex_mem_edge_elim {m : ℕ} {P : PrePolygon m} {c i : ZMod (m + 3)}
    (hc : P.vertex c ∈ P.edge i) :
    P.vertex c ∈ ({P.vertex i, P.vertex (i + 1)} : Set Plane) := by
  by_cases hci : c = i
  · exact Or.inl (by rw [hci])
  · exact P.edges_meet i c (Ne.symm hci) ⟨hc, left_mem_segment ℝ _ _⟩

/-! ## Splicing two chains into a closed polygon

The crosscut of Theorem 2.8 asks for three closed polygons whose *edge lists* fit together, and
independent realizations of three curves do not. The way out is to realize only the curve `C`,
and to build the two spliced curves out of one arc of `C` and one presentation of the crosscut —
so that the three edge lists agree by construction. This is that construction: two chains with
the same pair of ends, meeting only there, laid end to end. -/

/-- **Two arcs with common ends splice into a closed polygon whose edge list is their
concatenation.** `P.arcPieces a k` runs from `p` to `q` and `P'.arcPieces b l` runs from `q` back
to `p`; the two meet only at `p` and `q`. -/
theorem exists_splice {m m' : ℕ} (P : PrePolygon m) (P' : PrePolygon m')
    {a : ZMod (m + 3)} {k : ℕ} {b : ZMod (m' + 3)} {l : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (hl1 : 1 ≤ l) (hl2 : l ≤ m' + 2)
    (hstart : P'.vertex b = P.vertex (a + (k : ZMod (m + 3))))
    (hend : P'.vertex (b + (l : ZMod (m' + 3))) = P.vertex a)
    (hinter : P.arc a k ∩ P'.arc b l = {P.vertex a, P.vertex (a + (k : ZMod (m + 3)))}) :
    ∃ (n : ℕ) (Q : PrePolygon n), Q.pieces = P.arcPieces a k ++ P'.arcPieces b l := by
  -- The two chains cannot both be a single edge: they would be the same segment.
  have hthree : 3 ≤ k + l := by
    by_contra hcon
    obtain rfl : k = 1 := by omega
    obtain rfl : l = 1 := by omega
    rw [Nat.cast_one] at hstart hinter
    rw [Nat.cast_one] at hend
    have hseg : P'.edge b = P.edge a := by
      rw [edge, edge, hstart, hend, segment_symm]
    rw [P.arc_one a, P'.arc_one b, hseg, Set.inter_self] at hinter
    obtain ⟨z, hz, hz1, hz2⟩ := exists_mem_segment_ne (vertex_ne_succ (P := P) a)
    rcases hinter.subset hz with h | h
    exacts [hz1 h, hz2 h]
  obtain ⟨n, hn⟩ : ∃ n, k + l = n + 3 := ⟨k + l - 3, by omega⟩
  -- Pieces of one arc lie in that arc; that is all the intersection hypothesis is used through.
  have hPedge : ∀ t : ℕ, t < k → P.edge (a + (t : ZMod (m + 3))) ⊆ P.arc a k :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hP'edge : ∀ t : ℕ, t < l → P'.edge (b + (t : ZMod (m' + 3))) ⊆ P'.arc b l :=
    fun t ht z hz => mem_arc_iff.2 ⟨t, ht, hz⟩
  have hcross : ∀ s : ℕ, s < k → ∀ t : ℕ, t < l →
      P.edge (a + (s : ZMod (m + 3))) ∩ P'.edge (b + (t : ZMod (m' + 3)))
        ⊆ ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    intro s hs t ht z hz
    rw [← hinter]
    exact ⟨hPedge s hs hz.1, hP'edge t ht hz.2⟩
  -- The spliced vertex list.
  set w : ZMod (n + 3) → Plane := fun j =>
    if j.val < k then P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)))
    else P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) with hwdef
  have hbound : ∀ j : ZMod (n + 3), j.val < k + l := fun j => by
    have := ZMod.val_lt j; omega
  have hw_lt : ∀ j : ZMod (n + 3), j.val < k →
      w j = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))) := fun j hj => by
    rw [hwdef]; exact if_pos hj
  have hw_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w j = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := fun j hj => by
    rw [hwdef]; exact if_neg hj
  have hsucc_lt : ∀ j : ZMod (n + 3), j.val < k →
      w (j + 1) = P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1) := by
    intro j hj
    have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
    by_cases hlt : j.val + 1 < k
    · rw [hw_lt (j + 1) (by omega), hval]
      congr 1
      push_cast
      ring
    · have hk' : j.val + 1 = k := by omega
      rw [hw_ge (j + 1) (by omega), hval, hk', Nat.sub_self, Nat.cast_zero, add_zero, hstart]
      congr 1
      rw [← hk']
      push_cast
      ring
  have hsucc_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      w (j + 1) = P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1) := by
    intro j hj
    have hjb := hbound j
    by_cases hlt : j.val + 1 < n + 3
    · have hval : (j + 1).val = j.val + 1 := val_succ_of_lt (m := n) (by omega)
      rw [hw_ge (j + 1) (by omega), hval]
      congr 1
      rw [show j.val + 1 - k = (j.val - k) + 1 by omega]
      push_cast
      ring
    · have hval : (j + 1).val = 0 := val_succ_last (m := n) (by omega)
      rw [hw_lt (j + 1) (by omega), hval, Nat.cast_zero, add_zero, ← hend]
      congr 1
      have hc : ((l - 1 : ℕ) : ZMod (m' + 3)) + 1 = ((l : ℕ) : ZMod (m' + 3)) :=
        ClosedPolygon.natCast_pred_succ (by omega)
      rw [show j.val - k = l - 1 by omega, add_assoc, hc]
  -- The edges of the spliced list are the edges of the two arcs.
  have hE_lt : ∀ j : ZMod (n + 3), j.val < k →
      segment ℝ (w j) (w (j + 1)) = P.edge (a + ((j.val : ℕ) : ZMod (m + 3))) := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj, edge]
  have hE_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      segment ℝ (w j) (w (j + 1)) = P'.edge (b + ((j.val - k : ℕ) : ZMod (m' + 3))) := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj, edge]
  have hends_lt : ∀ j : ZMod (n + 3), j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P.vertex (a + ((j.val : ℕ) : ZMod (m + 3))),
           P.vertex (a + ((j.val : ℕ) : ZMod (m + 3)) + 1)} := by
    intro j hj
    rw [hw_lt j hj, hsucc_lt j hj]
  have hends_ge : ∀ j : ZMod (n + 3), ¬ j.val < k →
      ({w j, w (j + 1)} : Set Plane)
        = {P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3))),
           P'.vertex (b + ((j.val - k : ℕ) : ZMod (m' + 3)) + 1)} := by
    intro j hj
    rw [hw_ge j hj, hsucc_ge j hj]
  refine ⟨n, ⟨w, ?_, ?_⟩, ?_⟩
  · -- injectivity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    have hcase : ∀ i' j' : ZMod (n + 3), i'.val < k → ¬ j'.val < k → w i' ≠ w j' := by
      intro i' j' hi' hj' he
      rw [hw_lt i' hi', hw_ge j' hj'] at he
      have hval : P.vertex (a + ((i'.val : ℕ) : ZMod (m + 3))) ∈
          ({P.vertex a, P.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
        rw [← hinter]
        exact ⟨hPedge i'.val hi' (left_mem_segment ℝ _ _),
          he ▸ hP'edge (j'.val - k) (by have := hbound j'; omega) (left_mem_segment ℝ _ _)⟩
      rcases hval with hval | hval
      · -- the common point is `p`: on the second arc that forces the last index
        have h0 : i'.val = 0 := by
          have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show 0 < m + 3 by omega)
            (by rw [hval, Nat.cast_zero, add_zero])
          omega
        have hlast : P'.vertex (b + ((j'.val - k : ℕ) : ZMod (m' + 3)))
            = P'.vertex (b + ((l : ℕ) : ZMod (m' + 3))) := by rw [hend, ← he, hval]
        have := P'.natCast_shift_inj b (show j'.val - k < m' + 3 by have := hbound j'; omega)
          (show l < m' + 3 by omega) hlast
        have := hbound j'
        omega
      · have := P.natCast_shift_inj a (show i'.val < m + 3 by omega) (show k < m + 3 by omega)
          (by rw [hval])
        omega
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hw_lt i hli, hw_lt j hlj] at hij
      exact ZMod.val_injective _ (P.natCast_shift_inj a (by omega) (by omega) hij)
    · exact absurd hij (hcase i j hli hlj)
    · exact absurd hij.symm (hcase j i hlj hli)
    · rw [hw_ge i hli, hw_ge j hlj] at hij
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) hij
      exact ZMod.val_injective _ (by omega)
  · -- simplicity
    intro i j hij
    have hib := hbound i
    have hjb := hbound j
    by_cases hli : i.val < k <;> by_cases hlj : j.val < k
    · rw [hE_lt i hli, hE_lt j hlj, hends_lt i hli]
      refine P.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      exact P.natCast_shift_inj a (by omega) (by omega) (by rw [he])
    · rw [hE_lt i hli, hE_ge j hlj, hends_lt i hli]
      intro z hz
      have hz' := hcross i.val hli (j.val - k) (by omega) hz
      rcases hz' with rfl | rfl
      exacts [vertex_mem_edge_elim (P := P) (c := a) hz.1,
        vertex_mem_edge_elim (P := P) (c := a + (k : ZMod (m + 3))) hz.1]
    · rw [hE_ge i hli, hE_lt j hlj, hends_ge i hli]
      intro z hz
      have hz' := hcross j.val hlj (i.val - k) (by omega) ⟨hz.2, hz.1⟩
      rcases hz' with rfl | rfl
      · rw [← hend]
        exact vertex_mem_edge_elim (P := P') (c := b + (l : ZMod (m' + 3)))
          (by rw [hend]; exact hz.1)
      · rw [← hstart]
        exact vertex_mem_edge_elim (P := P') (c := b) (by rw [hstart]; exact hz.1)
    · rw [hE_ge i hli, hE_ge j hlj, hends_ge i hli]
      refine P'.edges_meet _ _ fun he => hij (ZMod.val_injective _ ?_)
      have := P'.natCast_shift_inj b (show i.val - k < m' + 3 by omega)
        (show j.val - k < m' + 3 by omega) (by rw [he])
      omega
  · -- the edge list
    have hrange : List.range (n + 3) = List.range k ++ (List.range l).map (k + ·) := by
      rw [← hn]; exact List.range_add
    change ((List.range (n + 3)).map fun j : ℕ =>
        (w ((j : ℕ) : ZMod (n + 3)), w (((j : ℕ) : ZMod (n + 3)) + 1))) = _
    rw [hrange, List.map_append, List.map_map, arcPieces, arcPieces]
    congr 1
    · refine List.map_congr_left fun t ht => ?_
      have htk : t < k := List.mem_range.1 ht
      have hval : ((t : ZMod (n + 3))).val = t := ZMod.val_cast_of_lt (by omega)
      have h1 : ((t : ZMod (n + 3))).val < k := by rw [hval]; exact htk
      rw [hw_lt _ h1, hsucc_lt _ h1, hval]
    · refine List.map_congr_left fun s hs => ?_
      have hsl : s < l := List.mem_range.1 hs
      have hval : (((k + s : ℕ) : ZMod (n + 3))).val = k + s := ZMod.val_cast_of_lt (by omega)
      have h1 : ¬ (((k + s : ℕ) : ZMod (n + 3))).val < k := by rw [hval]; omega
      simp only [Function.comp_apply]
      rw [hw_ge _ h1, hsucc_ge _ h1, hval, show k + s - k = s by omega]

/-! ## The polygon read backwards

Needed only to pin the *direction* in which a realization traverses a prescribed arc; the
`Schoenflies.ClosedPolygon` version is in `Schoenflies/Graph/K33Closed.lean`, and this is the
same construction with the `corner` field dropped. -/

/-- **The same closed polygon, traversed the other way.** -/
def reverse {m : ℕ} (P : PrePolygon m) : PrePolygon m where
  vertex j := P.vertex (-j)
  vertex_inj _ _ h := neg_injective (P.vertex_inj h)
  edges_meet i j hij := by
    have e1 : (-(i + 1) : ZMod (m + 3)) = -i - 1 := by ring
    have e2 : (-(j + 1) : ZMod (m + 3)) = -j - 1 := by ring
    have e3 : (-i - 1 : ZMod (m + 3)) + 1 = -i := by ring
    have e4 : (-j - 1 : ZMod (m + 3)) + 1 = -j := by ring
    have hij' : (-i - 1 : ZMod (m + 3)) ≠ -j - 1 := fun h => hij (by linear_combination -h)
    have h := P.edges_meet (-i - 1) (-j - 1) hij'
    rw [e3, e4] at h
    simp only [e1, e2]
    rw [segment_symm ℝ (P.vertex (-i)) (P.vertex (-i - 1)),
      segment_symm ℝ (P.vertex (-j)) (P.vertex (-j - 1)), Set.pair_comm]
    exact h

@[simp] theorem reverse_vertex {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.vertex j = P.vertex (-j) := rfl

theorem reverse_edge {m : ℕ} (P : PrePolygon m) (j : ZMod (m + 3)) :
    P.reverse.edge j = P.edge (-j - 1) := by
  rw [edge, edge, reverse_vertex, reverse_vertex,
    show (-(j + 1) : ZMod (m + 3)) = -j - 1 by ring,
    show (-j - 1 : ZMod (m + 3)) + 1 = -j by ring]
  exact segment_symm ℝ _ _

@[simp] theorem reverse_carrier {m : ℕ} (P : PrePolygon m) : P.reverse.carrier = P.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [reverse_edge] at hi
    exact Set.mem_iUnion.2 ⟨_, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    refine Set.mem_iUnion.2 ⟨-i - 1, ?_⟩
    rw [reverse_edge, show (-(-i - 1) - 1 : ZMod (m + 3)) = i by ring]
    exact hi

/-- **Reversing does not move an arc**, it only starts it at the other end. -/
theorem reverse_arc {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.reverse.arc (-a - (k : ZMod (m + 3))) k = P.arc a k := by
  ext z
  rw [mem_arc_iff, mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hz⟩
    rw [reverse_edge] at hz
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [show a + ((k - t - 1 : ℕ) : ZMod (m + 3))
        = -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3))) - 1 by
      linear_combination ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨k - t - 1, by omega, ?_⟩
    rw [reverse_edge, show -(-a - (k : ZMod (m + 3)) + ((k - t - 1 : ℕ) : ZMod (m + 3))) - 1
        = a + (t : ZMod (m + 3)) by
      linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) ht]
    exact hz

/-- **Reversing does not change the edge list either**, up to the order and the naming of each
edge's two ends — which is exactly what `Schoenflies.SameEdges` forgives. -/
theorem sameEdges_reverse_arcPieces {m : ℕ} (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    SameEdges (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k) (P.arcPieces a k) := by
  have key : (P.reverse.arcPieces (-a - (k : ZMod (m + 3))) k).map orientPiece
      = ((P.arcPieces a k).map orientPiece).reverse := by
    rw [arcPieces, arcPieces, List.map_map, List.map_map, ← List.map_reverse,
      List.range_eq_range', List.reverse_range', ← List.range_eq_range', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    have htk : t < k := List.mem_range.1 ht
    have he : (0 + k - 1 - t : ℕ) = k - t - 1 := by omega
    simp only [Function.comp_apply, he, reverse_vertex]
    rw [show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)))
          = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) + 1 by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk,
      show -(-a - (k : ZMod (m + 3)) + (t : ZMod (m + 3)) + 1)
        = a + ((k - t - 1 : ℕ) : ZMod (m + 3)) by
        linear_combination -ClosedPolygon.reverse_natCast (n := m + 3) htk]
    exact orientPiece_swap (_, _)
  rw [SameEdges, key]
  exact List.reverse_perm _

end PrePolygon

/-! ## The realization theorem, with the cut points anywhere on the curve

`Schoenflies.exists_closedPolygon_split` requires the two cut points to be *corners*, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that requirement cannot be dropped while the
realization is a `ClosedPolygon`. For a `PrePolygon` there is no such obstruction: a point of the
curve is either already a vertex or interior to an edge, and an edge may be cut. -/

/-- **The realization theorem for `PrePolygon`, with named points.** Any finite list of points of
the curve — corners or not — can be required to be among the vertices. -/
theorem exists_prePolygon_points {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    (S : List Plane) (hS : ∀ p ∈ S, p ∈ C) :
    ∃ (m : ℕ) (P : PrePolygon m), P.carrier = C ∧ ∀ p ∈ S, ∃ i : ZMod (m + 3), P.vertex i = p := by
  obtain ⟨m, P, hcar⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m', P', hcar', hnew, -⟩ :=
    PrePolygon.exists_prePolygon_vertices S P (fun z hz => by rw [hcar]; exact hS z hz)
  exact ⟨m', P', by rw [hcar', hcar], hnew⟩

/-- **The realization theorem, tracking a splitting at two arbitrary points.** -/
theorem exists_prePolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m, P, hcar, hvert⟩ := exists_prePolygon_points hJ hP [p, q]
    (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      exacts [hp, hq])
  obtain ⟨a, ha⟩ := hvert p (by simp)
  obtain ⟨b, hb⟩ := hvert q (by simp)
  have hab : b - a ≠ 0 := fun he => hpq (by rw [← ha, ← hb, show b = a by linear_combination he])
  refine ⟨m, P, a, (b - a).val, hcar, ha, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_rightInverse (b - a), add_sub_cancel]; exact hb
  · rcases Nat.eq_zero_or_pos (b - a).val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse (b - a), h0, Nat.cast_zero]) hab
    · exact h0
  · have := ZMod.val_lt (b - a)
    omega

/-- **The realization theorem, tracking a splitting into two named arcs.** -/
theorem exists_prePolygon_arcs {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      ((P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂) ∨
        (P.arc a k = A₂ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₁)) := by
  obtain ⟨m, P, a, k, hcar, hpa, hqa, hk1, hk2⟩ := exists_prePolygon_split hJ hP hp hq hpq
  refine ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, ?_⟩
  have hD1 : IsArcBetween (P.arc a k) p q := by
    rw [← hpa, ← hqa]; exact P.isArcBetween_arc a hk1 hk2
  have hD2 : IsArcBetween (P.arc (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    have h := P.isArcBetween_arc (a + (k : ZMod (m + 3))) (k := m + 3 - k) (by omega) (by omega)
    rw [zmod_add_sub_cancel (by omega) a] at h
    rw [← hpa, ← hqa]
    exact h.reverse
  have hDunion : P.arc a k ∪ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = C := by
    rw [P.arc_union a (by omega), hcar]
  have hDinter : P.arc a k ∩ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [P.arc_inter a hk1 hk2, hpa, hqa]
  rcases two_arcs_unique hunion hinter hDunion hDinter hA1 hA2 hD1 hD2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1.symm, e2.symm⟩
  · exact Or.inr ⟨e2.symm, e1.symm⟩

/-- **The realization of a splitting, with both the arcs and the direction fixed.** The two arcs
come out in the order they were given *and* the first is traversed from `p` to `q`; reading the
polygon backwards when it is not is what pins the direction.

This is the shape the crosscut wiring consumes, and — unlike
`Schoenflies.exists_closedPolygon_arcs_oriented` — it asks nothing of `p` and `q` beyond lying on
the curve. -/
theorem exists_prePolygon_arcs_oriented {C A₁ A₂ : Set Plane} (hJ : IsJordanCurve C)
    (hP : IsPolygonal C) {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q) (hunion : A₁ ∪ A₂ = C)
    (hinter : A₁ ∩ A₂ = {p, q}) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      1 ≤ k ∧ k ≤ m + 2 ∧ P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧
      P.arc a k = A₁ ∧ P.arc (a + (k : ZMod (m + 3))) (m + 3 - k) = A₂ := by
  obtain ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, hcase⟩ :=
    exists_prePolygon_arcs hJ hP hp hq hpq hA1 hA2 hunion hinter
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨m, P, a, k, hcar, hk1, hk2, hpa, hqa, e1, e2⟩
  · -- The realization runs the two arcs the other way round: read it backwards.
    have hneg : ((m + 3 - k : ℕ) : ZMod (m + 3)) = -(k : ZMod (m + 3)) := by
      linear_combination zmod_add_sub_cancel (m := m) (k := k) (by omega) 0
    refine ⟨m, P.reverse, -a, m + 3 - k, ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [PrePolygon.reverse_carrier]; exact hcar
    · rw [PrePolygon.reverse_vertex, neg_neg]; exact hpa
    · rw [PrePolygon.reverse_vertex, hneg,
        show -(-a + -(k : ZMod (m + 3))) = a + (k : ZMod (m + 3)) by ring]
      exact hqa
    · have h := P.reverse_arc (a + (k : ZMod (m + 3))) (m + 3 - k)
      rw [hneg, show -(a + (k : ZMod (m + 3))) - -(k : ZMod (m + 3)) = -a by ring] at h
      rw [h]; exact e2
    · have h := P.reverse_arc a k
      rw [show m + 3 - (m + 3 - k) = k by omega, hneg,
        show -a + -(k : ZMod (m + 3)) = -a - (k : ZMod (m + 3)) by ring, h]
      exact e1

/-! ## Theorem 2.8 and Corollary 2.9 for a polygon presented with redundant vertices

`Schoenflies.IsPolygonalCrosscut` is stated for `ClosedPolygon`s, and by
`Schoenflies.ClosedPolygon.isCornerAt_vertex` that pins the two cut points to be *corners* of the
curve. Nothing in the proof of Theorem 2.8 needs the `corner` field: what it uses of `C`, `J₁`,
`J₂` is that their carriers separate the plane and that their crossing counts are the ones the
edge lists compute. `Schoenflies/PrePolygonSep.lean` supplies both for a `PrePolygon`, so the
whole chain goes through with the cut points anywhere on the curve. -/

variable {m m₁ m₂ : ℕ} {C : PrePolygon m} {J₁ : PrePolygon m₁} {J₂ : PrePolygon m₂}
  {K : List Piece} {a : ZMod (m + 3)} {k : ℕ} {y : Plane}

/-- **The setting of Theorem 2.8, with the cut points unrestricted.** Word for word
`Schoenflies.IsPolygonalCrosscut`, with `PrePolygon` for `ClosedPolygon`. -/
structure IsPrePolygonalCrosscut (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (y : Plane) : Prop where
  /-- The first arc runs forward through at most a full turn. -/
  le : k ≤ m + 3
  /-- `J₁` carries the edges of the first arc together with those of the crosscut. -/
  edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K)
  /-- `J₂` carries the edges of the second arc together with those of the crosscut. -/
  edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K)
  /-- The crosscut meets the polygon only in points of the first arc … -/
  meets₁ : cover K ∩ C.carrier ⊆ C.arc a k
  /-- … and only in points of the second arc. -/
  meets₂ : cover K ∩ C.carrier ⊆ C.arc (a + k) (m + 3 - k)
  /-- The reference point lies off the polygon … -/
  notMem : y ∉ C.carrier
  /-- … and the crosscut does not enter its region. -/
  avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)

/-- **The front door.** A crosscut is normally presented by saying that it meets `C` exactly in
its two endpoints, and that those endpoints are the two cut vertices. -/
theorem IsPrePolygonalCrosscut.of_endpoints (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (edges₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (edges₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    (meets : cover K ∩ C.carrier ⊆ ({C.vertex a, C.vertex (a + k)} : Set Plane))
    (notMem : y ∉ C.carrier)
    (avoids : Disjoint (cover K) (connectedComponentIn C.carrierᶜ y)) :
    IsPrePolygonalCrosscut C J₁ J₂ K a k y :=
  ⟨by omega, edges₁, edges₂, meets.trans (C.endpoints_subset_arc a hk1),
    meets.trans (C.endpoints_subset_arc' a hk2), notMem, avoids⟩

namespace IsPrePolygonalCrosscut

variable (h : IsPrePolygonalCrosscut C J₁ J₂ K a k y)
include h

/-- **The two arcs may be swapped.** -/
theorem symm : IsPrePolygonalCrosscut C J₂ J₁ K (a + k) (m + 3 - k) y := by
  have hk : k ≤ m + 3 := h.le
  have hnat : m + 3 - (m + 3 - k) = k := by omega
  have hzmod := zmod_add_sub_cancel (k := k) hk a
  refine ⟨by omega, h.edges₂, ?_, h.meets₂, ?_, h.notMem, h.avoids⟩
  · rw [hzmod, hnat]; exact h.edges₁
  · rw [hzmod, hnat]; exact h.meets₁

/-! ### The elementary consequences -/

theorem notMem_cover : y ∉ cover K :=
  fun hy => Set.disjoint_left.1 h.avoids hy (mem_connectedComponentIn h.notMem)

theorem carrier₁ : J₁.carrier = C.arc a k ∪ cover K :=
  PrePolygon.carrier_eq_of_sameEdges h.edges₁

theorem notMem_carrier₁ : y ∉ J₁.carrier :=
  PrePolygon.notMem_carrier_of_sameEdges h.edges₁ h.notMem h.notMem_cover

theorem cover_subset_carrier₁ : cover K ⊆ J₁.carrier := by
  rw [h.carrier₁]; exact Set.subset_union_right

theorem carrier₁_subset : J₁.carrier ⊆ C.carrier ∪ cover K := by
  rw [h.carrier₁]
  exact Set.union_subset_union_left _ (C.arc_subset_carrier a k)

/-- The edges of the crosscut are nondegenerate, because they are edges of `J₁`. -/
theorem nondeg : ∀ Q ∈ K, Q.Nondeg := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.edges₁.symm.exists_mem (List.mem_append_right _ hQ)
  have hRn : (orientPiece R).Nondeg := orientPiece_nondeg (J₁.pieces_nondeg R hR)
  rw [hRQ] at hRn
  rcases orientPiece_eq_or Q with e | e
  · rw [e] at hRn; exact hRn
  · rw [e] at hRn; exact fun hh => hRn hh.symm

/-- A ray direction transverse to every edge of `C` and of the crosscut at once. -/
theorem exists_direction : ∃ u : Plane, Plane.IsDirection u ∧
    (∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) ∧ (∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) := by
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ K) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ' | hQ'
    · exact C.pieces_nondeg Q hQ'
    · exact h.nondeg Q hQ')
  exact ⟨u, hu, fun Q hQ => hlev Q (List.mem_append_left _ hQ),
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)⟩

/-! ### The two cells -/

theorem regionPairC :
    IsRegionPair C.carrier (farRegion C.carrier y) (connectedComponentIn C.carrierᶜ y) :=
  (C.isSeparating_carrier.isRegionPair_farRegion h.notMem).symm

theorem regionPair₁ :
    IsRegionPair J₁.carrier (connectedComponentIn J₁.carrierᶜ y) (farRegion J₁.carrier y) :=
  J₁.isSeparating_carrier.isRegionPair_farRegion h.notMem_carrier₁

/-- The untouched region of `ℝ² ∖ C` lies in one region of `ℝ² ∖ J₁`, namely the one of `y`. -/
theorem near_subset₁ :
    connectedComponentIn C.carrierᶜ y ⊆ connectedComponentIn J₁.carrierᶜ y := by
  refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
    (mem_connectedComponentIn h.notMem) (fun w hw => ?_)
  have hwC : w ∉ C.carrier := connectedComponentIn_subset _ _ hw
  have hwK : w ∉ cover K := fun hK => Set.disjoint_left.1 h.avoids hK hw
  exact PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hwC hwK

/-- **Lemma 2.6(a), first half**: the cell lies in `Ω ∖ P`. -/
theorem cell_subset₁ : farRegion J₁.carrier y ⊆ farRegion C.carrier y \ cover K :=
  cell_subset_region_diff (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁

theorem cell_subset₂ : farRegion J₂.carrier y ⊆ farRegion C.carrier y \ cover K :=
  h.symm.cell_subset₁

/-- **Lemma 2.6(a)**: the cell is a connected component of `Ω ∖ P`. -/
theorem cell_isComponent₁ : ∀ z ∈ farRegion J₁.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₁.carrier y :=
  cell_isComponent (P := cover K) C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC h.regionPair₁ h.near_subset₁ h.cover_subset_carrier₁ h.carrier₁_subset

theorem cell_isComponent₂ : ∀ z ∈ farRegion J₂.carrier y,
    connectedComponentIn (farRegion C.carrier y \ cover K) z = farRegion J₂.carrier y :=
  h.symm.cell_isComponent₁

/-- **Lemma 2.6(c)**: the closure of the cell meets the polygon exactly in its arc. -/
theorem closure_cell_inter₁ : closure (farRegion J₁.carrier y) ∩ C.carrier = C.arc a k := by
  rw [closure_cell_inter_curve C.isSeparating_carrier J₁.isSeparating_carrier
    h.regionPairC.right h.regionPair₁ h.near_subset₁, h.carrier₁]
  refine Set.Subset.antisymm ?_ (fun w hw => ⟨Or.inl hw, C.arc_subset_carrier a k hw⟩)
  rintro w ⟨hw | hw, hwC⟩
  · exact hw
  · exact h.meets₁ ⟨hw, hwC⟩

theorem closure_cell_inter₂ :
    closure (farRegion J₂.carrier y) ∩ C.carrier = C.arc (a + k) (m + 3 - k) :=
  h.symm.closure_cell_inter₁

/-! ### Exhaustion: the crossing counts add up -/

/-- **A point off `C ∪ P` is separated from `y` by `C` exactly when it is separated from `y` by
exactly one of `J₁, J₂`.** -/
theorem separates_xor {x : Plane} (hxC : x ∉ C.carrier) (hxK : x ∉ cover K) :
    x ∈ farRegion C.carrier y ↔
      (x ∈ farRegion J₁.carrier y ↔ ¬ x ∈ farRegion J₂.carrier y) := by
  obtain ⟨u, hu, hlevC, hlevK⟩ := h.exists_direction
  have hlev₁ := h.edges₁.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hlev₂ := h.edges₂.hgt_ne (PrePolygon.arcPieces_append_hgt_ne hlevC hlevK)
  have hxJ₁ := PrePolygon.notMem_carrier_of_sameEdges h.edges₁ hxC hxK
  have hxJ₂ := PrePolygon.notMem_carrier_of_sameEdges h.edges₂ hxC hxK
  rw [← C.parity_ne_iff_mem_farRegion hu hlevC hxC h.notMem,
    ← J₁.parity_ne_iff_mem_farRegion hu hlev₁ hxJ₁ h.notMem_carrier₁,
    ← J₂.parity_ne_iff_mem_farRegion hu hlev₂ hxJ₂ h.symm.notMem_carrier₁]
  have hsx := C.parity_splitting u a h.le h.edges₁ h.edges₂ x
  have hsy := C.parity_splitting u a h.le h.edges₁ h.edges₂ y
  have key : ∀ s₁ s₂ s t₁ t₂ t : ZMod 2, s₁ + s₂ = s → t₁ + t₂ = t →
      (s ≠ t ↔ ((s₁ ≠ t₁) ↔ ¬ (s₂ ≠ t₂))) := by decide
  exact key _ _ _ _ _ _ hsx hsy

/-- **Theorem 2.8, the two cells.** -/
theorem region_eq :
    farRegion C.carrier y \ cover K = farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
  refine Set.Subset.antisymm ?_ (Set.union_subset h.cell_subset₁ h.cell_subset₂)
  rintro w ⟨hwΩ, hwK⟩
  by_cases hw₁ : w ∈ farRegion J₁.carrier y
  · exact Or.inl hw₁
  · refine Or.inr ?_
    by_contra hw₂
    exact hw₁ (((h.separates_xor hwΩ.1 hwK).1 hwΩ).2 hw₂)

/-! ### Corollary 2.9 -/

/-- **The region the crosscut enters is the component of any of its points off `C`.** -/
theorem connectedComponentIn_cover_eq {z : Plane} (hz : z ∈ cover K) (hzC : z ∉ C.carrier) :
    connectedComponentIn C.carrierᶜ z = farRegion C.carrier y :=
  h.regionPairC.left.connectedComponentIn_eq C.isSeparating_carrier
    (diff_subset_farRegion h.avoids ⟨hz, hzC⟩)

/-- **Corollary 2.9, core form.** -/
theorem inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hconn : IsPreconnected Q) (hside : Q ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ farRegion C.carrier y \ cover K :=
    fun z hz => ⟨hside hz, fun hzK => hempty z ⟨hz, hzK⟩⟩
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ
    rw [Set.not_nonempty_iff_eq_empty] at hQ
    rw [hQ, closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ farRegion J₁.carrier y ∪ farRegion J₂.carrier y := by
    rw [← h.region_eq]; exact hsub hz
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ farRegion J₁.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₁ z hz₁] at hcc
    have hmem : w₂ ∈ closure (farRegion J₁.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₁ hw₂, C.arc_subset_carrier _ _ hw₂B⟩
    rw [h.closure_cell_inter₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ farRegion J₂.carrier y := by
      have hcc := hconn.subset_connectedComponentIn hz hsub
      rwa [h.cell_isComponent₂ z hz₂] at hcc
    have hmem : w₁ ∈ closure (farRegion J₂.carrier y) ∩ C.carrier :=
      ⟨closure_mono hQ₂ hw₁, C.arc_subset_carrier _ _ hw₁A⟩
    rw [h.closure_cell_inter₂] at hmem
    exact hw₁B hmem

/-- **Corollary 2.9 for a second crosscut presented as a simple arc.** -/
theorem arc_inter_cover_nonempty {Q : Set Plane} {w₁ w₂ : Plane}
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁A : w₁ ∈ C.arc a k) (hw₁B : w₁ ∉ C.arc (a + k) (m + 3 - k))
    (hw₂B : w₂ ∈ C.arc (a + k) (m + 3 - k)) (hw₂A : w₂ ∉ C.arc a k) :
    (Q ∩ cover K).Nonempty := by
  obtain ⟨z, hzQ, hzK⟩ := h.inter_cover_nonempty hQ.isPreconnected_diff hside
    hQ.left_mem_closure_diff hQ.right_mem_closure_diff hw₁A hw₁B hw₂B hw₂A
  exact ⟨z, hzQ.1, hzK⟩

/-- **Corollary 2.9 in the shape a plane-graph argument produces it.** -/
theorem alternating_inter_nonempty {A B Q : Set Plane} {p q w₁ w₂ : Plane}
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂) (hside : Q \ {w₁, w₂} ⊆ farRegion C.carrier y)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty := by
  refine h.arc_inter_cover_nonempty hQ hside (hA ▸ hw₁.1) ?_ (hB ▸ hw₂.1) ?_
  · rw [hB]; exact fun hmem => hw₁.2 (hAB ▸ Set.mem_inter hw₁.1 hmem)
  · rw [hA]; exact fun hmem => hw₂.2 (hAB ▸ Set.mem_inter hmem hw₂.1)

/-- **Corollary 2.9 with "the same side" read as "the same connected component".** -/
theorem alternating_inter_nonempty_of_same_side {A B Q : Set Plane} {p q w₁ w₂ z : Plane}
    (hz : z ∈ cover K) (hzC : z ∉ C.carrier)
    (hA : C.arc a k = A) (hB : C.arc (a + k) (m + 3 - k) = B)
    (hAB : A ∩ B = ({p, q} : Set Plane))
    (hQ : IsArcBetween Q w₁ w₂)
    (hside : Q \ {w₁, w₂} ⊆ connectedComponentIn C.carrierᶜ z)
    (hw₁ : w₁ ∈ A \ ({p, q} : Set Plane)) (hw₂ : w₂ ∈ B \ ({p, q} : Set Plane)) :
    (Q ∩ cover K).Nonempty :=
  h.alternating_inter_nonempty hA hB hAB hQ
    (hside.trans (h.connectedComponentIn_cover_eq hz hzC).subset) hw₁ hw₂

end IsPrePolygonalCrosscut

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {x y : Fin 3 → Plane} {e : Fin 3 → Fin 3 → β}
variable {drawing : β → ℝ → Plane} {s : Fin 3} {R : Set Plane}

/-! ## The six-cycle and one remaining edge, as a crosscut

`Graph.IsHexCrosscut` of `Schoenflies/Graph/K33Planar.lean` is the same statement with
`Schoenflies.ClosedPolygon` for `Schoenflies.PrePolygon`; the change is what removes the corner
condition on the two cut points, which is the whole of the remaining gap. -/

/-- **The six-cycle and one remaining edge, realized as a polygonal crosscut**, with the two cut
points wherever the drawing put them. -/
def IsPreHexCrosscut (drawing : β → ℝ → Plane) (e : Fin 3 → Fin 3 → β) (s : Fin 3) : Prop :=
  ∃ (m m₁ m₂ : ℕ) (C : PrePolygon m) (J₁ : PrePolygon m₁) (J₂ : PrePolygon m₂)
    (K : List Piece) (a : ZMod (m + 3)) (k : ℕ) (yref : Plane),
      C.carrier = hexSet drawing e ∧
      C.arc a k = edgesCover drawing (arcA e s) ∧
      C.arc (a + k) (m + 3 - k) = edgesCover drawing (arcB e s) ∧
      cover K = edgeArc drawing (e s (s + 1)) ∧
      IsPrePolygonalCrosscut C J₁ J₂ K a k yref

namespace IsK33Config

/-- **The crosscut exists, unconditionally, for any polygonal drawing.** The six-cycle is
realized as a `Schoenflies.PrePolygon` cut at the two ends of the remaining edge — possible
because a `PrePolygon` may have a vertex wherever one likes — and the two closed curves the
remaining edge forms with the two halves are then *built* from that realization and from one
presentation of the remaining edge, rather than found independently. That is what makes the three
edge lists agree, and it is why no matching lemma, and hence no general position, is needed. -/
theorem isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) (s : Fin 3) :
    IsPreHexCrosscut drawing e s := by
  have hpq : x s ≠ y (s + 1) := h.x_ne_y s (s + 1)
  have hA1 := h.arcA_isArcBetween hd s
  have hA2 := h.arcB_isArcBetween hd s
  have hCh := hd.edge_isArcBetween (h.isLink s (s + 1))
  have hinterA := h.chord_inter_arcA hd s
  have hinterB := h.chord_inter_arcB hd s
  have hPch : IsPolygonal (edgeArc drawing (e s (s + 1))) :=
    hpoly _ (h.isLink s (s + 1)).edge_mem
  have hP1 : IsPolygonal (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    (h.isPolygonal_arcA hd hpoly s).union hPch ⟨x s, hA1.left_mem, hCh.left_mem⟩
  have hJ1 : IsJordanCurve (edgesCover drawing (arcA e s) ∪ edgeArc drawing (e s (s + 1))) :=
    IsJordanCurve.of_two_arcs hA1 hCh.reverse fun z hz1 hz2 => by
      have hz : z ∈ ({x s, y (s + 1)} : Set Plane) := hinterA ▸ ⟨hz1, hz2⟩
      simpa using hz
  -- The six-cycle, cut at the two ends of the remaining edge.
  obtain ⟨m, C, a, k, hCcar, hk1, hk2, hCa, hCak, hCarc1, hCarc2⟩ :=
    exists_prePolygon_arcs_oriented (h.hexagon_isJordanCurve hd) (h.isPolygonal_hexSet hd hpoly)
      (h.x_mem_hexSet hd s) (h.y_mem_hexSet hd (s + 1)) hpq hA1 hA2
      (arcs_union (drawing := drawing) (e := e) s) (h.arcs_inter hd s)
  -- The remaining edge, as the second arc of the curve it forms with the first half.
  obtain ⟨m₁, D, b, l, -, hl1, hl2, hDb, hDbl, hDarc1, hDarc2⟩ :=
    exists_prePolygon_arcs_oriented hJ1 hP1 (Or.inl hA1.left_mem) (Or.inl hA1.right_mem) hpq
      hA1 hCh rfl hinterA
  set c : ZMod (m₁ + 3) := b + (l : ZMod (m₁ + 3)) with hc
  set r : ℕ := m₁ + 3 - l with hr
  have hwrapD : c + (r : ZMod (m₁ + 3)) = b := zmod_add_sub_cancel (by omega) b
  have hDc : D.vertex c = y (s + 1) := hDbl
  have hDcr : D.vertex (c + (r : ZMod (m₁ + 3))) = x s := by rw [hwrapD]; exact hDb
  have hKcover : cover (D.arcPieces c r) = edgeArc drawing (e s (s + 1)) := hDarc2
  have hKinter : C.arc a k ∩ D.arc c r
      = ({C.vertex a, C.vertex (a + (k : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc1, hDarc2, hCa, hCak]; exact hinterA
  -- The first spliced curve: the first half of the six-cycle, then the remaining edge.
  obtain ⟨n₁, J₁, hJ₁p⟩ := PrePolygon.exists_splice C D hk1 hk2 (by omega) (by omega)
    (by rw [hDc, hCak]) (by rw [hDcr, hCa]) hKinter
  -- The second spliced curve, with the remaining edge traversed the other way.
  have hwrapC : a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)) = a :=
    zmod_add_sub_cancel (by omega) a
  set c' : ZMod (m₁ + 3) := -c - (r : ZMod (m₁ + 3)) with hc'
  have hDrev1 : D.reverse.vertex c' = x s := by
    rw [PrePolygon.reverse_vertex, hc', show -(-c - (r : ZMod (m₁ + 3))) = c + (r : ZMod (m₁ + 3))
      by ring]
    exact hDcr
  have hDrev2 : D.reverse.vertex (c' + (r : ZMod (m₁ + 3))) = y (s + 1) := by
    rw [PrePolygon.reverse_vertex, hc',
      show -(-c - (r : ZMod (m₁ + 3)) + (r : ZMod (m₁ + 3))) = c by ring]
    exact hDc
  have hKinter' : C.arc (a + (k : ZMod (m + 3))) (m + 3 - k) ∩ D.reverse.arc c' r
      = ({C.vertex (a + (k : ZMod (m + 3))),
          C.vertex (a + (k : ZMod (m + 3)) + ((m + 3 - k : ℕ) : ZMod (m + 3)))} : Set Plane) := by
    rw [hCarc2, hc', D.reverse_arc c r, hDarc2, hwrapC, hCa, hCak, Set.pair_comm]
    exact hinterB
  obtain ⟨n₂, J₂, hJ₂p⟩ := PrePolygon.exists_splice C D.reverse (a := a + (k : ZMod (m + 3)))
    (k := m + 3 - k) (b := c') (l := r) (by omega) (by omega) (by omega) (by omega)
    (by rw [hDrev1, hwrapC, hCa]) (by rw [hDrev2, hCak]) hKinter'
  -- The reference point, and the two "meets" clauses.
  have hsep : IsSeparating (hexSet drawing e) := hCcar ▸ C.isSeparating_carrier
  obtain ⟨yref, hyref, hdisj⟩ := h.exists_reference_point hd hsep s
  refine ⟨m, n₁, n₂, C, J₁, J₂, D.arcPieces c r, a, k, yref, hCcar, hCarc1, hCarc2, hKcover,
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hJ₁p]
  · rw [hJ₂p]
    exact SameEdges.append (SameEdges.refl _) (D.sameEdges_reverse_arcPieces c r)
  · rw [hKcover, hCcar, hCarc1, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcA hd s
  · rw [hKcover, hCcar, hCarc2, h.chord_inter_hexSet hd s]
    exact h.endpoints_subset_arcB hd s
  · rw [hCcar]; exact hyref
  · rw [hKcover, hCcar]; exact hdisj

/-! ### The contradiction -/

/-- **The two remaining edges indexed by `s` and `s + 1` cannot lie in one region.** Their four
ends alternate around the six-cycle, so `cor:alternating-crosscuts` makes them meet; but distinct
edges of a plane graph meet only at shared vertices, and these two share none. -/
theorem false_of_isPreHexCrosscut (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hcross : IsPreHexCrosscut drawing e s) (hsep : IsSeparating (hexSet drawing e))
    (hR : IsRegionOf (hexSet drawing e) R)
    (h1 : openArc (drawing (e s (s + 1))) ⊆ R)
    (h2 : openArc (drawing (e (s + 1) (s + 1 + 1))) ⊆ R) : False := by
  obtain ⟨m, m₁, m₂, C, J₁, J₂, K, a, k, yref, hcar, hA, hB, hK, hcc⟩ := hcross
  obtain ⟨z, hz⟩ := chord_openArc_nonempty (drawing := drawing) (e := e) s
  have hzK : z ∈ cover K := by rw [hK]; exact h.chord_openArc_subset_edgeArc hd s hz
  have hzC : z ∉ C.carrier := by rw [hcar]; exact h.chord_openArc_subset_compl hd s hz
  have hzR : z ∈ R := h1 hz
  have hside : edgeArc drawing (e (s + 1) (s + 1 + 1)) \ ({x (s + 1), y (s + 1 + 1)} : Set Plane)
      ⊆ connectedComponentIn C.carrierᶜ z := by
    rw [hcar, hR.connectedComponentIn_eq hsep hzR, ← h.chord_openArc_eq hd (s + 1)]
    exact h2
  obtain ⟨w, hw₁, hw₂⟩ := hcc.alternating_inter_nonempty_of_same_side hzK hzC hA hB
    (h.arcs_inter hd s) (hd.edge_isArcBetween (h.isLink (s + 1) (s + 1 + 1))) hside
    (h.x_succ_mem_arcA hd s) (h.y_succ_mem_arcB hd s)
  have hs1 : ∀ s : Fin 3, s + 1 ≠ s := by decide
  have hdis := h.chords_disjoint hd (hs1 s)
  rw [Set.eq_empty_iff_forall_notMem] at hdis
  exact hdis w ⟨hw₁, by rwa [hK] at hw₂⟩

/-- **`lem:k33` for a drawing that is already polygonal, with nothing assumed.** -/
theorem false_of_polygonal (h : IsK33Config G x y e) (hd : IsDrawing G drawing)
    (hpoly : ∀ f ∈ E(G), IsPolygonal (edgeArc drawing f)) : False := by
  have hsep : IsSeparating (hexSet drawing e) := by
    obtain ⟨_, _, _, C, _, _, _, _, _, _, hcar, _⟩ := h.isPreHexCrosscut hd hpoly 0
    exact hcar ▸ C.isSeparating_carrier
  obtain ⟨s, t, hst, R, hR, h1, h2⟩ := h.exists_two_chords_same_region hd hsep
  have hpair : ∀ s t : Fin 3, s ≠ t → t = s + 1 ∨ s = t + 1 := by decide
  rcases hpair s t hst with rfl | rfl
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly s) hsep hR h1 h2
  · exact h.false_of_isPreHexCrosscut hd (h.isPreHexCrosscut hd hpoly t) hsep hR h2 h1

/-- **Lemma 3.10 (nonplanarity of `K(3,3)`), with no hypothesis left.** A finite graph carrying a
copy of `K(3,3)` has no plane drawing.

`lem:polygonal-redrawing` replaces an arbitrary drawing by a polygonal one on the same graph and
the same vertices; the contradiction is then `false_of_polygonal`. This is
`Graph.IsK33Config.not_isDrawing` of `Schoenflies/Graph/K33Planar.lean` with its realization
hypothesis discharged, and `Graph.IsK33Config.not_isDrawing_of_bendable` of
`Schoenflies/Graph/K33Closed.lean` with `Graph.Bendable` discharged: no drawing has to be bent,
because the crosscut no longer needs the six vertices to be corners. -/
theorem not_exists_isDrawing [G.Finite] (h : IsK33Config G x y e) :
    ¬ ∃ dr : β → ℝ → Plane, IsDrawing G dr := by
  rintro ⟨dr, hdr⟩
  obtain ⟨dr', hdr', hpoly'⟩ := polygonal_redrawing G dr hdr
  exact h.false_of_polygonal hdr' hpoly'

end IsK33Config

/-- **`lem:k33` for nine arcs**, unconditionally: no nine arcs in the plane meet only where a
`K(3,3)` forces them to. -/
theorem IsArcK33.elim {P : Fin 3 → Fin 3 → Set Plane} (h : IsArcK33 x y P) : False :=
  h.isK33Config.not_exists_isDrawing ⟨h.arcDrawing, h.isDrawing⟩

/-- **Corollary 3.11 (subdivisions of `K(3,3)`), unconditionally.** No subdivision of `K(3,3)`
has a plane drawing. -/
theorem IsK33Subdivision.elim {H : Graph Plane β} {W : Fin 3 → Fin 3 → List β}
    (hd : IsDrawing H drawing) (h : IsK33Subdivision H x y W) : False :=
  (h.isArcK33 hd).elim

/-- **The headline: `K(3,3)` has no plane drawing.** Stated for the concrete graph
`Graph.k33Graph x y`, whose nine edges are the index pairs, with nothing assumed beyond the six
points being six distinct points of the plane. -/
theorem k33Graph_not_exists_isDrawing (x y : Fin 3 → Plane) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    ¬ ∃ dr : Fin 3 × Fin 3 → ℝ → Plane, IsDrawing (k33Graph x y) dr :=
  IsK33Config.not_exists_isDrawing ⟨k33Graph_isLink x y, hx, hy, hxy⟩

end Graph
