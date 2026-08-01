/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SimpleArc
import Schoenflies.PolygonBridge
import Schoenflies.TwoArcs

/-!
# Realizing a polygonal Jordan curve as a `ClosedPolygon`

The blueprint's "simple closed polygonal curve" is set-theoretic: a `IsJordanCurve` that is
also `IsPolygonal`, with no condition on vertices at all. The development works instead with
`Schoenflies.ClosedPolygon`, a cyclic vertex list carrying a `corner` field — no three
consecutive vertices collinear. That field is a *presentation* condition, strictly stronger
than the blueprint's notion, and until now nothing said that a set-level polygonal Jordan
curve admits such a presentation. This module proves it.

## Blueprint

* `Schoenflies.PrePolygon` — a `ClosedPolygon` less the `corner` field: the blueprint's simple
  closed polygonal curve *presented by a vertex list*, redundant vertices allowed.
* `Schoenflies.PrePolygon.deleteLast`, `Schoenflies.exists_closedPolygon_of_prePolygon` — the
  blueprint's opening move in Lemma 1.8, "delete redundant vertices at which two consecutive
  edges are collinear", as an operation rather than an invariant.
* `Schoenflies.exists_closedPolygon` — §1: every simple closed polygonal curve, in the
  blueprint's set-level sense, is the carrier of a `ClosedPolygon`.
-/

open Metric Set

namespace Schoenflies

open Plane

/-! ## Polygons before normalization

`PrePolygon` is `ClosedPolygon` with the `corner` field removed. Everything the curve bridge of
`Schoenflies/PolygonBridge.lean` proves about a `ClosedPolygon` — that its carrier is a Jordan
curve, that it is polygonal — uses only `vertex_inj` and `edges_meet`, so it is already true
here; what `corner` buys is the germ argument of the strip lemma, and nothing else. -/

/-- A simple closed polygonal curve presented by its cyclic vertex list, with redundant
vertices allowed: `ClosedPolygon` less its `corner` field. -/
structure PrePolygon (m : ℕ) where
  /-- The vertices, in cyclic order. -/
  vertex : ZMod (m + 3) → Plane
  /-- The vertices are distinct. -/
  vertex_inj : Function.Injective vertex
  /-- Simplicity: an edge meets any other edge only at one of its own endpoints. -/
  edges_meet : ∀ i j : ZMod (m + 3), i ≠ j →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) ⊆
      {vertex i, vertex (i + 1)}

namespace PrePolygon

variable {m : ℕ} (P : PrePolygon m)

/-- The edge leaving vertex `i`. -/
def edge (i : ZMod (m + 3)) : Set Plane := segment ℝ (P.vertex i) (P.vertex (i + 1))

/-- The carrier: the union of the edges. -/
def carrier : Set Plane := ⋃ i, P.edge i

variable {P}

theorem edge_subset_carrier (i : ZMod (m + 3)) : P.edge i ⊆ P.carrier := Set.subset_iUnion _ i

theorem vertex_mem_carrier (i : ZMod (m + 3)) : P.vertex i ∈ P.carrier :=
  edge_subset_carrier i (left_mem_segment ℝ _ _)

theorem vertex_ne_succ (i : ZMod (m + 3)) : P.vertex i ≠ P.vertex (i + 1) := fun h =>
  ClosedPolygon.succ_ne_self i (P.vertex_inj h).symm

end PrePolygon

/-- A `ClosedPolygon` read as a `PrePolygon`: forget the `corner` field. -/
def ClosedPolygon.toPre {m : ℕ} (P : ClosedPolygon m) : PrePolygon m :=
  ⟨P.vertex, P.vertex_inj, P.edges_meet⟩

@[simp] theorem ClosedPolygon.carrier_toPre {m : ℕ} (P : ClosedPolygon m) :
    P.toPre.carrier = P.carrier := rfl

/-! ## Small facts about the cyclic index

`ZMod (m + 3)` has at least three elements; `0`, `1` and `2` are distinct, which is what makes
a vertex, its successor and its predecessor three different vertices. -/

namespace PrePolygon

variable {m : ℕ}

theorem two_ne_zero' : (2 : ZMod (m + 3)) ≠ 0 := by
  intro h
  rw [show (2 : ZMod (m + 3)) = ((2 : ℕ) : ZMod (m + 3)) by norm_num,
    ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (by norm_num) h
  omega

theorem pred_ne_succ (i : ZMod (m + 3)) : i - 1 ≠ i + 1 := fun h =>
  two_ne_zero' (m := m) (by linear_combination -h)

theorem val_one_eq : (1 : ZMod (m + 3)).val = 1 := by
  rw [show (1 : ZMod (m + 3)) = ((1 : ℕ) : ZMod (m + 3)) by norm_num]
  exact ZMod.val_cast_of_lt (by omega)

/-- The successor of a non-final index is the next one. -/
theorem val_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : (j + 1).val = j.val + 1 := by
  rw [ZMod.val_add, val_one_eq, Nat.mod_eq_of_lt h]

/-- The successor of the final index wraps to `0`. -/
theorem val_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : (j + 1).val = 0 := by
  rw [ZMod.val_add, val_one_eq, h, Nat.mod_self]

/-! ## Rotation

Reading the same cyclic list from a different starting vertex. It is used once, to bring the
vertex that is about to be deleted to the end of the list. -/

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : PrePolygon m) (a : ZMod (m + 3)) : PrePolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)

@[simp] theorem rotate_vertex (P : PrePolygon m) (a j : ZMod (m + 3)) :
    (P.rotate a).vertex j = P.vertex (a + j) := rfl

/-- Rotating does not move the curve: the edges are the same, listed from elsewhere. -/
theorem carrier_rotate (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.rotate a).carrier = P.carrier := by
  have hedge : ∀ j : ZMod (m + 3), (P.rotate a).edge j = P.edge (a + j) := by
    intro j
    rw [edge, edge, rotate_vertex, rotate_vertex, show a + (j + 1) = a + j + 1 by ring]
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · rw [hedge]; exact edge_subset_carrier _
  · refine le_trans (le_of_eq ?_) (edge_subset_carrier (P := P.rotate a) (i - a))
    rw [hedge, add_sub_cancel]

/-! ## Deleting the last vertex

The blueprint's opening move in the strip lemma. The vertex to be deleted is brought to the end
of the list by `rotate`, so only that one case has to be treated. `emb` is the inclusion of the
shortened index set into the old one: the same numeral, one modulus smaller. -/

section Delete

variable {m : ℕ}

/-- An index of the shortened list, read in the original one: the same numeral. -/
def emb (j : ZMod (m + 3)) : ZMod (m + 1 + 3) := ((j.val : ℕ) : ZMod (m + 1 + 3))

theorem neg_one_eq_cast : (-1 : ZMod (m + 1 + 3)) = ((m + 3 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem neg_two_eq_cast : (-1 - 1 : ZMod (m + 1 + 3)) = ((m + 2 : ℕ) : ZMod (m + 1 + 3)) := by
  have h0 : ((m + 1 + 3 : ℕ) : ZMod (m + 1 + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination -h0

theorem emb_injective : Function.Injective (emb (m := m)) := fun i j h =>
  ZMod.val_injective _ (ClosedPolygon.natCast_inj (m := m + 1)
    (by have := ZMod.val_lt i; omega) (by have := ZMod.val_lt j; omega) h)

theorem emb_succ_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) : emb (j + 1) = emb j + 1 := by
  rw [emb, emb, val_succ_of_lt h, Nat.cast_add, Nat.cast_one]

theorem emb_succ_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb (j + 1) = 0 := by
  rw [emb, val_succ_last h, Nat.cast_zero]

theorem emb_eq_last {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) : emb j = -1 - 1 := by
  rw [emb, neg_two_eq_cast, show j.val = m + 2 by omega]

/-- Below the last index, `emb` misses both the deleted vertex and its predecessor. -/
theorem emb_ne_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    emb j ≠ -1 ∧ emb j ≠ -1 - 1 := by
  have hj := ZMod.val_lt j
  constructor
  · rw [neg_one_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 3)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)
  · rw [neg_two_eq_cast]
    exact fun he => (by omega : j.val ≠ m + 2)
      (ClosedPolygon.natCast_inj (m := m + 1) (by omega) (by omega) he)

/-- Every index other than the deleted vertex and its predecessor is hit by `emb`. -/
theorem exists_emb_eq {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    ∃ j : ZMod (m + 3), j.val + 1 < m + 3 ∧ emb j = i := by
  have hi := ZMod.val_lt i
  have hne1 : i.val ≠ m + 3 := by
    rintro he
    exact h1 (by rw [neg_one_eq_cast, ← he, ZMod.natCast_rightInverse i])
  have hne2 : i.val ≠ m + 2 := by
    rintro he
    exact h2 (by rw [neg_two_eq_cast, ← he, ZMod.natCast_rightInverse i])
  refine ⟨(i.val : ZMod (m + 3)), ?_, ?_⟩
  · rw [ZMod.val_cast_of_lt (show i.val < m + 3 by omega)]; omega
  · rw [emb, ZMod.val_cast_of_lt (show i.val < m + 3 by omega), ZMod.natCast_rightInverse i]

variable (P : PrePolygon (m + 1))

/-- The vertex list with its last entry dropped. -/
def dropVertex (j : ZMod (m + 3)) : Plane := P.vertex (emb j)

variable {P}

theorem dropVertex_injective : Function.Injective P.dropVertex :=
  fun _ _ h => emb_injective (P.vertex_inj h)

/-- Away from the deleted vertex the edges are unchanged. -/
theorem dropVertex_edge_of_lt {j : ZMod (m + 3)} (h : j.val + 1 < m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (emb j) := by
  rw [dropVertex, dropVertex, emb_succ_of_lt h, edge]

/-- The final edge of the shortened list is the union of the two edges at the deleted vertex —
which is a segment precisely because the deleted vertex is interior to it. -/
theorem dropVertex_edge_last
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    {j : ZMod (m + 3)} (h : j.val + 1 = m + 3) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) = P.edge (-1 - 1) ∪ P.edge (-1) := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  rw [dropVertex, dropVertex, emb_succ_last h, emb_eq_last h, edge, edge, e1, e2]
  exact segment_split (openSegment_subset_segment ℝ _ _ hcol)

/-- The deleted vertex lies on no edge but its own two: `edges_meet` puts a meeting point at an
end of the other edge, and the deleted vertex is an end only of the two edges at it. -/
theorem vertex_last_notMem_edge {i : ZMod (m + 1 + 3)} (h1 : i ≠ -1) (h2 : i ≠ -1 - 1) :
    P.vertex (-1) ∉ P.edge i := by
  intro hmem
  have hself : P.vertex (-1) ∈ P.edge (-1) := left_mem_segment ℝ _ _
  have hme := P.edges_meet i (-1) h1 (Set.mem_inter hmem hself)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme
  rcases hme with he | he
  · exact h1 (P.vertex_inj he).symm
  · exact h2 (by linear_combination -P.vertex_inj he)

/-- **Simplicity survives the deletion.** The only new edge is the merged one, and the point
that has to be kept out of it — the deleted vertex — lies on no other edge at all. -/
theorem dropVertex_edges_meet
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0))
    (j k : ZMod (m + 3)) (hjk : j ≠ k) :
    segment ℝ (P.dropVertex j) (P.dropVertex (j + 1)) ∩
      segment ℝ (P.dropVertex k) (P.dropVertex (k + 1)) ⊆
      {P.dropVertex j, P.dropVertex (j + 1)} := by
  have e1 : (-1 - 1 : ZMod (m + 1 + 3)) + 1 = -1 := by ring
  have e2 : (-1 : ZMod (m + 1 + 3)) + 1 = 0 := by ring
  have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
  have hkv : k.val + 1 ≤ m + 3 := ZMod.val_lt k
  rcases eq_or_lt_of_le hjv with hj | hj
  · -- `j` is the last index, so its edge is the merged one.
    have hdj : P.dropVertex j = P.vertex (-1 - 1) := by rw [dropVertex, emb_eq_last hj]
    have hdj1 : P.dropVertex (j + 1) = P.vertex 0 := by rw [dropVertex, emb_succ_last hj]
    rcases eq_or_lt_of_le hkv with hk | hk
    · exact absurd (ZMod.val_injective _ (by omega : j.val = k.val)) hjk
    obtain ⟨hk1, hk2⟩ := emb_ne_of_lt hk
    have hout := vertex_last_notMem_edge (P := P) hk1 hk2
    rw [dropVertex_edge_last hcol hj, dropVertex_edge_of_lt hk, hdj, hdj1]
    rintro x ⟨hx1 | hx1, hx2⟩
    · have hme := P.edges_meet _ _ (fun h => hk2 h.symm) (Set.mem_inter hx1 hx2)
      rw [e1] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact hme.imp id fun h => absurd (h ▸ hx2) hout
    · have hme := P.edges_meet _ _ (fun h => hk1 h.symm) (Set.mem_inter hx1 hx2)
      rw [e2] at hme
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme ⊢
      exact Or.inr (hme.resolve_left fun h => absurd (h ▸ hx2) hout)
  · -- `j` is an ordinary index, so its edge is unchanged.
    obtain ⟨hj1, hj2⟩ := emb_ne_of_lt hj
    have hdj : P.dropVertex j = P.vertex (emb j) := rfl
    have hdj1 : P.dropVertex (j + 1) = P.vertex (emb j + 1) := by
      rw [dropVertex, emb_succ_of_lt hj]
    rw [dropVertex_edge_of_lt hj, hdj, hdj1]
    rcases eq_or_lt_of_le hkv with hk | hk
    · rw [dropVertex_edge_last hcol hk]
      rintro x ⟨hx1, hx2 | hx2⟩
      · exact P.edges_meet _ _ hj2 (Set.mem_inter hx1 hx2)
      · exact P.edges_meet _ _ hj1 (Set.mem_inter hx1 hx2)
    · rw [dropVertex_edge_of_lt hk]
      exact fun x hx => P.edges_meet _ _ (fun h => hjk (emb_injective h)) hx

/-- **The polygon with a redundant vertex deleted.** -/
def deleteLast (P : PrePolygon (m + 1))
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) : PrePolygon m where
  vertex := P.dropVertex
  vertex_inj := dropVertex_injective
  edges_meet := dropVertex_edges_meet hcol

/-- **Deleting a redundant vertex does not move the curve.** -/
theorem carrier_deleteLast
    (hcol : P.vertex (-1) ∈ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0)) :
    (deleteLast P hcol).carrier = P.carrier := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun j => ?_) (Set.iUnion_subset fun i => ?_)
  · have hjv : j.val + 1 ≤ m + 3 := ZMod.val_lt j
    rcases eq_or_lt_of_le hjv with hj | hj
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_last hcol hj]
      exact Set.union_subset (edge_subset_carrier _) (edge_subset_carrier _)
    · rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj]
      exact edge_subset_carrier _
  · by_cases hi : i = -1 ∨ i = -1 - 1
    · -- The two edges at the deleted vertex are both inside the merged one.
      set j : ZMod (m + 3) := ((m + 2 : ℕ) : ZMod (m + 3)) with hjdef
      have hj : j.val + 1 = m + 3 := by rw [hjdef, ZMod.val_cast_of_lt (by omega)]
      have hmerge : (deleteLast P hcol).edge j = P.edge (-1 - 1) ∪ P.edge (-1) :=
        dropVertex_edge_last hcol hj
      refine le_trans ?_ (le_trans (le_of_eq hmerge.symm) (edge_subset_carrier j))
      rcases hi with rfl | rfl
      · exact Set.subset_union_right
      · exact Set.subset_union_left
    · push Not at hi
      obtain ⟨j, hj, hemb⟩ := exists_emb_eq hi.1 hi.2
      have : (deleteLast P hcol).edge j = P.edge i := by
        rw [show (deleteLast P hcol).edge j = _ from dropVertex_edge_of_lt hj, hemb]
      exact le_trans (le_of_eq this.symm) (edge_subset_carrier j)

end Delete

/-! ## Recognising a redundant vertex

The `corner` field is `det ≠ 0` at every vertex. Where it fails the vertex is *interior* to the
segment joining its two neighbours, never an endpoint of it. That is the geometric content of
`edges_meet`: two edges leaving a vertex in the *same* direction would overlap in a
nondegenerate segment, and `edges_meet` would then put a whole segment inside a two-point
set. -/

/-- A nondegenerate segment is not contained in the pair of its own endpoints. -/
theorem exists_mem_segment_ne {a b : Plane} (hab : a ≠ b) :
    ∃ p ∈ segment ℝ a b, p ≠ a ∧ p ≠ b := by
  have hmem : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ∈ openSegment ℝ a b :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  refine ⟨_, openSegment_subset_segment ℝ a b hmem, ?_, ?_⟩
  · intro h
    rw [h] at hmem
    exact hab (left_mem_openSegment_iff.1 hmem)
  · intro h
    rw [h] at hmem
    exact hab (right_mem_openSegment_iff.1 hmem)

/-- **Three collinear points meeting only at the shared one are in the order that makes the
middle one interior.** The alternative — the two segments running the same way out of `b` —
makes them overlap in a nondegenerate segment, which the meeting hypothesis forbids. -/
theorem mem_openSegment_of_det_eq_zero' {a b c : Plane} (hab : a ≠ b) (hcb : c ≠ b)
    (hmeet : segment ℝ a b ∩ segment ℝ b c ⊆ {a, b})
    (h : det (a - b) (c - b) = 0) : b ∈ openSegment ℝ a c := by
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  obtain ⟨r, hr⟩ := (det_eq_zero_iff_smul _ _ hab').1 h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, sub_eq_zero] at hr
    exact hcb hr
  have hcexp : c = b + r • (a - b) := by linear_combination (norm := module) hr
  have hrneg : r < 0 := by
    rcases lt_trichotomy r 0 with hlt | heq | hgt
    · exact hlt
    · exact absurd heq hr0
    exfalso
    -- A short step out of `b` towards `a` is then also a step towards `c`.
    have hμpos : 0 < min 1 r / 2 := by positivity
    set μ : ℝ := min 1 r / 2 with hμdef
    have hμ1 : μ < 1 := by
      have h1 : min 1 r ≤ 1 := min_le_left _ _
      rw [hμdef]; linarith
    have hμler : μ / r < 1 := by
      rw [div_lt_one hgt]
      have h1 : min 1 r ≤ r := min_le_right _ _
      rw [hμdef]; linarith
    have hμr : μ / r * r = μ := div_mul_cancel₀ _ (ne_of_gt hgt)
    have hz₁ : μ • a + (1 - μ) • b ∈ segment ℝ a b :=
      ⟨μ, 1 - μ, hμpos.le, by linarith, by ring, rfl⟩
    have hz₂ : μ • a + (1 - μ) • b ∈ segment ℝ b c := by
      refine ⟨1 - μ / r, μ / r, by linarith, by positivity, by ring, ?_⟩
      have expand : (1 - μ / r) • b + (μ / r) • (b + r • (a - b))
          = (μ / r * r) • a + (1 - μ / r * r) • b := by module
      rw [hcexp, expand, hμr]
    have hmem := hmeet ⟨hz₁, hz₂⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with he | he
    · have hkey : (1 - μ) • (a - b) = 0 := by linear_combination (norm := module) -he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact (by linarith : (0 : ℝ) < 1 - μ).ne' h'
      · exact hab' h'
    · have hkey : μ • (a - b) = 0 := by linear_combination (norm := module) he
      rcases smul_eq_zero.1 hkey with h' | h'
      · exact hμpos.ne' h'
      · exact hab' h'
  -- Opposite directions: the vertex is a strict convex combination of its neighbours.
  have hden : (0 : ℝ) < 1 - r := by linarith
  refine ⟨-r / (1 - r), 1 / (1 - r), div_pos (by linarith) hden, div_pos one_pos hden,
    by field_simp; ring, ?_⟩
  have expand : (-r / (1 - r)) • a + (1 / (1 - r)) • (b + r • (a - b))
      = (-r / (1 - r) + 1 / (1 - r) * r) • a + (1 / (1 - r) - 1 / (1 - r) * r) • b := by module
  rw [hcexp, expand, show -r / (1 - r) + 1 / (1 - r) * r = 0 by field_simp; ring,
    show (1 : ℝ) / (1 - r) - 1 / (1 - r) * r = 1 by field_simp, zero_smul, one_smul, zero_add]

variable {m : ℕ} {P : PrePolygon m}

/-- **A redundant vertex is interior to the segment joining its neighbours.** -/
theorem mem_openSegment_of_det_eq_zero (i : ZMod (m + 3))
    (h : det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) = 0) :
    P.vertex i ∈ openSegment ℝ (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  have hpred : i - 1 + 1 = i := sub_add_cancel i 1
  have hne : i - 1 ≠ i := fun he =>
    ClosedPolygon.succ_ne_self (i - 1) (by rw [hpred]; exact he.symm)
  have hmeet := P.edges_meet (i - 1) i hne
  rw [hpred] at hmeet
  exact mem_openSegment_of_det_eq_zero' (fun he => hne (P.vertex_inj he))
    (fun he => ClosedPolygon.succ_ne_self i (P.vertex_inj he)) hmeet h

/-! ## Normalization

Delete redundant vertices until none is left. Each deletion shortens the list by one, and the
list can never shrink below three vertices: a triangle with a redundant vertex would have one
edge inside another, which `edges_meet` forbids. -/

/-- A three-vertex polygon has no redundant vertex: were the last one interior to the segment
joining the other two, the edge before it would lie inside the edge opposite it. -/
theorem not_collinear_triangle (P : PrePolygon 0) :
    P.vertex (-1) ∉ openSegment ℝ (P.vertex (-1 - 1)) (P.vertex 0) := by
  intro hcol
  have e1 : (-1 - 1 : ZMod (0 + 3)) + 1 = -1 := by decide
  have e2 : (-1 : ZMod (0 + 3)) ≠ -1 - 1 := by decide
  have hsplit : segment ℝ (P.vertex (-1 - 1)) (P.vertex 0)
      = segment ℝ (P.vertex (-1 - 1)) (P.vertex (-1)) ∪ segment ℝ (P.vertex (-1)) (P.vertex 0) :=
    segment_split (openSegment_subset_segment ℝ _ _ hcol)
  -- The edge before the redundant vertex sits inside the edge opposite it.
  have hsub : P.edge (-1 - 1) ⊆ P.edge (-1 - 1 - 1) := by
    have e3 : (-1 - 1 - 1 : ZMod (0 + 3)) = 0 := by decide
    have e4 : (0 : ZMod (0 + 3)) + 1 = -1 - 1 := by decide
    rw [edge, edge, e1, e3, e4, segment_symm ℝ (P.vertex 0) (P.vertex (-1 - 1)), hsplit]
    exact Set.subset_union_left
  obtain ⟨p, hp, hp1, hp2⟩ := exists_mem_segment_ne (P.vertex_ne_succ (-1 - 1))
  rcases P.edges_meet (-1 - 1) (-1 - 1 - 1) (by decide) ⟨hp, hsub hp⟩ with h | h
  exacts [hp1 h, hp2 h]

/-- **Every `PrePolygon` normalizes to a `ClosedPolygon` with the same carrier.** This is the
blueprint's "delete redundant vertices at which two consecutive edges are collinear", run to
completion; the induction is on the number of vertices, which each deletion lowers by one. -/
theorem exists_closedPolygon_of_prePolygon :
    ∀ (m : ℕ) (P : PrePolygon m), ∃ (m' : ℕ) (P' : ClosedPolygon m'), P'.carrier = P.carrier := by
  intro m
  induction m with
  | zero =>
    intro P
    by_cases hc : ∀ i : ZMod (0 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨0, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      refine absurd ?_ (not_collinear_triangle (P.rotate (i + 1)))
      have e1 : i + 1 + (-1 : ZMod (0 + 3)) = i := by ring
      have e2 : i + 1 + (-1 - 1 : ZMod (0 + 3)) = i - 1 := by ring
      have e3 : i + 1 + (0 : ZMod (0 + 3)) = i + 1 := by ring
      rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
      exact mem_openSegment_of_det_eq_zero i hi
  | succ m ih =>
    intro P
    by_cases hc : ∀ i : ZMod (m + 1 + 3),
        det (P.vertex (i - 1) - P.vertex i) (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨m + 1, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, rfl⟩
    · push Not at hc
      obtain ⟨i, hi⟩ := hc
      have hcol : (P.rotate (i + 1)).vertex (-1) ∈
          openSegment ℝ ((P.rotate (i + 1)).vertex (-1 - 1)) ((P.rotate (i + 1)).vertex 0) := by
        have e1 : i + 1 + (-1 : ZMod (m + 1 + 3)) = i := by ring
        have e2 : i + 1 + (-1 - 1 : ZMod (m + 1 + 3)) = i - 1 := by ring
        have e3 : i + 1 + (0 : ZMod (m + 1 + 3)) = i + 1 := by ring
        rw [rotate_vertex, rotate_vertex, rotate_vertex, e1, e2, e3]
        exact mem_openSegment_of_det_eq_zero i hi
      obtain ⟨m', P', hP'⟩ := ih (deleteLast (P.rotate (i + 1)) hcol)
      exact ⟨m', P', by rw [hP', carrier_deleteLast, carrier_rotate]⟩
end PrePolygon

end Schoenflies
