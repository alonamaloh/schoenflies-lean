/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FaceCyclesProof
import Schoenflies.PrePolygonSep

/-!
# `lem:face-cycles`, with nothing assumed

`Schoenflies/FaceCyclesProof.lean` proves `lem:face-cycles` modulo one hypothesis,
`Schoenflies.CrosscutSplitsRegion`: the exhaustion clause of `thm:polygonal-crosscut` for a
crosscut whose two endpoints are *arbitrary points* of the curve. This module proves that
hypothesis and restates the lemma without it (`Graph.face_cycles'`,
`Graph.IsDrawing.hasFaceCycles_union'`).

## Why the crosscut theorem had to be redone, and how far

`main`'s Theorem 2.8 (`Schoenflies.IsPolygonalCrosscut`) cuts a `ClosedPolygon` at two of *its
vertices*, and `Schoenflies.ClosedPolygon.isCornerAt_vertex` says a point at which the curve runs
straight is a vertex of no `ClosedPolygon` presentation of it. In the ear induction the two cut
points are graph vertices, at which the two cycle edges may leave along opposite rays. So the
presentation has to be `Schoenflies.PrePolygon`, which has no `corner` field, and the two `main`
hypotheses `edges₁`/`edges₂` — multiset equalities `SameEdges Jᵢ.pieces (Aᵢ ++ K)` — have to go
as well, for the reason `Schoenflies/FaceCyclesProof.lean` records: the merged curve `Aᵢ ∪ P` may
run straight through a cut point, and then no presentation of it has an edge ending there.

Both go away at once by never realizing `J₁` and `J₂` at all. The two curves of the split are
given by *literal* edge lists `Aᵢ ++ K`, so Lemma 2.7 (`Schoenflies.parity_split`) applies with
nothing to check, and only the *easy* half of Theorem 2.3 is asked of them: "points in the same
region have the same crossing count", which is Lemma 2.2
(`Schoenflies.parity_eq_of_mem_connectedComponentIn`) and needs no realization. The hard half —
the two values `0` and `1` — is needed for `J` alone, where
`Schoenflies.PrePolygon.parity_eq_one_iff` of `Schoenflies/PrePolygonSep.lean` supplies it. That
is the whole of the reduction; Lemma 2.6 (`Schoenflies.crosscut_cells`) is already stated at the
set level and is quoted unchanged.

What the presentation still has to do is put the two cut points *on* its vertex list, and that is
the one genuinely new construction here: `Schoenflies.PrePolygon.insertLastFC`, the inverse of
`Schoenflies.PrePolygon.deleteLast`. A point interior to an edge is brought to the last edge by
`Schoenflies.PrePolygon.rotate` and the edge is split in two; simplicity survives because the far
end of the split edge lies on neither half.

## For the integrator

`Schoenflies.PrePolygon.arcPiecesFC` and its API here are `Schoenflies.ClosedPolygon.arcPiecesFC` and
its API of `Schoenflies/ParitySplitting.lean` and `Schoenflies/Realization.lean` transcribed with
the structure changed — the proofs use `vertex_inj` and `edges_meet` and nothing else. The right
arrangement, as `Schoenflies/PrePolygonSep.lean` already says of `pieces`, is to prove them once
for `PrePolygon` and define the `ClosedPolygon` versions as `P.toPre.arcPiecesFC`; that needs
`PrePolygon` moved up beside `ClosedPolygon` in `Schoenflies/Strip.lean`.

Three declarations here are general and belong elsewhere:
`Schoenflies.isSeparating_of_isJordanCurve` in `Schoenflies/Realization.lean`,
`Schoenflies.IsArcBetween.ne` in `Schoenflies/Curve.lean`, and
`Schoenflies.isChainFrom_segsOf` in `Schoenflies/ParitySplitting.lean` beside
`Schoenflies.isChainFrom_pathPieces`. `Schoenflies.two_arcs_unique_of_isClosed` subsumes
`Schoenflies.two_arcs_unique` and should replace it in `Schoenflies/Realization.lean`.

Once this module is moved above `Schoenflies/FaceCyclesProof.lean`, the hypothesis
`Schoenflies.CrosscutSplitsRegion` can be deleted from `Graph.face_cycles` and
`Graph.IsDrawing.hasFaceCycles_union`, and the two primed statements at the end here dropped.

## Blueprint

* `Schoenflies.notMem_segment_left_of_mem_openSegment`,
  `…notMem_segment_right_of_mem_openSegment`, `Schoenflies.segment_inter_of_mem_openSegment` —
  the elementary geometry of cutting a segment at an interior point.
* `Schoenflies.PrePolygon.insertLastFC`, `…carrier_insertLastFC`, `…exists_insert_vertex`,
  `…exists_prePolygon_verticesFC` — a named point of a simple closed polygonal curve becomes a
  vertex of a presentation of it. This is `thm:realization` tracking prescribed points, with the
  corner hypothesis of `Schoenflies.exists_closedPolygon_corners` removed.
* `Schoenflies.PrePolygon.exists_prePolygon_split` — `thm:realization` tracking a splitting, at
  two arbitrary points of the curve.
* `Schoenflies.PrePolygon.arcPiecesFC`, `…arcFC`, `…isChainFrom_arcPiecesFC`,
  `…sameEdges_arcPieces_splitFC`, `…cover_arcPieces_unionFC`, `…arc_interFC`,
  `…arc_not_subset_endpoints`, `…arcList`, `…poly_arcList` — the two arcs of a splitting, §2.
* `Schoenflies.two_arcs_unique_of_isClosed` — the two arcs a pair of points cuts a curve into are
  determined, with the competing splitting known only to be closed and nondegenerate.
* `Schoenflies.crosscutSplitsRegion` — the exhaustion clause of `thm:polygonal-crosscut` at
  arbitrary cut points: `Schoenflies.CrosscutSplitsRegion`, proved.
* `Graph.IsDrawing.hasFaceCycles_union'` — one ear of `lem:face-cycles`, unconditionally.
* `Graph.face_cycles'` — **`lem:face-cycles`**, unconditionally.
* `Graph.IsFaceCycle.eq_inside_of_isBounded'` — "in particular, every bounded face is the
  interior of its boundary cycle".
-/
open Bornology Metric Set

namespace Schoenflies

/-! ## Cutting a segment at an interior point -/

variable {a b x : Plane}

/-- The far end is not on the near half. -/
theorem notMem_segment_left_of_mem_openSegment (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) : b ∉ segment ℝ a x := by
  intro hb
  have hxs : x ∈ segment ℝ a b := openSegment_subset_segment ℝ _ _ hx
  have h₁ : dist a b ≤ dist a x :=
    (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) hxs (by simp) hb).2
  have h₂ : dist a x ≤ dist a b :=
    (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
      (by simp) hxs).2
  have hxb : x ≠ b := by rintro rfl; exact hab (right_mem_openSegment_iff.1 hx)
  exact hxb (eq_of_dist_left_eq hab hxs (right_mem_segment ℝ a b) (le_antisymm h₂ h₁))

/-- The near end is not on the far half. -/
theorem notMem_segment_right_of_mem_openSegment (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) : a ∉ segment ℝ x b := by
  have hx' : x ∈ openSegment ℝ b a := by rwa [openSegment_symm]
  have := notMem_segment_left_of_mem_openSegment (Ne.symm hab) hx'
  rwa [segment_symm] at this

/-- The two halves of a cut segment meet only at the cut point. -/
theorem segment_inter_of_mem_openSegment (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
    segment ℝ a x ∩ segment ℝ x b ⊆ {x} := by
  have hxs : x ∈ segment ℝ a b := openSegment_subset_segment ℝ _ _ hx
  rintro z ⟨hz1, hz2⟩
  have hzs : z ∈ segment ℝ a b :=
    (convex_segment a b).segment_subset (left_mem_segment ℝ a b) hxs hz1
  have h₁ : dist a z ≤ dist a x :=
    (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) hxs (by simp) hz1).2
  have h₂ : dist a x ≤ dist a z :=
    (dist_le_of_mem_segment hab hxs (right_mem_segment ℝ a b)
      (dist_le_of_mem_segment hab (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
        (by simp) hxs).2 hz2).1
  exact eq_of_dist_left_eq hab hzs hxs (le_antisymm h₁ h₂)

namespace PrePolygon

/-! ## Inserting a vertex

`Schoenflies.PrePolygon.deleteLast` removes a vertex at which the curve runs straight; this is
the move in the other direction, and it is the reason `PrePolygon` is the right structure for a
consumer that needs named points to be vertices. The vertex is inserted at the end of the list,
so that the only edge that changes is the last one, which splits in two. -/

section Insert

variable {m : ℕ} {P : PrePolygon m} {x : Plane}

/-- The vertex family with `x` appended at the end: the old numerals name the old vertices, and
the one new index names `x`. -/
def insVertexFC (P : PrePolygon m) (x : Plane) (i : ZMod (m + 1 + 3)) : Plane :=
  if i.val < m + 3 then P.vertex ((i.val : ℕ) : ZMod (m + 3)) else x

theorem val_neg_one_ins : (-1 : ZMod (m + 1 + 3)).val = m + 3 := by
  rw [neg_one_eq_cast]
  exact ZMod.val_cast_of_lt (by omega)

theorem insVertex_of_lt {i : ZMod (m + 1 + 3)} (h : i.val < m + 3) :
    insVertexFC P x i = P.vertex ((i.val : ℕ) : ZMod (m + 3)) := if_pos h

theorem insVertex_last : insVertexFC P x (-1) = x := by
  rw [insVertexFC, if_neg (by rw [val_neg_one_ins]; omega)]

/-- The last index of the old list, as a numeral. -/
theorem natCast_last (m : ℕ) : ((m + 2 : ℕ) : ZMod (m + 3)) = -1 := by
  have h0 : ((m + 3 : ℕ) : ZMod (m + 3)) = 0 := ZMod.natCast_self _
  push_cast at h0 ⊢
  linear_combination h0

theorem insVertex_injective (hx : ∀ j : ZMod (m + 3), P.vertex j ≠ x) :
    Function.Injective (insVertexFC P x) := by
  intro i i' hii
  by_cases h : i.val < m + 3 <;> by_cases h' : i'.val < m + 3
  · rw [insVertex_of_lt h, insVertex_of_lt h'] at hii
    have := P.vertex_inj hii
    refine ZMod.val_injective _ ?_
    have hv : ((i.val : ℕ) : ZMod (m + 3)).val = ((i'.val : ℕ) : ZMod (m + 3)).val := by rw [this]
    rwa [ZMod.val_cast_of_lt h, ZMod.val_cast_of_lt h'] at hv
  · rw [insVertex_of_lt h, insVertexFC, if_neg h'] at hii
    exact absurd hii (hx _)
  · rw [insVertex_of_lt h', insVertexFC, if_neg h] at hii
    exact absurd hii.symm (hx _)
  · have hi := ZMod.val_lt i
    have hi' := ZMod.val_lt i'
    exact ZMod.val_injective _ (by omega)

/-- Away from the new vertex the edges are the old ones. -/
theorem insVertex_edge_of_lt {i : ZMod (m + 1 + 3)} (h : i.val + 1 < m + 3) :
    segment ℝ (insVertexFC P x i) (insVertexFC P x (i + 1))
      = P.edge ((i.val : ℕ) : ZMod (m + 3)) := by
  have hsucc : (i + 1).val = i.val + 1 := val_succ_of_lt (by omega)
  have hcast : (((i.val + 1 : ℕ)) : ZMod (m + 3)) = ((i.val : ℕ) : ZMod (m + 3)) + 1 := by
    push_cast; ring
  rw [insVertex_of_lt (by omega), insVertex_of_lt (by omega : (i + 1).val < m + 3), hsucc,
    hcast, edge]

/-! ### The vertices at the two ends of each kind of edge -/

theorem insVertex_snd_fst {i : ZMod (m + 1 + 3)} (h : i.val = m + 2) :
    insVertexFC P x i = P.vertex (-1) := by
  rw [insVertex_of_lt (by omega), h, natCast_last]

theorem insVertex_snd_snd {i : ZMod (m + 1 + 3)} (h : i.val = m + 2) :
    insVertexFC P x (i + 1) = x := by
  have hsucc : (i + 1).val = i.val + 1 := val_succ_of_lt (by omega)
  rw [insVertexFC, if_neg (by omega)]

theorem insVertex_last_fst {i : ZMod (m + 1 + 3)} (h : i.val = m + 3) :
    insVertexFC P x i = x := by
  rw [insVertexFC, if_neg (by omega)]

theorem insVertex_last_snd {i : ZMod (m + 1 + 3)} (h : i.val = m + 3) :
    insVertexFC P x (i + 1) = P.vertex 0 := by
  have hsucc : (i + 1).val = 0 := val_succ_last (by omega)
  rw [insVertex_of_lt (by omega), hsucc]
  norm_num

/-- The old last edge splits into the two edges at the new vertex. -/
theorem insVertex_edge_snd {i : ZMod (m + 1 + 3)} (h : i.val = m + 2) :
    segment ℝ (insVertexFC P x i) (insVertexFC P x (i + 1)) = segment ℝ (P.vertex (-1)) x := by
  rw [insVertex_snd_fst h, insVertex_snd_snd h]

theorem insVertex_edge_last {i : ZMod (m + 1 + 3)} (h : i.val = m + 3) :
    segment ℝ (insVertexFC P x i) (insVertexFC P x (i + 1)) = segment ℝ x (P.vertex 0) := by
  rw [insVertex_last_fst h, insVertex_last_snd h]

/-! ### The three kinds of index -/

/-- Every index either names an old edge, or is one of the two at the new vertex. -/
theorem ins_trichotomy (i : ZMod (m + 1 + 3)) :
    i.val + 1 < m + 3 ∨ i.val = m + 2 ∨ i.val = m + 3 := by
  have := ZMod.val_lt i
  omega

theorem val_neg_one_old : (-1 : ZMod (m + 3)).val = m + 2 := by
  rw [← natCast_last]
  exact ZMod.val_cast_of_lt (by omega)

/-- The old index an ordinary new index names is not the last old index. -/
theorem oldIndex_ne_last {i : ZMod (m + 1 + 3)} (h : i.val + 1 < m + 3) :
    ((i.val : ℕ) : ZMod (m + 3)) ≠ (-1 : ZMod (m + 3)) := by
  intro he
  have hv : ((i.val : ℕ) : ZMod (m + 3)).val = (-1 : ZMod (m + 3)).val := by rw [he]
  rw [ZMod.val_cast_of_lt (by omega), val_neg_one_old] at hv
  omega

theorem oldIndex_inj {i k : ZMod (m + 1 + 3)} (hi : i.val + 1 < m + 3) (hk : k.val + 1 < m + 3)
    (he : ((i.val : ℕ) : ZMod (m + 3)) = ((k.val : ℕ) : ZMod (m + 3))) : i = k := by
  have hv : ((i.val : ℕ) : ZMod (m + 3)).val = ((k.val : ℕ) : ZMod (m + 3)).val := by rw [he]
  rw [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at hv
  exact ZMod.val_injective _ hv

theorem insVertex_pair_of_lt {i : ZMod (m + 1 + 3)} (h : i.val + 1 < m + 3) :
    ({insVertexFC P x i, insVertexFC P x (i + 1)} : Set Plane)
      = {P.vertex ((i.val : ℕ) : ZMod (m + 3)),
          P.vertex (((i.val : ℕ) : ZMod (m + 3)) + 1)} := by
  have hsucc : (i + 1).val = i.val + 1 := val_succ_of_lt (by omega)
  have hcast : (((i.val + 1 : ℕ)) : ZMod (m + 3)) = ((i.val : ℕ) : ZMod (m + 3)) + 1 := by
    push_cast; ring
  rw [insVertex_of_lt (by omega), insVertex_of_lt (by omega : (i + 1).val < m + 3), hsucc, hcast]

/-! ### Simplicity survives the insertion -/

variable (P)

/-- The last old edge, written with the successor evaluated. -/
theorem edge_neg_one_eq : P.edge (-1) = segment ℝ (P.vertex (-1)) (P.vertex 0) := by
  rw [edge, show (-1 : ZMod (m + 3)) + 1 = 0 by ring]

theorem vertex_last_ne_zero : P.vertex (-1) ≠ P.vertex 0 := by
  have h := P.vertex_ne_succ (-1)
  rwa [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at h

variable {P}

/-- The two new edges lie inside the old edge they split. -/
theorem insVertex_edge_subset (hcol : x ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
    {i : ZMod (m + 1 + 3)} (h : i.val = m + 2 ∨ i.val = m + 3) :
    segment ℝ (insVertexFC P x i) (insVertexFC P x (i + 1)) ⊆ P.edge (-1) := by
  rw [edge_neg_one_eq, segment_split (openSegment_subset_segment ℝ _ _ hcol)]
  rcases h with h | h
  · rw [insVertex_edge_snd h]; exact Set.subset_union_left
  · rw [insVertex_edge_last h]; exact Set.subset_union_right

/-- **Simplicity survives the insertion.** The only edges that change are the two at the new
vertex, and both lie inside the old edge they split; the far end of that old edge is on neither
half, which is what keeps the intersection inside the right pair. -/
theorem insVertex_edges_meet (hcol : x ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0))
    (i k : ZMod (m + 1 + 3)) (hik : i ≠ k) :
    segment ℝ (insVertexFC P x i) (insVertexFC P x (i + 1)) ∩
        segment ℝ (insVertexFC P x k) (insVertexFC P x (k + 1)) ⊆
      {insVertexFC P x i, insVertexFC P x (i + 1)} := by
  have hab : P.vertex (-1) ≠ P.vertex 0 := vertex_last_ne_zero P
  have hleft := notMem_segment_left_of_mem_openSegment hab hcol
  have hright := notMem_segment_right_of_mem_openSegment hab hcol
  rcases ins_trichotomy i with hi | hi
  · -- `i` names an old edge, and so does the pair of its two ends.
    rw [insVertex_edge_of_lt hi, insVertex_pair_of_lt hi]
    rcases ins_trichotomy k with hk | hk
    · rw [insVertex_edge_of_lt hk]
      exact P.edges_meet _ _ fun he => hik (oldIndex_inj hi hk he)
    · exact fun z hz =>
        P.edges_meet _ _ (oldIndex_ne_last hi) ⟨hz.1, insVertex_edge_subset hcol hk hz.2⟩
  · -- `i` is one of the two new edges: whatever it meets is trapped in the split edge.
    have hbound : ∀ z ∈ segment ℝ (insVertexFC P x i) (insVertexFC P x (i + 1)) ∩
        segment ℝ (insVertexFC P x k) (insVertexFC P x (k + 1)),
        z = P.vertex (-1) ∨ z = P.vertex 0 ∨ z = x := by
      intro z hz
      rcases ins_trichotomy k with hk | hk
      · have h2 : z ∈ P.edge ((k.val : ℕ) : ZMod (m + 3)) := by
          rw [← insVertex_edge_of_lt hk]; exact hz.2
        have hme := P.edges_meet (-1) _ (Ne.symm (oldIndex_ne_last hk))
          ⟨insVertex_edge_subset hcol hi hz.1, h2⟩
        rw [show (-1 : ZMod (m + 3)) + 1 = 0 by ring] at hme
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hme
        tauto
      · refine Or.inr (Or.inr ?_)
        have hne : i.val ≠ k.val := fun he => hik (ZMod.val_injective _ he)
        rcases hi with hi | hi
        · rw [insVertex_edge_snd hi, insVertex_edge_last (by omega : k.val = m + 3)] at hz
          exact segment_inter_of_mem_openSegment hab hcol hz
        · rw [insVertex_edge_last hi, insVertex_edge_snd (by omega : k.val = m + 2)] at hz
          exact segment_inter_of_mem_openSegment hab hcol ⟨hz.2, hz.1⟩
    intro z hz
    rcases hi with hi | hi
    · rw [insVertex_snd_fst hi, insVertex_snd_snd hi]
      rcases hbound z hz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd (by rw [← insVertex_edge_snd hi]; exact hz.1) hleft
      · exact Or.inr rfl
    · rw [insVertex_last_fst hi, insVertex_last_snd hi]
      rcases hbound z hz with rfl | rfl | rfl
      · exact absurd (by rw [← insVertex_edge_last hi]; exact hz.1) hright
      · exact Or.inr rfl
      · exact Or.inl rfl

/-- **The polygon with a vertex inserted in its last edge.** -/
def insertLastFC (P : PrePolygon m) (x : Plane) (hx : ∀ j : ZMod (m + 3), P.vertex j ≠ x)
    (hcol : x ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) : PrePolygon (m + 1) where
  vertex := insVertexFC P x
  vertex_inj := insVertex_injective hx
  edges_meet := insVertex_edges_meet hcol

@[simp] theorem insertLast_vertexFC (hx : ∀ j : ZMod (m + 3), P.vertex j ≠ x)
    (hcol : x ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) (i : ZMod (m + 1 + 3)) :
    (insertLastFC P x hx hcol).vertex i = insVertexFC P x i := rfl

/-- **Inserting a vertex does not move the curve.** -/
theorem carrier_insertLastFC (hx : ∀ j : ZMod (m + 3), P.vertex j ≠ x)
    (hcol : x ∈ openSegment ℝ (P.vertex (-1)) (P.vertex 0)) :
    (insertLastFC P x hx hcol).carrier = P.carrier := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun i => ?_) (Set.iUnion_subset fun j => ?_)
  · rcases ins_trichotomy i with hi | hi
    · rw [show (insertLastFC P x hx hcol).edge i = _ from insVertex_edge_of_lt hi]
      exact edge_subset_carrier _
    · exact le_trans (insVertex_edge_subset hcol hi) (edge_subset_carrier _)
  · by_cases hj : j = -1
    · subst hj
      set i : ZMod (m + 1 + 3) := ((m + 2 : ℕ) : ZMod (m + 1 + 3)) with hidef
      have hival : i.val = m + 2 := by rw [hidef]; exact ZMod.val_cast_of_lt (by omega)
      have hi1 : (i + 1).val = m + 3 := by rw [val_succ_of_lt (by omega), hival]
      have h1 : (insertLastFC P x hx hcol).edge i = segment ℝ (P.vertex (-1)) x :=
        insVertex_edge_snd hival
      have h2 : (insertLastFC P x hx hcol).edge (i + 1) = segment ℝ x (P.vertex 0) :=
        insVertex_edge_last hi1
      rw [edge_neg_one_eq, segment_split (openSegment_subset_segment ℝ _ _ hcol)]
      exact Set.union_subset (h1 ▸ edge_subset_carrier i) (h2 ▸ edge_subset_carrier (i + 1))
    · set i : ZMod (m + 1 + 3) := ((j.val : ℕ) : ZMod (m + 1 + 3)) with hidef
      have hjv : j.val < m + 3 := ZMod.val_lt j
      have hjne : j.val ≠ m + 2 := by
        intro he
        exact hj (by rw [← ZMod.natCast_rightInverse j, he, natCast_last])
      have hival : i.val = j.val := by rw [hidef]; exact ZMod.val_cast_of_lt (by omega)
      have hedge : (insertLastFC P x hx hcol).edge i = P.edge j := by
        rw [show (insertLastFC P x hx hcol).edge i = _ from
          insVertex_edge_of_lt (i := i) (by omega), hival, ZMod.natCast_rightInverse j]
      exact hedge ▸ edge_subset_carrier i

/-! ### Any point of the curve can be made a vertex -/

theorem insVertex_embFC (j : ZMod (m + 3)) : insVertexFC P x (emb j) = P.vertex j := by
  have hjv := ZMod.val_lt j
  have hv : (emb j).val = j.val := by rw [emb]; exact ZMod.val_cast_of_lt (by omega)
  rw [insVertex_of_lt (by omega), hv, ZMod.natCast_rightInverse j]

/-- **A named point of the curve becomes a vertex**, and the old vertices stay vertices. If the
point is one already there is nothing to do; otherwise it is interior to exactly one edge, and
`Schoenflies.PrePolygon.insertLastFC` splits that edge — after a rotation bringing it to the end of
the list. -/
theorem exists_insert_vertex (P : PrePolygon m) {x : Plane} (hx : x ∈ P.carrier) :
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
      (∃ i, P'.vertex i = x) ∧ ∀ j, ∃ i, P'.vertex i = P.vertex j := by
  by_cases hv : ∃ j, P.vertex j = x
  · exact ⟨m, P, rfl, hv, fun j => ⟨j, rfl⟩⟩
  · push Not at hv
    obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 hx
    have hopen : x ∈ openSegment ℝ (P.vertex i₀) (P.vertex (i₀ + 1)) :=
      mem_openSegment_of_ne_left_right (hv i₀) (hv (i₀ + 1)) hi₀
    -- read the polygon from the far end of that edge, so the edge to split is the last one
    have hQ1 : (P.rotate (i₀ + 1)).vertex (-1) = P.vertex i₀ := by
      rw [rotate_vertex, show i₀ + 1 + (-1 : ZMod (m + 3)) = i₀ by ring]
    have hQ0 : (P.rotate (i₀ + 1)).vertex 0 = P.vertex (i₀ + 1) := by
      rw [rotate_vertex, add_zero]
    have hvQ : ∀ j, (P.rotate (i₀ + 1)).vertex j ≠ x := fun j => hv _
    have hcol : x ∈ openSegment ℝ ((P.rotate (i₀ + 1)).vertex (-1))
        ((P.rotate (i₀ + 1)).vertex 0) := by rw [hQ1, hQ0]; exact hopen
    refine ⟨m + 1, insertLastFC (P.rotate (i₀ + 1)) x hvQ hcol, ?_, ⟨-1, insVertex_last⟩, fun j => ?_⟩
    · rw [carrier_insertLastFC, carrier_rotate]
    · exact ⟨emb (j - (i₀ + 1)), by
        rw [insertLast_vertexFC, insVertex_embFC, rotate_vertex, add_sub_cancel]⟩

/-- **Every point of a finite list on the curve can be made a vertex at once.** -/
theorem exists_prePolygon_verticesFC : ∀ (S : List Plane) {m : ℕ} (P : PrePolygon m),
    (∀ x ∈ S, x ∈ P.carrier) →
    ∃ (m' : ℕ) (P' : PrePolygon m'), P'.carrier = P.carrier ∧
      (∀ x ∈ S, ∃ i, P'.vertex i = x) ∧ (∀ j, ∃ i, P'.vertex i = P.vertex j)
  | [], m, P, _ => ⟨m, P, rfl, by simp, fun j => ⟨j, rfl⟩⟩
  | x :: S, m, P, hS => by
    obtain ⟨m₁, P₁, hc₁, ⟨i₁, hi₁⟩, hold₁⟩ :=
      exists_insert_vertex P (hS x List.mem_cons_self)
    obtain ⟨m₂, P₂, hc₂, hnew₂, hold₂⟩ :=
      exists_prePolygon_verticesFC S P₁ fun y hy => by
        rw [hc₁]; exact hS y (List.mem_cons_of_mem _ hy)
    refine ⟨m₂, P₂, hc₂.trans hc₁, fun y hy => ?_, fun j => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy'
      · obtain ⟨i, hi⟩ := hold₂ i₁
        exact ⟨i, by rw [hi, hi₁]⟩
      · exact hnew₂ y hy'
    · obtain ⟨i', hi'⟩ := hold₁ j
      obtain ⟨i, hi⟩ := hold₂ i'
      exact ⟨i, by rw [hi, hi']⟩

/-- **The realization theorem tracking two named points**, for a presentation that may carry
redundant vertices. Unlike `Schoenflies.exists_closedPolygon_split` this asks nothing of the two
points but that they lie on the curve: a `PrePolygon` has no `corner` field to obstruct a vertex
where the curve runs straight. -/
theorem exists_prePolygon_split {C : Set Plane} (hJ : IsJordanCurve C) (hP : IsPolygonal C)
    {p q : Plane} (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ (m : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ), P.carrier = C ∧
      P.vertex a = p ∧ P.vertex (a + (k : ZMod (m + 3))) = q ∧ 1 ≤ k ∧ k ≤ m + 2 := by
  obtain ⟨m₀, P₀, hcar₀⟩ := exists_prePolygon_of_isJordanCurve hJ hP
  obtain ⟨m, P, hcar, hvert, -⟩ := exists_prePolygon_verticesFC [p, q] P₀ (by
    intro z hz
    rw [hcar₀]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    exacts [hp, hq])
  obtain ⟨a, ha⟩ := hvert p (by simp)
  obtain ⟨b, hb⟩ := hvert q (by simp)
  have hab : b - a ≠ 0 := fun he => hpq (by rw [← ha, ← hb, show b = a by linear_combination he])
  refine ⟨m, P, a, (b - a).val, hcar.trans hcar₀, ha, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_rightInverse (b - a), add_sub_cancel]; exact hb
  · rcases Nat.eq_zero_or_pos (b - a).val with h0 | h0
    · exact absurd (by rw [← ZMod.natCast_rightInverse (b - a), h0, Nat.cast_zero]) hab
    · exact h0
  · have := ZMod.val_lt (b - a)
    omega

end Insert

/-! ## The two arcs of a splitting, before normalization

Verbatim `Schoenflies.ClosedPolygon.arcPiecesFC` and its API, with the structure changed. Nothing
here looks at `corner`; the proofs are those of `Schoenflies/ParitySplitting.lean` and
`Schoenflies/Realization.lean` with `PrePolygon` written for `ClosedPolygon`. -/

section Arcs

variable {m : ℕ} {P : PrePolygon m} {a : ZMod (m + 3)} {k : ℕ} {u : Plane}

/-- The edge list of the arcFC of `P` that leaves vertex `a` and runs forward through `k` edges. -/
def arcPiecesFC (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (P.vertex (a + t), P.vertex (a + t + 1))

@[simp] theorem arcPieces_zeroFC (P : PrePolygon m) (a : ZMod (m + 3)) : P.arcPiecesFC a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`. -/
theorem arcPieces_addFC (P : PrePolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    P.arcPiecesFC a (k + l) = P.arcPiecesFC a k ++ P.arcPiecesFC (a + k) l := by
  rw [arcPiecesFC, arcPiecesFC, arcPiecesFC, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list. -/
theorem arcPieces_fullFC (P : PrePolygon m) : P.arcPiecesFC 0 (m + 3) = P.pieces := by
  rw [arcPiecesFC, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

theorem mem_pieces_of_mem_arcPiecesFC {Q : Piece} (hQ : Q ∈ P.arcPiecesFC a k) : Q ∈ P.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact P.mem_pieces _

theorem arcPieces_nondegFC (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ P.arcPiecesFC a k, Q.Nondeg :=
  fun _ hQ => P.pieces_nondeg _ (mem_pieces_of_mem_arcPiecesFC hQ)

theorem arcPieces_hgt_neFC (hL : ∀ Q ∈ P.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ P.arcPiecesFC a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPiecesFC hQ)

/-- **An arcFC is a chain from its first vertex to its last.** -/
theorem isChainFrom_arcPiecesFC (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (P.arcPiecesFC a k) (P.vertex a) (P.vertex (a + k)) := by
  intro f
  have hmap : ((P.arcPiecesFC a k).map fun Q => f Q.1 + f Q.2)
      = (List.range k).map fun j : ℕ =>
          f (P.vertex (a + (j : ZMod (m + 3))))
            + f (P.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPiecesFC, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, ClosedPolygon.natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (P.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** -/
theorem arcPieces_full_permFC (P : PrePolygon m) (a : ZMod (m + 3)) :
    (P.arcPiecesFC a (m + 3)).Perm P.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : P.arcPiecesFC a (m + 3)
      = P.arcPiecesFC a (m + 3 - a.val) ++ P.arcPiecesFC 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_addFC P a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : P.pieces = P.arcPiecesFC 0 a.val ++ P.arcPiecesFC a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_addFC P 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_fullFC, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `P` exactly once. -/
theorem arcPieces_split_permFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (P.arcPiecesFC a k ++ P.arcPiecesFC (a + k) (m + 3 - k)).Perm P.pieces := by
  rw [← arcPieces_addFC, Nat.add_sub_cancel' hk]
  exact arcPieces_full_permFC P a

theorem sameEdges_arcPieces_splitFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges P.pieces (P.arcPiecesFC a k ++ P.arcPiecesFC (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_permFC P a hk).symm

/-- The arcFC of `P` that leaves vertex `a` and runs forward through `k` edges, as a set. -/
def arcFC (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (P.arcPiecesFC a k)

theorem mem_arc_iffFC {z : Plane} :
    z ∈ P.arcFC a k ↔ ∃ t < k, z ∈ P.edge (a + (t : ZMod (m + 3))) := by
  constructor
  · intro hz
    obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hR
    exact ⟨t, List.mem_range.1 ht, hzR⟩
  · rintro ⟨t, ht, hz⟩
    exact mem_cover (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩) hz

/-- The two arcs between them carry the polygon. -/
theorem cover_arcPieces_unionFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    P.arcFC a k ∪ P.arcFC (a + k) (m + 3 - k) = P.carrier := by
  rw [arcFC, arcFC, ← cover_append, cover_perm (arcPieces_split_permFC P a hk), cover_pieces]

theorem arc_subset_carrierFC (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arcFC a k ⊆ P.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := ClosedPolygon.exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPiecesFC hR) hzR

theorem isCompact_arc (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : IsCompact (P.arcFC a k) :=
  isCompact_cover _

/-- Distinct index numerals below the modulus name distinct vertices, after any shift. -/
theorem natCast_shift_injFC (P : PrePolygon m) (a : ZMod (m + 3)) {y z : ℕ} (hy : y < m + 3)
    (hz : z < m + 3) (he : P.vertex (a + (y : ZMod (m + 3))) = P.vertex (a + (z : ZMod (m + 3)))) :
    y = z :=
  ClosedPolygon.natCast_inj hy hz (add_left_cancel (P.vertex_inj he))

/-- The first vertex of a nonempty arcFC lies on it. -/
theorem vertex_mem_arcFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex a ∈ P.arcFC a k := by
  refine mem_arc_iffFC.2 ⟨0, hk, ?_⟩
  rw [Nat.cast_zero, add_zero]
  exact left_mem_segment ℝ _ _

/-- The last vertex of a nonempty arcFC lies on it. -/
theorem vertex_add_mem_arcFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    P.vertex (a + k) ∈ P.arcFC a k := by
  refine mem_arc_iffFC.2 ⟨k - 1, by omega, ?_⟩
  have hlast : a + ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = a + (k : ZMod (m + 3)) := by
    have hc : ((k - 1 : ℕ) : ZMod (m + 3)) + 1 = ((k : ℕ) : ZMod (m + 3)) := by
      rw [show ((k : ℕ) : ZMod (m + 3)) = (((k - 1) + 1 : ℕ) : ZMod (m + 3)) by
        congr 1; omega, Nat.cast_add, Nat.cast_one]
    rw [add_assoc, hc]
  rw [edge, hlast]
  exact right_mem_segment ℝ _ _

theorem endpoints_subset_arcFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arcFC a k := by
  rintro w (rfl | rfl)
  · exact P.vertex_mem_arcFC a hk
  · exact P.vertex_add_mem_arcFC a hk

theorem endpoints_subset_arc'FC (P : PrePolygon m) (a : ZMod (m + 3)) (hk2 : k ≤ m + 2) :
    ({P.vertex a, P.vertex (a + k)} : Set Plane) ⊆ P.arcFC (a + k) (m + 3 - k) := by
  have hpos : 1 ≤ m + 3 - k := by omega
  have hwrap := zmod_add_sub_cancel (k := k) (by omega) a
  rintro w (rfl | rfl)
  · have hm := P.vertex_add_mem_arcFC (a + k) hpos
    rwa [hwrap] at hm
  · exact P.vertex_mem_arcFC (a + k) hpos

/-- **The two arcs of a splitting meet exactly at the two cut vertices.** -/
theorem arc_interFC (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) :
    P.arcFC a k ∩ P.arcFC (a + k) (m + 3 - k) = {P.vertex a, P.vertex (a + k)} := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (P.endpoints_subset_arcFC a hk1)
    (P.endpoints_subset_arc'FC a hk2))
  rintro z ⟨hz1, hz2⟩
  obtain ⟨s, hs, hzs⟩ := mem_arc_iffFC.1 hz1
  obtain ⟨t, ht, hzt⟩ := mem_arc_iffFC.1 hz2
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
  have hzero : k + t + 1 = m + 3 → ((k + t + 1 : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by
    intro he
    rw [he, Nat.cast_zero, ZMod.natCast_self]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.symm.trans hB) fun he => hij (P.vertex_inj he)
  · rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_injFC a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have hs0 : s = 0 := P.natCast_shift_injFC a (by omega) (by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      exact Or.inl (by rw [hA, hs0, Nat.cast_zero, add_zero])
  · have hst : s + 1 = k + t := P.natCast_shift_injFC a (by omega) hkt (hA.symm.trans hB)
    exact Or.inr (by rw [hA, show s + 1 = k by omega])
  · exfalso
    rcases Nat.lt_or_ge (k + t + 1) (m + 3) with hlt | hge
    · exact absurd (P.natCast_shift_injFC a (by omega) hlt (hA.symm.trans hB)) (by omega)
    · have he : k + t + 1 = m + 3 := by omega
      have := P.natCast_shift_injFC a (show s + 1 < m + 3 by omega) (show 0 < m + 3 by omega)
        ((hA.symm.trans hB).trans (by rw [hzero he]))
      omega

/-- An interior point of the first edge of an arcFC: a point of the arcFC that is neither cut
vertex, which is what says the arcFC is more than its two ends. -/
theorem arc_not_subset_endpoints (P : PrePolygon m) (a : ZMod (m + 3)) (hk1 : 1 ≤ k)
    (hk2 : k ≤ m + 2) : ¬ P.arcFC a k ⊆ ({P.vertex a, P.vertex (a + k)} : Set Plane) := by
  intro hsub
  set x : Plane := (1 / 2 : ℝ) • P.vertex a + (1 / 2 : ℝ) • P.vertex (a + 1) with hxdef
  have hxo : x ∈ openSegment ℝ (P.vertex a) (P.vertex (a + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxarc : x ∈ P.arcFC a k :=
    mem_arc_iffFC.2 ⟨0, hk1, by
      rw [Nat.cast_zero, add_zero]; exact openSegment_subset_segment ℝ _ _ hxo⟩
  have hkne : (k : ZMod (m + 3)) ≠ 0 := by
    intro he
    have h0 : ((k : ℕ) : ZMod (m + 3)) = ((0 : ℕ) : ZMod (m + 3)) := by rw [he, Nat.cast_zero]
    have hk0 := ClosedPolygon.natCast_inj (m := m) (show k < m + 3 by omega)
      (show 0 < m + 3 by omega) h0
    omega
  rcases hsub hxarc with h | h
  · exact P.vertex_ne_succ a (left_mem_openSegment_iff.1 (h ▸ hxo))
  · refine notMem_edge_of_mem_openSegment (P := P) (i := a) (j := a + k)
      (fun he => hkne (by linear_combination he)) hxo ?_
    rw [edge, h]
    exact left_mem_segment ℝ _ _

/-! ### An arcFC as a polyline

`arcFC a k` is the carrier of the vertex list `v a, v (a+1), …, v (a+k)`; that is how it is seen
to be polygonal, and how it is glued to a crosscut. -/

/-- The vertex list of an arcFC. -/
def arcList (P : PrePolygon m) (a : ZMod (m + 3)) : ℕ → List Plane
  | 0 => [P.vertex a]
  | k + 1 => P.vertex a :: arcList P (a + 1) k

theorem arcList_ne_nil (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) : P.arcList a k ≠ [] := by
  cases k <;> simp [arcList]

theorem head_arcList (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    (P.arcList a k).head (P.arcList_ne_nil a k) = P.vertex a := by
  cases k <;> rfl

theorem getLast_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    (P.arcList a k).getLast (P.arcList_ne_nil a k) = P.vertex (a + k)
  | 0, P, a => by simp [arcList]
  | k + 1, P, a => by
    change (P.vertex a :: P.arcList (a + 1) k).getLast (List.cons_ne_nil _ _)
        = P.vertex (a + ((k + 1 : ℕ) : ZMod (m + 3)))
    rw [List.getLast_cons (P.arcList_ne_nil (a + 1) k), getLast_arcList k P (a + 1)]
    congr 1
    push_cast
    ring

theorem arcPieces_succ (P : PrePolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    P.arcPiecesFC a (k + 1) = (P.vertex a, P.vertex (a + 1)) :: P.arcPiecesFC (a + 1) k := by
  rw [arcPiecesFC, arcPiecesFC, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [Nat.cast_zero, add_zero]
  · refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    congr 2 <;> · push_cast; ring

theorem poly_arcList : ∀ (k : ℕ) (P : PrePolygon m) (a : ZMod (m + 3)),
    poly (P.arcList a (k + 1)) = P.arcFC a (k + 1)
  | 0, P, a => by
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ ({P.vertex (a + 1)} : Set Plane)
        = cover (P.arcPiecesFC a 1)
    rw [arcPieces_succ P a 0, arcPieces_zeroFC, cover_cons, cover_nil, Set.union_empty]
    exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ _ _))
  | k + 1, P, a => by
    have hstep : poly (P.arcList a (k + 2))
        = segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ poly (P.arcList (a + 1) (k + 1)) := rfl
    rw [hstep, poly_arcList k P (a + 1)]
    change segment ℝ (P.vertex a) (P.vertex (a + 1)) ∪ cover (P.arcPiecesFC (a + 1) (k + 1))
        = cover (P.arcPiecesFC a (k + 2))
    rw [arcPieces_succ P a (k + 1), cover_cons]
    rfl

theorem poly_arcList_of_pos (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    poly (P.arcList a k) = P.arcFC a k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact poly_arcList k' P a

theorem isPolygonal_arc (P : PrePolygon m) (a : ZMod (m + 3)) (hk : 1 ≤ k) :
    IsPolygonal (P.arcFC a k) := ⟨P.arcList a k, (poly_arcList_of_pos P a hk).symm⟩

end Arcs

end PrePolygon

/-! ## Small pieces the assembly needs -/

/-- **A polygonal Jordan curve separates the plane** (Theorem 2.3, at the set level): realize it
and quote `Schoenflies.ClosedPolygon.isSeparating_carrier`. -/
theorem isSeparating_of_isJordanCurve {S : Set Plane} (hJ : IsJordanCurve S)
    (hP : IsPolygonal S) : IsSeparating S := by
  obtain ⟨m, Q, hQ⟩ := exists_closedPolygon hJ hP
  exact hQ ▸ Q.isSeparating_carrier

/-- The two ends of an arcFC are distinct: they are the images of `0` and `1`. -/
theorem IsArcBetween.ne {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) : p ≠ q := by
  obtain ⟨f, -, hinj, -, hf0, hf1⟩ := h
  intro he
  have h01 : (0 : ℝ) = 1 := hinj zero_mem_I one_mem_I (by rw [hf0, hf1, he])
  norm_num at h01

/-- **A polyline is a chain from its first point to its last**, with its degenerate steps
dropped. `Schoenflies.isChainFrom_pathPieces` says this for `Schoenflies.pathPieces`, which keeps
them; `Schoenflies.segsOf` is the list a consumer needing nondegenerate edges must use. -/
theorem isChainFrom_segsOf : ∀ (vs : List Plane) (h : vs ≠ []),
    IsChainFrom (segsOf vs) (vs.head h) (vs.getLast h)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isChainFrom_nil v
  | u :: v :: rest, hu => by
    classical
    have hne : (v :: rest) ≠ [] := List.cons_ne_nil _ _
    have ih : IsChainFrom (segsOf (v :: rest)) v ((v :: rest).getLast hne) :=
      isChainFrom_segsOf (v :: rest) hne
    have hgl : (u :: v :: rest).getLast hu = (v :: rest).getLast hne := List.getLast_cons hne
    rw [show (u :: v :: rest).head hu = u from rfl, hgl, segsOf_cons_cons]
    split_ifs with huv
    · rw [huv]; exact ih
    · intro f
      simp only [List.map_cons, List.sum_cons]
      rw [ih f]
      linear_combination add_self_zmod_two (f v)

/-- **The two-arcFC decomposition is determined, and the competitor need not be known to be two
arcs.** This is `Schoenflies.two_arcs_unique` with the hypotheses on the second splitting weakened
to what its proof uses: the two sets are closed and neither is just the two cut points. The edge
lists of a polygon supply exactly that, and nothing tells us they are arcs until this lemma has
said so. -/
theorem two_arcs_unique_of_isClosed {C A₁ A₂ D₁ D₂ : Set Plane} {p q : Plane}
    (hA : A₁ ∪ A₂ = C) (hAi : A₁ ∩ A₂ = {p, q})
    (hD : D₁ ∪ D₂ = C) (hDi : D₁ ∩ D₂ = {p, q})
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hc1 : IsClosed D₁) (hc2 : IsClosed D₂)
    (hn1 : ¬ D₁ ⊆ ({p, q} : Set Plane)) (hn2 : ¬ D₂ ⊆ ({p, q} : Set Plane)) :
    (A₁ = D₁ ∧ A₂ = D₂) ∨ (A₁ = D₂ ∧ A₂ = D₁) := by
  have hpA : p ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inl rfl
  have hqA : q ∈ A₁ ∩ A₂ := by rw [hAi]; exact Or.inr rfl
  have hpD : p ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inl rfl
  have hqD : q ∈ D₁ ∩ D₂ := by rw [hDi]; exact Or.inr rfl
  -- An arcFC between the two points lies on one side of the other splitting.
  have key : ∀ A : Set Plane, IsArcBetween A p q → A ⊆ C → A ⊆ D₁ ∨ A ⊆ D₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ D₁ᶜ ∪ D₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ D₁
      · by_cases h2 : w ∈ D₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hDi]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (D₁ᶜ ∩ D₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hD] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ D : Set Plane, p ∈ D → q ∈ D → A \ {p, q} ⊆ D → A ⊆ D := by
      intro D hpD' hqD' hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpD', hqD']
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ D₁ᶜ).Nonempty
    · refine Or.inr (hends D₂ hpD.2 hqD.2 fun w hw => ?_)
      by_contra hwD2
      exact hnone (hconn _ _ hc1.isOpen_compl hc2.isOpen_compl hsub hcase ⟨w, hw, hwD2⟩)
    · refine Or.inl (hends D₁ hpD.1 hqD.1 fun w hw => ?_)
      by_contra hwD1
      exact hcase ⟨w, hw, hwD1⟩
  -- Both arcs cannot land on the same side: the other side would be just the two points.
  have hnotboth : ∀ D D' : Set Plane, D ∪ D' = C → D ∩ D' = {p, q} →
      ¬ D' ⊆ ({p, q} : Set Plane) → A₁ ⊆ D → A₂ ⊆ D → False := by
    intro D D' hDD hDDi hD'n h1 h2
    refine hD'n ?_
    rw [← hDDi]
    intro w hw
    have hwC : w ∈ C := by rw [← hDD]; exact Or.inr hw
    rw [← hA] at hwC
    exact hwC.elim (fun h => ⟨h1 h, hw⟩) fun h => ⟨h2 h, hw⟩
  have heq : ∀ X Y X' Y' : Set Plane, X ∪ Y = C → X' ∪ Y' = C → X' ∩ Y' = {p, q} →
      p ∈ X → q ∈ X → X ⊆ X' → Y ⊆ Y' → X = X' := by
    intro X Y X' Y' hXY hX'Y' hX'Y'i hpX hqX hXX hYY
    refine Set.Subset.antisymm hXX fun w hw => ?_
    have hwC : w ∈ C := by rw [← hX'Y']; exact Or.inl hw
    rw [← hXY] at hwC
    rcases hwC with h | h
    · exact h
    · have hwpq : w ∈ ({p, q} : Set Plane) := by rw [← hX'Y'i]; exact ⟨hw, hYY h⟩
      rcases hwpq with rfl | rfl
      exacts [hpX, hqX]
  have hAC₁ : A₁ ⊆ C := by rw [← hA]; exact Set.subset_union_left
  have hAC₂ : A₂ ⊆ C := by rw [← hA]; exact Set.subset_union_right
  rcases key A₁ hA1 hAC₁ with h1 | h1 <;> rcases key A₂ hA2 hAC₂ with h2 | h2
  · exact absurd (hnotboth D₁ D₂ hD hDi hn2 h1 h2) (by simp)
  · exact Or.inl ⟨heq A₁ A₂ D₁ D₂ hA hD hDi hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₂ D₁ (by rw [Set.union_comm]; exact hA) (by rw [Set.union_comm]; exact hD)
        (by rw [Set.inter_comm]; exact hDi) hpA.2 hqA.2 h2 h1⟩
  · exact Or.inr ⟨heq A₁ A₂ D₂ D₁ hA (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hpA.1 hqA.1 h1 h2,
      heq A₂ A₁ D₁ D₂ (by rw [Set.union_comm]; exact hA) hD hDi hpA.2 hqA.2 h2 h1⟩
  · exact absurd (hnotboth D₂ D₁ (by rw [Set.union_comm]; exact hD)
      (by rw [Set.inter_comm]; exact hDi) hn1 h1 h2) (by simp)

/-! ## Theorem 2.8 at arbitrary cut points

The blueprint's Theorem 2.8 is proved on `main` for a crosscut cutting a `ClosedPolygon` at two
of *its vertices*; `Schoenflies.ClosedPolygon.isCornerAt_vertex` makes that a real restriction,
since a point where the curve runs straight is a vertex of no `ClosedPolygon` presentation. The
exhaustion clause is what a consumer splitting a face at two graph vertices needs, and here it is
proved with no condition on the two points beyond lying on the curve.

The route is the blueprint's, with `PrePolygon` in place of `ClosedPolygon` and with the two
`Schoenflies.SameEdges` hypotheses of `Schoenflies.IsPolygonalCrosscut` replaced by *literal*
edge lists: the two curves of the split are presented as `Aᵢ ++ K`, so Lemma 2.7
(`Schoenflies.parity_split`) applies with nothing to check. Only one direction of Theorem 2.3 is
needed for those two lists — "the same region forces the same count", which is Lemma 2.2 and asks
for no realization at all. The other direction is needed only for the curve `C` itself, and there
`Schoenflies.PrePolygon.parity_eq_one_iff` supplies it. -/

/-- **The exhaustion clause of the polygonal crosscut theorem, at arbitrary cut points.** This is
`Schoenflies.CrosscutSplitsRegion`, the hypothesis `Schoenflies/FaceCyclesProof.lean` was left
with. -/
theorem crosscutSplitsRegion : CrosscutSplitsRegion := by
  intro J A₁ A₂ P Ω p q hJsep hJpoly hPpoly hA1 hA2 hunion hinter hParc hPJ hΩ hPsub z hz
  have hpq : p ≠ q := hA1.ne
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  -- 1. Present the curve with the two cut points among its vertices.
  obtain ⟨m, C, a, k, hcar, hva, hvb, hk1, hk2⟩ :=
    PrePolygon.exists_prePolygon_split hJsep.isJordanCurve hJpoly hpJ hqJ hpq
  have hk3 : k ≤ m + 3 := by omega
  have hDunion : C.arcFC a k ∪ C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) = J := by
    rw [C.cover_arcPieces_unionFC a hk3, hcar]
  have hDinter : C.arcFC a k ∩ C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) = {p, q} := by
    rw [C.arc_interFC a hk1 hk2, hva, hvb]
  have hD1n : ¬ C.arcFC a k ⊆ ({p, q} : Set Plane) := by
    rw [← hva, ← hvb]; exact C.arc_not_subset_endpoints a hk1 hk2
  have hD2n : ¬ C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ ({p, q} : Set Plane) := by
    have h := C.arc_not_subset_endpoints (a + (k : ZMod (m + 3))) (k := m + 3 - k)
      (by omega) (by omega)
    rw [zmod_add_sub_cancel hk3 a, hva, hvb, Set.pair_comm q p] at h
    exact h
  -- 2. The two arcs of the presentation are the two given arcs.
  have hids := two_arcs_unique_of_isClosed hunion hinter hDunion hDinter hA1 hA2
    (C.isCompact_arc a k).isClosed (C.isCompact_arc _ _).isClosed hD1n hD2n
  have harc1 : IsArcBetween (C.arcFC a k) p q := by
    rcases hids with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact e1 ▸ hA1
    · exact e2 ▸ hA2
  have harc2 : IsArcBetween (C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k)) p q := by
    rcases hids with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact e2 ▸ hA2
    · exact e1 ▸ hA1
  have hD1J : C.arcFC a k ⊆ J := by rw [← hcar]; exact C.arc_subset_carrierFC a k
  have hD2J : C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ⊆ J := by
    rw [← hcar]; exact C.arc_subset_carrierFC _ _
  have hpqD1 : ({p, q} : Set Plane) ⊆ C.arcFC a k := by
    rw [← hDinter]; exact Set.inter_subset_left
  have hpqD2 : ({p, q} : Set Plane) ⊆ C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) := by
    rw [← hDinter]; exact Set.inter_subset_right
  -- 3. The crosscut, as a vertex list in each direction and as an edge list.
  obtain ⟨ws, hwsne, hwhead, hwlast, hwpoly⟩ := hParc.exists_poly_eq hPpoly hpq
  obtain ⟨ws', hwsne', hwhead', hwlast', hwpoly'⟩ := hParc.reverse.exists_poly_eq hPpoly hpq.symm
  have hKcover : cover (segsOf ws) = P := by
    rw [cover_segsOf_eq (a := p) (b := q) (by rw [hwpoly]; exact hParc.left_mem)
      (by rw [hwpoly]; exact hParc.right_mem) hpq, hwpoly]
  have hKchain : IsChainFrom (segsOf ws) p q := by
    have h := isChainFrom_segsOf ws hwsne
    rwa [hwhead, hwlast] at h
  -- 4. The two curves of the split are separating.
  have hpolyD1P : IsPolygonal (C.arcFC a k ∪ P) :=
    ⟨C.arcList a k ++ ws', by
      rw [poly_append_of_eq (C.arcList_ne_nil a k) hwsne'
          (by rw [PrePolygon.getLast_arcList k C a, hvb, hwhead']),
        PrePolygon.poly_arcList_of_pos C a hk1, hwpoly']⟩
  have hpolyD2P : IsPolygonal (C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    ⟨C.arcList (a + (k : ZMod (m + 3))) (m + 3 - k) ++ ws, by
      rw [poly_append_of_eq (C.arcList_ne_nil _ _) hwsne
          (by rw [PrePolygon.getLast_arcList (m + 3 - k) C _, zmod_add_sub_cancel hk3 a, hva,
            hwhead]),
        PrePolygon.poly_arcList_of_pos C _ (by omega : 1 ≤ m + 3 - k), hwpoly]⟩
  have hmeetP : ∀ (S : Set Plane), S ⊆ J → ∀ w ∈ S, w ∈ P → w = p ∨ w = q := by
    intro S hSJ w hw hwP
    have hmem : w ∈ ({p, q} : Set Plane) := by rw [← hPJ]; exact ⟨hwP, hSJ hw⟩
    simpa using hmem
  have hJ1 : IsSeparating (C.arcFC a k ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc1 hParc (hmeetP _ hD1J)) hpolyD1P
  have hJ2 : IsSeparating (C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) :=
    isSeparating_of_isJordanCurve (isJordanCurve_union harc2 hParc (hmeetP _ hD2J)) hpolyD2P
  -- 5. A reference point in the region the crosscut does not enter.
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside J, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨y, hy⟩ := (hΩpair.right.isConnected hJsep).nonempty
  have hyJ : y ∉ J := hΩpair.right.subset_compl hy
  have hnotP : ∀ w ∈ Ω', w ∉ P := by
    intro w hw hwP
    have hwJ : w ∉ J := hΩpair.right.subset_compl hw
    have hwpq : w ∉ ({p, q} : Set Plane) := by
      rintro (rfl | rfl)
      exacts [hwJ hpJ, hwJ hqJ]
    exact Set.disjoint_left.1 hΩpair.disjoint (hPsub ⟨hwP, hwpq⟩) hw
  have hΩ'sub : ∀ S : Set Plane, S ⊆ J → Ω' ⊆ (S ∪ P)ᶜ := by
    intro S hSJ w hw
    rintro (h | h)
    · exact hΩpair.right.subset_compl hw (hSJ h)
    · exact hnotP w hw h
  have hyJ1 : y ∉ C.arcFC a k ∪ P := hΩ'sub _ hD1J hy
  have hyJ2 : y ∉ C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := hΩ'sub _ hD2J hy
  have hΩW1 : Ω' ⊆ connectedComponentIn (C.arcFC a k ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD1J)
  have hΩW2 : Ω' ⊆
      connectedComponentIn (C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub _ hD2J)
  have heqΩ' : connectedComponentIn Jᶜ y = Ω' := hΩpair.right.connectedComponentIn_eq hJsep hy
  -- 6. Lemma 2.6: the two cells are components of `Ω ∖ P`.
  obtain ⟨⟨-, hV1comp⟩, ⟨-, hV2comp⟩, -, -, -⟩ :=
    crosscut_cells hJsep hJ1 hJ2 hD1J hD2J (by rw [hPJ]; exact hpqD1) (by rw [hPJ]; exact hpqD2)
      (arcs_ne (le_of_eq hDinter) hD1n) hΩpair (hJ1.isRegionPair_farRegion hyJ1) hΩW1
      (hJ2.isRegionPair_farRegion hyJ2) hΩW2
  -- 7. Exhaustion, by Lemma 2.7 and the two values of Theorem 2.3.
  obtain ⟨u, hu, hlev⟩ := exists_direction_hgt_ne (C.pieces ++ segsOf ws) (by
    intro Q hQ
    rcases List.mem_append.1 hQ with h | h
    · exact C.pieces_nondeg Q h
    · exact segsOf_nondeg ws Q h)
  have hlevC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_left _ hQ)
  have hlevK : ∀ Q ∈ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    fun Q hQ => hlev Q (List.mem_append_right _ hQ)
  have hlev1 : ∀ Q ∈ C.arcPiecesFC a k ++ segsOf ws, hgt u Q.1 ≠ hgt u Q.2 :=
    hgt_ne_append (PrePolygon.arcPieces_hgt_neFC hlevC) hlevK
  have hlev2 : ∀ Q ∈ C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws,
      hgt u Q.1 ≠ hgt u Q.2 := hgt_ne_append (PrePolygon.arcPieces_hgt_neFC hlevC) hlevK
  have hchain1 : IsChainFrom (C.arcPiecesFC a k) p q := by
    have h := C.isChainFrom_arcPiecesFC a k
    rwa [hva, hvb] at h
  have hchain2 : IsChainFrom (C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k)) q p := by
    have h := C.isChainFrom_arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k)
    rw [zmod_add_sub_cancel hk3 a] at h
    rwa [hva, hvb] at h
  have hclosed1 : IsClosedChain (C.arcPiecesFC a k ++ segsOf ws) :=
    hchain1.isClosedChain_append hKchain
  have hclosed2 : IsClosedChain
      (C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) :=
    isChainFrom_self_iff.1 (hchain2.append hKchain)
  have hcov1 : cover (C.arcPiecesFC a k ++ segsOf ws) = C.arcFC a k ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hcov2 : cover (C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws)
      = C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
    rw [cover_append, hKcover]
    rfl
  have hsplit : ∀ w : Plane,
      parity u (C.arcPiecesFC a k ++ segsOf ws) w
        + parity u (C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u C.pieces w :=
    fun w => parity_split u (C.sameEdges_arcPieces_splitFC a hk3) (List.Perm.refl _)
      (List.Perm.refl _) w
  have hexh : ∀ w ∈ Ω \ P, w ∈ farRegion (C.arcFC a k ∪ P) y ∨
      w ∈ farRegion (C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P) y := by
    intro w hw
    by_contra hcon
    push Not at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hwJ : w ∉ J := hΩ.subset_compl hw.1
    have hw1 : w ∉ C.arcFC a k ∪ P := by
      rintro (h | h)
      · exact hwJ (hD1J h)
      · exact hw.2 h
    have hw2 : w ∉ C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P := by
      rintro (h | h)
      · exact hwJ (hD2J h)
      · exact hw.2 h
    have hmem1 : w ∈ connectedComponentIn (C.arcFC a k ∪ P)ᶜ y := by
      by_contra hc1
      exact hn1 ⟨hw1, hc1⟩
    have hmem2 : w ∈
        connectedComponentIn (C.arcFC (a + (k : ZMod (m + 3))) (m + 3 - k) ∪ P)ᶜ y := by
      by_contra hc2
      exact hn2 ⟨hw2, hc2⟩
    have hp1 : parity u (C.arcPiecesFC a k ++ segsOf ws) w
        = parity u (C.arcPiecesFC a k ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev1 hclosed1 (by rw [hcov1]; exact hyJ1)
        (by rw [hcov1]; exact hmem1)
    have hp2 : parity u (C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) w
        = parity u (C.arcPiecesFC (a + (k : ZMod (m + 3))) (m + 3 - k) ++ segsOf ws) y :=
      parity_eq_of_mem_connectedComponentIn hu hlev2 hclosed2 (by rw [hcov2]; exact hyJ2)
        (by rw [hcov2]; exact hmem2)
    have hkey : parity u C.pieces w = parity u C.pieces y := by
      rw [← hsplit w, ← hsplit y, hp1, hp2]
    rcases hΩpair with ⟨hin, hout⟩ | ⟨hout, hin⟩
    · rw [C.parity_eq_one_of_mem_inside hu hlevC
          (show w ∈ inside C.carrier by rw [hcar]; exact hin ▸ hw.1),
        C.parity_eq_zero_of_mem_outside hu hlevC
          (show y ∈ outside C.carrier by rw [hcar]; exact hout ▸ hy)] at hkey
      exact absurd hkey (by decide)
    · rw [C.parity_eq_zero_of_mem_outside hu hlevC
          (show w ∈ outside C.carrier by rw [hcar]; exact hout ▸ hw.1),
        C.parity_eq_one_of_mem_inside hu hlevC
          (show y ∈ inside C.carrier by rw [hcar]; exact hin ▸ hy)] at hkey
      exact absurd hkey (by decide)
  -- 8. Read the conclusion off the identification of the two arcs.
  rcases hids with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hexh z hz with hv | hv
    · exact Or.inl (by rw [e1, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inr (by rw [e2, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)
  · rcases hexh z hz with hv | hv
    · exact Or.inr (by rw [e2, hV1comp z hv]; exact hJ1.isRegionOf_farRegion hyJ1)
    · exact Or.inl (by rw [e1, hV2comp z hv]; exact hJ2.isRegionOf_farRegion hyJ2)

end Schoenflies

namespace Graph

open scoped Graph

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane} {a b : Plane}

/-! ## `lem:face-cycles`, with nothing assumed

`Graph.IsDrawing.hasFaceCycles_union` and `Graph.face_cycles` of
`Schoenflies/FaceCyclesProof.lean` carry the hypothesis `Schoenflies.CrosscutSplitsRegion`;
`Schoenflies.crosscutSplitsRegion` above proves it, so here are the two statements with the
hypothesis discharged. **These are the forms a consumer should use.** Once this module's
`PrePolygon` development is hoisted above `Schoenflies/FaceCyclesProof.lean` the hypothesis can
be deleted from the originals and the primes here dropped. -/

/-- **One ear**, with no hypothesis assumed: `Graph.IsDrawing.hasFaceCycles_union` with
`Schoenflies.CrosscutSplitsRegion` discharged. -/
theorem IsDrawing.hasFaceCycles_union' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing :=
  h.hasFaceCycles_union crosscutSplitsRegion hpoly hBG hmot hpath hab ha hb hint hnew

/-- **`lem:face-cycles` (face cycles).** Every face of a finite 2-connected polygonal plane graph
has a cycle as its boundary and is one of the two complementary regions of that cycle.

This is `Graph.face_cycles` with its hypothesis `Schoenflies.CrosscutSplitsRegion` discharged by
`Schoenflies.crosscutSplitsRegion`; nothing is assumed. -/
theorem face_cycles' [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)) (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing :=
  face_cycles crosscutSplitsRegion h hpoly hG

/-- **Every bounded face is the interior of its boundary cycle.** -/
theorem IsFaceCycle.eq_inside_of_isBounded' {z : Plane} {e : β} {u v : Plane} {D : List β}
    (hf : IsFaceCycle G drawing z e u v D)
    (hbdd : Bornology.IsBounded (face G drawing z)) :
    face G drawing z = Schoenflies.inside (edgesCover drawing (e :: D)) :=
  hf.eq_inside_of_isBounded hbdd

end Graph
