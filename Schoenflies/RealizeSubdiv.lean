/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CellulationInvariants
import Schoenflies.Subarc

/-!
# Realizing an edge subdivision

`Schoenflies/GeneratedStructure.lean` performs the *abstract* edge subdivision
(`CellStructure.subdivideEdge`) and states what it means for a realization of the subdivided
structure to refine a realization of the old one (`SubdivData.IsRefinement`);
`Schoenflies/CellulationInvariants.lean` propagates assertions (i), (iv) and (vii) across such a
refinement. Nothing built such a realization. This module does.

The construction is the blueprint's own sentence — "the corresponding point is inserted into the
corresponding edge using the edge parametrization" — made into data: pick a parameter
`t ∈ (0,1)`, put the new 0-cell at `R.drawing d.edge t`, and draw the two new 1-cells with the
two halves of the old parametrization, each rescaled to `[0,1]`.

## The orientation of the drawn edge

`IsDrawing.edge_param` is deliberately orientation-free: it says
`G.IsLink e (drawing e 0) (drawing e 1)`, so `drawing d.edge 0` may be *either* `pos d.left` or
`pos d.right`. But `d.newEdge₁` runs from `d.left` to `d.newVertex` by definition of
`subdivideEdge`, so which half of the parametrization draws it is not fixed in advance.

Assuming `drawing d.edge 0 = pos d.left` would be a false hypothesis for half of all inputs, and
the caller cannot repair it (swapping `d.left` with `d.right` in the `SubdivData` also swaps the
two new edge *names*, producing a different abstract structure). So the orientation is read off
instead: `SubdivData.leftParam` is the endpoint parameter, `0` or `1`, at which the drawn edge
sits at `d.left`. Every statement below is orientation-free; only the two lemmas
`SubdivData.drawing_leftParam` and `SubdivData.drawing_rightParam` look inside.

Because of that, the construction is phrased with `Schoenflies.subarc` — the general affine
reparametrization already on `main` — rather than with `firstHalf` / `secondHalf`, which are the
two halves in the standard orientation and are recorded here as the named special case.

## No side conditions

`SubdivData.realize` takes no geometric hypothesis beyond `t ∈ Ioo 0 1`. Everything else it
needs — that `d.edge` is drawn, injectively and continuously, between the positions of `d.left`
and `d.right`, and that an interior point of a drawn edge is not a vertex — is already carried by
`CellStructure.Realization`, and is extracted here rather than assumed.

## Blueprint

* `def:generated-structure`, operation 1 (edge subdivision) — the geometric half of the
  operation, whose abstract half is `CellStructure.subdivideEdge`.
* `lem:cellulation-invariants` (i) and (iv), the paragraph "Suppose first that an open edge `e`
  is subdivided at a new vertex `v`": `SubdivData.isRefinement_realize` produces exactly the
  hypotheses that `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan` consumes.

Declarations:

* `Schoenflies.uIcc_union_uIcc`, `Schoenflies.uIcc_inter_uIcc` — a parameter interval cut at an
  interior point.
* `Schoenflies.subarc_image_union`, `Schoenflies.subarc_image_inter` — the two subarcs of a cut
  cover the arc and meet exactly at the cut point.
* `Schoenflies.firstHalf`, `Schoenflies.secondHalf` — the two halves of a drawn edge in the
  standard orientation, with their endpoint values, continuity, injectivity, images, meet and
  union.
* `Schoenflies.CellStructure.SubdivData.leftParam` / `rightParam` — the orientation of the drawn
  edge.
* `Schoenflies.CellStructure.SubdivData.realize` — the realization of the subdivided structure.
* `Schoenflies.CellStructure.SubdivData.isRefinement_realize` — it refines the given one.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph

/-! ### Cutting a parameter interval at an interior point -/

variable {a b t : ℝ}

/-- The two halves of a parameter interval cut at a point of it cover it. -/
theorem uIcc_union_uIcc (h : t ∈ uIcc a b) : uIcc a t ∪ uIcc t b = uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h ⊢
    rw [uIcc_of_le h.1, uIcc_of_le h.2, Icc_union_Icc_eq_Icc h.1 h.2]
  · rw [uIcc_of_ge hab] at h ⊢
    rw [uIcc_of_ge h.2, uIcc_of_ge h.1, union_comm, Icc_union_Icc_eq_Icc h.1 h.2]

/-- …and meet exactly at the cut point. -/
theorem uIcc_inter_uIcc (h : t ∈ uIcc a b) : uIcc a t ∩ uIcc t b = {t} := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h
    rw [uIcc_of_le h.1, uIcc_of_le h.2, Icc_inter_Icc_eq_singleton h.1 h.2]
  · rw [uIcc_of_ge hab] at h
    rw [uIcc_of_ge h.2, uIcc_of_ge h.1, inter_comm, Icc_inter_Icc_eq_singleton h.1 h.2]

/-- The far endpoint is not in the near half. -/
theorem right_notMem_uIcc_left (h : t ∈ uIcc a b) (hb : b ≠ t) : b ∉ uIcc a t := fun hmem =>
  hb (by
    have : b ∈ uIcc a t ∩ uIcc t b := ⟨hmem, right_mem_uIcc⟩
    rwa [uIcc_inter_uIcc h, mem_singleton_iff] at this)

/-- …and symmetrically. -/
theorem left_notMem_uIcc_right (h : t ∈ uIcc a b) (ha : a ≠ t) : a ∉ uIcc t b := fun hmem =>
  ha (by
    have : a ∈ uIcc a t ∩ uIcc t b := ⟨left_mem_uIcc, hmem⟩
    rwa [uIcc_inter_uIcc h, mem_singleton_iff] at this)

theorem uIcc_left_subset (h : t ∈ uIcc a b) : uIcc a t ⊆ uIcc a b :=
  uIcc_subset_uIcc left_mem_uIcc h

theorem uIcc_right_subset (h : t ∈ uIcc a b) : uIcc t b ⊆ uIcc a b :=
  uIcc_subset_uIcc h right_mem_uIcc

/-! ### The two subarcs of a cut -/

variable {f : ℝ → Plane}

/-- **The two subarcs of a cut cover the arc.** -/
theorem subarc_image_union (h : t ∈ uIcc a b) :
    subarc f a t '' I ∪ subarc f t b '' I = f '' uIcc a b := by
  rw [subarc_image, subarc_image, ← image_union, uIcc_union_uIcc h]

/-- **The two subarcs of a cut meet exactly at the cut point.** -/
theorem subarc_image_inter (hi : InjOn f (uIcc a b)) (h : t ∈ uIcc a b) :
    subarc f a t '' I ∩ subarc f t b '' I = {f t} := by
  rw [subarc_image, subarc_image, ← hi.image_inter (uIcc_left_subset h) (uIcc_right_subset h),
    uIcc_inter_uIcc h, image_singleton]

/-! ### The two halves of a drawn edge

The special case `a = 0`, `b = 1` of the previous section, in the notation a consumer holding a
`Graph.IsDrawing` writes. -/

variable {β : Type*} {drawing : β → ℝ → Plane} {e : β}

theorem uIcc_zero_one : uIcc (0 : ℝ) 1 = I := uIcc_of_le zero_le_one

/-- The first half of a drawn edge, rescaled to `[0, 1]`. -/
def firstHalf (drawing : β → ℝ → Plane) (e : β) (t : ℝ) : ℝ → Plane := subarc (drawing e) 0 t

/-- The second half of a drawn edge, rescaled to `[0, 1]`. -/
def secondHalf (drawing : β → ℝ → Plane) (e : β) (t : ℝ) : ℝ → Plane := subarc (drawing e) t 1

theorem firstHalf_apply (s : ℝ) : firstHalf drawing e t s = drawing e (t * s) := by
  simp only [firstHalf, subarc, reparam]
  congr 1
  ring

theorem secondHalf_apply (s : ℝ) : secondHalf drawing e t s = drawing e (t + (1 - t) * s) := by
  simp only [secondHalf, subarc, reparam]
  congr 1
  ring

@[simp] theorem firstHalf_zero : firstHalf drawing e t 0 = drawing e 0 := subarc_zero

@[simp] theorem firstHalf_one : firstHalf drawing e t 1 = drawing e t := subarc_one

@[simp] theorem secondHalf_zero : secondHalf drawing e t 0 = drawing e t := subarc_zero

@[simp] theorem secondHalf_one : secondHalf drawing e t 1 = drawing e 1 := subarc_one

theorem continuousOn_firstHalf (hc : ContinuousOn (drawing e) I) (ht : t ∈ I) :
    ContinuousOn (firstHalf drawing e t) I := continuousOn_subarc hc zero_mem_I ht

theorem continuousOn_secondHalf (hc : ContinuousOn (drawing e) I) (ht : t ∈ I) :
    ContinuousOn (secondHalf drawing e t) I := continuousOn_subarc hc ht one_mem_I

theorem injOn_firstHalf (hi : InjOn (drawing e) I) (ht : t ∈ I) (h0 : t ≠ 0) :
    InjOn (firstHalf drawing e t) I :=
  injOn_subarc (hi.mono (uIcc_subset_I zero_mem_I ht)) (Ne.symm h0)

theorem injOn_secondHalf (hi : InjOn (drawing e) I) (ht : t ∈ I) (h1 : t ≠ 1) :
    InjOn (secondHalf drawing e t) I :=
  injOn_subarc (hi.mono (uIcc_subset_I ht one_mem_I)) h1

theorem image_firstHalf (ht : t ∈ I) :
    firstHalf drawing e t '' I = drawing e '' Icc 0 t := by
  rw [firstHalf, subarc_image, uIcc_of_le ht.1]

theorem image_secondHalf (ht : t ∈ I) :
    secondHalf drawing e t '' I = drawing e '' Icc t 1 := by
  rw [secondHalf, subarc_image, uIcc_of_le ht.2]

/-- **The two halves cover the drawn edge.** -/
theorem firstHalf_union_secondHalf (ht : t ∈ I) :
    firstHalf drawing e t '' I ∪ secondHalf drawing e t '' I = edgeArc drawing e := by
  rw [firstHalf, secondHalf, subarc_image_union (by rwa [uIcc_zero_one]), uIcc_zero_one, edgeArc]

/-- **The two halves meet exactly at the cut point.** -/
theorem firstHalf_inter_secondHalf (hi : InjOn (drawing e) I) (ht : t ∈ I) :
    firstHalf drawing e t '' I ∩ secondHalf drawing e t '' I = {drawing e t} := by
  rw [firstHalf, secondHalf,
    subarc_image_inter (by rwa [uIcc_zero_one]) (by rwa [uIcc_zero_one])]

/-- Each half is an arc between the corresponding endpoint and the cut point. -/
theorem isArcBetween_firstHalf (hc : ContinuousOn (drawing e) I) (hi : InjOn (drawing e) I)
    (ht : t ∈ I) (h0 : t ≠ 0) :
    IsArcBetween (firstHalf drawing e t '' I) (drawing e 0) (drawing e t) :=
  ⟨firstHalf drawing e t, continuousOn_firstHalf hc ht, injOn_firstHalf hi ht h0, rfl,
    firstHalf_zero, firstHalf_one⟩

theorem isArcBetween_secondHalf (hc : ContinuousOn (drawing e) I) (hi : InjOn (drawing e) I)
    (ht : t ∈ I) (h1 : t ≠ 1) :
    IsArcBetween (secondHalf drawing e t '' I) (drawing e t) (drawing e 1) :=
  ⟨secondHalf drawing e t, continuousOn_secondHalf hc ht, injOn_secondHalf hi ht h1, rfl,
    secondHalf_zero, secondHalf_one⟩

/-! ### The orientation of the drawn subdivided edge -/

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} (d : S.SubdivData) (R : S.Realization)

/-- What the realization already knows about the subdivided edge: it is an edge of the drawn
skeleton. -/
theorem edge_mem_edgeSet_graph : d.edge ∈ E(R.graph) := by
  rw [Realization.edgeSet_graph]; exact d.edge_mem_edgeSet

theorem continuousOn_drawing_edge : ContinuousOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).1

theorem injOn_drawing_edge : InjOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).2.1

theorem isLink_drawn_edge : R.graph.IsLink d.edge (R.pos d.left) (R.pos d.right) :=
  d.isLink.map R.pos

open scoped Classical in
/-- **The orientation of the drawn subdivided edge**: the endpoint parameter, `0` or `1`, at
which `R.drawing d.edge` sits at `R.pos d.left`.

`IsDrawing.edge_param` fixes only the unordered pair of endpoint values, so this cannot be read
off the structure; it is decided by a case distinction, once, here. -/
noncomputable def leftParam : ℝ := if R.drawing d.edge 0 = R.pos d.left then 0 else 1

/-- The endpoint parameter at which the drawn subdivided edge sits at `R.pos d.right`. -/
noncomputable def rightParam : ℝ := 1 - d.leftParam R

theorem leftParam_eq_zero_or_one : d.leftParam R = 0 ∨ d.leftParam R = 1 := by
  unfold leftParam
  split_ifs
  exacts [Or.inl rfl, Or.inr rfl]

/-- **The two endpoint parameters land on the two endpoints.** The only lemma that looks inside
`leftParam`; everything downstream is orientation-free. -/
theorem drawing_params :
    R.drawing d.edge (d.leftParam R) = R.pos d.left ∧
      R.drawing d.edge (d.rightParam R) = R.pos d.right := by
  have hd := R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)
  rcases (d.isLink_drawn_edge R).eq_and_eq_or_eq_and_eq hd.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hL : d.leftParam R = 0 := if_pos h0.symm
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 1 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm
  · -- Here `R.pos d.left = R.drawing d.edge 1`; the other reading would collapse the two
    -- endpoint values, which injectivity forbids.
    have hne : ¬ (R.drawing d.edge 0 = R.pos d.left) := fun hcon =>
      zero_ne_one (hd.2.1 zero_mem_I one_mem_I (by rw [hcon, h0]))
    have hL : d.leftParam R = 1 := if_neg hne
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 0 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm

theorem drawing_leftParam : R.drawing d.edge (d.leftParam R) = R.pos d.left :=
  (d.drawing_params R).1

theorem drawing_rightParam : R.drawing d.edge (d.rightParam R) = R.pos d.right :=
  (d.drawing_params R).2

theorem leftParam_mem_I : d.leftParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [zero_mem_I, one_mem_I]

theorem rightParam_mem_I : d.rightParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact one_mem_I
  · rw [rightParam, h, sub_self]; exact zero_mem_I

/-- The two endpoint parameters span the whole parameter interval, in whichever order. -/
theorem uIcc_params : uIcc (d.leftParam R) (d.rightParam R) = I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact uIcc_zero_one
  · rw [rightParam, h, sub_self, uIcc_comm]; exact uIcc_zero_one

theorem leftParam_ne (ht : t ∈ Ioo (0 : ℝ) 1) : d.leftParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [ht.1.ne, ht.2.ne']

theorem rightParam_ne (ht : t ∈ Ioo (0 : ℝ) 1) : d.rightParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact ht.2.ne'
  · rw [rightParam, h, sub_self]; exact ht.1.ne

theorem mem_uIcc_params (ht : t ∈ Ioo (0 : ℝ) 1) : t ∈ uIcc (d.leftParam R) (d.rightParam R) := by
  rw [d.uIcc_params R]; exact Ioo_subset_Icc_self ht

/-- **An interior point of a drawn edge is not a vertex.** The one geometric fact the
construction needs that is not simply read off a field, and the reason `SubdivData.realize`
needs no side condition. -/
theorem newPos_notMem_vertexSet (ht : t ∈ Ioo (0 : ℝ) 1) :
    R.drawing d.edge t ∉ V(R.graph) := by
  intro hmem
  have harc : R.drawing d.edge t ∈ edgeArc R.drawing d.edge :=
    ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  have hinj := d.injOn_drawing_edge R
  rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hmem harc with h | h
  · exact d.leftParam_ne R ht
      (hinj (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht) ((d.drawing_leftParam R).trans h.symm))
  · exact d.rightParam_ne R ht
      (hinj (d.rightParam_mem_I R) (Ioo_subset_Icc_self ht)
        ((d.drawing_rightParam R).trans h.symm))

theorem newPos_ne_pos (ht : t ∈ Ioo (0 : ℝ) 1) {v : γ} (hv : v ∈ V(S.skel)) :
    R.drawing d.edge t ≠ R.pos v := fun h =>
  d.newPos_notMem_vertexSet R ht (by rw [h, Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)

end SubdivData

end CellStructure

end Schoenflies
