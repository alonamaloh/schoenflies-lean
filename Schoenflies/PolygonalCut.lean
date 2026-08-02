/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SimpleArc
import Schoenflies.FaceCyclesProof

/-!
# An arc inside a polygonal arc is polygonal

`def:admissible-graph` asks that every nonboundary edge be a polygonal arc, and both elementary
operations of `def:generated-structure` cut existing arcs into smaller ones: an edge subdivision
splits a drawn edge at an interior point, and an ear contributes edge arcs cut out of the drawn
crosscut. Neither preserves `Schoenflies.IsPolygonal` for free — it is a statement about a *set*,
and nothing says a piece of a polyline is one.

`Schoenflies.IsArcBetween.isPolygonal_of_subset` says it does. The proof is not a list surgery:
`Schoenflies.exists_simple_poly_of_isPolygonal` already produces *some* polygonal arc between the
two points inside the ambient one, and what has to be shown is that there is only one such arc.

## Sub-arcs are unique

The engine is `Schoenflies.subarc_subset_of_isPreconnected`: a connected subset of an arc that
contains the source and the point at parameter `t` contains everything the arc traverses up to
`t`. That is where the topology sits — the parametrisation of an arc is a closed map, because
`I` is compact and the plane is Hausdorff, so `IsPreconnected.preimage_of_isClosedMap` pulls
connectedness back to the parameter interval, where a connected set is an interval.

Given it, two arcs between the same two points inside one ambient arc both contain the ambient
arc's own sub-arc, and `Schoenflies.IsArcBetween.eq_of_subset` collapses each onto it.

## Blueprint

* `Schoenflies.subarc_subset_of_isPreconnected` — sub-arc uniqueness, in the form that does the
  work.
* `Schoenflies.IsArcBetween.eq_of_subset_of_isArcBetween` — two arcs with the same ends inside
  one arc coincide.
* `Schoenflies.IsArcBetween.isPolygonal_of_subset` — the consequence
  `def:admissible-graph` needs across both elementary operations.
-/

open Set unitInterval

namespace Schoenflies

variable {f : ℝ → Plane} {A B C : Set Plane} {p q r : Plane} {t : ℝ}

/-- **A connected subset of an arc that reaches the parameter `t` contains everything before
it.** The parametrisation restricted to `I` is a continuous injection from a compact space to a
Hausdorff one, hence a closed map, so the part of `I` that lands in `C` is connected — and a
connected subset of `ℝ` containing `0` and `t` contains `uIcc 0 t`. -/
theorem subarc_subset_of_isPreconnected_of_mem (hc : ContinuousOn f I) (hi : InjOn f I)
    (hC : IsPreconnected C) (hCA : C ⊆ f '' I) {s : ℝ} (hs : s ∈ I) (ht : t ∈ I) (h0 : f s ∈ C)
    (htC : f t ∈ C) : f '' uIcc s t ⊆ C := by
  -- Restrict the parametrisation to `I`, where it is a closed injection.
  have hcs : Continuous (Set.restrict I f) := continuousOn_iff_continuous_restrict.1 hc
  have hinj : Function.Injective (Set.restrict I f) := fun a b hab =>
    Subtype.ext (hi a.2 b.2 hab)
  haveI : CompactSpace (I : Set ℝ) := isCompact_iff_compactSpace.1 isCompact_I
  have hclosed : IsClosedMap (Set.restrict I f) := hcs.isClosedMap
  have hrange : C ⊆ range (Set.restrict I f) := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := hCA hz
    exact ⟨⟨s, hs⟩, rfl⟩
  -- The parameters that land in `C` are connected, hence an interval containing `0` and `t`.
  have hpre : IsPreconnected (Set.restrict I f ⁻¹' C) :=
    hC.preimage_of_isClosedMap hinj hclosed hrange
  have himg : IsPreconnected (Subtype.val '' (Set.restrict I f ⁻¹' C)) :=
    hpre.image _ continuous_subtype_val.continuousOn
  have h0mem : s ∈ Subtype.val '' (Set.restrict I f ⁻¹' C) := ⟨⟨s, hs⟩, h0, rfl⟩
  have htmem : t ∈ Subtype.val '' (Set.restrict I f ⁻¹' C) := ⟨⟨t, ht⟩, htC, rfl⟩
  have hsub : uIcc s t ⊆ Subtype.val '' (Set.restrict I f ⁻¹' C) :=
    himg.ordConnected.uIcc_subset h0mem htmem
  rintro z ⟨s, hs, rfl⟩
  obtain ⟨⟨s', hs'⟩, hs'C, rfl⟩ := hsub hs
  exact hs'C

/-- The special case based at the parametrization's own start, which is the one
`IsArcBetween.eq_of_subset_of_isArcBetween` runs on. -/
theorem subarc_subset_of_isPreconnected (hc : ContinuousOn f I) (hi : InjOn f I)
    (hC : IsPreconnected C) (hCA : C ⊆ f '' I) (ht : t ∈ I) (h0 : f 0 ∈ C) (htC : f t ∈ C) :
    f '' uIcc 0 t ⊆ C :=
  subarc_subset_of_isPreconnected_of_mem hc hi hC hCA zero_mem_I ht h0 htC

/-- **Two arcs with the same ends inside one arc are the same arc.** Each contains the ambient
arc's own sub-arc between those ends, and an arc containing an arc with the same ends is it. -/
theorem IsArcBetween.eq_of_subset_of_isArcBetween (hA : IsArcBetween A p q)
    (hB : IsArcBetween B p r) (hC : IsArcBetween C p r) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hpr : p ≠ r) : B = C := by
  obtain ⟨f, hc, hi, rfl, hf0, hf1⟩ := hA
  -- The second endpoint sits at some parameter `t`, which is not `0`.
  obtain ⟨t, ht, hft⟩ : ∃ t ∈ I, f t = r := hBA hB.right_mem
  have ht0 : (0 : ℝ) ≠ t := fun hh => hpr (hf0 ▸ hh ▸ hft ▸ rfl)
  have harc : IsArcBetween (f '' uIcc 0 t) p r := by
    have := isArcBetween_subarc_of_injOn_I hc hi zero_mem_I ht ht0
    rwa [hf0, hft] at this
  -- Both arcs contain that sub-arc, and neither can be bigger.
  have hBsub : f '' uIcc 0 t ⊆ B :=
    subarc_subset_of_isPreconnected hc hi hB.isArc.isConnected.isPreconnected hBA ht
      (hf0 ▸ hB.left_mem) (hft ▸ hB.right_mem)
  have hCsub : f '' uIcc 0 t ⊆ C :=
    subarc_subset_of_isPreconnected hc hi hC.isArc.isConnected.isPreconnected hCA ht
      (hf0 ▸ hC.left_mem) (hft ▸ hC.right_mem)
  rw [← hB.eq_of_subset harc hBsub, ← hC.eq_of_subset harc hCsub]

/-- **An arc inside a polygonal arc is polygonal.** The clause `def:admissible-graph` imposes on
nonboundary edges therefore survives both elementary operations: the two halves of a subdivided
edge, and each edge arc of a drawn ear, are arcs inside an arc already known to be polygonal. -/
theorem IsArcBetween.isPolygonal_of_subset (hA : IsArcBetween A p q) (hpoly : IsPolygonal A)
    (hB : IsArcBetween B p r) (hBA : B ⊆ A) (hpr : p ≠ r) : IsPolygonal B := by
  obtain ⟨ws, hws, hhead, hlast, hsub, harc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly hA.isArc.isConnected.isPreconnected hpr hA.left_mem
      (hBA hB.right_mem)
  rw [hA.eq_of_subset_of_isArcBetween hB harc hBA hsub hpr]
  exact ⟨ws, rfl⟩

/-- **An arc inside a polygonal arc is polygonal, wherever inside it sits.**

`IsArcBetween.isPolygonal_of_subset` asks the sub-arc to *start where the ambient one does*.
That is enough for the two halves of a subdivided edge, which share an end with the edge, and
not enough for the interior edges of a drawn ear, which touch neither end of the crosscut they
were cut out of. Two applications remove the restriction: the ambient arc's initial piece up to
the sub-arc's *far* parameter is polygonal by the special case, and the sub-arc is then an
initial piece of that one, read backwards.

Identifying the sub-arc with `f '' uIcc a b` is where `subarc_subset_of_isPreconnected_of_mem`
is spent: a connected subset of an arc containing two of its points contains everything the arc
traverses between them, and an arc containing an arc with the same ends is it. -/
theorem IsArcBetween.isPolygonal_of_subset' (hA : IsArcBetween A p q) (hpoly : IsPolygonal A)
    {r s : Plane} (hB : IsArcBetween B r s) (hBA : B ⊆ A) (hrs : r ≠ s) : IsPolygonal B := by
  obtain ⟨f, hc, hi, rfl, hf0, hf1⟩ := hA
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ I, f a = r := hBA hB.left_mem
  obtain ⟨b, hb, hfb⟩ : ∃ b ∈ I, f b = s := hBA hB.right_mem
  have hab : a ≠ b := fun h => hrs (by rw [← hfa, ← hfb, h])
  have hfull : IsArcBetween (f '' I) (f 0) (f 1) := ⟨f, hc, hi, rfl, rfl, rfl⟩
  -- `B` is exactly what the ambient arc traverses between the two parameters.
  have hBeq : f '' uIcc a b = B :=
    hB.eq_of_subset (by rw [← hfa, ← hfb]; exact isArcBetween_subarc_of_injOn_I hc hi ha hb hab)
      (subarc_subset_of_isPreconnected_of_mem hc hi hB.isArc.isConnected.isPreconnected hBA ha hb
        (by rw [hfa]; exact hB.left_mem) (by rw [hfb]; exact hB.right_mem))
  -- The far parameter, and the ambient arc's initial piece up to it.
  have hcI : max a b ∈ I := ⟨le_trans ha.1 (le_max_left a b), max_le ha.2 hb.2⟩
  have hc0 : (0 : ℝ) ≠ max a b := by
    intro h
    have ha0 : a = 0 := le_antisymm (by rw [h]; exact le_max_left a b) ha.1
    have hb0 : b = 0 := le_antisymm (by rw [h]; exact le_max_right a b) hb.1
    exact hab (ha0.trans hb0.symm)
  have harc1 : IsArcBetween (f '' uIcc 0 (max a b)) (f 0) (f (max a b)) :=
    isArcBetween_subarc_of_injOn_I hc hi zero_mem_I hcI hc0
  have hne1 : f 0 ≠ f (max a b) := fun h => hc0 (hi zero_mem_I hcI h)
  have hpoly1 : IsPolygonal (f '' uIcc 0 (max a b)) :=
    hfull.isPolygonal_of_subset hpoly harc1 (Set.image_mono (uIcc_subset_I zero_mem_I hcI)) hne1
  -- and `B` is an initial piece of *that*, read from the far end.
  have hBsub : B ⊆ f '' uIcc 0 (max a b) := by
    rw [← hBeq]
    refine Set.image_mono (Set.uIcc_subset_uIcc ?_ ?_)
    · exact Set.mem_uIcc.2 (Or.inl ⟨ha.1, le_max_left a b⟩)
    · exact Set.mem_uIcc.2 (Or.inl ⟨hb.1, le_max_right a b⟩)
  rcases max_cases a b with ⟨hmax, -⟩ | ⟨hmax, -⟩
  · have hcf : f (max a b) = r := by rw [hmax]; exact hfa
    have hB' : IsArcBetween B (f (max a b)) s := by rw [hcf]; exact hB
    exact harc1.reverse.isPolygonal_of_subset hpoly1 hB' hBsub (by rw [hcf]; exact hrs)
  · have hcf : f (max a b) = s := by rw [hmax]; exact hfb
    have hB' : IsArcBetween B (f (max a b)) r := by rw [hcf]; exact hB.reverse
    exact harc1.reverse.isPolygonal_of_subset hpoly1 hB' hBsub
      (by rw [hcf]; exact Ne.symm hrs)

end Schoenflies
