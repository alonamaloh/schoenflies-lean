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
theorem subarc_subset_of_isPreconnected (hc : ContinuousOn f I) (hi : InjOn f I)
    (hC : IsPreconnected C) (hCA : C ⊆ f '' I) (ht : t ∈ I) (h0 : f 0 ∈ C) (htC : f t ∈ C) :
    f '' uIcc 0 t ⊆ C := by
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
  have h0mem : (0 : ℝ) ∈ Subtype.val '' (Set.restrict I f ⁻¹' C) := ⟨⟨0, zero_mem_I⟩, h0, rfl⟩
  have htmem : t ∈ Subtype.val '' (Set.restrict I f ⁻¹' C) := ⟨⟨t, ht⟩, htC, rfl⟩
  have hsub : uIcc 0 t ⊆ Subtype.val '' (Set.restrict I f ⁻¹' C) :=
    himg.ordConnected.uIcc_subset h0mem htmem
  rintro z ⟨s, hs, rfl⟩
  obtain ⟨⟨s', hs'⟩, hs'C, rfl⟩ := hsub hs
  exact hs'C

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

end Schoenflies
