/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.AccessibleJoin
import Schoenflies.CrosscutCells
import Schoenflies.JordanSeparates
import Schoenflies.TwoArcs
import Schoenflies.Graph.K33Land

/-!
# The Jordan curve theorem

## Blueprint

* `Schoenflies.exists_first_meeting` — the workhorse of `lem:accessible-dense`.
-/

open Metric Set unitInterval

namespace Schoenflies

variable {C S U Ω : Set Plane} {u v : Plane}

/-! ### The first meeting of a polygonal chain with a closed set

A chain that starts off a closed obstacle `S` and eventually hits it has a *first* hit, and
the piece of the chain before it never leaves the component of `U` its start lies in. This is
the only reason `lem:accessible-dense` produces an *accessible* point rather than merely a
point of the curve, and it is proved by structural recursion on the vertex list: on the first
segment the first hit is the infimum of the hitting parameters, and if the first segment
misses `S` the segment itself is swallowed by the component and the recursion moves on. -/

/-- **The first meeting on a single segment.** The parameter interval of the hits is closed and
bounded below, so it has a least element; before it the segment stays in `U`, hence in the
component of `U` carrying the near endpoint. -/
theorem exists_first_meeting_segment (hS : IsClosed S) (hUS : Disjoint U S) (hu : u ∈ U)
    (hsub : segment ℝ u v ⊆ U ∪ S) (hmeet : (segment ℝ u v ∩ S).Nonempty) :
    ∃ p ∈ segment ℝ u v ∩ S, segment ℝ u p ⊆ segment ℝ u v ∧
      segment ℝ u p \ {p} ⊆ connectedComponentIn U u := by
  set φ : ℝ → Plane := fun t => u + t • (v - u) with hφ
  have hcont : Continuous φ := by fun_prop
  have hseg : segment ℝ u v = φ '' Icc 0 1 := segment_eq_image' ℝ u v
  -- The parameters at which the segment sits on the obstacle.
  set T : Set ℝ := Icc 0 1 ∩ φ ⁻¹' S with hT
  have hTclosed : IsClosed T := isClosed_Icc.inter (hS.preimage hcont)
  have hTne : T.Nonempty := by
    obtain ⟨z, hz, hzS⟩ := hmeet
    rw [hseg] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, hzS⟩
  have hTbdd : BddBelow T := ⟨0, fun x hx => hx.1.1⟩
  set t₀ : ℝ := sInf T with ht₀
  have ht₀T : t₀ ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht₀I : t₀ ∈ Icc (0 : ℝ) 1 := ht₀T.1
  have ht₀S : φ t₀ ∈ S := ht₀T.2
  -- The infimum is positive: the near endpoint is off the obstacle.
  have ht₀pos : 0 < t₀ := by
    rcases ht₀I.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hmem : φ 0 ∈ S := by rw [h]; exact ht₀S
      have hu' : φ 0 = u := by simp [hφ]
      rw [hu'] at hmem
      exact hUS.ne_of_mem hu hmem rfl
  -- Before the infimum the segment misses the obstacle, so it lies in `U`.
  have hbefore : φ '' Ico 0 t₀ ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans ht₀I.2⟩
    have : φ t ∉ S := fun hcon => absurd (csInf_le hTbdd ⟨htI, hcon⟩) (not_le.2 ht.2)
    exact (hsub (hseg ▸ mem_image_of_mem φ htI)).resolve_right this
  have hcomp : φ '' Ico 0 t₀ ⊆ connectedComponentIn U u := by
    refine (isPreconnected_Ico.image φ hcont.continuousOn).subset_connectedComponentIn ?_ hbefore
    exact ⟨0, ⟨le_rfl, ht₀pos⟩, by simp [hφ]⟩
  refine ⟨φ t₀, ⟨hseg ▸ mem_image_of_mem φ ht₀I, ht₀S⟩, ?_, ?_⟩
  · -- The initial piece of the segment is a piece of the segment.
    rw [segment_eq_image' ℝ u (φ t₀), hseg]
    rintro z ⟨θ, hθ, rfl⟩
    refine ⟨θ * t₀, ⟨mul_nonneg hθ.1 ht₀I.1, ?_⟩, ?_⟩
    · nlinarith [hθ.1, hθ.2, ht₀I.1, ht₀I.2]
    · simp only [hφ, add_sub_cancel_left, smul_smul]
  · rintro z ⟨hz, hzne⟩
    rw [mem_singleton_iff] at hzne
    rw [segment_eq_image' ℝ u (φ t₀)] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    replace hzne : u + θ • (φ t₀ - u) ≠ φ t₀ := hzne
    change u + θ • (φ t₀ - u) ∈ connectedComponentIn U u
    have hzeq : u + θ • (φ t₀ - u) = φ (θ * t₀) := by
      simp only [hφ, add_sub_cancel_left, smul_smul]
    rw [hzeq] at hzne ⊢
    -- The excluded point is exactly the parameter `1`, so the rest is strictly below `t₀`.
    have hθ1 : θ < 1 := by
      rcases hθ.2.lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [h, one_mul]) hzne
    exact hcomp ⟨θ * t₀, ⟨mul_nonneg hθ.1 ht₀I.1, by nlinarith⟩, rfl⟩

/-- **The first meeting of a polygonal chain with a closed set.** A chain that starts in `U`,
runs inside `U ∪ S` and meets the closed set `S` has an initial piece — again a chain from the
same start — that reaches `S` exactly at its far end and otherwise stays inside the *component*
of `U` carrying the start.

The chain is returned as `u :: ws`, so that "same start" is definitional and no
`List.head` obligation is ever produced. -/
theorem exists_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) :
    ∀ (u : Plane) (vs : List Plane), u ∈ U → poly (u :: vs) ⊆ U ∪ S →
      (poly (u :: vs) ∩ S).Nonempty →
      ∃ (ws : List Plane) (p : Plane), p ∈ poly (u :: vs) ∩ S ∧
        poly (u :: ws) ⊆ poly (u :: vs) ∧
        (u :: ws).getLast (List.cons_ne_nil u ws) = p ∧
        poly (u :: ws) \ {p} ⊆ connectedComponentIn U u
  | u, [], hu, _, hmeet => by
      -- A one-vertex chain carries only its vertex, which is in `U` and so off `S`.
      obtain ⟨z, hz, hzS⟩ := hmeet
      rw [poly_singleton, mem_singleton_iff] at hz
      exact absurd (hz ▸ hzS) (fun h => hUS.ne_of_mem hu h rfl)
  | u, v :: rest, hu, hsub, hmeet => by
      rw [poly_cons_cons] at hsub hmeet ⊢
      by_cases hfirst : (segment ℝ u v ∩ S).Nonempty
      · -- The obstacle is met already on the first segment.
        obtain ⟨p, hp, hpsub, hpcomp⟩ :=
          exists_first_meeting_segment hS hUS hu (hsub.trans' subset_union_left) hfirst
        exact ⟨[p], p, ⟨Or.inl hp.1, hp.2⟩, by rw [poly_pair]; exact hpsub.trans subset_union_left,
          rfl, by rw [poly_pair]; exact hpcomp⟩
      · -- The first segment misses the obstacle, so it is swallowed by the component.
        rw [not_nonempty_iff_eq_empty] at hfirst
        have hempty : ∀ z, z ∈ segment ℝ u v → z ∉ S := fun z hz hzS =>
          Set.eq_empty_iff_forall_notMem.1 hfirst z ⟨hz, hzS⟩
        have hsegU : segment ℝ u v ⊆ U := fun z hz =>
          (hsub (Or.inl hz)).resolve_right (hempty z hz)
        have hsegcomp : segment ℝ u v ⊆ connectedComponentIn U u :=
          (convex_segment u v).isPreconnected.subset_connectedComponentIn
            (left_mem_segment ℝ u v) hsegU
        have hvU : v ∈ U := hsegU (right_mem_segment ℝ u v)
        have hvcomp : connectedComponentIn U v = connectedComponentIn U u :=
          (connectedComponentIn_eq (hsegcomp (right_mem_segment ℝ u v))).symm
        have hrestsub : poly (v :: rest) ⊆ U ∪ S := hsub.trans' subset_union_right
        have hrestmeet : (poly (v :: rest) ∩ S).Nonempty := by
          obtain ⟨z, hz, hzS⟩ := hmeet
          rcases hz with hz | hz
          · exact absurd hzS (hempty z hz)
          · exact ⟨z, hz, hzS⟩
        obtain ⟨ws, p, hp, hwsub, hwlast, hwcomp⟩ :=
          exists_first_meeting hS hUS v rest hvU hrestsub hrestmeet
        refine ⟨v :: ws, p, ⟨Or.inr hp.1, hp.2⟩, ?_, ?_, ?_⟩
        · rw [poly_cons_cons]
          exact union_subset_union_right _ hwsub
        · rw [List.getLast_cons (List.cons_ne_nil v ws)]; exact hwlast
        · rw [poly_cons_cons]
          rintro z ⟨hz | hz, hzne⟩
          · exact hsegcomp hz
          · exact hvcomp ▸ hwcomp ⟨hz, hzne⟩

/-- **The first meeting, as a simple arc.** The initial piece of the chain is re-extracted as a
*simple polygonal arc* from the first meeting point back to the start; it meets `S` only at
that point, and everything else on it stays in the component of `U` carrying the start.

This is the form both consumers want: `lem:accessible-dense` reads off the accessibility of `p`,
and the tripod construction of `thm:jordan` needs the arc itself. -/
theorem exists_arc_to_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) {u : Plane}
    {vs : List Plane} (hu : u ∈ U) (hsub : poly (u :: vs) ⊆ U ∪ S)
    (hmeet : (poly (u :: vs) ∩ S).Nonempty) :
    ∃ p ∈ poly (u :: vs) ∩ S, ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P p u ∧
      P ⊆ poly (u :: vs) ∧ P \ {p} ⊆ connectedComponentIn U u := by
  obtain ⟨ws, p, hp, hwsub, hwlast, hwcomp⟩ := exists_first_meeting hS hUS u vs hu hsub hmeet
  have hne : (u :: ws) ≠ [] := List.cons_ne_nil u ws
  have hpY : p ∈ poly (u :: ws) := hwlast ▸ getLast_mem_poly hne
  have huY : u ∈ poly (u :: ws) := head_mem_poly hne
  have hpu : p ≠ u := fun hcon => hUS.ne_of_mem hu (hcon ▸ hp.2) rfl
  obtain ⟨qs, hqs, hqhead, hqlast, hqsub, hqcomp, hqarc⟩ :=
    exists_simple_poly_of_isPolygonal_pinned ⟨u :: ws, rfl⟩ (isConnected_poly hne).2 hpu hpY huY
      hwcomp
  exact ⟨p, hp, poly qs, ⟨qs, rfl⟩, hqarc, hqsub.trans hwsub, hqcomp⟩

/-- The accessibility statement `lem:accessible-dense` produces: the first meeting point is
polygonally accessible from the component of `U` the chain started in. -/
theorem polyAccessible_first_meeting (hS : IsClosed S) (hUS : Disjoint U S) {u : Plane}
    {vs : List Plane} (hu : u ∈ U) (hsub : poly (u :: vs) ⊆ U ∪ S)
    (hmeet : (poly (u :: vs) ∩ S).Nonempty) :
    ∃ p ∈ poly (u :: vs) ∩ S, PolyAccessible (connectedComponentIn U u) p := by
  obtain ⟨ws, p, hp, -, hwlast, hwcomp⟩ := exists_first_meeting hS hUS u vs hu hsub hmeet
  have hpu : p ≠ u := fun hcon => hUS.ne_of_mem hu (hcon ▸ hp.2) rfl
  exact ⟨p, hp, polyAccessible_of_poly' (List.cons_ne_nil u ws) hwlast
    (fun hcon => hpu hcon.symm) hwcomp⟩

/-! ### An accessible point is a limit of the region

The half of `thm:jordan`'s boundary clause that `lem:accessible-dense` supplies: an accessible
point of the curve is in the closure of the region it is accessible from. The access chain is
connected and carries a point of the region, so the accessible point is not isolated on it. -/

/-- **An accessible point off the region lies in its closure.** -/
theorem PolyAccessible.mem_closure {a : Plane} (h : PolyAccessible Ω a) (ha : a ∉ Ω) :
    a ∈ closure Ω := by
  obtain ⟨vs, hvs, hhead, hlast, hint⟩ := h
  refine closure_mono hint ?_
  have haY : a ∈ poly vs := hhead ▸ head_mem_poly hvs
  have hzY : vs.getLast hvs ∈ poly vs := getLast_mem_poly hvs
  have hzne : vs.getLast hvs ≠ a := fun hcon => ha (hcon ▸ hlast)
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra hcon
  push Not at hcon
  -- Were `a` isolated on the chain, the ball around it and the complement of `{a}` would
  -- split the chain into two nonempty relatively open pieces — but the chain is connected.
  obtain ⟨w, hwY, hwball, hwne⟩ :=
    (isConnected_poly hvs).2 (Metric.ball a ε) {a}ᶜ Metric.isOpen_ball isOpen_compl_singleton
      (fun z _ => by
        rcases eq_or_ne z a with rfl | hza
        · exact Or.inl (Metric.mem_ball_self hε)
        · exact Or.inr hza)
      ⟨a, haY, Metric.mem_ball_self hε⟩ ⟨vs.getLast hvs, hzY, hzne⟩
  have := hcon w ⟨hwY, hwne⟩
  rw [Metric.mem_ball, dist_comm] at hwball
  exact absurd hwball (not_lt.2 this)

/-! ### The curve with an open subarc deleted

`lem:jordan-circle`'s "two points cut the curve into two arcs" in the form
`lem:accessible-dense` consumes it: the complement *in the curve* of a relatively open subarc
is one closed arc. The proof is the parameter bookkeeping of `Schoenflies/TwoArcs.lean` — no
new topology. -/

/-- **The curve minus an open subarc is the complementary closed arc.** -/
theorem IsLoop.compl_openArc {f : ℝ → Plane} (hf : IsLoop f) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hb1 : b ≠ 1) (hab : a < b) :
    f '' I \ f '' Ioo a b = f '' Icc 0 a ∪ f '' Icc b 1 := by
  have halt1 : a < 1 := lt_of_lt_of_le hab hb.2
  have hmI : ∀ m ∈ Ioo a b, m ∈ I ∧ m ≠ 1 := fun m hm =>
    ⟨⟨ha.1.trans hm.1.le, hm.2.le.trans hb.2⟩, ne_of_lt (lt_of_lt_of_le hm.2 hb.2)⟩
  -- No parameter outside `(a, b)` carries a point of the open subarc.
  have hfront : ∀ s ∈ Icc (0 : ℝ) a, f s ∉ f '' Ioo a b := by
    rintro s hs ⟨m, hm, hms⟩
    have hsI : s ∈ I := ⟨hs.1, hs.2.trans ha.2⟩
    have hs1 : s ≠ 1 := ne_of_lt (lt_of_le_of_lt hs.2 halt1)
    have := hf.injective_before_finish (hmI m hm).1 hsI (hmI m hm).2 hs1 hms
    exact absurd (this ▸ hm.1) (not_lt.2 hs.2)
  have hback : ∀ t ∈ Icc b (1 : ℝ), f t ∉ f '' Ioo a b := by
    rintro t ht ⟨m, hm, hms⟩
    have htI : t ∈ I := ⟨hb.1.trans ht.1, ht.2⟩
    rcases eq_or_ne t 1 with rfl | ht1
    · -- The finish carries the start, and the start is strictly before the open subarc.
      have := hf.injective_before_finish (hmI m hm).1 zero_mem_I (hmI m hm).2 one_ne_zero.symm
        (hms.trans hf.closes.symm)
      exact absurd (this ▸ hm.1) (not_lt.2 ha.1)
    · have := hf.injective_before_finish (hmI m hm).1 htI (hmI m hm).2 ht1 hms
      exact absurd (this ▸ hm.2) (not_lt.2 ht.1)
  apply Subset.antisymm
  · rintro z ⟨⟨t, htI, rfl⟩, hz⟩
    rcases le_or_gt t a with h | h
    · exact mem_union_left _ (mem_image_of_mem f ⟨htI.1, h⟩)
    · rcases le_or_gt b t with h' | h'
      · exact mem_union_right _ (mem_image_of_mem f ⟨h', htI.2⟩)
      · exact absurd (mem_image_of_mem f (⟨h, h'⟩ : t ∈ Ioo a b)) hz
  · rintro z (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨mem_image_of_mem f ⟨hs.1, hs.2.trans ha.2⟩, hfront s hs⟩
    · exact ⟨mem_image_of_mem f ⟨hb.1.trans ht.1, ht.2⟩, hback t ht⟩

/-! ### Density of accessible points, `lem:accessible-dense`

The blueprint's proof verbatim: shrink the given relatively open arc to one whose closure is
inside it, delete it from the curve to leave a simple arc, join `x` to a point of another
component in the (connected) complement of that arc by a polygonal chain, and take the first
meeting of the chain with the curve.

The shrinking step is done on parameters. Instead of "an open arc `J₀` with closure inside
`J`" the statement below takes the open subarc `f '' Ioo a b` with `0 < a < b < 1`, which is
already strictly inside the parameter interval; every relatively open piece of the curve
contains such a subarc (`Schoenflies.basic_piece_inside_ball` supplies one inside any ball),
and that is all the blueprint's `J₀` is for. -/

/-- **`lem:accessible-dense`, in the parameter form the proof produces.** Every open subarc
strictly inside the parameter interval carries a point accessible from the component of `x`.

`harc` is `thm:arc-complement`: the complement of a simple arc is connected. -/
theorem exists_polyAccessible_openArc (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    {f : ℝ → Plane} (hf : IsLoop f) {x : Plane} (hx : x ∉ f '' I)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ p ∈ f '' Ioo a b, PolyAccessible (connectedComponentIn (f '' I)ᶜ x) p := by
  have hCurve : IsJordanCurve (f '' I) := ⟨f, hf, rfl⟩
  have haI : a ∈ I := ⟨ha.le, (hab.trans hb).le⟩
  have hbI : b ∈ I := ⟨(ha.trans hab).le, hb.le⟩
  -- The curve minus the open subarc is a simple arc, so its complement is connected.
  set D : Set Plane := f '' Icc 0 a ∪ f '' Icc b 1 with hD
  have hDeq : f '' I \ f '' Ioo a b = D := hf.compl_openArc haI hbI (ne_of_lt hb) hab
  have hDarc : IsArc D :=
    (hf.outside_IsArcBetween haI hbI (ne_of_lt (hab.trans hb)) (ne_of_lt hb) hab).isArc
  have hDconn : IsConnected Dᶜ := harc D hDarc
  have hDopen : IsOpen Dᶜ := hDarc.isClosed.isOpen_compl
  have hDsub : D ⊆ f '' I := hDeq ▸ diff_subset
  have hxD : x ∈ Dᶜ := fun hcon => hx (hDsub hcon)
  -- A point in another component of the complement of the curve.
  obtain ⟨y, hyC, hyne⟩ : ∃ y ∈ (f '' I)ᶜ,
      connectedComponentIn (f '' I)ᶜ y ≠ connectedComponentIn (f '' I)ᶜ x := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := hCurve.exists_connectedComponentIn_ne
    by_cases h : connectedComponentIn (f '' I)ᶜ u₁ = connectedComponentIn (f '' I)ᶜ x
    · exact ⟨u₂, hu₂, fun hcon => hne (h.trans hcon.symm)⟩
    · exact ⟨u₁, hu₁, h⟩
  have hyD : y ∈ Dᶜ := fun hcon => hyC (hDsub hcon)
  obtain ⟨vs, hvs, hvsub, hvhead, hvlast⟩ :=
    exists_poly_of_isPreconnected hDopen hDconn.isPreconnected hxD hyD
  -- Present the chain as one headed by `x`, which is what the first-meeting lemma consumes.
  have hlist : x :: vs.tail = vs := by rw [← hvhead]; exact List.cons_head_tail hvs
  have hsubC : poly (x :: vs.tail) ⊆ (f '' I)ᶜ ∪ f '' I := fun z _ => em' (z ∈ f '' I)
  have hmeet : (poly (x :: vs.tail) ∩ f '' I).Nonempty := by
    rw [hlist]
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    -- Otherwise the chain avoids the curve, so it lies in one component — but its two ends
    -- were chosen in different ones.
    have hsubcompl : poly vs ⊆ (f '' I)ᶜ := fun z hz hzC =>
      Set.eq_empty_iff_forall_notMem.1 hcon z ⟨hz, hzC⟩
    have hone := (isConnected_poly hvs).2.subset_connectedComponentIn
      (hvhead ▸ head_mem_poly hvs) hsubcompl
    exact hyne (connectedComponentIn_eq (hone (hvlast ▸ getLast_mem_poly hvs))).symm
  obtain ⟨p, hp, hacc⟩ :=
    polyAccessible_first_meeting hCurve.isClosed disjoint_compl_left hx hsubC hmeet
  rw [hlist] at hp
  refine ⟨p, ?_, hacc⟩
  -- The first meeting is off the deleted arc, so it lies on the open subarc.
  by_contra hcon
  exact absurd (hDeq ▸ (⟨hp.2, hcon⟩ : p ∈ f '' I \ f '' Ioo a b)) (hvsub hp.1)

/-- **`lem:accessible-dense` (density of accessible points).** The points of `C` reachable from
`x` by a polygonal arc meeting `C` only at its endpoint are dense in `C`. -/
theorem accessible_dense (harc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ)
    (hC : IsJordanCurve C) {x : Plane} (hx : x ∉ C) :
    C ⊆ closure {p | p ∈ C ∧ PolyAccessible (connectedComponentIn Cᶜ x) p} := by
  obtain ⟨f, hf, rfl⟩ := hC
  intro z hz
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨c, d, hzcd, hball⟩ := basic_piece_inside_ball hf.continuousOn hz hr
  obtain ⟨w, hw, -⟩ := hzcd
  -- Trim the basic piece to an open subarc strictly inside the parameter interval.
  have h1 : c < w := hw.1.1
  have h2 : w < d := hw.1.2
  have h3 : (0 : ℝ) ≤ w := hw.2.1
  have h4 : w ≤ 1 := hw.2.2
  have hαβ : max c 0 < min d 1 := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by norm_num⟩⟩
  have hc0 : (0 : ℝ) ≤ max c 0 := le_max_right c 0
  have hd1 : min d 1 ≤ 1 := min_le_right d 1
  have hct : c ≤ max c 0 := le_max_left c 0
  have hdt : min d 1 ≤ d := min_le_left d 1
  set a : ℝ := max c 0 + (min d 1 - max c 0) / 3 with hadef
  set b : ℝ := max c 0 + 2 * (min d 1 - max c 0) / 3 with hbdef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hb1 : b < 1 := by rw [hbdef]; linarith
  have hsub : Ioo a b ⊆ Ioo c d ∩ I := by
    rintro t ⟨ht1, ht2⟩
    rw [hadef] at ht1
    rw [hbdef] at ht2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨p, hpIoo, hacc⟩ := exists_polyAccessible_openArc harc hf hx ha0 hab hb1
  refine ⟨p, ⟨image_mono (hsub.trans inter_subset_right) hpIoo, hacc⟩, ?_⟩
  rw [dist_comm]
  exact hball (image_mono hsub hpIoo)

/-! ### The tripod at a component

The blueprint builds the three internally disjoint branches from `x_i` to the three terminals
by overlaying the three access arcs, taking a minimal connected spanning subgraph, and reading
off its unique degree-three vertex (`lem:three-leaf-tree`). The construction below reaches the
same object without a graph: join the first two terminals by a *crosscut* — a simple polygonal
arc meeting the curve exactly at its two endpoints (`lem:accessible-endpoints` in crosscut
form) — then run a chain from the third terminal into the region and on to a point of that
crosscut, and take its **first meeting** with the crosscut. That meeting point is the branch
vertex; cutting the crosscut there (`IsArcBetween.exists_split`) supplies the other two
branches.

The output is the same three internally disjoint arcs, with the same two properties every
later step uses: each meets the curve only at its terminal, and two of them meet only at the
branch vertex. -/

/-- **Three internally disjoint arcs from one point of a region to three accessible points of
its complementary set.** The blueprint's `T_i` with its three branches, for `Ω` the `i`-th
component and the three points the terminals `p_{ij}`. -/
theorem exists_tripod (hΩopen : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hCclosed : IsClosed C)
    (hdisj : Disjoint Ω C) {a b c : Plane} (haC : a ∈ C) (hbC : b ∈ C) (hcC : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : PolyAccessible Ω a) (hb : PolyAccessible Ω b) (hc : PolyAccessible Ω c) :
    ∃ x ∈ Ω, ∃ Ta Tb Tc : Set Plane,
      IsArcBetween Ta x a ∧ IsArcBetween Tb x b ∧ IsArcBetween Tc x c ∧
        Ta \ {a} ⊆ Ω ∧ Tb \ {b} ⊆ Ω ∧ Tc \ {c} ⊆ Ω ∧
        Ta ∩ Tb ⊆ {x} ∧ Ta ∩ Tc ⊆ {x} ∧ Tb ∩ Tc ⊆ {x} := by
  classical
  -- The crosscut from `a` to `b`.
  obtain ⟨ws, hws, hwhead, hwlast, hwΩ, hwarc, hwC⟩ :=
    exists_crosscut_of_polyAccessible hΩopen hΩconn hdisj hab haC hbC ha hb
  set A : Set Plane := poly ws with hA
  have hAclosed : IsClosed A := (isCompact_poly ws).isClosed
  have hcA : c ∉ A := fun hcon => by
    rcases (hwC ▸ (⟨hcon, hcC⟩ : c ∈ A ∩ C) : c ∈ ({a, b} : Set Plane)) with h | h
    exacts [hac h.symm, hbc h.symm]
  -- The access chain from `c`, continued inside `Ω` to an interior point of the crosscut.
  obtain ⟨cs, hcs, hchead, hclast, hcsub⟩ := hc
  obtain ⟨w, hwmem⟩ := hwarc.nonempty_diff
  have hwΩ' : w ∈ Ω := hwΩ hwmem
  obtain ⟨ls, hls, hlsub, hlhead, hllast⟩ :=
    exists_poly_of_isPreconnected hΩopen hΩconn hclast hwΩ'
  have hcatlist : cs ++ ls = cs ++ cs.getLast hcs :: ls.tail := by
    rw [← hlhead, List.cons_head_tail hls]
  have hcat : poly (cs ++ ls) = poly cs ∪ poly ls := by
    rw [hcatlist, poly_append hcs _ _ rfl, ← hlhead, List.cons_head_tail hls]
  -- The full chain starts at `c`, runs in `Ω ∪ {c}`, and reaches the crosscut.
  have hfullne : cs ++ ls ≠ [] := by simp [hcs]
  have hfullhead : (cs ++ ls).head hfullne = c := by
    rw [List.head_append_of_ne_nil hcs, hchead]
  have hfulllist : c :: (cs ++ ls).tail = cs ++ ls := by
    rw [← hfullhead]; exact List.cons_head_tail hfullne
  set U : Set Plane := (Ω ∪ {c}) \ A with hU
  have hUS : Disjoint U A := disjoint_sdiff_left
  have hcU : c ∈ U := ⟨Or.inr rfl, hcA⟩
  have hfullsub : poly (c :: (cs ++ ls).tail) ⊆ U ∪ A := by
    rw [hfulllist, hcat]
    rintro z hz
    have hzΩ : z ∈ Ω ∪ {c} := by
      rcases hz with hz | hz
      · rcases eq_or_ne z c with rfl | hzc
        · exact Or.inr rfl
        · exact Or.inl (hcsub ⟨hz, hzc⟩)
      · exact Or.inl (hlsub hz)
    rcases em (z ∈ A) with h | h
    · exact Or.inr h
    · exact Or.inl ⟨hzΩ, h⟩
  have hfullmeet : (poly (c :: (cs ++ ls).tail) ∩ A).Nonempty := by
    rw [hfulllist, hcat]
    exact ⟨w, Or.inr (hllast ▸ getLast_mem_poly hls), hwmem.1⟩
  obtain ⟨x, hx, P, -, hParc, -, hPcomp⟩ :=
    exists_arc_to_first_meeting hAclosed hUS hcU hfullsub hfullmeet
  rw [hfulllist, hcat] at hx
  -- The branch vertex is interior to the crosscut.
  have hxU : ∀ z ∈ P, z ≠ x → z ∈ U := fun z hz hzx =>
    connectedComponentIn_subset _ _ (hPcomp ⟨hz, hzx⟩)
  have hxΩ : x ∈ Ω := by
    rcases hx.1 with hz | hz
    · rcases eq_or_ne x c with rfl | hxc
      · exact absurd hx.2 hcA
      · exact hcsub ⟨hz, hxc⟩
    · exact hlsub hz
  have hPC : P ∩ C = {c} := by
    apply Subset.antisymm
    · rintro z ⟨hzP, hzC⟩
      rcases eq_or_ne z x with rfl | hzx
      · exact absurd rfl (hdisj.ne_of_mem hxΩ hzC)
      · rcases (hxU z hzP hzx).1 with h | h
        · exact absurd rfl (hdisj.ne_of_mem h hzC)
        · exact h
    · rintro z rfl; exact ⟨hParc.right_mem, hcC⟩
  have hPΩ : P \ {c} ⊆ Ω := by
    rintro z ⟨hzP, hzc⟩
    rcases eq_or_ne z x with rfl | hzx
    · exact hxΩ
    · exact ((hxU z hzP hzx).1).resolve_right hzc
  have hPA : P ∩ A ⊆ {x} := by
    rintro z ⟨hzP, hzA⟩
    by_contra hzx
    exact (hxU z hzP (fun h => hzx (by rw [h]; rfl))).2 hzA
  -- Cut the crosscut at the branch vertex.
  have hxa : x ≠ a := fun hcon => hdisj.ne_of_mem hxΩ (hcon ▸ haC) rfl
  have hxb : x ≠ b := fun hcon => hdisj.ne_of_mem hxΩ (hcon ▸ hbC) rfl
  obtain ⟨A₁, A₂, hA₁, hA₂, hAcov, hAmeet⟩ := hwarc.exists_split hx.2 hxa hxb
  have hbA₁ : b ∉ A₁ := fun hcon => hxb (by
    have : b ∈ A₁ ∩ A₂ := ⟨hcon, hA₂.right_mem⟩
    rw [hAmeet] at this; exact this.symm)
  have haA₂ : a ∉ A₂ := fun hcon => hxa (by
    have : a ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, hcon⟩
    rw [hAmeet] at this; exact this.symm)
  have hAΩ : A \ {a, b} ⊆ Ω := hwΩ
  refine ⟨x, hxΩ, A₁, A₂, P, hA₁.reverse, hA₂, hParc, ?_, ?_, hPΩ, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hza⟩
    refine hAΩ ⟨hAcov ▸ mem_union_left _ hz, ?_⟩
    rintro (rfl | rfl)
    exacts [hza rfl, hbA₁ hz]
  · rintro z ⟨hz, hzb⟩
    refine hAΩ ⟨hAcov ▸ mem_union_right _ hz, ?_⟩
    rintro (rfl | rfl)
    exacts [haA₂ hz, hzb rfl]
  · exact hAmeet.subset
  · exact fun z hz => hPA ⟨hz.2, hAcov ▸ mem_union_left _ hz.1⟩
  · exact fun z hz => hPA ⟨hz.2, hAcov ▸ mem_union_right _ hz.1⟩

end Schoenflies
