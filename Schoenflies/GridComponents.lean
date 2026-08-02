/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.GridAttach

/-!
# Finitely many components of `cover l ∖ C` — the `hcov` of `prop:local-grid-attachment`

The joining loop of `prop:local-grid-attachment` ends with *"Since there are only finitely
many components, finitely many repetitions produce a 2-connected graph `H_n` for which
`|H_n| ∖ C` is connected."* `Schoenflies/GridAttach.lean` ran the loop
(`isConnected_union_joins`) but took the finiteness as the hypothesis `hcov` of
`gridAttachGraph_isConnected_diff`: a finite list `reps` of representatives such that every
point of `cover l ∖ C` is joined, inside `cover l ∖ C`, to one of them by a preconnected
subset. This module produces that list.

## What the finiteness actually rests on — read this before consuming the module

The blueprint's sentence is **not** a general fact about a finite union of segments minus a
closed set. `C` is an arbitrary Jordan curve: a single straight segment can meet a closed
set in a Cantor set, and then `segment ∖ C` has uncountably many components. The blueprint
never says why `|L| ∖ C` has finitely many components; the reason is implicit in `L` being a
*drawing* that contains `C` as a subcomplex. Two edge arcs of a drawing meet only in shared
endpoints, so each polygonal nonboundary edge meets `C` — a union of finitely many boundary
edge arcs — in finitely many points; the auxiliary crosscut has its open part inside a face,
disjoint from the graph and hence from `C`, so it meets `C` in at most its two endpoints;
and the grid lies in `W ⊆ D`, disjoint from `C` outright. That per-segment finiteness,
`MeetsFinitely`, is the weakest hypothesis under which the blueprint's count is true, and it
is the hypothesis everything here is proved from. It is a statement about `Γ`'s drawing,
which this module never sees — like the `hΓ` of `gridAttachGraph_isTwoConnected`, it is
discharged by the module that assembles the proposition from `Γ`'s invariants.

Under `MeetsFinitely` the count is a theorem, proved here with no hypothesis left: a
nondegenerate segment is `lineMap '' Icc 0 1` with `lineMap` injective, so the parameters
hitting `C` form a finite set `T ⊆ Icc 0 1`; midpoints of pairs drawn from
`T ∪ {0, 1}` give a finite list of parameters meeting every component of `Icc 0 1 ∖ T`
(`exists_reps_Icc_diff`), and their images represent every component of `segment ∖ C`
(`exists_reps_seg_diff`). Summing over the list of segments gives `exists_reps_cover_diff`,
and `exists_reps_hcov` restates it for the exact list
`gsegs ++ localGridEdges p s (localGridCount s ε)` that
`gridAttachGraph_isConnected_diff` quantifies over — its second conjunct is *syntactically*
that theorem's `hcov`. The composition `gridAttachGraph_isConnected_diff_of_meetsFinitely`
is the acceptance test: from `MeetsFinitely gsegs C`, grid-disjointness, and joining arcs
available at every point of the cover (which `lem:polygonal-connected` supplies inside `D`),
clause 1 of the proposition follows with no `hcov` left.

## Blueprint

* the joining loop's *"since there are only finitely many components"* in the proof of
  `prop:local-grid-attachment` — `Schoenflies.MeetsFinitely` (the implicit drawing fact it
  rests on), `Schoenflies.exists_reps_Icc_diff`, `Schoenflies.exists_reps_seg_diff`,
  `Schoenflies.exists_reps_cover_diff`, and the component form
  `Schoenflies.exists_reps_connectedComponentIn`.
* the `hcov` of `Schoenflies.gridAttachGraph_isConnected_diff` —
  `Schoenflies.exists_reps_hcov`, discharged end to end in
  `Schoenflies.gridAttachGraph_isConnected_diff_of_meetsFinitely`.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ## The hypothesis the blueprint spends silently

Each listed segment meets `C` in finitely many points. For the segments
`prop:local-grid-attachment` actually feeds the loop this is a drawing invariant: nonboundary
edges meet the subcomplex `C` only at shared vertices, the crosscut's open part lies in a
face, and the grid misses `C` entirely. For an arbitrary segment it can fail — a segment can
meet a wild `C` in a Cantor set — which is why it is a hypothesis and not a theorem here. -/

/-- Every listed segment meets `C` in a finite set. This is what makes the component count of
`cover l ∖ C` finite: without it a single segment can meet a closed set in a Cantor set. -/
def MeetsFinitely (l : List Piece) (C : Set Plane) : Prop :=
  ∀ P ∈ l, (P.seg ∩ C).Finite

/-- Segments disjoint from `C` meet it finitely — the grid's case, since the grid lies in
`W ⊆ D` and `C ∩ D = ∅`. -/
theorem MeetsFinitely.of_disjoint {l : List Piece} {C : Set Plane}
    (h : Disjoint (cover l) C) : MeetsFinitely l C := by
  intro P hP
  have hempty : P.seg ∩ C ⊆ (∅ : Set Plane) := fun x hx =>
    (Set.disjoint_left.1 h (mem_cover_iff.2 ⟨P, hP, hx.1⟩)) hx.2
  exact Set.finite_empty.subset hempty

theorem MeetsFinitely.append {l l' : List Piece} {C : Set Plane}
    (h : MeetsFinitely l C) (h' : MeetsFinitely l' C) : MeetsFinitely (l ++ l') C := by
  intro P hP
  rcases List.mem_append.1 hP with hP' | hP'
  exacts [h P hP', h' P hP']

/-! ## The interval: finitely many representatives for `Icc a b ∖ T`

The components of `Icc a b ∖ T`, `T` finite, are intervals whose endpoints lie in
`T ∪ {a, b}`; the midpoint of the two neighbours of a point stays in its component. So the
midpoints of all pairs drawn from `T ∪ {a, b}` — a finite list — meet every component, and
the interval from a point to its midpoint witnesses the join. No component is ever named:
the witness `uIcc t r ⊆ Icc a b \ T` is what the plane statement consumes. -/

/-- **Finitely many representatives for an interval minus a finite set.** Every point of
`Icc a b ∖ T` is joined to one of finitely many representatives by a subinterval avoiding
`T` — the interval-level form of *"there are only finitely many components"*. -/
theorem exists_reps_Icc_diff (a b : ℝ) {T : Set ℝ} (hT : T.Finite) :
    ∃ reps : List ℝ, (∀ r ∈ reps, r ∈ Icc a b \ T) ∧
      ∀ t ∈ Icc a b \ T, ∃ r ∈ reps, uIcc t r ⊆ Icc a b \ T := by
  classical
  -- endpoints of components lie among the removed points and the two ends
  set F : Finset ℝ := insert a (insert b hT.toFinset) with hF
  set cands : Finset ℝ :=
    ((F ×ˢ F).image fun q => (q.1 + q.2) / 2).filter (fun x => x ∈ Icc a b \ T) with hcands
  refine ⟨cands.toList, ?_, ?_⟩
  · intro r hr
    rw [Finset.mem_toList, hcands, Finset.mem_filter] at hr
    exact hr.2
  · rintro t ⟨htab, htT⟩
    have haF : a ∈ F := Finset.mem_insert_self _ _
    have hbF : b ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    -- the two neighbours of `t`: the largest marked point at or below it, the smallest at
    -- or above it
    set A : Finset ℝ := F.filter (· ≤ t) with hA
    set B : Finset ℝ := F.filter (t ≤ ·) with hB
    have hAne : A.Nonempty := ⟨a, Finset.mem_filter.2 ⟨haF, htab.1⟩⟩
    have hBne : B.Nonempty := ⟨b, Finset.mem_filter.2 ⟨hbF, htab.2⟩⟩
    set α := A.max' hAne with hα
    set β := B.min' hBne with hβ
    have hαF : α ∈ F := (Finset.mem_filter.1 (A.max'_mem hAne)).1
    have hβF : β ∈ F := (Finset.mem_filter.1 (B.min'_mem hBne)).1
    have hαt : α ≤ t := (Finset.mem_filter.1 (A.max'_mem hAne)).2
    have htβ : t ≤ β := (Finset.mem_filter.1 (B.min'_mem hBne)).2
    have haα : a ≤ α := A.le_max' a (Finset.mem_filter.2 ⟨haF, htab.1⟩)
    have hβb : β ≤ b := B.min'_le b (Finset.mem_filter.2 ⟨hbF, htab.2⟩)
    -- no removed point lies strictly between the two neighbours
    have hTgap : ∀ x ∈ T, x ∉ Ioo α β := by
      intro x hx hxo
      have hxF : x ∈ F := Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hT.mem_toFinset.2 hx))
      rcases le_or_gt x t with hxt | htx
      · exact absurd (A.le_max' x (Finset.mem_filter.2 ⟨hxF, hxt⟩)) (not_le.2 hxo.1)
      · exact absurd (B.min'_le x (Finset.mem_filter.2 ⟨hxF, htx.le⟩)) (not_le.2 hxo.2)
    -- the representative: the midpoint of the two neighbours
    set m := (α + β) / 2 with hm
    have hαm : α ≤ m := by rw [hm]; linarith [hαt.trans htβ]
    have hmβ : m ≤ β := by rw [hm]; linarith [hαt.trans htβ]
    have hmab : m ∈ Icc a b := ⟨haα.trans hαm, hmβ.trans hβb⟩
    have hmT : m ∉ T := by
      rcases eq_or_lt_of_le (hαt.trans htβ) with heq | hlt
      · -- the component is a single point: the midpoint is `t` itself
        have : m = t := by rw [hm, ← heq]; linarith [le_antisymm hαt (heq ▸ htβ)]
        exact this ▸ htT
      · exact fun hmem => hTgap m hmem ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩
    have hmcand : m ∈ cands := by
      rw [hcands, Finset.mem_filter]
      exact ⟨Finset.mem_image.2 ⟨(α, β), Finset.mem_product.2 ⟨hαF, hβF⟩, rfl⟩,
        hmab, hmT⟩
    refine ⟨m, Finset.mem_toList.2 hmcand, fun u hu => ?_⟩
    have hu' : u ∈ Icc α β := uIcc_subset_Icc ⟨hαt, htβ⟩ ⟨hαm, hmβ⟩ hu
    refine ⟨⟨haα.trans hu'.1, hu'.2.trans hβb⟩, fun huT => ?_⟩
    -- a removed point inside the join interval would have to be a neighbour itself, but
    -- the join interval stays strictly between removed neighbours
    rcases eq_or_lt_of_le hu'.1 with huα | hαu
    · -- `u = α ∈ T`: then `α < t` and `α < m`, so `α` is below the join interval
      have hαT : α ∈ T := huα ▸ huT
      have hαlt : α < t := lt_of_le_of_ne hαt (fun h => htT (h ▸ hαT))
      have hαβ : α < β := hαlt.trans_le htβ
      have hαm' : α < m := by rw [hm]; linarith
      rcases mem_uIcc.1 hu with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact absurd (huα ▸ h1) (not_le.2 hαlt)
      · exact absurd (huα ▸ h1) (not_le.2 hαm')
    · rcases eq_or_lt_of_le hu'.2 with huβ | huβ'
      · -- `u = β ∈ T`: symmetric, `β` is above the join interval
        have hβT : β ∈ T := huβ ▸ huT
        have hβgt : t < β := lt_of_le_of_ne htβ (fun h => htT (h.symm ▸ hβT))
        have hαβ : α < β := hαt.trans_lt hβgt
        have hmβ' : m < β := by rw [hm]; linarith
        rcases mem_uIcc.1 hu with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact absurd (huβ ▸ h2) (not_le.2 hmβ')
        · exact absurd (huβ ▸ h2) (not_le.2 hβgt)
      · exact hTgap u huT ⟨hαu, huβ'⟩

/-! ## One segment, then a list of them -/

/-- **Finitely many representatives for one segment minus `C`.** If the segment meets `C`
finitely, finitely many of its points meet every component of `segment ∖ C`, each join
witnessed by a preconnected subset. -/
theorem exists_reps_seg_diff (P : Piece) {C : Set Plane} (hfin : (P.seg ∩ C).Finite) :
    ∃ reps : List Plane, (∀ r ∈ reps, r ∈ P.seg \ C) ∧
      ∀ z ∈ P.seg \ C, ∃ r ∈ reps, ∃ S : Set Plane,
        S ⊆ P.seg \ C ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S := by
  by_cases hP : P.Nondeg
  · -- parametrize the segment; injectivity turns the finite meet into a finite parameter set
    set f : ℝ → Plane := fun t => AffineMap.lineMap P.1 P.2 t with hf
    have hfc : Continuous f := AffineMap.lineMap_continuous
    have hinj : Function.Injective f := Plane.lineMap_injective hP
    have hseg : P.seg = f '' Icc (0 : ℝ) 1 := by
      rw [show P.seg = segment ℝ P.1 P.2 from rfl, segment_eq_image_lineMap]
    set T : Set ℝ := f ⁻¹' C ∩ Icc 0 1 with hTdef
    have hTfin : T.Finite := by
      refine (hfin.preimage hinj.injOn).subset ?_
      rintro t ⟨htC, htI⟩
      exact ⟨hseg ▸ mem_image_of_mem f htI, htC⟩
    obtain ⟨rlist, hrmem, hrcov⟩ := exists_reps_Icc_diff 0 1 hTfin
    refine ⟨rlist.map f, ?_, ?_⟩
    · rintro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr
      obtain ⟨htI, htT⟩ := hrmem t ht
      exact ⟨hseg ▸ mem_image_of_mem f htI, fun hC => htT ⟨hC, htI⟩⟩
    · rintro z ⟨hzseg, hzC⟩
      rw [hseg] at hzseg
      obtain ⟨t, htI, rfl⟩ := hzseg
      obtain ⟨r, hr, hsub⟩ := hrcov t ⟨htI, fun ht => hzC ht.1⟩
      refine ⟨f r, List.mem_map_of_mem hr, f '' uIcc t r, ?_,
        isPreconnected_uIcc.image f hfc.continuousOn,
        mem_image_of_mem f left_mem_uIcc, mem_image_of_mem f right_mem_uIcc⟩
      rintro w ⟨u, hu, rfl⟩
      obtain ⟨huI, huT⟩ := hsub hu
      exact ⟨hseg ▸ mem_image_of_mem f huI, fun hC => huT ⟨hC, huI⟩⟩
  · -- a degenerate segment is a point: zero or one representative
    unfold Piece.Nondeg at hP
    have heq : P.1 = P.2 := not_not.1 hP
    have hseg : P.seg = {P.1} := by
      rw [show P.seg = segment ℝ P.1 P.2 from rfl, ← heq, segment_same]
    by_cases hC : P.1 ∈ C
    · refine ⟨[], by simp, ?_⟩
      rintro z ⟨hzseg, hzC⟩
      rw [hseg, mem_singleton_iff] at hzseg
      exact absurd (hzseg ▸ hC) hzC
    · refine ⟨[P.1], ?_, ?_⟩
      · intro r hr
        rw [List.mem_singleton] at hr
        exact hr ▸ ⟨hseg ▸ rfl, hC⟩
      · rintro z ⟨hzseg, hzC⟩
        rw [hseg, mem_singleton_iff] at hzseg
        refine ⟨P.1, List.mem_singleton_self _, {P.1},
          singleton_subset_iff.2 ⟨by rw [hseg]; rfl, hC⟩, isPreconnected_singleton, ?_, rfl⟩
        exact hzseg

/-- **The finiteness the joining loop terminates on.** If every listed segment meets `C`
finitely, then finitely many representatives meet every component of `cover l ∖ C`: every
point of `cover l ∖ C` is joined to a representative by a preconnected subset of
`cover l ∖ C`. The second conjunct is the `hcov` of
`isConnected_cover_diff_of_joins`, verbatim. -/
theorem exists_reps_cover_diff {C : Set Plane} :
    ∀ l : List Piece, MeetsFinitely l C →
      ∃ reps : List Plane, (∀ r ∈ reps, r ∈ cover l \ C) ∧
        ∀ z ∈ cover l \ C, ∃ r ∈ reps, ∃ S : Set Plane,
          S ⊆ cover l \ C ∧ IsPreconnected S ∧ z ∈ S ∧ r ∈ S
  | [], _ => ⟨[], by simp, by simp⟩
  | P :: ps, h => by
    obtain ⟨reps₁, hmem₁, hcov₁⟩ := exists_reps_seg_diff P (h P List.mem_cons_self)
    obtain ⟨reps₂, hmem₂, hcov₂⟩ :=
      exists_reps_cover_diff ps (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ))
    have hsub₁ : P.seg \ C ⊆ cover (P :: ps) \ C := fun w hw =>
      ⟨by rw [cover_cons]; exact Or.inl hw.1, hw.2⟩
    have hsub₂ : cover ps \ C ⊆ cover (P :: ps) \ C := fun w hw =>
      ⟨by rw [cover_cons]; exact Or.inr hw.1, hw.2⟩
    refine ⟨reps₁ ++ reps₂, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.1 hr with h1 | h2
      exacts [hsub₁ (hmem₁ r h1), hsub₂ (hmem₂ r h2)]
    · rintro z ⟨hz, hzC⟩
      rw [cover_cons] at hz
      rcases hz with hz | hz
      · obtain ⟨r, hr, S, hS, hSc, hzS, hrS⟩ := hcov₁ z ⟨hz, hzC⟩
        exact ⟨r, List.mem_append_left _ hr, S, hS.trans hsub₁, hSc, hzS, hrS⟩
      · obtain ⟨r, hr, S, hS, hSc, hzS, hrS⟩ := hcov₂ z ⟨hz, hzC⟩
        exact ⟨r, List.mem_append_right _ hr, S, hS.trans hsub₂, hSc, hzS, hrS⟩

/-- The honest reading of *"there are only finitely many components"*: the finite list meets
the connected component of every point of `cover l ∖ C`. -/
theorem exists_reps_connectedComponentIn {C : Set Plane} {l : List Piece}
    (h : MeetsFinitely l C) :
    ∃ reps : List Plane, (∀ r ∈ reps, r ∈ cover l \ C) ∧
      ∀ z ∈ cover l \ C, ∃ r ∈ reps, r ∈ connectedComponentIn (cover l \ C) z := by
  obtain ⟨reps, hmem, hcov⟩ := exists_reps_cover_diff l h
  refine ⟨reps, hmem, fun z hz => ?_⟩
  obtain ⟨r, hr, S, hS, hSc, hzS, hrS⟩ := hcov z hz
  exact ⟨r, hr, hSc.subset_connectedComponentIn hzS hS hrS⟩

/-! ## The call site

`gridAttachGraph_isConnected_diff` quantifies over
`cover (gsegs ++ localGridEdges p s (localGridCount s ε)) ∖ C`. Its `hcov` is the second
conjunct of `exists_reps_hcov` below, with the two `MeetsFinitely` inputs split the way the
caller holds them: a drawing fact for `gsegs`, outright disjointness for the grid (the grid
lies in `W ⊆ D` and `C ∩ D = ∅`). -/

/-- **`hcov`, produced.** Finitely many representatives meet every component of the
attachment cover minus `C`. The second conjunct is syntactically the `hcov` of
`gridAttachGraph_isConnected_diff`; the first is what lets the caller aim
`lem:polygonal-connected`'s joining arcs at the representatives. -/
theorem exists_reps_hcov {gsegs : List Piece} {C : Set Plane} {p : Plane} {s ε : ℝ}
    (hg : MeetsFinitely gsegs C)
    (hgrid : Disjoint (cover (localGridEdges p s (localGridCount s ε))) C) :
    ∃ reps : List Plane,
      (∀ r ∈ reps, r ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C) ∧
      ∀ z ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C,
        ∃ r ∈ reps, ∃ S : Set Plane,
          S ⊆ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C ∧
            IsPreconnected S ∧ z ∈ S ∧ r ∈ S :=
  exists_reps_cover_diff _ (hg.append (MeetsFinitely.of_disjoint hgrid))

/-- **Clause 1 of `prop:local-grid-attachment`, with the finiteness discharged.** Joining
arcs are asked for at every point of the cover — which `lem:polygonal-connected` supplies
inside `D` — and the representatives they are actually built for are produced here, so no
`hcov` remains. The graph depends on the produced representatives, hence the existential. -/
theorem gridAttachGraph_isConnected_diff_of_meetsFinitely {gsegs : List Piece}
    {Jarc : Plane → List Piece} {p : Plane} {s ε : ℝ} {extra : List Plane} {C : Set Plane}
    {r₀ : Plane}
    (hr₀ : r₀ ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C)
    (hg : MeetsFinitely gsegs C)
    (hgrid : Disjoint (cover (localGridEdges p s (localGridCount s ε))) C)
    (hJ : ∀ r ∈ cover (gsegs ++ localGridEdges p s (localGridCount s ε)) \ C,
      IsPreconnected (cover (Jarc r)) ∧ r₀ ∈ cover (Jarc r) ∧ r ∈ cover (Jarc r) ∧
        ∀ z ∈ cover (Jarc r), z ∉ C) :
    ∃ reps : List Plane, IsConnected
      (Graph.pointSet (gridAttachGraph gsegs reps Jarc p s ε extra) segmentDrawing \ C) := by
  obtain ⟨reps, hmem, hcov⟩ := exists_reps_hcov hg hgrid
  exact ⟨reps, gridAttachGraph_isConnected_diff hr₀
    (fun r hr => (hJ r (hmem r hr)).1) (fun r hr => (hJ r (hmem r hr)).2.1)
    (fun r hr => (hJ r (hmem r hr)).2.2.1) (fun r hr => (hJ r (hmem r hr)).2.2.2) hcov⟩

end Schoenflies
