/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.ArcComplement
import Schoenflies.FaceCyclesProof
import Schoenflies.Line

/-!
# The part of an overlay lying on one square boundary is 2-connected

`Schoenflies.SquaresTwoConnected`, the last hypothesis of `thm:arc-complement`, discharged.

## What has to be shown

`Schoenflies.squareGraph pieces points c r` is the set of edges of a polygonal overlay whose
segments lie on `frontier (Plane.closedSquare c r)`, spanned by `Schoenflies.segGraph`.  It
occupies the whole of that boundary (`Schoenflies.pointSet_squareGraph`), its edges are
nondegenerate segments with pairwise disjoint interiors
(`Schoenflies.overlayPieces_disjoint_interiors`), and there are finitely many of them.  So it is
the subdivided boundary of a square: a cycle, hence 2-connected.

## The route: two paths, not a cyclic order

The global cyclic order of the cut points around the square is never built.  Instead:

* **Each edge lies on a single side** (`Schoenflies.seg_subset_side`).  A nondegenerate segment
  inside the boundary of a square is axis-parallel and pinned to an extreme coordinate: if
  neither coordinate were constant along it, its midpoint would be strictly inside the square,
  because a strict convex combination of two distinct numbers in `[-r, r]` has absolute value
  `< r`.
* **The edges on one side chain up** (`Schoenflies.exists_isPath_side`).  On one side the
  parametrization `AffineMap.lineMap A B` and its inverse `Plane.lineCoord A B` turn the edges
  into closed subintervals of `[0, 1]` with pairwise disjoint interiors covering `(0, 1)`, and
  `Schoenflies.isPath_of_chain` peels them off from the left: the leftmost left endpoint is `0`,
  the edge realising it ends where the rest begins, and the induction repeats on `[b, 1]`.  No
  sorting and no limit argument: the leftmost endpoint is a minimum over a finite set, and the
  gap that would be left by a wrong guess is exhibited by a midpoint.
* **Three sides make one path, the fourth the other** (`Schoenflies.squaresTwoConnected`).  The
  top, left and bottom sides concatenate to a path from the north-east to the south-east corner
  (`Graph.IsPath.append`); the right side is a second such path; and the two meet only in those
  two corners.
* **Two internally disjoint paths with the same ends are 2-connected**
  (`Graph.isTwoConnected_of_two_paths`).  This is the general graph lemma the file is really
  built on, and it is stated for an ambient graph covered by the two paths rather than for their
  `Graph.union`, so that no graph equality has to be proved at the call site.

Deleting a vertex `c` is handled uniformly: every surviving vertex reaches an end of the path
it lies on (`Graph.IsPathGraph.reaches_an_end`), and the two ends are joined to each other by
whichever of the two paths misses `c` — one of them does, since the paths share only their ends.

## Two general lemmas that belong elsewhere

`Graph.IsPath.append` (concatenating two paths that meet only at the junction) and
`Graph.isTwoConnected_of_two_paths` are about abstract graphs and use nothing from the plane.
The integrator should hoist the first into `Schoenflies/Graph/Walk.lean` and the second into
`Schoenflies/Graph/TwoConnected.lean` or `Schoenflies/Graph/PathGraph.lean`;
`prop:anchored-square-mesh` wants the second as well ("the boundary of every collar rectangle is
a cycle").

## Blueprint

* `Graph.isTwoConnected_of_two_paths` — the cycle half of `lem:union-two-connected`'s
  neighbourhood: a cycle presented as two internally disjoint paths is 2-connected.  Used by
  `thm:arc-complement` and wanted again by `prop:anchored-square-mesh`.
* `Schoenflies.seg_subset_side`, `Schoenflies.exists_isPath_side`, `Schoenflies.isPath_of_chain`
  — "the polygonal overlay of the square boundaries associated with `A_i`" of
  `thm:arc-complement`, read one square at a time: the subdivided boundary cycle of a square.
* `Schoenflies.squaresTwoConnected` — the standing hypothesis `Schoenflies.SquaresTwoConnected`
  of `Schoenflies/ArcComplement.lean`, i.e. the step "it follows inductively from
  `lem:union-two-connected` that `Γ_i` is 2-connected" of `thm:arc-complement`, whose base case
  is that one square boundary is 2-connected.
-/

open Metric Set
open scoped Graph

/-! ## Part 1: two general graph lemmas -/

namespace Graph

variable {α β : Type*} {G K P Q : Graph α β} {u v w x c : α} {W W₁ W₂ : List β}

/-- **A graph covered by two paths with the same two ends, meeting only there, is
2-connected.**

Stated for an ambient graph `K` that the two paths cover, rather than for `Graph.union`, so
that a geometric consumer never has to prove a graph equality.

Deleting a vertex `c`: every surviving vertex reaches an end of its own path
(`Graph.IsPathGraph.reaches_an_end`).  If `c` is neither end, then `c` misses one of the two
paths — they share only `u` and `v` — and that whole path still joins `u` to `v`, so `u` is a
hub.  If `c` is an end, the branch reaching it is impossible (a deleted vertex is reached by
nothing) and the other end is the hub. -/
theorem isTwoConnected_of_two_paths (hPK : P ≤ K) (hQK : Q ≤ K) (hV : V(K) ⊆ V(P) ∪ V(Q))
    (hP : P.IsPathGraph u W₁ v) (hQ : Q.IsPathGraph u W₂ v) (huv : u ≠ v)
    (hmeet : ∀ x ∈ V(P), x ∈ V(Q) → x = u ∨ x = v) (h3 : K.HasThreeVertices) :
    K.IsTwoConnected where
  hasThreeVertices := h3
  connected :=
    Connected.of_two_subgraphs hPK hQK hV hP.connected hQ.connected hP.source_mem hQ.source_mem
  deleteVerts_connected := by
    intro c _
    -- Whatever is deleted, every surviving vertex reaches one of the two ends.
    have hreach : ∀ x ∈ V(K), x ≠ c →
        (K.deleteVerts {c}).Reaches x u ∨ (K.deleteVerts {c}).Reaches x v := by
      intro x hx hxc
      rcases hV hx with h | h
      · exact (hP.reaches_an_end h hxc).imp (fun hr ↦ hr.mono (deleteVerts_mono hPK _))
          fun hr ↦ hr.mono (deleteVerts_mono hPK _)
      · exact (hQ.reaches_an_end h hxc).imp (fun hr ↦ hr.mono (deleteVerts_mono hQK _))
          fun hr ↦ hr.mono (deleteVerts_mono hQK _)
    have huK : u ∈ V(K) := hPK.vertexSet_mono hP.source_mem
    have hvK : v ∈ V(K) := hPK.vertexSet_mono hP.target_mem
    by_cases hcu : c = u
    · -- The source is gone; the target is the hub, and the branch reaching the source cannot
      -- have happened.
      refine Connected.of_hub
        (mem_deleteVerts_singleton_of_ne hvK (by rw [hcu]; exact Ne.symm huv)) ?_
      intro x hx
      rw [vertexSet_deleteVerts] at hx
      have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
      rcases hreach x hx.1 hxc with hr | hr
      · exact absurd hcu.symm (mem_deleteVerts_singleton.1 hr.right_mem).2
      · exact hr.symm
    by_cases hcv : c = v
    · refine Connected.of_hub
        (mem_deleteVerts_singleton_of_ne huK (fun h ↦ hcu h.symm)) ?_
      intro x hx
      rw [vertexSet_deleteVerts] at hx
      have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
      rcases hreach x hx.1 hxc with hr | hr
      · exact hr.symm
      · exact absurd hcv.symm (mem_deleteVerts_singleton.1 hr.right_mem).2
    -- Otherwise one of the two paths never had `c`, and it joins the two ends.
    have hvu : (K.deleteVerts {c}).Reaches v u := by
      by_cases hcP : c ∈ V(P)
      · have hcQ : c ∉ V(Q) := fun h ↦ by
          rcases hmeet c hcP h with h' | h'
          exacts [hcu h', hcv h']
        have hr := hQ.connected.reaches hQ.target_mem hQ.source_mem
        rw [← deleteVerts_singleton_eq_self hcQ] at hr
        exact hr.mono (deleteVerts_mono hQK _)
      · have hr := hP.connected.reaches hP.target_mem hP.source_mem
        rw [← deleteVerts_singleton_eq_self hcP] at hr
        exact hr.mono (deleteVerts_mono hPK _)
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne huK (fun h ↦ hcu h.symm)) ?_
    intro x hx
    rw [vertexSet_deleteVerts] at hx
    have hxc : x ≠ c := fun h ↦ hx.2 (by simp [h])
    rcases hreach x hx.1 hxc with hr | hr
    · exact hr.symm
    · exact (hr.trans hvu).symm

end Graph

namespace Schoenflies

open Plane

/-! ## Part 2: a chain of edges along a parametrized segment

Nothing in this section is geometric.  A family of edges is presented through a parametrization
`γ` of the segment they lie on: each edge occupies `γ '' [lo Q, hi Q]`, the closed subintervals
have pairwise disjoint interiors, and together they cover `γ '' (m, 1)`.  The induction peels
off the edge whose left endpoint is least — that endpoint has to be `m`, or the gap just to the
right of `m` would be uncovered — and repeats on `[hi Q, 1]`. -/

/-- **The edges chain up into a path.**  The list is produced by the induction, so it comes out
in order and its membership is settled exactly (`Q ∈ W ↔ Q ∈ T`); the last clause is the
invariant that makes the freshness condition of `Graph.IsPath` immediate, since a vertex further
along the chain has a strictly larger parameter. -/
theorem isPath_of_chain {S₀ : Set Piece} {γ : ℝ → Plane} (hγ : Function.Injective γ)
    (lo hi : Piece → ℝ) (hend : γ 1 ∈ V(segGraph S₀)) :
    ∀ (n : ℕ) (T : Finset Piece) (m : ℝ), T.card = n → m ≤ 1 → (∀ Q ∈ T, Q ∈ S₀) →
      (∀ Q ∈ T, (γ (lo Q) = Q.1 ∧ γ (hi Q) = Q.2) ∨ (γ (lo Q) = Q.2 ∧ γ (hi Q) = Q.1)) →
      (∀ Q ∈ T, m ≤ lo Q) → (∀ Q ∈ T, hi Q ≤ 1) → (∀ Q ∈ T, lo Q < hi Q) →
      (∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → ∀ t, lo Q < t → t < hi Q → lo Q' < t → t < hi Q' → False) →
      (∀ t, m < t → t < 1 → ∃ Q ∈ T, lo Q ≤ t ∧ t ≤ hi Q) →
      ∃ W : List Piece, (segGraph S₀).IsPath (γ m) W (γ 1) ∧ (∀ Q, Q ∈ W ↔ Q ∈ T) ∧
        ∀ x ∈ (segGraph S₀).walkVertices (γ m) W, ∃ t, m ≤ t ∧ t ≤ 1 ∧ x = γ t := by
  classical
  intro n
  induction n with
  | zero =>
    intro T m hcard hm1 _ _ _ _ _ _ hcov
    obtain rfl : T = ∅ := Finset.card_eq_zero.1 hcard
    -- With no edges left there is nothing to the right of `m` to cover, so `m = 1`.
    obtain rfl : m = 1 := by
      by_contra hne
      obtain ⟨Q, hQ, -⟩ := hcov ((m + 1) / 2) (by linarith [lt_of_le_of_ne hm1 hne])
        (by linarith [lt_of_le_of_ne hm1 hne])
      simp at hQ
    refine ⟨[], .nil hend, by simp, fun x hx ↦ ?_⟩
    rw [Graph.walkVertices_nil, mem_singleton_iff] at hx
    exact ⟨1, le_rfl, le_rfl, hx⟩
  | succ n ih =>
    intro T m hcard hm1 hTS hends hlom hhi1 hlohi hdisj hcov
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    -- The leftmost left endpoint is `m` itself: otherwise the gap just to its right is
    -- uncovered, and a midpoint of that gap exhibits the failure.
    obtain ⟨e₁, he₁T, he₁min⟩ := T.exists_min_image lo hTne
    have hlo₁ : lo e₁ = m := by
      by_contra hne
      have hgt : m < lo e₁ := lt_of_le_of_ne (hlom e₁ he₁T) (Ne.symm hne)
      have hle1 : lo e₁ ≤ 1 := le_trans (hlohi e₁ he₁T).le (hhi1 e₁ he₁T)
      obtain ⟨Q, hQ, hQ1, -⟩ := hcov ((m + lo e₁) / 2) (by linarith) (by linarith)
      linarith [he₁min Q hQ]
    have hb₁ : m < hi e₁ := hlo₁ ▸ hlohi e₁ he₁T
    -- Everything else starts where `e₁` ends or later: an earlier start would overlap `e₁`.
    have hlo' : ∀ Q ∈ T.erase e₁, hi e₁ ≤ lo Q := by
      intro Q hQ'
      have hQ : Q ∈ T := Finset.mem_of_mem_erase hQ'
      have hQe : Q ≠ e₁ := Finset.ne_of_mem_erase hQ'
      by_contra hcon
      have hcon' : lo Q < hi e₁ := lt_of_not_ge hcon
      have hmin : min (hi Q) (hi e₁) > lo Q := lt_min (hlohi Q hQ) hcon'
      refine hdisj Q hQ e₁ he₁T hQe ((lo Q + min (hi Q) (hi e₁)) / 2) (by linarith) ?_
        (by linarith [he₁min Q hQ]) ?_
      · linarith [min_le_left (hi Q) (hi e₁)]
      · linarith [min_le_right (hi Q) (hi e₁)]
    have hcov' : ∀ t, hi e₁ < t → t < 1 → ∃ Q ∈ T.erase e₁, lo Q ≤ t ∧ t ≤ hi Q := by
      intro t ht1 ht2
      obtain ⟨Q, hQ, h1, h2⟩ := hcov t (by linarith) ht2
      refine ⟨Q, Finset.mem_erase.2 ⟨?_, hQ⟩, h1, h2⟩
      rintro rfl
      linarith
    obtain ⟨W', hW', hWmem, hWcoord⟩ := ih (T.erase e₁) (hi e₁)
      (by rw [Finset.card_erase_of_mem he₁T, hcard]; omega) (hhi1 e₁ he₁T)
      (fun Q hQ ↦ hTS Q (Finset.mem_of_mem_erase hQ))
      (fun Q hQ ↦ hends Q (Finset.mem_of_mem_erase hQ)) hlo'
      (fun Q hQ ↦ hhi1 Q (Finset.mem_of_mem_erase hQ))
      (fun Q hQ ↦ hlohi Q (Finset.mem_of_mem_erase hQ))
      (fun Q hQ Q' hQ' ↦ hdisj Q (Finset.mem_of_mem_erase hQ) Q' (Finset.mem_of_mem_erase hQ'))
      hcov'
    have hlink : (segGraph S₀).IsLink e₁ (γ m) (γ (hi e₁)) := by
      refine ⟨hTS e₁ he₁T, ?_⟩
      rcases hends e₁ he₁T with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hlo₁ ▸ h1, h2⟩
      · exact Or.inr ⟨hlo₁ ▸ h1, h2⟩
    have hfresh : γ m ∉ (segGraph S₀).walkVertices (γ (hi e₁)) W' := by
      intro hmem
      obtain ⟨t, ht1, -, ht3⟩ := hWcoord _ hmem
      have : m = t := hγ ht3
      linarith
    refine ⟨e₁ :: W', .cons hlink hW' hfresh, fun Q ↦ ?_, fun x hx ↦ ?_⟩
    · rw [List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact he₁T
        · exact Finset.mem_of_mem_erase ((hWmem Q).1 h)
      · intro h
        by_cases hQe : Q = e₁
        · exact Or.inl hQe
        · exact Or.inr ((hWmem Q).2 (Finset.mem_erase.2 ⟨hQe, h⟩))
    · rw [Graph.walkVertices_cons hlink] at hx
      rcases mem_insert_iff.1 hx with rfl | hx'
      · exact ⟨m, le_rfl, hm1, rfl⟩
      · obtain ⟨t, ht1, ht2, ht3⟩ := hWcoord _ hx'
        exact ⟨t, le_trans hb₁.le ht1, ht2, ht3⟩

/-! ## Part 3: the edges lying on one segment form a path between its ends -/

/-- **The edges of `S₀` lying on the segment `[A, B]` form a path from `A` to `B`.**

The hypotheses are exactly what a polygonal overlay supplies: nondegeneracy, pairwise disjoint
interiors, and that the open segment is covered by edges that do not leave the segment.  The
coordinate is `Plane.lineCoord A B`, which inverts `AffineMap.lineMap A B`, so ordering the
edges along the segment is ordering real numbers. -/
theorem exists_isPath_side {S₀ : Set Piece} {A B : Plane} (hAB : A ≠ B)
    (hBmem : B ∈ V(segGraph S₀)) (hnd : ∀ Q ∈ S₀, Q.Nondeg)
    (hdisj : ∀ Q ∈ S₀, ∀ Q' ∈ S₀, Q ≠ Q' → ∀ x, x ∈ Q.interior → x ∉ Q'.interior)
    (hfin : S₀.Finite)
    (hcov : ∀ z ∈ openSegment ℝ A B, ∃ Q ∈ S₀, z ∈ Q.seg ∧ Q.seg ⊆ segment ℝ A B) :
    ∃ W : List Piece, (segGraph S₀).IsPath A W B ∧
      (∀ Q, Q ∈ W ↔ (Q ∈ S₀ ∧ Q.seg ⊆ segment ℝ A B)) ∧
      ∀ x ∈ (segGraph S₀).walkVertices A W, x ∈ segment ℝ A B := by
  classical
  set γ : ℝ → Plane := ⇑(AffineMap.lineMap A B : ℝ →ᵃ[ℝ] Plane) with hγdef
  have hγinj : Function.Injective γ := Plane.lineMap_injective hAB
  have hγ0 : γ 0 = A := AffineMap.lineMap_apply_zero A B
  have hγ1 : γ 1 = B := AffineMap.lineMap_apply_one A B
  -- The coordinate inverts the parametrization on the segment.
  have hcoord : ∀ z ∈ segment ℝ A B, γ (Plane.lineCoord A B z) = z ∧
      0 ≤ Plane.lineCoord A B z ∧ Plane.lineCoord A B z ≤ 1 := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Plane.lineCoord_lineMap hAB]
    exact ⟨rfl, ht.1, ht.2⟩
  set lo : Piece → ℝ := fun Q ↦ min (Plane.lineCoord A B Q.1) (Plane.lineCoord A B Q.2) with hlodef
  set hi : Piece → ℝ := fun Q ↦ max (Plane.lineCoord A B Q.1) (Plane.lineCoord A B Q.2) with hhidef
  set T : Set Piece := {Q | Q ∈ S₀ ∧ Q.seg ⊆ segment ℝ A B} with hTdef
  have hTfin : T.Finite := hfin.subset fun _ hQ ↦ hQ.1
  -- The two ends of an edge on the segment are the parametrization of its two parameters.
  have hends : ∀ Q ∈ T, (γ (lo Q) = Q.1 ∧ γ (hi Q) = Q.2) ∨ (γ (lo Q) = Q.2 ∧ γ (hi Q) = Q.1) := by
    intro Q hQ
    have h1 := hcoord Q.1 (hQ.2 (left_mem_segment ℝ _ _))
    have h2 := hcoord Q.2 (hQ.2 (right_mem_segment ℝ _ _))
    rcases le_total (Plane.lineCoord A B Q.1) (Plane.lineCoord A B Q.2) with h | h
    · exact Or.inl ⟨by rw [hlodef]; simpa [min_eq_left h] using h1.1,
        by rw [hhidef]; simpa [max_eq_right h] using h2.1⟩
    · exact Or.inr ⟨by rw [hlodef]; simpa [min_eq_right h] using h2.1,
        by rw [hhidef]; simpa [max_eq_left h] using h1.1⟩
  have hlohi : ∀ Q ∈ T, lo Q < hi Q := by
    intro Q hQ
    have h1 := hcoord Q.1 (hQ.2 (left_mem_segment ℝ _ _))
    have h2 := hcoord Q.2 (hQ.2 (right_mem_segment ℝ _ _))
    have hne : Plane.lineCoord A B Q.1 ≠ Plane.lineCoord A B Q.2 := by
      intro h
      exact hnd Q hQ.1 (by rw [← h1.1, h, h2.1])
    simp only [hlodef, hhidef]
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have hlo0 : ∀ Q ∈ T, (0 : ℝ) ≤ lo Q := by
    intro Q hQ
    exact le_min (hcoord Q.1 (hQ.2 (left_mem_segment ℝ _ _))).2.1
      (hcoord Q.2 (hQ.2 (right_mem_segment ℝ _ _))).2.1
  have hhi1 : ∀ Q ∈ T, hi Q ≤ 1 := by
    intro Q hQ
    exact max_le (hcoord Q.1 (hQ.2 (left_mem_segment ℝ _ _))).2.2
      (hcoord Q.2 (hQ.2 (right_mem_segment ℝ _ _))).2.2
  -- A parameter strictly inside an edge's interval lands inside that edge.
  have hinner : ∀ Q ∈ T, ∀ t, lo Q < t → t < hi Q → γ t ∈ Q.interior := by
    intro Q hQ t h1 h2
    have hmem : γ t ∈ (AffineMap.lineMap A B) '' openSegment ℝ (lo Q) (hi Q) :=
      ⟨t, by rw [openSegment_eq_Ioo (hlohi Q hQ)]; exact ⟨h1, h2⟩, rfl⟩
    rw [image_openSegment] at hmem
    rcases hends Q hQ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [show (AffineMap.lineMap A B : ℝ → Plane) (lo Q) = Q.1 from e1,
        show (AffineMap.lineMap A B : ℝ → Plane) (hi Q) = Q.2 from e2] at hmem
      exact hmem
    · rw [show (AffineMap.lineMap A B : ℝ → Plane) (lo Q) = Q.2 from e1,
        show (AffineMap.lineMap A B : ℝ → Plane) (hi Q) = Q.1 from e2] at hmem
      rwa [openSegment_symm] at hmem
  have hdisj' : ∀ Q ∈ hTfin.toFinset, ∀ Q' ∈ hTfin.toFinset, Q ≠ Q' →
      ∀ t, lo Q < t → t < hi Q → lo Q' < t → t < hi Q' → False := by
    intro Q hQ Q' hQ' hne t h1 h2 h3 h4
    rw [Set.Finite.mem_toFinset] at hQ hQ'
    exact hdisj Q hQ.1 Q' hQ'.1 hne (γ t) (hinner Q hQ t h1 h2) (hinner Q' hQ' t h3 h4)
  -- Every interior parameter is covered by some edge's interval.
  have hcov' : ∀ t, (0 : ℝ) < t → t < 1 →
      ∃ Q ∈ hTfin.toFinset, lo Q ≤ t ∧ t ≤ hi Q := by
    intro t h0 h1
    have hmemopen : γ t ∈ openSegment ℝ A B := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ⟨h0, h1⟩, rfl⟩
    obtain ⟨Q, hQS, hQz, hQsub⟩ := hcov _ hmemopen
    have hQT : Q ∈ T := ⟨hQS, hQsub⟩
    refine ⟨Q, Set.Finite.mem_toFinset _ |>.2 hQT, ?_⟩
    -- The edge is the image of its closed parameter interval.
    have himg : Q.seg = (AffineMap.lineMap A B : ℝ → Plane) '' segment ℝ (lo Q) (hi Q) := by
      rw [image_segment]
      rcases hends Q hQT with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [show (AffineMap.lineMap A B : ℝ → Plane) (lo Q) = Q.1 from e1,
          show (AffineMap.lineMap A B : ℝ → Plane) (hi Q) = Q.2 from e2]
        rfl
      · rw [show (AffineMap.lineMap A B : ℝ → Plane) (lo Q) = Q.2 from e1,
          show (AffineMap.lineMap A B : ℝ → Plane) (hi Q) = Q.1 from e2]
        exact segment_symm ℝ Q.1 Q.2
    rw [himg] at hQz
    obtain ⟨s, hs, hst⟩ := hQz
    obtain rfl : s = t := hγinj hst
    rw [segment_eq_Icc (hlohi Q hQT).le] at hs
    exact hs
  obtain ⟨W, hW, hWmem, hWcoord⟩ :=
    isPath_of_chain (S₀ := S₀) hγinj lo hi (by rw [hγ1]; exact hBmem)
      hTfin.toFinset.card hTfin.toFinset 0 rfl zero_le_one
      (fun Q hQ ↦ (Set.Finite.mem_toFinset _ |>.1 hQ).1)
      (fun Q hQ ↦ hends Q (Set.Finite.mem_toFinset _ |>.1 hQ))
      (fun Q hQ ↦ hlo0 Q (Set.Finite.mem_toFinset _ |>.1 hQ))
      (fun Q hQ ↦ hhi1 Q (Set.Finite.mem_toFinset _ |>.1 hQ))
      (fun Q hQ ↦ hlohi Q (Set.Finite.mem_toFinset _ |>.1 hQ)) hdisj' hcov'
  rw [hγ0, hγ1] at hW
  rw [hγ0] at hWcoord
  refine ⟨W, hW, fun Q ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hWmem Q, Set.Finite.mem_toFinset]
    rfl
  · obtain ⟨t, ht0, ht1, rfl⟩ := hWcoord x hx
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

/-! ## Part 4: an edge on the boundary of a square lies on one of the four sides

The one geometric input.  Everything else about the square is already in
`Schoenflies/ArcComplementPrep.lean`: the four corners, the four sides, and the identification
of the boundary with their union. -/

/-- A convex combination with **positive** weights of two numbers of `[-r, r]` that are
distinct is strictly below `r`: at most one of them is `r`, so the combination is a strict
average of something smaller. -/
theorem combo_lt_right {x y a b r : ℝ} (hx : x ≤ r) (hy : y ≤ r) (hne : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a * x + b * y < r := by
  have hsum : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rcases eq_or_lt_of_le hx with h | h
  · have hy' : y < r := lt_of_le_of_ne hy fun hh ↦ hne (h.trans hh.symm)
    have h2 : b * y < b * r := mul_lt_mul_of_pos_left hy' hb
    have h1 : a * x = a * r := by rw [h]
    linarith
  · have h1 : a * x < a * r := mul_lt_mul_of_pos_left h ha
    have h2 : b * y ≤ b * r := mul_le_mul_of_nonneg_left hy hb.le
    linarith

/-- The two-sided form: a strict convex combination of two distinct numbers of `[-r, r]` has
absolute value strictly less than `r`.  This is what makes the midpoint of a segment whose two
coordinate differences both vary lie strictly inside the square. -/
theorem abs_combo_lt {x y a b r : ℝ} (hx : |x| ≤ r) (hy : |y| ≤ r) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : |a * x + b * y| < r := by
  rw [abs_le] at hx hy
  have h1 := combo_lt_right hx.2 hy.2 hxy ha hb hab
  have h2 := combo_lt_right (x := -x) (y := -y) (r := r) (by linarith [hx.1])
    (by linarith [hy.1])
    (fun h ↦ hxy (by linarith)) ha hb hab
  rw [abs_lt]
  constructor <;> linarith

variable {c z : Plane} {r : ℝ}

/-- The right side of the square, written from the north-east corner so that it runs the same
way as the three-sided path it is compared with.  `Plane.mem_seg_right` names it the other way
round. -/
theorem mem_seg_right' (hr : 0 ≤ r) :
    z ∈ segment ℝ (sqNE c r) (sqSE c r) ↔ z 0 = c 0 + r ∧ |z 1 - c 1| ≤ r := by
  rw [segment_symm]
  exact Plane.mem_seg_right hr

/-- A point on a segment whose two ends share a coordinate shares it too. -/
theorem coord_eq_of_mem_segment {p q z : Plane} (hz : z ∈ segment ℝ p q) (i : Fin 2)
    (hi : p i = q i) : z i = p i := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hz
  rw [Plane.smul_add_apply, ← hi]
  linear_combination (p i) * hab

/-- **A nondegenerate segment inside the boundary of a square lies on one of its four sides.**

If neither coordinate were constant along the segment, the midpoint would have *both*
coordinates strictly inside the square (`Schoenflies.abs_combo_lt` twice), contradicting the
boundary condition.  Once one coordinate is constant the same computation pins it: the other
coordinate of the midpoint is strictly inside, so it is the constant one that reaches the
extreme value, and the segment lies on the side at that value. -/
theorem seg_subset_side (hr : 0 < r) {p q : Plane} (hpq : p ≠ q)
    (hsub : segment ℝ p q ⊆ frontier (Plane.closedSquare c r)) :
    segment ℝ p q ⊆ segment ℝ (sqNE c r) (sqNW c r) ∨
      segment ℝ p q ⊆ segment ℝ (sqNW c r) (sqSW c r) ∨
      segment ℝ p q ⊆ segment ℝ (sqSW c r) (sqSE c r) ∨
      segment ℝ p q ⊆ segment ℝ (sqNE c r) (sqSE c r) := by
  -- Both ends and the midpoint are on the boundary.
  have hp := Plane.mem_frontier_closedSquare.1 (hsub (left_mem_segment ℝ _ _))
  have hq := Plane.mem_frontier_closedSquare.1 (hsub (right_mem_segment ℝ _ _))
  have hp0 : |p 0 - c 0| ≤ r := hp ▸ le_max_left _ _
  have hp1 : |p 1 - c 1| ≤ r := hp ▸ le_max_right _ _
  have hq0 : |q 0 - c 0| ≤ r := hq ▸ le_max_left _ _
  have hq1 : |q 1 - c 1| ≤ r := hq ▸ le_max_right _ _
  set m : Plane := (2⁻¹ : ℝ) • p + (2⁻¹ : ℝ) • q with hmdef
  have hmseg : m ∈ segment ℝ p q := ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, rfl⟩
  have hm := Plane.mem_frontier_closedSquare.1 (hsub hmseg)
  have hmc : ∀ i : Fin 2, m i - c i = 2⁻¹ * (p i - c i) + 2⁻¹ * (q i - c i) := by
    intro i
    rw [hmdef, Plane.smul_add_apply]
    ring
  -- Every point of the segment stays inside the closed square.
  have hin : ∀ z ∈ segment ℝ p q, |z 0 - c 0| ≤ r ∧ |z 1 - c 1| ≤ r := by
    intro z hz
    have := Plane.mem_frontier_closedSquare.1 (hsub hz)
    exact ⟨this ▸ le_max_left _ _, this ▸ le_max_right _ _⟩
  -- One of the two coordinates is constant along the segment.
  have hconst : p 0 = q 0 ∨ p 1 = q 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : |m 0 - c 0| < r := by
      rw [hmc 0]
      exact abs_combo_lt hp0 hq0 (fun h ↦ hcon.1 (by linarith)) (by norm_num) (by norm_num)
        (by norm_num)
    have h1 : |m 1 - c 1| < r := by
      rw [hmc 1]
      exact abs_combo_lt hp1 hq1 (fun h ↦ hcon.2 (by linarith)) (by norm_num) (by norm_num)
        (by norm_num)
    have hlt : max |m 0 - c 0| |m 1 - c 1| < r := max_lt h0 h1
    rw [hm] at hlt
    exact lt_irrefl r hlt
  rcases hconst with hconst | hconst
  · -- Vertical: the first coordinate is extreme, so the segment is on the left or right side.
    have hne1 : p 1 ≠ q 1 := fun h ↦ hpq (by ext i; fin_cases i; exacts [hconst, h])
    have h1 : |m 1 - c 1| < r := by
      rw [hmc 1]
      exact abs_combo_lt hp1 hq1 (fun h ↦ hne1 (by linarith)) (by norm_num) (by norm_num)
        (by norm_num)
    have h0 : |m 0 - c 0| = r := by
      rcases max_choice |m 0 - c 0| |m 1 - c 1| with hchoice | hchoice
      · rw [hchoice] at hm; exact hm
      · rw [hchoice] at hm; linarith
    have hp0' : |p 0 - c 0| = r := by
      rw [hmc 0, ← hconst] at h0
      rw [← h0]; congr 1; ring
    rcases (abs_eq hr.le).1 hp0' with h | h
    · refine Or.inr (Or.inr (Or.inr fun z hz ↦ (mem_seg_right' hr.le).2 ⟨?_, (hin z hz).2⟩))
      rw [coord_eq_of_mem_segment hz 0 hconst]; linarith
    · refine Or.inr (Or.inl fun z hz ↦ (Plane.mem_seg_left hr.le).2 ⟨?_, (hin z hz).2⟩)
      rw [coord_eq_of_mem_segment hz 0 hconst]; linarith
  · -- Horizontal: the second coordinate is extreme, so the segment is on the top or bottom.
    have hne0 : p 0 ≠ q 0 := fun h ↦ hpq (by ext i; fin_cases i; exacts [h, hconst])
    have h0 : |m 0 - c 0| < r := by
      rw [hmc 0]
      exact abs_combo_lt hp0 hq0 (fun h ↦ hne0 (by linarith)) (by norm_num) (by norm_num)
        (by norm_num)
    have h1 : |m 1 - c 1| = r := by
      rcases max_choice |m 0 - c 0| |m 1 - c 1| with hchoice | hchoice
      · rw [hchoice] at hm; linarith
      · rw [hchoice] at hm; exact hm
    have hp1' : |p 1 - c 1| = r := by
      rw [hmc 1, ← hconst] at h1
      rw [← h1]; congr 1; ring
    rcases (abs_eq hr.le).1 hp1' with h | h
    · refine Or.inl fun z hz ↦ (Plane.mem_seg_top hr.le).2 ⟨?_, (hin z hz).1⟩
      rw [coord_eq_of_mem_segment hz 1 hconst]; linarith
    · refine Or.inr (Or.inr (Or.inl fun z hz ↦ (Plane.mem_seg_bottom hr.le).2 ⟨?_, (hin z hz).1⟩))
      rw [coord_eq_of_mem_segment hz 1 hconst]; linarith

/-! ### How the four sides meet

Six statements, one for each unordered pair: adjacent sides meet in the corner they share,
opposite sides not at all. -/

theorem eq_sqNW_of_top_left (hr : 0 < r) (h1 : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h2 : z ∈ segment ℝ (sqNW c r) (sqSW c r)) : z = sqNW c r := by
  rw [Plane.mem_seg_top hr.le] at h1
  rw [Plane.mem_seg_left hr.le] at h2
  ext i
  fin_cases i
  exacts [h2.1, h1.1]

theorem eq_sqNE_of_top_right (hr : 0 < r) (h1 : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h2 : z ∈ segment ℝ (sqNE c r) (sqSE c r)) : z = sqNE c r := by
  rw [Plane.mem_seg_top hr.le] at h1
  rw [mem_seg_right' hr.le] at h2
  ext i
  fin_cases i
  exacts [h2.1, h1.1]

theorem eq_sqSW_of_left_bottom (hr : 0 < r) (h1 : z ∈ segment ℝ (sqNW c r) (sqSW c r))
    (h2 : z ∈ segment ℝ (sqSW c r) (sqSE c r)) : z = sqSW c r := by
  rw [Plane.mem_seg_left hr.le] at h1
  rw [Plane.mem_seg_bottom hr.le] at h2
  ext i
  fin_cases i
  exacts [h1.1, h2.1]

theorem eq_sqSE_of_bottom_right (hr : 0 < r) (h1 : z ∈ segment ℝ (sqSW c r) (sqSE c r))
    (h2 : z ∈ segment ℝ (sqNE c r) (sqSE c r)) : z = sqSE c r := by
  rw [Plane.mem_seg_bottom hr.le] at h1
  rw [mem_seg_right' hr.le] at h2
  ext i
  fin_cases i
  exacts [h2.1, h1.1]

theorem not_mem_top_bottom (hr : 0 < r) (h1 : z ∈ segment ℝ (sqNE c r) (sqNW c r))
    (h2 : z ∈ segment ℝ (sqSW c r) (sqSE c r)) : False := by
  rw [Plane.mem_seg_top hr.le] at h1
  rw [Plane.mem_seg_bottom hr.le] at h2
  have := h1.1.symm.trans h2.1
  linarith

theorem not_mem_left_right (hr : 0 < r) (h1 : z ∈ segment ℝ (sqNW c r) (sqSW c r))
    (h2 : z ∈ segment ℝ (sqNE c r) (sqSE c r)) : False := by
  rw [Plane.mem_seg_left hr.le] at h1
  rw [mem_seg_right' hr.le] at h2
  have := h1.1.symm.trans h2.1
  linarith

/-! ### The corners are pairwise distinct -/

theorem sqNE_ne_sqNW (hr : 0 < r) : sqNE c r ≠ sqNW c r := fun h ↦ by
  have h' : c 0 + r = c 0 - r := congrArg (fun w : Plane ↦ w 0) h
  linarith

theorem sqNW_ne_sqSW (hr : 0 < r) : sqNW c r ≠ sqSW c r := fun h ↦ by
  have h' : c 1 + r = c 1 - r := congrArg (fun w : Plane ↦ w 1) h
  linarith

theorem sqSW_ne_sqSE (hr : 0 < r) : sqSW c r ≠ sqSE c r := fun h ↦ by
  have h' : c 0 - r = c 0 + r := congrArg (fun w : Plane ↦ w 0) h
  linarith

theorem sqNE_ne_sqSE (hr : 0 < r) : sqNE c r ≠ sqSE c r := fun h ↦ by
  have h' : c 1 + r = c 1 - r := congrArg (fun w : Plane ↦ w 1) h
  linarith

theorem sqNW_ne_sqSE (hr : 0 < r) : sqNW c r ≠ sqSE c r := fun h ↦ by
  have h' : c 0 - r = c 0 + r := congrArg (fun w : Plane ↦ w 0) h
  linarith


/-! ## Part 5: the assembly

Three sides make one path from the north-east to the south-east corner, the fourth makes the
other, they meet only in those two corners, and `Graph.isTwoConnected_of_two_paths` finishes. -/

/-- **`Schoenflies.SquaresTwoConnected`**: the part of a polygonal overlay lying on the boundary
of one of its squares is 2-connected.

This is the last hypothesis of `thm:arc-complement`; substituting it makes that theorem,
`lem:accessible-dense` and `thm:jordan` unconditional. -/
theorem squaresTwoConnected : SquaresTwoConnected := by
  intro pieces points hnd hEnds hMeets c r hr hsub
  classical
  change (segGraph (squareEdges pieces points c r)).IsTwoConnected
  set S₀ : Set Piece := squareEdges pieces points c r with hS₀def
  -- What the overlay gives about this edge set.
  have hS₀nd : ∀ Q ∈ S₀, Q.Nondeg := fun Q hQ ↦ overlayPieces_nondeg points hnd Q hQ.1
  have hS₀fr : ∀ Q ∈ S₀, Q.seg ⊆ frontier (Plane.closedSquare c r) := fun Q hQ ↦ hQ.2
  have hS₀disj : ∀ Q ∈ S₀, ∀ Q' ∈ S₀, Q ≠ Q' → ∀ x, x ∈ Q.interior → x ∉ Q'.interior :=
    fun Q hQ Q' hQ' hne x hx ↦
      overlayPieces_disjoint_interiors hnd hEnds hMeets hQ.1 hQ'.1 hne hx
  have hS₀fin : S₀.Finite := squareEdges_finite
  have hcover : ∀ z ∈ frontier (Plane.closedSquare c r), ∃ Q ∈ S₀, z ∈ Q.seg := by
    have heq : (⋃ Q ∈ S₀, Q.seg) = frontier (Plane.closedSquare c r) := by
      rw [← pointSet_segGraph S₀]
      exact pointSet_squareGraph (points := points) hr.le hsub
    intro z hz
    rw [← heq] at hz
    simpa only [mem_iUnion, exists_prop] using hz
  -- Every edge lies on one of the four sides.
  have hside : ∀ Q ∈ S₀,
      Q.seg ⊆ segment ℝ (sqNE c r) (sqNW c r) ∨ Q.seg ⊆ segment ℝ (sqNW c r) (sqSW c r) ∨
        Q.seg ⊆ segment ℝ (sqSW c r) (sqSE c r) ∨ Q.seg ⊆ segment ℝ (sqNE c r) (sqSE c r) :=
    fun Q hQ ↦ seg_subset_side hr (hS₀nd Q hQ) (hS₀fr Q hQ)
  -- The four sides lie on the boundary.
  have htopfr : segment ℝ (sqNE c r) (sqNW c r) ⊆ frontier (Plane.closedSquare c r) :=
    fun z hz ↦ (Plane.mem_frontier_closedSquare_iff_sides hr.le).2 (Or.inl hz)
  have hleftfr : segment ℝ (sqNW c r) (sqSW c r) ⊆ frontier (Plane.closedSquare c r) :=
    fun z hz ↦ (Plane.mem_frontier_closedSquare_iff_sides hr.le).2 (Or.inr (Or.inl hz))
  have hbotfr : segment ℝ (sqSW c r) (sqSE c r) ⊆ frontier (Plane.closedSquare c r) :=
    fun z hz ↦ (Plane.mem_frontier_closedSquare_iff_sides hr.le).2 (Or.inr (Or.inr (Or.inl hz)))
  have hrightfr : segment ℝ (sqNE c r) (sqSE c r) ⊆ frontier (Plane.closedSquare c r) := by
    intro z hz
    rw [segment_symm] at hz
    exact (Plane.mem_frontier_closedSquare_iff_sides hr.le).2 (Or.inr (Or.inr (Or.inr hz)))
  -- The four corners are vertices: they are ends of source pieces, hence cut points.
  have hmem1 : ((sqNE c r, sqNW c r) : Piece) ∈ squarePieces c r := by simp [squarePieces]
  have hmem2 : ((sqNW c r, sqSW c r) : Piece) ∈ squarePieces c r := by simp [squarePieces]
  have hmem3 : ((sqSW c r, sqSE c r) : Piece) ∈ squarePieces c r := by simp [squarePieces]
  have hcornerV : ∀ z : Plane, z ∈ points → z ∈ frontier (Plane.closedSquare c r) →
      z ∈ V(segGraph S₀) := fun z hz hzf ↦ mem_vertexSet_squareGraph hnd hr.le hsub hz hzf
  have hNEV : sqNE c r ∈ V(segGraph S₀) :=
    hcornerV _ (hEnds _ (hsub _ hmem1) _ (Or.inl rfl)) (htopfr (left_mem_segment ℝ _ _))
  have hNWV : sqNW c r ∈ V(segGraph S₀) :=
    hcornerV _ (hEnds _ (hsub _ hmem1) _ (Or.inr rfl)) (htopfr (right_mem_segment ℝ _ _))
  have hSWV : sqSW c r ∈ V(segGraph S₀) :=
    hcornerV _ (hEnds _ (hsub _ hmem2) _ (Or.inr rfl)) (hleftfr (right_mem_segment ℝ _ _))
  have hSEV : sqSE c r ∈ V(segGraph S₀) :=
    hcornerV _ (hEnds _ (hsub _ hmem3) _ (Or.inr rfl)) (hbotfr (right_mem_segment ℝ _ _))
  -- Each side's relative interior is covered by edges that stay on that side: an edge through
  -- an interior point of one side cannot be on any of the other three.
  have hcovtop : ∀ z ∈ openSegment ℝ (sqNE c r) (sqNW c r),
      ∃ Q ∈ S₀, z ∈ Q.seg ∧ Q.seg ⊆ segment ℝ (sqNE c r) (sqNW c r) := by
    intro z hz
    have hzs : z ∈ segment ℝ (sqNE c r) (sqNW c r) := openSegment_subset_segment ℝ _ _ hz
    obtain ⟨Q, hQ, hzQ⟩ := hcover z (htopfr hzs)
    have hzA : z ≠ sqNE c r := fun he ↦ sqNE_ne_sqNW hr (left_mem_openSegment_iff.1 (he ▸ hz))
    have hzB : z ≠ sqNW c r := fun he ↦ sqNE_ne_sqNW hr (right_mem_openSegment_iff.1 (he ▸ hz))
    refine ⟨Q, hQ, hzQ, ?_⟩
    rcases hside Q hQ with h | h | h | h
    · exact h
    · exact absurd (eq_sqNW_of_top_left hr hzs (h hzQ)) hzB
    · exact (not_mem_top_bottom hr hzs (h hzQ)).elim
    · exact absurd (eq_sqNE_of_top_right hr hzs (h hzQ)) hzA
  have hcovleft : ∀ z ∈ openSegment ℝ (sqNW c r) (sqSW c r),
      ∃ Q ∈ S₀, z ∈ Q.seg ∧ Q.seg ⊆ segment ℝ (sqNW c r) (sqSW c r) := by
    intro z hz
    have hzs : z ∈ segment ℝ (sqNW c r) (sqSW c r) := openSegment_subset_segment ℝ _ _ hz
    obtain ⟨Q, hQ, hzQ⟩ := hcover z (hleftfr hzs)
    have hzA : z ≠ sqNW c r := fun he ↦ sqNW_ne_sqSW hr (left_mem_openSegment_iff.1 (he ▸ hz))
    have hzB : z ≠ sqSW c r := fun he ↦ sqNW_ne_sqSW hr (right_mem_openSegment_iff.1 (he ▸ hz))
    refine ⟨Q, hQ, hzQ, ?_⟩
    rcases hside Q hQ with h | h | h | h
    · exact absurd (eq_sqNW_of_top_left hr (h hzQ) hzs) hzA
    · exact h
    · exact absurd (eq_sqSW_of_left_bottom hr hzs (h hzQ)) hzB
    · exact (not_mem_left_right hr hzs (h hzQ)).elim
  have hcovbot : ∀ z ∈ openSegment ℝ (sqSW c r) (sqSE c r),
      ∃ Q ∈ S₀, z ∈ Q.seg ∧ Q.seg ⊆ segment ℝ (sqSW c r) (sqSE c r) := by
    intro z hz
    have hzs : z ∈ segment ℝ (sqSW c r) (sqSE c r) := openSegment_subset_segment ℝ _ _ hz
    obtain ⟨Q, hQ, hzQ⟩ := hcover z (hbotfr hzs)
    have hzA : z ≠ sqSW c r := fun he ↦ sqSW_ne_sqSE hr (left_mem_openSegment_iff.1 (he ▸ hz))
    have hzB : z ≠ sqSE c r := fun he ↦ sqSW_ne_sqSE hr (right_mem_openSegment_iff.1 (he ▸ hz))
    refine ⟨Q, hQ, hzQ, ?_⟩
    rcases hside Q hQ with h | h | h | h
    · exact (not_mem_top_bottom hr (h hzQ) hzs).elim
    · exact absurd (eq_sqSW_of_left_bottom hr (h hzQ) hzs) hzA
    · exact h
    · exact absurd (eq_sqSE_of_bottom_right hr hzs (h hzQ)) hzB
  have hcovright : ∀ z ∈ openSegment ℝ (sqNE c r) (sqSE c r),
      ∃ Q ∈ S₀, z ∈ Q.seg ∧ Q.seg ⊆ segment ℝ (sqNE c r) (sqSE c r) := by
    intro z hz
    have hzs : z ∈ segment ℝ (sqNE c r) (sqSE c r) := openSegment_subset_segment ℝ _ _ hz
    obtain ⟨Q, hQ, hzQ⟩ := hcover z (hrightfr hzs)
    have hzA : z ≠ sqNE c r := fun he ↦ sqNE_ne_sqSE hr (left_mem_openSegment_iff.1 (he ▸ hz))
    have hzB : z ≠ sqSE c r := fun he ↦ sqNE_ne_sqSE hr (right_mem_openSegment_iff.1 (he ▸ hz))
    refine ⟨Q, hQ, hzQ, ?_⟩
    rcases hside Q hQ with h | h | h | h
    · exact absurd (eq_sqNE_of_top_right hr (h hzQ) hzs) hzA
    · exact (not_mem_left_right hr (h hzQ) hzs).elim
    · exact absurd (eq_sqSE_of_bottom_right hr (h hzQ) hzs) hzB
    · exact h
  -- The four sides, each a path between its two corners.
  obtain ⟨Wtop, htopP, htopM, htopV⟩ :=
    exists_isPath_side (S₀ := S₀) (sqNE_ne_sqNW hr) hNWV hS₀nd hS₀disj hS₀fin hcovtop
  obtain ⟨Wleft, hleftP, hleftM, hleftV⟩ :=
    exists_isPath_side (S₀ := S₀) (sqNW_ne_sqSW hr) hSWV hS₀nd hS₀disj hS₀fin hcovleft
  obtain ⟨Wbot, hbotP, hbotM, hbotV⟩ :=
    exists_isPath_side (S₀ := S₀) (sqSW_ne_sqSE hr) hSEV hS₀nd hS₀disj hS₀fin hcovbot
  obtain ⟨Wright, hrightP, hrightM, hrightV⟩ :=
    exists_isPath_side (S₀ := S₀) (sqNE_ne_sqSE hr) hSEV hS₀nd hS₀disj hS₀fin hcovright
  -- Top, left and bottom concatenate: consecutive sides meet only in the corner they share.
  have hlb : (segGraph S₀).IsPath (sqNW c r) (Wleft ++ Wbot) (sqSE c r) :=
    hleftP.append hbotP fun x hx1 hx2 ↦ eq_sqSW_of_left_bottom hr (hleftV x hx1) (hbotV x hx2)
  have hpath1 : (segGraph S₀).IsPath (sqNE c r) (Wtop ++ (Wleft ++ Wbot)) (sqSE c r) := by
    refine htopP.append hlb fun x hx1 hx2 ↦ ?_
    rcases Graph.walkVertices_append_subset (G := segGraph S₀) (u := sqNW c r) (W₁ := Wleft)
      (W₂ := Wbot) (w := sqSW c r) hx2 with h | h
    · exact eq_sqNW_of_top_left hr (htopV x hx1) (hleftV x h)
    · exact (not_mem_top_bottom hr (htopV x hx1) (hbotV x h)).elim
  have hV1 : ∀ x ∈ (segGraph S₀).walkVertices (sqNE c r) (Wtop ++ (Wleft ++ Wbot)),
      x ∈ segment ℝ (sqNE c r) (sqNW c r) ∨ x ∈ segment ℝ (sqNW c r) (sqSW c r) ∨
        x ∈ segment ℝ (sqSW c r) (sqSE c r) := by
    intro x hx
    rcases Graph.walkVertices_append_subset (G := segGraph S₀) (u := sqNE c r) (W₁ := Wtop)
      (W₂ := Wleft ++ Wbot) (w := sqNW c r) hx with h | h
    · exact Or.inl (htopV x h)
    · rcases Graph.walkVertices_append_subset (G := segGraph S₀) (u := sqNW c r) (W₁ := Wleft)
        (W₂ := Wbot) (w := sqSW c r) h with h' | h'
      · exact Or.inr (Or.inl (hleftV x h'))
      · exact Or.inr (Or.inr (hbotV x h'))
  -- The two paths, as graphs.
  have hP₁le : (segGraph S₀).pathGraphOf (sqNE c r) (Wtop ++ (Wleft ++ Wbot)) ≤ segGraph S₀ :=
    Graph.pathGraphOf_le hpath1.isWalk
  have hP₂le : (segGraph S₀).pathGraphOf (sqNE c r) Wright ≤ segGraph S₀ :=
    Graph.pathGraphOf_le hrightP.isWalk
  have hVcov : V(segGraph S₀) ⊆
      V((segGraph S₀).pathGraphOf (sqNE c r) (Wtop ++ (Wleft ++ Wbot))) ∪
        V((segGraph S₀).pathGraphOf (sqNE c r) Wright) := by
    rintro v ⟨Q, hQ, hvQ⟩
    have hinc : (segGraph S₀).Inc Q v := by
      rcases hvQ with rfl | rfl
      · exact ⟨Q.2, hQ, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨Q.1, hQ, Or.inr ⟨rfl, rfl⟩⟩
    simp only [Graph.pathGraphOf_vertexSet, mem_union]
    rcases hside Q hQ with h | h | h | h
    · exact Or.inl (Graph.mem_walkVertices_of_mem_covered
        (Graph.mem_coveredVertices (List.mem_append_left _ ((htopM Q).2 ⟨hQ, h⟩)) hinc))
    · exact Or.inl (Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices
        (List.mem_append_right _ (List.mem_append_left _ ((hleftM Q).2 ⟨hQ, h⟩))) hinc))
    · exact Or.inl (Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices
        (List.mem_append_right _ (List.mem_append_right _ ((hbotM Q).2 ⟨hQ, h⟩))) hinc))
    · exact Or.inr (Graph.mem_walkVertices_of_mem_covered
        (Graph.mem_coveredVertices ((hrightM Q).2 ⟨hQ, h⟩) hinc))
  have hmeet : ∀ x ∈ V((segGraph S₀).pathGraphOf (sqNE c r) (Wtop ++ (Wleft ++ Wbot))),
      x ∈ V((segGraph S₀).pathGraphOf (sqNE c r) Wright) →
      x = sqNE c r ∨ x = sqSE c r := by
    intro x hx1 hx2
    rw [Graph.pathGraphOf_vertexSet] at hx1 hx2
    have hxr := hrightV x hx2
    rcases hV1 x hx1 with h | h | h
    · exact Or.inl (eq_sqNE_of_top_right hr h hxr)
    · exact (not_mem_left_right hr h hxr).elim
    · exact Or.inr (eq_sqSE_of_bottom_right hr h hxr)
  exact Graph.isTwoConnected_of_two_paths hP₁le hP₂le hVcov hpath1.isPathGraph_pathGraphOf
    hrightP.isPathGraph_pathGraphOf (sqNE_ne_sqSE hr) hmeet
    ⟨sqNE c r, hNEV, sqNW c r, hNWV, sqSE c r, hSEV, sqNE_ne_sqNW hr, sqNE_ne_sqSE hr,
      sqNW_ne_sqSE hr⟩


/-! ### What the discharge buys

`thm:arc-complement` becomes unconditional.  Both forms are restated here with the hypothesis
gone, the second in exactly the shape `Schoenflies/Jordan.lean` takes as its `harc`
hypothesis, so that closing `lem:accessible-dense` and `thm:jordan` is a substitution and not a
reformulation. -/

/-- **`thm:arc-complement`, unconditionally**: the complement of a simple arc is connected. -/
theorem isConnected_compl_of_isArc {A : Set Plane} (hA : IsArc A) : IsConnected Aᶜ :=
  isConnected_compl_arc hA squaresTwoConnected

/-- The same, in the `∀`-form that `lem:accessible-dense` and `thm:jordan` consume. -/
theorem forall_isConnected_compl_of_isArc : ∀ A : Set Plane, IsArc A → IsConnected Aᶜ :=
  fun _ hA ↦ isConnected_compl_of_isArc hA

/-- **`thm:arc-complement`, the polygonal half, unconditionally.** -/
theorem exists_simple_poly_compl_of_isArc {A : Set Plane} (hA : IsArc A) {u w : Plane}
    (huw : u ≠ w) (hu : u ∉ A) (hw : w ∉ A) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P u w ∧ P ⊆ Aᶜ :=
  exists_simple_poly_compl_arc hA squaresTwoConnected huw hu hw

end Schoenflies
