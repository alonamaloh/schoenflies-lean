/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.StageRecursion
import Schoenflies.LocalGrid
import Schoenflies.RealizeSplit
import Schoenflies.RefinementStars

/-!
# The grid-star estimate — `lem:grid-star-estimate`

*If `x` lies in the interior of `W_n(b_n)`, then `diam St_{Γ_n}(x) < 2 ε_n`.*

The geometry of the blueprint's proof: every 2-cell incident with the carrier of `x` is an open
connected set disjoint from the skeleton; the skeleton contains the frame `∂W` and all grid
lines of `W`; so the 2-cell lies in a single component of the complement of that finite union
of segments — one open grid rectangle of `W`, or the complement of `W`. The latter is excluded
because the closure of the 2-cell contains `x`, which lies in the *interior* of `W`. Trapped in
one grid rectangle, the closed 2-cell has diameter `≤ ε`, and `lem:star-face-mesh`(a)
(`IsCellDecomposition.diam_star_le`, `RefinementStars.lean`) doubles that to the star bound.

Two of those steps were already on `main` and are consumed, not reproved:

* the trapping itself is `Schoenflies.dist_lt_of_avoiding_localGrid` (`LocalGrid.lean`) — a
  preconnected subset of `W` avoiding the grid cover has diameter `< √2·(2s/k)` — so this
  module only has to place the 2-cell inside `W`, which is the connectedness argument above
  run against the frame of `W`;
* the doubling is `IsCellDecomposition.diam_star_le`.

## What is a hypothesis here, and who supplies it

The single geometric hypothesis is `hgrid`: **the realized skeleton contains the local grid
cover**, `cover (localGridEdges b s k) ⊆ R.skeletonSet`. Its supplier is the grid-attachment
transfer, in two halves that are both on `main`:

* `Schoenflies.localGrid_subset_gridAttachGraph` (`GridAttach.lean`) — the extension graph
  `gridAttachGraph` occupies the whole grid cover;
* `Schoenflies.IsPartialTransferOf.skeletonSet_eq` (`FiniteTransfer.lean`) — after the
  direction-(a) transfer, the new source skeleton occupies exactly what the transferred graph
  occupies: `T.src.skeletonSet = pointSet H Hdraw`.

Composing the two is the discharger's one remaining obligation, because it must first rename
the edges of `gridAttachGraph : Graph Plane Piece` into the abstract cell-name type `γ` that
`IsTransferOf` fixes — an edge renaming, which `Graph.map` does not provide (see the note on
`InitialCell.aux` in `InitialGenerated.lean` for the intended route). The renaming preserves
the drawn point set, which is all `hgrid` reads.

The remaining hypotheses — assertion (i) (`IsCellDecomposition`), assertion (vii)
(`IsFaceJordan`), the combinatorial invariants and boundedness of the domain — are fields of
any `Schoenflies.GeneratedPair` (`P.src_isCellDecomposition`, `P.src_isFaceJordan`,
`P.combInvariants`, with `Schoenflies.isBounded_union_inside` for the domain), so the
`StagePair` form below takes the pair itself and reads them off.

## Blueprint

* `Schoenflies.mem_cover_localGridEdges_of_supDist_eq` — the frame of `W` is part of the grid
  cover, which is what excludes the outer component: a 2-cell reaching from the window's
  interior to its complement would cross the frame, hence the skeleton.
* `Schoenflies.CellStructure.Realization.diam_closure_cell_le_of_grid` — the body of the
  blueprint proof: a 2-cell whose closure meets the open window is trapped in one closed grid
  rectangle, so its closed diameter is below the mesh.
* `Schoenflies.CellStructure.Realization.diam_star_carrier_le_of_grid` —
  **`lem:grid-star-estimate`** over an explicit square and mesh, via `lem:star-face-mesh`(a).
* `Schoenflies.CellStructure.Realization.diam_star_carrier_le_of_openWindow` — the same at the
  window `W(b)` of `Windows.lean`, with `windowRadius` for `s` and `localGridCount` for the
  mesh; the metric half (`windowRadius_pos`, `window_subset_inside`, `localGridCount_spec`) is
  consumed from `Windows.lean` and `LocalGrid.lean`.
* `Schoenflies.StagePair.diam_star_le_of_grid` — the estimate in the exact shape of the
  `Schoenflies.GridStepData.diam_star_le` field of `StageRecursion.lean`, which is what the
  `Schoenflies.HasGridSteps` discharger hands to the recursion.

The blueprint states the lemma *after* the direction-(b) pullback; the Lean consumer
(`GridStepData` in `StageRecursion.lean`) applies it to the output of the direction-(a) step
alone and lets `IsRefinementStep.diam_star_carrier_le` (refinement only shrinks stars) carry
the bound through the mesh half, so the parent-map paragraph of the blueprint proof —
`lem:refinement-compatibility`(a) — is not needed here.
-/

open Metric Set Bornology

namespace Schoenflies

/-! ### The frame of the window lies on the grid

A point of `W` at sup distance exactly `s` from the centre has an extreme coordinate, so it
lies on the grid line of index `0` or `k` — the frame is part of the grid cover. This is what
makes "the skeleton contains the grid lines of `W`" also mean "the skeleton contains `∂W`". -/

/-- **The frame of the window is part of the grid cover.** -/
theorem mem_cover_localGridEdges_of_supDist_eq {b : Plane} {s : ℝ} {k : ℕ}
    (hs : 0 < s) (hk : 1 ≤ k) {z : Plane} (hz : z ∈ Plane.closedSquare b s)
    (heq : Plane.supDist z b = s) : z ∈ cover (localGridEdges b s k) := by
  have hmax : max |z 0 - b 0| |z 1 - b 1| = s := by
    simpa [Plane.supDist, Plane.supNorm, Plane.sub_apply] using heq
  rcases max_choice |z 0 - b 0| |z 1 - b 1| with hm | hm
  · -- the first coordinate is extreme: `z` lies on the vertical grid line `0` or `k`
    rcases (abs_eq hs.le).1 (hm.symm.trans hmax) with h | h
    · exact mem_cover_of_coord_eq hs hk le_rfl hz (by rw [localGridX_last hk]; linarith)
    · exact mem_cover_of_coord_eq hs hk (Nat.zero_le k) hz (by rw [localGridX_zero]; linarith)
  · -- the second coordinate is extreme: `z` lies on the horizontal grid line `0` or `k`
    rcases (abs_eq hs.le).1 (hm.symm.trans hmax) with h | h
    · exact mem_cover_of_coord_eq' hs hk le_rfl hz (by rw [localGridY_last hk]; linarith)
    · exact mem_cover_of_coord_eq' hs hk (Nat.zero_le k) hz (by rw [localGridY_zero]; linarith)

namespace CellStructure.Realization

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization} {dom : Set Plane}
  {b : Plane} {s ε : ℝ} {k : ℕ}

/-! ### A 2-cell reaching into the open window is trapped in one grid rectangle -/

/-- **The trapping step of `lem:grid-star-estimate`.** A 2-cell whose closure meets the open
window is an open connected set missing the skeleton, hence missing the frame and the grid
lines of `W`; connectedness forces it inside the open window, where
`dist_lt_of_avoiding_localGrid` bounds its diameter by the grid mesh. -/
theorem diam_closure_cell_le_of_grid (hcd : R.IsCellDecomposition dom) (hJ : R.IsFaceJordan)
    (hs : 0 < s) (hk : 1 ≤ k) (hfine : Real.sqrt 2 * (2 * s / k) ≤ ε)
    (hgrid : cover (localGridEdges b s k) ⊆ R.skeletonSet)
    {F : γ} (hF : F ∈ S.faces) {x : Plane} (hx : x ∈ Plane.openSquare b s)
    (hxcl : x ∈ closure (R.cell F)) : diam (closure (R.cell F)) ≤ ε := by
  have hpre : IsPreconnected (R.cell F) := (hJ.isConnected hF).isPreconnected
  -- the 2-cell misses the grid, because it misses the skeleton
  have havoid : ∀ z ∈ R.cell F, z ∉ cover (localGridEdges b s k) := fun z hz hzc =>
    Set.disjoint_left.1 (R.disjoint_cell_skeletonSet hcd hF) hz (hgrid hzc)
  -- it meets the open window: the window is an open neighbourhood of the closure point `x`
  have hmeets : (R.cell F ∩ Plane.openSquare b s).Nonempty := by
    obtain ⟨y, hyW, hyF⟩ := mem_closure_iff.1 hxcl _ (Plane.isOpen_openSquare b s) hx
    exact ⟨y, hyF, hyW⟩
  -- every point of the 2-cell is inside the open window or beyond the closed one: a point of
  -- the closed window at extreme sup distance would lie on the frame, hence on the grid
  have hunion : R.cell F ⊆ Plane.openSquare b s ∪ (Plane.closedSquare b s)ᶜ := by
    intro z hz
    by_cases hzc : z ∈ Plane.closedSquare b s
    · rcases lt_or_eq_of_le (show Plane.supDist z b ≤ s from hzc) with h | h
      · exact Or.inl h
      · exact absurd (mem_cover_localGridEdges_of_supDist_eq hs hk hzc h) (havoid z hz)
    · exact Or.inr hzc
  -- connectedness picks the inner alternative
  have hdisj : Disjoint (Plane.openSquare b s) (Plane.closedSquare b s)ᶜ :=
    Set.disjoint_left.2 fun z hz hzc =>
      hzc (show Plane.supDist z b ≤ s from le_of_lt (show Plane.supDist z b < s from hz))
  have hsub : R.cell F ⊆ Plane.openSquare b s :=
    hpre.subset_left_of_subset_union (Plane.isOpen_openSquare b s)
      (Plane.isClosed_closedSquare b s).isOpen_compl hdisj hunion hmeets
  -- trapped in the window and avoiding the grid, the 2-cell is smaller than the mesh
  have hFW : R.cell F ⊆ Plane.closedSquare b s := fun w hw =>
    show Plane.supDist w b ≤ s from le_of_lt (show Plane.supDist w b < s from hsub hw)
  have hbound : ∀ y ∈ R.cell F, ∀ z ∈ R.cell F, dist y z ≤ ε := fun y hy z hz =>
    le_trans (dist_lt_of_avoiding_localGrid hs hk hpre hFW havoid hy hz).le hfine
  rw [Metric.diam_closure]
  refine diam_le_of_forall_dist_le ?_ hbound
  exact le_trans (by positivity) hfine

/-! ### `lem:grid-star-estimate` -/

/-- **`lem:grid-star-estimate`, over an explicit square and mesh.** If the realized skeleton
contains the `k × k` grid cover on the closed square of centre `b` and radius `s`, whose mesh
`√2·(2s/k)` is below `ε`, then the star of the carrier of any point of the *open* square has
diameter at most `2ε`.

Every closed 2-cell incident with the carrier contains `x` in its closure
(`IsCellDecomposition.mem_closure_face`), so the trapping step bounds it by `ε`, and
`lem:star-face-mesh`(a) (`IsCellDecomposition.diam_star_le`) doubles the bound. -/
theorem diam_star_carrier_le_of_grid [Nonempty γ] (hcd : R.IsCellDecomposition dom)
    (hS : S.CombInvariants) (hJ : R.IsFaceJordan) (hD : IsBounded dom)
    (hs : 0 < s) (hk : 1 ≤ k) (hfine : Real.sqrt 2 * (2 * s / k) ≤ ε)
    (hgrid : cover (localGridEdges b s k) ⊆ R.skeletonSet)
    {x : Plane} (hx : x ∈ Plane.openSquare b s) (hxdom : x ∈ dom) :
    diam (R.star (R.carrier x)) ≤ 2 * ε := by
  refine hcd.diam_star_le hS hD (hcd.mem_cells_carrier hxdom) fun F hF hsub => ?_
  exact diam_closure_cell_le_of_grid hcd hJ hs hk hfine hgrid hF hx
    (hcd.mem_closure_face (hcd.mem_cells_carrier hxdom) hF hsub (hcd.mem_cell_carrier hxdom))

/-- **`lem:grid-star-estimate` at the window `W(b)`** of `Windows.lean`: the square is
`window C ε b` and the grid is the one `prop:local-grid-attachment` installs, with
`localGridCount` intervals per side. The window arithmetic — the radius is positive, the window
lies in the domain, the mesh is below `ε` — is the metric half already on `main`
(`windowRadius_pos`, `window_subset_inside`, `localGridCount_spec`). -/
theorem diam_star_carrier_le_of_openWindow [Nonempty γ] {C : Set Plane} (hsep : IsSeparating C)
    (hcd : R.IsCellDecomposition (C ∪ inside C)) (hS : S.CombInvariants) (hJ : R.IsFaceJordan)
    (hε : 0 < ε) (hb : b ∈ inside C)
    (hgrid : cover (localGridEdges b (windowRadius C ε b)
      (localGridCount (windowRadius C ε b) ε)) ⊆ R.skeletonSet)
    {x : Plane} (hx : x ∈ openWindow C ε b) :
    diam (R.star (R.carrier x)) ≤ 2 * ε := by
  have hCcpt : IsCompact C := hsep.isJordanCurve.isCompact
  have hCne : C.Nonempty := hsep.isJordanCurve.nonempty
  have hbC : b ∉ C := fun h => inside_subset_compl hb h
  have hxdom : x ∈ C ∪ inside C := by
    refine Or.inr (window_subset_inside hCcpt hCne hsep hb hε ?_)
    exact show Plane.supDist x b ≤ windowRadius C ε b from
      le_of_lt (show Plane.supDist x b < windowRadius C ε b from hx)
  exact diam_star_carrier_le_of_grid hcd hS hJ (isBounded_union_inside hsep)
    (windowRadius_pos hCcpt hCne hbC) (one_le_localGridCount _ ε)
    (localGridCount_spec hε).le hgrid hx hxdom

end CellStructure.Realization

/-! ### The estimate in the shape the recursion consumes

`Schoenflies.GridStepData.diam_star_le` (`StageRecursion.lean`) is
`∀ ⦃x⦄, x ∈ openWindow C ε b → diam (next.src.star (next.src.carrier x)) ≤ 2 * ε`, read on the
stage pair the grid transfer produced. Every structural hypothesis of the estimate is a field
of that pair; only the grid-in-skeleton clause is about how the pair was made. -/

/-- **`lem:grid-star-estimate`, verbatim for the `Schoenflies.HasGridSteps` discharger.** For a
stage pair whose source skeleton contains the local grid cover on `W(b)`, the conclusion is the
`diam_star_le` field of `Schoenflies.GridStepData`, word for word. The discharger obtains
`hgrid` from `Schoenflies.localGrid_subset_gridAttachGraph` composed with
`Schoenflies.IsPartialTransferOf.skeletonSet_eq`. -/
theorem StagePair.diam_star_le_of_grid {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ}
    {C : Set Plane} (h₀ : S₀.CombInvariants) (hsep : IsSeparating C) (P : StagePair S₀ C)
    {ε : ℝ} (hε : 0 < ε) {b : Plane} (hb : b ∈ inside C)
    (hgrid : cover (localGridEdges b (windowRadius C ε b)
      (localGridCount (windowRadius C ε b) ε)) ⊆ P.src.skeletonSet) :
    ∀ ⦃x⦄, x ∈ openWindow C ε b → diam (P.src.star (P.src.carrier x)) ≤ 2 * ε :=
  fun _ hx => CellStructure.Realization.diam_star_carrier_le_of_openWindow hsep
    P.src_isCellDecomposition (P.combInvariants h₀) P.src_isFaceJordan hε hb hgrid hx

end Schoenflies
