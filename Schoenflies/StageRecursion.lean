/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.StageTower
import Schoenflies.Windows
import Schoenflies.EarStepTgt
import Schoenflies.InitialGenerated

/-!
# The stage recursion: from the two transfer directions to a `StageSequence`

`Schoenflies.StageSequence` (`StageTower.lean`) is the single deliverable of Phase 3: a sequence
of generated matched cellulations of the closed Jordan domain and the closed square whose
skeleton maps are nested and whose stars shrink, from which `StageSequence.limitTower` produces
everything `Schoenflies.HasLimitHomeomorphism` needs. This module **builds the recursion** that
produces one, against the two transfer theorems that are already unconditional
(`Schoenflies.finite_transfer_toward_square'`, `Schoenflies.finite_transfer_back'`), leaving the
*choice of enlargement* — the whole of `prop:local-grid-attachment`, `lem:grid-star-estimate`
and the mesh half of `prop:shrinking-stars` — as two named hypotheses stated in exactly the
shape the recursion consumes.

## The step interface

One recursion step of `quantitative-refinement` is: *attach a local source grid in the window
`W_n(b_n)` and transfer it to the square* (direction (a)), then *overlay the target with an
anchored mesh of size `ε_n` and transfer it back* (direction (b)). What the `StageSequence`
fields read off a step is captured by `Schoenflies.IsRefinementStep`: both realizations refine
along one shared parent map, the skeleton homeomorphism extends the old one, and both new
realizations are admissible. The two bridge theorems
`Schoenflies.IsTransferOfTgt.isRefinementStep` and
`Schoenflies.IsTransferOf.isRefinementStep` are machine-checked evidence that the conclusions
of the two transfer theorems deliver this interface — the second modulo the one clause
`IsPartialTransferOf` does not yet carry (see *The one interface gap* below).

## The two named hypotheses

* `Schoenflies.HasGridSteps` — **the source-grid chooser.** At any admissible stage, for any
  mesh `ε > 0` and any window centre `b ∈ inside C`, there is a refinement step whose source
  stars inside the open window `W(b)` have diameter at most `2ε`. Its discharger is
  `prop:local-grid-attachment` (`GridAttach.lean` + `LocalGrid.lean`, currently conditional on
  `hΓ` and `hcov`) to build the extension `H_n`, `Schoenflies.finite_transfer_toward_square'`
  to transfer it, and `lem:grid-star-estimate` — whose statement *is* the `diam_star_le` field,
  with `Windows.lean` supplying all the arithmetic — for the bound.
* `Schoenflies.HasMeshSteps` — **the target-mesh chooser.** At any admissible stage and any
  `ε > 0`, there is a refinement step all of whose closed target 2-cells have diameter at most
  `ε`. Its discharger is `prop:anchored-square-mesh` (done, `SquareMesh*.lean`), the polygonal
  overlay with the current target skeleton, and `Schoenflies.finite_transfer_back'`; the
  `HasFreshAnchors` hypothesis of the latter is exactly what the mesh's fresh anchor points
  (clauses 3 and 4 of the mesh proposition) provide.

Both hypotheses quantify over *arbitrary admissible stages* rather than over the stages of this
recursion: nothing in either discharger depends on the history of the construction — strong
accessibility of an anchor is a property of the fixed domain, and the mesh's freshness clause
avoids only the (finite) vertex set of the current stage.

## What the recursion itself proves

Given the two choosers, stage 0 (`InitialData.generatedPair`, hypothesis-free) and
`thm:jordan` for `C`, `Schoenflies.stageSequence` constructs the `StageSequence`. The
quantitative glue is proved here, not assumed:

* the **uniform half of `prop:shrinking-stars`** — every target star at stage `n + 1` has
  diameter at most `4 · 2^{-(n+1)}` — from the mesh chooser's 2-cell bound via
  `lem:star-face-mesh`(a) (`IsCellDecomposition.diam_star_le`), and at stage 0 from the bare
  containment of every target star in the closed square;
* the **pointwise half of `prop:shrinking-stars`** — for every `x ∈ inside C` the source star
  of the carrier of `x` has diameter tending to `0` — by the blueprint's own argument: a dense
  sequence of window centres in which every point recurs (`Schoenflies.recur` on
  `TopologicalSpace.denseSeq`), the window-catching arithmetic
  (`Schoenflies.mem_openWindow_of_supDist_lt`), the grid chooser's bound at the catch index,
  and monotonicity of stars under refinement (`Realization.Refines.star_carrier_subset`) to
  carry the bound to every later stage.

## The one interface gap, and how it is carried

`StageSequence.skelHomeo_succ` needs the stage-`n+1` skeleton map to agree with the stage-`n`
one on the old skeleton, *in both transfer directions*. Direction (b) carries it
(`IsPartialTransferOfTgt.homeo_eqOn`); direction (a) does not — `IsPartialTransferOf` has four
fields and that is not one of them (`docs/ROADMAP.md`, Phase 3, item 4). Until the clause lands
in `FiniteTransfer.lean`, `Schoenflies.IsTransferOf.isRefinementStep` takes it as an explicit
hypothesis `hhomeo`, and `HasGridSteps` demands it through the `homeo_eqOn` field of
`IsRefinementStep`. When the clause lands, the discharger of `HasGridSteps` reads it off the
transfer and `hhomeo` disappears at that call site; nothing in this module changes.

## Blueprint

* `Schoenflies.IsRefinementStep` — what one step of the recursion of *Quantitative refinement*
  hands to the next, i.e. the per-step content of the `StageSequence` fields.
* `Schoenflies.HasGridSteps` — `prop:local-grid-attachment` + `thm:finite-transfer`(a) +
  `lem:grid-star-estimate`, as one named hypothesis.
* `Schoenflies.HasMeshSteps` — `prop:anchored-square-mesh` + `thm:finite-transfer`(b) +
  the mesh sentence of the recursion step ("every closed target 2-cell has diameter
  `< ε_n`"), as one named hypothesis.
* `Schoenflies.stageSequence` — the recursion of *Quantitative refinement*: the two halves of
  `prop:shrinking-stars` proved from the choosers, and the stages assembled into a
  `Schoenflies.StageSequence`.
* `Schoenflies.stageSequence_of_isJordanCurve` — the same, launched from `prop:initial-pair`
  (`InitialData.generatedPair`) with `γ := InitialCell`.
-/

open Bornology Filter Metric Set Topology
open scoped Graph

namespace Schoenflies

open CellStructure

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}

/-! ### The stage pairs and the step interface -/

/-- The generated pairs the recursion runs on: matched cellulations of the closed Jordan domain
`C ∪ inside C` and the closed square, the instantiation `StageSequence` fixes. -/
abbrev StagePair (S₀ : CellStructure γ) (C : Set Plane) :=
  GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)

/-- **One step of the stage recursion, as `StageSequence` consumes it.** `T` refines `P` along
one parent map shared by the two sides, the skeleton homeomorphism extends the old one, and both
new realizations are admissible in the strong sense — the last because each recursion step ends
with a *complete* transfer, whose conclusion (`IsTransferOf` / `IsTransferOfTgt`) restores the
connectedness that `rem:intermediate-disconnection` waives mid-transfer.

Every field is delivered by the conclusion of one of the two transfer theorems; see
`Schoenflies.IsTransferOfTgt.isRefinementStep` and `Schoenflies.IsTransferOf.isRefinementStep`
for the machine-checked correspondence. -/
structure IsRefinementStep (T P : StagePair S₀ C) (par : γ → γ) : Prop where
  /-- The new source realization refines the old one along `par`. -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the old one along the *same* parent map —
  `lem:refinement-compatibility`(c). -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The new skeleton map extends the old one — the clause `StageSequence.skelHomeo_succ`
  needs at every step. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The new source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible C (C ∪ inside C)
  /-- The new target realization is admissible. -/
  tgt_isAdmissible : T.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)

namespace IsRefinementStep

variable {T' T P : StagePair S₀ C} {par' par : γ → γ}

omit [Nonempty γ] in
/-- The realized source skeleton grows across a step — `StageSequence.skeletonSet_mono`. -/
theorem skeletonSet_subset (h : IsRefinementStep T P par) :
    P.src.skeletonSet ⊆ T.src.skeletonSet :=
  h.refines_src.skeletonSet_subset P.src_isCellDecomposition T.src_isCellDecomposition

omit [Nonempty γ] in
/-- **Steps compose.** The two halves of one recursion step — grid attachment toward the
square, mesh pulled back from it — combine into one step along the composed parent map, which
is the `par n` the `StageSequence` records. -/
theorem trans (h' : IsRefinementStep T' T par') (h : IsRefinementStep T P par) :
    IsRefinementStep T' P (par ∘ par') where
  refines_src := h'.refines_src.trans h.refines_src
  refines_tgt := h'.refines_tgt.trans h.refines_tgt
  homeo_eqOn := fun x hx => by
    rw [h'.homeo_eqOn (h.skeletonSet_subset hx)]
    exact h.homeo_eqOn hx
  src_isAdmissible := h'.src_isAdmissible
  tgt_isAdmissible := h'.tgt_isAdmissible

/-- **Once a star is small it stays small** — `lem:refinement-compatibility`(b) read across one
recursion step, the monotonicity the pointwise half of `prop:shrinking-stars` iterates. -/
theorem diam_star_carrier_le (h : IsRefinementStep T P par) (h₀ : S₀.CombInvariants)
    (hsep : IsSeparating C) {x : Plane} (hx : x ∈ C ∪ inside C) :
    diam (T.src.star (T.src.carrier x)) ≤ diam (P.src.star (P.src.carrier x)) :=
  diam_mono
    (h.refines_src.star_carrier_subset (T.combInvariants h₀) P.src_isCellDecomposition
      T.src_isCellDecomposition hx)
    (P.src_isCellDecomposition.isBounded_star (P.combInvariants h₀)
      (isBounded_union_inside hsep))

end IsRefinementStep

/-! ### The transfer theorems deliver the step interface

The whole point of `IsRefinementStep` is that it is *exactly* what the two finite-transfer
conclusions hand over. These two theorems are the machine-checked statement of that fit; the
dischargers of the two chooser hypotheses below will consist of building the extension graph,
invoking the transfer, and applying one of these. -/

section Bridges

variable {T P : StagePair S₀ C} {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}

omit [Nonempty γ] in
/-- **A direction-(b) transfer is a refinement step.** Every field of `IsRefinementStep` is a
field of `IsTransferOfTgt`, `homeo_eqOn` included — the target-side invariant already carries
the skeleton-map extension clause. -/
theorem IsTransferOfTgt.isRefinementStep (hT : IsTransferOfTgt T P H Hdraw par) :
    IsRefinementStep T P par where
  refines_src := hT.refines_src
  refines_tgt := hT.refines_tgt
  homeo_eqOn := hT.homeo_eqOn
  src_isAdmissible := hT.src_isAdmissible
  tgt_isAdmissible := hT.tgt_isAdmissible

omit [Nonempty γ] in
/-- **A direction-(a) transfer is a refinement step — modulo one clause.**

`hhomeo` is item 4 of the Phase 3 list in `docs/ROADMAP.md`: `IsPartialTransferOf` does not yet
record that the transferred skeleton map extends the old one, though both elementary operations
build it that way (`SplitData.splitHomeo_eqOn`, and a subdivision leaves the point map
unchanged). A `homeo_eqOn` clause mirroring `IsPartialTransferOfTgt.homeo_eqOn` is being added
to `IsPartialTransferOf`; when it lands, a caller holding `hT` reads `hhomeo` off it and this
hypothesis is discharged verbatim. Until then it is carried explicitly, so that nothing in this
module silently claims what direction (a) does not yet provide. -/
theorem IsTransferOf.isRefinementStep (hT : IsTransferOf T P H Hdraw par)
    (hhomeo : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet) :
    IsRefinementStep T P par where
  refines_src := hT.refines_src
  refines_tgt := hT.refines_tgt
  homeo_eqOn := hhomeo
  src_isAdmissible := hT.src_isAdmissible
  tgt_isAdmissible := hT.tgt_isAdmissible

end Bridges

/-! ### The two named hypotheses

Each is *"at every stage there is an admissible enlargement whose transfer shrinks the stars"*,
for one of the two directions, stated as the existence of a bundle of data rather than of a bare
pair so that the recursion below can extract components by name after a single use of choice.

Neither mentions the extension graph `H`: the recursion consumes a transfer only through
`IsRefinementStep`, and keeping `H` out of the interface is what lets the discharger choose it
freely (grid, crosscut, joining loops on one side; mesh and overlay on the other). -/

/-- The data one source-grid step hands to the recursion: the refined stage, the parent map,
the step relation, and the grid-star estimate on the window. -/
structure GridStepData (P : StagePair S₀ C) (ε : ℝ) (b : Plane) where
  /-- The refined stage. -/
  next : StagePair S₀ C
  /-- The shared parent map. -/
  par : γ → γ
  /-- The refined stage is one recursion step beyond `P`. -/
  step : IsRefinementStep next P par
  /-- **`lem:grid-star-estimate`**: inside the open window `W(b)` the new source stars have
  diameter at most `2ε`. -/
  diam_star_le : ∀ ⦃x⦄, x ∈ openWindow C ε b →
    diam (next.src.star (next.src.carrier x)) ≤ 2 * ε

/-- The data one target-mesh step hands to the recursion: the refined stage, the parent map,
the step relation, and the mesh bound on the closed target 2-cells. -/
structure MeshStepData (P : StagePair S₀ C) (ε : ℝ) where
  /-- The refined stage. -/
  next : StagePair S₀ C
  /-- The shared parent map. -/
  par : γ → γ
  /-- The refined stage is one recursion step beyond `P`. -/
  step : IsRefinementStep next P par
  /-- **"Every closed target 2-cell has diameter `< ε_n`"** — the sentence of the recursion
  step that the anchored mesh establishes. `lem:star-face-mesh`(a) turns it into the uniform
  star bound below, so the star form is *not* part of the hypothesis. -/
  diam_closure_cell_le : ∀ ⦃F⦄, F ∈ next.str.faces → diam (closure (next.tgt.cell F)) ≤ ε

/-- **NAMED HYPOTHESIS — the source-grid chooser.**

At every admissible stage, every mesh `ε > 0` and every window centre `b` in the open Jordan
domain, some enlargement of the source skeleton transfers to a refinement step whose source
stars inside `W(b)` have diameter at most `2ε`.

Discharged by: `prop:local-grid-attachment` (`Schoenflies.localGrid` + `GridAttach.lean`,
once `hΓ` and `hcov` are closed) building the extension `H_n` over the window `W(b)` —
`Schoenflies.window_subset_inside` puts the window in the domain — then
`Schoenflies.finite_transfer_toward_square'` with the four ambient facts
(`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and companions), then
`lem:grid-star-estimate` for the bound, whose metric half is ready in `Windows.lean`. The
`homeo_eqOn` field inside `step` is the pending direction-(a) clause; see
`Schoenflies.IsTransferOf.isRefinementStep`. -/
def HasGridSteps (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃b : Plane⦄, b ∈ inside C → Nonempty (GridStepData P ε b)

/-- **NAMED HYPOTHESIS — the target-mesh chooser.**

At every admissible stage and every `ε > 0`, some enlargement of the target skeleton — the
anchored mesh of size `ε` overlaid with the current skeleton — transfers back to a refinement
step all of whose closed target 2-cells have diameter at most `ε`.

Discharged by: `prop:anchored-square-mesh` (done, `SquareMesh*.lean`) with `δ := ε`, the
polygonal overlay with the current target skeleton and the joining arcs
(`lem:polygonal-overlay`, `Graph.union` toolkit), then `Schoenflies.finite_transfer_back'`,
whose `HasFreshAnchors` is exactly clauses 3–4 of the mesh proposition; the 2-cell bound is
the mesh's clause 1 carried through the overlay ("every open target 2-cell of `Γ'_n` lies in
an open 2-cell of `T_n`"), with `lem:diameter-closure` for the closures. -/
def HasMeshSteps (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → Nonempty (MeshStepData P ε)

/-! ### The recursion -/

/-- One stage of the recursion: a stage pair together with the strong admissibility of both
realizations, which is what the two choosers demand of their input and what their outputs
restore. -/
structure AdmissibleStage (S₀ : CellStructure γ) (C : Set Plane) where
  /-- The stage pair. -/
  pair : StagePair S₀ C
  /-- The source realization is admissible. -/
  src_isAdmissible : pair.src.IsAdmissible C (C ∪ inside C)
  /-- The target realization is admissible. -/
  tgt_isAdmissible : pair.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)

section Recursion

variable (h₀ : S₀.CombInvariants) (hsep : IsSeparating C)
  (hgrid : HasGridSteps S₀ C) (hmesh : HasMeshSteps S₀ C) (s₀ : AdmissibleStage S₀ C)

/-- The window centre of stage `n`: the blueprint's `b_n`. The candidate is `recur` applied to a
dense sequence of the plane, so that every plane point has arbitrarily nearby candidates at
arbitrarily late stages; a candidate outside the open Jordan domain is replaced by a fixed
interior point, so the grid chooser always receives a legal centre. -/
noncomputable def stageCenter (hsep : IsSeparating C) (n : ℕ) : Plane :=
  open scoped Classical in
  if recur (TopologicalSpace.denseSeq Plane) n ∈ inside C
  then recur (TopologicalSpace.denseSeq Plane) n
  else hsep.isConnected_inside.nonempty.some

theorem stageCenter_mem (n : ℕ) : stageCenter hsep n ∈ inside C := by
  rw [stageCenter]
  split
  · assumption
  · exact hsep.isConnected_inside.nonempty.some_mem

theorem stageCenter_eq {n : ℕ}
    (h : recur (TopologicalSpace.denseSeq Plane) n ∈ inside C) :
    stageCenter hsep n = recur (TopologicalSpace.denseSeq Plane) n := by
  rw [stageCenter]
  split
  · rfl
  · exact absurd h ‹_›

/-- The grid half of step `n`: the source-grid chooser invoked with mesh `2⁻ⁿ` and centre
`b_n`. -/
noncomputable def gridStage (s : AdmissibleStage S₀ C) (n : ℕ) :
    GridStepData s.pair (((2 : ℝ) ^ n)⁻¹) (stageCenter hsep n) :=
  (hgrid s.pair s.src_isAdmissible s.tgt_isAdmissible (two_pow_neg_pos n)
    (stageCenter_mem hsep n)).some

/-- The mesh half of step `n`, applied to the output of the grid half. -/
noncomputable def meshStage (s : AdmissibleStage S₀ C) (n : ℕ) :
    MeshStepData (gridStage hsep hgrid s n).next (((2 : ℝ) ^ n)⁻¹) :=
  (hmesh (gridStage hsep hgrid s n).next
    (gridStage hsep hgrid s n).step.src_isAdmissible
    (gridStage hsep hgrid s n).step.tgt_isAdmissible (two_pow_neg_pos n)).some

/-- One full recursion step: grid toward the square, mesh pulled back from it. -/
noncomputable def nextStage (s : AdmissibleStage S₀ C) (n : ℕ) : AdmissibleStage S₀ C :=
  ⟨(meshStage hsep hgrid hmesh s n).next,
    (meshStage hsep hgrid hmesh s n).step.src_isAdmissible,
    (meshStage hsep hgrid hmesh s n).step.tgt_isAdmissible⟩

/-- The parent map of one full step: grid parent after mesh parent, the composition order
`Realization.Refines.trans` fixes. -/
noncomputable def stepPar (s : AdmissibleStage S₀ C) (n : ℕ) : γ → γ :=
  (gridStage hsep hgrid s n).par ∘ (meshStage hsep hgrid hmesh s n).par

/-- One full step is a refinement step along the composed parent map. -/
theorem nextStage_step (s : AdmissibleStage S₀ C) (n : ℕ) :
    IsRefinementStep (nextStage hsep hgrid hmesh s n).pair s.pair
      (stepPar hsep hgrid hmesh s n) :=
  (meshStage hsep hgrid hmesh s n).step.trans (gridStage hsep hgrid s n).step

include h₀ in
/-- **The catch estimate.** When the stage-`n` candidate centre lies in the open Jordan domain,
a point of the corresponding open window has, at stage `n + 1`, a source star of diameter at
most `2 · 2⁻ⁿ`: the grid half provides the bound and the mesh half only shrinks stars. -/
theorem nextStage_diam_star_le (s : AdmissibleStage S₀ C) {n : ℕ}
    (hb : recur (TopologicalSpace.denseSeq Plane) n ∈ inside C) {x : Plane}
    (hx : x ∈ openWindow C (((2 : ℝ) ^ n)⁻¹) (recur (TopologicalSpace.denseSeq Plane) n))
    (hxD : x ∈ C ∪ inside C) :
    diam ((nextStage hsep hgrid hmesh s n).pair.src.star
        ((nextStage hsep hgrid hmesh s n).pair.src.carrier x)) ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := by
  have hx' : x ∈ openWindow C (((2 : ℝ) ^ n)⁻¹) (stageCenter hsep n) := by
    rwa [stageCenter_eq hsep hb]
  exact le_trans
    ((meshStage hsep hgrid hmesh s n).step.diam_star_carrier_le h₀ hsep hxD)
    ((gridStage hsep hgrid s n).diam_star_le hx')

/-- The stages of the recursion. -/
noncomputable def stages : ℕ → AdmissibleStage S₀ C
  | 0 => s₀
  | n + 1 => nextStage hsep hgrid hmesh (stages n) n

@[simp] theorem stages_zero : stages hsep hgrid hmesh s₀ 0 = s₀ := rfl

theorem stages_succ (n : ℕ) :
    stages hsep hgrid hmesh s₀ (n + 1) =
      nextStage hsep hgrid hmesh (stages hsep hgrid hmesh s₀ n) n := rfl

include h₀ in
/-- **Once small, always small**: the source star of a fixed point is antitone along the
stages, by iterating the one-step monotonicity. -/
theorem diam_stages_star_anti {x : Plane} (hxD : x ∈ C ∪ inside C) {n m : ℕ} (hnm : n ≤ m) :
    diam ((stages hsep hgrid hmesh s₀ m).pair.src.star
        ((stages hsep hgrid hmesh s₀ m).pair.src.carrier x)) ≤
      diam ((stages hsep hgrid hmesh s₀ n).pair.src.star
        ((stages hsep hgrid hmesh s₀ n).pair.src.carrier x)) := by
  induction hnm with
  | refl => exact le_rfl
  | step _ ih =>
    exact le_trans
      ((nextStage_step hsep hgrid hmesh _ _).diam_star_carrier_le h₀ hsep hxD) ih

end Recursion

end Schoenflies
