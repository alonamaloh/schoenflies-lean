/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.StageRecursion
import Schoenflies.SkeletonCrosscuts
import Schoenflies.SquareMesh

/-!
# The target-mesh chooser: `Schoenflies.HasMeshSteps` from one mesh transfer per stage

`Schoenflies.HasMeshSteps` (`StageRecursion.lean`) is the target-mesh chooser of the stage
recursion: at every admissible stage `P` and every `ε > 0`, a refinement step all of whose
closed target 2-cells have diameter at most `ε`. Its intended discharger is
`prop:anchored-square-mesh` (done, `SquareMesh*.lean`) overlaid with the current target
skeleton and transferred back by `thm:finite-transfer`(b).

This module proves the whole *quantitative* half of that route, and confines the
*combinatorial* half — the overlay and the transfer — to one named hypothesis, cut at the
transfer's **conclusion**. The reason the cut is there and not at the transfer's hypotheses is
a genuine interface defect, recorded as a theorem below.

## The interface defect, machine-checked

`Schoenflies.finite_transfer_back'` (`EarStepTgt.lean`) consumes
`IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw` and `HasFreshAnchors P H Hdraw`. These two
hypotheses are **jointly unsatisfiable for every extension the mesh step needs**:

* `IsSourceExtension.edge_subset` says an edge of `H` whose arc meets an *open* old 1-cell
  runs inside that old edge's arc. A mesh spoke reaching `S` at a fresh point `z` touches, at
  `z` itself, the open 1-cell of the old outer edge `z` subdivides — so `edge_subset` forces
  the spoke inside `S`, which it is not.
* The escape — make `z` a 0-cell first, by subdividing the outer edge at `z` before proposing
  `H` — is closed off by `HasFreshAnchors.notMem_vertexSet`, which demands that a boundary
  point reached by a nonboundary edge of `H` *not* be a drawn 0-cell of the base pair; and the
  anchor bookkeeping of `IsPartialTransferOfTgt.anchor_uniqueFaceAt` genuinely needs that
  freshness, since it recognises fresh points by their ancestor being an outer *edge*.

`Schoenflies.edgeArc_subset_outer_of_hasFreshAnchors` is the formal statement: under the two
hypotheses of `finite_transfer_back'`, **every** edge of `H` meeting the outer curve lies
inside it. Consequently no nonboundary edge of `H` reaches `S` at all, `HasFreshAnchors` is
vacuous, and `H` cannot contain a mesh spoke — while `prop:anchored-square-mesh` clauses 1 and
5 (`squareMesh_face_small`, `squareMesh_isConnected_diff`) both *require* spokes. The same
overshoot of `edge_subset` also affects direction (a) — a grid edge attaches at a crossing
point inside an old open 1-cell — but there the base pair can be subdivided at the crossing
points first (`GeneratedPair.exists_subdivide_finite`), because direction (a) has no freshness
clause; direction (b) cannot pre-subdivide its fresh points. The repair therefore belongs to
the direction-(b) interface: either weaken `edge_subset` to allow an edge of `H` to *touch* an
open old 1-cell at its own endpoints (the touch points are exactly the overlay's subdivision
vertices), or extend the anchor invariant to fresh points that are 0-cells of the base
incident with a unique face. Both repairs change only hypotheses of existing theorems; the
conclusion `IsTransferOfTgt` is untouched, which is why the named hypothesis below is stated
against it and survives the repair verbatim.

## What is proved here

* the square-side domain fact `frontier (Q ∖ S) ⊆ S` that any direction-(b) discharger feeds
  to `earStepTgt` (the other three of the four ambient facts are already on `main`);
* the defect theorem above;
* **the mesh bound through the transfer**: if the transferred target skeleton contains the
  anchored mesh of size `ε` (with `ε`-dense fresh points), then every closed target 2-cell of
  the transferred stage has diameter at most `ε` —
  `Schoenflies.diam_closure_cell_le_of_mesh_subset`. This is `lem:diameter-closure` plus the
  blueprint's radial estimate, with the 2-cell read as a connected set missing the mesh
  (`Realization.cell_subset_sdiff` + `radial_diam_bound`), so nothing combinatorial about
  "which mesh face contains the cell" is needed;
* the assembly `Schoenflies.hasMeshSteps`: the named hypothesis implies `HasMeshSteps S₀ C`,
  with no other hypothesis — not even `S₀.CombInvariants` or `thm:jordan`.

## The named hypothesis

`Schoenflies.HasMeshTransfers`: at every admissible stage and every `ε > 0` there is a
`MeshTransfer` — an `ε`-dense fresh list, an extension `H` containing the anchored mesh of
size `ε`, and a completed direction-(b) transfer of `H`. Its discharger is exactly the
blueprint's mesh step: choose the fresh points among the `P.homeo`-images of a countable dense
set of strongly accessible points of `C` (`exists_countable_dense_stronglyAccessible`), so
that they are `ε`-dense on `S` and avoid the finite vertex set of the stage; overlay
`squareMesh ε fresh anchors` with the polygonal target skeleton (`lem:polygonal-overlay`,
`overlayGraph`, with 2-connectivity from `squareMesh_isTwoConnected` and the
`Graph.IsTwoConnected.union` toolkit); and run the *repaired* `thm:finite-transfer`(b), whose
fresh-anchor clauses are clauses 3–4 of the mesh proposition (`squareMesh_inner_edge_at_fresh`,
`squareMesh_unique_inner_edge`) and strong accessibility of the chosen anchors. Every clause
of the bundle is a clause of that route's conclusion, so nothing here restates a goal of this
module; what keeps the bundle conditional is the defect above, not any missing mathematics.

## Blueprint

* `Schoenflies.frontier_closedSquare_sdiff_modelCurve` — the square half of "both regions are
  closed Jordan regions" in the form the transfer consumes.
* `Schoenflies.edgeArc_subset_outer_of_hasFreshAnchors` — the finding: the stated hypotheses
  of `thm:finite-transfer`(b) admit no extension with a boundary-reaching nonboundary edge.
* `Schoenflies.IsLoop.not_meets_both_arcs`, `Schoenflies.IsLoop.exists_param_modulus`,
  `Schoenflies.freshDense_of_param_dense`, `Schoenflies.IsLoop.exists_param_window_of_dense`,
  `Schoenflies.exists_freshDense_of_dense` — the blueprint's "choose `z_0, …, z_{m-1}` in
  cyclic order so that each boundary arc between consecutive ones has diameter `< δ/4`",
  done: any dense subset of `S` contains a finite `FreshDense` list, for every `δ > 0`.
* `Schoenflies.diam_closure_cell_le_of_mesh_subset` — "every closed target 2-cell of `Γ'_n`
  has diameter `< ε_n`": the mesh sentence of *Quantitative refinement*, from
  `prop:anchored-square-mesh` clause 1's radial estimate and `lem:diameter-closure`.
* `Schoenflies.MeshTransfer`, `Schoenflies.HasMeshTransfers` — the mesh step of
  *Quantitative refinement* up to its transfer, as one named hypothesis.
* `Schoenflies.MeshTransfer.meshStepData`, `Schoenflies.hasMeshSteps` — the discharge of
  `Schoenflies.HasMeshSteps` from it.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-! ### The square-side domain facts

`earStepTgt` takes the two regions in one shape: `dom ∖ outer` open with frontier inside
`outer`. On the source side `Schoenflies.isOpen_sdiff_outer_of_isSeparating` and its companion
discharge both from `thm:jordan`; on the square side the openness half is
`Schoenflies.isOpen_closedSquare_sdiff_modelCurve` (`StageTower.lean`) and the frontier half is
proved here. -/

/-- The frontier of the open square is inside the model curve — the last of the four ambient
facts of `thm:finite-transfer`, and the only one that was not yet on `main`. -/
theorem frontier_closedSquare_sdiff_modelCurve :
    frontier (Plane.closedSquare 0 1 \ modelCurve) ⊆ modelCurve := by
  rw [closedSquare_sdiff_modelCurve, (Plane.isOpen_openSquare 0 1).frontier_eq]
  intro x hx
  have hcl : x ∈ Plane.closedSquare 0 1 :=
    closure_minimal (fun y hy => mem_closedSquare_zero_one.2 (mem_openSquare_zero_one.1 hy).le)
      (Plane.isClosed_closedSquare 0 1) hx.1
  have h1 : Plane.supNorm x ≤ 1 := mem_closedSquare_zero_one.1 hcl
  have h2 : ¬ Plane.supNorm x < 1 := fun h => hx.2 (mem_openSquare_zero_one.2 h)
  exact le_antisymm h1 (not_lt.1 h2)

/-! ### The interface defect of `thm:finite-transfer`(b), machine-checked -/

/-- **The hypotheses of `Schoenflies.finite_transfer_back'` admit no boundary-reaching
nonboundary edge.** If `H` is an `IsSourceExtension` of the target realization and its fresh
anchors satisfy `HasFreshAnchors`, then every edge of `H` that meets the outer curve lies
inside it.

The proof is short because the two hypotheses close every door: the meeting point is not a
drawn 0-cell of the stage (`HasFreshAnchors.notMem_vertexSet` — this is where a nonboundary
edge at the point is used), so it lies in the *open* 1-cell of an outer edge, and
`IsSourceExtension.edge_subset` then forces the whole arc of the meeting edge into that outer
edge's arc, which is part of the outer curve.

Read contrapositively: an extension with a mesh spoke — an edge reaching `S` without lying in
`S` — can never satisfy both hypotheses, whatever the fresh points are. This is why the named
hypothesis of this module is stated against the transfer's *conclusion* and not against its
hypotheses; see the module docstring for the two candidate repairs. -/
theorem edgeArc_subset_outer_of_hasFreshAnchors
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {H : Graph Plane γ}
    {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) (hA : HasFreshAnchors P H Hdraw)
    {f : γ} (hf : f ∈ E(H)) {p : Plane} (hp : p ∈ Graph.edgeArc Hdraw f)
    (hpS : p ∈ tgtOuter) : Graph.edgeArc Hdraw f ⊆ tgtOuter := by
  by_contra hnot
  -- `p` is reached by a nonboundary edge of `H`, so it is not a drawn 0-cell of the stage.
  have hpV : p ∉ V(P.tgt.graph) := hA.notMem_vertexSet hpS ⟨f, hf, hp, hnot⟩
  -- `p` lies on the realized outer cycle: on a drawn outer 0-cell — excluded — or on the arc
  -- of an outer edge.
  have hpOut : p ∈ P.tgt.outerSet := by
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]; exact hpS
  rcases hpOut with hv | hedge
  · refine hpV ?_
    rw [Graph.vertexSet_map] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    rw [Realization.vertexSet_graph]
    exact ⟨v, P.str.outerGraph_le.vertexSet_mono hv, rfl⟩
  · obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.1 hedge
    have heO : e ∈ E(P.str.outerGraph) := by rwa [Graph.edgeSet_map] at he
    have heE : e ∈ E(P.str.skel) := P.str.outerGraph_le.edgeSet_mono heO
    obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet heE
    -- off the drawn 0-cells, `p` lies in the *open* 1-cell of `e`
    have hpcell : p ∈ P.tgt.cell e := by
      rw [P.tgt.cell_edge hl]
      refine ⟨hpe, fun hmem => hpV ?_⟩
      have hOrEq : p = P.tgt.pos x ∨ p = P.tgt.pos y := by simpa using hmem
      rw [Realization.vertexSet_graph]
      rcases hOrEq with h | h
      · exact ⟨x, hl.left_mem, h.symm⟩
      · exact ⟨y, hl.right_mem, h.symm⟩
    -- and `edge_subset` forces the whole of `f` into the outer curve
    refine hnot ((hH.edge_subset heE hf ⟨p, hp, hpcell⟩).trans ?_)
    refine (Realization.edgeArc_subset_outerSet P.tgt heO).trans ?_
    rw [P.tgt_isWeaklyAdmissible.outerSet_eq]

/-- The anchor clauses of `thm:finite-transfer`(b), as stated, are vacuous: under the two
hypotheses of `finite_transfer_back'` no point of the outer curve is `NonboundaryAt` at all. -/
theorem not_nonboundaryAt_of_hasFreshAnchors
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {H : Graph Plane γ}
    {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) (hA : HasFreshAnchors P H Hdraw)
    {p : Plane} (hpS : p ∈ tgtOuter) : ¬ NonboundaryAt H Hdraw tgtOuter p := by
  rintro ⟨f, hf, hp, hnot⟩
  exact hnot (edgeArc_subset_outer_of_hasFreshAnchors hH hA hf hp hpS)

/-! ### `FreshDense` from parameter-dense fresh points

Nothing on `main` constructs a nontrivial `Schoenflies.FreshDense` list: the only construction
is the vacuous `Schoenflies.freshDense_of_four_sqrt_two_le`. The discharger of
`HasMeshTransfers` below has to make one out of the dense strongly accessible anchors, and
this section proves the geometric half of that step: **if the fresh points are `ρ`-dense in
the parameter of any loop parametrizing `S`, for a `ρ` within which the loop moves points by
at most `δ/4`, then `FreshDense fresh δ` holds** — with
`Schoenflies.IsLoop.exists_param_modulus` producing such a `ρ` for every loop and `δ`. What
remains for the discharger is a pure choice: pick, inside each parameter window of length `ρ`,
one fresh point from the dense anchor set.

The proof is the blueprint's "cut `S` into small arcs" argument run backwards on the machinery
of `TwoArcs.lean`. A preconnected subset of `S` avoiding all fresh points cannot have two
fresh parameters interleaved with two of its own (`IsLoop.not_meets_both_arcs`: the two arcs
between the fresh points, `IsLoop.pieces_cover` / `IsLoop.pieces_meet_at_ends`, have plane-open
complements covering the set and separating it). So the parameters the set visits either span
no fresh parameter — a window of length at most `ρ` — or trap every fresh parameter between
them, pinning both endpoints to the loop's seam; either way its points are within `δ/2`. -/

section FreshDenseConstruction

open unitInterval

variable {f : ℝ → Plane}

/-- **The separation lemma.** A preconnected set inside the loop's image which avoids the two
cut points `f a`, `f b` cannot meet both the middle arc and the outside arc: the complements of
the two arcs are plane-open, they cover the set, and each contains one of the two given
points, so preconnectedness would put a point of the set outside the whole curve. -/
theorem IsLoop.not_meets_both_arcs (hf : IsLoop f) {A : Set Plane} (hA : IsPreconnected A)
    (hsub : A ⊆ f '' I) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a < b) (hfa : f a ∉ A) (hfb : f b ∉ A) {x y : Plane} (hx : x ∈ A) (hy : y ∈ A)
    (hxm : x ∈ f '' Icc a b) (hyo : y ∈ f '' Icc 0 a ∪ f '' Icc b 1) : False := by
  set M : Set Plane := f '' Icc a b with hM
  set O : Set Plane := f '' Icc 0 a ∪ f '' Icc b 1 with hO
  have hMO : M ∪ O = f '' I := IsLoop.pieces_cover ha hb
  have hmeet : M ∩ O = {f a, f b} := hf.pieces_meet_at_ends ha hb ha1 hb1 hab
  have hMc : IsCompact M := isCompact_Icc.image_of_continuousOn
    (hf.continuousOn.mono (IsLoop.middle_subset_I ha hb))
  have hOc : IsCompact O :=
    (isCompact_Icc.image_of_continuousOn
        (hf.continuousOn.mono (IsLoop.front_subset_I ha))).union
      (isCompact_Icc.image_of_continuousOn (hf.continuousOn.mono (IsLoop.back_subset_I hb)))
  -- the set avoids the two cut points
  have hcut : ∀ ⦃z⦄, z ∈ A → z ∉ ({f a, f b} : Set Plane) := by
    intro z hz hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    exacts [hfa hz, hfb hz]
  -- so the two open complements cover it
  have hcover : A ⊆ Oᶜ ∪ Mᶜ := by
    intro z hz
    have hzMO : z ∈ M ∪ O := by rw [hMO]; exact hsub hz
    rcases hzMO with hzM | hzO
    · exact Or.inl fun hzO => hcut hz (by rw [← hmeet]; exact ⟨hzM, hzO⟩)
    · exact Or.inr fun hzM => hcut hz (by rw [← hmeet]; exact ⟨hzM, hzO⟩)
  have hxO : x ∉ O := fun hxO => hcut hx (by rw [← hmeet]; exact ⟨hxm, hxO⟩)
  have hyM : y ∉ M := fun hyM => hcut hy (by rw [← hmeet]; exact ⟨hyM, hyo⟩)
  obtain ⟨w, hwA, hwO, hwM⟩ := hA Oᶜ Mᶜ hOc.isClosed.isOpen_compl hMc.isClosed.isOpen_compl
    hcover ⟨x, hx, hxO⟩ ⟨y, hy, hyM⟩
  have hwMO : w ∈ M ∪ O := by rw [hMO]; exact hsub hwA
  rcases hwMO with h | h
  exacts [hwM h, hwO h]

/-- **A parameter modulus for every loop**: within some window length `ρ` the loop moves
points by at most `ε`. Heine–Cantor on the compact parameter interval. -/
theorem IsLoop.exists_param_modulus (hf : IsLoop f) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ u ∈ I, ∀ v ∈ I, |u - v| ≤ ρ → dist (f u) (f v) ≤ ε := by
  obtain ⟨ρ, hρ, h⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_I.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  refine ⟨ρ / 2, by linarith, fun u hu v hv huv => ?_⟩
  refine (h u hu v hv ?_).le
  rw [Real.dist_eq]
  linarith

/-- **`FreshDense` from parameter density.** If every parameter window of length `ρ` contains
a fresh point and the loop moves parameters `ρ` apart by at most `δ/4`, the fresh points are
`δ`-dense on `S` in the sense of `Schoenflies.FreshDense`. This is the geometric content of
the blueprint's "choose `z_0, …, z_{m-1}` in cyclic order so that each boundary arc between
consecutive ones has diameter `< δ/4`"; the cyclic order is replaced by the two-sided case
split on where the avoided parameters can sit. -/
theorem freshDense_of_param_dense (hf : IsLoop f) (himg : f '' I = modelCurve)
    {fresh : List Plane} {ρ δ : ℝ} (hρ : 0 < ρ)
    (hmod : ∀ u ∈ I, ∀ v ∈ I, |u - v| ≤ ρ → dist (f u) (f v) ≤ δ / 4)
    (hnet : ∀ u, 0 ≤ u → u + ρ ≤ 1 → ∃ w ∈ Ioo u (u + ρ), f w ∈ fresh) :
    FreshDense fresh δ := by
  have hδ0 : 0 ≤ δ := by
    have h := hmod 0 zero_mem_I 0 zero_mem_I (by simpa using hρ.le)
    rw [dist_self] at h
    linarith
  intro A hA hconn x hx y hy
  have hsub : A ⊆ f '' I := fun z hz => by rw [himg]; exact (hA hz).1
  have havoid : ∀ ⦃w⦄, w ∈ I → f w ∈ fresh → f w ∉ A := fun w _hw hwf h => (hA h).2 hwf
  -- the key claim, for ordered parameters short of the finish
  suffices key : ∀ s t : ℝ, s ∈ I → t ∈ I → s ≠ 1 → t ≠ 1 → s ≤ t →
      f s ∈ A → f t ∈ A → dist (f s) (f t) ≤ δ / 2 by
    obtain ⟨s, hs, hs1, hfs⟩ := hf.parameter_before_finish (hsub hx)
    obtain ⟨t, ht, ht1, hft⟩ := hf.parameter_before_finish (hsub hy)
    rcases le_total s t with h | h
    · rw [← hfs, ← hft]
      exact key s t hs ht hs1 ht1 h (by rw [hfs]; exact hx) (by rw [hft]; exact hy)
    · rw [← hfs, ← hft, dist_comm]
      exact key t s ht hs ht1 hs1 h (by rw [hft]; exact hy) (by rw [hfs]; exact hx)
  intro s t hs ht hs1 ht1 hst hfsA hftA
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [dist_self]; linarith
  by_cases hmid : ∃ w ∈ Ioo s t, f w ∈ fresh
  · -- A fresh parameter sits strictly between `s` and `t`. Then no fresh parameter can sit
    -- strictly outside `[s, t]` — the separation lemma — so the net pins both `s` and `t` to
    -- within `ρ` of the loop's seam, and the seam point bridges the two.
    obtain ⟨w₁, hw₁, hw₁f⟩ := hmid
    have hw₁I : w₁ ∈ I := ⟨hs.1.trans hw₁.1.le, hw₁.2.le.trans ht.2⟩
    have hw₁1 : w₁ ≠ 1 := ne_of_lt (lt_of_lt_of_le hw₁.2 ht.2)
    have hbefore : ∀ w, 0 ≤ w → w < s → f w ∈ fresh → False := by
      intro w hw0 hws hwf
      have hwI : w ∈ I := ⟨hw0, (hws.trans hlt).le.trans ht.2⟩
      exact hf.not_meets_both_arcs hconn hsub hwI hw₁I
        (ne_of_lt (lt_of_lt_of_le hws hs.2)) hw₁1 (hws.trans hw₁.1)
        (havoid hwI hwf) (havoid hw₁I hw₁f) hfsA hftA
        ⟨s, ⟨hws.le, hw₁.1.le⟩, rfl⟩ (Or.inr ⟨t, ⟨hw₁.2.le, ht.2⟩, rfl⟩)
    have hafter : ∀ w, t < w → w < 1 → f w ∈ fresh → False := by
      intro w htw hw1 hwf
      have hwI : w ∈ I := ⟨ht.1.trans htw.le, hw1.le⟩
      exact hf.not_meets_both_arcs hconn hsub hw₁I hwI hw₁1 (ne_of_lt hw1)
        (hw₁.2.trans htw) (havoid hw₁I hw₁f) (havoid hwI hwf) hftA hfsA
        ⟨t, ⟨hw₁.2.le, htw.le⟩, rfl⟩ (Or.inl ⟨s, ⟨hs.1, hw₁.1.le⟩, rfl⟩)
    have hsρ : s ≤ ρ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨w, hw, hwf⟩ := hnet 0 le_rfl (by linarith [hs.2])
      rw [zero_add] at hw
      exact hbefore w hw.1.le (hw.2.trans hcon) hwf
    have htρ : 1 - t ≤ ρ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨w, hw, hwf⟩ := hnet t ht.1 (by linarith)
      exact hafter w hw.1 (by linarith [hw.2]) hwf
    calc dist (f s) (f t) ≤ dist (f s) (f 0) + dist (f 0) (f t) := dist_triangle _ _ _
      _ ≤ δ / 4 + δ / 4 := by
          refine add_le_add (hmod s hs 0 zero_mem_I ?_) ?_
          · rw [sub_zero, abs_of_nonneg hs.1]; linarith
          · rw [← hf.finish_eq_start]
            refine hmod 1 one_mem_I t ht ?_
            rw [abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t)]
            linarith
      _ = δ / 2 := by ring
  · -- No fresh parameter between `s` and `t`: the net forces the window short, and the
    -- modulus finishes.
    have hts : t - s ≤ ρ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨w, hw, hwf⟩ := hnet s hs.1 (by linarith [ht.2])
      exact hmid ⟨w, ⟨hw.1, lt_trans hw.2 (by linarith)⟩, hwf⟩
    have h := hmod s hs t ht (by rw [abs_of_nonpos (by linarith : s - t ≤ 0)]; linarith)
    linarith

/-- **Density on the curve transfers to density in parameter.** For a dense subset `B` of the
loop's image, every parameter window contains a parameter carrying a point of `B`.

The window's midpoint is at positive distance from the image of the complementary parameter
set — that is injectivity of the loop, `IsLoop.injective_before_finish`, plus compactness —
and any point of `B` closer to the midpoint than that distance has all of its parameters
inside the window. -/
theorem IsLoop.exists_param_window_of_dense (hf : IsLoop f) {B : Set Plane}
    (hBS : B ⊆ f '' I) (hBdense : f '' I ⊆ closure B) {ρ : ℝ} (hρ : 0 < ρ)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u + ρ ≤ 1) : ∃ w ∈ Ioo u (u + ρ), f w ∈ B := by
  set m : ℝ := u + ρ / 2 with hm
  have hmI : m ∈ I := ⟨by linarith, by linarith⟩
  have hm1 : m ≠ 1 := ne_of_lt (by linarith)
  have hm0 : 0 < m := by linarith
  set K : Set Plane := f '' Icc 0 u ∪ f '' Icc (u + ρ) 1 with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn
        (hf.continuousOn.mono (Icc_subset_Icc le_rfl (by linarith)))).union
      (isCompact_Icc.image_of_continuousOn
        (hf.continuousOn.mono (Icc_subset_Icc (by linarith) le_rfl)))
  have hKne : K.Nonempty := ⟨f 0, Or.inl ⟨0, ⟨le_rfl, hu⟩, rfl⟩⟩
  -- the midpoint is off the complementary arcs: injectivity of the loop
  have hfmK : f m ∉ K := by
    rintro (⟨v, hv, hvm⟩ | ⟨v, hv, hvm⟩)
    · have hv1 : v ≠ 1 := ne_of_lt (lt_of_le_of_lt hv.2 (by linarith))
      have hvI : v ∈ I := ⟨hv.1, hv.2.trans (by linarith)⟩
      have : v = m := hf.injective_before_finish hvI hmI hv1 hm1 hvm
      linarith [hv.2]
    · rcases eq_or_ne v 1 with rfl | hv1
      · have h0m : f 0 = f m := hf.finish_eq_start ▸ hvm
        have : (0 : ℝ) = m :=
          hf.injective_before_finish zero_mem_I hmI one_ne_zero.symm hm1 h0m
        linarith
      · have hvI : v ∈ I := ⟨le_trans (by linarith) hv.1, hv.2⟩
        have : v = m := hf.injective_before_finish hvI hmI hv1 hm1 hvm
        linarith [hv.1]
  have hpos : 0 < Metric.infDist (f m) K :=
    (hKc.isClosed.notMem_iff_infDist_pos hKne).1 hfmK
  -- a point of `B` closer to the midpoint than the complementary arcs are
  obtain ⟨b, hbB, hbd⟩ := Metric.mem_closure_iff.1 (hBdense ⟨m, hmI, rfl⟩) _ hpos
  obtain ⟨w, hwI, hwb⟩ := hBS hbB
  have hwK : ∀ hbK : b ∈ K, False := fun hbK => by
    have h := Metric.infDist_le_dist_of_mem (x := f m) hbK
    linarith
  refine ⟨w, ⟨?_, ?_⟩, by rw [hwb]; exact hbB⟩
  · by_contra hcon
    push Not at hcon
    exact hwK (Or.inl ⟨w, ⟨hwI.1, hcon⟩, hwb⟩)
  · by_contra hcon
    push Not at hcon
    exact hwK (Or.inr ⟨w, ⟨hcon, hwI.2⟩, hwb⟩)

/-- **A `FreshDense` list inside any dense subset of the model curve.** Combined with
`Schoenflies.IsJordanCurve.homeomorph_modelCurve`'s loop (any loop parametrizing `S` will do),
this reduces the fresh-point selection of `prop:anchored-square-mesh` entirely to producing a
*dense set of admissible boundary points* — for the mesh step, the `P.homeo`-images of the
countable dense strongly accessible set of `Schoenflies.exists_countable_dense_stronglyAccessible`,
with the stage's finitely many drawn 0-cells removed. -/
theorem exists_freshDense_of_dense (hf : IsLoop f) (himg : f '' I = modelCurve)
    {B : Set Plane} (hBS : B ⊆ modelCurve) (hBdense : modelCurve ⊆ closure B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ fresh : List Plane, (∀ z ∈ fresh, z ∈ B) ∧ FreshDense fresh δ := by
  classical
  obtain ⟨ρ₁, hρ₁, hmod₁⟩ := hf.exists_param_modulus (by linarith : (0 : ℝ) < δ / 4)
  -- shrink the window so that it fits inside the parameter interval
  set ρ : ℝ := min ρ₁ 2⁻¹ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ (by norm_num)
  have hρ2 : ρ ≤ 2⁻¹ := min_le_right _ _
  have hmod : ∀ u ∈ I, ∀ v ∈ I, |u - v| ≤ ρ → dist (f u) (f v) ≤ δ / 4 :=
    fun u hu v hv huv => hmod₁ u hu v hv (huv.trans (min_le_left _ _))
  set half : ℝ := ρ / 2 with hhalfdef
  have hhalf0 : 0 < half := by rw [hhalfdef]; linarith
  have hBS' : B ⊆ f '' I := by rw [himg]; exact hBS
  have hBdense' : f '' I ⊆ closure B := by rw [himg]; exact hBdense
  -- one point of `B` in each half-window along a grid of spacing `half`
  have hpick : ∀ i : ℕ, (i : ℝ) * half + half ≤ 1 →
      ∃ w ∈ Ioo ((i : ℝ) * half) ((i : ℝ) * half + half), f w ∈ B := fun i hi =>
    hf.exists_param_window_of_dense hBS' hBdense' hhalf0 (by positivity) hi
  choose! w hw₁ hw₂ using hpick
  set N : ℕ := ⌊half⁻¹⌋₊ with hN
  have hmemle : ∀ i : ℕ, i < N → (i : ℝ) * half + half ≤ 1 := by
    intro i hi
    have h1 : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have h2 : (N : ℝ) ≤ half⁻¹ := Nat.floor_le (by positivity)
    have h3 : ((i + 1 : ℕ) : ℝ) * half ≤ half⁻¹ * half :=
      mul_le_mul_of_nonneg_right (h1.trans h2) hhalf0.le
    rw [inv_mul_cancel₀ hhalf0.ne'] at h3
    push_cast at h3
    linarith
  refine ⟨(List.range N).map fun i => f (w i), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
    exact hw₂ i (hmemle i (List.mem_range.1 hi))
  · refine freshDense_of_param_dense hf himg hρ hmod ?_
    intro u hu hu1
    -- the grid half-window caught inside `(u, u + ρ)`
    set i : ℕ := ⌈u / half⌉₊ with hi
    have hui : u ≤ (i : ℝ) * half := by
      have h1 : u / half ≤ (i : ℝ) := Nat.le_ceil _
      calc u = u / half * half := (div_mul_cancel₀ u hhalf0.ne').symm
        _ ≤ (i : ℝ) * half := mul_le_mul_of_nonneg_right h1 hhalf0.le
    have hiu : (i : ℝ) * half < u + half := by
      have h1 : (i : ℝ) < u / half + 1 := Nat.ceil_lt_add_one (by positivity)
      calc (i : ℝ) * half < (u / half + 1) * half := mul_lt_mul_of_pos_right h1 hhalf0
        _ = u + half := by rw [add_mul, div_mul_cancel₀ _ hhalf0.ne', one_mul]
    have hile : (i : ℝ) * half + half ≤ 1 := by
      have hhρ : half + half = ρ := by rw [hhalfdef]; ring
      linarith
    have hwin := hw₁ i hile
    refine ⟨w i, ⟨lt_of_le_of_lt hui hwin.1, ?_⟩, ?_⟩
    · have hhρ : half + half = ρ := by rw [hhalfdef]; ring
      linarith [hwin.2]
    · -- the pick is on the list: its index is below the grid size
      have hiN : i < N := by
        have h2 : ((i + 1 : ℕ) : ℝ) ≤ half⁻¹ := by
          rw [← one_div, le_div_iff₀ hhalf0]
          push_cast
          linarith
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_floor h2)
      exact List.mem_map.2 ⟨i, List.mem_range.2 hiN, rfl⟩

end FreshDenseConstruction

/-! ### The mesh bound through the transfer

The blueprint carries clause 1 of `prop:anchored-square-mesh` through the overlay as "every
open target 2-cell of `Γ'_n` lies in an open 2-cell of `T_n`". The formal route is shorter and
avoids the face correspondence entirely: a 2-cell of the transferred stage is a *connected* set
(`IsFaceJordan.isConnected`) inside the open square and disjoint from the drawn skeleton
(`Realization.cell_subset_sdiff`), and the drawn skeleton contains the mesh segments; so the
blueprint's own radial estimate `Schoenflies.radial_diam_bound` bounds its diameter directly,
and `Metric.diam_closure` (`lem:diameter-closure`) moves the bound to the closed 2-cell. -/

/-- **Every closed target 2-cell of a stage whose skeleton contains the anchored mesh of size
`ε` has diameter at most `ε`.** The mesh sentence of one step of *Quantitative refinement*. -/
theorem diam_closure_cell_le_of_mesh_subset
    {T : GeneratedPair S₀ srcOuter srcDom modelCurve (Plane.closedSquare 0 1)}
    {fresh : List Plane} {ε : ℝ} (hε : 0 < ε) (hdense : FreshDense fresh ε)
    (hmesh : cover (meshSegments (meshCount ε) fresh) ⊆ T.tgt.skeletonSet)
    {F : γ} (hF : F ∈ T.str.faces) : diam (closure (T.tgt.cell F)) ≤ ε := by
  have hJ := T.tgt_isFaceJordan
  have houter : modelCurve ⊆ T.tgt.skeletonSet := by
    have h1 := T.tgt.outerSet_subset_skeletonSet
    rwa [T.tgt_isWeaklyAdmissible.outerSet_eq] at h1
  have hsub : T.tgt.cell F ⊆
      (Plane.closedSquare 0 1 \ modelCurve) \ T.tgt.skeletonSet :=
    Realization.cell_subset_sdiff T.tgt_isCellDecomposition houter hF
  -- a base point of the 2-cell, inside the open square
  obtain ⟨b, hb⟩ := hJ.nonempty hF
  have hbase : Plane.supNorm b < 1 := by
    have h1 := (hsub hb).1
    rw [closedSquare_sdiff_modelCurve] at h1
    exact mem_openSquare_zero_one.1 h1
  -- the 2-cell misses the mesh, because it misses the whole drawn skeleton
  have hdisj : ∀ x ∈ T.tgt.cell F, x ∉ cover (meshSegments (meshCount ε) fresh) :=
    fun x hx hmem => (hsub hx).2 (hmesh hmem)
  have hNδ : 2 * Real.sqrt 2 ≤ ε * (meshCount ε : ℝ) := (meshCount_spec hε).le
  obtain ⟨-, hd⟩ := radial_diam_bound (two_le_meshCount ε) hNδ hdense
    (hJ.isConnected hF).isPreconnected hdisj hb hbase
  -- the arithmetic: `ε/2 + √2/N ≤ ε` because `2√2 ≤ εN`
  have hNR : (0 : ℝ) < (meshCount ε : ℝ) := by
    exact_mod_cast lt_of_lt_of_le two_pos (two_le_meshCount ε)
  have hhalf : Real.sqrt 2 / (meshCount ε : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ hNR]
    nlinarith [hNδ]
  have h0 : (0 : ℝ) ≤ ε / 2 + Real.sqrt 2 / (meshCount ε : ℝ) :=
    add_nonneg (by linarith) (div_nonneg (Real.sqrt_nonneg 2) hNR.le)
  rw [Metric.diam_closure]
  calc diam (T.tgt.cell F) ≤ ε / 2 + Real.sqrt 2 / (meshCount ε : ℝ) :=
        diam_le_of_forall_dist_le h0 hd
    _ ≤ ε := by linarith

/-! ### The named hypothesis and the discharge -/

variable [Nonempty γ] {C : Set Plane}

/-- **NAMED HYPOTHESIS (data): one mesh transfer at stage `P` with mesh `ε`.**

The blueprint's mesh step, cut at the conclusion of `thm:finite-transfer`(b): an `ε`-dense
fresh list on `S`, an extension containing the anchored mesh of size `ε`, and the completed
transfer. The cut is at the conclusion because the *hypotheses* of
`Schoenflies.finite_transfer_back'` are jointly unsatisfiable for a mesh overlay
(`Schoenflies.edgeArc_subset_outer_of_hasFreshAnchors`); the conclusion `IsTransferOfTgt` is
untouched by either candidate repair of that interface, so this bundle is stable under the
repair.

Discharged by (once the direction-(b) interface is repaired; see the module docstring):

* `fresh`/`hdense` — the `P.homeo`-images of strongly accessible points of `C`
  (`Schoenflies.exists_countable_dense_stronglyAccessible`), chosen `ε`-dense along `S` and
  avoiding the finite drawn vertex set of the stage; this is the blueprint's "choose
  `z_0, …, z_{m-1}` in cyclic order", in the order-free form `Schoenflies.FreshDense` was
  designed for.
* `H`/`Hdraw`/`mesh_subset` — `Schoenflies.squareMesh ε fresh anchors` overlaid with the
  polygonal target skeleton (`tgt_isPolygonal`) by the `lem:polygonal-overlay` machinery
  (`Schoenflies.overlayGraph`, `Schoenflies.attachGraph`), which only ever adds points, so the
  mesh cover survives into the overlay's point set and hence — by the transfer's
  `skeletonSet_eq` — into the new target skeleton.
* `transfer` — the repaired `thm:finite-transfer`(b), its fresh-anchor clauses supplied by
  clauses 3–4 of `prop:anchored-square-mesh` (`Schoenflies.squareMesh_inner_edge_at_fresh`,
  `Schoenflies.squareMesh_unique_inner_edge`), its 2-connectivity by
  `Schoenflies.squareMesh_isTwoConnected` (`hdense` and `ε < 4` give the two distinct fresh
  points) with the `Graph.IsTwoConnected.union` toolkit for the overlay, its connectedness
  clause by `Schoenflies.squareMesh_isConnected_diff`, and the four ambient facts by
  `Schoenflies.isOpen_sdiff_outer_of_isSeparating`,
  `Schoenflies.frontier_sdiff_outer_of_isSeparating`,
  `Schoenflies.isOpen_closedSquare_sdiff_modelCurve` and
  `Schoenflies.frontier_closedSquare_sdiff_modelCurve` above. -/
structure MeshTransfer (P : StagePair S₀ C) (ε : ℝ) where
  /-- The fresh boundary points of the mesh. -/
  fresh : List Plane
  /-- They are `ε`-dense along `S` — what makes every mesh face small. -/
  hdense : FreshDense fresh ε
  /-- The proposed extension: the mesh overlaid with the current target skeleton. -/
  H : Graph Plane γ
  /-- Its drawing. -/
  Hdraw : γ → ℝ → Plane
  /-- The transferred stage. -/
  next : StagePair S₀ C
  /-- The parent map of the transfer. -/
  par : γ → γ
  /-- The completed direction-(b) transfer — the conclusion of `thm:finite-transfer`(b) for
  the overlay. -/
  transfer : IsTransferOfTgt next P H Hdraw par
  /-- The overlay contains the anchored mesh of size `ε`. -/
  mesh_subset : cover (meshSegments (meshCount ε) fresh) ⊆ Graph.pointSet H Hdraw

/-- **NAMED HYPOTHESIS — the mesh transfer chooser**: at every admissible stage and every
`ε > 0`, some mesh transfer exists. `Schoenflies.hasMeshSteps` turns it into the target-mesh
chooser of the stage recursion; see `Schoenflies.MeshTransfer` for who discharges it. -/
def HasMeshTransfers (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → Nonempty (MeshTransfer P ε)

/-- **One mesh transfer is one mesh step.** The step relation is
`Schoenflies.IsTransferOfTgt.isRefinementStep`; the 2-cell bound is the mesh carried through
the transfer's `skeletonSet_eq` into `Schoenflies.diam_closure_cell_le_of_mesh_subset`. -/
def MeshTransfer.meshStepData {P : StagePair S₀ C} {ε : ℝ} (hε : 0 < ε)
    (M : MeshTransfer P ε) : MeshStepData P ε where
  next := M.next
  par := M.par
  step := M.transfer.isRefinementStep
  diam_closure_cell_le := fun _F hF =>
    diam_closure_cell_le_of_mesh_subset hε M.hdense
      (M.transfer.skeletonSet_eq ▸ M.mesh_subset) hF

omit [Nonempty γ] in
/-- **The discharge of the target-mesh chooser.** Given one mesh transfer per admissible stage
and mesh size, `Schoenflies.HasMeshSteps` holds — with no further hypothesis: the quantitative
sentence of the recursion step is proved, not assumed. -/
theorem hasMeshSteps (hM : HasMeshTransfers S₀ C) : HasMeshSteps S₀ C :=
  fun P hsrc htgt _ε hε => (hM P hsrc htgt hε).elim fun M => ⟨M.meshStepData hε⟩

/-! ### The interface, exercised

A machine-checked statement that the reduction composes with the stage recursion: over the
concrete base, the two remaining obligations of Phase 3 are the source-grid chooser and the
mesh transfer chooser, and together they produce the Phase 3 deliverable. -/

example {C : Set Plane} (hC : IsJordanCurve C) (hg : HasGridSteps initialStructure C)
    (hm : HasMeshTransfers initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC hg (hasMeshSteps hm)⟩

end Schoenflies
