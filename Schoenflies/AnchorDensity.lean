/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshTransfer
import Schoenflies.PolygonalSkeletonArcs

/-!
# `lem:anchor-density`: the dense anchor set of the stage tower

The last unformalized statement of the blueprint. `lem:anchor-density` says: let `𝒜∞ ⊆ 𝒜` be
the set of `u`-preimages of all fresh target anchors used over all stages of the recursion of
*Quantitative refinement*; then `u(𝒜∞)` is dense in `S`, `𝒜∞` is dense in `C`, and at every
stage containing a point of `𝒜∞` that point is incident with a nonboundary edge.

## The formulation, derived from the consumers

Phase 4 consumes the lemma through exactly three interfaces, and the shapes below are copied
from them rather than from the blueprint's prose:

* the **dense-anchor conjuncts** of `Schoenflies.HasLimitHomeomorphism`
  (`BoundaryContinuity2.lean`): a set `𝒜` with `𝒜 ⊆ C` and `C ⊆ closure 𝒜`;
* the **anchor-incidence hypothesis** of `GeneratedPair.exists_anchor_crosscut_stage`
  (`SkeletonCrosscuts.lean`): at a common finite stage, each anchor is a drawn 0-cell
  `P.src.pos va` with `va ∈ V(P.str.outerGraph)` and
  `∃ e, P.str.skel.Inc e va ∧ e ∉ E(P.str.outerGraph)`;
* the **boundary identification** that `docs/ROADMAP.md` Phase 4 says "whoever builds the stage
  tower must carry": clause 2 of `def:matched-pair`, `g = u` on `C`, which
  `CellStructure.SkeletonHomeo` deliberately does not record.

`Schoenflies.IsAnchorVertexAt` is the per-stage invariant: the point is a drawn *target*
0-cell, on the outer cycle combinatorially, with an incident nonboundary edge. It is stated on
the target side because that is what the mesh step naturally produces (the fresh points are
chosen on `S`); the source-side reading the crosscut lemma consumes is *derived*
(`AnchoredStageSequence.exists_src_anchor`) through the skeleton homeomorphism and the carried
identification `g = u` on `C`.

`Schoenflies.AnchoredStageSequence` extends `Schoenflies.StageSequence` by the anchor data:
the per-stage fresh lists with their `Schoenflies.FreshDense` density, the invariant that each
fresh point is an anchor vertex of the next stage, its persistence across one step, the
boundary identification at the base, and connectedness of each stage's source nonboundary part
(admissibility, which `StageSequence` dropped — see *Interface gaps* below). From those fields
everything of `lem:anchor-density` and its consumers is **proved**:

* `AnchoredStageSequence.anchors` is `𝒜∞`, as the `u`-preimage of the fresh points;
* `AnchoredStageSequence.dense_freshPoints` — "`u(𝒜∞)` is dense in `S`": the fresh points of a
  late stage are `eps n`-dense along the curve (`FreshDense`), and a subarc of `S` around any
  point has positive diameter, so it meets every sufficiently late fresh list;
* `AnchoredStageSequence.anchors_dense` — "`𝒜∞` is dense in `C`": the blueprint's "a continuous
  surjection carries dense subsets of its domain to dense subsets of its codomain", with
  `u⁻¹ = v` the continuous surjection `S → C`;
* `AnchoredStageSequence.hasAnchorCrosscuts` — `Schoenflies.HasAnchorCrosscuts` for the limit
  map, by running `GeneratedPair.exists_anchor_crosscut_stage` at a common stage (persistence
  supplies one) and replacing the stage homeomorphism `g` by `F` via
  `StageSequence.F_eq_skelHomeo` and by `u` at the endpoints via the carried identification;
* `AnchoredStageSequence.hasSpokes` — `Schoenflies.HasSpokes` for the limit map: the germ `J`
  is an initial open subarc of the incident nonboundary edge (the spoke), whose points lie in
  the open 1-cell, hence in `inside C`; its `g`-image clings to `g c = u c`.

The `example` after `hasLimitHomeomorphism_conjuncts` machine-checks that the five statements
are *exactly* the body of `Schoenflies.HasLimitHomeomorphism` for the given curve and boundary
map.

## The anchored recursion

The second half rebuilds the stage recursion of `StageRecursion.lean` so that it produces an
`AnchoredStageSequence`. `Schoenflies.stageSequence` cannot be reused as a term: its mesh
steps choose fresh points through `Nonempty.some` and export nothing about the choice — the
recorded interface gap of this wave. The enrichment is confined to the two chooser bundles:

* `Schoenflies.AnchoredMeshStepData` extends `MeshStepData` with the fresh list, its density,
  membership in `S`, the anchor-vertex invariant at the produced stage, and one-step
  persistence;
* `Schoenflies.AnchoredGridStepData` extends `GridStepData` with one-step persistence alone
  (a grid step touches no boundary vertex, so persistence is all it owes).

`Schoenflies.HasAnchoredGridSteps` / `Schoenflies.HasAnchoredMeshSteps` are the enriched
choosers, and `Schoenflies.anchoredStageSequence` is the recursion re-run on them — the
quantitative glue (`prop:shrinking-stars`, both halves) is re-proved here against the anchored
stages, reusing every per-step lemma of `StageRecursion.lean`.

## Blueprint

* `Schoenflies.IsAnchorVertexAt` — the per-stage clause of **`lem:anchor-density`**: "that
  point is incident with a nonboundary edge", as the stage's combinatorics states it.
* `Schoenflies.AnchoredStageSequence` — the stage tower of *Quantitative refinement* together
  with the anchor bookkeeping of **`lem:anchor-density`** and clause 2 of **`def:matched-pair`**.
* `AnchoredStageSequence.dense_freshPoints`, `.anchors_dense` — **`lem:anchor-density`**, the
  two density clauses.
* `AnchoredStageSequence.anchorVertexAt_of_le`, `.exists_src_anchor` — **`lem:anchor-density`**,
  the incidence clause "at every stage containing a given point of `𝒜∞`".
* `AnchoredStageSequence.hasAnchorCrosscuts` — **`lem:skeleton-crosscuts`** finished against
  the limit map: the consumer form `Schoenflies.HasAnchorCrosscuts`.
* `AnchoredStageSequence.hasSpokes` — the spoke clause of **`lem:anchor-density`** in the germ
  form `Schoenflies.HasSpokes` of `lem:crosscut-side-correspondence`.
* `Schoenflies.AnchoredMeshStepData`, `Schoenflies.AnchoredGridStepData`,
  `Schoenflies.anchoredStageSequence` — the recursion of *Quantitative refinement* rebuilt to
  carry the anchors of **`prop:anchored-square-mesh`** clauses 3–4 through the tower.
-/

open Bornology Filter Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}
  {u v : Plane → Plane}

/-! ### The per-stage invariant -/

/-- **The per-stage anchor invariant.** The point `z` is a drawn *target* 0-cell of the stage,
its name lies on the combinatorial outer cycle, and some nonboundary edge is incident with it —
the clause of `lem:anchor-density` that `GeneratedPair.exists_anchor_crosscut_stage` consumes.

Stated on the target side because the mesh step chooses its fresh points on `S`; the source
reading is derived in `AnchoredStageSequence.exists_src_anchor` through the skeleton
homeomorphism and the boundary identification `g = u` on `C`. -/
def IsAnchorVertexAt (P : StagePair S₀ C) (z : Plane) : Prop :=
  ∃ vz ∈ V(P.str.outerGraph), P.tgt.pos vz = z ∧
    ∃ e, P.str.skel.Inc e vz ∧ e ∉ E(P.str.outerGraph)

/-! ### The anchored stage tower -/

/-- **The stage tower with the anchor bookkeeping of `lem:anchor-density`.**

A `Schoenflies.StageSequence` together with the data the recursion of *Quantitative
refinement* knows and `StageSequence` forgets: which fresh boundary anchors each mesh step
used, that they are `eps`-dense along `S`, that each becomes an anchor vertex of the stage
that inserts it and stays one ever after, that the skeleton maps restrict to the boundary
homeomorphism `u` on `C` (clause 2 of `def:matched-pair`, which `SkeletonHomeo` deliberately
does not carry — `docs/ROADMAP.md` Phase 4: "whoever builds the stage tower must carry it"),
and that every stage is admissible (its source nonboundary part is connected).

From these fields the whole of `lem:anchor-density` and both consumer predicates
(`Schoenflies.HasAnchorCrosscuts`, `Schoenflies.HasSpokes`) are proved below; nothing else
about the anchors is assumed anywhere. -/
structure AnchoredStageSequence (γ : Type*) [Nonempty γ] (S₀ : CellStructure γ)
    (C : Set Plane) (u : Plane → Plane) extends StageSequence γ S₀ C where
  /-- The fresh target anchors the stage-`n` mesh step inserted. -/
  fresh : ℕ → List Plane
  /-- They lie on the boundary of the square. -/
  fresh_mem_curve : ∀ n, ∀ z ∈ fresh n, z ∈ modelCurve
  /-- They are `eps n`-dense along `S` — the mesh proposition's "consecutive fresh anchors
  bound arcs of `S` of diameter `< ε_n/4`", in the order-free form of `Schoenflies.FreshDense`. -/
  freshDense : ∀ n, FreshDense (fresh n) (eps n)
  /-- Each fresh point of step `n` is an anchor vertex of the stage that step produces. -/
  fresh_anchorAt : ∀ n, ∀ z ∈ fresh n, IsAnchorVertexAt (stage (n + 1)) z
  /-- **Anchor vertices persist**: "at all later stages an initial subedge of that spoke
  remains incident with it" — the persistence clause of `lem:anchor-density`, across one
  step. -/
  anchorAt_succ : ∀ n ⦃z⦄, IsAnchorVertexAt (stage n) z → IsAnchorVertexAt (stage (n + 1)) z
  /-- **Clause 2 of `def:matched-pair` at the base**: the stage-0 skeleton map restricts to
  the boundary homeomorphism on `C`. The nesting of the skeleton maps propagates it to every
  stage (`AnchoredStageSequence.homeo_eqOn_curve`). -/
  homeo_eq_u : Set.EqOn (stage 0).homeo.toFun u C
  /-- Every stage's source nonboundary part is connected — the admissibility that
  `StageSequence` dropped and `GeneratedPair.exists_anchor_crosscut_stage` demands. -/
  isConnected_src : ∀ n, IsConnected (stage n).src.nonboundary

namespace AnchoredStageSequence

variable (T : AnchoredStageSequence γ S₀ C u)

/-- The curve is part of every stage's realized source skeleton: it is the realized outer
cycle. -/
theorem curve_subset_skeletonSet (n : ℕ) : C ⊆ (T.stage n).src.skeletonSet :=
  (T.stage n).src_isWeaklyAdmissible.outerSet_eq.superset.trans
    (T.stage n).src.outerSet_subset_skeletonSet

/-- **Every stage's skeleton map restricts to `u` on the curve.** The base carries the clause
and the nesting of the skeleton maps (`StageSequence.skelHomeo_succ`) propagates it: the curve
lies in every stage's source skeleton. -/
theorem homeo_eqOn_curve : ∀ n, Set.EqOn (T.stage n).homeo.toFun u C := by
  intro n
  induction n with
  | zero => exact T.homeo_eq_u
  | succ n ih =>
    intro x hx
    exact (T.skelHomeo_succ n (T.curve_subset_skeletonSet n hx)).trans (ih hx)

/-- **Once an anchor vertex, always an anchor vertex** — the persistence clause of
`lem:anchor-density` iterated along the tower, which is what supplies a *common* stage for two
anchors. -/
theorem anchorVertexAt_of_le {z : Plane} {n m : ℕ} (hnm : n ≤ m)
    (h : IsAnchorVertexAt (T.stage n) z) : IsAnchorVertexAt (T.stage m) z := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact T.anchorAt_succ _ ih

/-! ### The anchor set `𝒜∞` -/

/-- The fresh target anchors of all stages together — the set the blueprint calls
`u(𝒜∞)`. -/
def freshPoints : Set Plane := ⋃ n, {z | z ∈ T.fresh n}

theorem freshPoints_subset : T.freshPoints ⊆ modelCurve := by
  rintro z hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hz
  exact T.fresh_mem_curve n z hn

/-- **`𝒜∞`**: the `u`-preimages on `C` of the fresh anchors used over all stages. -/
def anchors : Set Plane := {a ∈ C | ∃ n, u a ∈ T.fresh n}

/-- The first conjunct of `Schoenflies.HasLimitHomeomorphism`'s anchor clause. -/
theorem anchors_subset : T.anchors ⊆ C := fun _ ha => ha.1

/-- An anchor is an anchor vertex at some stage: the stage after the step that inserted its
fresh point. -/
theorem exists_anchorVertexAt_of_mem_anchors {a : Plane} (ha : a ∈ T.anchors) :
    ∃ n, IsAnchorVertexAt (T.stage n) (u a) := by
  obtain ⟨-, n, hn⟩ := ha
  exact ⟨n + 1, T.fresh_anchorAt n _ hn⟩

/-- **The source reading of the invariant** — the exact hypothesis pair of
`GeneratedPair.exists_anchor_crosscut_stage`. From target anchor-vertex-hood at `u a`, the
vertex is drawn at `a` on the source side: its source position lies on `C`, the skeleton map
sends it to its target position (`SkeletonHomeo.pos_apply`), the skeleton map is `u` on `C`
(the carried clause 2 of `def:matched-pair`), and `u` is injective on `C`. -/
theorem exists_src_anchor (hu : IsHomeoOn u v C modelCurve) {a : Plane} (haC : a ∈ C) {n : ℕ}
    (h : IsAnchorVertexAt (T.stage n) (u a)) :
    ∃ va ∈ V((T.stage n).str.outerGraph), (T.stage n).src.pos va = a ∧
      (T.stage n).tgt.pos va = u a ∧
      ∃ e, (T.stage n).str.skel.Inc e va ∧ e ∉ E((T.stage n).str.outerGraph) := by
  obtain ⟨va, hva, hpos, he⟩ := h
  have hvsk : va ∈ V((T.stage n).str.skel) :=
    (T.stage n).str.outerGraph_le.vertexSet_mono hva
  have hsrcC : (T.stage n).src.pos va ∈ C :=
    (T.stage n).src_isWeaklyAdmissible.outerSet_eq.subset
      ((T.stage n).src.pos_mem_outerSet hva)
  have hu_eq : u ((T.stage n).src.pos va) = (T.stage n).tgt.pos va :=
    (T.homeo_eqOn_curve n hsrcC).symm.trans ((T.stage n).homeo.pos_apply hvsk)
  have hsrc_pos : (T.stage n).src.pos va = a :=
    hu.injOn hsrcC haC (by rw [hu_eq, hpos])
  exact ⟨va, hva, hsrc_pos, hpos, he⟩

/-! ### Density

The blueprint's two density clauses. First `u(𝒜∞)` is dense in `S`: around any boundary point
there is a short subarc of positive diameter, and once `eps n` drops below twice that diameter
the `FreshDense` clause of stage `n` forces a fresh point onto the subarc. Then `𝒜∞` is dense
in `C`, because `u⁻¹` is a continuous surjection `S → C` and a continuous surjection carries
dense subsets of its domain to dense subsets of its codomain. -/

/-- **`u(𝒜∞)` is dense in `S`** — the first density clause of `lem:anchor-density`. -/
theorem dense_freshPoints : modelCurve ⊆ closure T.freshPoints := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f, hf, himg⟩ := isJordanCurve_modelCurve
  have hx' : x ∈ f '' I := by rw [himg]; exact hx
  obtain ⟨t, htI, ht1, hft⟩ := hf.parameter_before_finish hx'
  have ht1' : t < 1 := lt_of_le_of_ne htI.2 ht1
  -- a short parameter window to the right of `t` whose image stays in the `ε`-ball
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousWithinAt_iff.1 (hf.continuousOn t htI) ε hε
  set s : ℝ := min (t + δ / 2) ((t + 1) / 2) with hs
  have hts : t < s := lt_min (by linarith) (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsI : s ∈ I := ⟨htI.1.trans hts.le, hs1.le⟩
  have hwin : ∀ r ∈ Icc t s, dist (f r) x < ε := by
    intro r hr
    have hrI : r ∈ I := ⟨htI.1.trans hr.1, hr.2.trans hs1.le⟩
    have hrd : dist r t < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
      have := hr.2.trans (min_le_left (t + δ / 2) ((t + 1) / 2))
      linarith
    have := hcont hrI hrd
    rwa [hft] at this
  -- the second point of the subarc, distinct from `x` by injectivity of the loop
  have hyx : f s ≠ x := by
    rw [← hft]
    intro hcon
    exact hts.ne' (hf.injective_before_finish hsI htI (ne_of_lt hs1) ht1 hcon)
  have hd : 0 < dist (f s) x := dist_pos.2 hyx
  -- a stage whose mesh is below twice that distance
  obtain ⟨n, hn⟩ := (T.tendsto_eps.eventually_lt_const (by linarith :
    (0 : ℝ) < 2 * dist (f s) x)).exists
  by_cases hmeet : ∃ z ∈ T.fresh n, dist x z < ε
  · obtain ⟨z, hz, hzd⟩ := hmeet
    exact ⟨z, Set.mem_iUnion.2 ⟨n, hz⟩, hzd⟩
  · -- the subarc avoids the stage-`n` fresh points, contradicting their density
    exfalso
    push Not at hmeet
    set A : Set Plane := f '' Icc t s with hA
    have hAsub : A ⊆ modelCurve \ {z | z ∈ T.fresh n} := by
      rintro _ ⟨r, hr, rfl⟩
      have hrI : r ∈ I := ⟨htI.1.trans hr.1, hr.2.trans hs1.le⟩
      refine ⟨himg ▸ mem_image_of_mem f hrI, fun hzf => ?_⟩
      exact absurd (by rw [dist_comm]; exact hwin r hr) (not_lt.2 (hmeet _ hzf))
    have hApre : IsPreconnected A :=
      isPreconnected_Icc.image f
        (hf.continuousOn.mono fun r hr => ⟨htI.1.trans hr.1, hr.2.trans hs1.le⟩)
    have hxA : x ∈ A := ⟨t, ⟨le_refl t, hts.le⟩, hft⟩
    have hyA : f s ∈ A := ⟨s, ⟨hts.le, le_refl s⟩, rfl⟩
    have := T.freshDense n A hAsub hApre (f s) hyA x hxA
    linarith

/-- **`𝒜∞` is dense in `C`** — the second density clause of `lem:anchor-density`, and the
second conjunct of `Schoenflies.HasLimitHomeomorphism`'s anchor clause. The continuous
surjection `u⁻¹ = v : S → C` carries the dense fresh points to the anchors. -/
theorem anchors_dense (hu : IsHomeoOn u v C modelCurve) : C ⊆ closure T.anchors := by
  intro p hp
  have h1 : u p ∈ closure T.freshPoints := T.dense_freshPoints (hu.mapsTo hp)
  have hcl : closure T.freshPoints ⊆ modelCurve :=
    closure_minimal T.freshPoints_subset isJordanCurve_modelCurve.isCompact.isClosed
  have h2 : v '' closure T.freshPoints ⊆ closure (v '' T.freshPoints) :=
    ContinuousOn.image_closure (hu.continuousOn_inv.mono hcl)
  have h3 : v '' T.freshPoints ⊆ T.anchors := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hz
    have hzS : z ∈ modelCurve := T.fresh_mem_curve n z hn
    refine ⟨hu.mapsTo_inv hzS, n, ?_⟩
    rw [hu.invOn.2 hzS]
    exact hn
  have hpv : p = v (u p) := (hu.invOn.1 hp).symm
  rw [hpv]
  exact closure_mono h3 (h2 ⟨u p, h1, rfl⟩)

/-! ### The two consumer predicates -/

/-- **`Schoenflies.HasAnchorCrosscuts` for the limit map.** Two distinct anchors are anchor
vertices at a common stage (persistence supplies one);
`GeneratedPair.exists_anchor_crosscut_stage` joins them by a crosscut in that stage's skeleton
and transports it through the stage homeomorphism `g`; `StageSequence.F_eq_skelHomeo` replaces
`g` by `F` on the crosscut, and the carried identification `g = u` on `C` names the target
endpoints `u a`, `u b`. -/
theorem hasAnchorCrosscuts (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve) :
    HasAnchorCrosscuts C T.anchors u T.toStageSequence.limitTower.F := by
  intro a b ha hb hab
  obtain ⟨na, hna⟩ := T.exists_anchorVertexAt_of_mem_anchors ha
  obtain ⟨nb, hnb⟩ := T.exists_anchorVertexAt_of_mem_anchors hb
  have hA := T.anchorVertexAt_of_le (le_max_left na nb) hna
  have hB := T.anchorVertexAt_of_le (le_max_right na nb) hnb
  obtain ⟨va, hva, hposa, htga, hea⟩ := T.exists_src_anchor hu ha.1 hA
  obtain ⟨vb, hvb, hposb, htgb, heb⟩ := T.exists_src_anchor hu hb.1 hB
  obtain ⟨Pc, hPsub, hcS, hcT, heq⟩ :=
    (T.stage (max na nb)).exists_anchor_crosscut_stage hC (T.isConnected_src (max na nb))
      (T.stage (max na nb)).tgt_hasPolygonalArcs hva hvb
      (by rw [hposa, hposb]; exact hab) hea heb
  rw [hposa, hposb] at hcS
  rw [htga, htgb] at hcT
  rw [hposa, hposb, htga, htgb] at heq
  refine ⟨Pc, (T.stage (max na nb)).homeo.toFun '' Pc, hcS, hcT, ?_⟩
  have hFg : Set.EqOn T.toStageSequence.limitTower.F
      (T.stage (max na nb)).homeo.toFun (Pc \ {a, b}) := fun x hx =>
    T.toStageSequence.F_eq_skelHomeo (hPsub hx.1) (Or.inr (hcS.sdiff_subset hx))
  rw [hFg.image_eq, heq]

/-- **`Schoenflies.HasSpokes` for the limit map.** The germ `J` at an anchor `c` is an initial
open subarc of the incident nonboundary edge — the spoke `lem:anchor-density` attaches. Its
points are in the open 1-cell of the spoke, hence in `inside C`; it is small by continuity of
the drawing; `c` is in its closure; and its `F`-image is its `g`-image
(`StageSequence.F_eq_skelHomeo`), which clings to `g c = u c` by continuity of `g` on the
skeleton and the carried identification. -/
theorem hasSpokes (hu : IsHomeoOn u v C modelCurve) :
    HasSpokes C T.anchors u T.toStageSequence.limitTower.F := by
  intro c hc ε hε
  obtain ⟨n, hn⟩ := T.exists_anchorVertexAt_of_mem_anchors hc
  obtain ⟨vc, hvc, hposc, htgc, e, hinc, hout⟩ := T.exists_src_anchor hu hc.1 hn
  obtain ⟨w0, hlink⟩ := hinc
  have he : e ∈ E((T.stage n).str.skel) := hlink.edge_mem
  have hlm : (T.stage n).src.graph.IsLink e ((T.stage n).src.pos vc)
      ((T.stage n).src.pos w0) := Graph.IsLink.map _ hlink
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := (T.stage n).src.isDrawing.edge_isArcBetween hlm
  have hf0c : f 0 = c := by rw [hf0, hposc]
  -- the truncation parameter: small enough for the ball, short of the far endpoint
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hfc 0 zero_mem_I) ε hε
  set t : ℝ := min (δ / 2) 2⁻¹ with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hIsub : Ioo (0 : ℝ) t ⊆ I := fun r hr => ⟨hr.1.le, (hr.2.trans ht1).le⟩
  -- the germ is inside the open 1-cell of the spoke
  have hJcell : f '' Ioo 0 t ⊆ (T.stage n).src.cell e := by
    rintro _ ⟨r, hr, rfl⟩
    have hrI : r ∈ I := hIsub hr
    rw [(T.stage n).src.cell_edge hlink]
    refine ⟨hfim ▸ mem_image_of_mem f hrI, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    push Not
    constructor
    · rw [← hf0]
      exact fun hcon => hr.1.ne' (hfi hrI zero_mem_I hcon)
    · rw [← hf1]
      exact fun hcon => (hr.2.trans ht1).ne (hfi hrI one_mem_I hcon)
  have hJin : f '' Ioo 0 t ⊆ inside C := by
    intro z hz
    have := (T.stage n).src_isWeaklyAdmissible.cell_subset he hout (hJcell hz)
    rwa [union_inside_sdiff] at this
  have hJconn : IsPreconnected (f '' Ioo 0 t) :=
    isPreconnected_Ioo.image f (hfc.mono hIsub)
  have hJball : f '' Ioo 0 t ⊆ ball c ε := by
    rintro _ ⟨r, hr, rfl⟩
    have hrd : dist r 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]
      exact hr.2.trans_le ((min_le_left _ _).trans (by linarith))
    have := hcont (hIsub hr) hrd
    rw [hf0c] at this
    exact mem_ball.2 this
  have hJcl : c ∈ closure (f '' Ioo 0 t) := by
    have h0cl : (0 : ℝ) ∈ closure (Ioo 0 t) := by
      rw [closure_Ioo ht0.ne]
      exact ⟨le_refl 0, ht0.le⟩
    have := ((hfc 0 zero_mem_I).mono hIsub).mem_closure_image h0cl
    rwa [hf0c] at this
  refine ⟨f '' Ioo 0 t, hJin, hJconn, hJball, hJcl, ?_⟩
  -- the image germ: `F` is the stage map on the germ, and the stage map is `u` at `c`
  have hJsk : f '' Ioo 0 t ⊆ (T.stage n).src.skeletonSet :=
    hJcell.trans (Realization.cell_subset_skeletonSet (Or.inr he))
  have hFg : Set.EqOn T.toStageSequence.limitTower.F (T.stage n).homeo.toFun
      (f '' Ioo 0 t) := fun z hz =>
    T.toStageSequence.F_eq_skelHomeo (hJsk hz) (Or.inr (hJin hz))
  rw [hFg.image_eq]
  have hcsk : c ∈ (T.stage n).src.skeletonSet := T.curve_subset_skeletonSet n hc.1
  have hgc : ContinuousWithinAt (T.stage n).homeo.toFun (f '' Ioo 0 t) c :=
    ((T.stage n).homeo.continuousOn_toFun c hcsk).mono hJsk
  have := hgc.mem_closure_image hJcl
  rwa [T.homeo_eqOn_curve n hc.1] at this

/-! ### The interface, exercised -/

/-- **The four conjuncts of `Schoenflies.HasLimitHomeomorphism`, from one anchored stage
tower.** This is `lem:anchor-density` delivered to its consumers: the dense anchor set, the
interior homeomorphism, the anchor crosscuts and the spokes, in exactly the vocabulary of
`BoundaryContinuity2.lean`. -/
theorem hasLimitHomeomorphism_conjuncts (hC : IsJordanCurve C)
    (hu : IsHomeoOn u v C modelCurve) :
    T.anchors ⊆ C ∧ C ⊆ closure T.anchors ∧
      IsHomeoOn T.toStageSequence.limitTower.F T.toStageSequence.limitTower.inv
        (inside C) (Plane.openSquare 0 1) ∧
      HasAnchorCrosscuts C T.anchors u T.toStageSequence.limitTower.F ∧
      HasSpokes C T.anchors u T.toStageSequence.limitTower.F :=
  ⟨T.anchors_subset, T.anchors_dense hu, T.toStageSequence.isHomeoOn_F,
    T.hasAnchorCrosscuts hC hu, T.hasSpokes hu⟩

/-- The body of `Schoenflies.HasLimitHomeomorphism` for one curve and one boundary map, as a
machine-check that the conjuncts above are the right ones. -/
example (hC : IsJordanCurve C) (hu : IsHomeoOn u v C modelCurve) :
    ∃ (𝒜 : Set Plane) (F F' : Plane → Plane), 𝒜 ⊆ C ∧ C ⊆ closure 𝒜 ∧
      IsHomeoOn F F' (inside C) (Plane.openSquare 0 1) ∧
      HasAnchorCrosscuts C 𝒜 u F ∧ HasSpokes C 𝒜 u F :=
  ⟨T.anchors, T.toStageSequence.limitTower.F, T.toStageSequence.limitTower.inv,
    T.hasLimitHomeomorphism_conjuncts hC hu⟩

/-- The anchor-incidence hypothesis of `GeneratedPair.exists_anchor_crosscut_stage`, produced
from the structure: the acceptance test of the ROADMAP's "anchor incidence" row. -/
example (hu : IsHomeoOn u v C modelCurve) {a : Plane} (ha : a ∈ T.anchors) :
    ∃ n, ∃ va ∈ V((T.stage n).str.outerGraph), (T.stage n).src.pos va = a ∧
      ∃ e, (T.stage n).str.skel.Inc e va ∧ e ∉ E((T.stage n).str.outerGraph) := by
  obtain ⟨n, hn⟩ := T.exists_anchorVertexAt_of_mem_anchors ha
  obtain ⟨va, hva, hpos, -, he⟩ := T.exists_src_anchor hu ha.1 hn
  exact ⟨n, va, hva, hpos, he⟩

end AnchoredStageSequence

/-! ### The enriched step data

`Schoenflies.stageSequence` cannot produce an `AnchoredStageSequence`: its mesh steps choose
their fresh points through `Nonempty.some` and `MeshStepData` records nothing about the
choice. This wave's instance of the recurring "one invariant short" finding is that
`MeshStepData` is *four* fields short — the fresh list, its density, the anchor-vertex
invariant at `next`, and one-step persistence — and `GridStepData` is one short (persistence).
The recursion is therefore rebuilt below on the two enriched choosers; every per-step lemma of
`StageRecursion.lean` is reused. -/

/-- **NAMED HYPOTHESIS (data) — one anchored source-grid step.** A `GridStepData` together
with the persistence of anchor vertices across it.

Its discharger is the discharger of `Schoenflies.HasGridSteps` (`GridExtensionData` /
`nonempty_gridExtensionData_of_over`, `GridSteps.lean`) plus one further piece of bookkeeping
the transfer's conclusion does not carry: a grid step's extension `H` meets the boundary
nowhere (`prop:local-grid-attachment` draws the grid strictly inside the window, whose closure
is in `D`), so the common subdivision leaves every outer 0-cell and every nonboundary edge
incident with it in place, subdividing at most the spoke's interior — the sentence of
`lem:anchor-density`'s proof "at all later stages an initial subedge of that spoke remains
incident with it", read across one direction-(a) step. -/
structure AnchoredGridStepData (P : StagePair S₀ C) (ε : ℝ) (b : Plane)
    extends GridStepData P ε b where
  /-- Anchor vertices of the old stage survive the step. -/
  anchor_preserved : ∀ ⦃z⦄, IsAnchorVertexAt P z → IsAnchorVertexAt next z

/-- **NAMED HYPOTHESIS (data) — one anchored target-mesh step.** A `MeshStepData` together
with the anchor bookkeeping of `prop:anchored-square-mesh` clauses 3–4 carried through the
transfer, which `MeshStepData` (deliberately, and now visibly) forgets.

Its discharger is the discharger of `Schoenflies.HasMeshTransfers`
(`Schoenflies.HasMeshOverlays` + `Schoenflies.meshTransfer_of_extension`, `MeshTransfer.lean`)
plus the pieces the transfer's conclusion `IsTransferOfTgt` does not export:

* `fresh`, `fresh_mem_curve`, `fresh_freshDense` — already produced by
  `Schoenflies.exists_fresh_anchor_supply` and recorded in `Schoenflies.MeshTransfer`; they
  merely have to be *kept* (the projection to `MeshStepData` drops them);
* `fresh_anchorAt` — each fresh point is a vertex of the overlay `H` (a spoke endpoint,
  `Schoenflies.squareMesh`), hence a drawn target 0-cell of `next` by the transfer's
  `vertexSet_subset`; its name lies on the outer graph because the common subdivision
  (`GeneratedPair.exists_subdivide_finite_tgt`) inserts it into the outer cycle; and its
  incident nonboundary edge is the spoke, `Schoenflies.squareMesh_inner_edge_at_fresh`
  carried through the ear induction. None of the three clauses is derivable from
  `IsTransferOfTgt` alone — see the module docstring;
* `anchor_preserved` — old anchor vertices are vertices of `H` (the overlay contains the old
  skeleton, `MeshOverlayExtension.vertexSet_subset`), and the spoke of an old anchor is an old
  nonboundary edge, of which an initial subedge survives every subdivision. -/
structure AnchoredMeshStepData (P : StagePair S₀ C) (ε : ℝ) extends MeshStepData P ε where
  /-- The fresh boundary anchors of the mesh. -/
  fresh : List Plane
  /-- They lie on the boundary of the square. -/
  fresh_mem_curve : ∀ z ∈ fresh, z ∈ modelCurve
  /-- They are `ε`-dense along `S`. -/
  fresh_freshDense : FreshDense fresh ε
  /-- Each becomes an anchor vertex of the refined stage. -/
  fresh_anchorAt : ∀ z ∈ fresh, IsAnchorVertexAt next z
  /-- Anchor vertices of the old stage survive the step. -/
  anchor_preserved : ∀ ⦃z⦄, IsAnchorVertexAt P z → IsAnchorVertexAt next z

/-- **NAMED HYPOTHESIS — the anchored source-grid chooser.** `Schoenflies.HasGridSteps` with
persistence of anchor vertices; see `Schoenflies.AnchoredGridStepData` for the discharger. -/
def HasAnchoredGridSteps (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃b : Plane⦄, b ∈ inside C → Nonempty (AnchoredGridStepData P ε b)

/-- **NAMED HYPOTHESIS — the anchored target-mesh chooser.** `Schoenflies.HasMeshSteps` with
the anchor bookkeeping; see `Schoenflies.AnchoredMeshStepData` for the discharger. -/
def HasAnchoredMeshSteps (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → Nonempty (AnchoredMeshStepData P ε)

/-- The anchored grid chooser is in particular the plain one — so any discharge of the
enriched hypothesis also retires `Schoenflies.HasGridSteps`. -/
theorem HasAnchoredGridSteps.hasGridSteps (h : HasAnchoredGridSteps S₀ C) :
    HasGridSteps S₀ C := fun P h1 h2 _ε hε _b hb =>
  (h P h1 h2 hε hb).elim fun d => ⟨d.toGridStepData⟩

omit [Nonempty γ] in
/-- The anchored mesh chooser is in particular the plain one. -/
theorem HasAnchoredMeshSteps.hasMeshSteps (h : HasAnchoredMeshSteps S₀ C) :
    HasMeshSteps S₀ C := fun P h1 h2 _ε hε =>
  (h P h1 h2 hε).elim fun d => ⟨d.toMeshStepData⟩

/-! ### The anchored recursion

`Schoenflies.stageSequence` re-run on the enriched choosers. The definitions and the two
quantitative proofs mirror `StageRecursion.lean` clause for clause — they cannot be reused as
terms, because the original recursion's steps are `Nonempty.some` of the *plain* chooser and
carry no anchor data — but every per-step lemma (`IsRefinementStep.trans`,
`.diam_star_carrier_le`, `diam_tgt_star_le_four`, the window arithmetic) is consumed from
there rather than reproved. -/

section AnchoredRecursion

variable (h₀ : S₀.CombInvariants) (hsep : IsSeparating C)
  (hgrid : HasAnchoredGridSteps S₀ C) (hmesh : HasAnchoredMeshSteps S₀ C)
  (s₀ : AdmissibleStage S₀ C)

/-- The grid half of anchored step `n`. -/
noncomputable def anchoredGridStage (s : AdmissibleStage S₀ C) (n : ℕ) :
    AnchoredGridStepData s.pair (((2 : ℝ) ^ n)⁻¹) (stageCenter hsep n) :=
  (hgrid s.pair s.src_isAdmissible s.tgt_isAdmissible (two_pow_neg_pos n)
    (stageCenter_mem hsep n)).some

/-- The mesh half of anchored step `n`, applied to the output of the grid half. -/
noncomputable def anchoredMeshStage (s : AdmissibleStage S₀ C) (n : ℕ) :
    AnchoredMeshStepData (anchoredGridStage hsep hgrid s n).next (((2 : ℝ) ^ n)⁻¹) :=
  (hmesh (anchoredGridStage hsep hgrid s n).next
    (anchoredGridStage hsep hgrid s n).step.src_isAdmissible
    (anchoredGridStage hsep hgrid s n).step.tgt_isAdmissible (two_pow_neg_pos n)).some

/-- One full anchored recursion step. -/
noncomputable def anchoredNextStage (s : AdmissibleStage S₀ C) (n : ℕ) :
    AdmissibleStage S₀ C :=
  ⟨(anchoredMeshStage hsep hgrid hmesh s n).next,
    (anchoredMeshStage hsep hgrid hmesh s n).step.src_isAdmissible,
    (anchoredMeshStage hsep hgrid hmesh s n).step.tgt_isAdmissible⟩

/-- The parent map of one full anchored step. -/
noncomputable def anchoredStepPar (s : AdmissibleStage S₀ C) (n : ℕ) : γ → γ :=
  (anchoredGridStage hsep hgrid s n).par ∘ (anchoredMeshStage hsep hgrid hmesh s n).par

/-- One full anchored step is a refinement step along the composed parent map. -/
theorem anchoredNextStage_step (s : AdmissibleStage S₀ C) (n : ℕ) :
    IsRefinementStep (anchoredNextStage hsep hgrid hmesh s n).pair s.pair
      (anchoredStepPar hsep hgrid hmesh s n) :=
  (anchoredMeshStage hsep hgrid hmesh s n).step.trans
    (anchoredGridStage hsep hgrid s n).step

include h₀ in
/-- The catch estimate of `StageRecursion.lean`, for the anchored recursion. -/
theorem anchoredNextStage_diam_star_le (s : AdmissibleStage S₀ C) {n : ℕ}
    (hb : recur (TopologicalSpace.denseSeq Plane) n ∈ inside C) {x : Plane}
    (hx : x ∈ openWindow C (((2 : ℝ) ^ n)⁻¹) (recur (TopologicalSpace.denseSeq Plane) n))
    (hxD : x ∈ C ∪ inside C) :
    diam ((anchoredNextStage hsep hgrid hmesh s n).pair.src.star
        ((anchoredNextStage hsep hgrid hmesh s n).pair.src.carrier x)) ≤
      2 * ((2 : ℝ) ^ n)⁻¹ := by
  have hx' : x ∈ openWindow C (((2 : ℝ) ^ n)⁻¹) (stageCenter hsep n) := by
    rwa [stageCenter_eq hsep hb]
  exact le_trans
    ((anchoredMeshStage hsep hgrid hmesh s n).step.diam_star_carrier_le h₀ hsep hxD)
    ((anchoredGridStage hsep hgrid s n).diam_star_le hx')

/-- The stages of the anchored recursion. -/
noncomputable def anchoredStages : ℕ → AdmissibleStage S₀ C
  | 0 => s₀
  | n + 1 => anchoredNextStage hsep hgrid hmesh (anchoredStages n) n

@[simp] theorem anchoredStages_zero : anchoredStages hsep hgrid hmesh s₀ 0 = s₀ := rfl

theorem anchoredStages_succ (n : ℕ) :
    anchoredStages hsep hgrid hmesh s₀ (n + 1) =
      anchoredNextStage hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n := rfl

include h₀ in
/-- Once small, always small, along the anchored stages. -/
theorem diam_anchoredStages_star_anti {x : Plane} (hxD : x ∈ C ∪ inside C) {n m : ℕ}
    (hnm : n ≤ m) :
    diam ((anchoredStages hsep hgrid hmesh s₀ m).pair.src.star
        ((anchoredStages hsep hgrid hmesh s₀ m).pair.src.carrier x)) ≤
      diam ((anchoredStages hsep hgrid hmesh s₀ n).pair.src.star
        ((anchoredStages hsep hgrid hmesh s₀ n).pair.src.carrier x)) := by
  induction hnm with
  | refl => exact le_rfl
  | step _ ih =>
    exact le_trans
      ((anchoredNextStage_step hsep hgrid hmesh _ _).diam_star_carrier_le h₀ hsep hxD) ih

/-- **The anchored recursion, assembled.** `Schoenflies.stageSequence` re-proved over the
enriched choosers, together with the anchor fields of `Schoenflies.AnchoredStageSequence`:
the fresh lists are those the mesh steps chose, their invariants are the choosers' clauses,
the boundary identification at the base is the hypothesis `hbase` (for the concrete base it is
`InitialData.skeletonHomeo_eq_u`), and per-stage admissibility is read off the recursion. -/
noncomputable def anchoredStageSequence {u : Plane → Plane}
    (hbase : Set.EqOn s₀.pair.homeo.toFun u C) :
    AnchoredStageSequence γ S₀ C u where
  stage n := (anchoredStages hsep hgrid hmesh s₀ n).pair
  par n := anchoredStepPar hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n
  refines_src n :=
    (anchoredNextStage_step hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n).refines_src
  refines_tgt n :=
    (anchoredNextStage_step hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n).refines_tgt
  skeletonSet_mono n :=
    (anchoredNextStage_step hsep hgrid hmesh
      (anchoredStages hsep hgrid hmesh s₀ n) n).skeletonSet_subset
  skelHomeo_succ n :=
    (anchoredNextStage_step hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n).homeo_eqOn
  eps n := 4 * ((2 : ℝ) ^ n)⁻¹
  diam_tgtStar_le := by
    intro n τ hτ
    cases n with
    | zero => simpa using diam_tgt_star_le_four h₀ s₀.pair τ
    | succ n =>
      have hM := (anchoredMeshStage hsep hgrid hmesh
        (anchoredStages hsep hgrid hmesh s₀ n) n).diam_closure_cell_le
      have hb := (anchoredStages hsep hgrid hmesh s₀
          (n + 1)).pair.tgt_isCellDecomposition.diam_star_le
        ((anchoredStages hsep hgrid hmesh s₀ (n + 1)).pair.combInvariants h₀)
        (Plane.isBounded_closedSquare 0 1) hτ (fun F hF _ => hM hF)
      calc diam ((anchoredStages hsep hgrid hmesh s₀ (n + 1)).pair.tgt.star τ)
          ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := hb
        _ = 4 * ((2 : ℝ) ^ (n + 1))⁻¹ := by rw [pow_succ, mul_inv]; ring
  tendsto_eps := by
    have h := tendsto_two_pow_neg.const_mul (4 : ℝ)
    simpa using h
  tendsto_diam_srcStar := by
    intro x hx
    have hxD : x ∈ C ∪ inside C := Or.inr hx
    have hCcpt : IsCompact C := hsep.isJordanCurve.isCompact
    have hCne : C.Nonempty := hsep.isJordanCurve.nonempty
    have hxC : x ∉ C := fun h => inside_subset_compl hx h
    have hd : 0 < supRadius C x := supRadius_pos hCcpt hCne hxC
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨b, hbB, hbU, hbx⟩ := exists_mem_rat_supDist_lt
      (TopologicalSpace.denseRange_denseSeq Plane) hsep.isOpen_inside hx
      (by linarith : 0 < supRadius C x / 8)
    obtain ⟨k, hk⟩ := hbB
    have hmin : 0 < min (supRadius C x / 8) (ε / 4) := lt_min (by linarith) (by linarith)
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.1 (tendsto_two_pow_neg.eventually_lt_const hmin)
    obtain ⟨n, hnN, hrec⟩ := exists_le_recur_eq (TopologicalSpace.denseSeq Plane) k N
    have hb' : recur (TopologicalSpace.denseSeq Plane) n ∈ inside C := by
      rw [hrec, hk]; exact hbU
    have hxw : x ∈ openWindow C (((2 : ℝ) ^ n)⁻¹)
        (recur (TopologicalSpace.denseSeq Plane) n) := by
      rw [hrec, hk]
      exact mem_openWindow_of_supDist_lt hCcpt hCne hbx
        (lt_of_lt_of_le (hN n hnN) (min_le_left _ _))
    have hcatch := anchoredNextStage_diam_star_le h₀ hsep hgrid hmesh
      (anchoredStages hsep hgrid hmesh s₀ n) hb' hxw hxD
    refine ⟨n + 1, fun m hm => ?_⟩
    have hmono := diam_anchoredStages_star_anti h₀ hsep hgrid hmesh s₀ hxD hm
    have hlt : 2 * ((2 : ℝ) ^ n)⁻¹ < ε := by
      have := lt_of_lt_of_le (hN n hnN) (min_le_right _ _)
      linarith
    have hnonneg : (0 : ℝ) ≤
        diam ((anchoredStages hsep hgrid hmesh s₀ m).pair.src.star
          ((anchoredStages hsep hgrid hmesh s₀ m).pair.src.carrier x)) := diam_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt (le_trans hmono hcatch) hlt
  base := h₀
  isSeparating := hsep
  fresh n := (anchoredMeshStage hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n).fresh
  fresh_mem_curve n :=
    (anchoredMeshStage hsep hgrid hmesh (anchoredStages hsep hgrid hmesh s₀ n) n).fresh_mem_curve
  freshDense n :=
    (anchoredMeshStage hsep hgrid hmesh
      (anchoredStages hsep hgrid hmesh s₀ n) n).fresh_freshDense.mono
      (by nlinarith [two_pow_neg_pos n] : ((2 : ℝ) ^ n)⁻¹ ≤ 4 * ((2 : ℝ) ^ n)⁻¹)
  fresh_anchorAt n z hz :=
    (anchoredMeshStage hsep hgrid hmesh
      (anchoredStages hsep hgrid hmesh s₀ n) n).fresh_anchorAt z hz
  anchorAt_succ n z h :=
    (anchoredMeshStage hsep hgrid hmesh
      (anchoredStages hsep hgrid hmesh s₀ n) n).anchor_preserved
      ((anchoredGridStage hsep hgrid (anchoredStages hsep hgrid hmesh s₀ n) n).anchor_preserved h)
  homeo_eq_u := hbase
  isConnected_src n :=
    (anchoredStages hsep hgrid hmesh s₀ n).src_isAdmissible.isConnected_nonboundary

end AnchoredRecursion

/-! ### The concrete base, and the interface exercised -/

/-- `Schoenflies.IsSetHomeoOn` (the shape `InitialData.homeo` carries) is
`Schoenflies.IsHomeoOn` (the shape `BoundaryContinuity2.lean` consumes). The two structures
record the same six facts. -/
theorem IsSetHomeoOn.isHomeoOn {f g : Plane → Plane} {X Y : Set Plane}
    (h : IsSetHomeoOn f g X Y) : IsHomeoOn f g X Y :=
  ⟨h.mapsTo, h.mapsTo_inv, h.continuousOn, h.continuousOn_inv, ⟨h.leftInvOn, h.rightInvOn⟩⟩

/-- **The anchored Phase 3 deliverable over the concrete base.** From an initial pair `d` and
the two anchored choosers, the anchored stage tower for the boundary map `d.u`, launched at
`InitialData.generatedPair` with `InitialData.skeletonHomeo_eq_u` as the carried clause 2 of
`def:matched-pair`. -/
noncomputable def anchoredStageSequence_of_initialData {C : Set Plane} (hC : IsJordanCurve C)
    (hgrid : HasAnchoredGridSteps initialStructure C)
    (hmesh : HasAnchoredMeshSteps initialStructure C) (d : InitialData C) :
    AnchoredStageSequence InitialCell initialStructure C d.u :=
  anchoredStageSequence combInvariants_initialStructure (jordan_curve_theorem hC) hgrid hmesh
    ⟨d.generatedPair, d.generatedPair_src_isAdmissible, d.generatedPair_tgt_isAdmissible⟩
    (fun _x hx => d.skeletonHomeo_eq_u hx)

/-- **The composition, machine-checked**: over the concrete base, the two anchored choosers
produce the full body of `Schoenflies.HasLimitHomeomorphism` for the curve `C` and the
boundary map of the initial pair — all four conjuncts, `lem:anchor-density` included. What
still separates this from `HasLimitHomeomorphism` itself is only that the boundary map is
`d.u` rather than an arbitrarily prescribed one; see the module docstring. -/
example {C : Set Plane} (hC : IsJordanCurve C)
    (hgrid : HasAnchoredGridSteps initialStructure C)
    (hmesh : HasAnchoredMeshSteps initialStructure C) (d : InitialData C) :
    ∃ (𝒜 : Set Plane) (F F' : Plane → Plane), 𝒜 ⊆ C ∧ C ⊆ closure 𝒜 ∧
      IsHomeoOn F F' (inside C) (Plane.openSquare 0 1) ∧
      HasAnchorCrosscuts C 𝒜 d.u F ∧ HasSpokes C 𝒜 d.u F := by
  have T := anchoredStageSequence_of_initialData hC hgrid hmesh d
  exact ⟨T.anchors, T.toStageSequence.limitTower.F, T.toStageSequence.limitTower.inv,
    T.hasLimitHomeomorphism_conjuncts hC d.homeo.isHomeoOn⟩

end Schoenflies
