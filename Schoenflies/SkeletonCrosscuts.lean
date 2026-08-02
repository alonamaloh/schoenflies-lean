/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransfer
import Schoenflies.BoundaryContinuity2
import Schoenflies.StageCells

/-!
# `lem:skeleton-crosscuts` for an admissible realization

`Graph.IsStageOn.exists_crosscut` (`Schoenflies/BoundaryContinuity.lean`) proves the first
clause of `lem:skeleton-crosscuts` for one finite plane graph presented as a raw
`Graph.IsStageOn`. What no module supplied is the passage from the objects the construction
actually produces — an admissible realization of a cell structure
(`Schoenflies/FiniteTransfer.lean`), or the source side of a `Schoenflies.GeneratedPair` — to
that raw presentation. This module is that passage, together with the transport of the crosscut
through the skeleton homeomorphism (the second clause), on one named hypothesis.

## The bridge

`Realization.IsAdmissible.isStageOn` shows that an admissible realization *is* a stage in the
sense of `Graph.IsStageOn`, over the open domain `dom \ outer`. Each clause of `IsStageOn` is
one clause of `def:admissible-graph`, with two translations paid for here once:

* the drawn notion `Graph.Nonboundary` (the arc is not contained in the outer curve) versus the
  combinatorial notion `e ∉ E(S.outerGraph)`. They agree for a weakly admissible realization:
  an outer edge is drawn inside the realized outer cycle
  (`Realization.edgeArc_subset_outerSet`), and a non-outer edge has its open cell — which is
  nonempty, because an arc is more than its two endpoints — inside `dom \ outer`
  (`IsWeaklyAdmissible.nonboundary_of_notMem_outerGraph`);
* `edge_split` versus `cell_subset`: the open cell of a 1-cell is exactly the drawn arc minus
  its two ends, which is the shape `IsStageOn` speaks in.

`Realization.IsAdmissible.exists_crosscut` then reads `lem:skeleton-crosscuts`, clause 1, off
`Graph.IsStageOn.exists_crosscut`: two distinct drawn 0-cells on the outer curve, each incident
with a combinatorially nonboundary edge, are joined by a simple polygonal crosscut running
through the stage's skeleton. The incidence hypothesis is the one clause of
`lem:anchor-density` this statement consumes, and `lem:anchor-density` is open; the hypothesis
is stated combinatorially (`∃ e, S.skel.Inc e va ∧ e ∉ E(S.outerGraph)`) because that is the
form a stage construction has it in.

## The transport, and the one named hypothesis

`SkeletonHomeo.isCrosscut_image` is clause 2: the skeleton homeomorphism carries the source
crosscut to a crosscut of the target curve between the corresponding drawn 0-cells, with the
endpoint bookkeeping `g '' (P \ {a, b}) = g '' P \ {g a, g b}` that
`Schoenflies.HasAnchorCrosscuts` asks for. Everything is unconditional except one clause:

* **`Realization.HasPolygonalArcs`** — *every arc contained in the realized skeleton is
  polygonal*. This is the blueprint's sentence "the path uses finitely many subarcs of target
  edges, all of which are polygonal; hence `P'` is polygonal", and it is not on `main`. It is a
  true statement about any realization all of whose edges are polygonal (the target side of a
  `GeneratedPair` qualifies, by `GeneratedPair.tgt_isPolygonal`): the arc passes each drawn
  vertex at most once, so it decomposes into finitely many subarcs each inside one polygonal
  edge arc, and a subarc of a polygonal arc is polygonal. A later module can discharge it from
  exactly those two facts; neither exists yet.

`GeneratedPair.exists_anchor_crosscut` assembles the two clauses for the source side of a
generated pair, and `GeneratedPair.exists_anchor_crosscut_stage` instantiates the concrete
domains of a `Schoenflies.StageSequence` stage (the closed Jordan domain and the closed
square), discharging every side condition. Its conclusion is the triple
`Schoenflies.HasAnchorCrosscuts` wants, stated against the *skeleton homeomorphism* `g` of the
stage rather than against the limit map `F` and the boundary map `u`: a consumer holding
`prop:skeleton-agreement` (`StageSequence.F_eq_skelHomeo`) and the identification
`u (src anchor) = tgt drawn anchor` (clause 2 of `def:matched-pair`, deliberately not recorded
in `SkeletonHomeo`) finishes with `EqOn.image_eq` and nothing else.

## Blueprint

* `Schoenflies.CellStructure.Realization.IsAdmissible.isStageOn` — `def:admissible-graph`
  presented as the stage of `lem:skeleton-crosscuts`.
* `Schoenflies.CellStructure.Realization.IsAdmissible.exists_crosscut`,
  `…IsAdmissible.exists_isCrosscut` — `lem:skeleton-crosscuts`, clause 1, for an admissible
  realization.
* `Schoenflies.CellStructure.Realization.HasPolygonalArcs` — the named polygonality hypothesis;
  the sentence "the path uses finitely many subarcs of target edges, all of which are
  polygonal" of the proof of `lem:skeleton-crosscuts`.
* `Schoenflies.CellStructure.SkeletonHomeo.isCrosscut_image` — `lem:skeleton-crosscuts`,
  clause 2: the target crosscut.
* `Schoenflies.GeneratedPair.exists_anchor_crosscut`,
  `Schoenflies.GeneratedPair.exists_anchor_crosscut_stage` — both clauses assembled for a
  generated matched cellulation, in the shape `Schoenflies.HasAnchorCrosscuts` consumes.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

namespace Realization

variable {R : S.Realization} {outer dom : Set Plane}

/-- An outer edge is drawn inside the realized outer cycle: its arc is part of the point set of
the drawn outer subgraph. -/
theorem edgeArc_subset_outerSet (R : S.Realization) {e : γ} (he : e ∈ E(S.outerGraph)) :
    Graph.edgeArc R.drawing e ⊆ R.outerSet :=
  Graph.edgeArc_subset_pointSet (by rwa [Graph.edgeSet_map])

/-- A 0-cell of the outer cycle is drawn on the realized outer cycle. -/
theorem pos_mem_outerSet (R : S.Realization) {v : γ} (hv : v ∈ V(S.outerGraph)) :
    R.pos v ∈ R.outerSet :=
  Graph.vertexSet_subset_pointSet (by rw [Graph.vertexSet_map]; exact ⟨v, hv, rfl⟩)

/-- **A combinatorially nonboundary edge is drawn off the outer curve.** Its open cell is
nonempty — an arc is more than its two endpoints — and lies in `dom \ outer`, so the arc cannot
be contained in `outer`. This is the forward half of the translation between
`def:admissible-graph`'s combinatorial reading and `Graph.IsStageOn`'s drawn one. -/
theorem IsWeaklyAdmissible.nonboundary_of_notMem_outerGraph
    (hadm : R.IsWeaklyAdmissible outer dom) {e : γ} (he : e ∈ E(S.skel))
    (hout : e ∉ E(S.outerGraph)) : Graph.Nonboundary R.drawing outer e := by
  intro hsub
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have hdraw : Graph.IsDrawing R.graph R.drawing := R.isDrawing
  have hlm : R.graph.IsLink e (R.pos x) (R.pos y) := Graph.IsLink.map _ hl
  obtain ⟨z, hze, hzxy⟩ := not_subset.1 (hdraw.edge_isArcBetween hlm).not_subset_pair
  have hzcell : z ∈ R.cell e := by rw [R.cell_edge hl]; exact ⟨hze, hzxy⟩
  exact (hadm.cell_subset he hout hzcell).2 (hsub hze)

/-- The converse half of the translation: an edge drawn off the outer curve is not an outer
edge, since outer edges are drawn inside the realized outer cycle. -/
theorem IsWeaklyAdmissible.notMem_outerGraph_of_nonboundary
    (hadm : R.IsWeaklyAdmissible outer dom) {e : γ}
    (hnb : Graph.Nonboundary R.drawing outer e) : e ∉ E(S.outerGraph) := fun hout =>
  hnb (by rw [← hadm.outerSet_eq]; exact R.edgeArc_subset_outerSet hout)

/-- The open nonboundary part of a weakly admissible realization lies in the open domain. -/
theorem IsWeaklyAdmissible.nonboundary_subset (hadm : R.IsWeaklyAdmissible outer dom) :
    R.nonboundary ⊆ dom \ outer := by
  rw [Realization.nonboundary, hadm.outerSet_eq]
  exact fun z hz => ⟨hadm.skeletonSet_subset hz.1, hz.2⟩

/-- **An admissible realization is a stage.** Each clause of `def:admissible-graph` becomes the
corresponding clause of `Graph.IsStageOn` over the open domain `dom \ outer`; the two
translations — combinatorial versus drawn nonboundariness, and open cells versus arcs minus
ends — are the two lemmas above. -/
theorem IsAdmissible.isStageOn (hadm : R.IsAdmissible outer dom) :
    Graph.IsStageOn R.graph R.drawing outer (dom \ outer) where
  isDrawing := R.isDrawing
  polygonal := by
    intro e he hnb
    rw [Realization.edgeSet_graph] at he
    exact hadm.isPolygonal he
      (hadm.toIsWeaklyAdmissible.notMem_outerGraph_of_nonboundary hnb)
  disjoint := disjoint_sdiff_self_right
  vertex_mem := fun v hv hvC =>
    ⟨hadm.skeletonSet_subset (Graph.vertexSet_subset_pointSet hv), hvC⟩
  edge_split := by
    intro e x y hl
    have he : e ∈ E(S.skel) := by
      have h := hl.edge_mem
      rwa [Realization.edgeSet_graph] at h
    by_cases hout : e ∈ E(S.outerGraph)
    · refine Or.inl ?_
      rw [← hadm.outerSet_eq]
      exact R.edgeArc_subset_outerSet hout
    · -- off the outer cycle the edge's interior is its open cell, which admissibility places
      refine Or.inr ?_
      have hl' : (S.skel.map R.pos).IsLink e x y := hl
      obtain ⟨x', y', hl'', rfl, rfl⟩ := hl'
      have hcell := hadm.cell_subset he hout
      rw [R.cell_edge hl''] at hcell
      exact hcell
  isConnected_diff := by
    have h := hadm.isConnected_nonboundary
    rw [Realization.nonboundary, hadm.outerSet_eq] at h
    exact h

/-- **`lem:skeleton-crosscuts`, clause 1, for an admissible realization.** Two distinct drawn
0-cells on the outer curve, each incident with a combinatorially nonboundary edge — the clause
`lem:anchor-density` attaches to an anchor — are joined by a simple polygonal crosscut running
through the realized skeleton: it meets `outer` exactly at its two ends, and everything else
lies in the open domain. -/
theorem IsAdmissible.exists_crosscut (hadm : R.IsAdmissible outer dom) {va vb : γ}
    (hab : R.pos va ≠ R.pos vb) (haC : R.pos va ∈ outer) (hbC : R.pos vb ∈ outer)
    (hea : ∃ e, S.skel.Inc e va ∧ e ∉ E(S.outerGraph))
    (heb : ∃ e, S.skel.Inc e vb ∧ e ∉ E(S.outerGraph)) :
    ∃ P ⊆ R.skeletonSet, IsPolygonal P ∧ IsArcBetween P (R.pos va) (R.pos vb) ∧
      P ∩ outer = {R.pos va, R.pos vb} ∧ P \ {R.pos va, R.pos vb} ⊆ dom \ outer := by
  have hconv : ∀ v : γ, (∃ e, S.skel.Inc e v ∧ e ∉ E(S.outerGraph)) →
      ∃ e, R.graph.Inc e (R.pos v) ∧ Graph.Nonboundary R.drawing outer e := by
    rintro v ⟨e, ⟨w, hl⟩, hout⟩
    have hlm : R.graph.IsLink e (R.pos v) (R.pos w) := Graph.IsLink.map _ hl
    exact ⟨e, ⟨R.pos w, hlm⟩,
      hadm.toIsWeaklyAdmissible.nonboundary_of_notMem_outerGraph hl.edge_mem hout⟩
  exact hadm.isStageOn.exists_crosscut hab haC hbC (hconv va hea) (hconv vb heb)

/-- `Realization.IsAdmissible.exists_crosscut` packaged as a `Schoenflies.IsCrosscut`, the form
`thm:general-crosscut` and `Schoenflies.HasAnchorCrosscuts` consume. The identification of the
open domain with the Jordan domain, `dom \ outer ⊆ inside outer`, is an equality at the
concrete instantiation (`Schoenflies.sdiff_outer_eq_inside`). -/
theorem IsAdmissible.exists_isCrosscut (hadm : R.IsAdmissible outer dom)
    (hC : IsJordanCurve outer) (hins : dom \ outer ⊆ inside outer) {va vb : γ}
    (hab : R.pos va ≠ R.pos vb) (haC : R.pos va ∈ outer) (hbC : R.pos vb ∈ outer)
    (hea : ∃ e, S.skel.Inc e va ∧ e ∉ E(S.outerGraph))
    (heb : ∃ e, S.skel.Inc e vb ∧ e ∉ E(S.outerGraph)) :
    ∃ P ⊆ R.skeletonSet, IsCrosscut outer P (R.pos va) (R.pos vb) ∧
      P ∩ outer = {R.pos va, R.pos vb} := by
  obtain ⟨P, hPsub, hpoly, harc, hcut, hint⟩ := hadm.exists_crosscut hab haC hbC hea heb
  exact ⟨P, hPsub, ⟨hC, harc, hpoly, haC, hbC, fun z hz => hins (hint hz)⟩, hcut⟩

/-- **NAMED HYPOTHESIS — every arc contained in the realized skeleton is polygonal.**

This is the sentence of the proof of `lem:skeleton-crosscuts` that transports polygonality:
*"the path uses finitely many subarcs of target edges, all of which are polygonal; hence `P'`
is polygonal."* Nothing on `main` proves it.

It is a true statement about any realization all of whose edge arcs are polygonal — the target
side of a `Schoenflies.GeneratedPair` qualifies, by `GeneratedPair.tgt_isPolygonal` — and a
later module can discharge it from two facts, neither of which exists yet: an arc in the point
set of a finite plane graph passes each drawn vertex at most once and therefore decomposes into
finitely many subarcs each contained in one edge arc; and a subarc of a polygonal arc is
polygonal. -/
def HasPolygonalArcs (R : S.Realization) : Prop :=
  ∀ ⦃Q : Set Plane⦄, Q ⊆ R.skeletonSet → IsArc Q → IsPolygonal Q

end Realization

namespace SkeletonHomeo

variable {R₁ R₂ : S.Realization} {outer' dom' : Set Plane}

/-- **`lem:skeleton-crosscuts`, clause 2: the transported crosscut.** The skeleton
homeomorphism carries a crosscut of the source stage to a crosscut of the target curve between
the corresponding drawn 0-cells, together with the endpoint bookkeeping
`g '' (P \ {a, b}) = g '' P \ {g a, g b}` that `Schoenflies.HasAnchorCrosscuts` asks for.

Polygonality of the image is the one genuinely missing ingredient and is taken as the
hypothesis `hpoly'`; `Realization.HasPolygonalArcs` on the target realization supplies it, and
`GeneratedPair.exists_anchor_crosscut` below does exactly that. -/
theorem isCrosscut_image (g : SkeletonHomeo R₁ R₂)
    (htgt : R₂.IsWeaklyAdmissible outer' dom')
    (hC' : IsJordanCurve outer') (hins' : dom' \ outer' ⊆ inside outer')
    {P : Set Plane} {va vb : γ} (hva : va ∈ V(S.outerGraph)) (hvb : vb ∈ V(S.outerGraph))
    (hPsk : P ⊆ R₁.skeletonSet) (harc : IsArcBetween P (R₁.pos va) (R₁.pos vb))
    (hmeet : P ∩ R₁.outerSet ⊆ {R₁.pos va, R₁.pos vb})
    (hpoly' : IsPolygonal (g.toFun '' P)) :
    IsCrosscut outer' (g.toFun '' P) (R₂.pos va) (R₂.pos vb) ∧
      g.toFun '' (P \ {R₁.pos va, R₁.pos vb}) =
        g.toFun '' P \ {R₂.pos va, R₂.pos vb} := by
  have hva' : va ∈ V(S.skel) := S.outerGraph_le.vertexSet_mono hva
  have hvb' : vb ∈ V(S.skel) := S.outerGraph_le.vertexSet_mono hvb
  have hga : g.toFun (R₁.pos va) = R₂.pos va := g.pos_apply hva'
  have hgb : g.toFun (R₁.pos vb) = R₂.pos vb := g.pos_apply hvb'
  -- the image is an arc between the corresponding drawn 0-cells
  have harc' := harc.image_of_injOn hPsk g.continuousOn_toFun g.injOn
  rw [hga, hgb] at harc'
  -- the endpoint bookkeeping, from injectivity alone
  have heq := image_sdiff_eq_of_eqOn (F := g.toFun) hPsk g.injOn harc.left_mem
    harc.right_mem (fun z _ => rfl)
  rw [hga, hgb] at heq
  -- off its two ends the crosscut is nonboundary, and the homeomorphism keeps it so
  have hPnb : P \ {R₁.pos va, R₁.pos vb} ⊆ R₁.nonboundary := by
    rintro z ⟨hzP, hzab⟩
    exact ⟨hPsk hzP, fun hzo => hzab (hmeet ⟨hzP, hzo⟩)⟩
  have hint : g.toFun '' (P \ {R₁.pos va, R₁.pos vb}) ⊆ inside outer' := by
    have h1 : g.toFun '' (P \ {R₁.pos va, R₁.pos vb}) ⊆ R₂.nonboundary := by
      rw [← g.image_nonboundary]
      exact image_mono hPnb
    exact h1.trans (htgt.nonboundary_subset.trans hins')
  refine ⟨⟨hC', harc', hpoly', ?_, ?_, ?_⟩, heq⟩
  · rw [← htgt.outerSet_eq]; exact R₂.pos_mem_outerSet hva
  · rw [← htgt.outerSet_eq]; exact R₂.pos_mem_outerSet hvb
  · rw [← heq]; exact hint

end SkeletonHomeo

end CellStructure

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

namespace GeneratedPair

open CellStructure

/-- **`lem:skeleton-crosscuts` for a generated matched cellulation.** Two distinct anchors —
drawn 0-cells of the stage lying on the outer cycle, each incident with a nonboundary edge —
are joined by a polygonal crosscut of the source domain running through the source skeleton,
and the skeleton homeomorphism carries it to a polygonal crosscut of the target domain between
the corresponding target 0-cells, with the endpoint bookkeeping displayed.

Connectedness of the open nonboundary part (`hconn`) is what upgrades the bundled weak
admissibility to admissibility, per `rem:intermediate-disconnection` a property of a *finished*
stage only. `hpoly` is the named hypothesis `Realization.HasPolygonalArcs`; see its docstring.

The conclusion is the triple of `Schoenflies.HasAnchorCrosscuts`, stated against the stage's
skeleton homeomorphism rather than the limit map: a consumer holding `prop:skeleton-agreement`
(`Schoenflies.StageSequence.F_eq_skelHomeo`) and the boundary identification
`u (P.src.pos v) = P.tgt.pos v` of `def:matched-pair` finishes with `Set.EqOn.image_eq`. -/
theorem exists_anchor_crosscut (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hconn : IsConnected P.src.nonboundary)
    (hCsrc : IsJordanCurve srcOuter) (hins : srcDom \ srcOuter ⊆ inside srcOuter)
    (hCtgt : IsJordanCurve tgtOuter) (hins' : tgtDom \ tgtOuter ⊆ inside tgtOuter)
    (hpoly : P.tgt.HasPolygonalArcs)
    {va vb : γ} (hva : va ∈ V(P.str.outerGraph)) (hvb : vb ∈ V(P.str.outerGraph))
    (hab : P.src.pos va ≠ P.src.pos vb)
    (hea : ∃ e, P.str.skel.Inc e va ∧ e ∉ E(P.str.outerGraph))
    (heb : ∃ e, P.str.skel.Inc e vb ∧ e ∉ E(P.str.outerGraph)) :
    ∃ Pc ⊆ P.src.skeletonSet,
      IsCrosscut srcOuter Pc (P.src.pos va) (P.src.pos vb) ∧
        IsCrosscut tgtOuter (P.homeo.toFun '' Pc) (P.tgt.pos va) (P.tgt.pos vb) ∧
        P.homeo.toFun '' (Pc \ {P.src.pos va, P.src.pos vb}) =
          P.homeo.toFun '' Pc \ {P.tgt.pos va, P.tgt.pos vb} := by
  have hadm := P.src_isAdmissible hconn
  have haC : P.src.pos va ∈ srcOuter := hadm.outerSet_eq.subset (P.src.pos_mem_outerSet hva)
  have hbC : P.src.pos vb ∈ srcOuter := hadm.outerSet_eq.subset (P.src.pos_mem_outerSet hvb)
  obtain ⟨Pc, hPsub, hPpoly, hParc, hPcut, hPint⟩ :=
    hadm.exists_crosscut hab haC hbC hea heb
  -- the image is an arc in the target skeleton, hence polygonal by the named hypothesis
  have harc' := hParc.image_of_injOn hPsub P.homeo.continuousOn_toFun P.homeo.injOn
  have himg : P.homeo.toFun '' Pc ⊆ P.tgt.skeletonSet := by
    rw [← P.homeo.image_skeletonSet]
    exact image_mono hPsub
  have hpoly' : IsPolygonal (P.homeo.toFun '' Pc) := hpoly himg harc'.isArc
  have hmeet : Pc ∩ P.src.outerSet ⊆ {P.src.pos va, P.src.pos vb} := by
    rw [hadm.outerSet_eq]
    exact hPcut.subset
  obtain ⟨hcross', heq⟩ := P.homeo.isCrosscut_image P.tgt_isWeaklyAdmissible hCtgt hins'
    hva hvb hPsub hParc hmeet hpoly'
  exact ⟨Pc, hPsub, ⟨hCsrc, hParc, hPpoly, haC, hbC, fun z hz => hins (hPint hz)⟩,
    hcross', heq⟩

/-- `GeneratedPair.exists_anchor_crosscut` at the concrete domains of a stage sequence — the
closed Jordan domain of `C` and the closed unit square — with every side condition discharged:
`thm:jordan` identifies the open source domain with `inside C`, and the model-curve lemmas
identify the open square with `inside modelCurve`. -/
theorem exists_anchor_crosscut_stage {C : Set Plane}
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
    (hC : IsJordanCurve C) (hconn : IsConnected P.src.nonboundary)
    (hpoly : P.tgt.HasPolygonalArcs)
    {va vb : γ} (hva : va ∈ V(P.str.outerGraph)) (hvb : vb ∈ V(P.str.outerGraph))
    (hab : P.src.pos va ≠ P.src.pos vb)
    (hea : ∃ e, P.str.skel.Inc e va ∧ e ∉ E(P.str.outerGraph))
    (heb : ∃ e, P.str.skel.Inc e vb ∧ e ∉ E(P.str.outerGraph)) :
    ∃ Pc ⊆ P.src.skeletonSet,
      IsCrosscut C Pc (P.src.pos va) (P.src.pos vb) ∧
        IsCrosscut modelCurve (P.homeo.toFun '' Pc) (P.tgt.pos va) (P.tgt.pos vb) ∧
        P.homeo.toFun '' (Pc \ {P.src.pos va, P.src.pos vb}) =
          P.homeo.toFun '' Pc \ {P.tgt.pos va, P.tgt.pos vb} :=
  P.exists_anchor_crosscut hconn hC
    (sdiff_outer_eq_inside (jordan_curve_theorem hC)).subset
    isJordanCurve_modelCurve
    (closedSquare_sdiff_modelCurve.trans inside_modelCurve.symm).subset
    hpoly hva hvb hab hea heb

end GeneratedPair

end Schoenflies
