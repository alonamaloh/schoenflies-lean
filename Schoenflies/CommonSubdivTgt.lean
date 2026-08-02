/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CommonSubdiv

/-!
# Step 1 of `thm:finite-transfer`(b): the same, driven from the target side

Direction (b) transfers a refinement of `Γ'` back to the source. Its step 1 is the same
statement as direction (a)'s with the two realizations exchanged, and — this is the point of the
module — most of the machinery does not have to be rewritten to say so.

**`Schoenflies.IsSourceExtension` is direction-agnostic.** It is stated for an arbitrary
realization `R`, not for `P.src`, so the hypotheses `thm:finite-transfer`(b) puts on `H'` — a
finite 2-connected plane graph containing a subdivision of `Γ'`, drawn in the closed target
domain, with outer cycle `S`, and with `|H'| ∖ S` connected — are
`IsSourceExtension P.tgt tgtOuter tgtDom H' H'draw`. The name is now slightly wrong and the
structure is not; renaming it would touch every consumer and is left to the integrator.

The extra hypotheses of (b) — *every new nonboundary edge meeting `S` has exactly one endpoint
on `S`, that endpoint is a fresh point `u(a)` with `a ∈ 𝒜`, and exactly one new nonboundary edge
is incident with each such fresh point* — are **not** used by step 1. They are what the ear step
needs, in the one case where the source endpoint sits on the wild curve and
`lem:polygonal-side-accessibility` says nothing; `Schoenflies/FreshAccess.lean` is that case.

So `Schoenflies.sourcePart P.tgt H' H'draw` is the subgraph, `sourcePart_le` and
`pointSet_sourcePart` are two of the three clauses verbatim, and what this module adds is the
target-driven versions of the three things that do mention a side: the transfer invariant, the
edge matching, and the assembly.

## Blueprint

* `Schoenflies.IsPartialTransferOfTgt`, `Schoenflies.CommonSubdivisionTgt` — the invariant and
  step 1 of `thm:finite-transfer`(b).
* `Schoenflies.commonSubdivisionTgt` — step 1 of `thm:finite-transfer`(b), unconditional.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph CellStructure

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-! ### The invariant, driven from the target -/

/-- **An intermediate stage of the transfer, direction (b).** The mirror of
`Schoenflies.IsPartialTransferOf`: the parent map is still shared by the two realizations —
that is `lem:refinement-compatibility`(c) and it has no direction — but it is now the *target*
skeleton that is pinned to the current subgraph of the extension. -/
structure IsPartialTransferOfTgt (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the old one along `par`. -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the old one along the *same* parent map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The new target skeleton occupies exactly what the current subgraph occupies. -/
  skeletonSet_eq : T.tgt.skeletonSet = pointSet B Hdraw
  /-- Every vertex of the current subgraph is a 0-cell of the new structure. -/
  vertexSet_subset : V(B) ⊆ V(T.tgt.graph)
  /-- **The combinatorial paragraph of the proof.** A 0-cell whose ancestor in the base pair is an
  outer edge — a *fresh point* `u(a)`, inserted into the outer cycle by the common subdivision —
  is incident with at most one 2-cell, as long as the current subgraph still has no nonboundary
  edge there.

  Both conditions are needed and neither is decoration. Without the first the clause would have to
  hold at an old 0-cell of the outer cycle, which is a different statement, about the base pair.
  Without the second it is *false* from the moment the ear at `u(a)` is inserted, since an ear
  ending at a 0-cell puts it on both new boundary paths and leaves both descendants incident with
  it. What makes the pair work is that the two move together: the ear at `u(a)` is the *unique*
  new nonboundary edge there — the second sentence of `thm:finite-transfer`(b) — so the clause
  survives exactly as long as `Schoenflies.EarStepTgt` needs it and no longer.

  `Schoenflies.CellStructure.SplitData.uniqueFaceAt` is what carries it across an ear insertion,
  and `Schoenflies.CellStructure.Realization.unique_cell_of_uniqueFaceAt` turns it into the
  `hunique` of `Schoenflies.polyAccessible_of_stronglyAccessible`. -/
  anchor_uniqueFaceAt : ∀ ⦃z⦄, z ∈ V(T.str.skel) → par z ∈ E(P.str.outerGraph) →
    (∀ ⦃f⦄, f ∈ E(B) → T.tgt.pos z ∈ Graph.edgeArc Hdraw f →
      Graph.edgeArc Hdraw f ⊆ tgtOuter) →
    T.str.UniqueFaceAt z
  /-- **The skeleton map is an extension of the base pair's.**

  Both elementary operations build the new skeleton homeomorphism by *extending* the old one — a
  subdivision does not change it at all and a split adds the ear map — so this holds all along
  and is nowhere derivable from the other clauses, since `Realization.Refines` says nothing about
  the two homeomorphisms.

  It is what lets the fresh-anchor hypothesis be spent. That hypothesis is about the *base*
  pair's correspondence: `a ∈ 𝒜` is a property of the source point `P.homeo` matches with the
  fresh target point `u(a)`. Without this clause there is no way to know that the intermediate
  stage matches the same two points, and the strong accessibility of `a` cannot be transported to
  `T.src.pos z`. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet

/-- **Step 1 of `thm:finite-transfer`(b)**, as an interface, in the shape the ear induction of
direction (b) will consume. -/
def CommonSubdivisionTgt (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsPartialTransferOfTgt T₀ P K Hdraw par₀

/-! ### The open nonboundary part, read on the target

The last paragraph of the proof runs the other way in direction (b): it is `|H'| ∖ S` that is
assumed connected, so it is the *target* realization whose open nonboundary part is known, and
`lem:combinatorial-invariance`(b) moves it to the source. -/

/-- The open nonboundary part of the target realization, read off the two clauses that pin the
skeleton and the outer cycle. -/
theorem GeneratedPair.tgt_nonboundary_eq (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    P.tgt.nonboundary = P.tgt.skeletonSet \ tgtOuter := by
  rw [CellStructure.Realization.nonboundary, P.tgt_isWeaklyAdmissible.outerSet_eq]

/-- **The last paragraph of the proof of `thm:finite-transfer`(b), source half.** -/
theorem GeneratedPair.src_isAdmissible_of_tgt
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.tgt.nonboundary) : P.src.IsAdmissible srcOuter srcDom :=
  { P.src_isWeaklyAdmissible with
    isConnected_nonboundary := P.homeo.isConnected_nonboundary_iff.2 h }

/-- **The last paragraph of the proof of `thm:finite-transfer`(b), target half.** -/
theorem GeneratedPair.tgt_isAdmissible_of_tgt
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.tgt.nonboundary) : P.tgt.IsAdmissible tgtOuter tgtDom :=
  { P.tgt_isWeaklyAdmissible with isConnected_nonboundary := h }

/-! ### The edge matching and the assembly -/

/-- **The edge matching, target side.** A stage whose drawn target skeleton occupies `|Γ'|` and
whose target 0-cells are exactly the vertices of `sourcePart P.tgt H Hdraw` has its adjacency.
The proof is `Graph.adj_congr_of_pointSet_eq` again — the lemma knows nothing about sides. -/
theorem adj_match_tgt {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hK : T.tgt.skeletonSet = P.tgt.skeletonSet)
    (hV : V(T.tgt.graph) = V(sourcePart P.tgt H Hdraw)) ⦃x y : Plane⦄ :
    T.tgt.graph.Adj x y ↔ (sourcePart P.tgt H Hdraw).Adj x y := by
  haveI := hH.finite
  haveI : (sourcePart P.tgt H Hdraw).Finite := Graph.Finite.of_le sourcePart_le
  haveI := T.tgt.finite_graph
  have hd : IsDrawing T.tgt.graph T.tgt.drawing := T.tgt.isDrawing
  exact Graph.adj_congr_of_pointSet_eq hd (hH.isDrawing.mono sourcePart_le)
    (show T.tgt.skeletonSet = _ by rw [hK, pointSet_sourcePart hH]) hV

/-- **Step 1 of `thm:finite-transfer`(b), unconditional.**

Subdivide the given pair at every vertex of `H` lying on `|Γ'|` — `exists_subdivide_finite_tgt`,
which cuts each source edge at the parameter its target point corresponds to — and the resulting
stage has exactly the 0-cells of `sourcePart P.tgt H Hdraw`. Its drawn target skeleton is
2-connected for free, and `Graph.IsTwoConnected.of_adj_congr` carries that across the change of
edge names. -/
theorem commonSubdivisionTgt [Infinite γ] (h₀ : S₀.CombInvariants)
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    CommonSubdivisionTgt P H Hdraw := by
  haveI := hH.finite
  have hQfin : (V(H) ∩ P.tgt.skeletonSet).Finite := (Graph.finite_vertexSet H).inter_of_left _
  obtain ⟨T, par, hrs, hrt, hK, hVold, hVQ, hVsub, hprop, hg⟩ :=
    GeneratedPair.exists_subdivide_finite_tgt h₀ hQfin P Set.inter_subset_right
  have hPQ : V(P.tgt.graph) ⊆ V(H) ∩ P.tgt.skeletonSet := fun z hz =>
    ⟨hH.vertexSet_subset hz, Graph.vertexSet_subset_pointSet hz⟩
  have hVeq : V(T.tgt.graph) = V(sourcePart P.tgt H Hdraw) :=
    Set.Subset.antisymm (hVsub.trans (Set.union_subset hPQ subset_rfl)) hVQ
  refine ⟨sourcePart P.tgt H Hdraw, T, par, ?_, sourcePart_le, hrs, hrt, ?_, hVeq.ge, ?_,
    fun x _ => by rw [hg]⟩
  · exact Graph.IsTwoConnected.of_adj_congr hVeq (adj_match_tgt hH T hK hVeq)
      T.tgt_isWeaklyAdmissible.isTwoConnected
  · rw [hK, pointSet_sourcePart hH]
  -- Nothing has been split yet, so the third antecedent is not needed: a 0-cell inserted into an
  -- outer edge of `P` inherits `lem:cellulation-invariants`(vi) from that edge.
  · exact fun z hz hpar _ => hprop (T.str.mem_cells_of_mem_vertexSet hz)
      (CellStructure.uniqueFaceAt_of_mem_outerGraph (P.combInvariants h₀).outerEdge_unique hpar)

end Schoenflies
