/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CommonSubdivTgt

/-!
# `thm:finite-transfer`, direction (b): transfer back from an admissible target refinement

*Suppose `H'` is a finite 2-connected polygonal plane graph containing a subdivision of `Γ'`,
with outer cycle `S`, and with `|H'| ∖ S` connected. Assume that every new nonboundary edge of
`H' ∖ Γ'` meeting `S` has exactly one endpoint on `S`, that this endpoint is a fresh point
`u(a)` with `a ∈ 𝒜`, and that exactly one new nonboundary edge is incident with each such fresh
boundary point. Then the common subdivision can be made on `Γ`, and `H'` can be transferred to
an admissible source realization `H`.*

Everything of this except **one ear insertion** is proved here.

## What the statement takes, and what it does not

The first sentence is `Schoenflies.IsSourceExtension P.tgt tgtOuter tgtDom H' H'draw`. That
structure is stated for an arbitrary realization rather than for `P.src`, so it says of `H'`
exactly what direction (a) says of `H` — including, through `edge_dichotomy`, that every
nonboundary edge is polygonal. Its name is now half wrong; see `CommonSubdivTgt.lean`.

The second sentence — the fresh-anchor clauses — is **not** a hypothesis of anything below. It
is what the ear step needs, and only in the one case the blueprint singles out: when the target
ear starts on `S`, the corresponding source endpoint lies on the wild curve `C`, where no
polygonal skeleton reaches it. So it belongs to `Schoenflies.EarStepTgt`, whose discharger will
carry it, and not to the induction, which never looks at where an ear's ends are.

## What is left

`Schoenflies.EarStepTgt`, and nothing else. Its two halves are of quite different sizes:

* an endpoint off `C` is accessible from the corresponding source face by
  `lem:polygonal-side-accessibility`, both halves of which are in `SkeletonAccess.lean`;
* an endpoint on `C` is the anchor `a` of a fresh point `u(a)`, and
  `Schoenflies.polyAccessible_of_stronglyAccessible` (`FreshAccess.lean`) is that paragraph,
  proved — but carrying `hunique`, *the only current source 2-cell whose closure contains `a` is
  the one corresponding to the target face*. That is the blueprint's combinatorial paragraph
  ("each of the resulting outer subedges is incident with exactly one source 2-cell … hence
  exactly one descendant 2-cell remains incident with `a`"), an induction over the ear sequence,
  and it is the one piece of direction (b) with real content left.

## Blueprint

* `Schoenflies.EarStepTgt` — direction (b), step 3, as an interface.
* `Schoenflies.transfer_of_ears_tgt` — steps 2 and 3, the induction through the ear sequence.
* `Schoenflies.finite_transfer_back` — `thm:finite-transfer`(b), on the ear step alone.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph CellStructure

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- **The conclusion of `thm:finite-transfer`(b).** -/
structure IsTransferOfTgt (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsPartialTransferOfTgt T P H Hdraw par where
  /-- The transferred source realization is admissible — "`H'` can be transferred to an
  admissible source realization `H`". -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The refined target realization is admissible. -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

/-- **Step 3 of `thm:finite-transfer`(b)**, one ear insertion, as an interface.

Identical in shape to `Schoenflies.EarStep`; what differs is the invariant it carries, and
therefore which side the ear is given on. Here the ear is an ear of the *target* extension and
the crosscut has to be produced in the corresponding *source* 2-cell — which is why this is not
the same theorem with the arguments renamed, and why the fresh-anchor hypotheses of
`thm:finite-transfer`(b) are spent by its discharger.

`Infinite γ` is not decoration, for the same reason as in direction (a): the step consumes fresh
cell names. -/
def EarStepTgt [Infinite γ] (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOfTgt T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsPartialTransferOfTgt T' P (B.union (H.pathGraphOf a D)) Hdraw par'

/-- **Steps 2 and 3 of the proof of `thm:finite-transfer`(b).** The ear decomposition does not
know which side its invariant is about, so this is `Schoenflies.transfer_of_ears` with
`IsPartialTransferOfTgt` in place of `IsPartialTransferOf`, and step 1 already discharged by
`Schoenflies.commonSubdivisionTgt`. -/
theorem transfer_of_ears_tgt [Infinite γ] (h₀ : S₀.CombInvariants)
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) (hstep : EarStepTgt P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOfTgt T P H Hdraw par := by
  haveI := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := commonSubdivisionTgt h₀ P hH
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsPartialTransferOfTgt T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-- **`thm:finite-transfer`, direction (b), on the ear step alone.**

Step 1 is `Schoenflies.commonSubdivisionTgt`, proved; steps 2 and 4 and the final recovery of
admissibility are here. The last paragraph runs the other way from direction (a)'s: it is
`|H'| ∖ S` that is assumed connected, so the *target* realization is the one whose open
nonboundary part is known, and `lem:combinatorial-invariance`(b) moves it to the source. -/
theorem finite_transfer_back [Infinite γ] (h₀ : S₀.CombInvariants)
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) (hstep : EarStepTgt P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOfTgt T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ := transfer_of_ears_tgt h₀ hH hstep
  -- The final target realization occupies `|H'|`, so its open nonboundary part is `|H'| ∖ S`.
  have hconn : IsConnected T.tgt.nonboundary := by
    rw [T.tgt_nonboundary_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  exact ⟨T, par, hT, T.src_isAdmissible_of_tgt hconn, T.tgt_isAdmissible_of_tgt hconn⟩

end Schoenflies
