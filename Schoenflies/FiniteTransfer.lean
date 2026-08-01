/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.RefinementStars
import Schoenflies.SkeletonAccess
import Schoenflies.Graph.RelativeEar
import Schoenflies.Graph.CycleJordan
import Schoenflies.JordanClosed

/-!
# Finite transfer, direction (a): toward the square

`thm:finite-transfer` is the largest single statement of the manuscript. This module states it —
in full, with every hypothesis — for **direction (a)** only, and proves as much of its four-step
proof as is within reach of what is on `main`.

Direction (b) is deliberately absent: its extra accessibility problem at the wild source
boundary needs `lem:tangent-cone`, `lem:compact-separation`(c) and the fresh-point bookkeeping
of the target mesh, none of which enters (a).

## The statement, and how it is read

The blueprint's (a) reads: *let `(Γ, Γ')` be a generated matched cellulation; suppose `H` is a
finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`, with every
nonboundary edge polygonal, and with `|H| ∖ C` connected; then the common subdivision can be
made on `Γ'`, and `H` can be transferred to an admissible target realization `H'`; the resulting
generated matched cellulation refines the old one by explicit parent maps.*

Four objects carry that sentence.

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible` and
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`. The weak form
  is exactly the strong one with connectedness of the open nonboundary part waived, which is
  what `def:generated-structure` requires of an intermediate stage and what
  `rem:intermediate-disconnection` insists on.
* `Schoenflies.GeneratedPair` — a generated matched cell structure *with its geometry*: the
  abstract structure, its two realizations, the skeleton homeomorphism, and the two cell
  decompositions. This is the Lean form of "`(Γ, Γ')` is a generated matched cellulation".
  It is a bundle of **data**, not an existential: every consumer reads `.src`, `.tgt`, `.homeo`
  by name.
* `Schoenflies.IsSourceExtension` — the hypotheses on `H`.
* `Schoenflies.IsTransferOf` — the conclusion, relating the new pair to the old one by an
  explicit parent map.

The one place where the Lean statement is *weaker in form* than the prose, and deliberately so:
"`H` can be transferred" is recorded as `T.src.skeletonSet = pointSet H Hdraw`, an equality of
point sets, rather than as a graph isomorphism onto `H`. The reason is step 1: the common
subdivision inserts a vertex at every intersection of a new edge with an old one, so the source
realization of the transferred structure realizes a *subdivision* of `H`, never `H` itself. What
survives verbatim is what the construction uses downstream — the occupied set, the
2-connectivity (which `lem:combinatorial-invariance` moves to the target) and the refinement.

## What is proved here

* **Step 4, target side** — `Schoenflies.exists_target_crosscut` and
  `Schoenflies.exists_target_crosscut_split`. In direction (a) the target face `F*` is a
  polygonal Jordan region in the square by `lem:cellulation-invariants`(vii); every point of its
  boundary is polygonally accessible from its interior by `lem:polygonal-side-accessibility`
  (target half); and `lem:accessible-endpoints` gives a polygonal crosscut `P* ⊆ closure F*`
  from `v*` to `w*`, which by `thm:general-crosscut` splits `F*` into exactly the two Jordan
  regions bounded by `P*` and the two boundary paths. That whole paragraph is closed,
  unconditionally.
* **The last paragraph of the proof** — `Schoenflies.IsTransferOf.tgt_isAdmissible_of_src` and
  `Schoenflies.isAdmissible_of_isWeaklyAdmissible`. Admissibility of the *final* object is
  recovered from `lem:combinatorial-invariance`: the reproduced realization has the same
  2-connectivity and the same connectedness of the open nonboundary part as the given one.
  Unconditional.
* **The induction scheme, steps 2 and 3** — `Schoenflies.transfer_of_ears`. With one ear
  insertion assumed (`Schoenflies.EarStep`), `lem:relative-ear` in its iterated form
  (`Graph.IsTwoConnected.ear_decomposition`) transfers the whole extension. This is the backbone
  of the induction, and it honours `rem:intermediate-disconnection`: the invariant carried
  through the induction, `Schoenflies.IsPartialTransferOf`, asks only for *weak* admissibility,
  and connectedness of the open nonboundary part is restored only at the very end.

## What is **not** proved here, and is named rather than `sorry`-ed

* **Step 1**, the common subdivision. `lem:polygonal-overlay` is on `main`
  (`Schoenflies.polygonal_overlay`) but only as a statement about a *list of segments*; turning
  it into "the old skeleton is literally a subgraph of the new one on both sides" needs the
  transfer of each new subdivision point through the chosen edge parametrization, and the
  parametrization-level API for that (an inverse for `drawing e` on `[0,1]`, and the induced
  point on the other side) does not exist. The hypothesis
  `Schoenflies.CommonSubdivision` is the interface: it says that the extension can be
  presented over a subdivided pair, and it is a strictly weaker statement than the theorem.
* **Step 3's single ear**, `Schoenflies.EarStep`: one ear insertion produces a
  `SplitData` (after at most two `SubdivData`s) together with the two new realizations. Its
  geometric core on the target side is `Schoenflies.exists_target_crosscut_split`, proved here;
  what is missing is the bookkeeping that turns a geometric crosscut into the abstract
  `SplitData` fields and the realization update — i.e. the split analogue of
  `SubdivData.IsRefinement`, which `GeneratedStructure.lean` also records as absent.

## Blueprint

* `Schoenflies.CellStructure.Realization.IsWeaklyAdmissible`,
  `Schoenflies.CellStructure.Realization.IsAdmissible` — `def:admissible-graph`.
* `Schoenflies.GeneratedPair` — `def:generated-structure` with its two realizations,
  `def:matched-pair` and `def:matched-cellulation` folded in.
* `Schoenflies.IsSourceExtension` — the hypotheses of `thm:finite-transfer`(a) on `H`.
* `Schoenflies.IsPartialTransferOf`, `Schoenflies.IsTransferOf` — the conclusion of
  `thm:finite-transfer`, at an intermediate stage and at the end.
* `Schoenflies.exists_target_crosscut`, `Schoenflies.exists_target_crosscut_split` —
  the fourth paragraph of the proof of `thm:finite-transfer`, direction (a):
  `lem:cellulation-invariants`(vii) + `lem:polygonal-side-accessibility` +
  `lem:accessible-endpoints` + `thm:general-crosscut`.
* `Schoenflies.isAdmissible_of_isWeaklyAdmissible`,
  `Schoenflies.IsTransferOf.tgt_isAdmissible_of_src` — the last paragraph of the proof, via
  `lem:combinatorial-invariance`.
* `Schoenflies.EarStep`, `Schoenflies.CommonSubdivision` — the two named hypotheses.
* `Schoenflies.transfer_of_ears`, `Schoenflies.finite_transfer_toward_square` —
  `thm:finite-transfer`(a).
-/

open Metric Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*}

/-! ### `def:admissible-graph`

An admissible graph in the closed Jordan domain is a finite 2-connected plane graph whose outer
cycle is `C`, whose edges not contained in `C` are polygonal arcs with interiors in `D`, and
whose open nonboundary part `|Γ| ∖ C` is connected. A *weakly* admissible graph satisfies
everything but the last clause.

`outer` is the realized outer cycle and `dom` the closed domain; the open domain is `dom ∖
outer`. On the source side that reads `C` and `C ∪ D`; on the target side `S` and `Q`. -/

namespace CellStructure

namespace Realization

variable {S : CellStructure γ}

/-- **A weakly admissible realization** — `def:admissible-graph` with connectedness of the open
nonboundary part waived, which is what `def:generated-structure` requires of every intermediate
stage (`rem:intermediate-disconnection`). -/
structure IsWeaklyAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop where
  /-- The drawn skeleton is 2-connected. -/
  isTwoConnected : R.graph.IsTwoConnected
  /-- The realized outer cycle is the prescribed curve. -/
  outerSet_eq : R.outerSet = outer
  /-- Every nonboundary edge is a polygonal arc. -/
  isPolygonal : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → IsPolygonal (edgeArc R.drawing e)
  /-- Every nonboundary edge has its interior in the open domain. Endpoints may lie on the
  outer cycle, as for a crosscut. -/
  cell_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → e ∉ E(S.outerGraph) → R.cell e ⊆ dom \ outer
  /-- The whole skeleton lies in the closed domain. -/
  skeletonSet_subset : R.skeletonSet ⊆ dom

/-- **An admissible realization** — `def:admissible-graph` in full. -/
structure IsAdmissible (R : S.Realization) (outer dom : Set Plane) : Prop
    extends R.IsWeaklyAdmissible outer dom where
  /-- The open nonboundary part `|Γ| ∖ C` is connected. -/
  isConnected_nonboundary : IsConnected R.nonboundary

end Realization

end CellStructure

/-! ### A generated matched cell structure, with its geometry

`def:generated-structure` says what the *abstract* object is; `GeneratedStructure` in
`Schoenflies/GeneratedStructure.lean` is that. What a transfer produces, and what the
finite-transfer theorem consumes, is the abstract object together with its two realizations, the
skeleton homeomorphism between them, and the two cell decompositions of
`lem:cellulation-invariants`(i). That bundle is `GeneratedPair`.

It is data, not a `Prop`: a consumer reads `.src`, `.tgt`, `.homeo`, `.str` by name. -/

/-- **A generated matched cell structure with its two realizations.** The Lean form of
"`(Γ, Γ')` is a generated matched cellulation", except that only *weak* admissibility is a
field — `rem:intermediate-disconnection` — with the connected form carried separately by the
consumers that have it. -/
structure GeneratedPair (S₀ : CellStructure γ) (srcOuter srcDom tgtOuter tgtDom : Set Plane)
    where
  /-- The abstract cell structure. -/
  str : CellStructure γ
  /-- It is generated from the base by a finite sequence of elementary operations. -/
  generated : GeneratedStructure S₀ str
  /-- The realization in the closed Jordan domain. -/
  src : str.Realization
  /-- The realization in the closed square. -/
  tgt : str.Realization
  /-- The skeleton homeomorphism `g : |Γ| → |Γ'|` of `def:matched-pair`. -/
  homeo : CellStructure.SkeletonHomeo src tgt
  /-- **Assertion (i)** on the source side. -/
  src_isCellDecomposition : src.IsCellDecomposition srcDom
  /-- **Assertion (i)** on the target side. -/
  tgt_isCellDecomposition : tgt.IsCellDecomposition tgtDom
  /-- The source realization is weakly admissible. -/
  src_isWeaklyAdmissible : src.IsWeaklyAdmissible srcOuter srcDom
  /-- The target realization is weakly admissible. -/
  tgt_isWeaklyAdmissible : tgt.IsWeaklyAdmissible tgtOuter tgtDom

namespace GeneratedPair

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- The combinatorial invariants hold at every generated stage, once they hold at the base —
`Schoenflies.GeneratedStructure.combInvariants`, read off the bundle. -/
theorem combInvariants (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h₀ : S₀.CombInvariants) : P.str.CombInvariants :=
  P.generated.combInvariants h₀

/-- The open nonboundary part of the source realization, read off the two clauses that pin the
skeleton and the outer cycle. -/
theorem src_nonboundary_eq (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    P.src.nonboundary = P.src.skeletonSet \ srcOuter := by
  rw [CellStructure.Realization.nonboundary, P.src_isWeaklyAdmissible.outerSet_eq]

/-- **The last paragraph of the proof of `thm:finite-transfer`, target half.** Once the source
realization's open nonboundary part is connected, so is the target's — this is part (b) of
`lem:combinatorial-invariance` — and the target realization, weakly admissible by construction,
is therefore admissible. -/
theorem tgt_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.tgt.IsAdmissible tgtOuter tgtDom :=
  { P.tgt_isWeaklyAdmissible with
    isConnected_nonboundary := P.homeo.isConnected_nonboundary_iff.1 h }

/-- **The last paragraph of the proof, source half.** -/
theorem src_isAdmissible (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (h : IsConnected P.src.nonboundary) : P.src.IsAdmissible srcOuter srcDom :=
  { P.src_isWeaklyAdmissible with isConnected_nonboundary := h }

end GeneratedPair

/-! ### The hypotheses of direction (a) on the given extension

*`H` is a finite 2-connected plane graph containing a subdivision of `Γ`, with outer cycle `C`,
with every nonboundary edge polygonal, and with `|H| ∖ C` connected.*

"Contains a subdivision of `Γ`" is recorded by three clauses: every old vertex is a vertex of
`H`; the old skeleton is inside `|H|`; and any edge of `H` that meets an *open* old edge lies
inside that old edge. Together those say that each old edge is cut into a chain of `H`-edges and
nothing else runs along it, which is exactly what a subdivision is.

"With outer cycle `C`, with every nonboundary edge polygonal" is `edge_dichotomy`: each edge of
`H` either lies inside the outer curve or is polygonal with its interior in the open domain.
Recording the outer cycle as a *subgraph* would put data inside a `Prop`; this reading is what
every step of the proof actually uses, and `outer ⊆ pointSet H Hdraw` comes for free from
`skeletonSet_subset`. -/

/-- **The hypotheses of `thm:finite-transfer`(a) on the extension `H`.** -/
structure IsSourceExtension {S : CellStructure γ} (R : S.Realization) (outer dom : Set Plane)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop where
  /-- `H` is finite. -/
  finite : H.Finite
  /-- `H` is a plane graph. -/
  isDrawing : IsDrawing H Hdraw
  /-- `H` is 2-connected. -/
  isTwoConnected : H.IsTwoConnected
  /-- Every 0-cell of `Γ` is a vertex of `H`. -/
  vertexSet_subset : V(R.graph) ⊆ V(H)
  /-- `|Γ| ⊆ |H|`. -/
  skeletonSet_subset : R.skeletonSet ⊆ pointSet H Hdraw
  /-- An edge of `H` meeting an open edge of `Γ` runs inside it: `H` subdivides `Γ` rather than
  crossing it. -/
  edge_subset : ∀ ⦃e⦄, e ∈ E(S.skel) → ∀ ⦃f⦄, f ∈ E(H) →
    (edgeArc Hdraw f ∩ R.cell e).Nonempty → edgeArc Hdraw f ⊆ edgeArc R.drawing e
  /-- `H` is drawn in the closed domain. -/
  pointSet_subset : pointSet H Hdraw ⊆ dom
  /-- Each edge of `H` is an outer edge or a polygonal nonboundary edge with interior in the
  open domain. -/
  edge_dichotomy : ∀ ⦃f⦄, f ∈ E(H) → edgeArc Hdraw f ⊆ outer ∨
    (IsPolygonal (edgeArc Hdraw f) ∧ edgeArc Hdraw f \ V(H) ⊆ dom \ outer)
  /-- `|H| ∖ C` is connected. -/
  isConnected : IsConnected (pointSet H Hdraw \ outer)

namespace IsSourceExtension

variable {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane}
  {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- A plane graph has no loops, so `lem:relative-ear` applies to `H`. -/
theorem not_isLoopAt (h : IsSourceExtension R outer dom H Hdraw) ⦃f : γ⦄ ⦃x : Plane⦄ :
    ¬ H.IsLoopAt f x := h.isDrawing.not_isLoopAt f x

end IsSourceExtension

/-! ### The conclusion

`IsPartialTransferOf T P B par` is the invariant the induction of steps 2–3 carries: `T` is a
generated pair refining `P` along `par` whose source realization occupies exactly what the
current subgraph `B` of `H` occupies. It asks for **no** connectedness of the open nonboundary
part — `rem:intermediate-disconnection` — because an ear with both endpoints on the outer cycle
really does disconnect it, and later ears reconnect it.

`IsTransferOf` is the same with admissibility of both final realizations added; that is the
theorem's conclusion, and `GeneratedPair.src_isAdmissible` / `GeneratedPair.tgt_isAdmissible`
are what produce it from the connectedness hypothesis on `H`. -/

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- **An intermediate stage of the transfer.** -/
structure IsPartialTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the old one along `par` — assertion (iv). -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the old one along the *same* parent map. That sharing
  is `lem:refinement-compatibility`(c). -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The new source skeleton occupies exactly what the current subgraph occupies. -/
  skeletonSet_eq : T.src.skeletonSet = pointSet B Hdraw
  /-- Every vertex of the current subgraph is a 0-cell of the new structure: the new structure
  realizes a subdivision of `B`, so it has at least `B`'s vertices. -/
  vertexSet_subset : V(B) ⊆ V(T.src.graph)

/-- **The conclusion of `thm:finite-transfer`(a).** -/
structure IsTransferOf (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsPartialTransferOf T P H Hdraw par where
  /-- The transferred source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The transferred target realization is admissible — "`H` can be transferred to an
  admissible target realization `H'`". -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

/-! ### The two assumed steps

Both are strictly weaker than `thm:finite-transfer`(a) itself, and both are statements a later
module can discharge without circularity.

`CommonSubdivision` is **step 1**: after overlaying the proposed polygonal nonboundary edges
with the old polygonal nonboundary skeleton and subdividing at every intersection — and
transferring each new point to the other realization along the chosen edge parametrization —
the old skeleton is literally a subgraph of the new one on both sides. In Lean that is: some
2-connected subgraph `K ≤ H` carries a generated pair refining the given one. It is not the
theorem: it makes only edge subdivisions, inserts no ear, and its conclusion is about a subgraph
of `H`, not about `H`.

`EarStep` is **step 3**: one ear insertion — at most two edge subdivisions followed by one
2-cell split — carries a partial transfer of `B` to a partial transfer of `B` with the ear glued
on. Its geometric core in direction (a) is `Schoenflies.exists_target_crosscut_split` below,
which is proved unconditionally; what is assumed is the abstract-data bookkeeping around it. -/

/-- **Step 1, the common subdivision**, as an interface. -/
def CommonSubdivision (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsPartialTransferOf T₀ P K Hdraw par₀

/-- **Step 3, one ear insertion**, as an interface.

The data handed to the step is exactly what `Graph.IsTwoConnected.ear_decomposition` supplies:
the current subgraph `B`, the ear `D` as a path of `H` between two distinct vertices of `B`, and
the freshness of the ear's interior — which is what makes the ear's interior lie in a single
current face, since it is connected and disjoint from the current skeleton. -/
def EarStep (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

/-! ### Steps 2 and 3: the induction through the ear sequence -/

/-- **Steps 2 and 3 of the proof of `thm:finite-transfer`.** By `lem:relative-ear` the new finite
2-connected graph is obtained from the old subdivided graph by a finite sequence of ears; each
ear insertion is at most two edge subdivisions plus one 2-cell split, so every intermediate stage
is a generated matched cell structure. Given step 1 and one ear, the whole extension transfers.

The invariant carried through the induction is `IsPartialTransferOf`, which does **not** mention
connectedness of the open nonboundary part: `rem:intermediate-disconnection` says an
intermediate stage may genuinely have it disconnected, and nothing here assumes otherwise. -/
theorem transfer_of_ears {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsPartialTransferOf T P H Hdraw par := by
  haveI := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-! ### `thm:finite-transfer`(a) -/

/-- **`thm:finite-transfer`, direction (a): transfer toward the square.**

Let `(Γ, Γ')` be a generated matched cellulation. Suppose `H` is a finite 2-connected plane graph
containing a subdivision of `Γ`, with outer cycle `C`, with every nonboundary edge polygonal, and
with `|H| ∖ C` connected. Then the common subdivision can be made on `Γ'`, and `H` can be
transferred to an admissible target realization `H'`; the resulting generated matched cellulation
refines the old one by an explicit parent map.

The two hypotheses `CommonSubdivision` and `EarStep` are steps 1 and 3 of the blueprint's proof;
see the module docstring. Everything else — step 2, the induction, and the final recovery of
admissibility on both sides — is proved here. -/
theorem finite_transfer_toward_square {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsub : CommonSubdivision P H Hdraw) (hstep : EarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ := transfer_of_ears hH hsub hstep
  -- The final source realization occupies `|H|`, so its open nonboundary part is `|H| ∖ C`,
  -- which the hypothesis on `H` says is connected. Combinatorial invariance moves that to the
  -- target, and both realizations are then admissible.
  have hconn : IsConnected T.src.nonboundary := by
    rw [T.src_nonboundary_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  exact ⟨T, par, hT, T.src_isAdmissible hconn, T.tgt_isAdmissible hconn⟩

end Schoenflies
