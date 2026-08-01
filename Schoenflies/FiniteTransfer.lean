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
* **The second sentence of step 2** — `Schoenflies.CellStructure.Realization`
  `.exists_unique_face_subset_cell`: the interior of an ear lies in one current face, because it
  is connected and disjoint from the current skeleton. On one named hypothesis,
  `Schoenflies.CellsAbsorb`.
* **The last paragraph of the proof** — `Schoenflies.GeneratedPair.src_isAdmissible` and
  `Schoenflies.GeneratedPair.tgt_isAdmissible`. Admissibility of the *final* object is
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
* `Schoenflies.CellStructure.Realization.exists_unique_face_subset_cell` — "the interior of each
  ear lies in one current face", with
  `Schoenflies.CellStructure.Realization.cell_subset_skeletonSet` and
  `Schoenflies.CellStructure.Realization.mem_faces_of_notMem_skeletonSet`.
* `Schoenflies.CellStructure.Realization.pos_mem_closure_cell_congr`,
  `Schoenflies.exists_target_ear` — "let `F*, v*, w*` be the corresponding face and endpoints in
  the other realization", and the whole fourth paragraph assembled from the source-side data.
* `Schoenflies.GeneratedPair.src_isAdmissible`, `Schoenflies.GeneratedPair.tgt_isAdmissible` —
  the last paragraph of the proof, via `lem:combinatorial-invariance`.
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

/-! #### Where an ear can lie

*The interior of each ear lies in one current face, because it is connected and disjoint from the
current skeleton.* That is the second sentence of step 2, and it is proved here for an arbitrary
connected subset of the closed domain missing the skeleton.

The only input beyond assertion (i) is `Schoenflies.CellsAbsorb` — assertion (i) in the
"a connected set disjoint from the skeleton that meets a 2-cell lies in it" reading, which
`Schoenflies/SkeletonAccess.lean` also carries as its single hypothesis and which
`Schoenflies.cellsAbsorb_of_isComponent_in` discharges on the target side. -/

variable {R : S.Realization} {D N : Set Plane} {σ : γ} {z : Plane}

/-- An open 0-cell or 1-cell is part of the realized skeleton. -/
theorem cell_subset_skeletonSet (R : S.Realization) (hσ : σ ∈ V(S.skel) ∪ E(S.skel)) :
    R.cell σ ⊆ R.skeletonSet := by
  rcases hσ with hv | he
  · rw [R.cell_vertex hv]
    exact Set.singleton_subset_iff.2 (Graph.vertexSet_subset_pointSet
      (by rw [Realization.vertexSet_graph]; exact ⟨σ, hv, rfl⟩))
  · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    rw [R.cell_edge hl]
    exact Set.sdiff_subset.trans (Graph.edgeArc_subset_pointSet
      (by rw [Realization.edgeSet_graph]; exact he))

/-- A cell whose open part contains a point off the skeleton is a 2-cell. -/
theorem mem_faces_of_notMem_skeletonSet (R : S.Realization) (hσ : σ ∈ S.cells)
    (hz : z ∈ R.cell σ) (hznot : z ∉ R.skeletonSet) : σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd (R.cell_subset_skeletonSet hσ hz) hznot
  · exact hσ

/-- **An ear lies in a single current face.** A nonempty connected subset of the closed domain
disjoint from the realized skeleton lies inside one open 2-cell, and inside only that one. -/
theorem exists_unique_face_subset_cell (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨z, hz⟩ := hNne
  obtain ⟨F, hFc, hzF⟩ := h.exists_cell (hND hz)
  have hznot : z ∉ R.skeletonSet := Set.disjoint_left.1 hNdisj hz
  have hFf : F ∈ S.faces := R.mem_faces_of_notMem_skeletonSet hFc hzF hznot
  refine ⟨F, hFf, hcells N hN hNdisj (R.cell F) ⟨F, hFf, rfl⟩ ⟨z, hz, hzF⟩, fun T hT hNT => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (S.mem_cells_of_mem_faces hT) hFc hne) (hNT hz) hzF

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

/-! ### Step 4, direction (a): the target crosscut

*In part (a), `F*` is a polygonal Jordan region in the square, by
`lem:cellulation-invariants`(vii). Every point of its boundary is polygonally accessible from its
interior. `lem:accessible-endpoints` therefore gives a polygonal crosscut `P* ⊆ closure F*` from
`v*` to `w*`.* Then: *`thm:general-crosscut` says that the crosscut splits the face into exactly
the two Jordan regions bounded by the crosscut together with those two paths.*

That whole paragraph is closed below, unconditionally. It is stated for a *target* face — a
member of a family of components of `Q ∖ |G|` for an ambient open region `Q` whose frontier
belongs to the skeleton — because that is the shape
`Graph.polygonal_side_accessibility_target` consumes, and it is the shape a target realization
of a generated structure has: `Q` is the open square, `|G|` the target skeleton, and the family
is the set of realized open 2-cells. -/

section TargetEar

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {Q F J P A₁ A₂ : Set Plane} {cells : Set (Set Plane)} {v w : Plane}

/-- A target 2-cell is an open connected set disjoint from the skeleton. Everything the crosscut
construction needs about it, read off the presentation as a component of `Q ∖ |G|`. -/
theorem isOpen_isPreconnected_disjoint_of_target_cell [G.Finite] (h : IsDrawing G drawing)
    (hQ : IsOpen Q)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) :
    IsOpen F ∧ IsPreconnected F ∧ Disjoint F (pointSet G drawing) := by
  obtain ⟨-, z, rfl⟩ := hcell F hF
  have hopen : IsOpen (Q \ pointSet G drawing) := hQ.sdiff h.isClosed_pointSet
  exact ⟨hopen.connectedComponentIn, isPreconnected_connectedComponentIn,
    Set.disjoint_left.2 fun _ hx => (connectedComponentIn_subset _ _ hx).2⟩

/-- **The target crosscut of `thm:finite-transfer`(a), step 4.** Two distinct points of a curve
`J` inside the target skeleton, both in the closure of a target 2-cell `F`, are joined by a
simple polygonal arc lying in `F` apart from its two endpoints and meeting `J` exactly there.

The three inputs are the three the blueprint names: `lem:polygonal-side-accessibility` on the
target side for the accessibility of each endpoint, and `lem:accessible-endpoints` in its
crosscut form for the join. Nothing is assumed. -/
theorem exists_target_crosscut [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} := by
  obtain ⟨hopen, hconn, hdisj⟩ :=
    isOpen_isPreconnected_disjoint_of_target_cell h hQ hcell hF
  obtain ⟨ws, -, -, -, hsub, harc, hmeet⟩ :=
    exists_crosscut_of_polyAccessible hopen hconn (hdisj.mono_right hJ) hvw hvJ hwJ
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hv)
      (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hw)
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub, hmeet⟩

/-- **Step 4 in full: the target crosscut splits the target face into exactly two Jordan
regions.** By `lem:cellulation-invariants`(vii) the target 2-cell `F` is the bounded
complementary region of the Jordan curve `J` realizing its boundary walk; the crosscut of
`Schoenflies.exists_target_crosscut` is then a crosscut of `J` in the sense of
`thm:general-crosscut`, which decomposes `F` into the two Jordan regions bounded by the crosscut
together with the two boundary paths.

The conclusion is returned in the shape assertion (i) consumes at a 2-cell split
(`Schoenflies.crosscut_cell_partition`): the old open 2-cell is the disjoint union of the two new
open 2-cells and the open crosscut, each new 2-cell is open and nonempty, and the closure of each
is that open 2-cell together with its own boundary curve. -/
theorem exists_target_crosscut_split [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ pointSet G drawing)
    (hcell : ∀ R ∈ cells, R ⊆ Q ∧ ∃ z, R = connectedComponentIn (Q \ pointSet G drawing) z)
    (hF : F ∈ cells) (hJ : J ⊆ pointSet G drawing) (hJc : IsJordanCurve J) (hFJ : F = inside J)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hv : v ∈ closure F) (hw : w ∈ closure F) (hcut : IsCutPair J v w A₁ A₂) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} ∧
      IsCrosscut J P v w ∧
      F = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {v, w}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {v, w}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {v, w}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) := by
  obtain ⟨P, hPpoly, hParc, hPsub, hPmeet⟩ :=
    exists_target_crosscut h hpoly hQ hQK hcell hF hJ hvw hvJ hwJ hv hw
  have hcross : IsCrosscut J P v w :=
    ⟨hJc, hParc, hPpoly, hvJ, hwJ, by rw [← hFJ]; exact hPsub⟩
  have hpart := crosscut_cell_partition (fun _ hS => jordan_curve_theorem hS) hcross hcut
    hcross.hasArcCollars
  exact ⟨P, hPpoly, hParc, hPsub, hPmeet, hcross, by rw [hFJ]; exact hpart.1, hpart.2.1,
    hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1,
    hpart.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.2⟩

end TargetEar

/-! ### The ear's endpoints, transferred

*Let `F*, v*, w*` be the corresponding face and endpoints in the other realization.* Under the
representation of `Schoenflies/CombinatorialInvariance.lean` there is nothing to transport: `F`
and the two endpoint 0-cells are cells of the **one** abstract structure both realizations
realize, and assertion (ix) turns "the source endpoint lies on the boundary of the source face"
into the abstract statement `a ≼ F`, which reads back in the target realization. -/

section EndpointTransfer

variable {S : CellStructure γ} {R₁ R₂ : S.Realization} {D₁ D₂ Q J A₁ A₂ : Set Plane} {a b F : γ}

/-- **The endpoints of the ear transfer to the other realization.** A 0-cell on the boundary of a
2-cell in one realization is on the boundary of the same 2-cell in the other. -/
theorem CellStructure.Realization.pos_mem_closure_cell_congr
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂)
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R₁.pos a ∈ closure (R₁.cell F)) :
    R₂.pos a ∈ closure (R₂.cell F) := by
  have hac : a ∈ S.cells := S.mem_cells_of_mem_vertexSet ha
  have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
  have hsub : S.sub a F := by
    refine h₁.sub_of_subset_closure hac hFc ?_
    rw [R₁.cell_vertex ha]
    exact Set.singleton_subset_iff.2 hmem
  have := h₂.subset_closure hac hFc hsub
  rw [R₂.cell_vertex ha] at this
  exact this (Set.mem_singleton _)

/-- **The geometric half of one ear insertion, direction (a).**

The source ear lies in a current source 2-cell `F` and its two endpoints are 0-cells on the
boundary of `F` (`hacl`, `hbcl`). The target realization of `F` is a polygonal Jordan region in
the open square `Q` (`hFJ` — assertion (vii)) whose 2-cells are the components of
`Q ∖ |Γ'|` (`hcell` — assertion (i) on the target side). Then the corresponding target endpoints
are joined by a polygonal crosscut inside the closure of the target face, which splits that face
into exactly the two Jordan regions bounded by the crosscut and the two boundary paths.

This is the fourth paragraph of the blueprint's proof of `thm:finite-transfer`(a), assembled;
what is left of the induction step is the abstract-data bookkeeping around it. -/
theorem exists_target_ear (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂)
    (hpoly : ∀ ⦃e⦄, e ∈ E(S.skel) → IsPolygonal (edgeArc R₂.drawing e))
    (hQ : IsOpen Q) (hQK : frontier Q ⊆ R₂.skeletonSet)
    (hcell : ∀ T ∈ S.faces, R₂.cell T ⊆ Q ∧
      ∃ z, R₂.cell T = connectedComponentIn (Q \ R₂.skeletonSet) z)
    (hF : F ∈ S.faces) (hJ : J ⊆ R₂.skeletonSet) (hJc : IsJordanCurve J)
    (hFJ : R₂.cell F = inside J)
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel)) (hab : R₂.pos a ≠ R₂.pos b)
    (haJ : R₂.pos a ∈ J) (hbJ : R₂.pos b ∈ J)
    (hacl : R₁.pos a ∈ closure (R₁.cell F)) (hbcl : R₁.pos b ∈ closure (R₁.cell F))
    (hcut : IsCutPair J (R₂.pos a) (R₂.pos b) A₁ A₂) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P (R₂.pos a) (R₂.pos b) ∧
      P \ {R₂.pos a, R₂.pos b} ⊆ R₂.cell F ∧ P ∩ J = {R₂.pos a, R₂.pos b} ∧
      IsCrosscut J P (R₂.pos a) (R₂.pos b) ∧
      R₂.cell F = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∪ (P \ {R₂.pos a, R₂.pos b}) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (P \ {R₂.pos a, R₂.pos b}) ∧
      Disjoint (inside (A₂ ∪ P)) (P \ {R₂.pos a, R₂.pos b}) ∧
      IsOpen (inside (A₁ ∪ P)) ∧ IsOpen (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) ∧
      closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) := by
  -- The family of target 2-cells, in the shape `lem:polygonal-side-accessibility` consumes.
  have hcell' : ∀ T ∈ {A : Set Plane | ∃ T ∈ S.faces, A = R₂.cell T},
      T ⊆ Q ∧ ∃ z, T = connectedComponentIn (Q \ pointSet R₂.graph R₂.drawing) z := by
    rintro T ⟨T', hT', rfl⟩
    exact hcell T' hT'
  have hpoly' : ∀ e ∈ E(R₂.graph), IsPolygonal (edgeArc R₂.drawing e) := by
    intro e he
    rw [CellStructure.Realization.edgeSet_graph] at he
    exact hpoly he
  have hdraw : IsDrawing R₂.graph R₂.drawing := R₂.isDrawing
  exact exists_target_crosscut_split hdraw hpoly' hQ hQK hcell'
    ⟨F, hF, rfl⟩ hJ hJc hFJ hab haJ hbJ
    (CellStructure.Realization.pos_mem_closure_cell_congr h₁ h₂ ha hF hacl)
    (CellStructure.Realization.pos_mem_closure_cell_congr h₁ h₂ hb hF hbcl) hcut

end EndpointTransfer

end Schoenflies
