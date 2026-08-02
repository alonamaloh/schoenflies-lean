/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.RefinementStars
import Schoenflies.BoundaryWalks
import Schoenflies.OverlayGraph
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

* **Step 1, the overlay** — `Schoenflies.exists_overlay_of_biUnion_finite`: the union of
  finitely many nondegenerate polygonal sets is the point set of a finite plane graph drawn by
  straight segments. That is `lem:polygonal-overlay` in the form step 1 needs, bridging
  `Schoenflies.polygonal_overlay`, which is stated for a list of segments, to the finite family
  of polygonal *arcs* a skeleton stage arrives as. Unconditional.
* **Step 4, target side** — `Schoenflies.exists_target_crosscut` and
  `Schoenflies.exists_target_crosscut_split`. In direction (a) the target face `F*` is a
  polygonal Jordan region in the square by `lem:cellulation-invariants`(vii); every point of its
  boundary is polygonally accessible from its interior by `lem:polygonal-side-accessibility`
  (target half); and `lem:accessible-endpoints` gives a polygonal crosscut `P* ⊆ closure F*`
  from `v*` to `w*`, which by `thm:general-crosscut` splits `F*` into exactly the two Jordan
  regions bounded by `P*` and the two boundary paths. That whole paragraph is closed,
  unconditionally.
* **The second sentence of step 2** — `…IsCellDecomposition.exists_unique_face_subset_cell` and
  `…IsCellDecomposition.exists_face_of_ear`: the interior of an ear lies in one current face,
  because it is connected and disjoint from the current skeleton, and its two endpoints then lie
  on that face's boundary cycle. On one named hypothesis, `Schoenflies.CellsAbsorb`.
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

* **The second half of step 1**, the common subdivision. The overlay itself is proved
  (`Schoenflies.exists_overlay_of_biUnion_finite`, below); what is missing is that the *old
  skeleton* is literally a subgraph of the overlay **on both sides**, which needs each new
  subdivision point carried through the chosen edge parametrization to the other realization,
  and the parametrization-level API for that (an inverse for `drawing e` on `[0,1]`, and the
  induced point on the other side) does not exist on `main`. The hypothesis
  `Schoenflies.CommonSubdivision` is the interface: it says that the extension can be
  presented over a subdivided pair, and it is a strictly weaker statement than the theorem.
* **Step 3's single ear**, `Schoenflies.EarStep`: one ear insertion produces a
  `SplitData` (after at most two `SubdivData`s) together with the two new realizations. Its
  geometric core on the target side is `Schoenflies.exists_target_crosscut_split`, proved here;
  what is missing is the bookkeeping that turns a geometric crosscut into the abstract
  `SplitData` fields and the realization update — i.e. the *realization constructor* for a
  2-cell split. `Schoenflies/CellulationInvariants.lean` supplies the step theorem
  (`SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan`: given a realization of the
  split structure standing in the right relation to the old one, every invariant propagates);
  what no module yet supplies is a realization of the split structure *built from* a geometric
  crosscut. `EarStep` is exactly that gap, and it carries `[Infinite γ]` — see below, where the
  reason is spelled out, because without a supply of fresh cell names the hypothesis is false.

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
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.exists_unique_face_subset_cell`,
  `…IsCellDecomposition.exists_face_of_ear`,
  `…IsCellDecomposition.sub_of_pos_mem_closure_cell` — "the interior of each ear lies in one
  current face", with the two supporting facts
  `Schoenflies.CellStructure.Realization.cell_subset_skeletonSet` (hoisted to
  `Schoenflies/CombinatorialInvariance.lean`) and
  `Schoenflies.CellStructure.Realization.mem_faces_of_notMem_skeletonSet`.
* `Schoenflies.CellStructure.Realization.pos_mem_closure_cell_congr`,
  `Schoenflies.exists_target_ear` — "let `F*, v*, w*` be the corresponding face and endpoints in
  the other realization", and the whole fourth paragraph assembled from the source-side data.
* `Schoenflies.GeneratedPair.src_isAdmissible`, `Schoenflies.GeneratedPair.tgt_isAdmissible` —
  the last paragraph of the proof, via `lem:combinatorial-invariance`.
* `Schoenflies.exists_overlay_of_biUnion_finite` — `lem:polygonal-overlay` and
  `rem:polygonal-overlay-convention`, for a finite family of polygonal sets: the first half of
  step 1.
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

/-- A cell whose open part contains a point off the skeleton is a 2-cell. -/
theorem mem_faces_of_notMem_skeletonSet (R : S.Realization) (hσ : σ ∈ S.cells)
    (hz : z ∈ R.cell σ) (hznot : z ∉ R.skeletonSet) : σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd (cell_subset_skeletonSet hσ hz) hznot
  · exact hσ

namespace IsCellDecomposition

/-- A 0-cell in the closure of an open 2-cell is a subcell of it — assertion (ix) read at a
vertex. This is how an ear's endpoint is recognised as lying on the boundary cycle of the face
its interior occupies. -/
theorem sub_of_pos_mem_closure_cell (h : R.IsCellDecomposition D) {a F : γ}
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hmem : R.pos a ∈ closure (R.cell F)) :
    S.sub a F := by
  refine h.sub_of_subset_closure (S.mem_cells_of_mem_vertexSet ha)
    (S.mem_cells_of_mem_faces hF) ?_
  rw [R.cell_vertex ha]
  exact Set.singleton_subset_iff.2 hmem

/-- **A 0-cell below a 2-cell is drawn in its closure** — the converse of
`sub_of_pos_mem_closure_cell`, and assertion (ix) read the other way. Both ear steps use it to
turn the abstract incidence of an ear's end with its 2-cell into the geometric hypothesis the
crosscut construction asks for. -/
theorem pos_mem_closure_cell_of_sub (h : R.IsCellDecomposition D) {a F : γ}
    (ha : a ∈ V(S.skel)) (hF : F ∈ S.faces) (hsub : S.sub a F) :
    R.pos a ∈ closure (R.cell F) := by
  have hmem := h.subset_closure (S.mem_cells_of_mem_vertexSet ha)
    (S.mem_cells_of_mem_faces hF) hsub
  rw [R.cell_vertex ha] at hmem
  exact hmem rfl

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

/-- **One ear, placed — the source-side input of the induction step.** The open part `N` of the
ear is connected, inside the closed domain and disjoint from the current skeleton, so it lies in
a unique current 2-cell `F`; and each endpoint of the ear, being a 0-cell in the closure of `N`,
is a subcell of `F`, i.e. lies on its boundary cycle.

Feeding the two `S.sub` conclusions back through `IsCellDecomposition.subset_closure` in the
*other* realization is exactly `Schoenflies.exists_target_ear`'s two closure hypotheses. -/
theorem exists_face_of_ear (h : R.IsCellDecomposition D)
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F})
    (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ D)
    (hNdisj : Disjoint N R.skeletonSet) {a b : γ}
    (ha : a ∈ V(S.skel)) (hb : b ∈ V(S.skel))
    (hacl : R.pos a ∈ closure N) (hbcl : R.pos b ∈ closure N) :
    ∃ F ∈ S.faces, N ⊆ R.cell F ∧ S.sub a F ∧ S.sub b F ∧
      ∀ T ∈ S.faces, N ⊆ R.cell T → T = F := by
  obtain ⟨F, hF, hNF, huniq⟩ := h.exists_unique_face_subset_cell hcells hN hNne hND hNdisj
  exact ⟨F, hF, hNF,
    h.sub_of_pos_mem_closure_cell ha hF (closure_mono hNF hacl),
    h.sub_of_pos_mem_closure_cell hb hF (closure_mono hNF hbcl), huniq⟩

end IsCellDecomposition

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
  /-- **Assertion (vii)** on the source side: every open 2-cell is the bounded complementary
  region of a Jordan curve, namely its own frontier.

  Like `walks` below it travels with the bundle rather than being derived from `generated`. The
  reason is the same: `SplitData.isCellDecomposition_and_isFaceJordan_realize` *consumes* it at
  the current stage and reproduces it at the next, so there is no closure theorem over the raw
  inductive, only the two step constructions a consumer applies while building a stage. And
  `EarStep` needs it on **both** sides — on the target because
  `SplitData.isCutPair_of_inter`, which produces the `IsCutPair` that
  `Schoenflies.exists_target_ear` consumes, is stated against it. -/
  src_isFaceJordan : src.IsFaceJordan
  /-- **Assertion (vii)** on the target side. -/
  tgt_isFaceJordan : tgt.IsFaceJordan
  /-- **Every target edge is a polygonal arc — the outer ones included.**

  This is the one place where the two sides of a matched cellulation are genuinely *not*
  mirror images, and the reason it has to be a field. `IsWeaklyAdmissible.isPolygonal` restricts
  polygonality to the **nonboundary** edges, and that restriction is not slack:
  `def:admissible-graph` states it that way because the outer edges of a *source* stage are
  subarcs of the wild Jordan curve `C`, which is in general nowhere polygonal. (`IsStageOn`
  once dropped the restriction and was unsatisfiable in consequence — see `docs/ROADMAP.md`.)

  On the target side the outer cycle is the boundary of the square, so *every* edge is
  polygonal — and that is what `Schoenflies.exists_target_ear` needs, through
  `Graph.polygonal_side_accessibility_target`, which quantifies over all of `E(G)`. Nothing
  weaker will do, and nothing already in the bundle implies it. -/
  tgt_isPolygonal : ∀ ⦃e⦄, e ∈ E(str.skel) → IsPolygonal (Graph.edgeArc tgt.drawing e)
  /-- The source realization is weakly admissible. -/
  src_isWeaklyAdmissible : src.IsWeaklyAdmissible srcOuter srcDom
  /-- The target realization is weakly admissible. -/
  tgt_isWeaklyAdmissible : tgt.IsWeaklyAdmissible tgtOuter tgtDom
  /-- **The boundary-walk invariant**: every 2-cell's `boundary` datum is a cycle of the
  skeleton whose cells are exactly the cells below it.

  It travels with the bundle rather than being derived from `generated`, and it has to: a
  `GeneratedStructure` derivation may contain `SubdivData`s whose `boundaryStart` has nothing
  to do with any invariant, so there is no closure theorem over the raw inductive — only the two
  step constructions `BoundaryWalks.subdivideEdge` and `BoundaryWalks.splitFace`, which a
  consumer *building* a stage applies. `EarStep` is what needs it: the two boundary paths of the
  2-cell an ear is inserted into come from `BoundaryWalks.exists_boundary_paths`, and there is
  nowhere else to get them (`lem:face-cycles` is unavailable on the source side — see
  `docs/ROADMAP.md`). -/
  walks : str.BoundaryWalks

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
  /-- **The skeleton map is an extension of the base pair's.**

  Both elementary operations build the new skeleton homeomorphism by *extending* the old one — a
  subdivision does not change it at all and a split adds the ear map — so this holds all along
  and is nowhere derivable from the other clauses, since `Realization.Refines` says nothing about
  the two homeomorphisms. It is what `StageSequence.skelHomeo_succ` reads off a stage: without
  it, chaining stages loses all control of the skeleton maps. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet

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
which is proved unconditionally; what is assumed is the abstract-data bookkeeping around it.

**`EarStep` carries `[Infinite γ]`, and without it the hypothesis is false.** Every cell of
every structure in sight is a *name* drawn from the one type `γ`: `V(skel)`, `E(skel)` and
`faces` are three disjoint subsets of it. An ear insertion consumes fresh names — one per
interior vertex of the ear, one per ear edge, and two for the 2-cells the split creates
(`SplitData.edge_fresh`, `.vertex_fresh`, `.face₁_notMem`, `.face₂_notMem`) — while the
conclusion `IsPartialTransferOf T' P (B ∪ ear) Hdraw par'` forces `T'` to realize a subdivision
of the enlarged graph, so `V(B ∪ ear) ⊆ V(T'.src.graph) = T'.src.pos '' V(T'.str.skel)` and the
new skeleton must occupy strictly more of the plane than the old one. On a finite `γ` those
demands eventually exceed the supply: a structure realizing a subdivision of a 2-connected graph
with `e` edges needs at least `e` edge names, at least as many vertex names, and at least one
face name per complementary region, all pairwise distinct inside `γ`. A `γ` large enough to
carry the transfer of `B` and too small to carry the transfer of `B` with one more ear makes the
hypotheses of `EarStep` satisfiable and its conclusion unsatisfiable.

That argument is prose, not machine-checked: pinning it down needs a `GeneratedPair` over an
exactly-exhausted finite `γ`, which is a page of construction for a defect the type class
removes outright. What *is* machine-checked is that nothing below needs more than `Infinite γ`,
and the consumer instantiates `γ := ℕ`. The rule that found this is the standing one: a
hypothesis must be a statement one believes, and `EarStep` without a supply of fresh names is
not one. -/

/-- **Step 1, the common subdivision**, as an interface. -/
def CommonSubdivision (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsPartialTransferOf T₀ P K Hdraw par₀

/-- **Step 3, one ear insertion**, as an interface.

The data handed to the step is exactly what `Graph.IsTwoConnected.ear_decomposition` supplies:
the current subgraph `B`, the ear `D` as a path of `H` between two distinct vertices of `B`, and
the freshness of the ear's interior — which is what makes the ear's interior lie in a single
current face, since it is connected and disjoint from the current skeleton.

`Infinite γ` is not decoration: the step consumes fresh cell names, and on a finite `γ` the
statement is false. See the section docstring above. -/
def EarStep [Infinite γ] (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
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
theorem transfer_of_ears [Infinite γ] {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
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
theorem finite_transfer_toward_square [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
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

/-- **The crosscut of a 2-cell, from the accessibility of its two endpoints.**

Two distinct points of a curve `J` bounding an open connected set `F`, each polygonally
accessible from `F`, are joined by a simple polygonal arc lying in `F` apart from its two
endpoints and meeting `J` exactly there. This is `lem:accessible-endpoints` in its crosscut form
and nothing else; the accessibility is the hypothesis.

**Where the accessibility comes from is what separates the two directions of
`thm:finite-transfer`.** On the target side it is `lem:polygonal-side-accessibility` applied to a
graph all of whose edges are polygonal (`Schoenflies.exists_target_crosscut` below). On the
source side no such graph exists — the outer edges are subarcs of the wild curve — and the two
halves of the argument are `Realization.polyAccessible_of_notMem_outer` at a point off `C` and
`Schoenflies.polyAccessible_of_stronglyAccessible` at one on it. Keeping the accessibility a
hypothesis is what lets both directions share this theorem. -/
theorem exists_crosscut_of_accessible_ends (hopen : IsOpen F) (hconn : IsPreconnected F)
    (hdisj : Disjoint F J) (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hav : PolyAccessible F v) (haw : PolyAccessible F w) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P v w ∧ P \ {v, w} ⊆ F ∧ P ∩ J = {v, w} := by
  obtain ⟨ws, -, -, -, hsub, harc, hmeet⟩ :=
    exists_crosscut_of_polyAccessible hopen hconn hdisj hvw hvJ hwJ hav haw
  exact ⟨poly ws, ⟨ws, rfl⟩, harc, hsub, hmeet⟩

/-- **The crosscut splits the 2-cell into exactly two Jordan regions.** By
`lem:cellulation-invariants`(vii) the 2-cell `F` is the bounded complementary region of the
Jordan curve `J` realizing its boundary walk; the crosscut of
`Schoenflies.exists_crosscut_of_accessible_ends` is then a crosscut of `J` in the sense of
`thm:general-crosscut`, which decomposes `F` into the two Jordan regions bounded by the crosscut
together with the two boundary paths.

The conclusion is returned in the shape assertion (i) consumes at a 2-cell split
(`Schoenflies.crosscut_cell_partition`): the old open 2-cell is the disjoint union of the two new
open 2-cells and the open crosscut, each new 2-cell is open and nonempty, and the closure of each
is that open 2-cell together with its own boundary curve. -/
theorem exists_crosscut_split_of_accessible_ends (hopen : IsOpen F) (hconn : IsPreconnected F)
    (hdisj : Disjoint F J) (hJc : IsJordanCurve J) (hFJ : F = inside J)
    (hvw : v ≠ w) (hvJ : v ∈ J) (hwJ : w ∈ J)
    (hav : PolyAccessible F v) (haw : PolyAccessible F w) (hcut : IsCutPair J v w A₁ A₂) :
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
    exists_crosscut_of_accessible_ends hopen hconn hdisj hvw hvJ hwJ hav haw
  have hcross : IsCrosscut J P v w :=
    ⟨hJc, hParc, hPpoly, hvJ, hwJ, by rw [← hFJ]; exact hPsub⟩
  have hpart := crosscut_cell_partition (fun _ hS => jordan_curve_theorem hS) hcross hcut
    hcross.hasArcCollars
  exact ⟨P, hPpoly, hParc, hPsub, hPmeet, hcross, by rw [hFJ]; exact hpart.1, hpart.2.1,
    hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1,
    hpart.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.1, hpart.2.2.2.2.2.2.2.2.2⟩

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
  obtain ⟨hopen, hconn, hdisj⟩ := isOpen_isPreconnected_disjoint_of_target_cell h hQ hcell hF
  exact exists_crosscut_of_accessible_ends hopen hconn (hdisj.mono_right hJ) hvw hvJ hwJ
    (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hv)
    (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hw)

/-- **Step 4 in full, on the target side**: the crosscut of
`Schoenflies.exists_target_crosscut` splits the target face into exactly two Jordan regions.
`Schoenflies.exists_crosscut_split_of_accessible_ends` with the accessibility supplied by
`lem:polygonal-side-accessibility`, which is available on the target side because every target
edge is polygonal. -/
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
  obtain ⟨hopen, hconn, hdisj⟩ := isOpen_isPreconnected_disjoint_of_target_cell h hQ hcell hF
  exact exists_crosscut_split_of_accessible_ends hopen hconn (hdisj.mono_right hJ) hJc hFJ hvw
    hvJ hwJ (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hv)
    (Graph.polygonal_side_accessibility_target h hpoly hQ hQK hcell hF hw) hcut

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
  have := h₂.subset_closure (S.mem_cells_of_mem_vertexSet ha) (S.mem_cells_of_mem_faces hF)
    (h₁.sub_of_pos_mem_closure_cell ha hF hmem)
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

/-! ### Step 1: the overlay

*By `lem:polygonal-overlay`, using the convention of `rem:polygonal-overlay-convention`, first
overlay the proposed polygonal nonboundary edges with the old polygonal nonboundary skeleton and
subdivide at all intersections.*

`Schoenflies.polygonal_overlay` does that for a **list of segments**. What step 1 has instead is
a finite family of polygonal *arcs* — the old nonboundary edges and the proposed new ones — so
the two have to be bridged. `Schoenflies.exists_overlay_of_biUnion_finite` is that bridge, and it
is the half of step 1 that is proved here: the union of finitely many nondegenerate polygonal
sets is the point set of a finite plane graph drawn by straight segments, whose vertices are the
ends of the subdivided pieces and therefore include every intersection point.

The nondegeneracy hypothesis is necessary, not cosmetic: a one-point set is polygonal
(`poly [a] = {a}`) and is not the point set of any overlay graph, whose vertices are the ends of
nondegenerate segments.

What remains of step 1 — that the *old skeleton* is literally a subgraph of the overlay on both
sides, which needs each new subdivision point carried through the chosen edge parametrization to
the other realization — is `Schoenflies.CommonSubdivision`, assumed. -/

/-- **`lem:polygonal-overlay` for a finite family of polygonal sets.** The union of finitely many
nondegenerate polygonal sets is the point set of a finite plane graph whose edges are straight
segments — the overlay, subdivided at every intersection.

This is the first half of step 1 of the proof of `thm:finite-transfer`. -/
theorem exists_overlay_of_biUnion_finite {ι : Type*} {s : Set ι} {A : ι → Set Plane}
    (hs : s.Finite) (hA : ∀ i ∈ s, IsPolygonal (A i))
    (hnd : ∀ i ∈ s, ∃ a ∈ A i, ∃ b ∈ A i, a ≠ b) :
    ∃ G : Graph Plane Piece, Graph.Finite G ∧ IsDrawing G segmentDrawing ∧
      pointSet G segmentDrawing = ⋃ i ∈ s, A i := by
  classical
  -- A vertex list for each member of the family, chosen once and for all.
  have hex : ∀ i : ι, ∃ ws : List Plane, i ∈ s → A i = poly ws := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨ws, hws⟩ := hA i hi
      exact ⟨ws, fun _ => hws⟩
    · exact ⟨[], fun h => absurd h hi⟩
  choose vsf hvsf using hex
  -- Enumerate the index set; the enumeration only feeds the list-indexed overlay.
  set l : List ι := hs.toFinset.toList with hl
  have hlmem : ∀ i, i ∈ l ↔ i ∈ s := by
    intro i; rw [hl, Finset.mem_toList, hs.mem_toFinset]
  -- A nondegenerate polygonal set is exactly what its own segments occupy.
  have hAcov : ∀ i ∈ s, cover (segsOf (vsf i)) = A i := by
    intro i hi
    obtain ⟨a, ha, b, hb, hab⟩ := hnd i hi
    rw [hvsf i hi] at ha hb ⊢
    exact cover_segsOf_eq ha hb hab
  have hcov : cover (l.flatMap fun i => segsOf (vsf i)) = ⋃ i ∈ s, A i := by
    rw [cover_flatMap_list]
    exact Set.iUnion_congr fun i => Set.iUnion_congr_Prop (hlmem i) fun hi => hAcov i hi
  have hnd' : ∀ P ∈ l.flatMap fun i => segsOf (vsf i), P.Nondeg := by
    intro P hP
    obtain ⟨i, -, hPi⟩ := List.mem_flatMap.1 hP
    exact segsOf_nondeg _ P hPi
  obtain ⟨G, hfin, hdraw, hpt⟩ := polygonal_overlay _ hnd'
  exact ⟨G, hfin, hdraw, by rw [hpt, hcov]⟩

/-! ### The interface, exercised

`thm:finite-transfer` exists to feed the recursion of the quantitative-refinement section, which
consumes a transfer only through `Realization.Refines`. This anonymous example is a
machine-checked statement that the conclusion of `finite_transfer_toward_square` delivers exactly
what that recursion reads: the source carrier refines (`lem:refinement-compatibility`(a)), the
same parent map serves both sides (part (c)), and the closed target star of a fixed source point
shrinks (`T_{n+1}(x) \subseteq T_n(x)`).

Nothing below mentions how the transfer was built. If a later change to `IsTransferOf` stopped
serving that recursion, this would break. -/
example [Nonempty γ] {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}
    (h₀ : S₀.CombInvariants) (P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTransferOf T P H Hdraw par) {x : Plane} (hx : x ∈ srcDom) :
    par (T.src.carrier x) = P.src.carrier x ∧
      T.tgt.star (T.src.carrier x) ⊆ P.tgt.star (P.src.carrier x) :=
  ⟨hT.refines_src.parent_carrier P.src_isCellDecomposition T.src_isCellDecomposition hx,
    hT.refines_src.target_star_subset hT.refines_tgt (T.combInvariants h₀)
      P.src_isCellDecomposition T.src_isCellDecomposition hx⟩

end Schoenflies
