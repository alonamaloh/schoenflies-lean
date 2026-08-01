/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.RefinementStars
import Schoenflies.Inversion

/-!
# The limit homeomorphism of the interiors

The blueprint opens this section with a sentence that is an instruction to the formalizer: "We
now forget how the decompositions were constructed and use only their nesting, matching, and
shrinking properties." This module takes it literally. `LimitTower` is a structure recording
exactly those properties — a sequence of matched cell structures with two realizations each, a
`Realization.Refines` instance between consecutive stages on each side sharing one parent map,
nested skeleton homeomorphisms, and the two shrinking hypotheses of `prop:shrinking-stars` — and
everything from the definition of `F` to `prop:interior-homeomorphism` is proved against it.
Nothing below mentions a mesh, a grid, or a constructor. The still-open construction has to
produce one `LimitTower`; none of the analysis waits for it.

## What is *not* a field

Three things the task list expected to appear as hypotheses turned out to be derivable and are
therefore proved here rather than assumed.

* **`lem:outer-incidence`.** `docs/ROADMAP.md` records it as done in `CombinatorialInvariance.lean`
  under `outerEdge_face_corresponds`; that is a different statement (assertion (vi) of
  `lem:cellulation-invariants`, transported). The real `lem:outer-incidence` — `closure σ` meets
  `C` iff some outer cell is a subcell of `σ` iff `closure σ'` meets `S` — is proved below as
  `Realization.IsCellDecomposition.closure_cell_meets_outer_iff` and, for stars,
  `LimitTower.srcStar_disjoint_bdry_of_tgtStar`. The one geometric input it needs is
  `Realization.outerSet_eq_iUnion_cell`: the realized outer cycle is exactly the union of the
  open cells of the outer cells, which is a consequence of the two `Realization` clauses
  `cell_vertex` and `cell_edge` and holds for any subcomplex.
* **Assertion (vii) of `lem:cellulation-invariants`** (every 2-cell boundary a Jordan curve with
  the open cell its bounded region). The limit argument was expected to need it, through
  assertion (viii). It does not: the only use is "a 2-cell is not a proper subcell of a 2-cell",
  and that is `CombInvariants.face_maximal`, which is already an inductive invariant on `main`.
  There is therefore no field for (vii) and no dependency on it.
* **`prop:target-skeleton-dense`.** The blueprint's surjectivity proof goes through the density
  of the target skeleton and a compactness argument in `C ∪ D`. That is not needed: the sets
  `⋂ₙ St_{Γₙ}(car_{Γ'ₙ}(y))` — the *source* stars of the *target* carriers of `y` — are a nested
  sequence of nonempty compacts, and any point of their intersection is already a preimage of
  `y`. `prop:target-skeleton-dense` is proved anyway, because the boundary-continuity module
  cites it, but it is not on the critical path to `prop:F-surjective`.

## The two shrinking hypotheses are not symmetric

`prop:shrinking-stars` gives *pointwise* convergence of the source star diameters and *uniform*
convergence of the target ones. The asymmetry is real and is used: `F` is defined, and continuous,
on the whole closed domain (only the uniform bound enters), whereas injectivity and the continuity
of the inverse hold on the open region (they need the pointwise bound at a point of `D`).

One hypothesis that the blueprint does not state is carried throughout: the closed domains are
bounded. It is not optional — `Metric.diam` is `0` on an unbounded set, so without it the star
diameter bounds are false rather than weak — and it is trivially true for a closed Jordan domain.

## Blueprint

* `Schoenflies.CellStructure.LimitTower` — the abstraction of the head of the section: "we now
  forget how the decompositions were constructed".
* `Schoenflies.CellStructure.LimitTower.F` — the limit map, with
  `…iInter_tgtStar_eq_singleton` (`lem:nested-compact` applied to the nested stars) and
  `…F_mem_tgtStar` its characterisation.
* `lem:outer-incidence` —
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.closure_cell_meets_outer_iff`,
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.star_meets_outer_iff`, and their
  matched form `Schoenflies.CellStructure.LimitTower.srcStar_disjoint_bdry_of_tgtStar`.
* `prop:skeleton-agreement` — `Schoenflies.CellStructure.LimitTower.F_eq_skelHomeo`.
* `prop:F-continuous` — `Schoenflies.CellStructure.LimitTower.continuousOn_F` (on the *closed*
  domain).
* `prop:image-interior` — `Schoenflies.CellStructure.LimitTower.F_mem_region'`.
* `prop:F-injective` — `Schoenflies.CellStructure.LimitTower.injOn_F`.
* `prop:target-skeleton-dense` — `Schoenflies.CellStructure.LimitTower.tgtSkeleton_dense`.
* `prop:F-surjective` — `Schoenflies.CellStructure.LimitTower.surjOn_F`.
* `lem:exact-cell-correspondence` — `Schoenflies.CellStructure.LimitTower.image_cell`, with the
  corollary the inverse argument actually uses,
  `Schoenflies.CellStructure.LimitTower.tgt_carrier_F`.
* `prop:inverse-continuous` — `Schoenflies.CellStructure.LimitTower.continuousOn_inv`.
* `prop:interior-homeomorphism` — `Schoenflies.CellStructure.LimitTower.isHomeoOn_F`, in the
  `Schoenflies.IsHomeoOn` shape that `Endgame.lean` consumes.
-/

open Set Metric Bornology Filter
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ### The realized skeleton and outer cycle, cell by cell

`Realization.skeletonSet` and `Realization.outerSet` are defined as point sets of drawn graphs.
The limit argument needs them as unions of *open cells*, because that is the form in which they
interact with `IsCellDecomposition`: "the carrier of any point of `C` is an outer cell" is the
first sentence of the blueprint's proof of `lem:outer-incidence`, and it is exactly this
rewriting. -/

namespace Realization

variable (R : S.Realization)

/-- The realized point set of a subcomplex of the skeleton is the union of the open cells of its
0- and 1-cells. A drawn edge is its open cell together with the two 0-cells at its ends, and
those ends belong to the subcomplex whenever the edge does. -/
theorem pointSet_map_eq_iUnion_cell {H : Graph γ γ} (hH : H ≤ S.skel) :
    Graph.pointSet (H.map R.pos) R.drawing = ⋃ κ ∈ V(H) ∪ E(H), R.cell κ := by
  refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun κ hκ => ?_)
  · rcases hz with hz | hz
    · -- a drawn 0-cell
      rw [Graph.vertexSet_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact Set.mem_biUnion (Or.inl hv)
        (by rw [R.cell_vertex (hH.vertexSet_mono hv)]; rfl)
    · -- a point of a drawn 1-cell: either interior to it, or one of its two ends
      rw [Graph.edgeSet_map] at hz
      obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
      obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      by_cases hend : z ∈ ({R.pos a, R.pos b} : Set Plane)
      · rcases hend with rfl | rfl
        · exact Set.mem_biUnion (Or.inl hl.left_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.left_mem)]; rfl)
        · exact Set.mem_biUnion (Or.inl hl.right_mem)
            (by rw [R.cell_vertex (hH.vertexSet_mono hl.right_mem)]; rfl)
      · exact Set.mem_biUnion (Or.inr he) (by rw [R.cell_edge (hl.mono hH)]; exact ⟨hze, hend⟩)
  · rcases hκ with hv | he
    · rw [R.cell_vertex (hH.vertexSet_mono hv)]
      exact Set.singleton_subset_iff.2 (Graph.vertexSet_subset_pointSet
        (by rw [Graph.vertexSet_map]; exact ⟨κ, hv, rfl⟩))
    · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      rw [R.cell_edge (hl.mono hH)]
      exact Set.Subset.trans Set.sdiff_subset
        (Graph.edgeArc_subset_pointSet (by rw [Graph.edgeSet_map]; exact he))

/-- **The realized 1-skeleton is the union of the open 0- and 1-cells.** -/
theorem skeletonSet_eq_iUnion_cell :
    R.skeletonSet = ⋃ κ ∈ V(S.skel) ∪ E(S.skel), R.cell κ :=
  R.pointSet_map_eq_iUnion_cell le_rfl

/-- **The realized outer cycle is the union of the open outer cells.** This is the sentence "`C`
is exactly the union of the outer vertices and the open outer edges" at the head of the
blueprint's proof of `lem:outer-incidence`. -/
theorem outerSet_eq_iUnion_cell : R.outerSet = ⋃ κ ∈ S.outerCells, R.cell κ :=
  R.pointSet_map_eq_iUnion_cell S.outerGraph_le

variable {R}

theorem outerCells_subset_cells : S.outerCells ⊆ S.cells := by
  rintro κ (hv | he)
  · exact S.mem_cells_of_mem_vertexSet (S.outerGraph_le.vertexSet_mono hv)
  · exact S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono he)

theorem cell_subset_skeletonSet {κ : γ} (hκ : κ ∈ V(S.skel) ∪ E(S.skel)) :
    R.cell κ ⊆ R.skeletonSet := by
  rw [R.skeletonSet_eq_iUnion_cell]; exact Set.subset_biUnion_of_mem hκ

theorem cell_subset_outerSet {κ : γ} (hκ : κ ∈ S.outerCells) : R.cell κ ⊆ R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell]; exact Set.subset_biUnion_of_mem hκ

/-- A cell that is neither a 0-cell nor a 1-cell of the skeleton is a 2-cell — the three
collections exhaust `cells`. -/
theorem mem_faces_of_notMem_skel {σ : γ} (hσ : σ ∈ S.cells) (h : σ ∉ V(S.skel) ∪ E(S.skel)) :
    σ ∈ S.faces := by
  rcases hσ with hσ | hσ
  · exact absurd hσ h
  · exact hσ

/-- A 2-cell is never an outer cell: outer cells are 0- and 1-cells of the skeleton. -/
theorem notMem_outerCells_of_mem_faces {F : γ} (hF : F ∈ S.faces) : F ∉ S.outerCells := by
  rintro (hv | he)
  · exact S.faces_ne_vertexSet hF (S.outerGraph_le.vertexSet_mono hv) rfl
  · exact S.faces_ne_edgeSet hF (S.outerGraph_le.edgeSet_mono he) rfl

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ : γ} {x : Plane}

/-- Off the outer cycle, the open cell of a cell that is not an outer cell. Open cells are
disjoint and the outer cycle is the union of the outer ones, so a cell's open part misses the
outer cycle exactly when the cell is not outer. -/
theorem cell_disjoint_outerSet (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hout : σ ∉ S.outerCells) : Disjoint (R.cell σ) R.outerSet := by
  rw [R.outerSet_eq_iUnion_cell, Set.disjoint_iUnion₂_right]
  intro κ hκ
  exact h.disjoint hσ (outerCells_subset_cells hκ) (fun hcon => hout (hcon ▸ hκ))

/-- The carrier of a point of the realized outer cycle is an outer cell. -/
theorem carrier_mem_outerCells [Nonempty γ] (h : R.IsCellDecomposition D)
    (hx : x ∈ R.outerSet) : R.carrier x ∈ S.outerCells := by
  rw [R.outerSet_eq_iUnion_cell] at hx
  obtain ⟨κ, hκ, hxκ⟩ := Set.mem_iUnion₂.1 hx
  rwa [h.carrier_eq (outerCells_subset_cells hκ) hxκ]

/-- **`lem:outer-incidence`**, the closed-cell form: a closed cell meets the realized outer cycle
exactly when some outer cell is one of its subcells. The middle condition is a statement of the
abstract structure alone, which is what makes the equivalence transfer between the two
realizations with nothing to transport. -/
theorem closure_cell_meets_outer_iff (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    (closure (R.cell τ) ∩ R.outerSet).Nonempty ↔ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpτ, hpout⟩
    rw [R.outerSet_eq_iUnion_cell] at hpout
    obtain ⟨κ, hκ, hpκ⟩ := Set.mem_iUnion₂.1 hpout
    exact ⟨κ, hκ, h.sub_of_mem (outerCells_subset_cells hκ) hτ hpκ hpτ⟩
  · rintro ⟨κ, hκ, hsub⟩
    obtain ⟨z, hz⟩ := h.nonempty (outerCells_subset_cells hκ)
    exact ⟨z, h.subset_closure (outerCells_subset_cells hκ) hτ hsub hz, cell_subset_outerSet hκ hz⟩

/-- **`lem:outer-incidence`**, the star form: a closed star meets the realized outer cycle
exactly when some supercell of the cell has an outer subcell. -/
theorem star_meets_outer_iff (h : R.IsCellDecomposition D)
    (hS : S.CombInvariants) (σ : γ) :
    (R.star σ ∩ R.outerSet).Nonempty ↔ ∃ τ, S.sub σ τ ∧ ∃ κ ∈ S.outerCells, S.sub κ τ := by
  constructor
  · rintro ⟨p, hpstar, hpout⟩
    obtain ⟨τ, hτ, hpτ⟩ := mem_star_iff.1 hpstar
    exact ⟨τ, hτ, (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).1 ⟨p, hpτ, hpout⟩⟩
  · rintro ⟨τ, hτ, hex⟩
    obtain ⟨p, hpτ, hpout⟩ := (h.closure_cell_meets_outer_iff (hS.sub_mem_right hτ)).2 hex
    exact ⟨p, closure_cell_subset_star hτ hpτ, hpout⟩

end IsCellDecomposition

end Realization

/-! ### The tower of matched cellulations

Every field below is an obligation on whoever eventually constructs the sequence of
decompositions, and there is nothing here that the limit argument does not use. -/

/-- **The nesting, matching and shrinking properties of a sequence of matched cellulations**, and
nothing else. The blueprint's "we now forget how the decompositions were constructed" is this
structure.

`str n` is the stage-`n` abstract matched cell structure; `src n` and `tgt n` are its two
realizations, in the closed Jordan domain `dom` and in the closed square `dom'`; `skelHomeo n` is
the stage-`n` skeleton homeomorphism `g_n`. Consecutive stages are related by a pair of
`Realization.Refines` instances **sharing one parent map** `par n` — that sharing is
`lem:refinement-compatibility`(c), "corresponding cells have corresponding parents", under the
representation of `CombinatorialInvariance.lean`, where cells are abstract names.

The shrinking clauses are `prop:shrinking-stars`, and they are deliberately asymmetric, exactly
as the blueprint states them: the *target* star diameters are bounded uniformly by a null
sequence `eps`, while the *source* star diameters are only assumed to tend to zero pointwise, and
only at points of the open region. -/
structure LimitTower (γ : Type*) [Nonempty γ] where
  /-- The stage-`n` abstract matched cell structure. -/
  str : ℕ → CellStructure γ
  /-- The source realization, in the closed Jordan domain. -/
  src : ∀ n, (str n).Realization
  /-- The target realization, in the closed square. -/
  tgt : ∀ n, (str n).Realization
  /-- The stage-`n` skeleton homeomorphism `g_n`. -/
  skelHomeo : ∀ n, SkeletonHomeo (src n) (tgt n)
  /-- The composite parent map from stage `n + 1` to stage `n`, shared by the two sides. -/
  par : ℕ → γ → γ
  /-- The closed source domain `C ∪ D`. -/
  dom : Set Plane
  /-- The source outer curve `C`. -/
  bdry : Set Plane
  /-- The closed target domain `Q`. -/
  dom' : Set Plane
  /-- The target outer curve `S`. -/
  bdry' : Set Plane
  /-- The uniform target mesh: `2 ε_n` of the blueprint. -/
  eps : ℕ → ℝ
  /-- **Assertions (i) and (ii)** on the source side. -/
  srcDecomp : ∀ n, (src n).IsCellDecomposition dom
  /-- **Assertions (i) and (ii)** on the target side. -/
  tgtDecomp : ∀ n, (tgt n).IsCellDecomposition dom'
  /-- **Assertions (iii), (v), (vi)** and the rest of the combinatorial invariants. -/
  comb : ∀ n, (str n).CombInvariants
  /-- Consecutive source stages refine, along `par n`. -/
  srcRefines : ∀ n, (src (n + 1)).Refines (src n) (par n)
  /-- Consecutive target stages refine, along the *same* `par n`. -/
  tgtRefines : ∀ n, (tgt (n + 1)).Refines (tgt n) (par n)
  /-- The realized source outer cycle is `C`, at every stage. -/
  srcOuterSet : ∀ n, (src n).outerSet = bdry
  /-- The realized target outer cycle is `S`, at every stage. -/
  tgtOuterSet : ∀ n, (tgt n).outerSet = bdry'
  /-- `C ∪ D` is closed. -/
  isClosed_dom : IsClosed dom
  /-- `Q` is closed. -/
  isClosed_dom' : IsClosed dom'
  /-- `C ∪ D` is bounded. Not in the blueprint, and not optional: `Metric.diam` is `0` on an
  unbounded set. -/
  isBounded_dom : IsBounded dom
  /-- `Q` is bounded, for the same reason. -/
  isBounded_dom' : IsBounded dom'
  /-- `D = Int(C)` is open. -/
  isOpen_region : IsOpen (dom \ bdry)
  /-- `Q°` is open. -/
  isOpen_region' : IsOpen (dom' \ bdry')
  /-- The realized source skeletons grow. -/
  skeletonSet_mono : ∀ n, (src n).skeletonSet ⊆ (src (n + 1)).skeletonSet
  /-- **The skeleton maps are nested**: "an edge subdivision leaves the skeleton map unchanged as
  a point map, and a 2-cell split extends it by the chosen homeomorphism on the new ear". -/
  skelHomeo_succ : ∀ n,
    Set.EqOn (skelHomeo (n + 1)).toFun (skelHomeo n).toFun (src n).skeletonSet
  /-- **`prop:shrinking-stars`, the uniform half**: every stage-`n` target star has diameter at
  most `eps n`. -/
  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (str n).cells → diam ((tgt n).star σ) ≤ eps n
  /-- …and `eps` is a null sequence. -/
  tendsto_eps : Tendsto eps atTop (nhds 0)
  /-- **`prop:shrinking-stars`, the pointwise half**: at every point of the open region the
  source star diameters tend to zero. -/
  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ dom \ bdry →
    Tendsto (fun n => diam ((src n).star ((src n).carrier x))) atTop (nhds 0)

namespace LimitTower

variable [Nonempty γ] (L : LimitTower γ) {x y z : Plane} {m n : ℕ} {σ : γ}

/-- The open source region `D = Int(C)`. -/
def region : Set Plane := L.dom \ L.bdry

/-- The open target region `Q°`. -/
def region' : Set Plane := L.dom' \ L.bdry'

/-- `St_{Γ'_n}(σ'_n(x))`, written `T_n(x)` in the blueprint: the closed target star of the cell
corresponding to the source carrier of `x`. -/
def tgtStar (n : ℕ) (x : Plane) : Set Plane := (L.tgt n).star ((L.src n).carrier x)

/-- `St_{Γ_n}(x)`, the closed source star of the source carrier of `x`. -/
def srcStar (n : ℕ) (x : Plane) : Set Plane := (L.src n).star ((L.src n).carrier x)

variable {L}

theorem region_subset_dom : L.region ⊆ L.dom := Set.sdiff_subset

theorem region'_subset_dom' : L.region' ⊆ L.dom' := Set.sdiff_subset

/-! #### Stars of the tower -/

theorem srcStar_subset_dom (n : ℕ) (σ : γ) : (L.src n).star σ ⊆ L.dom :=
  ((L.srcDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom.closure_subset

theorem tgtStar_subset_dom' (n : ℕ) (σ : γ) : (L.tgt n).star σ ⊆ L.dom' :=
  ((L.tgtDecomp n).star_subset_closure_domain (L.comb n)).trans L.isClosed_dom'.closure_subset

theorem isBounded_tgt_star (n : ℕ) (σ : γ) : IsBounded ((L.tgt n).star σ) :=
  (L.tgtDecomp n).isBounded_star (L.comb n) L.isBounded_dom'

theorem isBounded_src_star (n : ℕ) (σ : γ) : IsBounded ((L.src n).star σ) :=
  (L.srcDecomp n).isBounded_star (L.comb n) L.isBounded_dom

theorem mem_srcStar_self (hx : x ∈ L.dom) (n : ℕ) : x ∈ L.srcStar n x :=
  (L.srcDecomp n).mem_star_carrier hx

/-- **`lem:refinement-compatibility`(b)** at a point: `T_{n+1}(x) ⊆ T_n(x)`. -/
theorem tgtStar_succ_subset (hx : x ∈ L.dom) (n : ℕ) : L.tgtStar (n + 1) x ⊆ L.tgtStar n x :=
  (L.srcRefines n).target_star_subset (L.tgtRefines n) (L.comb (n + 1)) (L.srcDecomp n)
    (L.srcDecomp (n + 1)) hx

theorem tgtStar_antitone (hx : x ∈ L.dom) : Antitone (fun n => L.tgtStar n x) :=
  antitone_nat_of_succ_le (L.tgtStar_succ_subset hx)

theorem tgtStar_nonempty (hx : x ∈ L.dom) (n : ℕ) : (L.tgtStar n x).Nonempty :=
  (L.tgtDecomp n).star_nonempty ((L.srcDecomp n).mem_cells_carrier hx)

theorem isCompact_tgtStar (n : ℕ) (x : Plane) : IsCompact (L.tgtStar n x) :=
  (L.tgtDecomp n).isCompact_star (L.comb n) L.isBounded_dom'

theorem diam_tgtStar (hx : x ∈ L.dom) (n : ℕ) : diam (L.tgtStar n x) ≤ L.eps n :=
  L.diam_tgtStar_le n ((L.srcDecomp n).mem_cells_carrier hx)

theorem tendsto_diam_tgtStar (hx : x ∈ L.dom) :
    Tendsto (fun n => diam (L.tgtStar n x)) atTop (nhds 0) :=
  squeeze_zero (fun _ => diam_nonneg) (L.diam_tgtStar hx) L.tendsto_eps

/-! #### The limit map -/

theorem exists_eq_singleton_iInter_tgtStar (hx : x ∈ L.dom) :
    ∃ p, ⋂ n, L.tgtStar n x = {p} :=
  Plane.eq_singleton_iInter_of_diam_tendsto_zero (L.tgtStar_nonempty hx)
    (fun n => L.isCompact_tgtStar n x) (L.tgtStar_antitone hx) (L.tendsto_diam_tgtStar hx)

open scoped Classical in
/-- **The limit map `F`**: the unique point of `⋂ₙ T_n(x)`. Junk off the closed domain; every
lemma about it carries `x ∈ L.dom`. -/
noncomputable def F (L : LimitTower γ) (x : Plane) : Plane :=
  if h : ∃ p, ⋂ n, L.tgtStar n x = {p} then h.choose else 0

/-- **The characterising property of `F`.** -/
theorem iInter_tgtStar_eq (hx : x ∈ L.dom) : ⋂ n, L.tgtStar n x = {L.F x} := by
  rw [F, dif_pos (L.exists_eq_singleton_iInter_tgtStar hx)]
  exact (L.exists_eq_singleton_iInter_tgtStar hx).choose_spec

theorem F_mem_iInter (hx : x ∈ L.dom) : L.F x ∈ ⋂ n, L.tgtStar n x := by
  rw [L.iInter_tgtStar_eq hx]
  exact rfl

theorem F_mem_tgtStar (hx : x ∈ L.dom) (n : ℕ) : L.F x ∈ L.tgtStar n x :=
  Set.mem_iInter.1 (L.F_mem_iInter hx) n

/-- Uniqueness: anything in every `T_n(x)` is `F x`. -/
theorem eq_F_of_mem_iInter (hx : x ∈ L.dom) (hz : ∀ n, z ∈ L.tgtStar n x) : z = L.F x := by
  have : z ∈ ⋂ n, L.tgtStar n x := Set.mem_iInter.2 hz
  rwa [L.iInter_tgtStar_eq hx, Set.mem_singleton_iff] at this

theorem F_mem_dom' (hx : x ∈ L.dom) : L.F x ∈ L.dom' :=
  tgtStar_subset_dom' 0 _ (L.F_mem_tgtStar hx 0)

/-- `F x` is within `eps n` of anything in the stage-`n` target star of `x`. -/
theorem dist_F_le_of_mem_tgtStar (hx : x ∈ L.dom) (hz : z ∈ L.tgtStar n x) :
    dist (L.F x) z ≤ L.eps n :=
  le_trans (dist_le_diam_of_mem (isBounded_tgt_star n _) (L.F_mem_tgtStar hx n) hz)
    (L.diam_tgtStar hx n)

end LimitTower

end CellStructure

end Schoenflies
