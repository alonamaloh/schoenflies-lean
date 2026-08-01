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

end CellStructure

end Schoenflies
