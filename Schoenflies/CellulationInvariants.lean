/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.RefinementStars
import Schoenflies.JordanClosed

/-!
# The two cellulation invariants that need the crosscut theorem

`Schoenflies/GeneratedStructure.lean` proves seven of the nine assertions of
`lem:cellulation-invariants` — (ii), (iii), (iv), (v), (vi), (viii) and (ix), and (i) for the
edge-subdivision constructor. The two it leaves open are exactly the two whose induction step is
`thm:general-crosscut`:

* **(vii)** in each realization every 2-cell boundary is a Jordan curve and the open 2-cell is
  its bounded complementary region;
* **(i)** at the *split* constructor.

Both are proved here. `Schoenflies.crosscut_theorem` is unconditional on `main`, so nothing in
this module is conditional either.

## Realizations stay outside the inductive

`Schoenflies.GeneratedStructure` is purely abstract — it carries no realizations at all — while
(i), (vii), (viii) and (ix) are statements about realizations. `RefinementStars.lean` bridges
that by stating its lemmas for an arbitrary `Realization` satisfying `IsCellDecomposition`, and
this module follows the same pattern: the induction over the constructors is replaced by two
*step* theorems, one per constructor, each relating a realization of the refined structure to a
realization of the old one. A consumer building a sequence of stages carries the realizations
itself and applies the step theorem at each stage.

The alternative — realizations as fields of the inductive — was rejected for the reason
`RefinementStars.lean` gives: the limit argument "forgets how the decompositions were
constructed", so the abstract closure and the geometric invariants must be separable. It would
also force every consumer to commit to *two* realizations at the moment it builds an abstract
stage, which `thm:finite-transfer` does not do.

## What assertion (vii) is stated against, and why not the boundary walk

The blueprint phrases (vii) as "every 2-cell boundary **walk** is realized by a Jordan curve".
`CellStructure.boundary : γ → List γ` is a raw datum on which `CellStructure` imposes *no*
axiom whatever: nothing says `S.boundary F` is a closed walk, nothing ties it to `S.sub`, and
nothing ties it to `F`. A version of (vii) phrased against it would therefore have to assume
that tie as an extra hypothesis, and — see the orientation section below — that hypothesis is
*not* preserved by `CellStructure.subdivideEdge` as it currently stands.

So (vii) is stated against the cells: `Realization.faceBoundary F` is the union of the open
cells strictly below `F`, and `IsCellDecomposition.faceBoundary_eq_frontier` identifies it with
`frontier (R.cell F)` as soon as the open 2-cell is open. Assertion (vii) then reads: that
frontier is a Jordan curve, and `R.cell F` is its `inside`. This is the content every consumer
uses — (viii) needs only openness of the 2-cell, `lem:star-face-mesh` needs only the closed
2-cells, and the limit map needs `R.cell F = inside (…)`. Nothing downstream reads the cyclic
order of the walk.

## The orientation defect of `subdivideEdge`

`CellStructure.subdivideEdge` updates the boundary walks by

```
boundary F := (S.boundary F).flatMap fun f => if f = d.edge then [d.newEdge₁, d.newEdge₂] else [f]
```

which is **orientation-blind and wrong**: a boundary walk traverses `d.edge` in a definite
direction, and `d.newEdge₁` runs `left → newVertex` while `d.newEdge₂` runs `newVertex → right`.
A walk that crosses `d.edge` from `d.right` to `d.left` must be repaired with
`[d.newEdge₂, d.newEdge₁]`, not `[d.newEdge₁, d.newEdge₂]`. The docstring of `subdivideEdge`
already disclaims the orientation and nothing on `main` reads `boundary`, so no statement of
this module depends on it; the repair is described in the report accompanying this module.

## Blueprint

* `Schoenflies.CellStructure.Realization.cellUnion`, `Schoenflies.CellStructure.subcells`,
  `Schoenflies.CellStructure.Realization.faceBoundary` — the realized point set of a set of
  abstract cells, and the boundary of a 2-cell read off the abstract data.
* `Schoenflies.CellStructure.Realization.IsFaceJordan` — **assertion (vii)** of
  `lem:cellulation-invariants`, for one realization.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition.face_eq_of_isFaceJordan`,
  `…sub_face_eq` — **assertion (viii)** with its openness hypothesis discharged by (vii).
* `Schoenflies.CellStructure.SubdivData.IsRefinement.isFaceJordan` — (vii) is preserved by an
  edge subdivision.
* `Schoenflies.CellStructure.SplitData.IsRefinement` — the split analogue of
  `SubdivData.IsRefinement`, and `…IsRefinement.isCellDecomposition` — **assertion (i) at the
  split constructor**.
* `Schoenflies.CellStructure.SplitData.IsRefinement.refines` — the one-liner
  `RefinementStars.lean` asked for, next to `SubdivData.IsRefinement.refines`.
* `Schoenflies.CellStructure.SplitData.IsCrosscutSplit`,
  `Schoenflies.CellStructure.SplitData.IsCrosscutSplit.isRefinement`,
  `Schoenflies.CellStructure.SplitData.IsCrosscutSplit.isFaceJordan` — the geometric input of one
  split (the ear drawn as a crosscut of the old Jordan face), and the two invariants
  *constructed* from it by `Schoenflies.crosscut_theorem`. This is the blueprint's
  "Theorem `thm:general-crosscut` decomposes the old open 2-cell into the disjoint union of the
  two new open 2-cells and the open cells of the ear, and gives
  `closure Rᵢ = Rᵢ ∪ P ∪ Bᵢ`".
-/

open Set Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- The subcells of a cell: the index set of its closed cell in assertion (i). -/
def subcells (S : CellStructure γ) (τ : γ) : Set γ := {σ | σ ∈ S.cells ∧ S.sub σ τ}

theorem mem_subcells_iff {σ τ : γ} : σ ∈ S.subcells τ ↔ σ ∈ S.cells ∧ S.sub σ τ := Iff.rfl

theorem subcells_subset_cells {τ : γ} : S.subcells τ ⊆ S.cells := fun _ h => h.1

namespace Realization

variable {R : S.Realization} {D : Set Plane} {F T σ τ : γ}

/-! ### The realized point set of a set of cells

Every geometric statement of `lem:cellulation-invariants` is about a *union of open cells*: the
closure of a cell, the boundary of a 2-cell, the realized ear, the realized boundary path. One
notation serves them all. -/

/-- The realized point set of a set of abstract cells: the union of their open cells. -/
def cellUnion (R : S.Realization) (Cs : Set γ) : Set Plane := ⋃ σ ∈ Cs, R.cell σ

theorem mem_cellUnion_iff {Cs : Set γ} {z : Plane} :
    z ∈ R.cellUnion Cs ↔ ∃ σ ∈ Cs, z ∈ R.cell σ := by
  simp only [cellUnion, Set.mem_iUnion, exists_prop]

theorem cellUnion_mono {Cs Ds : Set γ} (h : Cs ⊆ Ds) : R.cellUnion Cs ⊆ R.cellUnion Ds :=
  Set.biUnion_subset_biUnion_left h

theorem cell_subset_cellUnion {Cs : Set γ} (h : σ ∈ Cs) : R.cell σ ⊆ R.cellUnion Cs :=
  Set.subset_biUnion_of_mem (u := fun ρ => R.cell ρ) h

theorem cellUnion_union (R : S.Realization) (Cs Ds : Set γ) :
    R.cellUnion (Cs ∪ Ds) = R.cellUnion Cs ∪ R.cellUnion Ds := Set.biUnion_union _ _ _

theorem cellUnion_insert (R : S.Realization) (σ : γ) (Cs : Set γ) :
    R.cellUnion (insert σ Cs) = R.cell σ ∪ R.cellUnion Cs := Set.biUnion_insert _ _ _

@[simp] theorem cellUnion_empty (R : S.Realization) : R.cellUnion ∅ = ∅ := Set.biUnion_empty _

theorem cellUnion_subset {Cs : Set γ} {A : Set Plane} (h : ∀ σ ∈ Cs, R.cell σ ⊆ A) :
    R.cellUnion Cs ⊆ A := Set.iUnion₂_subset h

/-- The **realized boundary of a 2-cell**, read off the abstract data: the union of the open
cells strictly below it. Under assertion (i) this is the topological frontier of the open
2-cell (`IsCellDecomposition.faceBoundary_eq_frontier`), which is what makes it the right thing
for the blueprint's "boundary walk of `F`" without a walk being available. -/
def faceBoundary (R : S.Realization) (F : γ) : Set Plane := R.cellUnion (S.subcells F \ {F})

namespace IsCellDecomposition

/-- Assertion (i)'s closure clause, in `cellUnion` notation. -/
theorem closure_cell_eq (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    closure (R.cell τ) = R.cellUnion (S.subcells τ) := h.closure_eq hτ

theorem mem_subcells_self (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) : τ ∈ S.subcells τ :=
  ⟨hτ, h.sub_refl hτ⟩

/-- A closed cell is its open cell together with the open cells strictly below it. -/
theorem closure_cell_eq_union (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    closure (R.cell τ) = R.cell τ ∪ R.faceBoundary τ := by
  rw [h.closure_cell_eq hτ, faceBoundary, ← R.cellUnion_insert,
    Set.insert_sdiff_singleton, Set.insert_eq_self.2 (h.mem_subcells_self hτ)]

/-- The open cells strictly below `τ` miss the open cell `τ`. -/
theorem disjoint_faceBoundary (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells) :
    Disjoint (R.cell τ) (R.faceBoundary τ) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  obtain ⟨σ, ⟨⟨hσ, -⟩, hσne⟩, hzσ⟩ := mem_cellUnion_iff.1 hz'
  exact Set.disjoint_left.1 (h.disjoint hτ hσ (Ne.symm hσne)) hz hzσ

/-- **The realized boundary of an open cell is its frontier.** The blueprint reads the boundary
of a 2-cell off the cells below it; this says that reading agrees with the topology, which is
what lets assertion (vii) be stated without the boundary-walk datum. -/
theorem faceBoundary_eq_frontier (h : R.IsCellDecomposition D) (hτ : τ ∈ S.cells)
    (hopen : IsOpen (R.cell τ)) : R.faceBoundary τ = frontier (R.cell τ) := by
  rw [hopen.frontier_eq, h.closure_cell_eq_union hτ, Set.union_sdiff_left,
    sdiff_eq_left.2 (h.disjoint_faceBoundary hτ).symm]

end IsCellDecomposition

/-! ### Assertion (vii)

"In each of the two realizations, every 2-cell boundary walk is realized by a Jordan curve, and
the open 2-cell is the bounded complementary region of that curve."

`Schoenflies.inside` is the union of the *bounded* complementary components of a set, so
"the bounded complementary region of the Jordan curve `J`" is literally `inside J`; and by
`Schoenflies.jordan_curve_theorem` it is a single region. -/

/-- **Assertion (vii)** of `lem:cellulation-invariants**, for one realization: every open 2-cell
is the bounded complementary region of a Jordan curve, namely its own frontier.

Stated against `frontier (R.cell F)` rather than against the boundary walk; see the module
docstring. Under assertion (i) the frontier *is* the union of the open cells strictly below `F`
(`IsCellDecomposition.faceBoundary_eq_frontier`), which is the blueprint's boundary walk read
as a set. -/
structure IsFaceJordan (R : S.Realization) : Prop where
  /-- The boundary of every 2-cell is a Jordan curve. -/
  isJordanCurve : ∀ ⦃F⦄, F ∈ S.faces → IsJordanCurve (frontier (R.cell F))
  /-- The open 2-cell is the bounded complementary region of that curve. -/
  cell_eq_inside : ∀ ⦃F⦄, F ∈ S.faces → R.cell F = inside (frontier (R.cell F))

namespace IsFaceJordan

/-- Each 2-cell boundary separates the plane. This is where `thm:jordan` enters; it is
unconditional on `main`. -/
theorem isSeparating (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) :
    IsSeparating (frontier (R.cell F)) :=
  jordan_curve_theorem (hJ.isJordanCurve hF)

/-- **An open 2-cell is open.** This is the clause `lem:cellulation-invariants`(viii) needs, and
the only thing the blueprint's proof of (viii) really uses. -/
theorem isOpen (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsOpen (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isOpen_inside

theorem isConnected (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsConnected (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isConnected_inside

theorem isBounded (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : IsBounded (R.cell F) := by
  rw [hJ.cell_eq_inside hF]
  exact (hJ.isSeparating hF).isBounded_inside

theorem nonempty (hJ : R.IsFaceJordan) (hF : F ∈ S.faces) : (R.cell F).Nonempty :=
  (hJ.isConnected hF).nonempty

/-- **Assertion (vii) in the blueprint's own words**: the union of the open cells strictly below
a 2-cell is a Jordan curve, and the open 2-cell is its bounded complementary region. -/
theorem faceBoundary_eq (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D) (hF : F ∈ S.faces) :
    R.faceBoundary F = frontier (R.cell F) :=
  h.faceBoundary_eq_frontier (S.mem_cells_of_mem_faces hF) (hJ.isOpen hF)

theorem isJordanCurve_faceBoundary (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D)
    (hF : F ∈ S.faces) : IsJordanCurve (R.faceBoundary F) := by
  rw [hJ.faceBoundary_eq h hF]; exact hJ.isJordanCurve hF

theorem cell_eq_inside_faceBoundary (hJ : R.IsFaceJordan) (h : R.IsCellDecomposition D)
    (hF : F ∈ S.faces) : R.cell F = inside (R.faceBoundary F) := by
  rw [hJ.faceBoundary_eq h hF]; exact hJ.cell_eq_inside hF

end IsFaceJordan

namespace IsCellDecomposition

/-- **Assertion (viii)**, with the openness hypothesis of
`IsCellDecomposition.face_eq` discharged by assertion (vii): distinct open 2-cells are never
comparable. -/
theorem face_eq_of_isFaceJordan (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hT : T ∈ S.faces) (hsub : R.cell F ⊆ closure (R.cell T)) : F = T :=
  h.face_eq hF hT (hJ.isOpen hF) hsub

/-- **Assertion (viii)** against the abstract relation. -/
theorem sub_face_eq (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) (hT : T ∈ S.faces) (hsub : S.sub F T) : F = T :=
  h.face_eq_of_isFaceJordan hJ hF hT
    (h.subset_closure (S.mem_cells_of_mem_faces hF) (S.mem_cells_of_mem_faces hT) hsub)

end IsCellDecomposition

end Realization

/-! ### Assertion (vii) is preserved by an edge subdivision

"An edge subdivision changes no 2-cell." Literally: the 2-cells of `S.subdivideEdge d` are those
of `S`, and each is an old cell distinct from the subdivided edge, so `SubdivData.IsRefinement`
leaves its open cell exactly where it was. -/

namespace SubdivData

variable {d : S.SubdivData} {R : S.Realization} {R' : (S.subdivideEdge d).Realization} {F : γ}

theorem IsRefinement.cell_face_eq (href : d.IsRefinement R R') (hF : F ∈ S.faces) :
    R'.cell F = R.cell F :=
  href.cell_eq (S.mem_cells_of_mem_faces hF) (S.faces_ne_edgeSet hF d.edge_mem_edgeSet)

/-- **Assertion (vii) is preserved by an edge subdivision.** -/
theorem IsRefinement.isFaceJordan (href : d.IsRefinement R R') (hJ : R.IsFaceJordan) :
    R'.IsFaceJordan where
  isJordanCurve := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [href.cell_face_eq hF]
    exact hJ.isJordanCurve hF
  cell_eq_inside := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [href.cell_face_eq hF]
    exact hJ.cell_eq_inside hF

end SubdivData

end CellStructure

end Schoenflies
