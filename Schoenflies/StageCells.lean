/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransfer
import Schoenflies.RealizeSplit

/-!
# The 2-cells of a stage are the components of the open domain minus the skeleton

`Schoenflies.CellsAbsorb` — *a connected set disjoint from the skeleton that meets a 2-cell lies
in it* — has been carried as a **named hypothesis** through `SkeletonAccess.lean`,
`FiniteTransfer.lean` and `FreshAccess.lean` since it was written, with
`Schoenflies.cellsAbsorb_of_isComponent_in` recorded as "the discharger, when the cells are the
components". This module observes that at a stage they always are, and discharges it.

## Why it is a theorem and not a field

Assertion (i) says the open cells partition the closed domain; assertion (vii) says every open
2-cell is the bounded region of a Jordan curve, hence **open and connected**. Together with
`Realization.disjoint_cell_skeletonSet` — an open 2-cell misses the drawn skeleton — the open
2-cells are a partition of `(dom ∖ outer) ∖ |Γ|` into disjoint nonempty *open connected* pieces,
and such a partition is exactly the decomposition into connected components. Nothing else is
needed, and in particular no new field of `Schoenflies.GeneratedPair`: the invariant that had to
be added was assertion (vii), and this comes with it.

The one thing that is not a property of the stage is the shape of the domain — `dom ∖ outer` has
to be open with its frontier inside `outer`. That is a fact about the two fixed regions, the
same at every stage, so it is a hypothesis here and
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` / `.frontier_sdiff_outer_of_isSeparating`
discharge it for a closed Jordan region, which is the shape both sides have.

## Blueprint

* `Schoenflies.CellStructure.Realization.cell_isComponent`,
  `.cells_isComponent_in` — `lem:cellulation-invariants`(i) in its geometric reading, the one
  `Schoenflies.exists_target_ear` and `Schoenflies.polygonal_side_accessibility_target` consume.
* `Schoenflies.CellStructure.Realization.cellsAbsorb` — `Schoenflies.CellsAbsorb`, discharged.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

namespace Realization

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane} {F : γ}
  {z : Plane}

/-- **An open 2-cell lies in the open domain and misses the skeleton.** -/
theorem cell_subset_sdiff (hcd : R.IsCellDecomposition dom) (houter : outer ⊆ R.skeletonSet)
    (hF : F ∈ S.faces) : R.cell F ⊆ (dom \ outer) \ R.skeletonSet := by
  intro x hx
  have hxK : x ∉ R.skeletonSet := Set.disjoint_left.1 (R.disjoint_cell_skeletonSet hcd hF) hx
  refine ⟨⟨?_, fun hxo => hxK (houter hxo)⟩, hxK⟩
  rw [← hcd.iUnion_eq]
  exact Set.mem_biUnion (S.mem_cells_of_mem_faces hF) hx

/-- **What is left of the open domain after the skeleton is exactly the open 2-cells.** One
inclusion is the line above; the other is assertion (i)'s covering clause together with
`Realization.mem_faces_of_notMem_skeletonSet`, which says a cell containing a point off the
skeleton is a 2-cell. -/
theorem biUnion_faces_eq (hcd : R.IsCellDecomposition dom) (houter : outer ⊆ R.skeletonSet) :
    ⋃ F ∈ S.faces, R.cell F = (dom \ outer) \ R.skeletonSet := by
  refine Set.Subset.antisymm (Set.iUnion₂_subset fun F hF => cell_subset_sdiff hcd houter hF) ?_
  rintro x ⟨⟨hxD, -⟩, hxK⟩
  rw [← hcd.iUnion_eq] at hxD
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hxD
  exact Set.mem_biUnion (R.mem_faces_of_notMem_skeletonSet hσ hxσ hxK) hxσ

/-- **Each open 2-cell is a connected component of the open domain minus the skeleton.**

`⊇` is that a 2-cell is connected and sits inside; `⊆` is the separation argument that makes a
partition into open pieces a partition into components — the component is covered by the 2-cell
and the union of all the others, both open and disjoint, so a connected set meeting the first
cannot meet the second. -/
theorem cell_isComponent (hcd : R.IsCellDecomposition dom) (hJ : R.IsFaceJordan)
    (houter : outer ⊆ R.skeletonSet) (hF : F ∈ S.faces) (hz : z ∈ R.cell F) :
    connectedComponentIn ((dom \ outer) \ R.skeletonSet) z = R.cell F := by
  have hsub := cell_subset_sdiff hcd houter hF
  refine Set.Subset.antisymm ?_
    ((hJ.isConnected hF).isPreconnected.subset_connectedComponentIn hz hsub)
  -- the other 2-cells, as one open set
  set V : Set Plane := ⋃ T ∈ S.faces \ {F}, R.cell T with hV
  have hVopen : IsOpen V := isOpen_biUnion fun T hT => hJ.isOpen hT.1
  have hcover : connectedComponentIn ((dom \ outer) \ R.skeletonSet) z ⊆ R.cell F ∪ V := by
    intro x hx
    rw [← biUnion_faces_eq hcd houter] at hx
    · obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.1 (connectedComponentIn_subset _ _ hx)
      by_cases hTF : T = F
      · exact Or.inl (hTF ▸ hxT)
      · exact Or.inr (Set.mem_biUnion ⟨hT, hTF⟩ hxT)
  have hzmem : z ∈ (dom \ outer) \ R.skeletonSet := hsub hz
  intro x hx
  by_contra hxF
  refine absurd (isPreconnected_connectedComponentIn (F := (dom \ outer) \ R.skeletonSet)
    (x := z) (R.cell F) V (hJ.isOpen hF) hVopen hcover ⟨z, mem_connectedComponentIn hzmem, hz⟩
    ⟨x, hx, (hcover hx).resolve_left hxF⟩) ?_
  rintro ⟨y, -, hyF, hyV⟩
  obtain ⟨T, hT, hyT⟩ := Set.mem_iUnion₂.1 hyV
  exact Set.disjoint_left.1 (hcd.disjoint (S.mem_cells_of_mem_faces hF)
    (S.mem_cells_of_mem_faces hT.1) (Ne.symm hT.2)) hyF hyT

/-- **The family of open 2-cells, in the shape `Schoenflies.exists_target_ear` and
`Graph.polygonal_side_accessibility_target` consume**: each is contained in the open domain and
is a connected component of what the skeleton leaves of it. -/
theorem cells_isComponent_in (hcd : R.IsCellDecomposition dom) (hJ : R.IsFaceJordan)
    (houter : outer ⊆ R.skeletonSet) (hF : F ∈ S.faces) :
    R.cell F ⊆ dom \ outer ∧
      ∃ z, R.cell F = connectedComponentIn ((dom \ outer) \ R.skeletonSet) z :=
  ⟨(cell_subset_sdiff hcd houter hF).trans Set.diff_subset,
    (hJ.nonempty hF).choose, (cell_isComponent hcd hJ houter hF (hJ.nonempty hF).choose_spec).symm⟩

/-- **A refinement occupies at least what it refines.** The realized skeleton only grows, and
this is a consequence of the interface rather than a fact about how the refinement was built: a
point of the old skeleton lies in the open cell of some old 0-cell or 1-cell
(`skeletonSet_subset_cellUnion`); it also lies in some new open cell, whose parent must be that
old cell, by disjointness; and the parent of a 2-cell is a 2-cell, so the new cell is not one
either, and its open cell is part of the new skeleton.

`thm:finite-transfer`(b) needs it to restrict `SplitData.splitHomeo_eqOn` — which says the
transported skeleton map agrees with the old one on the *current* skeleton — to the skeleton of
the base pair. It belongs beside `Realization.Refines` in `Schoenflies/RefinementStars.lean`, and
is here only because `disjoint_cell_skeletonSet` and `skeletonSet_subset_cellUnion` are. -/
theorem Refines.skeletonSet_subset {S' : CellStructure γ} {R' : S'.Realization} {par : γ → γ}
    (h : R'.Refines R par) (hcd : R.IsCellDecomposition dom) (hcd' : R'.IsCellDecomposition dom) :
    R.skeletonSet ⊆ R'.skeletonSet := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := mem_cellUnion_iff.1 (R.skeletonSet_subset_cellUnion hx)
  have hxD : x ∈ dom := by
    rw [← hcd.iUnion_eq]; exact Set.mem_biUnion (Or.inl hσ) hxσ
  obtain ⟨τ, hτ, hxτ⟩ := hcd'.exists_cell hxD
  have hpar : par τ = σ := by
    by_contra hne
    exact Set.disjoint_left.1 (hcd.disjoint (h.parent_mem_cells hτ) (Or.inl hσ) hne)
      (h.cell_subset hτ hxτ) hxσ
  refine cell_subset_skeletonSet (hτ.resolve_right fun hf => ?_) hxτ
  have hfσ : σ ∈ S.faces := hpar ▸ h.parent_mem_faces hf
  rcases hσ with h1 | h1
  exacts [S.faces_ne_vertexSet hfσ h1 rfl, S.faces_ne_edgeSet hfσ h1 rfl]

/-- **An open 1-cell that meets the outer curve is an outer edge.**

The realized outer cycle is its own 0-cells together with the arcs of its own edges. A point of
the *open* 1-cell of `e` is not a drawn 0-cell, so it lies on some outer edge's arc; and away
from the vertices a point of a plane graph lies on exactly one edge, so that outer edge is `e`.

`thm:finite-transfer`(b) is what needs it: a fresh boundary point is a 0-cell drawn on the outer
curve inside an open 1-cell of the base pair, and this is what makes that 1-cell an *outer* edge
— which is what "inserted in the interior of one outer edge" means, and what the anchor clause of
the transfer invariant asks of the ancestor. -/
theorem mem_edgeSet_outerGraph_of_cell_meets_outerSet {e : γ} (he : e ∈ E(S.skel))
    (hz : z ∈ R.cell e) (hout : z ∈ R.outerSet) : e ∈ E(S.outerGraph) := by
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have hdraw : Graph.IsDrawing R.graph R.drawing := R.isDrawing
  have hlmap : R.graph.IsLink e (R.pos x) (R.pos y) := Graph.IsLink.map _ hl
  rw [R.cell_edge hl] at hz
  -- A drawn 0-cell on the arc of `e` is one of its two ends, which `z` is not.
  have hnotV : z ∉ V(R.graph) := fun hv => by
    rcases hdraw.vertex_mem_edgeArc hlmap hv hz.1 with h | h
    exacts [hz.2 (Or.inl h), hz.2 (Or.inr h)]
  rcases hout with hv | hedge
  · exact absurd ((Graph.map_mono R.pos S.outerGraph_le).vertexSet_mono hv) hnotV
  · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hedge
    have hfE : f ∈ E(S.outerGraph) := by rwa [Graph.edgeSet_map] at hf
    have hfskel : f ∈ E(R.graph) := by
      rw [Realization.edgeSet_graph]; exact S.outerGraph_le.edgeSet_mono hfE
    have heskel : e ∈ E(R.graph) := by rw [Realization.edgeSet_graph]; exact he
    rwa [hdraw.unique_edge_at heskel hfskel hnotV hz.1 hzf]

/-- **The boundary curve of a 2-cell lies in the drawn skeleton.** Its frontier is the union of
the open cells strictly below it (assertions (i) and (vii)), and none of those is a 2-cell —
that is assertion (viii), `IsCellDecomposition.sub_face_eq`. So they are 0-cells and 1-cells,
which are part of the skeleton.

This is the clause `Schoenflies.exists_target_ear` asks of the Jordan curve it is handed. -/
theorem frontier_cell_subset_skeletonSet (hcd : R.IsCellDecomposition dom) (hJ : R.IsFaceJordan)
    (hF : F ∈ S.faces) : frontier (R.cell F) ⊆ R.skeletonSet := by
  rw [← hJ.faceBoundary_eq hcd hF, faceBoundary]
  refine cellUnion_subset fun σ hσ => ?_
  obtain ⟨⟨hσc, hsub⟩, hσne⟩ := hσ
  rcases hσc with hσv | hσf
  · exact cell_subset_skeletonSet hσv
  · exact absurd (hcd.sub_face_eq hJ hσf hF hsub) hσne

/-- **`Schoenflies.CellsAbsorb`, discharged.** The hypothesis that has been carried through three
modules as an assumption is a consequence of assertions (i) and (vii) at any stage. -/
theorem cellsAbsorb (hcd : R.IsCellDecomposition dom) (hJ : R.IsFaceJordan)
    (houter : outer ⊆ R.skeletonSet) (hQ : IsOpen (dom \ outer))
    (hfr : frontier (dom \ outer) ⊆ outer) :
    CellsAbsorb R.skeletonSet {A | ∃ F ∈ S.faces, A = R.cell F} :=
  cellsAbsorb_of_isComponent_in hQ (hfr.trans houter)
    (by rintro A ⟨F, hF, rfl⟩; exact cells_isComponent_in hcd hJ houter hF)

end Realization

end CellStructure

/-! ### The two domains

Both sides of a matched cellulation live over a closed Jordan region — `C ∪ D` on the source
side and the closed square on the target — and for such a region the two domain facts the
discharger needs are `thm:jordan` and nothing else. -/

variable {C : Set Plane}

theorem sdiff_outer_eq_inside (h : IsSeparating C) : (C ∪ inside C) \ C = inside C := by
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx => ⟨Or.inr hx, inside_subset_compl hx⟩
  exact hx.1.resolve_left hx.2

theorem isOpen_sdiff_outer_of_isSeparating (h : IsSeparating C) : IsOpen ((C ∪ inside C) \ C) := by
  rw [sdiff_outer_eq_inside h]; exact h.isOpen_inside

theorem frontier_sdiff_outer_of_isSeparating (h : IsSeparating C) :
    frontier ((C ∪ inside C) \ C) ⊆ C := by
  rw [sdiff_outer_eq_inside h, h.frontier_inside]

end Schoenflies
