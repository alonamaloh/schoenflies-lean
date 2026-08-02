/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.StageCells
import Schoenflies.Graph.PlaneEdges

/-!
# Polygonal accessibility inside a source 2-cell

*For part (b), an endpoint not on `C` is accessible from the corresponding source face by
`lem:polygonal-side-accessibility`.* One sentence of the blueprint's proof of
`thm:finite-transfer`, and the first half of what direction (b)'s ear step needs.

It is not `Graph.polygonal_side_accessibility_target`, which is what direction (a) uses: that
one asks every edge of the drawn graph to be polygonal, and a *source* realization never
satisfies it — its outer edges are subarcs of the wild Jordan curve `C`. The general form
`Graph.polygonal_side_accessibility` is the one that applies, because it already carries the
wild set: it takes the polygonal graph `G`, a **compact** set `C` to be adjoined, and the point
`x` off `C`.

So the whole content here is choosing `G`. It is
`CellStructure.Realization.nonboundaryGraph` — the drawn skeleton with the outer edges deleted,
which `IsWeaklyAdmissible.isPolygonal` says is polygonal edge by edge — and the compact set is
the outer curve itself. `pointSet_nonboundaryGraph_union` is the bookkeeping that the two
together are the whole realized skeleton, so that `Realization.cellsAbsorb` applies to them
unchanged: deleting the outer edges loses no *point*, since an outer edge's arc lies in the
realized outer cycle, which is the adjoined set.

## Blueprint

* `Schoenflies.CellStructure.Realization.polyAccessible_of_notMem_outer` —
  `lem:polygonal-side-accessibility` on the source side, in the form
  `thm:finite-transfer`(b) consumes.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

namespace CellStructure

namespace Realization

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane}
  {F : γ} {x : Plane}

/-- **The drawn skeleton with the outer edges deleted.** Every one of its edges is polygonal, by
`IsWeaklyAdmissible.isPolygonal`; the whole skeleton is not, and cannot be made to be. Its
vertices are all of the skeleton's — `Graph.restrict` removes no vertex — which is what keeps
the point set right. -/
def nonboundaryGraph (R : S.Realization) : Graph Plane γ :=
  R.graph.restrict {e | e ∉ E(S.outerGraph)}

theorem nonboundaryGraph_le : R.nonboundaryGraph ≤ R.graph := restrict_le

theorem mem_edgeSet_nonboundaryGraph {e : γ} (he : e ∈ E(R.nonboundaryGraph)) :
    e ∈ E(S.skel) ∧ e ∉ E(S.outerGraph) := by
  obtain ⟨he₁, he₂⟩ := he
  exact ⟨by rwa [Realization.edgeSet_graph] at he₁, he₂⟩

theorem isDrawing_nonboundaryGraph (R : S.Realization) :
    IsDrawing R.nonboundaryGraph R.drawing :=
  (show IsDrawing R.graph R.drawing from R.isDrawing).mono nonboundaryGraph_le

instance finite_nonboundaryGraph (R : S.Realization) : R.nonboundaryGraph.Finite :=
  haveI := R.finite_graph; Graph.Finite.of_le nonboundaryGraph_le

/-- **The realized outer cycle is compact**, which is what makes it usable as the wild set of
`Graph.polygonal_side_accessibility`. It is the point set of a finite plane graph, namely the
outer cycle drawn by the realization. -/
theorem isCompact_outerSet (R : S.Realization) : IsCompact R.outerSet := by
  have hle : S.outerGraph.map R.pos ≤ R.graph := Graph.map_mono R.pos S.outerGraph_le
  haveI := R.finite_graph
  haveI : (S.outerGraph.map R.pos).Finite := Graph.Finite.of_le hle
  exact IsDrawing.isCompact_pointSet ((show IsDrawing R.graph R.drawing from R.isDrawing).mono hle)

/-- **Deleting the outer edges loses no point of the skeleton that the outer cycle does not
already carry.** An outer edge's arc lies in the realized outer cycle, and every vertex survives
the deletion, so the nonboundary graph together with the outer curve occupies the whole
skeleton. -/
theorem pointSet_nonboundaryGraph_union (hadm : R.IsWeaklyAdmissible outer dom) :
    pointSet R.nonboundaryGraph R.drawing ∪ outer = R.skeletonSet := by
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · rintro p (hv | hedge)
    · exact Or.inl (nonboundaryGraph_le.vertexSet_mono hv)
    · obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.1 hedge
      exact Or.inr (Set.mem_iUnion₂.2 ⟨e, nonboundaryGraph_le.edgeSet_mono he, hpe⟩)
  · rw [← hadm.outerSet_eq]; exact R.outerSet_subset_skeletonSet
  · rintro p (hv | hedge)
    · exact Or.inl (Or.inl hv)
    obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.1 hedge
    by_cases hout : e ∈ E(S.outerGraph)
    · -- An outer edge is drawn inside the realized outer cycle.
      refine Or.inr (hadm.outerSet_eq ▸ ?_)
      exact Graph.edgeArc_subset_pointSet (by rwa [Graph.edgeSet_map]) hpe
    · exact Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨e, ⟨he, hout⟩, hpe⟩))

/-- **`lem:polygonal-side-accessibility` on the source side.** A point of the closure of a source
2-cell that does not lie on the outer curve is polygonally accessible from that 2-cell.

The four domain hypotheses are the ones every stage-level statement carries — `dom ∖ outer` open
with frontier inside `outer`, and `outer` inside the skeleton — and
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and its companion discharge them for a closed
Jordan region. -/
theorem polyAccessible_of_notMem_outer (hcd : R.IsCellDecomposition dom) (hJ : R.IsFaceJordan)
    (hadm : R.IsWeaklyAdmissible outer dom) (houter : outer ⊆ R.skeletonSet)
    (hQ : IsOpen (dom \ outer)) (hfr : frontier (dom \ outer) ⊆ outer)
    (hF : F ∈ S.faces) (hx : x ∈ closure (R.cell F)) (hxC : x ∉ outer) :
    PolyAccessible (R.cell F) x := by
  have hC : IsCompact outer := hadm.outerSet_eq ▸ R.isCompact_outerSet
  refine Graph.polygonal_side_accessibility (R.isDrawing_nonboundaryGraph)
    (fun e he => hadm.isPolygonal (mem_edgeSet_nonboundaryGraph he).1
      (mem_edgeSet_nonboundaryGraph he).2)
    hC (pointSet_nonboundaryGraph_union hadm).symm
    (R.cellsAbsorb hcd hJ houter hQ hfr) ⟨F, hF, rfl⟩
    (R.disjoint_cell_skeletonSet hcd hF) hx hxC

end Realization

end CellStructure

end Schoenflies
