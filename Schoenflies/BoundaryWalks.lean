/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CellulationInvariants

/-!
# The boundary walk of a 2-cell, maintained across the elementary operations

`CellStructure.boundary` is the one field of a `CellStructure` on which no axiom is imposed —
"the cyclic boundary walk of each 2-cell", a bare list of edge names. This module states what
it is *supposed* to be and carries that statement across both elementary operations:

> for every 2-cell `F`, `boundary F` is a closed walk of the skeleton, and the cells it runs
> through are exactly the cells strictly below `F`.

That is `Schoenflies.CellStructure.BoundaryWalks`. It is what the ear construction needs and
cannot get from geometry: `Graph.face_cycles'` asks every edge of the graph to be polygonal,
which a *source* realization never satisfies — its outer edges are subarcs of the wild curve.
On the source side the boundary cycle is maintained as data, and this is the maintenance.

## Blueprint

* `Schoenflies.CellStructure.BoundaryWalks` — the invariant. Not a numbered statement: it is
  the content `def:matched-cellulation` intends by "the cyclic boundary walk of each 2-cell",
  made explicit because `CellStructure` does not impose it.
* `Schoenflies.CellStructure.BoundaryWalks.subdivideEdge`,
  `Schoenflies.CellStructure.BoundaryWalks.splitFace` — it is preserved by the two elementary
  operations of `def:generated-structure`.
* `Schoenflies.CellStructure.BoundaryWalks.eq_of_sub_of_mem_faces` — a consequence worth
  naming: no 2-cell is strictly below another. The blueprint asserts this for the split update
  ("no 2-cell is below another"); here it is a theorem, because a boundary walk runs through
  0-cells and 1-cells only.
* `Schoenflies.CellStructure.BoundaryWalks.mem_boundary_iff_sub` — the tie between the two
  fields the invariant asserts: an edge lies on the boundary walk of `F` exactly when it is a
  subcell of `F`.

## Design

**The invariant carries its base points.** A closed walk needs a vertex to start at, and a bare
edge list does not determine one (an edge list that walks from `u` may also walk from the other
end of its first edge). `BoundaryWalks.start` is therefore a field, not an existential — which
is also what `SubdivData.boundaryStart` needs to be filled with, so the two fit together with no
choice principle at the seam.

**Preservation at the subdivision is where `IsSubstWalk` is spent.** `SubdivData.newBoundary`
was made data precisely so that this step exists; `SubstWalk.pathCells` is the second half of
it, the bookkeeping of *which cells* the corrected walk runs through: the subdivided edge is
gone and the three new cells have appeared, exactly when the walk crossed it.
-/

open Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {e x u w : α}

/-- The vertices an edge is incident to are its two ends. General; stated here because nothing
on `main` states it and the cell bookkeeping below is all incidence. -/
theorem IsLink.inc_iff {f u w x : α} {G : Graph α α} (hl : G.IsLink f u w) :
    G.Inc f x ↔ x = u ∨ x = w :=
  ⟨fun h => h.eq_or_eq_of_isLink hl, by rintro (rfl | rfl); exacts [hl.inc_left, hl.inc_right]⟩

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ} {u w f F : γ} {L : List γ}

/-! ### The cells of a walk, step by step -/

/-- One step of a walk contributes the edge it takes and the vertex it departs from. -/
theorem pathCells_cons (hl : S.skel.IsLink f u w) :
    S.pathCells u (f :: L) = insert f (insert u (S.pathCells w L)) := by
  ext c
  simp only [pathCells, Graph.walkVertices, Graph.coveredVertices, mem_union, mem_setOf_eq,
    List.mem_cons, mem_insert_iff, exists_eq_or_imp, hl.inc_iff]
  tauto

/-- A walk that takes no edge runs through its base point alone. -/
@[simp] theorem pathCells_nil : S.pathCells u [] = {u} := by
  simp [pathCells, Graph.walkVertices]

theorem pathCells_append {W₁ W₂ : List γ} :
    S.pathCells u (W₁ ++ W₂) = S.pathCells u W₁ ∪ S.pathCells u W₂ := by
  ext c
  simp only [pathCells, Graph.walkVertices, Graph.coveredVertices_append, mem_union,
    mem_setOf_eq, List.mem_append, mem_insert_iff]
  tauto

/-- The cells of a walk are 0-cells and 1-cells; no 2-cell is among them. -/
theorem notMem_pathCells_of_mem_faces (h : S.skel.IsWalk u L w) (hF : F ∈ S.faces) :
    F ∉ S.pathCells u L := by
  rintro (hc | hc)
  · exact S.faces_ne_edgeSet hF (h.edge_mem hc) rfl
  · exact S.faces_ne_vertexSet hF (h.walkVertices_subset hc) rfl

/-- An edge is never a vertex a walk visits, so it lies in the cells of a walk only by being
one of its edges. -/
theorem mem_pathCells_iff_mem_of_mem_edgeSet (h : S.skel.IsWalk u L w) (he : f ∈ E(S.skel)) :
    f ∈ S.pathCells u L ↔ f ∈ L := by
  refine ⟨fun hc => ?_, fun hc => Or.inl hc⟩
  rcases hc with hc | hc
  · exact hc
  · exact absurd rfl (S.vertexSet_ne_edgeSet (h.walkVertices_subset hc) he)

/-! ### The invariant -/

/-- **The boundary walks of a cell structure.** For every 2-cell `F`, `boundary F` is a closed
walk of the skeleton based at `start F`, and the cells it runs through — its edges, and the
vertices it visits — are exactly the cells strictly below `F`.

`CellStructure` imposes none of this: `boundary` and `sub` are both raw data, and a structure
that satisfies neither clause is a perfectly good `CellStructure`. The initial pair satisfies
it, both elementary operations preserve it, and the ear construction consumes it. -/
structure BoundaryWalks (S : CellStructure γ) where
  /-- The base point of each 2-cell's boundary walk. -/
  start : γ → γ
  /-- The boundary datum of a 2-cell really is a closed walk. -/
  isWalk : ∀ ⦃F⦄, F ∈ S.faces → S.skel.IsWalk (start F) (S.boundary F) (start F)
  /-- And the cells it runs through are exactly the cells strictly below the 2-cell. -/
  pathCells_eq : ∀ ⦃F⦄, F ∈ S.faces →
    S.pathCells (start F) (S.boundary F) = S.subcells F \ {F}

namespace BoundaryWalks

/-- **No 2-cell is strictly below another.** The cells below `F` are the cells of a walk, and a
walk runs through 0-cells and 1-cells only. The blueprint asserts this of its update lists; it
is a consequence of the invariant, not an extra clause. -/
theorem eq_of_sub_of_mem_faces (bw : S.BoundaryWalks) {T : γ} (hF : F ∈ S.faces)
    (hT : T ∈ S.faces) (h : S.sub F T) : F = T := by
  by_contra hne
  exact notMem_pathCells_of_mem_faces (bw.isWalk hT) hF
    (by rw [bw.pathCells_eq hT]; exact ⟨⟨S.mem_cells_of_mem_faces hF, h⟩, hne⟩)

/-- **An edge lies on the boundary walk of a 2-cell exactly when it is one of its subcells.**
The two clauses of the invariant, tied together in the form both preservation proofs use. -/
theorem mem_boundary_iff_sub (bw : S.BoundaryWalks) (hF : F ∈ S.faces) (he : f ∈ E(S.skel)) :
    f ∈ S.boundary F ↔ S.sub f F := by
  rw [← mem_pathCells_iff_mem_of_mem_edgeSet (bw.isWalk hF) he, bw.pathCells_eq hF]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨S.mem_cells_of_mem_edgeSet he, h⟩,
    S.faces_ne_edgeSet hF he ∘ Eq.symm⟩⟩

end BoundaryWalks

/-! ### Preservation by an edge subdivision -/

namespace SubdivData

variable {d : S.SubdivData}

/-- The cells a corrected walk gains: the three new ones, and only if the walk crossed the
subdivided edge at all. -/
def crossedCells (d : S.SubdivData) (W : List γ) : Set γ := {c | c ∈ d.newCells ∧ d.edge ∈ W}

theorem crossedCells_of_mem (d : S.SubdivData) {W : List γ} (h : d.edge ∈ W) :
    d.crossedCells W = d.newCells := by
  ext c; simp [crossedCells, h]

theorem crossedCells_of_notMem (d : S.SubdivData) {W : List γ} (h : d.edge ∉ W) :
    d.crossedCells W = ∅ := by
  ext c; simp only [crossedCells, mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact fun hc => h hc.2

theorem crossedCells_cons_of_ne {W : List γ} (hf : f ≠ d.edge) :
    d.crossedCells (f :: W) = d.crossedCells W := by
  ext c
  simp only [crossedCells, mem_setOf_eq, List.mem_cons]
  exact ⟨fun hc => ⟨hc.1, hc.2.resolve_left fun h => hf h.symm⟩, fun hc => ⟨hc.1, Or.inr hc.2⟩⟩

theorem crossedCells_subset_newCells {W : List γ} : d.crossedCells W ⊆ d.newCells :=
  fun _ hc => hc.1

/-- **The cells of a corrected boundary walk.** The subdivided edge is gone, and the new vertex
and the two new edges are there exactly when the walk crossed it. Together with
`CellStructure.subdivideEdge_isWalk_boundary` — the walk half — this is everything the
subdivision step of the invariant needs. -/
theorem SubstWalk.pathCells {u v : γ} {W W' : List γ} (hsub : d.SubstWalk u W W')
    (h : S.skel.IsWalk u W v) :
    (S.subdivideEdge d).pathCells u W' = (S.pathCells u W \ {d.edge}) ∪ d.crossedCells W := by
  have hnew : d.newCells = {d.newVertex, d.newEdge₁, d.newEdge₂} := rfl
  induction hsub generalizing v with
  | nil u =>
    cases h with
    | nil hx =>
      have hue : d.edge ∉ ({u} : Set γ) := fun h =>
        S.vertexSet_ne_edgeSet hx d.edge_mem_edgeSet (mem_singleton_iff.1 h).symm
      rw [pathCells_nil, pathCells_nil, d.crossedCells_of_notMem (by simp), union_empty,
        sdiff_singleton_eq_self hue]
  | @forward W₀ W₀' hs ih =>
    cases h with
    | cons hl hW =>
      obtain rfl := d.isLink.right_unique hl
      have hlink₁ : (S.subdivideEdge d).skel.IsLink d.newEdge₁ d.left d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hlink₂ : (S.subdivideEdge d).skel.IsLink d.newEdge₂ d.newVertex d.right :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rw [pathCells_cons hlink₁, pathCells_cons hlink₂, ih hW, pathCells_cons hl,
        d.crossedCells_of_mem List.mem_cons_self]
      ext c
      simp only [hnew, crossedCells, mem_insert_iff, mem_singleton_iff, mem_union, mem_sdiff,
        mem_setOf_eq]
      constructor
      · rintro (rfl | rfl | rfl | rfl | ⟨hc, hce⟩ | hc)
        exacts [Or.inr (Or.inr (Or.inl rfl)), Or.inl ⟨Or.inr (Or.inl rfl), d.left_ne_edge⟩,
          Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inl rfl), Or.inl ⟨Or.inr (Or.inr hc), hce⟩,
          Or.inr hc.1]
      · rintro (⟨rfl | rfl | hc, hce⟩ | hc)
        · exact absurd rfl hce
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, hce⟩))))
        · rcases hc with rfl | rfl | rfl
          exacts [Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))]
  | @backward W₀ W₀' hs ih =>
    cases h with
    | cons hl hW =>
      obtain rfl := d.isLink.symm.right_unique hl
      have hlink₂ : (S.subdivideEdge d).skel.IsLink d.newEdge₂ d.right d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      have hlink₁ : (S.subdivideEdge d).skel.IsLink d.newEdge₁ d.newVertex d.left :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
      rw [pathCells_cons hlink₂, pathCells_cons hlink₁, ih hW, pathCells_cons hl,
        d.crossedCells_of_mem List.mem_cons_self]
      ext c
      simp only [hnew, crossedCells, mem_insert_iff, mem_singleton_iff, mem_union, mem_sdiff,
        mem_setOf_eq]
      constructor
      · rintro (rfl | rfl | rfl | rfl | ⟨hc, hce⟩ | hc)
        exacts [Or.inr (Or.inr (Or.inr rfl)), Or.inl ⟨Or.inr (Or.inl rfl), d.right_ne_edge⟩,
          Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inl rfl), Or.inl ⟨Or.inr (Or.inr hc), hce⟩,
          Or.inr hc.1]
      · rintro (⟨rfl | rfl | hc, hce⟩ | hc)
        · exact absurd rfl hce
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, hce⟩))))
        · rcases hc with rfl | rfl | rfl
          exacts [Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inl rfl)), Or.inl rfl]
  | @other u₀ w₀ f₀ W₀ W₀' hl hf hs ih =>
    cases h with
    | cons hl' hW =>
      obtain rfl := hl.right_unique hl'
      have hlink : (S.subdivideEdge d).skel.IsLink f₀ u₀ w₀ :=
        d.skeleton_isLink.2 (Or.inl ⟨hl, hf,
          fun hh => d.newEdge₁_notMem_edgeSet (hh ▸ hl.edge_mem),
          fun hh => d.newEdge₂_notMem_edgeSet (hh ▸ hl.edge_mem)⟩)
      have hue : u₀ ≠ d.edge := S.vertexSet_ne_edgeSet hl.left_mem d.edge_mem_edgeSet
      rw [pathCells_cons hlink, ih hW, pathCells_cons hl, crossedCells_cons_of_ne hf]
      ext c
      simp only [mem_insert_iff, mem_union, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | ⟨hc, hce⟩ | hc)
        exacts [Or.inl ⟨Or.inl rfl, hf⟩, Or.inl ⟨Or.inr (Or.inl rfl), hue⟩,
          Or.inl ⟨Or.inr (Or.inr hc), hce⟩, Or.inr hc]
      · rintro (⟨rfl | rfl | hc, hce⟩ | hc)
        exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl ⟨hc, hce⟩)),
          Or.inr (Or.inr (Or.inr hc))]

/-- The subcell relation of a subdivided structure, at a 2-cell: the old subcells minus the
subdivided edge, plus the three new cells when the edge was one of them. -/
theorem subRel_face_iff {σ : γ} (hF : F ∈ S.faces) :
    d.subRel σ F ↔
      (σ ∉ d.newCells ∧ σ ≠ d.edge ∧ S.sub σ F) ∨ (σ ∈ d.newCells ∧ S.sub d.edge F) := by
  have hFn : F ∉ d.newCells := notMem_newCells_of_mem_cells (S.mem_cells_of_mem_faces hF)
  have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
  constructor
  · rintro (⟨h₁, -, h₃, -, h₅⟩ | ⟨rfl, h⟩ | ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨h₁, -, h₃⟩)
    · exact Or.inl ⟨h₁, h₃, h₅⟩
    · exact absurd h hFn
    · exact absurd (Or.inr (Or.inl rfl)) hFn
    · exact absurd (Or.inr (Or.inr rfl)) hFn
    · exact absurd (Or.inr (Or.inl rfl)) hFn
    · exact absurd (Or.inr (Or.inr rfl)) hFn
    · exact Or.inr ⟨h₁, h₃⟩
  · rintro (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl ⟨h₁, hFn, h₂, hFe, h₃⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h₁, hFe, h₂⟩))))

theorem subcells_subdivideEdge_of_sub (d : S.SubdivData) (hF : F ∈ S.faces)
    (hsub : S.sub d.edge F) :
    (S.subdivideEdge d).subcells F = (S.subcells F \ {d.edge}) ∪ d.newCells := by
  ext σ
  rw [mem_subcells_iff, subdivideEdge_sub, subRel_face_iff hF]
  constructor
  · rintro ⟨hcell, h⟩
    rw [subdivideEdge_cells] at hcell
    rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, -⟩
    · exact Or.inl ⟨⟨(hcell.resolve_right h₁).1, h₃⟩, h₂⟩
    · exact Or.inr h₁
  · rintro (⟨⟨hc, hs⟩, hne⟩ | h)
    · exact ⟨d.mem_subdivideEdge_cells_of_old hc hne,
        Or.inl ⟨notMem_newCells_of_mem_cells hc, hne, hs⟩⟩
    · exact ⟨d.mem_subdivideEdge_cells_of_new h, Or.inr ⟨h, hsub⟩⟩

theorem subcells_subdivideEdge_of_not_sub (d : S.SubdivData) (hF : F ∈ S.faces)
    (hsub : ¬ S.sub d.edge F) :
    (S.subdivideEdge d).subcells F = S.subcells F \ {d.edge} := by
  ext σ
  rw [mem_subcells_iff, subdivideEdge_sub, subRel_face_iff hF]
  constructor
  · rintro ⟨hcell, h⟩
    rw [subdivideEdge_cells] at hcell
    rcases h with ⟨h₁, h₂, h₃⟩ | ⟨-, h₂⟩
    · exact ⟨⟨(hcell.resolve_right h₁).1, h₃⟩, h₂⟩
    · exact absurd h₂ hsub
  · rintro ⟨⟨hc, hs⟩, hne⟩
    exact ⟨d.mem_subdivideEdge_cells_of_old hc hne,
      Or.inl ⟨notMem_newCells_of_mem_cells hc, hne, hs⟩⟩

end SubdivData

/-- **The invariant survives an edge subdivision.** The base points are unchanged — a
subdivision moves no old vertex — and that is why the `SubdivData` has to have been built with
`boundaryStart` the invariant's own base points. -/
def BoundaryWalks.subdivideEdge (bw : S.BoundaryWalks) (d : S.SubdivData)
    (hstart : d.boundaryStart = bw.start) : (S.subdivideEdge d).BoundaryWalks where
  start := bw.start
  isWalk F hF := by
    have h := subdivideEdge_isWalk_boundary d (F := F) (v := bw.start F) (hstart ▸ bw.isWalk hF)
    rwa [hstart] at h
  pathCells_eq F hF := by
    have hwalk : S.skel.IsWalk (bw.start F) (S.boundary F) (bw.start F) := bw.isWalk hF
    have hsubst : d.SubstWalk (bw.start F) (S.boundary F) ((S.subdivideEdge d).boundary F) :=
      hstart ▸ d.newBoundary_isSubstWalk F _ (hstart ▸ hwalk)
    have hFn : F ∉ d.newCells :=
      SubdivData.notMem_newCells_of_mem_cells (S.mem_cells_of_mem_faces hF)
    rw [SubdivData.SubstWalk.pathCells hsubst hwalk, bw.pathCells_eq hF]
    by_cases hedge : S.sub d.edge F
    · rw [d.subcells_subdivideEdge_of_sub hF hedge,
        d.crossedCells_of_mem ((bw.mem_boundary_iff_sub hF d.edge_mem_edgeSet).2 hedge),
        union_sdiff_distrib, sdiff_singleton_eq_self hFn, sdiff_sdiff_comm]
    · rw [d.subcells_subdivideEdge_of_not_sub hF hedge,
        d.crossedCells_of_notMem fun h => hedge ((bw.mem_boundary_iff_sub hF
          d.edge_mem_edgeSet).1 h), union_empty, sdiff_sdiff_comm]

end CellStructure

end Schoenflies
