/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CellulationInvariants
import Schoenflies.FaceCyclesProof

/-!
# The boundary walk of a 2-cell, maintained across the elementary operations

`CellStructure.boundary` is the one field of a `CellStructure` on which no axiom is imposed —
"the cyclic boundary walk of each 2-cell", a bare list of edge names. This module states what
it is *supposed* to be and carries that statement across both elementary operations:

> for every 2-cell `F`, `boundary F` is a **cycle** of the skeleton, and the cells it runs
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
  clauses the invariant asserts: an edge lies on the boundary walk of `F` exactly when it is a
  subcell of `F`.
* `Schoenflies.CellStructure.BoundaryWalks.exists_boundary_paths` — **what the invariant is
  for**: two distinct 0-cells below a 2-cell cut its boundary into two paths between them, which
  carry exactly the cells below the 2-cell and meet in nothing but the two 0-cells. Those are
  `CellStructure.SplitData.isPath₁`, `isPath₂`, `sub_face` and `paths_meet`, which is the whole
  of what `Schoenflies.EarStep` could not previously produce.

## Design

**The invariant carries its base points.** A closed walk needs a vertex to start at, and a bare
edge list does not determine one (an edge list that walks from `u` may also walk from the other
end of its first edge). `BoundaryWalks.start` is therefore a field, not an existential — which
is also what `SubdivData.boundaryStart` needs to be filled with, so the two fit together with no
choice principle at the seam.

**Why a cycle and not a closed walk.** `SplitData.paths_meet` asks the two boundary paths to
share nothing but their two ends, and a closed walk that repeats a vertex cuts into pieces that
meet in more than two points. The cycle is presented through its first edge — `boundary F =
e :: D.reverse` with `Graph.IsCycleThrough e (start F) v D` — because that is how
`Schoenflies/Graph/Cycle.lean` presents every cycle in this development, and because it makes
`Graph.IsCycleThrough.split_at` (already on `main`, in `FaceCyclesProof.lean`) directly
applicable.

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
  /-- The boundary datum of a 2-cell really is a **cycle** of the skeleton based at `start F`:
  it leaves by an edge `e` and comes back along a path, which is where vertex-simplicity lives.
  Presented through the edge, the way `Graph.IsCycleThrough` presents every cycle in this
  development — `Graph.IsPath` then does the ruling-out of repetitions, and
  `Graph.IsCycleThrough.split_at` is waiting on the other side. -/
  isCycle : ∀ ⦃F⦄, F ∈ S.faces → ∃ e v D, S.boundary F = e :: D.reverse ∧
    S.skel.IsCycleThrough e (start F) v D
  /-- And the cells it runs through are exactly the cells strictly below the 2-cell. -/
  pathCells_eq : ∀ ⦃F⦄, F ∈ S.faces →
    S.pathCells (start F) (S.boundary F) = S.subcells F \ {F}

namespace BoundaryWalks

/-- The boundary datum is a closed walk — the weaker half of `isCycle`, which is all most of
the bookkeeping needs. -/
theorem isWalk (bw : S.BoundaryWalks) (hF : F ∈ S.faces) :
    S.skel.IsWalk (bw.start F) (S.boundary F) (bw.start F) := by
  obtain ⟨e, v, D, hb, hl, hD, -⟩ := bw.isCycle hF
  rw [hb]
  exact .cons hl hD.reverse.isWalk

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

/-- The edges of a corrected walk are the old ones, except that the subdivided edge has become
the two new ones. -/
theorem SubstWalk.mem_of_mem {u : γ} {W W' : List γ} (hsub : d.SubstWalk u W W') {g : γ}
    (hg : g ∈ W') : g ∈ W ∨ g = d.newEdge₁ ∨ g = d.newEdge₂ := by
  induction hsub with
  | nil u => simp at hg
  | forward hs ih =>
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact Or.inr (Or.inl rfl)
    rcases List.mem_cons.1 hg' with rfl | hg''
    · exact Or.inr (Or.inr rfl)
    · exact (ih hg'').imp (List.mem_cons_of_mem _) id
  | backward hs ih =>
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact Or.inr (Or.inr rfl)
    rcases List.mem_cons.1 hg' with rfl | hg''
    · exact Or.inr (Or.inl rfl)
    · exact (ih hg'').imp (List.mem_cons_of_mem _) id
  | other hl hf hs ih =>
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact Or.inl List.mem_cons_self
    · exact (ih hg').imp (List.mem_cons_of_mem _) id

/-- An old edge other than the subdivided one keeps its ends. -/
theorem skeleton_inc_iff_of_mem_edgeSet {g z : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) :
    d.skeleton.Inc g z ↔ S.skel.Inc g z := by
  constructor
  · rintro ⟨y, hy⟩
    rcases d.skeleton_isLink.1 hy with ⟨hl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨y, hl⟩
    · exact absurd hg d.newEdge₁_notMem_edgeSet
    · exact absurd hg d.newEdge₂_notMem_edgeSet
  · rintro ⟨y, hy⟩
    exact ⟨y, d.skeleton_isLink.2 (Or.inl ⟨hy, hge,
      fun hh => d.newEdge₁_notMem_edgeSet (hh ▸ hg), fun hh => d.newEdge₂_notMem_edgeSet (hh ▸ hg)⟩)⟩

/-- A walk that never takes the subdivided edge visits the same vertices after the subdivision
as before. -/
theorem walkVertices_skeleton_eq {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v)
    (hW : d.edge ∉ W) : d.skeleton.walkVertices u W = S.skel.walkVertices u W := by
  have hcov : d.skeleton.coveredVertices W = S.skel.coveredVertices W := by
    ext z
    constructor
    · rintro ⟨g, hg, hz⟩
      exact ⟨g, hg, (d.skeleton_inc_iff_of_mem_edgeSet (h.edge_mem hg)
        (fun hh => hW (hh ▸ hg))).1 hz⟩
    · rintro ⟨g, hg, hz⟩
      exact ⟨g, hg, (d.skeleton_inc_iff_of_mem_edgeSet (h.edge_mem hg)
        (fun hh => hW (hh ▸ hg))).2 hz⟩
  rw [Graph.walkVertices, Graph.walkVertices, hcov]

/-- A corrected walk visits the vertices the old one did, and at most the new one besides. -/
theorem SubstWalk.walkVertices_subset {u v : γ} {W W' : List γ} (hsub : d.SubstWalk u W W')
    (h : S.skel.IsWalk u W v) :
    d.skeleton.walkVertices u W' ⊆ insert d.newVertex (S.skel.walkVertices u W) := by
  induction hsub generalizing v with
  | nil u =>
    rw [Graph.walkVertices_nil, Graph.walkVertices_nil]
    exact (Set.singleton_subset_iff.2 (mem_insert_of_mem _ rfl))
  | @forward W₀ W₀' hs ih =>
    cases h with
    | cons hl hW =>
      obtain rfl := d.isLink.right_unique hl
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rw [Graph.walkVertices_cons hlink₁, Graph.walkVertices_cons hlink₂,
        Graph.walkVertices_cons hl]
      intro z hz
      rcases hz with rfl | rfl | hz
      exacts [mem_insert_of_mem _ (mem_insert _ _), mem_insert _ _,
        (ih hW hz).elim (fun h => h ▸ mem_insert _ _)
          fun h => mem_insert_of_mem _ (mem_insert_of_mem _ h)]
  | @backward W₀ W₀' hs ih =>
    cases h with
    | cons hl hW =>
      obtain rfl := d.isLink.symm.right_unique hl
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
      rw [Graph.walkVertices_cons hlink₂, Graph.walkVertices_cons hlink₁,
        Graph.walkVertices_cons hl]
      intro z hz
      rcases hz with rfl | rfl | hz
      exacts [mem_insert_of_mem _ (mem_insert _ _), mem_insert _ _,
        (ih hW hz).elim (fun h => h ▸ mem_insert _ _)
          fun h => mem_insert_of_mem _ (mem_insert_of_mem _ h)]
  | @other u₀ w₀ g₀ W₀ W₀' hl hg hs ih =>
    cases h with
    | cons hl' hW =>
      obtain rfl := hl.right_unique hl'
      have hlink : d.skeleton.IsLink g₀ u₀ w₀ :=
        d.skeleton_isLink.2 (Or.inl ⟨hl, hg,
          fun hh => d.newEdge₁_notMem_edgeSet (hh ▸ hl.edge_mem),
          fun hh => d.newEdge₂_notMem_edgeSet (hh ▸ hl.edge_mem)⟩)
      rw [Graph.walkVertices_cons hlink, Graph.walkVertices_cons hl]
      intro z hz
      rcases hz with rfl | hz
      exacts [mem_insert_of_mem _ (mem_insert _ _),
        (ih hW hz).elim (fun h => h ▸ mem_insert _ _)
          fun h => mem_insert_of_mem _ (mem_insert_of_mem _ h)]

/-- **The corrected replacement of a path is a path.** The new vertex is fresh, so it cannot be
one the old path already visited, and every other vertex is visited exactly as before. This is
what carries vertex-simplicity of a boundary cycle across a subdivision. -/
theorem SubstWalk.isPath {u v : γ} {W W' : List γ} (hsub : d.SubstWalk u W W')
    (h : S.skel.IsPath u W v) : d.skeleton.IsPath u W' v := by
  induction hsub generalizing v with
  | nil u =>
    cases h with
    | nil hx =>
      exact .nil (by rw [d.skeleton_vertexSet]; exact mem_insert_of_mem _ hx)
  | @forward W₀ W₀' hs ih =>
    cases h with
    | cons hl hW hfresh =>
      obtain rfl := d.isLink.right_unique hl
      have hnd : d.edge ∉ W₀ :=
        (List.nodup_cons.1 (Graph.IsPath.cons hl hW hfresh).nodup).1
      obtain rfl : W₀' = W₀ := hs.eq_of_notMem hnd
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have hvert : d.skeleton.walkVertices d.right _ = S.skel.walkVertices d.right _ :=
        d.walkVertices_skeleton_eq hW.isWalk hnd
      refine .cons hlink₁ (.cons hlink₂ (ih hW) ?_) ?_
      · rw [hvert]
        exact fun hmem => d.newVertex_notMem
          (S.mem_cells_of_mem_vertexSet (hW.isWalk.walkVertices_subset hmem))
      · rw [Graph.walkVertices_cons hlink₂, hvert]
        rintro (h' | hmem)
        · exact d.newVertex_notMem (h' ▸ d.left_mem_cells)
        · exact hfresh hmem
  | @backward W₀ W₀' hs ih =>
    cases h with
    | cons hl hW hfresh =>
      obtain rfl := d.isLink.symm.right_unique hl
      have hnd : d.edge ∉ W₀ :=
        (List.nodup_cons.1 (Graph.IsPath.cons hl hW hfresh).nodup).1
      obtain rfl : W₀' = W₀ := hs.eq_of_notMem hnd
      have hlink₂ : d.skeleton.IsLink d.newEdge₂ d.right d.newVertex :=
        d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      have hlink₁ : d.skeleton.IsLink d.newEdge₁ d.newVertex d.left :=
        d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))
      have hvert : d.skeleton.walkVertices d.left _ = S.skel.walkVertices d.left _ :=
        d.walkVertices_skeleton_eq hW.isWalk hnd
      refine .cons hlink₂ (.cons hlink₁ (ih hW) ?_) ?_
      · rw [hvert]
        exact fun hmem => d.newVertex_notMem
          (S.mem_cells_of_mem_vertexSet (hW.isWalk.walkVertices_subset hmem))
      · rw [Graph.walkVertices_cons hlink₁, hvert]
        rintro (h' | hmem)
        · exact d.newVertex_notMem (h' ▸ d.right_mem_cells)
        · exact hfresh hmem
  | @other u₀ w₀ g₀ W₀ W₀' hl hg hs ih =>
    cases h with
    | cons hl' hW hfresh =>
      obtain rfl := hl.right_unique hl'
      have hlink : d.skeleton.IsLink g₀ u₀ w₀ :=
        d.skeleton_isLink.2 (Or.inl ⟨hl, hg,
          fun hh => d.newEdge₁_notMem_edgeSet (hh ▸ hl.edge_mem),
          fun hh => d.newEdge₂_notMem_edgeSet (hh ▸ hl.edge_mem)⟩)
      refine .cons hlink (ih hW) fun hmem => ?_
      rcases SubstWalk.walkVertices_subset (d := d) hs hW.isWalk hmem with rfl | hmem'
      · exact d.newVertex_notMem (S.mem_cells_of_mem_vertexSet hl.left_mem)
      · exact hfresh hmem'

/-- A path that avoids the subdivided edge is a path of the subdivided skeleton. -/
theorem isPath_skeleton_of_notMem {u v : γ} {W : List γ} (h : S.skel.IsPath u W v)
    (hW : d.edge ∉ W) : d.skeleton.IsPath u W v := by
  obtain ⟨W', hW'⟩ := d.exists_substWalk h.isWalk
  obtain rfl := hW'.eq_of_notMem hW
  exact SubstWalk.isPath hW' h

theorem newVertex_notMem_walkVertices {u v : γ} {W : List γ} (h : S.skel.IsPath u W v)
    (hW : d.edge ∉ W) : d.newVertex ∉ d.skeleton.walkVertices u W := by
  rw [d.walkVertices_skeleton_eq h.isWalk hW]
  exact fun hmem => d.newVertex_notMem
    (S.mem_cells_of_mem_vertexSet (h.isWalk.walkVertices_subset hmem))

/-- An old edge is never one of the two new ones. -/
theorem ne_newEdge_of_mem_edgeSet {g : γ} (hg : g ∈ E(S.skel)) :
    g ≠ d.newEdge₁ ∧ g ≠ d.newEdge₂ :=
  ⟨fun h => d.newEdge₁_notMem_edgeSet (h ▸ hg), fun h => d.newEdge₂_notMem_edgeSet (h ▸ hg)⟩

/-- **The boundary cycle survives an edge subdivision.** Three cases, and they are the three
constructors of `IsSubstWalk`: the walk either leaves the 2-cell's base point by the subdivided
edge — in one direction or the other, and then the new vertex is inserted right at the front of
the cycle — or it leaves by some other edge, and the correction happens further along. -/
theorem isCycle_newBoundary (bw : S.BoundaryWalks) (d : S.SubdivData)
    (hstart : d.boundaryStart = bw.start) {F : γ} (hF : F ∈ S.faces) :
    ∃ e v D, d.newBoundary F = e :: D.reverse ∧
      d.skeleton.IsCycleThrough e (bw.start F) v D := by
  obtain ⟨e, v, D, hb, hlink, hD, hnot⟩ := bw.isCycle hF
  have hsubst : d.SubstWalk (bw.start F) (S.boundary F) (d.newBoundary F) :=
    hstart ▸ d.newBoundary_isSubstWalk F _ (hstart ▸ bw.isWalk hF)
  rcases hsubst.cons_inv hb with ⟨rfl, hcase⟩ | ⟨hne, w, L', hL, hlw, hs⟩
  · -- The cycle leaves its base point by the subdivided edge, so the new vertex comes first.
    have hDrev : d.edge ∉ D.reverse := by simpa using hnot
    rcases hcase with ⟨hu, L', hL, hs⟩ | ⟨hu, L', hL, hs⟩
    · obtain rfl : L' = D.reverse := hs.eq_of_notMem hDrev
      obtain rfl : v = d.right := (d.isLink.right_unique (hu ▸ hlink)).symm
      refine ⟨d.newEdge₁, d.newVertex, D ++ [d.newEdge₂], by rw [hL, List.reverse_append]; rfl,
        ?_, ?_, ?_⟩
      · rw [hu]; exact d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · refine (d.isPath_skeleton_of_notMem hD hnot).extend_at_target
          (d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))).symm
          (d.newVertex_notMem_walkVertices hD hnot)
      · rw [List.mem_append]
        rintro (hmem | hmem)
        · exact (d.ne_newEdge_of_mem_edgeSet (hD.isWalk.edge_mem hmem)).1.symm rfl
        · exact d.newEdge_ne (List.eq_of_mem_singleton hmem)
    · obtain rfl : L' = D.reverse := hs.eq_of_notMem hDrev
      obtain rfl : v = d.left := (d.isLink.symm.right_unique (hu ▸ hlink)).symm
      refine ⟨d.newEdge₂, d.newVertex, D ++ [d.newEdge₁], by rw [hL, List.reverse_append]; rfl,
        ?_, ?_, ?_⟩
      · rw [hu]; exact d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, Sym2.eq_swap⟩))
      · refine (d.isPath_skeleton_of_notMem hD hnot).extend_at_target
          (d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, Sym2.eq_swap⟩))).symm
          (d.newVertex_notMem_walkVertices hD hnot)
      · rw [List.mem_append]
        rintro (hmem | hmem)
        · exact (d.ne_newEdge_of_mem_edgeSet (hD.isWalk.edge_mem hmem)).2.symm rfl
        · exact d.newEdge_ne (List.eq_of_mem_singleton hmem).symm
  · -- The cycle leaves by another edge, which survives; the correction is inside the path.
    obtain rfl : w = v := hlw.right_unique hlink
    have hpath : d.skeleton.IsPath w L' (bw.start F) := SubstWalk.isPath hs hD.reverse
    refine ⟨e, w, L'.reverse, by rw [hL, List.reverse_reverse], ?_, hpath.reverse, ?_⟩
    · exact d.skeleton_isLink.2 (Or.inl ⟨hlink, hne,
        (d.ne_newEdge_of_mem_edgeSet hlink.edge_mem).1,
        (d.ne_newEdge_of_mem_edgeSet hlink.edge_mem).2⟩)
    · rw [List.mem_reverse]
      intro hmem
      rcases SubstWalk.mem_of_mem (d := d) hs hmem with hmem' | rfl | rfl
      · exact hnot (by simpa using hmem')
      · exact (d.ne_newEdge_of_mem_edgeSet hlink.edge_mem).1 rfl
      · exact (d.ne_newEdge_of_mem_edgeSet hlink.edge_mem).2 rfl

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
  isCycle F hF := SubdivData.isCycle_newBoundary bw d hstart hF
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
        union_sdiff_distrib, sdiff_singleton_eq_self hFn, Set.sdiff_sdiff_comm]
    · rw [d.subcells_subdivideEdge_of_not_sub hF hedge,
        d.crossedCells_of_notMem fun h => hedge ((bw.mem_boundary_iff_sub hF
          d.edge_mem_edgeSet).1 h), union_empty, Set.sdiff_sdiff_comm]

/-! ### Preservation by a 2-cell split -/

namespace SplitData

variable (c : S.SplitData)

open scoped Classical in
@[simp] theorem splitFace_boundary_face₁ :
    (S.splitFace c).boundary c.face₁ = c.path₁ ++ c.earWalk.reverse := by
  change (if c.face₁ = c.face₁ then _ else _) = _
  rw [if_pos rfl]

open scoped Classical in
@[simp] theorem splitFace_boundary_face₂ :
    (S.splitFace c).boundary c.face₂ = c.path₂ ++ c.earWalk.reverse := by
  change (if c.face₂ = c.face₁ then _ else if c.face₂ = c.face₂ then _ else _) = _
  rw [if_neg c.face_ne.symm, if_pos rfl]

open scoped Classical in
theorem splitFace_boundary_of_ne {F : γ} (h₁ : F ≠ c.face₁) (h₂ : F ≠ c.face₂) :
    (S.splitFace c).boundary F = S.boundary F := by
  change (if F = c.face₁ then _ else if F = c.face₂ then _ else _) = _
  rw [if_neg h₁, if_neg h₂]

/-- An old walk runs through the same cells after a split: the skeleton only grows, and it grows
by edges the old walk does not take. -/
theorem coveredVertices_splitFace {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    (S.splitFace c).skel.coveredVertices W = S.skel.coveredVertices W := by
  ext z
  constructor
  · rintro ⟨f, hf, y, hy⟩
    rcases Graph.union_isLink.1 hy with hl | ⟨hne, -⟩
    · exact ⟨f, hf, y, hl⟩
    · exact absurd (h.edge_mem hf) hne
  · rintro ⟨f, hf, y, hy⟩
    exact ⟨f, hf, y, Or.inl hy⟩

theorem walkVertices_splitFace {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    (S.splitFace c).skel.walkVertices u W = S.skel.walkVertices u W := by
  rw [Graph.walkVertices, Graph.walkVertices, c.coveredVertices_splitFace h]

theorem pathCells_splitFace {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    (S.splitFace c).pathCells u W = S.pathCells u W := by
  simp only [pathCells, Graph.walkVertices, c.coveredVertices_splitFace h]

/-- An edge of the ear is incident in the new skeleton to exactly what it was incident to in the
ear: it is a fresh name, so the old skeleton has no say. -/
theorem inc_iff_of_mem_ear_edgeSet {f z : γ} (hf : f ∈ E(c.ear)) :
    (S.splitFace c).skel.Inc f z ↔ c.ear.Inc f z := by
  have hfS : f ∉ E(S.skel) := fun h => c.edge_fresh hf (S.mem_cells_of_mem_edgeSet h)
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (Graph.union_isLink.1 hy).elim (fun h => absurd h.edge_mem hfS) fun h => h.2⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Or.inr ⟨hfS, hy⟩⟩

/-- **The ear contributes exactly its own cells.** Its edge list is its edge set and the
vertices it visits are its vertex set, both by `Graph.IsPathGraph`. -/
theorem coveredVertices_earWalk : (S.splitFace c).skel.coveredVertices c.earWalk =
    c.ear.coveredVertices c.earWalk := by
  ext z
  constructor
  · rintro ⟨f, hf, hz⟩
    exact ⟨f, hf, (c.inc_iff_of_mem_ear_edgeSet (c.isPathGraph.mem_edgeSet hf)).1 hz⟩
  · rintro ⟨f, hf, hz⟩
    exact ⟨f, hf, (c.inc_iff_of_mem_ear_edgeSet (c.isPathGraph.mem_edgeSet hf)).2 hz⟩

/-- The vertices the ear's walk visits in the new skeleton are the ear's own vertices. -/
theorem walkVertices_earWalk :
    (S.splitFace c).skel.walkVertices c.source c.earWalk = V(c.ear) := by
  rw [Graph.walkVertices, c.coveredVertices_earWalk, c.isPathGraph.vertexSet_eq,
    Graph.walkVertices]

theorem pathCells_earWalk_reverse :
    (S.splitFace c).pathCells c.source c.earWalk.reverse = c.earCells := by
  have hcov := c.coveredVertices_earWalk
  ext z
  simp only [pathCells, Graph.walkVertices, Graph.coveredVertices_reverse, hcov, earCells,
    mem_union, mem_setOf_eq, List.mem_reverse, mem_insert_iff, c.isPathGraph.edgeSet_eq,
    c.isPathGraph.vertexSet_eq, Graph.walkVertices]
  tauto

/-- **The boundary cycle of a new 2-cell.** The boundary path the 2-cell was split along,
closed up by the ear. It is a *cycle* and not merely a closed walk because the ear meets the old
skeleton only at its two ends (`SplitData.vertexSet_inter`) and the path never returns to its
own source. Stated for one boundary path, so that both new 2-cells use it. -/
theorem isCycle_path_append_ear {P : List γ} (hP : S.skel.IsPath c.source P c.target)
    (hb : (S.splitFace c).boundary F = P ++ c.earWalk.reverse) :
    ∃ e v D, (S.splitFace c).boundary F = e :: D.reverse ∧
      (S.splitFace c).skel.IsCycleThrough e c.source v D := by
  obtain ⟨g, P₀, hp⟩ : ∃ g P₀, P = g :: P₀ := by
    rcases hl : P with _ | ⟨a, l⟩
    · exact absurd ((hl ▸ hP).isWalk.eq_of_nil) c.source_ne_target
    · exact ⟨a, l, rfl⟩
  have hP' : S.skel.IsPath c.source (g :: P₀) c.target := hp ▸ hP
  cases hP' with
  | cons hlink hP₀ hfresh =>
    have hear : (S.splitFace c).skel.IsPath c.source c.earWalk c.target :=
      c.isPathGraph.isPath.mono c.ear_le_skeleton
    have hrev : (S.splitFace c).skel.IsPath c.target P₀.reverse _ :=
      hP₀.reverse.mono c.le_skeleton
    have hmeet : ∀ y ∈ (S.splitFace c).skel.walkVertices c.source c.earWalk,
        y ∈ (S.splitFace c).skel.walkVertices c.target P₀.reverse → y = c.target := by
      intro y hy hy'
      rw [c.walkVertices_earWalk] at hy
      rw [c.walkVertices_splitFace hP₀.reverse.isWalk] at hy'
      have hyS : y ∈ V(S.skel) := hP₀.reverse.isWalk.walkVertices_subset hy'
      have hmem : y ∈ ({c.source, c.target} : Set γ) := by
        rw [← c.vertexSet_inter]; exact ⟨hy, hyS⟩
      rcases hmem with hys | hyt
      · subst hys
        rcases Graph.mem_walkVertices_iff.1 hy' with hy'' | hcov
        · exact absurd hy'' c.source_ne_target
        · exact absurd (Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_reverse ▸ hcov)) hfresh
      · exact hyt
    refine ⟨g, _, c.earWalk ++ P₀.reverse, ?_, hlink.mono c.le_skeleton,
      hear.append hrev hmeet, ?_⟩
    · rw [hb, hp, List.reverse_append, List.reverse_reverse]
      rfl
    · rw [List.mem_append]
      rintro (hmem | hmem)
      · exact c.edge_fresh (c.isPathGraph.mem_edgeSet hmem)
          (S.mem_cells_of_mem_edgeSet hlink.edge_mem)
      · exact (List.nodup_cons.1 (Graph.IsPath.cons hlink hP₀ hfresh).nodup).1
          (List.mem_reverse.1 hmem)

/-- The boundary cycles of the 2-cells a split does not touch are the old ones. -/
theorem isCycle_boundary_of_ne (bw : S.BoundaryWalks) (hF : F ∈ S.faces) (h₁ : F ≠ c.face₁)
    (h₂ : F ≠ c.face₂) :
    ∃ e v D, (S.splitFace c).boundary F = e :: D.reverse ∧
      (S.splitFace c).skel.IsCycleThrough e (bw.start F) v D := by
  obtain ⟨e, v, D, hb, hlink, hD, hnot⟩ := bw.isCycle hF
  exact ⟨e, v, D, by rw [c.splitFace_boundary_of_ne h₁ h₂, hb], hlink.mono c.le_skeleton,
    hD.mono c.le_skeleton, hnot⟩

theorem face₁_notMem_cells₁ : c.face₁ ∉ c.cells₁ := fun h => c.face₁_notMem (c.cells₁_subset h)

theorem face₂_notMem_cells₂ : c.face₂ ∉ c.cells₂ := fun h => c.face₂_notMem (c.cells₂_subset h)

theorem face₁_notMem_earCells : c.face₁ ∉ c.earCells := c.face₁_notMem_ear

theorem face₂_notMem_earCells : c.face₂ ∉ c.earCells := c.face₂_notMem_ear

/-- The subcells of an old 2-cell are untouched by a split. Needs the invariant, and only for
this: the split 2-cell `face` is not below any other 2-cell, which is `eq_of_sub_of_mem_faces`.
-/
theorem subcells_splitFace_of_ne (bw : S.BoundaryWalks) {F : γ} (hF : F ∈ S.faces)
    (hne : F ≠ c.face) : (S.splitFace c).subcells F = S.subcells F := by
  have hFn : F ∉ c.newCells := notMem_newCells_of_mem_cells (S.mem_cells_of_mem_faces hF)
  have hear : F ∉ E(c.ear) := fun h => c.edge_fresh h (S.mem_cells_of_mem_faces hF)
  ext σ
  rw [mem_subcells_iff, mem_subcells_iff, splitFace_sub]
  constructor
  · rintro ⟨hcell, h⟩
    rw [splitFace_cells] at hcell
    rcases h with ⟨h₁, -, h₃, -, h₅⟩ | ⟨rfl, h⟩ | h | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨(hcell.resolve_right h₁).1, h₅⟩
    · exact absurd h hFn
    · exact absurd h.edge_mem hear
    · exact absurd (Or.inr (Or.inl rfl)) hFn
    · exact absurd (Or.inr (Or.inr rfl)) hFn
  · rintro ⟨hcell, hsub⟩
    have hσf : σ ≠ c.face := fun h =>
      hne (bw.eq_of_sub_of_mem_faces c.face_mem hF (h ▸ hsub)).symm
    exact ⟨c.mem_splitFace_cells_of_old hcell hσf,
      Or.inl ⟨notMem_newCells_of_mem_cells hcell, hFn, hσf, hne, hsub⟩⟩

end SplitData

open scoped Classical in
/-- **The invariant survives a 2-cell split.** The two new 2-cells get the boundary path they
were split along, closed up by the ear; every other 2-cell keeps its walk, and a split adds no
cell below an old 2-cell. -/
noncomputable def BoundaryWalks.splitFace (bw : S.BoundaryWalks) (c : S.SplitData) :
    (S.splitFace c).BoundaryWalks where
  start F := if F = c.face₁ ∨ F = c.face₂ then c.source else bw.start F
  isCycle F hF := by
    rcases hF with rfl | rfl | ⟨hF, hne⟩
    · rw [if_pos (Or.inl rfl)]
      exact c.isCycle_path_append_ear c.isPath₁ c.splitFace_boundary_face₁
    · rw [if_pos (Or.inr rfl)]
      exact c.isCycle_path_append_ear c.isPath₂ c.splitFace_boundary_face₂
    · have h₁ : F ≠ c.face₁ := fun h => c.face₁_notMem (h ▸ S.mem_cells_of_mem_faces hF)
      have h₂ : F ≠ c.face₂ := fun h => c.face₂_notMem (h ▸ S.mem_cells_of_mem_faces hF)
      rw [if_neg (by rintro (h | h); exacts [h₁ h, h₂ h])]
      exact c.isCycle_boundary_of_ne bw hF h₁ h₂
  pathCells_eq F hF := by
    rcases hF with rfl | rfl | ⟨hF, hne⟩
    · have hL : (S.splitFace c).pathCells c.source ((S.splitFace c).boundary c.face₁)
          = c.cells₁ ∪ c.earCells := by
        rw [c.splitFace_boundary_face₁, pathCells_append, c.pathCells_splitFace c.isPath₁.isWalk,
          c.pathCells_earWalk_reverse]
        rfl
      rw [if_pos (Or.inl rfl), hL, c.subcells_face₁, union_sdiff_distrib, union_sdiff_distrib,
        Set.sdiff_self, empty_union, sdiff_singleton_eq_self c.face₁_notMem_earCells,
        sdiff_singleton_eq_self c.face₁_notMem_cells₁]
      exact union_comm _ _
    · have hL : (S.splitFace c).pathCells c.source ((S.splitFace c).boundary c.face₂)
          = c.cells₂ ∪ c.earCells := by
        rw [c.splitFace_boundary_face₂, pathCells_append, c.pathCells_splitFace c.isPath₂.isWalk,
          c.pathCells_earWalk_reverse]
        rfl
      rw [if_pos (Or.inr rfl), hL, c.subcells_face₂, union_sdiff_distrib, union_sdiff_distrib,
        Set.sdiff_self, empty_union, sdiff_singleton_eq_self c.face₂_notMem_earCells,
        sdiff_singleton_eq_self c.face₂_notMem_cells₂]
      exact union_comm _ _
    · have h₁ : F ≠ c.face₁ := fun h => c.face₁_notMem (h ▸ S.mem_cells_of_mem_faces hF)
      have h₂ : F ≠ c.face₂ := fun h => c.face₂_notMem (h ▸ S.mem_cells_of_mem_faces hF)
      rw [if_neg (by rintro (h | h); exacts [h₁ h, h₂ h]), c.splitFace_boundary_of_ne h₁ h₂,
        c.pathCells_splitFace (bw.isWalk hF), c.subcells_splitFace_of_ne bw hF hne,
        bw.pathCells_eq hF]

/-! ### Cutting a boundary cycle at two of its 0-cells

The consumer-facing theorem: this is the package `CellStructure.SplitData` asks for, and the
reason the invariant had to carry a cycle rather than a closed walk. -/

namespace BoundaryWalks

variable (bw : S.BoundaryWalks)

/-- A 0-cell below a 2-cell lies on its boundary cycle. -/
theorem mem_walkVertices_of_sub {D : List γ} {e v : γ} (hF : F ∈ S.faces)
    (hb : S.boundary F = e :: D.reverse) (hcyc : S.skel.IsCycleThrough e (bw.start F) v D)
    (hz : u ∈ V(S.skel)) (hsub : S.sub u F) : u ∈ S.skel.walkVertices (bw.start F) D := by
  have hwalk : S.skel.IsWalk (bw.start F) (e :: D.reverse) (bw.start F) := hb ▸ bw.isWalk hF
  have hV : S.skel.walkVertices (bw.start F) (e :: D.reverse) =
      S.skel.walkVertices (bw.start F) D := by
    have hv : v ∈ insert (bw.start F) (S.skel.coveredVertices D) :=
      hcyc.isPath.target_mem_walkVertices
    ext z
    simp only [Graph.walkVertices, Graph.coveredVertices, mem_insert_iff, mem_setOf_eq,
      List.mem_cons, List.mem_reverse, exists_eq_or_imp]
    constructor
    · rintro (rfl | hinc | hz)
      · exact Or.inl rfl
      · rcases hcyc.isLink.inc_iff.1 hinc with rfl | rfl
        · exact Or.inl rfl
        · exact mem_insert_iff.1 hv
      · exact Or.inr hz
    · rintro (rfl | hz)
      exacts [Or.inl rfl, Or.inr (Or.inr hz)]
  have hmem : u ∈ S.pathCells (bw.start F) (S.boundary F) := by
    rw [bw.pathCells_eq hF]
    exact ⟨⟨S.mem_cells_of_mem_vertexSet hz, hsub⟩,
      fun h => S.faces_ne_vertexSet hF hz h.symm⟩
  rw [hb] at hmem
  rcases hmem with hlist | hvert
  · exact absurd rfl (S.vertexSet_ne_edgeSet hz (hwalk.edge_mem hlist))
  · rwa [hV] at hvert

/-- The cells of a walk that already visits its own base point are its edges and the vertices
its edges touch. -/
theorem pathCells_of_mem_covered {x : γ} {L : List γ} (hx : x ∈ S.skel.coveredVertices L) :
    S.pathCells x L = {c | c ∈ L} ∪ S.skel.coveredVertices L := by
  simp only [pathCells, Graph.walkVertices]
  rw [Set.insert_eq_self.2 hx]

/-- **Two distinct 0-cells below a 2-cell cut its boundary into two paths between them.**
The two paths carry exactly the cells below the 2-cell, and they meet in nothing but the two
0-cells themselves — which are, in order, the `sub_face` and `paths_meet` fields of
`CellStructure.SplitData`, with `isPath₁` and `isPath₂` alongside. `EarStep` calls this at the
two ends of the ear. -/
theorem exists_boundary_paths (bw : S.BoundaryWalks) (hS : S.CombInvariants)
    (hF : F ∈ S.faces) {a b : γ}
    (ha : a ∈ V(S.skel)) (hbv : b ∈ V(S.skel)) (hsa : S.sub a F) (hsb : S.sub b F) (hab : a ≠ b) :
    ∃ P₁ P₂, S.skel.IsPath a P₁ b ∧ S.skel.IsPath a P₂ b ∧
      (∀ ⦃σ⦄, S.sub σ F ↔ σ = F ∨ σ ∈ S.pathCells a P₁ ∪ S.pathCells a P₂) ∧
      S.pathCells a P₁ ∩ S.pathCells a P₂ = {a, b} := by
  obtain ⟨e, v, D, hb, hcyc⟩ := bw.isCycle hF
  obtain ⟨D₁, D₂, hp₁, hp₂, hperm, hmeet⟩ := hcyc.split_at
    (bw.mem_walkVertices_of_sub hF hb hcyc ha hsa)
    (bw.mem_walkVertices_of_sub hF hb hcyc hbv hsb) hab
  -- The two arcs are the cycle cut in two: same edges, and no edge twice.
  have hcovperm : S.skel.coveredVertices (D₁ ++ D₂) = S.skel.coveredVertices (e :: D) := by
    ext z
    exact ⟨fun ⟨g, hg, hz⟩ => ⟨g, hperm.mem_iff.1 hg, hz⟩,
      fun ⟨g, hg, hz⟩ => ⟨g, hperm.mem_iff.2 hg, hz⟩⟩
  have hnodup : (D₁ ++ D₂).Nodup :=
    hperm.symm.nodup (List.nodup_cons.2 ⟨hcyc.notMem, hcyc.isPath.nodup⟩)
  have hdisj : ∀ g, g ∈ D₁ → g ∈ D₂ → False := fun g hg₁ hg₂ =>
    List.disjoint_of_nodup_append hnodup hg₁ hg₂
  -- Each arc is nonempty — its two ends are distinct — so each end lies on one of its edges.
  have hacov : a ∈ S.skel.coveredVertices D₁ := by
    cases hp₁ with
    | nil => exact absurd rfl hab
    | cons hl _ _ => exact ⟨_, List.mem_cons_self, hl.inc_left⟩
  have hbcov : b ∈ S.skel.coveredVertices D₂ := by
    cases hp₂ with
    | nil => exact absurd rfl hab.symm
    | cons hl _ _ => exact ⟨_, List.mem_cons_self, hl.inc_left⟩
  have hacov₂ : a ∈ S.skel.coveredVertices D₂ :=
    (Graph.mem_walkVertices_iff.1 hp₂.isWalk.target_mem_walkVertices).resolve_left hab
  have hacov₂' : a ∈ S.skel.coveredVertices D₂.reverse := by
    rwa [Graph.coveredVertices_reverse]
  have hbcov' : b ∈ S.skel.coveredVertices D₂.reverse := by
    rwa [Graph.coveredVertices_reverse]
  have hp₂' : S.skel.IsPath a D₂.reverse b := hp₂.reverse
  refine ⟨D₁, D₂.reverse, hp₁, hp₂', fun σ => ?_, ?_⟩
  · -- The cells below the 2-cell are the cells of the cycle, and the two arcs cover it.
    have hcells : S.pathCells a D₁ ∪ S.pathCells a D₂.reverse =
        S.pathCells (bw.start F) (S.boundary F) := by
      have hstart : bw.start F ∈ S.skel.coveredVertices (e :: D) :=
        ⟨e, List.mem_cons_self, hcyc.isLink.inc_left⟩
      have hcovrev : S.skel.coveredVertices (e :: D.reverse) =
          S.skel.coveredVertices (e :: D) := by
        ext z
        simp only [Graph.coveredVertices, mem_setOf_eq, List.mem_cons, List.mem_reverse]
      rw [hb, pathCells_of_mem_covered hacov,
        pathCells_of_mem_covered hacov₂',
        pathCells_of_mem_covered (hcovrev ▸ hstart)]
      have hrev : ∀ z : γ, z ∈ e :: D.reverse ↔ z ∈ e :: D := by
        intro z; simp only [List.mem_cons, List.mem_reverse]
      ext z
      simp only [mem_union, mem_setOf_eq, List.mem_reverse, Graph.coveredVertices]
      constructor
      · rintro ((hz | hz) | (hz | hz))
        · exact Or.inl ((hrev z).2 (hperm.mem_iff.1 (List.mem_append_left _ hz)))
        · obtain ⟨g, hg, hzg⟩ := hz
          exact Or.inr ⟨g, (hrev g).2 (hperm.mem_iff.1 (List.mem_append_left _ hg)), hzg⟩
        · exact Or.inl ((hrev z).2 (hperm.mem_iff.1 (List.mem_append_right _ hz)))
        · obtain ⟨g, hg, hzg⟩ := hz
          exact Or.inr ⟨g, (hrev g).2 (hperm.mem_iff.1 (List.mem_append_right _ hg)), hzg⟩
      · rintro (hz | ⟨g, hg, hzg⟩)
        · rcases List.mem_append.1 (hperm.mem_iff.2 ((hrev z).1 hz)) with hz' | hz'
          exacts [Or.inl (Or.inl hz'), Or.inr (Or.inl hz')]
        · rcases List.mem_append.1 (hperm.mem_iff.2 ((hrev g).1 hg)) with hg' | hg'
          exacts [Or.inl (Or.inr ⟨g, hg', hzg⟩), Or.inr (Or.inr ⟨g, hg', hzg⟩)]
    rw [hcells, bw.pathCells_eq hF]
    constructor
    · intro h
      by_cases hσ : σ = F
      · exact Or.inl hσ
      · exact Or.inr ⟨⟨hS.sub_mem_left h, h⟩, hσ⟩
    · rintro (rfl | ⟨⟨-, h⟩, -⟩)
      · exact hS.sub_refl (S.mem_cells_of_mem_faces hF)
      · exact h
  · -- The two arcs meet in the two cut points and nothing else.
    ext z
    constructor
    · rintro ⟨hz₁, hz₂⟩
      rcases hz₁ with hz₁ | hz₁ <;> rcases hz₂ with hz₂ | hz₂
      · exact absurd (hdisj z hz₁ ((List.mem_reverse (as := D₂)).1 hz₂)) not_false
      · exact absurd rfl (S.vertexSet_ne_edgeSet (hp₂'.isWalk.walkVertices_subset hz₂)
          (hp₁.isWalk.edge_mem hz₁))
      · exact absurd rfl (S.vertexSet_ne_edgeSet (hp₁.isWalk.walkVertices_subset hz₁)
          (hp₂'.isWalk.edge_mem (show z ∈ D₂.reverse from hz₂)))
      · rcases Graph.mem_walkVertices_iff.1 hz₂ with hza | hcov
        · exact Or.inl hza
        · exact hmeet z hz₁ (Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_reverse (G := S.skel) (W := D₂) ▸ hcov))
    · rintro (rfl | rfl)
      · exact ⟨Or.inr Graph.mem_walkVertices_self, Or.inr Graph.mem_walkVertices_self⟩
      · exact ⟨Or.inr hp₁.target_mem_walkVertices,
          Or.inr (Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_reverse (G := S.skel) (W := D₂) ▸ hbcov))⟩

end BoundaryWalks

end CellStructure

end Schoenflies
