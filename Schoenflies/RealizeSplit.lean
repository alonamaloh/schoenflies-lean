/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CellulationInvariants
import Schoenflies.JordanClosed
import Schoenflies.Graph.PathGraph

/-!
# Realizing a 2-cell split

`Schoenflies/CellulationInvariants.lean` proves the *step* theorems of the second elementary
operation: given a realization `R'` of `S.splitFace d` standing in the relation
`SplitData.IsCrosscutSplit` to a realization `R` of `S`, the two invariants of
`lem:cellulation-invariants` propagate. Nothing built such an `R'`. This module does.

## Blueprint

* `def:generated-structure`, operation 2 — the 2-cell split whose realization is constructed
  here.
* `lem:cellulation-invariants` (i), (vii) — the invariants that
  `SplitData.IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` derives from the output of
  this module.
* `thm:general-crosscut` (`Schoenflies.crosscut_theorem`) — what turns the constructed ear into
  the two new open 2-cells; it is applied inside `IsCrosscutSplit.isRefinement`, and this module
  supplies its hypotheses.

## What is constructed

* `Schoenflies.CellStructure.SplitData.EarCrosscut` — the geometric input: an assignment of
  points to the ear's vertices and of parametrizations to the ear's edges, drawing the ear as a
  polygonal crosscut of the realized open 2-cell.
* `Schoenflies.CellStructure.SplitData.realize` — the realization of `S.splitFace d` built from
  `R` and such an ear. It is a `def` with lemmas, not an existential: `realize_pos`,
  `realize_drawing`, `realize_cell_of_old`, `realize_cell_face₁`, … name every component.
* `Schoenflies.CellStructure.SplitData.isCrosscutSplit_realize` — the constructed realization
  stands in the relation `IsCrosscutSplit` to `R`. Composed with
  `IsCrosscutSplit.isCellDecomposition_and_isFaceJordan` this is the full induction step.

## The general lemmas this needed

Three facts about drawings and paths had no home on `main` and are proved here in the root
`Graph` namespace. If a second consumer appears they belong in `Schoenflies/Graph/`:

* `Graph.IsPath.map`, `Graph.walkVertices_map`, `Graph.IsPathGraph.map` — a path pushes forward
  along an injective relabelling of the vertices. `Graph.IsWalk.map` was already on `main` (in
  `Schoenflies/CombinatorialInvariance.lean`); the path version needs the injectivity, because
  the freshness clause is a *non*-membership.
* `Graph.IsDrawing.isArcBetween_walkPointSet` — **the point set of a drawn path is a simple
  arc between its two ends.** This is the workhorse: it is what makes the realized ear an arc
  (so `IsCrosscut` applies) and what makes each realized boundary path an arc (so `IsCutPair`
  applies). The induction is on `Graph.IsPath`, and the freshness clause of a path is exactly
  what rules out the returning point that would break `IsArcBetween.concatenate`.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

/-! ### Pushing a path forward along a relabelling -/

section Map

variable {α α' β : Type*} {G : Graph α β} {f : α → α'} {u v : α} {W : List β}

theorem coveredVertices_map (f : α → α') :
    (G.map f).coveredVertices W = f '' G.coveredVertices W := by
  ext x
  simp only [mem_coveredVertices_iff, map_inc, Set.mem_image]
  constructor
  · rintro ⟨e, he, v, hv, rfl⟩
    exact ⟨v, ⟨e, he, hv⟩, rfl⟩
  · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
    exact ⟨e, he, v, hv, rfl⟩

theorem walkVertices_map (f : α → α') (u : α) (W : List β) :
    (G.map f).walkVertices (f u) W = f '' G.walkVertices u W := by
  rw [walkVertices, walkVertices, coveredVertices_map, Set.image_insert_eq]

/-- **A path pushes forward along an injective relabelling.** Unlike `Graph.IsWalk.map` this
needs the injectivity: the freshness clause is a non-membership, and only an injective map
reflects it. -/
theorem IsPath.map (hf : InjOn f V(G)) (h : G.IsPath u W v) : (G.map f).IsPath (f u) W (f v) := by
  induction h with
  | nil hx => exact .nil (by simpa using Set.mem_image_of_mem f hx)
  | @cons u w v e W hl hW hfresh ih =>
    refine .cons (hl.map f) ih ?_
    rw [walkVertices_map]
    rintro ⟨z, hz, hzf⟩
    have hzV : z ∈ V(G) := walkVertices_subset_vertexSet hW.isWalk.left_mem hz
    exact hfresh (hf hzV hl.left_mem hzf ▸ hz)

/-- Relabelling commutes with the union. Both sides resolve a shared edge name in favour of
the left-hand graph, and `Graph.map` keeps the edge set, so the two resolutions agree. -/
theorem map_union (G H : Graph α β) (f : α → α') :
    (G.union H).map f = (G.map f).union (H.map f) := by
  refine Graph.ext (by simp [Set.image_union]) fun e x y => ?_
  simp only [map_isLink, union_isLink, Relation.map_apply, edgeSet_map]
  constructor
  · rintro ⟨a, b, hab | ⟨he, hab⟩, rfl, rfl⟩
    · exact Or.inl ⟨a, b, hab, rfl, rfl⟩
    · exact Or.inr ⟨he, a, b, hab, rfl, rfl⟩
  · rintro (⟨a, b, hab, rfl, rfl⟩ | ⟨he, a, b, hab, rfl, rfl⟩)
    · exact ⟨a, b, Or.inl hab, rfl, rfl⟩
    · exact ⟨a, b, Or.inr ⟨he, hab⟩, rfl, rfl⟩

theorem IsPathGraph.map {P : Graph α β} (hf : InjOn f V(P)) (h : P.IsPathGraph u W v) :
    (P.map f).IsPathGraph (f u) W (f v) where
  isPath := h.isPath.map hf
  edgeSet_eq := by rw [edgeSet_map]; exact h.edgeSet_eq
  vertexSet_eq := by rw [vertexSet_map, walkVertices_map, h.vertexSet_eq]

end Map

section Drawing

variable {β : Type*} {H K : Graph Plane β} {drw : β → ℝ → Plane}

/-! ### The point set of a drawn path

`Graph.pointSet` reads the vertex set and the edge set of a graph. Along a walk both are read
off the list instead, and that is the form the induction below runs on. -/

/-- The point set a walk occupies: the vertices it visits together with the arcs of its
edges. For a path graph this is the whole of `Graph.pointSet` (`walkPointSet_eq_pointSet`). -/
def walkPointSet (H : Graph Plane β) (drw : β → ℝ → Plane) (u : Plane) (W : List β) : Set Plane :=
  H.walkVertices u W ∪ ⋃ e ∈ ({e | e ∈ W} : Set β), edgeArc drw e

theorem walkPointSet_eq_pointSet {u v : Plane} {W : List β} (h : H.IsPathGraph u W v) :
    walkPointSet H drw u W = pointSet H drw := by
  rw [walkPointSet, pointSet, h.vertexSet_eq, h.edgeSet_eq]

theorem walkPointSet_nil (u : Plane) : walkPointSet H drw u ([] : List β) = {u} := by
  rw [walkPointSet, walkVertices_nil]
  simp

/-- Peeling the first step off a walk peels its arc off the point set. The vertex the step
departs from is an end of that arc, which is why nothing is left behind. -/
theorem walkPointSet_cons (hD : IsDrawing H drw) {e : β} {u w : Plane} {W : List β}
    (hl : H.IsLink e u w) :
    walkPointSet H drw u (e :: W) = edgeArc drw e ∪ walkPointSet H drw w W := by
  have hu : u ∈ edgeArc drw e := (hD.edge_isArcBetween hl).left_mem
  have hset : ({f | f ∈ e :: W} : Set β) = insert e {f | f ∈ W} := by
    ext f; simp [List.mem_cons]
  rw [walkPointSet, walkPointSet, walkVertices_cons hl, hset, Set.biUnion_insert]
  refine Set.Subset.antisymm ?_ ?_
  · rintro z (hz | hz)
    · rcases hz with rfl | hz
      · exact Or.inl hu
      · exact Or.inr (Or.inl hz)
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
  · rintro z (hz | hz | hz)
    · exact Or.inr (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr (Or.inr hz)

/-- **The point set of a drawn path is a simple arc between its two ends.**

The two pieces glued at each step are the arc of the first edge and the point set of the rest
of the path, and `IsArcBetween.concatenate` asks that they meet only at the vertex between
them. That is precisely the freshness clause of `Graph.IsPath`: the vertex the path departs
from is not among those the rest of it visits, and every point the first arc shares with the
rest of the drawing is a vertex the rest visits — a vertex by `vertex_mem_edgeArc` if it is
one of the rest's vertices, and by `edge_inter` if it lies on one of the rest's arcs. -/
theorem IsDrawing.isArcBetween_walkPointSet (hD : IsDrawing H drw) :
    ∀ {u v : Plane} {W : List β}, H.IsPath u W v → u ≠ v →
      IsArcBetween (walkPointSet H drw u W) u v := by
  intro u v W hp
  induction hp with
  | nil => exact fun h => absurd rfl h
  | @cons u w v e W hl hW hfresh ih =>
    intro _
    rw [walkPointSet_cons hD hl]
    have harc : IsArcBetween (edgeArc drw e) u w := hD.edge_isArcBetween hl
    by_cases hwv : w = v
    · subst hwv
      rw [hW.eq_nil_of_eq, walkPointSet_nil,
        Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.2 harc.right_mem)]
      exact harc
    · refine harc.concatenate (ih hwv) ?_
      intro z hz hz'
      -- every point the first arc shares with the rest is a vertex the rest visits
      have hzw : z ∈ H.walkVertices w W := by
        rcases hz' with hz' | hz'
        · exact hz'
        · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hz'
          have hfe : e ≠ f := by
            rintro rfl
            exact (List.nodup_cons.1 (IsPath.cons hl hW hfresh).nodup).1 hf
          exact mem_walkVertices_of_mem_covered ⟨f, hf,
            (hD.edge_inter hl.edge_mem (hW.isWalk.edge_mem hf) hfe hz hzf).2.2⟩
      have hzV : z ∈ V(H) := walkVertices_subset_vertexSet hW.isWalk.left_mem hzw
      rcases hD.vertex_mem_edgeArc hl hzV hz with rfl | rfl
      · exact absurd hzw hfresh
      · rfl

theorem IsDrawing.isArcBetween_pointSet (hD : IsDrawing H drw) {u v : Plane} {W : List β}
    (h : H.IsPathGraph u W v) (huv : u ≠ v) : IsArcBetween (pointSet H drw) u v := by
  rw [← walkPointSet_eq_pointSet h]
  exact hD.isArcBetween_walkPointSet h.isPath huv

end Drawing

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-! ## What a realization does to a walk

Two facts about an existing realization, both of the shape "the realized cells of a piece of
the skeleton occupy the point set that piece of the drawing occupies". They are what let the
crosscut theorem, which speaks of point sets, be fed from the cell structure, which speaks of
cells. -/

namespace Realization

variable (R : S.Realization)

theorem walkVertices_graph (u : γ) (W : List γ) :
    R.graph.walkVertices (R.pos u) W = R.pos '' S.skel.walkVertices u W :=
  Graph.walkVertices_map _ _ _

/-- **The realized cells of a path occupy the point set the drawn path occupies.** The two
differ only in the endpoints an open 1-cell drops, and those are the points of the 0-cells the
walk visits. -/
theorem cellUnion_pathCells {u v : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    R.cellUnion (S.pathCells u W) = Graph.walkPointSet R.graph R.drawing (R.pos u) W := by
  have hsub : S.skel.walkVertices u W ⊆ V(S.skel) :=
    Graph.walkVertices_subset_vertexSet h.left_mem
  have hV : R.cellUnion (S.skel.walkVertices u W) = R.pos '' S.skel.walkVertices u W := by
    refine Set.Subset.antisymm (cellUnion_subset fun z hz => ?_) ?_
    · rw [R.cell_vertex (hsub hz)]
      exact Set.singleton_subset_iff.2 ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cell_subset_cellUnion hz (by rw [R.cell_vertex (hsub hz)]; rfl)
  rw [CellStructure.pathCells, cellUnion_union, hV, Graph.walkPointSet, R.walkVertices_graph]
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.union_subset (cellUnion_subset fun f hf => ?_) Set.subset_union_left
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    rw [R.cell_edge hl]
    exact fun x hx => Or.inr (Set.mem_biUnion hf hx.1)
  · refine Set.union_subset Set.subset_union_right (Set.iUnion₂_subset fun f hf x hx => ?_)
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem hf)
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · exact Or.inr ⟨a, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_left⟩, rfl⟩
      · exact Or.inr ⟨b, Graph.mem_walkVertices_of_mem_covered ⟨f, hf, hl.inc_right⟩, rfl⟩
    · exact Or.inl (cell_subset_cellUnion hf (by rw [R.cell_edge hl]; exact ⟨hx, hxab⟩))

/-- The drawn skeleton is covered by the open cells of dimension 0 and 1. -/
theorem skeletonSet_subset_cellUnion :
    R.skeletonSet ⊆ R.cellUnion (V(S.skel) ∪ E(S.skel)) := by
  intro x hx
  rcases hx with hx | hx
  · rw [Realization.vertexSet_graph] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    refine cell_subset_cellUnion (Set.mem_union_left _ hz) ?_
    rw [R.cell_vertex hz]
    rfl
  · obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hx
    rw [Realization.edgeSet_graph] at hf
    obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
    by_cases hxab : x ∈ ({R.pos a, R.pos b} : Set Plane)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
      rcases hxab with rfl | rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.left_mem) ?_
        rw [R.cell_vertex hl.left_mem]
        rfl
      · refine cell_subset_cellUnion (Set.mem_union_left _ hl.right_mem) ?_
        rw [R.cell_vertex hl.right_mem]
        rfl
    · refine cell_subset_cellUnion (Set.mem_union_right _ hf) ?_
      rw [R.cell_edge hl]
      exact ⟨hxf, hxab⟩

/-- **An open 2-cell misses the drawn skeleton.** Immediate from the disjointness clause of
assertion (i): the skeleton is covered by cells of lower dimension. -/
theorem disjoint_cell_skeletonSet {D : Set Plane} (hcd : R.IsCellDecomposition D) {F : γ}
    (hF : F ∈ S.faces) : Disjoint (R.cell F) R.skeletonSet := by
  refine Set.disjoint_right.2 fun x hx hxF => ?_
  obtain ⟨σ, hσ, hxσ⟩ := mem_cellUnion_iff.1 (R.skeletonSet_subset_cellUnion hx)
  have hne : F ≠ σ := by
    rintro rfl
    rcases hσ with hσ | hσ
    exacts [Set.disjoint_left.1 S.disjoint_faces_vertexSet hF hσ,
      Set.disjoint_left.1 S.disjoint_faces_edgeSet hF hσ]
  have hσc : σ ∈ S.cells := by
    rcases hσ with hσ | hσ
    exacts [S.mem_cells_of_mem_vertexSet hσ, S.mem_cells_of_mem_edgeSet hσ]
  exact Set.disjoint_left.1 (hcd.disjoint (S.mem_cells_of_mem_faces hF) hσc hne) hxF hxσ

end Realization

/-! ## The ear, drawn

`SplitData` fixes the *abstract* ear: a path graph `d.ear` glued to the skeleton at
`d.source` and `d.target`. Drawing it means choosing a point for each of its vertices and a
parametrization for each of its edges. `EarCrosscut` is the bundle of conditions under which
that drawing is a polygonal crosscut of the realized open 2-cell `R.cell d.face`. -/

namespace SplitData

variable (d : S.SplitData)

theorem source_mem_ear : d.source ∈ V(d.ear) :=
  (d.vertexSet_inter ▸ (Set.mem_insert _ _ : d.source ∈ ({d.source, d.target} : Set γ))).1

theorem target_mem_ear : d.target ∈ V(d.ear) :=
  (d.vertexSet_inter ▸
    (Set.mem_insert_of_mem _ rfl : d.target ∈ ({d.source, d.target} : Set γ))).1

theorem source_mem_cells₂ : d.source ∈ d.cells₂ :=
  Or.inr Graph.mem_walkVertices_self

theorem target_mem_cells₂ : d.target ∈ d.cells₂ :=
  Or.inr d.isPath₂.isWalk.target_mem_walkVertices

/-- **The cells strictly below the split 2-cell are the cells of its two boundary paths.**
This is `SplitData.sub_face` read as a set identity; with assertion (i) it identifies the
frontier of the old open 2-cell with the two realized boundary paths. -/
theorem subcells_face_diff : S.subcells d.face \ {d.face} = d.cells₁ ∪ d.cells₂ := by
  ext σ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, CellStructure.mem_subcells_iff, Set.mem_union]
  constructor
  · rintro ⟨⟨-, hsub⟩, hne⟩
    rcases d.sub_face.1 hsub with rfl | h
    · exact absurd rfl hne
    · exact h
  · intro h
    refine ⟨⟨?_, d.sub_face.2 (Or.inr h)⟩, ?_⟩
    · rcases h with h | h
      exacts [d.cells₁_subset h, d.cells₂_subset h]
    · rcases h with h | h
      exacts [d.cells₁_ne_face h, d.cells₂_ne_face h]

/-- The drawn ear: the abstract ear pushed into the plane along the chosen positions. -/
def earGraph (d : S.SplitData) (earPos : γ → Plane) : Graph Plane γ := d.ear.map earPos

@[simp] theorem vertexSet_earGraph (earPos : γ → Plane) :
    V(d.earGraph earPos) = earPos '' V(d.ear) := Graph.vertexSet_map _ _

@[simp] theorem edgeSet_earGraph (earPos : γ → Plane) :
    E(d.earGraph earPos) = E(d.ear) := Graph.edgeSet_map _ _

/-- The point set the drawn ear occupies: the crosscut `P` of `thm:general-crosscut`. -/
def earSet (d : S.SplitData) (earPos : γ → Plane) (earDraw : γ → ℝ → Plane) : Set Plane :=
  Graph.pointSet (d.earGraph earPos) earDraw

/-- **The geometric input of one 2-cell split.** A position for each vertex of the abstract
ear and a parametrization for each of its edges, drawing the ear as a polygonal crosscut of
the realized open 2-cell `R.cell d.face`.

Every clause is a statement about the ear's own drawing, and every one of them is what the
finite-transfer module has in hand when it produces a crosscut from
`Schoenflies.exists_crosscut_of_polyAccessible`: it starts from a simple polygonal arc `P`
inside the face with its two ends on the boundary, and cuts `P` into the ear's edges. -/
structure EarCrosscut (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) : Prop where
  /-- The ear starts where the old 0-cell `d.source` sits. -/
  pos_source : earPos d.source = R.pos d.source
  /-- …and ends where `d.target` sits. -/
  pos_target : earPos d.target = R.pos d.target
  /-- Distinct vertices of the ear are drawn at distinct points. -/
  injOn : InjOn earPos V(d.ear)
  /-- The ear is drawn as a plane graph. -/
  isDrawing : Graph.IsDrawing (d.earGraph earPos) earDraw
  /-- Every point of the drawn ear but its two ends is inside the old open 2-cell. -/
  subset_face : d.earSet earPos earDraw \ {R.pos d.source, R.pos d.target} ⊆ R.cell d.face
  /-- The drawn ear is polygonal. -/
  polygonal : IsPolygonal (d.earSet earPos earDraw)

namespace EarCrosscut

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
theorem source_ne_target_pos : R.pos d.source ≠ R.pos d.target := fun h =>
  d.source_ne_target (R.injOn_pos d.source_mem_skel d.target_mem_skel h)

theorem mem_earSet_of_mem_ear {z : γ} (hz : z ∈ V(d.ear)) : earPos z ∈ d.earSet earPos earDraw :=
  Graph.vertexSet_subset_pointSet (by rw [d.vertexSet_earGraph]; exact ⟨z, hz, rfl⟩)

theorem edgeArc_subset_earSet {f : γ} (hf : f ∈ E(d.ear)) :
    Graph.edgeArc earDraw f ⊆ d.earSet earPos earDraw :=
  Graph.edgeArc_subset_pointSet (by rw [d.edgeSet_earGraph]; exact hf)

variable (hE : d.EarCrosscut R earPos earDraw)

include hE

/-- On the two ends — the only vertices the ear shares with the old skeleton — the ear's
positions agree with the old ones. -/
theorem earPos_eq {z : γ} (hz : z ∈ V(d.ear)) (hz' : z ∈ V(S.skel)) : earPos z = R.pos z := by
  have : z ∈ ({d.source, d.target} : Set γ) := d.vertexSet_inter ▸ ⟨hz, hz'⟩
  rcases this with rfl | rfl
  exacts [hE.pos_source, hE.pos_target]

theorem pos_source_mem_earSet : R.pos d.source ∈ d.earSet earPos earDraw :=
  hE.pos_source ▸ mem_earSet_of_mem_ear d.source_mem_ear

theorem pos_target_mem_earSet : R.pos d.target ∈ d.earSet earPos earDraw :=
  hE.pos_target ▸ mem_earSet_of_mem_ear d.target_mem_ear

/-- An interior vertex of the ear is drawn strictly inside the old open 2-cell. -/
theorem earPos_mem_cell_face {z : γ} (hz : z ∈ V(d.ear)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : earPos z ∈ R.cell d.face := by
  refine hE.subset_face ⟨mem_earSet_of_mem_ear hz, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h)
  · exact hs (hE.injOn hz d.source_mem_ear (h.trans hE.pos_source.symm))
  · exact ht (hE.injOn hz d.target_mem_ear (h.trans hE.pos_target.symm))

/-- **The drawn ear meets the old skeleton exactly in its two ends.** The interior of the ear
is inside the open 2-cell, and an open 2-cell misses the drawn skeleton. -/
theorem earSet_inter_skeletonSet {D : Set Plane} (hcd : R.IsCellDecomposition D) :
    d.earSet earPos earDraw ∩ R.skeletonSet ⊆ {R.pos d.source, R.pos d.target} := by
  rintro x ⟨hx, hx'⟩
  by_contra hcon
  exact Set.disjoint_left.1 (R.disjoint_cell_skeletonSet hcd d.face_mem)
    (hE.subset_face ⟨hx, hcon⟩) hx'

/-- **An ear edge's arc meets the ear's vertices exactly at its own two ends**, so dropping
all of the ear's vertices from it is the same as dropping its own two ends. This is what makes
the definition of the new open 1-cells independent of a choice of orientation. -/
theorem edgeArc_diff {f a b : γ} (hl : d.ear.IsLink f a b) :
    Graph.edgeArc earDraw f \ earPos '' V(d.ear) =
      Graph.edgeArc earDraw f \ {earPos a, earPos b} := by
  have hlm : (d.earGraph earPos).IsLink f (earPos a) (earPos b) := hl.map earPos
  refine Set.Subset.antisymm (Set.sdiff_subset_sdiff_right ?_) (fun x ⟨hx, hx'⟩ => ⟨hx, ?_⟩)
  · rintro _ (rfl | rfl)
    exacts [⟨a, hl.left_mem, rfl⟩, ⟨b, hl.right_mem, rfl⟩]
  · rintro ⟨w, hw, rfl⟩
    have hwV : earPos w ∈ V(d.earGraph earPos) := by
      rw [d.vertexSet_earGraph]; exact ⟨w, hw, rfl⟩
    exact hx' (hE.isDrawing.vertex_mem_edgeArc hlm hwV hx)

end EarCrosscut

/-! ## The realization built from a drawn ear -/

open scoped Classical in
/-- Where the split puts each 0-cell: the ear's vertices go where the ear's drawing puts them,
everything else stays. On the ear's two ends the two prescriptions agree. -/
noncomputable def splitPos (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane) :
    γ → Plane := fun z => if z ∈ V(d.ear) then earPos z else R.pos z

open scoped Classical in
/-- How the split draws each 1-cell. -/
noncomputable def splitDrawing (d : S.SplitData) (R : S.Realization)
    (earDraw : γ → ℝ → Plane) : γ → ℝ → Plane :=
  fun f => if f ∈ E(d.ear) then earDraw f else R.drawing f

open scoped Classical in
/-- The point set of each open cell after the split: the two new 2-cells are the two sides of
the crosscut, the ear's vertices and edges are their points and their open arcs, and every
surviving cell keeps its old point set. -/
noncomputable def splitCell (d : S.SplitData) (R : S.Realization) (earPos : γ → Plane)
    (earDraw : γ → ℝ → Plane) : γ → Set Plane := fun σ =>
  if σ = d.face₁ then inside (R.cellUnion d.cells₁ ∪ d.earSet earPos earDraw)
  else if σ = d.face₂ then inside (R.cellUnion d.cells₂ ∪ d.earSet earPos earDraw)
  else if σ ∈ V(d.ear) ∧ σ ∉ V(S.skel) then {earPos σ}
  else if σ ∈ E(d.ear) then Graph.edgeArc earDraw σ \ earPos '' V(d.ear)
  else R.cell σ

variable {d} {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}

theorem splitPos_of_mem_ear {z : γ} (hz : z ∈ V(d.ear)) : d.splitPos R earPos z = earPos z := by
  classical
  simp only [splitPos, if_pos hz]

theorem splitPos_of_notMem_ear {z : γ} (hz : z ∉ V(d.ear)) : d.splitPos R earPos z = R.pos z := by
  classical
  simp only [splitPos, if_neg hz]

theorem EarCrosscut.splitPos_eq (hE : d.EarCrosscut R earPos earDraw) {z : γ}
    (hz : z ∈ V(S.skel)) : d.splitPos R earPos z = R.pos z := by
  by_cases hz' : z ∈ V(d.ear)
  · rw [splitPos_of_mem_ear hz', hE.earPos_eq hz' hz]
  · rw [splitPos_of_notMem_ear hz']

theorem splitDrawing_of_mem_ear {f : γ} (hf : f ∈ E(d.ear)) :
    d.splitDrawing R earDraw f = earDraw f := by
  classical
  simp only [splitDrawing, if_pos hf]

theorem splitDrawing_of_mem_skel {f : γ} (hf : f ∈ E(S.skel)) :
    d.splitDrawing R earDraw f = R.drawing f := by
  classical
  simp only [splitDrawing, if_neg (Set.disjoint_left.1 d.disjoint_edgeSet hf)]

theorem splitCell_face₁ : d.splitCell R earPos earDraw d.face₁ =
    inside (R.cellUnion d.cells₁ ∪ d.earSet earPos earDraw) := by
  classical
  unfold splitCell
  rw [if_pos rfl]

theorem splitCell_face₂ : d.splitCell R earPos earDraw d.face₂ =
    inside (R.cellUnion d.cells₂ ∪ d.earSet earPos earDraw) := by
  classical
  unfold splitCell
  rw [if_neg (Ne.symm d.face_ne), if_pos rfl]

theorem splitCell_of_mem_cells {σ : γ} (hσ : σ ∈ S.cells) :
    d.splitCell R earPos earDraw σ = R.cell σ := by
  classical
  have h₁ : σ ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem hσ
  have h₂ : σ ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem hσ
  have h₃ : ¬ (σ ∈ V(d.ear) ∧ σ ∉ V(S.skel)) := by
    rintro ⟨hv, hnv⟩
    rcases d.mem_cells_of_mem_ear_vertexSet hv hσ with rfl | rfl
    exacts [hnv d.source_mem_skel, hnv d.target_mem_skel]
  have h₄ : σ ∉ E(d.ear) := fun h => d.edge_fresh h hσ
  unfold splitCell
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄]

theorem EarCrosscut.splitCell_earVertex (hE : d.EarCrosscut R earPos earDraw) {z : γ}
    (hz : z ∈ V(d.ear)) : d.splitCell R earPos earDraw z = {earPos z} := by
  classical
  by_cases hz' : z ∈ V(S.skel)
  · rw [splitCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hz'), R.cell_vertex hz',
      hE.earPos_eq hz hz']
  · have h₁ : z ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem_ear (Or.inl hz)
    have h₂ : z ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem_ear (Or.inl hz)
    unfold splitCell
    rw [if_neg h₁, if_neg h₂, if_pos (show z ∈ V(d.ear) ∧ z ∉ V(S.skel) from ⟨hz, hz'⟩)]

theorem splitCell_earEdge {f : γ} (hf : f ∈ E(d.ear)) :
    d.splitCell R earPos earDraw f = Graph.edgeArc earDraw f \ earPos '' V(d.ear) := by
  classical
  have h₁ : f ≠ d.face₁ := by rintro rfl; exact d.face₁_notMem_ear (Or.inr hf)
  have h₂ : f ≠ d.face₂ := by rintro rfl; exact d.face₂_notMem_ear (Or.inr hf)
  have h₃ : ¬ (f ∈ V(d.ear) ∧ f ∉ V(S.skel)) := fun h =>
    Set.disjoint_left.1 d.ear_disjoint h.1 hf
  unfold splitCell
  rw [if_neg h₁, if_neg h₂, if_neg h₃, if_pos hf]

end SplitData

end CellStructure

end Schoenflies
