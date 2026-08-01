/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.CombinatorialInvariance
import Schoenflies.Graph.PathGraph
import Schoenflies.GeneralCrosscut

/-!
# Generated matched cell structures

The spine of Part II. `def:generated-structure` says that every cell structure the Schönflies
construction ever meets is obtained from the initial two-face structure of
`prop:initial-pair` by a finite sequence of two elementary operations — *edge subdivision* and
*2-cell splitting by an ear* — performed simultaneously in the two realizations. This module
builds the two operations as `def`s on `Schoenflies.CellStructure`, closes them into the
inductive `Schoenflies.GeneratedStructure`, and proves the assertions of
`lem:cellulation-invariants` that are within reach.

## Blueprint

* `Schoenflies.CellStructure.SubdivData`, `Schoenflies.CellStructure.subdivideEdge` — the first
  elementary operation of `def:generated-structure` (tex, operation 1).
* `Schoenflies.CellStructure.SplitData`, `Schoenflies.CellStructure.splitFace` — the second
  (tex, operation 2).
* `Schoenflies.GeneratedStructure` — `def:generated-structure`, as the inductive closure of a
  base structure under the two operations.
* `Schoenflies.CellStructure.SubdivData.parent`,
  `Schoenflies.CellStructure.SplitData.parent`,
  `Schoenflies.CellStructure.SubdivData.sub_parent`,
  `Schoenflies.CellStructure.SplitData.sub_parent` — assertion (iv) of
  `lem:cellulation-invariants`, the parent map of one elementary refinement and the
  compatibility `σ ≼ τ → par σ ≼ par τ`.
* `Schoenflies.CellStructure.CombInvariants` and its two preservation theorems
  `.subdivideEdge`, `.splitFace`, closed by
  `Schoenflies.GeneratedStructure.combInvariants` — assertions (iii), (v), (vi), together with
  the abstract form of (viii) and the bookkeeping facts about `≼_abs` that the blueprint uses
  silently.
* `Schoenflies.CellStructure.Realization.IsCellDecomposition` — assertion (i) for one
  realization, and from it, with no further geometry:
  `.frontier_property` (assertion (ii)), `.sub_iff_subset_closure` and
  `Schoenflies.CellStructure.subset_closure_congr` (assertion (ix)), and `.face_eq`
  (assertion (viii)).
* `Schoenflies.crosscut_cell_partition` — the geometric content of one 2-cell split, from
  `Schoenflies.general_crosscut`, in the shape assertion (i) consumes.

## Design

**The base case is a parameter.** `prop:initial-pair` is being built elsewhere, so
`GeneratedStructure S₀ S` is relative to an arbitrary base `S₀`, and every invariant theorem
reads "the invariants of `S₀` propagate to `S`". That is both cleaner and independent of the
initial pair's schedule: the consumer supplies `S₀` and the base case, and gets the invariant
at every stage.

**`rem:intermediate-disconnection` is honoured by omission.** Nothing in this module mentions
`Realization.nonboundary`, let alone its connectedness: an intermediate stage really can have
disconnected open nonboundary part, and every statement here is proved without that hypothesis.

**`≼_abs` stays a raw datum.** `CellStructure.sub` is not made a preorder. The reflexivity and
transitivity facts that the blueprint uses are fields of `CombInvariants`, established for the
base and propagated, never assumed of an arbitrary `CellStructure`.

**Fidelity note on reflexivity.** The blueprint's two update lists (tex, operations 1 and 2)
do not mention the reflexive pairs of the *new* cells, while the base relation is declared to
contain "the reflexive pairs". Assertion (i) forces them: the closure of a new open cell
contains that cell, and (i) says a closed cell is the union of its open subcells. Both `subRel`
definitions below therefore declare `σ ≼ σ` for every new cell; that is the only place where
this module adds a pair the blueprint's prose does not list.
-/

open Set Schoenflies
open scoped Graph

namespace Schoenflies

variable {γ : Type*}

/-! ### Subdividing an edge of a graph

The graph-theoretic half of the first elementary operation, stated for an arbitrary graph so
that one definition serves both the skeleton and the outer cycle: when `H` does not carry `e`
from `x` to `y` — which is the case for the outer cycle whenever the subdivided edge is not an
outer edge — the construction leaves `H` alone (`subdivGraph_eq_self`). Without that, the
definition of `CellStructure.subdivideEdge` would need a case split on whether the subdivided
edge is outer, and every lemma about it would inherit the split. -/

/-- The graph `H` with the edge `e`, running from `x` to `y`, replaced by a new vertex `v` and
two new edges `e₁ : x — v`, `e₂ : v — y`.

The three guards `f ≠ e`, `f ≠ e₁`, `f ≠ e₂` on the surviving links make the three disjuncts
mutually exclusive with no hypotheses, and `hne` does the same for the last two. The freshness
hypotheses `h₁`, `h₂` are what make `edgeSet` right. -/
def subdivGraph (H : Graph γ γ) (e x y v e₁ e₂ : γ) (hne : e₁ ≠ e₂)
    (h₁ : e₁ ∉ E(H)) (h₂ : e₂ ∉ E(H)) : Graph γ γ where
  vertexSet := V(H) ∪ {z | z = v ∧ H.IsLink e x y}
  edgeSet := (E(H) \ {e}) ∪ {f | (f = e₁ ∨ f = e₂) ∧ H.IsLink e x y}
  IsLink f a b :=
    (H.IsLink f a b ∧ f ≠ e ∧ f ≠ e₁ ∧ f ≠ e₂) ∨
      (f = e₁ ∧ H.IsLink e x y ∧ s(a, b) = s(x, v)) ∨
      (f = e₂ ∧ H.IsLink e x y ∧ s(a, b) = s(v, y))
  isLink_symm _ _ :=
    { symm := by
        rintro a b (⟨hl, hf, hf₁, hf₂⟩ | ⟨rfl, hl, hs⟩ | ⟨rfl, hl, hs⟩)
        · exact Or.inl ⟨hl.symm, hf, hf₁, hf₂⟩
        · exact Or.inr (Or.inl ⟨rfl, hl, Sym2.eq_swap.trans hs⟩)
        · exact Or.inr (Or.inr ⟨rfl, hl, Sym2.eq_swap.trans hs⟩) }
  eq_or_eq_of_isLink_of_isLink := by
    rintro f a b c d h h'
    rcases h with ⟨hl, -, hf₁, hf₂⟩ | ⟨hfe, -, hs⟩ | ⟨hfe, -, hs⟩ <;>
      rcases h' with ⟨hl', -, hg₁, hg₂⟩ | ⟨hge, -, hs'⟩ | ⟨hge, -, hs'⟩
    · exact hl.left_eq_or_eq hl'
    · exact absurd hge hf₁
    · exact absurd hge hf₂
    · exact absurd hfe hg₁
    · have := Sym2.eq_iff.1 (hs.trans hs'.symm); tauto
    · exact absurd (hfe.symm.trans hge) hne
    · exact absurd hfe hg₂
    · exact absurd (hge.symm.trans hfe) hne
    · have := Sym2.eq_iff.1 (hs.trans hs'.symm); tauto
  edge_mem_iff_exists_isLink f := by
    constructor
    · rintro (⟨hf, hfe⟩ | ⟨hf, hl⟩)
      · obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet hf
        exact ⟨a, b, Or.inl ⟨hab, hfe, fun h => h₁ (h ▸ hf), fun h => h₂ (h ▸ hf)⟩⟩
      · rcases hf with rfl | rfl
        · exact ⟨x, v, Or.inr (Or.inl ⟨rfl, hl, rfl⟩)⟩
        · exact ⟨v, y, Or.inr (Or.inr ⟨rfl, hl, rfl⟩)⟩
    · rintro ⟨a, b, (⟨hl, hf, -, -⟩ | ⟨rfl, hl, -⟩ | ⟨rfl, hl, -⟩)⟩
      · exact Or.inl ⟨hl.edge_mem, hf⟩
      · exact Or.inr ⟨Or.inl rfl, hl⟩
      · exact Or.inr ⟨Or.inr rfl, hl⟩
  left_mem_of_isLink := by
    rintro f a b (⟨hl, -, -, -⟩ | ⟨rfl, hl, hs⟩ | ⟨rfl, hl, hs⟩)
    · exact Or.inl hl.left_mem
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl hl.left_mem
      · exact Or.inr ⟨rfl, hl⟩
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr ⟨rfl, hl⟩
      · exact Or.inl hl.right_mem

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

@[simp] theorem subdivGraph_vertexSet {hne h₁ h₂} :
    V(subdivGraph H e x y v e₁ e₂ hne h₁ h₂) = V(H) ∪ {z | z = v ∧ H.IsLink e x y} := rfl

@[simp] theorem subdivGraph_edgeSet {hne h₁ h₂} :
    E(subdivGraph H e x y v e₁ e₂ hne h₁ h₂) =
      (E(H) \ {e}) ∪ {f | (f = e₁ ∨ f = e₂) ∧ H.IsLink e x y} := rfl

theorem subdivGraph_isLink {hne h₁ h₂} {f a b : γ} :
    (subdivGraph H e x y v e₁ e₂ hne h₁ h₂).IsLink f a b ↔
      (H.IsLink f a b ∧ f ≠ e ∧ f ≠ e₁ ∧ f ≠ e₂) ∨
        (f = e₁ ∧ H.IsLink e x y ∧ s(a, b) = s(x, v)) ∨
        (f = e₂ ∧ H.IsLink e x y ∧ s(a, b) = s(v, y)) := Iff.rfl

/-- Subdividing is monotone in the graph: a subgraph carrying the subdivided edge is subdivided
along with the whole, and one that does not carry it is left alone and still fits inside. This
is what gives `CellStructure.subdivideEdge` its `outerGraph_le`. -/
theorem subdivGraph_mono (hHK : H ≤ K) {hne h₁ h₂ h₁' h₂'} :
    subdivGraph H e x y v e₁ e₂ hne h₁ h₂ ≤ subdivGraph K e x y v e₁ e₂ hne h₁' h₂' where
  vertexSet_mono := by
    rintro z (hz | ⟨rfl, hl⟩)
    · exact Or.inl (hHK.vertexSet_mono hz)
    · exact Or.inr ⟨rfl, hHK.isLink_mono hl⟩
  isLink_mono := by
    rintro f a b (⟨hl, hf, hf₁, hf₂⟩ | ⟨rfl, hl, hs⟩ | ⟨rfl, hl, hs⟩)
    · exact Or.inl ⟨hHK.isLink_mono hl, hf, hf₁, hf₂⟩
    · exact Or.inr (Or.inl ⟨rfl, hHK.isLink_mono hl, hs⟩)
    · exact Or.inr (Or.inr ⟨rfl, hHK.isLink_mono hl, hs⟩)

/-- A graph that does not carry the subdivided edge is untouched. -/
theorem subdivGraph_eq_self {hne h₁ h₂} (he : e ∉ E(H)) :
    subdivGraph H e x y v e₁ e₂ hne h₁ h₂ = H := by
  have hno : ¬ H.IsLink e x y := fun h => he h.edge_mem
  refine Graph.ext ?_ fun f a b => ?_
  · simp [hno]
  · simp only [subdivGraph_isLink, hno, and_false, false_and, or_false]
    refine ⟨fun hl => hl.1, fun hl => ⟨hl, ?_, ?_, ?_⟩⟩
    exacts [fun h => he (h ▸ hl.edge_mem), fun h => h₁ (h ▸ hl.edge_mem),
      fun h => h₂ (h ▸ hl.edge_mem)]

/-- An edge of a subgraph has the same ends there as in the ambient graph. General; it is
here because nothing on `main` states it, and both elementary operations need it to know that
the outer cycle carries the subdivided edge with its own endpoints. -/
theorem isLink_of_le_of_mem_edgeSet (hHK : H ≤ K) (he : e ∈ E(H)) (h : K.IsLink e x y) :
    H.IsLink e x y := by
  obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
  rcases (hHK.isLink_mono hab).eq_and_eq_or_eq_and_eq h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [hab, hab.symm]

/-! ### The cells of an abstract structure -/

namespace CellStructure

variable (S : CellStructure γ)

theorem mem_cells_of_mem_vertexSet {z : γ} (h : z ∈ V(S.skel)) : z ∈ S.cells :=
  Or.inl (Or.inl h)

theorem mem_cells_of_mem_edgeSet {z : γ} (h : z ∈ E(S.skel)) : z ∈ S.cells :=
  Or.inl (Or.inr h)

theorem mem_cells_of_mem_faces {z : γ} (h : z ∈ S.faces) : z ∈ S.cells := Or.inr h

theorem vertexSet_ne_edgeSet {z w : γ} (hz : z ∈ V(S.skel)) (hw : w ∈ E(S.skel)) : z ≠ w :=
  fun h => Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet hz (h ▸ hw)

theorem faces_ne_vertexSet {z w : γ} (hz : z ∈ S.faces) (hw : w ∈ V(S.skel)) : z ≠ w :=
  fun h => Set.disjoint_left.1 S.disjoint_faces_vertexSet hz (h ▸ hw)

theorem faces_ne_edgeSet {z w : γ} (hz : z ∈ S.faces) (hw : w ∈ E(S.skel)) : z ≠ w :=
  fun h => Set.disjoint_left.1 S.disjoint_faces_edgeSet hz (h ▸ hw)

/-- The cells of a walk: its edges, and the vertices it visits. This is what the blueprint
calls "the cells of the boundary walk `Bᵢ`". -/
def pathCells (u : γ) (W : List γ) : Set γ := {c | c ∈ W} ∪ S.skel.walkVertices u W

variable {S}

theorem pathCells_subset_cells {u : γ} {W : List γ} (h : S.skel.IsWalk u W v) :
    S.pathCells u W ⊆ S.cells := by
  rintro z (hz | hz)
  · exact S.mem_cells_of_mem_edgeSet (h.edge_mem hz)
  · exact S.mem_cells_of_mem_vertexSet (h.walkVertices_subset hz)

/-! ### Elementary operation 1: edge subdivision

Blueprint, `def:generated-structure`, operation 1: "the edge `e` is replaced by a new vertex
`v` and two new edges `e₁, e₂`, whose endpoints are `v` together with one old endpoint of `e`
each; the relation `≼_abs` is extended by declaring `v ≼ e₁` and `v ≼ e₂`, each old endpoint of
`e` a subcell of its adjacent new edge, and `v, e₁, e₂` subcells of exactly the old strict
supercells of `e`; all pairs not involving `e` are unchanged." -/

/-- The data of one **edge subdivision**: the edge to be subdivided together with its two
endpoints, and three names — fresh, i.e. not cells of `S` — for the new vertex and the two new
edges. The operation is a `def` of this data, not an existential: everything downstream refers
to `d.newVertex`, `d.newEdge₁`, `d.newEdge₂` by name. -/
structure SubdivData (S : CellStructure γ) where
  /-- The subdivided 1-cell. -/
  edge : γ
  /-- One endpoint of the subdivided edge. -/
  left : γ
  /-- The other endpoint. -/
  right : γ
  /-- The inserted 0-cell. -/
  newVertex : γ
  /-- The new 1-cell from `left` to `newVertex`. -/
  newEdge₁ : γ
  /-- The new 1-cell from `newVertex` to `right`. -/
  newEdge₂ : γ
  /-- `edge` really runs from `left` to `right`. -/
  isLink : S.skel.IsLink edge left right
  /-- The new vertex is a fresh name. -/
  newVertex_notMem : newVertex ∉ S.cells
  /-- The first new edge is a fresh name. -/
  newEdge₁_notMem : newEdge₁ ∉ S.cells
  /-- The second new edge is a fresh name. -/
  newEdge₂_notMem : newEdge₂ ∉ S.cells
  /-- The three new names are distinct. -/
  newVertex_ne₁ : newVertex ≠ newEdge₁
  /-- The three new names are distinct. -/
  newVertex_ne₂ : newVertex ≠ newEdge₂
  /-- The three new names are distinct. -/
  newEdge_ne : newEdge₁ ≠ newEdge₂

namespace SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

/-- The three cells the subdivision creates. -/
def newCells : Set γ := {d.newVertex, d.newEdge₁, d.newEdge₂}

variable {d}

theorem notMem_cells_of_mem_newCells {z : γ} (h : z ∈ d.newCells) : z ∉ S.cells := by
  rcases h with rfl | rfl | rfl
  exacts [d.newVertex_notMem, d.newEdge₁_notMem, d.newEdge₂_notMem]

theorem notMem_newCells_of_mem_cells {z : γ} (h : z ∈ S.cells) : z ∉ d.newCells := fun hz =>
  notMem_cells_of_mem_newCells hz h

variable (d)

theorem edge_mem_edgeSet : d.edge ∈ E(S.skel) := d.isLink.edge_mem

theorem edge_mem_cells : d.edge ∈ S.cells := S.mem_cells_of_mem_edgeSet d.edge_mem_edgeSet

theorem left_mem_cells : d.left ∈ S.cells := S.mem_cells_of_mem_vertexSet d.isLink.left_mem

theorem right_mem_cells : d.right ∈ S.cells := S.mem_cells_of_mem_vertexSet d.isLink.right_mem

theorem newEdge₁_notMem_edgeSet : d.newEdge₁ ∉ E(S.skel) := fun h =>
  d.newEdge₁_notMem (S.mem_cells_of_mem_edgeSet h)

theorem newEdge₂_notMem_edgeSet : d.newEdge₂ ∉ E(S.skel) := fun h =>
  d.newEdge₂_notMem (S.mem_cells_of_mem_edgeSet h)

theorem newEdge₁_notMem_outer : d.newEdge₁ ∉ E(S.outerGraph) := fun h =>
  d.newEdge₁_notMem_edgeSet (S.outerGraph_le.edgeSet_mono h)

theorem newEdge₂_notMem_outer : d.newEdge₂ ∉ E(S.outerGraph) := fun h =>
  d.newEdge₂_notMem_edgeSet (S.outerGraph_le.edgeSet_mono h)

/-- The subdivided skeleton. -/
def skeleton : Graph γ γ :=
  subdivGraph S.skel d.edge d.left d.right d.newVertex d.newEdge₁ d.newEdge₂
    d.newEdge_ne d.newEdge₁_notMem_edgeSet d.newEdge₂_notMem_edgeSet

/-- The subdivided outer cycle. When the subdivided edge is not an outer edge this is the old
outer cycle unchanged (`SubdivData.outer_eq`). -/
def outer : Graph γ γ :=
  subdivGraph S.outerGraph d.edge d.left d.right d.newVertex d.newEdge₁ d.newEdge₂
    d.newEdge_ne d.newEdge₁_notMem_outer d.newEdge₂_notMem_outer

theorem outer_le_skeleton : d.outer ≤ d.skeleton := subdivGraph_mono S.outerGraph_le

@[simp] theorem skeleton_vertexSet : V(d.skeleton) = insert d.newVertex V(S.skel) := by
  ext z
  simp only [skeleton, subdivGraph_vertexSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.isLink, and_true]
  tauto

@[simp] theorem skeleton_edgeSet :
    E(d.skeleton) = insert d.newEdge₁ (insert d.newEdge₂ (E(S.skel) \ {d.edge})) := by
  ext f
  simp only [skeleton, subdivGraph_edgeSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.isLink, and_true]
  tauto

theorem skeleton_isLink {f a b : γ} :
    d.skeleton.IsLink f a b ↔
      (S.skel.IsLink f a b ∧ f ≠ d.edge ∧ f ≠ d.newEdge₁ ∧ f ≠ d.newEdge₂) ∨
        (f = d.newEdge₁ ∧ s(a, b) = s(d.left, d.newVertex)) ∨
        (f = d.newEdge₂ ∧ s(a, b) = s(d.newVertex, d.right)) := by
  simp only [skeleton, subdivGraph_isLink, d.isLink, true_and]

/-- The outer cycle is untouched when the subdivided edge is not outer. -/
theorem outer_eq (he : d.edge ∉ E(S.outerGraph)) : d.outer = S.outerGraph :=
  subdivGraph_eq_self he

/-- The subdivided edge, when it is outer, is outer with its own two endpoints. -/
theorem outer_isLink (he : d.edge ∈ E(S.outerGraph)) :
    S.outerGraph.IsLink d.edge d.left d.right :=
  isLink_of_le_of_mem_edgeSet S.outerGraph_le he d.isLink

theorem outer_edgeSet_of_mem (he : d.edge ∈ E(S.outerGraph)) :
    E(d.outer) = insert d.newEdge₁ (insert d.newEdge₂ (E(S.outerGraph) \ {d.edge})) := by
  ext f
  simp only [outer, subdivGraph_edgeSet, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_insert_iff, d.outer_isLink he, and_true]
  tauto

/-- **The abstract subcell relation after an edge subdivision.** Read off the blueprint's
update list, in order: the old pairs that involve neither `e` nor a new cell; the reflexive
pairs of the new cells (see the fidelity note in the module docstring); `v ≼ e₁, e₂`; each old
endpoint below its adjacent new edge; and the new cells below exactly the old *strict*
supercells of `e`. -/
def subRel : γ → γ → Prop := fun σ τ =>
  (σ ∉ d.newCells ∧ τ ∉ d.newCells ∧ σ ≠ d.edge ∧ τ ≠ d.edge ∧ S.sub σ τ) ∨
    (σ = τ ∧ σ ∈ d.newCells) ∨
    (σ = d.newVertex ∧ (τ = d.newEdge₁ ∨ τ = d.newEdge₂)) ∨
    (σ = d.left ∧ τ = d.newEdge₁) ∨
    (σ = d.right ∧ τ = d.newEdge₂) ∨
    (σ ∈ d.newCells ∧ τ ≠ d.edge ∧ S.sub d.edge τ)

end SubdivData

open scoped Classical in
/-- **Elementary operation 1: edge subdivision.** The abstract-data update of
`def:generated-structure`, operation 1.

The boundary walks are updated by replacing every occurrence of the subdivided edge by the two
new edges. `boundary` is a raw datum of `CellStructure` and the blueprint's update list does
not spell out its behaviour under a subdivision; the orientation of the replacement is
therefore *not* guaranteed to make the walk a walk, and nothing below reads it. -/
noncomputable def subdivideEdge (S : CellStructure γ) (d : S.SubdivData) : CellStructure γ where
  skel := d.skeleton
  faces := S.faces
  outerGraph := d.outer
  outerGraph_le := d.outer_le_skeleton
  boundary F := (S.boundary F).flatMap fun f =>
    if f = d.edge then [d.newEdge₁, d.newEdge₂] else [f]
  sub := d.subRel
  finite_vertexSet := by
    rw [d.skeleton_vertexSet]; exact S.finite_vertexSet.insert _
  finite_edgeSet := by
    rw [d.skeleton_edgeSet]
    exact ((S.finite_edgeSet.diff).insert _).insert _
  finite_faces := S.finite_faces
  disjoint_vertexSet_edgeSet := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [d.skeleton_vertexSet, Set.mem_insert_iff] at hz
    rw [d.skeleton_edgeSet, Set.mem_insert_iff, Set.mem_insert_iff] at hz'
    rcases hz with rfl | hz
    · rcases hz' with h | h | hz'
      · exact d.newVertex_ne₁ h
      · exact d.newVertex_ne₂ h
      · exact d.newVertex_notMem (S.mem_cells_of_mem_edgeSet hz'.1)
    · rcases hz' with rfl | rfl | hz'
      · exact d.newEdge₁_notMem (S.mem_cells_of_mem_vertexSet hz)
      · exact d.newEdge₂_notMem (S.mem_cells_of_mem_vertexSet hz)
      · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet hz hz'.1
  disjoint_faces_vertexSet := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [d.skeleton_vertexSet, Set.mem_insert_iff] at hz'
    rcases hz' with rfl | hz'
    · exact d.newVertex_notMem (S.mem_cells_of_mem_faces hz)
    · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz hz'
  disjoint_faces_edgeSet := by
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [d.skeleton_edgeSet, Set.mem_insert_iff, Set.mem_insert_iff] at hz'
    rcases hz' with rfl | rfl | hz'
    · exact d.newEdge₁_notMem (S.mem_cells_of_mem_faces hz)
    · exact d.newEdge₂_notMem (S.mem_cells_of_mem_faces hz)
    · exact Set.disjoint_left.1 S.disjoint_faces_edgeSet hz hz'.1

variable {S : CellStructure γ} (d : S.SubdivData)

@[simp] theorem subdivideEdge_skel : (S.subdivideEdge d).skel = d.skeleton := rfl

@[simp] theorem subdivideEdge_faces : (S.subdivideEdge d).faces = S.faces := rfl

@[simp] theorem subdivideEdge_outerGraph : (S.subdivideEdge d).outerGraph = d.outer := rfl

@[simp] theorem subdivideEdge_sub {σ τ : γ} :
    (S.subdivideEdge d).sub σ τ ↔ d.subRel σ τ := Iff.rfl

/-- The cells after a subdivision: the old ones except the subdivided edge, plus the three new
ones. -/
theorem subdivideEdge_cells : (S.subdivideEdge d).cells = (S.cells \ {d.edge}) ∪ d.newCells := by
  ext z
  simp only [cells, subdivideEdge_skel, subdivideEdge_faces, d.skeleton_vertexSet,
    d.skeleton_edgeSet, SubdivData.newCells, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_diff]
  constructor
  · rintro ((hz | hz) | hz)
    · rcases hz with rfl | hz
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨S.mem_cells_of_mem_vertexSet hz,
          S.vertexSet_ne_edgeSet hz d.edge_mem_edgeSet⟩
    · rcases hz with rfl | rfl | ⟨hz, hz'⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl ⟨S.mem_cells_of_mem_edgeSet hz, hz'⟩
    · exact Or.inl ⟨S.mem_cells_of_mem_faces hz, S.faces_ne_edgeSet hz d.edge_mem_edgeSet⟩
  · rintro (⟨hz, hz'⟩ | rfl | rfl | rfl)
    · rcases hz with (hz | hz) | hz
      · exact Or.inl (Or.inl (Or.inr hz))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hz, hz'⟩)))
      · exact Or.inr hz
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))

/-! ### Elementary operation 2: splitting a 2-cell by an ear

Blueprint, `def:generated-structure`, operation 2: "the 2-cell `R` is replaced by `R₁, R₂`; the
new interior vertices and edges of the ear `P` are added with their incidences along `P` (each
interior vertex a subcell of its two adjacent ear edges, each ear endpoint a subcell of its
adjacent ear edge); the relation `≼_abs` is extended by declaring every cell of the boundary
walk of `Rᵢ`, together with every cell of `P`, a subcell of `Rᵢ`, for `i = 1, 2`; no 2-cell is
declared a subcell of another, and all pairs not involving `R` or the new cells are unchanged."

The ear enters as a *graph* `ear` together with `Graph.IsPathGraph`, rather than as a bare list
of names: the incidences "along `P`" are then `ear.Inc`, and the union `S.skel.union ear` is
the new skeleton with no further bookkeeping. -/

/-- The data of one **2-cell split by an ear**: the split 2-cell, two fresh names for the two
new 2-cells, and the ear — a path graph whose two ends are old vertices and all of whose other
cells are fresh — together with the two boundary paths of the split cell between the ends of
the ear.

`sub_face` is the statement that the two boundary paths carry exactly the cells of the split
2-cell; `paths_disjoint` that they share no edge. Both are consequences of the invariants at
the stage being refined, and both are what the blueprint means by "the two boundary paths
between its endpoints". -/
structure SplitData (S : CellStructure γ) where
  /-- The 2-cell being split. -/
  face : γ
  /-- The first new 2-cell, bounded by `path₁` and the ear. -/
  face₁ : γ
  /-- The second new 2-cell, bounded by `path₂` and the ear. -/
  face₂ : γ
  /-- The inserted ear, as an abstract path graph. -/
  ear : Graph γ γ
  /-- One end of the ear. -/
  source : γ
  /-- The other end of the ear. -/
  target : γ
  /-- The ear's own edges, in order. -/
  earWalk : List γ
  /-- The first boundary path of the split 2-cell, from `source` to `target`. -/
  path₁ : List γ
  /-- The second boundary path. -/
  path₂ : List γ
  /-- The ear is a path graph between its two ends. -/
  isPathGraph : ear.IsPathGraph source earWalk target
  /-- The first boundary path really is a path of the skeleton between the ear's ends. -/
  isPath₁ : S.skel.IsPath source path₁ target
  /-- So is the second. -/
  isPath₂ : S.skel.IsPath source path₂ target
  /-- The ear's vertex names and edge names are distinct. -/
  ear_disjoint : Disjoint V(ear) E(ear)
  /-- The two ends of the ear are distinct. -/
  source_ne_target : source ≠ target
  /-- The split cell is a 2-cell. -/
  face_mem : face ∈ S.faces
  /-- The ear meets the old skeleton exactly in its two ends. -/
  vertexSet_inter : V(ear) ∩ V(S.skel) = {source, target}
  /-- Every edge of the ear is a fresh name. -/
  edge_fresh : ∀ ⦃f⦄, f ∈ E(ear) → f ∉ S.cells
  /-- Every interior vertex of the ear is a fresh name. -/
  vertex_fresh : ∀ ⦃z⦄, z ∈ V(ear) → z ≠ source → z ≠ target → z ∉ S.cells
  /-- The first new 2-cell has a fresh name. -/
  face₁_notMem : face₁ ∉ S.cells
  /-- The second new 2-cell has a fresh name. -/
  face₂_notMem : face₂ ∉ S.cells
  /-- The first new 2-cell is not a cell of the ear either. -/
  face₁_notMem_ear : face₁ ∉ V(ear) ∪ E(ear)
  /-- Nor is the second. -/
  face₂_notMem_ear : face₂ ∉ V(ear) ∪ E(ear)
  /-- The two new 2-cells are distinct. -/
  face_ne : face₁ ≠ face₂
  /-- The cells below the split 2-cell are exactly the cells of its two boundary paths. -/
  sub_face : ∀ ⦃σ⦄, S.sub σ face ↔
    σ = face ∨ σ ∈ S.pathCells source path₁ ∪ S.pathCells source path₂
  /-- The two boundary paths share no edge. -/
  paths_disjoint : ∀ ⦃f⦄, f ∈ path₁ → f ∉ path₂

namespace SplitData

variable {S : CellStructure γ} (d : S.SplitData)

/-- All cells of the ear: its vertices, including its two old ends, and its edges. -/
def earCells : Set γ := V(d.ear) ∪ E(d.ear)

/-- The cells the split creates: the interior cells of the ear, its edges, and the two new
2-cells. The ear's two ends are *not* new — they are old vertices, and the blueprint is
explicit that they are their own parents. -/
def newCells : Set γ := (V(d.ear) \ {d.source, d.target}) ∪ E(d.ear) ∪ {d.face₁, d.face₂}

/-- The cells of the first boundary path. -/
def cells₁ : Set γ := S.pathCells d.source d.path₁

/-- The cells of the second boundary path. -/
def cells₂ : Set γ := S.pathCells d.source d.path₂

theorem source_mem_skel : d.source ∈ V(S.skel) := d.isPath₁.left_mem

theorem target_mem_skel : d.target ∈ V(S.skel) := d.isPath₁.right_mem

theorem source_mem_cells : d.source ∈ S.cells := S.mem_cells_of_mem_vertexSet d.source_mem_skel

theorem target_mem_cells : d.target ∈ S.cells := S.mem_cells_of_mem_vertexSet d.target_mem_skel

theorem face_mem_cells : d.face ∈ S.cells := S.mem_cells_of_mem_faces d.face_mem

theorem cells₁_subset : d.cells₁ ⊆ S.cells := pathCells_subset_cells d.isPath₁.isWalk

theorem cells₂_subset : d.cells₂ ⊆ S.cells := pathCells_subset_cells d.isPath₂.isWalk

/-- A vertex of the ear other than its two ends is a fresh name; an end is an old vertex. -/
theorem mem_cells_of_mem_ear_vertexSet {z : γ} (hz : z ∈ V(d.ear)) (h : z ∈ S.cells) :
    z = d.source ∨ z = d.target := by
  by_contra hcon
  push Not at hcon
  exact d.vertex_fresh hz hcon.1 hcon.2 h

variable {d}

theorem notMem_cells_of_mem_newCells {z : γ} (h : z ∈ d.newCells) : z ∉ S.cells := by
  rcases h with (⟨hz, hz'⟩ | hz) | hz
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
    push Not at hz'
    exact d.vertex_fresh hz hz'.1 hz'.2
  · exact d.edge_fresh hz
  · rcases hz with rfl | rfl
    exacts [d.face₁_notMem, d.face₂_notMem]

theorem notMem_newCells_of_mem_cells {z : γ} (h : z ∈ S.cells) : z ∉ d.newCells := fun hz =>
  notMem_cells_of_mem_newCells hz h

variable (d)

theorem face_notMem_newCells : d.face ∉ d.newCells := notMem_newCells_of_mem_cells d.face_mem_cells

theorem face₁_mem_newCells : d.face₁ ∈ d.newCells := Or.inr (Or.inl rfl)

theorem face₂_mem_newCells : d.face₂ ∈ d.newCells := Or.inr (Or.inr rfl)

theorem disjoint_edgeSet : Disjoint E(S.skel) E(d.ear) :=
  Set.disjoint_left.2 fun _ hz hz' => d.edge_fresh hz' (S.mem_cells_of_mem_edgeSet hz)

theorem compatible : S.skel.Compatible d.ear := Graph.Compatible.of_disjoint_edgeSet d.disjoint_edgeSet

/-- The skeleton after the split: the old skeleton with the ear glued in along its two ends. -/
def skeleton : Graph γ γ := S.skel.union d.ear

@[simp] theorem skeleton_vertexSet : V(d.skeleton) = V(S.skel) ∪ V(d.ear) := rfl

@[simp] theorem skeleton_edgeSet : E(d.skeleton) = E(S.skel) ∪ E(d.ear) := rfl

theorem le_skeleton : S.skel ≤ d.skeleton := Graph.left_le_union _ _

theorem ear_le_skeleton : d.ear ≤ d.skeleton := d.compatible.right_le_union

theorem finite_ear_vertexSet : V(d.ear).Finite := by
  rw [d.isPathGraph.vertexSet_eq]; exact d.isPathGraph.isWalk.finite_walkVertices

theorem finite_ear_edgeSet : E(d.ear).Finite := by
  rw [d.isPathGraph.edgeSet_eq]; exact d.earWalk.finite_toSet

/-- **The abstract subcell relation after a 2-cell split.** Read off the blueprint's update
list, in order: the old pairs involving neither `R` nor a new cell; the reflexive pairs of the
new cells (see the fidelity note in the module docstring); the incidences along the ear; and
the cells of `P` and of `Bᵢ`, together with `Rᵢ` itself, below `Rᵢ`. No 2-cell is below
another. -/
def subRel : γ → γ → Prop := fun σ τ =>
  (σ ∉ d.newCells ∧ τ ∉ d.newCells ∧ σ ≠ d.face ∧ τ ≠ d.face ∧ S.sub σ τ) ∨
    (σ = τ ∧ σ ∈ d.newCells) ∨
    d.ear.Inc τ σ ∨
    (τ = d.face₁ ∧ (σ = d.face₁ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₁)) ∨
    (τ = d.face₂ ∧ (σ = d.face₂ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₂))

end SplitData

open scoped Classical in
/-- **Elementary operation 2: 2-cell splitting by an ear.** The abstract-data update of
`def:generated-structure`, operation 2.

As with `CellStructure.subdivideEdge`, the boundary walks are a raw datum: the two new 2-cells
get the concatenation of their boundary path with the reversed ear, and nothing below reads
the orientation. -/
noncomputable def splitFace (S : CellStructure γ) (d : S.SplitData) : CellStructure γ where
  skel := d.skeleton
  faces := insert d.face₁ (insert d.face₂ (S.faces \ {d.face}))
  outerGraph := S.outerGraph
  outerGraph_le := S.outerGraph_le.trans d.le_skeleton
  boundary F :=
    if F = d.face₁ then d.path₁ ++ d.earWalk.reverse
    else if F = d.face₂ then d.path₂ ++ d.earWalk.reverse
    else S.boundary F
  sub := d.subRel
  finite_vertexSet := S.finite_vertexSet.union d.finite_ear_vertexSet
  finite_edgeSet := S.finite_edgeSet.union d.finite_ear_edgeSet
  finite_faces := ((S.finite_faces.diff).insert _).insert _
  disjoint_vertexSet_edgeSet := by
    rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet hz hz'
    · exact d.edge_fresh hz' (S.mem_cells_of_mem_vertexSet hz)
    · rcases d.mem_cells_of_mem_ear_vertexSet hz (S.mem_cells_of_mem_edgeSet hz') with rfl | rfl
      · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet d.source_mem_skel hz'
      · exact Set.disjoint_left.1 S.disjoint_vertexSet_edgeSet d.target_mem_skel hz'
    · exact Set.disjoint_left.1 d.ear_disjoint hz hz'
  disjoint_faces_vertexSet := by
    rw [Set.disjoint_left]
    rintro z hz (hz' | hz')
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem (S.mem_cells_of_mem_vertexSet hz')
      · exact d.face₂_notMem (S.mem_cells_of_mem_vertexSet hz')
      · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz hz'
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem_ear (Or.inl hz')
      · exact d.face₂_notMem_ear (Or.inl hz')
      · rcases d.mem_cells_of_mem_ear_vertexSet hz' (S.mem_cells_of_mem_faces hz) with rfl | rfl
        · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz d.source_mem_skel
        · exact Set.disjoint_left.1 S.disjoint_faces_vertexSet hz d.target_mem_skel
  disjoint_faces_edgeSet := by
    rw [Set.disjoint_left]
    rintro z hz (hz' | hz')
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem (S.mem_cells_of_mem_edgeSet hz')
      · exact d.face₂_notMem (S.mem_cells_of_mem_edgeSet hz')
      · exact Set.disjoint_left.1 S.disjoint_faces_edgeSet hz hz'
    · rcases hz with rfl | rfl | ⟨hz, -⟩
      · exact d.face₁_notMem_ear (Or.inr hz')
      · exact d.face₂_notMem_ear (Or.inr hz')
      · exact d.edge_fresh hz' (S.mem_cells_of_mem_faces hz)

variable {S : CellStructure γ} (c : S.SplitData)

@[simp] theorem splitFace_skel : (S.splitFace c).skel = c.skeleton := rfl

@[simp] theorem splitFace_faces :
    (S.splitFace c).faces = insert c.face₁ (insert c.face₂ (S.faces \ {c.face})) := rfl

@[simp] theorem splitFace_outerGraph : (S.splitFace c).outerGraph = S.outerGraph := rfl

@[simp] theorem splitFace_sub {σ τ : γ} : (S.splitFace c).sub σ τ ↔ c.subRel σ τ := Iff.rfl

/-- The cells after a split: the old ones except the split 2-cell, plus the ear's cells and the
two new 2-cells. (The ear's two ends are old cells and appear on both sides.) -/
theorem splitFace_cells : (S.splitFace c).cells = (S.cells \ {c.face}) ∪ c.newCells := by
  ext z
  simp only [cells, splitFace_skel, splitFace_faces, c.skeleton_vertexSet, c.skeleton_edgeSet,
    SplitData.newCells, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_diff]
  constructor
  · rintro ((hz | hz) | hz)
    · rcases hz with hz | hz
      · exact Or.inl ⟨S.mem_cells_of_mem_vertexSet hz,
          fun h => S.faces_ne_vertexSet c.face_mem hz h.symm⟩
      · by_cases hcell : z ∈ S.cells
        · rcases c.mem_cells_of_mem_ear_vertexSet hz hcell with rfl | rfl
          · exact Or.inl ⟨c.source_mem_cells,
              fun h => S.faces_ne_vertexSet c.face_mem c.source_mem_skel h.symm⟩
          · exact Or.inl ⟨c.target_mem_cells,
              fun h => S.faces_ne_vertexSet c.face_mem c.target_mem_skel h.symm⟩
        · refine Or.inr (Or.inl (Or.inl ⟨hz, ?_⟩))
          rintro (rfl | rfl)
          exacts [hcell c.source_mem_cells, hcell c.target_mem_cells]
    · rcases hz with hz | hz
      · exact Or.inl ⟨S.mem_cells_of_mem_edgeSet hz,
          fun h => S.faces_ne_edgeSet c.face_mem hz h.symm⟩
      · exact Or.inr (Or.inl (Or.inr hz))
    · rcases hz with rfl | rfl | ⟨hz, hz'⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl ⟨S.mem_cells_of_mem_faces hz, hz'⟩
  · rintro (⟨hz, hz'⟩ | ((⟨hz, -⟩ | hz) | (rfl | rfl)))
    · rcases hz with (hz | hz) | hz
      · exact Or.inl (Or.inl (Or.inl hz))
      · exact Or.inl (Or.inr (Or.inl hz))
      · exact Or.inr (Or.inr (Or.inr ⟨hz, hz'⟩))
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inl (Or.inr (Or.inr hz))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

end CellStructure

/-! ### Generated matched cell structures -/

/-- **`def:generated-structure`**: the closure of a base structure under the two elementary
operations.

The base is a *parameter*. The blueprint's base is the initial matched cellulation of
`prop:initial-pair`, which is being built elsewhere; parameterising over it makes every theorem
below read "the invariants propagate", with the base case supplied by the producer of `S₀`.

`rem:intermediate-disconnection` is honoured by omission: the realizations of a generated
structure are required only to be weakly admissible — connectedness of the open nonboundary
part is waived — and nothing in this file, or in any statement about
`GeneratedStructure`, mentions that connectedness. -/
inductive GeneratedStructure (S₀ : CellStructure γ) : CellStructure γ → Prop
  /-- The base structure is generated, by the empty sequence of operations. -/
  | base : GeneratedStructure S₀ S₀
  /-- Subdividing an edge of a generated structure gives a generated structure. -/
  | subdivideEdge {S : CellStructure γ} (h : GeneratedStructure S₀ S) (d : S.SubdivData) :
      GeneratedStructure S₀ (S.subdivideEdge d)
  /-- Splitting a 2-cell of a generated structure by an ear gives a generated structure. -/
  | splitFace {S : CellStructure γ} (h : GeneratedStructure S₀ S) (d : S.SplitData) :
      GeneratedStructure S₀ (S.splitFace d)

namespace CellStructure

/-! ### The combinatorial invariants

Assertions (iii), (v) and (vi) of `lem:cellulation-invariants`, together with the abstract form
of (viii) and the bookkeeping facts about `≼_abs` that the blueprint's proof uses without
comment (the relation relates cells to cells, it is reflexive, and a vertex is below each edge
it bounds). They are bundled because the induction propagates them together: the preservation
proof of each one reads the others at the previous stage. -/

/-- The combinatorial invariants of `lem:cellulation-invariants`. -/
structure CombInvariants (S : CellStructure γ) : Prop where
  /-- `≼_abs` relates cells to cells. -/
  sub_mem_left : ∀ ⦃σ τ⦄, S.sub σ τ → σ ∈ S.cells
  /-- `≼_abs` relates cells to cells. -/
  sub_mem_right : ∀ ⦃σ τ⦄, S.sub σ τ → τ ∈ S.cells
  /-- `≼_abs` is reflexive on cells. The blueprint declares the reflexive pairs in the base
  relation and preserves them under both constructors. -/
  sub_refl : ∀ ⦃σ⦄, σ ∈ S.cells → S.sub σ σ
  /-- Each endpoint of an edge is a subcell of it. -/
  sub_isLink : ∀ ⦃f a b⦄, S.skel.IsLink f a b → S.sub a f
  /-- **Abstract (viii)**: no 2-cell is a subcell of anything but itself. -/
  face_maximal : ∀ ⦃F τ⦄, F ∈ S.faces → S.sub F τ → τ = F
  /-- **(iii)**: every 2-cell boundary contains a nonboundary edge. -/
  nonboundary_edge : ∀ ⦃F⦄, F ∈ S.faces → ∃ f ∈ E(S.skel), f ∉ E(S.outerGraph) ∧ S.sub f F
  /-- **(v)**: every cell is a subcell of at least one 2-cell. -/
  mem_face : ∀ ⦃σ⦄, σ ∈ S.cells → ∃ F ∈ S.faces, S.sub σ F
  /-- **(vi)**: every outer edge is a subcell of exactly one 2-cell. -/
  outerEdge_unique : OuterEdgeUniqueFace S

namespace CombInvariants

/-- The other endpoint of an edge is below it too. -/
theorem sub_isLink' {S : CellStructure γ} (hS : S.CombInvariants) ⦃f a b : γ⦄
    (h : S.skel.IsLink f a b) : S.sub b f := hS.sub_isLink h.symm

end CombInvariants

/-! ### Edge subdivision preserves the combinatorial invariants -/

namespace SubdivData

variable {S : CellStructure γ} (d : S.SubdivData)

theorem subRel_of_old {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.edge) (hτ : τ ≠ d.edge) (h : S.sub σ τ) : d.subRel σ τ :=
  Or.inl ⟨notMem_newCells_of_mem_cells hσc, notMem_newCells_of_mem_cells hτc, hσ, hτ, h⟩

/-- On old cells other than the subdivided edge, the relation is unchanged: "all pairs not
involving `e` are unchanged". -/
theorem old_subRel_iff {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.edge) (hτ : τ ≠ d.edge) : d.subRel σ τ ↔ S.sub σ τ := by
  refine ⟨fun h => ?_, d.subRel_of_old hσc hτc hσ hτ⟩
  rcases h with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -, -⟩
  · exact h
  · exact absurd hσc (notMem_cells_of_mem_newCells h)
  · exact absurd (h ▸ hσc) d.newVertex_notMem
  · exact absurd (h ▸ hτc) d.newEdge₁_notMem
  · exact absurd (h ▸ hτc) d.newEdge₂_notMem
  · exact absurd hσc (notMem_cells_of_mem_newCells h)

/-- A new cell is below exactly the old strict supercells of the subdivided edge. -/
theorem newCells_subRel_iff {σ τ : γ} (hσ : σ ∈ d.newCells) (hτc : τ ∈ S.cells) :
    d.subRel σ τ ↔ (τ ≠ d.edge ∧ S.sub d.edge τ) := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hσ, h.1, h.2⟩))))⟩
  rcases h with ⟨h, -, -, -, -⟩ | ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h
  · exact absurd hσ h
  · exact absurd (h ▸ hσ) (notMem_newCells_of_mem_cells hτc)
  · exact absurd (h ▸ hτc) d.newEdge₁_notMem
  · exact absurd (h ▸ hτc) d.newEdge₂_notMem
  · exact absurd (h ▸ hτc) d.newEdge₁_notMem
  · exact absurd (h ▸ hτc) d.newEdge₂_notMem
  · exact h.2

theorem mem_subdivideEdge_cells_of_old {z : γ} (hz : z ∈ S.cells) (hze : z ≠ d.edge) :
    z ∈ (S.subdivideEdge d).cells := by
  rw [subdivideEdge_cells]; exact Or.inl ⟨hz, hze⟩

theorem mem_subdivideEdge_cells_of_new {z : γ} (hz : z ∈ d.newCells) :
    z ∈ (S.subdivideEdge d).cells := by
  rw [subdivideEdge_cells]; exact Or.inr hz

theorem left_ne_edge : d.left ≠ d.edge :=
  S.vertexSet_ne_edgeSet d.isLink.left_mem d.edge_mem_edgeSet

theorem right_ne_edge : d.right ≠ d.edge :=
  S.vertexSet_ne_edgeSet d.isLink.right_mem d.edge_mem_edgeSet

/-- **Edge subdivision preserves the combinatorial invariants**: the induction step of
assertions (iii), (v), (vi) — and of abstract (viii) — over the first constructor. -/
theorem combInvariants (hS : S.CombInvariants) : (S.subdivideEdge d).CombInvariants where
  sub_mem_left := by
    rintro σ τ (⟨-, -, hσ, -, h⟩ | ⟨-, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨h, -, -⟩)
    · exact d.mem_subdivideEdge_cells_of_old (hS.sub_mem_left h) hσ
    · exact d.mem_subdivideEdge_cells_of_new h
    · exact d.mem_subdivideEdge_cells_of_new (Or.inl rfl)
    · exact d.mem_subdivideEdge_cells_of_old d.left_mem_cells d.left_ne_edge
    · exact d.mem_subdivideEdge_cells_of_old d.right_mem_cells d.right_ne_edge
    · exact d.mem_subdivideEdge_cells_of_new h
  sub_mem_right := by
    rintro σ τ (⟨-, -, -, hτ, h⟩ | ⟨rfl, h⟩ | ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, hτ, h⟩)
    · exact d.mem_subdivideEdge_cells_of_old (hS.sub_mem_right h) hτ
    · exact d.mem_subdivideEdge_cells_of_new h
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl))
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl))
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inl rfl))
    · exact d.mem_subdivideEdge_cells_of_new (Or.inr (Or.inr rfl))
    · exact d.mem_subdivideEdge_cells_of_old (hS.sub_mem_right h) hτ
  sub_refl := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσ, hσe⟩ | hσ
    · exact d.subRel_of_old hσ hσ hσe hσe (hS.sub_refl hσ)
    · exact Or.inr (Or.inl ⟨rfl, hσ⟩)
  sub_isLink := by
    intro f a b hl
    rw [subdivideEdge_skel, d.skeleton_isLink] at hl
    rcases hl with ⟨hl, hfe, -, -⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
    · exact d.subRel_of_old (S.mem_cells_of_mem_vertexSet hl.left_mem)
        (S.mem_cells_of_mem_edgeSet hl.edge_mem)
        (S.vertexSet_ne_edgeSet hl.left_mem d.edge_mem_edgeSet) hfe (hS.sub_isLink hl)
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  face_maximal := by
    intro F τ hF h
    rw [subdivideEdge_faces] at hF
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
    rcases h with ⟨-, -, -, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩
    · exact hS.face_maximal hF h
    · exact h.symm
    · exact absurd (h ▸ hFc) d.newVertex_notMem
    · exact absurd (S.faces_ne_vertexSet hF d.isLink.left_mem) (not_not.2 h)
    · exact absurd (S.faces_ne_vertexSet hF d.isLink.right_mem) (not_not.2 h)
    · exact absurd hFc (notMem_cells_of_mem_newCells h)
  nonboundary_edge := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    obtain ⟨f, hfE, hfO, hfsub⟩ := hS.nonboundary_edge hF
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    have hFe : F ≠ d.edge := S.faces_ne_edgeSet hF d.edge_mem_edgeSet
    by_cases hfe : f = d.edge
    · subst hfe
      refine ⟨d.newEdge₁, ?_, ?_, ?_⟩
      · rw [subdivideEdge_skel, d.skeleton_edgeSet]; exact Set.mem_insert _ _
      · rw [subdivideEdge_outerGraph, d.outer_eq hfO]; exact d.newEdge₁_notMem_outer
      · exact (d.newCells_subRel_iff (Or.inr (Or.inl rfl)) hFc).2 ⟨hFe, hfsub⟩
    · refine ⟨f, ?_, ?_, ?_⟩
      · rw [subdivideEdge_skel, d.skeleton_edgeSet]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hfE, hfe⟩)
      · rw [subdivideEdge_outerGraph]
        rintro (⟨hz, -⟩ | ⟨hz, -⟩)
        · exact hfO hz
        · rcases hz with rfl | rfl
          exacts [d.newEdge₁_notMem (S.mem_cells_of_mem_edgeSet hfE),
            d.newEdge₂_notMem (S.mem_cells_of_mem_edgeSet hfE)]
      · exact d.subRel_of_old (S.mem_cells_of_mem_edgeSet hfE) hFc hfe hFe hfsub
  mem_face := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσ, hσe⟩ | hσ
    · obtain ⟨F, hF, hsub⟩ := hS.mem_face hσ
      exact ⟨F, hF, d.subRel_of_old hσ (S.mem_cells_of_mem_faces hF) hσe
        (S.faces_ne_edgeSet hF d.edge_mem_edgeSet) hsub⟩
    · obtain ⟨F, hF, hsub⟩ := hS.mem_face d.edge_mem_cells
      exact ⟨F, hF, (d.newCells_subRel_iff hσ (S.mem_cells_of_mem_faces hF)).2
        ⟨S.faces_ne_edgeSet hF d.edge_mem_edgeSet, hsub⟩⟩
  outerEdge_unique := by
    intro f hf
    rw [subdivideEdge_outerGraph, outer, subdivGraph_edgeSet] at hf
    rcases hf with ⟨hfO, hfe⟩ | ⟨hfnew, hlink⟩
    · obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := hS.outerEdge_unique hfO
      have hfc : f ∈ S.cells :=
        S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hfO)
      refine ⟨F, ⟨hF, d.subRel_of_old hfc (S.mem_cells_of_mem_faces hF) hfe
        (S.faces_ne_edgeSet hF d.edge_mem_edgeSet) hsub⟩, fun T hT => ?_⟩
      exact huniq T ⟨hT.1, (d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT.1) hfe
        (S.faces_ne_edgeSet hT.1 d.edge_mem_edgeSet)).1 hT.2⟩
    · have hfnew' : f ∈ d.newCells := by
        rcases hfnew with rfl | rfl
        exacts [Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
      obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := hS.outerEdge_unique hlink.edge_mem
      refine ⟨F, ⟨hF, (d.newCells_subRel_iff hfnew' (S.mem_cells_of_mem_faces hF)).2
        ⟨S.faces_ne_edgeSet hF d.edge_mem_edgeSet, hsub⟩⟩, fun T hT => ?_⟩
      exact huniq T ⟨hT.1, ((d.newCells_subRel_iff hfnew'
        (S.mem_cells_of_mem_faces hT.1)).1 hT.2).2⟩

/-! #### The parent map of an edge subdivision -/

open scoped Classical in
/-- **The parent map of one edge subdivision** — assertion (iv). The three new cells have the
subdivided edge as parent; every surviving cell is its own parent. -/
noncomputable def parent : γ → γ := fun σ => if σ ∈ d.newCells then d.edge else σ

theorem parent_of_mem_newCells {σ : γ} (h : σ ∈ d.newCells) : d.parent σ = d.edge := by
  rw [parent]; exact if_pos h

theorem parent_of_notMem_newCells {σ : γ} (h : σ ∉ d.newCells) : d.parent σ = σ := by
  rw [parent]; exact if_neg h

theorem parent_of_mem_cells {σ : γ} (h : σ ∈ S.cells) : d.parent σ = σ :=
  d.parent_of_notMem_newCells (notMem_newCells_of_mem_cells h)

/-- **Assertion (iv), the compatibility clause**: `σ ≼ τ` in the refined structure implies
`par σ ≼ par τ` in the old one. -/
theorem sub_parent (hS : S.CombInvariants) {σ τ : γ} (h : (S.subdivideEdge d).sub σ τ) :
    S.sub (d.parent σ) (d.parent τ) := by
  rcases h with ⟨hσ, hτ, -, -, h⟩ | ⟨rfl, hσ⟩ | ⟨rfl, hτ⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hσ, -, h⟩
  · rw [d.parent_of_notMem_newCells hσ, d.parent_of_notMem_newCells hτ]; exact h
  · rw [d.parent_of_mem_newCells hσ]; exact hS.sub_refl d.edge_mem_cells
  · rw [d.parent_of_mem_newCells (Or.inl rfl)]
    rcases hτ with rfl | rfl
    · rw [d.parent_of_mem_newCells (Or.inr (Or.inl rfl))]; exact hS.sub_refl d.edge_mem_cells
    · rw [d.parent_of_mem_newCells (Or.inr (Or.inr rfl))]; exact hS.sub_refl d.edge_mem_cells
  · rw [d.parent_of_mem_cells d.left_mem_cells, d.parent_of_mem_newCells (Or.inr (Or.inl rfl))]
    exact hS.sub_isLink d.isLink
  · rw [d.parent_of_mem_cells d.right_mem_cells, d.parent_of_mem_newCells (Or.inr (Or.inr rfl))]
    exact hS.sub_isLink' d.isLink
  · rw [d.parent_of_mem_newCells hσ, d.parent_of_mem_cells (hS.sub_mem_right h)]; exact h

end SubdivData

/-! ### A 2-cell split preserves the combinatorial invariants -/

namespace SplitData

variable {S : CellStructure γ} (d : S.SplitData)

theorem source_mem_cells₁ : d.source ∈ d.cells₁ := Or.inr Graph.mem_walkVertices_self

theorem target_mem_cells₁ : d.target ∈ d.cells₁ := Or.inr d.isPath₁.target_mem_walkVertices

theorem cells₁_ne_face {σ : γ} (h : σ ∈ d.cells₁) : σ ≠ d.face := by
  rcases h with h | h
  · exact fun heq => S.faces_ne_edgeSet d.face_mem (d.isPath₁.edge_mem h) heq.symm
  · exact fun heq =>
      S.faces_ne_vertexSet d.face_mem (d.isPath₁.isWalk.walkVertices_subset h) heq.symm

theorem cells₂_ne_face {σ : γ} (h : σ ∈ d.cells₂) : σ ≠ d.face := by
  rcases h with h | h
  · exact fun heq => S.faces_ne_edgeSet d.face_mem (d.isPath₂.edge_mem h) heq.symm
  · exact fun heq =>
      S.faces_ne_vertexSet d.face_mem (d.isPath₂.isWalk.walkVertices_subset h) heq.symm

theorem notMem_faces_of_mem_cells₁ {σ : γ} (h : σ ∈ d.cells₁) (hσ : σ ∈ S.faces) : False := by
  rcases h with h | h
  · exact S.faces_ne_edgeSet hσ (d.isPath₁.edge_mem h) rfl
  · exact S.faces_ne_vertexSet hσ (d.isPath₁.isWalk.walkVertices_subset h) rfl

theorem notMem_faces_of_mem_cells₂ {σ : γ} (h : σ ∈ d.cells₂) (hσ : σ ∈ S.faces) : False := by
  rcases h with h | h
  · exact S.faces_ne_edgeSet hσ (d.isPath₂.edge_mem h) rfl
  · exact S.faces_ne_vertexSet hσ (d.isPath₂.isWalk.walkVertices_subset h) rfl

/-- An edge of the skeleton belongs to the cells of a boundary path exactly when it is one of
that path's edges — a vertex of the walk cannot be an edge name. -/
theorem edge_mem_cells₁_iff {f : γ} (hf : f ∈ E(S.skel)) : f ∈ d.cells₁ ↔ f ∈ d.path₁ := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | h
  · exact h
  · exact absurd rfl (S.vertexSet_ne_edgeSet (d.isPath₁.isWalk.walkVertices_subset h) hf)

theorem edge_mem_cells₂_iff {f : γ} (hf : f ∈ E(S.skel)) : f ∈ d.cells₂ ↔ f ∈ d.path₂ := by
  refine ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with h | h
  · exact h
  · exact absurd rfl (S.vertexSet_ne_edgeSet (d.isPath₂.isWalk.walkVertices_subset h) hf)

/-- The ear has at least one edge: its two ends are distinct, so its walk is not empty. -/
theorem exists_ear_edge : ∃ f, f ∈ E(d.ear) := by
  rcases hw : d.earWalk with _ | ⟨f, rest⟩
  · exfalso
    have hmem := d.isPathGraph.target_mem
    rw [d.isPathGraph.vertexSet_eq, hw, Graph.walkVertices_nil, Set.mem_singleton_iff] at hmem
    exact d.source_ne_target hmem.symm
  · exact ⟨f, d.isPathGraph.mem_edgeSet (by rw [hw]; exact List.mem_cons_self ..)⟩

theorem subRel_of_old {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.face) (hτ : τ ≠ d.face) (h : S.sub σ τ) : d.subRel σ τ :=
  Or.inl ⟨notMem_newCells_of_mem_cells hσc, notMem_newCells_of_mem_cells hτc, hσ, hτ, h⟩

/-- On old cells other than the split 2-cell, the relation is unchanged: "all pairs not
involving `R` or the new cells are unchanged". -/
theorem old_subRel_iff {σ τ : γ} (hσc : σ ∈ S.cells) (hτc : τ ∈ S.cells)
    (hσ : σ ≠ d.face) (hτ : τ ≠ d.face) : d.subRel σ τ ↔ S.sub σ τ := by
  refine ⟨fun h => ?_, d.subRel_of_old hσc hτc hσ hτ⟩
  rcases h with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ | h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd hσc (notMem_cells_of_mem_newCells h)
  · exact absurd hτc (d.edge_fresh h.edge_mem)
  · exact absurd (h ▸ hτc) d.face₁_notMem
  · exact absurd (h ▸ hτc) d.face₂_notMem

/-- The cells below the first new 2-cell are exactly the ear's cells, the first boundary path's
cells, and itself. -/
theorem subRel_face₁_iff {σ : γ} :
    d.subRel σ d.face₁ ↔ (σ = d.face₁ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₁) := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))⟩
  rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | h | ⟨-, h⟩ | ⟨h, -⟩
  · exact absurd d.face₁_mem_newCells h
  · exact Or.inl h
  · exact absurd h.edge_mem fun hh => d.face₁_notMem_ear (Or.inr hh)
  · exact h
  · exact absurd h d.face_ne

theorem subRel_face₂_iff {σ : γ} :
    d.subRel σ d.face₂ ↔ (σ = d.face₂ ∨ σ ∈ d.earCells ∨ σ ∈ d.cells₂) := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))⟩
  rcases h with ⟨-, h, -, -, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd d.face₂_mem_newCells h
  · exact Or.inl h
  · exact absurd h.edge_mem fun hh => d.face₂_notMem_ear (Or.inr hh)
  · exact absurd h.symm d.face_ne
  · exact h

theorem mem_splitFace_cells_of_old {z : γ} (hz : z ∈ S.cells) (hzf : z ≠ d.face) :
    z ∈ (S.splitFace d).cells := by
  rw [splitFace_cells]; exact Or.inl ⟨hz, hzf⟩

theorem mem_splitFace_cells_of_new {z : γ} (hz : z ∈ d.newCells) :
    z ∈ (S.splitFace d).cells := by
  rw [splitFace_cells]; exact Or.inr hz

theorem mem_splitFace_cells_of_ear {z : γ} (hz : z ∈ d.earCells) :
    z ∈ (S.splitFace d).cells := by
  rcases hz with hz | hz
  · by_cases hc : z ∈ S.cells
    · rcases d.mem_cells_of_mem_ear_vertexSet hz hc with rfl | rfl
      · exact d.mem_splitFace_cells_of_old hc fun h =>
          S.faces_ne_vertexSet d.face_mem d.source_mem_skel h.symm
      · exact d.mem_splitFace_cells_of_old hc fun h =>
          S.faces_ne_vertexSet d.face_mem d.target_mem_skel h.symm
    · refine d.mem_splitFace_cells_of_new (Or.inl (Or.inl ⟨hz, ?_⟩))
      rintro (rfl | rfl)
      exacts [hc d.source_mem_cells, hc d.target_mem_cells]
  · exact d.mem_splitFace_cells_of_new (Or.inl (Or.inr hz))

/-- **A 2-cell split preserves the combinatorial invariants**: the induction step of assertions
(iii), (v), (vi) — and of abstract (viii) — over the second constructor. -/
theorem combInvariants (hS : S.CombInvariants) : (S.splitFace d).CombInvariants where
  sub_mem_left := by
    rintro σ τ (⟨-, -, hσ, -, h⟩ | ⟨-, h⟩ | h | ⟨-, h⟩ | ⟨-, h⟩)
    · exact d.mem_splitFace_cells_of_old (hS.sub_mem_left h) hσ
    · exact d.mem_splitFace_cells_of_new h
    · exact d.mem_splitFace_cells_of_ear (Or.inl h.vertex_mem)
    · rcases h with rfl | h | h
      · exact d.mem_splitFace_cells_of_new d.face₁_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₁_subset h) (d.cells₁_ne_face h)
    · rcases h with rfl | h | h
      · exact d.mem_splitFace_cells_of_new d.face₂_mem_newCells
      · exact d.mem_splitFace_cells_of_ear h
      · exact d.mem_splitFace_cells_of_old (d.cells₂_subset h) (d.cells₂_ne_face h)
  sub_mem_right := by
    rintro σ τ (⟨-, -, -, hτ, h⟩ | ⟨rfl, h⟩ | h | ⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact d.mem_splitFace_cells_of_old (hS.sub_mem_right h) hτ
    · exact d.mem_splitFace_cells_of_new h
    · exact d.mem_splitFace_cells_of_ear (Or.inr h.edge_mem)
    · exact d.mem_splitFace_cells_of_new d.face₁_mem_newCells
    · exact d.mem_splitFace_cells_of_new d.face₂_mem_newCells
  sub_refl := by
    intro σ hσ
    rw [splitFace_cells] at hσ
    rcases hσ with ⟨hσ, hσf⟩ | hσ
    · exact d.subRel_of_old hσ hσ hσf hσf (hS.sub_refl hσ)
    · exact Or.inr (Or.inl ⟨rfl, hσ⟩)
  sub_isLink := by
    intro f a b hl
    rw [splitFace_skel, skeleton, d.compatible.union_isLink] at hl
    rcases hl with hl | hl
    · exact d.subRel_of_old (S.mem_cells_of_mem_vertexSet hl.left_mem)
        (S.mem_cells_of_mem_edgeSet hl.edge_mem)
        (fun h => S.faces_ne_vertexSet d.face_mem hl.left_mem h.symm)
        (fun h => S.faces_ne_edgeSet d.face_mem hl.edge_mem h.symm) (hS.sub_isLink hl)
    · exact Or.inr (Or.inr (Or.inl ⟨b, hl⟩))
  face_maximal := by
    intro F τ hF h
    rw [splitFace_faces] at hF
    rcases hF with rfl | rfl | ⟨hF, hFne⟩
    · rcases h with ⟨h, -, -, -, -⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd d.face₁_mem_newCells h
      · exact h.symm
      · exact absurd h.vertex_mem fun hh => d.face₁_notMem_ear (Or.inl hh)
      · exact h
      · rcases h with h | h | h
        · exact absurd h d.face_ne
        · exact absurd h d.face₁_notMem_ear
        · exact absurd (d.cells₂_subset h) d.face₁_notMem
    · rcases h with ⟨h, -, -, -, -⟩ | ⟨h, -⟩ | h | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd d.face₂_mem_newCells h
      · exact h.symm
      · exact absurd h.vertex_mem fun hh => d.face₂_notMem_ear (Or.inl hh)
      · rcases h with h | h | h
        · exact absurd h.symm d.face_ne
        · exact absurd h d.face₂_notMem_ear
        · exact absurd (d.cells₁_subset h) d.face₂_notMem
      · exact h
    · have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
      have hFear : F ∉ d.earCells := by
        rintro (hh | hh)
        · rcases d.mem_cells_of_mem_ear_vertexSet hh hFc with rfl | rfl
          exacts [S.faces_ne_vertexSet hF d.source_mem_skel rfl,
            S.faces_ne_vertexSet hF d.target_mem_skel rfl]
        · exact d.edge_fresh hh hFc
      rcases h with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ | h | ⟨-, h⟩ | ⟨-, h⟩
      · exact hS.face_maximal hF h
      · exact absurd hFc (notMem_cells_of_mem_newCells h)
      · exact absurd (Or.inl h.vertex_mem) hFear
      · rcases h with rfl | h | h
        · exact absurd hFc d.face₁_notMem
        · exact absurd h hFear
        · exact (d.notMem_faces_of_mem_cells₁ h hF).elim
      · rcases h with rfl | h | h
        · exact absurd hFc d.face₂_notMem
        · exact absurd h hFear
        · exact (d.notMem_faces_of_mem_cells₂ h hF).elim
  nonboundary_edge := by
    intro F hF
    rw [splitFace_faces] at hF
    obtain ⟨f, hf⟩ := d.exists_ear_edge
    have hfnew : f ∈ E((S.splitFace d).skel) := Or.inr hf
    have hfout : f ∉ E((S.splitFace d).outerGraph) := by
      rw [splitFace_outerGraph]
      exact fun hh => d.edge_fresh hf (S.mem_cells_of_mem_edgeSet (S.outerGraph_le.edgeSet_mono hh))
    rcases hF with rfl | rfl | ⟨hF, hFne⟩
    · exact ⟨f, hfnew, hfout, d.subRel_face₁_iff.2 (Or.inr (Or.inl (Or.inr hf)))⟩
    · exact ⟨f, hfnew, hfout, d.subRel_face₂_iff.2 (Or.inr (Or.inl (Or.inr hf)))⟩
    · obtain ⟨g, hgE, hgO, hgsub⟩ := hS.nonboundary_edge hF
      refine ⟨g, Or.inl hgE, hgO, d.subRel_of_old (S.mem_cells_of_mem_edgeSet hgE)
        (S.mem_cells_of_mem_faces hF) (fun h => S.faces_ne_edgeSet d.face_mem hgE h.symm)
        hFne hgsub⟩
  mem_face := by
    intro σ hσ
    rw [splitFace_cells] at hσ
    rcases hσ with ⟨hσ, hσf⟩ | hσ
    · obtain ⟨F, hF, hsub⟩ := hS.mem_face hσ
      by_cases hFf : F = d.face
      · subst hFf
        rcases d.sub_face.1 hsub with h | h | h
        · exact absurd h hσf
        · exact ⟨d.face₁, Set.mem_insert _ _, d.subRel_face₁_iff.2 (Or.inr (Or.inr h))⟩
        · exact ⟨d.face₂, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
            d.subRel_face₂_iff.2 (Or.inr (Or.inr h))⟩
      · exact ⟨F, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hF, hFf⟩),
          d.subRel_of_old hσ (S.mem_cells_of_mem_faces hF) hσf
            hFf hsub⟩
    · rcases hσ with (⟨hσ, -⟩ | hσ) | hσ
      · exact ⟨d.face₁, Set.mem_insert _ _,
          d.subRel_face₁_iff.2 (Or.inr (Or.inl (Or.inl hσ)))⟩
      · exact ⟨d.face₁, Set.mem_insert _ _,
          d.subRel_face₁_iff.2 (Or.inr (Or.inl (Or.inr hσ)))⟩
      · rcases hσ with rfl | rfl
        · exact ⟨d.face₁, Set.mem_insert _ _, d.subRel_face₁_iff.2 (Or.inl rfl)⟩
        · exact ⟨d.face₂, Set.mem_insert_of_mem _ (Set.mem_insert _ _),
            d.subRel_face₂_iff.2 (Or.inl rfl)⟩
  outerEdge_unique := by
    intro f hf
    rw [splitFace_outerGraph] at hf
    have hfE : f ∈ E(S.skel) := S.outerGraph_le.edgeSet_mono hf
    have hfc : f ∈ S.cells := S.mem_cells_of_mem_edgeSet hfE
    have hff : f ≠ d.face := fun h => S.faces_ne_edgeSet d.face_mem hfE h.symm
    have hfear : f ∉ d.earCells := by
      rintro (hh | hh)
      · rcases d.mem_cells_of_mem_ear_vertexSet hh hfc with rfl | rfl
        exacts [S.vertexSet_ne_edgeSet d.source_mem_skel hfE rfl,
          S.vertexSet_ne_edgeSet d.target_mem_skel hfE rfl]
      · exact d.edge_fresh hh hfc
    obtain ⟨F, ⟨hF, hsub⟩, huniq⟩ := hS.outerEdge_unique hf
    by_cases hFf : F = d.face
    · subst hFf
      -- the old incident 2-cell is the one being split: exactly one boundary path carries `f`
      have hcells : f ∈ d.cells₁ ∨ f ∈ d.cells₂ := by
        rcases d.sub_face.1 hsub with h | h | h
        exacts [absurd h hff, Or.inl h, Or.inr h]
      have hexcl : ¬ (f ∈ d.cells₁ ∧ f ∈ d.cells₂) := fun ⟨h₁, h₂⟩ =>
        d.paths_disjoint ((d.edge_mem_cells₁_iff hfE).1 h₁) ((d.edge_mem_cells₂_iff hfE).1 h₂)
      have hother : ∀ T, T ∈ S.faces → T ≠ d.face → ¬ S.sub f T := fun T hT hTf hsubT =>
        hTf (huniq T ⟨hT, hsubT⟩ ▸ rfl)
      rcases hcells with h | h
      · refine ⟨d.face₁, ⟨Set.mem_insert _ _, d.subRel_face₁_iff.2 (Or.inr (Or.inr h))⟩,
          fun T hT => ?_⟩
        rcases hT.1 with rfl | rfl | ⟨hT', hT''⟩
        · rfl
        · rcases d.subRel_face₂_iff.1 hT.2 with hh | hh | hh
          · exact absurd (hh ▸ hfc) d.face₂_notMem
          · exact absurd hh hfear
          · exact absurd ⟨h, hh⟩ hexcl
        · exact absurd ((d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT') hff hT'').1 hT.2)
            (hother T hT' hT'')
      · refine ⟨d.face₂, ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _),
          d.subRel_face₂_iff.2 (Or.inr (Or.inr h))⟩, fun T hT => ?_⟩
        rcases hT.1 with rfl | rfl | ⟨hT', hT''⟩
        · rcases d.subRel_face₁_iff.1 hT.2 with hh | hh | hh
          · exact absurd (hh ▸ hfc) d.face₁_notMem
          · exact absurd hh hfear
          · exact absurd ⟨hh, h⟩ hexcl
        · rfl
        · exact absurd ((d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT') hff hT'').1 hT.2)
            (hother T hT' hT'')
    · refine ⟨F, ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hF, hFf⟩),
        d.subRel_of_old hfc (S.mem_cells_of_mem_faces hF) hff hFf hsub⟩, fun T hT => ?_⟩
      rcases hT.1 with rfl | rfl | ⟨hT', hT''⟩
      · rcases d.subRel_face₁_iff.1 hT.2 with hh | hh | hh
        · exact absurd (hh ▸ hfc) d.face₁_notMem
        · exact absurd hh hfear
        · exact absurd (huniq d.face ⟨d.face_mem, d.sub_face.2 (Or.inr (Or.inl hh))⟩).symm hFf
      · rcases d.subRel_face₂_iff.1 hT.2 with hh | hh | hh
        · exact absurd (hh ▸ hfc) d.face₂_notMem
        · exact absurd hh hfear
        · exact absurd (huniq d.face ⟨d.face_mem, d.sub_face.2 (Or.inr (Or.inr hh))⟩).symm hFf
      · exact huniq T ⟨hT', (d.old_subRel_iff hfc (S.mem_cells_of_mem_faces hT') hff hT'').1 hT.2⟩

/-! #### The parent map of a 2-cell split -/

open scoped Classical in
/-- **The parent map of one 2-cell split** — assertion (iv). The ear's interior cells and both
new 2-cells have the split 2-cell as parent; every surviving cell — including the ear's two
endpoints, which the split does not create — is its own parent. -/
noncomputable def parent : γ → γ := fun σ => if σ ∈ d.newCells then d.face else σ

theorem parent_of_mem_newCells {σ : γ} (h : σ ∈ d.newCells) : d.parent σ = d.face := by
  rw [parent]; exact if_pos h

theorem parent_of_notMem_newCells {σ : γ} (h : σ ∉ d.newCells) : d.parent σ = σ := by
  rw [parent]; exact if_neg h

theorem parent_of_mem_cells {σ : γ} (h : σ ∈ S.cells) : d.parent σ = σ :=
  d.parent_of_notMem_newCells (notMem_newCells_of_mem_cells h)

theorem sub_parent_of_mem_cells₁ {σ : γ} (h : σ ∈ d.cells₁) : S.sub (d.parent σ) d.face := by
  rw [d.parent_of_mem_cells (d.cells₁_subset h)]; exact d.sub_face.2 (Or.inr (Or.inl h))

theorem sub_parent_of_mem_cells₂ {σ : γ} (h : σ ∈ d.cells₂) : S.sub (d.parent σ) d.face := by
  rw [d.parent_of_mem_cells (d.cells₂_subset h)]; exact d.sub_face.2 (Or.inr (Or.inr h))

theorem sub_parent_of_mem_earCells (hS : S.CombInvariants) {σ : γ} (h : σ ∈ d.earCells) :
    S.sub (d.parent σ) d.face := by
  rcases h with h | h
  · by_cases hc : σ ∈ S.cells
    · rcases d.mem_cells_of_mem_ear_vertexSet h hc with rfl | rfl
      · exact d.sub_parent_of_mem_cells₁ d.source_mem_cells₁
      · exact d.sub_parent_of_mem_cells₁ d.target_mem_cells₁
    · rw [d.parent_of_mem_newCells (Or.inl (Or.inl ⟨h, by
        rintro (rfl | rfl)
        exacts [hc d.source_mem_cells, hc d.target_mem_cells]⟩))]
      exact hS.sub_refl d.face_mem_cells
  · rw [d.parent_of_mem_newCells (Or.inl (Or.inr h))]; exact hS.sub_refl d.face_mem_cells

/-- **Assertion (iv), the compatibility clause**, for a 2-cell split. -/
theorem sub_parent (hS : S.CombInvariants) {σ τ : γ} (h : (S.splitFace d).sub σ τ) :
    S.sub (d.parent σ) (d.parent τ) := by
  rcases h with ⟨hσ, hτ, -, -, h⟩ | ⟨rfl, hσ⟩ | h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [d.parent_of_notMem_newCells hσ, d.parent_of_notMem_newCells hτ]; exact h
  · rw [d.parent_of_mem_newCells hσ]; exact hS.sub_refl d.face_mem_cells
  · rw [d.parent_of_mem_newCells (Or.inl (Or.inr h.edge_mem))]
    exact d.sub_parent_of_mem_earCells hS (Or.inl h.vertex_mem)
  · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]
    rcases h with rfl | h | h
    · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]; exact hS.sub_refl d.face_mem_cells
    · exact d.sub_parent_of_mem_earCells hS h
    · exact d.sub_parent_of_mem_cells₁ h
  · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]
    rcases h with rfl | h | h
    · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]; exact hS.sub_refl d.face_mem_cells
    · exact d.sub_parent_of_mem_earCells hS h
    · exact d.sub_parent_of_mem_cells₂ h

end SplitData

/-! ### The invariants at every stage -/

/-- **Assertions (iii), (v), (vi) and abstract (viii) hold at every generated stage.** The
induction is over the two constructors; the base case is supplied by the producer of `S₀` —
`prop:initial-pair` for the blueprint's own generated structures. -/
theorem GeneratedStructure.combInvariants {S₀ S : CellStructure γ}
    (h : GeneratedStructure S₀ S) (h₀ : S₀.CombInvariants) : S.CombInvariants := by
  induction h with
  | base => exact h₀
  | subdivideEdge _ d ih => exact d.combInvariants ih
  | splitFace _ d ih => exact d.combInvariants ih

end CellStructure

end Schoenflies
