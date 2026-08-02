/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.GeneratedStructure

/-!
# Exactly one 2-cell is incident with a fresh anchor

The combinatorial paragraph of the proof of `thm:finite-transfer`(b):

> Now suppose the target endpoint is on `S`. By hypothesis it is a fresh point `u(a)`, and the
> only new target edge incident with it is the one occurring in the present ear. At the common
> subdivision stage, `a` is inserted in the interior of one outer edge. By
> `lem:cellulation-invariants`(vi), each of the resulting outer subedges is incident with exactly
> one source 2-cell. The two subedges have the same incident 2-cell, because they subdivide one
> old outer edge. By `lem:combinatorial-invariance`(c), this cell corresponds to the unique target
> 2-cell incident with the matching outer subedges. Earlier ears do not end at `a`. Whenever such
> an ear splits the unique 2-cell incident with `a`, exactly one of the two new boundary paths
> contains `a`; hence exactly one descendant 2-cell remains incident with `a`. The same
> combinatorial assertion holds on the target side.

It is `hunique` of `Schoenflies.polyAccessible_of_stronglyAccessible` (`FreshAccess.lean`), and it
is the only part of direction (b) that is not either geometry already on `main` or bookkeeping.

## What the paragraph is, once the representation is fixed

Everything above is a statement about the **abstract** structure that both realizations realize,
and three of its sentences become vacuous in that reading.

* *"The two subedges have the same incident 2-cell"* is not needed at all. The paragraph tracks
  the two outer subedges because they are what carries the incidence in the manuscript's
  set-level language; here the anchor is a **0-cell** `z` of the abstract structure, and the
  property tracked is `S.UniqueFaceAt z` — at most one 2-cell above `z`. The subdivision
  constructor hands the new vertex exactly the supercells of the edge it cuts
  (`SubdivData.newCells_subRel_iff`), so one subdivision moves (vi) from the outer edge to `z`
  and no comparison of the two halves ever arises.
* *"By `lem:combinatorial-invariance`(c), this cell corresponds to the unique target 2-cell"* and
  *"the same combinatorial assertion holds on the target side"* are free: `S.sub` is a field of
  the one `CellStructure` that `P.src` and `P.tgt` both realize, so the source 2-cell above `z`
  and the target 2-cell above `z` are the *same name*. There is nothing to transport.
* *"Earlier ears do not end at `a`"* is the one sentence that stays, as a hypothesis of the split
  step: `σ ∉ d.earCells`. It is not slack — an ear ending at `z` puts `z` on *both* new boundary
  paths, and both descendant 2-cells are then incident with it.

## The induction, and where its two ends are

`UniqueFaceAt` is an invariant of the ear induction of `thm:finite-transfer`(b), and the two
elementary operations are `SubdivData.uniqueFaceAt` / `.uniqueFaceAt_of_mem_newCells` and
`SplitData.uniqueFaceAt` below. What is **not** here is the threading: `IsPartialTransferOfTgt`
does not carry the invariant, so the induction of `Schoenflies.transfer_of_ears_tgt` does not
maintain it. That is a change to the transfer invariant, not to this paragraph, and it is what
`Schoenflies.EarStepTgt` still waits on. See `docs/ROADMAP.md`.

## Blueprint

* `Schoenflies.CellStructure.UniqueFaceAt` — "exactly one 2-cell is incident with `σ`", the
  uniqueness half; with `lem:cellulation-invariants`(v) it is `∃!`
  (`UniqueFaceAt.existsUnique`).
* `Schoenflies.CellStructure.uniqueFaceAt_of_mem_outerGraph` —
  `lem:cellulation-invariants`(vi) in that form.
* `Schoenflies.CellStructure.SubdivData.uniqueFaceAt`,
  `…SubdivData.uniqueFaceAt_of_mem_newCells` — "at the common subdivision stage, `a` is inserted
  in the interior of one outer edge", so the fresh anchor inherits (vi) from that edge.
* `Schoenflies.CellStructure.SplitData.uniqueFaceAt` — "whenever such an ear splits the unique
  2-cell incident with `a`, exactly one of the two new boundary paths contains `a`; hence exactly
  one descendant 2-cell remains incident with `a`".
* `Schoenflies.CellStructure.Realization.eq_face_of_pos_mem_closure_cell`,
  `…Realization.unique_cell_of_uniqueFaceAt` — the paragraph in the geometric shape
  `Schoenflies.polyAccessible_of_stronglyAccessible` consumes.
-/

open Set
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ} {σ : γ}

/-! ### The invariant -/

/-- **At most one 2-cell is incident with `σ`.**

The uniqueness half of `lem:cellulation-invariants`(vi), stated for an arbitrary cell rather than
for an outer edge, because the ear induction of `thm:finite-transfer`(b) has to carry it at the
0-cell of a fresh anchor. Existence is (v), a field of `CellStructure.CombInvariants`, so the two
together give `∃!` — see `UniqueFaceAt.existsUnique`. -/
def UniqueFaceAt (S : CellStructure γ) (σ : γ) : Prop :=
  ∀ ⦃F G⦄, F ∈ S.faces → G ∈ S.faces → S.sub σ F → S.sub σ G → F = G

/-- **Exactly one 2-cell**, from the uniqueness half and `lem:cellulation-invariants`(v). -/
theorem UniqueFaceAt.existsUnique (h : S.UniqueFaceAt σ) (hS : S.CombInvariants)
    (hσ : σ ∈ S.cells) : ∃! F, F ∈ S.faces ∧ S.sub σ F := by
  obtain ⟨F, hF, hsub⟩ := hS.mem_face hσ
  exact ⟨F, ⟨hF, hsub⟩, fun G hG => h hG.1 hF hG.2 hsub⟩

/-- The invariant names the 2-cell: anything above `σ` is the one 2-cell known to be. -/
theorem UniqueFaceAt.eq (h : S.UniqueFaceAt σ) {F G : γ} (hF : F ∈ S.faces) (hsub : S.sub σ F)
    (hG : G ∈ S.faces) (hsubG : S.sub σ G) : G = F := h hG hF hsubG hsub

/-- **`lem:cellulation-invariants`(vi)** in the form the induction starts from: an outer edge is
incident with at most one 2-cell. -/
theorem uniqueFaceAt_of_mem_outerGraph (h : OuterEdgeUniqueFace S) {e : γ}
    (he : e ∈ E(S.outerGraph)) : S.UniqueFaceAt e := by
  obtain ⟨F, -, huniq⟩ := h he
  intro F₁ F₂ h₁ h₂ hs₁ hs₂
  rw [huniq F₁ ⟨h₁, hs₁⟩, huniq F₂ ⟨h₂, hs₂⟩]

/-! ### Elementary operation 1: edge subdivision

Two statements, because a subdivision treats the anchor's 0-cell in two different ways depending
on whether it already exists. An old cell other than the subdivided edge keeps its supercells
verbatim; the cells the subdivision creates — the new vertex in particular — get exactly the
supercells of the edge that was cut. The second is what carries `lem:cellulation-invariants`(vi)
from the old outer edge to the anchor inserted in its interior. -/

namespace SubdivData

variable (d : S.SubdivData)

/-- **An old cell keeps its 2-cells across a subdivision.** -/
theorem uniqueFaceAt (h : S.UniqueFaceAt σ) (hσ : σ ∈ S.cells) (hσe : σ ≠ d.edge) :
    (S.subdivideEdge d).UniqueFaceAt σ := by
  intro F₁ F₂ h₁ h₂ hs₁ hs₂
  rw [subdivideEdge_faces] at h₁ h₂
  rw [subdivideEdge_sub, d.old_subRel_iff hσ (S.mem_cells_of_mem_faces h₁) hσe
    (S.faces_ne_edgeSet h₁ d.edge_mem_edgeSet)] at hs₁
  rw [subdivideEdge_sub, d.old_subRel_iff hσ (S.mem_cells_of_mem_faces h₂) hσe
    (S.faces_ne_edgeSet h₂ d.edge_mem_edgeSet)] at hs₂
  exact h h₁ h₂ hs₁ hs₂
/-- **The fresh anchor inherits (vi) from the outer edge it cuts.** A cell the subdivision
creates — the new vertex, or either of the two new edges — lies below exactly the 2-cells the
subdivided edge lay below, so it is incident with at most one as soon as that edge was.

This is "at the common subdivision stage, `a` is inserted in the interior of one outer edge; by
`lem:cellulation-invariants`(vi), each of the resulting outer subedges is incident with exactly
one source 2-cell". The blueprint's next sentence — that the two subedges agree — is not needed,
because the anchor is tracked as the new *vertex* and the vertex is one cell, not two. -/
theorem uniqueFaceAt_of_mem_newCells (h : S.UniqueFaceAt d.edge) (hσ : σ ∈ d.newCells) :
    (S.subdivideEdge d).UniqueFaceAt σ := by
  intro F₁ F₂ h₁ h₂ hs₁ hs₂
  rw [subdivideEdge_faces] at h₁ h₂
  rw [subdivideEdge_sub, d.newCells_subRel_iff hσ (S.mem_cells_of_mem_faces h₁)] at hs₁
  rw [subdivideEdge_sub, d.newCells_subRel_iff hσ (S.mem_cells_of_mem_faces h₂)] at hs₂
  exact h h₁ h₂ hs₁.2 hs₂.2

end SubdivData

/-! ### Elementary operation 2: a 2-cell split

*Whenever such an ear splits the unique 2-cell incident with `a`, exactly one of the two new
boundary paths contains `a`; hence exactly one descendant 2-cell remains incident with `a`.*

"Exactly one of the two new boundary paths" is `SplitData.paths_meet` — the two paths share
nothing but the ear's two ends — and that is precisely why *"earlier ears do not end at `a`"* is
a hypothesis: at an end of the ear both paths contain the anchor and both descendants inherit it.
The remaining case, a split of some *other* 2-cell, is `SplitData.old_subRel_iff` on one side and
`SplitData.sub_face` on the other: a cell on a boundary path of the split 2-cell is below it, so
it cannot also be below a different old 2-cell. -/

namespace SplitData

variable (d : S.SplitData)

/-- The three ways a cell can sit below a 2-cell of the split structure, given that it is an old
cell, is not the split 2-cell, and is no cell of the ear. -/
private theorem sub_splitFace_cases (hσ : σ ∈ S.cells) (hface : σ ≠ d.face)
    (hear : σ ∉ d.earCells) ⦃F : γ⦄ (hF : F ∈ (S.splitFace d).faces)
    (hs : (S.splitFace d).sub σ F) :
    (F = d.face₁ ∧ σ ∈ d.cells₁) ∨ (F = d.face₂ ∧ σ ∈ d.cells₂) ∨
      (F ∈ S.faces ∧ F ≠ d.face ∧ S.sub σ F) := by
  rw [splitFace_faces] at hF
  rw [splitFace_sub] at hs
  rcases hF with rfl | rfl | ⟨hF, hFface⟩
  · rw [d.subRel_face₁_iff] at hs
    rcases hs with rfl | hs | hs
    · exact absurd hσ d.face₁_notMem
    · exact absurd hs hear
    · exact Or.inl ⟨rfl, hs⟩
  · rw [d.subRel_face₂_iff] at hs
    rcases hs with rfl | hs | hs
    · exact absurd hσ d.face₂_notMem
    · exact absurd hs hear
    · exact Or.inr (Or.inl ⟨rfl, hs⟩)
  · rw [d.old_subRel_iff hσ (S.mem_cells_of_mem_faces hF) hface
      (Set.mem_singleton_iff.not.1 hFface)] at hs
    exact Or.inr (Or.inr ⟨hF, Set.mem_singleton_iff.not.1 hFface, hs⟩)

/-- **A 2-cell split away from the ear's ends preserves the invariant.**

`hear` — the anchor is no cell of the ear, in particular neither of its two ends — is the
blueprint's *"earlier ears do not end at `a`"*, and it is exactly what the statement needs: an
anchor at an end of the ear lies on both new boundary paths, and both new 2-cells are then
incident with it. -/
theorem uniqueFaceAt (h : S.UniqueFaceAt σ) (hσ : σ ∈ S.cells) (hface : σ ≠ d.face)
    (hear : σ ∉ d.earCells) : (S.splitFace d).UniqueFaceAt σ := by
  -- On a boundary path of the split 2-cell, the anchor is below that 2-cell — and below no
  -- other, by the invariant. So the "one new, one old" cases cannot occur.
  have hpath : ∀ ⦃F⦄, F ∈ S.faces → F ≠ d.face → S.sub σ F →
      σ ∉ S.pathCells d.source d.path₁ ∪ S.pathCells d.source d.path₂ := by
    intro F hF hFne hsub hmem
    exact hFne (h hF d.face_mem hsub (d.sub_face.2 (Or.inr hmem)))
  -- The two boundary paths meet only at the ear's two ends, which are cells of the ear.
  have hmeet : σ ∈ d.cells₁ → σ ∈ d.cells₂ → False := by
    intro h₁ h₂
    have hmem : σ ∈ S.pathCells d.source d.path₁ ∩ S.pathCells d.source d.path₂ := ⟨h₁, h₂⟩
    rw [d.paths_meet] at hmem
    rcases hmem with rfl | rfl
    exacts [hear (Or.inl d.isPathGraph.source_mem), hear (Or.inl d.isPathGraph.target_mem)]
  intro F₁ F₂ hF₁ hF₂ hs₁ hs₂
  have hcase := d.sub_splitFace_cases hσ hface hear
  rcases hcase hF₁ hs₁ with ⟨rfl, hc₁⟩ | ⟨rfl, hc₁⟩ | ⟨ho₁, hn₁, hb₁⟩ <;>
    rcases hcase hF₂ hs₂ with ⟨rfl, hc₂⟩ | ⟨rfl, hc₂⟩ | ⟨ho₂, hn₂, hb₂⟩
  · rfl
  · exact (hmeet hc₁ hc₂).elim
  · exact absurd (Set.mem_union_left _ hc₁) (hpath ho₂ hn₂ hb₂)
  · exact (hmeet hc₂ hc₁).elim
  · rfl
  · exact absurd (Set.mem_union_right _ hc₁) (hpath ho₂ hn₂ hb₂)
  · exact absurd (Set.mem_union_left _ hc₂) (hpath ho₁ hn₁ hb₁)
  · exact absurd (Set.mem_union_right _ hc₂) (hpath ho₁ hn₁ hb₁)
  · exact h ho₁ ho₂ hb₁ hb₂

/-- **A 0-cell away from the ear's two ends is away from the ear.** The hypothesis
`SplitData.uniqueFaceAt` asks for, in the form a consumer has it: the ear meets the old skeleton
exactly at its two ends, and its edges are fresh names. -/
theorem notMem_earCells_of_mem_vertexSet {z : γ} (hz : z ∈ V(S.skel)) (hs : z ≠ d.source)
    (ht : z ≠ d.target) : z ∉ d.earCells := by
  rintro (hmem | hmem)
  · have : z ∈ ({d.source, d.target} : Set γ) := d.vertexSet_inter ▸ ⟨hmem, hz⟩
    rcases this with rfl | rfl
    exacts [hs rfl, ht rfl]
  · exact d.edge_fresh hmem (S.mem_cells_of_mem_vertexSet hz)

end SplitData

/-! ### The paragraph, in geometric shape

`Schoenflies.polyAccessible_of_stronglyAccessible` asks for `hunique`, *the only current source
2-cell whose closure contains `a` is the prescribed one*. That is the abstract invariant read
through assertion (ix): a 0-cell in the closure of an open 2-cell is below it. -/

namespace Realization

variable {R : S.Realization} {D : Set Plane} {z F : γ}

/-- **The 2-cell above `z` is the only one whose closure contains `R.pos z`.** Assertion (ix)
turns the geometric incidence into the abstract one, and the invariant names the cell. -/
theorem eq_face_of_pos_mem_closure_cell (hcd : R.IsCellDecomposition D) (h : S.UniqueFaceAt z)
    (hz : z ∈ V(S.skel)) (hF : F ∈ S.faces) (hsub : S.sub z F) {G : γ} (hG : G ∈ S.faces)
    (hmem : R.pos z ∈ closure (R.cell G)) : G = F := by
  refine h.eq hF hsub hG (hcd.sub_of_subset_closure (S.mem_cells_of_mem_vertexSet hz)
    (S.mem_cells_of_mem_faces hG) ?_)
  rw [R.cell_vertex hz]
  exact Set.singleton_subset_iff.2 hmem

/-- **`hunique` of `Schoenflies.polyAccessible_of_stronglyAccessible`.** The only current 2-cell
whose closure contains the anchor is the prescribed one — the whole point of the combinatorial
paragraph, in the shape the access-cone argument consumes.

The family `cells` is the one `Schoenflies.CellsAbsorb` is stated for at a stage, namely the open
2-cells of the realization. Nothing here is about which realization: the same theorem applied to
`P.src` and to `P.tgt` gives the source and target halves, with the *same* abstract `F`. -/
theorem unique_cell_of_uniqueFaceAt (hcd : R.IsCellDecomposition D) (h : S.UniqueFaceAt z)
    (hz : z ∈ V(S.skel)) (hF : F ∈ S.faces) (hsub : S.sub z F) :
    ∀ A ∈ {A : Set Plane | ∃ G ∈ S.faces, A = R.cell G}, R.pos z ∈ closure A → A = R.cell F := by
  rintro A ⟨G, hG, rfl⟩ hmem
  rw [eq_face_of_pos_mem_closure_cell hcd h hz hF hsub hG hmem]

end Realization

end CellStructure

end Schoenflies
