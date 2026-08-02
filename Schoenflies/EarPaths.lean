/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransfer

/-!
# The abstract half of one ear insertion

`Schoenflies.EarStep` — step 3 of `thm:finite-transfer`(a) — has to turn a drawn ear into a
`CellStructure.SplitData` and two new realizations. This module does the first half: from the
ear's two endpoints and its interior it produces **the 2-cell the ear is inserted into, the two
0-cells its ends are, and the two boundary paths between them**, with the two properties
`SplitData` asks of them (`sub_face` and `paths_meet`).

That is everything the abstract `SplitData` needs except the ear graph itself and the fresh
names for the two new 2-cells.

## No subdivision is needed

The blueprint's step 3 reads "at most two edge subdivisions followed by one 2-cell split", the
subdivisions being what turns the ear's endpoints into 0-cells. In the Lean formulation they are
**already** 0-cells: `IsPartialTransferOf.vertexSet_subset` says `V(B) ⊆ V(T.src.graph)` and
`EarStep` hypothesises that both ends lie in `V(B)`, so
`IsPartialTransferOf.exists_cell_of_mem_vertexSet` names the 0-cells they are. The interface
assumes as much on its own account: `IsCellDecomposition.exists_face_of_ear` takes the two ends
as *cells* `a b : γ` and would not apply otherwise.

So one ear insertion is one split, and the subdivision constructor is needed by
`Schoenflies.CommonSubdivision` — step 1 — and not by the ear induction.

## Blueprint

* `Schoenflies.IsPartialTransferOf.exists_cell_of_mem_vertexSet` — a vertex of the current
  subgraph is a drawn 0-cell of the current stage.
* `Schoenflies.GeneratedPair.exists_face_and_boundary_paths` — the fourth paragraph of the proof
  of `thm:finite-transfer`(a) on the source side: "the interior of the ear lies in one current
  face `F`, and its endpoints lie on the boundary cycle of `F`", together with the cut of that
  cycle into the two boundary paths `B₁`, `B₂` of `def:generated-structure`, operation 2.
* `Schoenflies.GeneratedPair.splitDataOfEar` — the abstract data of operation 2, assembled. What
  `EarStep` still owes past this is the ear graph on fresh names and the two realizations.
-/

open Set
open scoped Graph

namespace Schoenflies

open CellStructure

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}
  {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {B : Graph Plane γ}
  {Hdraw : γ → ℝ → Plane} {par : γ → γ}

/-- **A vertex of the transferred subgraph is a drawn 0-cell.** Three lines, and the reason the
ear step needs no subdivision: `IsPartialTransferOf` already asks the current structure to have
`B`'s vertices among its 0-cells. -/
theorem IsPartialTransferOf.exists_cell_of_mem_vertexSet
    (h : IsPartialTransferOf T P B Hdraw par) {a : Plane} (ha : a ∈ V(B)) :
    ∃ z ∈ V(T.str.skel), T.src.pos z = a := by
  have hmem := h.vertexSet_subset ha
  rw [Realization.vertexSet_graph] at hmem
  obtain ⟨z, hz, hza⟩ := hmem
  exact ⟨z, hz, hza⟩

namespace GeneratedPair

/-- **The 2-cell an ear is inserted into, and the two boundary paths of `def:generated-structure`
operation 2.** The ear's interior `N` is connected, nonempty, inside the domain and off the
skeleton; its two ends are drawn 0-cells in its closure. Then there is a unique 2-cell whose
open cell contains `N`, both ends are 0-cells below it, and its boundary cycle cuts at them into
two paths that carry exactly the cells below it and meet only at the two ends.

The last two conclusions are `SplitData.sub_face` and `SplitData.paths_meet` verbatim; the two
before them are `isPath₁` and `isPath₂`. What a `SplitData` still needs beyond this is the ear
graph itself and fresh names for the two new 2-cells. -/
theorem exists_face_and_boundary_paths (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hS : T.str.CombInvariants)
    (hcells : CellsAbsorb T.src.skeletonSet {A | ∃ F ∈ T.str.faces, A = T.src.cell F})
    {N : Set Plane} (hN : IsPreconnected N) (hNne : N.Nonempty) (hND : N ⊆ srcDom)
    (hNdisj : Disjoint N T.src.skeletonSet) {a b : Plane} (hab : a ≠ b)
    {z w : γ} (hz : z ∈ V(T.str.skel)) (hw : w ∈ V(T.str.skel))
    (hza : T.src.pos z = a) (hwb : T.src.pos w = b)
    (hacl : a ∈ closure N) (hbcl : b ∈ closure N) :
    ∃ F ∈ T.str.faces, N ⊆ T.src.cell F ∧ (∀ F' ∈ T.str.faces, N ⊆ T.src.cell F' → F' = F) ∧
      ∃ P₁ P₂, T.str.skel.IsPath z P₁ w ∧ T.str.skel.IsPath z P₂ w ∧
        (∀ ⦃σ⦄, T.str.sub σ F ↔ σ = F ∨ σ ∈ T.str.pathCells z P₁ ∪ T.str.pathCells z P₂) ∧
        T.str.pathCells z P₁ ∩ T.str.pathCells z P₂ = {z, w} := by
  have hzw : z ≠ w := fun hh => hab (hza ▸ hwb ▸ hh ▸ rfl)
  obtain ⟨F, hF, hNF, hsz, hsw, huniq⟩ := T.src_isCellDecomposition.exists_face_of_ear hcells
    hN hNne hND hNdisj hz hw (hza ▸ hacl) (hwb ▸ hbcl)
  obtain ⟨P₁, P₂, hp₁, hp₂, hsub, hmeet⟩ :=
    T.walks.exists_boundary_paths hS hF hz hw hsz hsw hzw
  exact ⟨F, hF, hNF, huniq, P₁, P₂, hp₁, hp₂, hsub, hmeet⟩

/-- **The abstract `SplitData` of one ear insertion.** Everything the split constructor needs,
from the ear graph and two fresh 2-cell names together with the output of
`exists_face_and_boundary_paths`. Nothing here is geometric: the caller supplies the ear as an
abstract path graph on fresh names, and this checks it into the structure.

What `Schoenflies.EarStep` still owes after this is the ear graph itself — the fresh names for
the drawn ear's interior vertices and edges — and the two realizations. -/
def splitDataOfEar (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {F z w : γ}
    (hF : F ∈ T.str.faces) (hzw : z ≠ w) {ear : Graph γ γ} {earWalk P₁ P₂ : List γ}
    (hear : ear.IsPathGraph z earWalk w)
    (hdisj : Disjoint V(ear) E(ear))
    (hinter : V(ear) ∩ V(T.str.skel) = {z, w})
    (hedge : ∀ ⦃f⦄, f ∈ E(ear) → f ∉ T.str.cells)
    (hvert : ∀ ⦃c⦄, c ∈ V(ear) → c ≠ z → c ≠ w → c ∉ T.str.cells)
    {face₁ face₂ : γ} (h₁ : face₁ ∉ T.str.cells) (h₂ : face₂ ∉ T.str.cells)
    (h₁ear : face₁ ∉ V(ear) ∪ E(ear)) (h₂ear : face₂ ∉ V(ear) ∪ E(ear)) (hne : face₁ ≠ face₂)
    (hp₁ : T.str.skel.IsPath z P₁ w) (hp₂ : T.str.skel.IsPath z P₂ w)
    (hsub : ∀ ⦃σ⦄, T.str.sub σ F ↔ σ = F ∨ σ ∈ T.str.pathCells z P₁ ∪ T.str.pathCells z P₂)
    (hmeet : T.str.pathCells z P₁ ∩ T.str.pathCells z P₂ = {z, w}) :
    T.str.SplitData where
  face := F
  face₁ := face₁
  face₂ := face₂
  ear := ear
  source := z
  target := w
  earWalk := earWalk
  path₁ := P₁
  path₂ := P₂
  isPathGraph := hear
  isPath₁ := hp₁
  isPath₂ := hp₂
  ear_disjoint := hdisj
  source_ne_target := hzw
  face_mem := hF
  vertexSet_inter := hinter
  edge_fresh := hedge
  vertex_fresh := hvert
  face₁_notMem := h₁
  face₂_notMem := h₂
  face₁_notMem_ear := h₁ear
  face₂_notMem_ear := h₂ear
  face_ne := hne
  sub_face := hsub
  paths_meet := hmeet

end GeneratedPair

end Schoenflies
