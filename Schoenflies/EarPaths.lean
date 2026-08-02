/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransfer
import Schoenflies.Graph.PathOn

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

/-- **A supply of fresh names.** `EarStep` needs `2k + 1` names outside the current structure's
cells — one per ear edge, one per interior vertex, and two for the new 2-cells — and this is
where `[Infinite γ]` is spent. The cells of a `CellStructure` are finite by three of its own
fields, so their complement is infinite and holds a set of any size. -/
theorem exists_fresh_list [Infinite γ] {s : Set γ} (hs : s.Finite) (n : ℕ) :
    ∃ l : List γ, l.length = n ∧ l.Nodup ∧ ∀ z ∈ l, z ∉ s := by
  obtain ⟨t, hts, hcard⟩ := hs.infinite_compl.exists_subset_card_eq n
  exact ⟨t.toList, by simp [hcard], t.nodup_toList,
    fun z hz => hts (Finset.mem_toList.1 hz)⟩

/-- **The abstract ear on fresh names.** Between two distinct 0-cells there is, for every
length, a path graph whose edges and interior vertices are cells of no current structure — the
four freshness fields of `CellStructure.SplitData`, discharged. The names come from
`exists_fresh_list` and the graph from `Graph.pathOn`. -/
theorem exists_abstract_ear [Infinite γ] (S : CellStructure γ) {z w : γ}
    (hz : z ∈ V(S.skel)) (hw : w ∈ V(S.skel)) (hzw : z ≠ w) (k : ℕ) :
    ∃ (ear : Graph γ γ) (earWalk : List γ), ear.IsPathGraph z earWalk w ∧
      earWalk.length = k + 1 ∧ Disjoint V(ear) E(ear) ∧
      V(ear) ∩ V(S.skel) = {z, w} ∧ (∀ ⦃f⦄, f ∈ E(ear) → f ∉ S.cells) ∧
      (∀ ⦃c⦄, c ∈ V(ear) → c ≠ z → c ≠ w → c ∉ S.cells) := by
  classical
  obtain ⟨l, hlen, hnd, hfresh⟩ := exists_fresh_list S.finite_cells (2 * k + 1)
  set fs := l.take (k + 1) with hfs
  set vs := l.drop (k + 1) with hvs
  have hfslen : fs.length = k + 1 := by simp [hfs, hlen]; omega
  have hvslen : vs.length = k := by simp [hvs, hlen]; omega
  have hfsnd : fs.Nodup := hnd.sublist (List.take_sublist _ _)
  have hvsnd : vs.Nodup := hnd.sublist (List.drop_sublist _ _)
  have hdisj : fs.Disjoint vs := List.disjoint_take_drop hnd le_rfl
  have hfsfresh : ∀ f ∈ fs, f ∉ S.cells := fun f hf => hfresh f (List.mem_of_mem_take hf)
  have hvsfresh : ∀ c ∈ vs, c ∉ S.cells := fun c hc => hfresh c (List.mem_of_mem_drop hc)
  -- The steps: each fresh edge takes us to the next fresh vertex, the last one to `w`.
  set steps := fs.zip (vs ++ [w]) with hsteps
  have hlen₂ : (vs ++ [w]).length = k + 1 := by simp [hvslen]
  have hmapfst : steps.map Prod.fst = fs := List.map_fst_zip (by omega)
  have hmapsnd : steps.map Prod.snd = vs ++ [w] := List.map_snd_zip (by omega)
  have hlast : ∀ (d : γ) (l : List γ), (l ++ [w]).getLastD d = w := by
    intro d l
    induction l generalizing d with
    | nil => rfl
    | cons a t ih => rw [List.cons_append, List.getLastD_cons]; exact ih a
  have hwvs : w ∉ vs := fun hh => hvsfresh w hh (S.mem_cells_of_mem_vertexSet hw)
  have hzvs : z ∉ vs := fun hh => hvsfresh z hh (S.mem_cells_of_mem_vertexSet hz)
  have hnodupv : (z :: steps.map Prod.snd).Nodup := by
    rw [hmapsnd]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton]
      exact fun hh => hh.elim hzvs hzw
    · refine List.nodup_append.2 ⟨hvsnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      rintro rfl
      exact hwvs (hb ▸ ha)
  have hpath := Graph.isPathGraph_pathOn hnodupv (hmapfst ▸ hfsnd)
  rw [hmapfst, hmapsnd, hlast z vs] at hpath
  have hV : V(Graph.pathOn z steps) = insert z {c | c ∈ vs ++ [w]} := by
    rw [Graph.vertexSet_pathOn, hmapsnd]
  have hE : E(Graph.pathOn z steps) = {g | g ∈ fs} := by
    rw [Graph.edgeSet_pathOn, hmapfst]
  refine ⟨Graph.pathOn z steps, fs, hpath, hfslen, ?_, ?_, ?_, ?_⟩
  · rw [hV, hE, Set.disjoint_left]
    rintro c (rfl | hc) hcE
    · exact hfsfresh c hcE (S.mem_cells_of_mem_vertexSet hz)
    · rcases List.mem_append.1 hc with hc' | hc'
      · exact hdisj hcE hc'
      · rw [List.mem_singleton] at hc'
        exact hfsfresh c hcE (hc' ▸ S.mem_cells_of_mem_vertexSet hw)
  · rw [hV]
    ext c
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_setOf_eq, List.mem_append,
      List.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hc | hc, hcV⟩
      · exact Or.inl rfl
      · exact absurd (S.mem_cells_of_mem_vertexSet hcV) (hvsfresh c hc)
      · exact Or.inr hc
    · rintro (rfl | rfl)
      exacts [⟨Or.inl rfl, hz⟩, ⟨Or.inr (Or.inr rfl), hw⟩]
  · intro f hf
    rw [hE] at hf
    exact hfsfresh f hf
  · intro c hc hcz hcw
    rw [hV] at hc
    rcases hc with rfl | hc
    · exact absurd rfl hcz
    · rcases List.mem_append.1 hc with hc' | hc'
      · exact hvsfresh c hc'
      · exact absurd (List.mem_singleton.1 hc') hcw

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
