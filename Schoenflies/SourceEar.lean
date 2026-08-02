/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SourceAccess
import Schoenflies.FreshAccess
import Schoenflies.AnchorFace

/-!
# The source crosscut of one ear insertion, direction (b)

Direction (a) of `thm:finite-transfer` is handed its ear on the source side and has to produce
the corresponding crosscut in the target 2-cell; `Schoenflies.exists_target_ear` does that.
Direction (b) runs the other way, and this module is its mirror: the ear is given in the target,
`Schoenflies.exists_earCrosscut` places it there, and what has to be produced is a polygonal
crosscut of the **source** 2-cell between the corresponding source endpoints.

## Why it is not the same theorem with the arguments renamed

The join is the same — `lem:accessible-endpoints`, now
`Schoenflies.exists_crosscut_of_accessible_ends`, which takes the accessibility of the two
endpoints as hypotheses precisely so that both directions can share it. What differs is where
that accessibility comes from, and it is the one place where the two sides of a matched
cellulation are genuinely not mirror images.

On the target side every edge is polygonal, so `lem:polygonal-side-accessibility` applies to the
drawn skeleton as it stands. A *source* realization never satisfies that: its outer edges are
subarcs of the wild curve `C`. So the source side splits into two cases, and this module is that
split:

* **off `C`** — `CellStructure.Realization.polyAccessible_of_notMem_outer` (`SourceAccess.lean`),
  which runs `lem:polygonal-side-accessibility` against the drawn skeleton *with the outer edges
  deleted*, carrying `C` as the compact wild set the general statement already allows;
* **on `C`** — the anchor paragraph, `Schoenflies.polyAccessible_of_stronglyAccessible`
  (`FreshAccess.lean`), whose three inputs this module supplies from the stage: the absorption
  and covering halves of `lem:cellulation-invariants`(i), and `hunique` from the combinatorial
  invariant of `AnchorFace.lean`.

The second case is the one that needs `K` and `K'` kept apart. `K'` is the whole drawn skeleton,
which is what the cells are read against; `K` is the blueprint's compact set — the old closed
nonboundary edges together with the source ears already inserted — which is what the cone is
shrunk away from and what does not contain the anchor. `hKK` is the only relation between them
the argument uses, and it is stated here in the form a stage supplies: a point of the open region
that lies on the skeleton lies in `K`.

## Blueprint

* `Schoenflies.GeneratedPair.polyAccessible_src_of_notMem_outer`,
  `…polyAccessible_src_of_stronglyAccessible` — "for part (b), an endpoint not on `C` is
  accessible from the corresponding source face by `lem:polygonal-side-accessibility`" and the
  paragraph that follows it, both in the form the ear step consumes: a 0-cell below a 2-cell is
  polygonally accessible from it.
* `Schoenflies.GeneratedPair.exists_source_ear` — the source half of the fourth paragraph of the
  proof of `thm:finite-transfer`(b): the polygonal crosscut of the source 2-cell between the
  ear's two endpoints, which `Schoenflies.exists_target_earCrosscut` then draws the source ear
  along.
-/

open Set
open scoped Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

namespace GeneratedPair

variable (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)

/-! ### Accessibility of a source 0-cell from the 2-cell above it -/

/-- **An endpoint off the wild curve.** `lem:polygonal-side-accessibility` on the source side,
with the geometric hypothesis produced from the abstract incidence `z ≼ F`.

The three domain hypotheses are the ones every stage-level statement carries; see
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and its companion. -/
theorem polyAccessible_src_of_notMem_outer (hsrcOut : srcOuter ⊆ T.src.skeletonSet)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    {F z : γ} (hF : F ∈ T.str.faces) (hz : z ∈ V(T.str.skel)) (hsub : T.str.sub z F)
    (hoff : T.src.pos z ∉ srcOuter) :
    PolyAccessible (T.src.cell F) (T.src.pos z) :=
  Realization.polyAccessible_of_notMem_outer T.src_isCellDecomposition T.src_isFaceJordan
    T.src_isWeaklyAdmissible hsrcOut hsrcQ hsrcFr hF
    (Realization.IsCellDecomposition.pos_mem_closure_cell_of_sub T.src_isCellDecomposition hz hF
      hsub) hoff

/-- **An endpoint on the wild curve: the anchor paragraph.** A 0-cell drawn at a strongly
accessible point of `C`, off the compact part `K` of everything already drawn inside, is
polygonally accessible from the 2-cell above it — provided that 2-cell is the *only* one above
it, which is `CellStructure.UniqueFaceAt` and which the ear induction of
`thm:finite-transfer`(b) carries as the `anchor_uniqueFaceAt` clause of its invariant.

The covering half of `lem:cellulation-invariants`(i) is read off
`Realization.biUnion_faces_eq`: what the open region has left after the skeleton is exactly the
open 2-cells. -/
theorem polyAccessible_src_of_stronglyAccessible (hsrcOut : srcOuter ⊆ T.src.skeletonSet)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    {F z : γ} (hF : F ∈ T.str.faces) (hz : z ∈ V(T.str.skel)) (hsub : T.str.sub z F)
    (hu : T.str.UniqueFaceAt z) {D K : Set Plane} (hD : D ⊆ srcDom \ srcOuter)
    (hacc : StronglyAccessible D (T.src.pos z)) (hKc : IsCompact K) (hzK : T.src.pos z ∉ K)
    (hKK : ∀ ⦃x⦄, x ∈ D → x ∈ T.src.skeletonSet → x ∈ K) :
    PolyAccessible (T.src.cell F) (T.src.pos z) := by
  refine polyAccessible_of_stronglyAccessible hacc hKc hzK hKK
    (T.src.cellsAbsorb T.src_isCellDecomposition T.src_isFaceJordan hsrcOut hsrcQ hsrcFr) ?_
    (Realization.unique_cell_of_uniqueFaceAt T.src_isCellDecomposition hu hz hF hsub)
  intro x hxD hxK
  have hx : x ∈ (srcDom \ srcOuter) \ T.src.skeletonSet := ⟨hD hxD, hxK⟩
  rw [← Realization.biUnion_faces_eq T.src_isCellDecomposition hsrcOut] at hx
  obtain ⟨G, hG, hxG⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨T.src.cell G, ⟨G, hG, rfl⟩, hxG⟩

/-! ### The crosscut -/

/-- **The source crosscut of one ear insertion, direction (b).**

Given the abstract split data — which `Schoenflies.exists_earCrosscut` produced on the target
side, where the ear was handed to us — and the accessibility of the two source endpoints from
the source 2-cell, `lem:accessible-endpoints` supplies a polygonal crosscut of that 2-cell
between them. `Schoenflies.exists_target_earCrosscut` then draws the source ear along it.

Everything else is read off the stage: the 2-cell is the bounded region of the Jordan curve of
its own boundary walk (assertion (vii)), each endpoint is on that curve because it is a 0-cell
below the 2-cell, and the two endpoints are distinct because the two 0-cells are and positions
are injective. -/
theorem exists_source_ear {d : T.str.SplitData}
    (h₁ : PolyAccessible (T.src.cell d.face) (T.src.pos d.source))
    (h₂ : PolyAccessible (T.src.cell d.face) (T.src.pos d.target)) :
    ∃ P : Set Plane, IsPolygonal P ∧
      IsArcBetween P (T.src.pos d.source) (T.src.pos d.target) ∧
      P \ {T.src.pos d.source, T.src.pos d.target} ⊆ T.src.cell d.face ∧
      P ∩ frontier (T.src.cell d.face) = {T.src.pos d.source, T.src.pos d.target} := by
  have hopen : IsOpen (T.src.cell d.face) := T.src_isFaceJordan.isOpen d.face_mem
  have hfr := SplitData.frontier_cell_face (d := d) T.src_isCellDecomposition T.src_isFaceJordan
  refine exists_crosscut_of_accessible_ends hopen
    (T.src_isFaceJordan.isConnected d.face_mem).isPreconnected
    (Set.disjoint_iff_inter_eq_empty.2 hopen.inter_frontier_eq)
    (fun h => d.source_ne_target
      (T.src.injOn_pos d.source_mem_skel d.target_mem_skel h)) ?_ ?_ h₁ h₂
  · rw [hfr]; exact Or.inl SplitData.pos_source_mem_cellUnion_cells₁
  · rw [hfr]; exact Or.inl SplitData.pos_target_mem_cellUnion_cells₁

end GeneratedPair

end Schoenflies
