/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.EarDraw

/-!
# Where the ear lies, and the crosscut it becomes

`Schoenflies/EarDraw.lean` draws the ear; this module says **where the drawn ear is** with
respect to the current stage, and assembles the `SplitData.EarCrosscut` out of that. It is
stated for either realization of the stage: direction (a) of `thm:finite-transfer` is handed its
ear on the source side and (b) on the target side, and the placement argument does not know the
difference — see the docstring of `Schoenflies.exists_earCrosscut`.

Four facts, in the order they are used.

* `Graph.disjoint_walkPointSet_diff` — **the ear's interior misses the current subgraph.** The
  hypotheses of `Schoenflies.EarStep` say only that the ear's interior *vertices* are new; that
  its interior *points* are new is the plane-graph condition on `H`, spent twice: a point on an
  ear edge that is a vertex of `B` is an end of that ear edge, and a point on both an ear edge
  and an edge of `B` is a vertex shared by the two.
* `Graph.IsPath.eq_singleton_of_inc` (`Schoenflies/Graph/Walk.lean`) — **the one case that is not
  covered**: an ear edge that is already an edge of `B` has both its ends in `V(B)`, hence both
  equal to the two prescribed ends, and a path whose edge joins its own two ends is that one
  edge. `Schoenflies.EarStep` is then trivial on such an ear, since `B ∪ ear = B`
  (`Graph.union_eq_left_of_le`, `Schoenflies/Graph/TwoConnected.lean`); every other ear satisfies
  `∀ e ∈ D, e ∉ E(B)`, which is what the disjointness above asks for.
* `Graph.IsDrawing.isPolygonal_walkPointSet` (`Schoenflies/Graph/DrawnWalk.lean`) — a drawn walk
  whose edges are polygonal arcs is a polygonal set, by `Schoenflies.IsPolygonal.union` along the
  walk. With the disjointness this gives `EarCrosscut.polygonal`: no ear edge can be an *outer*
  edge, because the outer curve is already occupied by `B` and the ear's interior is not.

## Blueprint

* `Schoenflies.exists_earCrosscut` — the fourth paragraph of the proof of
  `thm:finite-transfer`: "the interior of each ear lies in one current face", turned into the
  geometric input `SplitData.EarCrosscut` that `SplitData.realize` consumes.
-/

open Set
open scoped Graph

namespace Graph

section Plane

open Schoenflies

variable {β : Type*} {H B : Graph Plane β} {Hdraw : β → ℝ → Plane}

/-- **The ear's interior misses the current subgraph.**

`x` is a point of the drawn path other than its two ends and a point of `|B|`. Then `x` is a
vertex the path visits — if it were an interior point of an ear edge it would have to be a
vertex of `H` shared with `B`, and the plane-graph condition puts every such point at an end of
the ear edge — and, being on `|B|`, it is a vertex of `B`. The freshness of the ear's interior
vertices does the rest.

The hypothesis `hfresh` is not decoration: without it the ear could be an edge `B` already has,
and then its whole arc lies in `|B|`. `Graph.IsPath.eq_singleton_of_inc` shows that is the only
way it can fail. -/
theorem disjoint_walkPointSet_diff (hH : IsDrawing H Hdraw) (hBH : B ≤ H)
    {a b : Plane} {D : List β} (hD : H.IsPath a D b)
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hfresh : ∀ e ∈ D, e ∉ E(B)) :
    Disjoint (walkPointSet H Hdraw a D \ {a, b}) (pointSet B Hdraw) := by
  rw [Set.disjoint_left]
  rintro x ⟨hx, hxab⟩ hxB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxab
  push Not at hxab
  -- Every point of `|B|` on the drawn path is a vertex the path visits.
  have hxwalk : x ∈ H.walkVertices a D := by
    rcases hx with hx | hx
    · exact hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨p, q, hl⟩ := exists_isLink_of_mem_edgeSet (hD.edge_mem he)
    have hends : x = p ∨ x = q → x ∈ H.walkVertices a D := by
      rintro (rfl | rfl)
      exacts [mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_left⟩,
        mem_walkVertices_of_mem_covered ⟨e, he, hl.inc_right⟩]
    rcases hxB with hxB | hxB
    · exact hends (hH.vertex_mem_edgeArc hl (hBH.vertexSet_mono hxB) hxe)
    · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 hxB
      have hge : e ≠ g := fun h => hfresh e he (h ▸ hg)
      obtain ⟨-, hInc, -⟩ := hH.edge_inter (hD.edge_mem he) (hBH.edgeSet_mono hg) hge hxe hxg
      exact mem_walkVertices_of_mem_covered ⟨e, he, hInc⟩
  -- …and it is a vertex of `B`.
  have hxV : x ∈ V(B) := by
    rcases hxB with hxB | hxB
    · exact hxB
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 hxB
    obtain ⟨p, q, hl⟩ := exists_isLink_of_mem_edgeSet (hBH.edgeSet_mono hg)
    rcases hH.vertex_mem_edgeArc hl (walkVertices_subset_vertexSet hD.left_mem hxwalk) hxg with
      rfl | rfl
    exacts [mem_vertexSet_of_inc_of_mem_edgeSet hBH hg hl.inc_left,
      mem_vertexSet_of_inc_of_mem_edgeSet hBH hg hl.inc_right]
  exact hint x hxwalk hxab.1 hxab.2 hxV

/-- **An interior point of an edge arc is neither of two prescribed vertices.** The plane-graph
condition puts every vertex on an edge arc at one of its two ends. -/
theorem notMem_of_mem_edgeArc_diff (hH : IsDrawing H Hdraw) {e : β} {p q x : Plane}
    (hl : H.IsLink e p q) (hx : x ∈ edgeArc Hdraw e \ {p, q}) {y : Plane} (hy : y ∈ V(H)) :
    x ≠ y := by
  rintro rfl
  exact hx.2 (hH.vertex_mem_edgeArc hl hy hx.1)

/-- **A walk between distinct ends departs along an edge.** The ear step of
`thm:finite-transfer`(b) needs the ear's first edge, as the nonboundary edge the fresh anchor at
that end carries; the other end's is the first edge of the reversed walk. -/
theorem IsWalk.exists_isLink_left_of_ne {a b : Plane} {D : List β} (h : H.IsWalk a D b)
    (hab : a ≠ b) : ∃ e ∈ D, ∃ m, H.IsLink e a m := by
  cases h with
  | nil => exact absurd rfl hab
  | cons hl _ => exact ⟨_, List.mem_cons_self .., _, hl⟩

/-- **The degenerate ear adds nothing.** If some edge of the ear is already an edge of `B` then
both its ends lie in `V(B)`, so both are among the two prescribed ends, and
`Graph.IsPath.eq_singleton_of_inc` makes the ear that one edge — which `B` already has, so the
union is `B` itself.

This is the branch `Schoenflies.exists_earCrosscut` excludes with its hypothesis
`∀ e ∈ D, e ∉ E(B)`; together the two cover every ear an ear step is handed, in either
direction. -/
theorem union_pathGraphOf_eq_left (hH : IsDrawing H Hdraw) (hBH : B ≤ H) {a b : Plane} {D : List β}
    (hD : H.IsPath a D b) (hab : a ≠ b) (ha : a ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    {e : β} (heD : e ∈ D) (heB : e ∈ E(B)) :
    B.union (H.pathGraphOf a D) = B := by
  obtain ⟨p, q, hl⟩ := exists_isLink_of_mem_edgeSet (hD.edge_mem heD)
  have hpq : p ≠ q := fun h => hH.not_isLoopAt e p (by rw [← h] at hl; exact hl)
  have hpV : p ∈ V(B) := mem_vertexSet_of_inc_of_mem_edgeSet hBH heB hl.inc_left
  have hqV : q ∈ V(B) := mem_vertexSet_of_inc_of_mem_edgeSet hBH heB hl.inc_right
  have hends : ∀ {x : Plane}, x ∈ H.walkVertices a D → x ∈ V(B) → x = a ∨ x = b := by
    intro x hx hxB
    by_contra hcon
    push Not at hcon
    exact hint x hx hcon.1 hcon.2 hxB
  have hp' := hends (mem_walkVertices_of_mem_covered ⟨e, heD, hl.inc_left⟩) hpV
  have hq' := hends (mem_walkVertices_of_mem_covered ⟨e, heD, hl.inc_right⟩) hqV
  have hkey : H.Inc e a ∧ H.Inc e b := by
    rcases hp' with hp | hp <;> rcases hq' with hq | hq
    · exact absurd (hp.trans hq.symm) hpq
    · exact ⟨by rw [← hp]; exact hl.inc_left, by rw [← hq]; exact hl.inc_right⟩
    · exact ⟨by rw [← hq]; exact hl.inc_right, by rw [← hp]; exact hl.inc_left⟩
    · exact absurd (hp.trans hq.symm) hpq
  obtain rfl : D = [e] := hD.eq_singleton_of_inc hab heD hkey.1 hkey.2
  have hle : H.pathGraphOf a [e] ≤ B := by
    constructor
    · intro x hx
      rw [pathGraphOf_vertexSet] at hx
      rcases mem_walkVertices_iff.1 hx with rfl | ⟨f, hf, hinc⟩
      · exact ha
      · rw [List.mem_singleton] at hf
        subst hf
        rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
        exacts [hpV, hqV]
    · intro f x y hlk
      rw [pathGraphOf_isLink] at hlk
      obtain ⟨hf, hxy, -, -⟩ := hlk
      rw [List.mem_singleton] at hf
      subst hf
      exact (hBH.isLink_iff heB).2 hxy
  exact union_eq_left_of_le hle

/-- **No ear edge is an outer edge.** The outer curve is already occupied by `B`, and the ear's
interior is not; an ear edge drawn inside the outer curve would put an interior point of its own
arc in `|B|`, which `Graph.disjoint_walkPointSet_diff` forbids.

Both consumers of the ear need this. `Schoenflies.exists_earCrosscut` spends it on polygonality,
through `IsSourceExtension.edge_dichotomy`; the assembly of one ear insertion spends it on the
anchor clause of the transfer invariant, which asks that the ear really does bring a nonboundary
edge to each of its two ends. -/
theorem notSubset_of_mem_ear {outer : Set Plane} (hH : IsDrawing H Hdraw) (hBH : B ≤ H)
    {a b : Plane} {D : List β} (hD : H.IsPath a D b)
    (hdisj : Disjoint (walkPointSet H Hdraw a D \ {a, b}) (pointSet B Hdraw))
    (houter : outer ⊆ pointSet B Hdraw) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    {e : β} (he : e ∈ D) : ¬ edgeArc Hdraw e ⊆ outer := by
  intro hout
  obtain ⟨p, q, hl⟩ := exists_isLink_of_mem_edgeSet (hD.edge_mem he)
  obtain ⟨x, hx⟩ := (hH.edge_isArcBetween hl).nonempty_diff
  refine Set.disjoint_left.1 hdisj ⟨Or.inr (Set.mem_biUnion he hx.1), ?_⟩ (houter (hout hx.1))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  push Not
  exact ⟨notMem_of_mem_edgeArc_diff hH hl hx (hBH.vertexSet_mono ha),
    notMem_of_mem_edgeArc_diff hH hl hx (hBH.vertexSet_mono hb)⟩

end Plane

end Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- **The geometric half of one ear insertion.**

From the data `Schoenflies.EarStep` is handed — the current subgraph `B`, the ear as a path `D`
of `H` between two vertices of `B`, and the freshness of its interior — this produces the
abstract `CellStructure.SplitData` of the insertion together with the drawing that makes it a
polygonal crosscut of the current 2-cell it lands in.

Everything geometric happens here. The two ends are already drawn 0-cells, so no subdivision is
needed; the ear's interior is connected, misses the current skeleton
(`Graph.disjoint_walkPointSet_diff`) and lies in the closed domain, so
`GeneratedPair.exists_face_and_boundary_paths` places it in a unique 2-cell and cuts that
2-cell's boundary cycle into the two paths; and no ear edge can be an outer edge
(`Graph.notSubset_of_mem_ear`), so every ear edge is polygonal and the drawn ear is a polygonal
set.

**It is stated for either realization of the stage.** Direction (a) is handed its ear on the
source side and (b) on the target side, and nothing in the argument knows the difference: the
five clauses that used to name `T.src` are the realization's cell decomposition, its outer set,
what it occupies, which of its 0-cells are drawn, and the absorption family. `hH` is likewise
`IsSourceExtension` of *some* realization — only `isDrawing`, `pointSet_subset` and
`edge_dichotomy` are read, and those are about `H` and the two ambient sets.

`hfresh` is the one hypothesis not literally among `EarStep`'s: it says the ear brings new
edges. `Graph.IsPath.eq_singleton_of_inc` shows the only ear that fails it is a single edge `B`
already has, for which `B ∪ ear = B` and `EarStep` is trivial. -/
theorem exists_earCrosscut [Infinite γ]
    {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {S' : CellStructure γ} {R₀ : S'.Realization} {outer dom : Set Plane}
    {R : T.str.Realization} {H B : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension R₀ outer dom H Hdraw)
    (hS : T.str.CombInvariants)
    (hcd : R.IsCellDecomposition dom) (houterR : R.outerSet = outer)
    (hskel : R.skeletonSet = pointSet B Hdraw) (hVB : V(B) ⊆ V(R.graph))
    (hcells : CellsAbsorb R.skeletonSet {A | ∃ F ∈ T.str.faces, A = R.cell F})
    (hBH : B ≤ H) {a b : Plane} {D : List γ} (hD : H.IsPath a D b) (hab : a ≠ b)
    (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hfresh : ∀ e ∈ D, e ∉ E(B)) :
    ∃ (d : T.str.SplitData) (earPos : γ → Plane) (earDraw : γ → ℝ → Plane),
      d.EarCrosscut R earPos earDraw ∧
        d.earSet earPos earDraw = walkPointSet H Hdraw a D ∧
        R.pos d.source = a ∧ R.pos d.target = b ∧
        earPos '' V(d.ear) = H.walkVertices a D := by
  have hdrawH : IsDrawing H Hdraw := hH.isDrawing
  -- The ear's interior is disjoint from what the current stage occupies.
  have hdisj : Disjoint (walkPointSet H Hdraw a D \ {a, b}) (pointSet B Hdraw) :=
    disjoint_walkPointSet_diff hdrawH hBH hD hint hfresh
  have harc : IsArcBetween (walkPointSet H Hdraw a D) a b :=
    hdrawH.isArcBetween_walkPointSet hD hab
  -- The outer curve is already occupied, so no ear edge is an outer edge.
  have houter : outer ⊆ pointSet B Hdraw := by
    have h1 : R.outerSet ⊆ R.skeletonSet := R.outerSet_subset_skeletonSet
    rwa [houterR, hskel] at h1
  have hpolyD : ∀ e ∈ D, IsPolygonal (edgeArc Hdraw e) := fun e he =>
    ((hH.edge_dichotomy (hD.edge_mem he)).resolve_left
      (notSubset_of_mem_ear hdrawH hBH hD hdisj houter ha hb he)).1
  -- The two ends are drawn 0-cells of the current structure.
  obtain ⟨z, hzV, hza⟩ := (Realization.vertexSet_graph R) ▸ hVB ha
  obtain ⟨w, hwV, hwb⟩ := (Realization.vertexSet_graph R) ▸ hVB hb
  have hzw : z ≠ w := fun h => hab (by rw [← hza, ← hwb, h])
  have hzc : z ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hzV
  have hwc : w ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hwV
  -- The ear, on fresh names, drawn where `H` draws it.
  obtain ⟨ear, earWalk, earPos, earDraw, hpath, hdisjear, hvfresh, hefresh, hinj, hposz, hposw,
    himg, hdrawEar, hpts⟩ :=
    exists_drawn_ear hdrawH hD (iff_of_false hzw hab) T.str.finite_cells hzc hwc
  have hearSet : Graph.pointSet (ear.map earPos) earDraw = walkPointSet H Hdraw a D := by
    rw [hpts, pointSet_pathGraphOf hD.isWalk]
  -- The ear meets the old skeleton exactly in its two ends.
  have hinter : V(ear) ∩ V(T.str.skel) = {z, w} := by
    refine Set.Subset.antisymm (fun c ⟨hc, hcs⟩ => ?_) ?_
    · by_contra hcon
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
      push Not at hcon
      exact hvfresh hc hcon.1 hcon.2 (T.str.mem_cells_of_mem_vertexSet hcs)
    · rintro c (rfl | rfl)
      exacts [⟨hpath.source_mem, hzV⟩, ⟨hpath.target_mem, hwV⟩]
  -- Where it lies: one current 2-cell, whose boundary cycle cuts into the two paths.
  have hNsub : walkPointSet H Hdraw a D \ {a, b} ⊆ dom := by
    refine Set.Subset.trans (Set.Subset.trans Set.diff_subset ?_) hH.pointSet_subset
    rw [← pointSet_pathGraphOf hD.isWalk]
    exact pointSet_mono (pathGraphOf_le hD.isWalk)
  obtain ⟨F, hF, hNF, -, P₁, P₂, hp₁, hp₂, hsub, hmeet⟩ :=
    T.exists_face_and_boundary_paths hS hcd hcells
      harc.isPreconnected_diff harc.nonempty_diff
      hNsub (by rw [hskel]; exact hdisj) hab hzV hwV hza hwb
      harc.left_mem_closure_diff harc.right_mem_closure_diff
  obtain ⟨d, hdface, hdsrc, hdtgt, hdear, -, -, -⟩ :=
    T.exists_splitDataOfEar hF hzw hpath hdisjear hinter hefresh hvfresh hp₁ hp₂ hsub hmeet
  have hdearSet : d.earSet earPos earDraw = walkPointSet H Hdraw a D := by
    rw [show d.earSet earPos earDraw = Graph.pointSet (d.ear.map earPos) earDraw from rfl, hdear,
      hearSet]
  refine ⟨d, earPos, earDraw, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hdearSet, by rw [hdsrc]; exact hza,
    by rw [hdtgt]; exact hwb, by rw [hdear]; exact himg⟩
  · rw [hdsrc, hposz, hza]
  · rw [hdtgt, hposw, hwb]
  · rw [hdear]; exact hinj
  · rw [show d.earGraph earPos = d.ear.map earPos from rfl, hdear]; exact hdrawEar
  · rw [hdearSet, hdsrc, hdtgt, hza, hwb, hdface]
    exact hNF
  · rw [hdface]
    exact R.disjoint_cell_skeletonSet hcd hF
  · rw [hdearSet]
    exact hdrawH.isPolygonal_walkPointSet hD.isWalk hpolyD

/-- **The degenerate ear, disposed of** — direction (a). The ear adds nothing, so the partial
transfer carries over unchanged. -/
theorem isPartialTransferOf_union_of_mem_edgeSet
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {H B : Graph Plane γ}
    {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsPartialTransferOf T P B Hdraw par)
    (hH : IsDrawing H Hdraw) (hBH : B ≤ H) {a b : Plane} {D : List γ}
    (hD : H.IsPath a D b) (hab : a ≠ b) (ha : a ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    {e : γ} (heD : e ∈ D) (heB : e ∈ E(B)) :
    IsPartialTransferOf T P (B.union (H.pathGraphOf a D)) Hdraw par := by
  rw [Graph.union_pathGraphOf_eq_left hH hBH hD hab ha hint heD heB]
  exact hT


end Schoenflies
