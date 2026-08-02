/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshOverlay

/-!
# 2-connectivity of the mesh overlay, reduced to its mesh-and-skeleton core

`Schoenflies.HasTwoConnectedMeshOverlays` (`Schoenflies/MeshOverlay.lean`) asks, at every
admissible stage, mesh size and fresh list, for joining arcs whose overlay
`Schoenflies.meshOverlayGraph` is 2-connected. This module discharges the *joining-arc half*
of that: it **chooses** the joining arcs — the freedom the existential grants, and the reason
it is there — as simple polygonal chains, and proves that once the overlay restricted to the
mesh and the old skeleton is spanned by a 2-connected subgraph, the chains go in one ear at a
time and the whole overlay is 2-connected.

What remains is the mesh-and-skeleton core itself, the named hypothesis
`Schoenflies.HasTwoConnectedCores` below: a 2-connected subgraph of the overlay containing
every overlay vertex on the mesh or on the old skeleton. Its discharger is the subdivision
bridge — the overlay restricted to the mesh pieces refines `Schoenflies.squareMesh`
(2-connected by `Schoenflies.meshGraph_isTwoConnected`), the overlay restricted to the
skeleton pieces subdivides `Γ'` (2-connected by admissibility), and the two glue on two shared
outer-ring vertices by `Graph.IsTwoConnected.union`.

## The choice of joining arcs

For the joining chains that `Schoenflies.exists_joinsFor` would supply, 2-connectivity can be
false: a chain doubling back on itself subdivides to a pendant edge. The chains chosen here
cannot double back. Each one is read off a *path* of an auxiliary overlay graph
(`Schoenflies.exists_simpleChain_to_base`), so consecutive segments share exactly their
junction and non-consecutive ones share nothing — `Schoenflies.IsSimpleChain`. In the mesh
overlay, such a chain subdivides to a genuine path between its two ends
(`Schoenflies.simpleChain_isPath_overlay`), with both ends on the mesh-and-skeleton core; and
`Graph.IsTwoConnected.ear` needs *nothing else* — in particular it tolerates the chain
crossing the mesh, the skeleton, or another chain, because the ear lemma never asks the ear's
interior to be fresh.

## Blueprint

* `Graph.IsTwoConnected.of_spanning_paths` — the ear induction of `lem:subdivision-ear-preserve`
  (b) iterated: a 2-connected subgraph absorbs any family of paths anchored on it, and once the
  family spans, the whole graph is 2-connected. General-purpose; a candidate for hoisting into
  `Schoenflies/Graph/Ear.lean`.
* `IsSimpleChain`, `exists_simpleChain_of_isPath` — a polygonal chain read off an overlay path
  never returns to covered territory.
* `exists_simpleChain_to_base` — Lemma 1.1/1.2 in the strengthened form this module needs: the
  chain, not just its carrier, is simple.
* `exists_simple_joins` — the joining arcs of `lem:polygonal-overlay`, chosen simple.
* `simpleChain_isPath_overlay` — a simple chain of source segments subdivides to a path of the
  overlay covering every overlay vertex on the chain.
* `HasTwoConnectedCores` — **the remaining named hypothesis**: the mesh-and-skeleton core of
  the overlay is spanned by a 2-connected subgraph.
* `hasTwoConnectedMeshOverlays_of` — the reduction: cores suffice for
  `Schoenflies.HasTwoConnectedMeshOverlays`.
* `hasMeshSteps_of_cores` — the composition down to `Schoenflies.HasMeshSteps`.
-/

open Metric Set
open scoped Graph

namespace Graph

variable {α β : Type*} {H K : Graph α β} {T : Set α}

/-- **A 2-connected subgraph absorbs a spanning family of anchored paths.** If every vertex of
`H` outside the 2-connected subgraph `K` lies on some path of `H` between two distinct
vertices of an anchor set `T ⊆ V(K)`, then `H` itself is 2-connected: each path goes in as an
ear (`Graph.IsTwoConnected.ear`, which does not ask the ear's interior to be fresh), the
subgraph grows until it spans, and 2-connectivity passes up by
`Graph.IsTwoConnected.of_le_of_vertexSet_subset`.

(General-purpose; a candidate for hoisting into `Schoenflies/Graph/Ear.lean`.) -/
theorem IsTwoConnected.of_spanning_paths (hfin : V(H).Finite) (hK : K.IsTwoConnected)
    (hKH : K ≤ H) (hT : T ⊆ V(K))
    (hcond : ∀ x ∈ V(H), x ∉ V(K) → ∃ a b D, H.IsPath a D b ∧ a ≠ b ∧ a ∈ T ∧ b ∈ T ∧
      x ∈ H.walkVertices a D) :
    H.IsTwoConnected := by
  -- Grow the subgraph one ear at a time; the induction is on how many vertices are missing.
  suffices h : ∀ n : ℕ, ∀ Kc : Graph α β, (V(H) \ V(Kc)).ncard ≤ n → Kc.IsTwoConnected →
      Kc ≤ H → V(K) ⊆ V(Kc) →
      ∃ K' : Graph α β, K'.IsTwoConnected ∧ K' ≤ H ∧ V(H) ⊆ V(K') by
    obtain ⟨K', h2, hle, hV⟩ := h (V(H) \ V(K)).ncard K le_rfl hK hKH subset_rfl
    exact h2.of_le_of_vertexSet_subset hle hV
  intro n
  induction n with
  | zero =>
    intro Kc hcard hKc hKcH _
    refine ⟨Kc, hKc, hKcH, fun x hx => ?_⟩
    by_contra hxK
    have hne : (V(H) \ V(Kc)).Nonempty := ⟨x, hx, hxK⟩
    rw [← Set.ncard_pos (hfin.sdiff)] at hne
    omega
  | succ n ih =>
    intro Kc hcard hKc hKcH hKKc
    by_cases hall : V(H) ⊆ V(Kc)
    · exact ⟨Kc, hKc, hKcH, hall⟩
    obtain ⟨x, hxH, hxKc⟩ := Set.not_subset.1 hall
    obtain ⟨a, b, D, hpath, hab, haT, hbT, hxD⟩ :=
      hcond x hxH fun hxK => hxKc (hKKc hxK)
    have hple : H.pathGraphOf a D ≤ H := pathGraphOf_le hpath.isWalk
    -- The path is an ear on the current subgraph: its two distinct ends are anchors.
    have hK' : (Kc.union (H.pathGraphOf a D)).IsTwoConnected :=
      hKc.ear (Compatible.of_le_le hKcH hple) hpath.isPathGraph_pathGraphOf hab
        (hKKc (hT haT)) (hKKc (hT hbT))
    have hK'le : Kc.union (H.pathGraphOf a D) ≤ H := union_le hKcH hple
    -- The missing vertex is on the path, so the measure drops.
    have hxV' : x ∈ V(Kc.union (H.pathGraphOf a D)) := by
      rw [vertexSet_union, pathGraphOf_vertexSet]
      exact Or.inr hxD
    have hsub : V(H) \ V(Kc.union (H.pathGraphOf a D)) ⊆ (V(H) \ V(Kc)) \ {x} := by
      rintro y ⟨hyH, hyK⟩
      refine ⟨⟨hyH, fun hy => hyK ?_⟩, ?_⟩
      · rw [vertexSet_union]; exact Or.inl hy
      · simp only [mem_singleton_iff]
        rintro rfl
        exact hyK hxV'
    have hcard' : (V(H) \ V(Kc.union (H.pathGraphOf a D))).ncard ≤ n := by
      have h1 : ((V(H) \ V(Kc)) \ {x}).ncard < (V(H) \ V(Kc)).ncard :=
        Set.ncard_sdiff_singleton_lt_of_mem ⟨hxH, hxKc⟩ hfin.sdiff
      have h2 : (V(H) \ V(Kc.union (H.pathGraphOf a D))).ncard ≤
          ((V(H) \ V(Kc)) \ {x}).ncard :=
        Set.ncard_le_ncard hsub hfin.sdiff.sdiff
      omega
    refine ih _ hcard' hK' hK'le fun y hy => ?_
    rw [vertexSet_union]
    exact Or.inl (hKKc hy)

end Graph

namespace Schoenflies

open CellStructure Graph

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-! ### Simple chains

A polygonal chain that never returns to territory it has covered. This is strictly stronger
than its carrier being an arc — the chain `[a, b, a, b]` carries the arc `segment a b` — and
it is the exact invariant the overlay path machinery needs: each segment hands the walk over
to the rest of the chain at the junction vertex and nowhere else. -/

/-- A chain whose consecutive vertices are distinct and each of whose segments meets the rest
of the chain only in the junction vertex. -/
def IsSimpleChain : List Plane → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => u ≠ v ∧ (∀ x ∈ segment ℝ u v, x ∈ poly (v :: rest) → x = v) ∧
      IsSimpleChain (v :: rest)

@[simp] theorem isSimpleChain_nil : IsSimpleChain [] := trivial

@[simp] theorem isSimpleChain_singleton (v : Plane) : IsSimpleChain [v] := trivial

theorem isSimpleChain_cons_cons {u v : Plane} {rest : List Plane} :
    IsSimpleChain (u :: v :: rest) ↔
      u ≠ v ∧ (∀ x ∈ segment ℝ u v, x ∈ poly (v :: rest) → x = v) ∧
        IsSimpleChain (v :: rest) := Iff.rfl

variable {pieces : List Piece} {points : List Plane}

/-- An end of an edge of an overlay walk is covered by the walk. -/
theorem end_mem_coveredVertices {W : List Piece} {f : Piece} (hf : f ∈ W)
    (hfE : f ∈ overlayPieces pieces points) {x : Plane} (hx : x = f.1 ∨ x = f.2) :
    x ∈ (overlayGraph pieces points).coveredVertices W :=
  ⟨f, hf, overlayGraph_inc hfE hx⟩

/-- A point of an overlay edge that is a cut point is an end of that edge. -/
theorem end_of_mem_points {f : Piece} (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hfE : f ∈ overlayPieces pieces points) {x : Plane} (hx : x ∈ f.seg) (hxp : x ∈ points) :
    x = f.1 ∨ x = f.2 := by
  by_contra hcon
  push Not at hcon
  exact overlayPieces_avoids hnd x hxp f hfE
    (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hx)

/-- **The vertex chain of an overlay path is a simple chain.** This strengthens
`Schoenflies.exists_poly_eq_edgesCover`: the chain read off a *path* of the overlay not only
carries the path's edges, it never returns to covered territory — a segment of it can meet a
later segment only if the two overlay edges meet, which the drawing conditions confine to the
junction vertex. -/
theorem exists_simpleChain_of_isPath (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    {a b : Plane} {W : List Piece}
    (hpath : (overlayGraph pieces points).IsPath a W b) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = a ∧ vs.getLast h = b ∧
      IsSimpleChain vs ∧ poly vs = Graph.edgesCover segmentDrawing W := by
  induction hpath with
  | nil => exact absurd rfl hne
  | @cons u w v e W' hl hW hfresh ih =>
    -- The step's segment, in whichever order the edge names its ends.
    have heE : e ∈ overlayPieces pieces points := hl.edge_mem
    have hseg : segment ℝ u w = e.seg := by
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact segment_symm ℝ _ _
    have hedge : Graph.edgeArc segmentDrawing e = segment ℝ u w := by
      rw [edgeArc_segmentDrawing, hseg]
    have huend : u = e.1 ∨ u = e.2 := by
      rcases (overlayGraph_isLink.1 hl).2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [Or.inl rfl, Or.inr rfl]
    have hwend : w = e.1 ∨ w = e.2 := by
      rcases (overlayGraph_isLink.1 hl).2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
      exacts [Or.inr rfl, Or.inl rfl]
    -- The junction segment meets whatever a later edge carries only at the junction.
    have hmeet : ∀ {f : Piece}, f ∈ W' → ∀ {x}, x ∈ segment ℝ u w → x ∈ f.seg → x = w := by
      intro f hfW x hx1 hxf
      have hfE : f ∈ overlayPieces pieces points := hW.isWalk.edgeSet_subset f hfW
      have hef : e ≠ f := by
        rintro rfl
        exact hfresh (mem_walkVertices_of_mem_covered
          (end_mem_coveredVertices hfW hfE huend))
      have hx_e : x ∈ e.seg := hseg ▸ hx1
      by_cases hxend : x = e.1 ∨ x = e.2
      · -- An end of the step's edge is `u` or `w`; `u` would violate freshness.
        have hxuw : x = u ∨ x = w := by
          rcases (overlayGraph_isLink.1 hl).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
              rcases hxend with rfl | rfl
          · exact Or.inl h1.symm
          · exact Or.inr h2.symm
          · exact Or.inr h2.symm
          · exact Or.inl h1.symm
        rcases hxuw with rfl | rfl
        · -- `x = u`: a cut point on `f`, hence an end of `f`, hence covered — fresh no more.
          have hxp : x ∈ points := overlayPieces_ends_cut hEnds e heE x hxend
          exact absurd (mem_walkVertices_of_mem_covered (end_mem_coveredVertices hfW hfE
            (end_of_mem_points hnd hfE hxf hxp))) hfresh
        · rfl
      · push Not at hxend
        have hxint : x ∈ e.interior :=
          mem_openSegment_of_ne_left_right (Ne.symm hxend.1) (Ne.symm hxend.2) hx_e
        by_cases hfend : x = f.1 ∨ x = f.2
        · -- An end of `f` is a cut point, so it is interior to no edge — not to `e` either.
          have hxp : x ∈ points := overlayPieces_ends_cut hEnds f hfE x hfend
          exact absurd hxint (overlayPieces_avoids hnd x hxp e heE)
        · push Not at hfend
          have hxintf : x ∈ f.interior :=
            mem_openSegment_of_ne_left_right (Ne.symm hfend.1) (Ne.symm hfend.2) hxf
          exact absurd hxintf
            (overlayPieces_disjoint_interiors hnd hEnds hMeets heE hfE hef hxint)
    have huw : u ≠ w := by
      rintro rfl
      have : e.1 ≠ e.2 := overlayPieces_nondeg points hnd e heE
      rcases (overlayGraph_isLink.1 hl).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact this (h1 ▸ h2 ▸ rfl)
    rcases eq_or_ne W' [] with rfl | hWne
    · -- One step: the chain is the two ends.
      have hwv : w = v := hW.isWalk.eq_of_nil
      subst hwv
      refine ⟨[u, w], by simp, rfl, by simp, ?_, ?_⟩
      · exact ⟨huw, fun x _ hx => by simpa using hx, trivial⟩
      · rw [poly_pair, Graph.edgesCover_cons, Graph.edgesCover_nil, union_empty, hedge]
    · obtain ⟨vs, hvs, hhead, hlast, hSC, hpoly⟩ := ih hWne
      obtain ⟨v', rest, rfl⟩ := List.exists_cons_of_ne_nil hvs
      have hv'w : v' = w := hhead
      -- `subst` eliminates `w`; the junction vertex is called `v'` from here on.
      subst hv'w
      refine ⟨u :: v' :: rest, by simp, rfl, ?_, ?_, ?_⟩
      · rw [List.getLast_cons hvs]; exact hlast
      · refine ⟨huw, fun x hx1 hx2 => ?_, hSC⟩
        -- The rest of the chain carries exactly the rest of the path's edges.
        rw [hpoly] at hx2
        obtain ⟨f, hfW, hxf⟩ := Graph.mem_edgesCover_iff.1 hx2
        rw [edgeArc_segmentDrawing] at hxf
        exact hmeet hfW hx1 hxf
      · rw [poly_cons_cons, hpoly, Graph.edgesCover_cons, hedge]

/-- **A simple chain from any open-square point to the base point, inside the open square.**
This is `Schoenflies.exists_simple_poly_of_isPreconnected` strengthened from "the carrier is
an arc" to "the chain is simple", which is what the overlay path machinery consumes. -/
theorem exists_simpleChain_to_base {r : Plane} {ε : ℝ} (hr : r ∈ Plane.openSquare 0 1)
    (hrb : r ≠ meshBase ε) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = r ∧ vs.getLast h = meshBase ε ∧
      IsSimpleChain vs ∧ poly vs ⊆ Plane.openSquare 0 1 := by
  classical
  obtain ⟨us, hus, husub, huhead, hulast⟩ := exists_poly_of_isPreconnected
    (Plane.isOpen_openSquare 0 1) (Plane.convex_openSquare 0 1).isPreconnected hr
    (meshBase_mem_openSquare ε)
  have hnd : ∀ P ∈ segsOf us, P.Nondeg := segsOf_nondeg us
  have hrmem : r ∈ poly us := huhead ▸ head_mem_poly hus
  have hbmem : meshBase ε ∈ poly us := hulast ▸ getLast_mem_poly hus
  have hcov : cover (segsOf us) = poly us := cover_segsOf_eq hrmem hbmem hrb
  -- Put the two endpoints on the cut list, so that they are vertices of the overlay.
  obtain ⟨pts₀, hEnds₀, hMeets₀⟩ := exists_cut_points (segsOf us)
  set pts : List Plane := r :: meshBase ε :: pts₀ with hpts
  have hEnds : EndsAreCut (segsOf us) pts := fun P hP z hz => by
    simp [hpts, hEnds₀ P hP z hz]
  have hMeets : MeetsAreCut (segsOf us) pts := by
    intro P hP Q hQ hPQ hne
    obtain ⟨p, q, hpq, hp, hq⟩ := hMeets₀ P hP Q hQ hPQ hne
    exact ⟨p, q, hpq, by simp [hpts, hp], by simp [hpts, hq]⟩
  have hreach : (overlayGraph (segsOf us) pts).Reaches r (meshBase ε) :=
    overlayGraph_reaches hnd (hcov ▸ (isConnected_poly hus).isPreconnected)
      hEnds hMeets (by simp [hpts]) (by simp [hpts]) (hcov ▸ hrmem) (hcov ▸ hbmem)
  obtain ⟨W, hpath⟩ := hreach.exists_isPath
  have hWne : W ≠ [] := by
    rintro rfl
    exact hrb hpath.isWalk.eq_of_nil
  obtain ⟨vs, hvs, hh, hl, hSC, hpoly⟩ :=
    exists_simpleChain_of_isPath hnd hEnds hMeets hpath hWne
  refine ⟨vs, hvs, hh, hl, hSC, ?_⟩
  rw [hpoly]
  refine (Graph.edgesCover_subset_pointSet fun e he => hpath.edge_mem he).trans ?_
  rw [overlayGraph_pointSet, hcov]
  exact husub

end Schoenflies
