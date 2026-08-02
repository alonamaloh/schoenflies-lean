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
* `modelCurve_subset_cover_skelPieces`, `HasTwoConnectedMeshCores`,
  `HasTwoConnectedSkelCores`, `hasTwoConnectedCores_of` — `lem:union-two-connected` as the
  glue: the core splits into one obligation per side, shared along the fresh points.
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

/-! ### A simple chain subdivides to a path of the overlay

`Schoenflies.SubdividesToPath` — a theorem, by `Schoenflies.subdividesToPath_of_overlay` —
turns each segment of the chain into a path of the overlay between its two ends. The chain
being simple is exactly what lets the segments' paths concatenate: each hands over at the
junction vertex and meets the rest of the chain nowhere else. -/

/-- The two ends of a chain with at least one segment are ends of listed segments. This is
what makes them cut points of any overlay whose source list contains the chain's segments. -/
theorem ends_of_segsOf : ∀ (vs : List Plane) (h : vs ≠ []), IsSimpleChain vs →
    vs.head h ≠ vs.getLast h →
    (∃ Q ∈ segsOf vs, vs.head h = Q.1) ∧ ∃ Q ∈ segsOf vs, vs.getLast h = Q.2 := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    intro h hSC hne
    cases tl with
    | nil => simp at hne
    | cons v rest =>
      obtain ⟨huv, -, hSC'⟩ := hSC
      rw [segsOf_cons_cons, if_neg huv]
      have hlast : (u :: v :: rest).getLast h = (v :: rest).getLast (by simp) :=
        List.getLast_cons (by simp)
      refine ⟨⟨(u, v), List.mem_cons_self .., rfl⟩, ?_⟩
      by_cases hveq : v = (v :: rest).getLast (by simp)
      · exact ⟨(u, v), List.mem_cons_self .., by rw [hlast, ← hveq]⟩
      · obtain ⟨-, Q, hQ, hQ2⟩ := ih (by simp) hSC' hveq
        exact ⟨Q, List.mem_cons_of_mem _ hQ, by rw [hlast]; exact hQ2⟩

/-- **A simple chain of source segments subdivides to a path of the overlay.** The path runs
from the chain's head to its last vertex, its edges stay on the chain, and it visits every
overlay vertex lying on the chain. -/
theorem simpleChain_isPath_overlay (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points) :
    ∀ (vs : List Plane) (hvs : vs ≠ []), IsSimpleChain vs →
      (∀ Q ∈ segsOf vs, Q ∈ pieces) →
      vs.getLast hvs ∈ V(overlayGraph pieces points) →
      ∃ W : List Piece,
        (overlayGraph pieces points).IsPath (vs.head hvs) W (vs.getLast hvs) ∧
        (∀ Q ∈ W, Q.seg ⊆ poly vs) ∧
        ∀ x ∈ V(overlayGraph pieces points), x ∈ poly vs →
          x ∈ (overlayGraph pieces points).walkVertices (vs.head hvs) W := by
  intro vs
  induction vs with
  | nil => exact fun h => absurd rfl h
  | cons u tl ih =>
    intro hvs hSC hsub hlastV
    cases tl with
    | nil =>
      refine ⟨[], .nil (by simpa using hlastV), by simp, ?_⟩
      intro x _ hx2
      rw [poly_singleton, Set.mem_singleton_iff] at hx2
      subst hx2
      exact Graph.mem_walkVertices_self
    | cons v rest =>
      obtain ⟨huv, hmeet, hSC'⟩ := hSC
      have hlist : (u, v) :: segsOf (v :: rest) = segsOf (u :: v :: rest) := by
        rw [segsOf_cons_cons, if_neg huv]
      have hQmem : (u, v) ∈ pieces := hsub _ (hlist ▸ List.mem_cons_self ..)
      have hsub' : ∀ Q ∈ segsOf (v :: rest), Q ∈ pieces := fun Q hQ =>
        hsub Q (hlist ▸ List.mem_cons_of_mem _ hQ)
      have hlast : (u :: v :: rest).getLast hvs = (v :: rest).getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hlast] at hlastV
      -- The segment's own subdivision path, and the rest of the chain's by induction.
      obtain ⟨W₁, hW₁path, hW₁mem⟩ :=
        subdividesToPath_of_overlay hnd hEnds hMeets (u, v) hQmem huv
      obtain ⟨W₂, hW₂path, hW₂sub, hW₂cov⟩ := ih (by simp) hSC' hsub' hlastV
      have hW₁seg : ∀ Q ∈ W₁, Q.seg ⊆ segment ℝ u v := fun Q hQ => ((hW₁mem Q).1 hQ).2
      have hverts₁ : ∀ x ∈ (overlayGraph pieces points).walkVertices u W₁,
          x ∈ segment ℝ u v := fun x hx =>
        walkVertices_subset_of_edges (left_mem_segment ℝ u v) hW₁seg hx
      have hverts₂ : ∀ x ∈ (overlayGraph pieces points).walkVertices v W₂,
          x ∈ poly (v :: rest) := fun x hx =>
        walkVertices_subset_of_edges (mem_poly_of_mem (List.mem_cons_self ..)) hW₂sub hx
      -- The two paths meet only at the junction, so they concatenate to a path.
      have hpath : (overlayGraph pieces points).IsPath u (W₁ ++ W₂)
          ((v :: rest).getLast (by simp)) :=
        hW₁path.append_of_disjoint hW₂path fun x hx1 hx2 =>
          hmeet x (hverts₁ x hx1) (hverts₂ x hx2)
      refine ⟨W₁ ++ W₂, by rw [List.head_cons, hlast]; exact hpath, ?_, ?_⟩
      · intro Q hQ
        rw [poly_cons_cons]
        rcases List.mem_append.1 hQ with hQ | hQ
        · exact (hW₁seg Q hQ).trans subset_union_left
        · exact (hW₂sub Q hQ).trans subset_union_right
      · intro x hxV hxpoly
        rw [List.head_cons]
        rw [poly_cons_cons] at hxpoly
        have hleft : (overlayGraph pieces points).walkVertices u W₁ ⊆
            (overlayGraph pieces points).walkVertices u (W₁ ++ W₂) := by
          intro y hy
          rcases Graph.mem_walkVertices_iff.1 hy with rfl | hcov
          · exact Graph.mem_walkVertices_self
          · exact Graph.mem_walkVertices_of_mem_covered
              (Graph.coveredVertices_mono (List.subset_append_left _ _) hcov)
        rcases hxpoly with hx | hx
        · -- On the segment: the vertex is a cut point, hence an end of the covering edge.
          have hxpts : x ∈ points := by
            obtain ⟨eP, heP, hend⟩ := hxV
            exact overlayPieces_ends_cut hEnds eP heP x hend
          have hx' : x ∈ Graph.edgesCover segmentDrawing W₁ := by
            rw [edgesCover_eq_seg hQmem hW₁mem]
            exact hx
          obtain ⟨f, hfW, hxf⟩ := Graph.mem_edgesCover_iff.1 hx'
          rw [edgeArc_segmentDrawing] at hxf
          have hfE : f ∈ overlayPieces pieces points := ((hW₁mem f).1 hfW).1
          exact hleft (Graph.mem_walkVertices_of_mem_covered
            (end_mem_coveredVertices hfW hfE (end_of_mem_points hnd hfE hxf hxpts)))
        · -- On the rest of the chain: covered by induction, lifted along the append.
          have hx2 := hW₂cov x hxV hx
          rcases Graph.mem_walkVertices_iff.1 hx2 with rfl | hcov
          · exact hleft hW₁path.isWalk.target_mem_walkVertices
          · exact Graph.mem_walkVertices_of_mem_covered
              (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)

/-! ### The joining arcs, chosen simple

`Schoenflies.exists_joinsFor` produces joining chains that may double back; here each
representative of the nonboundary skeleton is joined to the base point by a *simple* chain,
and `Schoenflies.JoinsFor` is re-established for the collection. The chains are also exported,
because the main theorem needs to walk along them. -/

variable {P : StagePair S₀ C}

/-- **Simple joining arcs exist.** A list of simple chains, one from a representative of each
component of the nonboundary skeleton off `S` to the mesh base point, whose segments satisfy
`Schoenflies.JoinsFor`. -/
theorem exists_simple_joins (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1))
    (ε : ℝ) :
    ∃ (VS : List (List Plane)) (joins : List Piece), joins = VS.flatMap segsOf ∧
      JoinsFor P ε joins ∧
      (∀ vs ∈ VS, ∃ h : vs ≠ [], IsSimpleChain vs ∧ vs.getLast h = meshBase ε ∧
        vs.head h ≠ meshBase ε ∧ vs.head h ∈ cover (skelNbPieces P) ∧
        poly vs ⊆ Plane.openSquare 0 1) ∧
      cover joins = ⋃ vs ∈ VS, poly vs := by
  obtain ⟨reps, hrmem, hrcov⟩ :=
    exists_reps_cover_diff (skelNbPieces P) (skelNbPieces_meetsFinitely htgt)
  -- every representative sits in the open square
  have hrepΩ : ∀ r ∈ reps, r ∈ Plane.openSquare 0 1 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hrmem r hr
    obtain ⟨Q, hQ, hrQ⟩ := mem_cover_iff.1 hr1
    obtain ⟨e, ⟨he, -⟩, hQe⟩ := mem_skelNbPieces.1 hQ
    have hsq : r ∈ Plane.closedSquare 0 1 := htgt.skeletonSet_subset
      (arc_subset_skeletonSet P he (seg_subset_edgeArc P he hQe hrQ))
    exact mem_openSquare_zero_one.2
      (lt_of_le_of_ne (mem_closedSquare_zero_one.1 hsq) fun h => hr2 h)
  -- one simple chain per representative other than the base point itself
  have key : ∀ rs : List Plane, (∀ r ∈ rs, r ∈ cover (skelNbPieces P) ∧
      r ∈ Plane.openSquare 0 1) →
      ∃ VS : List (List Plane),
        (∀ vs ∈ VS, ∃ h : vs ≠ [], IsSimpleChain vs ∧ vs.getLast h = meshBase ε ∧
          vs.head h ≠ meshBase ε ∧ vs.head h ∈ cover (skelNbPieces P) ∧
          poly vs ⊆ Plane.openSquare 0 1) ∧
        ∀ r ∈ rs, r = meshBase ε ∨ ∃ vs ∈ VS, ∃ h : vs ≠ [], vs.head h = r := by
    intro rs
    induction rs with
    | nil => exact fun _ => ⟨[], by simp, by simp⟩
    | cons r rs ih =>
      intro hmem
      obtain ⟨VS, hVS, hcov⟩ := ih fun w hw => hmem w (List.mem_cons_of_mem _ hw)
      by_cases hrb : r = meshBase ε
      · refine ⟨VS, hVS, fun w hw => ?_⟩
        rcases List.mem_cons.1 hw with rfl | hw
        exacts [Or.inl hrb, hcov w hw]
      · obtain ⟨vs, hvs, hh, hl, hSC, hΩ⟩ :=
          exists_simpleChain_to_base (hmem r List.mem_cons_self).2 hrb
        refine ⟨vs :: VS, ?_, ?_⟩
        · intro ws hws
          rcases List.mem_cons.1 hws with rfl | hws
          · exact ⟨hvs, hSC, hl, by rw [hh]; exact hrb,
              hh ▸ (hmem r List.mem_cons_self).1, hΩ⟩
          · exact hVS ws hws
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact Or.inr ⟨vs, List.mem_cons_self .., hvs, hh⟩
          · rcases hcov w hw with h | ⟨ws, hws, h⟩
            exacts [Or.inl h, Or.inr ⟨ws, List.mem_cons_of_mem _ hws, h⟩]
  obtain ⟨VS, hVS, hcov⟩ := key reps fun r hr => ⟨(hrmem r hr).1, hrepΩ r hr⟩
  -- each chain's segments occupy exactly its carrier
  have hpolyeq : ∀ vs ∈ VS, cover (segsOf vs) = poly vs := by
    intro vs hvs
    obtain ⟨h, -, hl, hne, -, -⟩ := hVS vs hvs
    exact cover_segsOf_eq (head_mem_poly h) (getLast_mem_poly h) (by rw [hl]; exact hne)
  have hjcov : cover (VS.flatMap segsOf) = ⋃ vs ∈ VS, poly vs := by
    rw [cover_flatMap_list]
    ext x
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨vs, hvs, hx⟩
      exact ⟨vs, hvs, by rw [← hpolyeq vs hvs]; exact hx⟩
    · rintro ⟨vs, hvs, hx⟩
      exact ⟨vs, hvs, by rw [hpolyeq vs hvs]; exact hx⟩
  have hΩall : (⋃ vs ∈ VS, poly vs) ⊆ Plane.openSquare 0 1 := by
    intro x hx
    obtain ⟨vs, hvs, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨-, -, -, -, -, hΩ⟩ := hVS vs hvs
    exact hΩ hx
  have hjS : ∀ w ∈ (⋃ vs ∈ VS, poly vs), w ∉ modelCurve := fun w hw =>
    (openSquare_subset_closedSquare_diff (hΩall hw)).2
  have hbS : meshBase ε ∉ modelCurve := meshBase_notMem_modelCurve ε
  refine ⟨VS, VS.flatMap segsOf, rfl, ⟨?_, ?_, ?_⟩, hVS, hjcov⟩
  · -- nondegeneracy
    intro Q hQ
    obtain ⟨vs, -, hQvs⟩ := List.mem_flatMap.1 hQ
    exact segsOf_nondeg vs Q hQvs
  · rw [hjcov]
    exact hΩall
  · -- the connectivity clause of `JoinsFor`
    rintro x ⟨hx, hxS⟩
    rcases hx with hx | hx
    · -- on the nonboundary skeleton: representative first, then its chain
      obtain ⟨r, hr, A₀, hA₀sub, hA₀conn, hxA₀, hrA₀⟩ := hrcov x ⟨hx, hxS⟩
      rcases hcov r hr with hrb | ⟨vs, hvs, hne, hhead⟩
      · -- the representative is the base point itself
        refine ⟨A₀ ∪ {meshBase ε}, ?_,
          IsPreconnected.union (meshBase ε) (hrb ▸ hrA₀) rfl hA₀conn
            isPreconnected_singleton, Or.inl hxA₀, Or.inr rfl⟩
        rintro w (hw | hw)
        · obtain ⟨hw1, hw2⟩ := hA₀sub hw
          exact ⟨Or.inl (Or.inl hw1), hw2⟩
        · rw [mem_singleton_iff] at hw
          subst hw
          exact ⟨Or.inr rfl, hbS⟩
      · -- down the chain to the base point
        obtain ⟨hne', -, hlast, -, -, -⟩ := hVS vs hvs
        refine ⟨A₀ ∪ poly vs, ?_,
          IsPreconnected.union r hrA₀ (hhead ▸ head_mem_poly hne) hA₀conn
            (isConnected_poly hne).isPreconnected, Or.inl hxA₀,
          Or.inr (hlast ▸ getLast_mem_poly hne')⟩
        rintro w (hw | hw)
        · obtain ⟨hw1, hw2⟩ := hA₀sub hw
          exact ⟨Or.inl (Or.inl hw1), hw2⟩
        · refine ⟨Or.inl (Or.inr ?_), hjS w (mem_iUnion₂.2 ⟨vs, hvs, hw⟩)⟩
          rw [hjcov]
          exact mem_iUnion₂.2 ⟨vs, hvs, hw⟩
    · -- on a joining arc: its own chain reaches the base point
      rw [hjcov] at hx
      obtain ⟨vs, hvs, hxvs⟩ := mem_iUnion₂.1 hx
      obtain ⟨hne, -, hlast, -, -, -⟩ := hVS vs hvs
      refine ⟨poly vs, ?_, (isConnected_poly hne).isPreconnected, hxvs,
        hlast ▸ getLast_mem_poly hne⟩
      intro w hw
      refine ⟨Or.inl (Or.inr ?_), hjS w (mem_iUnion₂.2 ⟨vs, hvs, hw⟩)⟩
      rw [hjcov]
      exact mem_iUnion₂.2 ⟨vs, hvs, hw⟩

/-! ### The named hypothesis, and the reduction -/

/-- **NAMED HYPOTHESIS — the mesh-and-skeleton core of the overlay.** At every admissible
stage, mesh size, valid fresh list with two distinct points, and `JoinsFor` list of joining
arcs, the overlay has a 2-connected subgraph containing every overlay vertex that lies on the
mesh or on the old drawn skeleton.

The intended discharger is the subdivision bridge of the blueprint's `lem:polygonal-overlay`:

* the overlay restricted to the edges inside the mesh pieces refines
  `Schoenflies.squareMesh ε fresh anchors` by finitely many extra cut points — each one a
  single-edge subdivision (`Graph.IsSubdivisionOf`, or `Graph.IsTwoConnected.replace_edge_by_path`
  edge by edge) — and `Schoenflies.meshGraph_isTwoConnected` makes the mesh 2-connected from
  exactly the two distinct fresh points supplied here;
* the overlay restricted to the edges inside the old skeleton is a subdivision of `Γ'`,
  2-connected by admissibility (`IsWeaklyAdmissible.isTwoConnected`); this crossing of edge
  name types (`γ` to `Schoenflies.Piece`) is the genuinely new content;
* the two share the four corners of the outer ring — vertices of both, since the outer 1-cells
  of the stage occupy `S` (`IsAdmissible.outerSet_eq`) and the outer ring does too — so
  `Graph.IsTwoConnected.union` glues them, and the union contains every overlay vertex on
  mesh or skeleton.

The quantifier over `joins` is universal because the core does not depend on which joining
arcs are drawn: they only refine the subdivision further. -/
def HasTwoConnectedCores (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃fresh : List Plane⦄,
      (∀ z ∈ fresh, z ∈ modelCurve ∧ z ∉ V(P.tgt.graph)) →
      (∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w) →
      ∀ ⦃joins : List Piece⦄, JoinsFor P ε joins →
      ∃ K : Graph Plane Piece, K ≤ meshOverlayGraph P ε fresh joins ∧ K.IsTwoConnected ∧
        ∀ x ∈ V(meshOverlayGraph P ε fresh joins),
          x ∈ cover (meshSegments (meshCount ε) fresh) ∪ cover (skelPieces P) → x ∈ V(K)

/-- **The reduction: a 2-connected mesh-and-skeleton core makes the whole overlay
2-connected.** The joining arcs are chosen simple (`Schoenflies.exists_simple_joins`), each
chain subdivides to a path of the overlay between a skeleton vertex and the mesh base point —
two distinct vertices of the core — and `Graph.IsTwoConnected.of_spanning_paths` absorbs the
chains one ear at a time. -/
theorem hasTwoConnectedMeshOverlays_of (hcore : HasTwoConnectedCores S₀ C) :
    HasTwoConnectedMeshOverlays S₀ C := by
  intro P hsrc htgt ε hε fresh hfresh hne2
  obtain ⟨VS, joins, hjdef, hjoins, hchains, hjcov⟩ := exists_simple_joins htgt ε
  refine ⟨joins, hjoins, ?_⟩
  obtain ⟨K, hKle, hK2, hKcov⟩ := hcore P hsrc htgt hε hfresh hne2 hjoins
  have hfresh' : ∀ z ∈ fresh, z ∈ modelCurve := fun z hz => (hfresh z hz).1
  have hnd := meshOverlayPieces_nondeg (P := P) (ε := ε) hfresh' hjoins.nondeg
  have hEnds := meshOverlayPoints_endsAreCut P ε fresh joins
  have hMeets := meshOverlayPoints_meetsAreCut P ε fresh joins
  have hfin : V(meshOverlayGraph P ε fresh joins).Finite :=
    (meshOverlayGraph_finite P ε fresh joins).finite_vertexSet
  refine hK2.of_spanning_paths hfin hKle
    (T := {x ∈ V(meshOverlayGraph P ε fresh joins) |
      x ∈ cover (meshSegments (meshCount ε) fresh) ∪ cover (skelPieces P)})
    (fun x hx => hKcov x hx.1 hx.2) ?_
  intro x hxH hxK
  -- a vertex outside the core lies on a joining chain
  have hxjoin : x ∈ cover joins := by
    obtain ⟨e, heE, hend⟩ := id hxH
    have hxe : x ∈ e.seg := by
      rcases hend with rfl | rfl
      exacts [left_mem_segment ℝ _ _, right_mem_segment ℝ _ _]
    obtain ⟨R, hR, hsubR, -⟩ := meshOverlayGraph_edge_source (P := P) (ε := ε) heE
    rcases List.mem_append.1 hR with hmesh | hrest
    · exact absurd (hKcov x hxH (Or.inl (mem_cover_iff.2 ⟨R, hmesh, hsubR hxe⟩))) hxK
    rcases List.mem_append.1 hrest with hskel | hjoin
    · exact absurd (hKcov x hxH (Or.inr (mem_cover_iff.2 ⟨R, hskel, hsubR hxe⟩))) hxK
    · exact mem_cover_iff.2 ⟨R, hjoin, hsubR hxe⟩
  rw [hjcov] at hxjoin
  obtain ⟨vs, hvsVS, hxvs⟩ := mem_iUnion₂.1 hxjoin
  obtain ⟨hne, hSC, hlast, hheadne, hheadskel, -⟩ := hchains vs hvsVS
  have hsegsub : ∀ Q ∈ segsOf vs, Q ∈ meshOverlayPieces P ε fresh joins := by
    intro Q hQ
    refine List.mem_append_right _ (List.mem_append_right _ ?_)
    rw [hjdef]
    exact List.mem_flatMap.2 ⟨vs, hvsVS, hQ⟩
  -- the chain's two ends are cut points, hence vertices, and both lie on the core
  have hheadlast : vs.head hne ≠ vs.getLast hne := by rw [hlast]; exact hheadne
  obtain ⟨⟨Qh, hQh, hQh1⟩, Ql, hQl, hQl2⟩ := ends_of_segsOf vs hne hSC hheadlast
  have hheadpts : vs.head hne ∈ meshOverlayPoints P ε fresh joins :=
    hEnds Qh (hsegsub Qh hQh) _ (Or.inl hQh1)
  have hlastpts : vs.getLast hne ∈ meshOverlayPoints P ε fresh joins :=
    hEnds Ql (hsegsub Ql hQl) _ (Or.inr hQl2)
  obtain ⟨Rh, hRh, hheadRh⟩ := mem_cover_iff.1 hheadskel
  have hheadV : vs.head hne ∈ V(meshOverlayGraph P ε fresh joins) :=
    overlay_mem_vertexSet_of_cut hheadpts
      (List.mem_append_right _ (List.mem_append_left _ (skelNbPieces_subset P hRh))) hheadRh
  obtain ⟨Rm, hRm, hbRm⟩ := mem_cover_iff.1 (meshBase_mem_cover_meshSegments ε fresh)
  have hlastRm : vs.getLast hne ∈ Rm.seg := by rw [hlast]; exact hbRm
  have hlastV : vs.getLast hne ∈ V(meshOverlayGraph P ε fresh joins) :=
    overlay_mem_vertexSet_of_cut hlastpts (List.mem_append_left _ hRm) hlastRm
  -- the chain's overlay path is the ear through `x`
  obtain ⟨W, hWpath, -, hWcov⟩ :=
    simpleChain_isPath_overlay hnd hEnds hMeets vs hne hSC hsegsub hlastV
  exact ⟨vs.head hne, vs.getLast hne, W, hWpath, hheadlast,
    ⟨hheadV, Or.inr (mem_cover_iff.2 ⟨Rh, skelNbPieces_subset P hRh, hheadRh⟩)⟩,
    ⟨hlastV, Or.inl (mem_cover_iff.2 ⟨Rm, hRm, hlastRm⟩)⟩, hWcov x hxH hxvs⟩

/-- `Schoenflies.HasMeshSteps` from the core hypothesis alone: the whole mesh-transfer chain
composes through `Schoenflies.hasMeshOverlays_of`, `Schoenflies.hasMeshTransfers` and
`Schoenflies.hasMeshSteps`. -/
theorem hasMeshSteps_of_cores {γ : Type*} [Infinite γ] {S₀ : CellStructure γ} {C : Set Plane}
    (h₀ : S₀.CombInvariants) (hsep : IsSeparating C)
    (hcore : HasTwoConnectedCores S₀ C) : HasMeshSteps S₀ C :=
  hasMeshSteps (hasMeshTransfers h₀ hsep
    (hasMeshOverlays_of (hasTwoConnectedMeshOverlays_of hcore)))

/-- The interface, exercised: over the concrete base, the stage sequence of Phase 3 now rests
on the source-grid chooser and the core hypothesis. -/
example {C : Set Plane} (hC : IsJordanCurve C) (hg : HasGridSteps initialStructure C)
    (hcore : HasTwoConnectedCores initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC hg
    (hasMeshSteps_of_cores combInvariants_initialStructure (jordan_curve_theorem hC) hcore)⟩

/-! ### Splitting the core into its two sides

`Schoenflies.HasTwoConnectedCores` glues out of one 2-connected subgraph per side — one
spanning the overlay vertices on the mesh, one spanning those on the old skeleton — because
the two sides share every fresh point: a fresh point is a vertex of the overlay, an end of
its own spoke on the mesh, and a point of `S`, which the old skeleton occupies through its
outer 1-cells. The glue is `Graph.IsTwoConnected.union` on two distinct fresh points, which
the mesh-transfer caller always supplies. With it, the discharger of the core can treat the
two subdivision bridges as independent obligations. -/

/-- `S` lies on the pieces of the old skeleton: it is the realized outer cycle, whose drawn
0-cells lie on drawn 1-cell arcs and whose 1-cell arcs are skeleton arcs. -/
theorem modelCurve_subset_cover_skelPieces
    (htgt : P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1)) :
    modelCurve ⊆ cover (skelPieces P) := by
  rw [← htgt.outerSet_eq]
  intro x hx
  rw [cover_skelPieces]
  simp only [CellStructure.Realization.outerSet, Graph.pointSet, Set.mem_union, mem_iUnion,
    exists_prop] at hx
  rcases hx with hx | ⟨e, he, hxe⟩
  · -- a drawn 0-cell of the outer cycle lies on the drawn arc of one of its 1-cells
    rw [vertexSet_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨e, he, hmem⟩ :=
      pos_mem_edgeArc_of_vertex htgt (P.str.outerGraph_le.vertexSet_mono hv)
    exact mem_iUnion₂.2 ⟨e, he, hmem⟩
  · -- an outer 1-cell is a 1-cell
    rw [edgeSet_map] at he
    exact mem_iUnion₂.2 ⟨e, P.str.outerGraph_le.edgeSet_mono he, hxe⟩

/-- **NAMED HYPOTHESIS — the mesh side of the core**: a 2-connected subgraph of the overlay
containing every overlay vertex on the mesh. Its discharger is the refinement bridge: the
overlay edges inside the mesh pieces subdivide `Schoenflies.squareMesh` — same edge name type,
finitely many extra cut points, each interior to at most one edge, so
`Graph.IsSubdivisionOf.isTwoConnected` (or `Graph.IsTwoConnected.replace_edge_by_path`)
applies one point at a time — and `Schoenflies.meshGraph_isTwoConnected` starts it off from
the two distinct fresh points supplied here. -/
def HasTwoConnectedMeshCores (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃fresh : List Plane⦄,
      (∀ z ∈ fresh, z ∈ modelCurve ∧ z ∉ V(P.tgt.graph)) →
      (∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w) →
      ∀ ⦃joins : List Piece⦄, JoinsFor P ε joins →
      ∃ K : Graph Plane Piece, K ≤ meshOverlayGraph P ε fresh joins ∧ K.IsTwoConnected ∧
        ∀ x ∈ V(meshOverlayGraph P ε fresh joins),
          x ∈ cover (meshSegments (meshCount ε) fresh) → x ∈ V(K)

/-- **NAMED HYPOTHESIS — the skeleton side of the core**: a 2-connected subgraph of the
overlay containing every overlay vertex on the old drawn skeleton. Its discharger is the
cross-type subdivision bridge — the overlay edges inside the drawn 1-cell arcs form a
subdivision of `Γ'` (edge names `γ` on one side, `Schoenflies.Piece` on the other), which is
2-connected by admissibility (`IsWeaklyAdmissible.isTwoConnected`); the transport needs a
subdivision-with-relabelling analogue of `Graph.IsSubdivisionOf.isTwoConnected`, with
`Graph.IsDrawing.not_isLoopAt` supplying its looplessness proviso. -/
def HasTwoConnectedSkelCores (S₀ : CellStructure γ) (C : Set Plane) : Prop :=
  ∀ P : StagePair S₀ C, P.src.IsAdmissible C (C ∪ inside C) →
    P.tgt.IsAdmissible modelCurve (Plane.closedSquare 0 1) →
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ ⦃fresh : List Plane⦄,
      (∀ z ∈ fresh, z ∈ modelCurve ∧ z ∉ V(P.tgt.graph)) →
      (∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w) →
      ∀ ⦃joins : List Piece⦄, JoinsFor P ε joins →
      ∃ K : Graph Plane Piece, K ≤ meshOverlayGraph P ε fresh joins ∧ K.IsTwoConnected ∧
        ∀ x ∈ V(meshOverlayGraph P ε fresh joins),
          x ∈ cover (skelPieces P) → x ∈ V(K)

/-- **The glue: the two per-side cores union to the joint core.** The two sides share the two
distinct fresh points — each is a vertex of the overlay, lies on its own spoke, and lies on
`S`, which the skeleton occupies — so `Graph.IsTwoConnected.union` applies. -/
theorem hasTwoConnectedCores_of (hmesh : HasTwoConnectedMeshCores S₀ C)
    (hskel : HasTwoConnectedSkelCores S₀ C) : HasTwoConnectedCores S₀ C := by
  intro P hsrc htgt ε hε fresh hfresh hne2 joins hjoins
  obtain ⟨K₁, hK₁le, hK₁2, hK₁cov⟩ := hmesh P hsrc htgt hε hfresh hne2 hjoins
  obtain ⟨K₂, hK₂le, hK₂2, hK₂cov⟩ := hskel P hsrc htgt hε hfresh hne2 hjoins
  obtain ⟨z, hz, w, hw, hzw⟩ := hne2
  -- a fresh point is a vertex, on the mesh, and on the skeleton
  have hmem : ∀ ⦃p⦄, p ∈ fresh → p ∈ V(K₁) ∧ p ∈ V(K₂) := by
    intro p hp
    have hpV : p ∈ V(meshOverlayGraph P ε fresh joins) :=
      fresh_mem_vertexSet_meshOverlayGraph hp
    have hpmesh : p ∈ cover (meshSegments (meshCount ε) fresh) :=
      mem_cover_iff.2 ⟨spokePiece (meshCount ε) p, spokePiece_mem_meshSegments hp,
        left_mem_segment ℝ _ _⟩
    have hpskel : p ∈ cover (skelPieces P) :=
      modelCurve_subset_cover_skelPieces htgt (hfresh p hp).1
    exact ⟨hK₁cov p hpV hpmesh, hK₂cov p hpV hpskel⟩
  refine ⟨K₁.union K₂, union_le hK₁le hK₂le, ?_, ?_⟩
  · exact IsTwoConnected.union (Compatible.of_le_le hK₁le hK₂le) hK₁2 hK₂2 hzw
      (hmem hz).1 (hmem hz).2 (hmem hw).1 (hmem hw).2
  · intro x hxV hx
    rw [vertexSet_union]
    rcases hx with hx | hx
    exacts [Or.inl (hK₁cov x hxV hx), Or.inr (hK₂cov x hxV hx)]

/-- The interface, exercised again: the stage sequence from the two per-side cores. -/
example {C : Set Plane} (hC : IsJordanCurve C) (hg : HasGridSteps initialStructure C)
    (hmesh : HasTwoConnectedMeshCores initialStructure C)
    (hskel : HasTwoConnectedSkelCores initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC hg
    (hasMeshSteps_of_cores combInvariants_initialStructure (jordan_curve_theorem hC)
      (hasTwoConnectedCores_of hmesh hskel))⟩

end Schoenflies
