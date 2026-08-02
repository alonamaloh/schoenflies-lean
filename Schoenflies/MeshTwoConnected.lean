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

end Schoenflies
