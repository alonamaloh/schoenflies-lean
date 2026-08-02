/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshTwoConnected

/-!
# The skeleton side of the mesh-overlay core: `Schoenflies.HasTwoConnectedSkelCores`

`Schoenflies.HasTwoConnectedSkelCores` (`Schoenflies/MeshTwoConnected.lean`) asks, at every
admissible stage, mesh size, fresh list and `JoinsFor` list, for a 2-connected subgraph of the
overlay `Schoenflies.meshOverlayGraph` containing every overlay vertex on the old drawn
skeleton. This module discharges it.

The recorded obstacle was the cross-type subdivision: the drawn skeleton `Γ'` has edge names
in `γ`, the overlay in `Schoenflies.Piece`, so `Graph.IsSubdivisionOf` cannot even be stated
between them. Neither `Graph.renameEdges` nor `Graph.IsSubdivisionOf` is used here; instead
the transport is proved once, directly, in the two-type form it is needed in:
`Graph.IsTwoConnected.of_edge_paths` says that a graph `H` obtained from a 2-connected `G` by
replacing each edge by a path — same two ends, interior vertices confined to their own edge —
is 2-connected. Its proof is the blueprint's: connectivity transports walk by walk, deleting
an old vertex reduces to `G` minus that vertex, and deleting a new vertex reduces to `G` minus
the one edge whose path carries it, which `Graph.IsTwoConnected.no_bridge` keeps connected.

The per-edge paths come from the one genuinely new geometric fact: **the overlay edges lying
inside a drawn 1-cell arc chain up into a path from one drawn end to the other**, visiting
every overlay vertex on the arc (`Schoenflies.exists_arcPath_overlay`). This is the arc
analogue of `Schoenflies.exists_incWalk_insideEdges`, whose straight-segment ordering (the
distance from an end) is replaced by the parameter of the arc's own parametrization: the
parameters of an overlay edge inside the arc form a closed subinterval whose endpoints map to
the edge's two ends (`Schoenflies.exists_arc_param_Icc`), the intervals tile `[0, 1]`, and
`Graph.IsIncWalk` walks them in order.

## Blueprint

* `Graph.IsTwoConnected.of_edge_paths` — `lem:subdivision-ear-preserve`(a) iterated across
  edge-name types: replacing every edge of a 2-connected graph by an internally-disjoint path
  preserves 2-connectivity. General-purpose; a candidate for hoisting into
  `Schoenflies/Graph/` beside `Graph/Subdivision.lean`.
* `end_of_isPreconnected_diff` — a point of a segment whose removal leaves the segment
  connected is an end. (General-purpose; a candidate for hoisting into a segment module.)
* `exists_arc_param_Icc` — a nondegenerate segment inside an arc is the image of a closed
  parameter subinterval, endpoints to ends.
* `exists_arcPiece_beyond`, `exists_arcPath_overlay` — `lem:polygonal-overlay` along an arc:
  the overlay edges inside a drawn arc are a path of the overlay between the arc's two ends,
  covering every overlay vertex on the arc.
* `hasTwoConnectedSkelCores` — the discharge of `Schoenflies.HasTwoConnectedSkelCores`.
-/

open Metric Set unitInterval
open scoped Graph

namespace Graph

variable {α β β' : Type*} {G : Graph α β} {H : Graph α β'}

/-- **Replacing every edge of a 2-connected graph by a path keeps it 2-connected**, stated
across edge-name types — the subdivision-with-relabelling transport that
`Schoenflies.HasTwoConnectedSkelCores` records as its genuinely new content. `G` is
2-connected; each edge `e` of `G` is assigned a path of `H` between its two (distinct) ends;
every vertex of `H` lies on some path; a path vertex that is a `G`-vertex is one of its own
edge's ends; and two different edges' paths meet only in `G`-vertices. Then `H` is
2-connected: connectivity transports walk by walk, deleting an old vertex `z` transports
`G - z` (whose edges' paths all avoid `z`), and deleting a new vertex `z` transports
`G` minus the one edge whose path carries `z` — connected by `Graph.IsTwoConnected.no_bridge`
— while the cut path still reaches an end by `Graph.IsPath.reaches_an_end`.

Extra edges of `H` beyond the paths are tolerated: 2-connectivity only sees vertices.

(General-purpose; a candidate for hoisting into `Schoenflies/Graph/`.) -/
theorem IsTwoConnected.of_edge_paths (hG : G.IsTwoConnected) {x y : β → α} {W : β → List β'}
    (hlink : ∀ e ∈ E(G), G.IsLink e (x e) (y e))
    (hpath : ∀ e ∈ E(G), H.IsPath (x e) (W e) (y e))
    (hVH : ∀ v ∈ V(H), ∃ e ∈ E(G), v ∈ H.walkVertices (x e) (W e))
    (hGmem : ∀ e ∈ E(G), ∀ ⦃v⦄, v ∈ H.walkVertices (x e) (W e) → v ∈ V(G) →
      v = x e ∨ v = y e)
    (hdisj : ∀ e ∈ E(G), ∀ e' ∈ E(G), e ≠ e' → ∀ ⦃v⦄, v ∈ H.walkVertices (x e) (W e) →
      v ∈ H.walkVertices (x e') (W e') → v ∈ V(G)) :
    H.IsTwoConnected := by
  -- Every vertex of `G` is an end of some edge, hence on that edge's path.
  have hGv : ∀ v ∈ V(G), ∃ e ∈ E(G), v ∈ H.walkVertices (x e) (W e) := by
    intro v hv
    obtain ⟨w, hw, hwv, -⟩ := hG.hasThreeVertices.exists_ne_ne v v
    obtain ⟨e, u, hl⟩ := hG.connected.exists_isLink_left hv hw (Ne.symm hwv)
    have he := hl.edge_mem
    refine ⟨e, he, ?_⟩
    rcases hl.left_eq_or_eq (hlink e he) with rfl | rfl
    · exact mem_walkVertices_self
    · exact (hpath e he).isWalk.target_mem_walkVertices
  have hVGH : V(G) ⊆ V(H) := by
    intro v hv
    obtain ⟨e, he, hmem⟩ := hGv v hv
    exact (hpath e he).isWalk.walkVertices_subset hmem
  -- A walk of `G` transports into `H`, one path per step.
  have hHreach : ∀ ⦃u v⦄, G.Reaches u v → H.Reaches u v := by
    rintro u v ⟨D, hD⟩
    induction hD with
    | nil hu => exact Reaches.refl (hVGH hu)
    | @cons a c b f D hl hD' ih =>
      refine Reaches.trans ?_ ih
      have hf := hl.edge_mem
      have hr : H.Reaches (x f) (y f) := ⟨W f, (hpath f hf).isWalk⟩
      rcases hl.eq_and_eq_or_eq_and_eq (hlink f hf) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hr
      · exact hr.symm
  -- After deleting any vertex, a path vertex still reaches one of its path's ends.
  have hreach_end : ∀ z : α, ∀ e ∈ E(G), ∀ ⦃v⦄, v ∈ H.walkVertices (x e) (W e) → v ≠ z →
      ∃ w, (w = x e ∨ w = y e) ∧ w ≠ z ∧ (H.deleteVerts {z}).Reaches v w := by
    intro z e he v hv hvz
    rcases (hpath e he).reaches_an_end hv hvz with hr | hr
    · exact ⟨x e, Or.inl rfl, (mem_deleteVerts_singleton.1 hr.right_mem).2, hr⟩
    · exact ⟨y e, Or.inr rfl, (mem_deleteVerts_singleton.1 hr.right_mem).2, hr⟩
  -- A first edge, for the connectivity hub.
  obtain ⟨a₀, ha₀, b₀, hb₀, -, -, hab₀, -, -⟩ := hG.hasThreeVertices
  obtain ⟨e₀, u₀, hl₀⟩ := hG.connected.exists_isLink_left ha₀ hb₀ hab₀
  have he₀ := hl₀.edge_mem
  have hconn : H.Connected := by
    refine Connected.of_hub (u := x e₀) (hpath e₀ he₀).left_mem fun v hv => ?_
    obtain ⟨e, he, hmem⟩ := hVH v hv
    obtain ⟨W₁, W₂, -, h₁, -, -⟩ := (hpath e he).split hmem
    exact (hHreach (hG.connected.reaches (hlink e₀ he₀).left_mem
      (hlink e he).left_mem)).trans ⟨W₁, h₁.isWalk⟩
  have hthree : H.HasThreeVertices := by
    -- `HasThreeVertices.mono` is same-edge-type; rebuild the triple across the type change.
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := hG.hasThreeVertices
    exact ⟨p, hVGH hp, q, hVGH hq, r, hVGH hr, hpq, hpr, hqr⟩
  refine ⟨hthree, hconn, ?_⟩
  intro z hz
  by_cases hzG : z ∈ V(G)
  · -- Deleting an old vertex: `G - z` transports, since no other edge's path visits `z`.
    have htrans : ∀ ⦃u v⦄, (G.deleteVerts {z}).Reaches u v →
        (H.deleteVerts {z}).Reaches u v := by
      rintro u v ⟨D, hD⟩
      induction hD with
      | nil hu =>
        rw [mem_deleteVerts_singleton] at hu
        exact Reaches.refl (mem_deleteVerts_singleton_of_ne (hVGH hu.1) hu.2)
      | @cons a c b f D hl hD' ih =>
        refine Reaches.trans ?_ ih
        rw [deleteVerts_isLink] at hl
        obtain ⟨hlG, haz, hcz⟩ := hl
        have haz' : a ≠ z := by simpa using haz
        have hcz' : c ≠ z := by simpa using hcz
        have hf := hlG.edge_mem
        have hends : x f ≠ z ∧ y f ≠ z := by
          rcases hlG.eq_and_eq_or_eq_and_eq (hlink f hf) with ⟨ha, hc⟩ | ⟨ha, hc⟩
          · exact ⟨ha ▸ haz', hc ▸ hcz'⟩
          · exact ⟨hc ▸ hcz', ha ▸ haz'⟩
        have hzW : z ∉ H.walkVertices (x f) (W f) := fun hmem =>
          (hGmem f hf hmem hzG).elim (fun h => hends.1 h.symm) (fun h => hends.2 h.symm)
        have hstep : (H.deleteVerts {z}).Reaches (x f) (y f) :=
          ⟨W f, (hpath f hf).isWalk.avoiding hzW⟩
        rcases hlG.eq_and_eq_or_eq_and_eq (hlink f hf) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hstep
        · exact hstep.symm
    obtain ⟨a₁, ha₁G, ha₁z, -⟩ := hG.hasThreeVertices.exists_ne_ne z z
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne (hVGH ha₁G) ha₁z)
      fun v hv => ?_
    rw [mem_deleteVerts_singleton] at hv
    obtain ⟨e, he, hmem⟩ := hVH v hv.1
    obtain ⟨w, hwend, hwz, hr⟩ := hreach_end z e he hmem hv.2
    have hwG : w ∈ V(G) := by
      rcases hwend with rfl | rfl
      exacts [(hlink e he).left_mem, (hlink e he).right_mem]
    have h2 : (H.deleteVerts {z}).Reaches w a₁ :=
      htrans ((hG.deleteVerts_connected hzG).reaches
        (mem_deleteVerts_singleton_of_ne hwG hwz)
        (mem_deleteVerts_singleton_of_ne ha₁G ha₁z))
    exact (hr.trans h2).symm
  · -- Deleting a new vertex: only one edge's path carries it, and that edge is no bridge.
    obtain ⟨e₁, he₁, hze₁⟩ := hVH z hz
    have hDE : (G.deleteEdges {e₁}).Connected :=
      hG.connected.deleteEdges_singleton
        ((liesOnCycle_iff_deleteEdges_reaches (hlink e₁ he₁)).2
          (hG.no_bridge (hlink e₁ he₁)))
    have htrans : ∀ ⦃u v⦄, (G.deleteEdges {e₁}).Reaches u v →
        (H.deleteVerts {z}).Reaches u v := by
      rintro u v ⟨D, hD⟩
      induction hD with
      | nil hu =>
        rw [vertexSet_deleteEdges] at hu
        exact Reaches.refl
          (mem_deleteVerts_singleton_of_ne (hVGH hu) fun h => hzG (h ▸ hu))
      | @cons a c b f D hl hD' ih =>
        refine Reaches.trans ?_ ih
        have hfE := hl.edge_mem
        rw [mem_edgeSet_deleteEdges_iff] at hfE
        obtain ⟨hf, hfe₁⟩ := hfE
        have hfe₁' : f ≠ e₁ := by simpa using hfe₁
        have hlG : G.IsLink f a c := deleteEdges_le.isLink_mono hl
        have hzW : z ∉ H.walkVertices (x f) (W f) := fun hmem =>
          hzG (hdisj f hf e₁ he₁ hfe₁' hmem hze₁)
        have hstep : (H.deleteVerts {z}).Reaches (x f) (y f) :=
          ⟨W f, (hpath f hf).isWalk.avoiding hzW⟩
        rcases hlG.eq_and_eq_or_eq_and_eq (hlink f hf) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hstep
        · exact hstep.symm
    refine Connected.of_hub (u := x e₁) (mem_deleteVerts_singleton_of_ne
      (hpath e₁ he₁).left_mem fun h => hzG (h ▸ (hlink e₁ he₁).left_mem)) fun v hv => ?_
    rw [mem_deleteVerts_singleton] at hv
    obtain ⟨e, he, hmem⟩ := hVH v hv.1
    obtain ⟨w, hwend, hwz, hr⟩ := hreach_end z e he hmem hv.2
    have hwG : w ∈ V(G) := by
      rcases hwend with rfl | rfl
      exacts [(hlink e he).left_mem, (hlink e he).right_mem]
    have h2 : (H.deleteVerts {z}).Reaches w (x e₁) := by
      refine htrans (hDE.reaches ?_ ?_)
      · rw [vertexSet_deleteEdges]; exact hwG
      · rw [vertexSet_deleteEdges]; exact (hlink e₁ he₁).left_mem
    exact (hr.trans h2).symm

end Graph
