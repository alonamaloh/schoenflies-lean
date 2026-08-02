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

namespace Schoenflies

/-! ### The parameter interval of a segment inside an arc

An overlay edge lying inside a drawn 1-cell arc occupies, in the arc's own parameter, a closed
subinterval whose two endpoints map to the edge's two ends. This is what replaces the
distance-from-an-end coordinate of `Schoenflies.exists_incWalk_insideEdges` when the ambient
is an arc rather than a straight segment. The inverse continuity is
`Schoenflies.image_isRelOpen`, spent twice: once to see the preimage of the segment is
connected, once (through preconnectedness of the punctured image) to see the interval's
endpoints map to the segment's ends. -/

/-- **A point whose removal leaves a nondegenerate segment connected is an end.** Removing an
interior point splits the segment into the near part and the far part, separated by the
distance from the first end. (General-purpose; a candidate for hoisting into
`Schoenflies/SegmentOrder.lean`.) -/
theorem end_of_isPreconnected_diff {Q : Piece} (hQN : Q.Nondeg) {z : Plane} (hz : z ∈ Q.seg)
    (hpre : IsPreconnected (Q.seg \ {z})) : z = Q.1 ∨ z = Q.2 := by
  by_contra hcon
  push Not at hcon
  have hzi : z ∈ Q.interior :=
    mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hz
  have hlt : dist Q.1 Q.1 < dist Q.1 z ∧ dist Q.1 z < dist Q.1 Q.2 :=
    dist_lt_of_mem_openSegment hQN (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _) hQN
      (by rw [dist_self]; exact dist_nonneg) hzi
  rw [dist_self] at hlt
  -- The two open half-planes at the distance of `z` from `Q.1` separate the remainder.
  have hU₁ : IsOpen {w : Plane | dist Q.1 w < dist Q.1 z} :=
    isOpen_lt (by fun_prop) continuous_const
  have hU₂ : IsOpen {w : Plane | dist Q.1 z < dist Q.1 w} :=
    isOpen_lt continuous_const (by fun_prop)
  have hsub : Q.seg \ {z} ⊆ {w | dist Q.1 w < dist Q.1 z} ∪ {w | dist Q.1 z < dist Q.1 w} := by
    rintro w ⟨hw, hwz⟩
    rcases lt_trichotomy (dist Q.1 w) (dist Q.1 z) with h | h | h
    · exact Or.inl h
    · exact absurd (eq_of_dist_left_eq hQN hw hz h) (by simpa using hwz)
    · exact Or.inr h
  have h₁ : ((Q.seg \ {z}) ∩ {w | dist Q.1 w < dist Q.1 z}).Nonempty :=
    ⟨Q.1, ⟨left_mem_segment ℝ _ _, by simpa using fun h => hcon.1 h.symm⟩,
      by simpa [dist_self] using hlt.1⟩
  have h₂ : ((Q.seg \ {z}) ∩ {w | dist Q.1 z < dist Q.1 w}).Nonempty :=
    ⟨Q.2, ⟨right_mem_segment ℝ _ _, by simpa using fun h => hcon.2 h.symm⟩, hlt.2⟩
  obtain ⟨w, -, hw₁, hw₂⟩ := hpre _ _ hU₁ hU₂ hsub h₁ h₂
  rw [mem_setOf_eq] at hw₁ hw₂
  exact absurd (hw₁.trans hw₂) (lt_irrefl _)

variable {f : ℝ → Plane}

/-- **A nondegenerate segment inside an arc is the image of a closed parameter interval**,
whose endpoints map to the segment's two ends. Compactness and inverse continuity
(`Schoenflies.image_isRelOpen`) make the parameter set a compact interval; puncturing it at
either endpoint leaves the image connected, so each endpoint maps to an end by
`Schoenflies.end_of_isPreconnected_diff`. -/
theorem exists_arc_param_Icc (hc : ContinuousOn f I) (hi : InjOn f I)
    {Q : Piece} (hQN : Q.Nondeg) (hQsub : Q.seg ⊆ f '' I) :
    ∃ s t : ℝ, s ∈ I ∧ t ∈ I ∧ s < t ∧ I ∩ f ⁻¹' Q.seg = Icc s t ∧
      f '' Icc s t = Q.seg ∧
      ((f s = Q.1 ∧ f t = Q.2) ∨ (f s = Q.2 ∧ f t = Q.1)) := by
  set T : Set ℝ := I ∩ f ⁻¹' Q.seg with hTdef
  have hTsubI : T ⊆ I := inter_subset_left
  have hTcl : IsClosed T :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc (isCompact_segment Q.1 Q.2).isClosed
  have hTcp : IsCompact T := isCompact_I.of_isClosed_subset hTcl hTsubI
  have hfT : f '' T = Q.seg := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact hu.2
    · intro q hq
      obtain ⟨u, hu, rfl⟩ := hQsub hq
      exact ⟨u, ⟨hu, hq⟩, rfl⟩
  have hTne : T.Nonempty := by
    obtain ⟨u, hu, huq⟩ := hQsub (left_mem_segment ℝ Q.1 Q.2)
    exact ⟨u, hu, by rw [mem_preimage, huq]; exact left_mem_segment ℝ Q.1 Q.2⟩
  -- The preimage is preconnected: its two would-be halves have relatively open images.
  have hTpre : IsPreconnected T := by
    intro U V hU hV hTUV hTU hTV
    obtain ⟨U', hU'op, hU'eq⟩ := image_isRelOpen hc hi hU
    obtain ⟨V', hV'op, hV'eq⟩ := image_isRelOpen hc hi hV
    have hmemU' : ∀ u ∈ T, u ∈ U → f u ∈ U' := fun u hu huU => by
      have : f u ∈ f '' (U ∩ I) := ⟨u, ⟨huU, hTsubI hu⟩, rfl⟩
      rw [hU'eq] at this
      exact this.1
    have hmemV' : ∀ u ∈ T, u ∈ V → f u ∈ V' := fun u hu huV => by
      have : f u ∈ f '' (V ∩ I) := ⟨u, ⟨huV, hTsubI hu⟩, rfl⟩
      rw [hV'eq] at this
      exact this.1
    have hcov : Q.seg ⊆ U' ∪ V' := by
      intro q hq
      have hq' : q ∈ f '' T := by rw [hfT]; exact hq
      obtain ⟨u, hu, rfl⟩ := hq'
      exact (hTUV hu).imp (hmemU' u hu) (hmemV' u hu)
    obtain ⟨u₁, hu₁T, hu₁U⟩ := hTU
    obtain ⟨u₂, hu₂T, hu₂V⟩ := hTV
    have him₁ : f u₁ ∈ Q.seg := by rw [← hfT]; exact mem_image_of_mem f hu₁T
    have him₂ : f u₂ ∈ Q.seg := by rw [← hfT]; exact mem_image_of_mem f hu₂T
    obtain ⟨q, hqseg, hqU', hqV'⟩ :=
      (convex_segment Q.1 Q.2).isPreconnected _ _ hU'op hV'op hcov
        ⟨f u₁, him₁, hmemU' u₁ hu₁T hu₁U⟩ ⟨f u₂, him₂, hmemV' u₂ hu₂T hu₂V⟩
    have hq' : q ∈ f '' T := by rw [hfT]; exact hqseg
    obtain ⟨u, huT, rfl⟩ := hq'
    have himu : f u ∈ f '' I := mem_image_of_mem f (hTsubI huT)
    -- pull the common point back along injectivity
    have huU : u ∈ U := by
      have h1 : f u ∈ f '' (U ∩ I) := by rw [hU'eq]; exact ⟨hqU', himu⟩
      obtain ⟨u', hu', he⟩ := h1
      exact (hi hu'.2 (hTsubI huT) he) ▸ hu'.1
    have huV : u ∈ V := by
      have h1 : f u ∈ f '' (V ∩ I) := by rw [hV'eq]; exact ⟨hqV', himu⟩
      obtain ⟨u', hu', he⟩ := h1
      exact (hi hu'.2 (hTsubI huT) he) ▸ hu'.1
    exact ⟨u, huT, huU, huV⟩
  have hIcc : T = Icc (sInf T) (sSup T) := eq_Icc_of_connected_compact ⟨hTne, hTpre⟩ hTcp
  set s := sInf T
  set t := sSup T
  have hstle : s ≤ t := nonempty_Icc.1 (hIcc ▸ hTne)
  have hsT : s ∈ T := hIcc ▸ mem_Icc.2 ⟨le_rfl, hstle⟩
  have htT : t ∈ T := hIcc ▸ mem_Icc.2 ⟨hstle, le_rfl⟩
  have hsI : s ∈ I := hTsubI hsT
  have htI : t ∈ I := hTsubI htT
  have hfIcc : f '' Icc s t = Q.seg := by rw [← hIcc]; exact hfT
  have hst : s < t := by
    rcases lt_or_eq_of_le hstle with h | h
    · exact h
    -- a one-point interval would collapse the segment to a point
    exfalso
    rw [h, Icc_self, image_singleton] at hfIcc
    refine hQN ?_
    have h1 : Q.1 ∈ ({f t} : Set Plane) := by rw [hfIcc]; exact left_mem_segment ℝ Q.1 Q.2
    have h2 : Q.2 ∈ ({f t} : Set Plane) := by rw [hfIcc]; exact right_mem_segment ℝ Q.1 Q.2
    rw [mem_singleton_iff] at h1 h2
    rw [h1, h2]
  -- Each interval endpoint maps to an end of the segment.
  have hIccI : Icc s t ⊆ I := hIcc ▸ hTsubI
  have hfsmem : f s ∈ Q.seg := by rw [← hfIcc]; exact mem_image_of_mem f (mem_Icc.2 ⟨le_rfl, hstle⟩)
  have hftmem : f t ∈ Q.seg := by rw [← hfIcc]; exact mem_image_of_mem f (mem_Icc.2 ⟨hstle, le_rfl⟩)
  have hfs : f s = Q.1 ∨ f s = Q.2 := by
    have himg : f '' Ioc s t = Q.seg \ {f s} := by
      rw [← Icc_sdiff_left,
        (hi.mono hIccI).image_sdiff_subset (singleton_subset_iff.2 (mem_Icc.2 ⟨le_rfl, hstle⟩)),
        image_singleton, hfIcc]
    refine end_of_isPreconnected_diff hQN hfsmem ?_
    rw [← himg]
    exact (isPreconnected_Ioc).image f (hc.mono ((Ioc_subset_Icc_self).trans hIccI))
  have hft : f t = Q.1 ∨ f t = Q.2 := by
    have himg : f '' Ico s t = Q.seg \ {f t} := by
      rw [← Icc_sdiff_right,
        (hi.mono hIccI).image_sdiff_subset (singleton_subset_iff.2 (mem_Icc.2 ⟨hstle, le_rfl⟩)),
        image_singleton, hfIcc]
    refine end_of_isPreconnected_diff hQN hftmem ?_
    rw [← himg]
    exact (isPreconnected_Ico).image f (hc.mono ((Ico_subset_Icc_self).trans hIccI))
  have hfst : f s ≠ f t := fun h => (ne_of_lt hst) (hi hsI htI h)
  refine ⟨s, t, hsI, htI, hst, hIcc, hfIcc, ?_⟩
  · rcases hfs with h1 | h1 <;> rcases hft with h2 | h2
    · exact absurd (h1.trans h2.symm) hfst
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hfst

/-! ### The overlay edges inside an arc, walked in order of the arc parameter -/

/-- **The overlay piece leaving the current parameter.** Among finitely many overlay pieces
inside the arc covering everything at and beyond parameter `p` (short of the far end), some
piece's parameter interval starts at or before `p` and ends strictly beyond it: take a
parameter just short of the first piece-end parameter beyond `p` and look at the piece
covering it. -/
theorem exists_arcPiece_beyond {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hc : ContinuousOn f I) (hi : InjOn f I)
    {E : Set Piece} (hEov : ∀ Q ∈ E, Q ∈ overlayPieces pieces points)
    (hEsub : ∀ Q ∈ E, Q.seg ⊆ f '' I)
    {p : ℝ} (hpI : p ∈ I) (hp1 : p ≠ 1)
    (hcov : ∀ r ∈ Icc p (1 : ℝ), r ≠ 1 → ∃ Q ∈ E, f r ∈ Q.seg) :
    ∃ Q ∈ E, ∃ s t : ℝ, s ∈ I ∧ t ∈ I ∧ s < t ∧ I ∩ f ⁻¹' Q.seg = Icc s t ∧
      f '' Icc s t = Q.seg ∧
      ((f s = Q.1 ∧ f t = Q.2) ∨ (f s = Q.2 ∧ f t = Q.1)) ∧ s ≤ p ∧ p < t := by
  have hEfin : E.Finite := (List.finite_toSet _).subset fun Q hQ => hEov Q hQ
  -- the parameters of piece ends beyond `p`, together with the far end of the arc
  set D : Set ℝ := {r | r ∈ I ∧ p < r ∧ (r = 1 ∨ ∃ Q ∈ E, f r = Q.1 ∨ f r = Q.2)} with hD
  have hDfin : D.Finite := by
    have hsub : D ⊆ insert (1 : ℝ)
        (⋃ Q ∈ E, {r | r ∈ I ∧ f r = Q.1} ∪ {r | r ∈ I ∧ f r = Q.2}) := by
      rintro r ⟨hrI, -, h1 | ⟨Q, hQ, hend⟩⟩
      · exact Or.inl h1
      · refine Or.inr (mem_iUnion₂.2 ⟨Q, hQ, ?_⟩)
        rcases hend with h | h
        exacts [Or.inl ⟨hrI, h⟩, Or.inr ⟨hrI, h⟩]
    refine Finite.subset (Finite.insert _ (Finite.biUnion hEfin fun Q _ => ?_)) hsub
    refine Finite.union ?_ ?_ <;>
      exact Set.Subsingleton.finite fun r₁ h₁ r₂ h₂ => hi h₁.1 h₂.1 (h₁.2.trans h₂.2.symm)
  have hp1' : p < 1 := lt_of_le_of_ne hpI.2 hp1
  have h1D : (1 : ℝ) ∈ D := ⟨one_mem_I, hp1', Or.inl rfl⟩
  obtain ⟨m, hmD, hmmin⟩ := Set.exists_min_image D id hDfin ⟨1, h1D⟩
  have hpm : p < m := hmD.2.1
  have hm1 : m ≤ 1 := by simpa using hmmin 1 h1D
  -- a parameter strictly between `p` and the first end beyond it
  set r : ℝ := (p + m) / 2 with hr
  have hpr : p < r := by rw [hr]; linarith
  have hrm : r < m := by rw [hr]; linarith
  have hrI : r ∈ I := ⟨hpI.1.trans hpr.le, hrm.le.trans hm1⟩
  have hr1 : r ≠ 1 := ne_of_lt (lt_of_lt_of_le hrm hm1)
  obtain ⟨Q, hQE, hrQ⟩ := hcov r ⟨hpr.le, hrI.2⟩ hr1
  have hQN : Q.Nondeg := overlayPieces_nondeg points hnd Q (hEov Q hQE)
  obtain ⟨s, t, hsI, htI, hst, hT, hfIcc, hends⟩ :=
    exists_arc_param_Icc hc hi hQN (hEsub Q hQE)
  have hrT : r ∈ Icc s t := by rw [← hT]; exact ⟨hrI, hrQ⟩
  -- the piece's near end is at or before `p`: it is short of `m`, the least end beyond `p`
  have hsp : s ≤ p := by
    by_contra hcon
    have hsD : s ∈ D := by
      refine ⟨hsI, not_le.1 hcon, Or.inr ⟨Q, hQE, ?_⟩⟩
      rcases hends with ⟨h, -⟩ | ⟨h, -⟩
      exacts [Or.inl h, Or.inr h]
    have h1 : m ≤ s := by simpa using hmmin s hsD
    have h2 : s ≤ r := hrT.1
    linarith
  exact ⟨Q, hQE, s, t, hsI, htI, hst, hT, hfIcc, hends, hsp, lt_of_lt_of_le hpr hrT.2⟩

/-- **The overlay edges inside an arc are a path from one end of the arc to the other**,
taking every overlay edge inside the arc exactly once, in increasing arc parameter, and
visiting every overlay vertex on the arc. This is the arc analogue of
`Schoenflies.exists_incWalk_insideEdges`, with the distance-from-an-end coordinate replaced by
the parameter of the arc's own parametrization. -/
theorem exists_arcPath_overlay {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points)
    (hc : ContinuousOn f I) (hi : InjOn f I)
    (hsrc : ∀ z ∈ f '' I, ∃ R ∈ pieces, z ∈ R.seg ∧ R.seg ⊆ f '' I)
    (h1V : f 1 ∈ V(overlayGraph pieces points)) :
    ∃ W : List Piece, (overlayGraph pieces points).IsPath (f 0) W (f 1) ∧
      (∀ Q ∈ W, Q ∈ E(overlayGraph pieces points) ∧ Q.seg ⊆ f '' I) ∧
      ∀ v ∈ V(overlayGraph pieces points), v ∈ f '' I →
        v ∈ (overlayGraph pieces points).walkVertices (f 0) W := by
  classical
  -- the family: the overlay edges lying inside the arc; every point short of the far end is
  -- on one of them
  have hcovA : ∀ r ∈ I, r ≠ 1 →
      ∃ Q, (Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ f '' I) ∧ f r ∈ Q.seg := by
    intro r hrI _
    obtain ⟨R, hR, hfrR, hRsub⟩ := hsrc (f r) (mem_image_of_mem f hrI)
    obtain ⟨Q, hQov, hfrQ, hQR⟩ := exists_overlayPiece_mem_subset (points := points) hR hfrR
    exact ⟨Q, ⟨hQov, hQR.trans hRsub⟩, hfrQ⟩
  suffices key : ∀ n : ℕ, ∀ p, p ∈ I → ∀ E : Set Piece, E.ncard = n →
      (∀ Q ∈ E, Q ∈ overlayPieces pieces points) →
      (∀ Q ∈ E, Q.seg ⊆ f '' Icc p 1) →
      (∀ r ∈ Icc p (1 : ℝ), r ≠ 1 → ∃ Q ∈ E, f r ∈ Q.seg) →
      ∃ W : List Piece, (∀ Q, Q ∈ W ↔ Q ∈ E) ∧
        (overlayGraph pieces points).IsIncWalk (Function.invFunOn f I) (f p) W (f 1) by
    obtain ⟨W, hWmem, hWwalk⟩ := key
      {Q | Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ f '' I}.ncard 0 zero_mem_I
      {Q | Q ∈ overlayPieces pieces points ∧ Q.seg ⊆ f '' I} rfl
      (fun Q hQ => hQ.1) (fun Q hQ => hQ.2)
      (fun r hr hr1 => by
        obtain ⟨Q, hQ, hfrQ⟩ := hcovA r hr hr1
        exact ⟨Q, hQ, hfrQ⟩)
    refine ⟨W, hWwalk.isPath, fun Q hQ => (hWmem Q).1 hQ, ?_⟩
    intro v hvV hvA
    obtain ⟨tv, htvI, rfl⟩ := hvA
    by_cases htv1 : tv = 1
    · subst htv1
      exact hWwalk.isWalk.target_mem_walkVertices
    · obtain ⟨Q, hQA, hfQ⟩ := hcovA tv htvI htv1
      have hQW : Q ∈ W := (hWmem Q).2 hQA
      -- an overlay vertex is a cut point, hence an end of the edge covering it
      obtain ⟨eP, hePov, hend⟩ := overlayGraph_mem_vertexSet.1 hvV
      have hvpts : f tv ∈ points := overlayPieces_ends_cut hEnds eP hePov _ hend
      have hvend : f tv = Q.1 ∨ f tv = Q.2 := by
        by_contra hcon
        push Not at hcon
        exact overlayPieces_avoids hnd _ hvpts Q hQA.1
          (mem_openSegment_of_ne_left_right (Ne.symm hcon.1) (Ne.symm hcon.2) hfQ)
      exact Graph.mem_walkVertices_of_mem_covered (end_mem_coveredVertices hQW hQA.1 hvend)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hpI E hcard hEov hEsub hcov
    by_cases hp1 : p = 1
    · -- nothing lies beyond the far end: the family is empty and the walk is over
      subst hp1
      have hE : E = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro Q hQ
        have h1 := hEsub Q hQ
        rw [Icc_self, image_singleton] at h1
        refine overlayPieces_nondeg points hnd Q (hEov Q hQ) ?_
        have e1 : Q.1 ∈ ({f 1} : Set Plane) := h1 (left_mem_segment ℝ Q.1 Q.2)
        have e2 : Q.2 ∈ ({f 1} : Set Plane) := h1 (right_mem_segment ℝ Q.1 Q.2)
        rw [mem_singleton_iff] at e1 e2
        rw [e1, e2]
      exact ⟨[], by simp [hE], .nil h1V⟩
    · have hEfin : E.Finite := (List.finite_toSet _).subset fun Q hQ => hEov Q hQ
      have hEsubI : ∀ Q ∈ E, Q.seg ⊆ f '' I := fun Q hQ =>
        (hEsub Q hQ).trans (image_mono fun u hu => ⟨hpI.1.trans hu.1, hu.2⟩)
      -- the parameter interval of any family member sits inside `[p, 1]`
      have hIccP : ∀ R ∈ E, ∀ s' t', I ∩ f ⁻¹' R.seg = Icc s' t' → Icc s' t' ⊆ Icc p 1 := by
        intro R hRE s' t' hT' u hu
        have hmem : u ∈ I ∩ f ⁻¹' R.seg := by rw [hT']; exact hu
        obtain ⟨u', hu', he⟩ := hEsub R hRE hmem.2
        exact (hi (⟨hpI.1.trans hu'.1, hu'.2⟩ : u' ∈ I) hmem.1 he) ▸ hu'
      -- a parameter strictly inside a member's interval maps into its interior
      have hintP : ∀ R ∈ E, ∀ s' t', s' ∈ I → t' ∈ I → I ∩ f ⁻¹' R.seg = Icc s' t' →
          ((f s' = R.1 ∧ f t' = R.2) ∨ (f s' = R.2 ∧ f t' = R.1)) →
          ∀ u, s' < u → u < t' → f u ∈ R.interior := by
        intro R hRE s' t' hs'I ht'I hT' hends' u hsu hut
        have huIcc : u ∈ Icc s' t' := ⟨hsu.le, hut.le⟩
        have hmem : u ∈ I ∩ f ⁻¹' R.seg := by rw [hT']; exact huIcc
        have hne1 : f u ≠ f s' := fun h => absurd (hi hmem.1 hs'I h) (ne_of_gt hsu)
        have hne2 : f u ≠ f t' := fun h => absurd (hi hmem.1 ht'I h) (ne_of_lt hut)
        have hR12 : R.1 ≠ f u ∧ R.2 ≠ f u := by
          rcases hends' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨by rw [← h1]; exact fun h => hne1 h.symm,
              by rw [← h2]; exact fun h => hne2 h.symm⟩
          · exact ⟨by rw [← h2]; exact fun h => hne2 h.symm,
              by rw [← h1]; exact fun h => hne1 h.symm⟩
        exact mem_openSegment_of_ne_left_right hR12.1 hR12.2 hmem.2
      obtain ⟨Q, hQE, s, t, hsI, htI, hst, hT, hfIcc, hends, hsp, hpt⟩ :=
        exists_arcPiece_beyond hnd hc hi hEov hEsubI hpI hp1 hcov
      have hps : p ≤ s := (hIccP Q hQE s t hT (mem_Icc.2 ⟨le_rfl, hst.le⟩)).1
      have hsp2 : s = p := le_antisymm hsp hps
      have hQov := hEov Q hQE
      have hlinkQ : (overlayGraph pieces points).IsLink Q Q.1 Q.2 := ⟨hQov, Or.inl ⟨rfl, rfl⟩⟩
      -- the step from `f p` to the far end of the leaving piece
      have hstep : (overlayGraph pieces points).IsLink Q (f p) (f t) := by
        rw [← hsp2]
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hlinkQ
        · rw [h1, h2]; exact hlinkQ.symm
      have hcoord : Function.invFunOn f I (f p) < Function.invFunOn f I (f t) := by
        rw [hi.leftInvOn_invFunOn hpI, hi.leftInvOn_invFunOn htI]
        exact hpt
      -- every other member lies beyond `t`: overlapping intervals would overlap interiors
      have hbeyond : ∀ R ∈ E, R ≠ Q → ∀ s' t', s' ∈ I → t' ∈ I → s' < t' →
          I ∩ f ⁻¹' R.seg = Icc s' t' →
          ((f s' = R.1 ∧ f t' = R.2) ∨ (f s' = R.2 ∧ f t' = R.1)) → t ≤ s' := by
        intro R hRE hRQ s' t' hs'I ht'I hst' hT' hends'
        by_contra hcon
        have hs't : s' < t := not_le.1 hcon
        have hps' : p ≤ s' := (hIccP R hRE s' t' hT' (mem_Icc.2 ⟨le_rfl, hst'.le⟩)).1
        set u := (s' + min t' t) / 2 with hu
        have humin : s' < min t' t := lt_min hst' hs't
        have hu1 : s' < u := by rw [hu]; linarith
        have hu2 : u < min t' t := by rw [hu]; linarith
        have hut' : u < t' := lt_of_lt_of_le hu2 (min_le_left _ _)
        have hut : u < t := lt_of_lt_of_le hu2 (min_le_right _ _)
        have hsu : s < u := by rw [hsp2]; exact lt_of_le_of_lt hps' hu1
        exact overlayPieces_disjoint_interiors hnd hEnds hMeets (hEov R hRE) hQov hRQ
          (hintP R hRE s' t' hs'I ht'I hT' hends' u hu1 hut')
          (hintP Q hQE s t hsI htI hT hends u hsu hut)
      -- the pruned family covers from `t` on
      have hcov' : ∀ r ∈ Icc t (1 : ℝ), r ≠ 1 → ∃ R ∈ E \ {Q}, f r ∈ R.seg := by
        intro r hr hr1
        have hrI : r ∈ I := ⟨htI.1.trans hr.1, hr.2⟩
        have hpt' : p ≤ t := hps.trans hst.le
        obtain ⟨R, hRE, hfrR⟩ := hcov r ⟨hpt'.trans hr.1, hr.2⟩ hr1
        by_cases hRQ : R = Q
        · -- the point is the junction `f t` itself; the piece beyond it is a different one
          rw [hRQ] at hfrR
          have hrT : r ∈ Icc s t := by rw [← hT]; exact ⟨hrI, hfrR⟩
          have hrt : r = t := le_antisymm hrT.2 hr.1
          have ht1 : t ≠ 1 := by rw [← hrt]; exact hr1
          obtain ⟨R₂, hR₂E, s₂, t₂, hs₂I, ht₂I, hst₂, hT₂, hfIcc₂, hends₂, hs₂r, hrt₂⟩ :=
            exists_arcPiece_beyond hnd hc hi hEov hEsubI htI ht1
              (fun r' hr' hr'1 => hcov r' ⟨hpt'.trans hr'.1, hr'.2⟩ hr'1)
          have hR₂Q : R₂ ≠ Q := by
            rintro rfl
            have hII : Icc s t = Icc s₂ t₂ := by rw [← hT, ← hT₂]
            have h2 : t = t₂ := by
              have e1 : sSup (Icc s t) = t := csSup_Icc hst.le
              have e2 : sSup (Icc s₂ t₂) = t₂ := csSup_Icc hst₂.le
              rw [← e1, ← e2, hII]
            rw [← h2] at hrt₂
            exact lt_irrefl _ hrt₂
          refine ⟨R₂, ⟨hR₂E, by simpa using hR₂Q⟩, ?_⟩
          have hmem : t ∈ I ∩ f ⁻¹' R₂.seg := by
            rw [hT₂]; exact ⟨hs₂r, hrt₂.le⟩
          rw [hrt]
          exact hmem.2
        · exact ⟨R, ⟨hRE, by simpa using hRQ⟩, hfrR⟩
      have hsub' : ∀ R ∈ E \ {Q}, R.seg ⊆ f '' Icc t 1 := by
        rintro R ⟨hRE, hRQ⟩
        have hRQ' : R ≠ Q := by simpa using hRQ
        have hRN : R.Nondeg := overlayPieces_nondeg points hnd R (hEov R hRE)
        obtain ⟨s', t', hs'I, ht'I, hst', hT', hfIcc', hends'⟩ :=
          exists_arc_param_Icc hc hi hRN (hEsubI R hRE)
        have hts' : t ≤ s' := hbeyond R hRE hRQ' s' t' hs'I ht'I hst' hT' hends'
        rw [← hfIcc']
        exact image_mono fun u hu => ⟨hts'.trans hu.1, hu.2.trans ht'I.2⟩
      have hEov' : ∀ R ∈ E \ {Q}, R ∈ overlayPieces pieces points := fun R hR => hEov R hR.1
      have hcard' : (E \ {Q}).ncard < n := by
        rw [← hcard]
        exact Set.ncard_sdiff_singleton_lt_of_mem hQE hEfin
      obtain ⟨W', hW'mem, hW'walk⟩ := ih _ hcard' t htI (E \ {Q}) rfl hEov' hsub' hcov'
      refine ⟨Q :: W', fun R => ?_, .cons hstep hcoord hW'walk⟩
      simp only [List.mem_cons, hW'mem, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | ⟨h, -⟩)
        exacts [hQE, h]
      · intro hR
        by_cases h : R = Q
        · exact Or.inl h
        · exact Or.inr ⟨hR, h⟩

end Schoenflies
