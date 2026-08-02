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

end Schoenflies
