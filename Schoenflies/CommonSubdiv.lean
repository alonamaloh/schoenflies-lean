/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SubdivPoints
import Schoenflies.EarStep
import Schoenflies.Graph.AdjCongr
import Schoenflies.Graph.PlaneEdges

/-!
# Step 1 of `thm:finite-transfer`(a): the part of the extension that lies on the old skeleton

`Schoenflies.CommonSubdivision` asks for a 2-connected subgraph `K ≤ H` carrying a generated
pair that refines the given one. Since the pair may only be refined by *edge subdivisions* at
this step — no ear is inserted — and a subdivision does not move the realized skeleton
(`SubdivData.skeletonSet_realize`), the point set of `K` is forced: it has to be `|Γ|`. So `K`
is forced too, and it is what this module builds.

`Schoenflies.sourcePart R H Hdraw` is the subgraph of `H` on the vertices of `H` that lie on
`|Γ|`, with the edges of `H` whose arcs lie on `|Γ|`. Two facts about it are proved here:

* `sourcePart_le` — it is a subgraph of `H`, which is one of the three clauses;
* `pointSet_sourcePart` — it occupies exactly `|Γ|`, which is the other geometric one.

The second is where the hypotheses on the extension are spent, and only two of them: `|Γ| ⊆ |H|`
puts every skeleton point on `H`, and `edge_subset` — *an edge of `H` meeting an open edge of
`Γ` at a non-vertex of `H` runs inside it* — turns "this edge of `H` passes through `|Γ|` away
from all vertices" into "this edge of `H` lies inside `|Γ|`". That second hypothesis is the
whole of "`H` contains a subdivision of `Γ`" as far as step 1 is concerned: it is what says `H`
does not *cross* `Γ`, so that the blueprint's overlay has, in the Lean formulation, already been
performed by the hypothesis. A skeleton point that is a vertex of `H` — where an `H`-edge is
allowed to merely *touch* an old open 1-cell — needs no edge at all: it survives `sourcePart`'s
vertex restriction directly.

This module also carries `IsSourceExtension.edge_subset_of_edgeArc_subset_skeletonSet`, the
recovery of the pre-repair `edge_subset` for the edges drawn *on* the old skeleton — the one
fact about the weakened field that direction (b)'s fresh-anchor bookkeeping needs beyond the
field itself.

## The third clause, and why it was the hard one

`K.IsTwoConnected` is not read off the bundle, and the obstruction is names rather than
mathematics: 2-connectivity of the *realized* skeleton is a field of `IsWeaklyAdmissible` and so
is free at every stage, but that graph carries names drawn from `γ` by the freshness lemmas
while `K ≤ H` forces `K` to carry `H`'s names, and there is no edge relabelling in Mathlib or
here. Choosing `H`'s names for the subdivisions is not open either: `SubdivData.newEdge₁_notMem`
wants them fresh, and nothing stops an edge name of `H` from already being a cell of `P`.

Three results close it, and none of them mentions the other two's subject matter:

* `GeneratedPair.exists_subdivide_finite` (`SubdivPoints.lean`) produces the stage whose 0-cells
  are exactly the old ones together with `V(H) ∩ |Γ|`, i.e. `V(sourcePart)` — the reverse vertex
  inclusion is what makes that an equality;
* `Graph.adj_congr_of_pointSet_eq` (`Graph/PlaneEdges.lean`) says two finite plane graphs
  occupying the same points with the same vertices have the same adjacency, because the open
  edges of a plane graph are the connected components of what its vertices leave of it. That is
  `Schoenflies.adj_match`;
* `Graph.IsTwoConnected.of_adj_congr` (`Graph/AdjCongr.lean`) carries 2-connectivity along that
  adjacency, across the change of edge type.

## Blueprint

* `Schoenflies.sourcePart` — the subgraph the blueprint's step 1 subdivides `Γ` to match.
* `Schoenflies.pointSet_sourcePart` — "the old skeleton is literally a subgraph of the overlay",
  on the source side and at the level of point sets.
* `Schoenflies.commonSubdivision` — step 1 of `thm:finite-transfer`(a), unconditional.
* `Schoenflies.finite_transfer_toward_square'` — `thm:finite-transfer`(a), unconditional.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

open Graph CellStructure

variable {γ : Type*} {S : CellStructure γ} {R : S.Realization} {outer dom : Set Plane}
  {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- **The part of the extension graph that lies on the old skeleton**: the vertices of `H` on
`|Γ|`, with the edges of `H` whose whole arc is on `|Γ|`.

Restricting the edges is not redundant given the vertex restriction: an edge of `H` between two
0-cells may leave `|Γ|` entirely in between — that is exactly what an ear is. -/
def sourcePart (R : S.Realization) (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Graph Plane γ :=
  (H.induce (V(H) ∩ R.skeletonSet)).restrict {f | edgeArc Hdraw f ⊆ R.skeletonSet}

@[simp] theorem sourcePart_vertexSet :
    V(sourcePart R H Hdraw) = V(H) ∩ R.skeletonSet := rfl

theorem sourcePart_isLink {f : γ} {x y : Plane} :
    (sourcePart R H Hdraw).IsLink f x y ↔ edgeArc Hdraw f ⊆ R.skeletonSet ∧ H.IsLink f x y ∧
      (x ∈ V(H) ∧ x ∈ R.skeletonSet) ∧ (y ∈ V(H) ∧ y ∈ R.skeletonSet) := Iff.rfl

/-- The first clause of `Schoenflies.CommonSubdivision`: it is a subgraph. -/
theorem sourcePart_le : sourcePart R H Hdraw ≤ H :=
  le_trans restrict_le (Graph.induce_le Set.inter_subset_left)

/-- An edge of `H` drawn inside the old skeleton is an edge of the part. Its two ends are
vertices of `H` on its own arc, so the vertex restriction does not lose it. -/
theorem mem_edgeSet_sourcePart (hH : IsSourceExtension R outer dom H Hdraw) {f : γ}
    (hf : f ∈ E(H)) (harc : edgeArc Hdraw f ⊆ R.skeletonSet) : f ∈ E(sourcePart R H Hdraw) := by
  have hl := (hH.isDrawing.edge_param hf).2.2
  have h0 : Hdraw f 0 ∈ edgeArc Hdraw f := ⟨0, zero_mem_I, rfl⟩
  have h1 : Hdraw f 1 ∈ edgeArc Hdraw f := ⟨1, one_mem_I, rfl⟩
  exact (sourcePart_isLink.2
    ⟨harc, hl, ⟨hl.left_mem, harc h0⟩, ⟨hl.right_mem, harc h1⟩⟩).edge_mem

/-- An edge of the part is drawn inside the old skeleton — the defining clause, read back. -/
theorem edgeArc_subset_of_mem_edgeSet_sourcePart {f : γ} (hf : f ∈ E(sourcePart R H Hdraw)) :
    edgeArc Hdraw f ⊆ R.skeletonSet := by
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet hf
  exact (sourcePart_isLink.1 hl).1

/-- **The part of the extension on the old skeleton occupies exactly the old skeleton.**

`⊆` is the definition. `⊇` is where `H` being an extension is spent: a skeleton point is a
0-cell — hence a vertex of `H`, hence of the part — or an interior point of a drawn 1-cell, and
then either it is itself a vertex of `H` — an `H`-edge is allowed to *end* on an open old
1-cell — and survives the vertex restriction, or the edge of `H` carrying it meets that open
1-cell away from the vertices, so `IsSourceExtension.edge_subset` puts the whole of that edge
inside the 1-cell's arc and therefore inside `|Γ|`. -/
theorem pointSet_sourcePart (hH : IsSourceExtension R outer dom H Hdraw) :
    pointSet (sourcePart R H Hdraw) Hdraw = R.skeletonSet := by
  refine Set.Subset.antisymm (Set.union_subset Set.inter_subset_right
    (Set.iUnion₂_subset fun f hf => edgeArc_subset_of_mem_edgeSet_sourcePart hf)) fun p hp => ?_
  -- A 0-cell is a vertex of `H`, so it survives the vertex restriction.
  rcases Realization.mem_vertexSet_or_exists_cell hp with hv | ⟨e, he, hpe⟩
  · exact Or.inl ⟨hH.vertexSet_subset hv, hp⟩
  -- A vertex of `H` on the skeleton survives the vertex restriction too, wherever it sits.
  by_cases hpV : p ∈ V(H)
  · exact Or.inl ⟨hpV, hp⟩
  -- Otherwise `p` lies on some edge of `H` which meets the open 1-cell away from the vertices.
  rcases hH.skeletonSet_subset hp with hv | hedge
  · exact absurd hv hpV
  obtain ⟨f, hf, hpf⟩ := Set.mem_iUnion₂.1 hedge
  have harc : edgeArc Hdraw f ⊆ R.skeletonSet :=
    (hH.edge_subset he hf hpf hpe hpV).trans
      (Graph.edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph]))
  exact Or.inr (Set.mem_iUnion₂.2
    ⟨f, mem_edgeSet_sourcePart hH hf harc, hpf⟩)

/-- **An extension edge lying on the old skeleton that meets an open old 1-cell runs inside
it.** This recovers, for the edges on which it is *true*, what the pre-repair form of
`IsSourceExtension.edge_subset` asserted of every edge: the weakened field exempts only a touch
at a vertex of `H`, and an edge whose whole arc lies on the old skeleton cannot merely touch —
its arc continues *inside the skeleton* past the meeting point, and near a point of an open
1-cell the skeleton is nothing but that 1-cell, so the arc re-enters the open cell at a
non-vertex parameter and the weakened field fires after all.

This is what keeps the fresh-anchor bookkeeping of `thm:finite-transfer`(b) sound after the
repair: an old skeleton edge cannot end at a fresh boundary point, only a *new* edge can. -/
theorem IsSourceExtension.edge_subset_of_edgeArc_subset_skeletonSet
    (hH : IsSourceExtension R outer dom H Hdraw) {f : γ} (hf : f ∈ E(H))
    (harc : edgeArc Hdraw f ⊆ R.skeletonSet) {e : γ} (he : e ∈ E(S.skel))
    {p : Plane} (hp : p ∈ edgeArc Hdraw f) (hpe : p ∈ R.cell e) :
    edgeArc Hdraw f ⊆ edgeArc R.drawing e := by
  classical
  obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  -- If the arc meets the open 1-cell away from the vertices of `H`, the subdivision clause
  -- closes immediately; the rest of the proof rules the alternative out.
  by_cases hwit : ∃ q, (q ∈ edgeArc Hdraw f ∧ q ∈ R.cell e) ∧ q ∉ V(H)
  · obtain ⟨q, ⟨hq, hqe⟩, hqV⟩ := hwit
    exact hH.edge_subset he hf hq hqe hqV
  push Not at hwit
  exfalso
  -- The closed set the point avoids: the drawn vertices and every other edge's arc.
  set K : Set Plane :=
    V(R.graph) ∪ ⋃ e' ∈ E(S.skel) \ {e}, edgeArc R.drawing e' with hK
  have hKcl : IsClosed K := by
    refine (Graph.finite_vertexSet R.graph).isClosed.union
      (Set.Finite.isClosed_biUnion (S.finite_edgeSet.subset Set.sdiff_subset)
        fun e' he' => ?_)
    exact (R.isDrawing.isCompact_edgeArc
      (by rw [Graph.edgeSet_map]; exact he'.1)).isClosed
  have hparc : p ∈ edgeArc R.drawing e := by rw [R.cell_edge hl] at hpe; exact hpe.1
  -- `p` is not a drawn vertex …
  have hpV : p ∉ V(S.skel.map R.pos) := by
    intro hv
    rcases R.isDrawing.vertex_mem_edgeArc (hl.map R.pos) hv hparc with h | h <;>
      · rw [R.cell_edge hl] at hpe
        exact hpe.2 (by simp [h])
  -- … and on no other edge's arc, so it is off `K`.
  have hpK : p ∉ K := by
    rintro (hv | hedge)
    · exact hpV hv
    · obtain ⟨e', he', hpe'⟩ := Set.mem_iUnion₂.1 hedge
      refine hpV (R.isDrawing.edge_inter
        (by rw [Graph.edgeSet_map]; exact he'.1) (by rw [Graph.edgeSet_map]; exact he)
        (fun h => he'.2 (by simp [h])) hpe' hparc).1
  -- Near `p`, the skeleton is inside the open 1-cell of `e`.
  have hlocal : ∀ ⦃z⦄, z ∈ R.skeletonSet → z ∉ K → z ∈ R.cell e := by
    intro z hz hzK
    rcases hz with hzv | hze
    · exact absurd (Set.mem_union_left _ hzv) hzK
    obtain ⟨e', he', hze'⟩ := Set.mem_iUnion₂.1 hze
    have he'' : e' ∈ E(S.skel) := by rwa [Realization.edgeSet_graph] at he'
    by_cases hee : e' = e
    · subst hee
      rw [R.cell_edge hl]
      refine ⟨hze', fun hmem => hzK (Set.mem_union_left _ ?_)⟩
      have hzxy : z = R.pos x ∨ z = R.pos y := by simpa using hmem
      rw [Realization.vertexSet_graph]
      rcases hzxy with rfl | rfl
      · exact ⟨x, hl.left_mem, rfl⟩
      · exact ⟨y, hl.right_mem, rfl⟩
    · exact absurd (Set.mem_union_right _
        (Set.mem_biUnion (show e' ∈ E(S.skel) \ {e} from
          ⟨he'', fun hs => hee (by simpa using hs)⟩) hze')) hzK
  -- Every meeting point is a vertex of `H`, hence an end parameter of the arc of `f`.
  obtain ⟨hc, hi, hlf⟩ := hH.isDrawing.edge_param hf
  have hend : ∀ ⦃t : ℝ⦄, t ∈ I → Hdraw f t ∈ R.cell e → t = 0 ∨ t = 1 := by
    intro t htI htcell
    have htV : Hdraw f t ∈ V(H) := hwit _ ⟨⟨t, htI, rfl⟩, htcell⟩
    rcases hH.isDrawing.vertex_mem_edgeArc hlf htV ⟨t, htI, rfl⟩ with h | h
    · exact Or.inl (hi htI zero_mem_I h)
    · exact Or.inr (hi htI one_mem_I h)
  obtain ⟨t₀, ht₀, hpt₀⟩ := hp
  have ht₀end : t₀ = 0 ∨ t₀ = 1 := hend ht₀ (by rw [hpt₀]; exact hpe)
  -- The ball around `p` off `K`, and the modulus that keeps the arc of `f` inside it: a
  -- parameter strictly inside the interval and close to the end parameter of `p` lands the
  -- arc in the open 1-cell at a non-vertex, which `hend` forbids.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hKcl.isOpen_compl p hpK
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hc t₀ ht₀) ε hε
  have key : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 → dist t t₀ < δ → False := by
    intro t ht htδ
    have htI : t ∈ I := ⟨ht.1.le, ht.2.le⟩
    have hqK : Hdraw f t ∈ Kᶜ := by
      refine hball ?_
      rw [Metric.mem_ball, ← hpt₀]
      exact hcont htI htδ
    rcases hend htI (hlocal (harc ⟨t, htI, rfl⟩) hqK) with h | h
    · exact ht.1.ne' h
    · exact ht.2.ne h
  have hmin0 : 0 < min (δ / 2) (2⁻¹ : ℝ) := lt_min (by linarith) (by norm_num)
  have hmin2 : min (δ / 2) (2⁻¹ : ℝ) ≤ 2⁻¹ := min_le_right _ _
  have hminδ : min (δ / 2) (2⁻¹ : ℝ) ≤ δ / 2 := min_le_left _ _
  rcases ht₀end with rfl | rfl
  · refine key (min (δ / 2) 2⁻¹) ⟨hmin0, by linarith⟩ ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hmin0]
    linarith
  · refine key (1 - min (δ / 2) 2⁻¹) ⟨by linarith, by linarith⟩ ?_
    rw [Real.dist_eq, abs_of_nonpos (by linarith : (1 : ℝ) - min (δ / 2) 2⁻¹ - 1 ≤ 0)]
    linarith

/-! ### Step 1, assembled on the edge matching alone

Everything except the matching is now in hand, so it is worth recording exactly what is left:
`Schoenflies.CommonSubdivision` follows from the single hypothesis `hmatch` below. That is what
makes the remaining gap one statement rather than a diffuse "the rest of step 1", and it is a
statement about *one* refined stage, not about the induction that produced it. -/

variable {S₀ : CellStructure γ} {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- **Step 1 of `thm:finite-transfer`(a), given the edge matching.**

Subdivide the given pair at every vertex of `H` that lies on `|Γ|` — finitely many points of the
skeleton, so `GeneratedPair.exists_subdivide_finite` does it — and the resulting stage has
exactly the 0-cells of `sourcePart`. Its drawn skeleton is 2-connected for free, being a field
of weak admissibility, and `Graph.IsTwoConnected.of_adj_congr` carries that to `sourcePart` as
soon as the two graphs have the same adjacency.

`hmatch` is that last step. It is **discharged** by `Schoenflies.adj_match` below; the
hypothesis is kept only because it isolates the one thing this assembly needs to know about the
geometry, and keeping the two apart is what makes each of them short. -/
theorem commonSubdivision_of_adj_match [Infinite γ] (h₀ : S₀.CombInvariants)
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hmatch : ∀ T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom,
      T.src.skeletonSet = P.src.skeletonSet →
      V(T.src.graph) = V(sourcePart P.src H Hdraw) →
      ∀ ⦃x y : Plane⦄, T.src.graph.Adj x y ↔ (sourcePart P.src H Hdraw).Adj x y) :
    CommonSubdivision P H Hdraw := by
  haveI := hH.finite
  -- The vertices of `H` on the old skeleton: finitely many points of `|Γ|`.
  have hQfin : (V(H) ∩ P.src.skeletonSet).Finite :=
    (Graph.finite_vertexSet H).inter_of_left _
  obtain ⟨T, par, hrs, hrt, hK, hVold, hVQ, hVsub, hg⟩ :=
    GeneratedPair.exists_subdivide_finite h₀ hQfin P Set.inter_subset_right
  -- Every old 0-cell was already a vertex of `H` on the skeleton, so the new 0-cells are
  -- exactly the vertices of the part.
  have hPQ : V(P.src.graph) ⊆ V(H) ∩ P.src.skeletonSet := fun z hz =>
    ⟨hH.vertexSet_subset hz, Graph.vertexSet_subset_pointSet hz⟩
  have hVeq : V(T.src.graph) = V(sourcePart P.src H Hdraw) :=
    Set.Subset.antisymm (hVsub.trans (Set.union_subset hPQ subset_rfl)) hVQ
  refine ⟨sourcePart P.src H Hdraw, T, par, ?_, sourcePart_le, hrs, hrt, ?_, hVeq.ge,
    fun x _ => by rw [hg]⟩
  · exact Graph.IsTwoConnected.of_adj_congr hVeq (hmatch T hK hVeq)
      T.src_isWeaklyAdmissible.isTwoConnected
  · rw [hK, pointSet_sourcePart hH]

/-! ### The edge matching, and step 1 unconditional

The stage produced above and `sourcePart` are two finite plane graphs occupying the same points
with the same vertices — the first because a subdivision does not move the skeleton, the second
by `pointSet_sourcePart`; the vertices agree because that is what subdividing at every vertex of
`H` on `|Γ|` achieved. `Graph.adj_congr_of_pointSet_eq` says two such graphs have the same
adjacency, and that is the whole of the matching: the open edges of a finite plane graph are the
connected components of what its vertices leave of it, so the edge names carry nothing adjacency
can see. -/

/-- **The edge matching.** A stage whose drawn skeleton occupies `|Γ|` and whose 0-cells are
exactly the vertices of `sourcePart` has the adjacency of `sourcePart`. -/
theorem adj_match {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hK : T.src.skeletonSet = P.src.skeletonSet)
    (hV : V(T.src.graph) = V(sourcePart P.src H Hdraw)) ⦃x y : Plane⦄ :
    T.src.graph.Adj x y ↔ (sourcePart P.src H Hdraw).Adj x y := by
  haveI := hH.finite
  haveI : (sourcePart P.src H Hdraw).Finite := Graph.Finite.of_le sourcePart_le
  haveI := T.src.finite_graph
  -- The ascription matters: `Realization.isDrawing` is stated for `skel.map pos`, and the
  -- `Finite` instance for `T.src.graph`, which is that graph by definition but not by syntax.
  have hd : IsDrawing T.src.graph T.src.drawing := T.src.isDrawing
  exact Graph.adj_congr_of_pointSet_eq hd (hH.isDrawing.mono sourcePart_le)
    (show T.src.skeletonSet = _ by rw [hK, pointSet_sourcePart hH]) hV

/-- **Step 1 of `thm:finite-transfer`(a), unconditional.** `Schoenflies.CommonSubdivision`,
which stood as a named hypothesis in `FiniteTransfer.lean` since the module was written. -/
theorem commonSubdivision [Infinite γ] (h₀ : S₀.CombInvariants)
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw) :
    CommonSubdivision P H Hdraw :=
  commonSubdivision_of_adj_match h₀ P hH fun T hK hV => adj_match hH T hK hV

/-- **`thm:finite-transfer`, direction (a), unconditional.**

`Schoenflies.finite_transfer_toward_square` assumed steps 1 and 3;
`Schoenflies.finite_transfer_toward_square_of_commonSubdivision` discharged step 3, and step 1
is `Schoenflies.commonSubdivision` above. What remains as hypotheses are the four
stage-independent facts about the two ambient domains — `dom ∖ outer` open with frontier inside
`outer` on each side — which `Schoenflies.isOpen_sdiff_outer_of_isSeparating` and its companion
supply for a closed Jordan region, the shape both sides have. -/
theorem finite_transfer_toward_square' [Infinite γ] (h₀ : S₀.CombInvariants)
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    (htgtQ : IsOpen (tgtDom \ tgtOuter)) (htgtFr : frontier (tgtDom \ tgtOuter) ⊆ tgtOuter) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision h₀ hH hsrcQ hsrcFr htgtQ htgtFr
    (commonSubdivision h₀ P hH)

end Schoenflies
