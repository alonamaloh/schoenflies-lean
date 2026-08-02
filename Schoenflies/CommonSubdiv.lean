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
`Γ` runs inside it* — turns "this edge of `H` touches `|Γ|` away from the 0-cells" into "this
edge of `H` lies inside `|Γ|`". That second hypothesis is the whole of "`H` contains a
subdivision of `Γ`" as far as step 1 is concerned: it is what says `H` does not *cross* `Γ`,
so that the blueprint's overlay has, in the Lean formulation, already been performed by the
hypothesis.

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
then the edge of `H` carrying it meets that open 1-cell, so `IsSourceExtension.edge_subset`
puts the whole of that edge inside the 1-cell's arc and therefore inside `|Γ|`. -/
theorem pointSet_sourcePart (hH : IsSourceExtension R outer dom H Hdraw) :
    pointSet (sourcePart R H Hdraw) Hdraw = R.skeletonSet := by
  refine Set.Subset.antisymm (Set.union_subset Set.inter_subset_right
    (Set.iUnion₂_subset fun f hf => edgeArc_subset_of_mem_edgeSet_sourcePart hf)) fun p hp => ?_
  -- A 0-cell is a vertex of `H`, so it survives the vertex restriction.
  rcases Realization.mem_vertexSet_or_exists_cell hp with hv | ⟨e, he, hpe⟩
  · exact Or.inl ⟨hH.vertexSet_subset hv, hp⟩
  -- Otherwise `p` lies on some edge of `H`, and that edge meets the open 1-cell it lies in.
  rcases hH.skeletonSet_subset hp with hv | hedge
  · exact Or.inl ⟨hv, hp⟩
  obtain ⟨f, hf, hpf⟩ := Set.mem_iUnion₂.1 hedge
  have harc : edgeArc Hdraw f ⊆ R.skeletonSet :=
    (hH.edge_subset he hf ⟨p, hpf, hpe⟩).trans
      (Graph.edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph]))
  exact Or.inr (Set.mem_iUnion₂.2
    ⟨f, mem_edgeSet_sourcePart hH hf harc, hpf⟩)

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
