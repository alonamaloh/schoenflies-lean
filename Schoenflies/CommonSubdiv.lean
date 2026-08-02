/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SubdivPoints
import Schoenflies.EarStep
import Schoenflies.Graph.AdjCongr

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

## What is still missing, and what it is missing for

The third clause, `K.IsTwoConnected`, is **not** proved here. The route is settled and its two
halves are in place:

* `Graph.IsTwoConnected.of_adj_congr` (`Schoenflies/Graph/AdjCongr.lean`) transports
  2-connectivity between two graphs on the same vertex set with the same adjacency, across a
  change of edge *names* — which is the only obstruction, since 2-connectivity of the realized
  skeleton is a field of `IsWeaklyAdmissible` and so is free at every stage;
* `GeneratedPair.exists_subdivide_finite` (`Schoenflies/SubdivPoints.lean`) produces the stage
  whose 0-cells are exactly the old ones together with `V(H) ∩ |Γ|`, i.e. `V(sourcePart)`.

What is missing between them is the **edge matching**: that after subdividing at every vertex of
`H` on `|Γ|`, each drawn 1-cell of the new stage is the arc of exactly one edge of
`sourcePart`, and conversely — hence the two graphs have the same adjacency. That is an
ordering argument along one drawn edge of `Γ`: both an edge of `sourcePart` and a drawn 1-cell
of the refined stage are sub-arcs of the same ambient arc whose interiors avoid the same finite
set of marked points, and two such sub-arcs meeting are equal. `IsArcBetween.eq_of_subset` and
`Schoenflies.subarc_subset_of_isPreconnected` (`PolygonalCut.lean`) are the tools; nothing of it
is written yet.

## Blueprint

* `Schoenflies.sourcePart` — the subgraph the blueprint's step 1 subdivides `Γ` to match.
* `Schoenflies.pointSet_sourcePart` — "the old skeleton is literally a subgraph of the overlay",
  on the source side and at the level of point sets.
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

`hmatch` is that last step and is the only thing assumed. It says: a stage whose skeleton is
still `|Γ|` and whose 0-cells are exactly the vertices of `sourcePart` has the adjacency of
`sourcePart`. Both directions are the same ordering argument along one drawn edge of `Γ` — see
the module docstring — and neither is proved yet. It is a statement about arcs of a single
plane graph, believed and discharged by a later module; it is not a restatement of the goal,
since it says nothing about cell structures being generated, refined, or matched. -/
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
  obtain ⟨T, par, hrs, hrt, hK, hVold, hVQ, hVsub⟩ :=
    GeneratedPair.exists_subdivide_finite h₀ hQfin P Set.inter_subset_right
  -- Every old 0-cell was already a vertex of `H` on the skeleton, so the new 0-cells are
  -- exactly the vertices of the part.
  have hPQ : V(P.src.graph) ⊆ V(H) ∩ P.src.skeletonSet := fun z hz =>
    ⟨hH.vertexSet_subset hz, Graph.vertexSet_subset_pointSet hz⟩
  have hVeq : V(T.src.graph) = V(sourcePart P.src H Hdraw) :=
    Set.Subset.antisymm (hVsub.trans (Set.union_subset hPQ subset_rfl)) hVQ
  refine ⟨sourcePart P.src H Hdraw, T, par, ?_, sourcePart_le, hrs, hrt, ?_, hVeq.ge⟩
  · exact Graph.IsTwoConnected.of_adj_congr hVeq (hmatch T hK hVeq)
      T.src_isWeaklyAdmissible.isTwoConnected
  · rw [hK, pointSet_sourcePart hH]

/-- **`thm:finite-transfer`, direction (a), on the edge matching alone.**

`Schoenflies.finite_transfer_toward_square` assumed steps 1 and 3;
`Schoenflies.finite_transfer_toward_square_of_commonSubdivision` discharged step 3. This
discharges everything of step 1 except the edge matching, so the whole of direction (a) now
rests on `hmatch` and on four stage-independent facts about the two ambient domains — which
`Schoenflies.isOpen_sdiff_outer_of_isSeparating` and its companion supply for a closed Jordan
region, the shape both sides have. -/
theorem finite_transfer_toward_square_of_adj_match [Infinite γ] (h₀ : S₀.CombInvariants)
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hH : IsSourceExtension P.src srcOuter srcDom H Hdraw)
    (hsrcQ : IsOpen (srcDom \ srcOuter)) (hsrcFr : frontier (srcDom \ srcOuter) ⊆ srcOuter)
    (htgtQ : IsOpen (tgtDom \ tgtOuter)) (htgtFr : frontier (tgtDom \ tgtOuter) ⊆ tgtOuter)
    (hmatch : ∀ T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom,
      T.src.skeletonSet = P.src.skeletonSet →
      V(T.src.graph) = V(sourcePart P.src H Hdraw) →
      ∀ ⦃x y : Plane⦄, T.src.graph.Adj x y ↔ (sourcePart P.src H Hdraw).Adj x y) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTransferOf T P H Hdraw par :=
  finite_transfer_toward_square_of_commonSubdivision h₀ hH hsrcQ hsrcFr htgtQ htgtFr
    (commonSubdivision_of_adj_match h₀ P hH hmatch)

end Schoenflies
