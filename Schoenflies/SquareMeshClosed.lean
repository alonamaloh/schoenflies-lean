/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.LocalGrid
import Schoenflies.SquareCycle

/-!
# The anchored square mesh, closed

`Schoenflies/SquareMesh.lean` builds `Schoenflies.squareMesh δ fresh anchors` and proves the
geometric clauses of `prop:anchored-square-mesh`; `Schoenflies/SquareMeshConnected.lean`,
`Schoenflies/SquareMeshFixed.lean` and `Schoenflies/LocalGrid.lean` add the grid combinatorics,
the outer cycle **conditional on a hypothesis**, and the degenerate cases. This module removes
the hypothesis.

## The hypothesis that is discharged here

`Schoenflies.SubdividesToPath pieces points` says: *the overlay edges lying inside a source
segment are exactly the edges of a path of the overlay from one end of that segment to the
other.* `SquareMeshFixed.lean` states it as an explicit hypothesis, and its docstring says the
theorem does not exist on `main`.

It does exist. `Schoenflies.exists_incWalk_insideEdges` in `Schoenflies/SquareCycle.lean` is
exactly that statement in the vocabulary of `Graph.IsIncWalk` — a walk along which
`dist P.1 ·` strictly increases — and `Graph.IsIncWalk.isPath` turns it into a path. The two
modules were simply never in one import chain: `SquareCycle.lean` was imported only by
`Schoenflies/JordanClosed.lean`. `Schoenflies.subdividesToPath_of_overlay` is the four-line
bridge, and every conditional theorem of `SquareMeshFixed.lean` becomes unconditional.

## The outer cycle, as data

`Schoenflies.meshGraph_outer_cycle` is existential — its own docstring says *"once that
hypothesis is discharged by a theorem exporting the chain as a `def`, this should be restated
with the cycle as data"*. That is done here: `outerCycleEdge`, `outerCycleStart`,
`outerCycleEnd`, `outerCycleThird` and `outerCycleDetour` are `def`s, and the three clauses
are separate lemmas about them. A consumer needing the outer cycle of the mesh takes these
five names, not an `∃` it has to destructure at every use.

## Blueprint

* `subdividesToPath_of_overlay`, `meshSubdividesToPath` — `lem:polygonal-overlay`: the
  subdivision of one source segment is a path of the overlay. This discharges
  `Schoenflies.SubdividesToPath`.
* `meshGraph_outer_cycle_of_mem_modelCurve`, `squareMesh_outer_cycle_unconditional` —
  `prop:anchored-square-mesh` clause 3 as a **cycle**, with no hypothesis beyond
  `fresh ⊆ S`.
* `outerCycleEdge`, `outerCycleStart`, `outerCycleEnd`, `outerCycleThird`, `outerCycleDetour`,
  `squareMesh_isLongCycle_outerCycle`, `squareMesh_outerCycle_subset_modelCurve`,
  `squareMesh_outerCycle_edgesCover` — the same cycle as data with its clauses as lemmas.
* `squareMesh_outerCycleGraph_isTwoConnected_unconditional` — the first step of clause 5.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### `SubdividesToPath` is a theorem

The membership clause of `Schoenflies.SubdividesToPath` and the membership clause of
`Schoenflies.insideEdges` are the same statement: `Q ∈ E(overlayGraph pieces points)` unfolds
to `Q ∈ overlayPieces pieces points` by `Iff.rfl`. So the only work is to turn the increasing
walk into a path, which `Graph.IsIncWalk.isPath` does. -/

/-- **The subdivision of a source segment is a path of the overlay.** This is
`Schoenflies.SubdividesToPath`, the hypothesis `Schoenflies/SquareMeshFixed.lean` carries
through all of its results, proved from `Schoenflies.exists_incWalk_insideEdges`. -/
theorem subdividesToPath_of_overlay {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points) : SubdividesToPath pieces points := by
  intro P hP hPnd
  obtain ⟨W, hW, hinc⟩ := exists_incWalk_insideEdges hnd hEnds hMeets hP hPnd
  exact ⟨W, hinc.isPath, hW⟩

/-- The mesh's own instance of `Schoenflies.SubdividesToPath`. -/
theorem meshSubdividesToPath {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
  subdividesToPath_of_overlay (meshSegments_nondeg hN hfresh)
    (meshPoints_endsAreCut N fresh anchors) (meshPoints_meetsAreCut N fresh anchors)

/-! ### The outer cycle, with no hypothesis -/

/-- **Clause 3 as a cycle**, for `meshGraph`, unconditionally. -/
theorem meshGraph_outer_cycle_of_mem_modelCurve {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  meshGraph_outer_cycle hN hfresh anchors (meshSubdividesToPath hN hfresh anchors)

/-- **Clause 3 as a cycle**, for `squareMesh`, unconditionally. -/
theorem squareMesh_outer_cycle_unconditional {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (squareMesh δ fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  squareMesh_outer_cycle hfresh δ anchors
    (meshSubdividesToPath (two_le_meshCount δ) hfresh anchors)

/-- The outer cycle is a 2-connected subgraph of the mesh, unconditionally. -/
theorem squareMesh_outerCycleGraph_isTwoConnected_unconditional {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∃ (e : Piece) (u : Plane) (D : List Piece),
      ((squareMesh δ fresh anchors).cycleGraph u e D).IsTwoConnected ∧
        Graph.edgesCover segmentDrawing (e :: D) = modelCurve :=
  squareMesh_outer_cycleGraph_isTwoConnected hfresh δ anchors
    (meshSubdividesToPath (two_le_meshCount δ) hfresh anchors)

/-! ### The outer cycle as data

Five `def`s and three lemmas, replacing the five-fold existential above. The `dite` is what
makes the definition total: the hypothesis `fresh ⊆ S` is not available inside a `def`, so the
data is junk when it fails and the lemmas carry the hypothesis. -/

open scoped Classical in
/-- The outer cycle of the mesh, as a tuple `(e, u, v, w, D)`: the distinguished edge, its two
ends, the third vertex, and the detour. Junk when `fresh ⊄ S`. -/
noncomputable def outerCycleData (δ : ℝ) (fresh anchors : List Plane) :
    Piece × Plane × Plane × Plane × List Piece :=
  if h : ∃ t : Piece × Plane × Plane × Plane × List Piece,
      (squareMesh δ fresh anchors).IsLongCycle t.1 t.2.1 t.2.2.1 t.2.2.2.2 t.2.2.2.1 ∧
        (∀ Q ∈ t.1 :: t.2.2.2.2, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (t.1 :: t.2.2.2.2) = modelCurve
    then h.choose else ((0, 0), 0, 0, 0, [])

/-- The distinguished edge of the outer cycle. -/
noncomputable def outerCycleEdge (δ : ℝ) (fresh anchors : List Plane) : Piece :=
  (outerCycleData δ fresh anchors).1

/-- The vertex the outer cycle starts at: one end of `outerCycleEdge`. -/
noncomputable def outerCycleStart (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.1

/-- The other end of `outerCycleEdge`, where the detour ends. -/
noncomputable def outerCycleEnd (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.2.1

/-- A third vertex of the outer cycle, distinct from its two named ones: this is what makes the
cycle *long*, hence 2-connected. -/
noncomputable def outerCycleThird (δ : ℝ) (fresh anchors : List Plane) : Plane :=
  (outerCycleData δ fresh anchors).2.2.2.1

/-- The detour of the outer cycle: the path from `outerCycleStart` to `outerCycleEnd` avoiding
`outerCycleEdge`. -/
noncomputable def outerCycleDetour (δ : ℝ) (fresh anchors : List Plane) : List Piece :=
  (outerCycleData δ fresh anchors).2.2.2.2

theorem outerCycleData_spec {fresh : List Plane} (hfresh : ∀ z ∈ fresh, z ∈ modelCurve)
    (δ : ℝ) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsLongCycle (outerCycleEdge δ fresh anchors)
        (outerCycleStart δ fresh anchors) (outerCycleEnd δ fresh anchors)
        (outerCycleDetour δ fresh anchors) (outerCycleThird δ fresh anchors) ∧
      (∀ Q ∈ outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors,
        Q.seg ⊆ modelCurve) ∧
      Graph.edgesCover segmentDrawing
        (outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors) = modelCurve := by
  classical
  have h : ∃ t : Piece × Plane × Plane × Plane × List Piece,
      (squareMesh δ fresh anchors).IsLongCycle t.1 t.2.1 t.2.2.1 t.2.2.2.2 t.2.2.2.1 ∧
        (∀ Q ∈ t.1 :: t.2.2.2.2, Q.seg ⊆ modelCurve) ∧
        Graph.edgesCover segmentDrawing (t.1 :: t.2.2.2.2) = modelCurve := by
    obtain ⟨e, u, v, x, D, h₁, h₂, h₃⟩ := squareMesh_outer_cycle_unconditional hfresh δ anchors
    exact ⟨(e, u, v, x, D), h₁, h₂, h₃⟩
  have hd : outerCycleData δ fresh anchors = h.choose := dif_pos h
  simpa [outerCycleEdge, outerCycleStart, outerCycleEnd, outerCycleThird, outerCycleDetour, hd]
    using h.choose_spec

/-- **Clause 3, as data.** The edge, the two ends, the third vertex and the detour form a long
cycle of the mesh. -/
theorem squareMesh_isLongCycle_outerCycle {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    (squareMesh δ fresh anchors).IsLongCycle (outerCycleEdge δ fresh anchors)
      (outerCycleStart δ fresh anchors) (outerCycleEnd δ fresh anchors)
      (outerCycleDetour δ fresh anchors) (outerCycleThird δ fresh anchors) :=
  (outerCycleData_spec hfresh δ anchors).1

/-- Every edge of the outer cycle lies on `S`. -/
theorem squareMesh_outerCycle_subset_modelCurve {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ∀ Q ∈ outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors,
      Q.seg ⊆ modelCurve :=
  (outerCycleData_spec hfresh δ anchors).2.1

/-- The outer cycle occupies exactly `S`. -/
theorem squareMesh_outerCycle_edgesCover {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    Graph.edgesCover segmentDrawing
      (outerCycleEdge δ fresh anchors :: outerCycleDetour δ fresh anchors) = modelCurve :=
  (outerCycleData_spec hfresh δ anchors).2.2

/-- The outer cycle, as a subgraph, is 2-connected. -/
theorem squareMesh_outerCycleGraph_isTwoConnected {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (δ : ℝ) (anchors : List Plane) :
    ((squareMesh δ fresh anchors).cycleGraph (outerCycleStart δ fresh anchors)
      (outerCycleEdge δ fresh anchors) (outerCycleDetour δ fresh anchors)).IsTwoConnected :=
  (squareMesh_isLongCycle_outerCycle hfresh δ anchors).isTwoConnected

end Schoenflies
