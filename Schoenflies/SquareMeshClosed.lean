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

/-! ### The four sides of a ring of arbitrary radius

`Schoenflies/SquareMeshFixed.lean` names the four sides of the *outer* ring — `sideT`, `sideL`,
`sideB`, `sideR` — and proves the handful of coordinate facts that the outer-cycle argument
runs on. Every inner ring needs the same facts, so they are restated here with the radius as a
parameter; `rsideT 1 = sideT` and so on, definitionally. -/

/-- The top side of the ring of radius `r`, from the north-east corner to the north-west one. -/
def rsideT (r : ℝ) : Piece := (Plane.mk r r, Plane.mk (-r) r)

/-- The left side of the ring of radius `r`, from north-west to south-west. -/
def rsideL (r : ℝ) : Piece := (Plane.mk (-r) r, Plane.mk (-r) (-r))

/-- The bottom side of the ring of radius `r`, from south-west to south-east. -/
def rsideB (r : ℝ) : Piece := (Plane.mk (-r) (-r), Plane.mk r (-r))

/-- The right side of the ring of radius `r`, from south-east back to north-east. -/
def rsideR (r : ℝ) : Piece := (Plane.mk r (-r), Plane.mk r r)

theorem rsideT_one : rsideT 1 = sideT := rfl
theorem rsideL_one : rsideL 1 = sideL := rfl
theorem rsideB_one : rsideB 1 = sideB := rfl
theorem rsideR_one : rsideR 1 = sideR := rfl

theorem rsideT_mem_ringPieces (r : ℝ) : rsideT r ∈ ringPieces r := by
  simp [ringPieces, rsideT]

theorem rsideL_mem_ringPieces (r : ℝ) : rsideL r ∈ ringPieces r := by
  simp [ringPieces, rsideL]

theorem rsideB_mem_ringPieces (r : ℝ) : rsideB r ∈ ringPieces r := by
  simp [ringPieces, rsideB]

theorem rsideR_mem_ringPieces (r : ℝ) : rsideR r ∈ ringPieces r := by
  simp [ringPieces, rsideR]

theorem mem_rsideT {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg) : x 1 = r :=
  (mem_segment_horiz.1 h).1

theorem mem_rsideB {r : ℝ} {x : Plane} (h : x ∈ (rsideB r).seg) : x 1 = -r :=
  (mem_segment_horiz.1 h).1

theorem mem_rsideL {r : ℝ} {x : Plane} (h : x ∈ (rsideL r).seg) : x 0 = -r :=
  (mem_segment_vert.1 h).1

theorem mem_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideR r).seg) : x 0 = r :=
  (mem_segment_vert.1 h).1

theorem rsideT_inter_rsideL {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideL r).seg) : x = Plane.mk (-r) r :=
  plane_eq_of_coords (by rw [mem_rsideL h', Plane.mk_zero]) (by rw [mem_rsideT h, Plane.mk_one])

theorem rsideL_inter_rsideB {r : ℝ} {x : Plane} (h : x ∈ (rsideL r).seg)
    (h' : x ∈ (rsideB r).seg) : x = Plane.mk (-r) (-r) :=
  plane_eq_of_coords (by rw [mem_rsideL h, Plane.mk_zero]) (by rw [mem_rsideB h', Plane.mk_one])

theorem rsideB_inter_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideB r).seg)
    (h' : x ∈ (rsideR r).seg) : x = Plane.mk r (-r) :=
  plane_eq_of_coords (by rw [mem_rsideR h', Plane.mk_zero]) (by rw [mem_rsideB h, Plane.mk_one])

theorem rsideT_inter_rsideR {r : ℝ} {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideR r).seg) : x = Plane.mk r r :=
  plane_eq_of_coords (by rw [mem_rsideR h', Plane.mk_zero]) (by rw [mem_rsideT h, Plane.mk_one])

theorem rsideT_disjoint_rsideB {r : ℝ} (hr : 0 < r) {x : Plane} (h : x ∈ (rsideT r).seg)
    (h' : x ∈ (rsideB r).seg) : False := by
  have := (mem_rsideT h).symm.trans (mem_rsideB h'); linarith

theorem rsideL_disjoint_rsideR {r : ℝ} (hr : 0 < r) {x : Plane} (h : x ∈ (rsideL r).seg)
    (h' : x ∈ (rsideR r).seg) : False := by
  have := (mem_rsideL h).symm.trans (mem_rsideR h'); linarith

/-- The four sides of the ring of radius `r` occupy that ring. -/
theorem rsides_cover {r : ℝ} (hr : 0 ≤ r) :
    (rsideT r).seg ∪ (rsideL r).seg ∪ (rsideB r).seg ∪ (rsideR r).seg = ringSet r := by
  rw [← cover_ringPieces hr]
  simp only [ringPieces, cover_cons, cover_nil, Set.union_empty, rsideT, rsideL, rsideB, rsideR]
  ext z
  simp only [Set.mem_union]
  tauto

theorem rside_seg_subset_ringSet {r : ℝ} (hr : 0 ≤ r) {P : Piece}
    (h : P = rsideT r ∨ P = rsideL r ∨ P = rsideB r ∨ P = rsideR r) : P.seg ⊆ ringSet r := by
  rw [← rsides_cover hr]
  rcases h with rfl | rfl | rfl | rfl
  exacts [fun x hx => Or.inl (Or.inl (Or.inl hx)), fun x hx => Or.inl (Or.inl (Or.inr hx)),
    fun x hx => Or.inl (Or.inr hx), fun x hx => Or.inr hx]

/-- Every side of every ring of the mesh is a mesh segment. -/
theorem ring_ringPieces_mem {N : ℕ} {fresh : List Plane} {r : ℝ} (hr : r ∈ meshRadii N)
    {R : Piece} (hR : R ∈ ringPieces r) : R ∈ meshSegments N fresh :=
  mem_meshSegments.2 (Or.inl ⟨r, hr, hR⟩)

/-! ### Every ring of the mesh is a cycle

`Schoenflies.meshGraph_outer_cycle` proves this for the outer ring, `r = 1`, and every step of
its proof is about the four sides of that ring and nothing else. With the sides of a ring of
arbitrary radius now available, the same argument runs verbatim at every radius: the four sides
are four overlay paths, three concatenations glue them into one path once round the ring, and
the last edge of the fourth is peeled off to close the cycle.

This is the theorem the blueprint's *"adding these finitely many cycles one at a time"* needs
for the inner rings, and which `Schoenflies/SquareMeshFixed.lean` names as missing. -/

/-- **Every ring of the mesh is a long cycle of the mesh graph**, and its edges occupy exactly
that ring.

For `r = 1` this is `Schoenflies.meshGraph_outer_cycle`; the content added here is that the
statement holds at every radius of `Schoenflies.meshRadii`, which is what the assembly of
clause 5 of `prop:anchored-square-mesh` consumes. -/
theorem meshGraph_ring_cycle {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ z ∈ fresh, z ∈ modelCurve) (anchors : List Plane) {r : ℝ}
    (hr : r ∈ meshRadii N) :
    ∃ (e : Piece) (u v x : Plane) (D : List Piece),
      (meshGraph N fresh anchors).IsLongCycle e u v D x ∧
        (∀ Q ∈ e :: D, Q.seg ⊆ ringSet r) ∧
        Graph.edgesCover segmentDrawing (e :: D) = ringSet r := by
  have hrpos : 0 < r := meshRadii_pos hN hr
  have hsub : SubdividesToPath (meshSegments N fresh) (meshPoints N fresh anchors) :=
    meshSubdividesToPath hN hfresh anchors
  have hmemT := ring_ringPieces_mem (fresh := fresh) hr (rsideT_mem_ringPieces r)
  have hmemL := ring_ringPieces_mem (fresh := fresh) hr (rsideL_mem_ringPieces r)
  have hmemB := ring_ringPieces_mem (fresh := fresh) hr (rsideB_mem_ringPieces r)
  have hmemR := ring_ringPieces_mem (fresh := fresh) hr (rsideR_mem_ringPieces r)
  obtain ⟨WT, hpT, hcT⟩ := hsub _ hmemT (ringPieces_nondeg hrpos _ (rsideT_mem_ringPieces r))
  obtain ⟨WL, hpL, hcL⟩ := hsub _ hmemL (ringPieces_nondeg hrpos _ (rsideL_mem_ringPieces r))
  obtain ⟨WB, hpB, hcB⟩ := hsub _ hmemB (ringPieces_nondeg hrpos _ (rsideB_mem_ringPieces r))
  obtain ⟨WR, hpR, hcR⟩ := hsub _ hmemR (ringPieces_nondeg hrpos _ (rsideR_mem_ringPieces r))
  have hsegT : ∀ Q ∈ WT, Q.seg ⊆ (rsideT r).seg := fun Q hQ => ((hcT Q).1 hQ).2
  have hsegL : ∀ Q ∈ WL, Q.seg ⊆ (rsideL r).seg := fun Q hQ => ((hcL Q).1 hQ).2
  have hsegB : ∀ Q ∈ WB, Q.seg ⊆ (rsideB r).seg := fun Q hQ => ((hcB Q).1 hQ).2
  have hsegR : ∀ Q ∈ WR, Q.seg ⊆ (rsideR r).seg := fun Q hQ => ((hcR Q).1 hQ).2
  -- the vertices each side path visits stay on that side
  have hVT : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideT r).1 WT,
      x ∈ (rsideT r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegT hx
  have hVL : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideL r).1 WL,
      x ∈ (rsideL r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegL hx
  have hVB : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideB r).1 WB,
      x ∈ (rsideB r).seg := fun x hx =>
    walkVertices_subset_of_edges (left_mem_segment ℝ _ _) hsegB hx
  -- top, then left
  have hp1 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 (WT ++ WL) (rsideL r).2 :=
    hpT.append_of_disjoint hpL fun x hx hx2 => rsideT_inter_rsideL (hVT x hx) (hVL x hx2)
  have hV1 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      (rsideT r).1 (WT ++ WL), x ∈ (rsideT r).seg ∪ (rsideL r).seg := by
    refine fun x hx => walkVertices_subset_of_edges (Or.inl (left_mem_segment ℝ _ _))
      (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    exacts [(hsegT Q h).trans Set.subset_union_left, (hsegL Q h).trans Set.subset_union_right]
  -- … then the bottom
  have hp2 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 ((WT ++ WL) ++ WB) (rsideB r).2 := by
    refine hp1.append_of_disjoint hpB fun x hx hx2 => ?_
    rcases hV1 x hx with h | h
    · exact absurd (rsideT_disjoint_rsideB hrpos h (hVB x hx2)) not_false
    · exact rsideL_inter_rsideB h (hVB x hx2)
  have hV2 : ∀ x ∈ (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices
      (rsideT r).1 ((WT ++ WL) ++ WB),
      x ∈ (rsideT r).seg ∪ (rsideL r).seg ∪ (rsideB r).seg := by
    refine fun x hx => walkVertices_subset_of_edges
      (Or.inl (Or.inl (left_mem_segment ℝ _ _))) (fun Q hQ => ?_) hx
    rcases List.mem_append.1 hQ with h | h
    · rcases List.mem_append.1 h with h' | h'
      exacts [(hsegT Q h').trans (Set.subset_union_left.trans Set.subset_union_left),
        (hsegL Q h').trans (Set.subset_union_right.trans Set.subset_union_left)]
    · exact (hsegB Q h).trans Set.subset_union_right
  -- the right side, read backwards, so that its last edge is its first step
  have hRne : (rsideR r).1 ≠ (rsideR r).2 := ringPieces_nondeg hrpos _ (rsideR_mem_ringPieces r)
  have hWRne : WR ≠ [] := by
    rintro rfl
    exact hRne hpR.isWalk.eq_of_nil
  obtain ⟨eR, L, hL⟩ := List.exists_cons_of_ne_nil
    (show WR.reverse ≠ [] by simpa using hWRne)
  have hpRrev := hpR.reverse
  rw [hL] at hpRrev
  obtain ⟨w, hlink, htail, hfr⟩ := hpRrev.cons_cases
  have heRmem : eR ∈ WR := by
    rw [← List.mem_reverse, hL]; exact List.mem_cons_self ..
  have hLmem : ∀ Q ∈ L, Q ∈ WR := fun Q hQ => by
    rw [← List.mem_reverse, hL]; exact List.mem_cons_of_mem _ hQ
  have hwR : w ∈ (rsideR r).seg := by
    rcases hlink.2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsegR eR heRmem (right_mem_segment ℝ _ _),
      hsegR eR heRmem (left_mem_segment ℝ _ _)]
  have hVRtail : ∀ x ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices w L, x ∈ (rsideR r).seg := fun x hx =>
    walkVertices_subset_of_edges hwR (fun Q hQ => hsegR Q (hLmem Q hQ)) hx
  have hrevV : (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices (rsideB r).2 L.reverse
      = (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).walkVertices w L :=
    htail.isWalk.reverse_walkVertices
  -- the fourth append: what is left of the right side, from the south-east corner
  have hp3 : (overlayGraph (meshSegments N fresh) (meshPoints N fresh anchors)).IsPath
      (rsideT r).1 (((WT ++ WL) ++ WB) ++ L.reverse) w := by
    refine hp2.append_of_disjoint htail.reverse fun x hx hx2 => ?_
    rw [hrevV] at hx2
    have hxR : x ∈ (rsideR r).seg := hVRtail x hx2
    rcases hV2 x hx with (h | h) | h
    · refine absurd (show (rsideR r).2 ∈ (overlayGraph (meshSegments N fresh)
        (meshPoints N fresh anchors)).walkVertices w L from ?_) hfr
      rwa [show (rsideR r).2 = x from (rsideT_inter_rsideR h hxR).symm]
    · exact absurd (rsideL_disjoint_rsideR hrpos h hxR) not_false
    · exact rsideB_inter_rsideR h hxR
  -- the closing edge is not one of the others
  have hnondegR : eR.Nondeg :=
    meshGraph_edge_nondeg (anchors := anchors) hN hfresh ((hcR eR).1 heRmem).1
  have hnotT : eR ∉ WT := fun hmem => hnondegR (by
    have h1 := rsideT_inter_rsideR (hsegT eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := rsideT_inter_rsideR (hsegT eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotL : eR ∉ WL := fun hmem =>
    rsideL_disjoint_rsideR hrpos (hsegL eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
  have hnotB : eR ∉ WB := fun hmem => hnondegR (by
    have h1 := rsideB_inter_rsideR (hsegB eR hmem (left_mem_segment ℝ _ _))
      (hsegR eR heRmem (left_mem_segment ℝ _ _))
    have h2 := rsideB_inter_rsideR (hsegB eR hmem (right_mem_segment ℝ _ _))
      (hsegR eR heRmem (right_mem_segment ℝ _ _))
    exact h1.trans h2.symm)
  have hnotLrev : eR ∉ L.reverse := by
    have hnodup : (eR :: L).Nodup := hL ▸ hpR.reverse.nodup
    rw [List.mem_reverse]
    exact (List.nodup_cons.1 hnodup).1
  have hnotD : eR ∉ ((WT ++ WL) ++ WB) ++ L.reverse := by
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · rcases List.mem_append.1 h with h' | h'
      · rcases List.mem_append.1 h' with h'' | h''
        exacts [hnotT h'', hnotL h'']
      · exact hnotB h'
    · exact hnotLrev h
  -- every edge of the cycle lies on the ring
  have hmT : (rsideT r).seg ⊆ ringSet r := rside_seg_subset_ringSet hrpos.le (Or.inl rfl)
  have hmL : (rsideL r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inl rfl))
  have hmB : (rsideB r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inr (Or.inl rfl)))
  have hmR : (rsideR r).seg ⊆ ringSet r :=
    rside_seg_subset_ringSet hrpos.le (Or.inr (Or.inr (Or.inr rfl)))
  have hsegsAll : ∀ Q ∈ eR :: (((WT ++ WL) ++ WB) ++ L.reverse), Q.seg ⊆ ringSet r := by
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | h
    · exact (hsegR Q heRmem).trans hmR
    rcases List.mem_append.1 h with h' | h'
    · rcases List.mem_append.1 h' with h'' | h''
      · rcases List.mem_append.1 h'' with h3 | h3
        exacts [(hsegT Q h3).trans hmT, (hsegL Q h3).trans hmL]
      · exact (hsegB Q h'').trans hmB
    · exact (hsegR Q (hLmem Q (List.mem_reverse.1 h'))).trans hmR
  -- a third vertex on the cycle: the north-west corner, where the top side meets the left one
  have hthird : (rsideT r).2 ∈ (overlayGraph (meshSegments N fresh)
      (meshPoints N fresh anchors)).walkVertices (rsideT r).1
        (((WT ++ WL) ++ WB) ++ L.reverse) :=
    Graph.walkVertices_mono
      (List.Subset.trans (List.subset_append_left _ _)
        (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _)))
      hpT.isWalk.target_mem_walkVertices
  have hne₁ : (rsideT r).2 ≠ (rsideT r).1 :=
    mk_ne_mk_of_fst (by intro h; linarith)
  have hne₂ : (rsideT r).2 ≠ w := by
    intro h
    have hw := mem_rsideR (h ▸ hwR)
    rw [rsideT, Plane.mk_zero] at hw
    linarith
  refine ⟨eR, (rsideT r).1, w, (rsideT r).2, ((WT ++ WL) ++ WB) ++ L.reverse,
    ⟨⟨hlink, hp3, hnotD⟩, hthird, hne₁, hne₂⟩, hsegsAll, ?_⟩
  have hcovT : Graph.edgesCover segmentDrawing WT = (rsideT r).seg := edgesCover_eq_seg hmemT hcT
  have hcovL : Graph.edgesCover segmentDrawing WL = (rsideL r).seg := edgesCover_eq_seg hmemL hcL
  have hcovB : Graph.edgesCover segmentDrawing WB = (rsideB r).seg := edgesCover_eq_seg hmemB hcB
  have hcovR : Graph.edgesCover segmentDrawing WR = (rsideR r).seg := edgesCover_eq_seg hmemR hcR
  refine subset_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
    rw [edgeArc_segmentDrawing] at hzQ
    exact hsegsAll Q hQ hzQ
  · rw [← rsides_cover hrpos.le] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · rw [← hcovT] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hQ)))) hzQ
    · rw [← hcovL] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hQ)))) hzQ
    · rw [← hcovB] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      exact Graph.mem_edgesCover (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_append_right _ hQ))) hzQ
    · rw [← hcovR] at hz
      obtain ⟨Q, hQ, hzQ⟩ := Graph.mem_edgesCover_iff.1 hz
      rw [← List.mem_reverse, hL] at hQ
      rcases List.mem_cons.1 hQ with rfl | hQ'
      · exact Graph.mem_edgesCover List.mem_cons_self hzQ
      · exact Graph.mem_edgesCover (List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_reverse.2 hQ'))) hzQ

end Schoenflies
