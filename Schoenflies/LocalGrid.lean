/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SquareMeshFixed
import Schoenflies.Graph.TwoPaths

/-!
# The local source grid, and the missing hypothesis of the anchored square mesh

Two things, and the second is the more important.

## 1. `prop:anchored-square-mesh` clause 5 — which hypothesis repairs it

`docs/ROADMAP.md` records clause 5, *the skeleton of `T` is 2-connected*, as **false** for
`Schoenflies.squareMesh` when the fresh-point set is too small, and names
`Schoenflies.FreshDense` as "the shape the missing hypothesis should take". The first section
of this module checks that, and the answer is **no: `FreshDense` alone does not repair
clause 5.**

* `Schoenflies.freshDense_of_four_sqrt_two_le` — for `4√2 ≤ δ`, `FreshDense fresh δ` holds for
  **every** list `fresh`, the empty one included, because `S` itself has diameter `2√2`. So
  `FreshDense fresh δ` is vacuous at large `δ` and excludes nothing.
* `Schoenflies.freshDense_not_isTwoConnected` — the counterexample made formal: at
  `δ = 4√2` the hypotheses `0 < δ` and `FreshDense [] δ` both hold and
  `squareMesh δ [] anchors` is still not 2-connected.

What does repair it is `FreshDense` **together with a bound on `δ`**:

* `Schoenflies.exists_two_distinct_fresh_of_freshDense` — `FreshDense fresh δ` and `δ < 4`
  force two distinct fresh points. (`4` is not the sharp constant — `4√2` is — but it is the
  one a side of `S`, whose two ends are `2` apart, gives with no work. The blueprint's own
  `δ = ε_n = 2^{-n}` is far below either.)

and two distinct fresh points is exactly the right amount, because *fewer* is always fatal:

* `Schoenflies.not_isTwoConnected_meshGraph_of_fresh_subsingleton` — a mesh whose fresh points
  are not two distinct points is **never** 2-connected. This closes the case
  `SquareMeshFixed.lean` left open in prose: with exactly one fresh point `z` the mesh is
  connected, but `z` is a cut vertex, because the spoke at `z` is the only edge of the mesh
  that changes the sup norm and every other edge preserves it.

So the correct statement of clause 5 carries the hypothesis `∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w`,
which `FreshDense fresh δ ∧ δ < 4` supplies, and which is necessary as well as sufficient in
the degenerate range.

## 2. `prop:local-grid-attachment` — the grid

The blueprint's proof begins: *"Choose sufficiently fine finite horizontal and vertical
coordinate sets in `W`, with at least two intervals in each direction. Begin with the outer
rectangle of the resulting grid `K` … By `lem:subdivision-ear-preserve`, `K` is 2-connected."*

`Schoenflies.localGrid` is that `K`, as a `def`: the uniform `k × k` grid on the closed square
`W` of centre `p` and radius `s`. `Schoenflies/SquareMeshConnected.lean` and
`Schoenflies/SquareMeshFixed.lean` supply everything combinatorial about a grid, so what is
added here is the *quantitative* clause the proposition needs — every closed grid rectangle has
diameter `< ε` — together with the instantiation of the general grid lemmas at these
coordinates.

The rest of `prop:local-grid-attachment` — the overlay of `K` with the polygonal nonboundary
skeleton of `Γ`, the three cases, and the component-joining loop — is **not** here; see the
report.

## Blueprint

* `prop:anchored-square-mesh`, clause 5 — `freshDense_of_four_sqrt_two_le`,
  `freshDense_not_isTwoConnected`, `exists_two_distinct_fresh_of_freshDense`,
  `not_isTwoConnected_meshGraph_of_fresh_subsingleton`,
  `not_isTwoConnected_squareMesh_of_fresh_subsingleton`.
* `prop:local-grid-attachment`, the grid `K` — `localGrid`, `localGrid_isTwoConnected`,
  `localGrid_subdivide_isTwoConnected`, `localGrid_isDrawing`, `localGrid_outer_cycle`,
  `diam_localGridCell_lt`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union` and
  `Graph.IsTwoConnected.ear`; `Graph.IsTwoConnected.of_le_of_vertexSet_subset` is the
  "spanning 2-connected subgraph" form the assembly needs.
-/

open Metric Set
open scoped Graph

namespace Schoenflies

/-! ### The diameter of `S`

`S = modelCurve` is the frame of `[-1,1]²`, so any two of its points are at sup distance at
most `2` and hence at Euclidean distance at most `2√2`. That single bound is what makes
`FreshDense fresh δ` vacuous once `δ ≥ 4√2`. -/

/-- The sup distance is at most the Euclidean distance. -/
theorem supDist_le_dist (x y : Plane) : Plane.supDist x y ≤ dist x y := by
  rw [dist_eq_norm]
  exact Plane.supNorm_le_norm _

/-- **Any two points of `S` are within `2√2`.** -/
theorem dist_le_of_mem_modelCurve {x y : Plane} (hx : x ∈ modelCurve) (hy : y ∈ modelCurve) :
    dist x y ≤ 2 * Real.sqrt 2 := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  calc dist x y ≤ Real.sqrt 2 * Plane.supNorm (x - y) := dist_le_sqrt_two_mul_supNorm x y
    _ ≤ Real.sqrt 2 * (Plane.supNorm x + Plane.supNorm y) :=
        mul_le_mul_of_nonneg_left (supNorm_sub_le x y) hsq.le
    _ = 2 * Real.sqrt 2 := by
        rw [show Plane.supNorm x = 1 from hx, show Plane.supNorm y = 1 from hy]; ring

/-- **`FreshDense` is vacuous at large `δ`.** For `δ ≥ 4√2` *every* list of fresh points is
`δ`-dense, the empty one included: the whole of `S` has diameter `2√2 ≤ δ/2`.

This is the first half of the finding: `FreshDense` alone cannot be the missing hypothesis of
`prop:anchored-square-mesh` clause 5, because it does not exclude `fresh = []`. -/
theorem freshDense_of_four_sqrt_two_le {fresh : List Plane} {δ : ℝ}
    (hδ : 4 * Real.sqrt 2 ≤ δ) : FreshDense fresh δ := by
  intro A hA _ x hx y hy
  have := dist_le_of_mem_modelCurve (hA hx).1 (hA hy).1
  linarith

/-- **The counterexample, formally.** There is a positive `δ` for which `FreshDense [] δ`
holds and the mesh is still not 2-connected. So clause 5 is not repaired by adding
`FreshDense` alone. -/
theorem freshDense_not_isTwoConnected (anchors : List Plane) :
    ∃ δ : ℝ, 0 < δ ∧ FreshDense [] δ ∧ ¬ (squareMesh δ [] anchors).IsTwoConnected := by
  have hsq : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  exact ⟨4 * Real.sqrt 2, by linarith, freshDense_of_four_sqrt_two_le le_rfl,
    not_isTwoConnected_squareMesh_of_fresh_nil _ _⟩

/-! ### What does repair clause 5

A side of `S` is a connected subset of `S` whose two ends are `2` apart. If no two fresh points
are distinct then some side avoids all of them — a single point cannot lie on both the top and
the bottom side — and `FreshDense fresh δ` applied to that side forces `4 ≤ δ`. -/

/-- The two ends of the top or the bottom side of `S` are at distance at least `2`. -/
theorem two_le_dist_side {P : Piece} (h : P = sideT ∨ P = sideB) : (2 : ℝ) ≤ dist P.1 P.2 := by
  refine le_trans (le_of_eq ?_) (supDist_le_dist P.1 P.2)
  rcases h with rfl | rfl <;>
    · simp only [sideT, sideB, Plane.supDist, Plane.supNorm, Plane.sub_apply]
      norm_num

/-- A single point cannot lie on both horizontal sides of `S`, so one of them avoids a
one-point set. -/
theorem exists_side_avoiding (fresh : List Plane) (hsub : ∀ z ∈ fresh, ∀ w ∈ fresh, z = w) :
    ∃ P : Piece, (P = sideT ∨ P = sideB) ∧ ∀ z ∈ fresh, z ∉ P.seg := by
  by_cases hex : ∃ z, z ∈ fresh
  · obtain ⟨z, hz⟩ := hex
    by_cases hzT : z ∈ sideT.seg
    · refine ⟨sideB, Or.inr rfl, fun w hw hwB => ?_⟩
      have : w = z := hsub w hw z hz
      subst this
      exact sideT_disjoint_sideB hzT hwB
    · exact ⟨sideT, Or.inl rfl, fun w hw hwT => hzT (by rwa [← hsub w hw z hz])⟩
  · push Not at hex
    exact ⟨sideT, Or.inl rfl, fun z hz _ => absurd hz (hex z)⟩

/-- **`FreshDense` with a small `δ` gives two distinct fresh points.** This is the hypothesis
`prop:anchored-square-mesh` clause 5 actually needs, and the blueprint supplies it: its
`δ = ε_n = 2^{-n}` is well below `4`. -/
theorem exists_two_distinct_fresh_of_freshDense {fresh : List Plane} {δ : ℝ}
    (hdense : FreshDense fresh δ) (hδ : δ < 4) : ∃ z ∈ fresh, ∃ w ∈ fresh, z ≠ w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hP, havoid⟩ := exists_side_avoiding fresh hcon
  have hseg : P.seg ⊆ modelCurve \ {x | x ∈ fresh} := by
    intro x hx
    refine ⟨side_seg_subset_modelCurve ?_ hx, fun hmem => havoid x hmem hx⟩
    rcases hP with rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))]
  have := hdense P.seg hseg (convex_segment P.1 P.2).isPreconnected
    P.1 (left_mem_segment ℝ _ _) P.2 (right_mem_segment ℝ _ _)
  have := two_le_dist_side hP
  linarith

/-! ### Fewer than two distinct fresh points is always fatal

`SquareMeshFixed.not_isTwoConnected_squareMesh_of_fresh_nil` settles `fresh = []` by showing
the mesh disconnected. The remaining degenerate case — exactly one fresh point — is settled
here, and by the same invariant.

Every edge of the mesh is a subsegment of a source segment, and a source segment is either a
side of a ring, on which the sup norm is constant, or the spoke at a fresh point `z`, along
which the only point of sup norm `1` is `z` itself. So once `z` is deleted, **no** edge of the
mesh joins a vertex of sup norm `1` to a vertex of smaller sup norm: `z` is a cut vertex. -/

/-- Along an edge of the mesh whose ends are both different from the one fresh point `z`, the
predicate "sup norm is `1`" is constant. -/
theorem supNorm_eq_one_iff_of_isLink {N : ℕ} (hN : 2 ≤ N) {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (hsub : ∀ u ∈ fresh, ∀ w ∈ fresh, u = w)
    {anchors : List Plane} {z : Plane} (hz : z ∈ fresh) {P : Piece} {x y : Plane}
    (h : (meshGraph N fresh anchors).IsLink P x y) (hx : x ≠ z) (hy : y ≠ z) :
    (Plane.supNorm x = 1 ↔ Plane.supNorm y = 1) := by
  obtain ⟨R, hR, hRsub⟩ := meshGraph_edge_source h.1
  -- the ends of `P`, in whichever order the link presents them
  have hends : (x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1) := h.2
  rcases mem_meshSegments.1 hR with ⟨r, hr, hRr⟩ | ⟨u, hu, rfl⟩
  · -- a side of a ring: both ends have sup norm `r`
    have hring : P.seg ⊆ ringSet r :=
      hRsub.trans (ringPieces_seg_subset (meshRadii_pos hN hr).le hRr)
    have h1 : Plane.supNorm P.1 = r := hring (left_mem_segment ℝ _ _)
    have h2 : Plane.supNorm P.2 = r := hring (right_mem_segment ℝ _ _)
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [by rw [h1, h2], by rw [h1, h2]]
  · -- the spoke at the single fresh point: sup norm `1` only at its outer end
    rw [hsub u hu z hz] at hRsub
    have hspoke : ∀ q ∈ (spokePiece N z).seg, Plane.supNorm q = 1 → q = z := by
      intro q hq hq1
      have : q ∈ (spokePiece N z).seg ∩ modelCurve := ⟨hq, hq1⟩
      rwa [spokePiece_inter_modelCurve hN (hfresh z hz)] at this
    have hne : ∀ q, (q = P.1 ∨ q = P.2) → q ≠ z → Plane.supNorm q ≠ 1 := by
      rintro q (rfl | rfl) hqz hq1
      exacts [hqz (hspoke _ (hRsub (left_mem_segment ℝ _ _)) hq1),
        hqz (hspoke _ (hRsub (right_mem_segment ℝ _ _)) hq1)]
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun hc => absurd hc (hne _ (Or.inl rfl) hx),
        fun hc => absurd hc (hne _ (Or.inr rfl) hy)⟩
    · exact ⟨fun hc => absurd hc (hne _ (Or.inr rfl) hx),
        fun hc => absurd hc (hne _ (Or.inl rfl) hy)⟩

/-- An end of a side of the outer ring is a vertex of the mesh. -/
theorem corner_mem_vertexSet_meshGraph {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane}
    {R : Piece} (hR : R ∈ ringPieces 1) : R.1 ∈ V(meshGraph N fresh anchors) :=
  end_mem_vertexSet_meshGraph (outer_ringPieces_mem hN hR) (Or.inl rfl)

theorem supNorm_corner_pp : Plane.supNorm (Plane.mk (1 : ℝ) (1 : ℝ)) = 1 := by
  simp [Plane.supNorm]

theorem supNorm_corner_mm : Plane.supNorm (Plane.mk (-1 : ℝ) (-1 : ℝ)) = 1 := by
  simp [Plane.supNorm]

/-- Whichever point `z` is, one of the two corners `(1,1)`, `(-1,-1)` differs from it and is a
vertex of the mesh of sup norm `1`. -/
theorem exists_outer_vertex_ne {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane} (z : Plane) :
    ∃ c : Plane, c ∈ V(meshGraph N fresh anchors) ∧ Plane.supNorm c = 1 ∧ c ≠ z := by
  by_cases h : (Plane.mk (1 : ℝ) (1 : ℝ)) = z
  · refine ⟨Plane.mk (-1 : ℝ) (-1 : ℝ), corner_mem_vertexSet_meshGraph (fresh := fresh)
      (anchors := anchors) hN (R := (Plane.mk (-1) (-1), Plane.mk 1 (-1))) (by simp [ringPieces]),
      supNorm_corner_mm, ?_⟩
    rw [← h]
    exact mk_ne_mk_of_fst (by norm_num)
  · exact ⟨Plane.mk (1 : ℝ) (1 : ℝ), corner_mem_vertexSet_meshGraph (fresh := fresh)
      (anchors := anchors) hN (R := (Plane.mk 1 1, Plane.mk (-1) 1)) (by simp [ringPieces]),
      supNorm_corner_pp, h⟩

/-- The corner of the innermost ring is a vertex of the mesh, and its sup norm is not `1`. -/
theorem exists_inner_vertex {N : ℕ} (hN : 2 ≤ N) {fresh anchors : List Plane} :
    ∃ c : Plane, c ∈ V(meshGraph N fresh anchors) ∧ Plane.supNorm c ≠ 1 := by
  refine ⟨Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹),
    end_mem_vertexSet_meshGraph
      (R := (Plane.mk ((N : ℝ)⁻¹) ((N : ℝ)⁻¹), Plane.mk (-(N : ℝ)⁻¹) ((N : ℝ)⁻¹)))
      (mem_meshSegments.2 (Or.inl ⟨(N : ℝ)⁻¹, inv_mem_meshRadii hN, by simp [ringPieces]⟩))
      (Or.inl rfl), ?_⟩
  rw [supNorm_mk, abs_of_nonneg (inv_cast_pos hN).le, max_self]
  exact ne_of_lt (inv_cast_lt_one hN)

/-- **A mesh whose fresh points are not two distinct points is never 2-connected.** With none
the mesh is disconnected (`not_connected_meshGraph_of_fresh_nil`); with one, `z`, the point `z`
is a cut vertex.

This is the second half of the finding: two distinct fresh points is not merely a convenient
hypothesis for clause 5, it is a *necessary* one. -/
theorem not_isTwoConnected_meshGraph_of_fresh_subsingleton {N : ℕ} (hN : 2 ≤ N)
    {fresh : List Plane} (hfresh : ∀ u ∈ fresh, u ∈ modelCurve)
    (hsub : ∀ u ∈ fresh, ∀ w ∈ fresh, u = w) (anchors : List Plane) :
    ¬ (meshGraph N fresh anchors).IsTwoConnected := by
  by_cases hex : ∃ z, z ∈ fresh
  swap
  · push Not at hex
    obtain rfl : fresh = [] := List.eq_nil_iff_forall_not_mem.2 hex
    exact fun h => not_connected_meshGraph_of_fresh_nil hN anchors h.connected
  obtain ⟨z, hz⟩ := hex
  intro h2
  -- after deleting `z`, no edge changes the truth of "the sup norm is `1`"
  have hinv : ∀ {u v : Plane}, ((meshGraph N fresh anchors).deleteVerts {z}).Reaches u v →
      (Plane.supNorm u = 1 ↔ Plane.supNorm v = 1) := by
    rintro u v ⟨W, hW⟩
    induction hW with
    | nil => exact Iff.rfl
    | @cons a b c e W hl _ ih =>
      rw [Graph.deleteVerts_isLink] at hl
      exact (supNorm_eq_one_iff_of_isLink hN hfresh hsub hz hl.1
        (by simpa using hl.2.1) (by simpa using hl.2.2)).trans ih
  obtain ⟨c, hcV, hc1, hcz⟩ := exists_outer_vertex_ne (fresh := fresh) (anchors := anchors) hN z
  obtain ⟨d, hdV, hd1⟩ := exists_inner_vertex (fresh := fresh) (anchors := anchors) hN
  have hdz : d ≠ z := by
    rintro rfl
    exact hd1 (hfresh d hz)
  have := hinv ((h2.deleteVerts_connected' z).reaches
    (Graph.mem_deleteVerts_singleton_of_ne hcV hcz)
    (Graph.mem_deleteVerts_singleton_of_ne hdV hdz))
  exact hd1 (this.1 hc1)

/-- **`prop:anchored-square-mesh` clause 5 needs two distinct fresh points**, for
`Schoenflies.squareMesh` itself. -/
theorem not_isTwoConnected_squareMesh_of_fresh_subsingleton {fresh : List Plane}
    (hfresh : ∀ u ∈ fresh, u ∈ modelCurve) (hsub : ∀ u ∈ fresh, ∀ w ∈ fresh, u = w)
    (δ : ℝ) (anchors : List Plane) : ¬ (squareMesh δ fresh anchors).IsTwoConnected :=
  not_isTwoConnected_meshGraph_of_fresh_subsingleton (two_le_meshCount δ) hfresh hsub anchors

end Schoenflies
