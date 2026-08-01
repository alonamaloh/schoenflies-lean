/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.PolyPath
import Schoenflies.Curve

/-!
# Polygonal sets, and segments as arcs

`IsPolygonal` is the blueprint's set-level predicate: a finite union of line segments, which
here is exactly the carrier of some vertex list.

The theorem the plane-graph layer needs from this module is `isArcBetween_segment`: a
*nondegenerate* segment is an arc between its endpoints. It is what makes the drawing
condition free for a polygonal plane graph — an edge's arc obligation is discharged by the
segment itself, and the distinctness of its ends is already part of well-formedness.

## Blueprint

* `IsPolygonal` — §1, "an arc or curve is polygonal if it is a finite union of line segments".
* `isArcBetween_segment` — a nondegenerate segment is an arc between its endpoints.
-/

open Metric Set

namespace Schoenflies

/-- A set is polygonal when it is the carrier of a finite vertex list, that is, a finite union
of line segments. -/
def IsPolygonal (A : Set Plane) : Prop := ∃ vs : List Plane, A = poly vs

theorem IsPolygonal.isCompact {A : Set Plane} (h : IsPolygonal A) : IsCompact A := by
  obtain ⟨vs, rfl⟩ := h
  exact isCompact_poly vs

@[simp] theorem poly_pair (a b : Plane) : poly [a, b] = segment ℝ a b := by
  rw [poly_cons_cons, poly_singleton]
  exact union_eq_self_of_subset_right (singleton_subset_iff.2 (right_mem_segment ℝ a b))

theorem isPolygonal_segment (a b : Plane) : IsPolygonal (segment ℝ a b) :=
  ⟨[a, b], (poly_pair a b).symm⟩

/-- `lineMap a b` is injective on the unit interval exactly when the segment is
nondegenerate: two parameters differ by a multiple of `b - a`. Exposed separately because the
plane-graph drawing condition asks for the parametrization, not just its image. -/
theorem injOn_lineMap {a b : Plane} (hab : a ≠ b) :
    Set.InjOn (AffineMap.lineMap a b : ℝ → Plane) I := by
  intro s _ t _ hst
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have key : (s - t) • (b - a) = 0 := by
    simp only [AffineMap.lineMap_apply_module] at hst
    linear_combination (norm := module) hst
  rcases smul_eq_zero.1 key with h | h
  · linarith
  · exact absurd h hba

/-- A nondegenerate segment is an arc between its endpoints, parametrized by
`AffineMap.lineMap a b`. -/
theorem isArcBetween_segment {a b : Plane} (hab : a ≠ b) :
    IsArcBetween (segment ℝ a b) a b := by
  refine ⟨AffineMap.lineMap a b, AffineMap.lineMap_continuous.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact injOn_lineMap hab
  · rw [segment_eq_image_lineMap]
  · simp
  · simp

theorem isArc_segment {a b : Plane} (hab : a ≠ b) : IsArc (segment ℝ a b) :=
  (isArcBetween_segment hab).isArc

end Schoenflies
