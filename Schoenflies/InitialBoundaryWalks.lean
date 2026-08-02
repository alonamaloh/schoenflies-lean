/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.BoundaryWalks
import Schoenflies.InitialGenerated

/-!
# The initial structure has boundary walks

The base case of `Schoenflies.CellStructure.BoundaryWalks`. `InitialPairFixed.lean` proved the
two halves separately — `isWalk_initBoundary_false`, `.._true` that the two boundary lists are
closed walks, and `mem_faceCells_iff` that the cells they run through are the `faceCells` the
base value of `≼_abs` declares. This module packages them, which is all that was left to do:
both were written for exactly this.

## Blueprint

* `Schoenflies.initialBoundaryWalks` — `prop:initial-pair`'s structure satisfies the invariant
  of `def:matched-cellulation` on boundary walks.
-/

open Set
open scoped Graph

namespace Schoenflies

open CellStructure

/-- The base point of each initial boundary walk: an end of the chord, which both walks take. -/
def initStart : InitialCell → InitialCell
  | .face true => .vert 4
  | _ => .vert 1

theorem isWalk_initBoundary (k : Bool) :
    initSkel.IsWalk (initStart (.face k)) (initBoundary (.face k)) (initStart (.face k)) := by
  cases k
  exacts [isWalk_initBoundary_false, isWalk_initBoundary_true]

/-- Membership in the vertices an explicit walk of `initSkel` visits, in a shape `decide` can
finish: an edge of the initial skeleton is incident exactly to its two `ends`. -/
theorem mem_initSkel_walkVertices_iff {u x : InitialCell} {W : List InitialCell} :
    x ∈ initSkel.walkVertices u W ↔
      x = u ∨ ∃ e ∈ W, e ∈ InitialCell.edges ∧ (x = e.ends.1 ∨ x = e.ends.2) := by
  simp only [Graph.walkVertices, Graph.coveredVertices, mem_insert_iff, mem_setOf_eq,
    initSkel_inc_iff]

/-- **`B₁ ∪ P` is a cycle at `a`, and `B₂ ∪ P` one at `b`.** The two boundary walks of the
initial structure repeat no vertex: each runs along three outer edges and back over the chord,
through four of the six boundary vertices. -/
theorem isCycle_initBoundary (k : Bool) :
    ∃ e v D, initBoundary (.face k) = e :: D.reverse ∧
      initSkel.IsCycleThrough e (initStart (.face k)) v D := by
  cases k
  · refine ⟨.edge 1, .vert 2, [.chord, .edge 3, .edge 2], rfl,
      initSkel_isLink_edge (by decide : (1 : Fin 6) + 1 = 2), ?_, by decide⟩
    refine .cons initSkel_isLink_chord
      (.cons (initSkel_isLink_edge (by decide : (3 : Fin 6) + 1 = 4)).symm
        (.cons (initSkel_isLink_edge (by decide : (2 : Fin 6) + 1 = 3)).symm
          (.nil (InitialCell.vert_mem_vertices 2)) ?_) ?_) ?_ <;>
      simp [mem_initSkel_walkVertices_iff, InitialCell.ends, initStart]
  · refine ⟨.edge 4, .vert 5, [.chord, .edge 0, .edge 5], rfl,
      initSkel_isLink_edge (by decide : (4 : Fin 6) + 1 = 5), ?_, by decide⟩
    refine .cons initSkel_isLink_chord.symm
      (.cons (initSkel_isLink_edge (by decide : (0 : Fin 6) + 1 = 1)).symm
        (.cons (initSkel_isLink_edge (by decide : (5 : Fin 6) + 1 = 0)).symm
          (.nil (InitialCell.vert_mem_vertices 5)) ?_) ?_) ?_ <;>
      simp [mem_initSkel_walkVertices_iff, InitialCell.ends, initStart]

/-- The cells of an initial boundary walk are the `faceCells` of its 2-cell. The base point is
covered by the walk itself — both walks take the chord, whose ends are the two base points — so
adding it changes nothing, which is the whole gap between `mem_faceCells_iff` and this. -/
theorem pathCells_initBoundary (k : Bool) :
    initialStructure.pathCells (initStart (.face k)) (initBoundary (.face k)) = faceCells k := by
  have hchord : ∀ b : Bool, ∃ e ∈ initBoundary (.face b), initSkel.Inc e (initStart (.face b)) := by
    rintro (_ | _)
    · exact ⟨.chord, by simp [initBoundary], initSkel_isLink_chord.inc_left⟩
    · exact ⟨.chord, by simp [initBoundary], initSkel_isLink_chord.inc_right⟩
  ext c
  simp only [pathCells, Graph.walkVertices, Graph.coveredVertices, mem_union, mem_setOf_eq,
    mem_insert_iff, mem_faceCells_iff, initialStructure_skel]
  constructor
  · rintro (hc | rfl | hc)
    exacts [Or.inl hc, Or.inr (hchord k), Or.inr hc]
  · rintro (hc | hc)
    exacts [Or.inl hc, Or.inr (Or.inr hc)]

/-- The cells strictly below an initial 2-cell are its `faceCells`. -/
theorem subcells_face_sdiff (k : Bool) :
    initialStructure.subcells (.face k) \ {(.face k : InitialCell)} = faceCells k := by
  ext c
  rw [mem_sdiff, mem_subcells_iff, mem_singleton_iff, initialStructure_sub]
  constructor
  · rintro ⟨⟨-, h⟩, hne⟩
    exact (initSub_iff_face.1 h).resolve_left hne
  · intro hc
    exact ⟨⟨mem_cells_of_mem_faceCells hc, initSub_face hc⟩, fun h => face_notMem_faceCells (h ▸ hc)⟩

/-- **The initial structure satisfies the boundary-walk invariant.** -/
def initialBoundaryWalks : initialStructure.BoundaryWalks where
  start := initStart
  isCycle := by
    rintro F ⟨k, rfl⟩
    exact isCycle_initBoundary k
  pathCells_eq := by
    rintro F ⟨k, rfl⟩
    change initialStructure.pathCells _ (initBoundary (.face k)) = _
    rw [pathCells_initBoundary k, subcells_face_sdiff k]

end Schoenflies
