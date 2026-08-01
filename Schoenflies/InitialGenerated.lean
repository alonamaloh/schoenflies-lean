/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FiniteTransfer
import Schoenflies.InitialPairFixed
import Schoenflies.BoundaryContinuity2

/-!
# Stage 0: the initial pair as a `GeneratedPair`

`Schoenflies/FiniteTransfer.lean` defines `Schoenflies.GeneratedPair`, the object every stage of
the Schönflies recursion is and that `thm:finite-transfer` consumes and produces. Nothing built
one. This module builds the first: the initial matched pair of `prop:initial-pair`, which is
generated from itself by the empty sequence of elementary operations.

## What has to be shown

The two realizations, the skeleton homeomorphism and weak admissibility are all in
`Schoenflies/InitialPair.lean` and `Schoenflies/InitialPairFixed.lean` already, or one step from
what is there. The work is the two `IsCellDecomposition` fields — assertion (i) of
`lem:cellulation-invariants` — and they are the same work twice, because both realizations have
the same shape: a `HexData` whose six outer arcs form a Jordan curve and whose chord is a
crosscut of it. So assertion (i) is proved **once**, for an arbitrary `HexData` carrying that
crosscut configuration (`Schoenflies.HexData.isCellDecomposition`), and instantiated on each
side. The same is true of weak admissibility (`Schoenflies.HexData.isWeaklyAdmissible`).

The four clauses go as follows.

* `nonempty` — the seven 0-cells are points; the seven open 1-cells are arcs minus their two
  endpoints (`IsArcBetween.nonempty_diff`); the two 2-cells are the two sides of the crosscut,
  nonempty by `thm:general-crosscut`.
* `disjoint` — fifteen cells, but only five kinds of pair. Two vertices are distinct points;
  a vertex misses every open edge it is not an end of (`HexData.mem_outer_iff`,
  `.mem_chord_iff`), and is an end of the ones it does meet; two open edges are disjoint by the
  two meeting conditions of `HexData`; every 1- or 0-cell lies on the skeleton and every 2-cell
  is inside the curve and off the crosscut; and the two 2-cells are the two sides of one
  crosscut.
* `iUnion_eq` — the 0-cells and open 1-cells reassemble the skeleton `C ∪ P`
  (`HexData.iUnion_skeleton_cellSet`), and the two 2-cells exhaust `D ∖ P`
  (`thm:general-crosscut`), so together they are `C ∪ D`.
* `closure_eq` — a finite case check against `Schoenflies.initSub`, the base value of `≼_abs`
  that the blueprint fixes. The four `initSub_iff_*` lemmas below read it off, and then the only
  topology needed is `closure (A ∖ {p, q}) = A` for an arc (`IsArcBetween.closure_diff`) and the
  closure of a crosscut side (`Schoenflies.crosscut_cell_partition`).

## The input is `InitialData`, not `AnchoredInitialData`

`AnchoredInitialData` adds exactly two fields, `a ∈ 𝒜` and `b ∈ 𝒜`. Nothing in `GeneratedPair`
mentions the anchor set: the anchoring is what lets a *later* stage run a fresh crosscut into `a`
or `b`, and it is read off `AnchoredInitialData.stronglyAccessible_a` at that point. So the pair
is built from `InitialData` — the weaker input — and
`Schoenflies.AnchoredInitialData.generatedPair` is the one-line specialisation for a consumer
holding the anchored form.

## Blueprint

* `Schoenflies.combInvariants_initialStructure` — `lem:cellulation-invariants` (iii), (v), (vi)
  and abstract (viii) for the base structure: the base case of
  `Schoenflies.GeneratedStructure.combInvariants`, which the whole recursion needs.
* `Schoenflies.initSub_iff_vert`, `.._edge`, `.._chord`, `.._face` — the base value of `≼_abs`
  (tex 1590–1602) read as "the subcells of each cell are exactly these".
* `Schoenflies.HexData.isCellDecomposition` — `lem:cellulation-invariants`(i) for either
  realization of `prop:initial-pair`.
* `Schoenflies.HexData.isWeaklyAdmissible` — `def:admissible-graph` minus the connectedness
  clause, for either realization.
* `Schoenflies.InitialData.generatedPair`, `Schoenflies.AnchoredInitialData.generatedPair` —
  `def:generated-structure` at stage 0: `prop:initial-pair` is a generated matched cellulation.
* `Schoenflies.InitialData.generatedPair_isAdmissible` — the *strong* form of
  `def:admissible-graph` on both sides, which the initial pair does satisfy
  (`rem:intermediate-disconnection` waives it only at intermediate stages).
-/

open Metric Set Topology unitInterval
open scoped Graph

namespace Schoenflies

open Graph

/-! ### An arc is the closure of its interior

General, and stated nowhere on `main`: `Schoenflies/Subarc.lean` has the two endpoint lemmas and
`IsArcBetween.isConnected_diff`, but not the closure identity itself. The integrator should hoist
this next to `IsArcBetween.right_mem_closure_diff`. -/

/-- **An arc is the closure of its interior.** The arc is compact, hence closed, so the closure
of the interior is inside it; conversely the interior is inside its own closure and each of the
two endpoints is a limit of it. -/
theorem IsArcBetween.closure_diff {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := by
  refine Subset.antisymm (h.isArc.isClosed.closure_subset_iff.2 sdiff_subset) fun z hz => ?_
  by_cases hzp : z = p
  · exact hzp ▸ h.left_mem_closure_diff
  by_cases hzq : z = q
  · exact hzq ▸ h.right_mem_closure_diff
  exact subset_closure ⟨hz, by rintro (rfl | rfl) <;> simp_all⟩

/-! ### The cells of the initial structure, and `≼_abs`

`InitialCell` has exactly four constructors and `initialStructure` declares every one of them a
cell, so `cells` is the whole type. That is worth recording once: it removes the membership side
condition from every clause of assertion (i) below. -/

theorem mem_cells_initialStructure (c : InitialCell) : c ∈ initialStructure.cells := by
  cases c with
  | vert i => exact Or.inl (Or.inl ⟨i, rfl⟩)
  | edge i => exact Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))
  | chord => exact Or.inl (Or.inr (Or.inr rfl))
  | face k => exact Or.inr ⟨k, rfl⟩

theorem initialStructure_cells : initialStructure.cells = Set.univ :=
  Set.eq_univ_of_forall mem_cells_initialStructure

/-- A `face` name is never a 0-cell or a 1-cell. -/
theorem face_notMem_faceCells {k l : Bool} : InitialCell.face k ∉ faceCells l := by
  cases l <;> simp [faceCells]

/-- The subcells of a 0-cell are itself alone. -/
theorem initSub_iff_vert {i : Fin 6} {c : InitialCell} :
    initSub c (.vert i) ↔ c = .vert i := by
  refine ⟨fun h => ?_, fun h => h ▸ initSub_refl _⟩
  rcases h with h | ⟨h, -⟩ | ⟨k, hk, -⟩
  · exact h
  · exact absurd h (by simp [InitialCell.edges])
  · exact absurd hk (by simp)

/-- The subcells of an outer 1-cell are itself and its two ends. -/
theorem initSub_iff_edge {i : Fin 6} {c : InitialCell} :
    initSub c (.edge i) ↔ c = .edge i ∨ c = .vert i ∨ c = .vert (i + 1) := by
  constructor
  · rintro (h | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl _
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).1
    · exact (initSub_ends (InitialCell.edge_mem_edges i)).2

/-- The subcells of the crosscut are itself and its two ends. -/
theorem initSub_iff_chord {c : InitialCell} :
    initSub c .chord ↔ c = .chord ∨ c = .vert 1 ∨ c = .vert 4 := by
  constructor
  · rintro (h | ⟨-, h | h⟩ | ⟨k, hk, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hk (by simp)
  · rintro (rfl | rfl | rfl)
    · exact initSub_refl _
    · exact (initSub_ends InitialCell.chord_mem_edges).1
    · exact (initSub_ends InitialCell.chord_mem_edges).2

/-- The subcells of a 2-cell are itself together with the cells of its boundary walk. -/
theorem initSub_iff_face {k : Bool} {c : InitialCell} :
    initSub c (.face k) ↔ c = .face k ∨ c ∈ faceCells k := by
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨l, hl, hmem⟩)
    · exact Or.inl h
    · exact absurd h (by simp [InitialCell.edges])
    · cases hl; exact Or.inr hmem
  · rintro (rfl | h)
    · exact initSub_refl _
    · exact initSub_face h

/-! ### The combinatorial invariants at the base

`Schoenflies.GeneratedStructure.combInvariants` propagates `lem:cellulation-invariants` (iii),
(v), (vi) and abstract (viii) along the two elementary operations *given the base case*. This is
the base case. Assertion (vi) is `Schoenflies.outerEdgeUniqueFace_initialStructure`, already on
`main`; the other seven clauses are read off `initSub`. -/

/-- **The combinatorial invariants hold for the initial structure.** The base case of
`Schoenflies.GeneratedStructure.combInvariants`, hence of `GeneratedPair.combInvariants`. -/
theorem combInvariants_initialStructure : initialStructure.CombInvariants where
  sub_mem_left := fun {c _} _ => mem_cells_initialStructure c
  sub_mem_right := fun {_ τ} _ => mem_cells_initialStructure τ
  sub_refl := fun {c} _ => initSub_refl c
  sub_isLink := by
    rintro f a b ⟨hf, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    exacts [(initSub_ends hf).1, (initSub_ends hf).2]
  face_maximal := by
    rintro F τ ⟨k, rfl⟩ h
    rcases h with h | ⟨he, hends⟩ | ⟨l, rfl, hmem⟩
    · exact h.symm
    · -- both ends of a 1-cell are 0-cells, and a 2-cell name is neither
      rcases he with ⟨j, rfl⟩ | rfl <;> simp [InitialCell.ends] at hends
    · exact absurd hmem face_notMem_faceCells
  nonboundary_edge := by
    rintro F ⟨k, rfl⟩
    refine ⟨.chord, InitialCell.chord_mem_edges, by simp [InitialCell.outerEdges], ?_⟩
    exact initSub_face (by cases k <;> simp [faceCells])
  mem_face := by
    rintro c -
    -- every cell appears among the subcells of one of the two 2-cells
    cases c with
    | vert i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | edge i =>
      refine ⟨.face (![true, false, false, false, true, true] i), ⟨_, rfl⟩, initSub_face ?_⟩
      fin_cases i <;> simp [faceCells]
    | chord => exact ⟨.face false, ⟨_, rfl⟩, initSub_face (by simp [faceCells])⟩
    | face k => exact ⟨.face k, ⟨k, rfl⟩, initSub_refl _⟩
  outerEdge_unique := outerEdgeUniqueFace_initialStructure

end Schoenflies
