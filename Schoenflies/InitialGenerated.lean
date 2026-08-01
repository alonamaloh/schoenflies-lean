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

/-! ### The open cells of a `HexData`

Everything assertion (i) needs about the fifteen realized open cells, stated for an arbitrary
`HexData` so that the source and the target realization are served by one proof. Nothing in this
section mentions the crosscut configuration; that enters only for the two 2-cells. -/

namespace HexData

variable (H : HexData)

@[simp] theorem cellSet_vert (i : Fin 6) : H.cellSet (.vert i) = {H.pos i} := rfl

@[simp] theorem cellSet_edge (i : Fin 6) :
    H.cellSet (.edge i) = H.outer i '' I \ {H.pos i, H.pos (i + 1)} := rfl

@[simp] theorem cellSet_chord : H.cellSet .chord = H.chordSet \ {H.pos 1, H.pos 4} := rfl

@[simp] theorem cellSet_face (k : Bool) :
    H.cellSet (.face k) = inside (H.arcOf k ∪ H.chordSet) := rfl

theorem cellSet_edge_subset (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outer i '' I := sdiff_subset

theorem cellSet_edge_subset_outerArcs (i : Fin 6) : H.cellSet (.edge i) ⊆ H.outerArcs :=
  (H.cellSet_edge_subset i).trans (Set.subset_iUnion (fun i : Fin 6 => H.outer i '' I) i)

theorem cellSet_chord_subset : H.cellSet .chord ⊆ H.chordSet := sdiff_subset

theorem pos_mem_outerArcs (i : Fin 6) : H.pos i ∈ H.outerArcs :=
  Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩

/-- **The 1-cells are nonempty**: an arc has more points than its two endpoints. -/
theorem nonempty_cellSet_edge (i : Fin 6) : (H.cellSet (.edge i)).Nonempty :=
  (H.isArcBetween_outer i).nonempty_diff

theorem nonempty_cellSet_chord : (H.cellSet .chord).Nonempty :=
  H.isArcBetween_chordSet.nonempty_diff

/-- **A closed 1-cell is the drawn edge**: an arc is the closure of its interior. -/
theorem closure_cellSet_edge (i : Fin 6) :
    closure (H.cellSet (.edge i)) = H.outer i '' I :=
  (H.isArcBetween_outer i).closure_diff

theorem closure_cellSet_chord : closure (H.cellSet .chord) = H.chordSet :=
  H.isArcBetween_chordSet.closure_diff

/-- **A 0-cell never lies on an open 1-cell.** A vertex on a drawn outer edge is one of its two
ends (`HexData.mem_outer_iff`), and the open edge is exactly the drawn edge without them. -/
theorem pos_notMem_cellSet_edge (k i : Fin 6) : H.pos k ∉ H.cellSet (.edge i) := by
  rintro ⟨hz, hne⟩
  rcases H.mem_outer_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

theorem pos_notMem_cellSet_chord (k : Fin 6) : H.pos k ∉ H.cellSet .chord := by
  rintro ⟨hz, hne⟩
  rcases H.mem_chord_iff hz with rfl | rfl
  exacts [hne (Or.inl rfl), hne (Or.inr rfl)]

/-- **Two distinct open outer 1-cells are disjoint.** The two edges meet only at points that are
ends of both, and those are removed. -/
theorem disjoint_cellSet_edge {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet (.edge j)) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hne⟩ ⟨hzj, -⟩
  exact hne (H.outer_meet i j hij ⟨hzi, hzj⟩).1

/-- **The open crosscut misses every open outer 1-cell.** -/
theorem disjoint_cellSet_edge_chord (i : Fin 6) :
    Disjoint (H.cellSet (.edge i)) (H.cellSet .chord) := by
  rw [Set.disjoint_left]
  rintro z ⟨hzi, -⟩ ⟨hzc, hne⟩
  exact hne (H.chord_meet i ⟨hzc, hzi⟩)

/-- A point of a drawn outer edge is on the open edge or is one of its two ends. -/
theorem mem_cellSet_edge_or {i : Fin 6} {z : Plane} (hz : z ∈ H.outer i '' I) :
    z ∈ H.cellSet (.edge i) ∨ z = H.pos i ∨ z = H.pos (i + 1) := by
  by_cases h : z ∈ ({H.pos i, H.pos (i + 1)} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

/-- A point of the crosscut is on the open crosscut or is one of its two ends. -/
theorem mem_cellSet_chord_or {z : Plane} (hz : z ∈ H.chordSet) :
    z ∈ H.cellSet .chord ∨ z = H.pos 1 ∨ z = H.pos 4 := by
  by_cases h : z ∈ ({H.pos 1, H.pos 4} : Set Plane)
  · rcases h with h | h
    exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]
  · exact Or.inl ⟨hz, h⟩

/-- **The 0-cells and the open 1-cells reassemble the skeleton `C ∪ P`.** -/
theorem iUnion_cellSet (H : HexData) :
    (⋃ c : InitialCell, H.cellSet c) =
      (H.outerArcs ∪ H.chordSet) ∪ (H.cellSet (.face false) ∪ H.cellSet (.face true)) := by
  refine Subset.antisymm (Set.iUnion_subset fun c => ?_) fun z hz => ?_
  · cases c with
    | vert i =>
      rintro z rfl
      exact Or.inl (Or.inl (H.pos_mem_outerArcs i))
    | edge i => exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset_outerArcs i hz))
    | chord => exact fun z hz => Or.inl (Or.inr (H.cellSet_chord_subset hz))
    | face k =>
      cases k
      exacts [fun z hz => Or.inr (Or.inl hz), fun z hz => Or.inr (Or.inr hz)]
  · rcases hz with (hz | hz) | (hz | hz)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
      rcases H.mem_cellSet_edge_or hi with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.edge i, h⟩, Set.mem_iUnion.2 ⟨.vert i, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert (i + 1), rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion.2 ⟨.chord, h⟩, Set.mem_iUnion.2 ⟨.vert 1, rfl⟩,
        Set.mem_iUnion.2 ⟨.vert 4, rfl⟩]
    · exact Set.mem_iUnion.2 ⟨.face false, hz⟩
    · exact Set.mem_iUnion.2 ⟨.face true, hz⟩

/-- **Three consecutive outer edges and the crosscut reassemble their union.** The two 2-cells of
the initial structure differ only in *which* three outer edges bound them, so the union over the
cells of a boundary walk is computed once, for an arbitrary set `F` of cells presented as the
four vertices, the three edges and the crosscut. -/
theorem biUnion_of_three_edges (H : HexData) (F : Set InitialCell) {i j l : Fin 6}
    (hij : i + 1 = j) (hjl : j + 1 = l)
    (hmem : ∀ c ∈ F, c = .vert i ∨ c = .vert j ∨ c = .vert l ∨ c = .vert (l + 1) ∨
      c = .edge i ∨ c = .edge j ∨ c = .edge l ∨ c = .chord)
    (hvi : InitialCell.vert i ∈ F) (hvj : InitialCell.vert j ∈ F)
    (hvl : InitialCell.vert l ∈ F) (hvl1 : InitialCell.vert (l + 1) ∈ F)
    (hei : InitialCell.edge i ∈ F) (hej : InitialCell.edge j ∈ F)
    (hel : InitialCell.edge l ∈ F) (hch : InitialCell.chord ∈ F)
    (hv1 : InitialCell.vert 1 ∈ F) (hv4 : InitialCell.vert 4 ∈ F) :
    (⋃ c ∈ F, H.cellSet c)
      = (H.outer i '' I ∪ (H.outer j '' I ∪ H.outer l '' I)) ∪ H.chordSet := by
  refine Subset.antisymm (Set.iUnion₂_subset fun c hc => ?_) fun z hz => ?_
  · rcases hmem c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer i))
    · rintro z rfl; exact Or.inl (Or.inl (H.pos_mem_outer_of_succ hij))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inl (H.pos_mem_outer_of_succ hjl)))
    · rintro z rfl; exact Or.inl (Or.inr (Or.inr (H.pos_succ_mem_outer l)))
    · exact fun z hz => Or.inl (Or.inl (H.cellSet_edge_subset i hz))
    · exact fun z hz => Or.inl (Or.inr (Or.inl (H.cellSet_edge_subset j hz)))
    · exact fun z hz => Or.inl (Or.inr (Or.inr (H.cellSet_edge_subset l hz)))
    · exact fun z hz => Or.inr (H.cellSet_chord_subset hz)
  · rcases hz with (hz | hz | hz) | hz
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hei, h⟩, Set.mem_iUnion₂.2 ⟨_, hvi, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (i + 1), by rw [hij]; exact hvj, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hej, h⟩, Set.mem_iUnion₂.2 ⟨_, hvj, rfl⟩,
        Set.mem_iUnion₂.2 ⟨InitialCell.vert (j + 1), by rw [hjl]; exact hvl, rfl⟩]
    · rcases H.mem_cellSet_edge_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hel, h⟩, Set.mem_iUnion₂.2 ⟨_, hvl, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hvl1, rfl⟩]
    · rcases H.mem_cellSet_chord_or hz with h | rfl | rfl
      exacts [Set.mem_iUnion₂.2 ⟨_, hch, h⟩, Set.mem_iUnion₂.2 ⟨_, hv1, rfl⟩,
        Set.mem_iUnion₂.2 ⟨_, hv4, rfl⟩]

/-- **The cells of a 2-cell's boundary walk reassemble `Aₖ ∪ P`.** The blueprint declares
`faceCells k` to be the subcells of `Rₖ`; geometrically that union is exactly the boundary curve
of `Rₖ`, which is what `closure_eq` has to match at a 2-cell. -/
theorem biUnion_faceCells (H : HexData) (k : Bool) :
    (⋃ c ∈ faceCells k, H.cellSet c) = H.arcOf k ∪ H.chordSet := by
  cases k
  · rw [HexData.arcOf_false]
    refine H.biUnion_of_three_edges _ (i := 1) (j := 2) (l := 3) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)
  · rw [HexData.arcOf_true]
    refine H.biUnion_of_three_edges _ (i := 4) (j := 5) (l := 0) (by decide) (by decide)
      (fun c hc => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    all_goals (simp only [faceCells, Set.mem_insert_iff, Set.mem_singleton_iff]; decide)

end HexData

end Schoenflies
