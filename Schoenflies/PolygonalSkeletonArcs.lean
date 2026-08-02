/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.PlaneEdges
import Schoenflies.PolygonalCut
import Schoenflies.SkeletonCrosscuts

/-!
# Arcs in a polygonal skeleton are polygonal

`Schoenflies.CellStructure.Realization.HasPolygonalArcs`
(`Schoenflies/SkeletonCrosscuts.lean`) is the named hypothesis "every arc contained in the
realized skeleton is polygonal" — the sentence of the proof of `lem:skeleton-crosscuts` that
transports polygonality through the skeleton homeomorphism. This module discharges it, for any
realization all of whose edge arcs are polygonal, and in particular for the target side of a
`Schoenflies.GeneratedPair`, whose `tgt_isPolygonal` field says exactly that.

## The argument

Everything happens at the level of one finite plane graph. An arc in
`Graph.pointSet G drawing` is parametrized by an injective continuous map on `[0, 1]`;
injectivity makes the set of parameters at drawn vertices finite, since the vertex set is. The
recursion runs on the number of such parameters *interior* to `[0, 1]`:

* if there are none, the image of the open parameter interval is a connected subset of
  `pointSet ∖ V(G)` — which decomposes into the open edges, with the open edges its connected
  components (`Graph.subset_openEdge_of_isPreconnected`, proved in
  `Schoenflies/Graph/PlaneEdges.lean`) — so it lies inside one open edge, and by closure the
  whole arc lies inside that one *closed* edge arc (`Graph.exists_edgeArc_superset`). An arc
  inside a polygonal arc is polygonal (`Schoenflies.IsArcBetween.isPolygonal_of_subset'`),
  wherever inside it sits — which matters, because the ends of the arc need not be vertices;
* otherwise, cut at an interior vertex parameter `t`. Each half is again an arc, by
  `Schoenflies.subarc`, with strictly fewer interior vertex parameters — the affine
  reparametrization is injective and carries them into the old ones, avoiding `t` — so each
  half is polygonal by recursion, and the two halves meet at the cut point, so their union is
  polygonal (`Schoenflies.IsPolygonal.union`).

No connectedness, admissibility or cell-structure hypothesis appears: the statement is a fact
about any finite plane graph with polygonal edge arcs, and the realization and generated-pair
forms are read off it.

## Blueprint

* `Graph.IsDrawing.isPolygonal_of_isArc` — the sentence "the path uses finitely many subarcs
  of target edges, all of which are polygonal; hence `P'` is polygonal" of the proof of
  `lem:skeleton-crosscuts`, for one finite plane graph.
* `Schoenflies.CellStructure.Realization.hasPolygonalArcs_of_isPolygonal` — the discharge of
  the named hypothesis `Realization.HasPolygonalArcs`.
* `Schoenflies.GeneratedPair.tgt_hasPolygonalArcs` — the instantiation on the target side of a
  generated matched cellulation, where `GeneratedPair.tgt_isPolygonal` supplies polygonality
  of every edge; the form `GeneratedPair.exists_anchor_crosscut` consumes.
-/

open Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- The parameters interior to `[0, 1]` at which an injective parametrization passes through a
drawn vertex form a finite set: injectivity maps them into the finite vertex set one-to-one. -/
theorem finite_interior_vertexParams [G.Finite] {f : ℝ → Plane} (hi : InjOn f I) :
    {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)}.Finite := by
  refine Set.Finite.of_finite_image ?_ (hi.mono fun t ht => Ioo_subset_I ht.1)
  refine (Graph.finite_vertexSet G).subset ?_
  rintro _ ⟨t, ⟨-, htV⟩, rfl⟩
  exact htV

/-- **An arc in a finite plane graph passing through no vertex in its interior lies inside one
closed edge arc.** The image of the open parameter interval is a connected subset of
`pointSet ∖ V(G)`, whose connected components are the open edges; taking closures recovers the
two endpoints, which may be vertices or interior points of the edge. -/
theorem exists_edgeArc_superset [G.Finite] (h : IsDrawing G drawing)
    {f : ℝ → Plane} (hc : ContinuousOn f I)
    (hQ : f '' I ⊆ pointSet G drawing)
    (hnov : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ V(G)) :
    ∃ e ∈ E(G), f '' I ⊆ edgeArc drawing e := by
  -- The interior of the arc misses the vertices, so it lives where the open edges are.
  have hA : f '' Ioo 0 1 ⊆ pointSet G drawing \ V(G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hQ (mem_image_of_mem f (Ioo_subset_I ht)), hnov t ht⟩
  have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hhalf : f (1 / 2 : ℝ) ∈ ⋃ e ∈ E(G), openEdge G drawing e := by
    rw [biUnion_openEdge]
    exact hA (mem_image_of_mem f hmid)
  obtain ⟨e, he, hemem⟩ := Set.mem_iUnion₂.1 hhalf
  -- The open edges are the components of `pointSet ∖ V(G)`, so the interior stays in this one.
  have hsub : f '' Ioo 0 1 ⊆ openEdge G drawing e :=
    subset_openEdge_of_isPreconnected h he
      (isPreconnected_Ioo.image f (hc.mono Ioo_subset_I)) hA
      ⟨f (1 / 2 : ℝ), mem_image_of_mem f hmid, hemem⟩
  -- The whole arc is the closure of its interior, and the closed edge arc is closed.
  have hcc : ContinuousOn f (closure (Ioo (0 : ℝ) 1)) := by
    rw [closure_Ioo (zero_ne_one (α := ℝ))]
    exact hc
  have hclos : f '' I ⊆ closure (f '' Ioo (0 : ℝ) 1) := by
    have h2 := hcc.image_closure
    rw [closure_Ioo (zero_ne_one (α := ℝ))] at h2
    exact h2
  exact ⟨e, he, hclos.trans (closure_minimal (hsub.trans openEdge_subset)
    (h.isCompact_edgeArc he).isClosed)⟩

/-- The vertex-free case of the recursion: an arc through no interior vertex lies inside one
closed edge arc, and an arc inside a polygonal arc is polygonal. -/
theorem isPolygonal_image_of_no_interior_vertex [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    {f : ℝ → Plane} (hc : ContinuousOn f I) (hi : InjOn f I)
    (hQ : f '' I ⊆ pointSet G drawing)
    (hnov : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ V(G)) : IsPolygonal (f '' I) := by
  obtain ⟨e, he, hsub⟩ := exists_edgeArc_superset h hc hQ hnov
  obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
  have hB : IsArcBetween (f '' I) (f 0) (f 1) := ⟨f, hc, hi, rfl, rfl, rfl⟩
  have h01 : f 0 ≠ f 1 := fun heq => zero_ne_one (α := ℝ) (hi zero_mem_I one_mem_I heq)
  exact (h.edge_isArcBetween hl).isPolygonal_of_subset' (hpoly e he) hB hsub h01

/-- The recursion of `lem:skeleton-crosscuts`' polygonality sentence, on the number of interior
parameters at drawn vertices: cut at one such parameter, recurse into the two subarcs, and glue
the two polygonal halves at the cut point. -/
theorem isPolygonal_image_of_subset_pointSet [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) :
    ∀ (n : ℕ) (f : ℝ → Plane), ContinuousOn f I → InjOn f I →
      f '' I ⊆ pointSet G drawing →
      {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)}.ncard ≤ n → IsPolygonal (f '' I) := by
  intro n
  induction n with
  | zero =>
    intro f hc hi hQ hcard
    refine isPolygonal_image_of_no_interior_vertex h hpoly hc hi hQ fun t ht htV => ?_
    -- Cardinality zero of a finite set means there is no interior vertex parameter at all.
    have hempty : {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)} = ∅ :=
      (Set.ncard_eq_zero (finite_interior_vertexParams hi)).1
        (Nat.le_zero.1 hcard)
    exact absurd (hempty ▸ (⟨ht, htV⟩ : t ∈ {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)}))
      (Set.notMem_empty t)
  | succ n ih =>
    intro f hc hi hQ hcard
    by_cases hS : {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)}.Nonempty
    case neg =>
      exact isPolygonal_image_of_no_interior_vertex h hpoly hc hi hQ
        fun t ht htV => hS ⟨t, ht, htV⟩
    case pos =>
      obtain ⟨t, htI, htV⟩ := hS
      have ht0 : (0 : ℝ) < t := htI.1
      have ht1 : t < 1 := htI.2
      have htmem : t ∈ I := Ioo_subset_I htI
      have hSfin : {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)}.Finite :=
        finite_interior_vertexParams hi
      -- Removing the cut parameter drops the count below the recursion bound.
      have hSd : ({u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)} \ {t}).ncard ≤ n := by
        have hlt := Set.ncard_sdiff_singleton_lt_of_mem
          (s := {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)}) (a := t) ⟨htI, htV⟩ hSfin
        omega
      -- The initial half, as a subarc: continuous, injective, inside the point set.
      have hc₁ : ContinuousOn (subarc f 0 t) I := continuousOn_subarc hc zero_mem_I htmem
      have hi₁ : InjOn (subarc f 0 t) I :=
        injOn_subarc (hi.mono (uIcc_subset_I zero_mem_I htmem)) ht0.ne
      have himg₁ : subarc f 0 t '' I = f '' Icc 0 t := by
        rw [subarc_image, uIcc_of_le ht0.le]
      have hQ₁ : subarc f 0 t '' I ⊆ pointSet G drawing :=
        (subarc_image_subset zero_mem_I htmem).trans hQ
      -- Its interior vertex parameters inject into the old ones, avoiding the cut.
      have hcard₁ : {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f 0 t s ∈ V(G)}.ncard ≤ n := by
        have himage : reparam 0 t '' {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f 0 t s ∈ V(G)} ⊆
            {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)} \ {t} := by
          rintro _ ⟨s, ⟨⟨hs0, hs1⟩, hsV⟩, rfl⟩
          have hval : reparam 0 t s = s * t := by simp [reparam]
          have hfV : f (s * t) ∈ V(G) := by rw [← hval]; exact hsV
          rw [hval]
          refine ⟨⟨⟨by positivity, by nlinarith⟩, hfV⟩, fun hst => ?_⟩
          rw [Set.mem_singleton_iff] at hst
          nlinarith [mul_pos ht0 (by linarith : (0 : ℝ) < 1 - s)]
        calc {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f 0 t s ∈ V(G)}.ncard
            = (reparam 0 t '' {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f 0 t s ∈ V(G)}).ncard :=
              ((reparam_injective ht0.ne).injOn.ncard_image).symm
          _ ≤ ({u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)} \ {t}).ncard :=
              Set.ncard_le_ncard himage (hSfin.sdiff)
          _ ≤ n := hSd
      -- The final half, the same way.
      have hc₂ : ContinuousOn (subarc f t 1) I := continuousOn_subarc hc htmem one_mem_I
      have hi₂ : InjOn (subarc f t 1) I :=
        injOn_subarc (hi.mono (uIcc_subset_I htmem one_mem_I)) ht1.ne
      have himg₂ : subarc f t 1 '' I = f '' Icc t 1 := by
        rw [subarc_image, uIcc_of_le ht1.le]
      have hQ₂ : subarc f t 1 '' I ⊆ pointSet G drawing :=
        (subarc_image_subset htmem one_mem_I).trans hQ
      have hcard₂ : {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f t 1 s ∈ V(G)}.ncard ≤ n := by
        have himage : reparam t 1 '' {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f t 1 s ∈ V(G)} ⊆
            {u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)} \ {t} := by
          rintro _ ⟨s, ⟨⟨hs0, hs1⟩, hsV⟩, rfl⟩
          have hval : reparam t 1 s = t + s * (1 - t) := by simp [reparam]
          have hfV : f (t + s * (1 - t)) ∈ V(G) := by rw [← hval]; exact hsV
          rw [hval]
          have hpos : (0 : ℝ) < s * (1 - t) := by positivity
          refine ⟨⟨⟨by linarith, by nlinarith⟩, hfV⟩, fun hst => ?_⟩
          rw [Set.mem_singleton_iff] at hst
          nlinarith
        calc {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f t 1 s ∈ V(G)}.ncard
            = (reparam t 1 '' {s | s ∈ Ioo (0 : ℝ) 1 ∧ subarc f t 1 s ∈ V(G)}).ncard :=
              ((reparam_injective ht1.ne).injOn.ncard_image).symm
          _ ≤ ({u | u ∈ Ioo (0 : ℝ) 1 ∧ f u ∈ V(G)} \ {t}).ncard :=
              Set.ncard_le_ncard himage (hSfin.sdiff)
          _ ≤ n := hSd
      -- Recurse into the halves and glue them at the cut point.
      have hpoly₁ : IsPolygonal (f '' Icc 0 t) := by
        rw [← himg₁]
        exact ih (subarc f 0 t) hc₁ hi₁ hQ₁ hcard₁
      have hpoly₂ : IsPolygonal (f '' Icc t 1) := by
        rw [← himg₂]
        exact ih (subarc f t 1) hc₂ hi₂ hQ₂ hcard₂
      have hsplit : f '' I = f '' Icc 0 t ∪ f '' Icc t 1 := by
        rw [← image_union, Icc_union_Icc_eq_Icc ht0.le ht1.le]
      rw [hsplit]
      exact hpoly₁.union hpoly₂
        ⟨f t, mem_image_of_mem f (right_mem_Icc.2 ht0.le),
          mem_image_of_mem f (left_mem_Icc.2 ht1.le)⟩

/-- **An arc in the point set of a finite plane graph with polygonal edge arcs is polygonal.**
The set-level form: the parametrization is unpacked here and the recursion above does the
work. -/
theorem IsDrawing.isPolygonal_of_isArc [G.Finite] (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e))
    {Q : Set Plane} (hQ : Q ⊆ pointSet G drawing) (harc : IsArc Q) : IsPolygonal Q := by
  obtain ⟨f, hc, hi, rfl⟩ := harc
  exact isPolygonal_image_of_subset_pointSet h hpoly _ f hc hi hQ le_rfl

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- **Discharge of the named hypothesis `Realization.HasPolygonalArcs`.** A realization all of
whose edge arcs are polygonal has every arc in its skeleton polygonal: the realized skeleton is
the point set of the finite drawn graph, and `Graph.IsDrawing.isPolygonal_of_isArc` applies.
The hypothesis is stated with the strict-implicit binder of `GeneratedPair.tgt_isPolygonal`, so
that field discharges it directly. -/
theorem Realization.hasPolygonalArcs_of_isPolygonal (R : S.Realization)
    (hpoly : ∀ ⦃e⦄, e ∈ E(S.skel) → IsPolygonal (Graph.edgeArc R.drawing e)) :
    R.HasPolygonalArcs := by
  intro Q hQ harc
  -- Name the drawn graph so the `Graph.Finite` instance on `R.graph` is found syntactically.
  have hdraw : Graph.IsDrawing R.graph R.drawing := R.isDrawing
  refine hdraw.isPolygonal_of_isArc (fun e he => ?_) hQ harc
  rw [Realization.edgeSet_graph] at he
  exact hpoly he

end CellStructure

/-- **The target side of a generated matched cellulation has polygonal arcs** — the acceptance
test of the named hypothesis: `GeneratedPair.tgt_isPolygonal` says every target edge arc is
polygonal, and that is all the discharge needs. `GeneratedPair.exists_anchor_crosscut` and
`GeneratedPair.exists_anchor_crosscut_stage` consume this as their `hpoly` argument. -/
theorem GeneratedPair.tgt_hasPolygonalArcs {γ : Type*} {S₀ : CellStructure γ}
    {srcOuter srcDom tgtOuter tgtDom : Set Plane}
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    P.tgt.HasPolygonalArcs :=
  P.tgt.hasPolygonalArcs_of_isPolygonal P.tgt_isPolygonal

end Schoenflies
