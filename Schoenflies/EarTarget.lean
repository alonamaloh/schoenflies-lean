/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.EarSource
import Schoenflies.MatchedSplit
import Schoenflies.InitialPair

/-!
# The ear on the target side

The source ear is drawn where the extension graph draws it; the target ear has no such
constraint — the only thing fixed on the target side is the *crosscut*
`Schoenflies.exists_target_ear` produces, a polygonal arc inside the target 2-cell between the
two corresponding 0-cells. The ear then has to be cut into that arc with the same combinatorics
as on the source side: the same edges, in the same order, meeting at the same vertices.

## Transport, not subdivision

The obvious route is to cut the target arc at prescribed parameters. This module takes the other
one: **push the source drawing forward along a homeomorphism of the two arcs.** Both drawn ears
are arcs between their ends, so `Schoenflies.exists_arc_homeo` gives a homeomorphism `φ` matching
the ends, and the target ear is *defined* as `φ ∘ (source ear)`, vertex for vertex and edge for
edge.

Two things fall out that the parameter route would have had to prove.

* The target drawing is a plane graph — `Graph.IsDrawing.map_of_injOn`, which is the general
  fact that a plane graph pushed forward along an injection continuous on its point set is a
  plane graph. Nothing about arcs enters.
* The chosen homeomorphism of `CellStructure.SplitData.EarHomeo` is `φ` itself, and its two
  matching clauses hold **by definition** rather than by a computation with parameters. That is
  the whole reason `Schoenflies/MatchedSplit.lean` asks for the ear map as data: see its section
  "How the ear map is presented, and why".

## Blueprint

* `Schoenflies.exists_arc_homeo` — a homeomorphism between two arcs matching their prescribed
  ends. Not a blueprint statement; it is what "let `F*, v*, w*` be the corresponding face and
  endpoints in the other realization" needs to become a drawing.
* `Graph.IsDrawing.map_of_injOn`, `Graph.pointSet_map` — a drawn graph pushed forward.

## One import that is in the wrong place

`Schoenflies.continuousOn_invFunOn_image` — *a continuous injection of a compact set has a
continuous inverse on its image* — is a general topology fact and lives in
`Schoenflies/InitialPair.lean`, where it was first needed. It is the only thing this module
takes from there, and the import is otherwise dead weight. The honest fix is for the integrator
to hoist it into `Schoenflies/Topology.lean` and drop the import; it is not restated here.
-/

open Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ### A homeomorphism between two arcs -/

/-- **Two arcs with prescribed ends are homeomorphic by a map matching the ends.**

Both parametrizations are continuous injections of the compact `I`, so each has a continuous
inverse on its image (`Schoenflies.continuousOn_invFunOn_image`), and the composite of one with
the other's inverse is the homeomorphism. It is *the* parameter-matching one: the target ear
below is defined as the source ear's image under it, which is why nothing here has to be chosen
twice. -/
theorem exists_arc_homeo {A B : Set Plane} {p q p' q' : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p' q') :
    ∃ φ ψ : Plane → Plane, ContinuousOn φ A ∧ ContinuousOn ψ B ∧
      LeftInvOn ψ φ A ∧ RightInvOn ψ φ B ∧ φ '' A = B ∧ φ p = p' ∧ φ q = q' := by
  obtain ⟨f, hfc, hfi, rfl, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, rfl, hg0, hg1⟩ := hB
  have hmapf : MapsTo (Function.invFunOn f I) (f '' I) I := fun _ hy =>
    Function.invFunOn_mem (by rwa [Set.image, Set.mem_setOf_eq] at hy)
  have hmapg : MapsTo (Function.invFunOn g I) (g '' I) I := fun _ hy =>
    Function.invFunOn_mem (by rwa [Set.image, Set.mem_setOf_eq] at hy)
  have himf : Function.invFunOn f I '' (f '' I) = I :=
    Set.Subset.antisymm (Set.image_subset_iff.2 hmapf)
      fun s hs => ⟨f s, ⟨s, hs, rfl⟩, hfi.leftInvOn_invFunOn hs⟩
  have himg : Function.invFunOn g I '' (g '' I) = I :=
    Set.Subset.antisymm (Set.image_subset_iff.2 hmapg)
      fun s hs => ⟨g s, ⟨s, hs, rfl⟩, hgi.leftInvOn_invFunOn hs⟩
  refine ⟨g ∘ Function.invFunOn f I, f ∘ Function.invFunOn g I,
    hgc.comp (continuousOn_invFunOn_image isCompact_I hfc hfi) hmapf,
    hfc.comp (continuousOn_invFunOn_image isCompact_I hgc hgi) hmapg, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y hy
    have hs : Function.invFunOn f I y ∈ I := hmapf hy
    simp only [Function.comp_apply, hgi.leftInvOn_invFunOn hs]
    exact Function.invFunOn_eq (by rwa [Set.image, Set.mem_setOf_eq] at hy)
  · rintro y hy
    have hs : Function.invFunOn g I y ∈ I := hmapg hy
    simp only [Function.comp_apply, hfi.leftInvOn_invFunOn hs]
    exact Function.invFunOn_eq (by rwa [Set.image, Set.mem_setOf_eq] at hy)
  · rw [Set.image_comp, himf]
  · rw [← hf0, ← hg0, Function.comp_apply, hfi.leftInvOn_invFunOn zero_mem_I]
  · rw [← hf1, ← hg1, Function.comp_apply, hfi.leftInvOn_invFunOn one_mem_I]

end Schoenflies

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drw : β → ℝ → Plane} {φ : Plane → Plane}

theorem edgeArc_map (e : β) : edgeArc (fun f => φ ∘ drw f) e = φ '' edgeArc drw e := by
  rw [edgeArc, edgeArc, Set.image_comp]

/-- A drawn graph pushed forward occupies the image of what it occupied. -/
theorem pointSet_map : pointSet (G.map φ) (fun f => φ ∘ drw f) = φ '' pointSet G drw := by
  rw [pointSet, pointSet, vertexSet_map, edgeSet_map, Set.image_union, Set.image_iUnion₂]
  exact congrArg _ (Set.iUnion₂_congr fun e _ => edgeArc_map e)

/-- **A plane graph pushed forward along an injection continuous on its point set is a plane
graph.** Every clause is the old clause pulled back through the injection: two points of the
image coincide only if their preimages do, which is what turns each of the three conditions
into its own image. -/
theorem IsDrawing.map_of_injOn (h : IsDrawing G drw) (hcont : ContinuousOn φ (pointSet G drw))
    (hinj : InjOn φ (pointSet G drw)) : IsDrawing (G.map φ) (fun f => φ ∘ drw f) where
  edge_param := by
    intro e he
    rw [edgeSet_map] at he
    obtain ⟨hc, hi, hl⟩ := h.edge_param he
    have hsub : MapsTo (drw e) I (pointSet G drw) := fun t ht =>
      edgeArc_subset_pointSet he ⟨t, ht, rfl⟩
    exact ⟨hcont.comp hc hsub, hinj.comp hi hsub, hl.map φ⟩
  vertex_mem_edgeArc := by
    intro e x y vv hlk hv hmem
    obtain ⟨p, q, hpq, rfl, rfl⟩ := hlk
    rw [vertexSet_map] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    rw [edgeArc_map] at hmem
    obtain ⟨u, hu, heq⟩ := hmem
    obtain rfl : v' = u := hinj (vertexSet_subset_pointSet hv')
      (edgeArc_subset_pointSet hpq.edge_mem hu) heq.symm
    rcases h.vertex_mem_edgeArc hpq hv' hu with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  edge_inter := by
    intro e f he hf hef p hpe hpf
    rw [edgeSet_map] at he hf
    rw [edgeArc_map] at hpe hpf
    obtain ⟨x, hx, rfl⟩ := hpe
    obtain ⟨y, hy, heq⟩ := hpf
    have hxf : x ∈ edgeArc drw f := by
      have hyx : y = x := hinj (edgeArc_subset_pointSet hf hy)
        (edgeArc_subset_pointSet he hx) heq
      rwa [hyx] at hy
    obtain ⟨hxV, hIe, hIf⟩ := h.edge_inter he hf hef hx hxf
    exact ⟨by rw [vertexSet_map]; exact ⟨x, hxV, rfl⟩, hIe.map φ, hIf.map φ⟩

end Graph
