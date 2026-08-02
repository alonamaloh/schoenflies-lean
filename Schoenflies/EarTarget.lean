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

namespace Schoenflies

open CellStructure Graph

/-! ### The ear, transported

The target drawing of the ear is the source drawing composed with a homeomorphism of the two
arcs. Both are functions of `φ` alone, so they are `def`s and everything below is a lemma about
them rather than an existential. -/

variable {γ : Type*}

/-- Where the transported ear puts each 0-cell. -/
def transportPos (φ : Plane → Plane) (earPos : γ → Plane) : γ → Plane := fun c => φ (earPos c)

/-- How the transported ear draws each 1-cell. -/
def transportDraw (φ : Plane → Plane) (earDraw : γ → ℝ → Plane) : γ → ℝ → Plane :=
  fun f => φ ∘ earDraw f

namespace CellStructure.SplitData

variable {S : CellStructure γ} {d : S.SplitData} {R₁ R₂ : S.Realization} {earPos₁ : γ → Plane}
  {earDraw₁ : γ → ℝ → Plane} {φ ψ : Plane → Plane}

theorem earGraph_transportPos :
    d.earGraph (transportPos φ earPos₁) = (d.earGraph earPos₁).map φ := by
  rw [earGraph, earGraph, Graph.map_map]
  rfl

/-- **The transported ear occupies the image of the source ear.** -/
theorem earSet_transportPos :
    d.earSet (transportPos φ earPos₁) (transportDraw φ earDraw₁)
      = φ '' d.earSet earPos₁ earDraw₁ := by
  rw [earSet, earSet, earGraph_transportPos]
  exact Graph.pointSet_map

/-- **The transported ear is a crosscut of the corresponding target 2-cell.**

Every field is the source field pushed forward: the two ends go where `φ` sends them, the
drawing is a plane graph by `Graph.IsDrawing.map_of_injOn`, and the two geometric clauses are
statements about the image arc `Pset`, which the caller supplies from
`Schoenflies.exists_target_ear`. -/
theorem earCrosscut_transport (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hφc : ContinuousOn φ (d.earSet earPos₁ earDraw₁))
    (hφi : InjOn φ (d.earSet earPos₁ earDraw₁))
    (hφs : φ (R₁.pos d.source) = R₂.pos d.source)
    (hφt : φ (R₁.pos d.target) = R₂.pos d.target)
    {Pset : Set Plane} (hφimg : φ '' d.earSet earPos₁ earDraw₁ = Pset)
    (hPpoly : IsPolygonal Pset)
    (hPsub : Pset \ {R₂.pos d.source, R₂.pos d.target} ⊆ R₂.cell d.face)
    (hdisj : Disjoint (R₂.cell d.face) R₂.skeletonSet) :
    d.EarCrosscut R₂ (transportPos φ earPos₁) (transportDraw φ earDraw₁) where
  pos_source := by rw [transportPos, hE₁.pos_source, hφs]
  pos_target := by rw [transportPos, hE₁.pos_target, hφt]
  injOn := fun _ hx _ hy h =>
    hE₁.injOn hx hy (hφi (EarCrosscut.mem_earSet_of_mem_ear hx)
      (EarCrosscut.mem_earSet_of_mem_ear hy) h)
  isDrawing := by
    rw [earGraph_transportPos]
    exact hE₁.isDrawing.map_of_injOn hφc hφi
  subset_face := by rw [earSet_transportPos, hφimg]; exact hPsub
  disjoint_skeleton := hdisj
  polygonal := by rw [earSet_transportPos, hφimg]; exact hPpoly

/-- **The chosen homeomorphism between the two drawn ears is the transporting map itself.**

This is the payoff of transporting rather than cutting: `earPos_apply` and `edgeArc_image` — the
two clauses of `CellStructure.SplitData.EarHomeo` that match cell for cell — hold by definition,
because the target ear *is* the image of the source one. -/
def earHomeo_transport (hφc : ContinuousOn φ (d.earSet earPos₁ earDraw₁))
    (hψc : ContinuousOn ψ (φ '' d.earSet earPos₁ earDraw₁))
    (hleft : LeftInvOn ψ φ (d.earSet earPos₁ earDraw₁))
    (hright : RightInvOn ψ φ (φ '' d.earSet earPos₁ earDraw₁)) :
    d.EarHomeo earPos₁ earDraw₁ (transportPos φ earPos₁) (transportDraw φ earDraw₁) where
  toFun := φ
  invFun := ψ
  continuousOn_toFun := hφc
  continuousOn_invFun := by rw [earSet_transportPos]; exact hψc
  leftInvOn := hleft
  rightInvOn := by rw [earSet_transportPos]; exact hright
  earPos_apply := fun _ _ => rfl
  edgeArc_image := fun _ _ => (Graph.edgeArc_map _).symm

end CellStructure.SplitData

/-- **The target half of one ear insertion.**

The target crosscut `Pset` is a polygonal arc between the two corresponding 0-cells whose
interior lies in the target 2-cell — exactly what `Schoenflies.exists_target_ear` produces. The
drawn source ear is an arc between the source ends, so the two are homeomorphic by a map
matching the ends, and the target ear is the image of the source one under it.

What comes out is the second `SplitData.EarCrosscut` — the input to `SplitData.realize` on the
target side — together with the `SplitData.EarHomeo` that `SplitData.splitHomeo` needs to carry
the skeleton homeomorphism across the split. -/
theorem exists_target_earCrosscut {S : CellStructure γ} {d : S.SplitData}
    {R₁ R₂ : S.Realization} {earPos₁ : γ → Plane} {earDraw₁ : γ → ℝ → Plane}
    (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    {Pset : Set Plane} (hPpoly : IsPolygonal Pset)
    (hParc : IsArcBetween Pset (R₂.pos d.source) (R₂.pos d.target))
    (hPsub : Pset \ {R₂.pos d.source, R₂.pos d.target} ⊆ R₂.cell d.face)
    (hdisj : Disjoint (R₂.cell d.face) R₂.skeletonSet) :
    ∃ (earPos₂ : γ → Plane) (earDraw₂ : γ → ℝ → Plane)
      (_ : d.EarCrosscut R₂ earPos₂ earDraw₂),
      d.earSet earPos₂ earDraw₂ = Pset ∧
        Nonempty (d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) := by
  obtain ⟨φ, ψ, hφc, hψc, hleft, hright, himg, hφs, hφt⟩ :=
    exists_arc_homeo hE₁.isArcBetween_earSet hParc
  refine ⟨transportPos φ earPos₁, transportDraw φ earDraw₁,
    CellStructure.SplitData.earCrosscut_transport hE₁ hφc (hleft.injOn) hφs hφt himg hPpoly
      hPsub hdisj, by rw [CellStructure.SplitData.earSet_transportPos, himg], ⟨?_⟩⟩
  exact CellStructure.SplitData.earHomeo_transport hφc (by rw [himg]; exact hψc) hleft
    (by rw [himg]; exact hright)

end Schoenflies
