/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshTwoConnected
import Schoenflies.Graph.Subdivision
import Schoenflies.ArcComplementPrep

/-!
# The mesh side of the overlay core: `Schoenflies.HasTwoConnectedMeshCores`, discharged

`Schoenflies.HasTwoConnectedMeshCores` (`Schoenflies/MeshTwoConnected.lean`) asks, at every
admissible stage, mesh size, valid fresh list with two distinct points and `JoinsFor` list,
for a 2-connected subgraph of `Schoenflies.meshOverlayGraph` containing every overlay vertex
on the mesh. This module builds it: the subgraph is the overlay of the mesh segments alone at
the *overlay's own* cut points, `overlayGraph (meshSegments (meshCount ε) fresh)
(meshOverlayPoints P ε fresh joins)`.

Three facts assemble the discharge.

* **The mesh-restricted overlay is a subgraph of the full overlay** —
  `Schoenflies.overlayGraph_mono_pieces`: `subdivide` is monotone in the piece list
  (`Schoenflies.subdivide_mono`), and orienting and deduplicating preserve membership.
* **Its vertices are exactly the overlay vertices on the mesh** — an overlay vertex is a cut
  point (`Schoenflies.overlayPieces_ends_cut`), and a cut point on a mesh segment is a vertex
  of the mesh-restricted overlay (`Schoenflies.overlay_mem_vertexSet_of_cut`).
* **It is 2-connected.** Taking the overlay's cut points as the *anchors* of
  `Schoenflies.meshGraph` makes `meshGraph (meshCount ε) fresh pts` — 2-connected by
  `Schoenflies.meshGraph_isTwoConnected` from the two distinct fresh points — literally the
  overlay `overlayGraph (meshSegments …) (pts ++ meshCutPoints …)`: the same segments, cut at
  the same points *plus* the mesh's own. Removing those extra points one at a time undoes one
  single-vertex subdivision each (`Schoenflies.overlayGraph_snoc_isSubdivisionOf`: a point
  interior to an overlay edge is interior to exactly one, because distinct overlay edges have
  disjoint interiors), and **2-connectivity descends along a subdivision**
  (`Graph.IsSubdivisionOf.isTwoConnected_descend`) — the genuinely new graph theory here, the
  converse of `Graph.IsSubdivisionOf.isTwoConnected`.

The descent needs the coarse graph to keep three vertices — a triangle is a subdivision of the
two-vertex banana, which this repository's convention rightly refuses to call 2-connected — and
the mesh always has them: three corners of the outer ring.

The `Graph`-namespace results (`Graph.reaches_of_collapse`,
`Graph.IsSubdivisionOf.connected_descend`, `Graph.IsSubdivisionOf.isTwoConnected_descend`) are
general-purpose and are candidates for hoisting into `Schoenflies/Graph/Subdivision.lean`;
`Schoenflies.subdivide_points_append` belongs beside `Schoenflies.subdivide_append` and
`Schoenflies.subdivide_mono`.

## Blueprint

* `Graph.reaches_of_collapse`, `Graph.IsSubdivisionOf.connected_descend`,
  `Graph.IsSubdivisionOf.isTwoConnected_descend` — the converse half of
  `lem:subdivision-ear-preserve`(a): un-subdividing an edge preserves connectedness and
  2-connectedness.
* `overlayGraph_snoc_of_no_interior`, `overlayGraph_snoc_isSubdivisionOf` — one extra cut
  point refines an overlay by exactly one single-vertex subdivision, or not at all.
* `overlayGraph_isTwoConnected_of_extend` — 2-connectivity of an overlay does not depend on
  cut points beyond the required ones: it descends from any extension of the cut list.
* `hasTwoConnectedMeshCores` — **the discharge**: `Schoenflies.HasTwoConnectedMeshCores`
  holds outright, via the subdivision bridge of `lem:polygonal-overlay` seeded by
  `prop:anchored-square-mesh` clause 5.
-/

open Metric Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G G' H H' : Graph α β} {e e₁ e₂ f : β} {x y v t z u w : α}

/-! ### Collapsing a vertex

The walk-transfer engine behind un-subdividing: if every link of `H'` between two vertices
other than `v` is matched by reachability in `H`, and every link of `H'` *at* `v` is matched
by reachability from a fixed target `t`, then reachability between non-`v` vertices descends
from `H'` to `H`. Applied four times below: to the subdivision itself and to its three kinds
of one-vertex deletions. (General-purpose; a candidate for hoisting into
`Schoenflies/Graph/Subdivision.lean`.) -/

/-- **Reachability descends along a vertex collapse.** Every passage of an `H'`-walk through
`v` enters and leaves along links at `v`, each of which `H` can answer from the collapse
target `t`; every other step `H` answers directly. -/
theorem reaches_of_collapse (ht : t ∈ V(H))
    (hV : ∀ a ∈ V(H'), a ≠ v → a ∈ V(H))
    (hlink : ∀ f a b, H'.IsLink f a b → a ≠ v → b ≠ v → H.Reaches a b)
    (hlinkv : ∀ f b, H'.IsLink f v b → b ≠ v → H.Reaches t b)
    {u w : α} (hr : H'.Reaches u w) (hu : u ≠ v) (hw : w ≠ v) : H.Reaches u w := by
  classical
  suffices key : ∀ a b, H'.Reaches a b →
      H.Reaches (if a = v then t else a) (if b = v then t else b) by
    have h := key u w hr
    rwa [if_neg hu, if_neg hw] at h
  intro a₀ b₀ hab
  obtain ⟨W, hW⟩ := hab
  induction hW with
  | @nil a ha =>
    by_cases hav : a = v
    · rw [if_pos hav]
      exact Reaches.refl ht
    · rw [if_neg hav]
      exact Reaches.refl (hV _ ha hav)
  | @cons a c b f W hl hW ih =>
    refine Reaches.trans ?_ ih
    by_cases hav : a = v <;> by_cases hcv : c = v
    · rw [if_pos hav, if_pos hcv]
      exact Reaches.refl ht
    · subst hav
      rw [if_pos rfl, if_neg hcv]
      exact hlinkv f c hl hcv
    · subst hcv
      rw [if_neg hav, if_pos rfl]
      exact (hlinkv f a hl.symm hav).symm
    · rw [if_neg hav, if_neg hcv]
      exact hlink f a c hl hav hcv

namespace IsSubdivisionOf

variable (h : IsSubdivisionOf G' G e x y v e₁ e₂)
include h

/-- **Connectedness descends across a subdivision** — the converse of
`Graph.IsSubdivisionOf.connected`. The collapse target is `x`: both new edges answer to it,
one by reflexivity and one by the subdivided edge itself. -/
theorem connected_descend (hG' : G'.Connected) : G.Connected := by
  refine Connected.of_hub h.isLink.left_mem fun u hu => ?_
  have hxv : x ≠ v := fun hh => h.newVertex_notMem (hh ▸ h.isLink.left_mem)
  refine reaches_of_collapse (v := v) h.isLink.left_mem ?_ ?_ ?_
    (hG'.reaches h.left_mem (h.mem_vertexSet_of_mem hu)) hxv
    (fun hh => h.newVertex_notMem (hh ▸ hu))
  · intro a ha hav
    rw [h.vertexSet_eq] at ha
    exact ha.resolve_left hav
  · intro f a b hl hav hbv
    rcases (h.isLink_iff f a b).1 hl with ⟨hold, -⟩ | ⟨-, hs⟩ | ⟨-, hs⟩
    · exact Reaches.of_isLink hold
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd rfl hbv, absurd rfl hav]
    · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [absurd rfl hav, absurd rfl hbv]
  · intro f b hl hbv
    rcases (h.isLink_iff f v b).1 hl with ⟨hold, -⟩ | ⟨-, hs⟩ | ⟨-, hs⟩
    · exact absurd hold.left_mem h.newVertex_notMem
    · rcases Sym2.eq_iff.1 hs with ⟨-, hbv'⟩ | ⟨-, rfl⟩
      · exact absurd hbv' hbv
      · exact Reaches.refl h.isLink.left_mem
    · rcases Sym2.eq_iff.1 hs with ⟨-, rfl⟩ | ⟨-, hbv'⟩
      · exact Reaches.of_isLink h.isLink
      · exact absurd hbv' hbv

/-- **2-connectivity descends across a subdivision** — the converse of
`Graph.IsSubdivisionOf.isTwoConnected`. Both side conditions are honest: for `x ≠ y` the loop
that subdivides to a two-edge cycle, and for `HasThreeVertices` the banana whose subdivision
is a triangle — the triangle is 2-connected and the banana, on two vertices, is not. -/
theorem isTwoConnected_descend (hG' : G'.IsTwoConnected) (hxy : x ≠ y)
    (h3 : G.HasThreeVertices) : G.IsTwoConnected where
  hasThreeVertices := h3
  connected := h.connected_descend hG'.connected
  deleteVerts_connected := by
    intro z hz
    have hzv : z ≠ v := fun hh => h.newVertex_notMem (hh ▸ hz)
    by_cases hzx : z = x
    · -- deleting `x`: collapse to `y`, which the surviving new edge `e₂` answers.
      subst hzx
      have hyz : y ≠ z := Ne.symm hxy
      have hty : y ∈ V(G.deleteVerts {z}) :=
        mem_deleteVerts_singleton_of_ne h.isLink.right_mem hyz
      refine Connected.of_hub hty fun u hu => ?_
      rw [mem_deleteVerts_singleton] at hu
      have huv : u ≠ v := fun hh => h.newVertex_notMem (hh ▸ hu.1)
      have hr : (G'.deleteVerts {z}).Reaches y u :=
        (hG'.deleteVerts_connected (h.mem_vertexSet_of_mem hz)).reaches
          (mem_deleteVerts_singleton_of_ne h.right_mem hyz)
          (mem_deleteVerts_singleton_of_ne (h.mem_vertexSet_of_mem hu.1) hu.2)
      refine reaches_of_collapse (v := v) hty ?_ ?_ ?_ hr
        (fun hh => h.newVertex_notMem (hh ▸ h.isLink.right_mem)) huv
      · intro a ha hav
        rw [mem_deleteVerts_singleton] at ha ⊢
        rw [h.vertexSet_eq] at ha
        exact ⟨ha.1.resolve_left hav, ha.2⟩
      · intro f a b hl hav hbv
        rw [deleteVerts_isLink] at hl
        obtain ⟨hl', ha, hb⟩ := hl
        rcases (h.isLink_iff f a b).1 hl' with ⟨hold, -⟩ | ⟨-, hs⟩ | ⟨-, hs⟩
        · exact Reaches.of_isLink ((deleteVerts_isLink _ _).2 ⟨hold, ha, hb⟩)
        · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          exacts [absurd rfl hbv, absurd rfl hav]
        · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          exacts [absurd rfl hav, absurd rfl hbv]
      · intro f b hl hbv
        rw [deleteVerts_isLink] at hl
        obtain ⟨hl', -, hb⟩ := hl
        rcases (h.isLink_iff f v b).1 hl' with ⟨hold, -⟩ | ⟨-, hs⟩ | ⟨-, hs⟩
        · exact absurd hold.left_mem h.newVertex_notMem
        · -- `e₁` ran to the deleted `x`; both readings contradict a survivor.
          rcases Sym2.eq_iff.1 hs with ⟨-, hbv'⟩ | ⟨-, rfl⟩
          exacts [absurd hbv' hbv, absurd (mem_singleton _) hb]
        · rcases Sym2.eq_iff.1 hs with ⟨-, rfl⟩ | ⟨-, hbv'⟩
          · exact Reaches.refl hty
          · exact absurd hbv' hbv
    · -- deleting anything else: collapse to `x`.
      have hxz : x ≠ z := Ne.symm hzx
      have htx : x ∈ V(G.deleteVerts {z}) :=
        mem_deleteVerts_singleton_of_ne h.isLink.left_mem hxz
      refine Connected.of_hub htx fun u hu => ?_
      rw [mem_deleteVerts_singleton] at hu
      have huv : u ≠ v := fun hh => h.newVertex_notMem (hh ▸ hu.1)
      have hr : (G'.deleteVerts {z}).Reaches x u :=
        (hG'.deleteVerts_connected (h.mem_vertexSet_of_mem hz)).reaches
          (mem_deleteVerts_singleton_of_ne h.left_mem hxz)
          (mem_deleteVerts_singleton_of_ne (h.mem_vertexSet_of_mem hu.1) hu.2)
      refine reaches_of_collapse (v := v) htx ?_ ?_ ?_ hr
        (fun hh => h.newVertex_notMem (hh ▸ h.isLink.left_mem)) huv
      · intro a ha hav
        rw [mem_deleteVerts_singleton] at ha ⊢
        rw [h.vertexSet_eq] at ha
        exact ⟨ha.1.resolve_left hav, ha.2⟩
      · intro f a b hl hav hbv
        rw [deleteVerts_isLink] at hl
        obtain ⟨hl', ha, hb⟩ := hl
        rcases (h.isLink_iff f a b).1 hl' with ⟨hold, -⟩ | ⟨-, hs⟩ | ⟨-, hs⟩
        · exact Reaches.of_isLink ((deleteVerts_isLink _ _).2 ⟨hold, ha, hb⟩)
        · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          exacts [absurd rfl hbv, absurd rfl hav]
        · rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          exacts [absurd rfl hav, absurd rfl hbv]
      · intro f b hl hbv
        rw [deleteVerts_isLink] at hl
        obtain ⟨hl', -, hb⟩ := hl
        rcases (h.isLink_iff f v b).1 hl' with ⟨hold, -⟩ | ⟨-, hs⟩ | ⟨-, hs⟩
        · exact absurd hold.left_mem h.newVertex_notMem
        · rcases Sym2.eq_iff.1 hs with ⟨-, hbv'⟩ | ⟨-, rfl⟩
          · exact absurd hbv' hbv
          · exact Reaches.refl htx
        · rcases Sym2.eq_iff.1 hs with ⟨-, rfl⟩ | ⟨-, hbv'⟩
          · -- `e₂` survives whole: `y` is not the deleted vertex, its end `b = y` says so.
            refine Reaches.of_isLink ((deleteVerts_isLink _ _).2 ⟨h.isLink, ?_, hb⟩)
            simpa using hxz
          · exact absurd hbv' hbv

end IsSubdivisionOf

end Graph

namespace Schoenflies

variable {pieces : List Piece} {points : List Plane} {p : Plane}

/-! ### One extra cut point, at the end of the list

`subdivide` recurses on the head of the point list, so appending a point *cuts last*: the
result is one `splitAllAt` applied to the finished subdivision. At the level of the overlay
graph that one cut is either nothing at all — the point was interior to no edge — or exactly
one single-vertex subdivision, because distinct overlay edges have disjoint interiors
(`Schoenflies.overlayPieces_disjoint_interiors`). -/

/-- Subdividing at an appended point list is subdividing twice.
(General-purpose; a candidate for hoisting into `Schoenflies/Subdivide.lean` beside
`Schoenflies.subdivide_append`.) -/
theorem subdivide_points_append :
    ∀ (ps : List Plane) (pieces : List Piece) (qs : List Plane),
      subdivide pieces (ps ++ qs) = subdivide (subdivide pieces ps) qs := by
  intro ps
  induction ps with
  | nil => intro pieces qs; rfl
  | cons r rs ih =>
    intro pieces qs
    rw [List.cons_append, subdivide_cons, subdivide_cons, ih]

/-- Appending one cut point cuts the finished subdivision once. -/
theorem subdivide_snoc (pieces : List Piece) (points : List Plane) (p : Plane) :
    subdivide pieces (points ++ [p]) = splitAllAt p (subdivide pieces points) := by
  rw [subdivide_points_append, subdivide_cons, subdivide_nil]

/-- A cut point interior to no edge changes the overlay not at all — on the nose. -/
theorem overlayGraph_snoc_of_no_interior
    (hnone : ∀ Q ∈ subdivide pieces points, p ∉ Q.interior) :
    overlayGraph pieces (points ++ [p]) = overlayGraph pieces points := by
  have hlist : overlayPieces pieces (points ++ [p]) = overlayPieces pieces points := by
    unfold overlayPieces
    rw [subdivide_snoc, splitAllAt_eq_self hnone]
  exact Graph.ext (by rw [overlayGraph_vertexSet, overlayGraph_vertexSet, hlist])
    fun f a b => by rw [overlayGraph_isLink, overlayGraph_isLink, hlist]

/-- **A cut point interior to some edge subdivides the overlay at exactly that edge.** The
uniqueness is `Schoenflies.overlayPieces_disjoint_interiors`; the two halves, oriented, are
the two new edges, and neither can be an old edge because each has the new point — which is
not a cut point — as an end. -/
theorem overlayGraph_snoc_isSubdivisionOf (hnd : ∀ P ∈ pieces, P.Nondeg)
    (hEnds : EndsAreCut pieces points) (hMeets : MeetsAreCut pieces points)
    {Q₀ : Piece} (hQ₀ : Q₀ ∈ subdivide pieces points) (hp : p ∈ Q₀.interior) :
    ∃ e f₁ f₂ : Piece, e.Nondeg ∧
      Graph.IsSubdivisionOf (overlayGraph pieces (points ++ [p]))
        (overlayGraph pieces points) e e.1 e.2 p f₁ f₂ := by
  classical
  set e := orientPiece Q₀ with hedef
  set f₁ := orientPiece (e.1, p) with hf₁def
  set f₂ := orientPiece (p, e.2) with hf₂def
  have hpe : p ∈ e.interior := by rw [hedef, orientPiece_interior]; exact hp
  have heE : e ∈ overlayPieces pieces points := mem_overlayPieces.2 ⟨Q₀, hQ₀, rfl⟩
  have hend : e.Nondeg := overlayPieces_nondeg points hnd e heE
  have hppts : p ∉ points := fun hpp => subdivide_avoids points hnd p hpp Q₀ hQ₀ hp
  have hp1 : p ≠ e.1 := fun hh => hend (left_mem_openSegment_iff.1 (hh ▸ hpe))
  have hp2 : p ≠ e.2 := fun hh => hend (right_mem_openSegment_iff.1 (hh ▸ hpe))
  -- which points the two halves have as ends
  have hf₁ends : f₁ = (e.1, p) ∨ f₁ = (p, e.1) := by
    rw [hf₁def]
    by_cases hh : Precedes e.1 p
    · exact Or.inl (orientPiece_of_precedes hh)
    · exact Or.inr (orientPiece_of_not_precedes hh)
  have hf₂ends : f₂ = (p, e.2) ∨ f₂ = (e.2, p) := by
    rw [hf₂def]
    by_cases hh : Precedes p e.2
    · exact Or.inl (orientPiece_of_precedes hh)
    · exact Or.inr (orientPiece_of_not_precedes hh)
  have hf₁p : p = f₁.1 ∨ p = f₁.2 := by
    rcases hf₁ends with h | h <;> rw [h]
    exacts [Or.inr rfl, Or.inl rfl]
  have hf₂p : p = f₂.1 ∨ p = f₂.2 := by
    rcases hf₂ends with h | h <;> rw [h]
    exacts [Or.inl rfl, Or.inr rfl]
  -- the edge through `p` is unique, and its two readings as a raw piece
  have hEcut : ∀ f ∈ overlayPieces pieces points, ∀ z, (z = f.1 ∨ z = f.2) → z ∈ points :=
    overlayPieces_ends_cut hEnds
  have huniq : ∀ f ∈ overlayPieces pieces points, p ∈ f.interior → f = e := by
    intro f hf hpf
    by_contra hne
    exact overlayPieces_disjoint_interiors hnd hEnds hMeets hf heE hne hpf hpe
  have hcasesR : ∀ R ∈ subdivide pieces points, p ∈ R.interior → R = e ∨ R = (e.2, e.1) := by
    intro R hR hpR
    have hoRe : orientPiece R = e := huniq _ (mem_overlayPieces.2 ⟨R, hR, rfl⟩)
      (by rw [orientPiece_interior]; exact hpR)
    by_cases hprec : Precedes R.1 R.2
    · exact Or.inl (by rw [← hoRe, orientPiece_of_precedes hprec])
    · have h2 : (R.2, R.1) = e := by rw [← hoRe, orientPiece_of_not_precedes hprec]
      have h3 := Prod.ext_iff.1 h2
      exact Or.inr (Prod.ext h3.2 h3.1)
  -- the two halves are fresh names, distinct from each other and from everything old
  have hf₁new : f₁ ∉ overlayPieces pieces points := fun hf₁E => hppts (hEcut f₁ hf₁E p hf₁p)
  have hf₂new : f₂ ∉ overlayPieces pieces points := fun hf₂E => hppts (hEcut f₂ hf₂E p hf₂p)
  have hf₁₂ : f₁ ≠ f₂ := by
    rcases hf₁ends with h1 | h1 <;> rcases hf₂ends with h2 | h2 <;> rw [h1, h2] <;>
      intro hh <;> rw [Prod.ext_iff] at hh
    · exact hp1 hh.1.symm
    · exact hend hh.1
    · exact hend hh.2
    · exact hp2 hh.1
  -- membership in the refined overlay
  have hmemQ : ∀ f : Piece, f ∈ overlayPieces pieces (points ++ [p]) ↔
      (f ∈ overlayPieces pieces points ∧ p ∉ f.interior) ∨ f = f₁ ∨ f = f₂ := by
    intro f
    rw [mem_overlayPieces, subdivide_snoc]
    constructor
    · rintro ⟨Rh, hRh, rfl⟩
      obtain ⟨R, hR, hRhR⟩ := List.mem_flatMap.1 hRh
      by_cases hpR : p ∈ R.interior
      · rw [splitAt, if_pos hpR] at hRhR
        rcases hcasesR R hR hpR with rfl | hRswap
        · -- the split piece reads as `e` itself
          rcases List.mem_cons.1 hRhR with rfl | hRh2
          · exact Or.inr (Or.inl rfl)
          · rcases List.mem_singleton.1 hRh2 with rfl
            exact Or.inr (Or.inr rfl)
        · -- the split piece reads as `e` reversed; its halves orient to the same two names
          subst hRswap
          rcases List.mem_cons.1 hRhR with rfl | hRh2
          · exact Or.inr (Or.inr (orientPiece_swap (p, e.2)))
          · rcases List.mem_singleton.1 hRh2 with rfl
            exact Or.inr (Or.inl (orientPiece_swap (e.1, p)))
      · rw [splitAt, if_neg hpR] at hRhR
        rw [List.mem_singleton.1 hRhR]
        refine Or.inl ⟨mem_overlayPieces.2 ⟨R, hR, rfl⟩, ?_⟩
        rw [orientPiece_interior]
        exact hpR
    · have hQhalves : ∀ Rh ∈ splitAt p Q₀, ∃ S ∈ splitAllAt p (subdivide pieces points),
          orientPiece S = orientPiece Rh :=
        fun Rh hRh => ⟨Rh, List.mem_flatMap.2 ⟨Q₀, hQ₀, hRh⟩, rfl⟩
      have hQsplit : splitAt p Q₀ = [(Q₀.1, p), (p, Q₀.2)] := by rw [splitAt, if_pos hp]
      rintro (⟨hfE, hpf⟩ | rfl | rfl)
      · obtain ⟨R, hR, rfl⟩ := mem_overlayPieces.1 hfE
        have hpR : p ∉ R.interior := by rw [← orientPiece_interior R]; exact hpf
        exact ⟨R, List.mem_flatMap.2 ⟨R, hR,
          by rw [splitAt, if_neg hpR]; exact List.mem_singleton_self _⟩, rfl⟩
      · -- `f₁` arises from the split of `Q₀`, whichever way `Q₀` reads `e`
        rcases hcasesR Q₀ hQ₀ hp with hQe | hQe
        · obtain ⟨S, hS, hSo⟩ := hQhalves (Q₀.1, p) (by rw [hQsplit]; exact List.mem_cons_self ..)
          exact ⟨S, hS, by rw [hSo, hQe]⟩
        · obtain ⟨S, hS, hSo⟩ := hQhalves (p, Q₀.2)
            (by rw [hQsplit]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
          refine ⟨S, hS, ?_⟩
          rw [hSo, hQe]
          exact orientPiece_swap (e.1, p)
      · rcases hcasesR Q₀ hQ₀ hp with hQe | hQe
        · obtain ⟨S, hS, hSo⟩ := hQhalves (p, Q₀.2)
            (by rw [hQsplit]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
          exact ⟨S, hS, by rw [hSo, hQe]⟩
        · obtain ⟨S, hS, hSo⟩ := hQhalves (Q₀.1, p) (by rw [hQsplit]; exact List.mem_cons_self ..)
          refine ⟨S, hS, ?_⟩
          rw [hSo, hQe]
          exact orientPiece_swap (p, e.2)
  -- the structure
  refine ⟨e, f₁, f₂, hend, ?_⟩
  refine ⟨⟨heE, Or.inl ⟨rfl, rfl⟩⟩, ?_, ?_, ?_, hf₁₂, ?_, ?_⟩
  · -- the new vertex is new
    rintro ⟨g, hg, hpg⟩
    exact hppts (hEcut g hg p hpg)
  · -- the first new edge is new
    exact fun hf₁E => hf₁new hf₁E
  · exact fun hf₂E => hf₂new hf₂E
  · -- the vertex set gains exactly `p`
    ext w
    simp only [overlayGraph_vertexSet, endSet, mem_setOf_eq, mem_insert_iff]
    constructor
    · rintro ⟨g, hg, hw⟩
      rcases (hmemQ g).1 hg with ⟨hgE, -⟩ | rfl | rfl
      · exact Or.inr ⟨g, hgE, hw⟩
      · rcases hf₁ends with h | h <;> rw [h] at hw <;> rcases hw with rfl | rfl
        exacts [Or.inr ⟨e, heE, Or.inl rfl⟩, Or.inl rfl, Or.inl rfl,
          Or.inr ⟨e, heE, Or.inl rfl⟩]
      · rcases hf₂ends with h | h <;> rw [h] at hw <;> rcases hw with rfl | rfl
        exacts [Or.inl rfl, Or.inr ⟨e, heE, Or.inr rfl⟩, Or.inr ⟨e, heE, Or.inr rfl⟩,
          Or.inl rfl]
    · rintro (rfl | ⟨g, hg, hw⟩)
      · refine ⟨f₁, (hmemQ f₁).2 (Or.inr (Or.inl rfl)), hf₁p⟩
      · by_cases hpg : p ∈ g.interior
        · obtain rfl := huniq g hg hpg
          rcases hw with rfl | rfl
          · refine ⟨f₁, (hmemQ f₁).2 (Or.inr (Or.inl rfl)), ?_⟩
            rcases hf₁ends with h | h <;> rw [h]
            exacts [Or.inl rfl, Or.inr rfl]
          · refine ⟨f₂, (hmemQ f₂).2 (Or.inr (Or.inr rfl)), ?_⟩
            rcases hf₂ends with h | h <;> rw [h]
            exacts [Or.inr rfl, Or.inl rfl]
        · exact ⟨g, (hmemQ g).2 (Or.inl ⟨hg, hpg⟩), hw⟩
  · -- the links: everything old except `e`, plus the two halves
    intro g a b
    constructor
    · rintro ⟨hg, hab⟩
      rcases (hmemQ g).1 hg with ⟨hgE, hpg⟩ | rfl | rfl
      · refine Or.inl ⟨⟨hgE, hab⟩, ?_, ?_, ?_⟩
        · rintro rfl; exact hpg hpe
        · rintro rfl; exact hf₁new hgE
        · rintro rfl; exact hf₂new hgE
      · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        rcases hf₁ends with h | h <;> rw [h] at hab <;>
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [rfl, Sym2.eq_swap, Sym2.eq_swap, rfl]
      · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        rcases hf₂ends with h | h <;> rw [h] at hab <;>
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        exacts [rfl, Sym2.eq_swap, Sym2.eq_swap, rfl]
    · rintro (⟨⟨hgE, hab⟩, hge, -, -⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩)
      · exact ⟨(hmemQ g).2 (Or.inl ⟨hgE, fun hpg => hge (huniq g hgE hpg)⟩), hab⟩
      · refine ⟨(hmemQ f₁).2 (Or.inr (Or.inl rfl)), ?_⟩
        rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hf₁ends with h | h <;> rw [h]
        exacts [Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩]
      · refine ⟨(hmemQ f₂).2 (Or.inr (Or.inr rfl)), ?_⟩
        rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hf₂ends with h | h <;> rw [h]
        exacts [Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩]

end Schoenflies
