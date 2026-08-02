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
