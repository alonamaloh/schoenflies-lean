/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FaceCycles
import Schoenflies.Realization

/-!
# Face cycles, continued

Work in progress.
-/

open Metric Set unitInterval
open scoped Graph

namespace Schoenflies

/-! ## An arc inside an arc with the same ends is the whole of it -/

/-- **An arc between two points contained in an arc between the same two points is all of
it.** Removing an interior point of the ambient arc splits it into two relatively open halves;
a connected subset containing both ends would have to meet both and therefore their empty
intersection. -/
theorem IsArcBetween.eq_of_subset {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hBA : B ⊆ A) : B = A := by
  obtain ⟨f, hc, hi, hAim, hf0, hf1⟩ := hA
  refine Set.Subset.antisymm hBA fun x hx => ?_
  by_contra hxB
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ I, f t = x := by rw [← hAim] at hx; exact hx
  -- The parameter is strictly inside, since both ends belong to `B`.
  have ht0 : (0 : ℝ) < t := by
    rcases eq_or_lt_of_le ht.1 with rfl | h
    · exact absurd (hf0 ▸ hB.left_mem) hxB
    · exact h
  have ht1 : t < 1 := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact absurd (hf1 ▸ hB.right_mem) hxB
    · exact h
  obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hc hi (U := Iio t) isOpen_Iio
  obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hc hi (U := Ioi t) isOpen_Ioi
  rw [hAim] at hV₁ hV₂
  -- The two halves are disjoint, by injectivity of the parametrisation.
  have hdisj : (A ∩ (V₁ ∩ V₂)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z ⟨hzA, hz₁, hz₂⟩ => ?_
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzA⟩
    obtain ⟨r, hr, hrs⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzA⟩
    have hrs' : r = s := hi hr.2 hs.2 hrs
    have h1 : t < r := hr.1
    have h2 : s < t := hs.1
    rw [hrs'] at h1
    linarith
  -- `B` misses the removed point, so it lies in the union of the two halves.
  have hsub : B ⊆ V₁ ∪ V₂ := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ I, f s = z := by
      have := hBA hz; rw [← hAim] at this; exact this
    have hst : s ≠ t := by rintro rfl; exact hxB hz
    rcases lt_or_gt_of_ne hst with h | h
    · exact Or.inl (by
        have : f s ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
    · exact Or.inr (by
        have : f s ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1)
  have hp₁ : (B ∩ V₁).Nonempty := by
    refine ⟨p, hB.left_mem, ?_⟩
    have : f 0 ∈ V₁ ∩ A := by rw [← hV₁]; exact ⟨0, ⟨ht0, zero_mem_I⟩, rfl⟩
    exact hf0 ▸ this.1
  have hq₂ : (B ∩ V₂).Nonempty := by
    refine ⟨q, hB.right_mem, ?_⟩
    have : f 1 ∈ V₂ ∩ A := by rw [← hV₂]; exact ⟨1, ⟨ht1, one_mem_I⟩, rfl⟩
    exact hf1 ▸ this.1
  obtain ⟨z, hzB, hz⟩ :=
    hB.isArc.isConnected.isPreconnected V₁ V₂ hV₁open hV₂open hsub hp₁ hq₂
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj z ⟨hBA hzB, hz⟩

/-! ## Concatenating polylines -/

/-- **Appending two vertex lists joins their carriers by one segment.** The segment runs from
the last vertex of the first list to the first vertex of the second, and is degenerate — hence
contributes nothing — exactly when the two lists already share that vertex. -/
theorem poly_append : ∀ {as : List Plane} (h₁ : as ≠ []) {bs : List Plane} (h₂ : bs ≠ []),
    poly (as ++ bs) = poly as ∪ segment ℝ (as.getLast h₁) (bs.head h₂) ∪ poly bs
  | [], h₁, _, _ => absurd rfl h₁
  | [x], _, bs, h₂ => by
    rw [List.singleton_append, poly_cons_of_ne_nil h₂, poly_singleton,
      List.getLast_singleton]
    rw [Set.union_assoc, Set.singleton_union]
    exact (Set.insert_eq_self.2
      (Set.mem_union_left _ (left_mem_segment ℝ x (bs.head h₂)))).symm
  | x :: y :: as, _, bs, h₂ => by
    have hne : (y :: as) ≠ [] := List.cons_ne_nil _ _
    rw [List.cons_append, poly_cons_of_ne_nil (by simp), poly_cons_cons,
      poly_append hne h₂, List.head_append_of_ne_nil hne,
      List.getLast_cons hne]
    ac_rfl

/-- **Two polylines meeting end to head concatenate.** The joining segment collapses to the
shared vertex. -/
theorem poly_append_of_eq {as bs : List Plane} (h₁ : as ≠ []) (h₂ : bs ≠ [])
    (h : as.getLast h₁ = bs.head h₂) : poly (as ++ bs) = poly as ∪ poly bs := by
  rw [poly_append h₁ h₂, h, segment_same, Set.union_assoc, Set.singleton_union,
    Set.insert_eq_self.2 (head_mem_poly h₂)]

/-! ## A component survives the removal of a set

The face of the enlarged graph through a point of an old face is a component of *that old
face* with the ear removed — not merely of the whole old exterior with the ear removed. No
topology is needed: a component of the small set is preconnected inside the big one, and back
again. -/

/-- **Cutting inside one component.** The component of `z` in `S ∖ P` sees only the component
of `z` in `S`. -/
theorem connectedComponentIn_diff (S P : Set Plane) (z : Plane) :
    connectedComponentIn (S \ P) z = connectedComponentIn (connectedComponentIn S z \ P) z := by
  by_cases hz : z ∈ S \ P
  · have hcomp : connectedComponentIn (S \ P) z ⊆ connectedComponentIn S z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) ((connectedComponentIn_subset _ _).trans diff_subset)
    have hzR : z ∈ connectedComponentIn (connectedComponentIn S z \ P) z :=
      mem_connectedComponentIn ⟨mem_connectedComponentIn hz.1, hz.2⟩
    refine Set.Subset.antisymm
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hz) fun w hw =>
          ⟨hcomp hw, (connectedComponentIn_subset _ _ hw).2⟩)
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzR fun w hw => ?_)
    have hw' : w ∈ connectedComponentIn S z \ P := connectedComponentIn_subset _ _ hw
    exact ⟨connectedComponentIn_subset _ _ hw'.1, hw'.2⟩
  · rw [connectedComponentIn_eq_empty hz, connectedComponentIn_eq_empty]
    rintro ⟨hw, hwP⟩
    exact hz ⟨connectedComponentIn_subset _ _ hw, hwP⟩

/-! ## A polygonal arc is a polyline running from one end to the other -/

/-- **A polygonal arc is `poly` of a vertex list running from one of its ends to the other.**
`Schoenflies.exists_simple_poly_of_isPolygonal` produces a simple polygonal arc *inside* the
set between the two points; being an arc between the same two ends it is the whole of it, by
`Schoenflies.IsArcBetween.eq_of_subset`. -/
theorem IsArcBetween.exists_poly_eq {A : Set Plane} {p q : Plane} (harc : IsArcBetween A p q)
    (hpoly : IsPolygonal A) (hpq : p ≠ q) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], vs.head h = p ∧ vs.getLast h = q ∧ poly vs = A := by
  obtain ⟨vs, hvs, hhead, hlast, hsub, hsubarc⟩ :=
    exists_simple_poly_of_isPolygonal hpoly harc.isArc.isConnected.isPreconnected hpq
      harc.left_mem harc.right_mem
  exact ⟨vs, hvs, hhead, hlast, harc.eq_of_subset hsubarc hsub⟩

end Schoenflies

namespace Graph

/-! ## Cutting and joining paths

Two general facts about paths that `Schoenflies/Graph/Walk.lean` does not have, and that the
splitting of a cycle at two of its vertices runs on. **The integrator should hoist both into
`Schoenflies/Graph/Walk.lean`**, next to `Graph.IsPath.split`, which is the weaker form of the
second. -/

section GeneralWalk

variable {α β : Type*} {G : Graph α β} {u v w x y : α} {e : β} {W W₁ W₂ : List β}

/-- **Two paths meeting only at the junction concatenate.** The freshness clause of the joined
path is the freshness of the first together with the meeting condition: a vertex the second
half visits and the first half departs from would be the junction, which the first half has
already arrived at. -/
theorem IsPath.append : ∀ {u w v : α} {W₁ W₂ : List β}, G.IsPath u W₁ w → G.IsPath w W₂ v →
    (∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices w W₂ → y = w) → G.IsPath u (W₁ ++ W₂) v := by
  intro u w v W₁ W₂ h₁
  induction h₁ with
  | nil hx => intro h₂ _; simpa using h₂
  | @cons u w₀ w e W hl hW hfresh ih =>
    intro h₂ hmeet
    refine List.cons_append .. ▸ IsPath.cons hl
      (ih h₂ fun y hy hy₂ => hmeet y (mem_walkVertices_cons_of_mem hl hy) hy₂) fun hmem => ?_
    -- The departure vertex is fresh: the only new vertices are those of the second half, and
    -- one of those shared with the first half would be the junction, already visited.
    rcases mem_walkVertices_iff.1 hmem with rfl | hcov
    · exact hfresh mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with hcov | hcov
    · exact hfresh (mem_walkVertices_of_mem_covered hcov)
    · have := hmeet u mem_walkVertices_self (mem_walkVertices_of_mem_covered hcov)
      exact hfresh (this ▸ hW.target_mem_walkVertices)

/-- **A path splits at any vertex it visits, and the two halves meet only there.** This is
`Graph.IsPath.split` with the meeting condition in place of its weaker last clause. -/
theorem IsPath.split_meet (h : G.IsPath u W v) (hx : x ∈ G.walkVertices u W) :
    ∃ W₁ W₂, W = W₁ ++ W₂ ∧ G.IsPath u W₁ x ∧ G.IsPath x W₂ v ∧
      ∀ y ∈ G.walkVertices u W₁, y ∈ G.walkVertices x W₂ → y = x := by
  induction h with
  | nil hx' =>
    rw [walkVertices_nil] at hx
    obtain rfl := hx
    exact ⟨[], [], rfl, .nil hx', .nil hx', fun y hy _ => by simpa using hy⟩
  | @cons u w v e W hl hW hfresh ih =>
    rcases mem_walkVertices_cons hl hx with rfl | hx'
    · exact ⟨[], e :: W, rfl, .nil hl.left_mem, .cons hl hW hfresh,
        fun y hy _ => by simpa using hy⟩
    obtain ⟨W₁, W₂, rfl, h₁, h₂, hmeet⟩ := ih hx'
    have hsub₁ : W₁ ⊆ W₁ ++ W₂ := List.subset_append_left _ _
    have hsub₂ : W₂ ⊆ W₁ ++ W₂ := List.subset_append_right _ _
    refine ⟨e :: W₁, W₂, rfl, .cons hl h₁ fun hmem => hfresh (walkVertices_mono hsub₁ hmem),
      h₂, fun y hy hy₂ => ?_⟩
    -- A vertex of the extended prefix is either the new source — which the far half never
    -- visits, by freshness — or one the induction hypothesis already handles.
    rcases mem_walkVertices_cons hl hy with rfl | hy'
    · exfalso
      rcases mem_walkVertices_iff.1 hy₂ with rfl | hcov
      · exact hfresh (walkVertices_mono hsub₁ h₁.target_mem_walkVertices)
      · exact hfresh (mem_walkVertices_of_mem_covered (coveredVertices_mono hsub₂ hcov))
    · exact hmeet y hy' hy₂

/-- The source of a nonempty walk is an end of its first edge, so a nonempty walk visits no
vertex its edges do not cover. -/
theorem IsWalk.walkVertices_eq_covered (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices u W = G.coveredVertices W := by
  refine Set.insert_eq_self.2 ?_
  cases h with
  | nil => exact absurd rfl hne
  | cons hl _ => exact mem_coveredVertices List.mem_cons_self hl.inc_left

/-- Running a nonempty walk backwards changes neither the edges nor the vertices it visits. -/
theorem IsWalk.walkVertices_reverse_eq (h : G.IsWalk u W v) (hne : W ≠ []) :
    G.walkVertices v W.reverse = G.walkVertices u W := by
  rw [h.reverse.walkVertices_eq_covered (by simpa using hne), coveredVertices_reverse,
    h.walkVertices_eq_covered hne]

/-! ### Cutting a cycle at two of its vertices

The cycle is `X ++ Y ++ Z` closed up by the edge `e`, cut at the two vertices `c` (between `X`
and `Y`) and `d` (between `Y` and `Z`). One arc is `Y`; the other runs `Z`, then the closing
edge, then `X`. Both cases of "which of the two named vertices comes first along the detour"
feed this one lemma. -/

/-- **The complementary arc of a cut cycle**, together with the two facts a geometric consumer
needs: that the two arcs between them use every edge of the cycle exactly once, and that they
visit no common vertex but the two cut points. -/
theorem IsCycleThrough.split_aux {G : Graph α β} {e : β} {u v c d : α} {D X Y Z : List β}
    (hc : G.IsCycleThrough e u v D) (hD : D = X ++ (Y ++ Z)) (hX : G.IsPath u X c)
    (hY : G.IsPath c Y d) (hZ : G.IsPath d Z v) (hcd : c ≠ d)
    (hM1 : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices c (Y ++ Z) → y = c)
    (hM2 : ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d Z → y = d) :
    G.IsPath d (Z ++ e :: X) c ∧ (Y ++ (Z ++ e :: X)).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices c Y, y ∈ G.walkVertices d (Z ++ e :: X) → y = c ∨ y = d := by
  have hZsub : G.walkVertices d Z ⊆ G.walkVertices c (Y ++ Z) := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | hcov
    · exact walkVertices_mono (List.subset_append_left _ _) hY.target_mem_walkVertices
    · exact mem_walkVertices_of_mem_covered (coveredVertices_mono
        (List.subset_append_right _ _) hcov)
  -- A vertex of the first stretch that the last stretch also reaches would merge the two cuts.
  have hclash : ∀ y ∈ G.walkVertices u X, y ∈ G.walkVertices d Z → False := by
    intro y hy hyZ
    obtain rfl : y = c := hM1 y hy (hZsub hyZ)
    exact hcd (hM2 y mem_walkVertices_self hyZ)
  have hvZ : v ∈ G.walkVertices d Z := hZ.target_mem_walkVertices
  have hvX : v ∉ G.walkVertices u X := fun hh => hclash v hh hvZ
  -- The closing edge, then the first stretch, is a path from the far end back to the first cut.
  have hePath : G.IsPath v (e :: X) c := IsPath.cons hc.isLink.symm hX hvX
  -- Its vertices, other than `v` itself, are those of the first stretch.
  have hcons : ∀ y ∈ G.walkVertices v (e :: X), y = v ∨ y ∈ G.walkVertices u X := by
    intro y hy
    rcases mem_walkVertices_iff.1 hy with rfl | ⟨g, hg, hinc⟩
    · exact Or.inl rfl
    rcases List.mem_cons.1 hg with rfl | hg'
    · rcases hinc.eq_or_eq_of_isLink hc.isLink with rfl | rfl
      · exact Or.inr mem_walkVertices_self
      · exact Or.inl rfl
    · exact Or.inr (mem_walkVertices_of_mem_covered ⟨g, hg', hinc⟩)
  refine ⟨hZ.append hePath fun y hy hy' => ?_, ?_, fun y hy hy' => ?_⟩
  · rcases hcons y hy' with rfl | hyX
    · rfl
    · exact absurd hyX fun hh => hclash y hh hy
  · subst hD
    rw [show Y ++ (Z ++ e :: X) = (Y ++ Z) ++ (e :: X) by rw [List.append_assoc]]
    exact List.perm_middle.trans (List.Perm.cons _ List.perm_append_comm)
  · -- A vertex on both arcs is on the last stretch — hence the second cut — or on the first,
    -- hence the first cut.
    rcases mem_walkVertices_iff.1 hy' with rfl | hcov
    · exact Or.inr rfl
    rw [coveredVertices_append] at hcov
    rcases hcov with hcovZ | hcovE
    · exact Or.inr (hM2 y hy (mem_walkVertices_of_mem_covered hcovZ))
    · rcases hcons y (mem_walkVertices_of_mem_covered hcovE) with rfl | hyX
      · exact Or.inr (hM2 y hy hvZ)
      · exact Or.inl (hM1 y hyX (walkVertices_mono (List.subset_append_left _ _) hy))

/-- **A cycle cut at two of its vertices is two paths between them.** The two arcs use every
edge of the cycle exactly once — that is what the permutation says — and they have no vertex in
common but the two cut points. This is the combinatorial half of "the ear is a crosscut of the
face": the geometric half reads the two arcs of the Jordan curve off it. -/
theorem IsCycleThrough.split_at {G : Graph α β} {e : β} {u v a b : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) (ha : a ∈ G.walkVertices u D) (hb : b ∈ G.walkVertices u D)
    (hab : a ≠ b) :
    ∃ D₁ D₂ : List β, G.IsPath a D₁ b ∧ G.IsPath b D₂ a ∧ (D₁ ++ D₂).Perm (e :: D) ∧
      ∀ y ∈ G.walkVertices a D₁, y ∈ G.walkVertices b D₂ → y = a ∨ y = b := by
  obtain ⟨P, Q, hPQ, hP, hQ, hM1⟩ := hc.isPath.split_meet ha
  -- The second cut point lies on one of the two stretches the first one made.
  have hcases : b ∈ G.walkVertices a Q ∨ b ∈ G.walkVertices u P := by
    rw [hPQ] at hb
    rcases mem_walkVertices_iff.1 hb with rfl | hcov
    · exact Or.inr mem_walkVertices_self
    rw [coveredVertices_append] at hcov
    rcases hcov with h | h
    · exact Or.inr (mem_walkVertices_of_mem_covered h)
    · exact Or.inl (mem_walkVertices_of_mem_covered h)
  rcases hcases with hbQ | hbP
  · -- `b` comes after `a`: cut the far stretch at `b`.
    obtain ⟨Q₁, Q₂, hQ12, hQ1, hQ2, hM2⟩ := hQ.split_meet hbQ
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P) (Y := Q₁) (Z := Q₂)
      (by rw [hPQ, hQ12]) hP hQ1 hQ2 hab (by rw [← hQ12]; exact hM1) hM2
    exact ⟨Q₁, Q₂ ++ e :: P, hQ1, hpath, hperm, hmeet⟩
  · -- `b` comes before `a`: cut the near stretch at `b`, and the two roles are exchanged.
    obtain ⟨P₁, P₂, hP12, hP1, hP2, hM2⟩ := hP.split_meet hbP
    have hP1sub : G.walkVertices u P₁ ⊆ G.walkVertices u P :=
      walkVertices_mono (by rw [hP12]; exact List.subset_append_left _ _)
    have hP2sub : G.walkVertices b P₂ ⊆ G.walkVertices u P := by
      intro y hy
      rcases mem_walkVertices_iff.1 hy with rfl | hcov
      · exact hbP
      · exact mem_walkVertices_of_mem_covered
          (coveredVertices_mono (by rw [hP12]; exact List.subset_append_right _ _) hcov)
    have hM1' : ∀ y ∈ G.walkVertices u P₁, y ∈ G.walkVertices b (P₂ ++ Q) → y = b := by
      intro y hy hy'
      rcases mem_walkVertices_iff.1 hy' with rfl | hcov
      · rfl
      rw [coveredVertices_append] at hcov
      rcases hcov with h | h
      · exact hM2 y hy (mem_walkVertices_of_mem_covered h)
      · -- A vertex both stretches of the near half and the far half reach merges the two cuts.
        exfalso
        obtain rfl : y = a := hM1 y (hP1sub hy) (mem_walkVertices_of_mem_covered h)
        exact hab (hM2 y hy hP2.target_mem_walkVertices)
    obtain ⟨hpath, hperm, hmeet⟩ := hc.split_aux (X := P₁) (Y := P₂) (Z := Q)
      (by rw [hPQ, hP12, List.append_assoc]) hP1 hP2 hQ (Ne.symm hab) hM1'
      fun y hy hy' => hM1 y (hP2sub hy) hy'
    refine ⟨Q ++ e :: P₁, P₂, hpath, hP2, List.perm_append_comm.trans hperm, fun y hy hy' => ?_⟩
    exact (hmeet y hy' hy).symm

end GeneralWalk

open Schoenflies

variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {e f : β} {u v w z a b : Plane} {W D : List β}

/-! ## What a walk of a polygonal plane graph draws -/

/-- **The realisation of a walk with polygonal edges is a polyline from its source to its
target.** The induction is along the walk: the first edge contributes its own vertex list, and
the two lists are joined at the waypoint, which is the last vertex of the first and the first
vertex of the rest. -/
theorem IsDrawing.exists_poly_eq_edgesCover (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hW : G.IsWalk u W v) (hne : W ≠ []) :
    ∃ vs : List Plane, ∃ hv : vs ≠ [], vs.head hv = u ∧ vs.getLast hv = v ∧
      poly vs = edgesCover drawing W := by
  induction hW with
  | nil => exact absurd rfl hne
  | @cons u w v e W hl hW ih =>
    have hedge : ∃ vs : List Plane, ∃ hv : vs ≠ [], vs.head hv = u ∧ vs.getLast hv = w ∧
        poly vs = edgeArc drawing e :=
      (h.edge_isArcBetween hl).exists_poly_eq (hpoly e hl.edge_mem) (h.ne_of_isLink hl)
    obtain ⟨es, hes, heshead, heslast, hespoly⟩ := hedge
    rcases eq_or_ne W [] with rfl | hWne
    · obtain rfl : w = v := hW.eq_of_nil
      exact ⟨es, hes, heshead, heslast, by
        rw [hespoly, edgesCover_cons, edgesCover_nil, Set.union_empty]⟩
    · obtain ⟨vs, hvs, hhead, hlast, hpolyv⟩ := ih hWne
      -- The two lists share the waypoint, so their carriers join there.
      refine ⟨es ++ vs, by simp [hes], ?_, ?_, ?_⟩
      · rw [List.head_append_of_ne_nil hes]; exact heshead
      · rw [List.getLast_append_of_ne_nil _ hvs]; exact hlast
      · rw [poly_append_of_eq hes hvs (by rw [heslast, hhead]), hespoly, hpolyv,
          edgesCover_cons]

/-- **What a nonempty walk of a polygonal plane graph draws is polygonal.** -/
theorem IsDrawing.isPolygonal_edgesCover (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) (hW : G.IsWalk u W v) (hne : W ≠ []) :
    IsPolygonal (edgesCover drawing W) := by
  obtain ⟨vs, -, -, -, hvs⟩ := h.exists_poly_eq_edgesCover hpoly hW hne
  exact ⟨vs, hvs.symm⟩

/-! ## The realisation of a cycle is a separating curve

This is the composition the base case of `lem:face-cycles` needs, and the one thing that was
missing from it: `Graph.IsDrawing.cycle_isJordanCurve` says the realisation is a Jordan curve
and `Graph.IsDrawing.isPolygonal_edgesCover` says it is polygonal, and
`Schoenflies.exists_closedPolygon` — the realization theorem — turns that pair into a
`Schoenflies.ClosedPolygon`, whose carrier `Schoenflies.ClosedPolygon.isSeparating_carrier`
knows to separate the plane. Nothing here inspects the polygon; it is used and discarded. -/

/-- Going round the cycle the other way: the edge, then the detour, is a closed walk at the
edge's far end. This is the walk whose edge list is `e :: D`, the list every statement about
the realisation of a cycle is phrased with. -/
theorem IsCycleThrough.isWalk_cons {α : Type*} {G : Graph α β} {e : β} {u v : α} {D : List β}
    (hc : G.IsCycleThrough e u v D) : G.IsWalk v (e :: D) v :=
  IsWalk.cons hc.isLink.symm hc.isPath.isWalk

/-- **The realisation of a cycle of a polygonal plane graph is a separating Jordan curve.**
`Schoenflies.IsSeparating` is Definition 2.4: the complement has exactly two regions, one
bounded and one unbounded, each with the curve as its boundary. -/
theorem IsDrawing.cycle_isSeparating (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : IsSeparating (edgesCover drawing (e :: D)) := by
  obtain ⟨m, P, hP⟩ := exists_closedPolygon (h.cycle_isJordanCurve hc)
    (h.isPolygonal_edgesCover hpoly hc.isWalk_cons (List.cons_ne_nil _ _))
  exact hP ▸ P.isSeparating_carrier

/-! ## What a subgraph spanned by a walk occupies -/

/-- An end of an edge lies on that edge's arc. -/
theorem IsDrawing.inc_mem_edgeArc (h : IsDrawing G drawing) {x : Plane} (hinc : G.Inc e x) :
    x ∈ edgeArc drawing e := by
  obtain ⟨y, hy⟩ := hinc
  exact (h.edge_isArcBetween hy).left_mem

/-- **The subgraph spanned by a nonempty walk occupies exactly what the walk draws.** Its
vertices are ends of its edges, so they add nothing to the union of the edge arcs. -/
theorem IsDrawing.pointSet_pathGraphOf (h : IsDrawing G drawing) (hW : G.IsWalk u W v)
    (hne : W ≠ []) : pointSet (G.pathGraphOf u W) drawing = edgesCover drawing W := by
  obtain ⟨f, T, rfl⟩ : ∃ f T, W = f :: T := by
    cases W with
    | nil => exact absurd rfl hne
    | cons f T => exact ⟨f, T, rfl⟩
  refine Set.Subset.antisymm (Set.union_subset ?_ ?_) ?_
  · -- Every vertex the walk visits is an end of one of its edges.
    intro x hx
    rw [pathGraphOf_vertexSet] at hx
    rcases mem_walkVertices_iff.1 hx with rfl | ⟨g, hg, hinc⟩
    · cases hW with
      | cons hl _ => exact mem_edgesCover List.mem_cons_self (h.inc_mem_edgeArc hl.inc_left)
    · exact mem_edgesCover hg (h.inc_mem_edgeArc hinc)
  · refine Set.iUnion₂_subset fun g hg => ?_
    rw [pathGraphOf_edgeSet hW] at hg
    exact fun z hz => mem_edgesCover hg hz
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := mem_edgesCover_iff.1 hz
    refine edgeArc_subset_pointSet ?_ hzg
    rw [pathGraphOf_edgeSet hW]
    exact hg

/-- **The cycle subgraph occupies exactly what the cycle draws.** -/
theorem IsDrawing.pointSet_cycleGraph (h : IsDrawing G drawing) {e : β} {u v : Plane}
    {D : List β} (hc : G.IsCycleThrough e u v D) :
    pointSet (G.cycleGraph u e D) drawing = edgesCover drawing (e :: D) := by
  have hround := h.pointSet_pathGraphOf hc.isWalk_round (by simp)
  rw [cycleGraph, hround]
  refine Set.Subset.antisymm (edgesCover_mono fun g hg => ?_) (edgesCover_mono fun g hg => ?_)
  · rcases List.mem_append.1 hg with hg' | hg'
    · exact List.mem_cons_of_mem _ hg'
    · obtain rfl : g = e := by simpa using hg'
      exact List.mem_cons_self
  · rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ hg'

/-! ## The conclusion of `lem:face-cycles`, at one face -/

/-- **A face bounded by a named cycle.** The face `face G drawing z` is one of the two regions
of the complement of the realisation of the cycle `e :: D` — which is the blueprint's "every
face … has a cycle as its boundary *and is one of the two complementary regions of that
cycle*". The cycle is a parameter rather than an existential so that a consumer that has
produced one keeps it. -/
structure IsFaceCycle (G : Graph Plane β) (drawing : β → ℝ → Plane) (z : Plane)
    (e : β) (u v : Plane) (D : List β) : Prop where
  /-- The named data really is a cycle of the graph. -/
  isCycle : G.IsCycleThrough e u v D
  /-- Its realisation separates the plane into exactly two regions. -/
  isSeparating : IsSeparating (edgesCover drawing (e :: D))
  /-- The face is one of those two. -/
  isRegionOf : IsRegionOf (edgesCover drawing (e :: D)) (face G drawing z)

namespace IsFaceCycle

variable {e : β} {u v : Plane} {D : List β}

/-- **"has a cycle as its boundary"**: the frontier of the face is the realisation. -/
theorem frontier_eq (h : IsFaceCycle G drawing z e u v D) :
    frontier (face G drawing z) = edgesCover drawing (e :: D) :=
  h.isRegionOf.frontier_eq h.isSeparating

/-- The face is the interior or the exterior of its boundary cycle. -/
theorem eq_inside_or_outside (h : IsFaceCycle G drawing z e u v D) :
    face G drawing z = inside (edgesCover drawing (e :: D)) ∨
      face G drawing z = outside (edgesCover drawing (e :: D)) := h.isRegionOf

/-- A face bounded by a cycle of a subgraph is bounded by the same cycle of the whole graph,
*provided the face itself is unchanged* — which is the shape the induction step needs when it
carries a face past an ear that does not touch it. -/
theorem mono (h : IsFaceCycle B drawing z e u v D) (hBG : B ≤ G)
    (hface : face G drawing z = face B drawing z) : IsFaceCycle G drawing z e u v D where
  isCycle := ⟨h.isCycle.isLink.mono hBG, h.isCycle.isPath.mono hBG, h.isCycle.notMem⟩
  isSeparating := h.isSeparating
  isRegionOf := hface ▸ h.isRegionOf

end IsFaceCycle

/-- **`lem:face-cycles`, as a property of a plane graph**: every face has a cycle as its
boundary and is one of the two complementary regions of that cycle. -/
def HasFaceCycles (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop :=
  ∀ z ∈ exterior G drawing, ∃ (e : β) (u v : Plane) (D : List β), IsFaceCycle G drawing z e u v D

/-! ## The base case: the faces of a single cycle

"This is true for the initial cycle by Theorem `thm:polygonal-jordan`." The cycle subgraph
occupies exactly the cycle's realisation, so its faces are literally the components of the
complement of that curve, and the curve is separating. -/

/-- **The base case of `lem:face-cycles`.** Both faces of the graph consisting of one cycle
are regions of that cycle. -/
theorem IsDrawing.hasFaceCycles_cycleGraph (h : IsDrawing G drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc drawing e)) {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : HasFaceCycles (G.cycleGraph u e D) drawing := by
  have hsep : IsSeparating (edgesCover drawing (e :: D)) := h.cycle_isSeparating hpoly hc
  -- The same cycle, read inside the subgraph it spans.
  have hcyc : (G.cycleGraph u e D).IsCycleThrough e u v D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]; exact List.mem_append_left _ hg,
      hc.notMem⟩
  intro z hz
  refine ⟨e, u, v, D, hcyc, hsep, ?_⟩
  rw [face, exterior, h.pointSet_cycleGraph hc]
  refine hsep.isRegionOf_connectedComponentIn ?_
  rw [exterior, h.pointSet_cycleGraph hc] at hz
  exact hz

end Graph
