/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FaceCyclesLand
import Schoenflies.Graph.TwoConnected

/-!
# The outer face of a chain of plane graphs

`lem:outer-chain`. Let `Γ 0, …, Γ n` (`n ≥ 2`, so at least three graphs) be finite 2-connected
polygonal plane graphs, consecutive ones sharing at least two vertices and nonconsecutive ones
disjoint. If a point `x` is in the outer face of every consecutive pair `Γ p ∪ Γ (p+1)`, then it
is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`.

## How the chain is formalised

The blueprint says "after subdividing common points into vertices". Here that is true by
construction rather than by a theorem: the family shares **one** ambient edge type `β` and
**one** drawing `drawing : β → ℝ → Plane`, and every member is a subgraph of a single plane
graph `G` — see `Graph.IsPlaneChain`. Two members therefore agree about the ends of a shared
edge, meet only where `G` lets them meet, and `Γ p ∪ Γ q` is `Graph.union` with nothing to
check. The ambient `G` is allowed to be larger than the chain's own union; a consumer that has
built all its pieces inside one polygonal overlay hands that overlay over as `G`.

`Graph.chainUnion Γ i m` is the block `Γ i ∪ Γ (i+1) ∪ ⋯ ∪ Γ (i+m)`, indexed by its **length**
`m` rather than by its right endpoint, so that the recursion is on `m` and the blueprint's
"choose `i ≤ j` with `j - i` minimum" is a plain strong induction on `m`. A consecutive pair is
`chainUnion Γ p 1`.

"`x` is in the outer face of `H`" is spelled, as everywhere in this development, as *`x` is off
the drawing and the face through it is unbounded* — `x ∈ exterior H drawing` together with
`¬ Bornology.IsBounded (face H drawing x)`. `Graph.unbounded_face_unique` is what makes that
"the" outer face, and `Graph.beyondSquare_subset_face` is how a consumer proves it.

## What is proved and what is assumed

The blueprint's proof is a minimal-counterexample argument on two measures: first the length of
the index interval, then the number of edges of the enclosing cycle lying outside `Γ (j-1)`.
Both minimisations are carried out here, as strong inductions, together with

* the reduction of "`x` lies in a bounded face" to "some cycle encloses `x`"
  (`Graph.encloses_of_isBounded_face`, from `Graph.face_cycles'`) and back
  (`Graph.isBounded_face_of_encloses`);
* 2-connectivity of every block, by iterating `Graph.IsTwoConnected.union`
  (`lem:union-two-connected`);
* the base case `j - i ≤ 1`, which is the blueprint's paragraph "If `j-i ≤ 1`, choose a
  consecutive pair `H` containing that union …";
* the two minimality consequences "`C` contains an edge of `Γ j` outside `Γ (j-1)`" and "`C`
  contains an edge of the earlier chain outside `Γ (j-1)`", each proved by pushing the cycle
  down into a shorter block with `Graph.IsCycleThrough.anti`.

**Assumed**: `Graph.Descent`, the middle paragraph of the blueprint's proof — from a cycle `C`
of `Γ i ∪ ⋯ ∪ Γ j` enclosing `x` and having an edge of `Γ j` and an edge of `Γ i ∪ ⋯ ∪ Γ (j-2)`
outside `Γ (j-1)`, produce a cycle of the same block enclosing `x` with strictly fewer edges
outside `Γ (j-1)`. That is the crosscut construction: the two arcs of `C` between two points of
`C ∩ Γ (j-1)` on different maximal subpaths, a minimum-length path `R` in `Γ (j-1)` joining
them, and `thm:polygonal-crosscut` deciding which of `R ∪ C₁`, `R ∪ C₂` still encloses `x`. It
is a statement about **one** step, not about the chain's outer face, and it is exactly the
hypothesis a later module discharges with `Schoenflies.crosscutSplitsRegion`,
`Graph.IsCycleThrough.split_at` and `Graph.exists_spliced_cycle`.

## Blueprint

* `Graph.chainUnion` — `Γ i ∪ ⋯ ∪ Γ (i+m)`, with `chainUnion_le`, `le_chainUnion`,
  `chainUnion_finite`, `chainUnion_isTwoConnected` (the last is repeated
  `lem:union-two-connected`).
* `Graph.Encloses` — "that face is the interior of its boundary cycle, which therefore encloses
  `x`", as a property of a graph.
* `Graph.encloses_of_isBounded_face`, `Graph.isBounded_face_of_encloses` — the two directions
  of that reduction; the second is the blueprint's "the face of `H` containing `x` … lies in the
  bounded set `Int(C)` and therefore is not the outer face of `H`".
* `Graph.IsPlaneChain` — the hypotheses of `lem:outer-chain`.
* `Graph.Descent` — **assumed**: the crosscut paragraph of the proof.
* `Graph.IsPlaneChain.not_encloses` — the double minimisation.
* `Graph.IsPlaneChain.outer_chain` — **`lem:outer-chain`**.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

/-! ## Blocks of a chain -/

section General

variable {α β : Type*} {Γ : ℕ → Graph α β} {G K : Graph α β} {i m p : ℕ}

/-- `chainUnion Γ i m` is `Γ i ∪ Γ (i+1) ∪ ⋯ ∪ Γ (i+m)`.

Indexed by the **length** `m` of the block rather than by its right endpoint: the blueprint
minimises `j - i`, and with this indexing that is a strong induction on the second argument
with no subtraction anywhere. -/
def chainUnion (Γ : ℕ → Graph α β) (i : ℕ) : ℕ → Graph α β
  | 0 => Γ i
  | m + 1 => (chainUnion Γ i m).union (Γ (i + m + 1))

@[simp]
theorem chainUnion_zero (Γ : ℕ → Graph α β) (i : ℕ) : chainUnion Γ i 0 = Γ i := rfl

@[simp]
theorem chainUnion_succ (Γ : ℕ → Graph α β) (i m : ℕ) :
    chainUnion Γ i (m + 1) = (chainUnion Γ i m).union (Γ (i + m + 1)) := rfl

/-- A block of length one is a consecutive pair. -/
theorem chainUnion_one (Γ : ℕ → Graph α β) (i : ℕ) :
    chainUnion Γ i 1 = (Γ i).union (Γ (i + 1)) := rfl

theorem mem_vertexSet_chainUnion {x : α} :
    x ∈ V(chainUnion Γ i m) ↔ ∃ p, i ≤ p ∧ p ≤ i + m ∧ x ∈ V(Γ p) := by
  induction m with
  | zero =>
    refine ⟨fun h => ⟨i, le_rfl, by omega, h⟩, ?_⟩
    rintro ⟨p, hp, hp', hx⟩
    obtain rfl : p = i := by omega
    exact hx
  | succ m ih =>
    rw [chainUnion_succ, vertexSet_union, Set.mem_union, ih]
    constructor
    · rintro (⟨p, hp, hp', hx⟩ | hx)
      · exact ⟨p, hp, by omega, hx⟩
      · exact ⟨i + m + 1, by omega, by omega, hx⟩
    · rintro ⟨p, hp, hp', hx⟩
      rcases Nat.lt_or_ge p (i + m + 1) with h | h
      · exact Or.inl ⟨p, hp, by omega, hx⟩
      · obtain rfl : p = i + m + 1 := by omega
        exact Or.inr hx

theorem mem_edgeSet_chainUnion {e : β} :
    e ∈ E(chainUnion Γ i m) ↔ ∃ p, i ≤ p ∧ p ≤ i + m ∧ e ∈ E(Γ p) := by
  induction m with
  | zero =>
    refine ⟨fun h => ⟨i, le_rfl, by omega, h⟩, ?_⟩
    rintro ⟨p, hp, hp', he⟩
    obtain rfl : p = i := by omega
    exact he
  | succ m ih =>
    rw [chainUnion_succ, edgeSet_union, Set.mem_union, ih]
    constructor
    · rintro (⟨p, hp, hp', he⟩ | he)
      · exact ⟨p, hp, by omega, he⟩
      · exact ⟨i + m + 1, by omega, by omega, he⟩
    · rintro ⟨p, hp, hp', he⟩
      rcases Nat.lt_or_ge p (i + m + 1) with h | h
      · exact Or.inl ⟨p, hp, by omega, he⟩
      · obtain rfl : p = i + m + 1 := by omega
        exact Or.inr he

/-- A block sits inside any graph containing all of its members. -/
theorem chainUnion_le (h : ∀ p, i ≤ p → p ≤ i + m → Γ p ≤ G) : chainUnion Γ i m ≤ G := by
  induction m with
  | zero => exact h i le_rfl le_rfl
  | succ m ih =>
    exact union_le (ih fun p hp hp' => h p hp (by omega)) (h (i + m + 1) (by omega) le_rfl)

/-- Each member of a block is a subgraph of it. The compatibility hypothesis is what makes the
*right*-hand summand of a `Graph.union` a subgraph, and it is free once every member lies in one
ambient graph. -/
theorem le_chainUnion (hle : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G) (hp : i ≤ p) (hp' : p ≤ i + m) :
    Γ p ≤ chainUnion Γ i m := by
  induction m with
  | zero =>
    obtain rfl : p = i := by omega
    exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge p (i + m + 1) with h | h
    · exact (ih (fun q hq hq' => hle q hq (by omega)) (by omega)).trans (left_le_union _ _)
    · obtain rfl : p = i + m + 1 := by omega
      have hcompat : (chainUnion Γ i m).Compatible (Γ (i + m + 1)) :=
        Compatible.of_le_le (chainUnion_le fun q hq hq' => hle q hq (by omega))
          (hle _ (by omega) le_rfl)
      exact hcompat.right_le_union

/-- A block of finite graphs is finite. -/
theorem chainUnion_finite (h : ∀ p, i ≤ p → p ≤ i + m → (Γ p).Finite) :
    (chainUnion Γ i m).Finite := by
  induction m with
  | zero => exact h i le_rfl le_rfl
  | succ m ih =>
    have h1 := ih fun p hp hp' => h p hp (by omega)
    have h2 := h (i + m + 1) (by omega) le_rfl
    exact { finite_vertexSet := by
              rw [chainUnion_succ, vertexSet_union]
              exact h1.finite_vertexSet.union h2.finite_vertexSet
            finite_edgeSet := by
              rw [chainUnion_succ, edgeSet_union]
              exact h1.finite_edgeSet.union h2.finite_edgeSet }

/-- **`lem:union-two-connected`, iterated.** A block of 2-connected graphs in which consecutive
members share two distinct vertices is 2-connected. -/
theorem chainUnion_isTwoConnected (hle : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G)
    (htc : ∀ q, i ≤ q → q ≤ i + m → (Γ q).IsTwoConnected)
    (hmeet : ∀ q, i ≤ q → q < i + m → ∃ a b : α, a ≠ b ∧ a ∈ V(Γ q) ∧ a ∈ V(Γ (q + 1)) ∧
      b ∈ V(Γ q) ∧ b ∈ V(Γ (q + 1))) :
    (chainUnion Γ i m).IsTwoConnected := by
  induction m with
  | zero => exact htc i le_rfl le_rfl
  | succ m ih =>
    have hle' : ∀ q, i ≤ q → q ≤ i + m → Γ q ≤ G := fun q hq hq' => hle q hq (by omega)
    have hih := ih hle' (fun q hq hq' => htc q hq (by omega))
      (fun q hq hq' => hmeet q hq (by omega))
    obtain ⟨a, b, hab, haq, haq', hbq, hbq'⟩ := hmeet (i + m) (by omega) (by omega)
    have hsub : Γ (i + m) ≤ chainUnion Γ i m := le_chainUnion hle' (by omega) le_rfl
    have hcompat : (chainUnion Γ i m).Compatible (Γ (i + m + 1)) :=
      Compatible.of_le_le (chainUnion_le hle') (hle _ (by omega) le_rfl)
    exact hih.union hcompat (htc _ (by omega) le_rfl) hab (hsub.vertexSet_mono haq) haq'
      (hsub.vertexSet_mono hbq) hbq'

/-! ### Reading a cycle inside a subgraph

`Graph.IsCycleThrough.anti` is the cycle counterpart of `Graph.IsPath.anti`; it is what turns
"no edge of `C` is outside this block" into "`C` is a cycle of this block". -/

/-- Every edge on a cycle is an edge of the graph. -/
theorem IsCycleThrough.mem_edgeSet_cons {e g : β} {u v : α} {D : List β}
    (h : G.IsCycleThrough e u v D) (hg : g ∈ e :: D) : g ∈ E(G) := by
  rcases List.mem_cons.1 hg with rfl | hg
  · exact h.isLink.edge_mem
  · exact h.isPath.edge_mem hg

/-- A cycle all of whose edges belong to a subgraph is a cycle of that subgraph. -/
theorem IsCycleThrough.anti {e : β} {u v : α} {D : List β} (h : G.IsCycleThrough e u v D)
    (hKG : K ≤ G) (hE : ∀ g ∈ e :: D, g ∈ E(K)) : K.IsCycleThrough e u v D := by
  have he : e ∈ E(K) := hE e List.mem_cons_self
  have hl : K.IsLink e u v := (hKG.isLink_iff he).2 h.isLink
  exact ⟨hl, h.isPath.anti hKG hl.left_mem fun g hg => hE g (List.mem_cons_of_mem _ hg),
    h.notMem⟩

/-- The edges of a walk that the graph `H` does not have. The second measure of the blueprint's
minimal-counterexample argument is the size of this set for `H = Γ (j-1)`. -/
def edgesOutside (H : Graph α β) (W : List β) : Set β := {g | g ∈ W ∧ g ∉ E(H)}

theorem mem_edgesOutside {H : Graph α β} {W : List β} {g : β} :
    g ∈ edgesOutside H W ↔ g ∈ W ∧ g ∉ E(H) := Iff.rfl

theorem finite_edgesOutside (H : Graph α β) (W : List β) : (edgesOutside H W).Finite :=
  (W.finite_toSet).subset fun _ hg => hg.1

theorem edgesOutside_append (H : Graph α β) (W₁ W₂ : List β) :
    edgesOutside H (W₁ ++ W₂) = edgesOutside H W₁ ∪ edgesOutside H W₂ := by
  ext g
  simp only [mem_edgesOutside, List.mem_append, Set.mem_union]
  tauto

theorem edgesOutside_perm {H : Graph α β} {W₁ W₂ : List β} (hp : W₁.Perm W₂) :
    edgesOutside H W₁ = edgesOutside H W₂ := by
  ext g
  simp only [mem_edgesOutside, hp.mem_iff]

theorem edgesOutside_eq_empty {H : Graph α β} {W : List β} (h : ∀ g ∈ W, g ∈ E(H)) :
    edgesOutside H W = ∅ := by
  ext g
  simp only [mem_edgesOutside, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  exact h g

/-- **The count the descent step decreases.** Replacing one arc `D₂` of a cycle by a list `R` of
edges the graph `H` already has strictly lowers the number of edges outside `H`, provided the
discarded arc had at least one such edge.

The two arcs of a cycle share no edge, which is why the discarded edge is not silently still
present on the arc that was kept: that is what the `Nodup` hypothesis on the cycle's edge list
supplies. It holds for a cycle because the detour of `Graph.IsCycleThrough` is a path and does
not contain the named edge. -/
theorem edgesOutside_splice_lt {H : Graph α β} {W W' D₁ D₂ R : List β} (hnodup : W.Nodup)
    (hperm : W.Perm (D₁ ++ D₂)) (hperm' : W'.Perm (D₁ ++ R)) (hR : ∀ g ∈ R, g ∈ E(H))
    (hD₂ : ∃ g ∈ D₂, g ∉ E(H)) :
    (edgesOutside H W').ncard < (edgesOutside H W).ncard := by
  obtain ⟨g, hgD₂, hgH⟩ := hD₂
  have hdisj : List.Disjoint D₁ D₂ :=
    List.disjoint_of_nodup_append ((List.Perm.nodup_iff hperm).1 hnodup)
  have hW' : edgesOutside H W' = edgesOutside H D₁ := by
    rw [edgesOutside_perm hperm', edgesOutside_append, edgesOutside_eq_empty hR,
      Set.union_empty]
  have hW : edgesOutside H W = edgesOutside H D₁ ∪ edgesOutside H D₂ := by
    rw [edgesOutside_perm hperm, edgesOutside_append]
  have hsub : edgesOutside H W' ⊆ edgesOutside H W := by
    rw [hW', hW]; exact Set.subset_union_left
  refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2 ⟨g, ?_, ?_⟩)
    (finite_edgesOutside H W)
  · rw [hW]; exact Or.inr ⟨hgD₂, hgH⟩
  · rw [hW']
    exact fun hg' => hdisj hg'.1 hgD₂

end General

/-! ## Enclosing a point -/

section Plane

variable {β : Type*} {H K : Graph Plane β} {drawing : β → ℝ → Plane} {x : Plane}

/-- **"That face is the interior of its boundary cycle, which therefore encloses `x`."** A graph
*encloses* a point when some cycle of it has that point in its interior. -/
def Encloses (H : Graph Plane β) (drawing : β → ℝ → Plane) (x : Plane) : Prop :=
  ∃ (e : β) (u v : Plane) (D : List β),
    H.IsCycleThrough e u v D ∧ x ∈ inside (edgesCover drawing (e :: D))

/-- A cycle of a subgraph encloses whatever it enclosed. -/
theorem Encloses.mono (hHK : H ≤ K) (h : Encloses H drawing x) : Encloses K drawing x := by
  obtain ⟨e, u, v, D, hc, hin⟩ := h
  exact ⟨e, u, v, D, ⟨hc.isLink.mono hHK, hc.isPath.mono hHK, hc.notMem⟩, hin⟩

/-- **"The face of `H` containing `x` is connected and disjoint from `C`; since it contains
`x ∈ Int(C)` it lies in the bounded set `Int(C)`."** An enclosed point has a bounded face. -/
theorem isBounded_face_of_encloses (hx : x ∈ exterior H drawing)
    (henc : Encloses H drawing x) : Bornology.IsBounded (face H drawing x) := by
  obtain ⟨e, u, v, D, hcyc, hin⟩ := henc
  have hsub : edgesCover drawing (e :: D) ⊆ pointSet H drawing :=
    edgesCover_subset_pointSet fun g hg => hcyc.mem_edgeSet_cons hg
  -- The face is a connected subset of the complement of the cycle through `x`, so it lies in
  -- the component of `x` there, which is bounded because `x` is inside.
  have h1 : face H drawing x ⊆ connectedComponentIn (edgesCover drawing (e :: D))ᶜ x :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_face hx) fun w hw hw' => (face_subset_exterior _ _ _ hw) (hsub hw')
  exact (mem_inside_iff.1 hin).2.subset h1

/-- **"By `lem:face-cycles`, that face is the interior of its boundary cycle."** A point in a
bounded face of a finite 2-connected polygonal plane graph is enclosed by a cycle of it. -/
theorem encloses_of_isBounded_face [H.Finite] (hd : IsDrawing H drawing)
    (hpoly : ∀ g ∈ E(H), IsPolygonal (edgeArc drawing g)) (h2 : H.IsTwoConnected)
    (hx : x ∈ exterior H drawing) (hb : Bornology.IsBounded (face H drawing x)) :
    Encloses H drawing x := by
  obtain ⟨e, u, v, D, hfc⟩ := face_cycles' hd hpoly h2 x hx
  exact ⟨e, u, v, D, hfc.isCycle, hfc.eq_inside_of_isBounded' hb ▸ mem_face hx⟩

end Plane

/-! ## The chain -/

section Chain

variable {β : Type*} {Γ : ℕ → Graph Plane β} {G : Graph Plane β} {drawing : β → ℝ → Plane}
variable {n : ℕ} {x : Plane}

/-- **The hypotheses of `lem:outer-chain`.** `Γ 0, …, Γ n` are finite 2-connected polygonal
plane graphs, all drawn inside one ambient plane graph `G` — which is what makes "after
subdividing common points into vertices" true by construction — with consecutive members
sharing at least two vertices and nonconsecutive members disjoint. `n ≥ 2` is the blueprint's
`k ≥ 3`. -/
structure IsPlaneChain (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (G : Graph Plane β)
    (n : ℕ) : Prop where
  /-- At least three graphs. -/
  two_le : 2 ≤ n
  /-- Every member is drawn inside the ambient plane graph. -/
  le_ambient : ∀ p ≤ n, Γ p ≤ G
  /-- The ambient graph is a plane graph. -/
  isDrawing : IsDrawing G drawing
  /-- Its edges are polygonal. -/
  polygonal : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g)
  /-- Every member is finite. -/
  finite : ∀ p ≤ n, (Γ p).Finite
  /-- Every member is 2-connected. -/
  twoConnected : ∀ p ≤ n, (Γ p).IsTwoConnected
  /-- Consecutive members have at least two vertices in common. -/
  meet : ∀ p, p + 1 ≤ n → ∃ a b : Plane, a ≠ b ∧ a ∈ V(Γ p) ∧ a ∈ V(Γ (p + 1)) ∧
      b ∈ V(Γ p) ∧ b ∈ V(Γ (p + 1))
  /-- Nonconsecutive members are disjoint — as point sets, which is what the blueprint means
  and what the crosscut step of the proof uses. -/
  disjoint : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      Disjoint (pointSet (Γ p) drawing) (pointSet (Γ q) drawing)

namespace IsPlaneChain

variable {i m p : ℕ}

theorem block_le (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) : chainUnion Γ i m ≤ G :=
  chainUnion_le fun p _ hp' => h.le_ambient p (by omega)

theorem le_block (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) (hp : i ≤ p)
    (hp' : p ≤ i + m) : Γ p ≤ chainUnion Γ i m :=
  le_chainUnion (G := G) (fun q _ hq' => h.le_ambient q (by omega)) hp hp'

theorem block_finite (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    (chainUnion Γ i m).Finite :=
  chainUnion_finite fun p _ hp' => h.finite p (by omega)

theorem block_isDrawing (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    IsDrawing (chainUnion Γ i m) drawing :=
  h.isDrawing.mono (h.block_le hm)

theorem block_polygonal (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    ∀ g ∈ E(chainUnion Γ i m), IsPolygonal (edgeArc drawing g) :=
  fun g hg => h.polygonal g ((h.block_le hm).edgeSet_mono hg)

theorem block_isTwoConnected (h : IsPlaneChain Γ drawing G n) (hm : i + m ≤ n) :
    (chainUnion Γ i m).IsTwoConnected :=
  chainUnion_isTwoConnected (G := G) (fun q _ hq' => h.le_ambient q (by omega))
    (fun q _ hq' => h.twoConnected q (by omega)) fun q _ hq' => h.meet q (by omega)

/-- A point of a block's drawing lies on one of its members. -/
theorem mem_pointSet_block {z : Plane} (hz : z ∈ pointSet (chainUnion Γ i m) drawing) :
    ∃ p, i ≤ p ∧ p ≤ i + m ∧ z ∈ pointSet (Γ p) drawing := by
  induction m with
  | zero => exact ⟨i, le_rfl, le_rfl, hz⟩
  | succ m ih =>
    rw [chainUnion_succ, pointSet_union, Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨p, hp, hp', hzp⟩ := ih hz
      exact ⟨p, hp, by omega, hzp⟩
    · exact ⟨i + m + 1, by omega, by omega, hz⟩

/-- **"`Γ j` meets the earlier chain only through `Γ (j-1)`."** The block `Γ i ∪ ⋯ ∪ Γ (i+m)` and
the member `Γ (i+m+2)` are disjoint, every pair of indices involved being nonconsecutive. This
is the form the descent step consumes. -/
theorem disjoint_block_far (h : IsPlaneChain Γ drawing G n) (hm : i + m + 2 ≤ n) :
    Disjoint (pointSet (chainUnion Γ i m) drawing) (pointSet (Γ (i + m + 2)) drawing) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨q, -, hq', hzq⟩ := mem_pointSet_block hz
  exact Set.disjoint_left.1 (h.disjoint q (i + m + 2) (by omega) (by omega) (by omega)) hzq hz'

/-- Nonconsecutive members share no vertex. -/
theorem disjoint_vertexSet (h : IsPlaneChain Γ drawing G n) {q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (hpq : p + 1 < q) : Disjoint V(Γ p) V(Γ q) :=
  (h.disjoint p q hp hq hpq).mono vertexSet_subset_pointSet vertexSet_subset_pointSet

/-- Nonconsecutive members share no edge: an edge of both would be drawn inside both point
sets. -/
theorem disjoint_edgeSet (h : IsPlaneChain Γ drawing G n) {q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (hpq : p + 1 < q) : Disjoint E(Γ p) E(Γ q) := by
  rw [Set.disjoint_left]
  intro g hgp hgq
  have hmem : drawing g 0 ∈ edgeArc drawing g := ⟨0, unitInterval.zero_mem, rfl⟩
  exact Set.disjoint_left.1 (h.disjoint p q hp hq hpq)
    (edgeArc_subset_pointSet hgp hmem) (edgeArc_subset_pointSet hgq hmem)

end IsPlaneChain

/-! ### The assumed step

Everything in the blueprint's proof except this one paragraph is discharged below. -/

/-- **The crosscut step of `lem:outer-chain`, assumed.**

Given a cycle `C` of the block `Γ i ∪ ⋯ ∪ Γ (i+m+2)` that encloses `x`, which has an edge of the
last member `Γ (i+m+2)` outside `Γ (i+m+1)` *and* an edge of the earlier chain
`Γ i ∪ ⋯ ∪ Γ (i+m)` outside `Γ (i+m+1)`, there is a cycle of the same block that encloses `x`
and has strictly fewer edges outside `Γ (i+m+1)`.

This is the blueprint's paragraph beginning "Minimality of the interval implies that `C`
contains an edge of `Γ j` outside `Γ (j-1)`": choose points `a, b` in the interiors of the two
edges; each of the two arcs of `C` from `a` to `b` must meet `Γ (j-1)`, because `Γ j` meets the
earlier chain only through `Γ (j-1)`; take the two maximal subpaths of `C ∩ Γ (j-1)` they
contain and a minimum-length path `R` in `Γ (j-1)` from one to the other; `R` is a crosscut of
the side of `C` it lies in, and `thm:polygonal-crosscut` says exactly one of `R ∪ C₁`, `R ∪ C₂`
encloses `x`. That cycle stays in the block, and one nonempty outside portion of `C` has been
replaced by `R ⊆ Γ (j-1)`.

It is a statement about a single descent step, not about outer faces, and it does not mention
`n` except to keep the block inside the chain. A discharging module has
`Graph.IsCycleThrough.split_at`, `Graph.exists_spliced_cycle`, `Graph.IsDrawing.arcs_of_split`
and `Schoenflies.crosscutSplitsRegion` available. -/
def Descent (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) : Prop :=
  ∀ (i m : ℕ), i + (m + 2) ≤ n →
    ∀ (e : β) (u v : Plane) (D : List β),
      (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
      x ∈ inside (edgesCover drawing (e :: D)) →
      (∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1))) →
      (∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1))) →
      ∃ (e' : β) (u' v' : Plane) (D' : List β),
        (chainUnion Γ i (m + 2)).IsCycleThrough e' u' v' D' ∧
          x ∈ inside (edgesCover drawing (e' :: D')) ∧
          (edgesOutside (Γ (i + m + 1)) (e' :: D')).ncard <
            (edgesOutside (Γ (i + m + 1)) (e :: D)).ncard

namespace IsPlaneChain

variable {i m p : ℕ}

/-- The hypothesis of `lem:outer-chain` on consecutive pairs: `x` is in the outer face of every
`Γ p ∪ Γ (p+1)`. -/
def OuterOnPairs (Γ : ℕ → Graph Plane β) (drawing : β → ℝ → Plane) (n : ℕ) (x : Plane) : Prop :=
  ∀ p, p + 1 ≤ n → x ∈ exterior (chainUnion Γ p 1) drawing ∧
    ¬ Bornology.IsBounded (face (chainUnion Γ p 1) drawing x)

/-- **The base case, `j = i + 1`.** No cycle of a consecutive pair encloses a point of that
pair's outer face. -/
theorem not_encloses_pair (hout : OuterOnPairs Γ drawing n x) (hp : p + 1 ≤ n) :
    ¬ Encloses (chainUnion Γ p 1) drawing x := fun henc =>
  (hout p hp).2 (isBounded_face_of_encloses (hout p hp).1 henc)

/-- **The base case, `j = i`.** A single member of the chain is contained in a consecutive pair
— the one after it, or, at the far end, the one before it. -/
theorem not_encloses_single (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hp : p ≤ n) : ¬ Encloses (Γ p) drawing x := by
  intro henc
  have hn : 2 ≤ n := h.two_le
  rcases Nat.lt_or_ge p n with hlt | hge
  · exact not_encloses_pair hout (by omega)
      (henc.mono (h.le_block (i := p) (m := 1) (by omega) le_rfl (by omega)))
  · -- `p = n ≥ 2`, so the pair `Γ (p-1) ∪ Γ p` exists.
    obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    obtain rfl : p = q + 1 := by omega
    exact not_encloses_pair hout (by omega)
      (henc.mono (h.le_block (i := q) (m := 1) (by omega) (by omega) (by omega)))

/-- **The double minimal-counterexample argument.** No block of the chain encloses `x`.

The outer induction is on the length `m` of the block — the blueprint's "choose indices `i ≤ j`
with `j - i` minimum". Inside it, for a block of length at least two, the induction on `c` is
the blueprint's "choose `C` so that the number of its edges outside `Γ (j-1)` is minimum". -/
theorem not_encloses (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hdesc : Descent Γ drawing n x) :
    ∀ m i, i + m ≤ n → ¬ Encloses (chainUnion Γ i m) drawing x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => exact fun i him => h.not_encloses_single hout (by omega)
    | 1 => exact fun i him => not_encloses_pair hout (by omega)
    | (m + 2) =>
      intro i him henc
      -- The inner minimisation, as an induction on a bound for the number of edges of the
      -- cycle lying outside `Γ (i+m+1)`.
      have inner : ∀ c (e : β) (u v : Plane) (D : List β),
          (chainUnion Γ i (m + 2)).IsCycleThrough e u v D →
          x ∈ inside (edgesCover drawing (e :: D)) →
          (edgesOutside (Γ (i + m + 1)) (e :: D)).ncard < c → False := by
        intro c
        induction c with
        | zero => exact fun _ _ _ _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)
        | succ c ihc =>
          intro e u v D hcyc hin hlt
          -- Every edge of the cycle is an edge of some member of the block.
          have hmem : ∀ g ∈ e :: D, ∃ q, i ≤ q ∧ q ≤ i + (m + 2) ∧ g ∈ E(Γ q) := fun g hg =>
            mem_edgeSet_chainUnion.1 (hcyc.mem_edgeSet_cons hg)
          -- **"`C` contains an edge of `Γ j` outside `Γ (j-1)`."** Otherwise the cycle lives
          -- in the block one shorter, which the outer induction has excluded.
          have hA : ∃ g ∈ e :: D, g ∈ E(Γ (i + m + 2)) ∧ g ∉ E(Γ (i + m + 1)) := by
            by_contra hcon
            push Not at hcon
            have hE : ∀ g ∈ e :: D, g ∈ E(chainUnion Γ i (m + 1)) := by
              intro g hg
              obtain ⟨q, hq, hq', hgq⟩ := hmem g hg
              rcases Nat.lt_or_ge q (i + m + 2) with hlt' | hge'
              · exact mem_edgeSet_chainUnion.2 ⟨q, hq, by omega, hgq⟩
              · obtain rfl : q = i + m + 2 := by omega
                exact mem_edgeSet_chainUnion.2
                  ⟨i + m + 1, by omega, by omega, hcon g hg hgq⟩
            exact ih (m + 1) (by omega) i (by omega)
              ⟨e, u, v, D, hcyc.anti (left_le_union _ _) hE, hin⟩
          -- **"… and an edge of the earlier chain outside `Γ (j-1)`."** Otherwise the cycle
          -- lives in the consecutive pair `Γ (j-1) ∪ Γ j`.
          have hB : ∃ g ∈ e :: D, g ∈ E(chainUnion Γ i m) ∧ g ∉ E(Γ (i + m + 1)) := by
            by_contra hcon
            push Not at hcon
            have hpair : chainUnion Γ (i + m + 1) 1 ≤ chainUnion Γ i (m + 2) :=
              chainUnion_le fun q hq hq' =>
                h.le_block him (by omega) (by omega)
            have hE : ∀ g ∈ e :: D, g ∈ E(chainUnion Γ (i + m + 1) 1) := by
              intro g hg
              obtain ⟨q, hq, hq', hgq⟩ := hmem g hg
              rcases Nat.lt_or_ge q (i + m + 1) with hlt' | hge'
              · exact mem_edgeSet_chainUnion.2 ⟨i + m + 1, by omega, by omega,
                  hcon g hg (mem_edgeSet_chainUnion.2 ⟨q, hq, by omega, hgq⟩)⟩
              · exact mem_edgeSet_chainUnion.2 ⟨q, by omega, by omega, hgq⟩
            exact ih 1 (by omega) (i + m + 1) (by omega)
              ⟨e, u, v, D, hcyc.anti hpair hE, hin⟩
          -- The assumed crosscut step now produces a cycle with a smaller count.
          obtain ⟨e', u', v', D', hcyc', hin', hlt'⟩ := hdesc i m him e u v D hcyc hin hA hB
          exact ihc e' u' v' D' hcyc' hin' (by omega)
      obtain ⟨e, u, v, D, hcyc, hin⟩ := henc
      exact inner _ e u v D hcyc hin (Nat.lt_succ_self _)

/-- `x` is off the whole chain: it is off every consecutive pair, and every member belongs to
one. -/
theorem mem_exterior_chain (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing := by
  intro hx
  have hn : 2 ≤ n := h.two_le
  obtain ⟨p, -, hp, hxp⟩ := mem_pointSet_block hx
  -- The member `Γ p` lies in a consecutive pair, whose point set `x` avoids.
  have key : ∀ q, q + 1 ≤ n → x ∉ pointSet (Γ q) drawing ∧ x ∉ pointSet (Γ (q + 1)) drawing := by
    intro q hq
    have := (hout q hq).1
    rw [exterior, chainUnion_one, Set.mem_compl_iff, pointSet_union] at this
    exact ⟨fun hc => this (Or.inl hc), fun hc => this (Or.inr hc)⟩
  rcases Nat.lt_or_ge p n with hlt | hge
  · exact (key p (by omega)).1 hxp
  · obtain ⟨q, hq⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
    obtain rfl : p = q + 1 := by omega
    exact (key q (by omega)).2 hxp

/-- **`lem:outer-chain` (outer face of a chain).** If `x` is in the outer face of every
consecutive pair `Γ p ∪ Γ (p+1)`, then `x` is in the outer face of `Γ 0 ∪ ⋯ ∪ Γ n`.

"In the outer face" is `x ∈ exterior … ∧ ¬ IsBounded (face … x)`; by
`Graph.unbounded_face_unique` there is only one unbounded face, so this really does say `x` is
in *the* outer face. -/
theorem outer_chain (h : IsPlaneChain Γ drawing G n) (hout : OuterOnPairs Γ drawing n x)
    (hdesc : Descent Γ drawing n x) :
    x ∈ exterior (chainUnion Γ 0 n) drawing ∧
      ¬ Bornology.IsBounded (face (chainUnion Γ 0 n) drawing x) := by
  have hext := h.mem_exterior_chain hout
  refine ⟨hext, fun hb => ?_⟩
  haveI : (chainUnion Γ 0 n).Finite := h.block_finite (i := 0) (m := n) (by omega)
  exact h.not_encloses hout hdesc n 0 (by omega)
    (encloses_of_isBounded_face (h.block_isDrawing (by omega)) (h.block_polygonal (by omega))
      (h.block_isTwoConnected (by omega)) hext hb)

end IsPlaneChain

end Chain

end Graph
