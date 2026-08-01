/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.SquareMesh
import Schoenflies.FaceCycles

/-!
# The inner grid of the anchored square mesh: 2-connectivity and the outer cycle

`Schoenflies/SquareMesh.lean` delivers the geometry of `prop:anchored-square-mesh` — the
diameter bound, the anchors, the inward edges at the fresh points, and connectedness of
`|T| ∖ S` — and leaves two clauses open, both of them combinatorial:

* clause 5, *the skeleton of `T` is 2-connected*, is absent;
* clause 3 is proved only as a point-set equation, never as a **cycle** of the graph.

This module supplies both for the object the blueprint's own proof of the proposition is about:
the **rectangular grid**. See "What this does and does not close" below for exactly what the
integrator still has to do.

## The grid, concretely

Two coordinate functions `xc yc : ℕ → ℝ` and two sizes `m n : ℕ` fix a grid: the vertices are
the `(m+1)(n+1)` points `gridPt xc yc i j = (xc i, yc j)`, the edges are the `m(n+1)`
horizontal steps `gridHEdge` and the `(m+1)n` vertical steps `gridVEdge`. Everything is a
`def` — an existentially quantified grid could not be refined against a second one, which is
what Part II does.

The only hypothesis the combinatorics needs is that the coordinates are **distinct**
(`Set.InjOn xc (Set.Iic m)`); monotonicity is needed only for the geometric statements about
what the outer cycle occupies.

The graph is `segGraph (gridEdges xc yc m n)`, where `segGraph` is the general "a list of
straight segments, read as a graph" constructor: an edge is a `Piece`, and it links exactly its
two ends. `segGraph` is `overlayGraph` without the subdivision — the vertices are the ends of
the listed segments and nothing is cut — and its point is that `segGraph l₁ ∪ segGraph l₂ =
segGraph (l₁ ++ l₂)` **on the nose** (`segGraph_union`), so that the blueprint's "add these
finitely many cycles one at a time" is list concatenation and every union is an equation
rather than an inclusion.

## 2-connectivity: two nested chains of `lem:union-two-connected`

The blueprint says "the inner grid is 2-connected by the same ear construction used for `K`".
The ear construction is replaced here by two applications of `Graph.IsTwoConnected.union`,
which is shorter and needs no ear at all:

* one **cell** — the boundary of a single rectangle of the grid — is a quadrilateral, and
  `Graph.isTwoConnected_of_quad` proves any quadrilateral 2-connected directly from the
  definition (delete a vertex; the other three are still a path);
* a **strip** (one column of cells) is the union of its cells, consecutive cells sharing the
  horizontal edge between them, hence two vertices;
* the **grid** is the union of its strips, consecutive strips sharing the whole vertical line
  between them, hence again two vertices.

Both chains need at least two vertices in common at every step, so both need `1 ≤ m` and
`1 ≤ n`: a grid with a single row of points is a path and is not 2-connected. That is the
degenerate case, and it is a hypothesis, not an oversight.

## The outer cycle

`gridBoundary` walks the four sides of the grid once, `gridBoundaryEdge`/`gridBoundaryPt`
naming the `2m + 2n` edges and vertices in order. `gridGraph_isCycleThrough_boundary` is a
`Graph.IsCycleThrough` of the grid graph, and `edgesCover_gridBoundary` computes what it
occupies: for a monotone grid it is exactly the frame of the bounding rectangle, and for the
grid on `[-1,1]²` that frame is `modelCurve`, i.e. `S`. That is the cycle
`thm:finite-transfer`(b) asks for, in the form it asks for it.

## What this does and does not close

**Closed.** Both clauses, for the rectangular grid, from an explicit construction.

**Not closed.** Neither clause is transported to `Schoenflies.squareMesh`, and the reason is
structural, not a matter of effort: `squareMesh` is `overlayGraph` applied to a list of
segments *and an unspecified list of cut points* obtained from `exists_cut_points` by choice.
Its edges are therefore the pieces of a subdivision nobody can enumerate, so neither "the
edges on `S` form a cycle" nor "the rings are cycles glued along the spokes" is available
without first proving that the subdivision of a segment at a finite point set is a **path**
— a theorem no module on `main` has. The honest statement of the missing step is
`Graph.IsTwoConnected.attach_cycles` below: it takes a 2-connected hub `K` and finitely many
2-connected pieces each meeting `K` in two distinct vertices, and concludes for the union.
Instantiating it at `squareMesh` needs the collar rectangles of the mesh as cycles, which is
exactly the enumeration that is missing.

## Blueprint

* `prop:anchored-square-mesh`, clause 5, for the inner grid — `gridGraph_isTwoConnected`.
* `prop:anchored-square-mesh`, clause 3, as a cycle — `gridGraph_isCycleThrough_boundary`
  together with `edgesCover_gridBoundary` and `edgesCover_gridBoundary_modelCurve`.
* `lem:union-two-connected` — used through `Graph.IsTwoConnected.union`; iterated here as
  `Graph.IsTwoConnected.attach_cycles`, which is the blueprint's "adding these finitely many
  cycles one at a time".
* `segGraph`, `segGraph_union` — the list-of-segments graph, and the fact that its unions are
  concatenations.
-/

open Metric Set
open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-! ### A quadrilateral is 2-connected

The base case of both chains below. The blueprint reaches it through the ear decomposition
(`lem:subdivision-ear-preserve` applied to a cycle); here it is read straight off the
definition of `Graph.IsTwoConnected`, because a four-vertex graph is small enough that
"delete one vertex and the rest is still connected" is four applications of one lemma. -/

/-- **A four-cycle is 2-connected.** No hypothesis on `G` beyond the four edges, the four
distinct vertices, and the fact that there are no other vertices. -/
theorem isTwoConnected_of_quad {e₁ e₂ e₃ e₄ : β} {a b c d : α}
    (h₁ : G.IsLink e₁ a b) (h₂ : G.IsLink e₂ b c) (h₃ : G.IsLink e₃ c d) (h₄ : G.IsLink e₄ d a)
    (hV : ∀ v ∈ V(G), v = a ∨ v = b ∨ v = c ∨ v = d)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a) (hac : a ≠ c) (hbd : b ≠ d) :
    G.IsTwoConnected := by
  -- Deleting a vertex keeps every link neither of whose ends was the one deleted.
  have dl : ∀ {f : β} {u v x : α}, G.IsLink f u v → u ≠ x → v ≠ x →
      (G.deleteVerts {x}).IsLink f u v := by
    intro f u v x h hu hv
    exact (deleteVerts_isLink _ _).2 ⟨h, by simpa using hu, by simpa using hv⟩
  -- After a deletion the three survivors form a path `p — q — r`; `q` is the hub.
  have main : ∀ (x p q r : α) (f g : β), G.IsLink f p q → G.IsLink g q r →
      p ≠ x → q ≠ x → r ≠ x → (∀ v ∈ V(G), v = x ∨ v = p ∨ v = q ∨ v = r) →
      (G.deleteVerts {x}).Connected := by
    intro x p q r f g hf hg hp hq hr hcov
    refine Connected.of_hub (mem_deleteVerts_singleton_of_ne hf.right_mem hq) ?_
    intro v hv
    obtain ⟨hvG, hvx⟩ := mem_deleteVerts_singleton.1 hv
    rcases hcov v hvG with rfl | rfl | rfl | rfl
    · exact absurd rfl hvx
    · exact (Reaches.of_isLink (dl hf hp hq)).symm
    · exact Reaches.refl (mem_deleteVerts_singleton_of_ne hf.right_mem hq)
    · exact Reaches.of_isLink (dl hg hq hr)
  refine ⟨⟨a, h₁.left_mem, b, h₁.right_mem, c, h₂.right_mem, hab, hac, hbc⟩, ?_, ?_⟩
  · refine Connected.of_hub h₁.left_mem fun v hv ↦ ?_
    rcases hV v hv with rfl | rfl | rfl | rfl
    · exact Reaches.refl h₁.left_mem
    · exact Reaches.of_isLink h₁
    · exact (Reaches.of_isLink h₁).trans (Reaches.of_isLink h₂)
    · exact (Reaches.of_isLink h₄).symm
  · intro x _
    rcases em (x = a) with rfl | hxa
    · exact main x b c d e₂ e₃ h₂ h₃ (Ne.symm hab) (Ne.symm hac) hda
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = b) with rfl | hxb
    · exact main x c d a e₃ e₄ h₃ h₄ (Ne.symm hbc) (Ne.symm hbd) hab
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = c) with rfl | hxc
    · exact main x d a b e₄ e₁ h₄ h₁ (Ne.symm hcd) hac hbc
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    rcases em (x = d) with rfl | hxd
    · exact main x a b c e₁ e₂ h₁ h₂ (Ne.symm hda) hbd hcd
        fun v hv ↦ by rcases hV v hv with h | h | h | h <;> tauto
    · -- Deleting a vertex the graph does not have changes nothing.
      refine Connected.deleteVerts_singleton_of_notMem ?_ fun hx ↦ ?_
      · refine Connected.of_hub h₁.left_mem fun v hv ↦ ?_
        rcases hV v hv with rfl | rfl | rfl | rfl
        · exact Reaches.refl h₁.left_mem
        · exact Reaches.of_isLink h₁
        · exact (Reaches.of_isLink h₁).trans (Reaches.of_isLink h₂)
        · exact (Reaches.of_isLink h₄).symm
      · rcases hV x hx with rfl | rfl | rfl | rfl
        exacts [hxa rfl, hxb rfl, hxc rfl, hxd rfl]

/-! ### Attaching finitely many pieces to a 2-connected hub

`prop:anchored-square-mesh`: *"The boundary of every collar rectangle is a cycle sharing with
the inner grid at least the two endpoints of its inner boundary arc. Adding these finitely many
cycles one at a time and applying `lem:union-two-connected` proves that the full mesh is
2-connected."*

`Graph.chainUnion_isTwoConnected` (`Schoenflies/OuterChain.lean`) iterates the same lemma along
a chain in which **consecutive** members meet. Here every piece meets the **hub**, which is
what the collar rectangles do — each meets the inner grid, but two collar rectangles on
opposite sides of the square meet nothing of each other. The two statements are independent;
the integrator may want them beside each other. -/

/-- The hub `K` with the pieces `Γ 0, …, Γ (m-1)` glued on, one at a time. -/
def attachUnion (K : Graph α β) (Γ : ℕ → Graph α β) : ℕ → Graph α β
  | 0 => K
  | (m + 1) => (attachUnion K Γ m).union (Γ m)

@[simp] theorem attachUnion_zero (K : Graph α β) (Γ : ℕ → Graph α β) :
    attachUnion K Γ 0 = K := rfl

@[simp] theorem attachUnion_succ (K : Graph α β) (Γ : ℕ → Graph α β) (m : ℕ) :
    attachUnion K Γ (m + 1) = (attachUnion K Γ m).union (Γ m) := rfl

theorem le_attachUnion (K : Graph α β) (Γ : ℕ → Graph α β) (m : ℕ) :
    K ≤ attachUnion K Γ m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (left_le_union _ _)

theorem attachUnion_le {K : Graph α β} {Γ : ℕ → Graph α β} {m : ℕ} (hK : K ≤ G)
    (hΓ : ∀ q, q < m → Γ q ≤ G) : attachUnion K Γ m ≤ G := by
  induction m with
  | zero => exact hK
  | succ m ih => exact union_le (ih fun q hq => hΓ q (by omega)) (hΓ m (by omega))

theorem piece_le_attachUnion {K : Graph α β} {Γ : ℕ → Graph α β} {m q : ℕ} (hK : K ≤ G)
    (hΓ : ∀ r, r < m → Γ r ≤ G) (hq : q < m) : Γ q ≤ attachUnion K Γ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | rfl
    · exact (ih (fun r hr => hΓ r (by omega)) h).trans (left_le_union _ _)
    · exact (Compatible.of_le_le (attachUnion_le hK fun r hr => hΓ r (by omega))
        (hΓ q (by omega))).right_le_union

/-- **`lem:union-two-connected`, iterated at a hub.** A 2-connected `K` and finitely many
2-connected pieces, each meeting `K` in two distinct vertices, have 2-connected union. -/
theorem IsTwoConnected.attach_cycles {K : Graph α β} {Γ : ℕ → Graph α β} {m : ℕ}
    (hK : K.IsTwoConnected) (hKG : K ≤ G) (hΓG : ∀ q, q < m → Γ q ≤ G)
    (hΓ : ∀ q, q < m → (Γ q).IsTwoConnected)
    (hmeet : ∀ q, q < m → ∃ a b : α, a ≠ b ∧ a ∈ V(K) ∧ a ∈ V(Γ q) ∧ b ∈ V(K) ∧ b ∈ V(Γ q)) :
    (attachUnion K Γ m).IsTwoConnected := by
  induction m with
  | zero => exact hK
  | succ m ih =>
    obtain ⟨a, b, hab, haK, haΓ, hbK, hbΓ⟩ := hmeet m (by omega)
    have hih := ih (fun q hq => hΓG q (by omega)) (fun q hq => hΓ q (by omega))
      fun q hq => hmeet q (by omega)
    have hcompat : (attachUnion K Γ m).Compatible (Γ m) :=
      Compatible.of_le_le (attachUnion_le hKG fun q hq => hΓG q (by omega)) (hΓG m (by omega))
    exact hih.union hcompat (hΓ m (by omega)) hab ((le_attachUnion K Γ m).vertexSet_mono haK)
      haΓ ((le_attachUnion K Γ m).vertexSet_mono hbK) hbΓ

end Graph

namespace Schoenflies

/-! ### The graph carried by a list of segments

`overlayGraph` subdivides; this does not. When the segments are already in general position —
which for a grid they are, by construction — no subdivision is wanted, and what is gained is
that unions are concatenations. -/

/-- The graph whose edges are the listed segments and whose vertices are their ends. -/
def segGraph (edges : List Piece) : Graph Plane Piece where
  vertexSet := endSet edges
  IsLink P x y := P ∈ edges ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1))
  edgeSet := {P | P ∈ edges}
  isLink_symm := fun _ _ => ⟨fun _ _ h => ⟨h.1, by tauto⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro P x y v w ⟨-, hxy⟩ ⟨-, hvw⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro P
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hP => ⟨P.1, P.2, hP, Or.inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, hP, _⟩ => hP⟩
  left_mem_of_isLink := by
    rintro P x y ⟨hP, h⟩
    exact ⟨P, hP, by tauto⟩

@[simp] theorem segGraph_vertexSet (l : List Piece) : V(segGraph l) = endSet l := rfl

@[simp] theorem segGraph_mem_edgeSet {l : List Piece} {P : Piece} :
    P ∈ E(segGraph l) ↔ P ∈ l := Iff.rfl

@[simp] theorem segGraph_isLink {l : List Piece} {P : Piece} {x y : Plane} :
    (segGraph l).IsLink P x y ↔
      P ∈ l ∧ ((x = P.1 ∧ y = P.2) ∨ (x = P.2 ∧ y = P.1)) := Iff.rfl

theorem segGraph_mem_vertexSet {l : List Piece} {v : Plane} :
    v ∈ V(segGraph l) ↔ ∃ P ∈ l, v = P.1 ∨ v = P.2 := Iff.rfl

/-- The canonical link of a listed segment: it joins its own two ends. -/
theorem segGraph_isLink_self {l : List Piece} {P : Piece} (h : P ∈ l) :
    (segGraph l).IsLink P P.1 P.2 := ⟨h, Or.inl ⟨rfl, rfl⟩⟩

theorem mem_vertexSet_segGraph_left {l : List Piece} {P : Piece} (h : P ∈ l) :
    P.1 ∈ V(segGraph l) := ⟨P, h, Or.inl rfl⟩

theorem mem_vertexSet_segGraph_right {l : List Piece} {P : Piece} (h : P ∈ l) :
    P.2 ∈ V(segGraph l) := ⟨P, h, Or.inr rfl⟩

theorem endSet_append (l l' : List Piece) : endSet (l ++ l') = endSet l ∪ endSet l' := by
  ext v
  simp only [endSet, Set.mem_setOf_eq, Set.mem_union, List.mem_append]
  constructor
  · rintro ⟨P, hP | hP, h⟩
    exacts [Or.inl ⟨P, hP, h⟩, Or.inr ⟨P, hP, h⟩]
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    exacts [⟨P, Or.inl hP, h⟩, ⟨P, Or.inr hP, h⟩]

theorem segGraph_mono {l l' : List Piece} (h : l ⊆ l') : segGraph l ≤ segGraph l' where
  vertexSet_mono := by
    rintro v ⟨P, hP, hv⟩
    exact ⟨P, h hP, hv⟩
  isLink_mono := by
    rintro P x y ⟨hP, hxy⟩
    exact ⟨h hP, hxy⟩

/-- Two segment graphs never disagree about a shared edge: an edge is its own pair of ends. -/
theorem segGraph_compatible (l l' : List Piece) : (segGraph l).Compatible (segGraph l') := by
  intro P hP hP' x y
  exact ⟨fun h => ⟨hP', h.2⟩, fun h => ⟨hP, h.2⟩⟩

/-- **The union of two segment graphs is the segment graph of the concatenation.** This is the
whole reason for `segGraph`: it turns "glue one more cycle on" into an equation. -/
theorem segGraph_union (l l' : List Piece) :
    (segGraph l).union (segGraph l') = segGraph (l ++ l') := by
  refine Graph.eq_of_le_of_subset_subset
    (Graph.union_le (segGraph_mono (List.subset_append_left _ _))
      (segGraph_mono (List.subset_append_right _ _))) ?_ ?_
  · rw [segGraph_vertexSet, endSet_append, Graph.vertexSet_union]
    exact subset_rfl
  · rintro P hP
    rcases List.mem_append.1 hP with h | h
    exacts [Or.inl h, Or.inr h]

/-! ### The rectangular grid

Two coordinate functions and two sizes. Nothing here asks the coordinates to be sorted: the
combinatorics needs only that **consecutive** coordinates differ, which is exactly what makes
each cell a genuine quadrilateral. Sortedness enters only with the geometry of the outer
cycle. -/

/-- The grid point with coordinate indices `(i, j)`. -/
def gridPt (xc yc : ℕ → ℝ) (i j : ℕ) : Plane := Plane.mk (xc i) (yc j)

/-- The horizontal grid edge from `(i, j)` to `(i+1, j)`. -/
def gridHEdge (xc yc : ℕ → ℝ) (i j : ℕ) : Piece := (gridPt xc yc i j, gridPt xc yc (i + 1) j)

/-- The vertical grid edge from `(i, j)` to `(i, j+1)`. -/
def gridVEdge (xc yc : ℕ → ℝ) (i j : ℕ) : Piece := (gridPt xc yc i j, gridPt xc yc i (j + 1))

theorem gridPt_ne_of_fst {xc yc : ℕ → ℝ} {i i' j j' : ℕ} (h : xc i ≠ xc i') :
    gridPt xc yc i j ≠ gridPt xc yc i' j' := fun he => by
  have := congrArg (fun p : Plane => p 0) he
  simp only [gridPt, Plane.mk_zero] at this
  exact h this

theorem gridPt_ne_of_snd {xc yc : ℕ → ℝ} {i i' j j' : ℕ} (h : yc j ≠ yc j') :
    gridPt xc yc i j ≠ gridPt xc yc i' j' := fun he => by
  have := congrArg (fun p : Plane => p 1) he
  simp only [gridPt, Plane.mk_one] at this
  exact h this

/-- The four sides of the cell whose lower-left corner is `(i, j)`, listed bottom, right, top,
left. -/
def cellEdges (xc yc : ℕ → ℝ) (i j : ℕ) : List Piece :=
  [gridHEdge xc yc i j, gridVEdge xc yc (i + 1) j, gridHEdge xc yc i (j + 1),
    gridVEdge xc yc i j]

/-- One column of `n` cells, the cells `(i, 0), …, (i, n-1)`. -/
def stripEdges (xc yc : ℕ → ℝ) (i n : ℕ) : List Piece :=
  (List.range n).flatMap (cellEdges xc yc i)

/-- The `m × n` grid: `m` columns of `n` cells. -/
def gridEdges (xc yc : ℕ → ℝ) (m n : ℕ) : List Piece :=
  (List.range m).flatMap fun i => stripEdges xc yc i n

/-- **The grid graph**: the `m × n` rectangular grid on the coordinates `xc`, `yc`, as a plane
graph with straight edges. -/
def gridGraph (xc yc : ℕ → ℝ) (m n : ℕ) : Graph Plane Piece := segGraph (gridEdges xc yc m n)

theorem stripEdges_succ (xc yc : ℕ → ℝ) (i n : ℕ) :
    stripEdges xc yc i (n + 1) = stripEdges xc yc i n ++ cellEdges xc yc i n := by
  rw [stripEdges, stripEdges, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem stripEdges_one (xc yc : ℕ → ℝ) (i : ℕ) :
    stripEdges xc yc i 1 = cellEdges xc yc i 0 := by
  rw [stripEdges_succ]; simp [stripEdges]

theorem cellEdges_subset_stripEdges {xc yc : ℕ → ℝ} {i j n : ℕ} (h : j < n) :
    cellEdges xc yc i j ⊆ stripEdges xc yc i n :=
  fun _ hP => List.mem_flatMap.2 ⟨j, List.mem_range.2 h, hP⟩

theorem gridEdges_succ (xc yc : ℕ → ℝ) (m n : ℕ) :
    gridEdges xc yc (m + 1) n = gridEdges xc yc m n ++ stripEdges xc yc m n := by
  rw [gridEdges, gridEdges, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem gridEdges_one (xc yc : ℕ → ℝ) (n : ℕ) :
    gridEdges xc yc 1 n = stripEdges xc yc 0 n := by
  rw [gridEdges_succ]; simp [gridEdges]

theorem stripEdges_subset_gridEdges {xc yc : ℕ → ℝ} {i m n : ℕ} (h : i < m) :
    stripEdges xc yc i n ⊆ gridEdges xc yc m n :=
  fun _ hP => List.mem_flatMap.2 ⟨i, List.mem_range.2 h, hP⟩

/-! ### The cell -/

/-- **One cell of the grid is 2-connected.** Its boundary is a quadrilateral, so this is
`Graph.isTwoConnected_of_quad` with the four corners named. Only the two consecutive-coordinate
inequalities are used. -/
theorem cellGraph_isTwoConnected {xc yc : ℕ → ℝ} {i j : ℕ} (hx : xc i ≠ xc (i + 1))
    (hy : yc j ≠ yc (j + 1)) : (segGraph (cellEdges xc yc i j)).IsTwoConnected := by
  have h₁ : gridHEdge xc yc i j ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₂ : gridVEdge xc yc (i + 1) j ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₃ : gridHEdge xc yc i (j + 1) ∈ cellEdges xc yc i j := by simp [cellEdges]
  have h₄ : gridVEdge xc yc i j ∈ cellEdges xc yc i j := by simp [cellEdges]
  refine Graph.isTwoConnected_of_quad (a := gridPt xc yc i j) (b := gridPt xc yc (i + 1) j)
    (c := gridPt xc yc (i + 1) (j + 1)) (d := gridPt xc yc i (j + 1))
    (segGraph_isLink_self h₁) (segGraph_isLink_self h₂)
    (segGraph_isLink_self h₃).symm (segGraph_isLink_self h₄).symm ?_
    (gridPt_ne_of_fst hx) (gridPt_ne_of_snd hy) (gridPt_ne_of_fst (Ne.symm hx))
    (gridPt_ne_of_snd (Ne.symm hy)) (gridPt_ne_of_fst hx) (gridPt_ne_of_fst (Ne.symm hx))
  rintro v ⟨P, hP, hv⟩
  simp only [cellEdges, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl <;>
    simp only [gridHEdge, gridVEdge] <;> tauto

/-! ### The strip, then the grid

Two chains of `Graph.IsTwoConnected.union`, and the two shared vertices are in each case the
two ends of one edge that both parts contain. -/

/-- **A column of cells is 2-connected.** Consecutive cells share the horizontal edge between
them, hence its two ends. -/
theorem stripGraph_isTwoConnected {xc yc : ℕ → ℝ} {i : ℕ} (hx : xc i ≠ xc (i + 1)) :
    ∀ k : ℕ, (∀ j ≤ k, yc j ≠ yc (j + 1)) →
      (segGraph (stripEdges xc yc i (k + 1))).IsTwoConnected := by
  intro k
  induction k with
  | zero =>
    intro hy
    rw [stripEdges_one]
    exact cellGraph_isTwoConnected hx (hy 0 le_rfl)
  | succ k ih =>
    intro hy
    -- The edge shared by the new cell and the previous one is the horizontal step at height
    -- `k+1`: the top of cell `(i, k)` and the bottom of cell `(i, k+1)`.
    have hold : gridHEdge xc yc i (k + 1) ∈ stripEdges xc yc i (k + 1) :=
      cellEdges_subset_stripEdges (Nat.lt_succ_self k) (by simp [cellEdges])
    have hnew : gridHEdge xc yc i (k + 1) ∈ cellEdges xc yc i (k + 1) := by simp [cellEdges]
    rw [stripEdges_succ, ← segGraph_union]
    exact (ih fun j hj => hy j (by omega)).union (segGraph_compatible _ _)
      (cellGraph_isTwoConnected hx (hy (k + 1) le_rfl)) (gridPt_ne_of_fst hx)
      (mem_vertexSet_segGraph_left hold) (mem_vertexSet_segGraph_left hnew)
      (mem_vertexSet_segGraph_right hold) (mem_vertexSet_segGraph_right hnew)

/-- **The grid is 2-connected.** Each new column shares with what is already there the whole
vertical line between them — in particular the two ends of its lowest edge.

The two size hypotheses are not decoration: a grid one point wide is a path, and a path is not
2-connected. -/
theorem gridGraph_isTwoConnected_aux {xc yc : ℕ → ℝ} {n : ℕ}
    (hy : ∀ j ≤ n, yc j ≠ yc (j + 1)) :
    ∀ k : ℕ, (∀ i ≤ k, xc i ≠ xc (i + 1)) →
      (segGraph (gridEdges xc yc (k + 1) (n + 1))).IsTwoConnected := by
  intro k
  induction k with
  | zero =>
    intro hx
    rw [gridEdges_one]
    exact stripGraph_isTwoConnected (hx 0 le_rfl) n hy
  | succ k ih =>
    intro hx
    -- The shared edge is the lowest vertical step of the new column: the right side of cell
    -- `(k, 0)` and the left side of cell `(k+1, 0)`.
    have hold : gridVEdge xc yc (k + 1) 0 ∈ gridEdges xc yc (k + 1) (n + 1) :=
      stripEdges_subset_gridEdges (Nat.lt_succ_self k)
        (cellEdges_subset_stripEdges (Nat.succ_pos n) (by simp [cellEdges]))
    have hnew : gridVEdge xc yc (k + 1) 0 ∈ stripEdges xc yc (k + 1) (n + 1) :=
      cellEdges_subset_stripEdges (Nat.succ_pos n) (by simp [cellEdges])
    rw [gridEdges_succ, ← segGraph_union]
    exact (ih fun i hi => hx i (by omega)).union (segGraph_compatible _ _)
      (stripGraph_isTwoConnected (hx (k + 1) le_rfl) n hy) (gridPt_ne_of_snd (hy 0 (by omega)))
      (mem_vertexSet_segGraph_left hold) (mem_vertexSet_segGraph_left hnew)
      (mem_vertexSet_segGraph_right hold) (mem_vertexSet_segGraph_right hnew)

/-- **`prop:anchored-square-mesh`, clause 5, for the inner grid.** -/
theorem gridGraph_isTwoConnected {xc yc : ℕ → ℝ} {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hx : ∀ i < m, xc i ≠ xc (i + 1)) (hy : ∀ j < n, yc j ≠ yc (j + 1)) :
    (gridGraph xc yc m n).IsTwoConnected := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := ⟨n - 1, by omega⟩
  exact gridGraph_isTwoConnected_aux (fun j hj => hy j (by omega)) k fun i hi => hx i (by omega)

end Schoenflies
