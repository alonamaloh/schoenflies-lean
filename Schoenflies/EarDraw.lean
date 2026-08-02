/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.EarPaths
import Schoenflies.RealizeSplit

/-!
# The abstract ear, drawn where the extension draws it

`Schoenflies.exists_abstract_ear` produces an ear as a path graph on fresh names, of any
prescribed length. `Schoenflies.EarStep` needs more: the ear has to be drawn **exactly where the
extension graph `H` draws the path it came from**, because the new stage must occupy
`|B ∪ ear|` and not merely something of the same shape.

So the abstract ear cannot be built first and drawn afterwards — the two are built together, and
that is what this module does. `Graph.IsEarChart` is the correspondence they stand in:

* the ear is `Graph.pathOn z steps` for a step list of fresh names,
* `earPos` carries its vertices to the points the concrete path visits, in order,
* `name` carries its edges to the concrete path's edges, in order,

and the last field, `isLink`, is what ties the two: every link of the abstract ear is a link of
`H` between the corresponding points.

## Why an edge-relabelling would not do

`Graph.map` relabels vertices only, and `Schoenflies/Graph/PathOn.lean` records why the drawn
ear cannot simply be pushed onto fresh names, nor its own edge names reused: `EarStep`
quantifies over every partial transfer, so a current cell may already carry a name that `H` uses
for an ear edge. `IsEarChart` is the alternative — not a graph isomorphism but a *chart*, a
correspondence recorded field by field, of which only what a drawing needs is asked for.

## What comes out

`Graph.exists_drawn_ear` returns the ear, its edge list, the two functions, and eight facts:
the ear is a path graph between the two old 0-cell names, its own names are fresh, `earPos` is
injective on it and carries it onto the concrete path's vertices, and — the two that matter —
**the drawn ear is a plane graph** and **it occupies exactly what the concrete path occupies**.
Those are `EarCrosscut.isDrawing` and the input to `EarCrosscut.subset_face` and `.polygonal`.

## Blueprint

* `Graph.IsEarChart`, `Graph.exists_isEarChart`, `Graph.exists_drawn_ear` — the ear of
  `def:generated-structure`, operation 2, as `thm:finite-transfer`(a) step 3 supplies it: a path
  of the extension graph `H`, presented on fresh cell names together with its drawing.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

variable {γ : Type*} {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}

/-- The set a list spans, peeled at the head. -/
theorem setOf_mem_cons {α : Type*} (a : α) (l : List α) :
    {x | x ∈ a :: l} = insert a {x | x ∈ l} := by
  ext x; simp [List.mem_cons]

/-! ### The correspondence between an abstract ear and a concrete path -/

/-- **A chart of the concrete path `a --D--> b` of `H` by an abstract ear on fresh names.**

`steps` is the ear's step list in the sense of `Graph.pathOn` — the ear itself is
`Graph.pathOn z steps` — so its vertex names are `z` followed by `steps.map Prod.snd` and its
edge names are `steps.map Prod.fst`. `earPos` places the vertex names and `name` matches the
edge names with `H`'s.

The two ends `z` and `w` are *old* names, the 0-cells of the current structure at `a` and `b`;
everything else is fresh, which is what `fresh_vertex` and `fresh_edge` say against the finite
set `avoid` the caller nominates.

`isLink` is the field that does the work: it is what makes the drawn ear a plane graph, since
every clause of `Graph.IsDrawing` for the ear is then the corresponding clause for `H`. -/
structure IsEarChart (H : Graph Plane γ) (a b : Plane) (D : List γ) (z w : γ) (avoid : Set γ)
    (steps : List (γ × γ)) (earPos : γ → Plane) (name : γ → γ) : Prop where
  /-- The ear's vertex names are distinct. -/
  nodup_vertices : (z :: steps.map Prod.snd).Nodup
  /-- So are its edge names. -/
  nodup_edges : (steps.map Prod.fst).Nodup
  /-- And no name is used for both. -/
  vertices_ne_edges : ∀ c ∈ z :: steps.map Prod.snd, c ∉ steps.map Prod.fst
  /-- Every interior vertex name is fresh. -/
  fresh_vertex : ∀ c ∈ steps.map Prod.snd, c ≠ w → c ∉ avoid
  /-- Every edge name is fresh. -/
  fresh_edge : ∀ g ∈ steps.map Prod.fst, g ∉ avoid
  /-- The ear ends at `w`. -/
  getLastD_eq : (steps.map Prod.snd).getLastD z = w
  /-- The ear's edges match the concrete path's, in order. -/
  map_name : (steps.map Prod.fst).map name = D
  /-- The ear starts where the concrete path starts. -/
  pos_source : earPos z = a
  /-- …and ends where it ends. -/
  pos_target : earPos w = b
  /-- The ear's vertices are placed at exactly the points the concrete path visits. -/
  image_pos : earPos '' {c | c ∈ z :: steps.map Prod.snd} = H.walkVertices a D
  /-- Distinct vertex names are placed at distinct points. -/
  injOn_pos : InjOn earPos {c | c ∈ z :: steps.map Prod.snd}
  /-- **Every link of the ear is the corresponding link of `H`.** -/
  isLink : ∀ ⦃f x y⦄, (pathOn z steps).IsLink f x y → H.IsLink (name f) (earPos x) (earPos y)

/-- **Every path of `H` is charted by an abstract ear on fresh names.**

The induction runs along the path from its source, which is where `Graph.IsPath` is built. Each
step consumes two fresh names — one for the edge and one for the vertex it arrives at — except
the last, which arrives at the prescribed old name `w`; the hypothesis `z = w ↔ a = b` is what
makes the two agree in the degenerate case and keeps the recursion uniform, since a path from a
vertex to itself is empty (`Graph.IsPath.eq_nil_of_eq`) and its chart is the one-vertex ear. -/
theorem exists_isEarChart [Infinite γ] :
    ∀ {a b : Plane} {D : List γ}, H.IsPath a D b → ∀ (z w : γ) (avoid : Set γ), avoid.Finite →
      z ∈ avoid → w ∈ avoid → (z = w ↔ a = b) →
      ∃ (steps : List (γ × γ)) (earPos : γ → Plane) (name : γ → γ),
        IsEarChart H a b D z w avoid steps earPos name := by
  intro a b D hD
  induction hD with
  | @nil x hx =>
    intro z w _ _ _ _ hzw
    obtain rfl : z = w := hzw.2 rfl
    refine ⟨[], fun _ => x, id, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · rw [walkVertices_nil]
      ext p
      simp [eq_comm]
    · intro c₁ h₁ c₂ h₂ _
      simp at h₁ h₂
      rw [h₁, h₂]
    · intro g p q h
      simp only [pathOn_nil] at h
      exact absurd h (by simp)
  | @cons u m v e W hl hW hfresh ih =>
    classical
    intro z w avoid hav hz hw hzw
    -- The two ends of a nonempty path are distinct, so the two old names are too.
    have huv : u ≠ v := fun h => hfresh (h ▸ hW.isWalk.target_mem_walkVertices)
    have hzwne : z ≠ w := fun h => huv (hzw.1 h)
    obtain ⟨z₀, f, hz₀, hf, hz₀f⟩ := Schoenflies.exists_fresh_pair hav
    -- The next vertex's name: the prescribed `w` if the rest of the path is empty, else fresh.
    set z' : γ := if m = v then w else z₀ with hz'def
    have hz'ne : z' ≠ f := by
      by_cases hmv : m = v
      · rw [hz'def, if_pos hmv]; rintro rfl; exact hf hw
      · rw [hz'def, if_neg hmv]; exact hz₀f
    have hz'w : z' = w ↔ m = v := by
      by_cases hmv : m = v
      · simp [hz'def, hmv]
      · rw [hz'def, if_neg hmv]
        exact ⟨fun h => absurd (h ▸ hw) hz₀, fun h => absurd h hmv⟩
    have hz'avoid : z' ≠ w → z' ∉ avoid := by
      intro h
      rw [hz'def, if_neg (fun hmv => h (hz'w.2 hmv))]
      exact hz₀
    set avoid' : Set γ := insert z' (insert f avoid) with havd
    obtain ⟨steps', earPos', name', chart'⟩ := ih z' w avoid' ((hav.insert f).insert z')
      (mem_insert _ _) (mem_insert_of_mem _ (mem_insert_of_mem _ hw)) hz'w
    have havsub : avoid ⊆ avoid' := fun c hc => mem_insert_of_mem _ (mem_insert_of_mem _ hc)
    -- The names the sub-chart uses, and what `z` and `f` are not among.
    have hfreshV : ∀ c ∈ z' :: steps'.map Prod.snd, c ≠ w → c ∉ avoid := by
      rintro c hc hcw hca
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hz'avoid hcw hca
      · exact chart'.fresh_vertex c hc hcw (havsub hca)
    have hzV' : z ∉ z' :: steps'.map Prod.snd := fun hc => hfreshV z hc hzwne hz
    have hzE' : z ∉ steps'.map Prod.fst := fun hc => chart'.fresh_edge z hc (havsub hz)
    have hfw : f ≠ w := fun h => hf (h ▸ hw)
    have hfV' : f ∉ z' :: steps'.map Prod.snd := by
      rintro hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hz'ne rfl
      · exact chart'.fresh_vertex f hc hfw (mem_insert_of_mem _ (mem_insert _ _))
    have hfE' : f ∉ steps'.map Prod.fst := fun hc =>
      chart'.fresh_edge f hc (mem_insert_of_mem _ (mem_insert _ _))
    have hzf : z ≠ f := fun h => hf (h ▸ hz)
    refine ⟨(f, z') :: steps', fun c => if c = z then u else earPos' c,
      fun g => if g = f then e else name' g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.nodup_cons.2 ⟨by simpa using hzV', by simpa using chart'.nodup_vertices⟩
    · exact List.nodup_cons.2 ⟨by simpa using hfE', by simpa using chart'.nodup_edges⟩
    · intro c hc
      simp only [List.map_cons, List.mem_cons] at hc ⊢
      push Not
      refine ⟨?_, ?_⟩
      · rintro rfl
        rcases hc with h | h | h
        · exact hzf h.symm
        · exact hz'ne h.symm
        · exact hfV' (List.mem_cons_of_mem _ h)
      · intro hcE
        rcases hc with h | h | h
        · rw [h] at hcE; exact hzE' hcE
        · rw [h] at hcE; exact chart'.vertices_ne_edges z' (by simp) hcE
        · exact chart'.vertices_ne_edges c (by simp [h]) hcE
    · simp only [List.map_cons]
      exact hfreshV
    · intro g hg
      simp only [List.map_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hf
      · exact fun hc => chart'.fresh_edge g hg (havsub hc)
    · rw [List.map_cons, List.getLastD_cons]
      exact chart'.getLastD_eq
    · simp only [List.map_cons]
      rw [if_pos trivial]
      congr 1
      rw [← chart'.map_name]
      exact List.map_congr_left fun g hg =>
        if_neg (fun (h : g = f) => hfE' (by rw [← h]; exact hg))
    · simp
    · rw [if_neg (Ne.symm hzwne)]
      exact chart'.pos_target
    · have hagree : ∀ c ∈ {c | c ∈ z' :: steps'.map Prod.snd},
          (if c = z then u else earPos' c) = earPos' c :=
        fun c hc => if_neg (fun (h : c = z) => hzV' (by rw [← h]; exact hc))
      have hzu : (if z = z then u else earPos' z) = u := if_pos rfl
      rw [List.map_cons, setOf_mem_cons, Set.image_insert_eq, Set.image_congr hagree,
        chart'.image_pos, walkVertices_cons hl, hzu]
    · have hagree : ∀ c ∈ {c | c ∈ z' :: steps'.map Prod.snd},
          (if c = z then u else earPos' c) = earPos' c :=
        fun c hc => if_neg (fun (h : c = z) => hzV' (by rw [← h]; exact hc))
      have hzu : (if z = z then u else earPos' z) = u := if_pos rfl
      have hu : ∀ c ∈ {c | c ∈ z' :: steps'.map Prod.snd},
          (if c = z then u else earPos' c) ≠ u := by
        intro c hc hcon
        rw [hagree c hc] at hcon
        refine hfresh ?_
        rw [← hcon, ← chart'.image_pos]
        exact Set.mem_image_of_mem earPos' hc
      rw [List.map_cons, setOf_mem_cons]
      intro c₁ h₁ c₂ h₂ heq₀
      have heq : (if c₁ = z then u else earPos' c₁) = (if c₂ = z then u else earPos' c₂) := heq₀
      simp only [Set.mem_insert_iff] at h₁ h₂
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · rw [h₁, h₂]
      · rw [h₁, hzu] at heq
        exact absurd heq.symm (hu c₂ h₂)
      · rw [h₂, hzu] at heq
        exact absurd heq (hu c₁ h₁)
      · rw [hagree c₁ h₁, hagree c₂ h₂] at heq
        exact chart'.injOn_pos h₁ h₂ heq
    · intro g p q hlink
      show H.IsLink (if g = f then e else name' g)
        (if p = z then u else earPos' p) (if q = z then u else earPos' q)
      rw [pathOn_cons, union_isLink] at hlink
      have hz'z : z' ≠ z := fun h => hzV' (by rw [← h]; simp)
      rcases hlink with ⟨rfl, hs⟩ | ⟨hgne, hlink⟩
      · rw [if_pos rfl]
        rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [if_pos rfl, if_neg hz'z, chart'.pos_source]
          exact hl
        · rw [if_pos rfl, if_neg hz'z, chart'.pos_source]
          exact hl.symm
      · have hgf : g ≠ f := fun h => hgne (by simp [h])
        have hpV : p ∈ {c | c ∈ z' :: steps'.map Prod.snd} := by
          have := hlink.left_mem
          rwa [vertexSet_pathOn, ← setOf_mem_cons] at this
        have hqV : q ∈ {c | c ∈ z' :: steps'.map Prod.snd} := by
          have := hlink.right_mem
          rwa [vertexSet_pathOn, ← setOf_mem_cons] at this
        rw [if_neg hgf, if_neg (fun (h : p = z) => hzV' (by rw [← h]; exact hpV)),
          if_neg (fun (h : q = z) => hzV' (by rw [← h]; exact hqV))]
        exact chart'.isLink hlink

end Graph
