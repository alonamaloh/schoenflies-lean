/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.Graph.TwoConnected

/-!
# Connectivity sees only the adjacency relation

Two graphs on the same vertex set with the same adjacency relation are connected together and
2-connected together, **even when their edge types differ**. Nothing here is deep; what makes it
worth a module is that it is the only way this development has to compare two graphs that
differ in their edge *names*.

That situation is not exotic. `Schoenflies.CommonSubdivision` has to exhibit a 2-connected
subgraph `K` of the extension graph `H` whose point set is the old drawn skeleton. `K` carries
`H`'s edge names, while the cell structure that realizes it carries names drawn from the
naming type `γ` by the freshness lemmas — and the two are, in general, different names for the
same arcs. 2-connectivity of the realized skeleton is a field of `IsWeaklyAdmissible` and so is
free; carrying it to `K` is exactly this transport.

`Graph.map` relabels vertices only, and neither Mathlib nor this repo has edge relabelling —
see the note on `InitialCell.aux` in `Schoenflies/InitialGenerated.lean`. That is not a gap
here: nothing below *builds* a relabelled graph, it only moves a property between two graphs
that already exist, and adjacency is all the property can see.

## Blueprint

Not a numbered statement. `Graph.IsTwoConnected.of_adj_congr` is the transport
`def:admissible-graph`'s 2-connectivity clause needs when the same drawn skeleton is presented
under two different edge namings.
-/

open Set
open scoped Graph

namespace Graph

variable {α β β' : Type*} {G : Graph α β} {G' : Graph α β'} {u v x y : α} {X : Set α}

/-- **Reachability only sees adjacency.** A walk is a chain of adjacent pairs, and each link of
the chain is replayed in the other graph by whatever edge realizes the same adjacency. -/
theorem Reaches.of_adj_congr (hV : V(G) ⊆ V(G')) (hadj : ∀ ⦃x y⦄, G.Adj x y → G'.Adj x y)
    (h : G.Reaches u v) : G'.Reaches u v := by
  obtain ⟨W, hW⟩ := h
  induction hW with
  | nil hx => exact .refl (hV hx)
  | cons hl _ ih => exact (Reaches.of_adj (hadj ⟨_, hl⟩)).trans ih

/-- **Connectedness only sees adjacency.** -/
theorem Connected.of_adj_congr (hV : V(G) = V(G')) (hadj : ∀ ⦃x y⦄, G.Adj x y ↔ G'.Adj x y)
    (h : G.Connected) : G'.Connected := by
  refine ⟨hV ▸ h.nonempty, fun u hu v hv => ?_⟩
  rw [← hV] at hu hv
  exact Reaches.of_adj_congr hV.subset (fun _ _ ha => hadj.1 ha) (h.reaches hu hv)

/-- The adjacency of a vertex deletion, in the form the transport needs: an edge survives
exactly when both of its ends do. -/
theorem adj_deleteVerts_iff : (G.deleteVerts X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  constructor
  · rintro ⟨e, he⟩
    rw [deleteVerts_isLink] at he
    exact ⟨⟨e, he.1⟩, he.2⟩
  · rintro ⟨⟨e, he⟩, hx, hy⟩
    exact ⟨e, (deleteVerts_isLink _ _).2 ⟨he, hx, hy⟩⟩

/-- **The counting clause only sees the vertex set.** `HasThreeVertices.mono` says this for two
graphs with the same edge type; the point of this module is that the edge types differ. -/
theorem HasThreeVertices.of_vertexSet_eq (hV : V(G) = V(G')) (h : G.HasThreeVertices) :
    G'.HasThreeVertices := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := h
  exact ⟨a, hV ▸ ha, b, hV ▸ hb, c, hV ▸ hc, hab, hac, hbc⟩

/-- **2-connectivity only sees adjacency.** Each of the three clauses does: the counting one is
`HasThreeVertices.of_vertexSet_eq`, and both connectivity ones are `Connected.of_adj_congr`, the
second after `adj_deleteVerts_iff` has pushed the deletion through the adjacency. -/
theorem IsTwoConnected.of_adj_congr (hV : V(G) = V(G'))
    (hadj : ∀ ⦃x y⦄, G.Adj x y ↔ G'.Adj x y) (h : G.IsTwoConnected) : G'.IsTwoConnected where
  hasThreeVertices := HasThreeVertices.of_vertexSet_eq hV h.hasThreeVertices
  connected := Connected.of_adj_congr hV hadj h.connected
  deleteVerts_connected := by
    intro z _
    refine Connected.of_adj_congr (G := G.deleteVerts {z}) ?_ ?_ (h.deleteVerts_connected' z)
    · rw [vertexSet_deleteVerts, vertexSet_deleteVerts, hV]
    · intro a b
      rw [adj_deleteVerts_iff, adj_deleteVerts_iff, hadj]

end Graph
