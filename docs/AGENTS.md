# Implementer briefing — schoenflies-lean

## Your workspace

Provision a private git worktree that shares the main repo's already-built Mathlib:

```sh
/home/alvaro/claude/schoenflies-lean/docs/new-worker.sh <yourname>
```

It prints the worktree path. It is a real branch `wt/<yourname>` off `main`. Work there and
nowhere else. Never edit `/home/alvaro/claude/schoenflies-lean` directly — other agents are
running concurrently.

First thing in a fresh worktree, warm the build cache once:

```sh
cd <worktree> && export PATH="$HOME/.elan/bin:$PATH" && lake build Schoenflies
```

That takes ~35s from cold (Mathlib itself is shared and never rebuilt). After it, build
**only your own module**, by name:

```sh
lake build Schoenflies.<YourModule>
```

`lake build` with no target will *not* pick up a new file: the library's root module is
`Schoenflies.lean` and it lists imports explicitly. **Do not edit `Schoenflies.lean`** — every
agent would conflict on it; the integrator adds the import.

Warm builds of one module are ~2s. If a build takes minutes, something is wrong — say so
rather than waiting.

When your module compiles with no `sorry` and no errors, commit on your branch:

```sh
git add -A && git commit -m "<subject>

<body>

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>"
```

## Hard requirements

- **Commit early and often.** As soon as any coherent piece compiles, commit it — and keep
  committing as you go. Do not wait for the module to be finished. A `wip: <what is done so
  far>` commit is worth far more than an uncommitted better one.

  This is not bookkeeping. One wave was cut short partway through by an account spend limit,
  killing seven agents mid-run. The only work that survived was work already committed: two
  agents had committed a partial module and their branches were merged and are on `main`; three
  had not, and everything they had done was lost. Your worktree is not a safe place to leave
  work.

- **No `sorry`, no `admit`, no `native_decide`.** A module that does not compile clean is not
  done. If you cannot finish a declaration, say so explicitly in your report and leave the
  declaration OUT of the file rather than stubbing it.
- **A missing result is a hypothesis, never a `sorry`.** If your proof needs a fact that is
  not yet available, state it as an explicit hypothesis of your theorem and name it in your
  report. That keeps the axiom audit (`#print axioms`, everything on
  `propext`/`Classical.choice`/`Quot.sound`) a real guarantee, and makes an interface defect
  surface at the consumer rather than at the end. A hypothesis must be a *statement you
  believe and that a later module can discharge* — never a restatement of your own goal, and
  never something false.
- **When a theorem is the interface to a construction, export the construction.** Return the
  object as a `def` with lemmas about it, not an `∃`-packaged bundle of properties. An
  existentially packaged conclusion has typechecked and then proved too weak at the call site
  five separate times in this project.
- **Do not weaken a statement to make it provable** without saying so prominently in your
  report. A weaker lemma that silently fails to serve its consumer is worse than an admitted gap.
- Every file starts with the copyright header used by the existing modules and a module
  docstring whose `## Blueprint` section maps declarations to blueprint statement numbers.
- Match the surrounding style: `theorem`/`def` docstrings in prose, comments explaining *why*
  a step is taken, not what it does.

## This Mathlib (v4.32.2) — frictions already paid for

These cost real time to discover. Do not rediscover them.

- **`WithLp` is a structure, not a type synonym.** `EuclideanSpace ℝ (Fin 2)` elements are
  therefore *not* functions definitionally.
  - `x i` works, via a `CoeFun` instance (displayed as `x.ofLp i`).
  - To prove two points equal, use the `ext` tactic (`PiLp.ext` is `@[ext]`). **`funext` fails.**
  - Build points with `!₂[a, b]`, or with this repo's `Plane.mk a b`.
- **Inner product**: the ring is explicit — `inner ℝ u v`. The `⟪x, y⟫_ℝ` notation does **not**
  exist here; the scoped notation in `RealInnerProductSpace` is `⟪x, y⟫` with no subscript.
  `Schoenflies.Plane.inner_eq` reduces it to coordinates.
- **`push_neg` is deprecated**; write `push Not at h`.
- Useful coordinate lemmas: `EuclideanSpace.real_norm_sq_eq` (`‖x‖^2 = ∑ i, x i ^ 2`),
  `EuclideanSpace.norm_eq`, `EuclideanSpace.dist_eq`, `PiLp.inner_apply`, `Fin.sum_univ_two`,
  `sq_abs`. The usual shape is `rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]; ring`
  — and note `simp` sometimes closes the goal, making a trailing `ring` an error
  ("No goals to be solved"); drop it when that happens.
- `fin_cases i <;> simp` is the workhorse for a two-coordinate goal.
- Mathlib names confirmed present and useful: `isCompact_Icc`, `IsCompact.inter`,
  `IsCompact.exists_thickening_subset_open`, `Metric.mem_thickening_iff`, `Metric.diam_closure`,
  `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`,
  `eq_Icc_of_connected_compact`, `segment_eq_image_lineMap`, `segment_eq_image'`,
  `segment_eq_Icc`, `image_segment`, `Convex.affine_preimage`, `Convex.isConnected`,
  `Convex.isPreconnected`, `AffineMap.lineMap`, `AffineMap.lineMap_continuous`,
  `IsPreconnected.subset_connectedComponentIn`, `isPreconnected_connectedComponentIn`,
  `connectedComponentIn_subset`, `mem_connectedComponentIn`, `IsOpen.frontier_eq`.
- **Confirm every other Mathlib name by grepping** the source at
  `/home/alvaro/claude/schoenflies-lean/.lake/packages/mathlib/Mathlib`. Citing a lemma that
  does not exist in this version wastes more time than looking it up.

## What is already on `main`

> **The authoritative list is `docs/INVENTORY.md`** — every declaration on `main`, by module,
> regenerated by `docs/regen-inventory.py`. **Grep it before you state any lemma.** The prose
> summary below is the historical wave-1 list and is no longer complete; treat it as a guide
> to *which module holds what kind of thing*, not as an index.

Two gates, both a couple of seconds, both to be run from the repository root after a build:

```sh
python3 docs/regen-inventory.py   # rewrites INVENTORY.md; exits 1 on a duplicate name
python3 docs/audit-axioms.py      # #print axioms on every declaration; exits 1 on any other axiom
```

The duplicate gate is not redundant with the build: Lean's import checker accepts two modules
declaring the same name when the statements are alpha-equivalent `Prop`s, because proof
irrelevance makes them defeq. That has landed on `main` twice. The axiom gate is not redundant
with grepping for `sorry`: a `sorry` reached through a chain of definitions shows up as
`sorryAx` in the audit and nowhere else.

Sixty-two modules, ~28k lines, all `sorry`-free, every theorem on
`propext`/`Classical.choice`/`Quot.sound`. **Read the ones your module touches before
writing anything** — reuse their lemmas rather than reproving them, and tell the integrator if
one is stated in the wrong form for your use.

Plane geometry:
- `Plane.lean` — `Plane := EuclideanSpace ℝ (Fin 2)`, `Plane.mk`, `inner_eq`; the orientation
  form `det` and rotation `perp` with full algebra (`det_comm`, bilinearity, `det_perp_self`,
  `perp_perp`, `norm_perp`, `inner_perp_self`, `det_perp_right`, `det_perp_left`,
  `det_perp_perp`, `det_eq_zero_iff_smul`); compactness toolkit
  (`notMem_of_mem_segment_of_isMinOn`, `exists_thickening_subset`, `exists_dist_pos`,
  `exists_ball_subset_diff`, `eq_singleton_iInter_of_diam_tendsto_zero`,
  `connectedComponentIn_eq_of_frontier_disjoint`).
- `Topology.lean` — `isOpen_connectedComponentIn`, `frontier_connectedComponentIn_compl_subset`,
  `continuousOn_union_of_isClosed` (pasting, two closed pieces).
- `Direction.lean` — `IsDirection`, `dir`, `arcCCW` and the angle-free direction facts:
  `det_ne_zero_iff`, `arcCCW_disjoint`, `mem_ray_or_mem_arcCCW`,
  `same_arc_of_det_neg_of_det_pos`, the `det_germ*` / `germ_mem_arcCCW*` family, `germs_split`,
  `exists_germ_threshold`, `exists_isDirection_det_ne_zero` (a direction non-parallel to any of
  a finite set), `isOpen_arcCCW`.
- `Square.lean` — `sub_apply`, `smul_add_apply`, `continuous_coord`; `supNorm`, `supDist`,
  `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm`; `convex_coord_le/ge/lt/gt`,
  `isOpen_coord_lt/gt`; `closedSquare`, `openSquare` with convexity/openness/closedness;
  `beyondSquare`, `isConnected_beyondSquare`.
- `Bounded.lean` — `beyondSquare_eq_compl`, `exists_closedSquare_of_isBounded`,
  `IsCompact.exists_closedSquare`, `closedSquare_mono`, `exists_closedSquare_of_finite`,
  `isOpen_compl_of_finite_isCompact`.
- `SegmentCut.lean` — `segment_split`, `openSegment_left_subset`, `openSegment_right_subset`.
- `SegmentMeet.lean` — `segment_inter_segment` (two segments meet in nothing or in a segment).
- `SegmentOrder.lean` — the distance from an end as a coordinate: `parameter_le_of_distance`,
  `eq_of_dist_left_eq`, `dist_le_of_mem_segment` / `mem_segment_of_dist_le` and the strict
  pair, `dist_le_left_of_notMem_openSegment`, and the two overlay results
  `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` (plus `_oriented` forms).
  **Both are stated inside one ambient segment** — without that the first is false.
- `Line.lean` — `line`, `lineCoord`, `mem_line_iff_det_eq_zero`, `lineMap_injective`,
  `isClosed_line`, `exists_segment_eq_of_isCompact_isConnected`,
  `exists_openSegment_eq_connectedComponentIn` (a component of line ∩ bounded open is an open
  segment whose closure has **both endpoints in `frontier U`**), `eqOn_line_of_fixed`,
  `affineMap_ext_of_affineIndependent`.
- `PolyPath.lean` — `poly : List Plane → Set Plane`, `isCompact_segment`, `isCompact_poly`,
  `isConnected_poly`, `mem_poly_of_mem`, `head_mem_poly`, `getLast_mem_poly`, `poly_concat`,
  `exists_poly_of_isPreconnected`.
- `Polygonal.lean` — `IsPolygonal`, `poly_pair`, `isPolygonal_segment`,
  `isArcBetween_segment` (a nondegenerate segment is an arc between its endpoints),
  `isArc_segment`.

Curves:
- `Curve.lean` — `IsArc`, `IsArcBetween`, `IsLoop` (structure: `continuousOn`, `closes`,
  `injOn` on `Ico 0 1`), `IsJordanCurve`, parametrized by `unitInterval` as a **subset of ℝ**
  (`ContinuousOn f I`, `InjOn f I`, `f '' I = A`); `zero_mem_I`, `one_mem_I`, `isCompact_I`,
  `isConnected_I`, `isCompact_image_of_subset_I`; compactness / connectedness / closedness /
  endpoint membership / `IsArcBetween.reverse` / `IsArc.exists_isArcBetween`.
- `Subarc.lean` — `reparam`, `subarc`, `subarc_image`, `isArcBetween_subarc`, `isArc_subarc`,
  `IsArc.exists_isArcBetween_subset`, `openArc`, `openArc_eq_diff`, `image_isRelOpen`
  (a parametrization is an open map onto its arc), `openArc_isRelOpen`,
  `basic_piece_inside_ball`.
- `Concatenate.lean` — `lowerHalf`, `upperHalf`, `concatenate`, `continuousOn_concatenate`,
  `injOn_concatenate`, `image_concatenate`, `IsArcBetween.concatenate`, `IsArc.concatenate`,
  `IsLoop.concatenate`, `IsJordanCurve.of_two_arcs`.

## Graphs: Mathlib's multigraph, plus what wave 1 built

This Mathlib has `Mathlib/Combinatorics/Graph/` — a **general multigraph** `Graph α β`:
`V(G) : Set α`, `E(G) : Set β`, and `G.IsLink e x y`. Parallel edges are edges with equal ends
and different names, which is what a two-vertex cycle needs. Vertex and edge sets are embedded
in ambient types, so a subgraph is a term of the same type `Graph α β` with comparable edges.
`Delete.lean`, `Subgraph.lean`, `Lattice.lean`, `Maps.lean`, `Graph.Compatible` come with it.
Notation `V(G)`, `E(G)` needs `open scoped Graph`.

Mathlib has **no** walk, path, cycle, connectivity, degree, tree, 2-connectivity or ear theory
on it. Wave 1 built the first two layers of that, in `Schoenflies/Graph/`:

- `Graph/Walk.lean` — `coveredVertices`, `walkVertices`; `IsWalk` (an **inductive family in
  Prop, built at the source end**, i.e. the head of the edge list), `IsWalk.single/append/
  reverse/mono/anti/crossing/target_unique/edgeSet_subset/walkVertices_subset`;
  `IsPath` (same inductive plus the freshness clause: the vertex a step departs from is not
  among those the rest visits), `IsPath.nodup/reverse/split/from_visited/extend_at_target/
  not_isLoopAt/mono`; `IsWalk.contains_path`; `Reaches` (+`refl/symm/trans/of_isLink/of_adj/
  exists_isPath/mono`); `Connected` (+`nonempty/reaches/of_hub/exists_isPath`).
- `Graph/Degree.lean` — a `Graph.Finite` class (`finite_vertexSet`, `finite_edgeSet`) with
  `vertexFinset` / `edgeFinset`; `degree`; `sum_degree_eq_two_mul_ncard_edgeSet` (**the
  handshake lemma, loops allowed, no side condition**); `IsLeaf` and its API.

### Conventions these two fixed, which you must follow

1. **Namespace.** Graph declarations live in the ROOT `Graph` namespace, extending Mathlib's —
   NOT under `Schoenflies`. Without that, `G.IsWalk u W v` and `hW.append h₂` do not resolve by
   dot notation. Keep doing this in every `Schoenflies/Graph/*.lean` module.
2. **The empty walk requires `x ∈ V(G)`.** That makes `IsWalk.left_mem`, `.right_mem` and
   `.walkVertices_subset` hypothesis-free. The cost is that `Reaches.refl` takes `u ∈ V(G)`.
3. **Loops are tolerated by walks and excluded from paths by the definition.** Do NOT add a
   looplessness hypothesis to reach a conclusion about paths — `IsPath.not_isLoopAt` is
   available with none.
4. `IsWalk.mono` pushes a walk up an inclusion `H ≤ G`; `IsWalk.anti` pulls one down given that
   the source and all edges survive. `anti` is the tool every deletion argument reduces to.

### Two frictions wave 1 paid for

- **`List.Subset.trans` collides with the deprecated `HasSubset.Subset.trans`.** Dot notation
  `hAB.trans hBC` on a list subset resolves to the deprecated one and fails with "Invalid field
  notation". Write `List.Subset.trans hAB hBC` explicitly.
- **`induction` on `IsWalk`/`IsPath` auto-reverts every hypothesis mentioning an index**, and
  all three of source, edge list and target are indices — so the induction hypothesis silently
  gains those as extra arguments (`ih h₂`, `ih hl hv₀`). Expect it; it is not a bug.

## Sources

- Blueprint: `/home/alvaro/claude/schoenflies/jordan_schoenflies.tex` (statement numbers).
- Companion formalization of the same foundation, in a *different* proof language — read it for
  *what* is proved and for proof routes, never for syntax:
  `/home/alvaro/claude/math/library/{Plane,Plane/Graph,Graph,Metric}`, steered by
  `/home/alvaro/claude/math/PLAN_JORDAN_SCHOENFLIES.md`.

## Your report

Return: what compiled, what you left out and why, any Mathlib gap you had to work around, and
any place where the interface you were handed was wrong for its consumer. Be blunt — a
misleading "done" costs the integrator a rebuild.


## Update after waves 2a / 2b — READ THIS

`main` has moved on. Run
`ls /home/alvaro/claude/schoenflies-lean/Schoenflies /home/alvaro/claude/schoenflies-lean/Schoenflies/Graph`
and read what you depend on. Added since the inventory above:

- `TwoArcs.lean` — `IsJordanCurve.two_arcs` (two points cut a curve into two arcs), the
  parameter-level `IsLoop.two_arcs_at_parameters`, and `two_arcs_of_two_arcs` (the composition
  check against `of_two_arcs`).
- `Subdivide.lean` — `Piece := Plane × Plane`, `Piece.seg`, `Piece.interior`, `Piece.Nondeg`,
  `cover`, `splitAt`, `splitAllAt`, `subdivide`, and `subdivide_cover` / `subdivide_ne` /
  `subdivide_interior_subset` / `subdivide_avoids`.
- `Graph/Drawing.lean` — `edgeArc`, `IsDrawing`, `arcs_meet_at_vertex`, `unique_edge_at`,
  `pointSet`, `exterior`, `face`, `face_eq_or_disjoint`, and the compactness/openness lemmas.
- `Graph/OuterFace.lean` — `exists_unbounded_face`, `unbounded_face_unique`,
  `beyondSquare_subset_face`, `isBounded_closedSquare`.
- `Graph/Cycle.lean` — `IsCycleThrough`, `LiesOnCycle`, `IsAcyclic`, `IsBridge`,
  `liesOnCycle_iff_deleteEdges_reaches`, and a deletion interface for walks and paths.
- `Graph/TwoConnected.lean` — `deleteVerts` interface, `IsCutVertex`, `HasThreeVertices`,
  `IsTwoConnected`, `no_cut_vertex`, `no_bridge`, `not_isTwoConnected_banana`, union lemmas
  and `IsTwoConnected.union`.
- `Graph/PathGraph.lean` — `IsWalk.avoiding`, `IsPath.reaches_an_end`, `IsPathGraph` with its
  API, `pathGraphOf` and its vertex/edge/link lemmas, and finiteness of what it spans.

### Do not reprove these — a collision already cost a rebuild

Three agents independently proved `IsPath.anti` and `IsWalk.deleteEdges`, and merging their
branches failed with "environment already contains". Both now live in **`Graph/Walk.lean`**,
alongside:

  `IsWalk.mono`, `IsWalk.anti`, `IsPath.mono`, `IsPath.anti`,
  `coveredVertices_mono_of_le`, `walkVertices_mono_of_le`,
  `mem_edgeSet_deleteEdges_iff`, `IsWalk.deleteEdges`

**Before you state any general-purpose lemma about walks, paths, subgraph inclusions or edge
deletion, grep `Schoenflies/Graph/Walk.lean` and `Schoenflies/Graph/Cycle.lean` for it.** If
what you need is genuinely missing and genuinely general, still put it in YOUR file and say so
prominently in your report — the integrator will hoist it. Do not silently restate an existing
lemma under a new name either; that compiles but leaves two of everything.
