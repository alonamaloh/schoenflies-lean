# The Jordan–Schönflies theorem in Lean

A Lean 4 / Mathlib formalization of the Jordan–Schönflies theorem: every homeomorphism
between two Jordan curves in the plane extends to a homeomorphism of the plane. The
Jordan curve theorem is not assumed — it is proved along the way.

The prose blueprint this follows, written at formalization granularity with a
statement-level citation index and a suggested module order, is at
<https://github.com/alonamaloh/jordan-schoenflies>. Statement numbers below refer to
`jordan_schoenflies.tex` there.

Lean 4.32.2, Mathlib v4.32.2. `lake build`.

## Status

**Part I is complete.** The Jordan curve theorem and the general crosscut theorem are proved,
with nothing assumed:

| | |
|---|---|
| `Schoenflies.arc_complement` | `thm:arc-complement` — the complement of a simple arc is connected |
| `Schoenflies.jordan_curve_theorem` | `thm:jordan` — a Jordan curve separates the plane into exactly two regions, each with the curve as its boundary |
| `Schoenflies.crosscut_theorem` | `thm:general-crosscut` — a polygonal crosscut cuts a Jordan domain into exactly two, with named sides |

all in `Schoenflies/JordanClosed.lean`, and all on `propext`, `Classical.choice` and
`Quot.sound` alone. `thm:jordan` is stated as `IsSeparating C` — the *same* predicate the
polygonal case is stated through — so `inside`, `outside` and the whole region API apply to a
general Jordan curve with nothing to transport, and every consumer written against
`ClosedPolygon.polygonal_jordan` applies verbatim.

**Part II — the Schönflies extension — is in progress.** The abstract scaffolding was built
first, because `lem:combinatorial-invariance` has no internal prerequisites and could be proved
while the Jordan curve theorem was still open. The critical path is now assertions (i) and (vii)
of `lem:cellulation-invariants`, then `thm:finite-transfer`.

`docs/ROADMAP.md` has every one of the blueprint's 84 labelled statements with its status and
its Lean home. Work is scheduled off Appendix A of the blueprint — its machine-generated
citation index — rather than off the milestone list, because the index repeatedly reveals
substantial statements with no internal prerequisites that can be built in parallel far ahead
of the critical path.

### Milestones

| | |
|---|---|
| H6 polygonal redrawing | done |
| H7 the polygonal Jordan curve theorem | done |
| H8 nonplanarity of `K₃,₃` | done |
| H9 the outer-chain lemma | done |
| the Jordan curve theorem | **done** |
| H10 the general crosscut theorem | **done** |
| H11 Jordan–Schönflies | in progress |

### Two gates, and why the build is not enough

```sh
python3 docs/regen-inventory.py   # rewrites docs/INVENTORY.md; exits 1 on a duplicate name
python3 docs/audit-axioms.py      # #print axioms on every declaration; exits 1 on any other axiom
```

Neither is redundant. Lean's import checker accepts two modules declaring the same name when
the statements are alpha-equivalent `Prop`s, because proof irrelevance makes them defeq — so a
clean build is not a collision check. And a `sorry` reached through a chain of definitions shows
up as `sorryAx` in the axiom audit and nowhere else. Both run in about two seconds.

### Layer 0 — the plane

| Blueprint | Lean |
|---|---|
| Appendix C.1 orientation form, right-angle rotation | `Plane.det`, `Plane.perp`, `det_perp_self`, `perp_perp`, `norm_perp`, `det_perp_left/right`, `det_eq_zero_iff_smul` |
| Appendix C.1 sup metric and the comparison | `Plane.supNorm`, `supDist`, `supNorm_le_norm`, `norm_le_sqrt_two_mul_supNorm` |
| Appendix C.1 directions, angle-free | `Plane.IsDirection`, `arcCCW`, `same_arc_of_det_neg_of_det_pos`, `exists_isDirection_det_ne_zero`, the `det_germ*` family |
| Appendix C.1 lines | `Plane.exists_segment_eq_of_isCompact_isConnected`, `exists_openSegment_eq_connectedComponentIn` (endpoints in `frontier U`), `affineMap_ext_of_affineIndependent` |
| Lemma 1.3 nearest-point segment | `Plane.notMem_of_mem_segment_of_isMinOn` |
| Lemma 1.4(a)–(c) compact separation | `Plane.exists_thickening_subset`, `exists_dist_pos`, `exists_ball_subset_diff` |
| Lemma 1.6 nested compact singleton | `Plane.eq_singleton_iInter_of_diam_tendsto_zero` |
| Lemma 1.7 recognizing a component | `Plane.connectedComponentIn_eq_of_frontier_disjoint` |
| Lemma 3.7 how two segments meet | `segment_inter_segment` |
| cutting a segment | `segment_split`, `openSegment_left_subset`, `openSegment_right_subset` |
| the distance from an end as a coordinate | `parameter_le_of_distance`, `segment_inside_of_ends_outside`, `same_ends_of_meeting_interiors` |
| §1 polygonal paths | `poly`, `isCompact_poly`, `isConnected_poly`, `IsPolygonal`, `isArcBetween_segment` |
| Lemma 1.1 polygonal connectedness (existence half) | `exists_poly_of_isPreconnected` |
| the outside of a square is connected | `Plane.isConnected_beyondSquare`, `beyondSquare_eq_compl` |

### Layers 1–3 — the gaps Mathlib leaves

| Blueprint | Lean |
|---|---|
| Appendix C.4 components of open sets are open | `Plane.isOpen_connectedComponentIn` |
| Appendix C.5 boundary of a component of a closed set's complement | `Plane.frontier_connectedComponentIn_compl_subset` |
| Appendix C.6 pasting lemma | `Plane.continuousOn_union_of_isClosed` |

### Layer 4 — arcs and Jordan curves

| Blueprint | Lean |
|---|---|
| §1 simple arc, Jordan curve | `IsArc`, `IsArcBetween`, `IsLoop`, `IsJordanCurve` |
| subarcs, open arcs, the topology of an arc | `isArc_subarc`, `subarc_image`, `openArc`, `image_isRelOpen`, `basic_piece_inside_ball` |
| gluing arcs | `IsArcBetween.concatenate`, `IsLoop.concatenate`, `IsJordanCurve.of_two_arcs` |
| two points cut a curve into two arcs | `IsJordanCurve.two_arcs`, `IsLoop.two_arcs_at_parameters`, `two_arcs_of_two_arcs` |

### Layer 5 — finite graphs

Built on Mathlib's multigraph `Graph α β` (`Mathlib/Combinatorics/Graph/`), which supplies the
type, subgraphs, deletion and the lattice — and no walk, path, connectivity or degree theory
at all.

| Blueprint | Lean |
|---|---|
| walks, paths, reachability, connectedness | `Graph.IsWalk`, `IsPath`, `IsWalk.contains_path`, `Reaches`, `Connected` |
| degree and the handshake lemma | `Graph.degree`, `sum_degree_eq_two_mul_ncard_edgeSet`, `IsLeaf` |
| cycles, acyclicity, bridges | `Graph.LiesOnCycle`, `IsAcyclic`, `IsBridge`, `liesOnCycle_iff_deleteEdges_reaches` |
| 2-connectivity | `Graph.IsTwoConnected`, `no_cut_vertex`, `no_bridge`, `IsTwoConnected.union` |
| a path presented as a graph | `Graph.IsPathGraph`, `pathGraphOf`, `IsPathGraph.reaches_an_end` |
| Lemma 3.4 trees with three leaves | `Graph.IsTree`, `has_leaf`, `delete_leaf`, `edge_count`, `IsTree.three_leaves` |
| Lemma 3.6 subdivisions and ears preserve 2-connectivity | `Graph.IsTwoConnected.ear`, `replace_edge_by_path`, `Reaches.reroute` |
| Lemma 3.5 ear decomposition | `Graph.IsTwoConnected.grows_by_ear`, `ear_exists` |
| components and shortest paths | `Graph.component`, `induce_component_connected`, `exists_minLength_isPath` |

### Blueprint content

| Blueprint | Lean |
|---|---|
| Lemma 3.5 relative ear decomposition | `Graph.IsTwoConnected.relative_ear_exists`, `relative_grows_by_ear`, `ear_decomposition` |
| Def 6.1 strong accessibility, Lemma 6.2–6.4 | `Accessible.lean` — nearest points are strongly accessible, the tangent-disk cone, a countable dense strong-access set |
| Def 2.4 separating curve, Lemma 2.5 absorption, Lemma 2.6 crosscut cells | `CrosscutCells.lean` — `IsSeparating`, `inside`/`outside`, `IsRegionPair`, `absorption`, `crosscut_cells` |
| Lemma 4.1 model-curve parametrization | `ModelCurve.lean` — the square boundary as a Jordan curve, its four sides, and the homeomorphism criterion |
| Lemma 7.2 combinatorial invariance | `CombinatorialInvariance.lean` — `CellStructure`, `Realization`, `SkeletonHomeo`, `combinatorial_invariance` |

The model curve is the **square** boundary, not the circle: the circle would need a traversal
of it by an interval, which is exactly what a trigonometry-free development withholds. The
four sides are segments, each an arc by `isArcBetween_segment`, glued by
`IsArcBetween.concatenate` and `IsJordanCurve.of_two_arcs`.

### Layer 6 — plane graphs

| Blueprint | Lean |
|---|---|
| a plane graph | `Graph.IsDrawing` (abstract graph **plus** drawing), `edgeArc` |
| distinct edges meet only at shared vertices | `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` |
| point set, exterior, faces | `Graph.pointSet`, `exterior`, `face`, `face_eq_or_disjoint` |
| the outer face | `Graph.exists_unbounded_face`, `unbounded_face_unique`, `beyondSquare_subset_face` |
| subdividing a segment list | `Piece`, `cover`, `subdivide`, `subdivide_cover` / `_ne` / `_interior_subset` / `_avoids` |
| the realisation of a cycle is a Jordan curve | `Graph.IsDrawing.cycle_isJordanCurve`, `path_isArcBetween` |
| **Lemma 3.7 polygonal overlay** | `polygonal_overlay`, `overlayGraph`, `orientPiece`, `subdivide_separated`, `exists_cut_points` |
| "choose ε small enough for all of them" | `exists_pos_le_of_finite`, `exists_pos_forall_of_finite` |

**Verification.** `docs/audit-axioms.py` runs `#print axioms` over every declaration in the
development on every check — over three thousand of them. All depend only on `propext`,
`Classical.choice` and `Quot.sound`; `sorryAx` appears nowhere, and a repository-wide sweep
finds no `sorry`, `admit` or `native_decide`.

## Relation to the `math` foundation

The same blueprint has a foundation built in a separate, self-contained proof system,
whose Layers 0–6 cover the plane's geometry, arcs and Jordan curves, finite graphs, and
plane graphs with the polygonal overlay and the outer face. This development has since carried
the blueprint's own content, from the two-sided strip lemma through the Jordan curve theorem,
well past where that foundation stops.

Design decisions settled there and adopted here:

* **Orientation, not angles.** `det(u, v) = u₁v₂ − u₂v₁` and its sign, with
  `det(u, u^⊥) = ⟨u, u⟩` as the identity the strip lemma runs on. No trigonometry enters.
* **A polygonal path is its vertex list**, not a union of segments from which vertices are
  existentially recovered. `poly` is the carrier.
* **A plane graph is an abstract graph *plus* a drawing, unbundled**, with plane points as
  vertices, so every combinatorial theorem applies with no projection to go through.
* **A polygonal edge *is* its pair of endpoints**, so deduplicating geometric subsegments
  is deduplicating a list of names, with no geometry in it.
* **Two segments meet in nothing or in a segment** — a dichotomy, since a point is a
  degenerate segment — proved from compactness and convexity, with no parallel/non-parallel
  split and no determinant.

Two decisions deliberately not carried over:

1. **No `Point` / `Vector` split.** There, two sealed types make `p + q` unwritable, and
   the blueprint's affine idiom (`a + (x − a)/‖x − a‖²`) is typed exactly. Here the plane
   is a single normed space, because `segment`, `Convex`, `Metric.ball` and `dist` are all
   stated on it, and an affine/linear split would forfeit that API for a discipline the
   type checker is not being asked to enforce.
2. **Compactness and connectedness are Mathlib's**, in their open-cover and separation
   forms, rather than sequential compactness and the clopen criterion taken as definitions.
   The clopen criterion is a two-line consequence where it is wanted — see
   `connectedComponentIn_eq_of_frontier_disjoint` and `exists_poly_of_isPreconnected`.

## Findings

Places where formalizing found the blueprint, or the companion development, over-assuming,
under-assuming, or doing more work than needed. None is an error in the mathematics.

1. **The meet of two segments needs no degenerate case.** The companion splits on `a = b`
   first, so that an equation-shaped case never has to reconcile two spellings of the same
   segment. Parametrizing by `AffineMap.lineMap a b` and pulling the meet back removes the
   split: the preimage carries the meet forward whether or not the parametrization is
   injective. `segment_inter_segment` has no case analysis at all.

2. **`splitAt_avoids` needs nondegeneracy, and the companion's four properties of `subdivide`
   do not record it.** A degenerate piece `(p, p)` has `p` in its interior, and cutting it
   produces two more copies of itself, so "after cutting at `p`, no piece has `p` in its
   interior" is false without `Nondeg`. The hypothesis is free in context — `subdivide_ne`
   supplies it — but it belongs in the statement.

3. **The handshake lemma holds with loops.** The companion proves it only for loopless
   well-formed graphs. Mathlib's `IsLoopAt` / `IsNonloopAt` split makes the general statement
   clean, and `sum_degree_eq_two_mul_ncard_edgeSet` carries no side condition.

4. **No looplessness hypothesis propagates through the path theory.** `Graph.IsPath` excludes
   loops by its own freshness clause — a step from `u` requires `u` to be absent from what the
   rest visits, and the arrival is always present — so `IsPath.not_isLoopAt` needs nothing of
   the graph. The companion excludes loops in `IsWellFormed` and then carries that hypothesis
   through several files.

5. **"An edge determines where taking it arrives" needs no distinctness.** Mathlib's
   `eq_or_eq_of_isLink_of_isLink` is strong enough that a loop also determines its arrival
   (back where it started), so `IsWalk.target_unique` has no side condition. The companion's
   `Graph.Joins.unique` assumes distinct ends.

6. **`IsTwoConnected.ear_exists` needs a looplessness hypothesis that is *not* removable.** A
   2-connected graph plus a loop is 2-connected, so a 2-connected subgraph missing only that
   loop grows by no ear and the conclusion — a path between *distinct* vertices — is false. A
   plane consumer discharges it from `IsDrawing.ne_of_isLink`.

7. **`Reaches.reroute`'s premise has to be universally quantified.** The companion asserts
   that the replaced edge joins its two ends in the vertex-deleted graph, which does not
   follow — the ends may themselves have been deleted. Quantifying over what the edge joins
   makes that case vacuous instead of false.

8. **The blueprint's "internal vertices are new" is unnecessary for half (b) of
   `lem:subdivision-ear-preserve`.** The companion found this and it reproduces in Lean with
   nothing extra: what the proof turns on is `IsPathGraph.reaches_an_end`. Half (a) does need
   it, and the two statements differ accordingly.

9. **`IsTree.three_leaves` should assert uniqueness.** The companion gives only existence of a
   degree-3 vertex; the blueprint's `lem:three-leaf-tree` also wants that every other vertex
   has degree at most two, and the ear decomposition cites it. It costs nothing extra in the
   handshake count.

10. **The outside of a square is connected for every radius.** No sign condition is needed: for
    `r < 0` the four half-planes already cover the plane.

11. **The polygonal overlay must carry finiteness in its conclusion.** Stated as
    `∃ G, IsDrawing G _ ∧ pointSet G _ = cover pieces`, the graph is hidden behind a binder and
    no `[G.Finite]` instance can be recovered — so the overlay could not be handed to the face
    machinery at all, though both halves compiled in isolation. `Schoenflies/Compose.lean`
    exists to catch exactly this class of drift.

12. **H6's brick B2 is too weak as designed.** "For each vertex, a radius whose square meets
    no other vertex and no non-incident edge arc" does not make distinct vertex squares
    disjoint — a square about `v` avoiding `w` says nothing about the square about `w` reaching
    towards `v` — so brick B4's "the core meets no other vertex square" fails. The fix costs
    nothing but must be made at B2: choose one radius for all vertices by B1, then **halve it**.
    Two squares of radius `r` that met would put their centres within `2r` in the sup metric,
    which the unhalved choice already forbids. `IsDrawing.exists_vertexSquares` is stated that
    way, and it is why `Square.lean` needed a triangle inequality for `supDist`.

13. **H6's brick B4 needs "first entry *after* the last exit", not "first entry".** Nothing
    forbids an edge arc dipping into the far vertex's square, returning to the near one, and
    only then running to its endpoint; with the global first entry the two parameters come out
    in the wrong order and the core is empty or reversed. This is why brick B3 is stated over
    an arbitrary `Icc α β` rather than over `[0, 1]` — the second application lives on `[a, 1]`.

14. **A drawing must name its parametrization.** `IsDrawing` originally asserted only that the
    *point set* of an edge is an arc between its ends. That makes two drawings with the same
    point sets indistinguishable — fine for the face theory, and useless for the redrawing,
    where "the last parameter at which this edge is inside the square at `v`" has to mean
    something. The field is now `edge_param`, and it must be stated orientation-free
    (`G.IsLink e (drawing e 0) (drawing e 1)`) because `IsLink` is symmetric: pinning
    `drawing e 0` to a named end of a given link would force the two ends to coincide.

15. **A plane graph has no loops, and H6 is therefore vacuous on them rather than incomplete.**
    `IsArcBetween A x x` would need an injective parametrization with `f 0 = f 1`, so
    `IsDrawing.ne_of_isLink` rules loops out. The design never says what a loop's core is; it
    does not have to.

16. **"Locally polygonally connected", stated the obvious way, is vacuous.** Both first
    attempts at the property — "every point has a neighbourhood `U` such that any two points of
    `U ∩ S` are joined by a polygonal path **in `S`**" — are satisfied by taking `U = univ`
    whenever `S` is polygonally connected at all. So they carry no local information. That is
    harmless for brick B6, whose clopen argument only needs *some* path, and fatal for B7,
    which needs the property to survive intersecting with an open set. The comb space
    (`{0}×[0,1] ∪ ⋃ₙ {1/n}×[0,1] ∪ [0,1]×{0}`) is polygonally connected, hence "locally"
    so everywhere under the weak reading, while its intersection with a thin strip about
    `y = 1` is not locally polygonally connected at `(0,1)`.

    Repairing it needs **two** changes, not one: the path must lie in `U ∩ S`, *and* `U` must
    range over a neighbourhood basis at `p`. The first alone still leaves you stuck with one
    fixed `U` that sticks out of the open set you are intersecting with. Brick B5's proof
    supports both without alteration — its paths already run through convex pieces of a small
    square about `p`, and the radius is downward-closed — so the strengthening was free, and the
    finitely-many-squares case got *shorter*, since it can now be derived from the one-square
    case rather than rerunning the star argument.

17. **Existential packaging repeatedly loses what the consumer needs.** This happened four
    times, always the same way: a theorem bundles its conclusion into `∃ x, P x`, the bundle
    typechecks, and the consumer then cannot get at something it needs about `x`.

    * `polygonal_overlay` hid the graph, so no `[G.Finite]` instance could be recovered and the
      face machinery was inapplicable.
    * `polygonal_collar` omitted `IsOpen N` and `carrier ⊆ N`, so it never asserted that `N` was
      a *neighbourhood* — which is exactly what the Jordan argument needs.
    * Even after that fix, `polygonal_collar` is still unusable by its main consumer: it hides
      the `StripData` behind an existential, and the "at least two regions" half of the
      polygonal Jordan curve theorem needs `StripData.local_two_sided`, which the packaged form
      does not expose. `PolygonalJordan.lean` therefore consumes `exists_stripData` and the
      unbundled facts directly, and `polygonal_collar` survives only as a statement of record.
    * Brick B5's `IsLocallyPolyConn` bundled the neighbourhood existentially without letting it
      shrink, which is finding 16.

    The lesson is not "avoid existentials" but: **when a theorem is the interface to a
    construction, export the construction, not a bundle**. `exists_stripData` returning a
    `StripData` — from which every consumer takes what it needs — is the shape that works;
    `polygonal_collar` returning a tuple of the properties one imagined a consumer wanting is
    the shape that keeps failing. A composition check (`Compose.lean`) catches the first three
    kinds of failure but not the fourth, because the bundle does compose — it just composes
    into something too weak.

18. **A presentation stronger than the notion its theorems are about.** The blueprint defines
    "polygonal" set-theoretically — *a finite union of line segments* — so a simple closed
    polygonal curve is exactly `IsJordanCurve C ∧ IsPolygonal C`, with no condition on vertices.
    This development works with `ClosedPolygon m`, a cyclic vertex list carrying `corner`
    (no three consecutive vertices collinear). The strip lemma genuinely needs `corner`, since
    its germ argument needs a nonzero determinant at each vertex — but nothing said that every
    set-level polygonal Jordan curve *admits* such a presentation, and without that the
    `ClosedPolygon` theorems say nothing about the objects the blueprint quantifies over.

    It bites where the crosscut theorem splices. At a join vertex the crosscut may leave along
    the ray directly opposite the arriving arc edge — perfectly compatible with the crosscut
    meeting the curve only at its two endpoints — so three consecutive points are collinear and
    the spliced curve is a genuine simple closed polygonal curve that is *not* a
    `ClosedPolygon`. Deleting the redundant vertex is the blueprint's own opening move in the
    strip lemma; the structure bakes it in as an invariant rather than offering it as an
    operation, and so cannot be closed under the splice its consumers perform.

    **The blueprint is not at fault.** Its statements are about the set-level notion throughout,
    and `thm:polygonal-crosscut`'s "all three curves are separating" is correct because `A_i ∪ P`
    is a Jordan curve and a finite union of segments. The divergence is entirely ours, and the
    repair is a realization theorem: every set-level simple closed polygonal curve admits a
    `ClosedPolygon` presentation, via a normalization that deletes redundant collinear vertices.

    Unlike findings 11 and 17 — omissions from a conclusion — this one is a *definition* too
    strong to be closed under the operations its consumers need, which is why it surfaced only
    when three separate consumers reached for it at once.

19. **A hypothesis assumed for a whole wave was false, and the no-`sorry` rule is what caught
    it.** `Graph.CrosscutEncloses` — the geometric half of the descent step of `lem:outer-chain`
    — stood on `main` as a named hypothesis while `lem:outer-chain` was proved from it. It is
    false. Nothing in its hypotheses stopped the crosscut from being drawn *through* the point
    `x`: take the unit square cycle with cut points `(0,0)` and `(1,1)`, let `R` be the two
    straight edges `(0,0) → (1/2,1/2) → (1,1)` through a fresh vertex, and let `x = (2/5,2/5)`.
    Every field of `IsCycleCrosscut` holds and `x` is inside the cycle; but `x` lies *on* both
    spliced curves, and `mem_inside_iff` puts a point of a curve inside neither region.

    The repair was one clause, `x ∈ exterior H drawing`, which the consumer already had from
    `OuterOnPairs` — so `Graph.Descent` came out verbatim and nothing downstream changed. The
    point is the failure mode avoided: had the gap been a `sorry`, it would have been filled in
    eventually and the falsity discovered only then, with everything written in the meantime
    resting on it. Because it was a named hypothesis, the discharger's job was to *prove* it,
    and what came back was a counterexample. The counterexample is recorded in `OuterChain.lean`
    where the false version stood.

20. **A blueprint clause is false as formalized, for a degenerate parameter the blueprint never
    hits.** `prop:anchored-square-mesh` clause 5 asserts the mesh skeleton is 2-connected. For
    `Schoenflies.squareMesh` with an empty fresh-point set it is not even connected — the mesh
    is then concentric ring frames, pairwise disjoint — and with exactly one fresh point its
    single spoke is the only thing joining the rings, so every interior vertex of that spoke is
    a cut vertex. The blueprint's own construction never reaches either case, because it chooses
    enough fresh points to make every boundary arc have diameter `< δ/4`; what is missing on the
    Lean side is that hypothesis on the parameter. Formalized as
    `not_isTwoConnected_squareMesh_of_fresh_nil`.

21. **`_root_.Foo` inside a namespace defeats a naive duplicate scan.** The inventory scanner
    recorded `theorem _root_.Schoenflies.X` written inside `namespace Graph` as
    `Graph._root_.Schoenflies.X`, so it could never collide with the real `Schoenflies.X`. Two
    modules had in fact both declared `IsArcBetween.left_mem_closure_diff`, with identical
    statements and different proofs, in modules that do not import each other — invisible to the
    build for the reason in the first friction below, and invisible to the scanner for this one.
    The same scanner also truncated subscripted names (`carrier₁` and `carrier₂` both became
    `carrier`), which both loses real names and manufactures phantom duplicates.

## Frictions

- **A duplicate theorem can compile.** `supDist_triangle` was proved independently in two
  modules and the build *succeeded*: the two statements are alpha-equivalent `Prop`s, so proof
  irrelevance lets the import checker accept both. Compiling is therefore not a sufficient
  collision check — only a name scan across the source is. (An earlier collision on
  `IsWalk.deleteEdges` did fail loudly, which is what made the silent case surprising.)
- **Parallel formalization collides on unstated general lemmas.** Three independent modules
  proved `IsPath.anti` and `IsWalk.deleteEdges`, and merging them failed with "environment
  already contains". The cause was that `Walk.lean` shipped `IsWalk.anti` without its path and
  deletion companions, leaving an obvious gap that every consumer filled locally. Both now sit
  in `Walk.lean`.
- `WithLp` is a structure in this Mathlib, so points of `EuclideanSpace ℝ (Fin 2)` are not
  functions definitionally: `ext` works and `funext` does not.
- `List.Subset.trans` collides with the deprecated `HasSubset.Subset.trans`, so dot notation on
  a list inclusion fails with "invalid field notation"; the fully qualified name works.
- `induction` on `IsWalk` / `IsPath` auto-reverts every hypothesis mentioning an index, and all
  three of source, edge list and target are indices, so the induction hypothesis silently gains
  them as arguments.

## License

[Apache 2.0](LICENSE), matching Mathlib and the rest of the Lean ecosystem. The companion
blueprint is CC BY 4.0.
