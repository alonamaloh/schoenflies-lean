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

**In progress.** The table records what is formalized; everything not listed is not yet
started.

| Blueprint | Lean |
|---|---|
| Appendix C.1 orientation form, right-angle rotation | `Plane.det`, `Plane.perp`, `Plane.det_perp_self` |
| Lemma 1.3 nearest-point segment | `Plane.notMem_of_mem_segment_of_isMinOn` |
| Lemma 1.4(a)–(c) compact separation | `Plane.exists_thickening_subset`, `Plane.exists_dist_pos`, `Plane.exists_ball_subset_diff` |
| Lemma 1.6 nested compact singleton | `Plane.eq_singleton_iInter_of_diam_tendsto_zero` |
| Lemma 1.7 recognizing a component | `Plane.connectedComponentIn_eq_of_frontier_disjoint` |
| §1 polygonal path carrier | `poly`, `isCompact_poly`, `isConnected_poly`, `poly_concat` |
| Lemma 1.1 polygonal connectedness (existence half) | `exists_poly_of_isPreconnected` |

| Lemma 3.7 how two segments meet | `segment_inter_segment` |

Lemma 1.1's passage from a polygonal path to a *simple* polygonal arc, and Lemma 1.2
(finite polygonal unions), both rest on the same subdivision procedure and a simple path
in the resulting finite graph; they are deferred to the graph module.

## The plane

`EuclideanSpace ℝ (Fin 2)`, so that `‖·‖` is the Euclidean norm the blueprint takes as
primary and `Metric.ball` is a round disk. Coordinates are `x 0` and `x 1`; `Plane.mk`
and Mathlib's `!₂[x, y]` build points.

## Module order

Following Appendix B of the blueprint:

1. metric compactness, segments, polygonal paths, and finite polygonal arrangements;
2. polygonal strips, parity, polygonal Jordan separation, and polygonal crosscuts;
3. finite graph infrastructure, polygonal redrawing, nonplanarity of `K₃,₃`, face cycles,
   and the outer-chain lemma;
4. complements of arcs, accessible boundary points, the general Jordan curve theorem, and
   the general crosscut theorem;
5. generated cellulations, carrier and parent compatibility, stars, and combinatorial
   invariance;
6. finite transfer, local source grids, anchored target meshes, and shrinking matched stars;
7. the shrinking-star limit, boundary continuity, pointed bounded extensions, inversion,
   and ambient pasting.

## What Mathlib supplies

Appendix C of the blueprint lists the imported background. Most of it is in Mathlib
already: the Euclidean plane and its metric, compactness (Heine–Borel, sequential
compactness, uniform continuity), the compact-to-Hausdorff homeomorphism criterion,
connectedness and connected components, frontiers, the pasting lemma, sequential
criteria for continuity, and density of `ℚ²`. Notably `Metric.diam_closure` is Lemma 1.5
verbatim. The plane topology proper — strips, parity, plane graphs, cellulations — is
entirely new.

## Relation to the `math` foundation

The same blueprint has a foundation built in a separate, self-contained proof system,
whose Layers 0–6 cover the plane's geometry, arcs and Jordan curves, finite graphs, and
plane graphs with the polygonal overlay and the outer face. The blueprint's own content
starts above that, at the two-sided strip lemma, and is unbuilt on both sides.

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

1. **The meet of two segments needs no degenerate case.** The other development splits on
   `a = b` first, so that an equation-shaped case never has to reconcile two spellings of
   the same segment. Parametrizing by `AffineMap.lineMap a b` and pulling the meet back
   removes the split: the preimage carries the meet forward whether or not the
   parametrization is injective, so `a = b` is not special. `segment_inter_segment` has no
   case analysis at all.

## License

[Apache 2.0](LICENSE), matching Mathlib and the rest of the Lean ecosystem. The companion
blueprint is CC BY 4.0.
