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

## License

[Apache 2.0](LICENSE), matching Mathlib and the rest of the Lean ecosystem. The companion
blueprint is CC BY 4.0.
