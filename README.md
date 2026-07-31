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

**In progress.** The foundation (Layers 0–6 of the companion plan) is most of the way in;
the blueprint's own content, from the two-sided strip lemma on, is not started.

| Layer | State |
|---|---|
| 0 — the plane's geometry | complete |
| 1–3 — topology, compactness, connectedness | complete (Mathlib, plus three gap-fillers) |
| 4 — arcs and Jordan curves | complete |
| 5 — finite graphs | walks, paths, degree, cycles, 2-connectivity, path graphs, trees, ears |
| 6 — plane graphs | drawings, faces, outer face, subdivision, cycle realisation, overlay |

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

### Layer 6 — plane graphs

| Blueprint | Lean |
|---|---|
| a plane graph | `Graph.IsDrawing` (abstract graph **plus** drawing), `edgeArc` |
| distinct edges meet only at shared vertices | `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` |
| point set, exterior, faces | `Graph.pointSet`, `exterior`, `face`, `face_eq_or_disjoint` |
| the outer face | `Graph.exists_unbounded_face`, `unbounded_face_unique`, `beyondSquare_subset_face` |
| subdividing a segment list | `Piece`, `cover`, `subdivide`, `subdivide_cover` / `_ne` / `_interior_subset` / `_avoids` |
| the realisation of a cycle is a Jordan curve | `Graph.IsDrawing.cycle_isJordanCurve`, `path_isArcBetween` |

Every theorem checked depends only on `propext`, `Classical.choice` and `Quot.sound`.

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
