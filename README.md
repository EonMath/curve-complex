> **Repository location update:** The maintained copy is now at [https://github.com/rational-intelligence/curve-complex](https://github.com/rational-intelligence/curve-complex). This original `EonMath/curve-complex` repository is preserved.

# Curve complex formalization

A Lean 4 formalization of the complex of essential curves that pairwise
intersect at most once, with contractibility in genus two as its main result.
The development follows *The Complex of Curves Pairwise Intersecting at Most
Once Is Contractible in Genus Two* (Apex Intelligence, 11 September 2026),
including the four numbered results in Section 1.2.

Start with [MainTheorems.lean](MainTheorems.lean): one public entry module imports
all four original theorem declarations and their necessary proof dependencies.

## The mathematical object

For a closed surface S, C₁(S) is the flag simplicial complex whose vertices are
ambient-isotopy classes of essential simple closed curves. A finite collection
of distinct vertices spans a simplex when every pair has geometric intersection
number at most one. The topological conclusions below concern its geometric
realization with the weak topology.

The more general `curveComplex S d` uses intersection bound `d`; thus C₀(S)
is the disjointness complex and C₁(S) allows one intersection. See
[SourceRealization.lean](curve-complex/CurveComplexGenusTwo/Foundations/SourceRealization.lean)
for the complex and its realization.

## Main results

The first three declarations live in `CurveComplexGenusTwo.SourceTopology`.
They take a surface `S` with a topology and a two-dimensional real charted-space
structure, together with the explicit `IsGenus S g` hypothesis. This predicate
records nonemptiness, a closed-surface structure, and the integral homology
conditions defining the genus; see
[Genus.lean](curve-complex/CurveComplexGenusTwo/Dictionary/Genus.lean).

| Article | Result | Lean declaration and proof source |
| --- | --- | --- |
| 1.1 | C₁(S) is contractible when S has genus two. | [`c1_contractible_genusTwo`](curve-complex/Theorems/MainTheorem11ProofOriginal12Consumer.lean) |
| 1.2 | C₁(S) is integrally acyclic in genus two: positive-degree homology vanishes and the degree-zero augmentation is an isomorphism. | [`c1_acyclic_genusTwo`](curve-complex/CurveComplexGenusTwo/Topology/ActualOriginalArticle/Main12OriginalCanonicalImportsHaasConditionalV15.lean) |
| 1.3 | C₁(S) is simply connected for every genus g ≥ 2. | [`c1_simplyConnected_allGenus`](curve-complex/Theorems/SourceTopologyMainBound.lean) |
| 1.4 | A supplied genus-two hyperelliptic model gives the unique full-preimage arc/circle dictionary for essential curve classes. | [`headline_hyperelliptic_dictionary`](curve-complex/CurveComplexGenusTwo/Topology/ActualOriginalArticle/MainTheorem14OriginalComplete86.lean) |

The fourth declaration is
`CurveComplex.HyperellipticModel.headline_hyperelliptic_dictionary`.
For a supplied `HyperellipticModel E S`, it identifies the disjoint union of
marked non-loop arc classes and 3|3 circle classes on the quotient surface
with all essential curve vertices on E. The correspondence is induced by
literal full preimages: arcs give curves with connected complement, while
3|3 circles give curves with disconnected complement. Its conclusion is a
unique equivalence of these classes, with the stated complement properties.

## Mathematical foundations

The supporting development connects concrete surface geometry to the topology
of the curve complex:

- **Surfaces and curves:** surface classification, Jordan curves, Schoenflies,
  essential curves, ambient isotopy, and geometric intersection numbers.
- **Geometric constructions:** proper arcs, simultaneous position, local disk
  and band arguments, covering spaces, and hyperbolic surface geometry.
- **Topology and algebraic topology:** simplicial realizations, CW structures,
  path homotopies, singular homology, and Hurewicz/Whitehead arguments.
- **Hyperelliptic geometry:** the supplied branched-cover model and the
  full-preimage correspondence between quotient arcs/circles and curves.

The genus-two contractibility proof combines the simple-connectivity and
integral-acyclicity results through the development's CW machinery. Its short
final assembly can be read directly in the linked Theorem 1.1 source.

## Source layout

[MainTheorems.lean](MainTheorems.lean) is the public entry point. The supporting
sources are grouped under [curve-complex/](curve-complex/):

| Directory | Contents |
| --- | --- |
| [`CurveComplexGenusTwo/`](curve-complex/CurveComplexGenusTwo/) | Curve-complex foundations, dictionary, topology, and CW/homotopy machinery. |
| [`ClassificationOfSurfaces/`](curve-complex/ClassificationOfSurfaces/) | Surface-classification infrastructure. |
| [`CurveTopology/`](curve-complex/CurveTopology/) | Curve and arc complexes, carriers, and finite geometric constructions. |
| [`CoveringSpaces/`](curve-complex/CoveringSpaces/) | Covering-space and branch-chart constructions. |
| [`HyperbolicGeometry/`](curve-complex/HyperbolicGeometry/) | Hyperbolic charts and geometric bridges. |
| [`SurfaceGeometry/`](curve-complex/SurfaceGeometry/) | Local surface geometry, arc alignment, and disk/band arguments. |
| [`Theorems/`](curve-complex/Theorems/) | Main contractibility and simple-connectivity proof assemblies. |
| [`vendor/schoenflies-lean/`](curve-complex/vendor/schoenflies-lean/) | Local Schoenflies dependency. |

## Build and verification status

Install Lean through elan, then run from the repository root:

```sh
lake update
lake exe cache get
lake build
```

The toolchain is pinned to **Lean 4.35.0-rc3** in
[lean-toolchain](lean-toolchain), and Mathlib to revision
`3f6737de4761ec7bf368491fe9faccc991ebd6ca` in
[lakefile.toml](lakefile.toml). The default Lake target is `MainTheorems`;
Schoenflies is resolved as a local source dependency.

The proof-source closure has compiled from source with the pinned Lean and
Mathlib versions. Matching third-party caches were used for Mathlib; all
project and vendored proof modules were freshly compiled. Ordinary `lake build`
passes in the delivered checkout. The Lean sources contain no `sorry` or
`admit`. The four original theorem statements are unchanged, and each theorem's
axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`.

The cleanup removes unused theorems and shortens two proofs. Its source-delta
audit compiles the original edited modules against the same fresh dependency
objects and compares their complete owned declarations with the delivered
versions. Source-authored theorem types, source-authored computational
definitions, and axiom sets are preserved; the report explicitly accounts for
the intended proof rewrites and binder labels in the listed compiler-generated
helpers. Source, compiled-reference, and applicable registration checks find no
outside consumers of the removed names or changed internal helpers.

The historical accepted-object comparison remains a separate provenance check
and reports strict mismatches. The four headline contracts still match that
reference. Source-delta validation does not claim a complete historical rebuild
or literal identity of every historical proof object. See
[tools/README.md](tools/README.md) for the reusable comparison tool and its
scope.

The full fresh source-build phase took about three hours in the recorded run;
the largest geometry module took about 83 minutes. Cold builds include these
expensive proofs.

## Source audit

The source audit of **5 October 2026** records two local manuscript issues:
Lemma 4.1 attaches an invariance qualifier to a subset of the wrong space, and
Lemma 4.6 uses a literal bigon-counting measure that need not be finite. It also
records three proof clarifications and one supplementary citation limitation
already acknowledged by the manuscript.

[SOURCE_ISSUES.md](SOURCE_ISSUES.md) gives source locations, suggested corrections,
and relevant formalization interfaces, while distinguishing manuscript findings
from historical Lean implementation defects. No finding establishes that any of
Theorems 1.1–1.4 is false.

## References and attribution

The mathematical source is *The Complex of Curves Pairwise Intersecting at Most
Once Is Contractible in Genus Two* (Apex Intelligence, 11 September 2026),
Section 1.2 for the four main results. Lean and Mathlib provide the underlying
proof language and library. See [THIRD_PARTY.md](THIRD_PARTY.md) for the vendored
Schoenflies revision, license, and dependency attribution.

To cite this formalization, refer to *Curve complex formalization*, specifying
the revision used: [EonMath/curve-complex](https://github.com/EonMath/curve-complex/).
