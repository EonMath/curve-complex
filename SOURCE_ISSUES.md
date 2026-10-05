# Source issues and formalization audit

## Current conclusion

The audit of 5 October 2026 identifies **two concrete local issues** in the
manuscript: a wrong-space invariance qualifier in Lemma 4.1 and an imprecise,
non-finite counting measure in the proof of Lemma 4.6. It also records three
proof clarifications and one explicitly acknowledged citation limitation.
**No finding establishes that any of Theorems 1.1–1.4 is false.** None is a
Lean-certified counterexample to the article.

The entries below distinguish findings from this fresh rereading from problems
encountered while developing Lean interfaces. A rejected formalization lemma
is not, by itself, evidence of an error in the paper. Historical progress
reports that said the proof was incomplete describe earlier work, not the
status of the delivered repository.

## Source, scope and evidence

Audited source: *The Complex of Curves Pairwise Intersecting at Most Once Is
Contractible in Genus Two*, Apex Intelligence, **11 September 2026**, 35 pages.

- PDF: `curve-complex-genus-two.pdf`, SHA-256
  `d1eadd01f94e9af17ee9f5fb2ee1b05b326430f37296309fd9417340ea366fd4`.
- Supplied text extraction: `curve-complex-genus-two.txt`, SHA-256
  `48d7d7a5112a7ce38355152b5f8eb0e518fa745666fd2dfd5a06eaef33b75bc4`.
- Canonical code inspected at revision
  `1a501d208d7867e389218bc6f2e17fc3c1e25842`.

Two focused reviews covered §§1–5 and §§6–11, compared the relevant retained
formalization records, and inspected the linked source declarations. Printed
page numbers agree with PDF page numbers. Pages 8, 10, 11, 14, 18, 21, 22, 23
and 27 were also visually checked. Extraction line numbers below refer only
to the pinned text above.

This is a documentation and source audit, not a fresh proof build or a complete
recheck of every Lean definition and dependency. The linked modules identify
concrete implementation interfaces; they do not imply that every paragraph
of the article has a separate corresponding theorem in this repository.

## Concrete source issues

### CC-01 — Invariance attached to a subset of the wrong space

**Classification:** minor notation/type mismatch. **Location:** Lemma 4.1,
§4.1, p. 11; extraction lines 504–511.

The final clause calls `Z ⊂ S²` an “ι-invariant subset”. Section 2.1 defines
`ι : S₂ → S₂` on the genus-two total space, whereas `Z` here lies in the base
sphere. The named involution does not act on the stated space. The displayed
full-preimage identity needs no invariance assumption on the base subset.

**Correction:** delete the invariance qualifier and take every subset `Z` of
the base sphere. Moving `Z` upstairs would not repair the displayed formula.
This leaves the intended lifting identity and dictionary unchanged.

**Formalization:**
[`lift_preimage`](curve-complex/CurveComplexGenusTwo/Dictionary/LiftPreimage.lean)
takes an arbitrary `(A : Set S)` in the base, assuming the supplied isotopies
commute with the projection. The lift itself is supplied separately by
`marked_isotopy_lift` in
[ArcVertexAPI.lean](curve-complex/CurveComplexGenusTwo/Dictionary/ArcVertexAPI.lean).

### CC-02 — The innermost-bigon paragraph needs a finite measure

**Classification:** proof-measure imprecision requiring an explicit argument.
**Location:** Lemma 4.6, §4.4, p. 14; extraction lines 678–687.

The proof first uses the finite outer measure `|c₁ ∩ c₂|`. Its inner selection
then chooses a bigon whose interior meets the **union of the multicurves** in
“as few points as possible”, and asserts that a smaller bigon strictly reduces
that number. Whenever a curve enters the open interior, this intersection
contains a subarc. It is not the finite set of transverse crossing points
needed for the stated finite descent.

**Correction:** specify the finite subdivided-graph complexity used in the
innermost selection and justify its strict decrease, or supply a separate
innermost-bigon selection lemma. Simply changing the word “union” to
“intersection” without checking the sub-bigon argument is not an established
repair. This identifies a defective literal proof measure, not a counterexample
to descent or to Theorem 1.4.

**Formalization:**
[Main14Circle33FiniteBigonElimination.lean](curve-complex/CurveComplexGenusTwo/Topology/ActualMain14Dictionary/Providers/Main14Circle33FiniteBigonElimination.lean)
uses natural-number strong induction on the finite intersection count and a
strict-drop step. The four-component analogue uses a sum of finite pairwise
counts in
[FourComponentWeightedDrop.lean](curve-complex/CurveComplexGenusTwo/Topology/ActualOriginalCDescent/FourComponentWeightedDrop.lean).
These handle finite outer elimination. The first module branches on whether
an empty bigon exists; it does not alone certify a replacement for the paper's
inner-selection paragraph.

## Proof clarifications

### CC-03 — Establish endpoint distinctness before compactification injectivity

**Classification:** local hypothesis/dependency-order clarification.
**Location:** Lemmas 3.8–3.9, §3.3, p. 8; extraction lines 352–363.

Lemma 3.8 proves convergence of the two lifted ends and immediately describes
the extension from `[-∞,+∞]` as a continuous injection. Distinctness of the
endpoint images is established only in Lemma 3.9, for essential arcs. The
preceding notation paragraph concerns essential arcs, but Lemma 3.8 says an
arc without repeating that restriction; Definition 2.3 also allows inessential
loop arcs.

**Clarification:** first state endpoint convergence, then prove distinctness
under essentiality, and only then infer the embedded interval compactification.
Alternatively make essentiality explicit and defer the final assertion to
Lemma 3.9. This records a proof-order and scope issue, not a certified false
statement under the intended essential-arc context.

### CC-04 — Prove projected simplicity before invoking embedded-arc isotopy

**Classification:** omitted ordering of prerequisites.
**Location:** Proposition 3.12, §3.3, pp. 9–10; extraction lines 420–450.

Part (i) invokes Epstein's theorem for embedded arcs before the injectivity of
the projected geodesic is proved in part (iii). The latter uses deck translates
and linked ideal endpoints, and does not use the isotopy conclusion of (i).

**Clarification:** prove simplicity first, verify the appropriate marked-arc
compactification and proper cusp-end homotopy, and then apply the embedded-arc
isotopy result. The early formalization audit already flagged this dependency;
the present rereading confirms the ordering issue. It does not establish that
the cited isotopy theorem is inapplicable once its hypotheses are supplied.

**Implementation boundary for CC-03 and CC-04:** this audit did not locate a
direct final module for these exact cusped lemmas. Historical conditional
statement reviews are not certificates that the current repository formalizes
or repairs these particular paragraphs. No new theorem hypothesis or change
to the main statements is proposed here.

### CC-05 — Specify the realization in the Farey contractibility argument

**Classification:** topology/proof-exposition clarification.
**Location:** Lemma 6.6, §6.2, p. 22; extraction lines 1012–1015.

The proof explains contractibility of the filled Farey complex through the
ideal tessellation of the hyperbolic plane. Ideal vertices lie at infinity;
the ordinary weak simplicial realization includes its slope vertices as
actual points. The sentence does not identify these topological objects or
itself supply a contraction of the latter, which the subsequent CW argument
requires.

**Clarification:** assert contractibility of the weak geometric realization
explicitly, with a precise reference or a finite-stage contraction and its
continuity argument. Do not encode the sentence as a literal homeomorphism
with the hyperbolic plane. This does not refute Lemma 6.6.

**Formalization:** `fareyRealization_contractible` in
[FareyCompletedContraction.lean](curve-complex/CurveComplexGenusTwo/Topology/FareyCompletedContraction.lean)
concerns `ContractibleSpace (RealizationPoint fareyComplex)` and uses a
continuous scheduled contraction. The result is consumed by
[FareyDictionaryStarDeletionConsumer.lean](curve-complex/CurveComplexGenusTwo/Topology/FareyDictionaryStarDeletionConsumer.lean).

## Acknowledged external-input limitation

### CC-06 — The supplementary arc-and-curve variant needs its own provenance

**Classification:** limitation already acknowledged by the manuscript.
**Location:** Fact 7.3 and Remark 7.4, p. 23, lines 1075–1081; supplementary
Proposition 7.8, p. 24, lines 1115–1140.

Remark 7.4 explicitly says that Hatcher's printed result concerns the arc
complex, while Fact 7.3 concerns the arc-and-curve complex. It attributes the
variant through Souto and the same surgery argument. A formalization cannot
identify the two statements merely by citing the arc-only theorem.

**Disposition:** retain the distinction and supply a proof of the variant or
an exact separate reference if this supplementary route is to be self-contained.
This audit has not independently rechecked the external publications. The
finding records the source's own caveat, not a newly discovered false theorem.

**Impact:** the paper explicitly confines this input to Proposition 7.8 and
excludes it from the main Theorem 7.7 and later contractibility argument. The
canonical [SourceTopologyMainBound.lean](curve-complex/Theorems/SourceTopologyMainBound.lean)
uses the Harer binding and intersection-one edge replacement for simple
connectivity, consistent with that distinction.

## Formalization findings that are not source errata

The historical audit records are useful evidence of implementation hazards,
but their rejection labels must not be transferred to the paper:

| Historical finding | Why it is not an original-paper error |
| --- | --- |
| A generic CW mapping-property helper lacked separation/final-topology assumptions. | Theorem 6.8, p. 22, explicitly uses the weak topology of the actual realization and its product with a locally compact interval. The recorded counterexample targeted the overgeneralized helper. |
| A free-gap helper omitted object coverage. | Section 9, pp. 27–28, fixes a bad stratum with `bv(S)=S` and states that every arc belongs to an object. Those standing hypotheses support Lemma 9.11. |
| A filtration interface lost augmentation or used the wrong quadrant. | Section 8 and Theorem 8.9, pp. 25–27, explicitly retain degree `−1` and say that the spectral sequence is not first quadrant. |
| Fixed-atlas, area-normalization, multiplication-order, compactness-instance and canonical-map issues appeared in Lean adapters. | These concern translating the source into library definitions or preserving its hypotheses and maps; surviving records do not establish corresponding source contradictions. |
| Overgeneralized minimum-family, boundary-mark and regional-geometry helpers were rejected. | A stronger auxiliary request is not the source statement. Several exact temporary reports are no longer available for independent inspection. |

The present review found no additional source defect in the finite-gap descent
and six-mark budget of §§9–10. The early audit's requests to expose these
arguments were proof obligations, not counterexamples.

## Audit limits

The retained history was checked alongside the source rather than treated as
an errata list. Eleven original temporary reports cited by that history were
removed during disk cleanup; their surviving summaries are historical context
only. No deleted certificate was reconstructed or rerun for this document.
Existing build verification is described separately in [README.md](README.md).
