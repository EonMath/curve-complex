import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.ActualCechResidue

open scoped Manifold ContDiff Bundle

namespace CanonicalDimensionTwo

/-- The one-point, simple-principal-part instance of McMullen, Theorem 10.5
(printed p. 92). This is a statement awaiting source review, not a proved
producer. The obstruction and the evaluations are the literal same-atlas maps. -/
def ActualPointMittagLefflerDetectionStatement
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E) : Prop := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  exact ∀ (p : E) (c : ℂ),
    (∀ s : ActualCanonicalSection E, c * actualCanonicalEvaluation p s = 0) →
      SameAtlasRRLocal.scalarCechBoundary p c = 0

end CanonicalDimensionTwo
