import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualMixedDerivativeSeparationCanonical85
import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.HarmonicConstancyCanonical85

open scoped Manifold ContDiff Bundle

namespace CanonicalDimensionTwo

theorem actualHodgePeriod_injective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Function.Injective (actualHodgePeriod (E := E)) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  exact actualHodgePeriod_injective_of_chartwise_harmonic_constancy
    E hg A hA (fun f hf x y => compact_chartwise_harmonic_eq E f hf x y)

theorem actualCanonicalSection_finrank_le_two
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Module.finrank ℂ (ActualCanonicalSection E) ≤ 2 :=
  actualCanonicalSection_finrank_le_two_of_hodge_injective E hg A hA
    (actualHodgePeriod_injective E hg A hA)

end CanonicalDimensionTwo
