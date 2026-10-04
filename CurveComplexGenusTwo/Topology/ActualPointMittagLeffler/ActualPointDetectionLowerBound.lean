import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualPointDetectionCanonicalInterface
import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualPointBoundaryNonzero
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped Manifold ContDiff Bundle
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace CanonicalDimensionTwo

/-- On the actual genus-two surface the missing ML implication is exactly
nonzero canonical evaluation at every point. Both maps are the literal
same-atlas maps; this equivalence does not prove either side. -/
theorem actualPointDetection_iff_evaluation_nonzero
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    ActualPointMittagLefflerDetectionStatement E hg A hA ↔
      (letI : ChartedSpace ℂ E := A
       letI : IsManifold 𝓘(ℂ) ∞ E := hA
       ∀ p : E, actualCanonicalEvaluation p ≠ 0) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  constructor
  · intro hd p hp
    have hz := hd p 1 (by intro s; simp [hp])
    have hone := (actualGenusTwo_scalarCechBoundary_zero_iff E hg A hA p 1).mp hz
    exact one_ne_zero hone
  · intro he
    intro p c hc
    have hex : ∃ s : ActualCanonicalSection E, actualCanonicalEvaluation p s ≠ 0 := by
      by_contra! h
      exact he p (LinearMap.ext h)
    obtain ⟨s, hs⟩ := hex
    have hz : c = 0 := (mul_eq_zero.mp (hc s)).resolve_right hs
    simp [hz]

/-- The remaining detection producer and the separately owned fact that a
nonzero canonical section has a zero produce two actual independent
sections. No dimension assumption is used in this algebraic consumer. -/
theorem actualTwoIndependentSections_of_detection_and_zeros
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E)
    (hDetection : ActualPointMittagLefflerDetectionStatement E hg A hA)
    (hZeros : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      ∀ s : ActualCanonicalSection E, s ≠ 0 → ∃ p : E, s p = 0) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    ∃ s t : ActualCanonicalSection E, LinearIndependent ℂ ![s, t] := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  have he := (actualPointDetection_iff_evaluation_nonzero E hg A hA).mp hDetection
  have hex : ∀ p : E, ∃ s : ActualCanonicalSection E, actualCanonicalEvaluation p s ≠ 0 := by
    intro p
    by_contra! h
    exact he p (LinearMap.ext h)
  obtain ⟨q⟩ := hg.1
  obtain ⟨t, htq⟩ := hex q
  have ht : t ≠ 0 := by intro h; exact htq (by simp [h])
  obtain ⟨p, htp⟩ := hZeros t ht
  obtain ⟨s, hsp⟩ := hex p
  refine ⟨s, t, linearIndependent_fin2.mpr ⟨ht, ?_⟩⟩
  intro c hc
  have hp0 : actualCanonicalEvaluation p t = 0 := by
    simp [actualCanonicalEvaluation, htp]
  have heq := congrArg (actualCanonicalEvaluation p) hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at heq
  rw [map_smul, hp0, smul_zero] at heq
  exact hsp heq.symm

/-- Final numeric consumer. Finiteness is already supplied independently
by the existing genus-two period-injection proof; detection and zeros
remain explicit dependencies here. -/
theorem actualCanonicalSection_finrank_ge_two_of_detection_and_zeros
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E)
    (hDetection : ActualPointMittagLefflerDetectionStatement E hg A hA)
    (hZeros : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      ∀ s : ActualCanonicalSection E, s ≠ 0 → ∃ p : E, s p = 0)
    (hFinite : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      Module.Finite ℂ (ActualCanonicalSection E)) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    2 ≤ Module.finrank ℂ (ActualCanonicalSection E) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : Module.Finite ℂ (ActualCanonicalSection E) := hFinite
  obtain ⟨s, t, hst⟩ := actualTwoIndependentSections_of_detection_and_zeros
    E hg A hA hDetection hZeros
  simpa using hst.fintype_card_le_finrank

#print axioms actualPointDetection_iff_evaluation_nonzero
#print axioms actualTwoIndependentSections_of_detection_and_zeros
#print axioms actualCanonicalSection_finrank_ge_two_of_detection_and_zeros
end CanonicalDimensionTwo
