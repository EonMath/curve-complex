import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnCovering
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnSquareCoordinates
import Mathlib.Analysis.Complex.OpenMapping

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def coneSquareCoordinate (w : HalfTurnMetricCone) : ℂ :=
  (cayley (halfTurnMetricCone_projection_surjective w).choose : ℂ) ^ 2

theorem coneSquareCoordinate_projection (z : H2) :
    coneSquareCoordinate (toHalfTurnMetricCone z) = (cayley z : ℂ) ^ 2 := by
  apply (cayley_square_fibers _ z).mpr
  exact (halfTurnMetricCone_projection_surjective (toHalfTurnMetricCone z)).choose_spec

theorem coneSquareCoordinate_injective : Function.Injective coneSquareCoordinate := by
  intro a b hab
  obtain ⟨z, rfl⟩ := halfTurnMetricCone_projection_surjective a
  obtain ⟨w, rfl⟩ := halfTurnMetricCone_projection_surjective b
  rw [coneSquareCoordinate_projection, coneSquareCoordinate_projection] at hab
  exact (cayley_square_fibers z w).mp hab

theorem coneSquareCoordinate_continuous : Continuous coneSquareCoordinate := by
  have hquot := halfTurnMetricCone_projection_open.isQuotientMap
    halfTurnMetricCone_projection_continuous halfTurnMetricCone_projection_surjective
  apply hquot.continuous_iff.mpr
  have heq : coneSquareCoordinate ∘ toHalfTurnMetricCone = fun z => (cayley z : ℂ) ^ 2 := by
    funext z
    exact coneSquareCoordinate_projection z
  rw [heq]
  exact (continuous_subtype_val.comp cayley_continuous).pow 2

theorem coneSquareCoordinate_open : IsOpenMap coneSquareCoordinate := by
  have hC : IsOpenMap (fun z : H2 => (cayley z : ℂ) ^ 2) :=
    (Complex.isOpenQuotientMap_pow 2).isOpenMap.comp
      ((Metric.isOpen_ball.isOpenEmbedding_subtypeVal).isOpenMap.comp cayleyHomeomorph.isOpenMap)
  intro U hU
  have hpre : IsOpen (toHalfTurnMetricCone ⁻¹' U) :=
    hU.preimage halfTurnMetricCone_projection_continuous
  have heq : coneSquareCoordinate '' U =
      (fun z : H2 => (cayley z : ℂ) ^ 2) '' (toHalfTurnMetricCone ⁻¹' U) := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨z, rfl⟩ := halfTurnMetricCone_projection_surjective a
      exact ⟨z, ha, (coneSquareCoordinate_projection z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨toHalfTurnMetricCone z, hz, coneSquareCoordinate_projection z⟩
  rw [heq]
  exact hC _ hpre

theorem coneSquareCoordinate_isOpenEmbedding : IsOpenEmbedding coneSquareCoordinate := by
  exact (isOpenEmbedding_iff_continuous_injective_isOpenMap).mpr
    ⟨coneSquareCoordinate_continuous, coneSquareCoordinate_injective, coneSquareCoordinate_open⟩

end CurveComplex.Hyperbolic
