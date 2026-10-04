import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactConeSquareDevelopment
import CurveComplexGenusTwo.Dictionary.BranchedCover

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def normalizedConeVertex : H2 := ⟨Complex.I, by simp⟩

theorem normalizedConeVertex_cayley : (cayley normalizedConeVertex : ℂ) = 0 := by
  change (Complex.I - Complex.I) / (Complex.I + Complex.I) = 0
  simp

noncomputable def halfTurnConeSquareBranchChart :
    SquareBranchChart H2 HalfTurnMetricCone toHalfTurnMetricCone normalizedConeVertex := by
  letI : Nonempty HalfTurnMetricCone := ⟨toHalfTurnMetricCone normalizedConeVertex⟩
  let f : H2 → ℂ := fun z => (cayley z : ℂ)
  have hf : IsOpenEmbedding f :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp cayleyHomeomorph.isOpenEmbedding
  let chartUp := hf.toOpenPartialHomeomorph f
  let chartDown := coneSquareCoordinate_isOpenEmbedding.toOpenPartialHomeomorph coneSquareCoordinate
  refine { upstairs := chartUp
           downstairs := chartDown
           upstairs_mem := ?_
           downstairs_mem := ?_
           upstairs_center := ?_
           downstairs_center := ?_
           image_mem := ?_
           square := ?_ }
  · simp [chartUp]
  · simp [chartDown]
  · change (cayley normalizedConeVertex : ℂ) = 0
    exact normalizedConeVertex_cayley
  · change coneSquareCoordinate (toHalfTurnMetricCone normalizedConeVertex) = 0
    rw [coneSquareCoordinate_projection, normalizedConeVertex_cayley, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · intro z hz
    simp [chartDown]
  · intro z hz
    change coneSquareCoordinate (toHalfTurnMetricCone z) = (cayley z : ℂ) ^ 2
    exact coneSquareCoordinate_projection z

end CurveComplex.Hyperbolic
