import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts

open scoped ContDiff
open MeasureTheory

namespace CanonicalDimensionTwo.LocalDbar.SourceReviewRequests

/-- Review request only. McMullen Theorem 8.1, printed p.78, after moving
the derivative onto the smooth compactly supported input. This is an
unproved Prop definition, not an inhabitant of the asserted identity. -/
def CompactCauchyIdentityStatement : Prop :=
  ∀ g : ℂ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
    ∀ z : ℂ, (∫ w : ℂ, w⁻¹ * dbar g (z - w)) = (Real.pi : ℂ) * g z

/-- Review request only. The literal normalized Cauchy transform of a
globally smooth compactly supported coefficient. No proof is asserted. -/
def CompactCauchyTransformStatement : Prop :=
  ∀ g : ℂ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
    let F : ℂ → ℂ := fun z => (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * g (z - w)
    ContDiff ℝ ∞ F ∧ ∀ z : ℂ, dbar F z = g z

end CanonicalDimensionTwo.LocalDbar.SourceReviewRequests
