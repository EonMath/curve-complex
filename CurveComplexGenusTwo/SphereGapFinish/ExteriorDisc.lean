import CurveComplexGenusTwo.Dependencies.ClosedDomain
import CurveComplexGenusTwo.SphereGapFinish.ExteriorInversion

namespace CurveComplex.SphereGapFinish

noncomputable section

/-- The one-point compactification of the closed exterior of a plane Jordan
curve is a genuine closed disc. The puncture is sent to an interior point by
inversion, then the bounded Schoenflies theorem supplies the disc model. -/
theorem plane_exterior_closed_disc (C : Set Schoenflies.Plane)
    (hC : Schoenflies.IsJordanCurve C) :
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      compactifiedExterior C) := by
  obtain ⟨a, ha⟩ := (Schoenflies.jordan_curve_theorem hC).isConnected_inside.nonempty
  have hC' : Schoenflies.IsJordanCurve (Schoenflies.invert a '' C) :=
    hC.invert_image ha.1
  obtain ⟨e⟩ := CurveComplex.SpherePort.plane_inside_closed_disc
    (Schoenflies.invert a '' C) hC'
  exact ⟨e.trans (exteriorToInvertedInterior C hC a ha).symm⟩

end

end CurveComplex.SphereGapFinish
