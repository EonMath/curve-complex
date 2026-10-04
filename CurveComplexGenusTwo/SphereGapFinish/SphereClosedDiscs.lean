import CurveComplexGenusTwo.Dependencies.InsideDisc
import CurveComplexGenusTwo.SphereGapFinish.ExteriorSphereDisc

namespace CurveComplex.SphereGapFinish

/-- Both closed sides of a spherical Jordan curve are closed discs. This is
an axiom-clean replacement body for `CurveComplex.SpherePort.chart_closed_discs`. -/
theorem chart_closed_discs_complete
    (c : CurveComplex.SpherePort.JordanCurve)
    (P : CurveComplex.SpherePort.Chart c) :
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (P.inside c)) ∧
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (P.outside c)) :=
  ⟨CurveComplex.SpherePort.chart_inside_closed_disc c P,
    chart_outside_closed_disc c P⟩

end CurveComplex.SphereGapFinish

namespace CurveComplex.SpherePort

/-- Both complementary closed sides of a spherical Jordan curve are discs. -/
theorem chart_closed_discs (c : JordanCurve) (P : Chart c) :
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (P.inside c)) ∧
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (P.outside c)) :=
  CurveComplex.SphereGapFinish.chart_closed_discs_complete c P

end CurveComplex.SpherePort
