import CurveComplexGenusTwo.Dependencies.ClosedDomain
import CurveComplexGenusTwo.Dependencies.ChartClosure

namespace CurveComplex.SpherePort

theorem chart_inside_closed_disc (c : JordanCurve) (P : Chart c) :
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (P.inside c)) := by
  let C := P.planeImage c
  have hC : Schoenflies.IsJordanCurve C := chart_image_jordan c P
  have hcompact : IsCompact (closure (Schoenflies.inside C)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (Schoenflies.jordan_curve_theorem hC).isBounded_inside.closure
  obtain ⟨e⟩ := plane_inside_closed_disc C hC
  exact ⟨e.trans <| chart_pullback_closure_homeomorph c P
    (Schoenflies.inside C) hcompact⟩

end CurveComplex.SpherePort
