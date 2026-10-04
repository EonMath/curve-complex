import CurveComplexGenusTwo.Dependencies.ChartClosure
import CurveComplexGenusTwo.SphereGapFinish.ExteriorDisc

namespace CurveComplex.SphereGapFinish

noncomputable section

/-- The exterior closed side of a spherical Jordan curve is a closed disc.
This fills the second geometric conjunct intended by `chart_closed_discs`
without using that declaration or its `sorry` proof. -/
theorem chart_outside_closed_disc
    (c : CurveComplex.SpherePort.JordanCurve)
    (P : CurveComplex.SpherePort.Chart c) :
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (P.outside c)) := by
  let C := P.planeImage c
  obtain ⟨e⟩ := plane_exterior_closed_disc C
    (CurveComplex.SpherePort.chart_image_jordan c P)
  have hset : compactifiedExterior C =
      closure (CurveComplex.SpherePort.compactifiedOutside
        (Schoenflies.outside C)) := by
    rw [CurveComplex.SpherePort.closure_compactifiedOutside]
    rfl
  exact ⟨e.trans (Homeomorph.setCongr hset) |>.trans
    (CurveComplex.SpherePort.chart_outside_closure_homeomorph c P)⟩

end

end CurveComplex.SphereGapFinish
