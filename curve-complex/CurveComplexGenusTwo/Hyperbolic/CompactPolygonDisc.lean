import CurveComplexGenusTwo.Hyperbolic.CompactHexagonRegion
import CurveComplexGenusTwo.Dictionary.JordanDiscHelper

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_closed_disc_with_boundary :
    ∃ d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ ClosedPolygon regularHexagonRegion,
      ∀ x, ((d x : H2) ∈ frontier regularHexagonRegion.interior ↔
        ‖(x : Schoenflies.Plane)‖ = 1) := by
  let e := hyperbolicPlaneHomeomorph
  let C := e '' (⋃ i : Fin 6, regularHexagonCandidate.edge i)
  obtain ⟨d, hboundary, _⟩ := CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary C
    (regularHexagon_plane_boundary_isJordanCurve e)
  have hclosure : e.symm '' closure (Schoenflies.inside C) =
      closure regularHexagonRegion.interior := by
    change e.symm '' closure (Schoenflies.inside C) =
      closure (e.symm '' Schoenflies.inside C)
    exact e.symm.image_closure _
  let D := d.trans ((e.symm.image (closure (Schoenflies.inside C))).trans
    (Homeomorph.setCongr hclosure))
  refine ⟨D, ?_⟩
  intro x
  rw [regularHexagonRegion.boundary_is_edges]
  change e.symm (d x) ∈ (⋃ i : Fin 6, regularHexagonCandidate.edge i) ↔
    ‖(x : Schoenflies.Plane)‖ = 1
  constructor
  · intro hx
    apply (hboundary x).mp
    exact ⟨e.symm (d x), hx, e.apply_symm_apply _⟩
  · intro hx
    obtain ⟨y, hy, heq⟩ := (hboundary x).mpr hx
    simpa only [← heq, e.symm_apply_apply] using hy

end CurveComplex.Hyperbolic
