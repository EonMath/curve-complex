import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusSurface
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
open Set Topology Schoenflies CurveComplex
/-- An actual embedded essential circle leaves an actual torus point outside
its image, constructed in a source crosscut chart. -/
theorem actual_essential_torus_curve_has_avoided_plane_point
    (b : EssentialCurve (Circle×Circle)) :
    ∃ p : Plane,(Circle.exp (p 0),Circle.exp (p 1))∉b.val.image := by
  obtain ⟨C,hC⟩ := actual_standard_torus_has_closed_surface_structure
  let := C
  let := hC
  let q := b.val.map (1 : Circle)
  have hq : q∈b.val.image := mem_range_self _
  obtain ⟨E,_,_,_,hSquare,hflat⟩ :=
    PositionUniverseV2.position_curve_crosscut_chart (Circle×Circle) b.val q hq univ
      isOpen_univ (mem_univ _)
  let z := Plane.mk 0 (1/2)
  have hzSquare : z∈Plane.closedSquare 0 1 := by
    norm_num [z,Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
  have hzt : z∈E.target := hSquare hzSquare
  let w := E.symm z
  have hws : w∈E.source := E.map_target hzt
  have hwavoid : w∉b.val.image := by
    intro hw
    have hf := (hflat w hws).mp hw
    have hEz : E w=z := E.right_inv hzt
    rw [hEz] at hf
    norm_num [z,Plane.mk] at hf
  obtain ⟨x,hx⟩ := Circle.exp_surjective w.1
  obtain ⟨y,hy⟩ := Circle.exp_surjective w.2
  refine ⟨Plane.mk x y,?_⟩
  change (Circle.exp x,Circle.exp y)∉b.val.image
  rw [hx,hy]
  exact hwavoid
#print axioms actual_essential_torus_curve_has_avoided_plane_point
