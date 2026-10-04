import CurveComplexGenusTwo.Dictionary.Circle24.PolarCellDisk
import CurveComplexGenusTwo.Dictionary.Circle24.DiscBoundaryLoop
import CurveComplexGenusTwo.Dictionary.Circle24.ActualCircle24Corridor
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 7000000

/-- A source one-mark closed disk has a complete disk lift, constructed from
its only interior branch point. No auxiliary boundary loop is supplied. -/
theorem one_mark_closed_disk_full_preimage
    (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m) :
    Nonempty (Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ
      M.cover.projection ⁻¹' Set.range f) := by
  obtain ⟨β,hends,hcoll,hrange⟩ := CurveComplex.unit_disc_boundary_loop_exists
  exact M.one_mark_disc_lift_is_closed_disk f hf m hm honly β hends hcoll hrange

/-- Both actual one-mark cells extracted from the Circle24 disk chart have
complete closed-disk lifts. The cell boundaries are tied to the source chart;
no cell-lift or annulus certificate is an input. -/
theorem actual_circle24_one_mark_cell_disk_lifts (M : HyperellipticModel E S)
    (a : Circle24 M) :
    ∃ f : C(dictPullbackSquare,S), IsEmbedding f ∧
      f '' {z | z.val ∈ frontier dictPullbackSquare}=a.val.image ∧
    ∃ lo hi : Fin 2 → ℝ × ℝ,
    ∃ F : Fin 2 → C(Metric.closedBall (0:Schoenflies.Plane) 1,S),
    ∃ m : Fin 2 → Metric.closedBall (0:Schoenflies.Plane) 1,
      (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
      dictPullbackEquiv '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2) ∪
      dictPullbackEquiv '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2)=dictPullbackSquare ∧
      (∀ i, IsEmbedding (F i) ∧ ‖(m i).val‖ < 1 ∧
        (∀ z, F i z ∈ M.cover.branch ↔ z=m i) ∧
        F i '' {z | ‖z.val‖=1} = f '' {z | z.val ∈ frontier
          (dictPullbackEquiv '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2))} ∧
        Nonempty (Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ
          M.cover.projection ⁻¹' Set.range (F i))) := by
  obtain ⟨U,d,hU,hconn,hcl,hb,hi,hcount⟩ := M.actual_circle24_two_mark_closed_side a
  obtain ⟨f,hf,havoid,hcard,houter,hinterior⟩ :=
    two_mark_closed_side_actual_square_chart M a.val U d hcl hb hi hcount
  obtain ⟨lo,hi,F,m,hdims,hcover,hshape,hcells⟩ :=
    M.two_marked_rectangle_disc_cells f hf havoid hcard
  refine ⟨f,hf,houter,lo,hi,F,m,hdims,hcover,?_⟩
  intro i
  obtain ⟨hF,hm,honly,hboundary⟩ := hcells i
  exact ⟨hF,hm,honly,hboundary,M.one_mark_closed_disk_full_preimage (F i) hF (m i) hm honly⟩

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.one_mark_closed_disk_full_preimage
#print axioms CurveComplex.HyperellipticModel.actual_circle24_one_mark_cell_disk_lifts
