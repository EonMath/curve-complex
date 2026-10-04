import ClassificationOfSurfaces.Moise.Brouwer
import CurveComplexGenusTwo.Foundations.PlanarDiscRecognition
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import CurveComplexGenusTwo.Topology.IntersectionParity.DiscRangeCoordinates
open Set Topology Schoenflies Bornology
namespace CurveComplex

theorem actual_jordan_disc_in_open_unit_ball
    (C : Set Plane) (hC : Schoenflies.IsJordanCurve C)
    (hball : C ⊆ Metric.ball (0 : Plane) 1) :
    ∃ d : C(Metric.closedBall (0 : Plane) 1,Plane), Topology.IsEmbedding d ∧
      d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C ∧
      Set.range d ⊆ Metric.ball (0 : Plane) 1 := by
  classical
  obtain ⟨square,hSquare,hBoundary⟩ := exists_embedded_square_disc_of_jordan hC
  obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Plane.convex_closedSquare 0 1)
    (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
    (Plane.isBounded_closedSquare 0 1)
  have hcl' : h '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
    simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hcl
  have hfront' : h '' Schoenflies.modelCurve = Metric.sphere (0 : Plane) 1 := by
    simpa only [← Schoenflies.modelCurve_eq_frontier] using hfront
  let e : Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Plane) 1 :=
    (h.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hcl')
  have he (x : Plane.closedSquare 0 1) : (e x).val = h x.val := rfl
  have heB : e.symm '' {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.sphere (0 : Plane) 1} =
      {x : Plane.closedSquare 0 1 | x.val ∈ Schoenflies.modelCurve} := by
    ext x
    constructor
    · rintro ⟨y,hy,hxy⟩
      have hy' : (e x).val ∈ Metric.sphere (0 : Plane) 1 := by
        rw [←hxy,e.apply_symm_apply]; exact hy
      rw [he,←hfront'] at hy'
      obtain ⟨z,hz,hzx⟩ := hy'
      change x.val ∈ Schoenflies.modelCurve
      rw [←h.injective hzx]
      exact hz
    · intro hx
      refine ⟨e x,?_,e.symm_apply_apply x⟩
      change (e x).val ∈ Metric.sphere (0 : Plane) 1
      rw [he,←hfront']
      exact Set.mem_image_of_mem h hx
  let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
    ⟨fun x => square (e.symm x),square.continuous.comp e.symm.continuous⟩
  have hd : Topology.IsEmbedding d := hSquare.comp e.symm.isEmbedding
  have hdB : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C := by
    change (square ∘ e.symm) '' _ = C
    rw [Set.image_comp,heB]
    exact hBoundary
  have hinside : Schoenflies.inside C ⊆ Metric.ball (0 : Plane) 1 := by
    intro x hx
    by_contra hxnot
    have hnorm : 1 ≤ ‖x‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hxnot
    let ray := (fun t : ℝ => t • x) '' Set.Ici (1 : ℝ)
    have hray : IsPreconnected ray := isPreconnected_Ici.image _
      (continuous_id.smul continuous_const).continuousOn
    have hxray : x ∈ ray := ⟨1,by simp,one_smul ℝ x⟩
    have hRayOff : ray ⊆ Cᶜ := by
      rintro y ⟨t,ht,rfl⟩ hy
      have hb : ‖t • x‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hball hy
      change 1 ≤ t at ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ t)] at hb
      nlinarith only [hb,ht,hnorm]
    have hRayCC := hray.subset_connectedComponentIn hxray hRayOff
    obtain ⟨R,hR⟩ := hx.2.exists_norm_le
    let t := max 1 ((R+1)/‖x‖)
    have ht : 1 ≤ t := le_max_left _ _
    have hbound := hR (t • x) (hRayCC ⟨t,ht,rfl⟩)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ t)] at hbound
    have hdiv : (R+1)/‖x‖ ≤ t := le_max_right _ _
    have hmul := (div_le_iff₀ (by linarith : 0 < ‖x‖)).mp hdiv
    linarith only [hmul,hbound]
  have hrange : Set.range d = Schoenflies.inside C ∪ C :=
    embedded_disc_range_eq_closed_inside d hd C hC hdB
  refine ⟨d,hd,hdB,?_⟩
  rw [hrange]
  exact Set.union_subset hinside hball

end CurveComplex
