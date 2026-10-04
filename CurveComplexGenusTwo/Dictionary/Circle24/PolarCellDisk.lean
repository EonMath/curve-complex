import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkCellQuotient
import CurveComplexGenusTwo.Dictionary.Circle24.LocalBranchDisk
import Mathlib.Topology.Algebra.ConstMulAction
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 6000000

private theorem complex_plane_isometry : Nonempty (ℂ ≃ₗᵢ[ℝ] Schoenflies.Plane) := by
  let e : ℂ ≃L[ℝ] Schoenflies.Plane :=
    Complex.equivRealProdCLM.trans ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  have hnorm (z : ℂ) : ‖e z‖=‖z‖ := by
    have he0 : e z 0=z.re := rfl
    have he1 : e z 1=z.im := rfl
    have heSq : ‖e z‖^2=‖z‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Complex.sq_norm]
      simp [Fin.sum_univ_two,he0,he1,Complex.normSq_apply,pow_two]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heSq
  exact ⟨{toLinearEquiv := e.toLinearEquiv,norm_map' := hnorm}⟩

private noncomputable def normalized_complex_disc (i : ℂ ≃ₗᵢ[ℝ] Schoenflies.Plane)
    (r : ℝ) (hr : 0 < r) : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ
      Metric.closedBall (0:ℂ) r :=
  (i.symm.toHomeomorph.trans (Homeomorph.smulOfNeZero (α := ℂ) r (ne_of_gt hr))).subtype (by
    intro z
    simp only [Metric.mem_closedBall,dist_zero_right,Homeomorph.trans_apply,
      Homeomorph.smulOfNeZero_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    change ‖z‖ ≤ 1 ↔ r * ‖i.symm z‖ ≤ r
    rw [i.symm.norm_map]
    constructor <;> intro hz <;> nlinarith)

namespace BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

private theorem downstairs_square_disk_branch_iff_zero
    (q : BranchedDoubleCover E S) (w : E) (hw : q.projection w ∈ q.branch)
    (r : ℝ) (hr : 0 < r)
    (hu : Metric.closedBall (0:ℂ) r ⊆ (q.branch_chart w hw).upstairs.target)
    (hd : Metric.closedBall (0:ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target)
    (y : ℂ) (hy : y ∈ Metric.closedBall (0:ℂ) (r^2)) :
    (q.branch_chart w hw).downstairs.symm y ∈ q.branch ↔ y=0 := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)
  have hznorm : ‖z‖ ≤ r := by
    have he : ‖z‖^2=‖y‖ := by rw [← norm_pow,hz]
    have hynorm : ‖y‖ ≤ r^2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    nlinarith [norm_nonneg z]
  have hzball : z ∈ Metric.closedBall (0:ℂ) r := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hznorm
  have hπ := q.square_chart_disk_projection w hw r hr hu hd z hzball
  rw [hz] at hπ
  rw [← hπ,q.square_chart_disk_branch_iff_zero w hw r hr hu hd z hzball]
  constructor
  · intro hz0
    simpa [hz0] using hz.symm
  · intro hy0
    have hzsq : z^2=0 := hz.trans hy0
    exact eq_zero_of_pow_eq_zero hzsq

end BranchedDoubleCover

namespace HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Calibrate the explicit polar cell against an actual local square branch
chart. This identifies it with the ordinary closed disk without assuming a
disk-lift certificate for the source cell. -/
theorem one_mark_polar_cell_is_closed_disk (M : HyperellipticModel E S)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0=β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β={z | ‖z.val‖=1}) :
    Nonempty (OneMarkPolarCell ≃ₜ Metric.closedBall (0:Schoenflies.Plane) 1) := by
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < M.cover.branch.card by rw [M.cover.branch_card]; norm_num)
  obtain ⟨w,hw⟩ := M.cover.projection_surjective b
  have hwbranch : M.cover.projection w ∈ M.cover.branch := hw ▸ hb
  obtain ⟨r,hr,hu,hd,hUp,hUpval⟩ := M.cover.local_square_disk_lift_exists w hwbranch
  obtain ⟨i⟩ := complex_plane_isometry
  let c := M.cover.branch_chart w hwbranch
  let D : Set S := c.downstairs.symm '' Metric.closedBall (0:ℂ) (r^2)
  let n := normalized_complex_disc i (r^2) (sq_pos_of_pos hr)
  let hDown : Metric.closedBall (0:ℂ) (r^2) ≃ₜ D :=
    c.downstairs.symm.homeomorphOfImageSubsetSource hd rfl
  let f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) :=
    ⟨fun z => (hDown (n z)).val,continuous_subtype_val.comp (hDown.continuous.comp n.continuous)⟩
  have hf : IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp (hDown.isEmbedding.comp n.isEmbedding)
  have honly (z) : f z ∈ M.cover.branch ↔ z=(⟨0,by simp⟩ : Metric.closedBall (0:Schoenflies.Plane) 1) := by
    change c.downstairs.symm (n z).val ∈ M.cover.branch ↔ z=⟨0,by simp⟩
    rw [M.cover.downstairs_square_disk_branch_iff_zero w hwbranch r hr hu hd _ (n z).property]
    constructor
    · intro hz
      apply n.injective
      apply Subtype.ext
      have hnzero : (n (⟨0,by simp⟩ : Metric.closedBall (0:Schoenflies.Plane) 1)).val=0 := by
        change (r^2) • i.symm 0=0
        simp
      exact hz.trans hnzero.symm
    · intro hz
      rw [hz]
      simp [n,normalized_complex_disc]
  obtain ⟨e,he⟩ := M.cover.projection_surjective (f (β 0))
  obtain ⟨H,hanchor⟩ := M.one_mark_disc_polar_cell_homeomorph f hf ⟨0,by simp⟩
    (by simp) honly β hends hcoll hrange e he
  have hfrange : Set.range f=D := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact (hDown (n z)).property
    · intro hy
      refine ⟨n.symm (hDown.symm ⟨y,hy⟩),?_⟩
      change (hDown (n (n.symm (hDown.symm ⟨y,hy⟩)))).val=y
      rw [n.apply_symm_apply,hDown.apply_symm_apply]
  let nUp := normalized_complex_disc i r hr
  exact ⟨H.trans ((Homeomorph.setCongr (congrArg (fun A => M.cover.projection ⁻¹' A) hfrange)).trans
    (hUp.symm.trans nUp.symm))⟩

/-- The full lift of an embedded closed disk containing exactly one interior
branch point is an actual closed disk. No lift existence is assumed. -/
theorem one_mark_disc_lift_is_closed_disk (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0=β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β={z | ‖z.val‖=1}) :
    Nonempty (Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ M.cover.projection ⁻¹' Set.range f) := by
  obtain ⟨e,he⟩ := M.cover.projection_surjective (f (β 0))
  obtain ⟨H,hanchor⟩ := M.one_mark_disc_polar_cell_homeomorph f hf m hm honly β hends hcoll hrange e he
  obtain ⟨d⟩ := M.one_mark_polar_cell_is_closed_disk β hends hcoll hrange
  exact ⟨d.symm.trans H⟩

end HyperellipticModel
end CurveComplex
#print axioms CurveComplex.HyperellipticModel.one_mark_polar_cell_is_closed_disk
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_lift_is_closed_disk
