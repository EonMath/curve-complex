import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 3000000

/-- Explicit boundary-fixed disk recentering. The map is `z+(1-‖z‖)m`.
Its perturbation has Lipschitz constant `‖m‖<1`, so it is a genuine global
homeomorphism before restriction to the disk. -/
theorem closed_disc_recenter
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1) :
    ∃ h : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ
        Metric.closedBall (0:Schoenflies.Plane) 1,
      (∀ z, (h z).val = z.val+(1-‖z.val‖) • m.val) ∧
      h ⟨0,by simp⟩ = m ∧
      (∀ z, ‖z.val‖=1 → h z=z) := by
  let F : Schoenflies.Plane → Schoenflies.Plane := fun z => z+(1-‖z‖) • m.val
  have happ : ApproximatesLinearOn F
      (ContinuousLinearEquiv.refl ℝ Schoenflies.Plane : Schoenflies.Plane →L[ℝ] Schoenflies.Plane)
      Set.univ ‖m.val‖₊ := by
    intro x _ y _
    have heq : F x-F y-(x-y) = (‖y‖-‖x‖) • m.val := by dsimp [F]; module
    change ‖F x-F y-(x-y)‖ ≤ ‖m.val‖ * ‖x-y‖
    rw [heq,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ ‖x-y‖ * ‖m.val‖ := mul_le_mul_of_nonneg_right
        (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x) (norm_nonneg _)
      _ = _ := mul_comm _ _
  let e := happ.toHomeomorph F (Or.inr (by simpa using (show ‖m.val‖₊ < 1 by exact_mod_cast hm)))
  have he (z) : e z=F z := rfl
  have hball (z : Schoenflies.Plane) : z ∈ Metric.closedBall (0:Schoenflies.Plane) 1 ↔
      e z ∈ Metric.closedBall (0:Schoenflies.Plane) 1 := by
    simp only [Metric.mem_closedBall,dist_zero_right,he]
    constructor
    · intro hz
      calc
        ‖F z‖ ≤ ‖z‖ + ‖(1-‖z‖) • m.val‖ := norm_add_le _ _
        _ = ‖z‖+(1-‖z‖)*‖m.val‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hz)]
        _ ≤ 1 := by nlinarith [norm_nonneg z]
    · intro hz
      by_contra hn
      have hzn : 1 < ‖z‖ := lt_of_not_ge hn
      have heq : z = F z-(1-‖z‖) • m.val := by dsimp [F]; abel
      have hle := norm_sub_le (F z) ((1-‖z‖) • m.val)
      rw [← heq,norm_smul,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hzn)] at hle
      nlinarith
  let h := e.subtype hball
  refine ⟨h,fun z => rfl,?_,?_⟩
  · apply Subtype.ext
    change F 0=m.val
    simp [F]
  · intro z hz
    apply Subtype.ext
    change F z.val=z.val
    simp [F,hz]

end CurveComplex
#print axioms CurveComplex.closed_disc_recenter
