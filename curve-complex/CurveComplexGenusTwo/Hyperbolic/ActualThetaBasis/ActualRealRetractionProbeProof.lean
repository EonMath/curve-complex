import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualRadialAxisFixingProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualLoopTransportDefinitions
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_real_plane_theta_negative_axis_retraction : ∃ R : ActualPuncturedRealPlane ≃ₕ ActualSquareTheta,
    (∀ (a : ℝ),0<a → ∀ (z : ActualPuncturedRealPlane),z.val=(-a,0) → R z=thetaBase) ∧
    (∀ z : ActualSquareTheta,R (thetaRealEmbedding z)=z) := by
  let P := {z : ℝ×ℝ // z≠((-1/2:ℝ),0) ∧ z≠((1/2:ℝ),0)}
  let shift : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) := Homeomorph.addRight ((-1/2:ℝ),0)
  have hs (z : ℝ×ℝ) : shift z=(z.1-1/2,z.2) := by
    apply Prod.ext <;> dsimp [shift] <;> ring
  have h0 (z : ℝ×ℝ) : shift z=((-1/2:ℝ),0) ↔ z=((0:ℝ),0) := by
    rw [hs];constructor
    · intro h;apply Prod.ext <;> have hx := congrArg Prod.fst h <;> have hy := congrArg Prod.snd h <;> dsimp at hx hy ⊢ <;> linarith
    · rintro rfl;norm_num
  have h1 (z : ℝ×ℝ) : shift z=((1/2:ℝ),0) ↔ z=((1:ℝ),0) := by
    rw [hs];constructor
    · intro h;apply Prod.ext <;> have hx := congrArg Prod.fst h <;> have hy := congrArg Prod.snd h <;> dsimp at hx hy ⊢ <;> linarith
    · rintro rfl;norm_num
  let shifted : ActualPuncturedRealPlane ≃ₜ P := shift.subtype
    (fun z => and_congr (not_congr (h0 z)).symm (not_congr (h1 z)).symm)
  obtain ⟨radial,haxis,hfix⟩ := actual_radial_negative_axis_and_theta_fixing
  refine ⟨shifted.toHomotopyEquiv.trans radial,?_,?_⟩
  · intro a ha z hz
    apply haxis a ha
    change shift z.val=(-a-1/2,0)
    rw [hs,hz]
  · intro z
    apply hfix z
    change shift (thetaRealEmbedding z).val=z.val
    rw [hs]
    apply Prod.ext <;> dsimp [thetaRealEmbedding] <;> ring
end CurveComplex.Hyperbolic.PantsTheta
