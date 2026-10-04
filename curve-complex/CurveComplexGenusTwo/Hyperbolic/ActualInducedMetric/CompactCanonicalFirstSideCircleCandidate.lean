import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfplaneJordanIdentificationCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalAreaCoordinatesCandidate

namespace CurveComplex.Hyperbolic

set_option maxHeartbeats 1000000 in
theorem regular_hexagon_first_side_circle_parameters :
    let c := regularHexagonSideCenter 0
    let t := Real.sqrt 3 + Real.sqrt 2
    1 < c.re ∧ 0 < c.im ∧ c.im = (c.re-1)*t ∧ 1+c.re = (c.re-1)*t^2 := by
  dsimp only
  let α := (1+regularHexagonRadius^2)/(3*regularHexagonRadius)
  have hα : 0 < α := div_pos (by positivity) (mul_pos (by norm_num) regularHexagonRadius_pos)
  have hαsq : α^2 = 2/3 := regular_hexagon_side_scale_identity
  have hs₃ : (Real.sqrt 3)^2 = 3 := by norm_num
  have hs₂ : (Real.sqrt 2)^2 = 2 := by norm_num
  have hp₃ : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hp₂ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hre : (regularHexagonSideCenter 0).re = 3*α/2 := by
    change (((α : ℂ) * (idealHexagonVertex 0 + idealHexagonVertex 1))).re = _
    simp [idealHexagonVertex, Complex.mul_re]; ring
  have him : (regularHexagonSideCenter 0).im = Real.sqrt 3*α/2 := by
    change (((α : ℂ) * (idealHexagonVertex 0 + idealHexagonVertex 1))).im = _
    simp [idealHexagonVertex, Complex.mul_im]; ring
  have hvsq : (Real.sqrt 3*α/2)^2 = 1/2 := by rw [div_pow,mul_pow,hs₃,hαsq]; norm_num
  have hv : Real.sqrt 3*α/2 = Real.sqrt 2/2 := by nlinarith [hvsq,hs₂,mul_pos hp₃ hα]
  have hu : 3*α/2 = Real.sqrt 3*Real.sqrt 2/2 := by
    have h := congrArg (fun v : ℝ => Real.sqrt 3*v) hv
    have hs : Real.sqrt 3*Real.sqrt 3*α = 3*α := by rw [← pow_two,hs₃]
    nlinarith [h,hs]
  rw [hre,him,hu,hv]
  have husq : (Real.sqrt 3*Real.sqrt 2/2)^2 = 3/2 := by rw [div_pow,mul_pow,hs₃,hs₂]; norm_num
  have hup : 0 < Real.sqrt 3*Real.sqrt 2/2 := by positivity
  have hul : 1 < Real.sqrt 3*Real.sqrt 2/2 := by
    by_contra h
    have hm : 0 ≤ (1-Real.sqrt 3*Real.sqrt 2/2)*(1+Real.sqrt 3*Real.sqrt 2/2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  refine ⟨hul,by positivity,?_,?_⟩
  · have h₁ := congrArg (fun v : ℝ => v*Real.sqrt 2) hs₃
    have h₂ := congrArg (fun v : ℝ => v*Real.sqrt 3) hs₂
    nlinarith [h₁,h₂]
  · have h₁ := congrArg (fun v : ℝ => v*Real.sqrt 3*Real.sqrt 2) hs₃
    have h₂ := congrArg (fun v : ℝ => v*Real.sqrt 3*Real.sqrt 2) hs₂
    have h₃ : (Real.sqrt 3)^3 = 3*Real.sqrt 3 := by
      calc _ = (Real.sqrt 3)^2*Real.sqrt 3 := by ring
           _ = _ := by rw [hs₃]
    have h₄ : (Real.sqrt 2)^3 = 2*Real.sqrt 2 := by
      calc _ = (Real.sqrt 2)^2*Real.sqrt 2 := by ring
           _ = _ := by rw [hs₂]
    ring_nf
    rw [hs₃,hs₂,h₃,h₄]
    ring

theorem regular_hexagon_first_side_upper_circle_iff (z : H2) :
    0 < regularHexagonSideEquation 0 (cayley z : ℂ) ↔
      z.re^2+z.im^2 < (Real.sqrt 3+Real.sqrt 2)^2 + 2*(Real.sqrt 3+Real.sqrt 2)*z.re := by
  let c := regularHexagonSideCenter 0
  let t := Real.sqrt 3+Real.sqrt 2
  obtain ⟨hu,hv,h₁,h₂⟩ := regular_hexagon_first_side_circle_parameters
  have h := cayley_disc_circle_signed_polynomial c z
  change regularHexagonSideEquation 0 (cayley z : ℂ)*(z.re^2+(z.im+1)^2) =
    2*((1-c.re)*(z.re^2+z.im^2)+(1+c.re)+2*c.im*z.re) at h
  have hP : (1-c.re)*(z.re^2+z.im^2)+(1+c.re)+2*c.im*z.re =
      (c.re-1)*(t^2+2*t*z.re-(z.re^2+z.im^2)) := by
    change _ = _
    rw [h₁,h₂]
    ring
  rw [hP] at h
  have hd : 0 < z.re^2+(z.im+1)^2 := by nlinarith [z.im_pos,sq_nonneg z.re]
  have hu' : 0 < c.re-1 := by change 0 < (regularHexagonSideCenter 0).re-1; linarith
  change _ ↔ z.re^2+z.im^2 < t^2+2*t*z.re
  constructor <;> intro hz
  · have hm : 0 < regularHexagonSideEquation 0 (cayley z : ℂ)*(z.re^2+(z.im+1)^2) := mul_pos hz hd
    rw [h] at hm
    have hp : 0 < t^2+2*t*z.re-(z.re^2+z.im^2) :=
      (mul_pos_iff_of_pos_left hu').mp (by linarith [hm])
    linarith
  · have hp : 0 < t^2+2*t*z.re-(z.re^2+z.im^2) := by linarith
    have hm : 0 < 2*((c.re-1)*(t^2+2*t*z.re-(z.re^2+z.im^2))) := by positivity
    rw [← h] at hm
    exact (mul_pos_iff_of_pos_right hd).mp hm

end CurveComplex.Hyperbolic
