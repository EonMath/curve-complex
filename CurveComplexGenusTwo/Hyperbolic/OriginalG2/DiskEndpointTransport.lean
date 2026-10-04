import CurveComplexGenusTwo.Topology.ActualGeometryRelease.H2IsometryClosedDiskExtensionPROVED
import CurveComplexGenusTwo.Hyperbolic.Cayley
import CurveComplexGenusTwo.Hyperbolic.VerticalGeodesic
import Mathlib

namespace CurveComplex.Hyperbolic

open Filter Topology
open scoped UpperHalfPlane MatrixGroups

private theorem sl_vertical_cayley_formula
    (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    (cayley (M • verticalPath t) : ℂ) =
      (((M 0 0:ℂ)*Complex.I*(Real.exp t)+M 0 1)-
        Complex.I*((M 1 0:ℂ)*Complex.I*(Real.exp t)+M 1 1))/
      (((M 0 0:ℂ)*Complex.I*(Real.exp t)+M 0 1)+
        Complex.I*((M 1 0:ℂ)*Complex.I*(Real.exp t)+M 1 1)) := by
  have hD : (M 1 0:ℂ)*Complex.I*(Real.exp t)+M 1 1 ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_im,Complex.ofReal_re,Complex.I_re,Complex.I_im,
      zero_mul,zero_add,add_zero] at him
    have him' : M 1 0 * Real.exp t = 0 := by
      simpa only [mul_zero,sub_zero,zero_mul,zero_add,one_mul,mul_one,
        Complex.zero_im] using him
    have hc : M 1 0 = 0 := by
      have : (Real.exp t) ≠ 0 := Real.exp_ne_zero _
      exact (mul_eq_zero.mp him').resolve_right this
    have hre := congrArg Complex.re h
    simp [hc] at hre
    have hdet : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
      simpa only [Matrix.det_fin_two] using M.property
    rw [hc,show M 1 1=0 by exact_mod_cast hre] at hdet
    norm_num at hdet
  change (((M • verticalPath t:H2):ℂ)-Complex.I)/
    (((M • verticalPath t:H2):ℂ)+Complex.I) = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((M 0 0:ℂ)*((verticalPath t: H2):ℂ)+M 0 1)/
      ((M 1 0:ℂ)*((verticalPath t: H2):ℂ)+M 1 1)-Complex.I)/
    (((M 0 0:ℂ)*((verticalPath t: H2):ℂ)+M 0 1)/
      ((M 1 0:ℂ)*((verticalPath t: H2):ℂ)+M 1 1)+Complex.I) = _
  have hv : ((verticalPath t:H2):ℂ)=Complex.I*(Real.exp t) := by
    change (⟨0,Real.exp t⟩:ℂ)=Complex.I*(Real.exp t)
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,zero_add,one_mul] <;> norm_num
  rw [hv]
  simp only [mul_assoc] at hD ⊢
  rw [div_sub' hD,div_add' _ _ _ hD,div_div_div_cancel_right₀ hD]
  congr 1 <;> ring

private theorem sl_vertical_cayley_atTop
    (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : M 0 0 ≠ 0) :
    Tendsto (fun t : ℝ => (cayley (M • verticalPath t) : ℂ))
      atTop (𝓝 (((M 0 0:ℂ)-Complex.I*(M 1 0:ℂ))/
        ((M 0 0:ℂ)+Complex.I*(M 1 0:ℂ)))) := by
  let N (q : ℝ) : ℂ :=
    (M 0 0:ℂ)*Complex.I+(M 0 1:ℂ)*q-
      Complex.I*((M 1 0:ℂ)*Complex.I+(M 1 1:ℂ)*q)
  let D (q : ℝ) : ℂ :=
    (M 0 0:ℂ)*Complex.I+(M 0 1:ℂ)*q+
      Complex.I*((M 1 0:ℂ)*Complex.I+(M 1 1:ℂ)*q)
  have hD : D 0 ≠ 0 := by
    change (M 0 0:ℂ)*Complex.I+(M 0 1:ℂ)*0+
      Complex.I*((M 1 0:ℂ)*Complex.I+(M 1 1:ℂ)*0) ≠ 0
    intro h
    have hi := congrArg Complex.im h
    have hz : M 0 0 = 0 := by
      simpa [Complex.add_im,Complex.mul_im,Complex.mul_re] using hi
    exact ha hz
  have hq : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hlim : Tendsto (fun t : ℝ => N (Real.exp (-t))/D (Real.exp (-t)))
      atTop (𝓝 (N 0/D 0)) := by
    have hcN : ContinuousAt N 0 := by fun_prop
    have hcD : ContinuousAt D 0 := by fun_prop
    exact (hcN.div hcD hD).tendsto.comp hq
  have heq (t : ℝ) : (cayley (M • verticalPath t) : ℂ) =
      N (Real.exp (-t))/D (Real.exp (-t)) := by
    rw [sl_vertical_cayley_formula]
    have hexp : (Real.exp t:ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero t
    have hmul : (Real.exp t:ℂ)*(Real.exp (-t):ℂ)=1 := by
      norm_cast
      rw [← Real.exp_add]
      simp
    have hmul' : (Real.exp (-t):ℂ)*(Real.exp t:ℂ)=1 := by
      rw [mul_comm]
      exact hmul
    have hN : N (Real.exp (-t))*(Real.exp t:ℂ) =
        ((M 0 0:ℂ)*Complex.I*(Real.exp t)+M 0 1)-
          Complex.I*((M 1 0:ℂ)*Complex.I*(Real.exp t)+M 1 1) := by
      dsimp [N]
      linear_combination
        ((M 0 1:ℂ)-Complex.I*(M 1 1:ℂ)) * hmul'
    have hDen : D (Real.exp (-t))*(Real.exp t:ℂ) =
        ((M 0 0:ℂ)*Complex.I*(Real.exp t)+M 0 1)+
          Complex.I*((M 1 0:ℂ)*Complex.I*(Real.exp t)+M 1 1) := by
      dsimp [D]
      linear_combination
        ((M 0 1:ℂ)+Complex.I*(M 1 1:ℂ)) * hmul'
    rw [←hN,←hDen]
    exact (mul_div_mul_right _ _ hexp)
  have htarget : N 0/D 0 =
      ((M 0 0:ℂ)-Complex.I*(M 1 0:ℂ))/
        ((M 0 0:ℂ)+Complex.I*(M 1 0:ℂ)) := by
    dsimp [N,D]
    simp only [Complex.ofReal_zero,mul_zero,add_zero]
    have hr : (M 0 0:ℂ)+Complex.I*(M 1 0:ℂ) ≠ 0 := by
      intro h
      have hz : M 0 0 = 0 := by
        simpa [Complex.add_im,Complex.mul_im,Complex.mul_re] using
          congrArg Complex.re h
      exact ha hz
    apply (div_eq_div_iff (by simpa [D] using hD) hr).2
    ring_nf
  simpa only [heq,htarget] using hlim

private theorem sl_vertical_cayley_atBot
    (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : M 1 1 ≠ 0) :
    Tendsto (fun t : ℝ => (cayley (M • verticalPath t) : ℂ))
      atBot (𝓝 (((M 0 1:ℂ)-Complex.I*(M 1 1:ℂ))/
        ((M 0 1:ℂ)+Complex.I*(M 1 1:ℂ)))) := by
  let N (q : ℝ) : ℂ :=
    ((M 0 0:ℂ)*Complex.I*q+M 0 1)-
      Complex.I*((M 1 0:ℂ)*Complex.I*q+M 1 1)
  let D (q : ℝ) : ℂ :=
    ((M 0 0:ℂ)*Complex.I*q+M 0 1)+
      Complex.I*((M 1 0:ℂ)*Complex.I*q+M 1 1)
  have hD : D 0 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    have hz : M 1 1 = 0 := by
      simpa [D,Complex.add_im,Complex.mul_im,Complex.mul_re] using hi
    exact hd hz
  have hq : Tendsto (fun t : ℝ => Real.exp t) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot
  have hcN : ContinuousAt N 0 := by fun_prop
  have hcD : ContinuousAt D 0 := by fun_prop
  have hlim : Tendsto (fun t : ℝ => N (Real.exp t)/D (Real.exp t))
      atBot (𝓝 (N 0/D 0)) := (hcN.div hcD hD).tendsto.comp hq
  have heq (t : ℝ) : (cayley (M • verticalPath t) : ℂ) =
      N (Real.exp t)/D (Real.exp t) := by
    rw [sl_vertical_cayley_formula]
  have htarget : N 0/D 0 =
      ((M 0 1:ℂ)-Complex.I*(M 1 1:ℂ))/
        ((M 0 1:ℂ)+Complex.I*(M 1 1:ℂ)) := by
    simp [N,D]
  simpa only [heq,htarget] using hlim

theorem sl_disk_extension_endpoint_images
    (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0)
    (e : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1)
    (he : ∀ z : H2, e (cayley z) = cayley (M • z)) :
    (e ⟨-1,by simp [Metric.mem_closedBall,dist_zero_right]⟩ : ℂ) =
      ((M 0 1:ℂ)-Complex.I*(M 1 1:ℂ))/
        ((M 0 1:ℂ)+Complex.I*(M 1 1:ℂ)) ∧
    (e ⟨1,by simp [Metric.mem_closedBall,dist_zero_right]⟩ : ℂ) =
      ((M 0 0:ℂ)-Complex.I*(M 1 0:ℂ))/
        ((M 0 0:ℂ)+Complex.I*(M 1 0:ℂ)) := by
  let left : Metric.closedBall (0:ℂ) 1 :=
    ⟨-1,by simp [Metric.mem_closedBall,dist_zero_right]⟩
  let right : Metric.closedBall (0:ℂ) 1 :=
    ⟨1,by simp [Metric.mem_closedBall,dist_zero_right]⟩
  have hbot : Tendsto (fun t : ℝ => cayley (verticalPath t)) atBot (𝓝 left) := by
    have h := cayley_vertical_atBot
    change Tendsto (fun t : ℝ => cayley (verticalPath t)) atBot (𝓝 left) at h
    exact h
  have htop : Tendsto (fun t : ℝ => cayley (verticalPath t)) atTop (𝓝 right) := by
    have h := cayley_vertical_atTop
    change Tendsto (fun t : ℝ => cayley (verticalPath t)) atTop (𝓝 right) at h
    exact h
  constructor
  · have h := ((continuous_subtype_val.continuousAt.tendsto).comp
      (e.continuous.continuousAt.tendsto.comp hbot))
    have h' : Tendsto (fun t : ℝ => (cayley (M • verticalPath t) : ℂ))
        atBot (𝓝 (e left:ℂ)) := by simpa only [Function.comp_def,he] using h
    exact tendsto_nhds_unique h' (sl_vertical_cayley_atBot M hd)
  · have h := ((continuous_subtype_val.continuousAt.tendsto).comp
      (e.continuous.continuousAt.tendsto.comp htop))
    have h' : Tendsto (fun t : ℝ => (cayley (M • verticalPath t) : ℂ))
        atTop (𝓝 (e right:ℂ)) := by simpa only [Function.comp_def,he] using h
    exact tendsto_nhds_unique h' (sl_vertical_cayley_atTop M ha)

#print axioms sl_vertical_cayley_formula
#print axioms sl_vertical_cayley_atTop
#print axioms sl_vertical_cayley_atBot
#print axioms sl_disk_extension_endpoint_images

end CurveComplex.Hyperbolic
