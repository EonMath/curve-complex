import CurveComplexGenusTwo.Hyperbolic.IdealDiscConcrete

namespace CurveComplex.Hyperbolic

open Filter
open Topology

structure ProperIdealLine (B C : Type*) [TopologicalSpace B] [TopologicalSpace C]
    (D : IdealDisc B C) where
  path : ℝ → H2
  embedding : IsEmbedding path
  minus : B
  plus : B
  distinct : minus ≠ plus
  tends_minus : Tendsto (D.interior ∘ path) atBot (nhds (D.ideal minus))
  tends_plus : Tendsto (D.interior ∘ path) atTop (nhds (D.ideal plus))

structure CompleteGeodesic (B C : Type*) [TopologicalSpace B] [TopologicalSpace C]
    (D : IdealDisc B C) where
  line : ProperIdealLine B C D
  isometry : Isometry line.path

noncomputable def verticalPath (t : ℝ) : H2 :=
  UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)

theorem verticalPath_isometry : Isometry verticalPath :=
  UpperHalfPlane.isometry_vertical_line 0

theorem verticalPath_embedding : IsEmbedding verticalPath :=
  verticalPath_isometry.isEmbedding

theorem cayley_vertical (t : ℝ) :
    (cayley (verticalPath t) : ℂ) =
      (((Real.exp t - 1) / (Real.exp t + 1) : ℝ) : ℂ) := by
  have he : Real.exp t + 1 ≠ 0 := by positivity
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply Complex.ext
  · simp [cayley, verticalPath, Complex.div_re, Complex.normSq_apply]
    rw [Complex.exp_ofReal_re]
  · simp [cayley, verticalPath, Complex.div_im, Complex.normSq_apply]

private theorem verticalRatio_atBot :
    Tendsto (fun t : ℝ => (Real.exp t - 1) / (Real.exp t + 1))
      atBot (nhds (-1 : ℝ)) := by
  convert (Real.tendsto_exp_atBot.sub tendsto_const_nhds).div
    (Real.tendsto_exp_atBot.add tendsto_const_nhds) (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
  · ext t; ring

private theorem verticalRatio_atTop :
    Tendsto (fun t : ℝ => (Real.exp t - 1) / (Real.exp t + 1))
      atTop (nhds (1 : ℝ)) := by
  have htop : Tendsto (fun t : ℝ => Real.exp t + 1) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun t : ℝ => (Real.exp t + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hlim : Tendsto (fun t : ℝ => 1 - 2 * (Real.exp t + 1)⁻¹)
      atTop (nhds (1 - 2 * 0 : ℝ)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  convert hlim using 1
  · ext t
    have hn : Real.exp t + 1 ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

private def verticalMinus : Circle := ⟨(-1 : ℂ), by
  change (-1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1
  norm_num [Metric.mem_sphere, dist_zero_right]⟩

private def verticalPlus : Circle := ⟨(1 : ℂ), by simp⟩

theorem cayley_vertical_atBot :
    Tendsto (standardIdealDisc.interior ∘ verticalPath) atBot
      (nhds (standardIdealDisc.ideal verticalMinus)) := by
  rw [tendsto_subtype_rng]
  change Tendsto (fun t : ℝ => (cayley (verticalPath t) : ℂ)) atBot (nhds (-1 : ℂ))
  simp_rw [cayley_vertical]
  simpa only [Function.comp_def, Complex.ofReal_neg, Complex.ofReal_one] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp verticalRatio_atBot

theorem cayley_vertical_atTop :
    Tendsto (standardIdealDisc.interior ∘ verticalPath) atTop
      (nhds (standardIdealDisc.ideal verticalPlus)) := by
  rw [tendsto_subtype_rng]
  change Tendsto (fun t : ℝ => (cayley (verticalPath t) : ℂ)) atTop (nhds (1 : ℂ))
  simp_rw [cayley_vertical]
  simpa only [Function.comp_def, Complex.ofReal_one] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp verticalRatio_atTop

noncomputable def standardVerticalGeodesic :
    CompleteGeodesic Circle (Metric.closedBall (0 : ℂ) 1) standardIdealDisc where
  line := {
    path := verticalPath
    embedding := verticalPath_embedding
    minus := verticalMinus
    plus := verticalPlus
    distinct := by
      intro h
      have := congrArg Subtype.val h
      norm_num [verticalMinus, verticalPlus] at this
    tends_minus := cayley_vertical_atBot
    tends_plus := cayley_vertical_atTop
  }
  isometry := verticalPath_isometry

end CurveComplex.Hyperbolic
