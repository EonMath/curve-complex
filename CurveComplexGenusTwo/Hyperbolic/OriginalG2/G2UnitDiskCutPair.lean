import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Topology.ArcStraightening
import Mathlib

namespace CurveComplex.Hyperbolic

open Set Topology Schoenflies CurveComplex.LocalSurgery

theorem g2_unit_circle_jordan : IsJordanCurve (Metric.sphere (0:Plane) 1) := by
  let r : C(Circle,Plane) := ⟨fun z => actualComplexSchoenflies (z : ℂ),
    actualComplexSchoenflies.continuous.comp continuous_subtype_val⟩
  have hr : IsEmbedding r :=
    actualComplexSchoenflies.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal
  have h := CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
  have heq : Set.range r = Metric.sphere (0:Plane) 1 := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      change dist (actualComplexSchoenflies (z:ℂ)) 0 = 1
      rw [dist_zero_right,actualComplexSchoenflies_norm]
      exact Circle.norm_coe z
    · intro hx
      have hnorm : ‖actualComplexSchoenflies.symm x‖ = 1 := by
        rw [← actualComplexSchoenflies_norm,actualComplexSchoenflies.apply_symm_apply]
        simpa only [Metric.mem_sphere,dist_zero_right] using hx
      let z : Circle := ⟨actualComplexSchoenflies.symm x,
        by
          change actualComplexSchoenflies.symm x ∈ Metric.sphere (0:ℂ) 1
          change dist (actualComplexSchoenflies.symm x) 0 = 1
          simpa only [dist_zero_right] using hnorm⟩
      exact ⟨z,actualComplexSchoenflies.apply_symm_apply x⟩
  rwa [heq] at h

theorem g2_unit_disk_inside :
    inside (Metric.sphere (0:Plane) 1) = Metric.ball (0:Plane) 1 := by
  have hsub : Metric.ball (0:Plane) 1 ⊆
      (Metric.sphere (0:Plane) 1)ᶜ := by
    intro x hx hs
    exact (ne_of_lt (Metric.mem_ball.mp hx)) (Metric.mem_sphere.mp hs)
  have hfr : frontier (Metric.ball (0:Plane) 1) ∩
      (Metric.sphere (0:Plane) 1)ᶜ = ∅ := by
    rw [frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0)]
    exact Set.inter_compl_self _
  have hzero : (0:Plane) ∈ Metric.ball (0:Plane) 1 := by simp
  have hcomp := Plane.connectedComponentIn_eq_of_frontier_disjoint
    Metric.isOpen_ball (convex_ball (0:Plane) 1).isPreconnected hsub hfr hzero
  have hinside : (0:Plane) ∈ inside (Metric.sphere (0:Plane) 1) := by
    refine ⟨hsub hzero,?_⟩
    rw [hcomp]
    exact Metric.isBounded_ball
  exact ((jordan_curve_theorem g2_unit_circle_jordan).connectedComponentIn_eq_inside
    hinside).symm.trans hcomp

theorem g2_embedded_interval_isArc (f : C(unitInterval,ℂ))
    (hf : IsEmbedding f) :
    IsArcBetween (actualComplexSchoenflies '' Set.range f)
      (actualComplexSchoenflies (f 0)) (actualComplexSchoenflies (f 1)) := by
  let g : ℝ → Plane := fun r => actualComplexSchoenflies (f (Set.projIcc 0 1 zero_le_one r))
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · exact (actualComplexSchoenflies.continuous.comp
      (f.continuous.comp continuous_projIcc)).continuousOn
  · intro x hx y hy h
    have he := hf.injective (actualComplexSchoenflies.injective h)
    have hx' : (Set.projIcc 0 1 zero_le_one x : ℝ) = x := by
      simp [Set.projIcc_of_mem zero_le_one hx]
    have hy' : (Set.projIcc 0 1 zero_le_one y : ℝ) = y := by
      simp [Set.projIcc_of_mem zero_le_one hy]
    simpa only [hx',hy'] using congrArg Subtype.val he
  · ext z
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨f (Set.projIcc 0 1 zero_le_one r), ⟨_,rfl⟩,rfl⟩
    · rintro ⟨_,⟨r,rfl⟩,rfl⟩
      refine ⟨r.val,r.property,?_⟩
      simp [g,Set.projIcc_of_mem zero_le_one r.property]
  · simp [g,Set.projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc 0 1 by simp)]
  · simp [g,Set.projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc 0 1 by simp)]

private theorem g2_arc_homeomorph_image (e : Plane ≃ₜ Plane)
    {A : Set Plane} {a b : Plane} (h : IsArcBetween A a b) :
    IsArcBetween (e '' A) (e a) (e b) := by
  obtain ⟨f,hc,hi,hr,h0,h1⟩ := h
  refine ⟨e ∘ f,e.continuous.comp_continuousOn hc,?_,?_,?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (e.injective he)
  · rw [Set.image_comp,hr]
  · simpa only [Function.comp_def,h0]
  · simpa only [Function.comp_def,h1]

theorem g2_upper_semicircle_arc : IsArcBetween
    (actualComplexSchoenflies '' {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im})
    (actualComplexSchoenflies (-1:ℂ))
    (actualComplexSchoenflies (1:ℂ)) := by
  let f : C(unitInterval,ℂ) :=
    ⟨fun t => ((2*(t:ℝ)-1:ℝ):ℂ)+Complex.I*(Real.sqrt (1-(2*(t:ℝ)-1)^2):ℂ),by fun_prop⟩
  have hinj : Function.Injective f := by
    intro s t h
    have hr := congrArg Complex.re h
    simp [f] at hr
    apply Subtype.ext
    linarith
  have hf : IsEmbedding f := (f.continuous.isClosedEmbedding hinj).isEmbedding
  have hrange : Set.range f = {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ z.im} := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      have hx : 0 ≤ 1-(2*(t:ℝ)-1)^2 := by
        have hm := mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)
        nlinarith
      have hs := Real.sq_sqrt hx
      have hn : ‖f t‖^2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
        simp [f]
        nlinarith
      constructor
      · nlinarith [norm_nonneg (f t)]
      · simp [f,Real.sqrt_nonneg]
    · rintro ⟨hn,hi⟩
      have hre : |z.re| ≤ 1 := by simpa only [hn] using Complex.abs_re_le_norm z
      let t : unitInterval := ⟨(z.re+1)/2,by constructor <;> linarith [abs_le.mp hre]⟩
      refine ⟨t,?_⟩
      have hzsq : z.re^2+z.im^2=1 := by
        have hh : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hn]; norm_num
        simpa only [Complex.normSq_apply,pow_two] using hh
      have hroot : Real.sqrt (1-z.re^2)=z.im := by
        rw [show 1-z.re^2=z.im^2 by linarith,Real.sqrt_sq_eq_abs,abs_of_nonneg hi]
      apply Complex.ext
      · simp [f,t]
        ring
      · have he : 2*((z.re+1)/2)-1=z.re := by ring
        simpa only [f,ContinuousMap.coe_mk,t,Complex.add_im,Complex.ofReal_im,
          Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,zero_add,
          one_mul,he] using hroot
  have h0 : f 0=(-1:ℂ) := by simp [f]
  have h1 : f 1=(1:ℂ) := by norm_num [f]
  simpa only [hrange,h0,h1] using g2_embedded_interval_isArc f hf

theorem g2_lower_semicircle_arc : IsArcBetween
    (actualComplexSchoenflies '' {z : ℂ | ‖z‖ = 1 ∧ z.im ≤ 0})
    (actualComplexSchoenflies (-1:ℂ))
    (actualComplexSchoenflies (1:ℂ)) := by
  let e : Plane ≃ₜ Plane := actualComplexSchoenflies.symm.toHomeomorph.trans
    (Complex.conjCLE.toHomeomorph.trans actualComplexSchoenflies.toHomeomorph)
  have he (z : ℂ) : e (actualComplexSchoenflies z) = actualComplexSchoenflies (star z) := by
    simp [e,Homeomorph.trans_apply,Complex.conjCLE_apply,Complex.star_def]
  have himage : e '' (actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im}) =
      actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0} := by
    ext z
    constructor
    · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
      rw [he]
      refine ⟨star w,⟨?_,?_⟩,rfl⟩
      · simpa only [norm_star] using hw.1
      · simpa [Complex.star_def] using neg_nonpos.mpr hw.2
    · rintro ⟨w,hw,rfl⟩
      refine ⟨actualComplexSchoenflies (star w),?_,?_⟩
      · refine ⟨star w,⟨?_,?_⟩,rfl⟩
        · simpa only [norm_star] using hw.1
        · simpa [Complex.star_def] using neg_nonneg.mpr hw.2
      · rw [he,star_star]
  have h := g2_arc_homeomorph_image e g2_upper_semicircle_arc
  rw [himage,he,he] at h
  simpa using h

theorem g2_unit_circle_cut_pair : IsCutPair (Metric.sphere (0:Plane) 1)
    (actualComplexSchoenflies (-1:ℂ)) (actualComplexSchoenflies (1:ℂ))
    (actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ 0 ≤ z.im})
    (actualComplexSchoenflies '' {z : ℂ | ‖z‖=1 ∧ z.im ≤ 0}) := by
  refine ⟨g2_upper_semicircle_arc,g2_lower_semicircle_arc,?_,?_⟩
  · ext z
    constructor
    · rintro (⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩) <;>
        simpa only [Metric.mem_sphere,dist_zero_right,actualComplexSchoenflies_norm] using hw.1
    · intro hz
      let w := actualComplexSchoenflies.symm z
      have hn : ‖w‖=1 := by
        rw [← actualComplexSchoenflies_norm]
        simpa only [w,actualComplexSchoenflies.apply_symm_apply,Metric.mem_sphere,dist_zero_right] using hz
      rcases le_total 0 w.im with hi | hi
      · exact Or.inl ⟨w,⟨hn,hi⟩,actualComplexSchoenflies.apply_symm_apply z⟩
      · exact Or.inr ⟨w,⟨hn,hi⟩,actualComplexSchoenflies.apply_symm_apply z⟩
  · ext z
    constructor
    · rintro ⟨⟨w,hw,rfl⟩,⟨v,hv,hvw⟩⟩
      have heq := actualComplexSchoenflies.injective hvw
      subst v
      have him : w.im=0 := le_antisymm hv.2 hw.2
      have hsq : w.re^2=1 := by
        have hn : Complex.normSq w=1 := by rw [Complex.normSq_eq_norm_sq,hw.1]; norm_num
        simp only [Complex.normSq_apply,him,mul_zero,add_zero] at hn
        simpa only [pow_two] using hn
      rcases (sq_eq_one_iff.mp hsq) with hr | hr
      · right
        have hw1 : w=(1:ℂ) := by apply Complex.ext <;> simp [hr,him]
        simp [hw1]
      · left
        have hw1 : w=(-1:ℂ) := by apply Complex.ext <;> simp [hr,him]
        simp [hw1]
    · intro hz
      rcases hz with hz | hz
      · rw [hz]
        constructor <;> exact ⟨-1,by simp,rfl⟩
      · have hz1 : z=actualComplexSchoenflies (1:ℂ) := by simpa using hz
        rw [hz1]
        constructor <;> exact ⟨1,by simp,rfl⟩

#print axioms g2_unit_circle_cut_pair

end CurveComplex.Hyperbolic
