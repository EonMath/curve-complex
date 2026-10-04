import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasHalfTurnReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasNormalizedBoundaryGeometryReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasSourceBridges.PantsAlgebra
open Set Topology Matrix
open scoped MatrixGroups UpperHalfPlane
namespace CurveComplex.Hyperbolic
set_option maxHeartbeats 2000000
theorem actual_normalized_boundary_orbit_hull_center_interior (d L : ℝ) (hd : 0 < d) :
    let D : ℝ → SL(2,ℝ) := fun s =>
      ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
    let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
    let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
    let A := D (-d/2)*R*D L*R⁻¹*D (d/2)
    let B := D (d/2)*R*D (-L)*R⁻¹*D (-d/2)
    let Γ := Subgroup.closure ({A,B}:Set SL(2,ℝ))
    let axes := Set.range (fun t : ℝ => D (-d/2) • (R • verticalPath t)) ∪
      Set.range (fun t : ℝ => D (d/2) • (R • verticalPath t))
    let seed := {z : H2 | ∃ g : SL(2,ℝ), g∈Γ ∧ ∃ x∈axes, z=g • x}
    let Ω := {z : H2 | ∀ C : Set H2, IsClosed C → seed⊆C →
      (∀ x∈C,∀ y∈C,∀ w : H2, dist x w+dist w y=dist x y → w∈C) → z∈C}
    UpperHalfPlane.I∈interior Ω := by
  dsimp only
  let D : ℝ → SL(2,ℝ) := fun s =>
    ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
  let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
  let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
  let A := D (-d/2)*R*D L*R⁻¹*D (d/2)
  let B := D (d/2)*R*D (-L)*R⁻¹*D (-d/2)
  let Γ := Subgroup.closure ({A,B}:Set SL(2,ℝ))
  let a : ℝ → H2 := fun t => D (-d/2) • (R • verticalPath t)
  let b : ℝ → H2 := fun t => D (d/2) • (R • verticalPath t)
  let axes := Set.range a ∪ Set.range b
  let seed := {z : H2 | ∃ g : SL(2,ℝ), g∈Γ ∧ ∃ x∈axes, z=g • x}
  let Ω := {z : H2 | ∀ C : Set H2, IsClosed C → seed⊆C →
    (∀ x∈C,∀ y∈C,∀ w : H2, dist x w+dist w y=dist x y → w∈C) → z∈C}
  have hcircle (s : ℝ) (z : H2) (hz : z.re^2+z.im^2=(Real.exp s)^2) :
      ∃ t : ℝ,D s • (R • verticalPath t)=z := by
    let D : ℝ → SL(2,ℝ) := fun s =>
      ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
    let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
    have hunit (u : H2) (hu : u.re^2+u.im^2=1) :
        ∃ t : ℝ,R • verticalPath t=u := by
      let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
      let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
      have hJv (t : ℝ) : J • verticalPath t=verticalPath (-t) := by
        apply UpperHalfPlane.coe_injective
        rw [UpperHalfPlane.coe_specialLinearGroup_apply]
        simp [J,verticalPath,UpperHalfPlane.num,UpperHalfPlane.denom]
        apply Complex.ext
        · simp [Complex.div_re,Complex.normSq_apply]
        · simp [Complex.div_im,Complex.normSq_apply,Real.exp_neg]
          field_simp [Real.exp_ne_zero]
      have hRinv : R⁻¹=R*J := by
        apply Subtype.ext
        change (R⁻¹).val=(R*J).val
        simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.SpecialLinearGroup.coe_mul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [R,J,stabilizerRotation,Matrix.SpecialLinearGroup.coe_inv,
            Matrix.adjugate_fin_two,Matrix.SpecialLinearGroup.coe_mul,
            Matrix.mul_apply,Fin.sum_univ_two] <;> ring
      let v := R • u
      have hvre : v.re=0 := by
        change (R • u : H2).re=0
        change ((R • u : H2):ℂ).re=0
        rw [stabilizerRotation_coe_smul]
        simp only [Complex.ofReal_one,one_mul,neg_mul,Complex.div_re,Complex.add_re,
          Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im]
        have hz : (u.re+1)*(-u.re+1)+(u.im+0)*(-u.im+0)=0 := by nlinarith [hu]
        simp only [UpperHalfPlane.re,UpperHalfPlane.im] at hu hz
        rw [←add_div,hz]
        simp
      have hv : v=verticalPath (Real.log v.im) := by
        apply UpperHalfPlane.ext_re_im
        · simpa [verticalPath] using hvre
        · simp [verticalPath,Real.exp_log v.im_pos]
      refine ⟨-Real.log v.im,?_⟩
      rw [←hJv,←mul_smul,←hRinv,←hv]
      exact inv_smul_smul R u
    have hscale (s : ℝ) (z : H2) : ((D s • z : H2):ℂ)=(Real.exp s : ℂ)*z := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [D,UpperHalfPlane.num,UpperHalfPlane.denom]
      rw [div_eq_mul_inv,←Complex.exp_neg]
      simp only [neg_neg]
      rw [mul_right_comm,←Complex.exp_add]
      congr 2
      ring
    let u := D (-s) • z
    have hu : u.re^2+u.im^2=1 := by
      suffices hh : Complex.normSq (u:ℂ)=1 by simpa [Complex.normSq_apply,pow_two] using hh
      change Complex.normSq ((D (-s) • z : H2):ℂ)=1
      rw [hscale,Complex.normSq_mul,Complex.normSq_ofReal]
      have hz' : Complex.normSq (z:ℂ)=(Real.exp s)^2 := by simpa [Complex.normSq_apply,pow_two] using hz
      rw [hz',Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    obtain ⟨t,ht⟩ := hunit u hu
    refine ⟨t,?_⟩
    rw [ht]
    apply UpperHalfPlane.coe_injective
    change ((D s • (D (-s) • z) : H2):ℂ)=(z:ℂ)
    rw [hscale,hscale,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add]
    simp
  have hinterior (C : Set H2) (r₁ r₂ : ℝ) (hr₁ : 0<r₁) (hr₁one : r₁<1) (hr₂ : 1<r₂)
      (hconv : ∀ a∈C,∀ b∈C,∀ z : H2,dist a z+dist z b=dist a b → z∈C)
      (h₁ : ∀ z : H2,z.re^2+z.im^2=r₁^2 → z∈C)
      (h₂ : ∀ z : H2,z.re^2+z.im^2=r₂^2 → z∈C) : UpperHalfPlane.I∈interior C := by
    let V : Set H2 := {z | |z.re|<r₁ ∧ r₁^2<z.re^2+z.im^2 ∧ z.re^2+z.im^2<r₂^2}
    have hV : IsOpen V := by
      have hr : Continuous (fun z : H2 => |z.re|) := by fun_prop
      have hn : Continuous (fun z : H2 => z.re^2+z.im^2) := by fun_prop
      exact (isOpen_lt hr continuous_const).inter ((isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const))
    have hIV : UpperHalfPlane.I∈V := by
      change |0|<r₁ ∧ r₁^2<0^2+1^2 ∧ 0^2+1^2<r₂^2
      simp only [abs_zero,zero_pow,one_pow,zero_add]
      constructor
      · exact hr₁
      · constructor <;> nlinarith
    have hVC : V⊆C := by
      intro z hz
      have hx : z.re^2<r₁^2 := by
        have habs := hz.1
        nlinarith [sq_abs z.re,abs_nonneg z.re]
      have hp₁ : 0<r₁^2-z.re^2 := sub_pos.mpr hx
      have hp₂ : 0<r₂^2-z.re^2 := by nlinarith [hz.2.2,z.im_pos]
      let a : H2 := ⟨⟨z.re,Real.sqrt (r₁^2-z.re^2)⟩,Real.sqrt_pos.mpr hp₁⟩
      let b : H2 := ⟨⟨z.re,Real.sqrt (r₂^2-z.re^2)⟩,Real.sqrt_pos.mpr hp₂⟩
      have ha2 : a.im^2=r₁^2-z.re^2 := Real.sq_sqrt hp₁.le
      have hb2 : b.im^2=r₂^2-z.re^2 := Real.sq_sqrt hp₂.le
      have ha : a∈C := h₁ a (by change z.re^2+a.im^2=r₁^2;linarith)
      have hb : b∈C := h₂ b (by change z.re^2+b.im^2=r₂^2;linarith)
      have hay : a.im≤z.im := by nlinarith [a.im_pos,z.im_pos,hz.2.1]
      have hyb : z.im≤b.im := by nlinarith [b.im_pos,z.im_pos,hz.2.2]
      have hla : Real.log a.im≤Real.log z.im := Real.log_le_log a.im_pos hay
      have hlb : Real.log z.im≤Real.log b.im := Real.log_le_log z.im_pos hyb
      apply hconv a ha b hb z
      rw [UpperHalfPlane.dist_of_re_eq (by rfl : a.re=z.re),
        UpperHalfPlane.dist_of_re_eq (by rfl : z.re=b.re),
        UpperHalfPlane.dist_of_re_eq (by rfl : a.re=b.re)]
      simp only [Real.dist_eq]
      rw [abs_of_nonpos (by linarith : Real.log a.im-Real.log z.im≤0),
        abs_of_nonpos (by linarith : Real.log z.im-Real.log b.im≤0),
        abs_of_nonpos (by linarith : Real.log a.im-Real.log b.im≤0)]
      ring
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hV.mem_nhds hIV) hVC)
  have hconv : ∀ x∈Ω,∀ y∈Ω,∀ w : H2,dist x w+dist w y=dist x y → w∈Ω := by
    intro x hx y hy w hw Q hQ hs hCQ
    exact hCQ x (hx Q hQ hs hCQ) y (hy Q hQ hs hCQ) w hw
  have h₁ (z : H2) (hz : z.re^2+z.im^2=(Real.exp (-d/2))^2) : z∈Ω := by
    obtain ⟨t,ht⟩ := hcircle (-d/2) z hz
    intro Q hQ hs hCQ
    apply hs
    exact ⟨1,Γ.one_mem,z,Or.inl ⟨t,ht⟩,by simp⟩
  have h₂ (z : H2) (hz : z.re^2+z.im^2=(Real.exp (d/2))^2) : z∈Ω := by
    obtain ⟨t,ht⟩ := hcircle (d/2) z hz
    intro Q hQ hs hCQ
    apply hs
    exact ⟨1,Γ.one_mem,z,Or.inr ⟨t,ht⟩,by simp⟩
  exact hinterior Ω (Real.exp (-d/2)) (Real.exp (d/2)) (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by linarith)) (Real.one_lt_exp_iff.mpr (by linarith)) hconv h₁ h₂

end CurveComplex.Hyperbolic
