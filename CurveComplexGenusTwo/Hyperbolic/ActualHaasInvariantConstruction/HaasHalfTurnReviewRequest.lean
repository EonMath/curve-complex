import CurveComplexGenusTwo.Hyperbolic.Stabilizer
open scoped UpperHalfPlane MatrixGroups
open Matrix
namespace CurveComplex.Hyperbolic

/-- The actual normalized half-turn used in Haas–Susskind Lemma1;
its action is involutive and its unique fixed point is the midpoint normal form I. -/
theorem hyperbolic_normalized_half_turn :
    let J : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
    Function.Involutive (fun z : UpperHalfPlane => J • z) ∧
      ∀ z : UpperHalfPlane, J • z = z ↔ z = UpperHalfPlane.I := by
 dsimp only
 let J : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
 have hact (z : UpperHalfPlane) : ((J • z : UpperHalfPlane) : ℂ) = -1 / (z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [J, UpperHalfPlane.num, UpperHalfPlane.denom]
 have hz (z : UpperHalfPlane) : (z : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  exact z.im_pos.ne' (by simpa using hi)
 constructor
 · intro z
   apply UpperHalfPlane.coe_injective
   rw [hact, hact]
   field_simp [hz z]
 · intro z
   constructor
   · intro hf
     have he : -1 / (z : ℂ) = (z : ℂ) := by rw [← hact, hf]
     have heq := (div_eq_iff (hz z)).mp he
     have hre := congrArg Complex.re heq
     have him := congrArg Complex.im heq
     simp [Complex.mul_re, Complex.mul_im] at hre him
     have hr : z.re = 0 := by nlinarith [z.im_pos]
     have hi : z.im = 1 := by nlinarith [z.im_pos]
     apply UpperHalfPlane.ext_re_im <;> simp [hr, hi]
   · rintro rfl
     apply UpperHalfPlane.coe_injective
     rw [hact]
     simp

/-- Moving the normalized half-turn to an actual point by an actual plane
isometry retains its involution and exact fixed-point description. -/
theorem hyperbolic_half_turn_at_point (p : UpperHalfPlane) :
    let J : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
    let e : UpperHalfPlane ≃ᵢ UpperHalfPlane := IsometryEquiv.constSMul p.toSL2R
    Function.Involutive (fun z => e (J • e.symm z)) ∧
      ∀ z, e (J • e.symm z) = z ↔ z = p := by
  dsimp only
  let J : SL(2, ℝ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  let F : UpperHalfPlane → UpperHalfPlane := fun z => J • z
  have hF : Function.Involutive F := hyperbolic_normalized_half_turn.1
  have hfix : ∀ z, F z = z ↔ z = UpperHalfPlane.I := hyperbolic_normalized_half_turn.2
  let e : UpperHalfPlane ≃ᵢ UpperHalfPlane := IsometryEquiv.constSMul p.toSL2R
  have he : e UpperHalfPlane.I = p := p.toSL2R_smul_I
  constructor
  · intro z
    change e (F (e.symm (e (F (e.symm z)))) ) = z
    rw [e.symm_apply_apply, hF, e.apply_symm_apply]
  · intro z
    change e (F (e.symm z)) = z ↔ z = p
    constructor
    · intro h
      have hh : F (e.symm z) = e.symm z := by
        simpa using congrArg e.symm h
      have hz := (hfix (e.symm z)).mp hh
      have ht := congrArg e hz
      simpa [he] using ht
    · intro hzp
      rw [hzp]
      have hp : e.symm p = UpperHalfPlane.I := by rw [← he, e.symm_apply_apply]
      rw [hp, (hfix UpperHalfPlane.I).mpr rfl, he]

end CurveComplex.Hyperbolic
