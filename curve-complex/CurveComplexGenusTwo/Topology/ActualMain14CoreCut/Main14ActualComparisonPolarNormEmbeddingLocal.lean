import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenToConstructedCommonPairLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies

-- An actual compact polar band, used only for transporting the SAME model traces.
example : ∃ P : C(Circle × Interval,Plane), Topology.IsEmbedding P ∧
    ∀ p, ‖P p‖=1+(p.2:ℝ) := by
  audit_main14_base3
    let f : C(Circle × Interval,ℂ) :=
      ⟨fun p => (1+(p.2:ℝ)) • (p.1:ℂ),by fun_prop⟩
    let P : C(Circle × Interval,Plane) :=
      ⟨fun p => Plane.mk (f p).re (f p).im,by fun_prop⟩
    have hi : Function.Injective P := by
      rintro ⟨z,u⟩ ⟨w,v⟩ he
      have hf : f (z,u)=f (w,v) := by
        apply Complex.ext
        · exact congrArg (fun x : Plane => x 0) he
        · exact congrArg (fun x : Plane => x 1) he
      have hu : u=v := by
        have hn := congrArg norm hf
        have hr : 0 < 1+(u:ℝ) := by linarith [u.property.1]
        have hs : 0 < 1+(v:ℝ) := by linarith [v.property.1]
        change ‖(1+(u:ℝ)) • (z:ℂ)‖ = ‖(1+(v:ℝ)) • (w:ℂ)‖ at hn
        simp only [norm_smul,Circle.norm_coe,mul_one,Real.norm_eq_abs,
          abs_of_pos hr,abs_of_pos hs] at hn
        apply Subtype.ext
        linarith
      subst v
      have hr : (1+(u:ℝ)) ≠ 0 := by linarith [u.property.1]
      have hz : (z:ℂ)=(w:ℂ) := by
        have hh := congrArg (fun x : ℂ => (1+(u:ℝ))⁻¹ • x) hf
        change (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (z:ℂ)) =
          (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (w:ℂ)) at hh
        simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hh
      exact Prod.ext (Subtype.ext hz) rfl
    refine ⟨P,(P.continuous.isClosedEmbedding hi).isEmbedding,?_⟩
    intro p
    have hn : ‖P p‖ ^ 2=‖f p‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq,Complex.sq_norm]
      simp [P,Fin.sum_univ_two,Complex.normSq_apply,pow_two]
    have hr : 0 < 1+(p.2:ℝ) := by linarith [p.2.property.1]
    have hf : ‖f p‖=1+(p.2:ℝ) := by
      change ‖(1+(p.2:ℝ)) • (p.1:ℂ)‖=1+(p.2:ℝ)
      rw [norm_smul,Circle.norm_coe,mul_one,Real.norm_eq_abs,abs_of_pos hr]
    rw [hf] at hn
    nlinarith [norm_nonneg (P p)]
end CurveComplex.HyperellipticModel
