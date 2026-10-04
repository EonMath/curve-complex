import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalPuncturedSourceDefinitions
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleProjectionEssential
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology
/-- A literal translated primitive winding parameter proves essentiality of
the actual target curve; no essentiality certificate is supplied. -/
theorem actual_translated_primitive_parameter_proves_essential
    (c : Curve (Circle×Circle)) (a : Circle×Circle) (m n : ℤ)
    (hgcd : m.gcd n=1) (hparam : ∀ z,c.map z=a*torusWindingMap m n z) : Essential c := by
  let u := Int.gcdA m n
  let v := Int.gcdB m n
  have hbez : m*u+n*v=1 := by
    have hh := Int.gcd_eq_gcd_ab m n
    rw [hgcd] at hh
    exact hh.symm
  let χ : C(Circle×Circle,Circle) :=
    ⟨fun w => (a.1⁻¹*w.1)^u*(a.2⁻¹*w.2)^v,by fun_prop⟩
  apply actual_circle_projected_curve_is_essential c χ
  intro z
  change (a.1⁻¹*(c.map z).1)^u*(a.2⁻¹*(c.map z).2)^v=z
  rw [hparam]
  simp only [Prod.fst_mul,Prod.snd_mul,torusWindingMap,← mul_assoc,inv_mul_cancel,mul_one,one_mul]
  rw [← zpow_mul,← zpow_mul,← zpow_add,hbez,zpow_one]
/-- The explicit translated primitive target parameter supplies an actual
original winding lift, including the FULL integer period law. -/
theorem actual_translated_primitive_parameter_has_literal_deck_lift
    (c : Curve (Circle×Circle)) (a : Circle×Circle) (m n : ℤ)
    (hparam : ∀ z,c.map z=a*torusWindingMap m n z) :
    ∃ F : C(ℝ,ℝ×ℝ),
      (∀ x,(Circle.exp (F x).1,Circle.exp (F x).2)=c.map (Circle.exp x)) ∧
      (∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=
        ((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi),(F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi))) := by
  obtain ⟨α,hα⟩ := Circle.exp_surjective a.1
  obtain ⟨β,hβ⟩ := Circle.exp_surjective a.2
  let F : C(ℝ,ℝ×ℝ) := ⟨fun x => (α+(m:ℝ)*x,β+(n:ℝ)*x),by fun_prop⟩
  refine ⟨F,?_,?_⟩
  · intro x
    rw [hparam]
    apply Prod.ext
    · change Circle.exp (α+(m:ℝ)*x)=a.1*(Circle.exp x)^m
      rw [Circle.exp_add,hα]
      simpa only [zsmul_eq_mul] using congrArg (a.1*·) (Circle.exp_zsmul x m)
    · change Circle.exp (β+(n:ℝ)*x)=a.2*(Circle.exp x)^n
      rw [Circle.exp_add,hβ]
      simpa only [zsmul_eq_mul] using congrArg (a.2*·) (Circle.exp_zsmul x n)
  · intro k x
    apply Prod.ext <;> change _=_ <;> dsimp [F] <;> ring
#print axioms actual_translated_primitive_parameter_proves_essential
#print axioms actual_translated_primitive_parameter_has_literal_deck_lift
