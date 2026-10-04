import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Topology.PrimitiveEssential
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
/-- The actual original homotopy-to-winding hypothesis constructs its literal
parametrized deck lift with that EXACT winding; no lift certificate is assumed. -/
theorem actual_homotopic_winding_source_has_exact_deck_lift
    (c : Curve (Circle×Circle)) (m n : ℤ)
    (hh : (⟨c.map,c.embedded.continuous⟩ : C(Circle,Circle×Circle)).Homotopic
      ⟨torusWindingMap m n,continuous_torusWindingMap m n⟩) :
    ∃ F : C(ℝ,ℝ×ℝ),
      (∀ x,(Circle.exp (F x).1,Circle.exp (F x).2)=c.map (Circle.exp x)) ∧
      (∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=
        ((F x).1+(k:ℝ)*(m:ℝ)*(2*Real.pi),(F x).2+(k:ℝ)*(n:ℝ)*(2*Real.pi))) := by
  obtain ⟨J⟩ := hh
  let H := J.symm
  let f : C(CurveComplex.Interval×ℝ,Circle×Circle) := ⟨fun tx => H (tx.1,Circle.exp tx.2),by fun_prop⟩
  let f₁ : C(CurveComplex.Interval×ℝ,Circle) := ⟨fun tx => (f tx).1,by fun_prop⟩
  let f₂ : C(CurveComplex.Interval×ℝ,Circle) := ⟨fun tx => (f tx).2,by fun_prop⟩
  let F₁ : C(ℝ,ℝ) := ⟨fun x => (m:ℝ)*x,by fun_prop⟩
  let F₂ : C(ℝ,ℝ) := ⟨fun x => (n:ℝ)*x,by fun_prop⟩
  have hzero₁ (x : ℝ) : f₁ (⟨0,by norm_num⟩,x)=Circle.exp (F₁ x) := by
    change (H (0,Circle.exp x)).1=Circle.exp ((m:ℝ)*x)
    rw [H.apply_zero]
    simpa only [ContinuousMap.coe_mk,torusWindingMap,zsmul_eq_mul] using (Circle.exp_zsmul x m).symm
  have hzero₂ (x : ℝ) : f₂ (⟨0,by norm_num⟩,x)=Circle.exp (F₂ x) := by
    change (H (0,Circle.exp x)).2=Circle.exp ((n:ℝ)*x)
    rw [H.apply_zero]
    simpa only [ContinuousMap.coe_mk,torusWindingMap,zsmul_eq_mul] using (Circle.exp_zsmul x n).symm
  have hfperiod (t : CurveComplex.Interval) (k : ℤ) (x : ℝ) : f (t,x+(k:ℝ)*(2*Real.pi))=f (t,x) := by
    change H (t,Circle.exp (x+(k:ℝ)*(2*Real.pi)))=H (t,Circle.exp x)
    rw [Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
  obtain ⟨A₁,hA₁,_,hAp₁⟩ := actual_circle_source_homotopy_retains_integer_winding f₁ F₁ m
    hzero₁ (fun t k x => congrArg Prod.fst (hfperiod t k x))
    (by intro k x; change (m:ℝ)*(x+(k:ℝ)*(2*Real.pi))=(m:ℝ)*x+((k*m:ℤ):ℝ)*(2*Real.pi); push_cast; ring)
  obtain ⟨A₂,hA₂,_,hAp₂⟩ := actual_circle_source_homotopy_retains_integer_winding f₂ F₂ n
    hzero₂ (fun t k x => congrArg Prod.snd (hfperiod t k x))
    (by intro k x; change (n:ℝ)*(x+(k:ℝ)*(2*Real.pi))=(n:ℝ)*x+((k*n:ℤ):ℝ)*(2*Real.pi); push_cast; ring)
  let F : C(ℝ,ℝ×ℝ) := ⟨fun x => (A₁ (⟨1,by norm_num⟩,x),A₂ (⟨1,by norm_num⟩,x)),by fun_prop⟩
  refine ⟨F,?_,?_⟩
  · intro x
    change (Circle.exp (A₁ (⟨1,by norm_num⟩,x)),Circle.exp (A₂ (⟨1,by norm_num⟩,x)))=_
    rw [hA₁,hA₂]
    exact H.apply_one (Circle.exp x)
  · intro k x
    apply Prod.ext
    · simpa only [F,ContinuousMap.coe_mk,Int.cast_mul,mul_assoc] using hAp₁ ⟨1,by norm_num⟩ k x
    · simpa only [F,ContinuousMap.coe_mk,Int.cast_mul,mul_assoc] using hAp₂ ⟨1,by norm_num⟩ k x
#print axioms actual_homotopic_winding_source_has_exact_deck_lift
