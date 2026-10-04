import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEssentialMarkedFinitePosition
import Mathlib.Topology.Homotopy.Lifting

open Set Topology Schoenflies CurveComplex

/-- Lift an actual source homotopy starting at its original lift. Covering
uniqueness proves that its original integer winding is retained at every time. -/
theorem actual_circle_source_homotopy_retains_integer_winding
    (H : C(Interval×ℝ,Circle)) (F : C(ℝ,ℝ)) (a : ℤ)
    (hzero : ∀ x, H (⟨0,by norm_num⟩,x)=Circle.exp (F x))
    (hHperiod : ∀ t (k : ℤ) x,
      H (t,x+(k:ℝ)*(2*Real.pi))=H (t,x))
    (hFperiod : ∀ (k : ℤ) x,
      F (x+(k:ℝ)*(2*Real.pi))=F x+((k*a:ℤ):ℝ)*(2*Real.pi)) :
    ∃ A : C(Interval×ℝ,ℝ),
      (∀ t x, Circle.exp (A (t,x))=H (t,x)) ∧
      (∀ x, A (⟨0,by norm_num⟩,x)=F x) ∧
      (∀ t (k : ℤ) x,
        A (t,x+(k:ℝ)*(2*Real.pi))=A (t,x)+((k*a:ℤ):ℝ)*(2*Real.pi)) := by
  let A := Circle.isCoveringMap_exp.liftHomotopy H F hzero
  have hAlift (t : Interval) (x : ℝ) : Circle.exp (A (t,x))=H (t,x) :=
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H F hzero) (t,x)
  have hAzero (x : ℝ) : A (⟨0,by norm_num⟩,x)=F x :=
    Circle.isCoveringMap_exp.liftHomotopy_zero H F hzero x
  refine ⟨A,hAlift,hAzero,?_⟩
  intro t k x
  let L : C(Interval×ℝ,ℝ) := ⟨fun tx => A (tx.1,tx.2+(k:ℝ)*(2*Real.pi)),by fun_prop⟩
  let R : C(Interval×ℝ,ℝ) := ⟨fun tx => A tx+((k*a:ℤ):ℝ)*(2*Real.pi),by fun_prop⟩
  have he : Circle.exp ∘ L=Circle.exp ∘ R := by
    funext tx
    change Circle.exp (A (tx.1,tx.2+(k:ℝ)*(2*Real.pi)))=
      Circle.exp (A tx+((k*a:ℤ):ℝ)*(2*Real.pi))
    rw [hAlift,hHperiod,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
    exact (hAlift tx.1 tx.2).symm
  have hezero : L ((⟨0,by norm_num⟩ : Interval),0)=R ((⟨0,by norm_num⟩ : Interval),0) := by
    change A (⟨0,by norm_num⟩,0+(k:ℝ)*(2*Real.pi))=
      A (⟨0,by norm_num⟩,0)+((k*a:ℤ):ℝ)*(2*Real.pi)
    rw [hAzero,hAzero,hFperiod]
  have heq : L=R := DFunLike.coe_injective
    (Circle.isCoveringMap_exp.eq_of_comp_eq L.continuous R.continuous he
      ((⟨0,by norm_num⟩ : Interval),0) hezero)
  exact congrArg (fun f : C(Interval×ℝ,ℝ) => f (t,x)) heq

#print axioms actual_circle_source_homotopy_retains_integer_winding
