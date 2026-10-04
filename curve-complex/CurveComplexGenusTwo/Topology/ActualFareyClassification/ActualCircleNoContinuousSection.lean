import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCompatiblePhysicalTerminalFragments

open Set Topology Schoenflies CurveComplex

/-- The ACTUAL exponential circle covering has no continuous global section.
Covering uniqueness on the connected real line forces a section's pullback to
be an affine lift, contradicting its actual periodicity. -/
theorem actual_circle_exp_has_no_continuous_section
    (s : C(Circle,ℝ)) (hs : ∀ z, Circle.exp (s z)=z) : False := by
  let F : C(ℝ,ℝ) := ⟨fun x => s (Circle.exp x),by fun_prop⟩
  let R : C(ℝ,ℝ) := ⟨fun x => x+s 1,by fun_prop⟩
  have hR : Circle.exp ∘ F=Circle.exp ∘ R := by
    funext x
    change Circle.exp (s (Circle.exp x))=Circle.exp (x+s 1)
    rw [hs,Circle.exp_add,hs,mul_one]
  have hZero : F 0=R 0 := by simp [F,R]
  have hFR : F=R := DFunLike.coe_injective
    (Circle.isCoveringMap_exp.eq_of_comp_eq F.continuous R.continuous hR 0 hZero)
  have hPeriod : F (2*Real.pi)=F 0 := by
    change s (Circle.exp (2*Real.pi))=s (Circle.exp 0)
    simp
  rw [hFR] at hPeriod
  change 2*Real.pi+s 1=0+s 1 at hPeriod
  linarith [Real.pi_pos]

#print axioms actual_circle_exp_has_no_continuous_section
