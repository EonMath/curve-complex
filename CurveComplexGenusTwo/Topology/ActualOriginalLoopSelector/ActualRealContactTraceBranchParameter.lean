import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualRealContactTraceSingleBranch
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual contact trace has a constructed positive scalar coordinate on
one fixed old-loop ray, including its zero corner and a normalized terminal
coordinate. This identifies a branch without supplying a branch selector. -/
theorem actual_real_contact_trace_branch_parameter
    (C : C(Icc (0:ℝ) (1/2),ℂ))
    (hzero : C ⟨0,le_rfl,by norm_num⟩=0)
    (hreal : ∀ t,(C t).im=0)
    (hnz : ∀ t,0<t.val → C t≠0) :
    ∃ f : C(Icc (0:ℝ) (1/2),ℝ),
      f ⟨0,le_rfl,by norm_num⟩=0 ∧ f ⟨1/2,by norm_num,le_rfl⟩=1 ∧
      (∀ t,0<t.val → 0<f t) ∧
      (∀ t,C t=(f t) • C ⟨1/2,by norm_num,le_rfl⟩) := by
  let q : Icc (0:ℝ) (1/2) := ⟨1/2,by norm_num,le_rfl⟩
  have hq : (C q).re≠0 := by
    intro h
    apply hnz q (by norm_num [q])
    exact Complex.ext h (hreal q)
  let f : C(Icc (0:ℝ) (1/2),ℝ) := ⟨fun t => (C t).re/(C q).re,by fun_prop⟩
  refine ⟨f,?_,?_,?_,?_⟩
  · change (C ⟨0,le_rfl,by norm_num⟩).re/(C q).re=0
    rw [hzero]; simp
  · exact div_self hq
  · intro t ht
    rcases actual_real_contact_trace_single_branch C hreal hnz with hpos | hneg
    · exact div_pos (hpos t ht) (hpos q (by norm_num [q]))
    · exact div_pos_of_neg_of_neg (hneg t ht) (hneg q (by norm_num [q]))
  · intro t
    apply Complex.ext
    · simp only [Complex.smul_re,smul_eq_mul]
      change (C t).re=((C t).re/(C q).re)*(C q).re
      exact (div_mul_cancel₀ _ hq).symm
    · simp only [Complex.smul_im,smul_eq_mul,hreal,mul_zero]
end CurveComplex.HyperellipticModel
