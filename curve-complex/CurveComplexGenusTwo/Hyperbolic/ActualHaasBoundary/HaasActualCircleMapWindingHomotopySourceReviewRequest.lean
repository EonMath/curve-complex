import CurveComplexGenusTwo.Topology.PrimitiveEssential
open Set Topology
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
theorem actual_circle_map_winding_homotopy_source (f : C(Circle,Circle)) :
    ∃n : ℤ,f.Homotopic ⟨fun z => z^n,continuous_zpow n⟩ := by
  let g : C(ℝ,Circle) := ⟨fun t => f (Circle.exp t),f.continuous.comp Circle.exp.continuous⟩
  obtain ⟨a,ha⟩ := Circle.exp_surjective (g 0)
  obtain ⟨F,hF,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 a ha
  have hFl (t : ℝ) : Circle.exp (F t)=f (Circle.exp t) := congrFun hF.2 t
  have hbase : Circle.exp (F (2*Real.pi))=Circle.exp (F 0) := by
    rw [hFl,hFl,Circle.exp_two_pi,Circle.exp_zero]
  obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hbase
  have hp : ∀t : ℝ,F (t+2*Real.pi)=F t+(n:ℝ)*(2*Real.pi) := by
    have heq : (fun t : ℝ => F (t+2*Real.pi))=
        (fun t : ℝ => F t+(n:ℝ)*(2*Real.pi)) := by
      refine Circle.isCoveringMap_exp.eq_of_comp_eq
        (F.continuous.comp (continuous_id.add continuous_const))
        (F.continuous.add continuous_const) ?_ 0 ?_
      · funext t
        change Circle.exp (F (t+2*Real.pi))=Circle.exp (F t+(n:ℝ)*(2*Real.pi))
        rw [hFl,Circle.exp_add_two_pi,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one,hFl]
      · simpa only [zero_add] using hn
    exact fun t => congrFun heq t
  exact ⟨n,circle_map_homotopic_winding_of_lift f n F hFl hp⟩
