import CurveComplexGenusTwo.Topology.Smoothing.SeedFirstExitDependency

open Set Topology unitInterval
namespace CurveComplex.SeedProbeHeaders

theorem embedded_first_exit_prefix {X : Type*} [TopologicalSpace X] {o a : X}
    (α : Path o a) (hα : Function.Injective α)
    (U : Set X) (hU : IsOpen U) (ho : o ∈ U) (ha : a ∉ U) :
    ∃ (c : I) (hc : 0 < c) (γ : Path o (α c)),
      α c ∈ frontier U ∧ Function.Injective γ ∧
      range γ = α '' Icc 0 c ∧ ∀ t : I, t < 1 → γ t ∈ U := by
  obtain ⟨c,hc,hex,hbefore⟩ := path_first_exit_frontier α U hU ho ha
  let k : I → I := fun t => ⟨(c:ℝ)*(t:ℝ), by
    constructor
    · exact mul_nonneg c.property.1 t.property.1
    · nlinarith [c.property.1,c.property.2,t.property.1,t.property.2]⟩
  let γ : Path o (α c) := {
    toFun := α ∘ k
    continuous_toFun := α.continuous.comp (by fun_prop)
    source' := by simp [k,α.source]
    target' := by simp [k] }
  have hk0 : k 0 = 0 := by apply Subtype.ext; simp [k]
  have hk1 : k 1 = c := by apply Subtype.ext; simp [k]
  refine ⟨c,hc,γ,hex,?_,?_,?_⟩
  · intro s t he
    have hst := congrArg Subtype.val (hα he)
    change (c:ℝ)*(s:ℝ) = (c:ℝ)*(t:ℝ) at hst
    apply Subtype.ext
    exact mul_left_cancel₀ (ne_of_gt hc) hst
  · ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨k t, ?_, rfl⟩
      exact ⟨(k t).property.1, by change (c:ℝ)*(t:ℝ) ≤ c; nlinarith [c.property.1,t.property.2]⟩
    · rintro ⟨s,hs,rfl⟩
      let t : I := ⟨(s:ℝ)/(c:ℝ), by
        constructor
        · exact div_nonneg s.property.1 hc.le
        · exact (div_le_one hc).mpr hs.2⟩
      refine ⟨t, ?_⟩
      change α (k t) = α s
      congr 1
      apply Subtype.ext
      change (c:ℝ)*((s:ℝ)/(c:ℝ)) = s
      field_simp [ne_of_gt hc]
  · intro t ht
    apply hbefore
    change (c:ℝ)*(t:ℝ) < c
    exact mul_lt_of_lt_one_right hc ht

end CurveComplex.SeedProbeHeaders

#print axioms CurveComplex.SeedProbeHeaders.embedded_first_exit_prefix
