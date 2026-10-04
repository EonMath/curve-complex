import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalIndexedFamilyDescent

/-- A genuine natural-number descent reaches zero in at most its initial
    measure, retaining a complete sequence of actual successor states. -/
theorem regional_finite_measure_descent_terminates
    {A : Type*} (measure : A → ℕ) (step : A → A → Prop)
    (hdrop : ∀ a b, step a b → measure b < measure a)
    (hnext : ∀ a, 0 < measure a → ∃ b, step a b) (initial : A) :
    ∃ n : ℕ, n ≤ measure initial ∧ ∃ seq : ℕ → A,
      seq 0 = initial ∧ measure (seq n) = 0 ∧
      ∀ i < n, step (seq i) (seq (i+1)) := by
  have aux : ∀ m : ℕ, ∀ a : A, measure a = m →
      ∃ n : ℕ, n ≤ measure a ∧ ∃ seq : ℕ → A,
        seq 0 = a ∧ measure (seq n) = 0 ∧
        ∀ i < n, step (seq i) (seq (i+1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a ha
      by_cases hm : m = 0
      · exact ⟨0,by omega,(fun _ => a),rfl,ha.trans hm,by omega⟩
      · obtain ⟨b,hab⟩ := hnext a (by omega)
        have hb : measure b < m := (hdrop a b hab).trans_eq ha
        obtain ⟨n,hn,seq,hseq0,hseqn,hsteps⟩ := ih (measure b) hb b rfl
        let f : ℕ → A := fun i => if i = 0 then a else seq (i-1)
        refine ⟨n+1,by have hd := hdrop a b hab; omega,f,by simp [f],?_,?_⟩
        · simpa [f] using hseqn
        · intro i hi
          by_cases hi0 : i = 0
          · subst i
            simpa [f,hseq0] using hab
          · have hip : i-1 < n := by omega
            have hst := hsteps (i-1) hip
            have heq : i-1+1 = i := by omega
            simpa [f,hi0,heq] using hst
  exact aux (measure initial) initial rfl

#print axioms regional_finite_measure_descent_terminates
