import CurveComplexGenusTwo.Topology.ActualConnectivity.CanonicalNonseparatingReducingStep
namespace CurveComplex
theorem source_genus_two_nonseparating_finite_edge_chain
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (α β : {v : Vertex S // nonseparatingVertex v}) :
    ∃ n : ℕ, ∃ v : ℕ → {v : Vertex S // nonseparatingVertex v},
      v 0=α ∧ v n=β ∧
      ∀ j : ℕ, j<n → geometricIntersection (v j).val (v (j+1)).val ≤ 1 := by
  classical
  generalize hn : geometricIntersection α.val β.val=n
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih =>
    by_cases hsmall : geometricIntersection α.val β.val≤1
    · refine ⟨1,fun j=>if j=0 then α else β,by simp,by simp,?_⟩
      intro j hj
      have hj0 : j=0 := by omega
      subst j
      simpa using hsmall
    · obtain ⟨γ,hαγ,hdecrease⟩ := source_genus_two_nonseparating_reducing_step S hS α β
        (Nat.lt_of_not_ge hsmall)
      obtain ⟨m,v,hv0,hvm,hv⟩ := ih (geometricIntersection γ.val β.val) (by omega) γ rfl
      let w : ℕ → {v : Vertex S // nonseparatingVertex v} := fun j=>if j=0 then α else v (j-1)
      refine ⟨m+1,w,by simp [w],by simpa [w] using hvm,?_⟩
      intro j hj
      cases j with
      | zero => simpa [w,hv0] using hαγ
      | succ j => simpa [w] using hv j (by omega)
end CurveComplex
#print axioms CurveComplex.source_genus_two_nonseparating_finite_edge_chain
