import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
namespace CurveComplex
open Set Topology

/-- Uniformly narrow an actual whole strip to satisfy finitely many local
geometric constraints on specified CLOSED longitudinal sets. The one global
width factor preserves every existing coordinate-frame and seam equation. -/
theorem source_strip_finite_parameter_localization
    {S : Type} [TopologicalSpace S] [T2Space S]
    (B : Interval × Set.Icc (-1:ℝ) 1 → S) (hB : IsEmbedding B)
    (K : Type) [Fintype K] (C : K → Set Interval) (hC : ∀ k, IsClosed (C k))
    (U : K → Set S) (hU : ∀ k, IsOpen (U k))
    (hcenter : ∀ k t, t ∈ C k → B (t,⟨0,by norm_num⟩) ∈ U k) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ ∧ ρ ≤ 1,
      ∃ N : Interval × Set.Icc (-1:ℝ) 1 → S,
        IsEmbedding N ∧
        (∀ z, N z = B (z.1,⟨ρ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩)) ∧
        (∀ t, N (t,⟨0,by norm_num⟩) = B (t,⟨0,by norm_num⟩)) ∧
        ∀ k z, z.1 ∈ C k → N z ∈ U k := by
  classical
  let A : Interval × Set.Icc (-1:ℝ) 1 → Interval × S := fun z => (z.1,B z)
  have hAc : Continuous A := continuous_fst.prodMk hB.continuous
  have hAi : Function.Injective A := by
    intro z w he
    exact hB.injective (congrArg Prod.snd he)
  have hA : IsEmbedding A := (hAc.isClosedEmbedding hAi).isEmbedding
  let W : Set (Interval × S) := ⋂ k, (Prod.fst ⁻¹' C k)ᶜ ∪ Prod.snd ⁻¹' U k
  have hW : IsOpen W := isOpen_iInter_of_finite (fun k =>
    ((hC k).preimage continuous_fst).isOpen_compl.union ((hU k).preimage continuous_snd))
  have hcenterW (t : Interval) : A (t,⟨0,by norm_num⟩) ∈ W := by
    apply Set.mem_iInter.mpr
    intro k
    by_cases ht : t ∈ C k
    · exact Or.inr (hcenter k t ht)
    · exact Or.inl ht
  obtain ⟨ρ,hρ,M,hM,hMW,hMformula,hMcenter⟩ := source_shrink_embedded_strip_in_open A hA W hW hcenterW
  let N : Interval × Set.Icc (-1:ℝ) 1 → S := Prod.snd ∘ M
  have hNformula (z) : N z = B (z.1,⟨ρ*(z.2:ℝ),by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩) :=
    congrArg Prod.snd (hMformula z)
  have hNc : Continuous N := continuous_snd.comp hM.continuous
  have hNi : Function.Injective N := by
    intro z w he
    rw [hNformula,hNformula] at he
    have hh := hB.injective he
    apply Prod.ext
    · have hh0 := congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1 => q.1) hh
      exact hh0
    · apply Subtype.ext
      have hw := congrArg (fun q : Interval × Set.Icc (-1:ℝ) 1 => (q.2:ℝ)) hh
      exact mul_left_cancel₀ hρ.1.ne' hw
  refine ⟨ρ,hρ,N,(hNc.isClosedEmbedding hNi).isEmbedding,hNformula,?_,?_⟩
  · intro t
    exact congrArg Prod.snd (hMcenter t)
  · intro k z hz
    have hMz : M z ∈ W := hMW (Set.mem_range_self z)
    have hfirst : (M z).1 = z.1 := congrArg Prod.fst (hMformula z)
    have hMk := Set.mem_iInter.mp hMz k
    rcases hMk with hnot | hyes
    · apply False.elim
      apply hnot
      change (M z).1 ∈ C k
      rw [hfirst]
      exact hz
    · exact hyes
end CurveComplex
#print axioms CurveComplex.source_strip_finite_parameter_localization
