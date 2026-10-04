import Mathlib

namespace CurveComplex.HyperellipticModel.ArcSurgery

theorem finite_three_trace_contact_isolation
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (A B C : Set S)
    (hAB : (A ∩ B).Finite) (hAC : (A ∩ C).Finite)
    (hBC : (B ∩ C).Finite) (p : S) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
      (U ∩ A ∩ B ⊆ {p}) ∧
      (U ∩ A ∩ C ⊆ {p}) ∧
      (U ∩ B ∩ C ⊆ {p}) := by
  let X : Set S := (A ∩ B) ∪ (A ∩ C) ∪ (B ∩ C)
  have hX : X.Finite := (hAB.union hAC).union hBC
  let U : Set S := (X \ {p})ᶜ
  have hU : IsOpen U := (hX.sdiff).isClosed.isOpen_compl
  have hpU : p ∈ U := by simp [U]
  refine ⟨U,hU,hpU,?_,?_,?_⟩
  · rintro q ⟨⟨hqU,hqA⟩,hqB⟩
    by_contra hne
    exact hqU ⟨Or.inl (Or.inl ⟨hqA,hqB⟩),hne⟩
  · rintro q ⟨⟨hqU,hqA⟩,hqC⟩
    by_contra hne
    exact hqU ⟨Or.inl (Or.inr ⟨hqA,hqC⟩),hne⟩
  · rintro q ⟨⟨hqU,hqB⟩,hqC⟩
    by_contra hne
    exact hqU ⟨Or.inr ⟨hqB,hqC⟩,hne⟩

end CurveComplex.HyperellipticModel.ArcSurgery
