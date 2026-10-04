import Mathlib

open Set Topology unitInterval
namespace CurveComplex

/-- The first exit of a continuous path from an open disk lies on its
frontier, and the entire earlier segment lies in the disk interior. -/
theorem path_first_exit_frontier
    {S : Type*} [TopologicalSpace S] {x y : S}
    (p : Path x y) (U : Set S) (hU : IsOpen U)
    (hx : x ∈ U) (hy : y ∉ U) :
    ∃ t : I, 0 < t ∧ p t ∈ frontier U ∧ ∀ s : I, s < t → p s ∈ U := by
  let K : Set I := p ⁻¹' Uᶜ
  have hK : IsCompact K := (hU.isClosed_compl.preimage p.continuous).isCompact
  have hnonempty : K.Nonempty := ⟨1,by simpa [K,p.target] using hy⟩
  obtain ⟨t,ht,hmin⟩ := hK.exists_isMinOn hnonempty continuous_id.continuousOn
  have hnot : p t ∉ U := ht
  have htne : t ≠ 0 := by
    intro he
    apply hnot
    simpa [he,p.source] using hx
  have htpos : 0 < t := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm htne)
  have hbefore (s : I) (hst : s < t) : p s ∈ U := by
    by_contra hn
    have hs : s ∈ K := hn
    exact (not_le_of_gt hst) (hmin hs)
  have htclosure : t ∈ closure (Iio t : Set I) := by
    rw [closure_Iio' (show (Iio t : Set I).Nonempty from ⟨0,htpos⟩)]
    exact (show t ≤ t from le_refl t)
  have hclosed : IsClosed (p ⁻¹' closure U) := isClosed_closure.preimage p.continuous
  have hsub : (Iio t : Set I) ⊆ p ⁻¹' closure U := by
    intro s hs
    exact subset_closure (hbefore s hs)
  have hclos : p t ∈ closure U := hclosed.closure_subset_iff.mpr hsub htclosure
  refine ⟨t,htpos,?_,hbefore⟩
  rw [frontier,hU.interior_eq]
  exact ⟨hclos,hnot⟩

#print axioms path_first_exit_frontier

end CurveComplex
