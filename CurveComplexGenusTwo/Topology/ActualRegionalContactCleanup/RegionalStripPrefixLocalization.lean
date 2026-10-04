import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_strip_compact_prefix_localization
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (K : Set ↥F) (hK : IsClosed K)
    (V : Set Interval) (hV : IsOpen V)
    (havoid : ∀ t ∈ Vᶜ, E (t,⟨0,by norm_num⟩) ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (t : Interval) (w : Set.Icc (-1 : ℝ) 1),
        t ∈ Vᶜ → |(w : ℝ)| < δ → E (t,w) ∉ K := by
  let zero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  have hC : IsCompact (Vᶜ) :=
    isCompact_univ.of_isClosed_subset hV.isClosed_compl (Set.subset_univ _)
  have hprod : ({zero} : Set (Set.Icc (-1 : ℝ) 1)) ×ˢ Vᶜ ⊆
      (fun z : Set.Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) ⁻¹' Kᶜ := by
    rintro ⟨w,t⟩ ⟨hw,ht⟩
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact havoid t ht
  obtain ⟨U,W,hU,hW,hzero,hCsub,hUW⟩ := generalized_tube_lemma
    isCompact_singleton hC
    (hK.isOpen_compl.preimage (E.continuous.comp continuous_swap)) hprod
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU zero
    (hzero (Set.mem_singleton _))
  refine ⟨δ,hδ,?_⟩
  intro t w ht hw
  have hwU : w ∈ U := by
    apply hδU
    change dist (w : ℝ) 0 < δ
    simpa only [Real.dist_eq,sub_zero] using hw
  have htW : t ∈ W := hCsub ht
  exact hUW (show (w,t) ∈ U ×ˢ W from ⟨hwU,htW⟩)

#print axioms regional_strip_compact_prefix_localization
