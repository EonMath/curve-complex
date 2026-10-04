import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_strip_point_closed_obstacle_clearance
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (K : Set ↥F) (hK : IsClosed K)
    (s : Interval) (hclear : E (s,⟨0,by norm_num⟩) ∉ K) :
    ∃ V : Set Interval, IsOpen V ∧ s ∈ V ∧
      ∃ η : ℝ, 0 < η ∧
        ∀ t ∈ V, ∀ w : Set.Icc (-1 : ℝ) 1,
          |(w : ℝ)| < η → E (t,w) ∉ K := by
  let zero : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  have hprod : ({zero} : Set (Set.Icc (-1 : ℝ) 1)) ×ˢ {s} ⊆
      (fun z : Set.Icc (-1 : ℝ) 1 × Interval => E (z.2,z.1)) ⁻¹' Kᶜ := by
    rintro ⟨w,t⟩ ⟨hw,ht⟩
    obtain rfl := Set.mem_singleton_iff.mp hw
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact hclear
  obtain ⟨U,V,hU,hV,hzero,hsV,hUV⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_singleton
    (hK.isOpen_compl.preimage (E.continuous.comp continuous_swap)) hprod
  obtain ⟨η,hη,hηU⟩ := Metric.isOpen_iff.mp hU zero
    (hzero (Set.mem_singleton _))
  refine ⟨V,hV,hsV (Set.mem_singleton s),η,hη,?_⟩
  intro t ht w hw
  have hwU : w ∈ U := by
    apply hηU
    change dist (w : ℝ) 0 < η
    simpa only [Real.dist_eq,sub_zero] using hw
  exact hUV (show (w,t) ∈ U ×ˢ V from ⟨hwU,ht⟩)

#print axioms regional_strip_point_closed_obstacle_clearance
