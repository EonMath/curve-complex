import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualGlobalArcPrefix
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches
import CurveComplexGenusTwo.Topology.FrontierCircle.BandStraightening

namespace CurveComplex

/-- Review candidate for the actual geometric gluing obligation: an arbitrary
compact embedded source arc has a whole strip neighborhood, fixed center
parametrization, and prescribed open localization. No strip is assumed. -/
theorem source_whole_embedded_arc_strip
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S]
    (f : C(Interval,S)) (hf : Topology.IsEmbedding f)
    (U : Set S) (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ E : Interval × Set.Icc (-1:ℝ) 1 → S,
      Topology.IsEmbedding E ∧
      (∀ t, E (t,⟨0,by norm_num⟩) = f t) ∧ Set.range E ⊆ U := by
  obtain ⟨B⟩ := source_whole_arc_prefix_strip f hf U hU hfU
  let c : Interval → S := fun t => B.map (t,⟨0,by norm_num⟩)
  have hc : Topology.IsEmbedding c :=
    B.embedded.comp (isEmbedding_prodMkLeft (⟨0,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
  have hcr : Set.range c = Set.range f := by
    change Set.range (fun t => B.map (t,⟨0,by norm_num⟩)) = _
    rw [B.center_range,← unitInterval.univ_eq_Icc,Set.image_univ]
  let g : Interval → Set.range c := fun t =>
    ⟨f t,by rw [hcr]; exact Set.mem_range_self t⟩
  have hgc : Continuous g := f.continuous.subtype_mk _
  let h : Interval → Interval := hc.toHomeomorph.symm ∘ g
  have hhc : Continuous h := hc.toHomeomorph.symm.continuous.comp hgc
  have hcenter (t : Interval) : c (h t) = f t :=
    congrArg Subtype.val (hc.toHomeomorph.apply_symm_apply (g t))
  have hhi : Function.Injective h := by
    intro t u he
    apply hf.injective
    rw [← hcenter t,← hcenter u,he]
  let k : Interval × Set.Icc (-1:ℝ) 1 → Interval × Set.Icc (-1:ℝ) 1 :=
    fun z => (h z.1,z.2)
  have hkc : Continuous k := (hhc.comp continuous_fst).prodMk continuous_snd
  have hki : Function.Injective k := by
    intro z w he
    exact Prod.ext (hhi (congrArg Prod.fst he))
      (by simpa only [k] using congrArg Prod.snd he)
  let E := B.map ∘ k
  refine ⟨E,((B.embedded.continuous.comp hkc).isClosedEmbedding
    (B.embedded.injective.comp hki)).isEmbedding,?_,?_⟩
  · intro t
    exact hcenter t
  · exact (Set.range_comp_subset_range _ _).trans B.image_subset

end CurveComplex

#print axioms CurveComplex.source_whole_embedded_arc_strip
