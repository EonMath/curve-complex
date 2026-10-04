import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQDiskFContainment

open CurveComplex Set Topology

theorem regional_Q_boundary_parallel_reflects_F
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (Q F B : Set S) (hBQ : B ⊆ frontier Q)
    (hBF : B ⊆ F) (hFclosed : IsClosed F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hBdisj : ∀ i, Disjoint B (c i).val.image)
    (hfrontier : frontier F = B ∪ ⋃ i, (c i).val.image)
    (aF : C(Interval,↥F))
    (ha0 : (aF 0).val ∈ B) (ha1 : (aF 1).val ∈ B)
    (haProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (aF t).val ∉ frontier F)
    (aQ : C(Interval,↥Q))
    (haimage : ∀ t, (aQ t).val = (aF t).val)
    (hparallelQ :
      ∃ b : C(Interval,↥Q), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥Q),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range aQ ∪ Set.range b) :
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range aF ∪ Set.range b := by
  classical
  obtain ⟨b,hb,hbB,d,hd,hdimage⟩ := hparallelQ
  have haClear (i : J) (t : Interval) : (aF t).val ∉ (c i).val.image := by
    by_cases ht0 : t = 0
    · exact fun h => Set.disjoint_left.mp (hBdisj i) (ht0 ▸ ha0) h
    by_cases ht1 : t = 1
    · exact fun h => Set.disjoint_left.mp (hBdisj i) (ht1 ▸ ha1) h
    intro hc
    apply haProper t ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩
    rw [hfrontier]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i,hc⟩)
  have hboundary : (fun z => (d z).val) '' {z | z.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ F := by
    rintro y ⟨z,hz,rfl⟩
    have hz' : d z ∈ Set.range aQ ∪ Set.range b := hdimage ▸ ⟨z,hz,rfl⟩
    rcases hz' with ⟨t,ht⟩ | ⟨t,ht⟩
    · change (d z).val ∈ F
      rw [← ht,haimage]
      exact (aF t).property
    · change (d z).val ∈ F
      rw [← ht]
      exact hBF (hbB t)
  have hboundaryClear (i : J) : Disjoint (c i).val.image
      ((fun z => (d z).val) '' {z | z.val ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    apply Set.disjoint_left.mpr
    intro y hyc
    rintro ⟨z,hz,rfl⟩
    have hz' : d z ∈ Set.range aQ ∪ Set.range b := hdimage ▸ ⟨z,hz,rfl⟩
    rcases hz' with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact haClear i t (haimage t ▸ (congrArg Subtype.val ht).symm ▸ hyc)
    · exact Set.disjoint_left.mp (hBdisj i) (hbB t)
        ((congrArg Subtype.val ht).symm ▸ hyc)
  have hmeet : (Set.range (fun z => (d z).val) ∩ interior F).Nonempty := by
    let t : Interval := ⟨1/2,by norm_num⟩
    have ht : t ∈ Set.Ioo (0 : Interval) 1 := by
      constructor <;> apply Subtype.mk_lt_mk.mpr <;> norm_num [t]
    have hFi : (aF t).val ∈ interior F :=
      (mem_interior_iff_notMem_frontier (aF t).property).mpr (haProper t ht)
    have hay : aQ t ∈ Set.range d := by
      have hsub : Set.range aQ ⊆ Set.range d := by
        have hh : Set.range aQ ⊆ Set.range aQ ∪ Set.range b :=
          Set.subset_union_left
        rw [← hdimage] at hh
        exact hh.trans (Set.image_subset_range _ _)
      exact hsub (Set.mem_range_self t)
    obtain ⟨z,hz⟩ := hay
    exact ⟨(aF t).val,⟨z,(congrArg Subtype.val hz).trans
      (haimage t)⟩,hFi⟩
  have hdF := regional_embedded_Q_disk_with_regional_boundary_lies_in_F
    Q F B hBQ hFclosed J c hfrontier d hd hboundary hboundaryClear hmeet
  let bF : C(Interval,↥F) :=
    ⟨fun t => ⟨(b t).val,hBF (hbB t)⟩,
      (continuous_subtype_val.comp b.continuous).subtype_mk _⟩
  let dF : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F) :=
    ⟨fun z => ⟨(d z).val,hdF (Set.mem_range_self z)⟩,
      (continuous_subtype_val.comp d.continuous).subtype_mk _⟩
  have hbF : Topology.IsEmbedding bF := by
    apply Topology.IsEmbedding.of_comp bF.continuous continuous_subtype_val
    change Topology.IsEmbedding (fun t : Interval => (b t).val)
    exact Topology.IsEmbedding.subtypeVal.comp hb
  have hdFemb : Topology.IsEmbedding dF := by
    apply Topology.IsEmbedding.of_comp dF.continuous continuous_subtype_val
    change Topology.IsEmbedding (fun z : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin 2)) 1 => (d z).val)
    exact Topology.IsEmbedding.subtypeVal.comp hd
  refine ⟨bF,hbF,hbB,dF,hdFemb,?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨z,hz,rfl⟩
    have hq : d z ∈ Set.range aQ ∪ Set.range b := hdimage ▸ ⟨z,hz,rfl⟩
    rcases hq with ⟨t,ht⟩ | ⟨t,ht⟩
    · left
      exact ⟨t,Subtype.ext ((haimage t).symm.trans (congrArg Subtype.val ht))⟩
    · right
      exact ⟨t,Subtype.ext (by change (b t).val = (d z).val
                               exact congrArg Subtype.val ht)⟩
  · rintro y (⟨t,ht⟩ | ⟨t,ht⟩)
    · have hq : aQ t ∈ d '' {z | z.val ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [hdimage]
        exact Or.inl (Set.mem_range_self t)
      obtain ⟨z,hz,hzeq⟩ := hq
      refine ⟨z,hz,?_⟩
      apply Subtype.ext
      rw [← ht]
      change (d z).val = (aF t).val
      exact (congrArg Subtype.val hzeq).trans (haimage t)
    · have hq : b t ∈ d '' {z | z.val ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [hdimage]
        exact Or.inr (Set.mem_range_self t)
      obtain ⟨z,hz,hzeq⟩ := hq
      refine ⟨z,hz,?_⟩
      apply Subtype.ext
      rw [← ht]
      change (d z).val = (b t).val
      exact congrArg Subtype.val hzeq

#print axioms regional_Q_boundary_parallel_reflects_F
