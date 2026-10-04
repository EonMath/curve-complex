import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalDiskCrosscutSubdisk
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- A first-side intrusion cuts an actual two-sided disk into a smaller disk.
    The new first side remains on the original arc and its second side remains
    on the original second side. -/
theorem regional_two_side_disk_first_intrusion_subdisk
    {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (a first second : C(Interval,S))
    (ha : Topology.IsEmbedding a)
    (hfirst : Topology.IsEmbedding first)
    (hsecond : Topology.IsEmbedding second)
    (hfirstA : Set.range first ⊆ Set.range a)
    (h00 : first 0 = second 0) (h11 : first 1 = second 1)
    (d : C(Metric.closedBall (0 : Plane) 1,S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Set.range first ∪ Set.range second)
    (h0 : a 0 ∉ d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (h1 : a 1 ∉ d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
    (hin : (Set.range a ∩
      d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}).Nonempty) :
    ∃ (q g : C(Interval,S)) (e : C(Metric.closedBall (0 : Plane) 1,S)),
      Topology.IsEmbedding q ∧ Topology.IsEmbedding g ∧
      Set.range q ⊆ Set.range a ∧ Set.range g ⊆ Set.range second ∧
      q 0 = g 0 ∧ q 1 = g 1 ∧
      q '' Set.Ioo (0 : Interval) 1 ⊆
        d '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ∧
      Topology.IsEmbedding e ∧
      e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
        Set.range q ∪ Set.range g ∧
      Set.range e ⊆ Set.range d ∧
      e '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ⊆
        d '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ∧
      ∃ z ∈ ({first 0,first 1} : Set S), z ∉ Set.range e := by
  obtain ⟨q,hq,hqa,⟨r,hr⟩,⟨s,hs⟩,hqi,hnotboth⟩ :=
    regional_two_side_disk_first_arc_intrusion_crosscut_strict
      a first second ha hfirst hfirstA h00 h11 d hd hboundary h0 h1 hin
  have hrs : r ≠ s := by
    intro he
    have h01 : (0 : Interval) = 1 :=
      hq.injective (hr.symm.trans ((congrArg second he).trans hs))
    exact zero_ne_one h01
  let affine : Interval → Interval := fun t =>
    ⟨(1-t.val)*r.val+t.val*s.val,by
      constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
        s.property.1,s.property.2]⟩
  let g : C(Interval,S) := ⟨second ∘ affine,second.continuous.comp (by fun_prop)⟩
  have hg0 : g 0 = q 0 := by simpa [g,affine] using hr
  have hg1 : g 1 = q 1 := by simpa [g,affine] using hs
  have hgi : Function.Injective g := by
    intro t u he
    have hv := congrArg Subtype.val (hsecond.injective he)
    apply Subtype.ext
    have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
    dsimp [affine] at hv
    have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact False.elim (hne (sub_eq_zero.mp hz).symm)
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
  have hgg : Set.range g ⊆ Set.range second := by
    rintro x ⟨t,rfl⟩
    exact Set.mem_range_self (affine t)
  have hgBoundary : Set.range g ⊆
      d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} := by
    rw [hboundary]
    exact Set.Subset.trans hgg Set.subset_union_right
  obtain ⟨e,he,heB,heD,heOpen⟩ :=
    regional_disk_crosscut_bounds_interior_subdisk d hd q g hq hg
      hg0.symm hg1.symm hgBoundary hqi
  have hfree : Disjoint
      (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
      (Set.range first ∪ Set.range second) := by
    rw [← hboundary]
    apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,huz⟩ ⟨v,hv,hvz⟩
    have huv : u = v := hd.injective (huz.trans hvz.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hmissing : ∃ z ∈ ({first 0,first 1} : Set S), z ∉ Set.range e := by
    have hn01 : ¬ (r=0 ∧ s=1) := by
      rintro ⟨rfl,rfl⟩
      apply hnotboth
      rw [← hr,← hs,h00,h11]
      exact ⟨Or.inl rfl,Or.inr rfl⟩
    have hn10 : ¬ (r=1 ∧ s=0) := by
      rintro ⟨rfl,rfl⟩
      apply hnotboth
      rw [← hr,← hs,h11,h00]
      exact ⟨Or.inr rfl,Or.inl rfl⟩
    have hend : ∃ v : Interval, (v=0 ∨ v=1) ∧ r≠v ∧ s≠v := by
      by_cases hr0 : r=0
      · refine ⟨1,Or.inr rfl,?_,fun hs1 => hn01 ⟨hr0,hs1⟩⟩
        rw [hr0]
        exact zero_ne_one
      by_cases hs0 : s=0
      · refine ⟨1,Or.inr rfl,fun hr1 => hn10 ⟨hr1,hs0⟩,?_⟩
        rw [hs0]
        exact zero_ne_one
      exact ⟨0,Or.inl rfl,hr0,hs0⟩
    obtain ⟨v,hv,hrv,hsv⟩ := hend
    let z : S := second v
    have hzcorner : z ∈ ({first 0,first 1} : Set S) := by
      rcases hv with hv | hv
      · exact Or.inl ((congrArg second hv).trans h00.symm)
      · exact Or.inr ((congrArg second hv).trans h11.symm)
    have hzB : z ∈ Set.range first ∪ Set.range second :=
      Or.inr (Set.mem_range_self v)
    have hznotq : z ∉ Set.range q := by
      rintro ⟨t,ht⟩
      by_cases ht0 : t=0
      · apply hrv
        apply hsecond.injective
        exact hr.trans ((congrArg q ht0).symm.trans ht)
      by_cases ht1 : t=1
      · apply hsv
        apply hsecond.injective
        exact hs.trans ((congrArg q ht1).symm.trans ht)
      exact Set.disjoint_left.mp hfree
        (ht ▸ hqi ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
          lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩) hzB
    have hznotg : z ∉ Set.range g := by
      rintro ⟨t,ht⟩
      have hzEnd : g t = second 0 ∨ g t = second 1 := by
        rcases hv with hv | hv
        · exact Or.inl (ht.trans (congrArg second hv))
        · exact Or.inr (ht.trans (congrArg second hv))
      rcases CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
        second g hsecond hg hgg t hzEnd with ht0 | ht1
      · exact hznotq ⟨0,hg0.symm.trans ((congrArg g ht0).symm.trans ht)⟩
      · exact hznotq ⟨1,hg1.symm.trans ((congrArg g ht1).symm.trans ht)⟩
    have hznotB : z ∉
        e '' {u | u.val ∈ Metric.sphere (0 : Plane) 1} := by
      rw [heB]
      exact fun h => h.elim hznotq hznotg
    refine ⟨z,hzcorner,?_⟩
    rintro ⟨u,hu⟩
    have hnorm : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hne : ‖u.val‖ ≠ 1 := by
      intro h
      apply hznotB
      exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
        using h,hu⟩
    have hzinside : z ∈ d '' {u | u.val ∈ Metric.ball (0 : Plane) 1} :=
      heOpen ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right]
        using lt_of_le_of_ne hnorm hne,hu⟩
    exact Set.disjoint_left.mp hfree hzinside hzB
  exact ⟨q,g,e,hq,hg,hqa,hgg,hg0.symm,hg1.symm,hqi,he,heB,heD,
    heOpen,hmissing⟩

end RegionalEmbeddedFamily
