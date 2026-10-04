import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualSphereTwoTraceComparisonAnnulusLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

-- The actual old half of G is itself a maximal complementary cylinder region.
theorem embedded_annulus_inner_complement_component
    {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace Plane X]
    (q : C(Circle × Interval,X)) (hq : IsEmbedding q) :
    IsComplementComponent
      (Set.range (fun z : Circle => q (z,0)) ∪ Set.range (fun z : Circle => q (z,1)))
      (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
  audit_main14_base3
    let C := Set.range (fun z : Circle => q (z,0))
    let D := Set.range (fun z : Circle => q (z,1))
    have hq0 : Set.range (fun z : Circle => q (z,0))=C := rfl
    have hq1 : Set.range (fun z : Circle => q (z,1))=D := rfl
    let Qmiddle : Set X := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
    have hQmiddleConnected : IsConnected Qmiddle := by
      have he : {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}=
          (Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1 := by ext p;simp
      change IsConnected (q '' _)
      rw [he]
      exact (isConnected_univ.prod (isConnected_Ioo (by norm_num : (0:Interval)<1))).image _
        q.continuous.continuousOn
    have hQmiddleAvoid : Qmiddle ⊆ (C ∪ D)ᶜ := by
      rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩ (hc | hdmem)
      · obtain ⟨w,hw⟩ := hq0.symm ▸ hc
        have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
        change (0:ℝ)=(t:ℝ) at hh
        linarith
      · obtain ⟨w,hw⟩ := hq1.symm ▸ hdmem
        have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
        change (1:ℝ)=(t:ℝ) at hh
        linarith
    have hQmiddleDiff : Qmiddle=Set.range q \ (C ∪ D) := by
      apply Set.Subset.antisymm
      · exact fun x hx => ⟨by obtain ⟨p,hp,he⟩:=hx;exact ⟨p,he⟩,hQmiddleAvoid hx⟩
      · rintro x ⟨⟨⟨z,t⟩,rfl⟩,hx⟩
        have ht0 : (t:ℝ) ≠ 0 := by
          intro he
          have ht : t=0 := Subtype.ext he
          apply hx
          left
          rw [ht,← hq0]
          exact Set.mem_range_self z
        have ht1 : (t:ℝ) ≠ 1 := by
          intro he
          have ht : t=1 := Subtype.ext he
          apply hx
          right
          rw [ht,← hq1]
          exact Set.mem_range_self z
        exact ⟨(z,t),⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
    have hQmiddleOpen : IsOpen Qmiddle := by
      rw [isOpen_iff_forall_mem_open]
      rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩
      let k : Plane → X := fun x => q (z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1))
      let O : Set Plane := {x | x 0 ∈ Set.Ioo (-1:ℝ) 1 ∧ x 1 ∈ Set.Ioo (0:ℝ) 1}
      have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
        (isOpen_Ioo.preimage (by fun_prop))
      have hk : Continuous k := q.continuous.comp
        ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
          (continuous_projIcc.comp (by fun_prop)))
      have hki : InjOn k O := by
        intro x hx y hy he
        have hh := hq.injective he
        have h0 : Circle.exp (x 0)=Circle.exp (y 0) := mul_left_cancel (congrArg Prod.fst hh)
        have hlen : (1:ℝ)-(-1)<2*Real.pi := by linarith [Real.pi_gt_three]
        have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩ ⟨hy.1.1.le,hy.1.2.le⟩ h0
        have h1 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
        simp only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,
          Set.projIcc_of_mem zero_le_one ⟨hy.2.1.le,hy.2.2.le⟩] at h1
        ext i
        fin_cases i
        · exact h0'
        · exact h1
      have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
      have hsub : k '' O ⊆ Qmiddle := by
        rintro y ⟨x,hx,rfl⟩
        refine ⟨(z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1)),?_,rfl⟩
        change 0 < (Set.projIcc 0 1 zero_le_one (x 1):ℝ) ∧
          (Set.projIcc 0 1 zero_le_one (x 1):ℝ)<1
        simpa only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,Set.mem_Ioo] using hx.2
      refine ⟨k '' O,hsub,hopen,?_⟩
      refine ⟨Plane.mk 0 (t:ℝ),⟨by norm_num [O],⟨ht0,ht1⟩⟩,?_⟩
      simp [k,Set.projIcc_of_mem zero_le_one t.property]
    have hqRangeClosed : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
    have hQcomponent : IsComplementComponent (C ∪ D) Qmiddle := by
      refine ⟨hQmiddleConnected.nonempty,hQmiddleConnected,hQmiddleAvoid,?_⟩
      intro T hT hQT hTavoid
      have hsub : T ⊆ Qmiddle ∪ (Set.range q)ᶜ := by
        intro x hxT
        by_cases hxq : x ∈ Set.range q
        · left
          rw [hQmiddleDiff]
          exact ⟨hxq,hTavoid hxT⟩
        · exact Or.inr hxq
      have hdisj : Disjoint Qmiddle (Set.range q)ᶜ := by
        apply Set.disjoint_left.mpr
        intro x hx hxq
        rw [hQmiddleDiff] at hx
        exact hxq hx.1
      rcases hT.isPreconnected.subset_or_subset hQmiddleOpen hqRangeClosed.isOpen_compl
        hdisj hsub with hTQ | hTout
      · exact Set.Subset.antisymm hTQ hQT
      · obtain ⟨x,hx⟩ := hQmiddleConnected.nonempty
        exact False.elim (Set.disjoint_left.mp hdisj hx (hTout (hQT hx)))
    exact hQcomponent
end CurveComplex.HyperellipticModel
