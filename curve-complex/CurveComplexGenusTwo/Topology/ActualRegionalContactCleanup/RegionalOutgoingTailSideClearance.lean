import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalStripPointClearance

open CurveComplex Set Topology

theorem regional_outgoing_negative_tail_near_center_clearance
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (center anchor : C(Interval,↥F)) (ha : Topology.IsEmbedding anchor)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = center t)
    (r c u : Interval) (hru : r < u)
    (hcontact : anchor r = center c)
    (hin : ∀ z ∈ Set.Ioc r u, anchor z ∈ Set.range E)
    (hneg : ∀ z (hz : z ∈ Set.Ioc r u),
      ((hE.toHomeomorph.symm ⟨anchor z,hin z hz⟩).2 : ℝ) < 0) :
    ∃ V : Set Interval, IsOpen V ∧ c ∈ V ∧
      ∃ η : ℝ, 0 < η ∧ ∀ t ∈ V,
        ∀ w : Set.Icc (-1 : ℝ) 1, 0 < (w : ℝ) → (w : ℝ) < η →
          E (t,w) ∉ anchor '' Set.Icc r 1 := by
  let K : Set ↥F := anchor '' Set.Icc u 1
  have hK : IsClosed K := (isCompact_Icc.image anchor.continuous).isClosed
  have hcClear : E (c,⟨0,by norm_num⟩) ∉ K := by
    rintro ⟨z,hz,he⟩
    have hzr : z = r := ha.injective (he.trans ((hcenter c).trans hcontact.symm))
    exact (not_le_of_gt hru) (hzr ▸ hz.1)
  obtain ⟨V,hV,hcV,η,hη,hKclear⟩ :=
    regional_strip_point_closed_obstacle_clearance E K hK c hcClear
  refine ⟨V,hV,hcV,η,hη,?_⟩
  intro t ht w hw hwη
  rintro ⟨z,hz,he⟩
  by_cases huz : u ≤ z
  · exact hKclear t ht w (by rw [abs_of_pos hw]; exact hwη)
      ⟨z,⟨huz,hz.2⟩,he⟩
  · rcases eq_or_lt_of_le hz.1 with hrz | hrz
    · have he0 : E (t,w) = E (c,⟨0,by norm_num⟩) :=
        he.symm.trans ((congrArg anchor hrz.symm).trans
          (hcontact.trans (hcenter c).symm))
      have hw0 := congrArg (fun q : Interval × Set.Icc (-1 : ℝ) 1 =>
        (q.2 : ℝ)) (hE.injective he0)
      exact (ne_of_gt hw) hw0
    · have hzI : z ∈ Set.Ioc r u := ⟨hrz,(lt_of_not_ge huz).le⟩
      have hinv : hE.toHomeomorph.symm ⟨anchor z,hin z hzI⟩ = (t,w) := by
        calc
          hE.toHomeomorph.symm ⟨anchor z,hin z hzI⟩ =
              hE.toHomeomorph.symm ⟨E (t,w),Set.mem_range_self _⟩ :=
            congrArg hE.toHomeomorph.symm (Subtype.ext he)
          _ = (t,w) := hE.toHomeomorph.symm_apply_apply _
      have hn := hneg z hzI
      rw [hinv] at hn
      exact (lt_asymm hn hw).elim

#print axioms regional_outgoing_negative_tail_near_center_clearance
