import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFinitePrescribedTargetStrips

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Finite target contacts have a uniform strict parameter margin from both
marked endpoints; the margin is chosen from the actual contact parameters. -/
theorem actual_finite_interval_contacts_uniform_margin
    (K : Set Interval) (hK : K.Finite) (hKi : ∀ r ∈ K, 0 < r.val ∧ r.val < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ ∀ r ∈ K, δ < r.val ∧ r.val < 1-δ := by
  classical
  induction K,hK using Set.Finite.induction_on with
  | empty => exact ⟨1/4,by norm_num,by norm_num,by simp⟩
  | @insert r K hr hK ih =>
    have hri := hKi r (mem_insert r K)
    obtain ⟨δ,hδ,hδhalf,hcover⟩ := ih (fun s hs => hKi s (mem_insert_of_mem r hs))
    let ε := min δ (min (r.val/2) ((1-r.val)/2))
    have hε : 0 < ε := lt_min hδ (lt_min (half_pos hri.1) (by linarith))
    have hεδ : ε ≤ δ := min_le_left _ _
    have hεr : ε ≤ r.val/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hε1 : ε ≤ (1-r.val)/2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ε,hε,hεδ.trans_lt hδhalf,?_⟩
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · constructor <;> linarith
    · obtain ⟨hlo,hhi⟩ := hcover s hs
      constructor <;> linarith

def actualContactParameters (M : HyperellipticModel E S)
    (anchor a : EssentialMarkedArc M) : Set Interval :=
  a.val.map ⁻¹' crossings M anchor a

theorem actualContactParameters_interior
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M) :
    ∀ r ∈ actualContactParameters M anchor a, 0 < r.val ∧ r.val < 1 := by
  intro r hr
  exact anchor_interior_parameter_bounds M a r hr.2

theorem actualContactParameters_finite
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M)
    (hf : (crossings M anchor a).Finite) : (actualContactParameters M anchor a).Finite := by
  apply hf.preimage
  intro r hr s hs he
  rcases a.val.injective_except_loop_closure r s he with hh | hh | hh
  · exact hh
  · have hb := actualContactParameters_interior M anchor a r hr
    have he := congrArg Subtype.val hh.1
    change r.val=0 at he
    linarith [hb.1]
  · have hb := actualContactParameters_interior M anchor a r hr
    have he := congrArg Subtype.val hh.1
    change r.val=1 at he
    linarith [hb.2]

/-- Actual finite-position data produce both endpoint collars free of the
stationary anchor's INTERIOR contacts. Shared marked endpoints remain allowed.
No finite-margin, collar or endpoint-germ position is assumed. -/
theorem actual_prescribed_target_endpoint_contact_margin
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (Q : FinitePosition M anchor F)
    (v : {v // v ∈ F}) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      (∀ r ∈ actualContactParameters M anchor (Q.rep v), δ < r.val ∧ r.val < 1-δ) ∧
      (∀ r : Interval, 0 < r.val → r.val < δ → (Q.rep v).val.map r ∉ anchor.val.image) ∧
      (∀ r : Interval, 1-δ < r.val → r.val < 1 → (Q.rep v).val.map r ∉ anchor.val.image) := by
  obtain ⟨δ,hδ,hhalf,hcover⟩ := actual_finite_interval_contacts_uniform_margin
    (actualContactParameters M anchor (Q.rep v))
    (actualContactParameters_finite M anchor (Q.rep v) (Q.finite v))
    (actualContactParameters_interior M anchor (Q.rep v))
  have hcontact (r : Interval) (hr0 : 0 < r.val) (hr1 : r.val < 1)
      (ha : (Q.rep v).val.map r ∈ anchor.val.image) : r ∈ actualContactParameters M anchor (Q.rep v) := by
    have hm : (Q.rep v).val.map r ∉ M.cover.branch := by
      intro hm
      rcases (Q.rep v).val.marked_only_at_ends r hm with hh | hh
      · have he := congrArg Subtype.val hh; change r.val=0 at he; linarith
      · have he := congrArg Subtype.val hh; change r.val=1 at he; linarith
    exact ⟨⟨ha,hm⟩,mem_range_self r,hm⟩
  refine ⟨δ,hδ,hhalf,hcover,?_,?_⟩
  · intro r hr0 hrδ ha
    have hr1 : r.val < 1 := by linarith
    have h := (hcover r (hcontact r hr0 hr1 ha)).1
    linarith
  · intro r hrδ hr1 ha
    have hr0 : 0 < r.val := by linarith
    have h := (hcover r (hcontact r hr0 hr1 ha)).2
    linarith

end
end CurveComplex.HyperellipticModel.ArcSurgery
