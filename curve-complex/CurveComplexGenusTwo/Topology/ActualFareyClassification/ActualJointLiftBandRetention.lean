import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusSourceWindingTransport
open Set Topology Schoenflies CurveComplex
/-- A jointly lifted source path avoiding the projected boundary remains in
its initial physical band; no choice of a different lift component is made. -/
theorem actual_joint_lift_retains_horizontal_band
    (A : C(Interval × ℝ,ℝ × ℝ)) (d : ℝ)
    (hzero : ∀ x, d < (A (⟨0,by norm_num⟩,x)).2 ∧
      (A (⟨0,by norm_num⟩,x)).2 < d+2*Real.pi)
    (havoid : ∀ t x, Circle.exp (A (t,x)).2 ≠ Circle.exp d) :
    ∀ t x, d < (A (t,x)).2 ∧ (A (t,x)).2 < d+2*Real.pi := by
  have hside (x c : ℝ) (hc : ∀ t, (A (t,x)).2 ≠ c) :
      range (fun t : Interval => (A (t,x)).2) ⊆ Iio c ∨
      range (fun t : Interval => (A (t,x)).2) ⊆ Ioi c := by
    have ht : Continuous (fun t : Interval => (A (t,x)).2) := by fun_prop
    apply (isPreconnected_range ht).subset_or_subset isOpen_Iio isOpen_Ioi
      (disjoint_left.mpr (fun _ hl hr => lt_asymm hl hr))
    rintro y ⟨t,rfl⟩
    exact (lt_or_gt_of_ne (hc t)).elim Or.inl Or.inr
  intro t x
  have hlow : ∀ t, (A (t,x)).2 ≠ d := by
    intro s hs
    exact havoid s x (congrArg Circle.exp hs)
  have hupp : ∀ t, (A (t,x)).2 ≠ d+2*Real.pi := by
    intro s hs
    apply havoid s x
    rw [hs,Circle.exp_add_two_pi]
  constructor
  · rcases hside x d hlow with hl | hr
    · have hz := hl (mem_range_self (⟨0,by norm_num⟩ : Interval))
      exact False.elim (lt_asymm (hzero x).1 hz)
    · exact hr (mem_range_self t)
  · rcases hside x (d+2*Real.pi) hupp with hl | hr
    · exact hl (mem_range_self t)
    · have hz := hr (mem_range_self (⟨0,by norm_num⟩ : Interval))
      exact False.elim (lt_asymm (hzero x).2 hz)
