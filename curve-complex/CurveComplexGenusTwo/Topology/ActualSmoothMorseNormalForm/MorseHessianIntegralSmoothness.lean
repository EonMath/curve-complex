import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexSmoothMorseParity
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open scoped ContDiff Topology
open Set Filter Metric MeasureTheory

/-- Smooth dependence on the endpoint of Milnor's integrated Hessian coefficients. -/
theorem actual_complex_hessian_integral_contDiffOn
    (f : ℂ → ℝ) (z₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball z₀ r)) (v w : ℂ) :
    ContDiffOn ℝ ∞
      (fun z => ∫ t : ℝ in 0..1,
        (1 - t) * fderiv ℝ (fderiv ℝ f) (z₀ + t • (z - z₀)) v w)
      (Metric.ball z₀ r) := by
  have uniform : ∀ (E : Type) [NormedAddCommGroup E]
      (g : ℂ × ℝ → E) (O : Set (ℂ × ℝ)) (s : Set ℂ),
      IsOpen O → IsOpen s → s ×ˢ Icc (0 : ℝ) 1 ⊆ O → ContinuousOn g O →
      ∀ x ∈ s, ∃ ε C : ℝ, 0 < ε ∧ ball x ε ⊆ s ∧
        ∀ y ∈ ball x ε, ∀ t ∈ Icc (0 : ℝ) 1, ‖g (y, t)‖ ≤ C := by
    intro E _ g O s hO hs hsub hg x hx
    have hK : IsCompact ({x} ×ˢ Icc (0 : ℝ) 1) :=
      isCompact_singleton.prod isCompact_Icc
    obtain ⟨V, hKV, hV, hb⟩ :=
      exists_isOpen_isBounded_image_of_isCompact_of_continuousOn hK hO
        (by rintro ⟨y, t⟩ ⟨hy, ht⟩; simp only [mem_singleton_iff] at hy; subst y
            exact hsub ⟨hx, ht⟩) hg
    obtain ⟨ε, hε, hthick⟩ := hK.exists_thickening_subset_open hV hKV
    obtain ⟨δ, hδ, hsδ⟩ := Metric.isOpen_iff.mp hs x hx
    obtain ⟨C, _, hC⟩ := hb.subset_closedBall_lt 0 (0 : E)
    refine ⟨min ε δ, C, lt_min hε hδ,
      (ball_subset_ball (min_le_right _ _)).trans hsδ, ?_⟩
    intro y hy t ht
    apply mem_closedBall_zero_iff.mp
    apply hC
    apply mem_image_of_mem
    apply hthick
    refine mem_thickening_iff.mpr ⟨(x, t), ⟨rfl, ht⟩, ?_⟩
    simp only [Prod.dist_eq, dist_self, max_lt_iff]
    exact ⟨(mem_ball.mp hy).trans_le (min_le_left _ _), hε⟩
  have int_smooth : ∀ n : ℕ, ∀ (E : Type) [NormedAddCommGroup E]
      [NormedSpace ℝ E] [CompleteSpace E]
      (g : ℂ × ℝ → E) (O : Set (ℂ × ℝ)) (s : Set ℂ),
      IsOpen O → IsOpen s → s ×ˢ Icc (0 : ℝ) 1 ⊆ O → ContDiffOn ℝ ∞ g O →
      ContDiffOn ℝ n (fun x => ∫ t : ℝ in 0..1, g (x, t)) s := by
    intro n
    induction n with
    | zero =>
      intro E _ _ _ g O s hO hs hsub hg
      rw [Nat.cast_zero, contDiffOn_zero]
      intro x hx
      obtain ⟨ε, C, hε, hεs, hbound⟩ := uniform E g O s hO hs hsub hg.continuousOn x hx
      have htime : ∀ y ∈ s, ContinuousOn (fun t => g (y, t)) (Icc (0 : ℝ) 1) := by
        intro y hy
        exact hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => hsub ⟨hy, ht⟩)
      apply ContinuousAt.continuousWithinAt
      apply intervalIntegral.continuousAt_of_dominated_interval
        (F := fun x t => g (x, t)) (bound := fun _ => C)
      · filter_upwards [ball_mem_nhds x hε] with y hy
        simpa only [uIoc_of_le zero_le_one] using
          ((htime y (hεs hy)).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      · filter_upwards [ball_mem_nhds x hε] with y hy
        exact Eventually.of_forall (fun t ht => hbound y hy t
          (Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)))
      · exact (continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable 0 1
      · apply Eventually.of_forall
        intro t ht
        have hxt : (x, t) ∈ O := hsub ⟨hx,
          Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)⟩
        have hct : ContinuousAt g (x, t) :=
          hg.continuousOn.continuousAt (hO.mem_nhds hxt)
        have hpair : ContinuousAt (fun y : ℂ => (y, t)) x :=
          continuous_id.continuousAt.prodMk continuous_const.continuousAt
        exact hct.comp (f := fun y : ℂ => (y, t)) hpair
    | succ n ih =>
      intro E _ _ _ g O s hO hs hsub hg
      let D : ℂ × ℝ → ℂ →L[ℝ] E :=
        fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)
      have hD : ContDiffOn ℝ ∞ D O :=
        (hg.fderiv_of_isOpen hO (by simp)).clm_comp contDiffOn_const
      have htime : ∀ y ∈ s, ContinuousOn (fun t => g (y, t)) (Icc (0 : ℝ) 1) := by
        intro y hy
        exact hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => hsub ⟨hy, ht⟩)
      have hDtime : ∀ y ∈ s, ContinuousOn (fun t => D (y, t)) (Icc (0 : ℝ) 1) := by
        intro y hy
        exact hD.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => hsub ⟨hy, ht⟩)
      have hder : ∀ y ∈ s, HasFDerivAt (fun x => ∫ t : ℝ in 0..1, g (x, t))
          (∫ t : ℝ in 0..1, D (y, t)) y := by
        intro y hy
        obtain ⟨ε, C, hε, hεs, hbound⟩ := uniform (ℂ →L[ℝ] E) D O s
          hO hs hsub hD.continuousOn y hy
        apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F' := fun x t => D (x, t)) (bound := fun _ => C) (ball_mem_nhds y hε)
        · filter_upwards [hs.mem_nhds hy] with x hx
          simpa only [uIoc_of_le zero_le_one] using
            ((htime x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
        · exact (by simpa only [uIcc_of_le zero_le_one] using htime y hy :
            ContinuousOn (fun t => g (y, t)) (uIcc (0 : ℝ) 1)).intervalIntegrable
        · simpa only [uIoc_of_le zero_le_one] using
            ((hDtime y hy).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
        · apply Eventually.of_forall
          intro t ht x hx
          exact hbound x hx t
            (Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht))
        · exact (continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable 0 1
        · apply Eventually.of_forall
          intro t ht x hx
          have hxt : (x, t) ∈ O := hsub ⟨hεs hx,
            Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using ht)⟩
          convert ((hg.contDiffAt (hO.mem_nhds hxt)).differentiableAt (by simp)).hasFDerivAt.comp x
            ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) t x)) using 1
          · rfl
          · rfl
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
      refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih (ℂ →L[ℝ] E) D O s hO hs hsub hD).congr
        (fun x hx => (hder x hx).fderiv)
  let P : ℂ × ℝ → ℂ := fun p => z₀ + p.2 • (p.1 - z₀)
  let O : Set (ℂ × ℝ) := P ⁻¹' ball z₀ r
  have hP : ContDiff ℝ ∞ P :=
    contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  have hO : IsOpen O := isOpen_ball.preimage hP.continuous
  have hsub : ball z₀ r ×ˢ Icc (0 : ℝ) 1 ⊆ O := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    exact (convex_ball z₀ r).add_smul_mem (mem_ball_self hr)
      (show z₀ + (z - z₀) ∈ ball z₀ r by simpa using hz) ht
  let g : ℂ × ℝ → ℝ := fun p => (1 - p.2) * fderiv ℝ (fderiv ℝ f) (P p) v w
  have hH : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ f)) (ball z₀ r) :=
    (hf.fderiv_of_isOpen (m := ∞) isOpen_ball (by simp)).fderiv_of_isOpen
      (m := ∞) isOpen_ball (by simp)
  have hg : ContDiffOn ℝ ∞ g O := by
    exact (contDiffOn_const.sub contDiff_snd.contDiffOn).mul
      (((hH.comp hP.contDiffOn (fun _ hp => hp)).clm_apply contDiffOn_const).clm_apply
        contDiffOn_const)
  apply contDiffOn_infty.mpr
  intro n
  exact int_smooth n ℝ g O (ball z₀ r) hO isOpen_ball hsub hg
