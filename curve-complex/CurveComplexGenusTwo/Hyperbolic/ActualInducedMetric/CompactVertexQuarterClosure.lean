import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualVertexSectors

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem normSq_lt_one_eq_coe_ball :
    {z : H2 | z.re ^ 2 + z.im ^ 2 < 1} =
      ((↑) : H2 → ℂ) ⁻¹' Metric.ball 0 1 := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  have hn := Complex.normSq_eq_norm_sq (z : ℂ)
  simp only [Complex.normSq_apply] at hn
  change z.re * z.re + z.im * z.im = ‖(z : ℂ)‖ ^ 2 at hn
  constructor <;> intro h <;> nlinarith [norm_nonneg (z : ℂ)]

theorem unit_circle_mem_closure_inner (z : H2) (hz : z.re ^ 2 + z.im ^ 2 = 1) :
    z ∈ closure {w : H2 | w.re ^ 2 + w.im ^ 2 < 1} := by
  rw [normSq_lt_one_eq_coe_ball,
    ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
      UpperHalfPlane.continuous_coe,
    closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  change dist (z : ℂ) 0 ≤ 1
  rw [dist_zero_right]
  have hn := Complex.normSq_eq_norm_sq (z : ℂ)
  simp only [Complex.normSq_apply] at hn
  change z.re * z.re + z.im * z.im = ‖(z : ℂ)‖ ^ 2 at hn
  nlinarith [norm_nonneg (z : ℂ)]

theorem unit_circle_mem_closure_inner_quarter (p z : H2) (r : ℝ) (positive : Bool)
    (hz : z ∈ Metric.ball p r)
    (hs : if positive then 0 < z.re else z.re < 0)
    (hn : z.re ^ 2 + z.im ^ 2 = 1) :
    z ∈ closure (Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧ w.re ^ 2 + w.im ^ 2 < 1}) := by
  let A : Set H2 := Metric.ball p r ∩
    {w : H2 | if positive then 0 < w.re else w.re < 0}
  have hA : IsOpen A := by
    apply Metric.isOpen_ball.inter
    cases positive
    · exact isOpen_lt UpperHalfPlane.continuous_re continuous_const
    · exact isOpen_lt continuous_const UpperHalfPlane.continuous_re
  have hm : z ∈ A ∩ closure {w : H2 | w.re ^ 2 + w.im ^ 2 < 1} :=
    ⟨⟨hz, hs⟩, unit_circle_mem_closure_inner z hn⟩
  simpa only [A, Set.inter_assoc, ← Set.setOf_and] using hA.inter_closure hm

theorem unit_circle_mem_closure_outer_quarter (p z : H2) (r : ℝ) (positive : Bool)
    (hp : p.re ^ 2 + p.im ^ 2 = 1) (hz : z ∈ Metric.ball p r)
    (hs : if positive then 0 < z.re else z.re < 0)
    (hn : z.re ^ 2 + z.im ^ 2 = 1) :
    z ∈ closure (Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧ 1 < w.re ^ 2 + w.im ^ 2}) := by
  let V : Set H2 := Metric.ball p r ∩ {w : H2 |
    (if positive then 0 < w.re else w.re < 0) ∧ w.re ^ 2 + w.im ^ 2 < 1}
  let W : Set H2 := Metric.ball p r ∩ {w : H2 |
    (if positive then 0 < w.re else w.re < 0) ∧ 1 < w.re ^ 2 + w.im ^ 2}
  have hV : z ∈ closure V := unit_circle_mem_closure_inner_quarter p z r positive hz hs hn
  have himage : unitCircleReflectionEquiv '' V ⊆ W := by
    rintro w ⟨v, hv, rfl⟩
    have hpf := (unitCircleReflection_fixed_iff p).mpr hp
    have hball : unitCircleReflectionEquiv v ∈ Metric.ball p r := by
      change dist (unitCircleReflectionEquiv v) p < r
      calc
        _ = dist (unitCircleReflectionEquiv v) (unitCircleReflectionEquiv p) :=
          congrArg (dist (unitCircleReflectionEquiv v)) hpf.symm
        _ = dist v p := unitCircleReflectionEquiv.dist_eq _ _
        _ < r := hv.1
    have hnorm : 1 < (unitCircleReflectionEquiv v).re ^ 2 +
        (unitCircleReflectionEquiv v).im ^ 2 := by
      apply (unitCircleReflection_inner_iff_outer (unitCircleReflectionEquiv v)).mp
      rw [unitCircleReflection_involutive v]
      exact hv.2.2
    have hsign : if positive then 0 < (unitCircleReflectionEquiv v).re
        else (unitCircleReflectionEquiv v).re < 0 := by
      have hd : 0 < v.re ^ 2 + v.im ^ 2 := by nlinarith [v.im_pos]
      rw [unitCircleReflection_re]
      cases positive
      · change v.re / (v.re ^ 2 + v.im ^ 2) < 0
        rw [div_lt_iff₀ hd]
        simpa using hv.2.1
      · change 0 < v.re / (v.re ^ 2 + v.im ^ 2)
        exact div_pos hv.2.1 hd
    exact ⟨hball, hsign, hnorm⟩
  have hm : unitCircleReflectionEquiv z ∈ closure (unitCircleReflectionEquiv '' V) := by
    change unitCircleReflectionEquiv.toHomeomorph z ∈
      closure (unitCircleReflectionEquiv.toHomeomorph '' V)
    rw [← unitCircleReflectionEquiv.toHomeomorph.image_closure]
    exact ⟨z, hV, rfl⟩
  have hW := closure_mono himage hm
  rw [(unitCircleReflection_fixed_iff z).mpr hn] at hW
  exact hW

theorem vertical_axis_mem_closure_quarter (p z : H2) (r : ℝ) (positive inner : Bool)
    (hz : z ∈ Metric.ball p r) (hs : z.re = 0)
    (hn : if inner then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2) :
    z ∈ closure (Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧
      (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}) := by
  let A : Set H2 := Metric.ball p r ∩ {w : H2 |
    if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2}
  have hf : Continuous (fun w : H2 => w.re ^ 2 + w.im ^ 2) :=
    (UpperHalfPlane.continuous_re.pow 2).add (UpperHalfPlane.continuous_im.pow 2)
  have hA : IsOpen A := by
    apply Metric.isOpen_ball.inter
    cases inner
    · exact isOpen_lt continuous_const hf
    · exact isOpen_lt hf continuous_const
  have hhalf : z ∈ closure {w : H2 | if positive then 0 < w.re else w.re < 0} := by
    cases positive
    · change z ∈ closure (((↑) : H2 → ℂ) ⁻¹' {w : ℂ | w.re < 0})
      rw [← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
        UpperHalfPlane.continuous_coe, Complex.closure_setOfPred_re_lt]
      change z.re ≤ 0
      exact hs.le
    · change z ∈ closure (((↑) : H2 → ℂ) ⁻¹' {w : ℂ | 0 < w.re})
      rw [← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
        UpperHalfPlane.continuous_coe, Complex.closure_setOfPred_lt_re]
      change 0 ≤ z.re
      exact hs.ge
  have hm := hA.inter_closure (show z ∈ A ∩ closure
    {w : H2 | if positive then 0 < w.re else w.re < 0} from ⟨⟨hz, hn⟩, hhalf⟩)
  simpa only [A, Set.inter_assoc, ← Set.setOf_and, and_comm] using hm

theorem vertex_norm_condition_regularOpen (inner : Bool) :
    interior (closure {z : H2 | if inner then z.re ^ 2 + z.im ^ 2 < 1
      else 1 < z.re ^ 2 + z.im ^ 2}) =
      {z : H2 | if inner then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2} := by
  cases inner
  · change interior (closure {z : H2 | 1 < z.re ^ 2 + z.im ^ 2}) = _
    have he : {z : H2 | 1 < z.re ^ 2 + z.im ^ 2} =
        ((↑) : H2 → ℂ) ⁻¹' (Metric.closedBall 0 1)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Metric.mem_closedBall, dist_zero_right, not_le]
      have hn := Complex.normSq_eq_norm_sq (z : ℂ)
      simp only [Complex.normSq_apply] at hn
      change z.re * z.re + z.im * z.im = ‖(z : ℂ)‖ ^ 2 at hn
      constructor <;> intro h <;> nlinarith [norm_nonneg (z : ℂ)]
    rw [he, ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
      UpperHalfPlane.continuous_coe,
      ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
        UpperHalfPlane.continuous_coe,
      closure_compl, interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      interior_compl, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact he.symm
  · change interior (closure {z : H2 | z.re ^ 2 + z.im ^ 2 < 1}) = _
    rw [normSq_lt_one_eq_coe_ball,
      ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
        UpperHalfPlane.continuous_coe,
      ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
        UpperHalfPlane.continuous_coe,
      closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact normSq_lt_one_eq_coe_ball.symm

theorem vertex_real_condition_regularOpen (positive : Bool) :
    interior (closure {z : H2 | if positive then 0 < z.re else z.re < 0}) =
      {z : H2 | if positive then 0 < z.re else z.re < 0} := by
  cases positive
  · change interior (closure (((↑) : H2 → ℂ) ⁻¹' {w : ℂ | w.re < 0})) = _
    rw [← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
      UpperHalfPlane.continuous_coe,
      ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
        UpperHalfPlane.continuous_coe,
      Complex.closure_setOfPred_re_lt, Complex.interior_setOfPred_re_le]
    rfl
  · change interior (closure (((↑) : H2 → ℂ) ⁻¹' {w : ℂ | 0 < w.re})) = _
    rw [← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
      UpperHalfPlane.continuous_coe,
      ← UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
        UpperHalfPlane.continuous_coe,
      Complex.closure_setOfPred_lt_re, Complex.interior_setOfPred_le_re]
    rfl

end CurveComplex.Hyperbolic
