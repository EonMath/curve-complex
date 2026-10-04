import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactUnitSemicircleParam

namespace CurveComplex.Hyperbolic
open Set Topology

theorem normalized_vertex_mem_closure_quarter (p : H2) (hp : p.re = 0) (hi : p.im = 1)
    (r : ℝ) (hr : 0 < r) (positive inner : Bool) :
    p ∈ closure (Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧
      (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}) := by
  let Q : Set H2 := Metric.ball p r ∩ {w : H2 |
    (if positive then 0 < w.re else w.re < 0) ∧
    (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}
  have hcl : p ∈ closure (closure Q) := by
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨z, hz, hn, hs⟩ := unit_circle_point_of_either_sign_in_ball p hp hi
      (min δ r) (lt_min hδ hr) positive
    have hzV : z ∈ V := hball
      (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _)))
    have hzr : z ∈ Metric.ball p r :=
      Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _))
    have hzcl : z ∈ closure Q := by
      cases inner
      · exact unit_circle_mem_closure_outer_quarter p z r positive
          (by rw [hp, hi]; norm_num) hzr hs hn
      · exact unit_circle_mem_closure_inner_quarter p z r positive hzr hs hn
    exact ⟨z, hzV, hzcl⟩
  simpa only [closure_closure] using hcl

theorem normalized_closed_quarter_model (p : H2) (hp : p.re = 0) (hi : p.im = 1)
    (r : ℝ) (hr : 0 < r) (positive inner : Bool) (z : H2) (hz : z ∈ Metric.ball p r) :
    z ∈ closure (Metric.ball p r ∩ {w : H2 |
      (if positive then 0 < w.re else w.re < 0) ∧
      (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}) ↔
      (if positive then 0 ≤ z.re else z.re ≤ 0) ∧
      (if inner then z.re ^ 2 + z.im ^ 2 ≤ 1 else 1 ≤ z.re ^ 2 + z.im ^ 2) := by
  let Q : Set H2 := Metric.ball p r ∩ {w : H2 |
    (if positive then 0 < w.re else w.re < 0) ∧
    (if inner then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}
  constructor
  · intro hcl
    constructor
    · have hclosed : IsClosed {w : H2 | if positive then 0 ≤ w.re else w.re ≤ 0} := by
        cases positive
        · exact isClosed_le UpperHalfPlane.continuous_re continuous_const
        · exact isClosed_le continuous_const UpperHalfPlane.continuous_re
      apply closure_minimal (t := {w : H2 | if positive then 0 ≤ w.re else w.re ≤ 0}) ?_ hclosed hcl
      intro w hw
      have hs := hw.2.1
      cases positive <;> exact hs.le
    · have hf : Continuous (fun w : H2 => w.re ^ 2 + w.im ^ 2) :=
        (UpperHalfPlane.continuous_re.pow 2).add (UpperHalfPlane.continuous_im.pow 2)
      have hclosed : IsClosed {w : H2 | if inner then w.re ^ 2 + w.im ^ 2 ≤ 1
          else 1 ≤ w.re ^ 2 + w.im ^ 2} := by
        cases inner
        · exact isClosed_le continuous_const hf
        · exact isClosed_le hf continuous_const
      apply closure_minimal (t := {w : H2 | if inner then w.re ^ 2 + w.im ^ 2 ≤ 1
        else 1 ≤ w.re ^ 2 + w.im ^ 2}) ?_ hclosed hcl
      intro w hw
      have hs := hw.2.2
      cases inner <;> exact hs.le
  · rintro ⟨hreal, hnorm⟩
    by_cases hzr : z.re = 0
    · by_cases hzn : z.re ^ 2 + z.im ^ 2 = 1
      · have hzp : z = p := by
          apply UpperHalfPlane.ext_re_im
          · exact hzr.trans hp.symm
          · have hzim : z.im = 1 := by rw [hzr] at hzn; nlinarith [z.im_pos]
            exact hzim.trans hi.symm
        subst z
        exact normalized_vertex_mem_closure_quarter p hp hi r hr positive inner
      · apply vertical_axis_mem_closure_quarter p z r positive inner hz hzr
        cases inner
        · exact lt_of_le_of_ne hnorm (Ne.symm hzn)
        · exact lt_of_le_of_ne hnorm hzn
    · have hs : if positive then 0 < z.re else z.re < 0 := by
        cases positive
        · exact lt_of_le_of_ne hreal hzr
        · exact lt_of_le_of_ne hreal (Ne.symm hzr)
      by_cases hzn : z.re ^ 2 + z.im ^ 2 = 1
      · cases inner
        · exact unit_circle_mem_closure_outer_quarter p z r positive
            (by rw [hp, hi]; norm_num) hz hs hzn
        · exact unit_circle_mem_closure_inner_quarter p z r positive hz hs hzn
      · apply subset_closure
        refine ⟨hz, hs, ?_⟩
        cases inner
        · exact lt_of_le_of_ne hnorm (Ne.symm hzn)
        · exact lt_of_le_of_ne hnorm hzn

end CurveComplex.Hyperbolic
