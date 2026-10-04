import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexAxesInterior

namespace CurveComplex.Hyperbolic
open Set Topology

theorem off_vertex_axes_quarter_classification (z : H2) (hr : z.re ≠ 0)
    (hn : z.re ^ 2 + z.im ^ 2 ≠ 1) : ∃ a b : Bool,
      (if a then 0 < z.re else z.re < 0) ∧
      (if b then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2) := by
  rcases lt_or_gt_of_ne hr with h | h <;> rcases lt_or_gt_of_ne hn with h' | h'
  · exact ⟨false, true, h, h'⟩
  · exact ⟨false, false, h, h'⟩
  · exact ⟨true, true, h, h'⟩
  · exact ⟨true, false, h, h'⟩

theorem open_set_vertex_quarter_identification (U : Set H2) (hU : IsOpen U)
    (p : H2) (r : ℝ) (a b : Bool) (hball : U ⊆ Metric.ball p r)
    (hoff : ∀ z ∈ U, z.re ≠ 0 → z.re ^ 2 + z.im ^ 2 ≠ 1 →
      (if a then 0 < z.re else z.re < 0) ∧
      (if b then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2)) :
    U ⊆ Metric.ball p r ∩ {z : H2 |
      (if a then 0 < z.re else z.re < 0) ∧
      (if b then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2)} := by
  let Q : Set H2 := Metric.ball p r ∩ {z : H2 |
    (if a then 0 < z.re else z.re < 0) ∧
    (if b then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2)}
  have hcl : U ⊆ closure Q := by
    intro z hz
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨W, hWV, hW, hzW⟩ := mem_nhds_iff.mp hV
    obtain ⟨w, hw, hwr, hwn⟩ := open_set_contains_point_off_vertex_axes
      (U ∩ W) (hU.inter hW) ⟨z, hz, hzW⟩
    exact ⟨w, hWV hw.2, hball hw.1, hoff w hw.1 hwr hwn⟩
  have hint : U ⊆ interior (closure Q) := by
    simpa only [hU.interior_eq] using interior_mono hcl
  have hreal : interior (closure Q) ⊆ {z : H2 | if a then 0 < z.re else z.re < 0} := by
    have hsub : Q ⊆ {z : H2 | if a then 0 < z.re else z.re < 0} := fun z hz => hz.2.1
    have h := interior_mono (closure_mono hsub)
    rw [vertex_real_condition_regularOpen] at h
    exact h
  have hnorm : interior (closure Q) ⊆ {z : H2 | if b then z.re ^ 2 + z.im ^ 2 < 1
      else 1 < z.re ^ 2 + z.im ^ 2} := by
    have hsub : Q ⊆ {z : H2 | if b then z.re ^ 2 + z.im ^ 2 < 1
        else 1 < z.re ^ 2 + z.im ^ 2} := fun z hz => hz.2.2
    have h := interior_mono (closure_mono hsub)
    rw [vertex_norm_condition_regularOpen] at h
    exact h
  intro z hz
  exact ⟨hball hz, hreal (hint hz), hnorm (hint hz)⟩

end CurveComplex.Hyperbolic
