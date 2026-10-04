import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSeamIsolation
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactEdgeReflection
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDoubleInteriorCharts
namespace CurveComplex.Hyperbolic
open Set Topology

theorem metric_segment_local_full_geodesic (a b x : H2) (hab : a ≠ b)
    (hx : dist a x + dist x b = dist a b) (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ e : H2 ≃ᵢ H2, (e a).re = 0 ∧ (e b).re = 0 ∧ (e x).re = 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball x ε,
        (dist a z + dist z b = dist a b ↔ (e z).re = 0) := by
  obtain ⟨e, ha, hb⟩ := exists_pair_vertical_isometry a b
  obtain ⟨hxr, hxt⟩ := (metric_segment_iff_in_vertical_interval e a b x ha hb).mp hx
  let α := Real.log (e a).im
  let β := Real.log (e b).im
  let t := Real.log (e x).im
  have hta : t ≠ α := by
    intro he
    apply hxa
    apply e.injective
    apply UpperHalfPlane.ext_re_im
    · exact hxr.trans ha.symm
    · exact (Real.log_injOn_pos (e x).im_pos (e a).im_pos) he
  have htb : t ≠ β := by
    intro he
    apply hxb
    apply e.injective
    apply UpperHalfPlane.ext_re_im
    · exact hxr.trans hb.symm
    · exact (Real.log_injOn_pos (e x).im_pos (e b).im_pos) he
  have htt : min α β < t ∧ t < max α β := by
    rcases le_total α β with h | h
    · rw [Set.uIcc_of_le h] at hxt
      simpa [min_eq_left h, max_eq_right h] using
        And.intro (lt_of_le_of_ne hxt.1 hta.symm) (lt_of_le_of_ne hxt.2 htb)
    · rw [Set.uIcc_of_ge h] at hxt
      simpa [min_eq_right h, max_eq_left h] using
        And.intro (lt_of_le_of_ne hxt.1 htb.symm) (lt_of_le_of_ne hxt.2 hta)
  let U := {z : H2 | min α β < Real.log (e z).im ∧ Real.log (e z).im < max α β}
  have hlog : Continuous (fun z : H2 => Real.log (e z).im) :=
    (UpperHalfPlane.continuous_im.comp e.continuous).log (fun z => (e z).im_ne_zero)
  have hopen : IsOpen U := (isOpen_lt continuous_const hlog).inter
    (isOpen_lt hlog continuous_const)
  obtain ⟨ε, he, hball⟩ := Metric.isOpen_iff.mp hopen x htt
  refine ⟨e, ha, hb, hxr, ε, he, ?_⟩
  intro z hz
  rw [metric_segment_iff_in_vertical_interval e a b z ha hb]
  constructor
  · exact And.left
  · intro hzr
    refine ⟨hzr, ?_⟩
    exact ⟨(hball hz).1.le, (hball hz).2.le⟩

theorem Hexagon.actual_side_frontier_local_geodesic (P : Hexagon) (hP : P.IsEmbedded)
    (R : HexagonRegion P) (i : Fin 6) (x : H2) (hx : x ∈ P.edge i)
    (hxi : x ≠ P.vertex i) (hxn : x ≠ P.vertex (i + 1)) :
    ∃ e : H2 ≃ᵢ H2, (e x).re = 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ Metric.ball x ε, z ∈ frontier R.interior ↔ (e z).re = 0 := by
  have hne : P.vertex i ≠ P.vertex (i + 1) := by
    intro h
    have hi := P.injective h
    fin_cases i <;> norm_num at hi
  obtain ⟨e, _, _, hxe, ε, he, hloc⟩ := metric_segment_local_full_geodesic
    (P.vertex i) (P.vertex (i + 1)) x hne hx hxi hxn
  obtain ⟨δ, hd, hiso⟩ := P.embedded_side_local_isolation hP i x hx hxi hxn
  refine ⟨e, hxe, min ε δ, lt_min he hd, ?_⟩
  intro z hz
  have hze : z ∈ Metric.ball x ε :=
    Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _))
  have hzd : z ∈ Metric.ball x δ :=
    Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))
  rw [R.boundary_is_edges]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    by_cases hji : j = i
    · subst j
      exact (hloc z hze).mp hj
    · exact ((Set.disjoint_left.mp (hiso j hji)) hzd hj).elim
  · intro h
    exact Set.mem_iUnion.mpr ⟨i, (hloc z hze).mpr h⟩
end CurveComplex.Hyperbolic
