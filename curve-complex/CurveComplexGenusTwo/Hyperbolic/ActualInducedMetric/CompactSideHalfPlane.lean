import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfBallConnected
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactJordanRegionUniqueness
namespace CurveComplex.Hyperbolic
open Set Topology

private theorem moved_half_ball_preconnected (e : H2 ≃ᵢ H2) (x : H2) (ε : ℝ) :
    IsPreconnected (Metric.ball x ε ∩ {z : H2 | 0 < (e z).re}) ∧
    IsPreconnected (Metric.ball x ε ∩ {z : H2 | (e z).re < 0}) := by
  have himp : e '' (Metric.ball x ε ∩ {z : H2 | 0 < (e z).re}) =
      Metric.ball (e x) ε ∩ {z : H2 | 0 < z.re} := by
    change e '' (Metric.ball x ε ∩ e ⁻¹' {z : H2 | 0 < z.re}) = _
    rw [Set.image_inter_preimage, e.image_ball]
  have himn : e '' (Metric.ball x ε ∩ {z : H2 | (e z).re < 0}) =
      Metric.ball (e x) ε ∩ {z : H2 | z.re < 0} := by
    change e '' (Metric.ball x ε ∩ e ⁻¹' {z : H2 | z.re < 0}) = _
    rw [Set.image_inter_preimage, e.image_ball]
  constructor
  · apply e.toHomeomorph.isInducing.isPreconnected_image.mp
    change IsPreconnected (e '' (Metric.ball x ε ∩ {z : H2 | 0 < (e z).re}))
    rw [himp]
    exact (hyperbolic_half_ball_isPreconnected (e x) ε).1
  · apply e.toHomeomorph.isInducing.isPreconnected_image.mp
    change IsPreconnected (e '' (Metric.ball x ε ∩ {z : H2 | (e z).re < 0}))
    rw [himn]
    exact (hyperbolic_half_ball_isPreconnected (e x) ε).2

theorem HexagonRegion.actual_side_local_halfplane {P : Hexagon} (R : HexagonRegion P)
    (hP : P.IsEmbedded) (i : Fin 6) (x : H2) (hx : x ∈ P.edge i)
    (hxi : x ≠ P.vertex i) (hxn : x ≠ P.vertex (i + 1)) :
    ∃ e : H2 ≃ᵢ H2, (e x).re = 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ z ∈ Metric.ball x ε, z ∈ frontier R.interior ↔ (e z).re = 0) ∧
      ((∀ z ∈ Metric.ball x ε, z ∈ closure R.interior ↔ 0 ≤ (e z).re) ∨
       (∀ z ∈ Metric.ball x ε, z ∈ closure R.interior ↔ (e z).re ≤ 0)) := by
  obtain ⟨e, hxe, ε, he, hloc⟩ := P.actual_side_frontier_local_geodesic hP R i x hx hxi hxn
  let A := Metric.ball x ε ∩ {z : H2 | 0 < (e z).re}
  let B := Metric.ball x ε ∩ {z : H2 | (e z).re < 0}
  let O := (closure R.interior)ᶜ
  have hOopen : IsOpen O := isClosed_closure.isOpen_compl
  have hfrontO : frontier O = frontier R.interior := R.exterior_frontier_eq hP
  have hxf : x ∈ frontier R.interior := by
    rw [R.boundary_is_edges]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hxfO : x ∈ frontier O := hfrontO ▸ hxf
  have hA : IsPreconnected A := (moved_half_ball_preconnected e x ε).1
  have hB : IsPreconnected B := (moved_half_ball_preconnected e x ε).2
  have hdA : Disjoint (frontier R.interior) A := by
    apply Set.disjoint_left.mpr
    intro z hz hzA
    have hzero := (hloc z hzA.1).mp hz
    exact (ne_of_gt hzA.2) hzero
  have hdB : Disjoint (frontier R.interior) B := by
    apply Set.disjoint_left.mpr
    intro z hz hzB
    have hzero := (hloc z hzB.1).mp hz
    exact (ne_of_lt hzB.2) hzero
  have hdisO : Disjoint R.interior O := Set.disjoint_left.mpr
    (fun z hz hzO => hzO (subset_closure hz))
  have hnonzero (z : H2) (hz : z ∈ Metric.ball x ε) (hzR : z ∈ R.interior) : (e z).re ≠ 0 := by
    intro hzero
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr R.open_interior)
      ((hloc z hz).mpr hzero) hzR
  have hnonzeroO (z : H2) (hz : z ∈ Metric.ball x ε) (hzO : z ∈ O) : (e z).re ≠ 0 := by
    intro hzero
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hOopen)
      (hfrontO ▸ ((hloc z hz).mpr hzero)) hzO
  obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hxf) ε he
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hxfO) ε he
  have hyball : y ∈ Metric.ball x ε := by simpa [Metric.mem_ball, dist_comm] using hyd
  have hwball : w ∈ Metric.ball x ε := by simpa [Metric.mem_ball, dist_comm] using hwd
  have hpos (haR : A ⊆ R.interior) (hbO : B ⊆ O) :
      ∀ z ∈ Metric.ball x ε, z ∈ closure R.interior ↔ 0 ≤ (e z).re := by
    intro z hz
    constructor
    · intro hzR
      by_contra hn
      exact hbO ⟨hz, lt_of_not_ge hn⟩ hzR
    · intro hzre
      rcases eq_or_lt_of_le hzre with hzero | hgt
      · exact frontier_subset_closure ((hloc z hz).mpr hzero.symm)
      · exact subset_closure (haR ⟨hz, hgt⟩)
  have hneg (hbR : B ⊆ R.interior) (haO : A ⊆ O) :
      ∀ z ∈ Metric.ball x ε, z ∈ closure R.interior ↔ (e z).re ≤ 0 := by
    intro z hz
    constructor
    · intro hzR
      by_contra hn
      exact haO ⟨hz, lt_of_not_ge hn⟩ hzR
    · intro hzre
      rcases lt_or_eq_of_le hzre with hlt | hzero
      · exact subset_closure (hbR ⟨hz, hlt⟩)
      · exact frontier_subset_closure ((hloc z hz).mpr hzero)
  refine ⟨e, hxe, ε, he, hloc, ?_⟩
  rcases lt_or_gt_of_ne (hnonzero y hyball hy) with hyn | hyp
  · have hbR : B ⊆ R.interior := preconnected_subset_of_frontier_disjoint
      R.open_interior hB hdB ⟨y, ⟨hyball, hyn⟩, hy⟩
    have hwp : 0 < (e w).re := by
      rcases lt_or_gt_of_ne (hnonzeroO w hwball hw) with hwn | hwp
      · exact (Set.disjoint_left.mp hdisO (hbR ⟨hwball, hwn⟩) hw).elim
      · exact hwp
    have haO : A ⊆ O := preconnected_subset_of_frontier_disjoint hOopen hA
      (by rw [hfrontO]; exact hdA) ⟨w, ⟨hwball, hwp⟩, hw⟩
    exact Or.inr (hneg hbR haO)
  · have haR : A ⊆ R.interior := preconnected_subset_of_frontier_disjoint
      R.open_interior hA hdA ⟨y, ⟨hyball, hyp⟩, hy⟩
    have hwn : (e w).re < 0 := by
      rcases lt_or_gt_of_ne (hnonzeroO w hwball hw) with hwn | hwp
      · exact hwn
      · exact (Set.disjoint_left.mp hdisO (haR ⟨hwball, hwp⟩) hw).elim
    have hbO : B ⊆ O := preconnected_subset_of_frontier_disjoint hOopen hB
      (by rw [hfrontO]; exact hdB) ⟨w, ⟨hwball, hwn⟩, hw⟩
    exact Or.inl (hpos haR hbO)
end CurveComplex.Hyperbolic
