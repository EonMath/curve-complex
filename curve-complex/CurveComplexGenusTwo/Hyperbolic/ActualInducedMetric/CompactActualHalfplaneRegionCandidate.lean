import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactClosedHalfplaneRadialBoundCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalDiscEdgeCandidate

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def regularHexagonActualHalfplaneInterior : Set H2 :=
  {z | ∀ i : Fin 6, 0 < regularHexagonSideEquation i (cayley z : ℂ)}

theorem regular_hexagon_actual_side_continuous (i : Fin 6) :
    Continuous (fun z : H2 => regularHexagonSideEquation i (cayley z : ℂ)) := by
  have hc : Continuous (fun z : H2 => (cayley z : ℂ)) := continuous_subtype_val.comp cayley_continuous
  have hf : Continuous (regularHexagonSideEquation i) := by unfold regularHexagonSideEquation; fun_prop
  exact hf.comp hc

theorem regular_hexagon_actual_halfplane_open : IsOpen regularHexagonActualHalfplaneInterior := by
  have he : regularHexagonActualHalfplaneInterior = (⋂ i : Fin 6, {z : H2 | 0 < regularHexagonSideEquation i (cayley z : ℂ)}) := by ext z; simp [regularHexagonActualHalfplaneInterior]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (regular_hexagon_actual_side_continuous i))

theorem regular_hexagon_actual_halfplane_connected : IsConnected regularHexagonActualHalfplaneInterior := by
  let f : H2 → ℂ := fun z => (cayley z : ℂ)
  have hi : Function.Injective f := Subtype.val_injective.comp cayley_injective
  have ho : IsOpenMap f := by
    change IsOpenMap (Subtype.val ∘ cayleyHomeomorph)
    exact Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap.comp cayleyHomeomorph.isOpenMap
  have hr : regularHexagonDiscHalfplaneInterior ⊆ range f := by
    intro w hw
    have hn : w ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_def]
      have h := Real.sqrt_lt_sqrt (Complex.normSq_nonneg w) hw.1
      simpa only [Real.sqrt_one] using h
    exact ⟨cayleyInverse ⟨w, hn⟩, cayley_cayleyInverse ⟨w, hn⟩⟩
  have he : f ⁻¹' regularHexagonDiscHalfplaneInterior = regularHexagonActualHalfplaneInterior := by
    ext z
    change (Complex.normSq (cayley z : ℂ) < 1 ∧ _) ↔ _
    have hnorm : Complex.normSq (cayley z : ℂ) < 1 := by
      have hn : ‖(cayley z : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right, cayley] using cayley_mem_ball z
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (cayley z : ℂ)]
    exact and_iff_right hnorm
  rw [← he]
  exact regular_hexagon_disc_halfplane_connected.preimage_of_isOpenMap hi ho hr

theorem regular_hexagon_actual_halfplane_closure_side (z : H2)
    (hz : z ∈ closure regularHexagonActualHalfplaneInterior) (i : Fin 6) :
    0 ≤ regularHexagonSideEquation i (cayley z : ℂ) := by
  have hs : regularHexagonActualHalfplaneInterior ⊆
      {z : H2 | 0 ≤ regularHexagonSideEquation i (cayley z : ℂ)} := fun z hz => (hz i).le
  exact (closure_minimal hs (isClosed_le continuous_const (regular_hexagon_actual_side_continuous i))) hz

theorem regular_hexagon_actual_halfplane_bounded :
    Bornology.IsBounded regularHexagonActualHalfplaneInterior := by
  apply (Metric.isBounded_closedBall (x := regularHexagonCenter)
    (r := dist regularHexagonCenter (regularHexagonCandidate.vertex 0))).subset
  intro z hz
  have hn : Complex.normSq (cayley z : ℂ) ≤ 1 := by
    have h : ‖(cayley z : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right, cayley] using cayley_mem_ball z
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (cayley z : ℂ)]
  have hb := regular_hexagon_closed_side_disc_radial_bound (cayley z : ℂ) hn (fun i => (hz i).le)
  have hd := regular_hexagon_disc_radius_cosh_bound z hb
  rw [← regularHexagon_center_cosh_vertex 0] at hd
  have hd' : dist regularHexagonCenter z ≤ dist regularHexagonCenter (regularHexagonCandidate.vertex 0) :=
    (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp hd
  simpa only [Metric.mem_closedBall, dist_comm] using hd'

theorem regular_hexagon_actual_halfplane_frontier_subset :
    frontier regularHexagonActualHalfplaneInterior ⊆ frontier regularHexagonRegion.interior := by
  intro z hz
  have hcl := frontier_subset_closure hz
  have hs := regular_hexagon_actual_halfplane_closure_side z hcl
  have hnot : z ∉ regularHexagonActualHalfplaneInterior :=
    fun h => Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr regular_hexagon_actual_halfplane_open) hz h
  have hex : ∃ i : Fin 6, regularHexagonSideEquation i (cayley z : ℂ) = 0 := by
    by_contra h
    apply hnot
    intro i
    exact lt_of_le_of_ne (hs i) (Ne.symm (not_exists.mp h i))
  obtain ⟨i, hi⟩ := hex
  have hn : Complex.normSq (cayley z : ℂ) ≤ 1 := by
    have h : ‖(cayley z : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right, cayley] using cayley_mem_ball z
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (cayley z : ℂ)]
  have hb := regular_hexagon_closed_side_disc_radial_bound (cayley z : ℂ) hn hs
  have hedge : z ∈ regularHexagonCandidate.edge i := regular_hexagon_side_geodesic_radial_cut i ▸ ⟨hi, hb⟩
  rw [regularHexagonRegion.boundary_is_edges]
  exact mem_iUnion.mpr ⟨i, hedge⟩

end CurveComplex.Hyperbolic
