import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualVertexBoundary
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexSectorConnected
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactJordanRegionUniqueness

namespace CurveComplex.Hyperbolic
open Set Topology

def vertexQuarter (e : H2 ≃ᵢ H2) (x : H2) (r : ℝ) (positive inner : Bool) : Set H2 :=
  e ⁻¹' (Metric.ball (e x) r ∩ {z : H2 |
    (if positive then 0 < z.re else z.re < 0) ∧
    (if inner then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2)})

theorem vertexQuarter_preconnected (e : H2 ≃ᵢ H2) (x : H2) (r : ℝ)
    (hx : (e x).re ^ 2 + (e x).im ^ 2 = 1) (positive inner : Bool) :
    IsPreconnected (vertexQuarter e x r positive inner) := by
  have hi := hyperbolic_inner_quarter_ball_isPreconnected (e x) r
  have ho := hyperbolic_outer_quarter_ball_isPreconnected (e x) r hx
  have hp : IsPreconnected
      (Metric.ball (e x) r ∩ {z : H2 |
        (if positive then 0 < z.re else z.re < 0) ∧
        (if inner then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2)}) := by
    cases positive <;> cases inner
    · exact ho.2
    · exact hi.2
    · exact ho.1
    · exact hi.1
  have hm := hp.image e.symm e.symm.continuous.continuousOn
  convert hm using 1
  ext z
  simp only [vertexQuarter, Set.mem_preimage, Set.mem_image]
  constructor
  · intro hz
    exact ⟨e z, hz, e.symm_apply_apply z⟩
  · rintro ⟨w, hw, heq⟩
    subst z
    simpa only [e.apply_symm_apply] using hw

theorem HexagonRegion.actual_vertex_sector_dichotomy
    {P : Hexagon} (R : HexagonRegion P) (hP : P.IsRegularRight) (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (P.vertex i)).re = 0 ∧ (e (P.vertex i)).im = 1 ∧
      ∃ r : ℝ, 0 < r ∧ ∀ positive inner : Bool,
        vertexQuarter e (P.vertex i) r positive inner ⊆ R.interior ∨
        vertexQuarter e (P.vertex i) r positive inner ⊆ (closure R.interior)ᶜ := by
  classical
  obtain ⟨e, hp, hi, r, hr, hfront⟩ := R.actual_right_angle_vertex_boundary_coordinates hP i
  refine ⟨e, hp, hi, r, hr, ?_⟩
  intro positive inner
  let V := vertexQuarter e (P.vertex i) r positive inner
  have hv : IsPreconnected V := vertexQuarter_preconnected e (P.vertex i) r
    (by rw [hp, hi]; norm_num) positive inner
  have hd : Disjoint (frontier R.interior) V := by
    apply Set.disjoint_left.mpr
    intro z hz hvz
    have hball : z ∈ Metric.ball (P.vertex i) r := by
      have hh := hvz.1
      simpa only [Metric.mem_ball, e.dist_eq] using hh
    have ht := hfront z hball hz
    have hcoords := hvz.2
    change (if positive then 0 < (e z).re else (e z).re < 0) ∧
      (if inner then (e z).re ^ 2 + (e z).im ^ 2 < 1 else
        1 < (e z).re ^ 2 + (e z).im ^ 2) at hcoords
    cases positive <;> cases inner <;>
      simp at hcoords <;> rcases ht with ht | ht <;> linarith [hcoords.1, hcoords.2]
  by_cases hn : (V ∩ R.interior).Nonempty
  · exact Or.inl (preconnected_subset_of_frontier_disjoint R.open_interior hv hd hn)
  · right
    intro z hz hcl
    have hznot : z ∉ R.interior := by
      intro hzi
      exact hn ⟨z, hz, hzi⟩
    have hf : z ∈ frontier R.interior := by
      rw [frontier, R.open_interior.interior_eq]
      exact ⟨hcl, hznot⟩
    exact Set.disjoint_left.mp hd hf hz

end CurveComplex.Hyperbolic
