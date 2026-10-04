import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualRealContactTraceBranchParameter
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual interpolation of a normalized positive contact coordinate remains
in its existing range. No convex target-chart or trace filling is assumed. -/
theorem actual_positive_scalar_trace_interpolation_in_range
    (f : C(Icc (0:ℝ) (1/2),ℝ))
    (hzero : f ⟨0,le_rfl,by norm_num⟩=0)
    (hone : f ⟨1/2,by norm_num,le_rfl⟩=1)
    (hpos : ∀ t,0<t.val → 0<f t)
    (σ : unitInterval) (t : Icc (0:ℝ) (1/2)) :
    (1-(σ:ℝ))*f t+(σ:ℝ)*(2*t.val) ∈ range f := by
  let : PreconnectedSpace (Icc (0:ℝ) (1/2)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have ht : 0≤f t := by
    by_cases h : 0<t.val
    · exact (hpos t h).le
    · have he : t=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt h) t.property.1)
      rw [he,hzero]
  have hx0 : 0≤(1-(σ:ℝ))*f t+(σ:ℝ)*(2*t.val) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr σ.property.2) ht)
      (mul_nonneg σ.property.1 (mul_nonneg (by norm_num) t.property.1))
  have hxM : (1-(σ:ℝ))*f t+(σ:ℝ)*(2*t.val)≤ max (f t) 1 := by
    have h0 := mul_nonneg (sub_nonneg.mpr σ.property.2)
      (sub_nonneg.mpr (le_max_left (f t) 1))
    have h2 : 2*t.val≤ max (f t) 1 :=
      (by nlinarith only [t.property.2] : 2*t.val≤1).trans (le_max_right _ _)
    have h1 := mul_nonneg σ.property.1 (sub_nonneg.mpr h2)
    nlinarith
  rcases le_total (f t) 1 with hf | hf
  · apply intermediate_value_univ ⟨0,le_rfl,by norm_num⟩
      ⟨1/2,by norm_num,le_rfl⟩ f.continuous
    rw [hzero,hone]
    exact ⟨hx0,by simpa only [max_eq_right hf] using hxM⟩
  · apply intermediate_value_univ ⟨0,le_rfl,by norm_num⟩ t f.continuous
    rw [hzero]
    exact ⟨hx0,by simpa only [max_eq_left hf] using hxM⟩
end CurveComplex.HyperellipticModel
