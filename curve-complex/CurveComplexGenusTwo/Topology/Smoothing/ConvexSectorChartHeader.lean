import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import Mathlib.Analysis.Convex.GaugeRescale
open Set Metric Schoenflies Bornology

-- A genuine ambient chart and Jordan boundary are produced from convex
-- geometric sector data, with no supplied disk parametrization.
theorem convex_sector_ambient_square_chart (Q : Set Plane) (hc : Convex ℝ Q) (hQ : IsClosed Q)
    (hne : (interior Q).Nonempty) (hb : IsBounded Q) :
    ∃ E : Plane ≃ₜ Plane,
      E '' interior Q = Plane.openSquare 0 1 ∧
      E '' Q = Plane.closedSquare 0 1 ∧
      E '' frontier Q = modelCurve ∧ IsJordanCurve (frontier Q) := by
  have hnesq : (interior (Plane.closedSquare 0 1)).Nonempty := by
    rw [interior_closedSquare_zero_one]
    refine ⟨0, mem_openSquare_zero_one.mpr ?_⟩
    norm_num [Plane.supNorm]
  obtain ⟨E,hEi,hEc,hEf⟩ := exists_homeomorph_image_eq hc hne
    (NormedSpace.isVonNBounded_of_isBounded ℝ hb)
    (Plane.convex_closedSquare 0 1) hnesq
    (NormedSpace.isVonNBounded_of_isBounded ℝ (Plane.isBounded_closedSquare 0 1))
  have hi : E '' interior Q = Plane.openSquare 0 1 := by
    simpa only [interior_closedSquare_zero_one] using hEi
  have hq : E '' Q = Plane.closedSquare 0 1 := by
    simpa only [hQ.closure_eq, (Plane.isClosed_closedSquare 0 1).closure_eq] using hEc
  have hf : E '' frontier Q = modelCurve := by
    simpa only [← modelCurve_eq_frontier] using hEf
  refine ⟨E,hi,hq,hf,?_⟩
  obtain ⟨f,hfloop,hfimage⟩ := isJordanCurve_modelCurve
  refine ⟨E.symm ∘ f, ?_, ?_⟩
  · rcases hfloop with ⟨hfcont,hfclose,hfinj⟩
    refine ⟨E.symm.continuous.comp_continuousOn hfcont, ?_, ?_⟩
    · exact congrArg E.symm hfclose
    · intro x hx y hy he
      exact hfinj hx hy (E.symm.injective he)
  · rw [image_comp, hfimage, ← hf]
    exact E.symm_image_image (frontier Q)

#print axioms convex_sector_ambient_square_chart
