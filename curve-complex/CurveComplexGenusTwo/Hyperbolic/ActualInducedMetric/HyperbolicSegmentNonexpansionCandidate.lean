import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ConstantSpeedHyperbolicSegmentCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.LocalPathDistanceCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicMetricBallConvex

namespace CurveComplex.Hyperbolic
open Set

theorem hyperbolic_segment_nonexpansion_of_local_bound {B : Type} [PseudoMetricSpace B]
    (f : H2 → B) (s : Set H2) (hf : ContinuousOn f s)
    (hlocal : ∀ z ∈ s, ∃ ε : ℝ, 0 < ε ∧
      ∀ w ∈ s, dist z w < ε → dist (f z) (f w) ≤ dist z w)
    (a b : H2) (hsegment : {z | dist a z + dist z b = dist a b} ⊆ s) :
    dist (f a) (f b) ≤ dist a b := by
  by_cases hab : a = b
  · subst b; simp
  obtain ⟨p, hp, hinj, hp0, hp1, hrange, hspeed⟩ :=
    metric_segment_has_constant_speed_parametrization a b hab
  have hmaps : MapsTo p (Icc 0 1) s := by
    intro t ht
    have hseg : dist a (p t) + dist (p t) b = dist a b := by
      have : p t ∈ p '' Icc 0 1 := ⟨t, ht, rfl⟩
      rwa [hrange] at this
    exact hsegment hseg
  have hcont : ContinuousOn (f ∘ p) (Icc 0 1) := hf.comp hp.continuousOn hmaps
  have hbound := interval_distance_bound_of_local_forward_bound (f ∘ p) 0 1 (dist a b)
    (by norm_num) hcont (by
      intro t ht
      obtain ⟨ε, hε, he⟩ := hlocal (p t) (hmaps ⟨ht.1, ht.2.le⟩)
      have hL : 0 < dist a b := dist_pos.mpr hab
      refine ⟨ε / dist a b, div_pos hε hL, ?_⟩
      intro u hu hue
      have hdist : dist (p t) (p u) = dist a b * (u - t) := by
        rw [hspeed, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hu.1)]
      have hshort : dist (p t) (p u) < ε := by
        rw [hdist]
        have hu' : u - t < ε / dist a b := by linarith
        exact (lt_div_iff₀ hL).mp hu' |> fun h => by simpa only [mul_comm] using h
      simpa only [Function.comp_apply, hdist] using he (p u) (hmaps ⟨ht.1.trans hu.1, hu.2⟩) hshort)
  simpa only [Function.comp_apply, hp0, hp1, sub_zero, mul_one] using hbound

end CurveComplex.Hyperbolic
