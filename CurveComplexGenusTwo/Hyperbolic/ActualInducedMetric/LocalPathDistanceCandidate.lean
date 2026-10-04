import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import Mathlib.Topology.Order.IntermediateValue

namespace CurveComplex.Hyperbolic
open Set

theorem interval_distance_bound_of_local_forward_bound {B : Type} [PseudoMetricSpace B]
    (f : ℝ → B) (a b L : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hlocal : ∀ t ∈ Ico a b, ∃ ε : ℝ, 0 < ε ∧
      ∀ u ∈ Icc t b, u < t + ε → dist (f t) (f u) ≤ L * (u - t)) :
    dist (f a) (f b) ≤ L * (b - a) := by
  let s : Set ℝ := {t | dist (f a) (f t) ≤ L * (t - a)}
  have hs : IsClosed (s ∩ Icc a b) := by
    have h : IsClosed {t ∈ Icc a b | dist (f a) (f t) ≤ L * (t - a)} :=
      isClosed_Icc.isClosed_le (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hf))
      ((continuousOn_id.sub continuousOn_const).const_mul L)
    simpa [s, Set.inter_def, and_comm] using h
  apply hs.mem_of_ge_of_forall_exists_gt (by simp [s]) hab
  intro t ht
  obtain ⟨ε, hε, hbound⟩ := hlocal t ht.2
  let u := t + min ε (b - t) / 2
  have hmin : 0 < min ε (b - t) := lt_min hε (sub_pos.mpr ht.2.2)
  have htu : t < u := by dsimp [u]; linarith
  have hub : u ≤ b := by
    have := min_le_right ε (b - t)
    dsimp [u]; linarith
  have hue : u < t + ε := by
    have := min_le_left ε (b - t)
    dsimp [u]; linarith
  refine ⟨u, ?_, htu, hub⟩
  have hstep := hbound u ⟨htu.le, hub⟩ hue
  have hstart : dist (f a) (f t) ≤ L * (t - a) := ht.1
  change dist (f a) (f u) ≤ L * (u - a)
  calc
    dist (f a) (f u) ≤ dist (f a) (f t) + dist (f t) (f u) := dist_triangle _ _ _
    _ ≤ L * (t - a) + L * (u - t) := add_le_add hstart hstep
    _ = L * (u - a) := by ring

end CurveComplex.Hyperbolic
