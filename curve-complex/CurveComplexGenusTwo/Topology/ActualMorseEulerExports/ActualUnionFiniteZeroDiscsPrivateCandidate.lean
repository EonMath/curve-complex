import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Separation.Hausdorff
open Set Metric Topology Filter
open scoped Manifold
set_option backward.isDefEq.respectTransparency false
private theorem actual_finite_union_zero_discs_with_arbitrary_positive_radius_bounds
    {E : Type} [DecidableEq E] [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    (S T : Finset E) (b : E → ℝ) (hb : ∀ q, 0 < b q) :
    ∃ ρ : E → ℝ,
      (∀ q, 0 < ρ q ∧ ρ q < b q ∧
        closedBall ((chartAt ℂ q) q) (ρ q) ⊆ (chartAt ℂ q).target) ∧
      ((↑(S ∪ T) : Set E).PairwiseDisjoint
        (fun q => (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) (ρ q))) ∧
      ∀ q ∈ S ∪ T,
        q ∈ (chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) (ρ q) ∧
        IsOpen ((chartAt ℂ q).symm '' ball ((chartAt ℂ q) q) (ρ q)) ∧
        IsCompact ((chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) (ρ q)) ∧
        ∀ x ∈ (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) (ρ q),
          x ∈ S ∪ T → x = q := by
  classical
  have hfinite : (↑(S ∪ T) : Set E).Finite := (S ∪ T).finite_toSet
  obtain ⟨U,hU,hdisj⟩ := hfinite.t2_separation
  have hrad (q : E) : ∃ r : ℝ, 0 < r ∧ r < b q ∧
      closedBall ((chartAt ℂ q) q) r ⊆ (chartAt ℂ q).target ∧
      (chartAt ℂ q).symm '' closedBall ((chartAt ℂ q) q) r ⊆ U q := by
    let c := chartAt ℂ q
    have hq : q ∈ c.source := mem_chart_source ℂ q
    have hcq : c q ∈ c.target := c.map_source hq
    have hev : ∀ᶠ z in 𝓝 (c q), z ∈ c.target ∧ c.symm z ∈ U q := by
      have ht : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
        simpa only [c.left_inv hq] using (c.symm.continuousAt hcq).tendsto
      have htarg : ∀ᶠ z in 𝓝 (c q), z ∈ c.target := c.open_target.mem_nhds hcq
      exact htarg.and
        (ht.eventually ((hU q).2.mem_nhds (hU q).1))
    obtain ⟨ε,hε,hεall⟩ := Metric.eventually_nhds_iff_ball.mp hev
    let r := min ε (b q)/2
    have hr : 0 < r := half_pos (lt_min hε (hb q))
    have hrε : r < ε := lt_of_lt_of_le (half_lt_self (lt_min hε (hb q))) (min_le_left ε (b q))
    have hrb : r < b q := lt_of_lt_of_le (half_lt_self (lt_min hε (hb q))) (min_le_right ε (b q))
    refine ⟨r,hr,hrb,?_,?_⟩
    · intro z hz
      exact (hεall z (closedBall_subset_ball hrε hz)).1
    · rintro x ⟨z,hz,rfl⟩
      exact (hεall z (closedBall_subset_ball hrε hz)).2
  choose ρ hρ hρb htarget hUsub using hrad
  refine ⟨ρ,fun q => ⟨hρ q,hρb q,htarget q⟩,?_,?_⟩
  · intro q hq r hr hqr
    exact (hdisj hq hr hqr).mono (hUsub q) (hUsub r)
  · intro q hq
    let c := chartAt ℂ q
    refine ⟨⟨c q,mem_ball_self (hρ q),c.left_inv (mem_chart_source ℂ q)⟩,
      c.symm.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans (htarget q)),
      (isCompact_closedBall (c q) (ρ q)).image_of_continuousOn
        (c.symm.continuousOn.mono (htarget q)),?_⟩
    intro x hx hxZ
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hq hxZ (Ne.symm hne))
      (hUsub q hx) (hU x).1
