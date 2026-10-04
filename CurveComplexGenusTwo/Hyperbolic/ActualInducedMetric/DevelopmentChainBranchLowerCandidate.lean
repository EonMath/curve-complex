import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainLawsCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicMetricBallConvex

namespace CurveComplex.Hyperbolic
open Set
variable {E : Type} [TopologicalSpace E]

theorem developmentChain_branch_chart_lower_bound {B : Type} [MetricSpace B]
    (b : E → B) (F : Set (OpenPartialHomeomorph E H2))
    (hballs : ∀ a ∈ F, ∃ c : H2, ∃ s : ℝ, a.target = Metric.ball c s)
    (hcontract : ∀ a ∈ F, ∀ y ∈ a.source, ∀ z ∈ a.source,
      dist (b y) (b z) ≤ dist (a y) (a z))
    (e : OpenPartialHomeomorph E H2)
    (htransition : ∀ a ∈ F, ∀ y ∈ a.source, ∀ z ∈ a.source,
      (∀ v : H2, dist (a y) v + dist v (a z) = dist (a y) (a z) → a.symm v ∈ e.source) →
      dist (e y) (e z) ≤ dist (a y) (a z))
    (o : B) (R : ℝ) (hcover : b ⁻¹' Metric.ball o R ⊆ e.source)
    {x y : E} {r : ENNReal} (h : DevelopmentChain F x y r) :
    r ≠ ⊤ → dist (b x) o + r.toReal < R → dist (e x) (e y) ≤ r.toReal := by
  induction h with
  | nil x => intro _ _; simp
  | @cons x y z t a ha hx hy tail ih =>
    intro hfin hbudget
    have htfin : t ≠ ⊤ := (ENNReal.add_ne_top.mp hfin).2
    have hcost : (edist (a x) (a y) + t).toReal = dist (a x) (a y) + t.toReal := by
      rw [ENNReal.toReal_add (edist_ne_top (a x) (a y)) htfin]
      simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    rw [hcost] at hbudget ⊢
    obtain ⟨c, s, htarget⟩ := hballs a ha
    have hseg : ∀ v : H2, dist (a x) v + dist v (a y) = dist (a x) (a y) →
        a.symm v ∈ e.source := by
      intro v hv
      have hxball : a x ∈ Metric.ball c s := htarget ▸ a.map_source hx
      have hyball : a y ∈ Metric.ball c s := htarget ▸ a.map_source hy
      have hvt : v ∈ a.target := htarget.symm ▸
        metric_segment_stays_in_hyperbolic_ball c (a x) (a y) v hxball hyball hv
      apply hcover
      change dist (b (a.symm v)) o < R
      have hbc := hcontract a ha (a.symm v) (a.map_target hvt) x hx
      rw [a.right_inv hvt, dist_comm v (a x)] at hbc
      have htri := dist_triangle (b (a.symm v)) (b x) o
      linarith [dist_nonneg (x := v) (y := a y), ENNReal.toReal_nonneg (a := t)]
    have hfirst := htransition a ha x hx y hy hseg
    have hby := hcontract a ha y hy x hx
    rw [dist_comm (a y) (a x)] at hby
    have hbtri := dist_triangle (b y) (b x) o
    have htail := ih htfin (by linarith)
    exact (dist_triangle (e x) (e y) (e z)).trans (add_le_add hfirst htail)

end CurveComplex.Hyperbolic
