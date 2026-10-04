import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicShortStepSheetCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E : Type} [TopologicalSpace E]

theorem developmentChain_short_stays_in_sheet {B : Type} [MetricSpace B] (b : E → B)
    (F : Set (OpenPartialHomeomorph E H2))
    (hballs : ∀ e ∈ F, ∃ c : H2, ∃ s : ℝ, e.target = Metric.ball c s)
    (hcontract : ∀ e ∈ F, ∀ y ∈ e.source, ∀ z ∈ e.source,
      dist (b y) (b z) ≤ dist (e y) (e z))
    (A D : Set E) (hA : IsOpen A) (hD : IsOpen D) (hdisj : Disjoint A D)
    (o : B) (R : ℝ) (hcover : b ⁻¹' Metric.ball o R ⊆ A ∪ D)
    {x y : E} {r : ENNReal} (h : DevelopmentChain F x y r) :
    r ≠ ⊤ → dist (b x) o + r.toReal < R → x ∈ A → y ∈ A := by
  induction h with
  | nil x => intro _ _ hx; exact hx
  | @cons x y z t e he hx hy tail ih =>
    intro hfin hbudget hxA
    have htfin : t ≠ ⊤ := (ENNReal.add_ne_top.mp hfin).2
    have hcost : (edist (e x) (e y) + t).toReal = dist (e x) (e y) + t.toReal := by
      rw [ENNReal.toReal_add (edist_ne_top (e x) (e y)) htfin]
      simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    rw [hcost] at hbudget
    obtain ⟨c, s, htarget⟩ := hballs e he
    have hstep : dist (b x) o + dist (e x) (e y) < R := by
      linarith [ENNReal.toReal_nonneg (a := t)]
    have hyA := hyperbolic_short_step_stays_in_sheet b e c s htarget
      (hcontract e he) A D hA hD hdisj o R hcover x y hx hy hxA hstep
    have hby := hcontract e he y hy x hx
    rw [dist_comm (e y) (e x)] at hby
    have htri := dist_triangle (b y) (b x) o
    exact ih htfin (by linarith) hyA

theorem developmentChain_sheet_exit_lower_bound {B : Type} [MetricSpace B] (b : E → B)
    (F : Set (OpenPartialHomeomorph E H2))
    (hballs : ∀ e ∈ F, ∃ c : H2, ∃ s : ℝ, e.target = Metric.ball c s)
    (hcontract : ∀ e ∈ F, ∀ y ∈ e.source, ∀ z ∈ e.source,
      dist (b y) (b z) ≤ dist (e y) (e z))
    (A D : Set E) (hA : IsOpen A) (hD : IsOpen D) (hdisj : Disjoint A D)
    (x y : E) (R : ℝ) (hR : 0 < R)
    (hcover : b ⁻¹' Metric.ball (b x) R ⊆ A ∪ D)
    (hxA : x ∈ A) (hyA : y ∉ A) :
    ENNReal.ofReal R ≤ developmentChainEDist F x y := by
  apply le_iInf; intro r
  apply le_iInf; intro h
  by_contra hn
  have hlt : r < ENNReal.ofReal R := lt_of_not_ge hn
  have hfin : r ≠ ⊤ := ne_top_of_lt (hlt.trans_le le_top)
  have hreal : r.toReal < R := by
    have hh := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hlt
    simpa only [ENNReal.toReal_ofReal hR.le] using hh
  have hy := developmentChain_short_stays_in_sheet b F hballs hcontract
    A D hA hD hdisj (b x) R hcover h hfin (by simpa using hreal) hxA
  exact hyA hy

end CurveComplex.Hyperbolic
