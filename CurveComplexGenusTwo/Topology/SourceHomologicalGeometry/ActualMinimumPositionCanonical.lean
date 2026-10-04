import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingMinimalPosition
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

namespace CurveComplex

/-- The original homological-genus surface hypotheses produce actual
minimum-position representatives without assuming count-set nonemptiness. -/
theorem geometricIntersection_attained_of_isGenus
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (α β : Vertex S) :
    ∃ a b : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) a = α ∧
      Quotient.mk (essentialCurveSetoid S) b = β ∧
      ∃ h : Transverse a.val b.val,
        h.1.toFinset.card = geometricIntersection α β := by
  let : ClosedSurface S := Classical.choice hS.2.1
  exact source_geometric_intersection_attained S α β

/-- For an actual intersection-one edge, produce its essential representatives,
unique crossing point, and actual local axis chart directly from IsGenus. -/
theorem one_crossing_representatives_of_isGenus
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (α β : Vertex S)
    (hone : geometricIntersection α β = 1) :
    ∃ a b : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) a = α ∧
      Quotient.mk (essentialCurveSetoid S) b = β ∧
      ∃ h : Transverse a.val b.val,
        h.1.toFinset.card = 1 ∧
        ∃ p : S, p ∈ a.val.image ∩ b.val.image ∧
          CrossesAt a.val b.val p ∧
          ∀ q ∈ a.val.image ∩ b.val.image, q = p := by
  obtain ⟨a, b, ha, hb, h, hc⟩ := geometricIntersection_attained_of_isGenus S g hS α β
  have hc' : h.1.toFinset.card = 1 := hc.trans hone
  exact ⟨a, b, ha, hb, h, hc', unique_crossing_chart_of_count_one a.val b.val h hc'⟩

/-- Construct the actual compact crossing square by restricting the inverse
axis chart. No neighborhood, band, or boundary curve is supplied as a premise. -/
theorem embedded_crossing_square_of_chart
    {S : Type*} [TopologicalSpace S]
    {a b : Curve S} {p : S} (hp : CrossesAt a b p) :
    ∃ (r : ℝ) (hr : 0 < r)
      (f : Metric.closedBall ((0, 0) : ℝ × ℝ) r → S),
      Topology.IsEmbedding f ∧
      f ⟨0, Metric.mem_closedBall_self hr.le⟩ = p ∧
      (∀ z, (f z ∈ a.image ↔ z.val.1 = 0) ∧
        (f z ∈ b.image ↔ z.val.2 = 0)) ∧
      IsCompact (Set.range f) := by
  obtain ⟨U, V, hpU, h, _, _, hzero, haxes, r, hr, hsub⟩ :=
    exists_closed_disk_in_crossing_chart hp
  let j : Metric.closedBall ((0, 0) : ℝ × ℝ) r → V :=
    fun z => ⟨z.val, hsub z.property⟩
  let f : Metric.closedBall ((0, 0) : ℝ × ℝ) r → S :=
    fun z => (h.symm (j z)).val
  have hj : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.codRestrict V (fun z => hsub z.property)
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp (h.symm.isEmbedding.comp hj)
  refine ⟨r, hr, f, hf, ?_, ?_, isCompact_range hf.continuous⟩
  · have hz : j ⟨0, Metric.mem_closedBall_self hr.le⟩ = h ⟨p, hpU⟩ := by
      apply Subtype.ext
      exact hzero.symm
    change (h.symm (j ⟨0, Metric.mem_closedBall_self hr.le⟩)).val = p
    rw [hz, h.symm_apply_apply]
  · intro z
    have hh := haxes (h.symm (j z)).val (h.symm (j z)).property
    simpa only [h.apply_symm_apply] using hh

end CurveComplex

#print axioms CurveComplex.geometricIntersection_attained_of_isGenus
#print axioms CurveComplex.one_crossing_representatives_of_isGenus

#print axioms CurveComplex.embedded_crossing_square_of_chart
