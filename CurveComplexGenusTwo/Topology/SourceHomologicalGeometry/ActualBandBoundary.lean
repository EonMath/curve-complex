import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierCircleProof
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapProducer
import CurveComplexGenusTwo.Topology.ConsumerClean
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

namespace CurveComplex

/-- For the actual signed bands, the canonical frontier and disk-cap producers
construct an essential disjoint boundary, retaining its exact frontier identity.
Band existence remains a separate source obligation. -/
theorem essential_frontier_of_actual_compatible_bands
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) :
    ∃ c : EssentialCurve S,
      frontier (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) = c.val.image ∧
      Disjoint a.image c.val.image ∧ Disjoint b.image c.val.image := by
  let : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨_, _, hinside, c, hfront⟩ :=
    FrontierHeaders.exists_frontier_circle_of_compatibleOutsideBands D B
  obtain ⟨hc, hac, hbc⟩ := essential_disjoint_frontier_of_disk_cap_cover
    hg hS a b (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second)
    c hinside hfront (by
      intro hdisc
      obtain ⟨f, _, _, hU, hV, hcover, hinter, hcontr, p, hp⟩ :=
        actual_compatible_band_disk_cap_producer hg hS D B hfront hdisc
      exact ⟨_, _, hU, hV, hcover, hinter, hcontr, p, hp⟩)
  exact ⟨⟨c, hc⟩, hfront, hac, hbc⟩

/-- The same literal boundary supplies the intersection-zero detour and
three distinct isotopy classes for an intersection-one edge. -/
theorem intersection_one_detour_of_actual_compatible_bands
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {g : ℕ} (hg : 2 ≤ g) (hS : IsGenus S g)
    (a b : EssentialCurve S)
    (hone : geometricIntersection (Quotient.mk (essentialCurveSetoid S) a)
      (Quotient.mk (essentialCurveSetoid S) b) = 1)
    (D : OneCrossingBandBase a.val b.val) (B : CompatibleOutsideBands D) :
    ∃ c : EssentialCurve S,
      frontier (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) = c.val.image ∧
      geometricIntersection (Quotient.mk (essentialCurveSetoid S) a)
        (Quotient.mk (essentialCurveSetoid S) c) = 0 ∧
      geometricIntersection (Quotient.mk (essentialCurveSetoid S) b)
        (Quotient.mk (essentialCurveSetoid S) c) = 0 ∧
      Quotient.mk (essentialCurveSetoid S) a ≠ Quotient.mk (essentialCurveSetoid S) c ∧
      Quotient.mk (essentialCurveSetoid S) b ≠ Quotient.mk (essentialCurveSetoid S) c := by
  obtain ⟨c, hfront, hac, hbc⟩ := essential_frontier_of_actual_compatible_bands hg hS D B
  have haz := geometricIntersection_eq_zero_of_disjoint_representatives a c hac
  have hbz := geometricIntersection_eq_zero_of_disjoint_representatives b c hbc
  refine ⟨c, hfront, haz, hbz, ?_, ?_⟩
  · intro heq
    have hba : geometricIntersection (Quotient.mk (essentialCurveSetoid S) b)
        (Quotient.mk (essentialCurveSetoid S) a) = 1 := by
      rw [geometricIntersection_symm_of_chart]
      exact hone
    rw [heq, hbz] at hba
    norm_num at hba
  · intro heq
    rw [heq, haz] at hone
    norm_num at hone

end CurveComplex

#print axioms CurveComplex.essential_frontier_of_actual_compatible_bands

#print axioms CurveComplex.intersection_one_detour_of_actual_compatible_bands
