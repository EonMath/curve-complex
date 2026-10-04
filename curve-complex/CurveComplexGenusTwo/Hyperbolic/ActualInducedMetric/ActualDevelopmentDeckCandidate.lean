import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainLawsCandidate

namespace CurveComplex.Hyperbolic
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem actual_development_family_deck (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (e : OpenPartialHomeomorph E H2) (he : e ∈ actualCompactDevelopmentFamily q identify) :
    q.deck.toOpenPartialHomeomorph.trans e ∈ actualCompactDevelopmentFamily q identify := by
  obtain ⟨c, r, hr, ht, hc⟩ := he
  refine ⟨c, r, hr, ?_, ?_⟩
  · simpa using ht
  · intro x hx y hy
    have h := hc (q.deck x) hx.2 (q.deck y) hy.2
    simpa only [q.projection_deck, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply] using h

theorem actual_development_chain_deck (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    {x y : E} {r : ENNReal}
    (h : DevelopmentChain (actualCompactDevelopmentFamily q identify) x y r) :
    DevelopmentChain (actualCompactDevelopmentFamily q identify) (q.deck x) (q.deck y) r := by
  induction h with
  | nil x => exact DevelopmentChain.nil (q.deck x)
  | @cons x y z t e he hx hy tail ih =>
    have hx' : q.deck x ∈ (q.deck.toOpenPartialHomeomorph.trans e).source := by
      refine ⟨mem_univ _, ?_⟩
      change q.deck (q.deck x) ∈ e.source
      simpa only [q.deck_involution] using hx
    have hy' : q.deck y ∈ (q.deck.toOpenPartialHomeomorph.trans e).source := by
      refine ⟨mem_univ _, ?_⟩
      change q.deck (q.deck y) ∈ e.source
      simpa only [q.deck_involution] using hy
    simpa only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      q.deck_involution] using DevelopmentChain.cons
        (q.deck.toOpenPartialHomeomorph.trans e) (actual_development_family_deck q identify e he)
        hx' hy' ih

theorem actual_development_chain_edist_deck (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)) (x y : E) :
    developmentChainEDist (actualCompactDevelopmentFamily q identify) (q.deck x) (q.deck y) =
      developmentChainEDist (actualCompactDevelopmentFamily q identify) x y := by
  have hl (a b : E) :
      developmentChainEDist (actualCompactDevelopmentFamily q identify) (q.deck a) (q.deck b) ≤
        developmentChainEDist (actualCompactDevelopmentFamily q identify) a b := by
    apply le_iInf; intro r
    apply le_iInf; intro h
    exact developmentChainEDist_le_chain (actual_development_chain_deck q identify h)
  exact le_antisymm (hl x y) (by simpa only [q.deck_involution] using hl (q.deck x) (q.deck y))

end CurveComplex.Hyperbolic
