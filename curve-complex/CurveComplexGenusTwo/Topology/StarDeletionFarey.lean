import CurveComplexGenusTwo.Topology.StarSDRConditional
import CurveComplexGenusTwo.Topology.StarConeTopology
import CurveComplexGenusTwo.Topology.FareyJoinConsumer

namespace CurveComplexGenusTwo.Topology

open CurveComplex

theorem realization_star_deletion_of_farey_dictionaries
    {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (d : ∀ v : {u : V // separating u},
      FareyJoinLinkDictionary K intersect v.1) :
    IsStrongDeformationRetract (NonseparatingWeightLocus K separating) := by
  have hstar : ∀ v : {u : V // separating u},
      HasRealizedStarFaces K intersect v := by
    intro v
    exact hasRealizedStarFaces_of_fullCurveFaces K intersect v.1 hfull
  apply realization_star_deletion_of_contractible_links_and_quotient_charts
    K intersect separating hcurve hsep hstar
  · intro v
    exact fareyRealizedSeparatingLink_contractible K intersect separating v
      hcurve hfull hsep (d v)
  · intro v
    letI : ContractibleSpace
        (RealizedSeparatingLink K intersect separating v.1) :=
      fareyRealizedSeparatingLink_contractible K intersect separating v
        hcurve hfull hsep (d v)
    have hne : Nonempty
        (RealizedSeparatingLink K intersect separating v.1) := by
      obtain ⟨he⟩ := ContractibleSpace.hequiv_unit
        (RealizedSeparatingLink K intersect separating v.1)
      exact ⟨he.invFun ()⟩
    exact closedStarConeMap_isQuotientMap K intersect separating
      hcurve hfull hsep v (hstar v) hne

end CurveComplexGenusTwo.Topology
