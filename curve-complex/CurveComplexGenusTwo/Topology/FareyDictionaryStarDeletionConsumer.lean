import CurveComplexGenusTwo.Topology.StarDeletionFarey

set_option maxHeartbeats 2000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- A no-sorry downstream consumer of the integrated Farey contraction.  The
geometric dictionary remains an explicit input; this packet assembles the
already-proved Farey and star-deletion interfaces into the generic SDR theorem.
The explicit quotient-chart map is discharged by the integrated star-cone
quotient lemma. -/
theorem farey_dictionary_star_deletion_consumer
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

#print axioms CurveComplexGenusTwo.Topology.farey_dictionary_star_deletion_consumer
