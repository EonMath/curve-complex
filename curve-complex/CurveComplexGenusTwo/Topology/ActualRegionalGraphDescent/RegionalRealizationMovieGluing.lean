import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalRealizationFacewiseContinuity

namespace CurveComplex

private abbrev RegionalChart {V : Type*}
    (K : AbstractSimplicialComplex V) :=
  Σ σ : {σ : Finset V // σ ∈ K.faces}, FiniteSimplex σ.1

private noncomputable def regionalChooseChart {V : Type*}
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K) :
    RegionalChart K := by
  classical
  let e := exists_faceInclusion_eq K x
  let σ := Classical.choose e
  let hσ := Classical.choose (Classical.choose_spec e)
  let p := Classical.choose (Classical.choose_spec (Classical.choose_spec e))
  exact ⟨⟨σ,hσ⟩,p⟩

private theorem regionalChooseChart_eq {V : Type*}
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K) :
    faceInclusion K (regionalChooseChart K x).1.1
      (regionalChooseChart K x).1.2 (regionalChooseChart K x).2 = x := by
  classical
  unfold regionalChooseChart
  exact Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      (exists_faceInclusion_eq K x)))

/-- Coherent finite-face movies glue to a joint continuous movie on the
    actual weak realization. The equality premise identifies both
    parametrizations of every shared face, including zero-weight points. -/
theorem regional_coherent_finite_face_movies_glue
    {V W : Type*} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W)
    (movie : ∀ (σ : Finset V), σ ∈ K.faces →
      ConeTime × FiniteSimplex σ → RealizationPoint L)
    (hcontinuous : ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      Continuous (movie σ hσ))
    (hcoherent : ∀ (σ τ : Finset V) (hσ : σ ∈ K.faces)
      (hτ : τ ∈ K.faces) (t : ConeTime) (p : FiniteSimplex σ)
      (q : FiniteSimplex τ),
      faceInclusion K σ hσ p = faceInclusion K τ hτ q →
      movie σ hσ (t,p) = movie τ hτ (t,q)) :
    ∃ H : C(ConeTime × RealizationPoint K, RealizationPoint L),
      ∀ (σ : Finset V) (hσ : σ ∈ K.faces) (t : ConeTime)
        (p : FiniteSimplex σ),
        H (t,faceInclusion K σ hσ p) = movie σ hσ (t,p) := by
  classical
  let H : ConeTime × RealizationPoint K → RealizationPoint L := fun z =>
    let c := regionalChooseChart K z.2
    movie c.1.1 c.1.2 (z.1,c.2)
  have hchart (σ : Finset V) (hσ : σ ∈ K.faces)
      (t : ConeTime) (p : FiniteSimplex σ) :
      H (t,faceInclusion K σ hσ p) = movie σ hσ (t,p) := by
    dsimp [H]
    let c := regionalChooseChart K (faceInclusion K σ hσ p)
    exact hcoherent c.1.1 σ c.1.2 hσ t c.2 p
      (regionalChooseChart_eq K _)
  have hH : Continuous H := by
    apply continuous_realization_homotopy_of_facewise K L H
    intro σ hσ
    convert hcontinuous σ hσ using 1
    funext z
    exact hchart σ hσ z.1 z.2
  exact ⟨⟨H,hH⟩,hchart⟩

#print axioms regional_coherent_finite_face_movies_glue

end CurveComplex
