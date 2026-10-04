import CurveComplexGenusTwo.Foundations.RealizationCW
import CurveComplexGenusTwo.Foundations.ConeRealization

namespace CurveComplex

private abbrev RegionalFaceSimplex {V : Type*}
    (K : AbstractSimplicialComplex V) :=
  Σ σ : {σ : Finset V // σ ∈ K.faces}, FiniteSimplex σ.1

private noncomputable def regionalFaceCover {V : Type*}
    (K : AbstractSimplicialComplex V) :
    RegionalFaceSimplex K → RealizationPoint K :=
  fun p => faceInclusion K p.1.1 p.1.2 p.2

private theorem regionalFaceCover_quotient {V : Type*}
    (K : AbstractSimplicialComplex V) :
    Topology.IsQuotientMap (regionalFaceCover K) := by
  refine ⟨⟨?_⟩, ?_⟩
  · apply TopologicalSpace.ext
    funext U
    apply propext
    change IsOpen U ↔ IsOpen ((regionalFaceCover K) ⁻¹' U)
    constructor
    · intro hU
      exact isOpen_sigma_iff.mpr (fun i => hU i.1 i.2)
    · intro hU σ hσ
      exact isOpen_sigma_iff.mp hU ⟨σ,hσ⟩
  · intro x
    obtain ⟨σ,hσ,hzero,hsum⟩ := x.liesInFace
    let y : FiniteSimplex σ :=
      ⟨fun v => x.weight v, (fun v => x.nonneg v), by
        simpa only [Finset.sum_attach, Finset.univ_eq_attach] using hsum⟩
    refine ⟨⟨⟨σ,hσ⟩,y⟩, ?_⟩
    apply RealizationPoint.ext
    funext v
    by_cases hv : v ∈ σ
    · simp [regionalFaceCover,faceInclusion,y,hv]
    · simp [regionalFaceCover,faceInclusion,y,hv,hzero v hv]

/-- Joint continuity in the weak realization follows from genuine
    continuity on the interval times every finite face. -/
theorem continuous_realization_homotopy_of_facewise
    {V W : Type*} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W)
    (H : ConeTime × RealizationPoint K → RealizationPoint L)
    (hface : ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      Continuous (fun p : ConeTime × FiniteSimplex σ =>
        H (p.1, faceInclusion K σ hσ p.2))) :
    Continuous H := by
  apply (regionalFaceCover_quotient K).continuous_lift_prod_right
  have h : Continuous (fun p : RegionalFaceSimplex K × ConeTime =>
      H (p.2, regionalFaceCover K p.1)) := by
    let g : (Σ i : {σ : Finset V // σ ∈ K.faces},
        FiniteSimplex i.1 × ConeTime) → RealizationPoint L :=
      fun p => H (p.2.2, faceInclusion K p.1.1 p.1.2 p.2.1)
    have hg : Continuous g := continuous_sigma_iff.mpr (by
      intro i
      exact (hface i.1 i.2).comp continuous_swap)
    exact hg.comp (Homeomorph.sigmaProdDistrib
      (Y := ConeTime)).continuous
  exact h.comp continuous_swap

#print axioms continuous_realization_homotopy_of_facewise

end CurveComplex
