import CurveComplexGenusTwo.Topology.FareyCompletedContraction
import CurveComplexGenusTwo.Topology.FareyRestrictedJoin

set_option maxHeartbeats 2000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The two existing names for the filled Farey flag complex have the same
nonempty faces, so their weak realizations are homeomorphic. -/
noncomputable def fareyComplexFlagHomeomorph :
    RealizationPoint fareyComplex ≃ₜ RealizationPoint fareyFlagComplex := by
  apply CurveComplex.realizationHomeomorphOfVertexEquiv
    fareyComplex fareyFlagComplex (Equiv.refl FareySlope)
  intro σ
  simpa using (show σ ∈ fareyComplex.faces ↔ σ ∈ fareyFlagComplex.faces from Iff.rfl)

/-- Transport the concrete scheduled contraction to the Farey factor used
by the geometric join model. -/
noncomputable def fareyFlagScheduledHomotopy :
    ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyFlagComplex))
      (ContinuousMap.const (RealizationPoint fareyFlagComplex)
        (fareyComplexFlagHomeomorph fareyStageOneApex.1)) := by
  let e := fareyComplexFlagHomeomorph
  let H := fareyFiniteScheduleHomotopy.choose
  refine {
    toFun := fun z => e (H (z.1, e.symm z.2))
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }
  · exact e.continuous.comp
      (H.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  · intro x
    change e (H (0, e.symm x)) = x
    simp
  · intro x
    change e (H (1, e.symm x)) = e fareyStageOneApex.1
    exact congrArg e (H.map_one_left (e.symm x))

/-- The actual Farey join contracts using the constructed weak-realization
homotopy, with no cone-apex assumption on the Farey factor. -/
theorem fareyJoin_contractible :
    ContractibleSpace (RealizationPoint fareyJoinComplex) :=
  fareyJoin_contractible_of_left_factor_contraction
    (fareyComplexFlagHomeomorph fareyStageOneApex.1)
    fareyFlagScheduledHomotopy

/-- Given the geometric slope dictionary, the weak realization of the
separating link on its actual link vertices is contractible. -/
theorem fareyLinkVertex_contractible
    {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v) :
    ContractibleSpace (RealizationPoint (linkVertexComplex intersect v)) := by
  exact (Homeomorph.contractibleSpace_iff
    (d.realizationHomeomorph K intersect v)).mp fareyJoin_contractible

/-- The weight-support locus on link vertices is exactly the realized
separating link in the ambient weak realization. -/
theorem linkSupportLocus_eq_realizedSeparatingLink
    {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {w : V // separating w})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b) :
    CurveComplex.fullSupportLocus K (fun w => LinkFace intersect v.1 {w}) =
      RealizedSeparatingLink K intersect separating v.1 := by
  ext x
  constructor
  · intro hx
    let σ := supportFinset K x
    have hσ : σ ∈ K.faces := supportFinset_mem_faces K x
    have hvertices : ∀ w ∈ σ, LinkFace intersect v.1 {w} := by
      intro w hw
      by_contra hnot
      exact ((mem_supportFinset_iff K x w).1 hw) (hx w hnot)
    have hlink : LinkFace intersect v.1 σ :=
      linkFace_of_face_of_linkVertices K intersect v.1 hcurve σ hσ hvertices
    constructor
    · refine ⟨σ, hσ, hlink.2, ?_⟩
      intro w hw
      by_contra hne
      exact hw ((mem_supportFinset_iff K x w).2 hne)
    · intro u hu
      by_contra hne
      have hP : LinkFace intersect v.1 {u} := by
        by_contra hnot
        exact hne (hx u hnot)
      have hvu : v.1 ≠ u := by
        intro heq
        subst u
        exact hP.1 (Finset.mem_singleton_self v.1)
      have hle : intersect v.1 u ≤ 1 :=
        hP.2 (Finset.mem_insert_self _ _)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hvu
      have hgt := hsep v.1 u v.2 hu hvu
      omega
  · rintro ⟨⟨σ, hσ, hstar, hzero⟩, hcore⟩
    intro w hwP
    by_contra hne
    have hwσ : w ∈ σ := by
      by_contra hw
      exact hne (hzero w hw)
    have hvw : v.1 ≠ w := by
      intro heq
      subst w
      exact hne (hcore v.1 v.2)
    have hP : LinkFace intersect v.1 {w} := by
      constructor
      · simpa only [Finset.mem_singleton] using hvw
      · apply hstar.mono
        intro u hu
        rcases Finset.mem_insert.mp hu with huv | huw
        · subst u
          exact Finset.mem_insert_self _ _
        · have huw' : u = w := Finset.mem_singleton.mp huw
          subst u
          exact Finset.mem_insert_of_mem hwσ
    exact hwP hP

/-- On the actual link vertices, the abstract link complex agrees with the
full subcomplex of the ambient curve complex. -/
noncomputable def linkVertexFullHomeomorph
    {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces) :
    RealizationPoint (linkVertexComplex intersect v) ≃ₜ
      RealizationPoint
        (CurveComplex.fullSubcomplex K
          (fun w => LinkFace intersect v {w})) := by
  apply CurveComplex.realizationHomeomorphOfVertexEquiv
    (linkVertexComplex intersect v)
    (CurveComplex.fullSubcomplex K (fun w => LinkFace intersect v {w}))
    (Equiv.refl {w : V // LinkFace intersect v {w}})
  intro σ
  have hσimg : σ.image (Equiv.refl {w : V // LinkFace intersect v {w}}) = σ := by
    simp
  rw [hσimg, mem_linkVertexComplex_iff,
    CurveComplex.mem_fullSubcomplex_iff]
  constructor
  · rintro ⟨hne, hlink⟩
    exact (linkFace_iff_face_on_linkVertices K intersect v hcurve hfull σ hne).mp hlink
  · intro hK
    have hne : σ.Nonempty := Finset.image_nonempty.mp
      (K.isRelLowerSet_faces hK).1
    exact ⟨hne,
      (linkFace_iff_face_on_linkVertices K intersect v hcurve hfull σ hne).mpr hK⟩

/-- The realized separating link is contractible once its genuine geometric
Farey-join dictionary is supplied. No apex or contraction is assumed. -/
theorem fareyRealizedSeparatingLink_contractible
    {V : Type*} [DecidableEq V]
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop) (v : {w : V // separating w})
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (d : FareyJoinLinkDictionary K intersect v.1) :
    ContractibleSpace (RealizedSeparatingLink K intersect separating v.1) := by
  let e1 := linkVertexFullHomeomorph K intersect v.1 hcurve hfull
  let e2 := CurveComplex.fullSubcomplexHomeomorphSupported K
    (fun w => LinkFace intersect v.1 {w})
  have hc : ContractibleSpace
      (CurveComplex.fullSupportLocus K
        (fun w => LinkFace intersect v.1 {w})) :=
    (Homeomorph.contractibleSpace_iff (e1.trans e2)).mp
      (fareyLinkVertex_contractible K intersect v.1 d)
  rw [linkSupportLocus_eq_realizedSeparatingLink K intersect separating v
    hcurve hsep] at hc
  exact hc

end CurveComplexGenusTwo.Topology
