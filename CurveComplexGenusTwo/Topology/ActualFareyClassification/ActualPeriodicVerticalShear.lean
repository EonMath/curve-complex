import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusEssentialTerminal

open Set Topology Schoenflies CurveComplex

/-- A concrete triangular shear is an ambient isotopy for an arbitrary continuous
periodic coefficient; its inverse is the opposite shear at the same time. -/
theorem actual_periodic_vertical_shear_isotopy
    (β : C(ℝ,ℝ)) (T d : ℝ)
    (hβ : ∀ (k : ℤ) x, β (x+(k:ℝ)*T)=β x) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t z, H.map (t,z)=Plane.mk (z 0) (z 1+(t:ℝ)*d*β (z 0))) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t z, β (z 0)=0 → H.map (t,z)=z) ∧
      (∀ t z, H.map (t,z) 0=z 0) := by
  let f : Interval×Plane → Plane := fun q =>
    Plane.mk (q.2 0) (q.2 1+(q.1:ℝ)*d*β (q.2 0))
  have hf : Continuous f := by dsimp [f]; fun_prop
  let H : AmbientIsotopy Plane := {
    map := ⟨f,hf⟩
    homeomorphism_at := by
      intro t
      let e : Plane ≃ₜ Plane := {
        toFun := fun z => Plane.mk (z 0) (z 1+(t:ℝ)*d*β (z 0))
        invFun := fun z => Plane.mk (z 0) (z 1-(t:ℝ)*d*β (z 0))
        left_inv := by intro z; ext k; fin_cases k <;> simp
        right_inv := by intro z; ext k; fin_cases k <;> simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      exact ⟨e,fun _ => rfl⟩
    at_zero := by intro z; ext k; fin_cases k <;> simp [f,Plane.mk] }
  refine ⟨H,fun _ _ => rfl,?_,?_,fun _ _ => rfl⟩
  · intro t i z
    change Plane.mk (z 0+(i.1:ℝ)*T)
      (z 1+(i.2:ℝ)*T+(t:ℝ)*d*β (z 0+(i.1:ℝ)*T))=_
    rw [hβ]
    ext k
    fin_cases k <;> simp [H,f,Plane.mk]
    ring
  · intro t z hz
    ext k
    fin_cases k <;> simp [H,f,Plane.mk,hz]

#print axioms actual_periodic_vertical_shear_isotopy
