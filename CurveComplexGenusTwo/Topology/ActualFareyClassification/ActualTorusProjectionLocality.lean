import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualLiftedAxisChart

open Set Topology Schoenflies CurveComplex

/-- The literal exponential projection used by normalized source curves is a
local homeomorphism; its local branches are constructed from the circle cover. -/
theorem actual_plane_exponential_projection_is_local_homeomorph :
    IsLocalHomeomorph (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) := by
  let e : Plane ≃ₜ ℝ×ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans Homeomorph.finTwoArrow
  apply IsLocalHomeomorph.mk
  intro z
  obtain ⟨a,ha,hea⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph (z 0)
  obtain ⟨b,hb,heb⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph (z 1)
  let l := e.toOpenPartialHomeomorph.trans (a.prod b)
  refine ⟨l,?_,?_⟩
  · exact ⟨mem_univ z,ha,hb⟩
  · intro x _
    change (Circle.exp (x 0),Circle.exp (x 1))=(a (x 0),b (x 1))
    rw [← hea,← heb]

/-- The full lifted source image is the whole row family, not a chosen single
lift. The equality follows from the literal source projection and its period. -/
theorem actual_normalized_projection_preimage_is_whole_row_family
    (G : C(ℝ,Plane)) (T : ℝ)
    (hT : T=2*Real.pi)
    (hp : ∀ (i : ℤ) x, G (x+(i:ℝ)*T)=G x+Plane.mk ((i:ℝ)*T) 0) :
    (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) ⁻¹'
      ((fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range G)=
      ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
  subst T
  ext z
  constructor
  · rintro ⟨_,⟨x,rfl⟩,hx⟩
    obtain ⟨a,ha⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hx.symm)
    obtain ⟨b,hb⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hx.symm)
    refine mem_iUnion.mpr ⟨b,⟨x+(a:ℝ)*(2*Real.pi),?_⟩⟩
    change G (x+(a:ℝ)*(2*Real.pi))+Plane.mk 0 ((b:ℝ)*(2*Real.pi))=z
    rw [hp]
    ext k
    fin_cases k
    · simpa [Plane.mk] using ha.symm
    · simpa [Plane.mk] using hb.symm
  · intro hz
    obtain ⟨j,x,rfl⟩ := mem_iUnion.mp hz
    refine ⟨G x,mem_range_self x,?_⟩
    simp [Plane.mk,Circle.exp_add]

#print axioms actual_plane_exponential_projection_is_local_homeomorph
#print axioms actual_normalized_projection_preimage_is_whole_row_family
