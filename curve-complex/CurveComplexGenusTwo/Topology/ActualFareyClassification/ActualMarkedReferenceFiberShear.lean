import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPeriodicVerticalShear

open Set Topology Schoenflies CurveComplex

/-- Produce a genuine periodic shear near the actual puncture-free reference
fiber. It fixes the WHOLE puncture orbit at every time and moves every reference
fiber vertically by the specified amount; no motion certificate is supplied. -/
theorem actual_puncture_free_reference_has_marked_vertical_shear
    (c d : ℝ) (p : Plane)
    (hp : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠c) :
    ∃ ρ : ℝ, 0<ρ ∧ ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ t (i : ℤ×ℤ),
        H.map (t,p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ t (i : ℤ) y,
        H.map (t,Plane.mk (c+(i:ℝ)*(2*Real.pi)) y)=
          Plane.mk (c+(i:ℝ)*(2*Real.pi)) (y+(t:ℝ)*d)) ∧
      (∀ t z, ρ≤dist (Circle.exp (z 0)) (Circle.exp c) → H.map (t,z)=z) ∧
      (∀ t z, H.map (t,z) 0=z 0) := by
  have hne : Circle.exp c≠Circle.exp (p 0) := by
    intro he
    obtain ⟨i,hi⟩ := Circle.exp_eq_exp.mp he
    exact hp i hi.symm
  let D := dist (Circle.exp c) (Circle.exp (p 0))
  have hD : 0<D := dist_pos.mpr hne
  let ρ := D/2
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  let β : C(ℝ,ℝ) := ⟨fun x => max 0 (1-dist (Circle.exp x) (Circle.exp c)/ρ),by fun_prop⟩
  have hβc : β c=1 := by simp [β]
  have hβp : β (p 0)=0 := by
    have hd : D/ρ=2 := by dsimp [ρ]; field_simp
    change max 0 (1-dist (Circle.exp (p 0)) (Circle.exp c)/ρ)=0
    rw [dist_comm]
    change max 0 (1-D/ρ)=0
    rw [hd]
    norm_num
  have hβperiod (i : ℤ) (x : ℝ) : β (x+(i:ℝ)*(2*Real.pi))=β x := by
    simp only [β,ContinuousMap.coe_mk,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
  obtain ⟨H,hFormula,hEq,hZero,hFirst⟩ :=
    actual_periodic_vertical_shear_isotopy β (2*Real.pi) d hβperiod
  refine ⟨ρ,hρ,H,hEq,?_,?_,?_,hFirst⟩
  · intro t i
    rw [hEq]
    have hh := hZero t p hβp
    rw [hh]
  · intro t i y
    rw [hFormula]
    change Plane.mk (c+(i:ℝ)*(2*Real.pi))
      (y+(t:ℝ)*d*β (c+(i:ℝ)*(2*Real.pi)))=_
    rw [hβperiod,hβc,mul_one]
  · intro t z hz
    apply hZero
    change max 0 (1-dist (Circle.exp (z 0)) (Circle.exp c)/ρ)=0
    apply max_eq_left
    have hh : 1≤dist (Circle.exp (z 0)) (Circle.exp c)/ρ :=
      (le_div_iff₀ hρ).mpr (by simpa using hz)
    linarith

#print axioms actual_puncture_free_reference_has_marked_vertical_shear
