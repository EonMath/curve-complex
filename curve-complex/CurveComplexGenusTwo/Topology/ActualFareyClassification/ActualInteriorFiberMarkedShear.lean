import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualInteriorFiberSelection

open Set Topology Schoenflies CurveComplex

/-- Produce the ACTUAL interior-fiber shear fixing BOTH the puncture orbit and
EVERY reference fiber at all times. Its coefficient is constructed from the
actual positive distances to these two forbidden circle points. -/
theorem actual_interior_fiber_has_marked_shear_fixing_reference
    (b c d : ℝ) (p : Plane)
    (hbp : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠b)
    (hbc : ∀ i : ℤ, c+(i:ℝ)*(2*Real.pi)≠b) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ t (i : ℤ×ℤ),
        H.map (t,p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
          p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))) ∧
      (∀ t (i : ℤ) y, H.map (t,Plane.mk (c+(i:ℝ)*(2*Real.pi)) y)=
        Plane.mk (c+(i:ℝ)*(2*Real.pi)) y) ∧
      (∀ t (i : ℤ) y, H.map (t,Plane.mk (b+(i:ℝ)*(2*Real.pi)) y)=
        Plane.mk (b+(i:ℝ)*(2*Real.pi)) (y+(t:ℝ)*d)) ∧
      (∀ t z, H.map (t,z) 0=z 0) := by
  have hnep : Circle.exp b≠Circle.exp (p 0) := by
    intro he
    obtain ⟨i,hi⟩ := Circle.exp_eq_exp.mp he
    exact hbp i hi.symm
  have hnec : Circle.exp b≠Circle.exp c := by
    intro he
    obtain ⟨i,hi⟩ := Circle.exp_eq_exp.mp he
    exact hbc i hi.symm
  let Dp := dist (Circle.exp b) (Circle.exp (p 0))
  let Dc := dist (Circle.exp b) (Circle.exp c)
  have hDp : 0<Dp := dist_pos.mpr hnep
  have hDc : 0<Dc := dist_pos.mpr hnec
  let ρ := min Dp Dc/2
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρp : ρ≤Dp := by dsimp [ρ]; linarith [min_le_left Dp Dc,lt_min hDp hDc]
  have hρc : ρ≤Dc := by dsimp [ρ]; linarith [min_le_right Dp Dc,lt_min hDp hDc]
  let β : C(ℝ,ℝ) := ⟨fun x => max 0 (1-dist (Circle.exp x) (Circle.exp b)/ρ),by fun_prop⟩
  have hβb : β b=1 := by simp [β]
  have hZero (x : ℝ) (hx : ρ≤dist (Circle.exp x) (Circle.exp b)) : β x=0 := by
    apply max_eq_left
    have hh : 1≤dist (Circle.exp x) (Circle.exp b)/ρ :=
      (le_div_iff₀ hρ).mpr (by simpa using hx)
    linarith
  have hβp : β (p 0)=0 := hZero _ (by simpa [Dp,dist_comm] using hρp)
  have hβc : β c=0 := hZero _ (by simpa [Dc,dist_comm] using hρc)
  have hβperiod (i : ℤ) (x : ℝ) : β (x+(i:ℝ)*(2*Real.pi))=β x := by
    simp only [β,ContinuousMap.coe_mk,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
  obtain ⟨H,hFormula,hEq,hFixed,hFirst⟩ :=
    actual_periodic_vertical_shear_isotopy β (2*Real.pi) d hβperiod
  refine ⟨H,hEq,?_,?_,?_,hFirst⟩
  · intro t i
    rw [hEq,hFixed t p hβp]
  · intro t i y
    apply hFixed
    change β (c+(i:ℝ)*(2*Real.pi))=0
    rw [hβperiod,hβc]
  · intro t i y
    rw [hFormula]
    change Plane.mk (b+(i:ℝ)*(2*Real.pi))
      (y+(t:ℝ)*d*β (b+(i:ℝ)*(2*Real.pi)))=_
    rw [hβperiod,hβb,mul_one]

#print axioms actual_interior_fiber_has_marked_shear_fixing_reference
