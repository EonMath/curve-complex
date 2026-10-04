import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusReferencePointCorrection

open Set Topology Schoenflies CurveComplex

/-- Retain the literal `-q+p` reference translation produced by actual torus
point normalization. -/
theorem actual_torus_point_normalization_translates_reference
    (c : ℝ) (p q : Plane) :
    let e := Homeomorph.mulRight
      (((Circle.exp (q 0),Circle.exp (q 1)) : Circle×Circle)⁻¹*
        (Circle.exp (p 0),Circle.exp (p 1)))
    e '' {z : Circle×Circle | z.1=Circle.exp c}=
      {z : Circle×Circle | z.1=Circle.exp (c-q 0+p 0)} := by
  let e := Homeomorph.mulRight
    (((Circle.exp (q 0),Circle.exp (q 1)) : Circle×Circle)⁻¹*
      (Circle.exp (p 0),Circle.exp (p 1)))
  have he (z : Circle×Circle) : (e z).1=z.1*((Circle.exp (q 0))⁻¹*Circle.exp (p 0)) := by rfl
  have hexp : Circle.exp (c-q 0+p 0)=Circle.exp c*((Circle.exp (q 0))⁻¹*Circle.exp (p 0)) := by
    rw [Circle.exp_add,Circle.exp_sub,div_eq_mul_inv,mul_assoc]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change (e x).1=Circle.exp (c-q 0+p 0)
    rw [he,hx,hexp]
  · intro hz
    refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
    change (e.symm z).1=Circle.exp c
    apply mul_right_cancel (b:=((Circle.exp (q 0))⁻¹*Circle.exp (p 0)))
    rw [← he,e.apply_symm_apply,← hexp]
    exact hz

/-- The reference translation avoids the original puncture because the actual
normalizing point avoids the old grid. -/
theorem actual_normalizing_point_off_grid_gives_translated_reference_avoidance
    (T c : ℝ) (p q : Plane) (hAvoid : ∀ i : ℤ, q 0≠c+(i:ℝ)*T) :
    ∀ i : ℤ, p 0+(i:ℝ)*T≠c-q 0+p 0 := by
  intro i hi
  apply hAvoid (-i)
  push_cast
  linarith

#print axioms actual_torus_point_normalization_translates_reference
#print axioms actual_normalizing_point_off_grid_gives_translated_reference_avoidance
