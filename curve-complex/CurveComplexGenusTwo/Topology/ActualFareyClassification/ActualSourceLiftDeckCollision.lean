import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusSourceWindingTransport

open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

/-- Derive exact deck collisions for the actual transported source lift, with
its ORIGINAL parameter and winding retained. -/
theorem actual_embedded_source_lift_has_exact_deck_collision
    (c : Curve (Circle×Circle)) (F : C(ℝ,ℝ×ℝ)) (m n : ℤ)
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=c.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F x).2+((k*n:ℤ):ℝ)*(2*Real.pi))) :
    ∀ (x y : ℝ) (a b : ℤ),
      F x=((F y).1+(a:ℝ)*(2*Real.pi),(F y).2+(b:ℝ)*(2*Real.pi)) →
      ∃ k : ℤ, x=y+(k:ℝ)*(2*Real.pi) ∧ a=k*m ∧ b=k*n := by
  intro x y a b hxy
  have hExp : Circle.exp x=Circle.exp y := by
    apply c.embedded.injective
    rw [← hproj x,← hproj y,hxy]
    simp only [Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hExp
  have hh := (hxy.symm.trans (hk ▸ hp k y))
  have h1 := congrArg Prod.fst hh
  have h2 := congrArg Prod.snd hh
  dsimp at h1 h2
  refine ⟨k,hk,?_,?_⟩
  · have ha : (a:ℝ)=((k*m:ℤ):ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast ha
  · have hb : (b:ℝ)=((k*n:ℤ):ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast hb

/-- The actual transported source lift remains properly embedded whenever its
retained original winding is nonzero. -/
theorem actual_embedded_nonzero_winding_lift_is_closed_embedding
    (c : Curve (Circle×Circle)) (F : C(ℝ,ℝ×ℝ)) (m n : ℤ)
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=c.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F x).2+((k*n:ℤ):ℝ)*(2*Real.pi)))
    (hnz : m≠0 ∨ n≠0) : IsClosedEmbedding F := by
  have hInj : Function.Injective F := by
    intro x y hxy
    have hzero : F x=((F y).1+(0:ℝ)*(2*Real.pi),(F y).2+(0:ℝ)*(2*Real.pi)) := by simpa using hxy
    obtain ⟨k,hk,hkm,hkn⟩ := actual_embedded_source_lift_has_exact_deck_collision c F m n hproj hp x y 0 0 (by simpa using hzero)
    have hk0 : k=0 := by
      rcases hnz with hm | hn
      · exact (mul_eq_zero.mp hkm.symm).resolve_right hm
      · exact (mul_eq_zero.mp hkn.symm).resolve_right hn
    simpa [hk0] using hk
  obtain ⟨_,hClosed⟩ := torus_period_lift_isProperMap F m n
    (fun x => by simpa using hp 1 x) hnz
  exact hClosed hInj

#print axioms actual_embedded_source_lift_has_exact_deck_collision
#print axioms actual_embedded_nonzero_winding_lift_is_closed_embedding
