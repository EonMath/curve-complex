import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedGraphStraightening

open Set Topology Schoenflies CurveComplex

/-- Positive translation periodicity and continuity supply surjectivity, with
no bounded-range, inverse, or graph certificate. -/
theorem actual_positive_translation_coordinate_surjective
    (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 < T)
    (hp : ∀ (k : ℤ) x, f (x + (k : ℝ) * T) = f x + (k : ℝ) * T) :
    Function.Surjective f := by
  intro y
  let k : ℤ := Int.floor ((y - f 0) / T)
  have hlo : (k : ℝ) ≤ (y - f 0) / T := Int.floor_le _
  have hhi : (y - f 0) / T < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hleft : f ((k : ℝ) * T) ≤ y := by
    have hh := hp k 0
    simp only [zero_add] at hh
    rw [hh]
    have hl := (le_div_iff₀ hT).mp hlo
    linarith
  have hright : y ≤ f (((k + 1 : ℤ) : ℝ) * T) := by
    have hh := hp (k + 1) 0
    simp only [zero_add] at hh
    rw [hh]
    have hu := (div_lt_iff₀ hT).mp hhi
    push_cast
    linarith
  exact mem_range_of_exists_le_of_exists_ge hf ⟨_,hleft⟩ ⟨_,hright⟩

/-- Once actual local moves have made the horizontal coordinate injective,
periodicity itself supplies the global graph reparametrization. This changes
only parameters, not the curve image or its relative ambient isotopy class. -/
theorem actual_periodic_injective_coordinate_has_graph_reparametrization
    (G : C(ℝ, Plane)) (T : ℝ) (hT : 0 < T)
    (hp : ∀ (k : ℤ) x, G (x + (k : ℝ) * T) = G x + Plane.mk ((k : ℝ) * T) 0)
    (hInj : Function.Injective (fun x => G x 0)) :
    ∃ e : ℝ ≃ₜ ℝ, ∃ J : C(ℝ, Plane),
      (∀ x, e x = G x 0) ∧ (∀ x, J x = G (e.symm x)) ∧
      range J = range G ∧ (∀ x, J x 0 = x) ∧
      (∀ (k : ℤ) x, J (x + (k : ℝ) * T) = J x + Plane.mk ((k : ℝ) * T) 0) := by
  let f : ℝ → ℝ := fun x => G x 0
  have hf : Continuous f := by fun_prop
  have hfp : ∀ (k : ℤ) x, f (x + (k : ℝ) * T) = f x + (k : ℝ) * T := by
    intro k x
    exact congrArg (fun z : Plane => z 0) (hp k x)
  have hs := actual_positive_translation_coordinate_surjective f hf T hT hfp
  have hm : StrictMono f := by
    rcases hf.strictMono_of_inj hInj with hm | ha
    · exact hm
    · have hbad := ha hT
      have hh := hfp 1 0
      simp only [Int.cast_one,one_mul,zero_add] at hh
      linarith
  let E : ℝ ≃o ℝ := hm.orderIsoOfRightInverse f (Function.surjInv hs)
    (Function.rightInverse_surjInv hs)
  let e : ℝ ≃ₜ ℝ := { E.toEquiv with
    continuous_toFun := E.continuous
    continuous_invFun := E.symm.continuous }
  let J : C(ℝ, Plane) := ⟨fun x => G (e.symm x),by fun_prop⟩
  have he : ∀ x, e x = G x 0 := fun _ => rfl
  have hInv : ∀ (k : ℤ) x, e.symm (x + (k : ℝ) * T) = e.symm x + (k : ℝ) * T := by
    intro k x
    apply e.injective
    rw [e.apply_symm_apply]
    change x + (k : ℝ) * T = f (e.symm x + (k : ℝ) * T)
    rw [hfp]
    change x + (k : ℝ) * T = e (e.symm x) + (k : ℝ) * T
    rw [e.apply_symm_apply]
  refine ⟨e,J,he,fun _ => rfl,?_,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨e.symm x,rfl⟩
    · rintro ⟨x,rfl⟩; exact ⟨e x,by simp [J]⟩
  · intro x
    exact (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  · intro k x
    change G (e.symm (x + (k : ℝ) * T)) = _
    rw [hInv,hp]
    rfl
