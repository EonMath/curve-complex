import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport

open Set Topology Schoenflies CurveComplex

/-- An actual torus ambient move transports the original lifted source through
a joint continuous lift and retains BOTH original winding integers. -/
theorem actual_torus_ambient_move_retains_source_deck_winding
    (H : AmbientIsotopy (Circle×Circle)) (F : C(ℝ,ℝ×ℝ)) (m n : ℤ)
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F x).2+((k*n:ℤ):ℝ)*(2*Real.pi))) :
    ∃ A : C(Interval×ℝ,ℝ×ℝ),
      (∀ t x, (Circle.exp (A (t,x)).1,Circle.exp (A (t,x)).2)=
        H.map (t,(Circle.exp (F x).1,Circle.exp (F x).2))) ∧
      (∀ x, A (⟨0,by norm_num⟩,x)=F x) ∧
      (∀ t (k : ℤ) x, A (t,x+(k:ℝ)*(2*Real.pi))=
        ((A (t,x)).1+((k*m:ℤ):ℝ)*(2*Real.pi),
         (A (t,x)).2+((k*n:ℤ):ℝ)*(2*Real.pi))) := by
  let f : C(Interval×ℝ,Circle×Circle) :=
    ⟨fun tx => H.map (tx.1,(Circle.exp (F tx.2).1,Circle.exp (F tx.2).2)),by fun_prop⟩
  have hfperiod (t : Interval) (k : ℤ) (x : ℝ) :
      f (t,x+(k:ℝ)*(2*Real.pi))=f (t,x) := by
    change H.map (t,(Circle.exp (F (x+(k:ℝ)*(2*Real.pi))).1,
      Circle.exp (F (x+(k:ℝ)*(2*Real.pi))).2))=_
    rw [hp]
    simp only [Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
    rfl
  let f₁ : C(Interval×ℝ,Circle) := ⟨fun tx => (f tx).1,by fun_prop⟩
  let f₂ : C(Interval×ℝ,Circle) := ⟨fun tx => (f tx).2,by fun_prop⟩
  let F₁ : C(ℝ,ℝ) := ⟨fun x => (F x).1,by fun_prop⟩
  let F₂ : C(ℝ,ℝ) := ⟨fun x => (F x).2,by fun_prop⟩
  have hz₁ (x : ℝ) : f₁ (⟨0,by norm_num⟩,x)=Circle.exp (F₁ x) := by
    change (H.map (⟨0,by norm_num⟩,(Circle.exp (F x).1,Circle.exp (F x).2))).1=_
    rw [H.at_zero]
    rfl
  have hz₂ (x : ℝ) : f₂ (⟨0,by norm_num⟩,x)=Circle.exp (F₂ x) := by
    change (H.map (⟨0,by norm_num⟩,(Circle.exp (F x).1,Circle.exp (F x).2))).2=_
    rw [H.at_zero]
    rfl
  obtain ⟨A₁,hA₁,hA₁zero,hA₁period⟩ :=
    actual_circle_source_homotopy_retains_integer_winding f₁ F₁ m hz₁
      (fun t k x => congrArg Prod.fst (hfperiod t k x))
      (fun k x => congrArg Prod.fst (hp k x))
  obtain ⟨A₂,hA₂,hA₂zero,hA₂period⟩ :=
    actual_circle_source_homotopy_retains_integer_winding f₂ F₂ n hz₂
      (fun t k x => congrArg Prod.snd (hfperiod t k x))
      (fun k x => congrArg Prod.snd (hp k x))
  let A := A₁.prodMk A₂
  exact ⟨A,fun t x => Prod.ext (hA₁ t x) (hA₂ t x),
    fun x => Prod.ext (hA₁zero x) (hA₂zero x),
    fun t k x => Prod.ext (hA₁period t k x) (hA₂period t k x)⟩

#print axioms actual_torus_ambient_move_retains_source_deck_winding
