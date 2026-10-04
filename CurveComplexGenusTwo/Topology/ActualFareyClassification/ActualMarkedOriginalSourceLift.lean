import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSourceLiftDeckCollision

open Set Topology Schoenflies CurveComplex

/-- Transport the actual original parametrized essential source through a
marked ambient move, retaining its original deck winding and puncture avoidance.
The new source lift is constructed by homotopy lifting, not newly chosen. -/
theorem actual_marked_ambient_move_has_original_winding_source_lift
    (H : AmbientIsotopy (Circle×Circle)) (c : EssentialCurve (Circle×Circle))
    (F : C(ℝ,ℝ×ℝ)) (m n : ℤ) (hnz : m≠0 ∨ n≠0)
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=c.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F x).2+((k*n:ℤ):ℝ)*(2*Real.pi)))
    (p : ℝ×ℝ) (hfix : ∀ t, H.map (t,(Circle.exp p.1,Circle.exp p.2))=
      (Circle.exp p.1,Circle.exp p.2))
    (hAvoid : (Circle.exp p.1,Circle.exp p.2)∉c.val.image) :
    ∃ d : EssentialCurve (Circle×Circle), ∃ F' : C(ℝ,ℝ×ℝ),
      (∀ z, d.val.map z=H.finalMap (c.val.map z)) ∧
      H.finalMap '' c.val.image=d.val.image ∧
      (∀ x, (Circle.exp (F' x).1,Circle.exp (F' x).2)=d.val.map (Circle.exp x)) ∧
      (∀ (k : ℤ) x, F' (x+(k:ℝ)*(2*Real.pi))=
        ((F' x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F' x).2+((k*n:ℤ):ℝ)*(2*Real.pi))) ∧
      IsClosedEmbedding F' ∧
      (∀ (x y : ℝ) (a b : ℤ),
        F' x=((F' y).1+(a:ℝ)*(2*Real.pi),(F' y).2+(b:ℝ)*(2*Real.pi)) →
        ∃ k : ℤ, x=y+(k:ℝ)*(2*Real.pi) ∧ a=k*m ∧ b=k*n) ∧
      Disjoint (range F') (⋃ i : ℤ×ℤ,
        {((p.1+(i.1:ℝ)*(2*Real.pi)),(p.2+(i.2:ℝ)*(2*Real.pi)))}) := by
  obtain ⟨e,he⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
  have hE : H.finalMap=e := funext (fun z => (he z).symm)
  let d₀ : Curve (Circle×Circle) := {
    map := fun z => H.finalMap (c.val.map z)
    embedded := by change IsEmbedding (H.finalMap ∘ c.val.map); rw [hE]; exact e.isEmbedding.comp c.val.embedded }
  have hImage : H.finalMap '' c.val.image=d₀.image := by
    change H.finalMap '' range c.val.map=range (H.finalMap ∘ c.val.map)
    exact (range_comp H.finalMap c.val.map).symm
  have hEssential : Essential d₀ :=
    (essential_isotopy_invariant (show AmbientIsotopy.Rel c.val.image d₀.image from ⟨H,hImage⟩)).mp c.property
  obtain ⟨A,hA,_,hAp⟩ := actual_torus_ambient_move_retains_source_deck_winding H F m n hp
  let F' : C(ℝ,ℝ×ℝ) := ⟨fun x => A (⟨1,by norm_num⟩,x),by fun_prop⟩
  have hProj' (x : ℝ) : (Circle.exp (F' x).1,Circle.exp (F' x).2)=d₀.map (Circle.exp x) := by
    exact (hA _ x).trans (congrArg H.finalMap (hproj x))
  have hPeriod' (k : ℤ) (x : ℝ) : F' (x+(k:ℝ)*(2*Real.pi))=
      ((F' x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F' x).2+((k*n:ℤ):ℝ)*(2*Real.pi)) := hAp _ k x
  have hClosed' := actual_embedded_nonzero_winding_lift_is_closed_embedding d₀ F' m n hProj' hPeriod' hnz
  have hCollision' := actual_embedded_source_lift_has_exact_deck_collision d₀ F' m n hProj' hPeriod'
  have hAvoid' : (Circle.exp p.1,Circle.exp p.2)∉d₀.image := by
    rintro ⟨z,hz⟩
    have hh : H.finalMap (c.val.map z)=H.finalMap (Circle.exp p.1,Circle.exp p.2) := hz.trans (hfix _).symm
    have hc : c.val.map z=(Circle.exp p.1,Circle.exp p.2) := by
      apply e.injective
      simpa only [← hE] using hh
    exact hAvoid ⟨z,hc⟩
  refine ⟨⟨d₀,hEssential⟩,F',fun _ => rfl,hImage,hProj',hPeriod',hClosed',hCollision',?_⟩
  apply disjoint_left.mpr
  rintro z ⟨x,rfl⟩ hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  have heq : F' x=(p.1+(i.1:ℝ)*(2*Real.pi),p.2+(i.2:ℝ)*(2*Real.pi)) := hi
  apply hAvoid'
  refine ⟨Circle.exp x,?_⟩
  rw [← hProj' x,heq]
  simp only [Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]

#print axioms actual_marked_ambient_move_has_original_winding_source_lift
