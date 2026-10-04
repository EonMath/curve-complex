import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalEssentialFinitePosition
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEssentialMarkedWindingFinitePosition

open Set Topology Schoenflies CurveComplex

/-- Source-driven finite position with an ACTUAL transported original lift:
puncture-relative source/reference moves and finite transversality are produced,
and the ORIGINAL parametrization and both winding integers are retained. -/
theorem actual_horizontal_finite_position_retains_original_winding_lift
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.2=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠c)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ)) (m n : ℤ) (hnz : m≠0 ∨ n≠0)
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F x).2+((k*n:ℤ):ℝ)*(2*Real.pi))) :
    ∃ P Q : AmbientIsotopy (Circle×Circle), ∃ a' d : EssentialCurve (Circle×Circle),
    ∃ cf : ℝ, ∃ F' : C(ℝ,ℝ×ℝ),
      (∀ t, P.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ z, d.val.map z=P.finalMap (b.val.map z)) ∧
      P.finalMap '' b.val.image=d.val.image ∧
      Q.finalMap '' a.val.image=a'.val.image ∧
      a'.val.image={z : Circle×Circle | z.2=Circle.exp cf} ∧
      Transverse a'.val d.val ∧
      (∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠cf) ∧
      (∀ x, (Circle.exp (F' x).1,Circle.exp (F' x).2)=d.val.map (Circle.exp x)) ∧
      (∀ (k : ℤ) x, F' (x+(k:ℝ)*(2*Real.pi))=
        ((F' x).1+((k*m:ℤ):ℝ)*(2*Real.pi),(F' x).2+((k*n:ℤ):ℝ)*(2*Real.pi))) ∧
      IsClosedEmbedding F' ∧
      (∀ (x y : ℝ) (i j : ℤ),
        F' x=((F' y).1+(i:ℝ)*(2*Real.pi),(F' y).2+(j:ℝ)*(2*Real.pi)) →
        ∃ k : ℤ, x=y+(k:ℝ)*(2*Real.pi) ∧ i=k*m ∧ j=k*n) ∧
      Disjoint (range F') (⋃ i : ℤ×ℤ,
        {((p 0+(i.1:ℝ)*(2*Real.pi)),(p 1+(i.2:ℝ)*(2*Real.pi)))}) := by
  obtain ⟨P,Q,a',b',cf,hPfix,hQfix,hPimage,hQimage,hRef,hTrans,hCfAvoid,_⟩ :=
    actual_horizontal_essential_has_marked_finite_position a b c p ha hpgrid hAvoid
  obtain ⟨d,F',hParam,hDimage,hProj',hPeriod',hClosed',hCollision',hOrbitAvoid⟩ :=
    actual_marked_ambient_move_has_original_winding_source_lift P b F m n hnz hproj hp
      (p 0,p 1) hPfix hAvoid
  have hTrans' : Transverse a'.val d.val :=
    actual_transverse_of_literal_equal_images a'.val b'.val a'.val d.val rfl
      (hPimage.symm.trans hDimage) hTrans
  exact ⟨P,Q,a',d,cf,F',hPfix,hQfix,hParam,hDimage,hQimage,hRef,hTrans',hCfAvoid,
    hProj',hPeriod',hClosed',hCollision',hOrbitAvoid⟩


#print axioms actual_horizontal_finite_position_retains_original_winding_lift
