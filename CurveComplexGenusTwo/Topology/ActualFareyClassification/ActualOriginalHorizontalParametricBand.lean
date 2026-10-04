import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalMarkedPhysicalBand
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHorizontalParametricFiniteLift
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHomeomorphEssentialPositionTransport
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusIsotopyDescent
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusImageTransport

open Set Topology Schoenflies CurveComplex

/-- ORIGINAL essential horizontal winding representatives produce an actual
marked torus isotope confined to one lifted horizontal band. Finite transverse
position, actual reduction, finite termination and quotient descent are all
constructed; no finite contacts or reducing sequence is an input. -/
theorem actual_original_horizontal_essential_has_marked_parametric_band
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.2=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠c)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2)) :
    ∃ H : AmbientIsotopy (Circle×Circle),∃ Gf : C(ℝ,Plane),∃ b' : EssentialCurve (Circle×Circle),∃ d : ℝ,
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' b.val.image=
        (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range Gf ∧
      (∀ x, (Circle.exp (Gf x 0),Circle.exp (Gf x 1))=b'.val.map (Circle.exp x)) ∧
      b'.val.image=H.finalMap '' b.val.image ∧
      IsClosedEmbedding Gf ∧
      (∀ (k : ℤ) x,Gf (x+(k:ℝ)*(2*Real.pi))=Gf x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),Gf x=Gf y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))→j=0) ∧
      Disjoint (range Gf) (⋃ i : ℤ×ℤ,{p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      (∀ x,d<Gf x 1 ∧ Gf x 1<d+2*Real.pi) := by
  obtain ⟨P,Q,G,cf,hPfix,hQfix,hPimage,hQimage,hParam,hG,hperiod,hcollision,hRef,hGM,hFinite,hTrans⟩ :=
    actual_original_horizontal_winding_has_parametric_horizontal_finite_lift_source a b c p ha hpgrid hAvoid F hproj hp
  obtain ⟨S,Gf,cf',d,hGfEq,hSfix,hSeq,hGf,hpf,hcf,hRef',hGMf,hBand⟩ :=
    actual_horizontal_source_has_marked_physical_band G hG (2*Real.pi) cf (by positivity)
      hperiod hcollision hFinite hTrans p hRef hGM
  have hz : Plane.mk 0 0=(0:Plane) := by ext q; fin_cases q <;> rfl
  have hSp : ∀ t,S.map (t,p)=p := by intro t; simpa [hz] using hSfix t (0,0)
  obtain ⟨R,hRcomm,hRfix⟩ := actual_lattice_isotopy_descends_to_marked_torus S hSeq p hSp
  have hGfImage : S.finalMap '' range G=range Gf := by
    ext z
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩; exact ⟨x,hGfEq x⟩
    · rintro ⟨x,rfl⟩; exact ⟨G x,mem_range_self x,(hGfEq x).symm⟩
  let π : Plane→Circle×Circle := fun z => (Circle.exp (z 0),Circle.exp (z 1))
  have hImage : (P.compose R).finalMap '' b.val.image=π '' range Gf := by
    change (fun z => R.finalMap (P.finalMap z)) '' b.val.image=π '' range Gf
    rw [←image_image,hPimage,actual_quotient_commutation_transports_final_image π S R hRcomm,hGfImage]
  obtain ⟨e,he⟩ := (P.compose R).homeomorphism_at ⟨1,by norm_num⟩
  obtain ⟨b',hb'param,hb'image⟩ := actual_homeomorph_transports_essential_curve e b
  have hfinal : e=(P.compose R).finalMap := funext he
  refine ⟨P.compose R,Gf,b',d,?_,hImage,?_,?_,hGf,hpf,hcf,hGMf,hBand⟩
  · intro t
    change R.map (t,P.map (t,(Circle.exp (p 0),Circle.exp (p 1))))=(Circle.exp (p 0),Circle.exp (p 1))
    rw [hPfix,hRfix]
  · intro x
    rw [hb'param,hfinal]
    change π (Gf x)=R.finalMap (P.finalMap (b.val.map (Circle.exp x)))
    rw [hGfEq]
    calc
      π (S.finalMap (G x)) = R.finalMap (π (G x)) :=
        (hRcomm ⟨1,by norm_num⟩ (G x)).symm
      _ = _ := congrArg R.finalMap (hParam x)
  · simpa only [hfinal] using hb'image

#print axioms actual_original_horizontal_essential_has_marked_parametric_band
