import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusTranslatedReference
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHomeomorphTransverseTransport
import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteTransverseAssembly

open Set Topology Schoenflies CurveComplex

/-- Produce finite transverse representatives from the ORIGINAL essential
source, with actual puncture-relative source and reference isotopies. Neither
transverse representatives nor a marked class-preservation receipt is supplied. -/
theorem actual_essential_torus_has_puncture_relative_finite_position
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.1=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠c)
    (hp : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image) :
    ∃ P Q : AmbientIsotopy (Circle×Circle), ∃ a' b' : EssentialCurve (Circle×Circle),
    ∃ q : Plane, ∃ cf : ℝ,
      cf=c-q 0+p 0 ∧
      (∀ t, P.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      P.finalMap '' b.val.image=b'.val.image ∧
      Q.finalMap '' a.val.image=a'.val.image ∧
      a'.val.image={z : Circle×Circle | z.1=Circle.exp cf} ∧
      Transverse a'.val b'.val ∧
      (∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠cf) ∧
      (Circle.exp (p 0),Circle.exp (p 1))∉b'.val.image := by
  classical
  let mark : Circle×Circle := (Circle.exp (p 0),Circle.exp (p 1))
  let old : Unit → EssentialCurve (Circle×Circle) := fun _ => a
  have hOld : ∀ i j, i≠j → Transverse (old i).val (old j).val := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  obtain ⟨d,hClass,hTrans⟩ := position_extend_transverse_family (Circle×Circle) Unit old hOld b
  have hRel : AmbientIsotopy.Rel b.val.image d.val.image := by
    exact Quotient.eq.mp hClass.symm
  obtain ⟨H,hHimage⟩ := hRel
  obtain ⟨eH,hEH⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
  have hHinj : Function.Injective H.finalMap := by
    intro x y hxy
    apply eH.injective
    exact (hEH x).trans (hxy.trans (hEH y).symm)
  have hMovedOutside : H.finalMap mark∉d.val.image := by
    intro hz
    rw [← hHimage] at hz
    obtain ⟨x,hx,hxEq⟩ := hz
    have hxMark : x=mark := hHinj hxEq
    apply hp
    change mark∈b.val.image
    rw [← hxMark]
    exact hx
  obtain ⟨J,q,hJfix,hJpoint,hqAvoid⟩ :=
    actual_torus_outside_point_moves_off_reference_fixing_source d.val c (H.finalMap mark) hMovedOutside
  let R := H.compose J
  have hRfinal (z : Circle×Circle) : R.finalMap z=J.finalMap (H.finalMap z) := rfl
  have hJimage : J.finalMap '' d.val.image=d.val.image := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [AmbientIsotopy.finalMap,hJfix _ x hx] using hx
    · intro hz
      exact ⟨z,hz,hJfix _ z hz⟩
  have hRimage : R.finalMap '' b.val.image=d.val.image := by
    change (J.finalMap ∘ H.finalMap) '' b.val.image=d.val.image
    rw [image_comp,hHimage,hJimage]
  have hRpoint : R.finalMap mark=(Circle.exp (q 0),Circle.exp (q 1)) := by
    rw [hRfinal,hJpoint]
  obtain ⟨P,hPfix,hPformula⟩ := actual_group_isotopy_has_point_fixed_normalization R mark
  let e : (Circle×Circle) ≃ₜ (Circle×Circle) := Homeomorph.mulRight ((R.finalMap mark)⁻¹*mark)
  obtain ⟨ar,br,_,_,hAr,hBr,hArBr⟩ :=
    actual_homeomorph_transports_finite_transverse_curves e a.val d.val (hTrans Unit.unit)
  have hPfinal (z : Circle×Circle) : P.finalMap z=e (R.finalMap z) := by
    exact (hPformula _ z).trans (mul_assoc _ _ _)
  have hPimage : P.finalMap '' b.val.image=br.image := by
    have hMaps : P.finalMap=e ∘ R.finalMap := funext hPfinal
    rw [hMaps,image_comp,hRimage,← hBr]
  have hBrEssential : Essential br :=
    (essential_isotopy_invariant (show AmbientIsotopy.Rel b.val.image br.image from ⟨P,hPimage⟩)).mp b.property
  let cf := c-q 0+p 0
  have hCfAvoid : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠cf :=
    actual_normalizing_point_off_grid_gives_translated_reference_avoidance (2*Real.pi) c p q hqAvoid
  have hArReference : ar.image={z : Circle×Circle | z.1=Circle.exp cf} := by
    rw [hAr,ha]
    have heEq : e=Homeomorph.mulRight
        (((Circle.exp (q 0),Circle.exp (q 1)) : Circle×Circle)⁻¹*
          (Circle.exp (p 0),Circle.exp (p 1))) := by
      dsimp [e]
      rw [hRpoint]
      rfl
    rw [heEq]
    exact actual_torus_point_normalization_translates_reference c p q
  obtain ⟨Q₀,hQ₀fix,hQ₀eq,hQ₀grid⟩ :=
    actual_puncture_free_vertical_reference_grids_are_relative_isotopic
      (2*Real.pi) c cf p (by positivity) hpgrid hCfAvoid
  have hz : Plane.mk 0 0=(0:Plane) := by ext k; fin_cases k <;> rfl
  have hQ₀p : ∀ t, Q₀.map (t,p)=p := by intro t; simpa [hz] using hQ₀fix t (0,0)
  obtain ⟨Q,hQcomm,hQfix⟩ := actual_lattice_isotopy_descends_to_marked_torus Q₀ hQ₀eq p hQ₀p
  have hQimage : Q.finalMap '' a.val.image=ar.image := by
    rw [ha,← actual_vertical_grid_projection_is_reference_circle c]
    rw [actual_quotient_commutation_transports_final_image _ Q₀ Q hQcomm,hQ₀grid]
    rw [actual_vertical_grid_projection_is_reference_circle cf,← hArReference]
  have hArEssential : Essential ar :=
    (essential_isotopy_invariant (show AmbientIsotopy.Rel a.val.image ar.image from ⟨Q,hQimage⟩)).mp a.property
  have hBrAvoid : mark∉br.image := by
    intro hmark
    rw [← hPimage] at hmark
    obtain ⟨x,hx,hxEq⟩ := hmark
    obtain ⟨eP,heP⟩ := P.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hxp : x=mark := eP.injective ((heP x).trans (hxEq.trans ((hPfix _).symm.trans (heP mark).symm)))
    apply hp
    change mark∈b.val.image
    rw [← hxp]
    exact hx
  exact ⟨P,Q,⟨ar,hArEssential⟩,⟨br,hBrEssential⟩,q,cf,rfl,hPfix,hQfix,hPimage,hQimage,hArReference,hArBr,hCfAvoid,hBrAvoid⟩

#print axioms actual_essential_torus_has_puncture_relative_finite_position
