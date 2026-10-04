import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEssentialMarkedWindingFinitePosition
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFiniteSurfaceLiftBridge

open Set Topology Schoenflies CurveComplex

/-- Start with an ORIGINAL essential normalized-winding source and its literal
lift. Finite position, puncture-relative normalization, lifted transverse data,
actual Nat descent, and quotient isotopies are ALL constructed here. -/
theorem actual_original_horizontal_winding_essential_has_marked_terminal_strip
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.1=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠c)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2)) :
    ∃ H Q : AmbientIsotopy (Circle×Circle), ∃ Gf : C(ℝ,Plane), ∃ cf r : ℝ,
      (∀ t, H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' b.val.image=
        (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range Gf ∧
      Q.finalMap '' a.val.image={z : Circle×Circle | z.1=Circle.exp cf} ∧
      IsClosedEmbedding Gf ∧
      (∀ (k : ℤ) x, Gf (x+(k:ℝ)*(2*Real.pi))=
        Gf x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),
        Gf x=Gf y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0) ∧
      (∀ i : ℤ, p 0+(i:ℝ)*(2*Real.pi)≠cf) ∧
      Disjoint (range Gf)
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      {t : ℝ | Gf t 0=cf}={r} ∧
      (∀ t∈Ioo r (r+2*Real.pi), cf<Gf t 0 ∧ Gf t 0<cf+2*Real.pi) := by
  obtain ⟨P₀,Q₀,a',d,q,cf₀,F',_,hP₀fix,hQ₀fix,_,hDimage,hQ₀image,hRef,hTrans,
      hCf₀Avoid,hFproj,hFperiod,hFClosed,hFCollision,hFOrbitAvoid⟩ :=
    actual_essential_marked_finite_position_retains_original_winding_lift a b c p ha hpgrid hAvoid
      F 1 0 (Or.inl (by norm_num)) hproj (fun k x => by simpa using hp k x)
  let E : Plane ≃ₜ ℝ×ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans Homeomorph.finTwoArrow
  let G : C(ℝ,Plane) := ⟨fun x => E.symm (F' x),by fun_prop⟩
  have hG : IsClosedEmbedding G := E.symm.isClosedEmbedding.comp hFClosed
  have hGperiod (k : ℤ) (x : ℝ) : G (x+(k:ℝ)*(2*Real.pi))=
      G x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0 := by
    apply E.injective
    change F' (x+(k:ℝ)*(2*Real.pi))=((F' x).1+(k:ℝ)*(2*Real.pi),(F' x).2+0)
    simpa using hFperiod k x
  have hGcollision (x y : ℝ) (i j : ℤ)
      (hxy : G x=G y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))) : j=0 := by
    have hh := congrArg E hxy
    change F' x=((F' y).1+(i:ℝ)*(2*Real.pi),(F' y).2+(j:ℝ)*(2*Real.pi)) at hh
    obtain ⟨k,_,_,hj⟩ := hFCollision x y i j hh
    simpa using hj
  have hGOrbitAvoid : Disjoint (range G)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) := by
    apply disjoint_left.mpr
    rintro z ⟨x,rfl⟩ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have heq : G x=p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) := hi
    have hh := congrArg E heq
    change F' x=(p 0+(i.1:ℝ)*(2*Real.pi),p 1+(i.2:ℝ)*(2*Real.pi)) at hh
    exact disjoint_left.mp hFOrbitAvoid (mem_range_self x) (mem_iUnion.mpr ⟨i,hh⟩)
  let π : Plane → Circle×Circle := fun z => (Circle.exp (z 0),Circle.exp (z 1))
  have hGproj (x : ℝ) : π (G x)=d.val.map (Circle.exp x) := hFproj x
  have hImage : d.val.image=π '' range G := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      obtain ⟨x,rfl⟩ := Circle.exp_surjective w
      exact ⟨G x,mem_range_self x,hGproj x⟩
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨Circle.exp x,(hGproj x).symm⟩
  obtain ⟨hfinite,htrans⟩ := actual_finite_transverse_torus_has_normalized_lift_data
    G hG cf₀ hGperiod hGcollision a'.val d.val hRef hImage hTrans
  obtain ⟨P₁,Q₁,Gf,cf,r,hGfEq,hP₁fix,hP₁eq,hQ₁fix,hQ₁eq,hQ₁grid,
      hGf,hGfperiod,hGfcollision,hCfAvoid,hGfOrbit,hFiber,_,_,_,hStrip,_,_⟩ :=
    normalized_actual_source_has_marked_terminal_strip_and_relative_reference
      G hG (2*Real.pi) cf₀ (by positivity) hGperiod hGcollision hfinite htrans p hCf₀Avoid hGOrbitAvoid
  have hz : Plane.mk 0 0=(0:Plane) := by ext k; fin_cases k <;> rfl
  have hP₁p : ∀ t, P₁.map (t,p)=p := by intro t; simpa [hz] using hP₁fix t (0,0)
  have hQ₁p : ∀ t, Q₁.map (t,p)=p := by intro t; simpa [hz] using hQ₁fix t (0,0)
  obtain ⟨R,hRcomm,hRfix⟩ := actual_lattice_isotopy_descends_to_marked_torus P₁ hP₁eq p hP₁p
  obtain ⟨S,hScomm,hSfix⟩ := actual_lattice_isotopy_descends_to_marked_torus Q₁ hQ₁eq p hQ₁p
  have hGfImage : P₁.finalMap '' range G=range Gf := by
    ext z
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩; exact ⟨x,hGfEq x⟩
    · rintro ⟨x,rfl⟩; exact ⟨G x,mem_range_self x,(hGfEq x).symm⟩
  have hRimage : R.finalMap '' d.val.image=π '' range Gf := by
    rw [hImage,actual_quotient_commutation_transports_final_image π P₁ R hRcomm,hGfImage]
  have hSimage : S.finalMap '' a'.val.image={z : Circle×Circle | z.1=Circle.exp cf} := by
    rw [hRef,← actual_vertical_grid_projection_is_reference_circle cf₀]
    rw [actual_quotient_commutation_transports_final_image _ Q₁ S hScomm,hQ₁grid]
    exact actual_vertical_grid_projection_is_reference_circle cf
  let H := P₀.compose R
  let Q := Q₀.compose S
  have hHfix (t : Interval) : H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
      (Circle.exp (p 0),Circle.exp (p 1)) := by
    change R.map (t,P₀.map (t,_))=_
    rw [hP₀fix,hRfix]
  have hQfix (t : Interval) : Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
      (Circle.exp (p 0),Circle.exp (p 1)) := by
    change S.map (t,Q₀.map (t,_))=_
    rw [hQ₀fix,hSfix]
  have hHimage : H.finalMap '' b.val.image=π '' range Gf := by
    change (R.finalMap ∘ P₀.finalMap) '' b.val.image=_
    rw [image_comp,hDimage,hRimage]
  have hQimage : Q.finalMap '' a.val.image={z : Circle×Circle | z.1=Circle.exp cf} := by
    change (S.finalMap ∘ Q₀.finalMap) '' a.val.image=_
    rw [image_comp,hQ₀image,hSimage]
  exact ⟨H,Q,Gf,cf,r,hHfix,hQfix,hHimage,hQimage,hGf,hGfperiod,hGfcollision,
    hCfAvoid,hGfOrbit,hFiber,hStrip⟩

#print axioms actual_original_horizontal_winding_essential_has_marked_terminal_strip
