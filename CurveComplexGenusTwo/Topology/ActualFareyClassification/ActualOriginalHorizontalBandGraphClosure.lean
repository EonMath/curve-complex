import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHorizontalParametricBand
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalBandedVerticalFiniteLift
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBandedMarkedTerminalStrip
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalSingleBandMarkedGraph
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedGraphTorusStraightening
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardEssentialReferences
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusSurface
open Set Topology Schoenflies CurveComplex
/-- Actual original horizontal essential representatives straighten relative to
one puncture. Both finite positions, both terminating reductions and the actual
single physical rectangle are constructed from the source. -/
theorem actual_original_horizontal_essential_has_marked_straight_reference
    (b : EssentialCurve (Circle×Circle)) (p : Plane)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x,F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2)) :
    ∃ H : AmbientIsotopy (Circle×Circle),∃ h : ℝ,
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' b.val.image=range (fun z : Circle => (z,Circle.exp h)) := by
  obtain ⟨C,hC⟩ := actual_standard_torus_has_closed_surface_structure
  let := C
  let := hC
  let c₀ := p 0+Real.pi
  let h₀ := p 1+Real.pi
  have hcmark : ∀ i : ℤ,p 0+(i:ℝ)*(2*Real.pi)≠c₀ := by
    intro i hi
    have hh : (2:ℝ)*(i:ℝ)=1 := by dsimp [c₀] at hi; nlinarith [Real.pi_pos]
    have hhZ : (2:ℤ)*i=1 := by exact_mod_cast hh
    omega
  have hhmark : ∀ i : ℤ,p 1+(i:ℝ)*(2*Real.pi)≠h₀ := by
    intro i hi
    have hh : (2:ℝ)*(i:ℝ)=1 := by dsimp [h₀] at hi; nlinarith [Real.pi_pos]
    have hhZ : (2:ℤ)*i=1 := by exact_mod_cast hh
    omega
  obtain ⟨a,ah,_,_,ha,hah⟩ := actual_standard_torus_has_essential_straight_references c₀ h₀
  obtain ⟨L,G₀,b₀,d₀,hLfix,hLimage,hG₀proj,hb₀image,hG₀,hp₀,hc₀,hGM₀,hBand₀⟩ :=
    actual_original_horizontal_essential_has_marked_parametric_band ah b h₀ p hah hhmark hAvoid F hproj hp
  let E : Plane ≃ₜ ℝ×ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans Homeomorph.finTwoArrow
  let F₀ : C(ℝ,ℝ×ℝ) := ⟨fun x => E (G₀ x),by fun_prop⟩
  have hF₀proj : ∀ x,(Circle.exp (F₀ x).1,Circle.exp (F₀ x).2)=b₀.val.map (Circle.exp x) := hG₀proj
  have hF₀period (k : ℤ) (x : ℝ) : F₀ (x+(k:ℝ)*(2*Real.pi))=
      ((F₀ x).1+(k:ℝ)*(2*Real.pi),(F₀ x).2) := by
    change E (G₀ (x+(k:ℝ)*(2*Real.pi)))=_
    rw [hp₀]
    apply Prod.ext
    · rfl
    · change G₀ x 1+0=G₀ x 1
      exact add_zero _
  have hb₀avoid : (Circle.exp (p 0),Circle.exp (p 1))∉b₀.val.image := by
    rw [hb₀image]
    rintro ⟨z,hz,hzEq⟩
    obtain ⟨e,he⟩ := L.homeomorphism_at ⟨1,by norm_num⟩
    have heq : z=(Circle.exp (p 0),Circle.exp (p 1)) := e.injective
      (by rw [he,he]; exact hzEq.trans (hLfix ⟨1,by norm_num⟩).symm)
    exact hAvoid (heq ▸ hz)
  obtain ⟨K,G,hKfix,hKimage,hG,hperiod,hcollision,hBand,hGM,hFinite,hTrans⟩ :=
    actual_original_banded_source_has_vertical_finite_lift a b₀ c₀ d₀ p ha F₀
      hF₀proj hF₀period hBand₀ hb₀avoid
  obtain ⟨P,_,Gf,cf,df,r,hGfEq,hPfix,hPeq,_,_,_,hGf,hpf,_,hBandf,_,_,hFiber,_,_,_,hStrip,_,_⟩ :=
    actual_banded_source_has_marked_terminal_strip_and_relative_reference
      G hG (2*Real.pi) c₀ d₀ (by positivity) hperiod hcollision hBand hFinite hTrans p hcmark hGM
  have hz : Plane.mk 0 0=(0:Plane) := by ext k; fin_cases k <;> rfl
  have hPp : ∀ t,P.map (t,p)=p := by intro t; simpa [hz] using hPfix t (0,0)
  obtain ⟨R,hRcomm,hRfix⟩ := actual_lattice_isotopy_descends_to_marked_torus P hPeq p hPp
  obtain ⟨U,J,hUeq,hUfix,hUJ,hJfirst,hJperiod⟩ :=
    actual_terminal_single_band_has_marked_periodic_graph Gf hGf (2*Real.pi) cf df r
      (by positivity) hpf hFiber hStrip hBandf p
  obtain ⟨V,hVcomm,hVfix⟩ := actual_lattice_isotopy_descends_to_marked_torus U hUeq p hUfix
  obtain ⟨W,hWfix,hWimage⟩ := actual_periodic_graph_has_marked_torus_straightening J p hJfirst hJperiod
  let π : Plane→Circle×Circle := fun z => (Circle.exp (z 0),Circle.exp (z 1))
  have hPGf : P.finalMap '' range G=range Gf := by
    ext z
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩; exact ⟨x,hGfEq x⟩
    · rintro ⟨x,rfl⟩; exact ⟨G x,mem_range_self x,(hGfEq x).symm⟩
  have hRimage : R.finalMap '' (π '' range G)=π '' range Gf := by
    rw [actual_quotient_commutation_transports_final_image π P R hRcomm,hPGf]
  have hVimage : V.finalMap '' (π '' range Gf)=
      range (fun x : ℝ => (Circle.exp (J x 0),Circle.exp (J x 1))) := by
    rw [actual_quotient_commutation_transports_final_image π U V hVcomm,hUJ]
    exact (range_comp π J).symm
  let H := (((L.compose K).compose R).compose V).compose W
  refine ⟨H,J (p 0) 1,?_,?_⟩
  · intro t
    change W.map (t,V.map (t,R.map (t,K.map (t,L.map (t,π p)))))=π p
    rw [hLfix,hKfix,hRfix,hVfix,hWfix]
  · change (W.finalMap ∘ (V.finalMap ∘ (R.finalMap ∘ (K.finalMap ∘ L.finalMap)))) '' b.val.image=_
    rw [image_comp,image_comp,image_comp,image_comp,← hb₀image,hKimage,hRimage,hVimage,hWimage]
#print axioms actual_original_horizontal_essential_has_marked_straight_reference
