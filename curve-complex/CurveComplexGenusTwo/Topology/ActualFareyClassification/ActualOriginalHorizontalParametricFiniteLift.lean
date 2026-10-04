import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalWindingFinitePosition
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFiniteSurfaceLiftBridge

open Set Topology Schoenflies CurveComplex

/-- ORIGINAL essential horizontal-winding data constructs EVERY source datum
needed by the zero-drift reducer. No finite contacts or transverse certificate
is supplied. This is an actual source producer, not a reduction consumer. -/
theorem actual_original_horizontal_winding_has_parametric_horizontal_finite_lift_source
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.2=Circle.exp c})
    (hpgrid : ∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠c)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image)
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2)) :
    ∃ P Q : AmbientIsotopy (Circle×Circle), ∃ G : C(ℝ,Plane), ∃ cf : ℝ,
      (∀ t, P.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      (∀ t, Q.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      P.finalMap '' b.val.image=
        (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range G ∧
      Q.finalMap '' a.val.image={z : Circle×Circle | z.2=Circle.exp cf} ∧
      (∀ x, (Circle.exp (G x 0),Circle.exp (G x 1))=P.finalMap (b.val.map (Circle.exp x))) ∧
      IsClosedEmbedding G ∧
      (∀ (k : ℤ) x, G (x+(k:ℝ)*(2*Real.pi))=
        G x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),
        G x=G y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0) ∧
      (∀ i : ℤ, p 1+(i:ℝ)*(2*Real.pi)≠cf) ∧
      Disjoint (range G)
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      {t : Ico 0 (0+2*Real.pi) | ∃ i : ℤ, G t.val 1=cf+(i:ℝ)*(2*Real.pi)}.Finite ∧
    (∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) →
      q 1=cf+(i:ℝ)*(2*Real.pi) →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=cf+(i:ℝ)*(2*Real.pi) ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))) := by
  obtain ⟨P,Q,a',d,cf,F',hPfix,hQfix,hParam,hDimage,hQimage,hRef,hTrans,
      hCfAvoid,hFproj,hFperiod,hFClosed,hFCollision,hFOrbitAvoid⟩ :=
    actual_horizontal_finite_position_retains_original_winding_lift a b c p ha hpgrid hAvoid
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
  obtain ⟨hfinite,htrans⟩ := actual_finite_horizontal_transverse_torus_has_normalized_lift_data
    G hG cf hGperiod hGcollision a'.val d.val hRef hImage hTrans
  refine ⟨P,Q,G,cf,hPfix,hQfix,?_,?_,?_,hG,hGperiod,hGcollision,hCfAvoid,hGOrbitAvoid,hfinite,htrans⟩
  · exact hDimage.trans hImage
  · exact hQimage.trans hRef
  · intro x
    exact (hGproj x).trans (hParam (Circle.exp x))

#print axioms actual_original_horizontal_winding_has_parametric_horizontal_finite_lift_source
