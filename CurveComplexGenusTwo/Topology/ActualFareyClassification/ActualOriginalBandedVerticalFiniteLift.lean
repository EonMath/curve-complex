import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBandedVerticalFinitePosition
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFiniteSurfaceLiftBridge
open Set Topology Schoenflies CurveComplex
/-- Actual relative-band surface finite position supplies the WHOLE lifted
vertical family and finite full-real reference contacts, retaining the band. -/
theorem actual_original_banded_source_has_vertical_finite_lift
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (c d : ℝ) (p : Plane)
    (ha : a.val.image={z : Circle×Circle | z.1=Circle.exp c})
    (F : C(ℝ,ℝ×ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2))
    (hband : ∀ x, d<(F x).2 ∧ (F x).2<d+2*Real.pi)
    (hAvoid : (Circle.exp (p 0),Circle.exp (p 1))∉b.val.image) :
    ∃ H : AmbientIsotopy (Circle×Circle), ∃ G : C(ℝ,Plane),
      (∀ t,H.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) ∧
      H.finalMap '' b.val.image=
        (fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range G ∧
      IsClosedEmbedding G ∧
      (∀ (k : ℤ) x,G (x+(k:ℝ)*(2*Real.pi))=G x+Plane.mk ((k:ℝ)*(2*Real.pi)) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ),G x=G y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi))→j=0) ∧
      (∀ x,d<G x 1 ∧ G x 1<d+2*Real.pi) ∧
      Disjoint (range G) (⋃ i : ℤ×ℤ,{p+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi))}) ∧
      {t : ℝ | G t 0=c}.Finite ∧
      (∀ (q : Plane) (i : ℤ),
        q∈(⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) →
        q 0=c+(i:ℝ)*(2*Real.pi) →
        ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
          IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
          (∀ z (hz : z∈U),
            (z 0=c+(i:ℝ)*(2*Real.pi) ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
            (z∈(⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) ↔
              ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))) := by
  obtain ⟨P₀,b',F',hP₀fix,_,_,hDimage,hTrans,hFproj,hFperiod,hFband,hFClosed,hFCollision,hFOrbitAvoid⟩ :=
    actual_banded_source_has_marked_vertical_finite_position a b F d (p 0,p 1)
      hproj hp hband hAvoid
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
  have hGproj (x : ℝ) : π (G x)=b'.val.map (Circle.exp x) := hFproj x
  have hImage : b'.val.image=π '' range G := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      obtain ⟨x,rfl⟩ := Circle.exp_surjective w
      exact ⟨G x,mem_range_self x,hGproj x⟩
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨Circle.exp x,(hGproj x).symm⟩
  obtain ⟨hfinite,htrans⟩ := actual_finite_transverse_torus_has_normalized_lift_data
    G hG c hGperiod hGcollision a.val b'.val ha hImage hTrans
  refine ⟨P₀,G,hP₀fix,hDimage.trans hImage,hG,hGperiod,hGcollision,?_,hGOrbitAvoid,hfinite,htrans⟩
  intro x
  exact hFband x
