import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.TopologicalPrescribedV
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.DisjointTransport
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHomotopicPrimitiveMarkedUniqueness
import CurveComplexGenusTwo.Topology.SourceCycleActual.SourceEssentialCurveComplete
import CurveComplexGenusTwo.Topology.PrimitiveTorusCurve

open Set Topology CurveComplex CurveComplex.Hyperbolic
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplexGenusTwo.Topology

theorem actual_curve_in_literal_punctured_side_fills_torus
    {E : Type} [TopologicalSpace E]
    (V : Set E)
    (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)})
    (g : Curve E) (hgV : g.image ⊆ V) :
    ∃ t : Curve (Circle × Circle),
      (∀ z : Circle, t.map z = (e ⟨g.map z,hgV ⟨z,rfl⟩⟩).val) ∧
      (1,1) ∉ t.image := by
  let f : Circle → Circle × Circle :=
    fun z => (e ⟨g.map z,hgV ⟨z,rfl⟩⟩).val
  have hfcont : Continuous f :=
    continuous_subtype_val.comp (e.continuous.comp
      (g.embedded.continuous.subtype_mk (fun z => hgV ⟨z,rfl⟩)))
  have hfinj : Function.Injective f := by
    intro z w h
    apply g.embedded.injective
    have he : e ⟨g.map z,hgV ⟨z,rfl⟩⟩ =
        e ⟨g.map w,hgV ⟨w,rfl⟩⟩ := Subtype.ext h
    exact congrArg (fun x : V => x.val) (e.injective he)
  have hf : IsEmbedding f := (hfcont.isClosedEmbedding hfinj).isEmbedding
  let t : Curve (Circle × Circle) := ⟨f,hf⟩
  refine ⟨t,fun z => rfl,?_⟩
  rintro ⟨z,hz⟩
  exact (e ⟨g.map z,hgV ⟨z,rfl⟩⟩).property hz

theorem actual_filled_geodesic_horizontal_homotopy
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (d g : Curve E) (Q : C(E,Circle × Circle))
    (t : Curve (Circle × Circle))
    (hdQ : ∀ z : Circle, Q (d.map z)=(z,-1))
    (htQ : ∀ z : Circle, t.map z=Q (g.map z))
    (hhom : FreeHomotopic ⟨d.map,d.embedded.continuous⟩
      ⟨g.map,g.embedded.continuous⟩) :
    (⟨t.map,t.embedded.continuous⟩ : C(Circle,Circle × Circle)).Homotopic
      ⟨torusWindingMap 1 0,continuous_torusWindingMap 1 0⟩ := by
  obtain ⟨K,hK0,hK1⟩ := hhom
  let horizontal : C(Circle,Circle × Circle) :=
    ⟨fun z => (z,-1),continuous_id.prodMk continuous_const⟩
  have hto : horizontal.Homotopic
      (⟨t.map,t.embedded.continuous⟩ : C(Circle,Circle × Circle)) := by
    refine ⟨{ toFun := fun p => Q (K (p.2,p.1))
              continuous_toFun := Q.continuous.comp
                (K.continuous.comp (continuous_snd.prodMk continuous_fst))
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      simpa [horizontal] using (congrArg Q (hK0 z)).trans (hdQ z)
    · intro z
      simpa using (congrArg Q (hK1 z)).trans (htQ z).symm
  have hwind : horizontal.Homotopic
      (⟨torusWindingMap 1 0,continuous_torusWindingMap 1 0⟩ :
        C(Circle,Circle × Circle)) := by
    refine ⟨{ toFun := fun p =>
                (p.2,(PathConnectedSpace.somePath (-1 : Circle) 1) p.1)
              continuous_toFun := continuous_snd.prodMk
                ((PathConnectedSpace.somePath (-1 : Circle) 1).continuous.comp continuous_fst)
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      simp [horizontal]
    · intro z
      simp [torusWindingMap]
  exact hto.symm.trans hwind

theorem actual_filled_horizontal_class_essential
    (t : Curve (Circle × Circle))
    (hwind : (⟨t.map,t.embedded.continuous⟩ :
      C(Circle,Circle × Circle)).Homotopic
        ⟨torusWindingMap 1 0,continuous_torusWindingMap 1 0⟩) :
    Essential t := by
  intro hdisc
  have hnull :=
    CurveComplexGenusTwo.SourceTopology.boundsDisc_curveMap_nullhomotopic
      t hdisc
  obtain ⟨x,hx⟩ := hnull
  have hwnull :
      (⟨torusWindingMap 1 0,continuous_torusWindingMap 1 0⟩ :
        C(Circle,Circle × Circle)).Nullhomotopic :=
    ⟨x,hwind.symm.trans hx⟩
  let fst : C(Circle × Circle,Circle) :=
    ⟨Prod.fst,continuous_fst⟩
  have hfirst := hwnull.comp_right fst
  have hfid : (ContinuousMap.id Circle).Nullhomotopic := by
    convert hfirst using 1
    ext z
    simp [fst,torusWindingMap]
  exact actual_circle_id_not_nullhomotopic hfid

theorem actual_literal_side_horizontal_and_geodesic_marked_alignment
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (V : Set E) (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)})
    (d g : Curve E) (hdV : d.image ⊆ V) (hgV : g.image ⊆ V)
    (Q : C(E,Circle × Circle))
    (hQV : ∀ x : V, Q x.val=(e x).val)
    (hdQ : ∀ z : Circle, Q (d.map z)=(z,-1))
    (hhom : FreeHomotopic ⟨d.map,d.embedded.continuous⟩
      ⟨g.map,g.embedded.continuous⟩) :
    ∃ td tg : Curve (Circle × Circle),
      (∀ z : Circle, td.map z=(e ⟨d.map z,hdV ⟨z,rfl⟩⟩).val) ∧
      (∀ z : Circle, tg.map z=(e ⟨g.map z,hgV ⟨z,rfl⟩⟩).val) ∧
      ∃ H : AmbientIsotopy (Circle × Circle),
        (∀ t, H.map (t,(1,1))=(1,1)) ∧
        H.finalMap '' td.image=tg.image := by
  obtain ⟨td,htd,htdp⟩ :=
    actual_curve_in_literal_punctured_side_fills_torus V e d hdV
  obtain ⟨tg,htg,htgp⟩ :=
    actual_curve_in_literal_punctured_side_fills_torus V e g hgV
  have htdQ (z : Circle) : td.map z=Q (d.map z) :=
    (htd z).trans (hQV ⟨d.map z,hdV ⟨z,rfl⟩⟩).symm
  have htgQ (z : Circle) : tg.map z=Q (g.map z) :=
    (htg z).trans (hQV ⟨g.map z,hgV ⟨z,rfl⟩⟩).symm
  have hwd := actual_filled_geodesic_horizontal_homotopy
    d d Q td hdQ htdQ (actual_free_homotopic_refl _)
  have hwg := actual_filled_geodesic_horizontal_homotopy
    d g Q tg hdQ htgQ hhom
  let a : EssentialCurve (Circle × Circle) :=
    ⟨td,actual_filled_horizontal_class_essential td hwd⟩
  let b : EssentialCurve (Circle × Circle) :=
    ⟨tg,actual_filled_horizontal_class_essential tg hwg⟩
  have hpunct :
      (Circle.exp ((0 : Schoenflies.Plane) 0),
        Circle.exp ((0 : Schoenflies.Plane) 1))=(1,1) := by
    simp
  have ha :
      (Circle.exp ((0 : Schoenflies.Plane) 0),
        Circle.exp ((0 : Schoenflies.Plane) 1))∉a.val.image := by
    rw [hpunct]
    exact htdp
  have hb :
      (Circle.exp ((0 : Schoenflies.Plane) 0),
        Circle.exp ((0 : Schoenflies.Plane) 1))∉b.val.image := by
    rw [hpunct]
    exact htgp
  obtain ⟨H,hfix,himage⟩ :=
    actual_same_primitive_homotopy_class_has_marked_ambient_uniqueness
      a b 0 ha hb 1 0 (by norm_num) hwd hwg
  refine ⟨td,tg,htd,htg,H,?_,himage⟩
  intro t
  simpa [hpunct] using hfix t

theorem actual_marked_torus_alignment_preserves_side_complement_connected
    {E : Type} [TopologicalSpace E]
    (V : Set E) (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)})
    (d g : Curve E) (hdV : d.image ⊆ V) (hgV : g.image ⊆ V)
    (Q : C(E,Circle × Circle))
    (hQV : ∀ x : V, Q x.val=(e x).val)
    (td tg : Curve (Circle × Circle))
    (htd : ∀ z : Circle, td.map z=(e ⟨d.map z,hdV ⟨z,rfl⟩⟩).val)
    (htg : ∀ z : Circle, tg.map z=(e ⟨g.map z,hgV ⟨z,rfl⟩⟩).val)
    (H : AmbientIsotopy (Circle × Circle))
    (hfix : ∀ t, H.map (t,(1,1))=(1,1))
    (himage : H.finalMap '' td.image=tg.image)
    (hdconn : IsConnected (V \ d.image)) :
    IsConnected (V \ g.image) := by
  let p : Circle × Circle := (1,1)
  let Sd : Set (Circle × Circle) := {y | y ≠ p ∧ y ∉ td.image}
  let Sg : Set (Circle × Circle) := {y | y ≠ p ∧ y ∉ tg.image}
  have hQd : Q '' (V \ d.image)=Sd := by
    ext y
    constructor
    · rintro ⟨x,⟨hxV,hxd⟩,rfl⟩
      rw [hQV ⟨x,hxV⟩]
      constructor
      · exact (e ⟨x,hxV⟩).property
      · rintro ⟨z,hz⟩
        have he : e ⟨x,hxV⟩=e ⟨d.map z,hdV ⟨z,rfl⟩⟩ :=
          Subtype.ext (hz.symm.trans (htd z))
        exact hxd ⟨z,(congrArg Subtype.val (e.injective he)).symm⟩
    · rintro ⟨hy,hyt⟩
      let x : V := e.symm ⟨y,hy⟩
      have hxd : x.val ∉ d.image := by
        rintro ⟨z,hz⟩
        apply hyt
        refine ⟨z,?_⟩
        have hdx : (⟨d.map z,hdV ⟨z,rfl⟩⟩ : V)=x := Subtype.ext hz
        rw [htd z,hdx]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)
      refine ⟨x.val,⟨x.property,hxd⟩,?_⟩
      rw [hQV]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)
  have hSd : IsConnected Sd := by
    rw [← hQd]
    exact hdconn.image Q Q.continuous.continuousOn
  obtain ⟨h,hh⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : (h : Circle × Circle → Circle × Circle)=H.finalMap := funext hh
  have hpfix : h p=p := by
    exact hh p |>.trans (hfix ⟨1,by norm_num⟩)
  have hmap : h '' td.image=tg.image := by
    rw [hfinal]
    exact himage
  have hSg : h '' Sd=Sg := by
    ext y
    constructor
    · rintro ⟨x,⟨hxp,hxD⟩,rfl⟩
      constructor
      · intro he
        exact hxp (h.injective (he.trans hpfix.symm))
      · intro hyG
        apply hxD
        have : h x ∈ h '' td.image := hmap ▸ hyG
        obtain ⟨w,hw,he⟩ := this
        simpa [h.injective he] using hw
    · intro hy
      let x := h.symm y
      have hx : h x=y := h.apply_symm_apply y
      have hxp : x≠p := by
        intro he
        exact hy.1 (by rw [←hx,he,hpfix])
      have hxD : x∉td.image := by
        intro hxd
        exact hy.2 (hmap ▸ ⟨x,hxd,hx⟩)
      exact ⟨x,⟨hxp,hxD⟩,hx⟩
  have hSgconn : IsConnected Sg := by
    rw [←hSg]
    exact hSd.image h h.continuous.continuousOn
  let R : Sg → E := fun y =>
    (e.symm ⟨y.val,y.property.1⟩).val
  have hR : Continuous R := by
    apply continuous_subtype_val.comp
    apply e.symm.continuous.comp
    exact continuous_subtype_val.subtype_mk _
  have hRange : range R=V \ g.image := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      refine ⟨(e.symm ⟨y.val,y.property.1⟩).property,?_⟩
      rintro ⟨z,hz⟩
      apply y.property.2
      refine ⟨z,?_⟩
      rw [htg]
      have he : e ⟨g.map z,hgV ⟨z,rfl⟩⟩=
          e (e.symm ⟨y.val,y.property.1⟩) :=
        congrArg e (Subtype.ext hz)
      simpa using congrArg Subtype.val he
    · rintro ⟨hxV,hxg⟩
      let y := e ⟨x,hxV⟩
      have hyG : y.val ∉ tg.image := by
        rintro ⟨z,hz⟩
        apply hxg
        have he : e ⟨g.map z,hgV ⟨z,rfl⟩⟩=y :=
          Subtype.ext ((htg z).symm.trans hz)
        exact ⟨z,congrArg Subtype.val (e.injective he)⟩
      refine ⟨⟨y.val,⟨y.property,hyG⟩⟩,?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x,hxV⟩)
  rw [←hRange]
  letI : ConnectedSpace Sg := isConnected_iff_connectedSpace.mp hSgconn
  exact isConnected_range hR

#print axioms actual_curve_in_literal_punctured_side_fills_torus
#print axioms actual_filled_geodesic_horizontal_homotopy
#print axioms actual_filled_horizontal_class_essential
#print axioms actual_literal_side_horizontal_and_geodesic_marked_alignment
#print axioms actual_marked_torus_alignment_preserves_side_complement_connected
