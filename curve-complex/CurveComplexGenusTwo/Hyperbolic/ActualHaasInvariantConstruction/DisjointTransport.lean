import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.TopologicalPrescribedV
import CurveComplexGenusTwo.Hyperbolic.OriginalG3Annulus.ActualDisjointHomotopicAnnulus

open Set Topology CurveComplex CurveComplex.Hyperbolic

theorem actual_free_homotopic_symm
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (f g : C(Circle,E)) (h : FreeHomotopic f g) :
    FreeHomotopic g f := by
  obtain ⟨K,h0,h1⟩ := h
  let rev : Interval → Interval := fun t =>
    ⟨1-(t:ℝ),by
      constructor
      · linarith [t.property.2]
      · linarith [t.property.1]⟩
  have hrev : Continuous rev :=
    (continuous_const.sub continuous_subtype_val).subtype_mk
      (fun t => (rev t).property)
  refine ⟨⟨fun p => K (p.1,rev p.2),
    K.continuous.comp (continuous_fst.prodMk (hrev.comp continuous_snd))⟩,?_,?_⟩
  · intro z
    simpa [rev] using h1 z
  · intro z
    simpa [rev] using h0 z

theorem actual_free_homotopic_refl
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (f : C(Circle,E)) : FreeHomotopic f f := by
  refine ⟨⟨fun p => f p.1,f.continuous.comp continuous_fst⟩,?_,?_⟩
  · intro z; rfl
  · intro z; rfl

theorem actual_nondividing_of_disjoint_free_homotopy
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (d g : Curve E)
    (hd : ¬ DividingCurve d) (hde : Essential d) (hge : Essential g)
    (hhom : FreeHomotopic ⟨d.map,d.embedded.continuous⟩
      ⟨g.map,g.embedded.continuous⟩)
    (hdis : Disjoint d.image g.image) :
    ¬ DividingCurve g := by
  obtain ⟨B,hB,hBd,hBg,hBopen⟩ :=
    actual_disjoint_essential_homotopic_curves_have_collared_annulus
      H d g hde hge hhom hdis
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  obtain ⟨F,_,hF,_,_,_⟩ :=
    CurveComplex.G3Review.actual_collared_annulus_ambient_alignment
      d g B hB hBd hBg hBopen
  exact actual_nondividing_of_ambient_isotopy d g hd ⟨F,hF⟩

#print axioms actual_nondividing_of_disjoint_free_homotopy
#print axioms actual_free_homotopic_symm
#print axioms actual_free_homotopic_refl
