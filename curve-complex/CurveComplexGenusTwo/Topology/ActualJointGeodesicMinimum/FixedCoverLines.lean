import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting


namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane

private theorem source_quotient_cover_transport_to_h2
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (q : P → X) (hq : IsQuotientCoveringMap q (deck q))
    (e : P ≃ₜ H2) :
    IsQuotientCoveringMap (fun z : H2 => q (e.symm z))
      (deck (fun z : H2 => q (e.symm z))) := by
  let p : H2 → X := fun z => q (e.symm z)
  have hp : IsCoveringMap p := hq.isCoveringMap.comp_homeomorph e.symm
  have hsurj : Function.Surjective p := by
    intro x
    obtain ⟨y,hy⟩ := hq.surjective x
    exact ⟨e y,by simpa [p] using hy⟩
  let back (d : deck p) : deck q := by
    let φ : P ≃ₜ P := (e.trans d.val).trans e.symm
    have hφ : φ ∈ deck q := by
      apply deck.mem_iff.mpr
      funext u
      change q (e.symm ((d : H2 ≃ₜ H2) (e u))) = q u
      have hd := deck.proj_smul d (e u)
      change q (e.symm ((d : H2 ≃ₜ H2) (e u))) = q (e.symm (e u)) at hd
      simpa using hd
    exact ⟨φ,hφ⟩
  haveI : IsCancelSMul (deck p) H2 := by
    letI : IsCancelSMul (deck q) P := hq.isCancelSMul
    refine { right_cancel' := ?_ }
    intro d₁ d₂ z h
    have hb : back d₁ = back d₂ := by
      apply IsCancelSMul.right_cancel (back d₁) (back d₂) (e.symm z)
      apply e.injective
      change (d₁ : H2 ≃ₜ H2) z = (d₂ : H2 ≃ₜ H2) z at h
      simpa [back] using h
    apply Subtype.ext
    apply Homeomorph.ext
    intro u
    have hu := congrArg (fun k : deck q => (k : P ≃ₜ P) (e.symm u)) hb
    apply e.symm.injective
    simpa [back] using hu
  apply (isQuotientCoveringMap_iff_isCoveringMap_and p (deck p)).mpr
  refine ⟨hp,hsurj,inferInstance,inferInstance,?_⟩
  intro z w
  constructor
  · intro hzw
    have hqzw : q (e.symm z) = q (e.symm w) := hzw
    obtain ⟨η,hη⟩ := hq.apply_eq_iff_mem_orbit.mp hqzw
    let φ : H2 ≃ₜ H2 := (e.symm.trans η.val).trans e
    have hφ : φ ∈ deck p := by
      apply deck.mem_iff.mpr
      funext u
      change q (e.symm (e ((η : P ≃ₜ P) (e.symm u)))) = q (e.symm u)
      rw [e.symm_apply_apply]
      exact deck.proj_smul η (e.symm u)
    let d : deck p := ⟨φ,hφ⟩
    refine ⟨d,?_⟩
    change e ((η : P ≃ₜ P) (e.symm w)) = z
    apply e.symm.injective
    change (η : P ≃ₜ P) (e.symm w) = e.symm z at hη
    simpa only [e.symm_apply_apply] using hη
  · rintro ⟨d,rfl⟩
    exact deck.proj_smul d w

theorem developed_lines_project_onto_path
    {E : Type} [MetricSpace E] (p : H2 → E) (hp : IsCoveringMap p)
    (hmetric : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist (p y) (p z) = dist y z)
    (γ : C(ℝ, E))
    (hunit : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s v : ℝ,
      |s - t| < ε → |v - t| < ε → dist (γ s) (γ v) = |s - v|) :
    ∃ a : {x : H2 // p x ∈ Set.range γ} → ℝ → H2,
      (∀ x, Isometry (a x)) ∧
      (∀ x t, p (a x t) = γ t) ∧
      (∀ x, x.val ∈ Set.range (a x)) ∧
      p ⁻¹' Set.range γ = ⋃ x, Set.range (a x) := by
  classical
  let F := {x : H2 // p x ∈ Set.range γ}
  have hlift (x : F) : ∃ δ : C(ℝ,H2), Isometry δ ∧
      p ∘ δ = γ ∧ x.val ∈ Set.range δ := by
    obtain ⟨t,ht⟩ := x.property
    obtain ⟨δ,⟨hδt,hδp⟩,_⟩ := hp.existsUnique_continuousMap_lifts γ t x.val ht.symm
    have hprojection (u : ℝ) : p (δ u) = γ u := congrFun hδp u
    have hlocal (u : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ s v : ℝ,
        |s-u| < ε → |v-u| < ε → dist (δ s) (δ v) = |s-v| := by
      obtain ⟨ε₀,hε₀,hu⟩ := hunit u
      obtain ⟨U,hU,hδU,hm⟩ := hmetric (δ u)
      obtain ⟨ε₁,hε₁,hball⟩ := Metric.isOpen_iff.mp
        (hU.preimage δ.continuous) u hδU
      refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,?_⟩
      intro s v hs hv
      have hsU : δ s ∈ U := hball (by
        simpa only [Metric.mem_ball,Real.dist_eq] using hs.trans_le (min_le_right _ _))
      have hvU : δ v ∈ U := hball (by
        simpa only [Metric.mem_ball,Real.dist_eq] using hv.trans_le (min_le_right _ _))
      rw [←hm (δ s) hsU (δ v) hvU,hprojection s,hprojection v]
      exact hu s v (hs.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))
    exact ⟨δ,actual_h2_local_unit_geodesic_isometry δ δ.continuous hlocal,
      hδp,⟨t,hδt⟩⟩
  choose δ hδiso hδproj hδrange using hlift
  refine ⟨fun x => δ x,hδiso,?_,hδrange,?_⟩
  · intro x t
    exact congrFun (hδproj x) t
  · ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hδrange ⟨z,hz⟩⟩
    · intro hz
      obtain ⟨x,t,rfl⟩ := Set.mem_iUnion.mp hz
      exact ⟨t,(congrFun (hδproj x) t).symm⟩

section Surface

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem common_component_developed_cover
    (H : ClosedHyperbolicMetric E) (base : E) :
    ∃ p : H2 → connectedComponent base,
      IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Function.Surjective p ∧
      (∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          @dist E H.metric.toDist (p y).val (p z).val = dist y z) := by
  classical
  letI : CompactSpace E := H.compact
  have hT2metric : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at hT2metric
  letI : T2Space E := hT2metric
  let A := connectedComponent base
  letI : CompactSpace A :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  let U : TopologicalSpace.Opens E := ⟨A,isOpen_connectedComponent⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A :=
    TopologicalSpace.Opens.instChartedSpace U
  obtain ⟨coverTopology,_,_,_,hsimply,hquot,hsurj,_⟩ :=
    actual_topological_universal_cover (⟨base,mem_connectedComponent⟩ : A)
  letI : TopologicalSpace (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) := coverTopology
  letI : SimplyConnectedSpace (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) := hsimply
  let q : (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) → A := Sigma.fst
  obtain ⟨development,hmetric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H base
      q hquot.isCoveringMap hsurj
  let p : H2 → A := fun z => q (development.symm z)
  have hpquot : IsQuotientCoveringMap p (deck p) :=
    source_quotient_cover_transport_to_h2 q hquot development
  have hp : IsCoveringMap p :=
    hquot.isCoveringMap.comp_homeomorph development.symm
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨z,hz⟩ := hsurj y
    exact ⟨development z,by simpa [p] using hz⟩
  refine ⟨p,hpquot,hp,hpsurj,?_⟩
  intro x
  obtain ⟨V,hV,hxV,hmetricV⟩ := hmetric (development.symm x)
  refine ⟨development.symm ⁻¹' V,hV.preimage development.symm.continuous,?_,?_⟩
  · simpa only [Set.mem_preimage,development.symm_apply_apply] using hxV
  · intro y hy z hz
    change @dist E H.metric.toDist (q (development.symm y)).val
      (q (development.symm z)).val = dist y z
    simpa only [development.apply_symm_apply] using hmetricV _ hy _ hz

theorem closed_geodesic_lines_on_fixed_cover
    (H : ClosedHyperbolicMetric E) (c : Curve E) (base : E)
    (hbase : base ∈ c.image)
    (hgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image)
    (p : H2 → connectedComponent base) (hp : IsCoveringMap p)
    (hlocal : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        @dist E H.metric.toDist (p y).val (p z).val = dist y z) :
    ∃ γA : C(ℝ, connectedComponent base),
      Subtype.val '' Set.range γA = c.image ∧
      ∃ period : ℝ, 0 < period ∧ Function.Periodic γA period ∧
      ∃ a : {x : H2 // p x ∈ Set.range γA} → ℝ → H2,
        (∀ x, Isometry (a x)) ∧
        (∀ x t, p (a x t) = γA t) ∧
        (∀ x, x.val ∈ Set.range (a x)) ∧
        p ⁻¹' Set.range γA = ⋃ x, Set.range (a x) := by
  classical
  letI : MetricSpace E := H.metric
  let A := connectedComponent base
  let componentMetric : MetricSpace A :=
    MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have componentMetricTopology :
      componentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := componentMetric.replaceTopology componentMetricTopology.symm
  obtain ⟨path,period,hperiod,hcont,hperiodic,hrange,hunit⟩ := hgeo
  have hconnected : IsConnected c.image := by
    change IsConnected (Set.range c.map)
    exact isConnected_range c.embedded.continuous
  have himage : Set.range path ⊆ A := by
    rw [hrange]
    exact hconnected.subset_connectedComponent hbase
  let γA : C(ℝ,A) :=
    ⟨fun t => ⟨path t,himage (Set.mem_range_self t)⟩,hcont.subtype_mk _⟩
  have hunitA : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
        dist (γA s) (γA u) = |s-u| := by
    intro t
    obtain ⟨ε,hε,hm⟩ := hunit t
    refine ⟨ε,hε,?_⟩
    intro s u hs hu
    change @dist E H.metric.toDist (path s) (path u) = |s-u|
    exact hm s u hs hu
  obtain ⟨axes,haxes,hprojection,hanchors,hunion⟩ :=
    developed_lines_project_onto_path
      p hp (by
        intro x
        obtain ⟨U,hU,hxU,hm⟩ := hlocal x
        exact ⟨U,hU,hxU,by
          intro y hy z hz
          change @dist E H.metric.toDist (p y).val (p z).val = dist y z
          exact hm y hy z hz⟩) γA hunitA
  refine ⟨γA,?_,period,hperiod,?_,axes,haxes,hprojection,hanchors,hunion⟩
  · rw [←Set.range_comp]
    have hpath : (Subtype.val ∘ γA) = path := rfl
    rw [hpath]
    exact hrange
  · intro t
    apply Subtype.ext
    exact hperiodic t

theorem two_closed_geodesics_have_common_developed_lines
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (x : E) (hxa : x ∈ a.image) (hxb : x ∈ b.image) :
    ∃ p : H2 → connectedComponent x,
      ∃ γa γb : C(ℝ, connectedComponent x),
      IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Function.Surjective p ∧
      (∀ z : H2, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
        ∀ y ∈ U, ∀ w ∈ U,
          @dist E H.metric.toDist (p y).val (p w).val = dist y w) ∧
      Subtype.val '' Set.range γa = a.image ∧
      Subtype.val '' Set.range γb = b.image ∧
      (∃ period : ℝ, 0 < period ∧ Function.Periodic γa period) ∧
      (∃ period : ℝ, 0 < period ∧ Function.Periodic γb period) ∧
      (∃ fa : {z : H2 // p z ∈ Set.range γa} → ℝ → H2,
        (∀ z, Isometry (fa z)) ∧
        (∀ z t, p (fa z t) = γa t) ∧
        (∀ z, z.val ∈ Set.range (fa z)) ∧
        p ⁻¹' Set.range γa = ⋃ z, Set.range (fa z)) ∧
      (∃ fb : {z : H2 // p z ∈ Set.range γb} → ℝ → H2,
        (∀ z, Isometry (fb z)) ∧
        (∀ z t, p (fb z t) = γb t) ∧
        (∀ z, z.val ∈ Set.range (fb z)) ∧
        p ⁻¹' Set.range γb = ⋃ z, Set.range (fb z)) := by
  obtain ⟨p,hpquot,hp,hpsurj,hmetric⟩ := common_component_developed_cover H x
  obtain ⟨γa,haimage,pa,hpa,hγaper,fa,hfa,hfaproj,hfaanchor,hfaunion⟩ :=
    closed_geodesic_lines_on_fixed_cover H a x hxa hageo p hp hmetric
  obtain ⟨γb,hbimage,pb,hpb,hγbper,fb,hfb,hfbproj,hfbanchor,hfbunion⟩ :=
    closed_geodesic_lines_on_fixed_cover H b x hxb hbgeo p hp hmetric
  exact ⟨p,γa,γb,hpquot,hp,hpsurj,hmetric,haimage,hbimage,
    ⟨pa,hpa,hγaper⟩,⟨pb,hpb,hγbper⟩,
    ⟨fa,hfa,hfaproj,hfaanchor,hfaunion⟩,
    ⟨fb,hfb,hfbproj,hfbanchor,hfbunion⟩⟩

theorem distinct_closed_geodesics_have_meeting_distinct_lifts
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hne : a.image ≠ b.image)
    (x : E) (hxa : x ∈ a.image) (hxb : x ∈ b.image) :
    ∃ p : H2 → connectedComponent x,
      ∃ f g : ℝ → H2,
        ∃ γa γb : C(ℝ, connectedComponent x),
        ∃ pa pb : ℝ,
        IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Isometry f ∧ Isometry g ∧
        (∀ z : H2, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
          ∀ y ∈ U, ∀ w ∈ U,
            @dist E H.metric.toDist (p y).val (p w).val = dist y w) ∧
        0 < pa ∧ 0 < pb ∧ Function.Periodic γa pa ∧ Function.Periodic γb pb ∧
        (∀ u, p (f u) = γa u) ∧ (∀ u, p (g u) = γb u) ∧
        Subtype.val '' Set.range γa = a.image ∧
        Subtype.val '' Set.range γb = b.image ∧
        Set.range (fun u => (p (f u)).val) = a.image ∧
        Set.range (fun u => (p (g u)).val) = b.image ∧
        Set.range f ≠ Set.range g ∧
        ∃ s t : ℝ, f s = g t := by
  obtain ⟨p,γa,γb,hpquot,hp,hpsurj,hmetric,haimage,hbimage,
    ⟨pa,hpa,hγaper⟩,⟨pb,hpb,hγbper⟩,
    ⟨fa,hfa,hfaproj,hfaanchor,_⟩,
    ⟨fb,hfb,hfbproj,hfbanchor,_⟩⟩ :=
    two_closed_geodesics_have_common_developed_lines
      H a b hageo hbgeo x hxa hxb
  obtain ⟨z,hz⟩ := hpsurj (⟨x,mem_connectedComponent⟩ : connectedComponent x)
  have hza : p z ∈ Set.range γa := by
    have hx : x ∈ Subtype.val '' Set.range γa := by rw [haimage]; exact hxa
    obtain ⟨y,hy,hyx⟩ := hx
    have hpyeq : p z = y := by
      apply Subtype.ext
      exact (congrArg Subtype.val hz).trans hyx.symm
    exact hpyeq ▸ hy
  have hzb : p z ∈ Set.range γb := by
    have hx : x ∈ Subtype.val '' Set.range γb := by rw [hbimage]; exact hxb
    obtain ⟨y,hy,hyx⟩ := hx
    have hpyeq : p z = y := by
      apply Subtype.ext
      exact (congrArg Subtype.val hz).trans hyx.symm
    exact hpyeq ▸ hy
  let ia : {w : H2 // p w ∈ Set.range γa} := ⟨z,hza⟩
  let ib : {w : H2 // p w ∈ Set.range γb} := ⟨z,hzb⟩
  let f : ℝ → H2 := fa ia
  let g : ℝ → H2 := fb ib
  have hprojf : Set.range (fun u => (p (f u)).val) = a.image := by
    have hfun : (fun u => (p (f u)).val) = Subtype.val ∘ γa := by
      funext u
      exact congrArg Subtype.val (hfaproj ia u)
    rw [hfun,Set.range_comp]
    exact haimage
  have hprojg : Set.range (fun u => (p (g u)).val) = b.image := by
    have hfun : (fun u => (p (g u)).val) = Subtype.val ∘ γb := by
      funext u
      exact congrArg Subtype.val (hfbproj ib u)
    rw [hfun,Set.range_comp]
    exact hbimage
  have hfg : Set.range f ≠ Set.range g := by
    intro heq
    have hprojEq := congrArg
      (fun S : Set H2 => (fun w => (p w).val) '' S) heq
    rw [←Set.range_comp,←Set.range_comp] at hprojEq
    exact hne (hprojf.symm.trans (hprojEq.trans hprojg))
  obtain ⟨s,hs⟩ := hfaanchor ia
  obtain ⟨t,ht⟩ := hfbanchor ib
  exact ⟨p,f,g,γa,γb,pa,pb,hpquot,hp,hfa ia,hfb ib,hmetric,hpa,hpb,hγaper,hγbper,
    hfaproj ia,hfbproj ib,haimage,hbimage,hprojf,hprojg,hfg,s,t,hs.trans ht.symm⟩

end Surface

end CurveComplex.Hyperbolic.JointMinimum
