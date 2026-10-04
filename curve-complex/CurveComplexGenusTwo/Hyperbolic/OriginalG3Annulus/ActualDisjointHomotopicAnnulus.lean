import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualParametrizedClosedGeodesicG1GenusTwo
import CurveComplexGenusTwo.Topology.TorusPrimitiveLift
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Topology.ActualPrescribedFourArcRectangle
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Topology.TorusStrip.JordanSideContainment
import CurveComplexGenusTwo.Topology.TorusStrip.ArcInterval
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import CurveComplexGenusTwo.Topology.TorusStrip.ProperLineSeparationCore
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.EssentialCurveEssentialLoop
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicAxisAllPROVED
import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualTopologicalUniversalCoverPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualComponentHyperbolicDevelopmentPROVED
import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
open Set Topology CurveComplex CurveComplex.Hyperbolic TopologicalSpace
open Schoenflies
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open scoped Pointwise Manifold unitInterval ContDiff UpperHalfPlane ENNReal MatrixGroups
set_option maxHeartbeats 40000000
namespace CurveComplex.Hyperbolic
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual terminal disjoint-pair band constructor. Inputs are the original
metric, embedded essential curves and their original free homotopy. No annulus,
lift pairing, seam, finite replacement sequence or ambient isotopy is supplied.
The extra collars leave both curves inside the band, allowing a motion fixed
on its outer boundary to extend by identity to the ambient surface. -/
theorem actual_disjoint_essential_homotopic_curves_have_collared_annulus
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (ha : Essential a) (hb : Essential b)
    (hhom : FreeHomotopic ⟨a.map,a.embedded.continuous⟩
      ⟨b.map,b.embedded.continuous⟩)
    (hdis : Disjoint a.image b.image) :
    ∃ B : Circle × Interval → E, IsEmbedding B ∧
      Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩)) = a.image ∧
      Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩)) = b.image ∧
      IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
  classical
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  letI : CompactSpace E := H.compact
  have actual_free_homotopy_strip_lift
      {P X G : Type} [TopologicalSpace P] [TopologicalSpace X]
      [Group G] [MulAction G P]
      (p : P → X) (hp : IsQuotientCoveringMap p G)
      (F : C(Circle × Interval,X)) (x₀ : P)
      (hx₀ : p x₀ = F (1,0)) :
      ∃ L : C(ℝ × Interval,P), ∃ g : G,
        L (0,0) = x₀ ∧
        (∀ (s : ℝ) (t : Interval), p (L (s,t)) = F (Circle.exp s,t)) ∧
        (∀ (s : ℝ) (t : Interval), L (s+2*Real.pi,t) = g • L (s,t)) := by
    classical
    letI : ContinuousConstSMul G P := hp.toContinuousConstSMul
    letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).contractibleSpace
      (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    letI : LocallyPathConnectedSpace Interval :=
      (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).locallyPathConnectedSpace
    let strip : C(ℝ × Interval,X) :=
      ⟨fun st => F (Circle.exp st.1,st.2),
        F.continuous.comp ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd)⟩
    have hxstrip : p x₀ = strip (0,0) := by simpa [strip] using hx₀
    obtain ⟨L,⟨hL₀,hLift⟩,hUnique⟩ :=
      hp.isCoveringMap.existsUnique_continuousMap_lifts strip (0,0) x₀ hxstrip
    have hproject (s : ℝ) (t : Interval) : p (L (s,t)) = F (Circle.exp s,t) :=
      congrFun hLift (s,t)
    have hsame : p (L (2*Real.pi,0)) = p (L (0,0)) := by
      rw [hproject,hproject,Circle.exp_two_pi,Circle.exp_zero]
    obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp hsame
    let M : C(ℝ × Interval,P) :=
      ⟨fun st => g⁻¹ • L (st.1+2*Real.pi,st.2),by fun_prop⟩
    have hM₀ : M (0,0) = x₀ := by
      change g⁻¹ • L (0+2*Real.pi,0) = x₀
      rw [zero_add,← hg,inv_smul_smul,hL₀]
    have hMproject : p ∘ M = strip := by
      funext st
      change p (g⁻¹ • L (st.1+2*Real.pi,st.2)) = F (Circle.exp st.1,st.2)
      rw [hp.map_smul,hproject,Circle.exp_add_two_pi]
    have hML : M = L := hUnique M ⟨hM₀,hMproject⟩
    refine ⟨L,g,hL₀,hproject,?_⟩
    intro s t
    have h := congrArg (fun N : C(ℝ × Interval,P) => g • N (s,t)) hML
    change g • (g⁻¹ • L (s+2*Real.pi,t)) = g • L (s,t) at h
    simpa only [smul_inv_smul] using h
  have actual_source_homotopy_component_strip
      {P G : Type} [TopologicalSpace P] [Group G] [MulAction G P]
      (p : P → connectedComponent (a.map 1)) (hp : IsQuotientCoveringMap p G) :
      ∃ L : C(ℝ × Interval,P), ∃ g : G,
        (∀ (s : ℝ), (p (L (s,0))).val = a.map (Circle.exp s)) ∧
        (∀ (s : ℝ), (p (L (s,1))).val = b.map (Circle.exp s)) ∧
        (∀ (s : ℝ) (t : Interval), L (s+2*Real.pi,t) = g • L (s,t)) := by
    classical
    obtain ⟨F,hF₀,hF₁⟩ := hhom
    have hFrange : Set.range F ⊆ connectedComponent (a.map 1) := by
      apply (isConnected_range F.continuous).subset_connectedComponent
      exact ⟨(1,0),hF₀ 1⟩
    let componentF : C(Circle × Interval,connectedComponent (a.map 1)) :=
      ⟨fun z => ⟨F z,hFrange (Set.mem_range_self z)⟩,F.continuous.subtype_mk _⟩
    let base : connectedComponent (a.map 1) := ⟨a.map 1,mem_connectedComponent⟩
    obtain ⟨x₀,hx₀⟩ := hp.surjective base
    have hxF : p x₀ = componentF (1,0) := by
      rw [hx₀]
      apply Subtype.ext
      exact (hF₀ 1).symm
    obtain ⟨L,g,hL₀,hLproj,hLperiod⟩ := actual_free_homotopy_strip_lift p hp componentF x₀ hxF
    refine ⟨L,g,?_,?_,hLperiod⟩
    · intro s
      exact (congrArg Subtype.val (hLproj s 0)).trans (hF₀ (Circle.exp s))
    · intro s
      exact (congrArg Subtype.val (hLproj s 1)).trans (hF₁ (Circle.exp s))
  let A := connectedComponent (a.map 1)
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace
    (EuclideanSpace ℝ (Fin 2)) E
  have haOpen : IsOpen A := isOpen_connectedComponent
  let componentOpen : TopologicalSpace.Opens E := ⟨A,haOpen⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A :=
    TopologicalSpace.Opens.instChartedSpace componentOpen
  let base : A := ⟨a.map 1,mem_connectedComponent⟩
  obtain ⟨coverTopology,hsecond,hcoverT2,hcharts,hsc,hqc,hsurj,hlift⟩ :=
    actual_topological_universal_cover base
  let P := Σ z : A, Path.Homotopic.Quotient base z
  letI : TopologicalSpace P := coverTopology
  letI : SecondCountableTopology P := hsecond
  letI : T2Space P := hcoverT2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P := hcharts.some
  letI : SimplyConnectedSpace P := hsc
  obtain ⟨development,development_metric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H (a.map 1)
      (Sigma.fst : P → A) hqc.isCoveringMap hsurj
  obtain ⟨L,monodromy,hL0,hL1,hLperiod⟩ :=
    actual_source_homotopy_component_strip (Sigma.fst : P → A) hqc
  let sourceLift : C(ℝ,H2) := ⟨fun s => development (L (s,0)),
    development.continuous.comp (L.continuous.comp
      (continuous_id.prodMk continuous_const))⟩
  let targetLift : C(ℝ,H2) := ⟨fun s => development (L (s,1)),
    development.continuous.comp (L.continuous.comp
      (continuous_id.prodMk continuous_const))⟩
  let developedProjection : H2 → E := fun z => (development.symm z).1.val
  have sourceLift_projection (s : ℝ) :
      developedProjection (sourceLift s) = a.map (Circle.exp s) := by
    change (development.symm (development (L (s,0)))).1.val = _
    rw [development.symm_apply_apply]
    exact hL0 s
  have targetLift_projection (s : ℝ) :
      developedProjection (targetLift s) = b.map (Circle.exp s) := by
    change (development.symm (development (L (s,1)))).1.val = _
    rw [development.symm_apply_apply]
    exact hL1 s
  let developedDeck : deck (Sigma.fst : P → A) → H2 ≃ₜ H2 :=
    fun k => (development.symm.trans k.val).trans development
  have developedDeck_projection (k : deck (Sigma.fst : P → A)) (z : H2) :
      developedProjection (developedDeck k z) = developedProjection z := by
    change (development.symm (development (k • development.symm z))).1.val = _
    rw [development.symm_apply_apply]
    exact congrArg Subtype.val (hqc.map_smul k)
  have sourceLift_period (s : ℝ) : sourceLift (s+2*Real.pi) =
      developedDeck monodromy (sourceLift s) := by
    change development (L (s+2*Real.pi,0)) =
      development (monodromy • development.symm (development (L (s,0))))
    rw [hLperiod,development.symm_apply_apply]
  have targetLift_period (s : ℝ) : targetLift (s+2*Real.pi) =
      developedDeck monodromy (targetLift s) := by
    change development (L (s+2*Real.pi,1)) =
      development (monodromy • development.symm (development (L (s,1))))
    rw [hLperiod,development.symm_apply_apply]
  have all_developed_source_target_translates_disjoint
      (k l : deck (Sigma.fst : P → A)) :
      Disjoint ((developedDeck k) '' Set.range sourceLift)
        ((developedDeck l) '' Set.range targetLift) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨_,⟨s,rfl⟩,hs⟩ ⟨_,⟨t,rfl⟩,ht⟩
    have he : a.map (Circle.exp s) = b.map (Circle.exp t) := by
      calc
        a.map (Circle.exp s) = developedProjection (sourceLift s) :=
          (sourceLift_projection s).symm
        _ = developedProjection (developedDeck k (sourceLift s)) :=
          (developedDeck_projection k _).symm
        _ = developedProjection (developedDeck l (targetLift t)) := by rw [hs,ht]
        _ = developedProjection (targetLift t) := developedDeck_projection l _
        _ = b.map (Circle.exp t) := targetLift_projection t
    exact Set.disjoint_left.mp hdis ⟨Circle.exp s,rfl⟩ ⟨Circle.exp t,he.symm⟩
  have monodromy_ne_one : monodromy ≠ 1 := by
    intro hm
    letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
    let bottom : C(ℝ,P) := ⟨fun s => L (s,0),
      L.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hend : bottom 0 = bottom (2*Real.pi) := by
      have hh := hLperiod 0 0
      simpa [bottom,hm] using hh.symm
    let circleLift : C(Circle,P) :=
      ⟨fun z => AddCircle.liftIco (2*Real.pi) 0 bottom (AddCircle.homeomorphCircle'.symm z),
        (AddCircle.liftIco_zero_continuous hend bottom.continuous.continuousOn).comp
          AddCircle.homeomorphCircle'.symm.continuous⟩
    have hcircle (z : Circle) : (circleLift z).1.val = a.map z := by
      change (L (((AddCircle.equivIco (2*Real.pi) 0)
        (AddCircle.homeomorphCircle'.symm z)),0)).1.val = _
      rw [hL0]
      rw [← AddCircle.homeomorphCircle'_apply_mk, AddCircle.coe_equivIco,
        AddCircle.homeomorphCircle'.apply_symm_apply]
    obtain ⟨plane⟩ := actual_hyperbolic_component_simply_connected_cover_is_plane
      H (a.map 1) (Sigma.fst : P → A) hqc.isCoveringMap hsurj
    have hprojection : Continuous (fun z : P => z.1.val) :=
      continuous_subtype_val.comp hqc.isCoveringMap.continuous
    let contraction : C(Circle × Interval,E) :=
      ⟨fun zt => (plane ((1 - zt.2.val) • plane.symm (circleLift zt.1))).1.val,
        hprojection.comp (plane.continuous.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
            (plane.symm.continuous.comp (circleLift.continuous.comp continuous_fst))))⟩
    apply essential_curve_is_essential_loop H a ha
    refine ⟨(plane 0).1.val,contraction,?_,?_⟩
    · intro z
      change (plane ((1 - (0 : ℝ)) • plane.symm (circleLift z))).1.val = a.map z
      simpa using hcircle z
    · intro z
      change (plane ((1 - (1 : ℝ)) • plane.symm (circleLift z))).1.val = (plane 0).1.val
      simp
  have monodromy_no_fixed_point (x : P) : monodromy • x ≠ x := by
    intro hx
    letI : IsCancelSMul (deck (Sigma.fst : P → A)) P := hqc.isCancelSMul
    exact monodromy_ne_one (IsCancelSMul.right_cancel _ _ x (by simpa using hx))
  have zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have vertical_radius_sphere (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r) :
      Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
        z.im * (1 + (Real.exp r) ^ 2) := by
    have hstd : dist (verticalPath 0) (verticalPath r) = r := by
      simpa [Real.dist_eq,abs_of_nonneg hr,abs_of_nonpos (neg_nonpos.mpr hr)] using
        verticalPath_isometry.dist_eq 0 r
    have hc := congrArg Real.cosh (h.trans (zero_eq_I ▸ hstd).symm)
    rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
    simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at hc
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,
      one_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
    field_simp at hc
    nlinarith [hc]
  have denominator_nonzero (a b : ℝ) (hab : 0 < a^2+b^2) (w : H2) :
      (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [Complex.mul_im] at him
    have hb : b = 0 := by
      rcases him with hb | hw
      · exact hb
      · exact (w.im_pos.ne' hw).elim
    have ha : a ≠ 0 := by
      intro ha
      rw [ha,hb] at hab
      norm_num at hab
    exact ha (by simpa [hb] using h)
  have rotation_maps_vertical_radius (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r)
      (hab : 0 < (1-Real.exp r*z.im)^2+z.re^2) :
      (stabilizerRotation (1-Real.exp r*z.im) z.re hab • verticalPath r : H2) = z := by
    let a := 1-Real.exp r*z.im
    let b := z.re
    have hsphere := vertical_radius_sphere r hr z h
    have hEim : (Complex.exp (r : ℂ)).im = 0 := by
      simpa using Complex.exp_ofReal_im r
    have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := by
      simpa using Complex.exp_ofReal_re r
    apply UpperHalfPlane.coe_injective
    rw [stabilizerRotation_coe_smul]
    apply (div_eq_iff (denominator_nonzero a b hab (verticalPath r))).2
    apply Complex.ext
    · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
        Complex.mul_im,Complex.neg_im]
      try rw [hEim]
      dsimp [a,b]
      ring
    · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
        Complex.mul_re,Complex.neg_re]
      try rw [hEre]
      dsimp [a,b]
      nlinarith [hsphere]
  have exists_stabilizer_radius (r : ℝ) (hr : 0 ≤ r) (z : H2) (h : dist UpperHalfPlane.I z = r) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧ e (verticalPath r) = z := by
    let a : ℝ := 1-Real.exp r*z.im
    let b : ℝ := z.re
    by_cases hpole : a = 0 ∧ b = 0
    · have him : z.im = Real.exp (-r) := by
        have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
        have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole;linarith [hpole.1]
        rw [Real.exp_neg,←one_div]
        exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
      have hz : z = verticalPath (-r) := by
        apply UpperHalfPlane.ext_re_im
        · simpa [verticalPath,b] using hpole.2
        · simpa [verticalPath] using him
      refine ⟨IsometryEquiv.constSMul
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
      · rw [←zero_eq_I]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
        have hh := modular_S_verticalPath 0
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
        simpa only [neg_zero] using hh
      · rw [hz]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
        exact modular_S_verticalPath r
    · have hab : 0 < a^2+b^2 := by
        by_contra hn
        have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        exact hpole ⟨ha,hb⟩
      refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),?_,?_⟩
      · exact stabilizerRotation_fixes_I a b hab
      · exact rotation_maps_vertical_radius r hr z h hab
  have ordered_pair_alignment (x y : H2) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = x ∧ e (verticalPath (dist x y)) = y := by
    let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
    have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
    let w := e0.symm y
    have hw : dist UpperHalfPlane.I w = dist x y := by
      have hd := e0.isometry.dist_eq UpperHalfPlane.I (e0.symm y)
      rw [e0.apply_symm_apply,he0] at hd
      exact hd.symm
    obtain ⟨s,hs0,hsr⟩ := exists_stabilizer_radius (dist x y) dist_nonneg w hw
    refine ⟨s.trans e0,?_,?_⟩
    · rw [IsometryEquiv.trans_apply,hs0,he0]
    · rw [IsometryEquiv.trans_apply,hsr]
      exact e0.apply_symm_apply y
  have actual_segment (x y : H2) :
      ∃ γ : Path x y, ∀ s t : unitInterval,
        dist (γ s) (γ t) = dist x y * dist (s : ℝ) (t : ℝ) := by
    obtain ⟨e,he0,he1⟩ := ordered_pair_alignment x y
    let γ : Path x y := {
      toFun := fun t => e (verticalPath ((t : ℝ) * dist x y))
      continuous_toFun := e.continuous.comp
        (verticalPath_isometry.continuous.comp (continuous_subtype_val.mul continuous_const))
      source' := by
        change e (verticalPath (0 * dist x y)) = x
        simpa only [zero_mul,zero_eq_I] using he0
      target' := by
        change e (verticalPath (1 * dist x y)) = y
        simpa only [one_mul] using he1 }
    refine ⟨γ,?_⟩
    intro s t
    change dist (e (verticalPath ((s : ℝ)*dist x y)))
      (e (verticalPath ((t : ℝ)*dist x y))) = _
    rw [e.isometry.dist_eq,verticalPath_isometry.dist_eq,Real.dist_eq,Real.dist_eq,
      ←sub_mul,abs_mul,abs_of_nonneg (dist_nonneg (x := x) (y := y)),mul_comm]
  have locally_isometric_homeomorph_nonexpanding (F : H2 ≃ₜ H2)
      (hF : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, dist (F y) (F z) = dist y z)
      (x y : H2) : dist (F x) (F y) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    choose U hU hxU hmetric using hF
    let V : Interval → Set Interval := fun t => γ ⁻¹' U (γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) : dist (F (γ (t n))) (F (γ (t (n+1)))) =
        dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
      simp only [neg_sub]
    have hbound (n : ℕ) : dist (F (γ (t 0))) (F (γ (t n))) ≤
        dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (F (γ (t 0))) (F (γ (t n))) (F (γ (t (n+1))))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  have all_developed_decks_locally_isometric (k : deck (Sigma.fst : P → A)) (x : H2) :
      ∃ W : Set H2, IsOpen W ∧ x ∈ W ∧
        ∀ y ∈ W, ∀ z ∈ W,
          dist (developedDeck k y) (developedDeck k z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetricU⟩ := development_metric (development.symm x)
    obtain ⟨V,hV,hxV,hmetricV⟩ := development_metric (k • development.symm x)
    let W := development.symm ⁻¹' (U ∩ k.val ⁻¹' V)
    have hW : IsOpen W := (hU.inter (hV.preimage k.val.continuous)).preimage
      development.symm.continuous
    refine ⟨W,hW,⟨hxU,hxV⟩,?_⟩
    intro y hy z hz
    change dist (development (k • development.symm y))
      (development (k • development.symm z)) = dist y z
    rw [← hmetricV (k • development.symm y) hy.2
      (k • development.symm z) hz.2]
    have hyproj : (k • development.symm y).1.val = (development.symm y).1.val :=
      congrArg Subtype.val (hqc.map_smul k)
    have hzproj : (k • development.symm z).1.val = (development.symm z).1.val :=
      congrArg Subtype.val (hqc.map_smul k)
    rw [hyproj,hzproj,hmetricU _ hy.1 _ hz.1]
    rw [development.apply_symm_apply,development.apply_symm_apply]
  have all_developed_decks_isometric (k : deck (Sigma.fst : P → A)) :
      Isometry (developedDeck k) := by
    have hinverse (x : H2) : ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          dist ((developedDeck k).symm y) ((developedDeck k).symm z) = dist y z := by
      obtain ⟨U,hU,hxU,hmetric⟩ := all_developed_decks_locally_isometric k
        ((developedDeck k).symm x)
      refine ⟨(developedDeck k).symm ⁻¹' U,
        hU.preimage (developedDeck k).symm.continuous,hxU,?_⟩
      intro y hy z hz
      have h := hmetric _ hy _ hz
      simpa only [Homeomorph.apply_symm_apply] using h.symm
    apply Isometry.of_dist_eq
    intro x y
    apply le_antisymm
    · exact locally_isometric_homeomorph_nonexpanding (developedDeck k)
        (all_developed_decks_locally_isometric k) x y
    · have h := locally_isometric_homeomorph_nonexpanding (developedDeck k).symm hinverse
        (developedDeck k x) (developedDeck k y)
      simpa only [Homeomorph.symm_apply_apply] using h
  let developedDeckIsometry : deck (Sigma.fst : P → A) → H2 ≃ᵢ H2 :=
    fun k => { (developedDeck k).toEquiv with isometry_toFun := all_developed_decks_isometric k }
  let sourceComponentMetric : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have sourceComponentMetric_topology :
      sourceComponentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := sourceComponentMetric.replaceTopology sourceComponentMetric_topology.symm
  have fiber_nonempty (a : A) : Nonempty ((Sigma.fst : P → A) ⁻¹' {a}) := by
    obtain ⟨z,hz⟩ := hsurj a
    exact ⟨⟨z,hz⟩⟩
  letI (a : A) : Nonempty ((Sigma.fst : P → A) ⁻¹' {a}) := fiber_nonempty a
  have actualCoveringMap : IsCoveringMap (Sigma.fst : P → A) := hqc.isCoveringMap
  let actualTrivialization (a : A) := (actualCoveringMap a).toTrivialization
  have actualTrivialization_base (a : A) : a ∈ (actualTrivialization a).baseSet :=
    (actualCoveringMap a).mem_toTrivialization_baseSet
  have uniform_evenly_covered_radius : ∃ ε : ℝ, 0 < ε ∧ ∀ x : A,
      ∃ a : A, Metric.ball x ε ⊆ (actualTrivialization a).baseSet := by
    obtain ⟨ε,hε,hcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
      (fun a => (actualTrivialization a).open_baseSet)
      (show Set.univ ⊆ ⋃ a, (actualTrivialization a).baseSet from
        fun x _ => Set.mem_iUnion.mpr ⟨x,actualTrivialization_base x⟩)
    exact ⟨ε,hε,fun x => hcover x (Set.mem_univ x)⟩
  let componentProjection : H2 → A := fun z => (development.symm z).1
  have componentProjection_continuous : Continuous componentProjection :=
    actualCoveringMap.continuous.comp development.symm.continuous
  have componentProjection_locally_isometric (x : H2) :
      ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          dist (componentProjection y) (componentProjection z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetric⟩ := development_metric (development.symm x)
    refine ⟨development.symm ⁻¹' U,hU.preimage development.symm.continuous,hxU,?_⟩
    intro y hy z hz
    change @dist E H.metric.toDist (development.symm y).1.val
      (development.symm z).1.val = dist y z
    rw [hmetric _ hy _ hz,development.apply_symm_apply,development.apply_symm_apply]
  have componentProjection_nonexpanding (x y : H2) :
      dist (componentProjection x) (componentProjection y) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    choose U hU hxU hmetric using componentProjection_locally_isometric
    let V : Interval → Set Interval := fun t => γ ⁻¹' U (γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) :
        dist (componentProjection (γ (t n))) (componentProjection (γ (t (n+1)))) =
          dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
      simp only [neg_sub]
    have hbound (n : ℕ) :
        dist (componentProjection (γ (t 0))) (componentProjection (γ (t n))) ≤
          dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (componentProjection (γ (t 0)))
          (componentProjection (γ (t n))) (componentProjection (γ (t (n+1))))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  have developed_monodromy_no_fixed_point (z : H2) :
      developedDeck monodromy z ≠ z := by
    intro hz
    apply monodromy_no_fixed_point (development.symm z)
    apply development.injective
    change development (monodromy • development.symm z) = development (development.symm z)
    simpa only [developedDeck,Homeomorph.trans_apply,Homeomorph.symm_apply_apply,
      development.apply_symm_apply,Subgroup.smul_def,Homeomorph.smul_def] using hz
  obtain ⟨coverRadius,coverRadius_pos,coverRadius_control⟩ := uniform_evenly_covered_radius
  have actual_positive_uniform_deck_displacement (z : H2) :
      coverRadius ≤ dist z ((developedDeck monodromy) z) := by
    by_contra hle
    have hshort : dist z ((developedDeck monodromy) z) < coverRadius := lt_of_not_ge hle
    obtain ⟨a,ha⟩ := coverRadius_control (componentProjection z)
    obtain ⟨γ,hγ⟩ := actual_segment z ((developedDeck monodromy) z)
    let Γ : C(Interval,P) := ⟨development.symm ∘ γ,
      development.symm.continuous.comp γ.continuous⟩
    let T := actualTrivialization a
    letI : DiscreteTopology ((Sigma.fst : P → A) ⁻¹' {a}) :=
      (actualCoveringMap a).discreteTopology_fiber
    have hsource (t : Interval) : Γ t ∈ T.source := by
      apply T.mem_source.mpr
      apply ha
      change dist (componentProjection (γ t)) (componentProjection z) < coverRadius
      have hπ := componentProjection_nonexpanding (γ t) z
      have hseg : dist (γ t) z = dist z ((developedDeck monodromy) z) * (t : ℝ) := by
        have h := hγ 0 t
        simpa [Real.dist_eq,abs_of_nonneg t.property.1,dist_comm] using h
      have hbound := mul_le_of_le_one_right
        (dist_nonneg (x := z) (y := (developedDeck monodromy) z)) t.property.2
      rw [hseg] at hπ
      exact lt_of_le_of_lt (hπ.trans hbound) hshort
    let label : Interval → ((Sigma.fst : P → A) ⁻¹' {a}) := fun t => (T (Γ t)).2
    have hlabel : Continuous label := continuous_snd.comp
      (T.toOpenPartialHomeomorph.continuousOn.comp_continuous Γ.continuous hsource)
    have hlabels : label 0 = label 1 :=
      (isPreconnected_range hlabel).subsingleton (mem_range_self 0) (mem_range_self 1)
    have hprojection : (Γ 0).1 = (Γ 1).1 := by
      change (development.symm (γ 0)).1 = (development.symm (γ 1)).1
      rw [γ.source,γ.target]
      change (development.symm z).1 =
        (development.symm (development (monodromy • development.symm z))).1
      rw [development.symm_apply_apply]
      exact (hqc.map_smul monodromy).symm
    have hcoords : T (Γ 0) = T (Γ 1) := by
      apply Prod.ext
      · change (T.toOpenPartialHomeomorph (Γ 0)).1 =
          (T.toOpenPartialHomeomorph (Γ 1)).1
        rw [T.proj_toFun _ (hsource 0),T.proj_toFun _ (hsource 1)]
        exact hprojection
      · exact hlabels
    have hend : Γ 0 = Γ 1 := T.injOn (hsource 0) (hsource 1) hcoords
    apply developed_monodromy_no_fixed_point z
    have h := congrArg development hend
    change development (development.symm (γ 0)) = development (development.symm (γ 1)) at h
    simpa only [development.apply_symm_apply,γ.source,γ.target] using h.symm
  obtain ⟨actualAxis,hactualAxis,axisPeriod,haxisPeriod,haxisTranslate⟩ :=
    actual_hyperbolic_isometry_axis_of_uniform_displacement
      (developedDeckIsometry monodromy) coverRadius coverRadius_pos
      actual_positive_uniform_deck_displacement
  have actual_compact_closed_shortest_connector
      {P : Type} [MetricSpace P] [ProperSpace P] (K L : Set P)
      (hK : IsCompact K) (hneK : K.Nonempty)
      (hL : IsClosed L) (hneL : L.Nonempty) (hdis : Disjoint K L) :
      ∃ x ∈ K, ∃ y ∈ L, 0 < dist x y ∧
        ∀ u ∈ K, ∀ v ∈ L, dist x y ≤ dist u v := by
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hneK
      (Metric.continuous_infDist_pt L).continuousOn
    obtain ⟨y, hy, heq⟩ := hL.exists_infDist_eq_dist hneL x
    refine ⟨x, hx, y, hy, dist_pos.mpr ?_, ?_⟩
    · intro hxy
      exact Set.disjoint_left.mp hdis hx (hxy ▸ hy)
    · intro u hu v hv
      rw [← heq]
      exact (hmin hu).trans (Metric.infDist_le_dist_of_mem hv)
  have actual_shortest_connector_interior_avoids_boundaries
      {P : Type} [MetricSpace P] (K L : Set P) (x y z : P)
      (hmin : ∀ u ∈ K, ∀ v ∈ L, dist x y ≤ dist u v)
      (hx : x ∈ K) (hy : y ∈ L)
      (hadd : dist x z + dist z y = dist x y)
      (hxz : x ≠ z) (hzy : z ≠ y) : z ∉ K ∧ z ∉ L := by
    constructor
    · intro hz
      have hle := hmin z hz y hy
      have hp := dist_pos.mpr hxz
      linarith
    · intro hz
      have hle := hmin x hx z hz
      have hp := dist_pos.mpr hzy
      linarith
  have actual_periodic_closed_line_shortest_connector
      {P : Type} [MetricSpace P] [ProperSpace P]
      (F J : C(ℝ,P)) (g : P ≃ᵢ P) (T : ℝ) (hT : 0 < T)
      (hF : ∀ s, F (s + T) = g (F s))
      (hJ : ∀ s, J (s + T) = g (J s))
      (hclosed : IsClosed (Set.range J))
      (hdis : Disjoint (Set.range F) (Set.range J)) :
      ∃ x ∈ Set.range F, ∃ y ∈ Set.range J, 0 < dist x y ∧
        ∀ u ∈ Set.range F, ∀ v ∈ Set.range J, dist x y ≤ dist u v := by
    have hinv : g '' Set.range J = Set.range J := by
      ext y
      constructor
      · rintro ⟨_, ⟨s,rfl⟩,rfl⟩
        exact ⟨s + T, hJ s⟩
      · rintro ⟨s,rfl⟩
        refine ⟨J (s-T), Set.mem_range_self _, ?_⟩
        rw [← hJ]
        congr 1
        ring
    let δ : ℝ → ℝ := fun s => Metric.infDist (F s) (Set.range J)
    have hc : Continuous δ := (Metric.continuous_infDist_pt _).comp F.continuous
    have hp : Function.Periodic δ T := by
      intro s
      dsimp [δ]
      rw [hF]
      calc
        Metric.infDist (g (F s)) (Set.range J) = Metric.infDist (g (F s)) (g '' Set.range J) := by rw [hinv]
        _ = Metric.infDist (F s) (Set.range J) := Metric.infDist_image g.isometry
    have hk : IsCompact (Set.range δ) := by
      rw [← hp.image_Icc hT 0]
      exact isCompact_Icc.image hc
    obtain ⟨d, ⟨s,rfl⟩, hleast⟩ := hk.exists_isLeast ⟨δ 0, Set.mem_range_self 0⟩
    obtain ⟨y, hy, heq⟩ := hclosed.exists_infDist_eq_dist
      ⟨J 0,Set.mem_range_self 0⟩ (F s)
    refine ⟨F s, Set.mem_range_self s, y, hy, dist_pos.mpr ?_, ?_⟩
    · intro he
      exact Set.disjoint_left.mp hdis (Set.mem_range_self s) (he ▸ hy)
    · rintro u ⟨r,rfl⟩ v hv
      rw [← heq]
      exact (hleast (Set.mem_range_self r)).trans (Metric.infDist_le_dist_of_mem hv)
  have developedProjection_continuous : Continuous developedProjection :=
    continuous_subtype_val.comp (hqc.isCoveringMap.continuous.comp development.symm.continuous)
  let sourcePreimage : Set H2 := developedProjection ⁻¹' a.image
  let targetPreimage : Set H2 := developedProjection ⁻¹' b.image
  have sourcePreimage_disjoint_target : Disjoint sourcePreimage targetPreimage :=
    hdis.preimage developedProjection
  have targetPreimage_closed : IsClosed targetPreimage :=
    (isCompact_range b.embedded.continuous).isClosed.preimage developedProjection_continuous
  have targetPreimage_nonempty : targetPreimage.Nonempty :=
    ⟨targetLift 0,by change developedProjection (targetLift 0) ∈ b.image
                     rw [targetLift_projection]; exact Set.mem_range_self _⟩
  have actual_sourcePreimage_deck_family (z : H2) (hz : z ∈ sourcePreimage) :
      ∃ k : deck (Sigma.fst : P → A), ∃ s : ℝ,
        developedDeck k (sourceLift s) = z := by
    obtain ⟨w,hw⟩ := hz
    obtain ⟨s,hs⟩ := Circle.exp_surjective w
    have he : (development.symm z).1 = (L (s,0)).1 := by
      apply Subtype.ext
      change developedProjection z = (L (s,0)).1.val
      rw [hL0,hs]
      exact hw.symm
    obtain ⟨k,hk⟩ := hqc.apply_eq_iff_mem_orbit.mp he
    change k • L (s,0) = development.symm z at hk
    refine ⟨k,s,?_⟩
    change development (k • development.symm (development (L (s,0)))) = z
    rw [development.symm_apply_apply,hk,development.apply_symm_apply]
  have actual_global_developed_shortest_connector :
      ∃ x ∈ sourcePreimage, ∃ y ∈ targetPreimage, 0 < dist x y ∧
        ∀ u ∈ sourcePreimage, ∀ v ∈ targetPreimage, dist x y ≤ dist u v := by
    let K : Set H2 := sourceLift '' Set.Icc 0 (2*Real.pi)
    have hK : IsCompact K := isCompact_Icc.image sourceLift.continuous
    have hKne : K.Nonempty := ⟨sourceLift 0,0,⟨le_rfl,by positivity⟩,rfl⟩
    have hKsource : K ⊆ sourcePreimage := by
      rintro _ ⟨s,hs,rfl⟩
      change developedProjection (sourceLift s) ∈ a.image
      rw [sourceLift_projection]
      exact Set.mem_range_self _
    obtain ⟨x,hx,y,hy,hpos,hmin⟩ := actual_compact_closed_shortest_connector K targetPreimage
      hK hKne targetPreimage_closed targetPreimage_nonempty
      (sourcePreimage_disjoint_target.mono_left hKsource)
    let δ : ℝ → ℝ := fun s => Metric.infDist (sourceLift s) targetPreimage
    have hinv : developedDeck monodromy '' targetPreimage = targetPreimage := by
      ext z
      constructor
      · rintro ⟨v,hv,rfl⟩
        change developedProjection (developedDeck monodromy v) ∈ b.image
        rw [developedDeck_projection]
        exact hv
      · intro hz
        refine ⟨(developedDeck monodromy).symm z,?_,Homeomorph.apply_symm_apply _ _⟩
        change developedProjection ((developedDeck monodromy).symm z) ∈ b.image
        have he := developedDeck_projection monodromy ((developedDeck monodromy).symm z)
        rw [Homeomorph.apply_symm_apply] at he
        rwa [← he]
    have hp : Function.Periodic δ (2*Real.pi) := by
      intro s
      dsimp [δ]
      rw [sourceLift_period]
      calc
        Metric.infDist (developedDeck monodromy (sourceLift s)) targetPreimage =
            Metric.infDist (developedDeck monodromy (sourceLift s))
              (developedDeck monodromy '' targetPreimage) := by rw [hinv]
        _ = Metric.infDist (sourceLift s) targetPreimage :=
          Metric.infDist_image (all_developed_decks_isometric monodromy)
    have hbase (s : ℝ) (v : H2) (hv : v ∈ targetPreimage) :
        dist x y ≤ dist (sourceLift s) v := by
      have heq : δ '' Set.Icc 0 (2*Real.pi) = Set.range δ := by
        simpa only [zero_add] using hp.image_Icc (by positivity : 0 < 2*Real.pi) 0
      have hs : δ s ∈ δ '' Set.Icc 0 (2*Real.pi) := by
        rw [heq]
        exact Set.mem_range_self s
      obtain ⟨r,hr,he⟩ := hs
      obtain ⟨q,hq,hinf⟩ := targetPreimage_closed.exists_infDist_eq_dist
        targetPreimage_nonempty (sourceLift r)
      have hl := hmin (sourceLift r) ⟨r,hr,rfl⟩ q hq
      have hd : dist x y ≤ δ r := by simpa only [δ,hinf] using hl
      rw [he] at hd
      exact hd.trans (Metric.infDist_le_dist_of_mem hv)
    refine ⟨x,hKsource hx,y,hy,hpos,?_⟩
    intro u hu v hv
    obtain ⟨k,s,rfl⟩ := actual_sourcePreimage_deck_family u hu
    have hvinv : (developedDeck k).symm v ∈ targetPreimage := by
      change developedProjection ((developedDeck k).symm v) ∈ b.image
      have he := developedDeck_projection k ((developedDeck k).symm v)
      rw [Homeomorph.apply_symm_apply] at he
      rwa [← he]
    have hh := hbase s ((developedDeck k).symm v) hvinv
    calc
      dist x y ≤ dist (sourceLift s) ((developedDeck k).symm v) := hh
      _ = dist (developedDeck k (sourceLift s)) v := by
        have hd := (all_developed_decks_isometric k).dist_eq (sourceLift s)
          ((developedDeck k).symm v)
        rw [Homeomorph.apply_symm_apply] at hd
        exact hd.symm
  have actual_axis_orbit_escape
      {X : Type} [MetricSpace X] (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ)
      (hτ : 0 < τ) (htranslate : ∀ t, g (axis t) = axis (t + τ)) :
      (∀ n : ℕ, ∀ t : ℝ, g^[n] (axis t) = axis (t + n * τ)) ∧
      (∀ x : X, ∀ n : ℕ,
        n * τ ≤ dist x (g^[n] x) + 2 * dist x (axis 0)) ∧
      (∀ x : X, ∀ m : ℕ, 0 < m → g^[m] x ≠ x) := by
    have hiter (n : ℕ) (t : ℝ) : g^[n] (axis t) = axis (t + n * τ) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, htranslate]
        congr 1
        push_cast
        ring
    have hidist (n : ℕ) (x y : X) : dist (g^[n] x) (g^[n] y) = dist x y := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply', hg.dist_eq] using ih
    have hbound (x : X) (n : ℕ) :
        n * τ ≤ dist x (g^[n] x) + 2 * dist x (axis 0) := by
      have hn : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
      have haxisdist : dist (axis 0) (g^[n] (axis 0)) = n * τ := by
        rw [hiter, zero_add, haxis.dist_eq, Real.dist_eq, zero_sub, abs_neg,
          abs_of_nonneg hn]
      have htriangle := dist_triangle (axis 0) x (g^[n] (axis 0))
      have htriangle' := dist_triangle x (g^[n] x) (g^[n] (axis 0))
      rw [hidist] at htriangle'
      rw [haxisdist, dist_comm (axis 0) x] at htriangle
      linarith
    refine ⟨hiter, hbound, ?_⟩
    intro x m hm hfix
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * dist x (axis 0) / ((m : ℝ) * τ))
    have hlarge := (div_lt_iff₀ (mul_pos hmreal hτ)).mp hk
    have hfix' : g^[m * k] x = x := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hfix k
    have hsmall := hbound x (m * k)
    rw [hfix', dist_self, zero_add, Nat.cast_mul] at hsmall
    nlinarith
  have actual_axis_periodic_curve_lift_injective
      {X : Type} [MetricSpace X] (p : X → E) (c : Curve E)
      (F : ℝ → X) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
      (htranslate : ∀ t, g (axis t) = axis (t + τ))
      (hproj : ∀ s, p (F s) = c.map (Circle.exp s))
      (hperiod : ∀ s, F (s + 2 * Real.pi) = g (F s)) :
      Function.Injective F := by
    have hno := (actual_axis_orbit_escape g hg axis haxis τ hτ htranslate).2.2
    have hiter (n : ℕ) (s : ℝ) : F (s + n * (2 * Real.pi)) = g^[n] (F s) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have he : s + (n + 1 : ℕ) * (2 * Real.pi) =
            (s + n * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
        rw [he, hperiod, ih, Function.iterate_succ_apply']
    intro s t hst
    have he : Circle.exp s = Circle.exp t := by
      apply c.embedded.injective
      rw [← hproj, ← hproj, hst]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
    cases k with
    | ofNat n =>
      change s = t + (n : ℝ) * (2 * Real.pi) at hk
      by_cases hn : n = 0
      · simpa [hn] using hk
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hfix : g^[n] (F t) = F t := by
          rw [← hiter, ← hk]
          exact hst
        exact False.elim (hno (F t) n hnpos hfix)
    | negSucc n =>
      have ht : t = s + (n + 1 : ℕ) * (2 * Real.pi) := by
        simp only [Int.cast_negSucc] at hk
        push_cast at hk
        push_cast
        linarith
      have hfix : g^[n + 1] (F s) = F s := by
        rw [← hiter, ← ht]
        exact hst.symm
      exact False.elim (hno (F s) (n + 1) (Nat.succ_pos _) hfix)
  have actual_axis_periodic_line_proper
      {X : Type} [MetricSpace X] (F : C(ℝ,X)) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ T : ℝ) (hτ : 0 < τ) (hT : 0 < T)
      (htranslate : ∀ t, g (axis t) = axis (t + τ))
      (hperiod : ∀ s, F (s + T) = g (F s)) :
      IsProperMap F := by
    let δ : ℝ → ℝ := fun s => dist (F s) (axis (s * (τ / T)))
    have hδcont : Continuous δ := F.continuous.dist (haxis.continuous.comp
      (continuous_id.mul continuous_const))
    have hδperiod : Function.Periodic δ T := by
      intro s
      dsimp [δ]
      have he : (s + T) * (τ / T) = s * (τ / T) + τ := by
        field_simp
      rw [hperiod, he, ← htranslate, hg.dist_eq]
    have hcompact : IsCompact (Set.range δ) := by
      rw [← hδperiod.image_Icc hT 0]
      exact isCompact_Icc.image hδcont
    obtain ⟨M,hM⟩ := hcompact.bddAbove
    have hbound (s : ℝ) : δ s ≤ M := hM ⟨s,rfl⟩
    have hlower (s : ℝ) : |s| * (τ / T) - M ≤ dist (F s) (axis 0) := by
      have htri := dist_triangle (axis (s * (τ / T))) (F s) (axis 0)
      rw [haxis.dist_eq, Real.dist_eq, sub_zero, abs_mul,
        abs_of_pos (div_pos hτ hT), dist_comm (axis (s * (τ / T))) (F s)] at htri
      have hb := hbound s
      dsimp [δ] at hb
      linarith
    have habs : Filter.Tendsto (fun s : ℝ => |s|) (Filter.cocompact ℝ) Filter.atTop := by
      convert tendsto_dist_right_cocompact_atTop (0 : ℝ) using 1
      ext s
      simp [Real.dist_eq]
    have hdist : Filter.Tendsto (fun s : ℝ => dist (F s) (axis 0))
        (Filter.cocompact ℝ) Filter.atTop := by
      apply Filter.tendsto_atTop.mpr
      intro R
      filter_upwards [(Filter.tendsto_atTop.mp habs) ((R + M) / (τ / T))] with s hs
      have hh := (div_le_iff₀ (div_pos hτ hT)).mp hs
      have hl := hlower s
      linarith
    exact isProperMap_iff_tendsto_cocompact.mpr
      ⟨F.continuous,tendsto_cocompact_of_tendsto_dist_comp_atTop (axis 0) hdist⟩
  have actual_axis_periodic_curve_lift_closed_embedding
      {X : Type} [MetricSpace X] (p : X → E) (c : Curve E)
      (F : C(ℝ,X)) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
      (htranslate : ∀ t, g (axis t) = axis (t + τ))
      (hproj : ∀ s, p (F s) = c.map (Circle.exp s))
      (hperiod : ∀ s, F (s + 2 * Real.pi) = g (F s)) :
      Topology.IsClosedEmbedding F := by
    have hproper := actual_axis_periodic_line_proper F g hg axis haxis
      τ (2 * Real.pi) hτ (by positivity) htranslate hperiod
    have hinj := actual_axis_periodic_curve_lift_injective p c F g hg axis haxis
      τ hτ htranslate hproj hperiod
    exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      F.continuous hinj hproper.isClosedMap
  have actual_sourceLift_closed_embedding : Topology.IsClosedEmbedding sourceLift :=
    actual_axis_periodic_curve_lift_closed_embedding developedProjection a sourceLift
      (developedDeckIsometry monodromy) (developedDeckIsometry monodromy).isometry
      actualAxis hactualAxis axisPeriod haxisPeriod haxisTranslate
      sourceLift_projection sourceLift_period
  have actual_targetLift_closed_embedding : Topology.IsClosedEmbedding targetLift :=
    actual_axis_periodic_curve_lift_closed_embedding developedProjection b targetLift
      (developedDeckIsometry monodromy) (developedDeckIsometry monodromy).isometry
      actualAxis hactualAxis axisPeriod haxisPeriod haxisTranslate
      targetLift_projection targetLift_period
  have actual_hyperbolic_shortest_seam
      (K L : Set H2) (x y : H2) (hx : x ∈ K) (hy : y ∈ L)
      (hxy : x ≠ y)
      (hmin : ∀ u ∈ K, ∀ v ∈ L, dist x y ≤ dist u v) :
      ∃ f : ℝ → H2, Continuous f ∧ Set.InjOn f (Icc 0 1) ∧
        f 0 = x ∧ f 1 = y ∧ ∀ t ∈ Ioo 0 1, f t ∉ K ∧ f t ∉ L := by
    obtain ⟨f,hc,hi,h0,h1,hr⟩ := metric_segment_has_parametrization x y hxy
    refine ⟨f,hc,hi,h0,h1,?_⟩
    intro t ht
    have hti : t ∈ Icc 0 1 := ⟨ht.1.le,ht.2.le⟩
    have hadd : dist x (f t) + dist (f t) y = dist x y := by
      have hm : f t ∈ f '' Icc 0 1 := ⟨t,hti,rfl⟩
      rw [hr] at hm
      exact hm
    have hxt : x ≠ f t := by
      intro he
      have he' : f 0 = f t := h0.trans he
      have := hi (by simp) hti he'
      linarith [ht.1]
    have hty : f t ≠ y := by
      intro he
      have he' : f t = f 1 := he.trans h1.symm
      have := hi hti (by simp) he'
      linarith [ht.2]
    constructor
    · intro hz
      have hle := hmin (f t) hz y hy
      have hp := dist_pos.mpr hxt
      linarith
    · intro hz
      have hle := hmin x hx (f t) hz
      have hp := dist_pos.mpr hty
      linarith
  obtain ⟨seamSource,hseamSource,seamTarget,hseamTarget,hseamDistance,hseamMinimum⟩ :=
    actual_global_developed_shortest_connector
  have hseamEndpoints : seamSource ≠ seamTarget := dist_pos.mp hseamDistance
  obtain ⟨seam,hseamContinuous,hseamInjective,hseam0,hseam1,hseamRange⟩ :=
    metric_segment_has_parametrization seamSource seamTarget hseamEndpoints
  have hseamAdd (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      dist seamSource (seam t) + dist (seam t) seamTarget = dist seamSource seamTarget := by
    have hh : seam t ∈ seam '' Set.Icc 0 1 := ⟨t,ht,rfl⟩
    rwa [hseamRange] at hh
  have hseamAvoid (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      seam t ∉ sourcePreimage ∧ seam t ∉ targetPreimage := by
    have hti : t ∈ Set.Icc 0 1 := ⟨ht.1.le,ht.2.le⟩
    apply actual_shortest_connector_interior_avoids_boundaries sourcePreimage targetPreimage
      seamSource seamTarget (seam t) hseamMinimum hseamSource hseamTarget (hseamAdd t hti)
    · intro he
      have hh := hseamInjective (by simp) hti (hseam0.trans he)
      linarith [ht.1]
    · intro he
      have hh := hseamInjective hti (by simp) (he.trans hseam1.symm)
      linarith [ht.2]
  have actual_all_deck_seam_interiors_avoid_curves
      (k : deck (Sigma.fst : P → A)) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      developedDeck k (seam t) ∉ sourcePreimage ∧
      developedDeck k (seam t) ∉ targetPreimage := by
    constructor
    · intro hz
      apply (hseamAvoid t ht).1
      change developedProjection (seam t) ∈ a.image
      change developedProjection (developedDeck k (seam t)) ∈ a.image at hz
      rwa [developedDeck_projection] at hz
    · intro hz
      apply (hseamAvoid t ht).2
      change developedProjection (seam t) ∈ b.image
      change developedProjection (developedDeck k (seam t)) ∈ b.image at hz
      rwa [developedDeck_projection] at hz
  have actual_h2_geodesic_continuation_unique (a z b c : H2)
      (haz : a ≠ z)
      (hb : dist a z + dist z b = dist a b)
      (hc : dist a z + dist z c = dist a c)
      (hd : dist a b = dist a c) : b = c := by
    obtain ⟨e,ha,hz⟩ := exists_pair_vertical_isometry a z
    have haz' : e a ≠ e z := fun h => haz (e.injective h)
    have hsq : (e z).im ^ 2 ≠ (e a).im ^ 2 := by
      intro h
      have him : (e a).im = (e z).im := by
        nlinarith [(e a).im_pos,(e z).im_pos]
      exact haz' (UpperHalfPlane.ext_re_im (ha.trans hz.symm) him)
    have hre (w : H2) (hw : dist a z + dist z w = dist a w) : (e w).re = 0 := by
      have hw' : dist (e a) (e z) + dist (e z) (e w) = dist (e a) (e w) := by
        simpa only [e.isometry.dist_eq] using hw
      have heq := metric_segment_circle_equation hw'
      simp only [ha,hz,sub_zero,zero_sub,mul_zero,zero_mul] at heq
      have hn : Complex.normSq (e z : ℂ) - Complex.normSq (e a : ℂ) ≠ 0 := by
        simpa only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,ha,hz,zero_mul,zero_add,pow_two,
          sub_ne_zero] using hsq
      exact (mul_eq_zero.mp heq).resolve_right hn
    have hb0 := hre b hb
    have hc0 := hre c hc
    have hdb : dist (e b) (e a) = dist (e c) (e a) := by
      simpa only [e.isometry.dist_eq,dist_comm] using hd
    have hdz : dist (e b) (e z) = dist (e c) (e z) := by
      simp only [e.isometry.dist_eq]
      rw [dist_comm b z,dist_comm c z]
      linarith
    have h0 := axis_equal_distance_cross (e b) (e c) (e a) hdb
    have h1 := axis_equal_distance_cross (e b) (e c) (e z) hdz
    simp only [ha,hz,hb0,hc0,sub_zero,zero_sub,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      zero_add] at h0 h1
    have hp : ((e z).im^2-(e a).im^2) * ((e c).im-(e b).im) = 0 := by
      nlinarith only [h0,h1]
    have him : (e b).im = (e c).im := by
      have hh := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hsq)
      linarith
    exact e.injective (UpperHalfPlane.ext_re_im (hb0.trans hc0.symm) him)
  have all_developed_decks_fixed_implies_one
      (k : deck (Sigma.fst : P → A)) (z : H2) (hz : developedDeck k z = z) : k = 1 := by
    letI : IsCancelSMul (deck (Sigma.fst : P → A)) P := hqc.isCancelSMul
    apply IsCancelSMul.right_cancel _ _ (development.symm z)
    have he := congrArg development.symm hz
    change development.symm (development (k • development.symm z)) = development.symm z at he
    simpa only [development.symm_apply_apply,one_smul] using he
  have actual_shortest_seam_disjoint_nontrivial_deck_translates
      (k : deck (Sigma.fst : P → A)) (hk : k ≠ 1) :
      Disjoint (seam '' Set.Icc 0 1)
        (developedDeck k '' (seam '' Set.Icc 0 1)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t,ht,htz⟩ ⟨_,⟨r,hr,rfl⟩,hrz⟩
    have hxk : developedDeck k seamSource ∈ sourcePreimage := by
      change developedProjection (developedDeck k seamSource) ∈ a.image
      rwa [developedDeck_projection]
    have hyk : developedDeck k seamTarget ∈ targetPreimage := by
      change developedProjection (developedDeck k seamTarget) ∈ b.image
      rwa [developedDeck_projection]
    have hadd1 : dist seamSource z + dist z seamTarget = dist seamSource seamTarget := by
      rw [← htz]
      exact hseamAdd t ht
    have hadd2 : dist (developedDeck k seamSource) z +
        dist z (developedDeck k seamTarget) = dist seamSource seamTarget := by
      rw [← hrz]
      rw [(all_developed_decks_isometric k).dist_eq,
        (all_developed_decks_isometric k).dist_eq]
      exact hseamAdd r hr
    have hcross1 := hseamMinimum seamSource hseamSource (developedDeck k seamTarget) hyk
    have hcross2 := hseamMinimum (developedDeck k seamSource) hxk seamTarget hseamTarget
    have htri1 := dist_triangle seamSource z (developedDeck k seamTarget)
    have htri2 := dist_triangle (developedDeck k seamSource) z seamTarget
    have hleft : dist seamSource z = dist (developedDeck k seamSource) z := by
      linarith
    have hright : dist z seamTarget = dist z (developedDeck k seamTarget) := by
      linarith
    have hcrossdist : dist seamSource (developedDeck k seamTarget) =
        dist seamSource seamTarget := by linarith
    by_cases hxz : seamSource = z
    · have he : developedDeck k seamSource = z := by
        apply dist_eq_zero.mp
        rw [← hleft,← hxz]
        exact dist_self _
      exact hk (all_developed_decks_fixed_implies_one k seamSource (he.trans hxz.symm))
    · have hcrossadd : dist seamSource z + dist z (developedDeck k seamTarget) =
          dist seamSource (developedDeck k seamTarget) := by linarith
      have he := actual_h2_geodesic_continuation_unique seamSource z seamTarget
        (developedDeck k seamTarget) hxz hadd1 hcrossadd hcrossdist.symm
      exact hk (all_developed_decks_fixed_implies_one k seamTarget he.symm)
  have actual_projected_shortest_seam_injective :
      Set.InjOn (developedProjection ∘ seam) (Set.Icc 0 1) := by
    intro s hs t ht he
    have he' : (development.symm (seam s)).1 = (development.symm (seam t)).1 :=
      Subtype.ext he
    obtain ⟨k,hk⟩ := hqc.apply_eq_iff_mem_orbit.mp he'
    change k • development.symm (seam t) = development.symm (seam s) at hk
    have hk' : developedDeck k (seam t) = seam s := by
      change development (k • development.symm (seam t)) = seam s
      rw [hk,development.apply_symm_apply]
    have hk1 : k = 1 := by
      by_contra hkn
      exact Set.disjoint_left.mp (actual_shortest_seam_disjoint_nontrivial_deck_translates k hkn)
        ⟨s,hs,rfl⟩ ⟨seam t,⟨t,ht,rfl⟩,hk'⟩
    have heq : seam t = seam s := by
      have h := congrArg development hk
      simpa only [hk1,one_smul,development.apply_symm_apply] using h
    exact (hseamInjective ht hs heq).symm
  have actual_projected_shortest_seam_closed_embedding :
      Topology.IsClosedEmbedding
        (fun t : Interval => developedProjection (seam t.val)) := by
    apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    · exact developedProjection_continuous.comp (hseamContinuous.comp continuous_subtype_val)
    · intro s t he
      apply Subtype.ext
      exact actual_projected_shortest_seam_injective s.property t.property he
    · exact (developedProjection_continuous.comp
        (hseamContinuous.comp continuous_subtype_val)).isClosedMap
  have actual_projected_shortest_seam_source : developedProjection (seam 0) ∈ a.image := by
    rw [hseam0]
    exact hseamSource
  have actual_projected_shortest_seam_target : developedProjection (seam 1) ∈ b.image := by
    rw [hseam1]
    exact hseamTarget
  have actual_projected_shortest_seam_interior
      (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      developedProjection (seam t) ∉ a.image ∪ b.image := by
    rintro (ha | hb)
    · exact (hseamAvoid t ht).1 ha
    · exact (hseamAvoid t ht).2 hb
  have actual_invariant_facing_side
      {P : Type} [TopologicalSpace P] (g : P ≃ₜ P)
      (F J U V : Set P) (hU : IsOpen U) (hV : IsOpen V)
      (hconnU : IsPreconnected U) (hdis : Disjoint U V)
      (hpartition : U ∪ V = Fᶜ) (hJ : J.Nonempty) (hJU : J ⊆ U)
      (hgF : g '' F = F) (hgJ : g '' J = J) :
      g '' U = U ∧ g '' V = V := by
    have forward (e : P ≃ₜ P) (heF : e '' F = F) (heJ : e '' J = J) : e '' U ⊆ U := by
      have hc : IsPreconnected (e '' U) := hconnU.image e e.continuous.continuousOn
      have havoid : e '' U ⊆ U ∪ V := by
        rintro _ ⟨x,hx,rfl⟩
        rw [hpartition]
        intro he
        rw [← heF] at he
        obtain ⟨y,hy,he⟩ := he
        have hxy : y = x := e.injective he
        have hxF : x ∈ F := hxy ▸ hy
        have hxnot : x ∉ F := by
          have hh : x ∈ U ∪ V := Or.inl hx
          rwa [hpartition] at hh
        exact hxnot hxF
      rcases hc.subset_or_subset hU hV hdis havoid with h | h
      · exact h
      · obtain ⟨j,hj⟩ := hJ
        have hgj : e j ∈ J := heJ ▸ Set.mem_image_of_mem e hj
        exact False.elim (Set.disjoint_left.mp hdis (hJU hgj)
          (h (Set.mem_image_of_mem e (hJU hj))))
    have inverseImageEq (S : Set P) (hS : g '' S = S) : g.symm '' S = S := by
      have hh := congrArg (fun T : Set P => g.symm '' T) hS
      simpa only [Set.image_image,Homeomorph.symm_apply_apply,Set.image_id'] using hh.symm
    have hforward := forward g hgF hgJ
    have hinverse := forward g.symm (inverseImageEq F hgF) (inverseImageEq J hgJ)
    have hUeq : g '' U = U := by
      apply Set.Subset.antisymm hforward
      intro u hu
      exact ⟨g.symm u,hinverse (Set.mem_image_of_mem _ hu),g.apply_symm_apply u⟩
    have hVeq : V = (F ∪ U)ᶜ := by
      ext x
      constructor
      · intro hx
        have hf : x ∉ F := by
          have hh : x ∈ U ∪ V := Or.inr hx
          rwa [hpartition] at hh
        exact fun h => h.elim hf (fun hu => Set.disjoint_left.mp hdis hu hx)
      · intro hx
        have hf : x ∉ F := fun h => hx (Or.inl h)
        have huv : x ∈ U ∪ V := by rwa [hpartition]
        exact huv.resolve_left (fun h => hx (Or.inr h))
    refine ⟨hUeq,?_⟩
    rw [hVeq,g.image_compl,Set.image_union,hgF,hUeq]
  obtain ⟨actualPlane⟩ := actual_hyperbolic_component_simply_connected_cover_is_plane
    H (a.map 1) (Sigma.fst : P → A) hqc.isCoveringMap hsurj
  let planeCoordinate : H2 ≃ₜ Schoenflies.Plane := development.symm.trans actualPlane.symm
  have actual_developed_line_sides (K : C(ℝ,H2))
      (hK : Topology.IsClosedEmbedding K) (center : H2) (hcenter : center ∉ Set.range K) :
      ∃ U V : Set H2, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = (Set.range K)ᶜ ∧
        frontier U = Set.range K ∧ frontier V = Set.range K := by
    let line : C(ℝ,Schoenflies.Plane) :=
      ⟨planeCoordinate ∘ K,planeCoordinate.continuous.comp K.continuous⟩
    have hlineClosed : Topology.IsClosedEmbedding line := planeCoordinate.isClosedEmbedding.comp hK
    have havoid : planeCoordinate center ∉ Set.range line := by
      rintro ⟨s,hs⟩
      exact hcenter ⟨s,planeCoordinate.injective hs⟩
    have hJordan := CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.proper_line_inversion_isJordanCurve
      line hlineClosed.isProperMap hlineClosed.injective (planeCoordinate center) havoid
    obtain ⟨U,V,hU,hV,hUc,hVc,hdis,hpart,hFU,hFV⟩ :=
      CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.proper_line_sides_of_inversion_jordan
        (Set.range line) (planeCoordinate center) havoid hJordan
    have hlineImage : planeCoordinate.symm '' Set.range line = Set.range K := by
      ext x
      constructor
      · rintro ⟨_,⟨s,rfl⟩,rfl⟩
        exact ⟨s,(planeCoordinate.symm_apply_apply (K s)).symm⟩
      · rintro ⟨s,rfl⟩
        exact ⟨line s,Set.mem_range_self s,planeCoordinate.symm_apply_apply (K s)⟩
    refine ⟨planeCoordinate.symm '' U,planeCoordinate.symm '' V,
      planeCoordinate.symm.isOpenMap U hU,planeCoordinate.symm.isOpenMap V hV,
      hUc.image _ planeCoordinate.symm.continuous.continuousOn,
      hVc.image _ planeCoordinate.symm.continuous.continuousOn,?_,?_,?_,?_⟩
    · exact hdis.image planeCoordinate.symm.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
    · rw [← Set.image_union,hpart,planeCoordinate.symm.image_compl,hlineImage]
    · rw [← planeCoordinate.symm.image_frontier,hFU,hlineImage]
    · rw [← planeCoordinate.symm.image_frontier,hFV,hlineImage]
  have actual_endpoint_lifts_disjoint : Disjoint (Set.range sourceLift) (Set.range targetLift) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs⟩ ⟨t,ht⟩
    apply Set.disjoint_left.mp sourcePreimage_disjoint_target
    · change developedProjection z ∈ a.image
      rw [← hs,sourceLift_projection]
      exact Set.mem_range_self _
    · change developedProjection z ∈ b.image
      rw [← ht,targetLift_projection]
      exact Set.mem_range_self _
  have actual_facing_line_sides (K J : C(ℝ,H2))
      (hK : Topology.IsClosedEmbedding K) (hdis : Disjoint (Set.range K) (Set.range J)) :
      ∃ U V : Set H2, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = (Set.range K)ᶜ ∧
        frontier U = Set.range K ∧ frontier V = Set.range K ∧ Set.range J ⊆ U := by
    have havoid : J 0 ∉ Set.range K := by
      intro h
      exact Set.disjoint_left.mp hdis h (Set.mem_range_self 0)
    obtain ⟨U,V,hU,hV,hUc,hVc,hUV,hpart,hFU,hFV⟩ := actual_developed_line_sides K hK (J 0) havoid
    have hJavoid : Set.range J ⊆ U ∪ V := by
      intro z hz
      rw [hpart]
      intro hKz
      exact Set.disjoint_left.mp hdis hKz hz
    rcases (isConnected_range J.continuous).isPreconnected.subset_or_subset hU hV hUV hJavoid with h | h
    · exact ⟨U,V,hU,hV,hUc,hVc,hUV,hpart,hFU,hFV,h⟩
    · exact ⟨V,U,hV,hU,hVc,hUc,hUV.symm,by rw [Set.union_comm,hpart],hFV,hFU,h⟩
  obtain ⟨sourceInner,sourceOuter,hSourceInnerOpen,hSourceOuterOpen,hSourceInnerConn,hSourceOuterConn,
    hSourceSidesDisjoint,hSourceSidesPartition,hSourceInnerFrontier,hSourceOuterFrontier,hTargetInSourceInner⟩ :=
    actual_facing_line_sides sourceLift targetLift actual_sourceLift_closed_embedding actual_endpoint_lifts_disjoint
  obtain ⟨targetInner,targetOuter,hTargetInnerOpen,hTargetOuterOpen,hTargetInnerConn,hTargetOuterConn,
    hTargetSidesDisjoint,hTargetSidesPartition,hTargetInnerFrontier,hTargetOuterFrontier,hSourceInTargetInner⟩ :=
    actual_facing_line_sides targetLift sourceLift actual_targetLift_closed_embedding actual_endpoint_lifts_disjoint.symm
  have actual_periodic_lift_range_invariant (K : C(ℝ,H2))
      (hK : ∀ s, K (s+2*Real.pi) = developedDeck monodromy (K s)) :
      developedDeck monodromy '' Set.range K = Set.range K := by
    ext z
    constructor
    · rintro ⟨_,⟨s,rfl⟩,rfl⟩
      exact ⟨s+2*Real.pi,hK s⟩
    · rintro ⟨s,rfl⟩
      refine ⟨K (s-2*Real.pi),Set.mem_range_self _,?_⟩
      rw [← hK]
      congr 1
      ring
  have hSourceMonodromyRange := actual_periodic_lift_range_invariant sourceLift sourceLift_period
  have hTargetMonodromyRange := actual_periodic_lift_range_invariant targetLift targetLift_period
  have actual_source_facing_sides_invariant := actual_invariant_facing_side (developedDeck monodromy)
    (Set.range sourceLift) (Set.range targetLift) sourceInner sourceOuter
    hSourceInnerOpen hSourceOuterOpen hSourceInnerConn.isPreconnected hSourceSidesDisjoint
    hSourceSidesPartition ⟨targetLift 0,Set.mem_range_self 0⟩ hTargetInSourceInner
    hSourceMonodromyRange hTargetMonodromyRange
  have actual_target_facing_sides_invariant := actual_invariant_facing_side (developedDeck monodromy)
    (Set.range targetLift) (Set.range sourceLift) targetInner targetOuter
    hTargetInnerOpen hTargetOuterOpen hTargetInnerConn.isPreconnected hTargetSidesDisjoint
    hTargetSidesPartition ⟨sourceLift 0,Set.mem_range_self 0⟩ hSourceInTargetInner
    hTargetMonodromyRange hSourceMonodromyRange
  have actual_between_region_frontier
      {P : Type} [TopologicalSpace P] (U V F J : Set P)
      (hU : IsOpen U) (hV : IsOpen V) (hFU : frontier U = F) (hFV : frontier V = J)
      (hFintoV : F ⊆ V) (hJintoU : J ⊆ U) (hF : F.Nonempty) :
      IsOpen (U ∩ V) ∧ (U ∩ V).Nonempty ∧ frontier (U ∩ V) = F ∪ J := by
    have hOpen := hU.inter hV
    have included (A B L : Set P) (hA : IsOpen A) (hB : IsOpen B)
        (hFA : frontier A = L) (hLB : L ⊆ B) : L ⊆ frontier (A ∩ B) := by
      intro x hx
      have hxf : x ∈ frontier A := hFA.symm ▸ hx
      have hxB := hLB hx
      rw [frontier,(hA.inter hB).interior_eq]
      constructor
      · apply _root_.mem_closure_iff.mpr
        intro W hW hxW
        obtain ⟨y,⟨hyW,hyB⟩,hyA⟩ := _root_.mem_closure_iff.mp hxf.1 (W ∩ B)
          (hW.inter hB) ⟨hxW,hxB⟩
        exact ⟨y,hyW,hyA,hyB⟩
      · intro hxAB
        apply hxf.2
        rw [hA.interior_eq]
        exact hxAB.1
    have hFfront := included U V F hU hV hFU hFintoV
    have hJfront : J ⊆ frontier (U ∩ V) := by
      simpa only [Set.inter_comm] using included V U J hV hU hFV hJintoU
    refine ⟨hOpen,?_,Set.Subset.antisymm ?_ (Set.union_subset hFfront hJfront)⟩
    · obtain ⟨x,hx⟩ := hF
      have hxc : x ∈ closure U := (hFU.symm ▸ hx : x ∈ frontier U).1
      exact (closure_inter_open_nonempty_iff hV).mp ⟨x,hxc,hFintoV hx⟩
    · intro x hx
      rcases frontier_inter_subset U V hx with h | h
      · exact Or.inl (hFU ▸ h.1)
      · exact Or.inr (hFV ▸ h.2)
  have actual_clear_path_in_facing_side
      {P : Type} [TopologicalSpace P] (f : C(ℝ,P)) (F U V : Set P)
      (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
      (hpart : U ∪ V = Fᶜ)
      (havoid : ∀ t ∈ Set.Ioo 0 1, f t ∉ F)
      (q : ℝ) (hq : q ∈ Set.Icc 0 1) (hendpoint : f q ∈ U) :
      f '' Set.Ioo 0 1 ⊆ U := by
    have hconn : IsPreconnected (f '' Set.Ioo 0 1) :=
      isPreconnected_Ioo.image f f.continuous.continuousOn
    have hsub : f '' Set.Ioo 0 1 ⊆ U ∪ V := by
      rintro _ ⟨t,ht,rfl⟩
      rw [hpart]
      exact havoid t ht
    rcases hconn.subset_or_subset hU hV hdis hsub with h | h
    · exact h
    · have hqclosure : q ∈ closure (Set.Ioo (0:ℝ) 1) := by
        rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
        exact hq
      have hfclosure : f q ∈ closure (f '' Set.Ioo 0 1) :=
        mem_closure_image f.continuous.continuousAt hqclosure
      have hvclosure : f q ∈ closure V := closure_mono h hfclosure
      exact False.elim (Set.disjoint_left.mp (hdis.symm.closure_left hU) hvclosure hendpoint)
  let facingRegion : Set H2 := sourceInner ∩ targetInner
  have actual_facing_region_geometry : IsOpen facingRegion ∧ facingRegion.Nonempty ∧
      frontier facingRegion = Set.range sourceLift ∪ Set.range targetLift :=
    actual_between_region_frontier sourceInner targetInner (Set.range sourceLift)
      (Set.range targetLift) hSourceInnerOpen hTargetInnerOpen
      hSourceInnerFrontier hTargetInnerFrontier hSourceInTargetInner hTargetInSourceInner
      ⟨sourceLift 0,Set.mem_range_self 0⟩
  have actual_facing_region_monodromy : developedDeck monodromy '' facingRegion = facingRegion := by
    dsimp [facingRegion]
    rw [Set.image_inter (developedDeck monodromy).injective,
      actual_source_facing_sides_invariant.1,actual_target_facing_sides_invariant.1]
  have actual_monodromy_cannot_reverse_source_sides :
      ¬ Set.MapsTo (developedDeck monodromy) sourceInner sourceOuter := by
    intro hflip
    have hx := hTargetInSourceInner (Set.mem_range_self (0:ℝ))
    have hy : developedDeck monodromy (targetLift 0) ∈ sourceInner := by
      rw [← targetLift_period]
      exact hTargetInSourceInner (Set.mem_range_self _)
    exact Set.disjoint_left.mp hSourceSidesDisjoint hy (hflip hx)
  obtain ⟨facingSeamSource,hFacingSeamSource,facingSeamTarget,hFacingSeamTarget,
    hFacingSeamDistance,hFacingSeamMinimum⟩ := actual_periodic_closed_line_shortest_connector
      sourceLift targetLift (developedDeckIsometry monodromy) (2*Real.pi) (by positivity)
      sourceLift_period targetLift_period actual_targetLift_closed_embedding.isClosed_range
      actual_endpoint_lifts_disjoint
  have hFacingSeamEndpoints : facingSeamSource ≠ facingSeamTarget := dist_pos.mp hFacingSeamDistance
  obtain ⟨facingSeam,hFacingSeamContinuous,hFacingSeamInjective,hFacingSeam0,hFacingSeam1,hFacingSeamRange⟩ :=
    metric_segment_has_parametrization facingSeamSource facingSeamTarget hFacingSeamEndpoints
  have hFacingSeamAdd (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      dist facingSeamSource (facingSeam t) + dist (facingSeam t) facingSeamTarget =
        dist facingSeamSource facingSeamTarget := by
    have hh : facingSeam t ∈ facingSeam '' Set.Icc 0 1 := ⟨t,ht,rfl⟩
    rwa [hFacingSeamRange] at hh
  have hFacingSeamAvoid (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
      facingSeam t ∉ Set.range sourceLift ∧ facingSeam t ∉ Set.range targetLift := by
    have hti : t ∈ Set.Icc 0 1 := ⟨ht.1.le,ht.2.le⟩
    apply actual_shortest_connector_interior_avoids_boundaries (Set.range sourceLift)
      (Set.range targetLift) facingSeamSource facingSeamTarget (facingSeam t)
      hFacingSeamMinimum hFacingSeamSource hFacingSeamTarget (hFacingSeamAdd t hti)
    · intro he
      have hh := hFacingSeamInjective (by simp) hti (hFacingSeam0.trans he)
      linarith [ht.1]
    · intro he
      have hh := hFacingSeamInjective hti (by simp) (he.trans hFacingSeam1.symm)
      linarith [ht.2]
  let facingSeamMap : C(ℝ,H2) := ⟨facingSeam,hFacingSeamContinuous⟩
  have actual_compatible_seam_in_facing_region : facingSeam '' Set.Ioo 0 1 ⊆ facingRegion := by
    have hSourceSide := actual_clear_path_in_facing_side facingSeamMap
      (Set.range sourceLift) sourceInner sourceOuter hSourceInnerOpen hSourceOuterOpen
      hSourceSidesDisjoint hSourceSidesPartition (fun t ht => (hFacingSeamAvoid t ht).1)
      1 (by norm_num) (by change facingSeam 1 ∈ sourceInner
                          rw [hFacingSeam1]; exact hTargetInSourceInner hFacingSeamTarget)
    have hTargetSide := actual_clear_path_in_facing_side facingSeamMap
      (Set.range targetLift) targetInner targetOuter hTargetInnerOpen hTargetOuterOpen
      hTargetSidesDisjoint hTargetSidesPartition (fun t ht => (hFacingSeamAvoid t ht).2)
      0 (by norm_num) (by change facingSeam 0 ∈ targetInner
                          rw [hFacingSeam0]; exact hSourceInTargetInner hFacingSeamSource)
    exact Set.subset_inter hSourceSide hTargetSide
  have actual_compatible_seam_stabilizer_translate_disjoint
      (k : deck (Sigma.fst : P → A)) (hk : k ≠ 1)
      (hkSource : developedDeck k '' Set.range sourceLift = Set.range sourceLift)
      (hkTarget : developedDeck k '' Set.range targetLift = Set.range targetLift) :
      Disjoint (facingSeam '' Set.Icc 0 1)
        (developedDeck k '' (facingSeam '' Set.Icc 0 1)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t,ht,htz⟩ ⟨_,⟨r,hr,rfl⟩,hrz⟩
    have hxk : developedDeck k facingSeamSource ∈ Set.range sourceLift :=
      hkSource ▸ Set.mem_image_of_mem _ hFacingSeamSource
    have hyk : developedDeck k facingSeamTarget ∈ Set.range targetLift :=
      hkTarget ▸ Set.mem_image_of_mem _ hFacingSeamTarget
    have hadd1 : dist facingSeamSource z + dist z facingSeamTarget = dist facingSeamSource facingSeamTarget := by
      rw [← htz]
      exact hFacingSeamAdd t ht
    have hadd2 : dist (developedDeck k facingSeamSource) z +
        dist z (developedDeck k facingSeamTarget) = dist facingSeamSource facingSeamTarget := by
      rw [← hrz]
      rw [(all_developed_decks_isometric k).dist_eq,
        (all_developed_decks_isometric k).dist_eq]
      exact hFacingSeamAdd r hr
    have hcross1 := hFacingSeamMinimum facingSeamSource hFacingSeamSource (developedDeck k facingSeamTarget) hyk
    have hcross2 := hFacingSeamMinimum (developedDeck k facingSeamSource) hxk facingSeamTarget hFacingSeamTarget
    have htri1 := dist_triangle facingSeamSource z (developedDeck k facingSeamTarget)
    have htri2 := dist_triangle (developedDeck k facingSeamSource) z facingSeamTarget
    have hleft : dist facingSeamSource z = dist (developedDeck k facingSeamSource) z := by
      linarith
    have hright : dist z facingSeamTarget = dist z (developedDeck k facingSeamTarget) := by
      linarith
    have hcrossdist : dist facingSeamSource (developedDeck k facingSeamTarget) =
        dist facingSeamSource facingSeamTarget := by linarith
    by_cases hxz : facingSeamSource = z
    · have he : developedDeck k facingSeamSource = z := by
        apply dist_eq_zero.mp
        rw [← hleft,← hxz]
        exact dist_self _
      exact hk (all_developed_decks_fixed_implies_one k facingSeamSource (he.trans hxz.symm))
    · have hcrossadd : dist facingSeamSource z + dist z (developedDeck k facingSeamTarget) =
          dist facingSeamSource (developedDeck k facingSeamTarget) := by linarith
      have he := actual_h2_geodesic_continuation_unique facingSeamSource z facingSeamTarget
        (developedDeck k facingSeamTarget) hxz hadd1 hcrossadd hcrossdist.symm
      exact hk (all_developed_decks_fixed_implies_one k facingSeamTarget he.symm)
  have actual_facing_seam_disjoint_monodromy :=
    actual_compatible_seam_stabilizer_translate_disjoint monodromy monodromy_ne_one
      hSourceMonodromyRange hTargetMonodromyRange
  have actual_clear_seam_boundary_intersections
      {X : Type} (f : ℝ → X) (F J : Set X) (hFJ : Disjoint F J)
      (h0 : f 0 ∈ F) (h1 : f 1 ∈ J)
      (havoid : ∀ t ∈ Set.Ioo 0 1, f t ∉ F ∧ f t ∉ J) :
      (∀ z ∈ f '' Set.Icc 0 1, z ∈ F → z = f 0) ∧
      (∀ z ∈ f '' Set.Icc 0 1, z ∈ J → z = f 1) := by
    constructor
    · rintro _ ⟨t,ht,rfl⟩ hz
      by_cases ht0 : t = 0
      · rw [ht0]
      by_cases ht1 : t = 1
      · rw [ht1] at hz
        exact False.elim (Set.disjoint_left.mp hFJ hz h1)
      exact False.elim ((havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 ht1⟩).1 hz)
    · rintro _ ⟨t,ht,rfl⟩ hz
      by_cases ht1 : t = 1
      · rw [ht1]
      by_cases ht0 : t = 0
      · rw [ht0] at hz
        exact False.elim (Set.disjoint_left.mp hFJ h0 hz)
      exact False.elim ((havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 ht1⟩).2 hz)
  have hFacingBoundaryIntersections := actual_clear_seam_boundary_intersections facingSeam
    (Set.range sourceLift) (Set.range targetLift) actual_endpoint_lifts_disjoint
    (hFacingSeam0.symm ▸ hFacingSeamSource) (hFacingSeam1.symm ▸ hFacingSeamTarget) hFacingSeamAvoid
  have monodromy_range_membership (K : Set H2)
      (hK : developedDeck monodromy '' K = K) (x : H2) :
      developedDeck monodromy x ∈ K ↔ x ∈ K := by
    constructor
    · intro hx
      rw [← hK] at hx
      obtain ⟨y,hy,he⟩ := hx
      exact (developedDeck monodromy).injective he ▸ hy
    · intro hx
      exact hK ▸ Set.mem_image_of_mem _ hx
  have hShiftedSeamSourceIntersection
      (z : H2) (hz : z ∈ developedDeck monodromy '' (facingSeam '' Set.Icc 0 1))
      (hF : z ∈ Set.range sourceLift) : z = developedDeck monodromy facingSeamSource := by
    obtain ⟨u,hu,rfl⟩ := hz
    have huF := (monodromy_range_membership _ hSourceMonodromyRange u).mp hF
    have he := (hFacingBoundaryIntersections.1 u hu huF).trans hFacingSeam0
    exact congrArg (developedDeck monodromy) he
  have hShiftedSeamTargetIntersection
      (z : H2) (hz : z ∈ developedDeck monodromy '' (facingSeam '' Set.Icc 0 1))
      (hJ : z ∈ Set.range targetLift) : z = developedDeck monodromy facingSeamTarget := by
    obtain ⟨u,hu,rfl⟩ := hz
    have huJ := (monodromy_range_membership _ hTargetMonodromyRange u).mp hJ
    have he := (hFacingBoundaryIntersections.2 u hu huJ).trans hFacingSeam1
    exact congrArg (developedDeck monodromy) he
  obtain ⟨sourceParameter,hSourceParameter⟩ := hFacingSeamSource
  obtain ⟨targetParameter,hTargetParameter⟩ := hFacingSeamTarget
  let sourceArc : Set H2 := sourceLift '' Set.Icc sourceParameter (sourceParameter+2*Real.pi)
  let targetArc : Set H2 := targetLift '' Set.Icc targetParameter (targetParameter+2*Real.pi)
  let firstSeam : Set H2 := facingSeam '' Set.Icc 0 1
  let secondSeam : Set H2 := developedDeck monodromy '' firstSeam
  have hSourceArcSubset : sourceArc ⊆ Set.range sourceLift := by
    rintro _ ⟨s,hs,rfl⟩; exact Set.mem_range_self _
  have hTargetArcSubset : targetArc ⊆ Set.range targetLift := by
    rintro _ ⟨s,hs,rfl⟩; exact Set.mem_range_self _
  let sourcePlaneMap : C(ℝ,Schoenflies.Plane) :=
    ⟨planeCoordinate ∘ sourceLift,planeCoordinate.continuous.comp sourceLift.continuous⟩
  let targetPlaneMap : C(ℝ,Schoenflies.Plane) :=
    ⟨planeCoordinate ∘ targetLift,planeCoordinate.continuous.comp targetLift.continuous⟩
  have hSourceArcPlane : Schoenflies.IsArcBetween (planeCoordinate '' sourceArc)
      (planeCoordinate facingSeamSource) (planeCoordinate (developedDeck monodromy facingSeamSource)) := by
    have h := continuous_injective_interval_isArcBetween sourcePlaneMap
      (planeCoordinate.injective.comp actual_sourceLift_closed_embedding.injective)
      (show sourceParameter < sourceParameter+2*Real.pi by linarith [Real.pi_pos])
    have hEnd : sourceLift (sourceParameter+2*Real.pi) = developedDeck monodromy facingSeamSource := by
      rw [sourceLift_period,hSourceParameter]
    simpa only [sourcePlaneMap,ContinuousMap.coe_mk,Function.comp_def,sourceArc,
      Set.image_image,hSourceParameter,hEnd] using h
  have hTargetArcPlane : Schoenflies.IsArcBetween (planeCoordinate '' targetArc)
      (planeCoordinate facingSeamTarget) (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
    have h := continuous_injective_interval_isArcBetween targetPlaneMap
      (planeCoordinate.injective.comp actual_targetLift_closed_embedding.injective)
      (show targetParameter < targetParameter+2*Real.pi by linarith [Real.pi_pos])
    have hEnd : targetLift (targetParameter+2*Real.pi) = developedDeck monodromy facingSeamTarget := by
      rw [targetLift_period,hTargetParameter]
    simpa only [targetPlaneMap,ContinuousMap.coe_mk,Function.comp_def,targetArc,
      Set.image_image,hTargetParameter,hEnd] using h
  have hFirstSeamPlane : Schoenflies.IsArcBetween (planeCoordinate '' firstSeam)
      (planeCoordinate facingSeamSource) (planeCoordinate facingSeamTarget) := by
    refine ⟨planeCoordinate ∘ facingSeam,?_,?_,?_,?_,?_⟩
    · exact (planeCoordinate.continuous.comp hFacingSeamContinuous).continuousOn
    · intro s hs t ht he
      exact hFacingSeamInjective hs ht (planeCoordinate.injective he)
    · change (planeCoordinate ∘ facingSeam) '' Set.Icc 0 1 =
        planeCoordinate '' (facingSeam '' Set.Icc 0 1)
      rw [Set.image_image]
      rfl
    · change planeCoordinate (facingSeam 0) = _
      rw [hFacingSeam0]
    · change planeCoordinate (facingSeam 1) = _
      rw [hFacingSeam1]
  have hSecondSeamPlane : Schoenflies.IsArcBetween (planeCoordinate '' secondSeam)
      (planeCoordinate (developedDeck monodromy facingSeamSource))
      (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
    refine ⟨fun s => planeCoordinate (developedDeck monodromy (facingSeam s)),?_,?_,?_,?_,?_⟩
    · exact (planeCoordinate.continuous.comp
        ((developedDeck monodromy).continuous.comp hFacingSeamContinuous)).continuousOn
    · intro s hs t ht he
      exact hFacingSeamInjective hs ht
        ((developedDeck monodromy).injective (planeCoordinate.injective he))
    · change (fun s => planeCoordinate (developedDeck monodromy (facingSeam s))) '' Set.Icc 0 1 =
        planeCoordinate '' (developedDeck monodromy '' (facingSeam '' Set.Icc 0 1))
      rw [Set.image_image,Set.image_image]
    · change planeCoordinate (developedDeck monodromy (facingSeam 0)) = _
      rw [hFacingSeam0]
    · change planeCoordinate (developedDeck monodromy (facingSeam 1)) = _
      rw [hFacingSeam1]
  have hSourceSecondMeet (z : Schoenflies.Plane) (hzP : z ∈ planeCoordinate '' sourceArc)
      (hzR : z ∈ planeCoordinate '' secondSeam) :
      z = planeCoordinate (developedDeck monodromy facingSeamSource) := by
    obtain ⟨u,hu,huz⟩ := hzP
    obtain ⟨v,hv,hvz⟩ := hzR
    have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
    have hvF : v ∈ Set.range sourceLift := huv ▸ hSourceArcSubset hu
    have hvEq := hShiftedSeamSourceIntersection v hv hvF
    exact hvz.symm.trans (congrArg planeCoordinate hvEq)
  have hFirstTargetMeet (z : Schoenflies.Plane) (hzE : z ∈ planeCoordinate '' firstSeam)
      (hzQ : z ∈ planeCoordinate '' targetArc) : z = planeCoordinate facingSeamTarget := by
    obtain ⟨u,hu,huz⟩ := hzE
    obtain ⟨v,hv,hvz⟩ := hzQ
    have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
    have huJ : u ∈ Set.range targetLift := huv.symm ▸ hTargetArcSubset hv
    have huEq := (hFacingBoundaryIntersections.2 u hu huJ).trans hFacingSeam1
    exact huz.symm.trans (congrArg planeCoordinate huEq)
  have hSourceFirstMeet (z : Schoenflies.Plane) (hzP : z ∈ planeCoordinate '' sourceArc)
      (hzE : z ∈ planeCoordinate '' firstSeam) : z = planeCoordinate facingSeamSource := by
    obtain ⟨u,hu,huz⟩ := hzP
    obtain ⟨v,hv,hvz⟩ := hzE
    have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
    have hvF : v ∈ Set.range sourceLift := huv ▸ hSourceArcSubset hu
    have hvEq := (hFacingBoundaryIntersections.1 v hv hvF).trans hFacingSeam0
    exact hvz.symm.trans (congrArg planeCoordinate hvEq)
  have hSecondTargetMeet (z : Schoenflies.Plane) (hzR : z ∈ planeCoordinate '' secondSeam)
      (hzQ : z ∈ planeCoordinate '' targetArc) :
      z = planeCoordinate (developedDeck monodromy facingSeamTarget) := by
    obtain ⟨u,hu,huz⟩ := hzR
    obtain ⟨v,hv,hvz⟩ := hzQ
    have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
    have huJ : u ∈ Set.range targetLift := huv.symm ▸ hTargetArcSubset hv
    have huEq := hShiftedSeamTargetIntersection u hu huJ
    exact huz.symm.trans (congrArg planeCoordinate huEq)
  have hSourceTargetArcDisjoint : Disjoint (planeCoordinate '' sourceArc) (planeCoordinate '' targetArc) :=
    (actual_endpoint_lifts_disjoint.mono hSourceArcSubset hTargetArcSubset).image
      planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  have hSecondFirstSeamDisjoint : Disjoint (planeCoordinate '' secondSeam) (planeCoordinate '' firstSeam) :=
    actual_facing_seam_disjoint_monodromy.symm.image
      planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  let fundamentalBoundary : Set Schoenflies.Plane :=
    ((planeCoordinate '' sourceArc) ∪ (planeCoordinate '' secondSeam)) ∪
      ((planeCoordinate '' firstSeam) ∪ (planeCoordinate '' targetArc))
  have actual_fundamental_boundary_jordan : Schoenflies.IsJordanCurve fundamentalBoundary := by
    have hfirst := hSourceArcPlane.concatenate hSecondSeamPlane hSourceSecondMeet
    have hsecond := hFirstSeamPlane.concatenate hTargetArcPlane hFirstTargetMeet
    apply Schoenflies.IsJordanCurve.of_two_arcs hfirst hsecond.reverse
    intro z hz hz'
    rcases hz with hzP | hzR <;> rcases hz' with hzE | hzQ
    · exact Or.inl (hSourceFirstMeet z hzP hzE)
    · exact False.elim (Set.disjoint_left.mp hSourceTargetArcDisjoint hzP hzQ)
    · exact False.elim (Set.disjoint_left.mp hSecondFirstSeamDisjoint hzR hzE)
    · exact Or.inr (hSecondTargetMeet z hzR hzQ)
  have actual_embedded_square_closed_carrier (B : Interval × Interval → Schoenflies.Plane) (hB : Topology.IsEmbedding B)
      (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
      (hboundary : B '' {u | u.1 = 0 ∨ u.1 = 1 ∨ u.2 = 0 ∨ u.2 = 1} = C) :
      Set.range B = Schoenflies.inside C ∪ C := by
    classical
    let V : Set Schoenflies.Plane := {x | 0 < x 0 ∧ x 0 < 1 ∧ 0 < x 1 ∧ x 1 < 1}
    let p (x : Schoenflies.Plane) : Interval × Interval :=
      (Set.projIcc 0 1 (by norm_num) (x 0),Set.projIcc 0 1 (by norm_num) (x 1))
    let f : Schoenflies.Plane → Schoenflies.Plane := B ∘ p
    have hc0 : Continuous (fun x : Schoenflies.Plane => x 0) := by fun_prop
    have hc1 : Continuous (fun x : Schoenflies.Plane => x 1) := by fun_prop
    have hp : Continuous p := (continuous_projIcc.comp hc0).prodMk
      (continuous_projIcc.comp hc1)
    have hf : Continuous f := hB.continuous.comp hp
    have hV : IsOpen V := by
      exact (isOpen_lt continuous_const hc0).inter
        ((isOpen_lt hc0 continuous_const).inter
          ((isOpen_lt continuous_const hc1).inter
            (isOpen_lt hc1 continuous_const)))
    have hpval (x : Schoenflies.Plane) (hx : x ∈ V) :
        ((p x).1:ℝ)=x 0 ∧ ((p x).2:ℝ)=x 1 := by
      constructor
      · exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num) ⟨hx.1.le,hx.2.1.le⟩)
      · exact congrArg Subtype.val (Set.projIcc_of_mem (by norm_num) ⟨hx.2.2.1.le,hx.2.2.2.le⟩)
    have hfinj : Set.InjOn f V := by
      intro x hx y hy he
      have he' := hB.injective he
      have h0 := congrArg (fun u : Interval × Interval => (u.1:ℝ)) he'
      have h1 := congrArg (fun u : Interval × Interval => (u.2:ℝ)) he'
      rw [(hpval x hx).1,(hpval y hy).1] at h0
      rw [(hpval x hx).2,(hpval y hy).2] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    let U := f '' V
    have hU : IsOpen U :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
        f V hV hf.continuousOn hfinj
    have hcompact : IsCompact (Set.range B) := isCompact_range hB.continuous
    have hUsub : U ⊆ Set.range B := by rintro _ ⟨x,hx,rfl⟩;exact ⟨p x,rfl⟩
    have hsplit : Set.range B = U ∪ C := by
      rw [← hboundary]
      ext z
      constructor
      · rintro ⟨uv,rfl⟩
        by_cases hb : uv.1 = 0 ∨ uv.1 = 1 ∨ uv.2 = 0 ∨ uv.2 = 1
        · exact Or.inr ⟨uv,hb,rfl⟩
        · left
          let x := Schoenflies.Plane.mk uv.1 uv.2
          have hx : x ∈ V := by
            have hn : uv.1 ≠ 0 ∧ uv.1 ≠ 1 ∧ uv.2 ≠ 0 ∧ uv.2 ≠ 1 := by tauto
            have h0 : (uv.1:ℝ) ≠ 0 := by intro h;exact hn.1 (Subtype.ext h)
            have h1 : (uv.1:ℝ) ≠ 1 := by intro h;exact hn.2.1 (Subtype.ext h)
            have h2 : (uv.2:ℝ) ≠ 0 := by intro h;exact hn.2.2.1 (Subtype.ext h)
            have h3 : (uv.2:ℝ) ≠ 1 := by intro h;exact hn.2.2.2 (Subtype.ext h)
            exact ⟨lt_of_le_of_ne uv.1.property.1 h0.symm,
              lt_of_le_of_ne uv.1.property.2 h1,
              lt_of_le_of_ne uv.2.property.1 h2.symm,
              lt_of_le_of_ne uv.2.property.2 h3⟩
          refine ⟨x,hx,?_⟩
          change B (p x) = B uv
          congr 1
          apply Prod.ext <;> apply Subtype.ext
          · exact (hpval x hx).1
          · exact (hpval x hx).2
      · rintro (⟨x,hx,rfl⟩|⟨uv,huv,rfl⟩)
        · exact ⟨p x,rfl⟩
        · exact ⟨uv,rfl⟩
    have hUC : U ⊆ Cᶜ := by
      rintro z ⟨x,hx,rfl⟩ hz
      rw [← hboundary] at hz
      obtain ⟨uv,huv,he⟩ := hz
      have huvEq : uv = p x := hB.injective he
      subst uv
      have hh := hpval x hx
      rcases huv with h | h | h | h
      · have hh' := congrArg Subtype.val h;rw [hh.1] at hh';norm_num at hh';linarith [hx.1]
      · have hh' := congrArg Subtype.val h;rw [hh.1] at hh';norm_num at hh';linarith [hx.2.1]
      · have hh' := congrArg Subtype.val h;rw [hh.2] at hh';norm_num at hh';linarith [hx.2.2.1]
      · have hh' := congrArg Subtype.val h;rw [hh.2] at hh';norm_num at hh';linarith [hx.2.2.2]
    have hfront : frontier U ⊆ C := by
      intro z hz
      have hzR : z ∈ Set.range B := hcompact.isClosed.closure_subset (closure_mono hUsub hz.1)
      rw [hsplit] at hzR
      rcases hzR with hzU | hzC
      · exact False.elim (hz.2 (by rwa [hU.interior_eq]))
      · exact hzC
    have hVconvex : Convex ℝ V := by
      have he : V = ((fun x : Schoenflies.Plane => x 0) ⁻¹' Set.Ioo (0:ℝ) 1 ∩
        (fun x : Schoenflies.Plane => x 1) ⁻¹' Set.Ioo (0:ℝ) 1) := by ext x; simp [V]; tauto
      rw [he]
      exact ((convex_Ioo (𝕜 := ℝ) (0:ℝ) 1).linear_preimage (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0)).inter
        ((convex_Ioo (𝕜 := ℝ) (0:ℝ) 1).linear_preimage (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1))
    have hpre : IsPreconnected U := hVconvex.isPreconnected.image f hf.continuousOn
    have hne : U.Nonempty := ⟨f (Schoenflies.Plane.mk (1/2) (1/2)),⟨_,by norm_num [V,Schoenflies.Plane.mk],rfl⟩⟩
    have hfr : frontier U ∩ Cᶜ = ∅ := by
      ext z
      simp only [Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_empty_iff_false,iff_false]
      exact fun hz => hz.2 (hfront hz.1)
    obtain ⟨x,hx⟩ := hne
    have hcomp : connectedComponentIn Cᶜ x = U :=
      Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint hU hpre hUC hfr hx
    have hsep := Schoenflies.jordan_curve_theorem hC
    have hxside : x ∈ Schoenflies.inside C ∨ x ∈ Schoenflies.outside C := by
      change x ∈ Schoenflies.inside C ∪ Schoenflies.outside C
      rw [Schoenflies.inside_union_outside]
      exact hUC hx
    have hEq : U = Schoenflies.inside C := by
      rcases hxside with hi | ho
      · exact hcomp.symm.trans (hsep.connectedComponentIn_eq_inside hi)
      · have he : Schoenflies.outside C = U := (hsep.connectedComponentIn_eq_outside ho).symm.trans hcomp
        exact False.elim (hsep.not_isBounded_outside (he ▸ hcompact.isBounded.subset hUsub))
    rw [hsplit,hEq]
  let markedSourceEdge (u : Interval) : Schoenflies.Plane :=
    planeCoordinate (sourceLift (sourceParameter + (u:ℝ)*(2*Real.pi)))
  let markedTargetEdge (u : Interval) : Schoenflies.Plane :=
    planeCoordinate (targetLift (targetParameter + (u:ℝ)*(2*Real.pi)))
  let markedFirstSeam (u : Interval) : Schoenflies.Plane := planeCoordinate (facingSeam u)
  let markedSecondSeam (u : Interval) : Schoenflies.Plane :=
    planeCoordinate (developedDeck monodromy (facingSeam u))
  have actual_affine_interval_embedding (p : ℝ) :
      Topology.IsEmbedding (fun u : Interval => p+(u:ℝ)*(2*Real.pi)) := by
    refine ((show Continuous (fun u : Interval => p+(u:ℝ)*(2*Real.pi)) from
      continuous_const.add (continuous_subtype_val.mul continuous_const)).isClosedEmbedding ?_).isEmbedding
    intro u v h
    apply Subtype.ext
    nlinarith [Real.pi_pos]
  have hMarkedSourceEmbedding : Topology.IsEmbedding markedSourceEdge :=
    planeCoordinate.isEmbedding.comp (actual_sourceLift_closed_embedding.isEmbedding.comp
      (actual_affine_interval_embedding sourceParameter))
  have hMarkedTargetEmbedding : Topology.IsEmbedding markedTargetEdge :=
    planeCoordinate.isEmbedding.comp (actual_targetLift_closed_embedding.isEmbedding.comp
      (actual_affine_interval_embedding targetParameter))
  have hMarkedFirstEmbedding : Topology.IsEmbedding markedFirstSeam := by
    refine ((show Continuous markedFirstSeam from
      planeCoordinate.continuous.comp (hFacingSeamContinuous.comp continuous_subtype_val)).isClosedEmbedding ?_).isEmbedding
    intro u v h
    apply Subtype.ext
    exact hFacingSeamInjective u.property v.property (planeCoordinate.injective h)
  have hMarkedSecondEmbedding : Topology.IsEmbedding markedSecondSeam := by
    refine ((show Continuous markedSecondSeam from planeCoordinate.continuous.comp
      ((developedDeck monodromy).continuous.comp
        (hFacingSeamContinuous.comp continuous_subtype_val))).isClosedEmbedding ?_).isEmbedding
    intro u v h
    apply Subtype.ext
    exact hFacingSeamInjective u.property v.property
      ((developedDeck monodromy).injective (planeCoordinate.injective h))
  have hMarkedSource0 : markedSourceEdge 0 = planeCoordinate facingSeamSource := by
    simp [markedSourceEdge,hSourceParameter]
  have hMarkedSource1 : markedSourceEdge 1 = planeCoordinate (developedDeck monodromy facingSeamSource) := by
    simp only [markedSourceEdge]
    simp
    rw [sourceLift_period,hSourceParameter]
  have hMarkedTarget0 : markedTargetEdge 0 = planeCoordinate facingSeamTarget := by
    simp [markedTargetEdge,hTargetParameter]
  have hMarkedTarget1 : markedTargetEdge 1 = planeCoordinate (developedDeck monodromy facingSeamTarget) := by
    simp only [markedTargetEdge]
    simp
    rw [targetLift_period,hTargetParameter]
  have hMarkedFirst0 : markedFirstSeam 0 = planeCoordinate facingSeamSource := by
    change planeCoordinate (facingSeam 0) = _; rw [hFacingSeam0]
  have hMarkedFirst1 : markedFirstSeam 1 = planeCoordinate facingSeamTarget := by
    change planeCoordinate (facingSeam 1) = _; rw [hFacingSeam1]
  have hMarkedSecond0 : markedSecondSeam 0 = planeCoordinate (developedDeck monodromy facingSeamSource) := by
    change planeCoordinate (developedDeck monodromy (facingSeam 0)) = _; rw [hFacingSeam0]
  have hMarkedSecond1 : markedSecondSeam 1 = planeCoordinate (developedDeck monodromy facingSeamTarget) := by
    change planeCoordinate (developedDeck monodromy (facingSeam 1)) = _; rw [hFacingSeam1]
  have hMarkedSourceMem (u : Interval) : markedSourceEdge u ∈ planeCoordinate '' sourceArc := by
    refine ⟨_,⟨_,?_,rfl⟩,rfl⟩
    constructor <;> nlinarith [u.property.1,u.property.2,Real.pi_pos]
  have hMarkedTargetMem (u : Interval) : markedTargetEdge u ∈ planeCoordinate '' targetArc := by
    refine ⟨_,⟨_,?_,rfl⟩,rfl⟩
    constructor <;> nlinarith [u.property.1,u.property.2,Real.pi_pos]
  have hMarkedFirstMem (u : Interval) : markedFirstSeam u ∈ planeCoordinate '' firstSeam :=
    ⟨_,⟨u,u.property,rfl⟩,rfl⟩
  have hMarkedSecondMem (u : Interval) : markedSecondSeam u ∈ planeCoordinate '' secondSeam :=
    ⟨_,⟨_,⟨u,u.property,rfl⟩,rfl⟩,rfl⟩
  obtain ⟨markedFundamentalDisk,hMarkedFundamentalDiskEmbedding,
      hMarkedFundamentalBottom,hMarkedFundamentalTop,
      hMarkedFundamentalLeft,hMarkedFundamentalRight⟩ :=
    CurveComplex.G3Review.actual_four_arc_cycle_has_prescribed_embedded_square
      markedSourceEdge markedTargetEdge markedFirstSeam markedSecondSeam
      hMarkedSourceEmbedding hMarkedTargetEmbedding hMarkedFirstEmbedding hMarkedSecondEmbedding
      (hMarkedSource0.trans hMarkedFirst0.symm) (hMarkedSource1.trans hMarkedSecond0.symm)
      (hMarkedTarget0.trans hMarkedFirst1.symm) (hMarkedTarget1.trans hMarkedSecond1.symm)
      (by intro s t h
          have he := hSourceFirstMeet _ (hMarkedSourceMem s) (h ▸ hMarkedFirstMem t)
          exact ⟨hMarkedSourceEmbedding.injective (he.trans hMarkedSource0.symm),
            hMarkedFirstEmbedding.injective (h.symm.trans (he.trans hMarkedFirst0.symm))⟩)
      (by intro s t h
          have he := hSourceSecondMeet _ (hMarkedSourceMem s) (h ▸ hMarkedSecondMem t)
          exact ⟨hMarkedSourceEmbedding.injective (he.trans hMarkedSource1.symm),
            hMarkedSecondEmbedding.injective (h.symm.trans (he.trans hMarkedSecond0.symm))⟩)
      (by intro s t h
          have he := hFirstTargetMeet _ (h ▸ hMarkedFirstMem t) (hMarkedTargetMem s)
          exact ⟨hMarkedTargetEmbedding.injective (he.trans hMarkedTarget0.symm),
            hMarkedFirstEmbedding.injective (h.symm.trans (he.trans hMarkedFirst1.symm))⟩)
      (by intro s t h
          have he := hSecondTargetMeet _ (h ▸ hMarkedSecondMem t) (hMarkedTargetMem s)
          exact ⟨hMarkedTargetEmbedding.injective (he.trans hMarkedTarget1.symm),
            hMarkedSecondEmbedding.injective (h.symm.trans (he.trans hMarkedSecond1.symm))⟩)
      (hSourceTargetArcDisjoint.mono (Set.range_subset_iff.mpr hMarkedSourceMem)
        (Set.range_subset_iff.mpr hMarkedTargetMem))
      (hSecondFirstSeamDisjoint.symm.mono (Set.range_subset_iff.mpr hMarkedFirstMem)
        (Set.range_subset_iff.mpr hMarkedSecondMem))
  have actual_marked_fundamental_seam_compatibility (v : Interval) :
      markedFundamentalDisk (1,v) =
        planeCoordinate (developedDeck monodromy (planeCoordinate.symm (markedFundamentalDisk (0,v)))) := by
    rw [hMarkedFundamentalRight,hMarkedFundamentalLeft]
    simp only [markedFirstSeam,markedSecondSeam,Homeomorph.symm_apply_apply]
  have actual_affine_period_arc_range (F : ℝ → H2) (p : ℝ) :
      Set.range (fun u : Interval => F (p+(u:ℝ)*(2*Real.pi))) =
        F '' Set.Icc p (p+2*Real.pi) := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      refine ⟨_,?_,rfl⟩
      constructor <;> nlinarith [u.property.1,u.property.2,Real.pi_pos]
    · rintro ⟨s,hs,rfl⟩
      let u : Interval := ⟨(s-p)/(2*Real.pi),by
        constructor
        · exact div_nonneg (sub_nonneg.mpr hs.1) (by positivity)
        · apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
          linarith [hs.2]⟩
      refine ⟨u,?_⟩
      congr 1
      dsimp [u]
      field_simp
      ring
  have hMarkedSourceRange : Set.range markedSourceEdge = planeCoordinate '' sourceArc := by
    change Set.range (planeCoordinate ∘ (fun u : Interval => sourceLift (sourceParameter+(u:ℝ)*(2*Real.pi)))) = _
    rw [Set.range_comp,actual_affine_period_arc_range]
  have hMarkedTargetRange : Set.range markedTargetEdge = planeCoordinate '' targetArc := by
    change Set.range (planeCoordinate ∘ (fun u : Interval => targetLift (targetParameter+(u:ℝ)*(2*Real.pi)))) = _
    rw [Set.range_comp,actual_affine_period_arc_range]
  have hMarkedFirstRange : Set.range markedFirstSeam = planeCoordinate '' firstSeam := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩;exact hMarkedFirstMem u
    · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩;exact ⟨⟨t,ht⟩,rfl⟩
  have hMarkedSecondRange : Set.range markedSecondSeam = planeCoordinate '' secondSeam := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩;exact hMarkedSecondMem u
    · rintro ⟨_,⟨_,⟨t,ht,rfl⟩,rfl⟩,rfl⟩;exact ⟨⟨t,ht⟩,rfl⟩
  let markedSquareBoundary : Set (Interval × Interval) :=
    {uv | uv.1 = 0 ∨ uv.1 = 1 ∨ uv.2 = 0 ∨ uv.2 = 1}
  have actual_marked_fundamental_boundary_image :
      markedFundamentalDisk '' markedSquareBoundary = fundamentalBoundary := by
    have he : markedFundamentalDisk '' markedSquareBoundary =
        (Set.range markedSourceEdge ∪ Set.range markedSecondSeam) ∪
        (Set.range markedFirstSeam ∪ Set.range markedTargetEdge) := by
      ext z
      constructor
      · rintro ⟨uv,huv,rfl⟩
        rcases huv with hl | hr | hb | ht
        · exact Or.inr (Or.inl ⟨uv.2,by rw [show uv = (0,uv.2) from Prod.ext hl rfl]; exact (hMarkedFundamentalLeft uv.2).symm⟩)
        · exact Or.inl (Or.inr ⟨uv.2,by rw [show uv = (1,uv.2) from Prod.ext hr rfl]; exact (hMarkedFundamentalRight uv.2).symm⟩)
        · exact Or.inl (Or.inl ⟨uv.1,by rw [show uv = (uv.1,0) from Prod.ext rfl hb]; exact (hMarkedFundamentalBottom uv.1).symm⟩)
        · exact Or.inr (Or.inr ⟨uv.1,by rw [show uv = (uv.1,1) from Prod.ext rfl ht]; exact (hMarkedFundamentalTop uv.1).symm⟩)
      · rintro ((⟨u,rfl⟩|⟨v,rfl⟩)|(⟨v,rfl⟩|⟨u,rfl⟩))
        · exact ⟨(u,0),Or.inr (Or.inr (Or.inl rfl)),hMarkedFundamentalBottom u⟩
        · exact ⟨(1,v),Or.inr (Or.inl rfl),hMarkedFundamentalRight v⟩
        · exact ⟨(0,v),Or.inl rfl,hMarkedFundamentalLeft v⟩
        · exact ⟨(u,1),Or.inr (Or.inr (Or.inr rfl)),hMarkedFundamentalTop u⟩
    rw [he,hMarkedSourceRange,hMarkedTargetRange,hMarkedFirstRange,hMarkedSecondRange]
  have actual_marked_fundamental_disk_closed_carrier :
      Set.range markedFundamentalDisk = Schoenflies.inside fundamentalBoundary ∪ fundamentalBoundary :=
    actual_embedded_square_closed_carrier markedFundamentalDisk hMarkedFundamentalDiskEmbedding
      fundamentalBoundary actual_fundamental_boundary_jordan actual_marked_fundamental_boundary_image
  obtain ⟨fundamentalDisk,hFundamentalDiskEmbedding,hFundamentalDiskBoundary⟩ :=
    CurveComplex.exists_embedded_square_disc_of_jordan actual_fundamental_boundary_jordan
  have actual_proper_line_side_unbounded (K : C(ℝ,Schoenflies.Plane))
      (hK : IsProperMap K) (V : Set Schoenflies.Plane) (hfront : frontier V = Set.range K) :
      ¬ Bornology.IsBounded V := by
    intro hbounded
    have hcompactLine : IsCompact (Set.range K) := by
      rw [← hfront]
      exact hbounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have hcompactPreimage := hK.isCompact_preimage hcompactLine
    have hcompactReal : IsCompact (Set.univ : Set ℝ) := by
      convert hcompactPreimage using 1
      ext x
      simp
    obtain ⟨M,hM⟩ := hcompactReal.bddAbove
    have hh : M+1 ≤ M := hM (Set.mem_univ _)
    linarith
  have hFirstSeamFacingClosure : firstSeam ⊆ closure facingRegion := by
    rintro _ ⟨t,ht,rfl⟩
    have htclosure : t ∈ closure (Set.Ioo (0:ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
      exact ht
    exact closure_mono actual_compatible_seam_in_facing_region
      (mem_closure_image hFacingSeamContinuous.continuousAt htclosure)
  have hSecondSeamFacingClosure : secondSeam ⊆ closure facingRegion := by
    have hmono := Set.image_mono hFirstSeamFacingClosure (f := developedDeck monodromy)
    rw [(developedDeck monodromy).image_closure,actual_facing_region_monodromy] at hmono
    exact hmono
  have hClosureFacingSource : closure facingRegion ⊆ sourceInner ∪ Set.range sourceLift := by
    have hh := closure_mono (Set.inter_subset_left : facingRegion ⊆ sourceInner)
    rw [closure_eq_self_union_frontier sourceInner,hSourceInnerFrontier] at hh
    exact hh
  have hClosureFacingTarget : closure facingRegion ⊆ targetInner ∪ Set.range targetLift := by
    have hh := closure_mono (Set.inter_subset_right : facingRegion ⊆ targetInner)
    rw [closure_eq_self_union_frontier targetInner,hTargetInnerFrontier] at hh
    exact hh
  have hFundamentalBoundarySourceSide : fundamentalBoundary ⊆
      (planeCoordinate '' sourceInner) ∪ (planeCoordinate '' Set.range sourceLift) := by
    rintro z ((⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩) | (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩))
    · exact Or.inr (Set.mem_image_of_mem _ (hSourceArcSubset hx))
    · rw [← Set.image_union]
      exact Set.mem_image_of_mem _ (hClosureFacingSource (hSecondSeamFacingClosure hx))
    · rw [← Set.image_union]
      exact Set.mem_image_of_mem _ (hClosureFacingSource (hFirstSeamFacingClosure hx))
    · exact Or.inl (Set.mem_image_of_mem _ (hTargetInSourceInner (hTargetArcSubset hx)))
  have hFundamentalBoundaryTargetSide : fundamentalBoundary ⊆
      (planeCoordinate '' targetInner) ∪ (planeCoordinate '' Set.range targetLift) := by
    rintro z ((⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩) | (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩))
    · exact Or.inl (Set.mem_image_of_mem _ (hSourceInTargetInner (hSourceArcSubset hx)))
    · rw [← Set.image_union]
      exact Set.mem_image_of_mem _ (hClosureFacingTarget (hSecondSeamFacingClosure hx))
    · rw [← Set.image_union]
      exact Set.mem_image_of_mem _ (hClosureFacingTarget (hFirstSeamFacingClosure hx))
    · exact Or.inr (Set.mem_image_of_mem _ (hTargetArcSubset hx))
  have hSourcePlaneRange : planeCoordinate '' Set.range sourceLift = Set.range sourcePlaneMap := by
    change planeCoordinate '' Set.range sourceLift = Set.range (planeCoordinate ∘ sourceLift)
    rw [Set.range_comp]
  have hTargetPlaneRange : planeCoordinate '' Set.range targetLift = Set.range targetPlaneMap := by
    change planeCoordinate '' Set.range targetLift = Set.range (planeCoordinate ∘ targetLift)
    rw [Set.range_comp]
  have hSourceOuterPlaneFrontier : frontier (planeCoordinate '' sourceOuter) = Set.range sourcePlaneMap := by
    rw [← planeCoordinate.image_frontier,hSourceOuterFrontier,hSourcePlaneRange]
  have hTargetOuterPlaneFrontier : frontier (planeCoordinate '' targetOuter) = Set.range targetPlaneMap := by
    rw [← planeCoordinate.image_frontier,hTargetOuterFrontier,hTargetPlaneRange]
  have hSourceOuterPlaneUnbounded := actual_proper_line_side_unbounded sourcePlaneMap
    (planeCoordinate.isClosedEmbedding.comp actual_sourceLift_closed_embedding).isProperMap
    (planeCoordinate '' sourceOuter) hSourceOuterPlaneFrontier
  have hTargetOuterPlaneUnbounded := actual_proper_line_side_unbounded targetPlaneMap
    (planeCoordinate.isClosedEmbedding.comp actual_targetLift_closed_embedding).isProperMap
    (planeCoordinate '' targetOuter) hTargetOuterPlaneFrontier
  have hInsideSourceSide : Schoenflies.inside fundamentalBoundary ⊆ planeCoordinate '' sourceInner := by
    apply jordan_inside_contained_in_proper_line_side actual_fundamental_boundary_jordan
      (planeCoordinate.isOpenMap _ hSourceInnerOpen) (planeCoordinate.isOpenMap _ hSourceOuterOpen)
      (hSourceOuterConn.image _ planeCoordinate.continuous.continuousOn)
      (hSourceSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
    · rw [← Set.image_union,hSourceSidesPartition,planeCoordinate.image_compl]
    · rw [← planeCoordinate.image_frontier,hSourceOuterFrontier]
    · exact hSourceOuterPlaneUnbounded
    · exact hFundamentalBoundarySourceSide
  have hInsideTargetSide : Schoenflies.inside fundamentalBoundary ⊆ planeCoordinate '' targetInner := by
    apply jordan_inside_contained_in_proper_line_side actual_fundamental_boundary_jordan
      (planeCoordinate.isOpenMap _ hTargetInnerOpen) (planeCoordinate.isOpenMap _ hTargetOuterOpen)
      (hTargetOuterConn.image _ planeCoordinate.continuous.continuousOn)
      (hTargetSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
    · rw [← Set.image_union,hTargetSidesPartition,planeCoordinate.image_compl]
    · rw [← planeCoordinate.image_frontier,hTargetOuterFrontier]
    · exact hTargetOuterPlaneUnbounded
    · exact hFundamentalBoundaryTargetSide
  have actual_fundamental_cell_inside_facing_region :
      Schoenflies.inside fundamentalBoundary ⊆ planeCoordinate '' facingRegion := by
    rw [Set.image_inter planeCoordinate.injective]
    exact Set.subset_inter hInsideSourceSide hInsideTargetSide
  have actual_same_curve_deck_overlap_reparametrizes
      (c : Curve E) (F : C(ℝ,H2))
      (hFproj : ∀ s, developedProjection (F s) = c.map (Circle.exp s))
      (k : deck (Sigma.fst : P → A)) (r s : ℝ)
      (hmeet : developedDeck k (F r) = F s) :
      ∀ u : ℝ, developedDeck k (F u) = F (u + (s-r)) := by
    have hangle : Circle.exp r = Circle.exp s := by
      apply c.embedded.injective
      rw [← hFproj, ← hFproj, ← hmeet, developedDeck_projection]
    have hangleShift (u : ℝ) : Circle.exp u = Circle.exp (u + (s-r)) := by
      obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hangle.symm
      apply Circle.exp_eq_exp.mpr
      refine ⟨-n,?_⟩
      push_cast
      linarith
    let f₁ : ℝ → P := fun u => k • development.symm (F u)
    let f₂ : ℝ → P := fun u => development.symm (F (u+(s-r)))
    have hc₁ : Continuous f₁ := (hqc.continuous_const_smul k).comp
      (development.symm.continuous.comp F.continuous)
    have hc₂ : Continuous f₂ := development.symm.continuous.comp
      (F.continuous.comp (continuous_id.add continuous_const))
    have hcomp : (Sigma.fst : P → A) ∘ f₁ = (Sigma.fst : P → A) ∘ f₂ := by
      funext u
      apply Subtype.ext
      change (k • development.symm (F u)).1.val =
        (development.symm (F (u+(s-r)))).1.val
      rw [congrArg Subtype.val (hqc.map_smul k)]
      change developedProjection (F u) = developedProjection (F (u+(s-r)))
      rw [hFproj,hFproj,hangleShift]
    have hbase : f₁ r = f₂ r := by
      apply development.injective
      change development (k • development.symm (F r)) =
        development (development.symm (F (r+(s-r))))
      rw [development.apply_symm_apply]
      change developedDeck k (F r) = F (r+(s-r))
      convert hmeet using 1 <;> congr 1 <;> ring
    have he := hqc.isCoveringMap.eq_of_comp_eq hc₁ hc₂ hcomp r hbase
    intro u
    have h := congrArg (fun f : ℝ → P => development (f u)) he
    simpa only [f₁,f₂,developedDeck,Homeomorph.trans_apply,
      development.apply_symm_apply,Subgroup.smul_def,Homeomorph.smul_def] using h
  have actual_same_curve_deck_lifts_equal_or_disjoint
      (c : Curve E) (F : C(ℝ,H2))
      (hFproj : ∀ s, developedProjection (F s) = c.map (Circle.exp s))
      (k : deck (Sigma.fst : P → A)) :
      developedDeck k '' Set.range F = Set.range F ∨
        Disjoint (developedDeck k '' Set.range F) (Set.range F) := by
    by_cases hd : Disjoint (developedDeck k '' Set.range F) (Set.range F)
    · exact Or.inr hd
    left
    obtain ⟨z,hz₁,hz₂⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨_,⟨r,rfl⟩,hr⟩ := hz₁
    obtain ⟨s,hs⟩ := hz₂
    have hparam := actual_same_curve_deck_overlap_reparametrizes c F hFproj k r s
      (hr.trans hs.symm)
    ext z
    constructor
    · rintro ⟨_,⟨u,rfl⟩,rfl⟩
      exact ⟨u+(s-r),(hparam u).symm⟩
    · rintro ⟨u,rfl⟩
      refine ⟨F (u-(s-r)),Set.mem_range_self _,?_⟩
      rw [hparam]
      congr 1
      ring
  have actual_all_source_deck_lifts_equal_or_disjoint :=
    actual_same_curve_deck_lifts_equal_or_disjoint a sourceLift sourceLift_projection
  have actual_all_target_deck_lifts_equal_or_disjoint :=
    actual_same_curve_deck_lifts_equal_or_disjoint b targetLift targetLift_projection
  have actual_developedDeck_mul (k l : deck (Sigma.fst : P → A)) (z : H2) :
      developedDeck (k*l) z = developedDeck k (developedDeck l z) := by
    simp only [developedDeck,Homeomorph.trans_apply,development.symm_apply_apply,
      Subgroup.coe_mul,Homeomorph.mul_apply]
  have actual_developedDeck_one (z : H2) : developedDeck 1 z = z := by
    simp only [developedDeck,Homeomorph.trans_apply,Subgroup.coe_one,
      Homeomorph.one_apply,development.apply_symm_apply]
  have actual_developedDeck_point_injective
      (k l : deck (Sigma.fst : P → A)) (z : H2)
      (he : developedDeck k z = developedDeck l z) : k = l := by
    letI : IsCancelSMul (deck (Sigma.fst : P → A)) P := hqc.isCancelSMul
    apply IsCancelSMul.right_cancel k l (development.symm z)
    apply development.injective
    simpa only [developedDeck,Homeomorph.trans_apply,Subgroup.smul_def,
      Homeomorph.smul_def] using he
  have actual_common_monodromy_integer_period
      (F : ℝ → H2) (hFperiod : ∀ s, F (s+2*Real.pi) = developedDeck monodromy (F s))
      (n : ℤ) : ∀ s, F (s + n*(2*Real.pi)) = developedDeck (monodromy^n) (F s) := by
    have hinvperiod (s : ℝ) : F (s-2*Real.pi) = developedDeck monodromy⁻¹ (F s) := by
      have hp := hFperiod (s-2*Real.pi)
      have harg : s-2*Real.pi+2*Real.pi = s := by ring
      rw [harg] at hp
      have hh := congrArg (developedDeck monodromy⁻¹) hp
      rw [← actual_developedDeck_mul,inv_mul_cancel,actual_developedDeck_one] at hh
      exact hh.symm
    induction n using Int.induction_on with
    | zero => intro s; simpa using (actual_developedDeck_one (F s)).symm
    | succ n ih =>
      intro s
      have harg : s + (((n : ℤ)+1 : ℤ):ℝ)*(2*Real.pi) =
          (s+2*Real.pi)+(n:ℤ)*(2*Real.pi) := by push_cast; ring
      rw [harg,ih,hFperiod,zpow_add_one,actual_developedDeck_mul]
    | pred n ih =>
      intro s
      have harg : s + ((-(n : ℤ)-1 : ℤ):ℝ)*(2*Real.pi) =
          (s-2*Real.pi)+((-(n:ℤ):ℤ):ℝ)*(2*Real.pi) := by push_cast; ring
      rw [harg,ih,hinvperiod,zpow_sub_one,actual_developedDeck_mul]
  have actual_source_integer_period := actual_common_monodromy_integer_period
    sourceLift sourceLift_period
  have actual_target_integer_period := actual_common_monodromy_integer_period
    targetLift targetLift_period
  have actual_monodromy_integer_range_invariant
      (F : ℝ → H2) (hFperiod : ∀ s, F (s+2*Real.pi) = developedDeck monodromy (F s))
      (n : ℤ) : developedDeck (monodromy^n) '' Set.range F = Set.range F := by
    have hp := actual_common_monodromy_integer_period F hFperiod n
    ext z
    constructor
    · rintro ⟨_,⟨s,rfl⟩,rfl⟩
      exact ⟨s+n*(2*Real.pi),hp s⟩
    · rintro ⟨s,rfl⟩
      refine ⟨F (s-n*(2*Real.pi)),Set.mem_range_self _,?_⟩
      rw [← hp]
      congr 1
      ring
  have actual_source_stabilizer_is_common_cyclic
      (k : deck (Sigma.fst : P → A))
      (hk : developedDeck k '' Set.range sourceLift = Set.range sourceLift) :
      ∃ n : ℤ, k = monodromy^n := by
    have hmem : developedDeck k (sourceLift 0) ∈ Set.range sourceLift :=
      hk ▸ Set.mem_image_of_mem _ (Set.mem_range_self _)
    obtain ⟨s,hs⟩ := hmem
    have he : Circle.exp s = Circle.exp 0 := by
      apply a.embedded.injective
      rw [← sourceLift_projection, ← sourceLift_projection,hs,developedDeck_projection]
    obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
    refine ⟨n,actual_developedDeck_point_injective k (monodromy^n) (sourceLift 0) ?_⟩
    rw [← actual_source_integer_period,← hn]
    exact hs.symm
  have actual_target_stabilizer_is_common_cyclic
      (k : deck (Sigma.fst : P → A))
      (hk : developedDeck k '' Set.range targetLift = Set.range targetLift) :
      ∃ n : ℤ, k = monodromy^n := by
    have hmem : developedDeck k (targetLift 0) ∈ Set.range targetLift :=
      hk ▸ Set.mem_image_of_mem _ (Set.mem_range_self _)
    obtain ⟨s,hs⟩ := hmem
    have he : Circle.exp s = Circle.exp 0 := by
      apply b.embedded.injective
      rw [← targetLift_projection, ← targetLift_projection,hs,developedDeck_projection]
    obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
    refine ⟨n,actual_developedDeck_point_injective k (monodromy^n) (targetLift 0) ?_⟩
    rw [← actual_target_integer_period,← hn]
    exact hs.symm
  have actual_common_monodromy_powers_injective : Function.Injective (fun n : ℤ => monodromy^n) := by
    intro n m hnm
    change monodromy^n = monodromy^m at hnm
    have he : sourceLift (0+n*(2*Real.pi)) = sourceLift (0+m*(2*Real.pi)) := by
      rw [actual_source_integer_period,actual_source_integer_period,hnm]
    have ha := actual_sourceLift_closed_embedding.injective he
    have hnreal : (n:ℝ) = (m:ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast hnreal
  have actual_noncyclic_source_and_target_translates_disjoint
      (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ, k ≠ monodromy^n) :
      Disjoint (developedDeck k '' Set.range sourceLift) (Set.range sourceLift) ∧
      Disjoint (developedDeck k '' Set.range targetLift) (Set.range targetLift) := by
    constructor
    · rcases actual_all_source_deck_lifts_equal_or_disjoint k with he | hd
      · obtain ⟨n,hn⟩ := actual_source_stabilizer_is_common_cyclic k he
        exact False.elim (hk n hn)
      · exact hd
    · rcases actual_all_target_deck_lifts_equal_or_disjoint k with he | hd
      · obtain ⟨n,hn⟩ := actual_target_stabilizer_is_common_cyclic k he
        exact False.elim (hk n hn)
      · exact hd
  have actual_facing_seam_disjoint_all_nonzero_monodromy_powers
      (n : ℤ) (hn : n ≠ 0) :
      Disjoint (facingSeam '' Set.Icc 0 1)
        (developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)) := by
    have hp : monodromy^n ≠ 1 := by
      intro he
      have hzero : monodromy^n = monodromy^(0:ℤ) := by simpa using he
      exact hn (actual_common_monodromy_powers_injective hzero)
    exact actual_compatible_seam_stabilizer_translate_disjoint _ hp
      (actual_monodromy_integer_range_invariant sourceLift sourceLift_period n)
      (actual_monodromy_integer_range_invariant targetLift targetLift_period n)
  have actual_all_integer_seams_pairwise_disjoint
      (n m : ℤ) (hnm : n ≠ m) :
      Disjoint (developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1))
        (developedDeck (monodromy^m) '' (facingSeam '' Set.Icc 0 1)) := by
    have hdiff : m-n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnm)
    have hd := actual_facing_seam_disjoint_all_nonzero_monodromy_powers (m-n) hdiff
    have hpow : monodromy^n * monodromy^(m-n) = monodromy^m := by
      rw [← zpow_add]
      congr 1
      ring
    have himage : developedDeck (monodromy^n) ''
        (developedDeck (monodromy^(m-n)) '' (facingSeam '' Set.Icc 0 1)) =
        developedDeck (monodromy^m) '' (facingSeam '' Set.Icc 0 1) := by
      rw [Set.image_image]
      congr 1
      funext z
      rw [← actual_developedDeck_mul,hpow]
    have h := hd.image (developedDeck (monodromy^n)).injective.injOn
      (Set.subset_univ _) (Set.subset_univ _)
    rwa [himage] at h
  have actual_facing_region_all_integer_monodromy_invariant
      (n : ℤ) : developedDeck (monodromy^n) '' facingRegion = facingRegion := by
    have hF := actual_monodromy_integer_range_invariant sourceLift sourceLift_period n
    have hJ := actual_monodromy_integer_range_invariant targetLift targetLift_period n
    have hsource := actual_invariant_facing_side (developedDeck (monodromy^n))
      (Set.range sourceLift) (Set.range targetLift) sourceInner sourceOuter
      hSourceInnerOpen hSourceOuterOpen hSourceInnerConn.isPreconnected hSourceSidesDisjoint
      hSourceSidesPartition ⟨targetLift 0,Set.mem_range_self 0⟩ hTargetInSourceInner hF hJ
    have htarget := actual_invariant_facing_side (developedDeck (monodromy^n))
      (Set.range targetLift) (Set.range sourceLift) targetInner targetOuter
      hTargetInnerOpen hTargetOuterOpen hTargetInnerConn.isPreconnected hTargetSidesDisjoint
      hTargetSidesPartition ⟨sourceLift 0,Set.mem_range_self 0⟩ hSourceInTargetInner hJ hF
    change developedDeck (monodromy^n) '' (sourceInner ∩ targetInner) = sourceInner ∩ targetInner
    rw [Set.image_inter (developedDeck (monodromy^n)).injective,hsource.1,htarget.1]
  let periodicSourceArc (n : ℤ) : Set H2 := sourceLift ''
    Set.Icc (sourceParameter+n*(2*Real.pi)) (sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi))
  let periodicTargetArc (n : ℤ) : Set H2 := targetLift ''
    Set.Icc (targetParameter+n*(2*Real.pi)) (targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi))
  let periodicSeam (n : ℤ) : Set H2 := developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)
  let periodicCellBoundary (n : ℤ) : Set H2 :=
    (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1))
  have actual_integer_seam_source_intersection (n : ℤ) (z : H2)
      (hz : z ∈ periodicSeam n) (hF : z ∈ Set.range sourceLift) :
      z = sourceLift (sourceParameter+n*(2*Real.pi)) := by
    obtain ⟨u,hu,rfl⟩ := hz
    have huF : u ∈ Set.range sourceLift := by
      rw [← actual_monodromy_integer_range_invariant sourceLift sourceLift_period n] at hF
      obtain ⟨v,hv,he⟩ := hF
      exact (developedDeck (monodromy^n)).injective he ▸ hv
    have he := (hFacingBoundaryIntersections.1 u hu huF).trans hFacingSeam0
    rw [he,← hSourceParameter,← actual_source_integer_period]
  have actual_integer_seam_target_intersection (n : ℤ) (z : H2)
      (hz : z ∈ periodicSeam n) (hJ : z ∈ Set.range targetLift) :
      z = targetLift (targetParameter+n*(2*Real.pi)) := by
    obtain ⟨u,hu,rfl⟩ := hz
    have huJ : u ∈ Set.range targetLift := by
      rw [← actual_monodromy_integer_range_invariant targetLift targetLift_period n] at hJ
      obtain ⟨v,hv,he⟩ := hJ
      exact (developedDeck (monodromy^n)).injective he ▸ hv
    have he := (hFacingBoundaryIntersections.2 u hu huJ).trans hFacingSeam1
    rw [he,← hTargetParameter,← actual_target_integer_period]
  have actual_source_arc_seam_index_separation (n j : ℤ)
      (hj : j < n ∨ n+1 < j) : Disjoint (periodicSourceArc n) (periodicSeam j) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ hz
    have he := actual_integer_seam_source_intersection j _ hz (Set.mem_range_self _)
    have hsEq := actual_sourceLift_closed_embedding.injective he
    change sourceParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
      s ≤ sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
    rcases hj with hj | hj
    · have hjreal : (j:ℝ) < (n:ℝ) := by exact_mod_cast hj
      nlinarith [Real.pi_pos]
    · have hjreal : ((n+1:ℤ):ℝ) < (j:ℝ) := by exact_mod_cast hj
      nlinarith [Real.pi_pos]
  have actual_target_arc_seam_index_separation (n j : ℤ)
      (hj : j < n ∨ n+1 < j) : Disjoint (periodicTargetArc n) (periodicSeam j) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ hz
    have he := actual_integer_seam_target_intersection j _ hz (Set.mem_range_self _)
    have hsEq := actual_targetLift_closed_embedding.injective he
    change targetParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
      s ≤ targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
    rcases hj with hj | hj
    · have hjreal : (j:ℝ) < (n:ℝ) := by exact_mod_cast hj
      nlinarith [Real.pi_pos]
    · have hjreal : ((n+1:ℤ):ℝ) < (j:ℝ) := by exact_mod_cast hj
      nlinarith [Real.pi_pos]
  have actual_nonadjacent_source_arcs_disjoint (n m : ℤ) (hnm : n+1 < m) :
      Disjoint (periodicSourceArc n) (periodicSourceArc m) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
    have hst := actual_sourceLift_closed_embedding.injective he
    have hreal : ((n+1:ℤ):ℝ) < (m:ℝ) := by exact_mod_cast hnm
    change sourceParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
      s ≤ sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
    change sourceParameter+(m:ℝ)*(2*Real.pi) ≤ t ∧
      t ≤ sourceParameter+((m+1:ℤ):ℝ)*(2*Real.pi) at ht
    nlinarith [Real.pi_pos]
  have actual_nonadjacent_target_arcs_disjoint (n m : ℤ) (hnm : n+1 < m) :
      Disjoint (periodicTargetArc n) (periodicTargetArc m) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
    have hst := actual_targetLift_closed_embedding.injective he
    have hreal : ((n+1:ℤ):ℝ) < (m:ℝ) := by exact_mod_cast hnm
    change targetParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
      s ≤ targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
    change targetParameter+(m:ℝ)*(2*Real.pi) ≤ t ∧
      t ≤ targetParameter+((m+1:ℤ):ℝ)*(2*Real.pi) at ht
    nlinarith [Real.pi_pos]
  have actual_all_source_target_periodic_arcs_disjoint (n m : ℤ) :
      Disjoint (periodicSourceArc n) (periodicTargetArc m) := by
    exact actual_endpoint_lifts_disjoint.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
  have actual_nonadjacent_periodic_cell_boundaries_disjoint (n m : ℤ) (hnm : n+1 < m) :
      Disjoint (periodicCellBoundary n) (periodicCellBoundary m) := by
    have hnm' : n < m := by omega
    have hnm1 : n ≠ m := by omega
    have hnmp1 : n ≠ m+1 := by omega
    have hnp1m : n+1 ≠ m := by omega
    have hnp1mp1 : n+1 ≠ m+1 := by omega
    have h1 : Disjoint (periodicSourceArc n) (periodicCellBoundary m) := by
      exact Set.disjoint_union_right.mpr
        ⟨Set.disjoint_union_right.mpr ⟨actual_nonadjacent_source_arcs_disjoint n m hnm,
          actual_all_source_target_periodic_arcs_disjoint n m⟩,
         Set.disjoint_union_right.mpr
          ⟨actual_source_arc_seam_index_separation n m (Or.inr hnm),
           actual_source_arc_seam_index_separation n (m+1) (Or.inr (by omega))⟩⟩
    have h2 : Disjoint (periodicTargetArc n) (periodicCellBoundary m) := by
      exact Set.disjoint_union_right.mpr
        ⟨Set.disjoint_union_right.mpr ⟨(actual_all_source_target_periodic_arcs_disjoint m n).symm,
          actual_nonadjacent_target_arcs_disjoint n m hnm⟩,
         Set.disjoint_union_right.mpr
          ⟨actual_target_arc_seam_index_separation n m (Or.inr hnm),
           actual_target_arc_seam_index_separation n (m+1) (Or.inr (by omega))⟩⟩
    have h3 : Disjoint (periodicSeam n) (periodicCellBoundary m) := by
      exact Set.disjoint_union_right.mpr
        ⟨Set.disjoint_union_right.mpr
          ⟨(actual_source_arc_seam_index_separation m n (Or.inl hnm')).symm,
           (actual_target_arc_seam_index_separation m n (Or.inl hnm')).symm⟩,
         Set.disjoint_union_right.mpr
          ⟨actual_all_integer_seams_pairwise_disjoint n m hnm1,
           actual_all_integer_seams_pairwise_disjoint n (m+1) hnmp1⟩⟩
    have h4 : Disjoint (periodicSeam (n+1)) (periodicCellBoundary m) := by
      exact Set.disjoint_union_right.mpr
        ⟨Set.disjoint_union_right.mpr
          ⟨(actual_source_arc_seam_index_separation m (n+1) (Or.inl hnm)).symm,
           (actual_target_arc_seam_index_separation m (n+1) (Or.inl hnm)).symm⟩,
         Set.disjoint_union_right.mpr
          ⟨actual_all_integer_seams_pairwise_disjoint (n+1) m hnp1m,
           actual_all_integer_seams_pairwise_disjoint (n+1) (m+1) hnp1mp1⟩⟩
    exact Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨h1,h2⟩,Set.disjoint_union_left.mpr ⟨h3,h4⟩⟩
  have actual_integer_periodic_arc_translate
      (F : ℝ → H2) (hFperiod : ∀ s, F (s+2*Real.pi) = developedDeck monodromy (F s))
      (p : ℝ) (n : ℤ) :
      developedDeck (monodromy^n) '' (F '' Set.Icc p (p+2*Real.pi)) =
        F '' Set.Icc (p+n*(2*Real.pi)) (p+((n+1:ℤ):ℝ)*(2*Real.pi)) := by
    have hp := actual_common_monodromy_integer_period F hFperiod n
    ext z
    constructor
    · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
      refine ⟨s+n*(2*Real.pi),?_,hp s⟩
      push_cast
      constructor <;> linarith [hs.1,hs.2]
    · rintro ⟨s,hs,rfl⟩
      refine ⟨F (s-n*(2*Real.pi)),⟨s-n*(2*Real.pi),?_,rfl⟩,?_⟩
      · push_cast at hs
        constructor <;> linarith [hs.1,hs.2]
      · rw [← hp]
        congr 1
        ring
  have hPeriodicSourceArcZero : periodicSourceArc 0 = sourceArc := by
    simp [periodicSourceArc,sourceArc]
  have hPeriodicTargetArcZero : periodicTargetArc 0 = targetArc := by
    simp [periodicTargetArc,targetArc]
  have hPeriodicSeamZero : periodicSeam 0 = firstSeam := by
    ext z
    simp only [periodicSeam,zpow_zero,Set.mem_image,actual_developedDeck_one,firstSeam]
    simp
  have hPeriodicSeamOne : periodicSeam 1 = secondSeam := by
    simp only [periodicSeam,zpow_one,secondSeam,firstSeam]
  have hFundamentalBoundaryCellZero : fundamentalBoundary = planeCoordinate '' periodicCellBoundary 0 := by
    change fundamentalBoundary = planeCoordinate ''
      ((periodicSourceArc 0 ∪ periodicTargetArc 0) ∪ (periodicSeam 0 ∪ periodicSeam 1))
    rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,
      hPeriodicSeamZero,hPeriodicSeamOne,Set.image_union,Set.image_union,Set.image_union]
    change (planeCoordinate '' sourceArc ∪ planeCoordinate '' secondSeam) ∪
      (planeCoordinate '' firstSeam ∪ planeCoordinate '' targetArc) = _
    ac_rfl
  have hPeriodicCellTranslate (n : ℤ) :
      developedDeck (monodromy^n) '' periodicCellBoundary 0 = periodicCellBoundary n := by
    have hsource := actual_integer_periodic_arc_translate sourceLift sourceLift_period sourceParameter n
    have htarget := actual_integer_periodic_arc_translate targetLift targetLift_period targetParameter n
    have hseams (j : ℤ) : developedDeck (monodromy^n) '' periodicSeam j = periodicSeam (n+j) := by
      change developedDeck (monodromy^n) ''
        (developedDeck (monodromy^j) '' (facingSeam '' Set.Icc 0 1)) =
        developedDeck (monodromy^(n+j)) '' (facingSeam '' Set.Icc 0 1)
      rw [Set.image_image]
      change (fun z => developedDeck (monodromy^n) (developedDeck (monodromy^j) z)) ''
        (facingSeam '' Set.Icc 0 1) = _
      have he : (fun z => developedDeck (monodromy^n) (developedDeck (monodromy^j) z)) =
          developedDeck (monodromy^(n+j)) := by
        funext z
        rw [← actual_developedDeck_mul,← zpow_add]
      rw [he]
    change developedDeck (monodromy^n) ''
      ((periodicSourceArc 0 ∪ periodicTargetArc 0) ∪ (periodicSeam 0 ∪ periodicSeam 1)) =
      (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1))
    rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,
      Set.image_union,Set.image_union,Set.image_union,hsource,htarget,hseams,hseams]
    simp only [add_zero]
    rfl
  let periodicPlaneDeck (n : ℤ) : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (planeCoordinate.symm.trans (developedDeck (monodromy^n))).trans planeCoordinate
  have hPeriodicPlaneBoundary (n : ℤ) :
      periodicPlaneDeck n '' fundamentalBoundary = planeCoordinate '' periodicCellBoundary n := by
    rw [hFundamentalBoundaryCellZero,Set.image_image]
    have he : (fun z => periodicPlaneDeck n (planeCoordinate z)) =
        fun z => planeCoordinate (developedDeck (monodromy^n) z) := by
      funext z
      simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    rw [he,← Set.image_image,hPeriodicCellTranslate]
  have actual_all_periodic_boundaries_jordan (n : ℤ) :
      Schoenflies.IsJordanCurve (planeCoordinate '' periodicCellBoundary n) := by
    rw [← hPeriodicPlaneBoundary]
    exact CurveComplex.jordan_curve_homeomorph_image actual_fundamental_boundary_jordan (periodicPlaneDeck n)
  have actual_all_periodic_cell_insides_in_facing_region (n : ℤ) :
      Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ⊆ planeCoordinate '' facingRegion := by
    rw [← hPeriodicPlaneBoundary,← CurveComplex.jordan_inside_homeomorph_image]
    rintro z ⟨y,hy,rfl⟩
    obtain ⟨u,hu,rfl⟩ := actual_fundamental_cell_inside_facing_region hy
    refine ⟨developedDeck (monodromy^n) u,?_,?_⟩
    · exact actual_facing_region_all_integer_monodromy_invariant n ▸ Set.mem_image_of_mem _ hu
    · simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
  have actual_each_periodic_cell_boundary_has_point_outside_facing_region (n : ℤ) :
      ∃ x : Schoenflies.Plane, x ∈ planeCoordinate '' periodicCellBoundary n ∧
        x ∉ planeCoordinate '' facingRegion := by
    let p := sourceParameter+n*(2*Real.pi)
    have hp : sourceLift p ∈ periodicSourceArc n := by
      refine ⟨p,⟨le_rfl,?_⟩,rfl⟩
      dsimp [p]
      push_cast
      linarith [Real.pi_pos]
    refine ⟨planeCoordinate (sourceLift p),
      Set.mem_image_of_mem _ (Or.inl (Or.inl hp)),?_⟩
    rintro ⟨u,hu,he⟩
    have he' := planeCoordinate.injective he
    have hinner : sourceLift p ∈ sourceInner := (he' ▸ hu).1
    have hcompl : sourceLift p ∈ (Set.range sourceLift)ᶜ := by
      rw [← hSourceSidesPartition]
      exact Or.inl hinner
    exact hcompl (Set.mem_range_self p)
  have actual_nonadjacent_closed_periodic_jordan_cells_disjoint (n m : ℤ) (hnm : n+1 < m) :
      Disjoint (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
          (planeCoordinate '' periodicCellBoundary n))
        (Schoenflies.inside (planeCoordinate '' periodicCellBoundary m) ∪
          (planeCoordinate '' periodicCellBoundary m)) := by
    have hboundaries := (actual_nonadjacent_periodic_cell_boundaries_disjoint n m hnm).image
      planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
    have no_nesting (i j : ℤ)
        (hd : Disjoint (planeCoordinate '' periodicCellBoundary i) (planeCoordinate '' periodicCellBoundary j)) :
        ¬ (Schoenflies.inside (planeCoordinate '' periodicCellBoundary i) ∪
          (planeCoordinate '' periodicCellBoundary i) ⊆
          Schoenflies.inside (planeCoordinate '' periodicCellBoundary j) ∪
          (planeCoordinate '' periodicCellBoundary j)) := by
      intro hnest
      obtain ⟨x,hx,hxNot⟩ := actual_each_periodic_cell_boundary_has_point_outside_facing_region i
      rcases hnest (Or.inr hx) with hinside | hboundary
      · exact hxNot (actual_all_periodic_cell_insides_in_facing_region j hinside)
      · exact Set.disjoint_left.mp hd hx hboundary
    rcases CurveComplex.jordan_curve_closed_regions_disjoint_or_nested
      (actual_all_periodic_boundaries_jordan n) (actual_all_periodic_boundaries_jordan m) hboundaries with
      hd | hnested | hnested
    · exact hd
    · exact False.elim (no_nesting n m hboundaries hnested)
    · exact False.elim (no_nesting m n hboundaries.symm hnested)
  obtain ⟨fundamentalBoundaryHomeomorph⟩ :=
    Schoenflies.IsJordanCurve.modelCurve_homeomorph actual_fundamental_boundary_jordan
  obtain ⟨fundamentalPlaneHomeomorph,hFundamentalPlaneBoundary⟩ :=
    Schoenflies.jordan_schoenflies_of_homeomorph Schoenflies.isJordanCurve_modelCurve
      actual_fundamental_boundary_jordan fundamentalBoundaryHomeomorph
  have hFundamentalPlaneBoundaryImage : fundamentalPlaneHomeomorph '' Schoenflies.modelCurve = fundamentalBoundary := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hFundamentalPlaneBoundary ⟨x,hx⟩]
      exact (fundamentalBoundaryHomeomorph ⟨x,hx⟩).property
    · intro hz
      let w := fundamentalBoundaryHomeomorph.symm ⟨z,hz⟩
      refine ⟨w.val,w.property,?_⟩
      rw [hFundamentalPlaneBoundary w]
      exact congrArg Subtype.val (fundamentalBoundaryHomeomorph.apply_symm_apply ⟨z,hz⟩)
  let actualFilledFundamentalDisk : C(Schoenflies.Plane.closedSquare 0 1,Schoenflies.Plane) :=
    ⟨fun x => fundamentalPlaneHomeomorph x,
      fundamentalPlaneHomeomorph.continuous.comp continuous_subtype_val⟩
  have actual_filled_fundamental_disk_embedding : Topology.IsEmbedding actualFilledFundamentalDisk :=
    fundamentalPlaneHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have actual_filled_fundamental_disk_range :
      Set.range actualFilledFundamentalDisk = fundamentalBoundary ∪ Schoenflies.inside fundamentalBoundary := by
    have hrange : Set.range actualFilledFundamentalDisk =
        fundamentalPlaneHomeomorph '' Schoenflies.Plane.closedSquare 0 1 := by
      ext z
      constructor
      · rintro ⟨x,rfl⟩; exact ⟨x,x.property,rfl⟩
      · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
    rw [hrange,← Schoenflies.modelCurve_union_inside,Set.image_union,
      CurveComplex.jordan_inside_homeomorph_image,hFundamentalPlaneBoundaryImage]
  have actual_filled_fundamental_disk_interior_in_facing_region :
      actualFilledFundamentalDisk '' {x | (x : Schoenflies.Plane) ∈ Schoenflies.Plane.openSquare 0 1} ⊆
        planeCoordinate '' facingRegion := by
    rintro z ⟨x,hx,rfl⟩
    apply actual_fundamental_cell_inside_facing_region
    rw [← hFundamentalPlaneBoundaryImage,← CurveComplex.jordan_inside_homeomorph_image]
    refine ⟨x,?_,rfl⟩
    rw [Schoenflies.inside_modelCurve]
    exact hx
  have actual_integer_source_corner_on_seam (n : ℤ) :
      sourceLift (sourceParameter+n*(2*Real.pi)) ∈ periodicSeam n := by
    change sourceLift (sourceParameter+n*(2*Real.pi)) ∈
      developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)
    rw [actual_source_integer_period,hSourceParameter]
    exact Set.mem_image_of_mem _ ⟨0,⟨le_rfl,zero_le_one⟩,hFacingSeam0⟩
  have actual_integer_target_corner_on_seam (n : ℤ) :
      targetLift (targetParameter+n*(2*Real.pi)) ∈ periodicSeam n := by
    change targetLift (targetParameter+n*(2*Real.pi)) ∈
      developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)
    rw [actual_target_integer_period,hTargetParameter]
    exact Set.mem_image_of_mem _ ⟨1,⟨zero_le_one,le_rfl⟩,hFacingSeam1⟩
  have actual_adjacent_source_arc_intersection (n : ℤ) (z : H2)
      (hz : z ∈ periodicSourceArc n) (hz' : z ∈ periodicSourceArc (n+1)) :
      z = sourceLift (sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi)) := by
    obtain ⟨s,hs,rfl⟩ := hz
    obtain ⟨t,ht,he⟩ := hz'
    have hts := actual_sourceLift_closed_embedding.injective he
    have hsEnd : s = sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi) :=
      le_antisymm hs.2 (hts ▸ ht.1)
    rw [hsEnd]
  have actual_adjacent_target_arc_intersection (n : ℤ) (z : H2)
      (hz : z ∈ periodicTargetArc n) (hz' : z ∈ periodicTargetArc (n+1)) :
      z = targetLift (targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi)) := by
    obtain ⟨s,hs,rfl⟩ := hz
    obtain ⟨t,ht,he⟩ := hz'
    have hts := actual_targetLift_closed_embedding.injective he
    have hsEnd : s = targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi) :=
      le_antisymm hs.2 (hts ▸ ht.1)
    rw [hsEnd]
  have actual_adjacent_periodic_cell_boundaries_intersection (n : ℤ) :
      periodicCellBoundary n ∩ periodicCellBoundary (n+1) = periodicSeam (n+1) := by
    ext z
    constructor
    · intro hz
      rcases hz.1 with (hS | hT) | (hE | hShared)
      · rcases hz.2 with (hS' | hT') | (hShared' | hFar)
        · rw [actual_adjacent_source_arc_intersection n z hS hS']
          exact actual_integer_source_corner_on_seam (n+1)
        · exact False.elim (Set.disjoint_left.mp
            (actual_all_source_target_periodic_arcs_disjoint n (n+1)) hS hT')
        · exact hShared'
        · exact False.elim (Set.disjoint_left.mp
            (actual_source_arc_seam_index_separation n (n+1+1) (Or.inr (by omega))) hS hFar)
      · rcases hz.2 with (hS' | hT') | (hShared' | hFar)
        · exact False.elim (Set.disjoint_left.mp
            (actual_all_source_target_periodic_arcs_disjoint (n+1) n).symm hT hS')
        · rw [actual_adjacent_target_arc_intersection n z hT hT']
          exact actual_integer_target_corner_on_seam (n+1)
        · exact hShared'
        · exact False.elim (Set.disjoint_left.mp
            (actual_target_arc_seam_index_separation n (n+1+1) (Or.inr (by omega))) hT hFar)
      · rcases hz.2 with (hS' | hT') | (hShared' | hFar)
        · exact False.elim (Set.disjoint_left.mp
            (actual_source_arc_seam_index_separation (n+1) n (Or.inl (by omega))).symm hE hS')
        · exact False.elim (Set.disjoint_left.mp
            (actual_target_arc_seam_index_separation (n+1) n (Or.inl (by omega))).symm hE hT')
        · exact False.elim (Set.disjoint_left.mp
            (actual_all_integer_seams_pairwise_disjoint n (n+1) (by omega)) hE hShared')
        · exact False.elim (Set.disjoint_left.mp
            (actual_all_integer_seams_pairwise_disjoint n (n+1+1) (by omega)) hE hFar)
      · exact hShared
    · intro hz
      exact ⟨Or.inr (Or.inr hz),Or.inr (Or.inl hz)⟩
  let periodicComplement (n j : ℤ) : Set H2 :=
    (periodicSourceArc n ∪ periodicSeam (n+j)) ∪ periodicTargetArc n
  let sourceCorner (n : ℤ) : Schoenflies.Plane := planeCoordinate
    (sourceLift (sourceParameter+n*(2*Real.pi)))
  let targetCorner (n : ℤ) : Schoenflies.Plane := planeCoordinate
    (targetLift (targetParameter+n*(2*Real.pi)))
  have hBaseLeftComplementArc : Schoenflies.IsArcBetween
      ((planeCoordinate '' sourceArc ∪ planeCoordinate '' secondSeam) ∪ planeCoordinate '' targetArc)
      (planeCoordinate facingSeamSource) (planeCoordinate facingSeamTarget) := by
    apply (hSourceArcPlane.concatenate hSecondSeamPlane hSourceSecondMeet).concatenate hTargetArcPlane.reverse
    intro z hz hzQ
    rcases hz with hzS | hzR
    · exact False.elim (Set.disjoint_left.mp hSourceTargetArcDisjoint hzS hzQ)
    · exact hSecondTargetMeet z hzR hzQ
  have hBaseRightComplementArc : Schoenflies.IsArcBetween
      ((planeCoordinate '' sourceArc ∪ planeCoordinate '' firstSeam) ∪ planeCoordinate '' targetArc)
      (planeCoordinate (developedDeck monodromy facingSeamSource))
      (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
    have hfirst := hSourceArcPlane.reverse.concatenate hFirstSeamPlane hSourceFirstMeet
    apply hfirst.concatenate hTargetArcPlane
    intro z hz hzQ
    rcases hz with hzS | hzE
    · exact False.elim (Set.disjoint_left.mp hSourceTargetArcDisjoint hzS hzQ)
    · exact hFirstTargetMeet z hzE hzQ
  have actual_periodic_complement_translate (n j : ℤ) :
      developedDeck (monodromy^n) '' periodicComplement 0 j = periodicComplement n j := by
    have hsource := actual_integer_periodic_arc_translate sourceLift sourceLift_period sourceParameter n
    have htarget := actual_integer_periodic_arc_translate targetLift targetLift_period targetParameter n
    have hseam : developedDeck (monodromy^n) '' periodicSeam j = periodicSeam (n+j) := by
      change developedDeck (monodromy^n) ''
        (developedDeck (monodromy^j) '' (facingSeam '' Set.Icc 0 1)) =
        developedDeck (monodromy^(n+j)) '' (facingSeam '' Set.Icc 0 1)
      rw [Set.image_image]
      congr 1
      funext z
      rw [← actual_developedDeck_mul,← zpow_add]
    change developedDeck (monodromy^n) ''
      ((periodicSourceArc 0 ∪ periodicSeam (0+j)) ∪ periodicTargetArc 0) = _
    rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,zero_add,Set.image_union,
      Set.image_union,hsource,htarget,hseam]
  have actual_periodic_complement_plane_translate (n j : ℤ) :
      periodicPlaneDeck n '' (planeCoordinate '' periodicComplement 0 j) =
        planeCoordinate '' periodicComplement n j := by
    rw [Set.image_image]
    have he : (fun z => periodicPlaneDeck n (planeCoordinate z)) =
        fun z => planeCoordinate (developedDeck (monodromy^n) z) := by
      funext z
      simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    rw [he,← Set.image_image,actual_periodic_complement_translate]
  have hPlaneSourceCorner (n : ℤ) :
      periodicPlaneDeck n (planeCoordinate facingSeamSource) = sourceCorner n := by
    simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    rw [← hSourceParameter,← actual_source_integer_period]
  have hPlaneTargetCorner (n : ℤ) :
      periodicPlaneDeck n (planeCoordinate facingSeamTarget) = targetCorner n := by
    simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    rw [← hTargetParameter,← actual_target_integer_period]
  have hPlaneFarSourceCorner (n : ℤ) :
      periodicPlaneDeck n (planeCoordinate (developedDeck monodromy facingSeamSource)) = sourceCorner (n+1) := by
    simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    rw [← actual_developedDeck_mul,← zpow_add_one]
    simpa only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      using (hPlaneSourceCorner (n+1))
  have hPlaneFarTargetCorner (n : ℤ) :
      periodicPlaneDeck n (planeCoordinate (developedDeck monodromy facingSeamTarget)) = targetCorner (n+1) := by
    simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    rw [← actual_developedDeck_mul,← zpow_add_one]
    simpa only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      using (hPlaneTargetCorner (n+1))
  have actual_left_periodic_complement_arc (n : ℤ) : Schoenflies.IsArcBetween
      (planeCoordinate '' periodicComplement n 1) (sourceCorner n) (targetCorner n) := by
    have hbase : Schoenflies.IsArcBetween (planeCoordinate '' periodicComplement 0 1)
        (planeCoordinate facingSeamSource) (planeCoordinate facingSeamTarget) := by
      change Schoenflies.IsArcBetween
        (planeCoordinate '' ((periodicSourceArc 0 ∪ periodicSeam (0+1)) ∪ periodicTargetArc 0)) _ _
      simp only [zero_add]
      rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,hPeriodicSeamOne,Set.image_union,Set.image_union]
      exact hBaseLeftComplementArc
    have h := hbase.image_of_injOn (Set.subset_univ _)
      (periodicPlaneDeck n).continuous.continuousOn (periodicPlaneDeck n).injective.injOn
    rwa [actual_periodic_complement_plane_translate,hPlaneSourceCorner,hPlaneTargetCorner] at h
  have actual_right_periodic_complement_arc (n : ℤ) : Schoenflies.IsArcBetween
      (planeCoordinate '' periodicComplement n 0) (sourceCorner (n+1)) (targetCorner (n+1)) := by
    have hbase : Schoenflies.IsArcBetween (planeCoordinate '' periodicComplement 0 0)
        (planeCoordinate (developedDeck monodromy facingSeamSource))
        (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
      change Schoenflies.IsArcBetween
        (planeCoordinate '' ((periodicSourceArc 0 ∪ periodicSeam (0+0)) ∪ periodicTargetArc 0)) _ _
      simp only [add_zero]
      rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,hPeriodicSeamZero,Set.image_union,Set.image_union]
      exact hBaseRightComplementArc
    have h := hbase.image_of_injOn (Set.subset_univ _)
      (periodicPlaneDeck n).continuous.continuousOn (periodicPlaneDeck n).injective.injOn
    rwa [actual_periodic_complement_plane_translate,hPlaneFarSourceCorner,hPlaneFarTargetCorner] at h
  have actual_arc_on_outside_from_one_excluded_inside_point
      {C A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
      (hC : Schoenflies.IsSeparating C) (hA : Schoenflies.IsArcBetween A p q)
      (hend : p ∈ C ∧ q ∈ C)
      (hmeet : ∀ z ∈ A, z ∈ C → z = p ∨ z = q)
      (hpoint : ∃ z, z ∈ A \ ({p,q} : Set Schoenflies.Plane) ∧ z ∉ Schoenflies.inside C) :
      A ⊆ Schoenflies.outside C ∪ C := by
    have hcover : A \ ({p,q} : Set Schoenflies.Plane) ⊆
        Schoenflies.inside C ∪ Schoenflies.outside C := by
      rw [Schoenflies.inside_union_outside]
      intro z hz hzC
      rcases hmeet z hz.1 hzC with he | he
      · exact hz.2 (by simp [he])
      · exact hz.2 (by simp [he])
    have hout : A \ ({p,q} : Set Schoenflies.Plane) ⊆ Schoenflies.outside C := by
      rcases hA.isPreconnected_diff.subset_or_subset hC.isOpen_inside hC.isOpen_outside
        Schoenflies.disjoint_inside_outside hcover with hin | hout
      · obtain ⟨z,hz,hzNot⟩ := hpoint
        exact False.elim (hzNot (hin hz))
      · exact hout
    intro z hz
    by_cases hp : z = p
    · exact Or.inr (hp ▸ hend.1)
    by_cases hq : z = q
    · exact Or.inr (hq ▸ hend.2)
    exact Or.inl (hout ⟨hz,by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; exact fun h => h.elim hp hq⟩)
  have actual_jordan_insides_disjoint_from_closed_outside_boundary
      {C K : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
      (hK : Schoenflies.IsSeparating K)
      (hKC : K ⊆ Schoenflies.outside C ∪ C)
      (hpoint : (C ∩ Schoenflies.outside K).Nonempty) :
      Disjoint (Schoenflies.inside C) (Schoenflies.inside K) := by
    have hcover : Schoenflies.inside C ⊆ Schoenflies.inside K ∪ Schoenflies.outside K := by
      rw [Schoenflies.inside_union_outside]
      intro z hz hzK
      rcases hKC hzK with hout | hboundary
      · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz hout
      · exact Schoenflies.inside_subset_compl hz hboundary
    have hout : Schoenflies.inside C ⊆ Schoenflies.outside K := by
      rcases hC.isConnected_inside.isPreconnected.subset_or_subset hK.isOpen_inside hK.isOpen_outside
        Schoenflies.disjoint_inside_outside hcover with hin | hout
      · obtain ⟨z,hzC,hzOut⟩ := hpoint
        have hzClosure : z ∈ closure (Schoenflies.inside C) := by
          apply frontier_subset_closure
          rw [hC.frontier_inside]
          exact hzC
        have hzKClosure := closure_mono hin hzClosure
        have hinter := hK.isOpen_outside.inter_closure ⟨hzOut,hzKClosure⟩
        obtain ⟨w,hwOut,hwIn⟩ := Set.Nonempty.of_closure ⟨z,hinter⟩
        exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hwIn hwOut)
      · exact hout
    exact Schoenflies.disjoint_inside_outside.symm.mono hout (Set.Subset.refl _)
  have actual_periodic_complement_source_midpoint (n j k : ℤ) (hk : k = n ∨ k = n+1) :
      ∃ x, x ∈ (planeCoordinate '' periodicComplement n j) \ ({sourceCorner k,targetCorner k} : Set Schoenflies.Plane) ∧
        ∀ i : ℤ, x ∉ Schoenflies.inside (planeCoordinate '' periodicCellBoundary i) := by
    let s := sourceParameter+(n:ℝ)*(2*Real.pi)+Real.pi
    have hsArc : sourceLift s ∈ periodicSourceArc n := by
      refine ⟨s,⟨?_,?_⟩,rfl⟩
      · dsimp [s]; linarith [Real.pi_pos]
      · dsimp [s]; push_cast; linarith [Real.pi_pos]
    have hxComplement : planeCoordinate (sourceLift s) ∈ planeCoordinate '' periodicComplement n j :=
      Set.mem_image_of_mem _ (Or.inl (Or.inl hsArc))
    have hneSource : planeCoordinate (sourceLift s) ≠ sourceCorner k := by
      intro he
      change planeCoordinate (sourceLift s) = planeCoordinate
        (sourceLift (sourceParameter+k*(2*Real.pi))) at he
      have hsEq := actual_sourceLift_closed_embedding.injective (planeCoordinate.injective he)
      rcases hk with rfl | rfl
      · dsimp [s] at hsEq; linarith [Real.pi_pos]
      · dsimp [s] at hsEq; push_cast at hsEq; linarith [Real.pi_pos]
    have hneTarget : planeCoordinate (sourceLift s) ≠ targetCorner k := by
      intro he
      change planeCoordinate (sourceLift s) = planeCoordinate
        (targetLift (targetParameter+k*(2*Real.pi))) at he
      have hst := planeCoordinate.injective he
      exact Set.disjoint_left.mp actual_endpoint_lifts_disjoint (Set.mem_range_self s)
        (hst.symm ▸ Set.mem_range_self (targetParameter+k*(2*Real.pi)))
    refine ⟨planeCoordinate (sourceLift s),⟨hxComplement,?_⟩,?_⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      exact not_or.mpr ⟨hneSource,hneTarget⟩
    · intro i hxInside
      obtain ⟨u,hu,he⟩ := actual_all_periodic_cell_insides_in_facing_region i hxInside
      have he' := planeCoordinate.injective he
      have hinner : sourceLift s ∈ sourceInner := (he' ▸ hu).1
      have hcompl : sourceLift s ∈ (Set.range sourceLift)ᶜ := by
        rw [← hSourceSidesPartition]
        exact Or.inl hinner
      exact hcompl (Set.mem_range_self s)
  have actual_complement_subset_cell (n j : ℤ) (hj : j = 0 ∨ j = 1) :
      periodicComplement n j ⊆ periodicCellBoundary n := by
    intro z hz
    rcases hz with (hS | hE) | hT
    · exact Or.inl (Or.inl hS)
    · rcases hj with rfl | rfl
      · exact Or.inr (Or.inl (by simpa only [add_zero] using hE))
      · exact Or.inr (Or.inr hE)
    · exact Or.inl (Or.inr hT)
  have actual_left_complement_meets_previous_at_endpoints (n : ℤ)
      (z : Schoenflies.Plane) (hz : z ∈ planeCoordinate '' periodicComplement n 1)
      (hzPrev : z ∈ planeCoordinate '' periodicCellBoundary (n-1)) :
      z = sourceCorner n ∨ z = targetCorner n := by
    obtain ⟨u,hu,heU⟩ := hz
    obtain ⟨v,hv,heV⟩ := hzPrev
    have huPrev : u ∈ periodicCellBoundary (n-1) := planeCoordinate.injective (heV.trans heU.symm) ▸ hv
    have huOwn := actual_complement_subset_cell n 1 (Or.inr rfl) hu
    have hidx : n-1+1 = n := by ring
    have hinter := actual_adjacent_periodic_cell_boundaries_intersection (n-1)
    rw [hidx] at hinter
    have huSeam : u ∈ periodicSeam n := by
      rw [← hinter]
      exact ⟨huPrev,huOwn⟩
    rcases hu with (hS | hFar) | hT
    · have he := actual_integer_seam_source_intersection n u huSeam (Set.image_subset_range _ _ hS)
      exact Or.inl (heU.symm.trans (congrArg planeCoordinate he))
    · exact False.elim (Set.disjoint_left.mp
        (actual_all_integer_seams_pairwise_disjoint (n+1) n (by omega)) hFar huSeam)
    · have he := actual_integer_seam_target_intersection n u huSeam (Set.image_subset_range _ _ hT)
      exact Or.inr (heU.symm.trans (congrArg planeCoordinate he))
  have actual_right_complement_meets_next_at_endpoints (n : ℤ)
      (z : Schoenflies.Plane) (hz : z ∈ planeCoordinate '' periodicComplement n 0)
      (hzNext : z ∈ planeCoordinate '' periodicCellBoundary (n+1)) :
      z = sourceCorner (n+1) ∨ z = targetCorner (n+1) := by
    obtain ⟨u,hu,heU⟩ := hz
    obtain ⟨v,hv,heV⟩ := hzNext
    have huNext : u ∈ periodicCellBoundary (n+1) := planeCoordinate.injective (heV.trans heU.symm) ▸ hv
    have huOwn := actual_complement_subset_cell n 0 (Or.inl rfl) hu
    have huSeam : u ∈ periodicSeam (n+1) := by
      rw [← actual_adjacent_periodic_cell_boundaries_intersection n]
      exact ⟨huOwn,huNext⟩
    rcases hu with (hS | hFirst) | hT
    · have he := actual_integer_seam_source_intersection (n+1) u huSeam (Set.image_subset_range _ _ hS)
      exact Or.inl (heU.symm.trans (congrArg planeCoordinate he))
    · have hFirst' : u ∈ periodicSeam n := by simpa only [add_zero] using hFirst
      exact False.elim (Set.disjoint_left.mp
        (actual_all_integer_seams_pairwise_disjoint n (n+1) (by omega)) hFirst' huSeam)
    · have he := actual_integer_seam_target_intersection (n+1) u huSeam (Set.image_subset_range _ _ hT)
      exact Or.inr (heU.symm.trans (congrArg planeCoordinate he))
  have actual_left_complement_outside_previous (n : ℤ) :
      planeCoordinate '' periodicComplement n 1 ⊆
        Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n-1)) ∪
          (planeCoordinate '' periodicCellBoundary (n-1)) := by
    have hSeamSubset : periodicSeam n ⊆ periodicCellBoundary (n-1) := by
      intro z hz
      refine Or.inr (Or.inr ?_)
      have hidx : n-1+1 = n := by ring
      rw [hidx]
      exact hz
    have hend : sourceCorner n ∈ planeCoordinate '' periodicCellBoundary (n-1) ∧
        targetCorner n ∈ planeCoordinate '' periodicCellBoundary (n-1) :=
      ⟨Set.mem_image_of_mem _ (hSeamSubset (actual_integer_source_corner_on_seam n)),
       Set.mem_image_of_mem _ (hSeamSubset (actual_integer_target_corner_on_seam n))⟩
    obtain ⟨x,hx,hxNot⟩ := actual_periodic_complement_source_midpoint n 1 n (Or.inl rfl)
    exact actual_arc_on_outside_from_one_excluded_inside_point
      (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan (n-1)))
      (actual_left_periodic_complement_arc n) hend
      (actual_left_complement_meets_previous_at_endpoints n) ⟨x,hx,hxNot (n-1)⟩
  have actual_right_complement_outside_next (n : ℤ) :
      planeCoordinate '' periodicComplement n 0 ⊆
        Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n+1)) ∪
          (planeCoordinate '' periodicCellBoundary (n+1)) := by
    have hSeamSubset : periodicSeam (n+1) ⊆ periodicCellBoundary (n+1) := by
      intro z hz
      exact Or.inr (Or.inl hz)
    have hend : sourceCorner (n+1) ∈ planeCoordinate '' periodicCellBoundary (n+1) ∧
        targetCorner (n+1) ∈ planeCoordinate '' periodicCellBoundary (n+1) :=
      ⟨Set.mem_image_of_mem _ (hSeamSubset (actual_integer_source_corner_on_seam (n+1))),
       Set.mem_image_of_mem _ (hSeamSubset (actual_integer_target_corner_on_seam (n+1)))⟩
    obtain ⟨x,hx,hxNot⟩ := actual_periodic_complement_source_midpoint n 0 (n+1) (Or.inr rfl)
    exact actual_arc_on_outside_from_one_excluded_inside_point
      (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan (n+1)))
      (actual_right_periodic_complement_arc n) hend
      (actual_right_complement_meets_next_at_endpoints n) ⟨x,hx,hxNot (n+1)⟩
  have actual_cell_boundary_left_complement_union_seam (n : ℤ) :
      periodicCellBoundary n = periodicComplement n 1 ∪ periodicSeam n := by
    change (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1)) =
      ((periodicSourceArc n ∪ periodicSeam (n+1)) ∪ periodicTargetArc n) ∪ periodicSeam n
    ac_rfl
  have actual_cell_boundary_right_complement_union_seam (n : ℤ) :
      periodicCellBoundary n = periodicComplement n 0 ∪ periodicSeam (n+1) := by
    change (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1)) =
      ((periodicSourceArc n ∪ periodicSeam (n+0)) ∪ periodicTargetArc n) ∪ periodicSeam (n+1)
    simp only [add_zero]
    ac_rfl
  have actual_next_boundary_outside_previous_closed (n : ℤ) :
      planeCoordinate '' periodicCellBoundary (n+1) ⊆
        Schoenflies.outside (planeCoordinate '' periodicCellBoundary n) ∪
          (planeCoordinate '' periodicCellBoundary n) := by
    rw [actual_cell_boundary_left_complement_union_seam,Set.image_union]
    apply Set.union_subset
    · have h := actual_left_complement_outside_previous (n+1)
      have hi : n+1-1 = n := by ring
      rwa [hi] at h
    · rintro z ⟨u,hu,rfl⟩
      exact Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inr hu)))
  have actual_previous_boundary_point_outside_next (n : ℤ) :
      ((planeCoordinate '' periodicCellBoundary n) ∩
        Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n+1))).Nonempty := by
    obtain ⟨x,hx,hxNot⟩ := actual_periodic_complement_source_midpoint n 0 (n+1) (Or.inr rfl)
    have hxCell : x ∈ planeCoordinate '' periodicCellBoundary n :=
      Set.image_mono (actual_complement_subset_cell n 0 (Or.inl rfl)) hx.1
    have hxNotNext : x ∉ planeCoordinate '' periodicCellBoundary (n+1) := by
      intro hxNext
      rcases actual_right_complement_meets_next_at_endpoints n x hx.1 hxNext with he | he
      · exact hx.2 (by simp [he])
      · exact hx.2 (by simp [he])
    rcases actual_right_complement_outside_next n hx.1 with hxOut | hxBoundary
    · exact ⟨x,hxCell,hxOut⟩
    · exact False.elim (hxNotNext hxBoundary)
  have actual_adjacent_periodic_jordan_cell_interiors_disjoint (n : ℤ) :
      Disjoint (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n))
        (Schoenflies.inside (planeCoordinate '' periodicCellBoundary (n+1))) := by
    exact actual_jordan_insides_disjoint_from_closed_outside_boundary
      (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan n))
      (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan (n+1)))
      (actual_next_boundary_outside_previous_closed n)
      (actual_previous_boundary_point_outside_next n)
  have actual_all_distinct_periodic_jordan_cell_interiors_disjoint (n m : ℤ) (hnm : n ≠ m) :
      Disjoint (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n))
        (Schoenflies.inside (planeCoordinate '' periodicCellBoundary m)) := by
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · by_cases hnext : m = n+1
      · rw [hnext]
        exact actual_adjacent_periodic_jordan_cell_interiors_disjoint n
      · have hgap : n+1 < m := by omega
        exact (actual_nonadjacent_closed_periodic_jordan_cells_disjoint n m hgap).mono
          Set.subset_union_left Set.subset_union_left
    · by_cases hnext : n = m+1
      · rw [hnext]
        exact (actual_adjacent_periodic_jordan_cell_interiors_disjoint m).symm
      · have hgap : m+1 < n := by omega
        exact (actual_nonadjacent_closed_periodic_jordan_cells_disjoint m n hgap).symm.mono
          Set.subset_union_left Set.subset_union_left
  let markedPeriodicDisk (n : ℤ) (uv : Interval × Interval) : H2 :=
    developedDeck (monodromy^n) (planeCoordinate.symm (markedFundamentalDisk uv))
  have actual_marked_periodic_disk_embedding (n : ℤ) : Topology.IsEmbedding (markedPeriodicDisk n) :=
    (developedDeck (monodromy^n)).isEmbedding.comp
      (planeCoordinate.symm.isEmbedding.comp hMarkedFundamentalDiskEmbedding)
  have actual_marked_periodic_disk_neighbor_gluing (n : ℤ) (v : Interval) :
      markedPeriodicDisk n (1,v) = markedPeriodicDisk (n+1) (0,v) := by
    simp only [markedPeriodicDisk,actual_marked_fundamental_seam_compatibility,
      Homeomorph.symm_apply_apply]
    rw [← actual_developedDeck_mul,← zpow_add_one]
  have actual_marked_periodic_disk_monodromy (n : ℤ) (uv : Interval × Interval) :
      markedPeriodicDisk (n+1) uv = developedDeck monodromy (markedPeriodicDisk n uv) := by
    change developedDeck (monodromy^(n+1)) _ = developedDeck monodromy (developedDeck (monodromy^n) _)
    have hp : monodromy^(n+1) = monodromy * monodromy^n := by
      calc
        monodromy^(n+1) = monodromy^((1:ℤ)+n) := by congr 1; omega
        _ = monodromy * monodromy^n := by rw [zpow_add,zpow_one]
    rw [hp,actual_developedDeck_mul]
  have actual_marked_periodic_disk_bottom (n : ℤ) (u : Interval) :
      markedPeriodicDisk n (u,0) = sourceLift (sourceParameter+(u:ℝ)*(2*Real.pi)+(n:ℝ)*(2*Real.pi)) := by
    simp only [markedPeriodicDisk,hMarkedFundamentalBottom,markedSourceEdge,
      Homeomorph.symm_apply_apply]
    exact (actual_source_integer_period n _).symm
  have actual_marked_periodic_disk_top (n : ℤ) (u : Interval) :
      markedPeriodicDisk n (u,1) = targetLift (targetParameter+(u:ℝ)*(2*Real.pi)+(n:ℝ)*(2*Real.pi)) := by
    simp only [markedPeriodicDisk,hMarkedFundamentalTop,markedTargetEdge,
      Homeomorph.symm_apply_apply]
    exact (actual_target_integer_period n _).symm
  have actual_marked_periodic_disk_plane_carrier (n : ℤ) :
      Set.range (planeCoordinate ∘ markedPeriodicDisk n) =
        Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
          (planeCoordinate '' periodicCellBoundary n) := by
    have he : planeCoordinate ∘ markedPeriodicDisk n = periodicPlaneDeck n ∘ markedFundamentalDisk := by
      funext uv
      simp only [Function.comp_apply,markedPeriodicDisk,periodicPlaneDeck,Homeomorph.trans_apply]
    rw [he,Set.range_comp,actual_marked_fundamental_disk_closed_carrier,
      Set.image_union,CurveComplex.jordan_inside_homeomorph_image,hPeriodicPlaneBoundary]
  have actual_previous_boundary_outside_next_closed (n : ℤ) :
      planeCoordinate '' periodicCellBoundary n ⊆
        Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n+1)) ∪
          (planeCoordinate '' periodicCellBoundary (n+1)) := by
    rw [actual_cell_boundary_right_complement_union_seam,Set.image_union]
    apply Set.union_subset
    · exact actual_right_complement_outside_next n
    · rintro z ⟨u,hu,rfl⟩
      exact Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inl hu)))
  have actual_adjacent_closed_periodic_cells_intersection (n : ℤ) :
      (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
        planeCoordinate '' periodicCellBoundary n) ∩
      (Schoenflies.inside (planeCoordinate '' periodicCellBoundary (n+1)) ∪
        planeCoordinate '' periodicCellBoundary (n+1)) = planeCoordinate '' periodicSeam (n+1) := by
    ext z
    constructor
    · rintro ⟨hz,hz'⟩
      rcases hz with hi | hb <;> rcases hz' with hi' | hb'
      · exact False.elim (Set.disjoint_left.mp (actual_adjacent_periodic_jordan_cell_interiors_disjoint n) hi hi')
      · rcases actual_next_boundary_outside_previous_closed n hb' with ho | he
        · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hi ho)
        · exact False.elim (Schoenflies.inside_subset_compl hi he)
      · rcases actual_previous_boundary_outside_next_closed n hb with ho | he
        · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hi' ho)
        · exact False.elim (Schoenflies.inside_subset_compl hi' he)
      · obtain ⟨u,hu,huEq⟩ := hb
        obtain ⟨v,hv,hvEq⟩ := hb'
        have huv : u = v := planeCoordinate.injective (huEq.trans hvEq.symm)
        refine ⟨u,?_,huEq⟩
        rw [← actual_adjacent_periodic_cell_boundaries_intersection]
        exact ⟨hu,huv.symm ▸ hv⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inr hu))),
        Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inl hu)))⟩
  have actual_marked_periodic_disk_left (n : ℤ) (v : Interval) :
      markedPeriodicDisk n (0,v) = developedDeck (monodromy^n) (facingSeam v) := by
    simp only [markedPeriodicDisk,hMarkedFundamentalLeft,markedFirstSeam,
      Homeomorph.symm_apply_apply]
  have actual_marked_periodic_disk_point_mem_carrier (n : ℤ) (uv : Interval × Interval) :
      planeCoordinate (markedPeriodicDisk n uv) ∈
        Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
          (planeCoordinate '' periodicCellBoundary n) := by
    rw [← actual_marked_periodic_disk_plane_carrier]
    exact ⟨uv,rfl⟩
  have actual_marked_periodic_disk_overlap_indices (n m : ℤ) (u v : Interval × Interval)
      (he : markedPeriodicDisk n u = markedPeriodicDisk m v) :
      n = m ∨ m = n+1 ∨ n = m+1 := by
    have hn := actual_marked_periodic_disk_point_mem_carrier n u
    have hm := actual_marked_periodic_disk_point_mem_carrier m v
    rw [← he] at hm
    rcases lt_trichotomy n m with hlt | hnm | hgt
    · by_cases hnext : m = n+1
      · exact Or.inr (Or.inl hnext)
      · have hfar : n+1 < m := by omega
        exact False.elim (Set.disjoint_left.mp (actual_nonadjacent_closed_periodic_jordan_cells_disjoint n m hfar) hn hm)
    · exact Or.inl hnm
    · by_cases hprev : n = m+1
      · exact Or.inr (Or.inr hprev)
      · have hfar : m+1 < n := by omega
        exact False.elim (Set.disjoint_left.mp (actual_nonadjacent_closed_periodic_jordan_cells_disjoint m n hfar) hm hn)
  have actual_marked_periodic_disk_neighbor_parameters (n : ℤ) (u v : Interval × Interval)
      (he : markedPeriodicDisk n u = markedPeriodicDisk (n+1) v) : u.1 = 1 ∧ v.1 = 0 := by
    have hn := actual_marked_periodic_disk_point_mem_carrier n u
    have hm := actual_marked_periodic_disk_point_mem_carrier (n+1) v
    rw [← he] at hm
    have hz : planeCoordinate (markedPeriodicDisk n u) ∈ planeCoordinate '' periodicSeam (n+1) := by
      rw [← actual_adjacent_closed_periodic_cells_intersection]
      exact ⟨hn,hm⟩
    obtain ⟨_,⟨_,⟨t,ht,rfl⟩,rfl⟩,htEq⟩ := hz
    have htEq' : developedDeck (monodromy^(n+1)) (facingSeam t) = markedPeriodicDisk n u :=
      planeCoordinate.injective htEq
    let w : Interval := ⟨t,ht⟩
    have hnext : markedPeriodicDisk (n+1) (0,w) = markedPeriodicDisk n u := by
      rw [actual_marked_periodic_disk_left]
      exact htEq'
    have hcurrent : markedPeriodicDisk n (1,w) = markedPeriodicDisk n u :=
      (actual_marked_periodic_disk_neighbor_gluing n w).trans hnext
    have hu : (1,w) = u := (actual_marked_periodic_disk_embedding n).injective hcurrent
    have hv : (0,w) = v := (actual_marked_periodic_disk_embedding (n+1)).injective (hnext.trans he)
    exact ⟨(congrArg Prod.fst hu).symm,(congrArg Prod.fst hv).symm⟩
  let stripCell (n : ℤ) : Set (ℝ × Interval) :=
    Prod.fst ⁻¹' Set.Icc (n:ℝ) ((n:ℝ)+1)
  let stripCellMap (n : ℤ) (x : ℝ × Interval) : H2 :=
    markedPeriodicDisk n (Set.projIcc 0 1 (by norm_num) (x.1-(n:ℝ)),x.2)
  have hStripCellMapContinuous (n : ℤ) : Continuous (stripCellMap n) := by
    exact (actual_marked_periodic_disk_embedding n).continuous.comp
      (((continuous_projIcc (a := (0:ℝ)) (b := 1) (h := by norm_num)).comp
        (continuous_fst.sub continuous_const)).prodMk continuous_snd)
  have hStripCellClosed (n : ℤ) : IsClosed (stripCell n) := isClosed_Icc.preimage continuous_fst
  have hStripCellCover (x : ℝ × Interval) : x ∈ stripCell ⌊x.1⌋ := by
    exact ⟨Int.floor_le _,(Int.lt_floor_add_one _).le⟩
  have hStripCellLocallyFinite : LocallyFinite stripCell := by
    intro x
    let U : Set (ℝ × Interval) := Prod.fst ⁻¹' Set.Ioo (x.1-1) (x.1+1)
    have hU : U ∈ 𝓝 x := (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨by linarith,by linarith⟩
    obtain ⟨N,hN⟩ := exists_nat_gt (|x.1|+3)
    refine ⟨U,hU,(Set.finite_Icc (-(N:ℤ)) (N:ℤ)).subset ?_⟩
    rintro n ⟨y,hy,hyU⟩
    have hy' : (n:ℝ) ≤ y.1 ∧ y.1 ≤ (n:ℝ)+1 := hy
    have hyU' : x.1-1 < y.1 ∧ y.1 < x.1+1 := hyU
    have hlo : -(N:ℝ) ≤ (n:ℝ) := by linarith [neg_abs_le x.1]
    have hhi : (n:ℝ) ≤ (N:ℝ) := by linarith [le_abs_self x.1]
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  have hStripCellMapNeighbor (n : ℤ) (x : ℝ × Interval)
      (hn : x ∈ stripCell n) (hn' : x ∈ stripCell (n+1)) :
      stripCellMap n x = stripCellMap (n+1) x := by
    have ht : x.1 = (n:ℝ)+1 := by
      have hlo : ((n+1:ℤ):ℝ) ≤ x.1 := hn'.1
      push_cast at hlo
      linarith [hn.2]
    have hl : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) (x.1-(n:ℝ)) = (1:Interval) := by
      apply Subtype.ext
      simp [ht]
    have hr : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) (x.1-((n+1:ℤ):ℝ)) = (0:Interval) := by
      apply Subtype.ext
      simp [ht]
    simp only [stripCellMap,hl,hr]
    exact actual_marked_periodic_disk_neighbor_gluing n x.2
  have hStripCellMapMatch (n m : ℤ) (x : ℝ × Interval)
      (hn : x ∈ stripCell n) (hm : x ∈ stripCell m) : stripCellMap n x = stripCellMap m x := by
    have hnmReal : (n:ℝ) ≤ (m:ℝ)+1 := hn.1.trans hm.2
    have hmnReal : (m:ℝ) ≤ (n:ℝ)+1 := hm.1.trans hn.2
    have hnm : n ≤ m+1 := by exact_mod_cast hnmReal
    have hmn : m ≤ n+1 := by exact_mod_cast hmnReal
    rcases lt_trichotomy n m with hlt | rfl | hgt
    · have hmEq : m = n+1 := by omega
      subst m
      exact hStripCellMapNeighbor n x hn hm
    · rfl
    · have hnEq : n = m+1 := by omega
      subst n
      exact (hStripCellMapNeighbor m x hm hn).symm
  let actualMarkedStrip (x : ℝ × Interval) : H2 := stripCellMap ⌊x.1⌋ x
  have actual_marked_strip_cell_formula (n : ℤ) (x : ℝ × Interval) (hx : x ∈ stripCell n) :
      actualMarkedStrip x = stripCellMap n x := hStripCellMapMatch _ _ x (hStripCellCover x) hx
  have actual_marked_strip_continuous : Continuous actualMarkedStrip := by
    apply hStripCellLocallyFinite.continuous
    · ext x
      simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
      exact ⟨_,hStripCellCover x⟩
    · exact hStripCellClosed
    · intro n
      apply (hStripCellMapContinuous n).continuousOn.congr
      intro x hx
      exact actual_marked_strip_cell_formula n x hx
  have actual_marked_strip_monodromy (x : ℝ × Interval) :
      actualMarkedStrip (x.1+1,x.2) = developedDeck monodromy (actualMarkedStrip x) := by
    let n : ℤ := ⌊x.1⌋
    have hx : x ∈ stripCell n := hStripCellCover x
    have hx' : (x.1+1,x.2) ∈ stripCell (n+1) := by
      change ((n+1:ℤ):ℝ) ≤ x.1+1 ∧ x.1+1 ≤ ((n+1:ℤ):ℝ)+1
      push_cast
      constructor <;> linarith [hx.1,hx.2]
    rw [actual_marked_strip_cell_formula n x hx,
      actual_marked_strip_cell_formula (n+1) (x.1+1,x.2) hx']
    have hu : (x.1+1)-((n+1:ℤ):ℝ) = x.1-(n:ℝ) := by push_cast; ring
    simp only [stripCellMap,hu]
    exact actual_marked_periodic_disk_monodromy n _
  have actual_marked_strip_bottom (t : ℝ) :
      actualMarkedStrip (t,0) = sourceLift (sourceParameter+t*(2*Real.pi)) := by
    let n : ℤ := ⌊t⌋
    have hn : t-(n:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · linarith [Int.floor_le t]
      · linarith [Int.lt_floor_add_one t]
    rw [actual_marked_strip_cell_formula n (t,0) (hStripCellCover (t,0))]
    simp only [stripCellMap,Set.projIcc_of_mem _ hn]
    rw [actual_marked_periodic_disk_bottom]
    congr 1
    change sourceParameter+(t-(n:ℝ))*(2*Real.pi)+(n:ℝ)*(2*Real.pi) = _
    ring
  have actual_marked_strip_top (t : ℝ) :
      actualMarkedStrip (t,1) = targetLift (targetParameter+t*(2*Real.pi)) := by
    let n : ℤ := ⌊t⌋
    have hn : t-(n:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      constructor
      · linarith [Int.floor_le t]
      · linarith [Int.lt_floor_add_one t]
    rw [actual_marked_strip_cell_formula n (t,1) (hStripCellCover (t,1))]
    simp only [stripCellMap,Set.projIcc_of_mem _ hn]
    rw [actual_marked_periodic_disk_top]
    congr 1
    change targetParameter+(t-(n:ℝ))*(2*Real.pi)+(n:ℝ)*(2*Real.pi) = _
    ring
  have actual_half_open_cell_pasting_injective {X : Type} [TopologicalSpace X]
      (B : ℤ → Interval × Interval → X)
      (hB : ∀ n, Function.Injective (B n))
      (hoverlap : ∀ n m u v, B n u = B m v → n=m ∨ m=n+1 ∨ n=m+1)
      (hneighbor : ∀ n u v, B n u = B (n+1) v → u.1=1 ∧ v.1=0) :
      Function.Injective (fun x : ℝ × Interval =>
        B ⌊x.1⌋ (⟨x.1-(⌊x.1⌋:ℝ),by
          constructor
          · linarith [Int.floor_le x.1]
          · linarith [Int.lt_floor_add_one x.1]⟩,x.2)) := by
    intro x y he
    let n := ⌊x.1⌋
    let m := ⌊y.1⌋
    let u : Interval := ⟨x.1-(n:ℝ),by
      constructor
      · linarith [Int.floor_le x.1]
      · linarith [Int.lt_floor_add_one x.1]⟩
    let v : Interval := ⟨y.1-(m:ℝ),by
      constructor
      · linarith [Int.floor_le y.1]
      · linarith [Int.lt_floor_add_one y.1]⟩
    have he' : B n (u,x.2) = B m (v,y.2) := he
    have huLt : (u:ℝ) < 1 := by change x.1-(⌊x.1⌋:ℝ)<1;linarith [Int.lt_floor_add_one x.1]
    have hvLt : (v:ℝ) < 1 := by change y.1-(⌊y.1⌋:ℝ)<1;linarith [Int.lt_floor_add_one y.1]
    rcases hoverlap n m (u,x.2) (v,y.2) he' with hnm | hnext | hprev
    · have huv : (u,x.2) = (v,y.2) := hB n (hnm ▸ he')
      have huEq : (u:ℝ) = (v:ℝ) := congrArg (fun z : Interval × Interval => (z.1:ℝ)) huv
      apply Prod.ext
      · change x.1-(n:ℝ) = y.1-(m:ℝ) at huEq
        rw [hnm] at huEq
        linarith
      · exact congrArg (fun z : Interval × Interval => z.2) huv
    · have huEq := (hneighbor n (u,x.2) (v,y.2) (hnext ▸ he')).1
      have hval := congrArg Subtype.val huEq
      change (u:ℝ)=1 at hval
      exact False.elim ((ne_of_lt huLt) hval)
    · have hvEq := (hneighbor m (v,y.2) (u,x.2) (hprev ▸ he'.symm)).1
      have hval := congrArg Subtype.val hvEq
      change (v:ℝ)=1 at hval
      exact False.elim ((ne_of_lt hvLt) hval)
  have actual_marked_strip_injective : Function.Injective actualMarkedStrip := by
    have h := actual_half_open_cell_pasting_injective markedPeriodicDisk
      (fun n => (actual_marked_periodic_disk_embedding n).injective)
      actual_marked_periodic_disk_overlap_indices actual_marked_periodic_disk_neighbor_parameters
    have he : actualMarkedStrip = (fun x : ℝ × Interval =>
      markedPeriodicDisk ⌊x.1⌋ (⟨x.1-(⌊x.1⌋:ℝ),by
        constructor
        · linarith [Int.floor_le x.1]
        · linarith [Int.lt_floor_add_one x.1]⟩,x.2)) := by
      funext x
      change markedPeriodicDisk ⌊x.1⌋ (Set.projIcc 0 1 (by norm_num) (x.1-(⌊x.1⌋:ℝ)),x.2) = _
      have hx : x.1-(⌊x.1⌋:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · linarith [Int.floor_le x.1]
        · linarith [Int.lt_floor_add_one x.1]
      rw [Set.projIcc_of_mem _ hx]
    rw [he]
    exact h
  have actual_axis_periodic_strip_proper {X : Type} [MetricSpace X]
      (F : C(ℝ × Interval,X)) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
      (htranslate : ∀ t, g (axis t) = axis (t+τ))
      (hperiod : ∀ x : ℝ × Interval, F (x.1+1,x.2) = g (F x)) :
      IsProperMap F := by
    let δ : ℝ × Interval → ℝ := fun x => dist (F x) (axis (x.1*τ))
    have hδcont : Continuous δ := F.continuous.dist
      (haxis.continuous.comp (continuous_fst.mul continuous_const))
    have hδperiod (v : Interval) : Function.Periodic (fun s => δ (s,v)) 1 := by
      intro s
      dsimp [δ]
      have ht : (s+1)*τ = s*τ+τ := by ring
      rw [hperiod (s,v),ht,← htranslate,hg.dist_eq]
    have hcompact : IsCompact (δ '' (Set.Icc (0:ℝ) 1 ×ˢ (Set.univ : Set Interval))) :=
      (isCompact_Icc.prod isCompact_univ).image hδcont
    obtain ⟨M,hM⟩ := hcompact.bddAbove
    have hbound (x : ℝ × Interval) : δ x ≤ M := by
      have hrange : δ x ∈ Set.range (fun s => δ (s,x.2)) := ⟨x.1,rfl⟩
      rw [← (hδperiod x.2).image_Icc (by norm_num : (0:ℝ)<1) 0] at hrange
      obtain ⟨s,hs,hsEq⟩ := hrange
      exact hM ⟨(s,x.2),⟨by simpa using hs,Set.mem_univ _⟩,hsEq⟩
    have hlower (x : ℝ × Interval) : |x.1| * τ-M ≤ dist (F x) (axis 0) := by
      have htri := dist_triangle (axis (x.1*τ)) (F x) (axis 0)
      rw [haxis.dist_eq,Real.dist_eq,sub_zero,abs_mul,abs_of_pos hτ,
        dist_comm (axis (x.1*τ)) (F x)] at htri
      have hb := hbound x
      dsimp [δ] at hb
      linarith
    have hfst : Filter.Tendsto (Prod.fst : ℝ × Interval → ℝ) (Filter.cocompact (ℝ × Interval)) (Filter.cocompact ℝ) :=
      (isProperMap_iff_tendsto_cocompact.mp isProperMap_fst_of_compactSpace).2
    have habs : Filter.Tendsto (fun x : ℝ × Interval => |x.1|) (Filter.cocompact (ℝ × Interval)) Filter.atTop := by
      have hreal : Filter.Tendsto (fun t : ℝ => |t|) (Filter.cocompact ℝ) Filter.atTop := by
        convert tendsto_dist_right_cocompact_atTop (0:ℝ) using 1
        ext t
        simp [Real.dist_eq]
      exact hreal.comp hfst
    have hdist : Filter.Tendsto (fun x : ℝ × Interval => dist (F x) (axis 0)) (Filter.cocompact (ℝ × Interval)) Filter.atTop := by
      apply Filter.tendsto_atTop.mpr
      intro R
      filter_upwards [(Filter.tendsto_atTop.mp habs) ((R+M)/τ)] with x hx
      have h := (div_le_iff₀ hτ).mp hx
      linarith [hlower x]
    exact isProperMap_iff_tendsto_cocompact.mpr
      ⟨F.continuous,tendsto_cocompact_of_tendsto_dist_comp_atTop (axis 0) hdist⟩
  let actualMarkedStripMap : C(ℝ × Interval,H2) := ⟨actualMarkedStrip,actual_marked_strip_continuous⟩
  have actual_marked_strip_proper : IsProperMap actualMarkedStrip :=
    actual_axis_periodic_strip_proper actualMarkedStripMap (developedDeck monodromy)
      (all_developed_decks_isometric monodromy) actualAxis hactualAxis axisPeriod haxisPeriod
      haxisTranslate actual_marked_strip_monodromy
  have actual_marked_strip_closed_embedding : Topology.IsClosedEmbedding actualMarkedStrip :=
    Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
      ⟨actual_marked_strip_continuous,actual_marked_strip_injective,actual_marked_strip_proper.isClosedMap⟩
  have actual_periodic_seam_in_facing_closure (n : ℤ) : periodicSeam n ⊆ closure facingRegion := by
    have h := Set.image_mono hFirstSeamFacingClosure (f := developedDeck (monodromy^n))
    rw [(developedDeck (monodromy^n)).image_closure,
      actual_facing_region_all_integer_monodromy_invariant] at h
    exact h
  have actual_periodic_boundary_in_facing_closure (n : ℤ) : periodicCellBoundary n ⊆ closure facingRegion := by
    intro z hz
    rcases hz with (hs | ht) | (hl | hr)
    · apply frontier_subset_closure
      rw [actual_facing_region_geometry.2.2]
      exact Or.inl (Set.image_subset_range _ _ hs)
    · apply frontier_subset_closure
      rw [actual_facing_region_geometry.2.2]
      exact Or.inr (Set.image_subset_range _ _ ht)
    · exact actual_periodic_seam_in_facing_closure n hl
    · exact actual_periodic_seam_in_facing_closure (n+1) hr
  have actual_marked_strip_range_in_facing_closure : Set.range actualMarkedStrip ⊆ closure facingRegion := by
    rintro z ⟨x,rfl⟩
    have hc := actual_marked_periodic_disk_point_mem_carrier ⌊x.1⌋
      (Set.projIcc 0 1 (by norm_num) (x.1-(⌊x.1⌋:ℝ)),x.2)
    change planeCoordinate (actualMarkedStrip x) ∈ _ at hc
    rcases hc with hi | hb
    · obtain ⟨u,hu,he⟩ := actual_all_periodic_cell_insides_in_facing_region _ hi
      have heu := planeCoordinate.injective he
      exact subset_closure (heu ▸ hu)
    · obtain ⟨u,hu,he⟩ := hb
      have heu := planeCoordinate.injective he
      exact heu ▸ actual_periodic_boundary_in_facing_closure _ hu
  let markedStripInteriorDomain : Set (ℝ × Interval) := {x | (0:ℝ) < x.2.val ∧ x.2.val < 1}
  let markedStripInterior : Set H2 := actualMarkedStrip '' markedStripInteriorDomain
  have actual_marked_strip_interior_avoids_boundary :
      Disjoint markedStripInterior (Set.range sourceLift ∪ Set.range targetLift) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ (⟨s,hs⟩ | ⟨s,hs⟩)
    · let t : ℝ := (s-sourceParameter)/(2*Real.pi)
      have ht : sourceParameter+t*(2*Real.pi) = s := by dsimp [t]; field_simp; ring
      have he : actualMarkedStrip (t,0) = actualMarkedStrip x := by rw [actual_marked_strip_bottom,ht];exact hs
      have hzero := congrArg (fun y : ℝ × Interval => (y.2:ℝ)) (actual_marked_strip_injective he)
      change 0 = (x.2:ℝ) at hzero
      exact (ne_of_gt hx.1) hzero.symm
    · let t : ℝ := (s-targetParameter)/(2*Real.pi)
      have ht : targetParameter+t*(2*Real.pi) = s := by dsimp [t]; field_simp; ring
      have he : actualMarkedStrip (t,1) = actualMarkedStrip x := by rw [actual_marked_strip_top,ht];exact hs
      have hone := congrArg (fun y : ℝ × Interval => (y.2:ℝ)) (actual_marked_strip_injective he)
      change 1 = (x.2:ℝ) at hone
      exact (ne_of_lt hx.2) hone.symm
  have actual_marked_strip_interior_in_facing : markedStripInterior ⊆ facingRegion := by
    intro z hz
    have hc := actual_marked_strip_range_in_facing_closure (Set.image_subset_range _ _ hz)
    rw [closure_eq_self_union_frontier,actual_facing_region_geometry.2.2] at hc
    rcases hc with hf | hb
    · exact hf
    · exact False.elim (Set.disjoint_left.mp actual_marked_strip_interior_avoids_boundary hz hb)
  have actual_embedded_open_strip_interior (B : ℝ × Interval → Schoenflies.Plane) (hB : Topology.IsEmbedding B) :
      IsOpen (B '' {u | (0:ℝ) < u.2.val ∧ u.2.val < 1}) := by
    let V : Set Schoenflies.Plane := {x | 0 < x 1 ∧ x 1 < 1}
    let p (x : Schoenflies.Plane) : ℝ × Interval := (x 0,Set.projIcc 0 1 (by norm_num) (x 1))
    let f : Schoenflies.Plane → Schoenflies.Plane := B ∘ p
    have hc0 : Continuous (fun x : Schoenflies.Plane => x 0) := by fun_prop
    have hc1 : Continuous (fun x : Schoenflies.Plane => x 1) := by fun_prop
    have hp : Continuous p := hc0.prodMk (continuous_projIcc.comp hc1)
    have hf : Continuous f := hB.continuous.comp hp
    have hV : IsOpen V := (isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)
    have hpval (x : Schoenflies.Plane) (hx : x ∈ V) : ((p x).2:ℝ)=x 1 :=
      congrArg Subtype.val (Set.projIcc_of_mem (by norm_num) ⟨hx.1.le,hx.2.le⟩)
    have hfinj : Set.InjOn f V := by
      intro x hx y hy he
      have he' := hB.injective he
      have h0 := congrArg Prod.fst he'
      have h1 := congrArg (fun u : ℝ × Interval => (u.2:ℝ)) he'
      rw [hpval x hx,hpval y hy] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hU : IsOpen (f '' V) :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
        f V hV hf.continuousOn hfinj
    have he : f '' V = B '' {u | (0:ℝ) < u.2.val ∧ u.2.val < 1} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨p x,?_,rfl⟩
        change (0:ℝ) < ((p x).2:ℝ) ∧ ((p x).2:ℝ) < 1
        rw [hpval x hx]
        exact hx
      · rintro ⟨u,hu,rfl⟩
        let x := Schoenflies.Plane.mk u.1 u.2
        have hx : x ∈ V := hu
        refine ⟨x,hx,?_⟩
        change B (p x) = B u
        congr 1
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact hpval x hx
    rwa [he] at hU
  have actual_marked_strip_interior_open : IsOpen markedStripInterior := by
    have h := actual_embedded_open_strip_interior (planeCoordinate ∘ actualMarkedStrip)
      (planeCoordinate.isEmbedding.comp actual_marked_strip_closed_embedding.isEmbedding)
    change IsOpen ((planeCoordinate ∘ actualMarkedStrip) '' markedStripInteriorDomain) at h
    rw [Set.image_comp] at h
    exact planeCoordinate.isOpen_image.mp h
  have actual_facing_region_disjoint_lifts : Disjoint facingRegion (Set.range sourceLift ∪ Set.range targetLift) := by
    rw [← actual_facing_region_geometry.2.2]
    exact (disjoint_frontier_iff_isOpen.mpr actual_facing_region_geometry.1).symm
  have actual_marked_strip_range_inter_facing : Set.range actualMarkedStrip ∩ facingRegion = markedStripInterior := by
    ext z
    constructor
    · rintro ⟨⟨x,rfl⟩,hf⟩
      refine ⟨x,?_,rfl⟩
      have hzero : x.2 ≠ 0 := by
        intro he
        have hz : actualMarkedStrip x ∈ Set.range sourceLift := by
          rw [show x = (x.1,0) from Prod.ext rfl he,actual_marked_strip_bottom]
          exact Set.mem_range_self _
        exact Set.disjoint_left.mp actual_facing_region_disjoint_lifts hf (Or.inl hz)
      have hone : x.2 ≠ 1 := by
        intro he
        have hz : actualMarkedStrip x ∈ Set.range targetLift := by
          rw [show x = (x.1,1) from Prod.ext rfl he,actual_marked_strip_top]
          exact Set.mem_range_self _
        exact Set.disjoint_left.mp actual_facing_region_disjoint_lifts hf (Or.inr hz)
      have hzeroVal : (x.2:ℝ) ≠ 0 := fun he => hzero (Subtype.ext he)
      have honeVal : (x.2:ℝ) ≠ 1 := fun he => hone (Subtype.ext he)
      exact ⟨lt_of_le_of_ne x.2.property.1 hzeroVal.symm,lt_of_le_of_ne x.2.property.2 honeVal⟩
    · intro hz
      exact ⟨Set.image_subset_range _ _ hz,actual_marked_strip_interior_in_facing hz⟩
  have actual_marked_strip_interior_relatively_clopen :
      IsClopen ((Subtype.val : facingRegion → H2) ⁻¹' markedStripInterior) := by
    constructor
    · have he : (Subtype.val : facingRegion → H2) ⁻¹' markedStripInterior =
          (Subtype.val : facingRegion → H2) ⁻¹' Set.range actualMarkedStrip := by
        ext z
        rw [← actual_marked_strip_range_inter_facing]
        simp only [Set.mem_preimage,Set.mem_inter_iff,and_iff_left z.property]
      rw [he]
      exact actual_marked_strip_closed_embedding.isClosed_range.preimage continuous_subtype_val
    · exact actual_marked_strip_interior_open.preimage continuous_subtype_val
  have actual_marked_strip_covers_facing_of_connected (hconn : IsConnected facingRegion) :
      markedStripInterior = facingRegion := by
    letI : ConnectedSpace facingRegion := isConnected_iff_connectedSpace.mp hconn
    let x : ℝ × Interval := (0,⟨1/2,by norm_num⟩)
    have hx : actualMarkedStrip x ∈ markedStripInterior := by
      refine ⟨x,?_,rfl⟩
      change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1
      norm_num
    have hne : ((Subtype.val : facingRegion → H2) ⁻¹' markedStripInterior).Nonempty :=
      ⟨⟨actualMarkedStrip x,actual_marked_strip_interior_in_facing hx⟩,hx⟩
    have hall := actual_marked_strip_interior_relatively_clopen.eq_univ hne
    apply Set.Subset.antisymm actual_marked_strip_interior_in_facing
    intro z hz
    have hm : (⟨z,hz⟩ : facingRegion) ∈ (Set.univ : Set facingRegion) := Set.mem_univ _
    rw [← hall] at hm
    exact hm
  open Schoenflies CurveComplexGenusTwo.Topology.PuncturedTorusCandidate Metric Filter in
  have actual_two_proper_lines_facing_connected (F G : C(ℝ,Plane)) (hG : Topology.IsClosedEmbedding G)
      (U Uout V Vout : Set Plane)
      (hU : IsOpen U) (hUout : IsOpen Uout) (hV : IsOpen V) (hVout : IsOpen Vout)
      (hUconn : IsConnected U) (hUoutconn : IsConnected Uout)
      (hVconn : IsConnected V) (hVoutconn : IsConnected Vout)
      (hUdis : Disjoint U Uout) (hVdis : Disjoint V Vout)
      (hUpart : U ∪ Uout = (Set.range F)ᶜ) (hVpart : V ∪ Vout = (Set.range G)ᶜ)
      (hUfront : frontier U = Set.range F) (hUoutfront : frontier Uout = Set.range F)
      (hVfront : frontier V = Set.range G) (hVoutfront : frontier Vout = Set.range G)
      (hGinU : Set.range G ⊆ U) (hFinV : Set.range F ⊆ V)
      (hF : Topology.IsClosedEmbedding F) : IsConnected (U ∩ V) := by
    have actual_proper_line_planar_side (F : C(ℝ,Plane)) (hF : Topology.IsClosedEmbedding F)
        (Uin Uout : Set Plane) (hinOpen : IsOpen Uin) (houtOpen : IsOpen Uout)
        (hinConn : IsConnected Uin) (houtConn : IsConnected Uout)
        (hgivenDisj : Disjoint Uin Uout) (hgivenPart : Uin ∪ Uout = (Set.range F)ᶜ) :
        Nonempty (Plane ≃ₜ Uin) := by
      classical
      obtain ⟨a,haOut⟩ := houtConn.nonempty
      let L := Set.range F
      have ha : a ∉ L := by
        have hx : a ∈ Uin ∪ Uout := Or.inr haOut
        rw [hgivenPart] at hx
        exact hx
      have hJ := proper_line_inversion_isJordanCurve F hF.isProperMap hF.injective a ha
      let C := insert a (invert a '' L)
      have hsep : IsSeparating C := jordan_curve_theorem hJ
      have haC : a ∈ C := Set.mem_insert a _
      have hain : a ∉ inside C := fun h => h.1 haC
      have haout : a ∉ outside C := fun h => h.1 haC
      let U := invert a '' inside C
      let V := invert a '' outside C ∪ {a}
      have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
      have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
        intro z hz
        simpa only [mem_compl_iff, mem_singleton_iff] using
          (show z ≠ a from fun h => haout (h ▸ hz))
      have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
        intro z hz
        simpa only [mem_compl_iff, mem_singleton_iff] using
          (show z ≠ a from fun h => hain (h ▸ hz))
      have hUconn : IsConnected U :=
        hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
      obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
      have hTopen : IsOpen (invert a '' outside C) :=
        isOpen_invert_image hsep.isOpen_outside haout
      have hVball : ball a R⁻¹ ⊆ V := by
        intro z hz
        rcases eq_or_ne z a with rfl | hza
        · exact Or.inr rfl
        · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
          have hpos : 0 < dist z a := dist_pos.2 hza
          rw [mem_compl_iff, mem_closedBall, dist_invert_center]
          exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
      have hVopen : IsOpen V := by
        have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
          refine Subset.antisymm (union_subset subset_union_left ?_)
            (union_subset subset_union_left hVball)
          rintro z rfl
          exact Or.inr (mem_ball_self (by positivity))
        rw [hrw]
        exact hTopen.union isOpen_ball
      have hacl : a ∈ closure (invert a '' outside C) := by
        rw [Metric.mem_closure_iff]
        intro e he
        obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
          by_contra hcon
          push Not at hcon
          exact hsep.not_isBounded_outside
            ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
        refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
        rw [dist_comm, dist_invert_center]
        exact inv_lt_of_inv_lt₀ he hzfar
      have hVconn : IsConnected V := by
        refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
        exact (hsep.isConnected_outside.image _
          ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
          (union_subset subset_closure (by rintro z rfl; exact hacl))
      have hdis : Disjoint U V := by
        apply Set.disjoint_left.mpr
        rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
        · have he' := invert_injective a he
          exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
        · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
      have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
        dsimp [C]
        simp only [mem_insert_iff, invert_eq_center_iff]
        rw [Set.mem_image]
        constructor
        · rintro (h | ⟨x, hx, he⟩)
          · exact Or.inl h
          · exact Or.inr ((invert_injective a he) ▸ hx)
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨z, h, rfl⟩
      have hpart : U ∪ V = Lᶜ := by
        ext z
        constructor
        · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
          · intro hz
            have := (hinv (invert a x)).mpr (Or.inr hz)
            rw [invert_invert] at this
            exact hx.1 this
          · intro hz
            have := (hinv (invert a x)).mpr (Or.inr hz)
            rw [invert_invert] at this
            exact hx.1 this
          · exact ha
        · intro hz
          by_cases hza : z = a
          · exact Or.inr (Or.inr hza)
          · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
            have hzside : invert a z ∈ inside C ∪ outside C := by
              rwa [inside_union_outside]
            rcases hzside with hu | hv
            · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
            · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
      have hUL : Disjoint U L := by
        apply Set.disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hL
      have hVL : Disjoint V L := by
        apply Set.disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hL
      have hfrontU : frontier U = L := by
        apply Subset.antisymm
        · intro x hx
          by_contra hxL
          have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
          rcases hside with hu | hv
          · exact (hUopen.frontier_eq ▸ hx).2 hu
          · exact Set.disjoint_right.mp (hdis.closure_left hVopen) hv (frontier_subset_closure hx)
        · intro x hx
          have hxa : x ≠ a := fun h => ha (h ▸ hx)
          have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
          have hixcl : invert a x ∈ closure (inside C) := by
            rw [← hsep.frontier_inside] at hixC
            exact frontier_subset_closure hixC
          rw [hUopen.frontier_eq]
          refine ⟨?_, fun h => Set.disjoint_left.mp hUL h hx⟩
          simpa only [invert_invert] using
            mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
      have hfrontV : frontier V = L := by
        apply Subset.antisymm
        · intro x hx
          by_contra hxL
          have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
          rcases hside with hu | hv
          · exact Set.disjoint_left.mp (hdis.closure_right hUopen) hu (frontier_subset_closure hx)
          · exact (hVopen.frontier_eq ▸ hx).2 hv
        · intro x hx
          have hxa : x ≠ a := fun h => ha (h ▸ hx)
          have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
          have hixcl : invert a x ∈ closure (outside C) := by
            rw [← hsep.frontier_outside] at hixC
            exact frontier_subset_closure hixC
          rw [hVopen.frontier_eq]
          refine ⟨?_, fun h => Set.disjoint_left.mp hVL h hx⟩
          apply closure_mono (show invert a '' outside C ⊆ V from subset_union_left)
          simpa only [invert_invert] using
            mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
      have hOutCover : Uout ⊆ U ∪ V := by
        intro z hz
        rw [hpart]
        exact hgivenPart ▸ Or.inr hz
      have hUoutSubsetV : Uout ⊆ V := by
        rcases houtConn.isPreconnected.subset_or_subset hUopen hVopen hdis hOutCover with hh | hh
        · exact False.elim (notMem_invert_image hain (hh haOut))
        · exact hh
      have hVsubOut : V ⊆ Uout := by
        have hVCover : V ⊆ Uin ∪ Uout := by
          intro z hz
          rw [hgivenPart]
          exact hpart ▸ Or.inr hz
        rcases hVconn.isPreconnected.subset_or_subset hinOpen houtOpen hgivenDisj hVCover with hh | hh
        · exact False.elim (Set.disjoint_left.mp hgivenDisj (hh (Or.inr rfl)) haOut)
        · exact hh
      have hUeq : U = Uin := by
        ext z
        constructor
        · intro hz
          have hh : z ∈ Uin ∪ Uout := hgivenPart.symm ▸ (hpart ▸ Or.inl hz)
          exact hh.resolve_right (fun hh => Set.disjoint_left.mp hdis hz (hUoutSubsetV hh))
        · intro hz
          have hh : z ∈ U ∪ V := hpart.symm ▸ (hgivenPart ▸ Or.inl hz)
          exact hh.resolve_right (fun hh => Set.disjoint_left.mp hgivenDisj hz (hVsubOut hh))
      have disc {D : Set Plane} (hD : IsJordanCurve D) : Nonempty (Plane ≃ₜ inside D) := by
        obtain ⟨e⟩ := hD.modelCurve_homeomorph
        obtain ⟨H,hH⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hD e
        have him : H '' modelCurve = D := by
          ext z
          constructor
          · rintro ⟨x,hx,rfl⟩
            rw [hH ⟨x,hx⟩]
            exact (e ⟨x,hx⟩).property
          · intro hz
            let w := e.symm ⟨z,hz⟩
            refine ⟨w.val,w.property,?_⟩
            rw [hH w]
            exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
        have hi : H '' inside modelCurve = inside D := by rw [jordan_inside_homeomorph_image,him]
        let A : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
        let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
        let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
          A.symm.subtype (fun x => by
            simp only [Metric.mem_ball,dist_zero_right,pi_norm_lt_iff (by norm_num : (0:ℝ)<1)]
            change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (A.symm x).supDist 0 < 1
            simp [Plane.supDist,Plane.supNorm,Fin.forall_fin_two,A,EuclideanSpace.equiv,PiLp.toLp_apply,Real.norm_eq_abs])
        let R : inside modelCurve ≃ₜ inside D :=
          (H.isEmbedding.homeomorphImage (inside modelCurve)).trans (Homeomorph.setCongr hi)
        exact ⟨((A.trans B).trans K).trans ((Homeomorph.setCongr inside_modelCurve.symm).trans R)⟩
      obtain ⟨d⟩ := disc hJ
      have hinv := isHomeoOn_invert hain
      let R : inside C ≃ₜ U := {
        toFun := fun x => ⟨invert a x,hinv.mapsTo x.property⟩
        invFun := fun y => ⟨invert a y,hinv.mapsTo_inv y.property⟩
        left_inv := fun x => Subtype.ext (invert_invert a x)
        right_inv := fun y => Subtype.ext (invert_invert a y)
        continuous_toFun := hinv.continuousOn.restrict.subtype_mk _
        continuous_invFun := hinv.continuousOn_inv.restrict.subtype_mk _ }
      exact ⟨(d.trans R).trans (Homeomorph.setCongr hUeq)⟩
    obtain ⟨e⟩ := actual_proper_line_planar_side F hF U Uout hU hUout hUconn hUoutconn hUdis hUpart
  
    have hVoutNoF : Vout ⊆ (Set.range F)ᶜ := by
      intro z hz hf
      exact Set.disjoint_left.mp hVdis (hFinV hf) hz
    have hVoutInU : Vout ⊆ U := by
      have hc : Vout ⊆ U ∪ Uout := by rwa [hUpart]
      rcases hVoutconn.isPreconnected.subset_or_subset hU hUout hUdis hc with hin | hout
      · exact hin
      · have hg : G 0 ∈ closure Vout := by
          apply frontier_subset_closure
          rw [hVoutfront]
          exact Set.mem_range_self _
        have hz := closure_mono hout hg
        exact False.elim (Set.disjoint_left.mp (hUdis.closure_right hU) (hGinU (Set.mem_range_self 0)) hz)
    let p : Plane → Plane := Subtype.val ∘ e
    have hp : Topology.IsOpenEmbedding p := hU.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
    have hprange : Set.range p = U := by
      ext z
      constructor
      · rintro ⟨x,rfl⟩
        exact (e x).property
      · intro hz
        exact ⟨e.symm ⟨z,hz⟩,by simp [p]⟩
    let Grestrict : C(ℝ,U) := ⟨fun t => ⟨G t,hGinU (Set.mem_range_self t)⟩,G.continuous.subtype_mk _⟩
    have hGrestrict : Topology.IsClosedEmbedding Grestrict :=
      Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal hG
    let line : C(ℝ,Plane) := ⟨e.symm ∘ Grestrict,e.symm.continuous.comp Grestrict.continuous⟩
    have hline : Topology.IsClosedEmbedding line := e.symm.isClosedEmbedding.comp hGrestrict
    have hlineRange : Set.range line = p ⁻¹' Set.range G := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨t,by simp [p,line,Grestrict]⟩
      · rintro ⟨t,ht⟩
        refine ⟨t,?_⟩
        apply e.injective
        apply Subtype.ext
        simpa [p,line,Grestrict] using ht
    let A : Set Plane := p ⁻¹' Vout
    let B : Set Plane := p ⁻¹' V
    have hA : IsOpen A := hVout.preimage hp.continuous
    have hB : IsOpen B := hV.preimage hp.continuous
    have hAconn : IsConnected A := hVoutconn.preimage_of_isOpenMap hp.injective hp.isOpenMap (by rwa [hprange])
    have hABdis : Disjoint B A := hVdis.preimage p
    have hABpart : B ∪ A = (Set.range line)ᶜ := by
      rw [hlineRange]
      change p ⁻¹' V ∪ p ⁻¹' Vout = (p ⁻¹' Set.range G)ᶜ
      rw [← Set.preimage_union,hVpart,Set.preimage_compl]
    have hAfront : frontier A = Set.range line := by
      rw [← hp.isOpenMap.preimage_frontier_eq_frontier_preimage hp.continuous,hVoutfront,← hlineRange]
    obtain ⟨x,hxA⟩ := hAconn.nonempty
    have hxAvoid : x ∉ Set.range line := by
      have hx : x ∈ (Set.range line)ᶜ := hABpart ▸ Or.inr hxA
      exact hx
    have hJ := proper_line_inversion_isJordanCurve line hline.isProperMap hline.injective x hxAvoid
    obtain ⟨C,D,hC,hD,hCc,hDc,hCD,hCDpart,hCfront,hDfront⟩ :=
      proper_line_sides_of_inversion_jordan (Set.range line) x hxAvoid hJ
    have component (K : Set Plane) (hK : IsOpen K) (hKc : IsPreconnected K)
        (hKfront : frontier K = Set.range line) (hx : x ∈ K) :
        connectedComponentIn (Set.range line)ᶜ x = K := by
      have hKsub : K ⊆ (Set.range line)ᶜ := by
        rw [← hKfront]
        exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hK).symm
      have hfr : frontier K ∩ (Set.range line)ᶜ = ∅ := by rw [hKfront];exact Set.inter_compl_self _
      exact Plane.connectedComponentIn_eq_of_frontier_disjoint hK hKc hKsub hfr hx
    have hAC : connectedComponentIn (Set.range line)ᶜ x = A := component A hA hAconn.isPreconnected hAfront hxA
    have hxCD : x ∈ C ∪ D := hCDpart.symm ▸ hxAvoid
    have hBconn : IsConnected B := by
      rcases hxCD with hxC | hxD
      · have hACeq : A = C := hAC.symm.trans (component C hC hCc.isPreconnected hCfront hxC)
        have he : B = D := by
          ext z
          constructor
          · intro hz
            have hh : z ∈ C ∪ D := hCDpart.symm ▸ (hABpart ▸ Or.inl hz)
            exact hh.resolve_left (fun hh => Set.disjoint_left.mp hABdis hz (hACeq.symm ▸ hh))
          · intro hz
            have hh : z ∈ B ∪ A := hABpart.symm ▸ (hCDpart ▸ Or.inr hz)
            exact hh.resolve_right (fun hh => Set.disjoint_left.mp hCD (hACeq ▸ hh) hz)
        exact he.symm ▸ hDc
      · have hADeq : A = D := hAC.symm.trans (component D hD hDc.isPreconnected hDfront hxD)
        have he : B = C := by
          ext z
          constructor
          · intro hz
            have hh : z ∈ C ∪ D := hCDpart.symm ▸ (hABpart ▸ Or.inl hz)
            exact hh.resolve_right (fun hh => Set.disjoint_left.mp hABdis hz (hADeq.symm ▸ hh))
          · intro hz
            have hh : z ∈ B ∪ A := hABpart.symm ▸ (hCDpart ▸ Or.inl hz)
            exact hh.resolve_right (fun hh => Set.disjoint_left.mp hCD hz (hADeq ▸ hh))
        exact he.symm ▸ hCc
    have himage : p '' B = U ∩ V := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨(e x).property,hx⟩
      · rintro ⟨hzU,hzV⟩
        refine ⟨e.symm ⟨z,hzU⟩,?_,?_⟩
        · simpa [B,p] using hzV
        · simp [p]
    rw [← himage]
    exact hBconn.image p hp.continuous.continuousOn
  have actual_facing_region_connected : IsConnected facingRegion := by
    let PF : C(ℝ,Schoenflies.Plane) := ⟨planeCoordinate ∘ sourceLift,planeCoordinate.continuous.comp sourceLift.continuous⟩
    let PG : C(ℝ,Schoenflies.Plane) := ⟨planeCoordinate ∘ targetLift,planeCoordinate.continuous.comp targetLift.continuous⟩
    have hPFRange : Set.range PF = planeCoordinate '' Set.range sourceLift := by
      exact Set.range_comp (planeCoordinate : H2 → Schoenflies.Plane) (sourceLift : ℝ → H2)
    have hPGRange : Set.range PG = planeCoordinate '' Set.range targetLift := by
      exact Set.range_comp (planeCoordinate : H2 → Schoenflies.Plane) (targetLift : ℝ → H2)
    have hPlaneConn := actual_two_proper_lines_facing_connected PF PG
      (planeCoordinate.isClosedEmbedding.comp actual_targetLift_closed_embedding)
      (planeCoordinate '' sourceInner) (planeCoordinate '' sourceOuter)
      (planeCoordinate '' targetInner) (planeCoordinate '' targetOuter)
      (planeCoordinate.isOpenMap _ hSourceInnerOpen) (planeCoordinate.isOpenMap _ hSourceOuterOpen)
      (planeCoordinate.isOpenMap _ hTargetInnerOpen) (planeCoordinate.isOpenMap _ hTargetOuterOpen)
      (hSourceInnerConn.image _ planeCoordinate.continuous.continuousOn)
      (hSourceOuterConn.image _ planeCoordinate.continuous.continuousOn)
      (hTargetInnerConn.image _ planeCoordinate.continuous.continuousOn)
      (hTargetOuterConn.image _ planeCoordinate.continuous.continuousOn)
      (hSourceSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
      (hTargetSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
      (by rw [← Set.image_union,hSourceSidesPartition,planeCoordinate.image_compl,← hPFRange])
      (by rw [← Set.image_union,hTargetSidesPartition,planeCoordinate.image_compl,← hPGRange])
      (by rw [← planeCoordinate.image_frontier,hSourceInnerFrontier,← hPFRange])
      (by rw [← planeCoordinate.image_frontier,hSourceOuterFrontier,← hPFRange])
      (by rw [← planeCoordinate.image_frontier,hTargetInnerFrontier,← hPGRange])
      (by rw [← planeCoordinate.image_frontier,hTargetOuterFrontier,← hPGRange])
      (by rw [hPGRange];exact Set.image_mono hTargetInSourceInner)
      (by rw [hPFRange];exact Set.image_mono hSourceInTargetInner)
      (planeCoordinate.isClosedEmbedding.comp actual_sourceLift_closed_embedding)
    have himage : planeCoordinate '' facingRegion = (planeCoordinate '' sourceInner) ∩ (planeCoordinate '' targetInner) :=
      Set.image_inter planeCoordinate.injective
    rw [← himage] at hPlaneConn
    have hback := hPlaneConn.image planeCoordinate.symm planeCoordinate.symm.continuous.continuousOn
    simpa only [Set.image_image,Function.comp_def,Homeomorph.symm_apply_apply,Set.image_id'] using hback
  have actual_marked_strip_interior_eq_facing : markedStripInterior = facingRegion :=
    actual_marked_strip_covers_facing_of_connected actual_facing_region_connected
  have actual_marked_strip_range_eq_facing_closure : Set.range actualMarkedStrip = closure facingRegion := by
    apply Set.Subset.antisymm actual_marked_strip_range_in_facing_closure
    intro z hz
    rw [closure_eq_self_union_frontier,actual_facing_region_geometry.2.2] at hz
    rcases hz with hf | ⟨t,ht⟩ | ⟨t,ht⟩
    · rw [← actual_marked_strip_interior_eq_facing] at hf
      exact Set.image_subset_range _ _ hf
    · let s : ℝ := (t-sourceParameter)/(2*Real.pi)
      have he : sourceParameter+s*(2*Real.pi) = t := by dsimp [s];field_simp;ring
      refine ⟨(s,0),?_⟩
      rw [actual_marked_strip_bottom,he]
      exact ht
    · let s : ℝ := (t-targetParameter)/(2*Real.pi)
      have he : targetParameter+s*(2*Real.pi) = t := by dsimp [s];field_simp;ring
      refine ⟨(s,1),?_⟩
      rw [actual_marked_strip_top,he]
      exact ht
  have actual_axis_periodic_strip_bounded {X : Type} [MetricSpace X]
      (F : C(ℝ × Interval,X)) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
      (htranslate : ∀ t, g (axis t) = axis (t+τ))
      (hperiod : ∀ x : ℝ × Interval, F (x.1+1,x.2) = g (F x)) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ × Interval, dist (F x) (axis (x.1*τ)) ≤ M := by
    let δ : ℝ × Interval → ℝ := fun x => dist (F x) (axis (x.1*τ))
    have hδcont : Continuous δ := F.continuous.dist
      (haxis.continuous.comp (continuous_fst.mul continuous_const))
    have hδperiod (v : Interval) : Function.Periodic (fun s => δ (s,v)) 1 := by
      intro s
      dsimp [δ]
      have ht : (s+1)*τ = s*τ+τ := by ring
      rw [hperiod (s,v),ht,← htranslate,hg.dist_eq]
    have hcompact : IsCompact (δ '' (Set.Icc (0:ℝ) 1 ×ˢ (Set.univ : Set Interval))) :=
      (isCompact_Icc.prod isCompact_univ).image hδcont
    obtain ⟨M,hM⟩ := hcompact.bddAbove
    have hbound (x : ℝ × Interval) : δ x ≤ M := by
      have hrange : δ x ∈ Set.range (fun s => δ (s,x.2)) := ⟨x.1,rfl⟩
      rw [← (hδperiod x.2).image_Icc (by norm_num : (0:ℝ)<1) 0] at hrange
      obtain ⟨s,hs,hsEq⟩ := hrange
      exact hM ⟨(s,x.2),⟨by simpa using hs,Set.mem_univ _⟩,hsEq⟩
    exact ⟨M,(dist_nonneg.trans (hbound (0,0))),hbound⟩
  have actual_complete_geodesic_vertical_normalization (a : ℝ → H2) (ha : Isometry a) :
      ∃ A : SL(2,ℝ), ∀ t : ℝ, (A • verticalPath t : H2) = a t := by
    have hd : dist (a 0) (a 1) = 1 := by
      rw [ha.dist_eq,Real.dist_eq]
      norm_num
    obtain ⟨A,hA0,hA1⟩ := axis_exists_ordered_pair_matrix (a 0) (a 1) hd
    let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
    have he0 : e UpperHalfPlane.I = a 0 := hA0
    have he1 : e (verticalPath 1) = a 1 := hA1
    refine ⟨A,?_⟩
    intro t
    let z := e.symm (a t)
    have hv0 : verticalPath 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
    have h0 : dist z UpperHalfPlane.I = dist (verticalPath t) UpperHalfPlane.I := by
      have h := e.isometry.dist_eq z UpperHalfPlane.I
      rw [he0,show e z = a t from e.apply_symm_apply _] at h
      rw [← h,ha.dist_eq]
      simpa only [hv0] using (verticalPath_isometry.dist_eq t 0).symm
    have h1 : dist z (verticalPath 1) = dist (verticalPath t) (verticalPath 1) := by
      have h := e.isometry.dist_eq z (verticalPath 1)
      rw [he1,show e z = a t from e.apply_symm_apply _] at h
      rw [← h,ha.dist_eq]
      exact (verticalPath_isometry.dist_eq t 1).symm
    obtain ⟨him,hre⟩ := axis_two_anchor_coordinates z (verticalPath t) h0 h1
    have hz : z = verticalPath t := by
      apply UpperHalfPlane.ext_re_im
      · simp only [verticalPath,UpperHalfPlane.mk_re] at hre ⊢
        nlinarith only [hre]
      · exact him
    change e (verticalPath t) = a t
    rw [← hz]
    exact e.apply_symm_apply _
  have vertical_tube_ideal_boundary (A : Set H2) (B : ℝ) (hB : 0 ≤ B)
      (hA : ∀ z ∈ A, ∃ t : ℝ, dist z (verticalPath t) ≤ B) :
      closure ((fun z : H2 => (cayley z : ℂ)) '' A) ∩ {w : ℂ | ‖w‖ = 1} ⊆ {-1,1} := by
    have tube_cone (A : Set H2) (B : ℝ) (hB : 0 ≤ B)
        (hA : ∀ z ∈ A, ∃ t : ℝ, dist z (verticalPath t) ≤ B) :
        ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ A, |z.re| ≤ K*z.im := by
      have vertical_coordinate_bounds (z : H2) (t B : ℝ) (hB : 0 ≤ B)
          (hd : dist z (verticalPath t) ≤ B) :
          Real.exp (t-B) ≤ z.im ∧
            ‖(z : ℂ)‖ ≤ (Real.sinh B+Real.cosh B)*Real.exp t := by
        have hlog := (UpperHalfPlane.dist_log_im_le z (verticalPath t)).trans hd
        simp only [verticalPath,UpperHalfPlane.mk_im,Real.log_exp,Real.dist_eq] at hlog
        have hlower : t-B ≤ Real.log z.im := by
          have h := (abs_le.mp hlog).1
          linarith
        have him : Real.exp (t-B) ≤ z.im := by
          have h := Real.exp_le_exp.mpr hlower
          simpa only [Real.exp_log z.im_pos] using h
        refine ⟨him,?_⟩
        have hball := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hd
        have hcenter : ((verticalPath t).center B : ℂ) =
            ((Real.exp t*Real.cosh B : ℝ) : ℂ)*Complex.I := by
          apply Complex.ext <;> simp [UpperHalfPlane.center,verticalPath,← Complex.ofReal_exp]
        have hnorm : ‖((verticalPath t).center B : ℂ)‖ = Real.exp t*Real.cosh B := by
          rw [hcenter,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
          exact abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
        have hball' : dist (z : ℂ) ((verticalPath t).center B : ℂ) ≤ Real.exp t*Real.sinh B := by
          simpa [verticalPath] using hball
        calc
          ‖(z : ℂ)‖ ≤ dist (z : ℂ) ((verticalPath t).center B : ℂ)+‖((verticalPath t).center B : ℂ)‖ :=
            by simpa only [dist_zero_right] using dist_triangle (z : ℂ) ((verticalPath t).center B : ℂ) 0
          _ ≤ Real.exp t*Real.sinh B+Real.exp t*Real.cosh B := add_le_add hball' hnorm.le
          _ = (Real.sinh B+Real.cosh B)*Real.exp t := by ring
    
      let C : ℝ := Real.sinh B + Real.cosh B
      have hC : 0 ≤ C := add_nonneg (Real.sinh_nonneg_iff.mpr hB) (Real.cosh_pos B).le
      let K : ℝ := C*Real.exp B
      have hK : 0 ≤ K := mul_nonneg hC (Real.exp_pos B).le
      refine ⟨K,hK,?_⟩
      intro z hz
      obtain ⟨t,ht⟩ := hA z hz
      obtain ⟨him,hnorm⟩ := vertical_coordinate_bounds z t B hB ht
      have habs : |z.re| ≤ ‖(z:ℂ)‖ := Complex.abs_re_le_norm _
      have he : Real.exp t = Real.exp B*Real.exp (t-B) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        |z.re| ≤ ‖(z:ℂ)‖ := habs
        _ ≤ C*Real.exp t := hnorm
        _ = K*Real.exp (t-B) := by rw [he]; dsimp [K]; ring
        _ ≤ K*z.im := mul_le_mul_of_nonneg_left him hK
    have cone_boundary (A : Set H2) (K : ℝ) (hK : 0 ≤ K)
        (hA : ∀ z ∈ A, |z.re| ≤ K*z.im) :
        closure ((fun z : H2 => (cayley z : ℂ)) '' A) ∩ {w : ℂ | ‖w‖ = 1} ⊆ {-1,1} := by
      let Q : Set ℂ := {w | |w.im| ≤ K/2*(1-Complex.normSq w)}
      have hQ : IsClosed Q := isClosed_le (Complex.continuous_im.abs)
        (continuous_const.mul (continuous_const.sub Complex.continuous_normSq))
      have hsub : (fun z : H2 => (cayley z : ℂ)) '' A ⊆ Q := by
        rintro w ⟨z,hz,rfl⟩
        have hy := z.im_pos
        have hD : 0 < Complex.normSq ((z:ℂ)+Complex.I) := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re,Complex.add_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
            Complex.I_re,Complex.I_im,add_zero]
          nlinarith [sq_nonneg z.re, sq_nonneg (z.im+1)]
        have hi : (cayley z : ℂ).im = -2*z.re/Complex.normSq ((z:ℂ)+Complex.I) := by
          change (((z:ℂ)-Complex.I)/((z:ℂ)+Complex.I)).im = _
          rw [Complex.div_im]
          simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
            UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,Complex.I_re,Complex.I_im,sub_zero,add_zero]
          congr 1
          ring
        have hn : 1-Complex.normSq (cayley z : ℂ) =
            4*z.im/Complex.normSq ((z:ℂ)+Complex.I) := by
          change 1-Complex.normSq (((z:ℂ)-Complex.I)/((z:ℂ)+Complex.I)) = _
          rw [Complex.normSq_div]
          field_simp
          simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,
            Complex.add_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,Complex.I_re,Complex.I_im,
            sub_zero,add_zero]
          ring
        change |(cayley z : ℂ).im| ≤ K/2*(1-Complex.normSq (cayley z : ℂ))
        rw [hi,hn,abs_div,abs_of_pos hD,abs_mul]
        norm_num
        apply (div_le_iff₀ hD).mpr
        field_simp
        nlinarith [hA z hz]
      have hclosed : closure ((fun z : H2 => (cayley z : ℂ)) '' A) ⊆ Q :=
        closure_minimal hsub hQ
      intro w hw
      have hineq := hclosed hw.1
      have hn : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq,hw.2]; norm_num
      have hi : w.im = 0 := by
        change |w.im| ≤ K/2*(1-Complex.normSq w) at hineq
        rw [hn] at hineq
        simpa using abs_eq_zero.mp (le_antisymm (by simpa using hineq) (abs_nonneg _))
      have hr : w.re^2 = 1 := by
        rw [Complex.normSq_apply,hi] at hn
        nlinarith
      rcases sq_eq_one_iff.mp hr with hr | hr
      · right
        apply Complex.ext <;> simp [hr,hi]
      · left
        apply Complex.ext <;> simp [hr,hi]
    obtain ⟨K,hK,hAK⟩ := tube_cone A B hB hA
    exact cone_boundary A K hK hAK
  obtain ⟨stripAxisBound,stripAxisBound_nonnegative,stripAxisBound_control⟩ :=
    actual_axis_periodic_strip_bounded actualMarkedStripMap (developedDeck monodromy)
      (all_developed_decks_isometric monodromy) actualAxis hactualAxis axisPeriod haxisPeriod
      haxisTranslate actual_marked_strip_monodromy
  obtain ⟨axisNormalizer,axisNormalizer_control⟩ :=
    actual_complete_geodesic_vertical_normalization actualAxis hactualAxis
  let axisNormalizingIsometry : H2 ≃ᵢ H2 := IsometryEquiv.constSMul axisNormalizer
  let normalizedMarkedStrip : ℝ × Interval → H2 :=
    fun x => axisNormalizingIsometry.symm (actualMarkedStrip x)
  have normalizedMarkedStrip_tube : ∀ z ∈ Set.range normalizedMarkedStrip,
      ∃ t : ℝ, dist z (verticalPath t) ≤ stripAxisBound := by
    rintro z ⟨x,rfl⟩
    refine ⟨x.1*axisPeriod,?_⟩
    have he := axisNormalizingIsometry.isometry.dist_eq (normalizedMarkedStrip x)
      (verticalPath (x.1*axisPeriod))
    rw [axisNormalizingIsometry.apply_symm_apply] at he
    change dist (actualMarkedStrip x) (axisNormalizer • verticalPath (x.1*axisPeriod)) = _ at he
    rw [axisNormalizer_control] at he
    rw [←he]
    exact stripAxisBound_control x
  have actual_normalized_marked_strip_has_only_axis_ideal_ends :
      closure ((fun z : H2 => (cayley z : ℂ)) '' Set.range normalizedMarkedStrip) ∩
        {w : ℂ | ‖w‖ = 1} ⊆ {-1,1} :=
    vertical_tube_ideal_boundary _ stripAxisBound stripAxisBound_nonnegative normalizedMarkedStrip_tube
  open Matrix in
  open scoped MatrixGroups in
  have translated_boundary_stabilizes_axis (F : ℝ × unitInterval → H2) (axis : ℝ → H2)
      (e : H2 ≃ᵢ H2) (he : ∀ t : ℝ, e (verticalPath t) = axis t)
      (τ M : ℝ) (hτ : 0 < τ) (hM : 0 ≤ M)
      (hbound : ∀ x : ℝ × unitInterval, dist (F x) (axis (x.1*τ)) ≤ M)
      (g : H2 ≃ᵢ H2) (hgF : ∀ t : ℝ, g (F (t,0)) ∈ Set.range F) :
      g '' Set.range axis = Set.range axis := by
    have tube_cone (A : Set H2) (B : ℝ) (hB : 0 ≤ B)
        (hA : ∀ z ∈ A, ∃ t : ℝ, dist z (verticalPath t) ≤ B) :
        ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ A, |z.re| ≤ K*z.im := by
      have vertical_coordinate_bounds (z : H2) (t B : ℝ) (hB : 0 ≤ B)
          (hd : dist z (verticalPath t) ≤ B) :
          Real.exp (t-B) ≤ z.im ∧
            ‖(z : ℂ)‖ ≤ (Real.sinh B+Real.cosh B)*Real.exp t := by
        have hlog := (UpperHalfPlane.dist_log_im_le z (verticalPath t)).trans hd
        simp only [verticalPath,UpperHalfPlane.mk_im,Real.log_exp,Real.dist_eq] at hlog
        have hlower : t-B ≤ Real.log z.im := by
          have h := (abs_le.mp hlog).1
          linarith
        have him : Real.exp (t-B) ≤ z.im := by
          have h := Real.exp_le_exp.mpr hlower
          simpa only [Real.exp_log z.im_pos] using h
        refine ⟨him,?_⟩
        have hball := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hd
        have hcenter : ((verticalPath t).center B : ℂ) =
            ((Real.exp t*Real.cosh B : ℝ) : ℂ)*Complex.I := by
          apply Complex.ext <;> simp [UpperHalfPlane.center,verticalPath,← Complex.ofReal_exp]
        have hnorm : ‖((verticalPath t).center B : ℂ)‖ = Real.exp t*Real.cosh B := by
          rw [hcenter,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
          exact abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
        have hball' : dist (z : ℂ) ((verticalPath t).center B : ℂ) ≤ Real.exp t*Real.sinh B := by
          simpa [verticalPath] using hball
        calc
          ‖(z : ℂ)‖ ≤ dist (z : ℂ) ((verticalPath t).center B : ℂ)+‖((verticalPath t).center B : ℂ)‖ :=
            by simpa only [dist_zero_right] using dist_triangle (z : ℂ) ((verticalPath t).center B : ℂ) 0
          _ ≤ Real.exp t*Real.sinh B+Real.exp t*Real.cosh B := add_le_add hball' hnorm.le
          _ = (Real.sinh B+Real.cosh B)*Real.exp t := by ring
    
      let C : ℝ := Real.sinh B + Real.cosh B
      have hC : 0 ≤ C := add_nonneg (Real.sinh_nonneg_iff.mpr hB) (Real.cosh_pos B).le
      let K : ℝ := C*Real.exp B
      have hK : 0 ≤ K := mul_nonneg hC (Real.exp_pos B).le
      refine ⟨K,hK,?_⟩
      intro z hz
      obtain ⟨t,ht⟩ := hA z hz
      obtain ⟨him,hnorm⟩ := vertical_coordinate_bounds z t B hB ht
      have habs : |z.re| ≤ ‖(z:ℂ)‖ := Complex.abs_re_le_norm _
      have he : Real.exp t = Real.exp B*Real.exp (t-B) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        |z.re| ≤ ‖(z:ℂ)‖ := habs
        _ ≤ C*Real.exp t := hnorm
        _ = K*Real.exp (t-B) := by rw [he]; dsimp [K]; ring
        _ ≤ K*z.im := mul_le_mul_of_nonneg_left him hK
    have cone_axis (A : GL (Fin 2) ℝ) (K : ℝ) (hK : 0 ≤ K)
        (hbound : ∀ t : ℝ, |(A • verticalPath t : H2).re| ≤ K*(A • verticalPath t : H2).im) :
        ∀ t : ℝ, (A • verticalPath t : H2).re = 0 := by
      have bounded_coefficients (a b K : ℝ) (hK : 0 ≤ K)
          (hbound : ∀ r : ℝ, 0 < r → |a*r^2+b| ≤ K*r) : a=0 ∧ b=0 := by
        have ha : a=0 := by
          by_contra hane
          have habs : 0 < |a| := abs_pos.mpr hane
          let r : ℝ := (K+|b|+1)/|a|+1
          have hr : 1 < r := by
            have hh : 0 < (K+|b|+1)/|a| := div_pos (by positivity) habs
            dsimp [r]
            linarith
          have har : |a| *r = K+|b|+1+|a| := by
            dsimp [r]
            field_simp <;> ring
          have h := hbound r (by linarith)
          have ht : |a*r^2| ≤ |a*r^2+b|+|b| := by
            calc
              |a*r^2| = |a*r^2+b-b| := by congr 1;ring
              _ ≤ |a*r^2+b|+|b| := by
                simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (a*r^2+b) 0 b
          have he : |a*r^2| = |a| *r^2 := by rw [abs_mul,abs_sq]
          rw [he] at ht
          nlinarith [abs_nonneg b]
        have hb : b=0 := by
          by_contra hbne
          have hbabs : 0 < |b| := abs_pos.mpr hbne
          let r : ℝ := |b|/(2*(K+1))
          have hr : 0 < r := by dsimp [r];positivity
          have he : 2*(K+1)*r=|b| := by dsimp [r];field_simp
          have h := hbound r hr
          rw [ha,zero_mul,zero_add] at h
          nlinarith
        exact ⟨ha,hb⟩
      have hRe (r : ℝ) (hr : 0 < r) :
          (A • verticalPath (Real.log r) : H2).re =
            (A 0 0*A 1 0*r^2+A 0 1*A 1 1)/Complex.normSq (UpperHalfPlane.denom A (verticalPath (Real.log r))) := by
        rw [UpperHalfPlane.re_smul]
        simp only [UpperHalfPlane.num,UpperHalfPlane.denom,Complex.div_re,
          Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
          Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
          verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,Real.exp_log hr,
          mul_zero,zero_mul,sub_zero,add_zero,zero_add]
        congr 1
        ring
      have hcoef : ∀ r : ℝ, 0 < r → |(A 0 0*A 1 0)*r^2+(A 0 1*A 1 1)| ≤
          (K*|A.det.val|)*r := by
        intro r hr
        have h := hbound (Real.log r)
        have hD : 0 < Complex.normSq (UpperHalfPlane.denom A (verticalPath (Real.log r))) :=
          UpperHalfPlane.normSq_denom_pos A (verticalPath (Real.log r)).im_ne_zero
        rw [hRe r hr,UpperHalfPlane.im_smul_eq_div_normSq,abs_div,abs_of_pos hD] at h
        have he : (verticalPath (Real.log r)).im = r := by simp [verticalPath,Real.exp_log hr]
        rw [he,←mul_div_assoc] at h
        have hh := (div_le_div_iff_of_pos_right hD).mp h
        nlinarith
      obtain ⟨hac,hbd⟩ := bounded_coefficients (A 0 0*A 1 0) (A 0 1*A 1 1)
        (K*|A.det.val|) (mul_nonneg hK (abs_nonneg _)) hcoef
      intro t
      have he : Real.log (Real.exp t) = t := Real.log_exp t
      rw [←he,hRe _ (Real.exp_pos t),hac,hbd]
      simp
    have axis_range (g : H2 ≃ᵢ H2) (hre : ∀ t : ℝ, (g (verticalPath t)).re = 0) :
        g '' Set.range verticalPath = Set.range verticalPath := by
      have real_isometry_translation_or_reflection (f : ℝ → ℝ) (hf : Isometry f) :
          (∀t, f t=f 0+t) ∨ (∀t, f t=f 0-t) := by
        have h01 := hf.dist_eq 1 0
        simp only [Real.dist_eq, sub_zero, abs_one] at h01
        have hsign : f 1-f 0 = 1 ∨ f 1-f 0 = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h01
        have heq (t : ℝ) : (f t-f 0)^2=t^2 ∧ (f t-f 1)^2=(t-1)^2 := by
          have h0 := hf.dist_eq t 0
          have h1 := hf.dist_eq t 1
          simp only [Real.dist_eq, sub_zero] at h0 h1
          constructor
          · nlinarith only [sq_abs (f t-f 0),sq_abs t, congrArg (fun x : ℝ => x^2) h0]
          · nlinarith only [sq_abs (f t-f 1),sq_abs (t-1), congrArg (fun x : ℝ => x^2) h1]
        rcases hsign with hp | hn
        · have hall (t : ℝ) : f t = f 0+t := by
            obtain ⟨h0,h1⟩ := heq t
            nlinarith only [h0,h1,hp]
          exact Or.inl hall
        · have hall (t : ℝ) : f t = f 0-t := by
            obtain ⟨h0,h1⟩ := heq t
            nlinarith only [h0,h1,hn]
          exact Or.inr hall
      
      
      let q : ℝ → ℝ := fun t => Real.log (g (verticalPath t)).im
      have hcoord (t : ℝ) : g (verticalPath t) = verticalPath (q t) := by
        apply UpperHalfPlane.ext_re_im
        · rw [hre]
          rfl
        · change (g (verticalPath t)).im = Real.exp (Real.log (g (verticalPath t)).im)
          exact (Real.exp_log (g (verticalPath t)).im_pos).symm
      have hq : Isometry q := by
        apply Isometry.of_dist_eq
        intro t u
        rw [←verticalPath_isometry.dist_eq,←hcoord,←hcoord,g.isometry.dist_eq,verticalPath_isometry.dist_eq]
      have hqsurj : Function.Surjective q := by
        rcases real_isometry_translation_or_reflection q hq with hp | hn
        · intro r
          exact ⟨r-q 0,by rw [hp];ring⟩
        · intro r
          exact ⟨q 0-r,by rw [hn];ring⟩
      ext z
      constructor
      · rintro ⟨_,⟨t,rfl⟩,rfl⟩
        exact ⟨q t,(hcoord t).symm⟩
      · rintro ⟨r,rfl⟩
        obtain ⟨t,ht⟩ := hqsurj r
        exact ⟨verticalPath t,Set.mem_range_self t,(hcoord t).trans (congrArg verticalPath ht)⟩
    let gn : H2 ≃ᵢ H2 := (e.trans g).trans e.symm
    have hgn (z : H2) : gn z = e.symm (g (e z)) := rfl
    have htube : ∀ z ∈ Set.range (fun t : ℝ => gn (verticalPath t)),
        ∃ r : ℝ, dist z (verticalPath r) ≤ 2*M := by
      rintro z ⟨t,rfl⟩
      let x : ℝ × unitInterval := (t/τ,0)
      obtain ⟨y,hy⟩ := hgF (t/τ)
      refine ⟨y.1*τ,?_⟩
      have hx : x.1*τ = t := by dsimp [x];field_simp
      have hd : dist (g (axis t)) (axis (y.1*τ)) ≤ 2*M := by
        have hb := hbound x
        rw [hx] at hb
        calc
          dist (g (axis t)) (axis (y.1*τ)) ≤
              dist (g (axis t)) (g (F x))+dist (g (F x)) (axis (y.1*τ)) := dist_triangle _ _ _
          _ = dist (axis t) (F x)+dist (F y) (axis (y.1*τ)) := by
            rw [g.isometry.dist_eq,←hy]
          _ ≤ M+M := add_le_add (by simpa only [dist_comm] using hb) (hbound y)
          _ = 2*M := by ring
      have hdist := e.isometry.dist_eq (gn (verticalPath t)) (verticalPath (y.1*τ))
      rw [hgn,e.apply_symm_apply,he,he] at hdist
      change dist (gn (verticalPath t)) (verticalPath (y.1*τ)) ≤ 2*M
      rw [hgn,he]
      rw [hdist] at hd
      exact hd
    obtain ⟨K,hK,hcone⟩ := tube_cone _ (2*M) (by positivity) htube
    obtain ⟨A,hA⟩ := axis_metric_isometry_gl_representation gn
    have hre : ∀ t : ℝ, (gn (verticalPath t)).re = 0 := by
      have hB : ∀ t : ℝ, |(A • verticalPath t : H2).re| ≤ K*(A • verticalPath t : H2).im := by
        intro t
        rw [←hA]
        exact hcone _ (Set.mem_range_self t)
      intro t
      rw [hA]
      exact cone_axis A K hK hB t
    have hrange := axis_range gn hre
    ext z
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      have hm : gn (verticalPath t) ∈ Set.range verticalPath := by
        rw [←hrange]
        exact Set.mem_image_of_mem gn (Set.mem_range_self t)
      obtain ⟨r,hr⟩ := hm
      refine ⟨r,?_⟩
      have h := congrArg e hr
      rw [hgn,e.apply_symm_apply,he,he] at h
      exact h
    · rintro ⟨r,rfl⟩
      have hm : verticalPath r ∈ gn '' Set.range verticalPath := by
        rw [hrange]
        exact Set.mem_range_self r
      obtain ⟨_,⟨t,rfl⟩,ht⟩ := hm
      refine ⟨axis t,Set.mem_range_self t,?_⟩
      have h := congrArg e ht
      rw [hgn,e.apply_symm_apply,he,he] at h
      exact h
  have actual_source_translate_inside_strip_stabilizes_axis
      (k : deck (Sigma.fst : P → A))
      (hk : developedDeck k '' Set.range sourceLift ⊆ Set.range actualMarkedStrip) :
      developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
    let g : H2 ≃ᵢ H2 := ⟨(developedDeck k).toEquiv,all_developed_decks_isometric k⟩
    apply translated_boundary_stabilizes_axis actualMarkedStrip actualAxis axisNormalizingIsometry
      axisNormalizer_control axisPeriod stripAxisBound haxisPeriod stripAxisBound_nonnegative
      stripAxisBound_control g
    intro t
    have ht : actualMarkedStrip (t,0) ∈ Set.range sourceLift := by
      rw [actual_marked_strip_bottom]
      exact Set.mem_range_self _
    exact hk (Set.mem_image_of_mem _ ht)
  have dilation_root_line_meeting (F : C(ℝ,H2)) (hF : IsProperMap F) (hinj : Function.Injective F)
      (e : H2 ≃ₜ ℝ × ℝ) (g : H2 ≃ᵢ H2) (L T : ℝ) (hL : L ≠ 0) (hT : 0 < T)
      (n : ℕ) (hn : 0 < n)
      (hcoord : ∀ z, e (g z) = e z + (L,0))
      (hperiod : ∀ (k : ℤ) (t : ℝ), F (t+(k:ℝ)*T) = (g^(k*(n:ℤ))) (F t)) :
      ¬ Disjoint (Set.range F) (g '' Set.range F) := by
    have hpow (k : ℤ) (z : H2) : e ((g^k) z) = e z + ((k:ℝ)*L,0) := by
      have hnat (m : ℕ) (z : H2) : e ((g^m) z) = e z + ((m:ℝ)*L,0) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ']
          change e (g ((g^m) z)) = _
          rw [hcoord,ih]
          ext <;> simp <;> ring
      cases k with
      | ofNat m => simpa using hnat m z
      | negSucc m =>
        have h := hnat (m+1) ((g^(-(m+1:ℤ))) z)
        have hc : (g^(m+1)) ((g^(-(m+1:ℤ))) z) = z := by
          change ((g^(m+1:ℤ))*(g^(-(m+1:ℤ)))) z = z
          rw [←_root_.zpow_add]
          simp
        rw [hc] at h
        rw [Int.negSucc_eq]
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        apply Prod.ext
        · simp only [Prod.fst_add,Prod.fst,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one]
          push_cast
          change (e z).1 = (e ((g^(-(m+1:ℤ))) z)).1 + ((m+1:ℕ):ℝ)*L at h1
          push_cast at h1
          linarith
        · change _ = (e z).2 + 0
          change (e z).2 = (e ((g^(-(m+1:ℤ))) z)).2 + 0 at h2
          linarith
    let FE : C(ℝ,ℝ × ℝ) := ⟨e ∘ F,e.continuous.comp F.continuous⟩
    have hFEperiod (k : ℤ) (t : ℝ) : FE (t+(k:ℝ)*T) =
        FE t + ((k:ℝ)*(n:ℝ)*L,(k:ℝ)*(n:ℝ)*0) := by
      change e (F _) = _
      rw [hperiod,hpow]
      push_cast
      simp [FE]
    have hmeet := CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.periodic_proper_line_meets_root_translate FE (e.isProperMap.comp hF)
      (e.injective.comp hinj) T L 0 hT (Or.inl hL) n hn hFEperiod
    intro hdis
    apply hmeet
    apply Set.disjoint_left.mpr
    rintro w ⟨s,rfl⟩ ⟨v,⟨t,rfl⟩,he⟩
    have hw : F s = g (F t) := e.injective ((hcoord _).trans he).symm
    exact Set.disjoint_left.mp hdis (Set.mem_range_self s)
      ⟨F t,Set.mem_range_self t,hw.symm⟩
  let deckIsometryHom : deck (Sigma.fst : P → A) →* H2 ≃ᵢ H2 :=
    { toFun := developedDeckIsometry
      map_one' := by
        ext z
        exact congrArg UpperHalfPlane.coe (actual_developedDeck_one z)
      map_mul' := by
        intro k l
        ext z
        exact congrArg UpperHalfPlane.coe (actual_developedDeck_mul k l z) }
  have actual_source_monodromy_has_no_proper_dilation_root
      (k : deck (Sigma.fst : P → A)) (n : ℕ) (hn : 0 < n)
      (hroot : monodromy = k^n)
      (e : H2 ≃ₜ ℝ × ℝ) (L : ℝ) (hL : L ≠ 0)
      (hcoord : ∀ z : H2, e (developedDeck k z) = e z+(L,0)) : n = 1 := by
    let clock : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ (2*Real.pi) (by positivity)
    let F : C(ℝ,H2) := ⟨sourceLift ∘ clock,sourceLift.continuous.comp clock.continuous⟩
    have hFclosed : Topology.IsClosedEmbedding F :=
      actual_sourceLift_closed_embedding.comp clock.isClosedEmbedding
    have hFperiod (j : ℤ) (t : ℝ) : F (t+(j:ℝ)*1) =
        ((deckIsometryHom k)^(j*(n:ℤ))) (F t) := by
      change sourceLift ((t+(j:ℝ)*1)*(2*Real.pi)) = _
      have he : (t+(j:ℝ)*1)*(2*Real.pi) = t*(2*Real.pi)+(j:ℝ)*(2*Real.pi) := by ring
      rw [he,actual_source_integer_period,hroot]
      have hp : (k^n)^j = k^(j*(n:ℤ)) := by
        rw [←_root_.zpow_natCast,←_root_.zpow_mul,mul_comm]
      rw [hp]
      have hm := deckIsometryHom.map_zpow k (j*(n:ℤ))
      exact congrArg (fun u : H2 ≃ᵢ H2 => u (F t)) hm
    have hmeet := dilation_root_line_meeting F hFclosed.isProperMap hFclosed.injective e
      (deckIsometryHom k) L 1 hL (by norm_num) n hn hcoord hFperiod
    have hr : Set.range F = Set.range sourceLift := by
      change Set.range (sourceLift ∘ clock) = Set.range sourceLift
      rw [Set.range_comp,Set.range_eq_univ.mpr clock.surjective,Set.image_univ]
    rw [hr] at hmeet
    have hs : developedDeck k '' Set.range sourceLift = Set.range sourceLift := by
      rcases actual_all_source_deck_lifts_equal_or_disjoint k with h | h
      · exact h
      · exact False.elim (hmeet h.symm)
    obtain ⟨m,hm⟩ := actual_source_stabilizer_is_common_cyclic k hs
    have he : (1:ℤ) = m*(n:ℤ) := by
      apply actual_common_monodromy_powers_injective
      change monodromy^(1:ℤ) = monodromy^(m*(n:ℤ))
      rw [zpow_one]
      calc
        monodromy = k^n := hroot
        _ = (monodromy^m)^n := by rw [hm]
        _ = monodromy^(m*(n:ℤ)) := by rw [←_root_.zpow_natCast,_root_.zpow_mul]
    have hh := Int.mul_eq_one_iff_eq_one_or_neg_one.mp he.symm
    rcases hh with h | h
    · exact_mod_cast h.2
    · have hnreal : (0:ℤ) < (n:ℤ) := by exact_mod_cast hn
      omega
  let normalizedDevelopment : P ≃ₜ H2 :=
    development.trans axisNormalizingIsometry.symm.toHomeomorph
  have normalizedDevelopment_metric : ∀ x : P, ∃ U : Set P, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist y.1 z.1 =
        dist (normalizedDevelopment y) (normalizedDevelopment z) := by
    intro x
    obtain ⟨U,hU,hx,hm⟩ := development_metric x
    refine ⟨U,hU,hx,?_⟩
    intro y hy z hz
    exact (hm y hy z hz).trans
      (axisNormalizingIsometry.symm.isometry.dist_eq (development y) (development z)).symm
  have normalized_original_axis_period (t : ℝ) :
      normalizedDevelopment (monodromy • normalizedDevelopment.symm (verticalPath t)) =
        verticalPath (t+axisPeriod) := by
    change axisNormalizingIsometry.symm (development
      (monodromy • development.symm (axisNormalizingIsometry (verticalPath t)))) = _
    rw [show axisNormalizingIsometry (verticalPath t) = actualAxis t from axisNormalizer_control t]
    change axisNormalizingIsometry.symm (developedDeckIsometry monodromy (actualAxis t)) = _
    rw [haxisTranslate,←axisNormalizer_control]
    exact axisNormalizingIsometry.symm_apply_apply _
  obtain ⟨axisPeriodHom,axisPeriodHom_injective,axisPeriodHom_action,
    minimalAxisPeriod,minimalAxisPeriod_positive,minimalAxisDeck,minimalAxisDeck_period,
    axisPeriods_lattice⟩ :=
    CurveComplex.Hyperbolic.actual_canonical_deck_axis_minimal_period Sigma.fst hqc
      normalizedDevelopment normalizedDevelopment_metric monodromy axisPeriod haxisPeriod
      normalized_original_axis_period
  let liftedNormalizedAxis : ℝ → P := fun t => normalizedDevelopment.symm (verticalPath t)
  let axisStabilizer := MulAction.stabilizer (deck (Sigma.fst : P → A))
    (Set.range liftedNormalizedAxis)
  have actual_every_axis_stabilizer_is_minimal_generator_power (k : axisStabilizer) :
      ∃ n : ℤ, k = minimalAxisDeck^n := by
    have hm : axisPeriodHom (Additive.ofMul k) ∈ AddSubgroup.zmultiples minimalAxisPeriod := by
      rw [←axisPeriods_lattice]
      exact ⟨Additive.ofMul k,rfl⟩
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    refine ⟨n,?_⟩
    apply Additive.ofMul.injective
    apply axisPeriodHom_injective
    rw [ofMul_zpow,map_zsmul,minimalAxisDeck_period]
    exact hn.symm
  have original_monodromy_in_axis_stabilizer : monodromy ∈ axisStabilizer := by
    apply MulAction.mem_stabilizer_iff.mpr
    change (fun z : P => monodromy • z) '' Set.range liftedNormalizedAxis =
      Set.range liftedNormalizedAxis
    have hact (t : ℝ) : monodromy • liftedNormalizedAxis t =
        liftedNormalizedAxis (t+axisPeriod) := by
      apply normalizedDevelopment.injective
      exact (normalized_original_axis_period t).trans
        (normalizedDevelopment.apply_symm_apply _).symm
    apply Set.Subset.antisymm
    · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨t+axisPeriod,(hact t).symm⟩
    · rintro _ ⟨t,rfl⟩
      exact ⟨liftedNormalizedAxis (t-axisPeriod),Set.mem_range_self _,by
        change monodromy • liftedNormalizedAxis (t-axisPeriod) = liftedNormalizedAxis t
        rw [hact,sub_add_cancel]⟩
  let originalAxisDeck : axisStabilizer := ⟨monodromy,original_monodromy_in_axis_stabilizer⟩
  have original_axis_deck_period : axisPeriodHom (Additive.ofMul originalAxisDeck) = axisPeriod := by
    have ht := axisPeriodHom_action originalAxisDeck 0
    rw [zero_add] at ht
    apply verticalPath_isometry.injective
    exact ht.symm.trans (by simpa only [zero_add] using normalized_original_axis_period 0)
  obtain ⟨originalAxisIndex,originalAxisIndex_power⟩ :=
    actual_every_axis_stabilizer_is_minimal_generator_power originalAxisDeck
  have original_axis_index_positive : 0 < originalAxisIndex := by
    have ht := congrArg (fun k => axisPeriodHom (Additive.ofMul k)) originalAxisIndex_power
    rw [original_axis_deck_period,ofMul_zpow,map_zsmul,minimalAxisDeck_period] at ht
    rw [zsmul_eq_mul] at ht
    change axisPeriod = (originalAxisIndex:ℝ)*minimalAxisPeriod at ht
    have hp : (0:ℝ) < originalAxisIndex := by nlinarith [haxisPeriod,minimalAxisPeriod_positive]
    exact_mod_cast hp
  have original_monodromy_minimal_axis_root :
      monodromy = minimalAxisDeck.val ^ originalAxisIndex := by
    exact congrArg Subtype.val originalAxisIndex_power
  have h2glideNoDisjoint (F : C(ℝ,H2)) (hF : IsProperMap F) (hi : Function.Injective F)
    (T L : ℝ) (hT : 0 < T) (hL : 0 < L)
    (g : H2 ≃ₜ H2)
    (hg : ∀ z, (g z).re = -Real.exp L*z.re ∧ (g z).im = Real.exp L*z.im)
    (hperiod : ∀ t, F (t+T) = g (F t))
    (R : Set H2) (hR : IsConnected R) (hdis : Disjoint R (Set.range F))
    (hfix : g '' R = R) : False := by
    have planar (F : C(ℝ,Plane)) (hF : IsProperMap F) (hi : Function.Injective F)
      (T L : ℝ) (hT : 0 < T) (hL : 0 < L)
      (e : Plane ≃ₜ Plane) (he : ∀ z, e z = Plane.mk (z 0+L) (-z 1))
      (hperiod : ∀ t, F (t+T) = e (F t))
      (R : Set Plane) (hR : IsConnected R) (hdis : Disjoint R (Set.range F))
      (hfix : e '' R = R) : False := by
      have geometry (F : C(ℝ,Plane)) (hF : IsProperMap F) (hi : Function.Injective F)
        (B : ℝ) (hB : 0 < B) (hbound : ∀ t, |F t 1| < B)
        (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
        (e : Plane ≃ₜ Plane) (L : ℝ) (he : ∀ z, e z = Plane.mk (z 0+L) (-z 1))
        (hline : e '' Set.range F = Set.range F)
        (R : Set Plane) (hR : IsConnected R) (hdis : Disjoint R (Set.range F))
        (hfix : e '' R = R) : False := by
        have no_crossing (F : C(ℝ, Plane)) (B : ℝ) (hB : 0 < B)
            (hbound : ∀ x : ℝ, |F x 1| < B)
            (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
            (u w : Plane) (hu : u 1 ≤ -B) (hw : B ≤ w 1) :
            ¬ JoinedIn (Set.range F)ᶜ u w := by
          have crossing_strip {a b c d : ℝ} (hab : a < b) (hcd : c < d)
              (h v : ℝ → Plane)
              (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
              (hhY : ∀ t ∈ Icc (-1 : ℝ) 1, c < h t 1 ∧ h t 1 < d)
              (hvX : ∀ t ∈ Icc (-1 : ℝ) 1, a < v t 0 ∧ v t 0 < b)
              (hh1 : h (-1) 0 ≤ a) (hh2 : b ≤ h 1 0)
              (hv1 : v (-1) 1 ≤ c) (hv2 : d ≤ v 1 1) :
              ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
            let H : ℝ → Plane := fun s => !₂[max a (min b (h s 0)), h s 1]
            let V : ℝ → Plane := fun t => !₂[v t 0, max c (min d (v t 1))]
            have hH : ContinuousOn H (Icc (-1) 1) := by
              apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
              apply continuousOn_pi.mpr
              intro i
              fin_cases i
              · exact (show Continuous (fun x : ℝ => max a (min b x)) by fun_prop).comp_continuousOn
                  ((EuclideanSpace.proj 0).continuous.comp_continuousOn hh)
              · exact (EuclideanSpace.proj 1).continuous.comp_continuousOn hh
            have hV : ContinuousOn V (Icc (-1) 1) := by
              apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
              apply continuousOn_pi.mpr
              intro i
              fin_cases i
              · exact (EuclideanSpace.proj 0).continuous.comp_continuousOn hv
              · exact (show Continuous (fun x : ℝ => max c (min d x)) by fun_prop).comp_continuousOn
                  ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv)
            have hHE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                H t 0 ∈ Icc a b ∧ H t 1 ∈ Icc c d := by
              exact ⟨⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩, (hhY t ht).1.le, (hhY t ht).2.le⟩
            have hVE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                V t 0 ∈ Icc a b ∧ V t 1 ∈ Icc c d := by
              exact ⟨⟨(hvX t ht).1.le, (hvX t ht).2.le⟩, le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
            have hH1 : H (-1) 0 = a := by
              dsimp [H]
              rw [min_eq_right (hh1.trans hab.le), max_eq_left hh1]
            have hH2 : H 1 0 = b := by
              dsimp [H]
              rw [min_eq_left hh2, max_eq_right hab.le]
            have hV1 : V (-1) 1 = c := by
              dsimp [V]
              rw [min_eq_right (hv1.trans hcd.le), max_eq_left hv1]
            have hV2 : V 1 1 = d := by
              dsimp [V]
              rw [min_eq_left hv2, max_eq_right hcd.le]
            obtain ⟨s, hs, t, ht, he⟩ := ClassificationJordanCurve.crossing ClassificationJordanCurve.Brouwer.brouwerFPT
              hab.le hcd.le H V hH hV hHE hVE hH1 hH2 hV1 hV2
            have clamp {l u x z : ℝ} (hlu : l < u) (hz : l < z ∧ z < u)
                (he : max l (min u x) = z) : x = z := by
              by_cases hx : x ≤ l
              · rw [min_eq_right (hx.trans hlu.le), max_eq_left hx] at he
                linarith [hz.1]
              · by_cases hxu : u ≤ x
                · rw [min_eq_left hxu, max_eq_right hlu.le] at he
                  linarith [hz.2]
                · rwa [min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hx)] at he
            refine ⟨s, hs, t, ht, ?_⟩
            have he0 := congrArg (fun p : Plane => p 0) he
            have he1 := congrArg (fun p : Plane => p 1) he
            ext i
            fin_cases i
            · exact clamp hab (hvX t ht) he0
            · exact (clamp hcd (hhY s hs) he1.symm).symm
          intro hjoin
          obtain ⟨v, hv, hv0, hv1, hvmem⟩ := ClassificationJordanCurve.arc_path hjoin
          have hvc : ContinuousOn (fun t : ℝ => |v t 0|) (Icc (-1) 1) :=
            continuous_abs.comp_continuousOn ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv)
          obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hvc).bddAbove
          let R := max M 0 + 1
          have hR : 0 < R := by dsimp [R]; positivity
          have hMv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |v t 0| < R := by
            have hm := hM (Set.mem_image_of_mem _ ht)
            dsimp [R]
            linarith [le_max_left M 0]
          obtain ⟨A, hA0, hA1⟩ := hends R
          let h : ℝ → Plane := fun s => F (A * s)
          have hhc : ContinuousOn h (Icc (-1) 1) :=
            (F.continuous.comp (by fun_prop : Continuous (fun s : ℝ => A * s))).continuousOn
          have hhY (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) : -B < h t 1 ∧ h t 1 < B :=
            abs_lt.mp (hbound (A * t))
          have hvX (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -R < v t 0 ∧ v t 0 < R :=
            abs_lt.mp (hMv t ht)
          have hh0 : h (-1) 0 ≤ -R := by simpa [h] using hA0.le
          have hh1 : R ≤ h 1 0 := by simpa [h] using hA1.le
          have hv0' : v (-1) 1 ≤ -B := by simpa [hv0] using hu
          have hv1' : B ≤ v 1 1 := by simpa [hv1] using hw
          obtain ⟨s, hs, t, ht, he⟩ := crossing_strip (by linarith : -R < R)
            (by linarith : -B < B) h v hhc hv hhY hvX hh0 hh1 hv0' hv1'
          exact hvmem t ht ⟨A * s, he⟩
        let p : Plane := Plane.mk 0 (B+1)
        let q : Plane := e p
        have hpL : p ∉ Set.range F := by
          rintro ⟨t,ht⟩
          have hb := (abs_lt.mp (hbound t)).2
          have hh := congrArg (fun z : Plane => z 1) ht
          change F t 1 = B+1 at hh
          linarith
        have hqL : q ∉ Set.range F := by
          intro hq
          have hh : p ∈ e.symm '' Set.range F := ⟨q,hq,e.symm_apply_apply p⟩
          have hs : e.symm '' Set.range F = Set.range F := by
            apply Set.Subset.antisymm
            · rintro _ ⟨x,hx,rfl⟩
              rw [←hline] at hx
              obtain ⟨y,hy,rfl⟩ := hx
              simpa only [e.symm_apply_apply] using hy
            · intro z hz
              exact ⟨e z,hline ▸ Set.mem_image_of_mem e hz,e.symm_apply_apply z⟩
          exact hpL (hs ▸ hh)
        have hno : ¬ JoinedIn (Set.range F)ᶜ q p := by
          apply no_crossing F B hB hbound hends q p
          · rw [show q = e p from rfl,he]
            change -(B+1) ≤ -B
            linarith
          · change B ≤ B+1
            linarith
        have hj := proper_line_inversion_isJordanCurve F hF hi p hpL
        obtain ⟨U,V,hU,hV,hUc,hVc,hd,hpart,hfU,hfV⟩ :=
          proper_line_sides_of_inversion_jordan (Set.range F) p hpL hj
        have hp : p ∈ U ∪ V := hpart.symm ▸ hpL
        have hq : q ∈ U ∪ V := hpart.symm ▸ hqL
        have hUL : U ⊆ (Set.range F)ᶜ := by intro z hz;exact hpart ▸ Or.inl hz
        have hVL : V ⊆ (Set.range F)ᶜ := by intro z hz;exact hpart ▸ Or.inr hz
        have sameU : ¬ (p ∈ U ∧ q ∈ U) := by
          rintro ⟨hp,hq⟩
          exact hno (((hU.isConnected_iff_isPathConnected.mp hUc).joinedIn q hq p hp).mono hUL)
        have sameV : ¬ (p ∈ V ∧ q ∈ V) := by
          rintro ⟨hp,hq⟩
          exact hno (((hV.isConnected_iff_isPathConnected.mp hVc).joinedIn q hq p hp).mono hVL)
        have swap (U V : Set Plane) (hU : IsOpen U) (hV : IsOpen V)
            (hUc : IsConnected U) (hVc : IsConnected V) (hd : Disjoint U V)
            (hpart : U ∪ V = (Set.range F)ᶜ) (hp : p ∈ U) (hq : q ∈ V) :
            e '' U ⊆ V ∧ e '' V ⊆ U := by
          have himagepart : e '' U ∪ e '' V = (Set.range F)ᶜ := by
            rw [←Set.image_union,hpart,Set.image_compl_eq e.bijective,hline]
          have hsub : e '' U ⊆ U ∪ V := by
            rw [hpart,←himagepart]
            exact Set.subset_union_left
          have hdisimage : Disjoint (e '' U) (e '' V) := hd.image e.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
          have heUc : IsPreconnected (e '' U) := (hUc.image e e.continuous.continuousOn).isPreconnected
          have heUV : e '' U ⊆ V := by
            rcases heUc.subset_or_subset hU hV hd hsub with h | h
            · exact False.elim (Set.disjoint_left.mp hd (h ⟨p,hp,rfl⟩) hq)
            · exact h
          have hVsub : V ⊆ e '' U ∪ e '' V := by
            rw [himagepart,←hpart]
            exact Set.subset_union_right
          have hVeU : V ⊆ e '' U := by
            rcases hVc.isPreconnected.subset_or_subset (e.isOpenMap _ hU)
                (e.isOpenMap _ hV) hdisimage hVsub with h | h
            · exact h
            · exact False.elim (Set.disjoint_left.mp hdisimage ⟨p,hp,rfl⟩ (h hq))
          refine ⟨heUV,?_⟩
          intro z hz
          have hzpart : z ∈ U ∪ V := by
            rw [hpart,←himagepart]
            exact Or.inr hz
          rcases hzpart with h | h
          · exact h
          · exact False.elim (Set.disjoint_left.mp hdisimage (hVeU h) hz)
        have hdR : R ⊆ U ∪ V := by
          rw [hpart]
          exact Set.disjoint_left.mp hdis
        have finish (heU : e '' U ⊆ V) (heV : e '' V ⊆ U) : False := by
          obtain ⟨r,hr⟩ := hR.nonempty
          have her : e r ∈ R := hfix ▸ Set.mem_image_of_mem e hr
          rcases hR.isPreconnected.subset_or_subset hU hV hd hdR with h | h
          · exact Set.disjoint_left.mp hd (h her) (heU ⟨r,h hr,rfl⟩)
          · exact Set.disjoint_left.mp hd (heV ⟨r,h hr,rfl⟩) (h her)
        rcases hp with hp | hp
        · have hqV : q ∈ V := hq.resolve_left (fun hq => sameU ⟨hp,hq⟩)
          obtain ⟨h1,h2⟩ := swap U V hU hV hUc hVc hd hpart hp hqV
          exact finish h1 h2
        · have hqU : q ∈ U := hq.resolve_right (fun hq => sameV ⟨hp,hq⟩)
          obtain ⟨h1,h2⟩ := swap V U hV hU hVc hUc hd.symm
            (by rw [Set.union_comm];exact hpart) hp hqU
          exact finish h2 h1
      have htwice (t : ℝ) : F (t+2*T) = F t + Plane.mk (2*L) 0 := by
        rw [show t+2*T=(t+T)+T by ring,hperiod,hperiod,he,he]
        ext i
        fin_cases i <;> simp [Plane.mk] <;> ring
      have hyperiod : Function.Periodic (fun t => F t 1) (2*T) := by
        intro t
        have h := congrArg (fun z : Plane => z 1) (htwice t)
        simpa [Plane.mk] using h
      have hycompact : IsCompact (Set.range (fun t => F t 1)) := by
        rw [←hyperiod.image_Icc (by linarith : 0 < 2*T) 0]
        exact isCompact_Icc.image ((EuclideanSpace.proj 1).continuous.comp F.continuous)
      obtain ⟨M,hM⟩ := (hycompact.image continuous_abs).bddAbove
      let B : ℝ := max M 0+1
      have hB : 0 < B := by dsimp [B];positivity
      have hbound (t : ℝ) : |F t 1| < B := by
        have h := hM ⟨F t 1,Set.mem_range_self t,rfl⟩
        dsimp [B]
        linarith [le_max_left M 0]
      have hnat (n : ℕ) (t : ℝ) : F (t+(n:ℝ)*(2*T)) = F t+Plane.mk ((n:ℝ)*(2*L)) 0 := by
        induction n with
        | zero => simp [Plane.mk]
        | succ n hn =>
          rw [Nat.cast_add,Nat.cast_one,show t+((n:ℝ)+1)*(2*T)=(t+(n:ℝ)*(2*T))+2*T by ring,htwice,hn]
          ext i
          fin_cases i <;> simp [Plane.mk] <;> ring
      have hends (r : ℝ) : ∃ A : ℝ, F (-A) 0 < -r ∧ r < F A 0 := by
        obtain ⟨n,hn⟩ := exists_nat_gt ((r+|F 0 0|)/(2*L))
        have hnl := (div_lt_iff₀ (by positivity : 0 < 2*L)).mp hn
        refine ⟨(n:ℝ)*(2*T),?_,?_⟩
        · have h := congrArg (fun z : Plane => z 0) (hnat n (-((n:ℝ)*(2*T))))
          simp only [neg_add_cancel] at h
          change F 0 0 = F (-((n:ℝ)*(2*T))) 0+(n:ℝ)*(2*L) at h
          linarith [le_abs_self (F 0 0)]
        · have h := congrArg (fun z : Plane => z 0) (hnat n 0)
          simp only [zero_add] at h
          change F ((n:ℝ)*(2*T)) 0 = F 0 0+(n:ℝ)*(2*L) at h
          linarith [neg_abs_le (F 0 0)]
      have hline : e '' Set.range F = Set.range F := by
        apply Set.Subset.antisymm
        · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          exact ⟨t+T,hperiod t⟩
        · rintro _ ⟨t,rfl⟩
          exact ⟨F (t-T),Set.mem_range_self _,by rw [←hperiod,sub_add_cancel]⟩
      exact geometry F hF hi B hB hbound hends e L he hline R hR hdis hfix
    have coordinates : ∃ e : H2 ≃ₜ ℝ × ℝ,
      (∀ z : H2, e z = (Real.log z.im,z.re/z.im)) ∧
      (∀ (g : H2 → H2) (L : ℝ),
        (∀ z, (g z).re=Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) →
        ∀ z, e (g z) = e z + (L,0)) ∧
      (∀ (g : H2 → H2) (L : ℝ),
        (∀ z, (g z).re= -Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) →
        ∀ z, e (g z) = ((e z).1+L,-(e z).2)) := by
      let f : H2 → ℝ × ℝ := fun z => (Real.log z.im,z.re/z.im)
      let G : ℝ × ℝ → H2 := fun x => ⟨⟨x.2*Real.exp x.1,Real.exp x.1⟩,Real.exp_pos _⟩
      have hf : Continuous f :=
        (UpperHalfPlane.continuous_im.log (fun z => z.im_pos.ne')).prodMk
          (UpperHalfPlane.continuous_re.div UpperHalfPlane.continuous_im (fun z => z.im_pos.ne'))
      have hG : Continuous G := by
        apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
        have hcR : Continuous (fun x : ℝ × ℝ => x.2*Real.exp x.1) := by fun_prop
        have hcI : Continuous (fun x : ℝ × ℝ => Real.exp x.1) := by fun_prop
        convert (Complex.continuous_ofReal.comp hcR).add
          ((Complex.continuous_ofReal.comp hcI).mul
            (continuous_const : Continuous (fun _ : ℝ × ℝ => Complex.I))) using 1
        funext x
        apply Complex.ext <;> simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,
          Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
          Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,
          sub_zero,add_zero,zero_add] <;> rfl
      let e : H2 ≃ₜ ℝ × ℝ :=
        { toFun := f, invFun := G,
          left_inv := by
            intro z
            apply UpperHalfPlane.ext_re_im
            · change (z.re/z.im)*Real.exp (Real.log z.im) = z.re
              rw [Real.exp_log z.im_pos]
              exact div_mul_cancel₀ _ z.im_pos.ne'
            · exact Real.exp_log z.im_pos
          right_inv := by
            intro x
            apply Prod.ext
            · exact Real.log_exp x.1
            · change x.2*Real.exp x.1/Real.exp x.1 = x.2
              exact mul_div_cancel_right₀ _ (Real.exp_ne_zero _)
          continuous_toFun := hf,continuous_invFun := hG }
      refine ⟨e,fun z => rfl,?_,?_⟩
      · intro g L hg z
        apply Prod.ext
        · change Real.log (g z).im = Real.log z.im+L
          rw [(hg z).2,Real.log_mul (Real.exp_ne_zero _) z.im_pos.ne',Real.log_exp]
          ring
        · change (g z).re/(g z).im = z.re/z.im+0
          rw [(hg z).1,(hg z).2]
          field_simp
          ring
      · intro g L hg z
        apply Prod.ext
        · change Real.log (g z).im = Real.log z.im+L
          rw [(hg z).2,Real.log_mul (Real.exp_ne_zero _) z.im_pos.ne',Real.log_exp]
          ring
        · change (g z).re/(g z).im = -(z.re/z.im)
          rw [(hg z).1,(hg z).2]
          field_simp <;> ring
    obtain ⟨e,he,hd,hgl⟩ := coordinates
    let prodPlane : (ℝ × ℝ) ≃ₜ Plane :=
      { toFun := fun x => Plane.mk x.1 x.2
        invFun := fun z => (z 0,z 1)
        left_inv := by intro x;rfl
        right_inv := by
          intro z
          ext i
          fin_cases i <;> rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let E : H2 ≃ₜ Plane := e.trans prodPlane
    let FP : C(ℝ,Plane) := ⟨E ∘ F,E.continuous.comp F.continuous⟩
    let GP : Plane ≃ₜ Plane := (E.symm.trans g).trans E
    have hGP (z : Plane) : GP z = Plane.mk (z 0+L) (-z 1) := by
      change prodPlane (e (g (E.symm z))) = _
      rw [hgl g L hg]
      have hh : e (E.symm z) = (z 0,z 1) := by
        change e (e.symm (prodPlane.symm z)) = _
        exact e.apply_symm_apply _
      rw [hh]
      rfl
    have hFP (t : ℝ) : FP (t+T) = GP (FP t) := by
      change E (F (t+T)) = E (g (E.symm (E (F t))))
      rw [hperiod,E.symm_apply_apply]
    have hRP : IsConnected (E '' R) := hR.image E E.continuous.continuousOn
    have hdRP : Disjoint (E '' R) (Set.range FP) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,hxz⟩ ⟨t,ht⟩
      have heq : x = F t := E.injective (hxz.trans ht.symm)
      exact Set.disjoint_left.mp hdis hx (heq ▸ Set.mem_range_self t)
    have hfixP : GP '' (E '' R) = E '' R := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
        change E (g (E.symm (E x))) ∈ E '' R
        rw [E.symm_apply_apply]
        exact Set.mem_image_of_mem E (hfix ▸ Set.mem_image_of_mem g hx)
      · rintro _ ⟨x,hx,rfl⟩
        rw [←hfix] at hx
        obtain ⟨y,hy,rfl⟩ := hx
        refine ⟨E y,Set.mem_image_of_mem E hy,?_⟩
        change E (g (E.symm (E y))) = E (g y)
        rw [E.symm_apply_apply]
    exact planar FP (E.isProperMap.comp hF) (E.injective.comp hi) T L hT hL
      GP hGP hFP (E '' R) hRP hdRP hfixP
  let normalizedMonodromy : H2 ≃ₜ H2 :=
    (axisNormalizingIsometry.toHomeomorph.trans (developedDeck monodromy)).trans
      axisNormalizingIsometry.symm.toHomeomorph
  have actual_source_common_monodromy_is_not_glide
      (hg : ∀ z : H2, (normalizedMonodromy z).re = -Real.exp axisPeriod*z.re ∧
        (normalizedMonodromy z).im = Real.exp axisPeriod*z.im) : False := by
    let F : C(ℝ,H2) := ⟨axisNormalizingIsometry.symm ∘ sourceLift,
      axisNormalizingIsometry.symm.continuous.comp sourceLift.continuous⟩
    let R : Set H2 := axisNormalizingIsometry.symm '' Set.range targetLift
    have hFperiod (t : ℝ) : F (t+2*Real.pi) = normalizedMonodromy (F t) := by
      change axisNormalizingIsometry.symm (sourceLift (t+2*Real.pi)) =
        axisNormalizingIsometry.symm (developedDeck monodromy
          (axisNormalizingIsometry (axisNormalizingIsometry.symm (sourceLift t))))
      rw [sourceLift_period,axisNormalizingIsometry.apply_symm_apply]
    have hR : IsConnected R := (isConnected_range targetLift.continuous).image
      axisNormalizingIsometry.symm axisNormalizingIsometry.symm.continuous.continuousOn
    have hdisLift : Disjoint (Set.range targetLift) (Set.range sourceLift) := by
      simpa only [actual_developedDeck_one,Set.image_id'] using
        (all_developed_source_target_translates_disjoint 1 1).symm
    have hdisFR : Disjoint R (Set.range F) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,hxz⟩ ⟨t,ht⟩
      have heq : x = sourceLift t := axisNormalizingIsometry.symm.injective (hxz.trans ht.symm)
      exact Set.disjoint_left.mp hdisLift hx (heq ▸ Set.mem_range_self t)
    have hfix : normalizedMonodromy '' R = R := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_,⟨_,⟨t,rfl⟩,rfl⟩,rfl⟩
        refine ⟨targetLift (t+2*Real.pi),Set.mem_range_self _,?_⟩
        change axisNormalizingIsometry.symm (targetLift (t+2*Real.pi)) =
          axisNormalizingIsometry.symm (developedDeck monodromy
            (axisNormalizingIsometry (axisNormalizingIsometry.symm (targetLift t))))
        rw [targetLift_period,axisNormalizingIsometry.apply_symm_apply]
      · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
        refine ⟨axisNormalizingIsometry.symm (targetLift (t-2*Real.pi)),
          ⟨targetLift (t-2*Real.pi),Set.mem_range_self _,rfl⟩,?_⟩
        change axisNormalizingIsometry.symm (developedDeck monodromy
          (axisNormalizingIsometry (axisNormalizingIsometry.symm (targetLift (t-2*Real.pi))))) =
          axisNormalizingIsometry.symm (targetLift t)
        rw [axisNormalizingIsometry.apply_symm_apply,←targetLift_period,sub_add_cancel]
    exact h2glideNoDisjoint F
      (axisNormalizingIsometry.symm.toHomeomorph.isProperMap.comp actual_sourceLift_closed_embedding.isProperMap)
      (axisNormalizingIsometry.symm.injective.comp actual_sourceLift_closed_embedding.injective)
      (2*Real.pi) axisPeriod (by positivity) haxisPeriod normalizedMonodromy hg
      hFperiod R hR hdisFR hfix
  have translatedAxisDilationOrGlide (g : H2 ≃ᵢ H2) (L : ℝ)
      (hperiod : ∀t : ℝ, g (verticalPath t)=verticalPath (t+L)) :
      (∀z : H2, (g z).re=Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) ∨
      (∀z : H2, (g z).re= -Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) := by
    let r : ℝ := Real.exp (L/2)
    have hr : r ≠ 0 := Real.exp_ne_zero _
    let A : SL(2,ℝ) := ⟨!![r,0;0,r⁻¹],by simp [Matrix.det_fin_two,hr]⟩
    let D : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
    have hr2 : r^2=Real.exp L := by
      change (Real.exp (L/2))^2=Real.exp L
      rw [pow_two,←Real.exp_add]
      congr 1
      ring
    have hDcoe (z : H2) : (D z:ℂ)=(Real.exp L:ℂ)*(z:ℂ) := by
      change (A • z:H2).coe=_
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      change ((r:ℂ)*(z:ℂ)+0)/(0*(z:ℂ)+((r⁻¹:ℝ):ℂ))=(Real.exp L:ℂ)*(z:ℂ)
      simp only [add_zero,zero_mul,zero_add,Complex.ofReal_inv,div_inv_eq_mul]
      have hh : (r:ℂ)*(z:ℂ)*(r:ℂ)=((r^2:ℝ):ℂ)*(z:ℂ) := by push_cast; ring
      rw [hh,hr2]
    have hDre (z : H2) : (D z).re=Real.exp L*z.re := by
      change (D z:ℂ).re=Real.exp L*(z:ℂ).re
      have h := congrArg Complex.re (hDcoe z)
      simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h
    have hDim (z : H2) : (D z).im=Real.exp L*z.im := by
      change (D z:ℂ).im=Real.exp L*(z:ℂ).im
      have h := congrArg Complex.im (hDcoe z)
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using h
    have hDvertical (t : ℝ) : D (verticalPath t)=verticalPath (t+L) := by
      apply UpperHalfPlane.ext_re_im
      · rw [hDre]
        simp [verticalPath]
      · rw [hDim]
        change Real.exp L*Real.exp t=Real.exp (t+L)
        rw [←Real.exp_add,add_comm]
    let h : H2 ≃ᵢ H2 := g.trans D.symm
    have hvert (t : ℝ) : h (verticalPath t)=verticalPath t := by
      change D.symm (g (verticalPath t))=verticalPath t
      rw [hperiod,←hDvertical,D.symm_apply_apply]
    have hI : h UpperHalfPlane.I=UpperHalfPlane.I := by
      have hv0 : verticalPath 0=UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      simpa only [hv0] using hvert 0
    rcases axis_normalized_isometry_identity_or_reflection h hI (hvert 1) with hid | hreflect
    · left
      intro z
      have hz : g z=D z := by
        have ht := congrArg D (hid z)
        simpa only [h,IsometryEquiv.trans_apply,D.apply_symm_apply] using ht
      rw [hz]
      exact ⟨hDre z,hDim z⟩
    · right
      intro z
      have hz : g z=D (axisZeroReflection z) := by
        have ht := congrArg D (hreflect z)
        simpa only [h,IsometryEquiv.trans_apply,D.apply_symm_apply] using ht
      rw [hz,hDre,hDim,axisZeroReflection_re,axisZeroReflection_im]
      constructor
      · ring
      · rfl
  have normalized_monodromy_axis_period (t : ℝ) :
      normalizedMonodromy (verticalPath t) = verticalPath (t+axisPeriod) := by
    change axisNormalizingIsometry.symm (developedDeck monodromy
      (axisNormalizingIsometry (verticalPath t))) = _
    rw [show axisNormalizingIsometry (verticalPath t) = actualAxis t from axisNormalizer_control t]
    change axisNormalizingIsometry.symm (developedDeckIsometry monodromy (actualAxis t)) = _
    rw [haxisTranslate,←axisNormalizer_control]
    exact axisNormalizingIsometry.symm_apply_apply _
  let normalizedMonodromyIsometry : H2 ≃ᵢ H2 :=
    (axisNormalizingIsometry.trans (developedDeckIsometry monodromy)).trans axisNormalizingIsometry.symm
  have actual_source_common_monodromy_is_dilation :
      ∀ z : H2, (normalizedMonodromy z).re = Real.exp axisPeriod*z.re ∧
        (normalizedMonodromy z).im = Real.exp axisPeriod*z.im := by
    rcases translatedAxisDilationOrGlide normalizedMonodromyIsometry axisPeriod
      normalized_monodromy_axis_period with hd | hg
    · exact hd
    · exact False.elim (actual_source_common_monodromy_is_not_glide hg)
  have logarithmicCoordinates : ∃ e : H2 ≃ₜ ℝ × ℝ,
    (∀ z : H2, e z = (Real.log z.im,z.re/z.im)) ∧
    (∀ (g : H2 → H2) (L : ℝ),
      (∀ z, (g z).re=Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) →
      ∀ z, e (g z) = e z + (L,0)) ∧
    (∀ (g : H2 → H2) (L : ℝ),
      (∀ z, (g z).re= -Real.exp L*z.re ∧ (g z).im=Real.exp L*z.im) →
      ∀ z, e (g z) = ((e z).1+L,-(e z).2)) := by
    let f : H2 → ℝ × ℝ := fun z => (Real.log z.im,z.re/z.im)
    let G : ℝ × ℝ → H2 := fun x => ⟨⟨x.2*Real.exp x.1,Real.exp x.1⟩,Real.exp_pos _⟩
    have hf : Continuous f :=
      (UpperHalfPlane.continuous_im.log (fun z => z.im_pos.ne')).prodMk
        (UpperHalfPlane.continuous_re.div UpperHalfPlane.continuous_im (fun z => z.im_pos.ne'))
    have hG : Continuous G := by
      apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
      have hcR : Continuous (fun x : ℝ × ℝ => x.2*Real.exp x.1) := by fun_prop
      have hcI : Continuous (fun x : ℝ × ℝ => Real.exp x.1) := by fun_prop
      convert (Complex.continuous_ofReal.comp hcR).add
        ((Complex.continuous_ofReal.comp hcI).mul
          (continuous_const : Continuous (fun _ : ℝ × ℝ => Complex.I))) using 1
      funext x
      apply Complex.ext <;> simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,
        Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,
        sub_zero,add_zero,zero_add] <;> rfl
    let e : H2 ≃ₜ ℝ × ℝ :=
      { toFun := f, invFun := G,
        left_inv := by
          intro z
          apply UpperHalfPlane.ext_re_im
          · change (z.re/z.im)*Real.exp (Real.log z.im) = z.re
            rw [Real.exp_log z.im_pos]
            exact div_mul_cancel₀ _ z.im_pos.ne'
          · exact Real.exp_log z.im_pos
        right_inv := by
          intro x
          apply Prod.ext
          · exact Real.log_exp x.1
          · change x.2*Real.exp x.1/Real.exp x.1 = x.2
            exact mul_div_cancel_right₀ _ (Real.exp_ne_zero _)
        continuous_toFun := hf,continuous_invFun := hG }
    refine ⟨e,fun z => rfl,?_,?_⟩
    · intro g L hg z
      apply Prod.ext
      · change Real.log (g z).im = Real.log z.im+L
        rw [(hg z).2,Real.log_mul (Real.exp_ne_zero _) z.im_pos.ne',Real.log_exp]
        ring
      · change (g z).re/(g z).im = z.re/z.im+0
        rw [(hg z).1,(hg z).2]
        field_simp
        ring
    · intro g L hg z
      apply Prod.ext
      · change Real.log (g z).im = Real.log z.im+L
        rw [(hg z).2,Real.log_mul (Real.exp_ne_zero _) z.im_pos.ne',Real.log_exp]
        ring
      · change (g z).re/(g z).im = -(z.re/z.im)
        rw [(hg z).1,(hg z).2]
        field_simp <;> ring
  obtain ⟨logarithmicCoordinate,logarithmicCoordinate_eq,dilationCoordinate,glideCoordinate⟩ := logarithmicCoordinates
  let sourceAxisCoordinate : H2 ≃ₜ ℝ × ℝ :=
    axisNormalizingIsometry.symm.toHomeomorph.trans logarithmicCoordinate
  let minimalAxisIsometry : H2 ≃ᵢ H2 :=
    (axisNormalizingIsometry.trans (developedDeckIsometry minimalAxisDeck.val)).trans
      axisNormalizingIsometry.symm
  have minimal_axis_isometry_period (t : ℝ) :
      minimalAxisIsometry (verticalPath t) = verticalPath (t+minimalAxisPeriod) := by
    have h := axisPeriodHom_action minimalAxisDeck t
    rw [minimalAxisDeck_period] at h
    exact h
  let originalAxisNatIndex : ℕ := originalAxisIndex.toNat
  have original_axis_nat_index_positive : 0 < originalAxisNatIndex :=
by
    dsimp [originalAxisNatIndex]
    omega
  have original_axis_nat_index_cast : (originalAxisNatIndex:ℤ) = originalAxisIndex :=
    Int.toNat_of_nonneg original_axis_index_positive.le
  have original_monodromy_minimal_axis_nat_root :
      monodromy = minimalAxisDeck.val ^ originalAxisNatIndex := by
    rw [←_root_.zpow_natCast,original_axis_nat_index_cast]
    exact original_monodromy_minimal_axis_root
  have actual_source_minimal_axis_index_one_or_two :
      originalAxisNatIndex = 1 ∨ originalAxisNatIndex = 2 := by
    rcases translatedAxisDilationOrGlide minimalAxisIsometry minimalAxisPeriod
      minimal_axis_isometry_period with hd | hg
    · left
      apply actual_source_monodromy_has_no_proper_dilation_root minimalAxisDeck.val
        originalAxisNatIndex original_axis_nat_index_positive original_monodromy_minimal_axis_nat_root
        sourceAxisCoordinate minimalAxisPeriod minimalAxisPeriod_positive.ne'
      intro z
      have h := dilationCoordinate minimalAxisIsometry minimalAxisPeriod hd
        (axisNormalizingIsometry.symm z)
      change logarithmicCoordinate (axisNormalizingIsometry.symm (developedDeckIsometry minimalAxisDeck.val z)) =
        logarithmicCoordinate (axisNormalizingIsometry.symm z)+(minimalAxisPeriod,0)
      simpa only [minimalAxisIsometry,sourceAxisCoordinate,Homeomorph.trans_apply,
        IsometryEquiv.trans_apply,axisNormalizingIsometry.apply_symm_apply] using h
    · have hkcoord (z : H2) : sourceAxisCoordinate (developedDeck minimalAxisDeck.val z) =
          ((sourceAxisCoordinate z).1+minimalAxisPeriod,-(sourceAxisCoordinate z).2) := by
        have h := glideCoordinate minimalAxisIsometry minimalAxisPeriod hg
          (axisNormalizingIsometry.symm z)
        change logarithmicCoordinate (axisNormalizingIsometry.symm (developedDeckIsometry minimalAxisDeck.val z)) =
          ((logarithmicCoordinate (axisNormalizingIsometry.symm z)).1+minimalAxisPeriod,
            -(logarithmicCoordinate (axisNormalizingIsometry.symm z)).2)
        simpa only [minimalAxisIsometry,sourceAxisCoordinate,Homeomorph.trans_apply,
          IsometryEquiv.trans_apply,axisNormalizingIsometry.apply_symm_apply] using h
      have hsquare (z : H2) : sourceAxisCoordinate (developedDeck (minimalAxisDeck.val^2) z) =
          sourceAxisCoordinate z+(2*minimalAxisPeriod,0) := by
        rw [pow_two,actual_developedDeck_mul,hkcoord,hkcoord]
        ext <;> simp <;> ring
      let clock : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ (2*Real.pi) (by positivity)
      let F : C(ℝ,H2) := ⟨sourceLift ∘ clock,sourceLift.continuous.comp clock.continuous⟩
      have hFclosed : Topology.IsClosedEmbedding F := actual_sourceLift_closed_embedding.comp clock.isClosedEmbedding
      have hperiod (j : ℤ) (t : ℝ) : F (t+(j:ℝ)*2) =
          ((deckIsometryHom (minimalAxisDeck.val^2))^(j*(originalAxisNatIndex:ℤ))) (F t) := by
        change sourceLift ((t+(j:ℝ)*2)*(2*Real.pi)) = _
        have ht : (t+(j:ℝ)*2)*(2*Real.pi) = t*(2*Real.pi)+((2*j:ℤ):ℝ)*(2*Real.pi) := by push_cast;ring
        rw [ht,actual_source_integer_period,original_monodromy_minimal_axis_nat_root]
        have hp : (minimalAxisDeck.val^originalAxisNatIndex)^(2*j) =
            (minimalAxisDeck.val^2)^(j*(originalAxisNatIndex:ℤ)) := by
          calc
            (minimalAxisDeck.val^originalAxisNatIndex)^(2*j) =
                minimalAxisDeck.val^((originalAxisNatIndex:ℤ)*(2*j)) := by
                  simpa only [_root_.zpow_natCast] using
                    (_root_.zpow_mul minimalAxisDeck.val (originalAxisNatIndex:ℤ) (2*j)).symm
            _ = minimalAxisDeck.val^((2:ℤ)*(j*(originalAxisNatIndex:ℤ))) := by congr 1;ring
            _ = (minimalAxisDeck.val^(2:ℤ))^(j*(originalAxisNatIndex:ℤ)) := by rw [_root_.zpow_mul]
            _ = (minimalAxisDeck.val^2)^(j*(originalAxisNatIndex:ℤ)) := by rw [zpow_ofNat]
        rw [hp]
        exact congrArg (fun u : H2 ≃ᵢ H2 => u (F t))
          (deckIsometryHom.map_zpow (minimalAxisDeck.val^2) (j*(originalAxisNatIndex:ℤ)))
      have hmeet := dilation_root_line_meeting F hFclosed.isProperMap hFclosed.injective
        sourceAxisCoordinate (deckIsometryHom (minimalAxisDeck.val^2)) (2*minimalAxisPeriod) 2
        (by positivity) (by norm_num) originalAxisNatIndex original_axis_nat_index_positive hsquare hperiod
      have hrange : Set.range F = Set.range sourceLift := by
        change Set.range (sourceLift ∘ clock) = Set.range sourceLift
        rw [Set.range_comp,Set.range_eq_univ.mpr clock.surjective,Set.image_univ]
      rw [hrange] at hmeet
      have hstabilizes : developedDeck (minimalAxisDeck.val^2) '' Set.range sourceLift =
          Set.range sourceLift := by
        rcases actual_all_source_deck_lifts_equal_or_disjoint (minimalAxisDeck.val^2) with h | h
        · exact h
        · exact False.elim (hmeet h.symm)
      obtain ⟨m,hm⟩ := actual_source_stabilizer_is_common_cyclic (minimalAxisDeck.val^2) hstabilizes
      have hsubgroup : minimalAxisDeck^(2:ℤ) = originalAxisDeck^m := by
        apply Subtype.ext
        simpa only [Subgroup.coe_zpow,Subgroup.coe_pow,zpow_ofNat,originalAxisDeck] using hm
      have heq := congrArg (fun k => axisPeriodHom (Additive.ofMul k)) hsubgroup
      rw [ofMul_zpow,ofMul_zpow,map_zsmul,map_zsmul,minimalAxisDeck_period,original_axis_deck_period,
        zsmul_eq_mul,zsmul_eq_mul] at heq
      have hindex := congrArg (fun k => axisPeriodHom (Additive.ofMul k)) originalAxisIndex_power
      rw [original_axis_deck_period,ofMul_zpow,map_zsmul,minimalAxisDeck_period,zsmul_eq_mul] at hindex
      have hmul : (2:ℝ) = (m:ℝ)*(originalAxisIndex:ℝ) := by
        have he : (2:ℝ)*minimalAxisPeriod = ((m:ℝ)*(originalAxisIndex:ℝ))*minimalAxisPeriod := by
          calc
            (2:ℝ)*minimalAxisPeriod = (m:ℝ)*axisPeriod := heq
            _ = (m:ℝ)*((originalAxisIndex:ℝ)*minimalAxisPeriod) := by rw [hindex]
            _ = ((m:ℝ)*(originalAxisIndex:ℝ))*minimalAxisPeriod := by ring
        exact mul_right_cancel₀ minimalAxisPeriod_positive.ne' he
      have hint : (2:ℤ) = m*originalAxisIndex := by exact_mod_cast hmul
      have hmpos : 0 < m := by
        by_contra h
        have hle : m ≤ 0 := le_of_not_gt h
        have hz := mul_nonpos_of_nonpos_of_nonneg hle original_axis_index_positive.le
        omega
      have hnle : originalAxisIndex ≤ 2 := by nlinarith
      have hNatLe : originalAxisNatIndex ≤ 2 := by omega
      omega
  have cyclicPlaneProjection {P Y : Type} [TopologicalSpace P] [TopologicalSpace Y]
    (τ : ℝ) (p : P → Y) (hp : IsCoveringMap p) (f : C(ℝ × ℝ,P))
    (hinj : Function.Injective f)
    (hperiod : ∀ x : ℝ × ℝ, p (f (x.1+τ,x.2)) = p (f x)) :
    ∃ F : C(AddCircle τ × ℝ,Y),
      (∀ x : ℝ × ℝ, F ((x.1:AddCircle τ),x.2) = p (f x)) ∧
      ∀ y, ∃ V ∈ 𝓝 y, Set.InjOn F V := by
    have descent {Y : Type} [TopologicalSpace Y] (f : C(ℝ × ℝ,Y))
        (hperiod : ∀ x : ℝ × ℝ, f (x.1+τ,x.2) = f x) :
        ∃ F : C(AddCircle τ × ℝ,Y), ∀ x : ℝ × ℝ,
          F ((x.1 : AddCircle τ),x.2) = f x := by
      have hp : Function.Periodic f.curry τ := by
        intro t
        apply ContinuousMap.ext
        intro u
        exact hperiod (t,u)
      let L : AddCircle τ → C(ℝ,Y) := hp.lift
      have hL : Continuous L := by
        exact f.curry.continuous.quotient_lift _
      let F : C(AddCircle τ × ℝ,Y) := ContinuousMap.uncurry ⟨L,hL⟩
      refine ⟨F,?_⟩
      intro x
      change hp.lift (x.1 : AddCircle τ) x.2 = f x
      rw [hp.lift_coe]
      rfl
    have descend_local_injectivity {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
        (q : X → Y) (f : Y → Z) (hq : Function.Surjective q) (hopen : IsOpenMap q)
        (hloc : ∀ x, ∃ U ∈ 𝓝 x, Set.InjOn (f ∘ q) U) :
        ∀ y, ∃ V ∈ 𝓝 y, Set.InjOn f V := by
      intro y
      obtain ⟨x,rfl⟩ := hq y
      obtain ⟨U,hU,hUinj⟩ := hloc x
      obtain ⟨O,hOU,hO,hxO⟩ := mem_nhds_iff.mp hU
      refine ⟨q '' O,(hopen O hO).mem_nhds (Set.mem_image_of_mem q hxO),?_⟩
      rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ he
      exact congrArg q (hUinj (hOU ha) (hOU hb) he)
    let pf : C(ℝ × ℝ,Y) := ⟨p ∘ f,hp.continuous.comp f.continuous⟩
    obtain ⟨F,hF⟩ := descent pf hperiod
    let q : ℝ × ℝ → AddCircle τ × ℝ :=
      fun x => (x.1,x.2)
    have hq : Function.Surjective q := by
      rintro ⟨z,u⟩
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective z
      exact ⟨(t,u),Prod.ext ht rfl⟩
    have hopen : IsOpenMap q := QuotientAddGroup.isOpenMap_coe.prodMap IsOpenMap.id
    have hloc : ∀ x, ∃ U ∈ 𝓝 x, Set.InjOn (F ∘ q) U := by
      intro x
      obtain ⟨V,hV,hfxV,hVinj⟩ := hp.isLocalHomeomorph.isLocallyInjective (f x)
      refine ⟨f ⁻¹' V,f.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hfxV),?_⟩
      intro a ha b hb he
      apply hinj
      apply hVinj ha hb
      exact (hF a).symm.trans (he.trans (hF b))
    exact ⟨F,hF,descend_local_injectivity q F hq hopen hloc⟩
  have cylinderFullCollar (c : C(Circle,Circle × ℝ)) (hc : Function.Injective c) :
    ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,Circle × ℝ), Function.Injective e ∧
      ∀ z, e (⟨0,by norm_num⟩,z) = c z := by
    have polarCoordinates : ∃ e : (Circle × ℝ) ≃ₜ {z : ℂ // z ≠ 0},
      ∀ x, (e x).val = (Real.exp x.2:ℂ)*(x.1:ℂ) := by
      classical
      let Z := {z : ℂ // z ≠ 0}
      have hn (z : Z) : ‖z.val‖ ≠ 0 := norm_ne_zero_iff.mpr z.property
      let unit : Z → Circle := fun z =>
        ⟨z.val / (‖z.val‖:ℂ),by
          change z.val / (‖z.val‖:ℂ) ∈ Metric.sphere (0:ℂ) 1
          rw [mem_sphere_zero_iff_norm]
          rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
          exact div_self (hn z)⟩
      have unitc : Continuous unit := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.div
          (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
          (fun z => Complex.ofReal_ne_zero.mpr (hn z))
      let f : Z → Circle × ℝ := fun z => (unit z,Real.log ‖z.val‖)
      let g : Circle × ℝ → Z := fun x =>
        ⟨(Real.exp x.2:ℂ)*(x.1:ℂ),mul_ne_zero
          (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) (Circle.coe_ne_zero _)⟩
      have gnorm (x : Circle × ℝ) : ‖(g x).val‖ = Real.exp x.2 := by
        dsimp [g]
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Circle.norm_coe,mul_one]
      have gf (z : Z) : g (f z) = z := by
        apply Subtype.ext
        change (Real.exp (Real.log ‖z.val‖):ℂ)*(z.val/(‖z.val‖:ℂ)) = z.val
        rw [Real.exp_log (norm_pos_iff.mpr z.property)]
        field_simp [Complex.ofReal_ne_zero.mpr (hn z)]
      have fg (x : Circle × ℝ) : f (g x) = x := by
        apply Prod.ext
        · apply Subtype.ext
          change (g x).val/(‖(g x).val‖:ℂ) = (x.1:ℂ)
          rw [gnorm]
          dsimp [g]
          field_simp
        · change Real.log ‖(g x).val‖ = x.2
          rw [gnorm,Real.log_exp]
      let e : (Circle × ℝ) ≃ₜ Z :=
        { toFun := g
          invFun := f
          left_inv := fg
          right_inv := gf
          continuous_toFun := by
            exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_snd)).mul
              (continuous_subtype_val.comp continuous_fst)).subtype_mk _
          continuous_invFun := by
            exact unitc.prodMk (continuous_subtype_val.norm.log (fun z => hn z)) }
      exact ⟨e,fun x => rfl⟩
    have planarFullCollar (c : Curve Plane) : ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,Plane),
      Topology.IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z) = c.map z := by
      have actualNormalize (c : Curve Plane) : ∃ F : Plane ≃ₜ Plane,
          ∀ z : Circle, F (c.map z) = ClassificationJordanCurve.Arcs.complexLIE z := by
        let r : C(Circle, Plane) := ⟨fun z => (ClassificationJordanCurve.Arcs.circleHomeoSphere z : Plane),
          continuous_subtype_val.comp ClassificationJordanCurve.Arcs.circleHomeoSphere.continuous⟩
        have hr : Topology.IsEmbedding r :=
          Topology.IsEmbedding.subtypeVal.comp ClassificationJordanCurve.Arcs.circleHomeoSphere.isEmbedding
        have hrange : Set.range r = sphere (0 : Plane) 1 := by
          ext x
          constructor
          · rintro ⟨z,rfl⟩; exact (ClassificationJordanCurve.Arcs.circleHomeoSphere z).property
          · intro hx
            refine ⟨ClassificationJordanCurve.Arcs.circleHomeoSphere.symm ⟨x,hx⟩,?_⟩
            change (ClassificationJordanCurve.Arcs.circleHomeoSphere (ClassificationJordanCurve.Arcs.circleHomeoSphere.symm ⟨x,hx⟩) : Plane)=x
            rw [ClassificationJordanCurve.Arcs.circleHomeoSphere.apply_symm_apply]
        have hJ := isJordanCurve_range_of_isEmbedding_circle r hr
        rw [hrange] at hJ
        -- the range homeomorphism has the opposite direction here
        let ec : c.image ≃ₜ sphere (0 : Plane) 1 := c.embedded.toHomeomorph.symm.trans ClassificationJordanCurve.Arcs.circleHomeoSphere
        obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
          (isJordanCurve_range_of_isEmbedding_circle ⟨c.map,c.embedded.continuous⟩ c.embedded) hJ ec
        refine ⟨F,fun z => ?_⟩
        have h := hF ⟨c.map z,⟨z,rfl⟩⟩
        simpa [ec] using h
      have openAnnulus
        (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, Plane))
        (hE : Function.Injective E) : Topology.IsOpenEmbedding E := by
        have hopen : IsOpenMap E := by
          intro V hV
          rw [isOpen_iff_forall_mem_open]
          rintro z ⟨⟨w,c⟩,hwV,rfl⟩
          let a : ℝ := ((w : ℝ)-1)/2
          let b : ℝ := ((w : ℝ)+1)/2
          have haw : a < (w : ℝ) := by dsimp [a]; linarith [w.property.1]
          have hwb : (w : ℝ) < b := by dsimp [b]; linarith [w.property.2]
          have ha : -1 < a := by dsimp [a]; linarith [w.property.1]
          have hb : b < 1 := by dsimp [b]; linarith [w.property.2]
          have hab : a ≤ b := (haw.trans hwb).le
          let width : ℝ → Set.Ioo (-1 : ℝ) 1 := fun t =>
            ⟨(Set.projIcc a b hab t : ℝ),
              ⟨ha.trans_le (Set.projIcc a b hab t).property.1,
                lt_of_le_of_lt (Set.projIcc a b hab t).property.2 hb⟩⟩
          have hwc : Continuous width := by
            exact (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
          let angle : ℝ := Complex.arg (c : ℂ)
          let F : EuclideanSpace ℝ (Fin 2) → Plane :=
            fun x => E (width (x 0), Circle.exp (x 1))
          have hFc : Continuous F := E.continuous.comp
            ((hwc.comp (by fun_prop)).prodMk (Circle.exp.continuous.comp (by fun_prop)))
          let U : Set (EuclideanSpace ℝ (Fin 2)) :=
            {x | x 0 ∈ Set.Ioo a b ∧ x 1 ∈ Set.Ioo (angle-Real.pi/2) (angle+Real.pi/2) ∧
              (width (x 0),Circle.exp (x 1)) ∈ V}
          have hU : IsOpen U :=
            (isOpen_Ioo.preimage (by fun_prop)).inter
              ((isOpen_Ioo.preimage (by fun_prop)).inter
                (hV.preimage ((hwc.comp (by fun_prop)).prodMk
                  (Circle.exp.continuous.comp (by fun_prop)))))
          have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ U) :
              (width (x 0) : ℝ) = x 0 := by
            exact congrArg Subtype.val (Set.projIcc_of_mem hab ⟨hx.1.1.le,hx.1.2.le⟩)
          have hi : Set.InjOn F U := by
            intro x hx y hy he
            have hh := hE he
            have hx0 := congrArg (fun q : Set.Ioo (-1 : ℝ) 1 × Circle => (q.1 : ℝ)) hh
            have hx1 := congrArg Prod.snd hh
            have hangle : x 1 = y 1 :=
              Circle.exp_injOn_Icc (a := angle-Real.pi/2) (b := angle+Real.pi/2)
                (by linarith [Real.pi_pos])
                ⟨hx.2.1.1.le,hx.2.1.2.le⟩ ⟨hy.2.1.1.le,hy.2.1.2.le⟩ hx1
            have hwidth : x 0 = y 0 := by
              change (width (x 0) : ℝ) = (width (y 0) : ℝ) at hx0
              simpa only [hclip x hx,hclip y hy] using hx0
            ext i
            fin_cases i
            · exact hwidth
            · exact hangle
          have hFU : IsOpen (F '' U) :=
            CurveComplex.surface_invariance_of_domain_probe F U hU hFc.continuousOn hi
          have hclipw : width (w : ℝ) = w := by
            apply Subtype.ext
            change (Set.projIcc a b hab (w : ℝ) : ℝ) = (w : ℝ)
            exact congrArg Subtype.val (Set.projIcc_of_mem hab ⟨haw.le,hwb.le⟩)
          have hexp : Circle.exp angle = c := Circle.exp_arg c
          let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (w : ℝ) angle
          have hx0 : x 0 = (w : ℝ) := by simp [x,Schoenflies.Plane.mk]
          have hx1 : x 1 = angle := by simp [x,Schoenflies.Plane.mk]
          have hx : x ∈ U := by
            refine ⟨?_,?_,?_⟩
            · change a < x 0 ∧ x 0 < b
              rw [hx0]
              exact ⟨haw,hwb⟩
            · rw [hx1]
              constructor <;> linarith [Real.pi_pos]
            · simpa only [hx0,hx1,hclipw,hexp] using hwV
          refine ⟨F '' U,?_,hFU,?_⟩
          · rintro y ⟨u,hu,rfl⟩
            exact ⟨(width (u 0),Circle.exp (u 1)),hu.2.2,rfl⟩
          · refine ⟨x,hx,?_⟩
            simp only [F,hx0,hx1,hclipw,hexp]
        exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap E.continuous hE hopen
      obtain ⟨N,hN⟩ := actualNormalize c
      let base : C(Set.Ioo (-1:ℝ) 1 × Circle,Plane) :=
        ⟨fun x => ClassificationJordanCurve.Arcs.complexLIE (((1+(x.1:ℝ)/2:ℝ):ℂ)*(x.2:ℂ)),by
          exact ClassificationJordanCurve.Arcs.complexLIE.continuous.comp
            ((Complex.continuous_ofReal.comp
              ((continuous_subtype_val.comp continuous_fst).div_const 2 |>.const_add 1)).mul
              (continuous_subtype_val.comp continuous_snd))⟩
      have base_injective : Function.Injective base := by
        rintro ⟨w,z⟩ ⟨v,d⟩ he
        have hc := ClassificationJordanCurve.Arcs.complexLIE.injective he
        have hpw : 0 < 1+(w:ℝ)/2 := by linarith [w.property.1]
        have hpv : 0 < 1+(v:ℝ)/2 := by linarith [v.property.1]
        have hn := congrArg norm hc
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos hpw,abs_of_pos hpv,Circle.norm_coe,mul_one] at hn
        have hw : w=v := Subtype.ext (by linarith)
        subst v
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hpw.ne') hc
      let e : C(Set.Ioo (-1:ℝ) 1 × Circle,Plane) :=
        ⟨N.symm ∘ base,N.symm.continuous.comp base.continuous⟩
      refine ⟨e,(openAnnulus e (N.symm.injective.comp base_injective)),?_⟩
      intro z
      change N.symm (ClassificationJordanCurve.Arcs.complexLIE (((1+(0:ℝ)/2:ℝ):ℂ)*(z:ℂ))) = c.map z
      simp only [zero_div,add_zero,Complex.ofReal_one,one_mul]
      rw [←hN,N.symm_apply_apply]
    obtain ⟨polar,hpolar⟩ := polarCoordinates
    let gamma : C(Circle,Plane) :=
      ⟨fun z => ClassificationJordanCurve.Arcs.complexLIE (polar (c z)).val,
        ClassificationJordanCurve.Arcs.complexLIE.continuous.comp
          (continuous_subtype_val.comp (polar.continuous.comp c.continuous))⟩
    have gamma_injective : Function.Injective gamma :=
      ClassificationJordanCurve.Arcs.complexLIE.injective.comp
        (Subtype.val_injective.comp (polar.injective.comp hc))
    let gammaCurve : Curve Plane := ⟨gamma,(gamma.continuous.isClosedEmbedding gamma_injective).isEmbedding⟩
    obtain ⟨H,hH,hcenter⟩ := planarFullCollar gammaCurve
    let W := Set.Ioo (-1:ℝ) 1
    let zeroW : W := ⟨0,by norm_num [W]⟩
    let O : Set (W × Circle) := {x | ClassificationJordanCurve.Arcs.complexLIE.symm (H x) ≠ 0}
    have hO : IsOpen O := isClosed_singleton.isOpen_compl.preimage
      (ClassificationJordanCurve.Arcs.complexLIE.symm.continuous.comp H.continuous)
    have hbase : ({zeroW}:Set W) ×ˢ (Set.univ:Set Circle) ⊆ O := by
      rintro ⟨w,z⟩ ⟨hw,_⟩
      have hw0 : w=zeroW := hw
      subst w
      change ClassificationJordanCurve.Arcs.complexLIE.symm (H (zeroW,z)) ≠ 0
      rw [hcenter]
      change ClassificationJordanCurve.Arcs.complexLIE.symm
        (ClassificationJordanCurve.Arcs.complexLIE (polar (c z)).val) ≠ 0
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact (polar (c z)).property
    obtain ⟨P,Q,hP,hQ,h0,hall,hPQ⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ hO hbase
    have hzP : zeroW ∈ P := h0 rfl
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hzP)
    let epsilon : ℝ := min (r/2) (1/2)
    have heps : 0 < epsilon := lt_min (by linarith) (by norm_num)
    have hepshalf : epsilon ≤ 1/2 := min_le_right _ _
    have hepsr : epsilon < r := (min_le_left _ _).trans_lt (by linarith)
    let width : W → W := fun w => ⟨epsilon*(w:ℝ),by
      constructor <;> nlinarith [w.property.1,w.property.2]⟩
    have hwidth : Continuous width :=
      (continuous_const.mul continuous_subtype_val).subtype_mk _
    have hwidthP (w : W) : width w ∈ P := by
      apply hball
      change |epsilon*(w:ℝ)-0| < r
      rw [sub_zero,abs_mul,abs_of_pos heps]
      have hwabs : |(w:ℝ)| < 1 := abs_lt.mpr w.property
      have h := mul_lt_mul_of_pos_left hwabs heps
      linarith
    have hclear (w : W) (z : Circle) : ClassificationJordanCurve.Arcs.complexLIE.symm (H (width w,z)) ≠ 0 :=
      hPQ ⟨hwidthP w,hall (Set.mem_univ z)⟩
    let lifted : C(W × Circle,{z:ℂ // z ≠ 0}) :=
      ⟨fun x => ⟨ClassificationJordanCurve.Arcs.complexLIE.symm (H (width x.1,x.2)),hclear x.1 x.2⟩,
        (ClassificationJordanCurve.Arcs.complexLIE.symm.continuous.comp
          (H.continuous.comp ((hwidth.comp continuous_fst).prodMk continuous_snd))).subtype_mk _⟩
    let e : C(W × Circle,Circle × ℝ) := ⟨polar.symm ∘ lifted,polar.symm.continuous.comp lifted.continuous⟩
    have hinj : Function.Injective e := by
      rintro ⟨w,z⟩ ⟨v,d⟩ he
      have hl := polar.symm.injective he
      have hplane := congrArg (fun q : {z:ℂ // z ≠ 0} => ClassificationJordanCurve.Arcs.complexLIE q.val) hl
      change ClassificationJordanCurve.Arcs.complexLIE
        (ClassificationJordanCurve.Arcs.complexLIE.symm (H (width w,z))) =
        ClassificationJordanCurve.Arcs.complexLIE
          (ClassificationJordanCurve.Arcs.complexLIE.symm (H (width v,d))) at hplane
      simp only [LinearIsometryEquiv.apply_symm_apply] at hplane
      have hh := hH.injective hplane
      have hw : width w = width v := congrArg Prod.fst hh
      have hwval : (w:ℝ)=(v:ℝ) := mul_left_cancel₀ heps.ne' (congrArg Subtype.val hw)
      have hz : z=d := by simpa only using congrArg (Prod.snd : W × Circle → Circle) hh
      exact Prod.ext (Subtype.ext hwval) hz
    refine ⟨e,hinj,?_⟩
    intro z
    have hwidth0 : width zeroW = zeroW := Subtype.ext (by simp [width,zeroW])
    change polar.symm (lifted (zeroW,z)) = c z
    apply polar.injective
    rw [polar.apply_symm_apply]
    apply Subtype.ext
    change ClassificationJordanCurve.Arcs.complexLIE.symm (H (width zeroW,z)) = (polar (c z)).val
    rw [hwidth0,hcenter]
    exact ClassificationJordanCurve.Arcs.complexLIE.symm_apply_apply _
  have uniformFullCollar {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (C : C(Set.Ioo (-1:ℝ) 1 × Circle,S))
    (hcenter : Function.Injective (fun z => C (⟨0,by norm_num⟩,z)))
    (hloc : ∀ x, ∃ U ∈ 𝓝 x, Set.InjOn C U) :
    ∃ E : C(Set.Ioo (-1:ℝ) 1 × Circle,S), Topology.IsOpenEmbedding E ∧
      ∀ z, E (⟨0,by norm_num⟩,z) = C (⟨0,by norm_num⟩,z) := by
    have openAnnulus
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S))
      (hE : Function.Injective E) : Topology.IsOpenEmbedding E := by
      have hopen : IsOpenMap E := by
        intro V hV
        rw [isOpen_iff_forall_mem_open]
        rintro z ⟨⟨w,c⟩,hwV,rfl⟩
        let a : ℝ := ((w : ℝ)-1)/2
        let b : ℝ := ((w : ℝ)+1)/2
        have haw : a < (w : ℝ) := by dsimp [a]; linarith [w.property.1]
        have hwb : (w : ℝ) < b := by dsimp [b]; linarith [w.property.2]
        have ha : -1 < a := by dsimp [a]; linarith [w.property.1]
        have hb : b < 1 := by dsimp [b]; linarith [w.property.2]
        have hab : a ≤ b := (haw.trans hwb).le
        let width : ℝ → Set.Ioo (-1 : ℝ) 1 := fun t =>
          ⟨(Set.projIcc a b hab t : ℝ),
            ⟨ha.trans_le (Set.projIcc a b hab t).property.1,
              lt_of_le_of_lt (Set.projIcc a b hab t).property.2 hb⟩⟩
        have hwc : Continuous width := by
          exact (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
        let angle : ℝ := Complex.arg (c : ℂ)
        let F : EuclideanSpace ℝ (Fin 2) → S :=
          fun x => E (width (x 0), Circle.exp (x 1))
        have hFc : Continuous F := E.continuous.comp
          ((hwc.comp (by fun_prop)).prodMk (Circle.exp.continuous.comp (by fun_prop)))
        let U : Set (EuclideanSpace ℝ (Fin 2)) :=
          {x | x 0 ∈ Set.Ioo a b ∧ x 1 ∈ Set.Ioo (angle-Real.pi/2) (angle+Real.pi/2) ∧
            (width (x 0),Circle.exp (x 1)) ∈ V}
        have hU : IsOpen U :=
          (isOpen_Ioo.preimage (by fun_prop)).inter
            ((isOpen_Ioo.preimage (by fun_prop)).inter
              (hV.preimage ((hwc.comp (by fun_prop)).prodMk
                (Circle.exp.continuous.comp (by fun_prop)))))
        have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ U) :
            (width (x 0) : ℝ) = x 0 := by
          exact congrArg Subtype.val (Set.projIcc_of_mem hab ⟨hx.1.1.le,hx.1.2.le⟩)
        have hi : Set.InjOn F U := by
          intro x hx y hy he
          have hh := hE he
          have hx0 := congrArg (fun q : Set.Ioo (-1 : ℝ) 1 × Circle => (q.1 : ℝ)) hh
          have hx1 := congrArg Prod.snd hh
          have hangle : x 1 = y 1 :=
            Circle.exp_injOn_Icc (a := angle-Real.pi/2) (b := angle+Real.pi/2)
              (by linarith [Real.pi_pos])
              ⟨hx.2.1.1.le,hx.2.1.2.le⟩ ⟨hy.2.1.1.le,hy.2.1.2.le⟩ hx1
          have hwidth : x 0 = y 0 := by
            change (width (x 0) : ℝ) = (width (y 0) : ℝ) at hx0
            simpa only [hclip x hx,hclip y hy] using hx0
          ext i
          fin_cases i
          · exact hwidth
          · exact hangle
        have hFU : IsOpen (F '' U) :=
          CurveComplex.surface_invariance_of_domain_probe F U hU hFc.continuousOn hi
        have hclipw : width (w : ℝ) = w := by
          apply Subtype.ext
          change (Set.projIcc a b hab (w : ℝ) : ℝ) = (w : ℝ)
          exact congrArg Subtype.val (Set.projIcc_of_mem hab ⟨haw.le,hwb.le⟩)
        have hexp : Circle.exp angle = c := Circle.exp_arg c
        let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (w : ℝ) angle
        have hx0 : x 0 = (w : ℝ) := by simp [x,Schoenflies.Plane.mk]
        have hx1 : x 1 = angle := by simp [x,Schoenflies.Plane.mk]
        have hx : x ∈ U := by
          refine ⟨?_,?_,?_⟩
          · change a < x 0 ∧ x 0 < b
            rw [hx0]
            exact ⟨haw,hwb⟩
          · rw [hx1]
            constructor <;> linarith [Real.pi_pos]
          · simpa only [hx0,hx1,hclipw,hexp] using hwV
        refine ⟨F '' U,?_,hFU,?_⟩
        · rintro y ⟨u,hu,rfl⟩
          exact ⟨(width (u 0),Circle.exp (u 1)),hu.2.2,rfl⟩
        · refine ⟨x,hx,?_⟩
          simp only [F,hx0,hx1,hclipw,hexp]
      exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap E.continuous hE hopen
    let W := Set.Ioo (-1:ℝ) 1
    let zeroW : W := ⟨0,by norm_num [W]⟩
    let K : Set (W × Circle) := ({zeroW}:Set W) ×ˢ Set.univ
    have hK : IsCompact K := isCompact_singleton.prod isCompact_univ
    have hKinj : Set.InjOn C K := by
      rintro ⟨w,z⟩ ⟨hw,_⟩ ⟨v,d⟩ ⟨hv,_⟩ he
      have hw0 : w=zeroW := hw
      have hv0 : v=zeroW := hv
      subst w
      subst v
      exact Prod.ext rfl (hcenter he)
    obtain ⟨N,hN,hKN,hNinj⟩ := hKinj.exists_isOpen_superset hK
      (fun x hx => C.continuous.continuousAt) (fun x hx => hloc x)
    obtain ⟨P,Q,hP,hQ,h0,hall,hPQ⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ hN hKN
    have hzP : zeroW ∈ P := h0 rfl
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hzP)
    let epsilon : ℝ := min (r/2) (1/2)
    have heps : 0 < epsilon := lt_min (by linarith) (by norm_num)
    have hepshalf : epsilon ≤ 1/2 := min_le_right _ _
    have hepsr : epsilon < r := (min_le_left _ _).trans_lt (by linarith)
    let width : W → W := fun w => ⟨epsilon*(w:ℝ),by
      constructor <;> nlinarith [w.property.1,w.property.2]⟩
    have hwidth : Continuous width :=
      (continuous_const.mul continuous_subtype_val).subtype_mk _
    have hwidthP (w : W) : width w ∈ P := by
      apply hball
      change |epsilon*(w:ℝ)-0| < r
      rw [sub_zero,abs_mul,abs_of_pos heps]
      have hwabs : |(w:ℝ)| < 1 := abs_lt.mpr w.property
      have h := mul_lt_mul_of_pos_left hwabs heps
      linarith
    let E : C(W × Circle,S) :=
      ⟨fun x => C (width x.1,x.2),C.continuous.comp
        ((hwidth.comp continuous_fst).prodMk continuous_snd)⟩
    have hE : Function.Injective E := by
      rintro ⟨w,z⟩ ⟨v,d⟩ he
      have hh := hNinj (hPQ ⟨hwidthP w,hall (Set.mem_univ _)⟩)
        (hPQ ⟨hwidthP v,hall (Set.mem_univ _)⟩) he
      have hw : width w=width v := congrArg Prod.fst hh
      have hwval : (w:ℝ)=(v:ℝ) := mul_left_cancel₀ heps.ne' (congrArg Subtype.val hw)
      have hz : z=d := by simpa only using congrArg (Prod.snd : W × Circle → Circle) hh
      exact Prod.ext (Subtype.ext hwval) hz
    refine ⟨E,openAnnulus E hE,?_⟩
    intro z
    have hw0 : width zeroW=zeroW := Subtype.ext (by simp [width,zeroW])
    change C (width zeroW,z)=C (zeroW,z)
    rw [hw0]
  have original_monodromy_coordinate (z : H2) :
      sourceAxisCoordinate (developedDeck monodromy z) = sourceAxisCoordinate z+(axisPeriod,0) := by
    have h := dilationCoordinate normalizedMonodromyIsometry axisPeriod
      actual_source_common_monodromy_is_dilation (axisNormalizingIsometry.symm z)
    change logarithmicCoordinate (axisNormalizingIsometry.symm (developedDeckIsometry monodromy z)) =
      logarithmicCoordinate (axisNormalizingIsometry.symm z)+(axisPeriod,0)
    simpa only [normalizedMonodromyIsometry,IsometryEquiv.trans_apply,
      axisNormalizingIsometry.apply_symm_apply] using h
  let modelLift : C(ℝ × ℝ,P) :=
    ⟨fun x => development.symm (sourceAxisCoordinate.symm (axisPeriod*x.1,x.2)),
      development.symm.continuous.comp (sourceAxisCoordinate.symm.continuous.comp
        ((continuous_const.mul continuous_fst).prodMk continuous_snd))⟩
  have modelLift_injective : Function.Injective modelLift := by
    intro x y h
    have hc := sourceAxisCoordinate.symm.injective (development.symm.injective h)
    have h1 := congrArg Prod.fst hc
    have h2 := congrArg Prod.snd hc
    exact Prod.ext (mul_left_cancel₀ haxisPeriod.ne' h1) h2
  have modelLift_period (x : ℝ × ℝ) : modelLift (x.1+1,x.2) = monodromy • modelLift x := by
    dsimp only [modelLift,ContinuousMap.coe_mk]
    apply development.injective
    apply sourceAxisCoordinate.injective
    rw [development.apply_symm_apply]
    change sourceAxisCoordinate (sourceAxisCoordinate.symm (axisPeriod*(x.1+1),x.2)) =
      sourceAxisCoordinate (developedDeck monodromy
        (sourceAxisCoordinate.symm (axisPeriod*x.1,x.2)))
    rw [original_monodromy_coordinate,sourceAxisCoordinate.apply_symm_apply,sourceAxisCoordinate.apply_symm_apply]
    ext <;> simp <;> ring
  obtain ⟨cyclicProjection,cyclicProjection_clock,cyclicProjection_locally_injective⟩ :=
    cyclicPlaneProjection 1 (Sigma.fst : P → A) actualCoveringMap modelLift modelLift_injective
      (fun x => (congrArg Sigma.fst (modelLift_period x)).trans (hqc.map_smul monodromy))
  let circleClock : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
  have originalCurveFullCollar (c : Curve E) (lift : C(ℝ,H2))
      (hlift : ∀ t, (development.symm (lift t)).1.val = c.map (Circle.exp t))
      (hperiodLift : ∀ t, lift (t+2*Real.pi) = developedDeck monodromy (lift t)) :
      ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,E), Topology.IsOpenEmbedding e ∧
        ∀ z, e (⟨0,by norm_num⟩,z) = c.map z := by
    let xs : C(ℝ,ℝ × ℝ) :=
      ⟨fun t => sourceAxisCoordinate (lift (t*(2*Real.pi))),
        sourceAxisCoordinate.continuous.comp (lift.continuous.comp
          (continuous_id.mul continuous_const))⟩
    have xs_period (t : ℝ) : xs (t+1) = xs t+(axisPeriod,0) := by
      change sourceAxisCoordinate (lift ((t+1)*(2*Real.pi))) = _
      rw [show (t+1)*(2*Real.pi)=t*(2*Real.pi)+2*Real.pi by ring,
        hperiodLift,original_monodromy_coordinate]
      rfl
    let r : C(ℝ,AddCircle (1:ℝ) × ℝ) :=
      ⟨fun t => (((xs t).1/axisPeriod:AddCircle (1:ℝ)),(xs t).2),
        ((AddCircle.continuous_mk' 1).comp (xs.continuous.fst.div_const _)).prodMk xs.continuous.snd⟩
    have r_period : Function.Periodic r 1 := by
      intro t
      apply Prod.ext
      · change (((xs (t+1)).1/axisPeriod:ℝ):AddCircle (1:ℝ)) = ((xs t).1/axisPeriod:ℝ)
        rw [xs_period]
        change ((((xs t).1+axisPeriod)/axisPeriod:ℝ):AddCircle (1:ℝ)) = ((xs t).1/axisPeriod:ℝ)
        rw [add_div,div_self haxisPeriod.ne',AddCircle.coe_add,AddCircle.coe_period,add_zero]
      · change (xs (t+1)).2=(xs t).2
        rw [xs_period]
        simp only [Prod.snd_add,Prod.snd,add_zero]
    let gammaA : C(AddCircle (1:ℝ),AddCircle (1:ℝ) × ℝ) :=
      ⟨r_period.lift,r.continuous.quotient_lift _⟩
    have gamma_clock (t : ℝ) : gammaA (t:AddCircle (1:ℝ)) = r t := r_period.lift_coe t
    let gamma : C(Circle,AddCircle (1:ℝ) × ℝ) :=
      gammaA.comp ⟨circleClock.symm,circleClock.symm.continuous⟩
    have projection_clock (t : ℝ) : (cyclicProjection (r t)).val =
        c.map (Circle.exp (t*(2*Real.pi))) := by
      have h := congrArg Subtype.val (cyclicProjection_clock ((xs t).1/axisPeriod,(xs t).2))
      change (cyclicProjection (r t)).val = (modelLift ((xs t).1/axisPeriod,(xs t).2)).1.val at h
      rw [h]
      have ht : (axisPeriod*((xs t).1/axisPeriod),(xs t).2) = xs t := by
        apply Prod.ext
        · exact mul_div_cancel₀ _ haxisPeriod.ne'
        · rfl
      change (development.symm (sourceAxisCoordinate.symm
        (axisPeriod*((xs t).1/axisPeriod),(xs t).2))).1.val = _
      rw [ht]
      change (development.symm (sourceAxisCoordinate.symm
        (sourceAxisCoordinate (lift (t*(2*Real.pi)))))).1.val = _
      rw [sourceAxisCoordinate.symm_apply_apply]
      exact hlift _
    have gamma_projection (z : Circle) : (cyclicProjection (gamma z)).val = c.map z := by
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (circleClock.symm z)
      have hz : circleClock (t:AddCircle (1:ℝ)) = z := by rw [ht,circleClock.apply_symm_apply]
      have he : Circle.exp (t*(2*Real.pi)) = z := by
        simpa only [circleClock,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,div_one,mul_comm] using hz
      change (cyclicProjection (gammaA (circleClock.symm z))).val = _
      rw [←ht,gamma_clock,projection_clock,he]
    have gamma_injective : Function.Injective gamma := by
      intro z w he
      apply c.embedded.injective
      exact (gamma_projection z).symm.trans
        ((congrArg (fun q => (cyclicProjection q).val) he).trans (gamma_projection w))
    let gammaCircle : C(Circle,Circle × ℝ) :=
      ⟨fun z => (circleClock (gamma z).1,(gamma z).2),
        (circleClock.continuous.comp gamma.continuous.fst).prodMk gamma.continuous.snd⟩
    have gammaCircle_injective : Function.Injective gammaCircle := by
      intro z w he
      apply gamma_injective
      have he1 : circleClock (gamma z).1 = circleClock (gamma w).1 := by
        simpa only [gammaCircle,ContinuousMap.coe_mk,Prod.fst] using
          congrArg (Prod.fst : Circle × ℝ → Circle) he
      have he2 : (gamma z).2 = (gamma w).2 := by
        simpa only [gammaCircle,ContinuousMap.coe_mk,Prod.snd] using
          congrArg (Prod.snd : Circle × ℝ → ℝ) he
      exact Prod.ext (circleClock.injective he1) he2
    obtain ⟨modelCollar,modelCollar_injective,modelCollar_center⟩ :=
      cylinderFullCollar gammaCircle gammaCircle_injective
    let modelCollarA : C(Set.Ioo (-1:ℝ) 1 × Circle,AddCircle (1:ℝ) × ℝ) :=
      ⟨fun x => (circleClock.symm (modelCollar x).1,(modelCollar x).2),
        (circleClock.symm.continuous.comp modelCollar.continuous.fst).prodMk modelCollar.continuous.snd⟩
    have modelCollarA_injective : Function.Injective modelCollarA := by
      intro x y he
      apply modelCollar_injective
      have he1 : circleClock.symm (modelCollar x).1 = circleClock.symm (modelCollar y).1 := by
        simpa only [modelCollarA,ContinuousMap.coe_mk,Prod.fst] using
          congrArg (Prod.fst : AddCircle (1:ℝ) × ℝ → AddCircle (1:ℝ)) he
      have he2 : (modelCollar x).2 = (modelCollar y).2 := by
        simpa only [modelCollarA,ContinuousMap.coe_mk,Prod.snd] using
          congrArg (Prod.snd : AddCircle (1:ℝ) × ℝ → ℝ) he
      exact Prod.ext (circleClock.symm.injective he1) he2
    have modelCollarA_center (z : Circle) : modelCollarA (⟨0,by norm_num⟩,z) = gamma z := by
      change (circleClock.symm (modelCollar (⟨0,by norm_num⟩,z)).1,
        (modelCollar (⟨0,by norm_num⟩,z)).2) = _
      rw [modelCollar_center]
      change (circleClock.symm (circleClock (gamma z).1),(gamma z).2) = _
      rw [circleClock.symm_apply_apply]
    let projectedCollar : C(Set.Ioo (-1:ℝ) 1 × Circle,E) :=
      ⟨fun x => (cyclicProjection (modelCollarA x)).val,
        continuous_subtype_val.comp (cyclicProjection.continuous.comp modelCollarA.continuous)⟩
    have projectedCollar_center (z : Circle) : projectedCollar (⟨0,by norm_num⟩,z) = c.map z := by
      change (cyclicProjection (modelCollarA (⟨0,by norm_num⟩,z))).val = _
      rw [modelCollarA_center,gamma_projection]
    have projectedCollar_locally_injective (x : Set.Ioo (-1:ℝ) 1 × Circle) :
        ∃ U ∈ 𝓝 x, Set.InjOn projectedCollar U := by
      obtain ⟨V,hV,hVi⟩ := cyclicProjection_locally_injective (modelCollarA x)
      refine ⟨modelCollarA ⁻¹' V,modelCollarA.continuous.continuousAt.preimage_mem_nhds hV,?_⟩
      intro y hy z hz he
      apply modelCollarA_injective
      apply hVi hy hz
      exact Subtype.val_injective he
    have projectedCollar_center_injective : Function.Injective
        (fun z => projectedCollar (⟨0,by norm_num⟩,z)) := by
      intro z w he
      change projectedCollar (⟨0,by norm_num⟩,z) = projectedCollar (⟨0,by norm_num⟩,w) at he
      rw [projectedCollar_center,projectedCollar_center] at he
      exact c.embedded.injective he
    obtain ⟨e,he,hcenter⟩ := uniformFullCollar projectedCollar
      projectedCollar_center_injective projectedCollar_locally_injective
    exact ⟨e,he,fun z => (hcenter z).trans (projectedCollar_center z)⟩
  obtain ⟨e0,he0,hcenter0⟩ := originalCurveFullCollar a sourceLift sourceLift_projection sourceLift_period
  obtain ⟨e1,he1,hcenter1⟩ := originalCurveFullCollar b targetLift targetLift_projection targetLift_period
  have restrictFullCollar
    (C : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (hC : Topology.IsOpenEmbedding C)
    (N : Set E) (hN : IsOpen N) (hcenter : ∀ z, C (⟨0,by norm_num⟩,z) ∈ N) :
    ∃ E : C(Set.Ioo (-1:ℝ) 1 × Circle,E), Topology.IsOpenEmbedding E ∧
      (∀ z, E (⟨0,by norm_num⟩,z)=C (⟨0,by norm_num⟩,z)) ∧ Set.range E ⊆ N := by
  
    let W := Set.Ioo (-1:ℝ) 1
    let zeroW : W := ⟨0,by norm_num [W]⟩
    have hKN : ({zeroW}:Set W) ×ˢ (Set.univ:Set Circle) ⊆ C ⁻¹' N := by
      rintro ⟨w,z⟩ ⟨hw,_⟩
      have hw0 : w=zeroW := hw
      subst w
      exact hcenter z
    obtain ⟨P,Q,hP,hQ,h0,hall,hPQ⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ (hN.preimage C.continuous) hKN
    have hzP : zeroW ∈ P := h0 rfl
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hzP)
    let epsilon : ℝ := min (r/2) (1/2)
    have heps : 0 < epsilon := lt_min (by linarith) (by norm_num)
    have hepshalf : epsilon ≤ 1/2 := min_le_right _ _
    have hepsr : epsilon < r := (min_le_left _ _).trans_lt (by linarith)
    let width : W → W := fun w => ⟨epsilon*(w:ℝ),by
      constructor <;> nlinarith [w.property.1,w.property.2]⟩
    have hwidth : Continuous width :=
      (continuous_const.mul continuous_subtype_val).subtype_mk _
    have hwidthP (w : W) : width w ∈ P := by
      apply hball
      change |epsilon*(w:ℝ)-0| < r
      rw [sub_zero,abs_mul,abs_of_pos heps]
      have hwabs : |(w:ℝ)| < 1 := abs_lt.mpr w.property
      have h := mul_lt_mul_of_pos_left hwabs heps
      linarith
    have hwidthEmb : Topology.IsEmbedding width := by
      apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      exact (Homeomorph.mulLeft₀ epsilon heps.ne').isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hwidthRange : Set.range width = (Subtype.val : W → ℝ) ⁻¹' Set.Ioo (-epsilon) epsilon := by
      ext v
      constructor
      · rintro ⟨w,rfl⟩
        change -epsilon < epsilon*(w:ℝ) ∧ epsilon*(w:ℝ)<epsilon
        constructor <;> nlinarith [w.property.1,w.property.2]
      · intro hv
        change -epsilon < (v:ℝ) ∧ (v:ℝ)<epsilon at hv
        have hw : (v:ℝ)/epsilon ∈ Set.Ioo (-1:ℝ) 1 := by
          constructor
          · exact (lt_div_iff₀ heps).mpr (by linarith)
          · exact (div_lt_iff₀ heps).mpr (by simpa using hv.2)
        refine ⟨⟨(v:ℝ)/epsilon,hw⟩,Subtype.ext ?_⟩
        exact mul_div_cancel₀ _ heps.ne'
    have hwidthOpen : Topology.IsOpenEmbedding width :=
      ⟨hwidthEmb,hwidthRange ▸ isOpen_Ioo.preimage continuous_subtype_val⟩
    let E : C(W × Circle,E) :=
      ⟨fun x => C (width x.1,x.2),C.continuous.comp
        ((hwidth.comp continuous_fst).prodMk continuous_snd)⟩
    have hE : Topology.IsOpenEmbedding E :=
      hC.comp (hwidthOpen.prodMap Topology.IsOpenEmbedding.id)
    refine ⟨E,hE,?_,?_⟩
    · intro z
      have hw0 : width zeroW=zeroW := Subtype.ext (by simp [width,zeroW])
      change C (width zeroW,z)=C (zeroW,z)
      rw [hw0]
    · rintro _ ⟨⟨w,z⟩,rfl⟩
      exact hPQ ⟨hwidthP w,hall (Set.mem_univ _)⟩
  have hclosedA : IsClosed a.image := (isCompact_range a.embedded.continuous).isClosed
  have hclosedB : IsClosed b.image := (isCompact_range b.embedded.continuous).isClosed
  obtain ⟨N0,N1,hN0,hN1,hAN0,hBN1,hNdis⟩ := normal_separation hclosedA hclosedB hdis
  obtain ⟨d0,hd0,hzero0,hrange0⟩ := restrictFullCollar e0 he0 N0 hN0 (fun z => by
    rw [hcenter0];exact hAN0 (Set.mem_range_self z))
  obtain ⟨d1,hd1,hzero1,hrange1⟩ := restrictFullCollar e1 he1 N1 hN1 (fun z => by
    rw [hcenter1];exact hBN1 (Set.mem_range_self z))
  open Matrix in
  open scoped MatrixGroups in
  have translated_horizontal_line_stabilizes_axis (F : ℝ × unitInterval → H2) (axis : ℝ → H2)
      (e : H2 ≃ᵢ H2) (he : ∀ t : ℝ, e (verticalPath t) = axis t)
      (τ M : ℝ) (hτ : 0 < τ) (hM : 0 ≤ M)
      (hbound : ∀ x : ℝ × unitInterval, dist (F x) (axis (x.1*τ)) ≤ M)
      (g : H2 ≃ᵢ H2) (v : unitInterval) (hgF : ∀ t : ℝ, g (F (t,v)) ∈ Set.range F) :
      g '' Set.range axis = Set.range axis := by
    have tube_cone (A : Set H2) (B : ℝ) (hB : 0 ≤ B)
        (hA : ∀ z ∈ A, ∃ t : ℝ, dist z (verticalPath t) ≤ B) :
        ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ A, |z.re| ≤ K*z.im := by
      have vertical_coordinate_bounds (z : H2) (t B : ℝ) (hB : 0 ≤ B)
          (hd : dist z (verticalPath t) ≤ B) :
          Real.exp (t-B) ≤ z.im ∧
            ‖(z : ℂ)‖ ≤ (Real.sinh B+Real.cosh B)*Real.exp t := by
        have hlog := (UpperHalfPlane.dist_log_im_le z (verticalPath t)).trans hd
        simp only [verticalPath,UpperHalfPlane.mk_im,Real.log_exp,Real.dist_eq] at hlog
        have hlower : t-B ≤ Real.log z.im := by
          have h := (abs_le.mp hlog).1
          linarith
        have him : Real.exp (t-B) ≤ z.im := by
          have h := Real.exp_le_exp.mpr hlower
          simpa only [Real.exp_log z.im_pos] using h
        refine ⟨him,?_⟩
        have hball := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hd
        have hcenter : ((verticalPath t).center B : ℂ) =
            ((Real.exp t*Real.cosh B : ℝ) : ℂ)*Complex.I := by
          apply Complex.ext <;> simp [UpperHalfPlane.center,verticalPath,← Complex.ofReal_exp]
        have hnorm : ‖((verticalPath t).center B : ℂ)‖ = Real.exp t*Real.cosh B := by
          rw [hcenter,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
          exact abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
        have hball' : dist (z : ℂ) ((verticalPath t).center B : ℂ) ≤ Real.exp t*Real.sinh B := by
          simpa [verticalPath] using hball
        calc
          ‖(z : ℂ)‖ ≤ dist (z : ℂ) ((verticalPath t).center B : ℂ)+‖((verticalPath t).center B : ℂ)‖ :=
            by simpa only [dist_zero_right] using dist_triangle (z : ℂ) ((verticalPath t).center B : ℂ) 0
          _ ≤ Real.exp t*Real.sinh B+Real.exp t*Real.cosh B := add_le_add hball' hnorm.le
          _ = (Real.sinh B+Real.cosh B)*Real.exp t := by ring
    
      let C : ℝ := Real.sinh B + Real.cosh B
      have hC : 0 ≤ C := add_nonneg (Real.sinh_nonneg_iff.mpr hB) (Real.cosh_pos B).le
      let K : ℝ := C*Real.exp B
      have hK : 0 ≤ K := mul_nonneg hC (Real.exp_pos B).le
      refine ⟨K,hK,?_⟩
      intro z hz
      obtain ⟨t,ht⟩ := hA z hz
      obtain ⟨him,hnorm⟩ := vertical_coordinate_bounds z t B hB ht
      have habs : |z.re| ≤ ‖(z:ℂ)‖ := Complex.abs_re_le_norm _
      have he : Real.exp t = Real.exp B*Real.exp (t-B) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        |z.re| ≤ ‖(z:ℂ)‖ := habs
        _ ≤ C*Real.exp t := hnorm
        _ = K*Real.exp (t-B) := by rw [he]; dsimp [K]; ring
        _ ≤ K*z.im := mul_le_mul_of_nonneg_left him hK
    have cone_axis (A : GL (Fin 2) ℝ) (K : ℝ) (hK : 0 ≤ K)
        (hbound : ∀ t : ℝ, |(A • verticalPath t : H2).re| ≤ K*(A • verticalPath t : H2).im) :
        ∀ t : ℝ, (A • verticalPath t : H2).re = 0 := by
      have bounded_coefficients (a b K : ℝ) (hK : 0 ≤ K)
          (hbound : ∀ r : ℝ, 0 < r → |a*r^2+b| ≤ K*r) : a=0 ∧ b=0 := by
        have ha : a=0 := by
          by_contra hane
          have habs : 0 < |a| := abs_pos.mpr hane
          let r : ℝ := (K+|b|+1)/|a|+1
          have hr : 1 < r := by
            have hh : 0 < (K+|b|+1)/|a| := div_pos (by positivity) habs
            dsimp [r]
            linarith
          have har : |a| *r = K+|b|+1+|a| := by
            dsimp [r]
            field_simp <;> ring
          have h := hbound r (by linarith)
          have ht : |a*r^2| ≤ |a*r^2+b|+|b| := by
            calc
              |a*r^2| = |a*r^2+b-b| := by congr 1;ring
              _ ≤ |a*r^2+b|+|b| := by
                simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (a*r^2+b) 0 b
          have he : |a*r^2| = |a| *r^2 := by rw [abs_mul,abs_sq]
          rw [he] at ht
          nlinarith [abs_nonneg b]
        have hb : b=0 := by
          by_contra hbne
          have hbabs : 0 < |b| := abs_pos.mpr hbne
          let r : ℝ := |b|/(2*(K+1))
          have hr : 0 < r := by dsimp [r];positivity
          have he : 2*(K+1)*r=|b| := by dsimp [r];field_simp
          have h := hbound r hr
          rw [ha,zero_mul,zero_add] at h
          nlinarith
        exact ⟨ha,hb⟩
      have hRe (r : ℝ) (hr : 0 < r) :
          (A • verticalPath (Real.log r) : H2).re =
            (A 0 0*A 1 0*r^2+A 0 1*A 1 1)/Complex.normSq (UpperHalfPlane.denom A (verticalPath (Real.log r))) := by
        rw [UpperHalfPlane.re_smul]
        simp only [UpperHalfPlane.num,UpperHalfPlane.denom,Complex.div_re,
          Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
          Complex.ofReal_re,Complex.ofReal_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
          verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,Real.exp_log hr,
          mul_zero,zero_mul,sub_zero,add_zero,zero_add]
        congr 1
        ring
      have hcoef : ∀ r : ℝ, 0 < r → |(A 0 0*A 1 0)*r^2+(A 0 1*A 1 1)| ≤
          (K*|A.det.val|)*r := by
        intro r hr
        have h := hbound (Real.log r)
        have hD : 0 < Complex.normSq (UpperHalfPlane.denom A (verticalPath (Real.log r))) :=
          UpperHalfPlane.normSq_denom_pos A (verticalPath (Real.log r)).im_ne_zero
        rw [hRe r hr,UpperHalfPlane.im_smul_eq_div_normSq,abs_div,abs_of_pos hD] at h
        have he : (verticalPath (Real.log r)).im = r := by simp [verticalPath,Real.exp_log hr]
        rw [he,←mul_div_assoc] at h
        have hh := (div_le_div_iff_of_pos_right hD).mp h
        nlinarith
      obtain ⟨hac,hbd⟩ := bounded_coefficients (A 0 0*A 1 0) (A 0 1*A 1 1)
        (K*|A.det.val|) (mul_nonneg hK (abs_nonneg _)) hcoef
      intro t
      have he : Real.log (Real.exp t) = t := Real.log_exp t
      rw [←he,hRe _ (Real.exp_pos t),hac,hbd]
      simp
    have axis_range (g : H2 ≃ᵢ H2) (hre : ∀ t : ℝ, (g (verticalPath t)).re = 0) :
        g '' Set.range verticalPath = Set.range verticalPath := by
      have real_isometry_translation_or_reflection (f : ℝ → ℝ) (hf : Isometry f) :
          (∀t, f t=f 0+t) ∨ (∀t, f t=f 0-t) := by
        have h01 := hf.dist_eq 1 0
        simp only [Real.dist_eq, sub_zero, abs_one] at h01
        have hsign : f 1-f 0 = 1 ∨ f 1-f 0 = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h01
        have heq (t : ℝ) : (f t-f 0)^2=t^2 ∧ (f t-f 1)^2=(t-1)^2 := by
          have h0 := hf.dist_eq t 0
          have h1 := hf.dist_eq t 1
          simp only [Real.dist_eq, sub_zero] at h0 h1
          constructor
          · nlinarith only [sq_abs (f t-f 0),sq_abs t, congrArg (fun x : ℝ => x^2) h0]
          · nlinarith only [sq_abs (f t-f 1),sq_abs (t-1), congrArg (fun x : ℝ => x^2) h1]
        rcases hsign with hp | hn
        · have hall (t : ℝ) : f t = f 0+t := by
            obtain ⟨h0,h1⟩ := heq t
            nlinarith only [h0,h1,hp]
          exact Or.inl hall
        · have hall (t : ℝ) : f t = f 0-t := by
            obtain ⟨h0,h1⟩ := heq t
            nlinarith only [h0,h1,hn]
          exact Or.inr hall
      
      
      let q : ℝ → ℝ := fun t => Real.log (g (verticalPath t)).im
      have hcoord (t : ℝ) : g (verticalPath t) = verticalPath (q t) := by
        apply UpperHalfPlane.ext_re_im
        · rw [hre]
          rfl
        · change (g (verticalPath t)).im = Real.exp (Real.log (g (verticalPath t)).im)
          exact (Real.exp_log (g (verticalPath t)).im_pos).symm
      have hq : Isometry q := by
        apply Isometry.of_dist_eq
        intro t u
        rw [←verticalPath_isometry.dist_eq,←hcoord,←hcoord,g.isometry.dist_eq,verticalPath_isometry.dist_eq]
      have hqsurj : Function.Surjective q := by
        rcases real_isometry_translation_or_reflection q hq with hp | hn
        · intro r
          exact ⟨r-q 0,by rw [hp];ring⟩
        · intro r
          exact ⟨q 0-r,by rw [hn];ring⟩
      ext z
      constructor
      · rintro ⟨_,⟨t,rfl⟩,rfl⟩
        exact ⟨q t,(hcoord t).symm⟩
      · rintro ⟨r,rfl⟩
        obtain ⟨t,ht⟩ := hqsurj r
        exact ⟨verticalPath t,Set.mem_range_self t,(hcoord t).trans (congrArg verticalPath ht)⟩
    let gn : H2 ≃ᵢ H2 := (e.trans g).trans e.symm
    have hgn (z : H2) : gn z = e.symm (g (e z)) := rfl
    have htube : ∀ z ∈ Set.range (fun t : ℝ => gn (verticalPath t)),
        ∃ r : ℝ, dist z (verticalPath r) ≤ 2*M := by
      rintro z ⟨t,rfl⟩
      let x : ℝ × unitInterval := (t/τ,v)
      obtain ⟨y,hy⟩ := hgF (t/τ)
      refine ⟨y.1*τ,?_⟩
      have hx : x.1*τ = t := by dsimp [x];field_simp
      have hd : dist (g (axis t)) (axis (y.1*τ)) ≤ 2*M := by
        have hb := hbound x
        rw [hx] at hb
        calc
          dist (g (axis t)) (axis (y.1*τ)) ≤
              dist (g (axis t)) (g (F x))+dist (g (F x)) (axis (y.1*τ)) := dist_triangle _ _ _
          _ = dist (axis t) (F x)+dist (F y) (axis (y.1*τ)) := by
            rw [g.isometry.dist_eq,←hy]
          _ ≤ M+M := add_le_add (by simpa only [dist_comm] using hb) (hbound y)
          _ = 2*M := by ring
      have hdist := e.isometry.dist_eq (gn (verticalPath t)) (verticalPath (y.1*τ))
      rw [hgn,e.apply_symm_apply,he,he] at hdist
      change dist (gn (verticalPath t)) (verticalPath (y.1*τ)) ≤ 2*M
      rw [hgn,he]
      rw [hdist] at hd
      exact hd
    obtain ⟨K,hK,hcone⟩ := tube_cone _ (2*M) (by positivity) htube
    obtain ⟨A,hA⟩ := axis_metric_isometry_gl_representation gn
    have hre : ∀ t : ℝ, (gn (verticalPath t)).re = 0 := by
      have hB : ∀ t : ℝ, |(A • verticalPath t : H2).re| ≤ K*(A • verticalPath t : H2).im := by
        intro t
        rw [←hA]
        exact hcone _ (Set.mem_range_self t)
      intro t
      rw [hA]
      exact cone_axis A K hK hB t
    have hrange := axis_range gn hre
    ext z
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      have hm : gn (verticalPath t) ∈ Set.range verticalPath := by
        rw [←hrange]
        exact Set.mem_image_of_mem gn (Set.mem_range_self t)
      obtain ⟨r,hr⟩ := hm
      refine ⟨r,?_⟩
      have h := congrArg e hr
      rw [hgn,e.apply_symm_apply,he,he] at h
      exact h
    · rintro ⟨r,rfl⟩
      have hm : verticalPath r ∈ gn '' Set.range verticalPath := by
        rw [hrange]
        exact Set.mem_range_self r
      obtain ⟨_,⟨t,rfl⟩,ht⟩ := hm
      refine ⟨axis t,Set.mem_range_self t,?_⟩
      have h := congrArg e ht
      rw [hgn,e.apply_symm_apply,he,he] at h
      exact h

  have actual_connected_translate_meeting_facing_is_inside
      (R : Set H2) (hconn : IsPreconnected R)
      (hdS : Disjoint R (Set.range sourceLift)) (hdT : Disjoint R (Set.range targetLift))
      (hmeet : (R ∩ facingRegion).Nonempty) : R ⊆ Set.range actualMarkedStrip := by
    have hS : R ⊆ sourceInner ∪ sourceOuter := by
      rw [hSourceSidesPartition]
      exact Set.disjoint_left.mp hdS
    have hT : R ⊆ targetInner ∪ targetOuter := by
      rw [hTargetSidesPartition]
      exact Set.disjoint_left.mp hdT
    obtain ⟨z,hzR,hzFacing⟩ := hmeet
    have hSin : R ⊆ sourceInner := by
      rcases hconn.subset_or_subset hSourceInnerOpen hSourceOuterOpen hSourceSidesDisjoint hS with h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp hSourceSidesDisjoint hzFacing.1 (h hzR))
    have hTin : R ⊆ targetInner := by
      rcases hconn.subset_or_subset hTargetInnerOpen hTargetOuterOpen hTargetSidesDisjoint hT with h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp hTargetSidesDisjoint hzFacing.2 (h hzR))
    intro w hw
    have hwf : w ∈ facingRegion := ⟨hSin hw,hTin hw⟩
    rw [←actual_marked_strip_interior_eq_facing] at hwf
    exact Set.image_subset_range _ _ hwf
  have actual_bottom_line_range_in_strip : Set.range sourceLift ⊆ Set.range actualMarkedStrip := by
    rintro z ⟨t,rfl⟩
    refine ⟨((t-sourceParameter)/(2*Real.pi),0),?_⟩
    rw [actual_marked_strip_bottom]
    congr 1
    field_simp
    ring
  have actual_top_line_range_in_strip : Set.range targetLift ⊆ Set.range actualMarkedStrip := by
    rintro z ⟨t,rfl⟩
    refine ⟨((t-targetParameter)/(2*Real.pi),1),?_⟩
    rw [actual_marked_strip_top]
    congr 1
    field_simp
    ring
  have actual_bottom_translate_in_strip_axis
      (k : deck (Sigma.fst : P → A))
      (hk : developedDeck k '' Set.range sourceLift ⊆ Set.range actualMarkedStrip) :
      developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
    apply translated_horizontal_line_stabilizes_axis actualMarkedStrip actualAxis axisNormalizingIsometry
      axisNormalizer_control axisPeriod stripAxisBound haxisPeriod stripAxisBound_nonnegative
      stripAxisBound_control (developedDeckIsometry k) 0
    intro t
    apply hk
    refine Set.mem_image_of_mem _ ?_
    rw [actual_marked_strip_bottom]
    exact Set.mem_range_self _
  have actual_top_translate_in_strip_axis
      (k : deck (Sigma.fst : P → A))
      (hk : developedDeck k '' Set.range targetLift ⊆ Set.range actualMarkedStrip) :
      developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
    apply translated_horizontal_line_stabilizes_axis actualMarkedStrip actualAxis axisNormalizingIsometry
      axisNormalizer_control axisPeriod stripAxisBound haxisPeriod stripAxisBound_nonnegative
      stripAxisBound_control (developedDeckIsometry k) 1
    intro t
    apply hk
    refine Set.mem_image_of_mem _ ?_
    rw [actual_marked_strip_top]
    exact Set.mem_range_self _
  have actual_noncyclic_any_facing_overlap_stabilizes_axis
      (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ, k ≠ monodromy^n)
      (hmeet : (developedDeck k '' facingRegion ∩ facingRegion).Nonempty) :
      developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
    by_cases hs : ((developedDeck k '' Set.range sourceLift) ∩ facingRegion).Nonempty
    · apply actual_bottom_translate_in_strip_axis k
      apply actual_connected_translate_meeting_facing_is_inside _
        ((isConnected_range sourceLift.continuous).image (developedDeck k)
          (developedDeck k).continuous.continuousOn).isPreconnected
        (actual_noncyclic_source_and_target_translates_disjoint k hk).1
      · simpa only [actual_developedDeck_one,Set.image_id'] using
          all_developed_source_target_translates_disjoint k 1
      · exact hs
    by_cases ht : ((developedDeck k '' Set.range targetLift) ∩ facingRegion).Nonempty
    · apply actual_top_translate_in_strip_axis k
      apply actual_connected_translate_meeting_facing_is_inside _
        ((isConnected_range targetLift.continuous).image (developedDeck k)
          (developedDeck k).continuous.continuousOn).isPreconnected
      · simpa only [actual_developedDeck_one,Set.image_id'] using
          (all_developed_source_target_translates_disjoint 1 k).symm
      · exact (actual_noncyclic_source_and_target_translates_disjoint k hk).2
      · exact ht
    have sidecontain (sideIn sideOut : Set H2) (hI : IsOpen sideIn) (hO : IsOpen sideOut) (hd : Disjoint sideIn sideOut)
        (hp : sideIn ∪ sideOut = (Set.range sourceLift)ᶜ)
        (havoid : ¬ ((developedDeck k '' Set.range sourceLift) ∩ facingRegion).Nonempty)
        (hw : (developedDeck k '' sideIn ∩ facingRegion).Nonempty) :
        facingRegion ⊆ developedDeck k '' sideIn := by
      have hsub : facingRegion ⊆ developedDeck k '' sideIn ∪ developedDeck k '' sideOut := by
        rw [←Set.image_union,hp,(developedDeck k).image_compl]
        intro z hz hzb
        exact havoid ⟨z,hzb,hz⟩
      rcases actual_facing_region_connected.isPreconnected.subset_or_subset
        ((developedDeck k).isOpenMap _ hI) ((developedDeck k).isOpenMap _ hO)
        (hd.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _)) hsub with h | h
      · exact h
      · obtain ⟨z,hzI,hzf⟩ := hw
        exact False.elim (Set.disjoint_left.mp
          (hd.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _)) hzI (h hzf))
    have sourcecontain : facingRegion ⊆ developedDeck k '' sourceInner := by
      apply sidecontain sourceInner sourceOuter hSourceInnerOpen hSourceOuterOpen
        hSourceSidesDisjoint hSourceSidesPartition hs
      obtain ⟨z,⟨w,hw,rfl⟩,hz⟩ := hmeet
      exact ⟨developedDeck k w,⟨w,hw.1,rfl⟩,hz⟩
    have targetcontain : facingRegion ⊆ developedDeck k '' targetInner := by
      have hsub : facingRegion ⊆ developedDeck k '' targetInner ∪ developedDeck k '' targetOuter := by
        rw [←Set.image_union,hTargetSidesPartition,(developedDeck k).image_compl]
        intro z hz hzb
        exact ht ⟨z,hzb,hz⟩
      rcases actual_facing_region_connected.isPreconnected.subset_or_subset
        ((developedDeck k).isOpenMap _ hTargetInnerOpen) ((developedDeck k).isOpenMap _ hTargetOuterOpen)
        (hTargetSidesDisjoint.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _)) hsub with h | h
      · exact h
      · obtain ⟨z,⟨w,hw,he⟩,hz⟩ := hmeet
        exact False.elim (Set.disjoint_left.mp
          (hTargetSidesDisjoint.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _))
          ⟨w,hw.2,he⟩ (h hz))
    have hf : facingRegion ⊆ developedDeck k '' facingRegion := by
      intro z hz
      obtain ⟨s,hsI,hsz⟩ := sourcecontain hz
      obtain ⟨t,htI,htz⟩ := targetcontain hz
      have hst : s = t := (developedDeck k).injective (hsz.trans htz.symm)
      exact ⟨s,⟨hsI,hst ▸ htI⟩,hsz⟩
    have hclosed : Set.range actualMarkedStrip ⊆ developedDeck k '' Set.range actualMarkedStrip := by
      rw [actual_marked_strip_range_eq_facing_closure,(developedDeck k).image_closure]
      exact closure_mono hf
    have hinverse : developedDeck k⁻¹ '' Set.range sourceLift ⊆ Set.range actualMarkedStrip := by
      rintro _ ⟨z,hz,rfl⟩
      obtain ⟨w,hw,hwe⟩ := hclosed (actual_bottom_line_range_in_strip hz)
      have hmul := actual_developedDeck_mul k⁻¹ k w
      rw [inv_mul_cancel] at hmul
      rw [actual_developedDeck_one] at hmul
      rw [←hwe]
      exact hmul ▸ hw
    have haxisinv := actual_bottom_translate_in_strip_axis k⁻¹ hinverse
    have him := congrArg (fun S : Set H2 => developedDeck k '' S) haxisinv
    rw [Set.image_image] at him
    have hcomp : (developedDeck k) ∘ (developedDeck k⁻¹) = id := by
      funext z
      have h := actual_developedDeck_mul k k⁻¹ z
      rw [mul_inv_cancel,actual_developedDeck_one] at h
      exact h.symm
    change ((developedDeck k) ∘ (developedDeck k⁻¹)) '' Set.range actualAxis = developedDeck k '' Set.range actualAxis at him
    rw [hcomp,Set.image_id] at him
    exact him.symm

  have actual_axis_preserving_deck_in_stabilizer
      (k : deck (Sigma.fst : P → A))
      (hk : developedDeck k '' Set.range actualAxis = Set.range actualAxis) :
      k ∈ axisStabilizer := by
    have hlift (t : ℝ) : liftedNormalizedAxis t = development.symm (actualAxis t) := by
      change development.symm (axisNormalizingIsometry (verticalPath t)) = _
      rw [show axisNormalizingIsometry (verticalPath t) = actualAxis t from axisNormalizer_control t]
    apply MulAction.mem_stabilizer_iff.mpr
    change (fun z : P => k • z) '' Set.range liftedNormalizedAxis = Set.range liftedNormalizedAxis
    apply Set.Subset.antisymm
    · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
      have hm : developedDeck k (actualAxis t) ∈ Set.range actualAxis := by
        rw [←hk]
        exact Set.mem_image_of_mem _ (Set.mem_range_self t)
      obtain ⟨s,hs⟩ := hm
      refine ⟨s,?_⟩
      rw [hlift,hlift]
      apply development.injective
      rw [development.apply_symm_apply]
      change actualAxis s = developedDeck k (actualAxis t)
      exact hs
    · rintro _ ⟨t,rfl⟩
      have hm : actualAxis t ∈ developedDeck k '' Set.range actualAxis := hk.symm ▸ Set.mem_range_self t
      obtain ⟨_,⟨s,rfl⟩,hs⟩ := hm
      refine ⟨liftedNormalizedAxis s,Set.mem_range_self s,?_⟩
      rw [hlift,hlift]
      apply development.injective
      rw [development.apply_symm_apply]
      change developedDeck k (actualAxis s) = actualAxis t
      exact hs
  have square_generator_cosets {G : Type} [Group G] (d g : G) (hd : d=g^2) (n : ℤ) :
      ∃ m : ℤ, g^n=d^m ∨ g^n=d^m*g := by
    refine ⟨n/2,?_⟩
    have hn : n=2*(n/2)+n%2 := by omega
    have hr : n%2=0 ∨ n%2=1 := by omega
    have hp : g^n=d^(n/2)*g^(n%2) := by
      calc
        g^n = g^(2*(n/2)+n%2) := congrArg (fun j : ℤ => g^j) hn
        _ = (g^2)^(n/2)*g^(n%2) := by rw [_root_.zpow_add,_root_.zpow_mul,zpow_ofNat]
        _ = d^(n/2)*g^(n%2) := by rw [←hd]
    rcases hr with hr | hr
    · left
      simpa only [hr,zpow_zero,mul_one] using hp
    · right
      simpa only [hr,zpow_one] using hp
  have actual_noncyclic_facing_overlap_is_residual_glide_coset
      (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ, k ≠ monodromy^n)
      (hmeet : (developedDeck k '' facingRegion ∩ facingRegion).Nonempty) :
      originalAxisNatIndex = 2 ∧ ∃ m : ℤ, k = monodromy^m*minimalAxisDeck.val := by
    have haxis := actual_noncyclic_any_facing_overlap_stabilizes_axis k hk hmeet
    let kAxis : axisStabilizer := ⟨k,actual_axis_preserving_deck_in_stabilizer k haxis⟩
    obtain ⟨n,hn⟩ := actual_every_axis_stabilizer_is_minimal_generator_power kAxis
    have hkgen : k = minimalAxisDeck.val^n := congrArg Subtype.val hn
    rcases actual_source_minimal_axis_index_one_or_two with h1 | h2
    · have hmono : monodromy=minimalAxisDeck.val := by
        rw [original_monodromy_minimal_axis_nat_root,h1,pow_one]
      exact False.elim (hk n (hkgen.trans (by rw [hmono])))
    · have hmono : monodromy=minimalAxisDeck.val^2 := by
        rw [original_monodromy_minimal_axis_nat_root,h2]
      obtain ⟨m,hm | hm⟩ := square_generator_cosets monodromy minimalAxisDeck.val hmono n
      · exact False.elim (hk m (hkgen.trans hm))
      · exact ⟨h2,m,hkgen.trans hm⟩
  have actual_index_one_has_arbitrary_deck_facing_separation
      (hindex : originalAxisNatIndex=1) (k : deck (Sigma.fst : P → A))
      (hk : ∀ n : ℤ, k ≠ monodromy^n) :
      Disjoint (developedDeck k '' facingRegion) facingRegion := by
    apply Set.disjoint_left.mpr
    intro z hz1 hz2
    have h2 := (actual_noncyclic_facing_overlap_is_residual_glide_coset k hk ⟨z,hz1,hz2⟩).1
    omega

  have actual_index_one_axis_preserving_deck_is_cyclic
      (hindex : originalAxisNatIndex=1) (k : deck (Sigma.fst : P → A))
      (haxis : developedDeck k '' Set.range actualAxis = Set.range actualAxis) :
      ∃ n : ℤ, k = monodromy^n := by
    let kAxis : axisStabilizer := ⟨k,actual_axis_preserving_deck_in_stabilizer k haxis⟩
    obtain ⟨n,hn⟩ := actual_every_axis_stabilizer_is_minimal_generator_power kAxis
    have hg : k = minimalAxisDeck.val^n := congrArg Subtype.val hn
    have hmono : monodromy=minimalAxisDeck.val := by
      rw [original_monodromy_minimal_axis_nat_root,hindex,pow_one]
    exact ⟨n,hg.trans (by rw [hmono])⟩
  have actual_index_one_no_noncyclic_boundary_in_facing
      (hindex : originalAxisNatIndex=1) (k : deck (Sigma.fst : P → A))
      (hk : ∀ n : ℤ, k ≠ monodromy^n) :
      Disjoint (developedDeck k '' Set.range sourceLift) facingRegion ∧
      Disjoint (developedDeck k '' Set.range targetLift) facingRegion := by
    constructor
    · apply Set.disjoint_left.mpr
      intro z hz1 hz2
      have hR := actual_connected_translate_meeting_facing_is_inside
        (developedDeck k '' Set.range sourceLift)
        ((isConnected_range sourceLift.continuous).image (developedDeck k)
          (developedDeck k).continuous.continuousOn).isPreconnected
        (actual_noncyclic_source_and_target_translates_disjoint k hk).1
        (by simpa only [actual_developedDeck_one,Set.image_id'] using
          all_developed_source_target_translates_disjoint k 1) ⟨z,hz1,hz2⟩
      obtain ⟨n,hn⟩ := actual_index_one_axis_preserving_deck_is_cyclic hindex k
        (actual_bottom_translate_in_strip_axis k hR)
      exact hk n hn
    · apply Set.disjoint_left.mpr
      intro z hz1 hz2
      have hR := actual_connected_translate_meeting_facing_is_inside
        (developedDeck k '' Set.range targetLift)
        ((isConnected_range targetLift.continuous).image (developedDeck k)
          (developedDeck k).continuous.continuousOn).isPreconnected
        (by simpa only [actual_developedDeck_one,Set.image_id'] using
          (all_developed_source_target_translates_disjoint 1 k).symm)
        (actual_noncyclic_source_and_target_translates_disjoint k hk).2 ⟨z,hz1,hz2⟩
      obtain ⟨n,hn⟩ := actual_index_one_axis_preserving_deck_is_cyclic hindex k
        (actual_top_translate_in_strip_axis k hR)
      exact hk n hn
  have actual_strip_point_in_facing_or_boundary (x : ℝ × Interval) :
      actualMarkedStrip x ∈ facingRegion ∨ actualMarkedStrip x ∈ Set.range sourceLift ∨
        actualMarkedStrip x ∈ Set.range targetLift := by
    by_cases h0 : x.2=0
    · right;left
      rw [show x=(x.1,0) from Prod.ext rfl h0,actual_marked_strip_bottom]
      exact Set.mem_range_self _
    by_cases h1 : x.2=1
    · right;right
      rw [show x=(x.1,1) from Prod.ext rfl h1,actual_marked_strip_top]
      exact Set.mem_range_self _
    left
    apply actual_marked_strip_interior_in_facing
    refine ⟨x,?_,rfl⟩
    constructor
    · change (0:ℝ)<(x.2:ℝ)
      by_contra h
      have he : (x.2:ℝ)=0 := le_antisymm (le_of_not_gt h) x.2.property.1
      exact h0 (Subtype.ext he)
    · change (x.2:ℝ)<1
      by_contra h
      have he : (x.2:ℝ)=1 := le_antisymm x.2.property.2 (le_of_not_gt h)
      exact h1 (Subtype.ext he)
  have actual_index_one_full_deck_strip_separation
      (hindex : originalAxisNatIndex=1) (k : deck (Sigma.fst : P → A))
      (hk : ∀ n : ℤ, k ≠ monodromy^n) :
      Disjoint (developedDeck k '' Set.range actualMarkedStrip) (Set.range actualMarkedStrip) := by
    have hkInv : ∀ n : ℤ, k⁻¹ ≠ monodromy^n := by
      intro n hn
      apply hk (-n)
      have h := congrArg Inv.inv hn
      simpa only [inv_inv,←_root_.zpow_neg] using h
    have hBD := actual_index_one_no_noncyclic_boundary_in_facing hindex k hk
    have hBDinv := actual_index_one_no_noncyclic_boundary_in_facing hindex k⁻¹ hkInv
    have hSS := (actual_noncyclic_source_and_target_translates_disjoint k hk).1
    have hTT := (actual_noncyclic_source_and_target_translates_disjoint k hk).2
    have hST : Disjoint (developedDeck k '' Set.range sourceLift) (Set.range targetLift) := by
      simpa only [actual_developedDeck_one,Set.image_id'] using all_developed_source_target_translates_disjoint k 1
    have hTS : Disjoint (developedDeck k '' Set.range targetLift) (Set.range sourceLift) := by
      simpa only [actual_developedDeck_one,Set.image_id'] using (all_developed_source_target_translates_disjoint 1 k).symm
    apply Set.disjoint_left.mpr
    rintro z ⟨_,⟨x,rfl⟩,hx⟩ ⟨y,hy⟩
    have hxy : developedDeck k (actualMarkedStrip x) = actualMarkedStrip y := hx.trans hy.symm
    have hinv : developedDeck k⁻¹ (actualMarkedStrip y) = actualMarkedStrip x := by
      have h := actual_developedDeck_mul k⁻¹ k (actualMarkedStrip x)
      rw [inv_mul_cancel,actual_developedDeck_one] at h
      rw [←hxy]
      exact h.symm
    rcases actual_strip_point_in_facing_or_boundary x with hxf | hxs | hxt
    · rcases actual_strip_point_in_facing_or_boundary y with hyf | hys | hyt
      · exact Set.disjoint_left.mp (actual_index_one_has_arbitrary_deck_facing_separation hindex k hk)
          ⟨actualMarkedStrip x,hxf,hxy⟩ hyf
      · exact Set.disjoint_left.mp hBDinv.1 ⟨actualMarkedStrip y,hys,hinv⟩ hxf
      · exact Set.disjoint_left.mp hBDinv.2 ⟨actualMarkedStrip y,hyt,hinv⟩ hxf
    · rcases actual_strip_point_in_facing_or_boundary y with hyf | hys | hyt
      · exact Set.disjoint_left.mp hBD.1 ⟨actualMarkedStrip x,hxs,hxy⟩ hyf
      · exact Set.disjoint_left.mp hSS ⟨actualMarkedStrip x,hxs,hxy⟩ hys
      · exact Set.disjoint_left.mp hST ⟨actualMarkedStrip x,hxs,hxy⟩ hyt
    · rcases actual_strip_point_in_facing_or_boundary y with hyf | hys | hyt
      · exact Set.disjoint_left.mp hBD.2 ⟨actualMarkedStrip x,hxt,hxy⟩ hyf
      · exact Set.disjoint_left.mp hTS ⟨actualMarkedStrip x,hxt,hxy⟩ hys
      · exact Set.disjoint_left.mp hTT ⟨actualMarkedStrip x,hxt,hxy⟩ hyt

  have descent {Y : Type} [TopologicalSpace Y] (f : C(ℝ × unitInterval,Y))
      (hperiod : ∀ x : ℝ × unitInterval, f (x.1+1,x.2) = f x) :
      ∃ F : C(AddCircle (1:ℝ) × unitInterval,Y), ∀ x : ℝ × unitInterval,
        F ((x.1 : AddCircle (1:ℝ)),x.2) = f x := by
    have hp : Function.Periodic f.curry (1:ℝ) := by
      intro t
      apply ContinuousMap.ext
      intro u
      exact hperiod (t,u)
    let L : AddCircle (1:ℝ) → C(unitInterval,Y) := hp.lift
    have hL : Continuous L := by
      exact f.curry.continuous.quotient_lift _
    let F : C(AddCircle (1:ℝ) × unitInterval,Y) := ContinuousMap.uncurry ⟨L,hL⟩
    refine ⟨F,?_⟩
    intro x
    change hp.lift (x.1 : AddCircle (1:ℝ)) x.2 = f x
    rw [hp.lift_coe]
    rfl
  have actual_marked_strip_integer_monodromy (n : ℤ) (t : ℝ) (u : Interval) :
      actualMarkedStrip (t+(n:ℝ),u)=developedDeck (monodromy^n) (actualMarkedStrip (t,u)) := by
    let f : ℝ → H2 := fun s => actualMarkedStrip (s/(2*Real.pi),u)
    have hp (s : ℝ) : f (s+2*Real.pi)=developedDeck monodromy (f s) := by
      change actualMarkedStrip ((s+2*Real.pi)/(2*Real.pi),u) = _
      rw [show (s+2*Real.pi)/(2*Real.pi)=s/(2*Real.pi)+1 by field_simp <;> ring]
      exact actual_marked_strip_monodromy (s/(2*Real.pi),u)
    have h := actual_common_monodromy_integer_period f hp n (t*(2*Real.pi))
    have ha : (t*(2*Real.pi)+(n:ℝ)*(2*Real.pi))/(2*Real.pi)=t+(n:ℝ) := by field_simp <;> ring
    have hb : (t*(2*Real.pi))/(2*Real.pi)=t := mul_div_cancel_right₀ t (by positivity)
    simpa only [f,ha,hb] using h
  have actual_index_one_embedded_annulus (hindex : originalAxisNatIndex=1) :
      ∃ F : C(AddCircle (1:ℝ) × Interval,E), Topology.IsClosedEmbedding F ∧
        (∀ t : ℝ, F ((t:AddCircle (1:ℝ)),0)=a.map (Circle.exp (sourceParameter+t*(2*Real.pi)))) ∧
        (∀ t : ℝ, F ((t:AddCircle (1:ℝ)),1)=b.map (Circle.exp (targetParameter+t*(2*Real.pi)))) := by
    let projectedStrip : C(ℝ × Interval,E) :=
      ⟨developedProjection ∘ actualMarkedStrip,
        developedProjection_continuous.comp actual_marked_strip_continuous⟩
    have hp (x : ℝ × Interval) : projectedStrip (x.1+1,x.2)=projectedStrip x := by
      change developedProjection (actualMarkedStrip (x.1+1,x.2)) = _
      rw [actual_marked_strip_monodromy,developedDeck_projection]
      rfl
    obtain ⟨F,hclock⟩ := descent projectedStrip hp
    have hF : Function.Injective F := by
      rintro ⟨x,u⟩ ⟨y,v⟩ he
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective y
      subst x
      subst y
      rw [hclock (t,u),hclock (s,v)] at he
      have hproj : (development.symm (actualMarkedStrip (t,u))).1 =
          (development.symm (actualMarkedStrip (s,v))).1 := Subtype.ext he
      obtain ⟨k,hk⟩ := hqc.apply_eq_iff_mem_orbit.mp hproj
      change k • development.symm (actualMarkedStrip (s,v)) =
        development.symm (actualMarkedStrip (t,u)) at hk
      have heDeck : developedDeck k (actualMarkedStrip (s,v)) = actualMarkedStrip (t,u) := by
        change development (k • development.symm (actualMarkedStrip (s,v))) = _
        rw [hk,development.apply_symm_apply]
      have hcyclic : ∃ n : ℤ, k=monodromy^n := by
        by_contra h
        have hkout : ∀ n : ℤ, k≠monodromy^n := by simpa using h
        exact Set.disjoint_left.mp (actual_index_one_full_deck_strip_separation hindex k hkout)
          ⟨actualMarkedStrip (s,v),Set.mem_range_self _,heDeck⟩ (Set.mem_range_self _)
      obtain ⟨n,rfl⟩ := hcyclic
      rw [←actual_marked_strip_integer_monodromy] at heDeck
      have hePair := actual_marked_strip_injective heDeck
      have heFirst : s+(n:ℝ)=t := congrArg Prod.fst hePair
      have heSecond : v=u := congrArg Prod.snd hePair
      apply Prod.ext
      · rw [←heFirst,AddCircle.coe_add]
        have hn : ((n:ℝ):AddCircle (1:ℝ))=0 := by
          have h := AddCircle.coe_zsmul (p:=(1:ℝ)) (n:=n) (x:=(1:ℝ))
          simpa only [zsmul_eq_mul,mul_one,AddCircle.coe_period,smul_zero] using h
        rw [hn,add_zero]
      · exact heSecond.symm
    refine ⟨F,F.continuous.isClosedEmbedding hF,?_,?_⟩
    · intro t
      rw [hclock (t,0)]
      change developedProjection (actualMarkedStrip (t,0)) = _
      rw [actual_marked_strip_bottom,sourceLift_projection]
    · intro t
      rw [hclock (t,1)]
      change developedProjection (actualMarkedStrip (t,1)) = _
      rw [actual_marked_strip_top,targetLift_projection]

  have actualFullCollarsExtendGivenAnnulus {E : Type} [TopologicalSpace E] [T2Space E] [ChartedSpace Plane E]
    (f : C(Circle × Interval,E)) (hf : Topology.IsEmbedding f)
    (e0 e1 : C(Set.Ioo (-1:ℝ) 1 × Circle,E))
    (he0 : Topology.IsOpenEmbedding e0) (he1 : Topology.IsOpenEmbedding e1)
    (hc0 : ∀ z, e0 (⟨0,by norm_num⟩,z)=f (z,0))
    (hc1 : ∀ z, e1 (⟨0,by norm_num⟩,z)=f (z,1))
    (hdis : Disjoint (Set.range e0) (Set.range e1)) :
    ∃ B : C(Circle × Interval,E), Topology.IsEmbedding B ∧
      (∀ z (u : Interval), B (z,⟨((u:ℝ)+1)/3,by
        constructor <;> linarith [u.property.1,u.property.2]⟩)=f (z,u)) := by
  
    have annulusFrontier {E : Type} [TopologicalSpace E] [T2Space E] [ChartedSpace Plane E]
      (f : C(Circle × Interval,E)) (hf : Topology.IsEmbedding f) :
      Set.range (fun z : Circle => f (z,0)) ∪ Set.range (fun z : Circle => f (z,1)) =
        frontier (Set.range f) := by
    
      let circle : Circle ≃ₜ sphere (0:Plane) 1 := ClassificationJordanCurve.Arcs.circleHomeoSphere
      have hcnorm (z : Circle) : ‖(circle z:Plane)‖=1 := mem_sphere_zero_iff_norm.mp (circle z).property
      let j : C(Circle × Interval,Plane) :=
        ⟨fun p => (1+(p.2:ℝ)) • (circle p.1:Plane),
          (continuous_const.add (continuous_subtype_val.comp continuous_snd)).smul
            (continuous_subtype_val.comp (circle.continuous.comp continuous_fst))⟩
      have hjnorm (p : Circle × Interval) : ‖j p‖=1+(p.2:ℝ) := by
        change ‖(1+(p.2:ℝ)) • (circle p.1:Plane)‖=_
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith [p.2.property.1]),hcnorm,mul_one]
      have hji : Function.Injective j := by
        rintro ⟨z,u⟩ ⟨w,v⟩ he
        have hn := congrArg norm he
        rw [hjnorm,hjnorm] at hn
        have hu : u=v := Subtype.ext (by linarith)
        subst v
        have hz : z=w := by
          apply circle.injective
          apply Subtype.ext
          exact (smul_right_injective Plane (by linarith [u.property.1] : (1+(u:ℝ))≠0)) he
        exact congrArg (fun c : Circle => (c,u)) hz
      let K : Set Plane := closedBall 0 2 ∩ (ball 0 1)ᶜ
      have hKmem (x : Plane) : x∈K ↔ 1≤‖x‖ ∧ ‖x‖≤2 := by
        simp only [K,mem_inter_iff,mem_closedBall,mem_compl_iff,mem_ball,dist_zero_right,not_lt]
        tauto
      have hjrange : Set.range j=K := by
        apply Set.Subset.antisymm
        · rintro _ ⟨p,rfl⟩
          rw [hKmem,hjnorm]
          constructor <;> linarith [p.2.property.1,p.2.property.2]
        · intro x hx
          have hx' := (hKmem x).mp hx
          have hnpos : 0<‖x‖ := by linarith
          let c : sphere (0:Plane) 1 := ⟨(‖x‖⁻¹:ℝ) • x,by
            rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnpos),inv_mul_cancel₀ hnpos.ne']⟩
          let u : Interval := ⟨‖x‖-1,by constructor <;> linarith⟩
          refine ⟨(circle.symm c,u),?_⟩
          change (1+(‖x‖-1)) • (circle (circle.symm c):Plane)=x
          rw [circle.apply_symm_apply]
          change (1+(‖x‖-1)) • ((‖x‖⁻¹:ℝ) • x)=x
          rw [show 1+(‖x‖-1)=‖x‖ by ring,smul_smul,mul_inv_cancel₀ hnpos.ne',one_smul]
      have hKclosed : IsClosed K := isClosed_closedBall.inter isOpen_ball.isClosed_compl
      have hKcompact : IsCompact K := (isCompact_closedBall (0:Plane) 2).inter_right isOpen_ball.isClosed_compl
      have hKint : interior K = ball 0 2 ∩ (closedBall 0 1)ᶜ := by
        dsimp only [K]
        rw [interior_inter,interior_closedBall _ (by norm_num),interior_compl,closure_ball _ (by norm_num)]
      have hKfront (x : Plane) (hx : x∈K) : x∈frontier K ↔ ‖x‖=1 ∨ ‖x‖=2 := by
        rw [hKclosed.frontier_eq]
        have hx' := (hKmem x).mp hx
        simp only [mem_diff,mem_inter_iff,hKint,mem_ball,mem_compl_iff,mem_closedBall,dist_zero_right] 
        constructor
        · rintro ⟨_,h⟩
          by_cases h1 : ‖x‖=1
          · exact Or.inl h1
          · right
            by_contra h2
            exact h ⟨lt_of_le_of_ne hx'.2 h2,not_le.mpr (lt_of_le_of_ne hx'.1 (Ne.symm h1))⟩
        · rintro (h1 | h2)
          · exact ⟨hx,fun h => h.2 (by rw [h1])⟩
          · exact ⟨hx,fun h => (lt_irrefl (2:ℝ)) (h2 ▸ h.1)⟩
      let toK : Circle × Interval ≃ₜ K :=
        (j.continuous.isClosedEmbedding hji).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hjrange)
      have htoK (p : Circle × Interval) : (toK p:Plane)=j p := rfl
      let g : C(K,E) := ⟨f ∘ toK.symm,f.continuous.comp toK.symm.continuous⟩
      have hg : Topology.IsEmbedding g := hf.comp toK.symm.isEmbedding
      have hgrange : Set.range g=Set.range f := by
        change Set.range (f ∘ toK.symm)=_
        rw [Set.range_comp,Set.range_eq_univ.mpr toK.symm.surjective,Set.image_univ]
      have hfront := embedded_compact_planar_region_frontier_probe K hKcompact g hg
      rw [hgrange] at hfront
      rw [←hfront]
      ext y
      constructor
      · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
        · refine ⟨toK (z,0),?_,?_⟩
          · change (toK (z,0):Plane)∈frontier K
            rw [hKfront _ (toK (z,0)).property,htoK,hjnorm]
            exact Or.inl (by norm_num)
          · change f (toK.symm (toK (z,0)))=f (z,0)
            rw [toK.symm_apply_apply]
        · refine ⟨toK (z,1),?_,?_⟩
          · change (toK (z,1):Plane)∈frontier K
            rw [hKfront _ (toK (z,1)).property,htoK,hjnorm]
            exact Or.inr (by norm_num)
          · change f (toK.symm (toK (z,1)))=f (z,1)
            rw [toK.symm_apply_apply]
      · rintro ⟨x,hx,rfl⟩
        let p := toK.symm x
        have he : j p=(x:Plane) := (htoK p).symm.trans (congrArg Subtype.val (toK.apply_symm_apply x))
        have hn := (hKfront (x:Plane) x.property).mp hx
        rw [←he,hjnorm] at hn
        rcases hn with h0 | h1
        · left
          have hp0 : p.2=0 := Subtype.ext (by change (p.2:ℝ)=0;linarith)
          refine ⟨p.1,?_⟩
          change f (p.1,0)=f p
          rw [←hp0]
        · right
          have hp1 : p.2=1 := Subtype.ext (by change (p.2:ℝ)=1;linarith)
          refine ⟨p.1,?_⟩
          change f (p.1,1)=f p
          rw [←hp1]
    have collarSide {E : Type} [TopologicalSpace E] [T2Space E]
      [ChartedSpace Schoenflies.Plane E] (U : Set E)
      (T : Circle × Interval ≃ₜ U)
      (hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
        Set.range (fun z : Circle => (T (z,1)).val) = frontier U)
      (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
      (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) = (T (z,0)).val)
      (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
      (hclear : Disjoint (e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε})
        (Set.range (fun z : Circle => (T (z,1)).val))) :
      (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∈ interior U) ∧
        (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U) ∨
      (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∧
        (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∈ interior U) := by
    
      letI : CompactSpace U := T.compactSpace
      have hclosed : IsClosed U := by
        have hh := (isCompact_univ : IsCompact (Set.univ : Set U)).image
          (continuous_subtype_val : Continuous (Subtype.val : U → E))
        have hr : (Subtype.val : U → E) '' Set.univ = U := by
          rw [Set.image_univ,Subtype.range_coe_subtype]
          rfl
        exact (hr ▸ hh).isClosed
      have actual_embedded_annulus_interior_isOpen
          (B : Circle × Interval → E) (hB : IsEmbedding B) :
          IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
        rw [isOpen_iff_forall_mem_open]
        rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
        have hu0 : (0:ℝ) < (u : ℝ) := hu.1
        have hu1 : (u : ℝ) < 1 := hu.2
        let lo : ℝ := (u : ℝ)/2
        let hi : ℝ := ((u : ℝ)+1)/2
        have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
        have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
        have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
        have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
        have hlh : lo ≤ hi := (hlu.trans huh).le
        let width : ℝ → Interval := fun s =>
          ⟨(Set.projIcc lo hi hlh s : ℝ),
            ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
              le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
        have hwc : Continuous width :=
          (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
        let θ := Complex.arg (z : ℂ)
        let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
        have hfc : Continuous f := hB.continuous.comp
          ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
        let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
          {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
        have hΩ : IsOpen Ω :=
          (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
        have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
            (width (x 0) : ℝ) = x 0 :=
          congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
        have hfi : Set.InjOn f Ω := by
          intro x hx w hw he
          have hp := hB.injective he
          have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
            (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
            ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
          have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
          change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
          rw [hclip x hx,hclip w hw] at hwidth
          ext i
          fin_cases i
          · exact hwidth
          · exact hangle
        have hopen : IsOpen (f '' Ω) :=
          CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
        have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
          rintro q ⟨x,hx,rfl⟩
          refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
          · change 0 < (width (x 0) : ℝ)
            rw [hclip x hx]
            exact hl0.trans hx.1.1
          · change (width (x 0) : ℝ) < 1
            rw [hclip x hx]
            exact hx.1.2.trans hh1
        let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
        have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
        have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
        have hx : x ∈ Ω := by
          refine ⟨?_,?_⟩
          · rw [hx0]; exact ⟨hlu,huh⟩
          · rw [hx1]; constructor <;> linarith [Real.pi_pos]
        have hwu : width (u : ℝ) = u := by
          apply Subtype.ext
          change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
          exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
        have hpoint : f x = B (z,u) := by
          dsimp [f]
          rw [hx0,hx1,hwu,Circle.exp_arg]
        exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
      let f : Circle × Interval → E := fun p => (T p).val
      have hfe : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
      let annulusInterior := f '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
      have hIo : IsOpen annulusInterior := actual_embedded_annulus_interior_isOpen f hfe
      have hIU : annulusInterior ⊆ U := by rintro x ⟨p,hp,rfl⟩; exact (T p).property
      have hIint : annulusInterior ⊆ interior U := hIo.subset_interior_iff.mpr hIU
      have hdense : U ⊆ closure (interior U) := by
        intro x hx
        let p := T.symm ⟨x,hx⟩
        have hp : p ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1) := by
          rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ 1 by norm_num)]
          exact ⟨Set.mem_univ _,p.2.property.1,p.2.property.2⟩
        have him : f p ∈ closure annulusInterior := image_closure_subset_closure_image hfe.continuous ⟨p,hp,rfl⟩
        have heq : f p = x := congrArg Subtype.val (T.apply_symm_apply ⟨x,hx⟩)
        rw [heq] at him
        exact closure_mono hIint him
      let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
      let wp : Set.Ioo (-1:ℝ) 1 := ⟨ε,by constructor <;> linarith⟩
      let wn : Set.Ioo (-1:ℝ) 1 := ⟨-ε,by constructor <;> linarith⟩
      let P := e '' (Set.Ioo w0 wp ×ˢ (Set.univ : Set Circle))
      let Q := e '' (Set.Ioo wn w0 ×ˢ (Set.univ : Set Circle))
      let O := e '' (Set.Ioo wn wp ×ˢ (Set.univ : Set Circle))
      have h0p : w0 < wp := hε
      have hn0 : wn < w0 := by change -ε < 0; linarith
      have hInterval (a b : Set.Ioo (-1:ℝ) 1) (hab : a < b) : IsConnected (Set.Ioo a b) := by
        letI : ConnectedSpace (Set.Ioo (a:ℝ) (b:ℝ)) := Subtype.connectedSpace (isConnected_Ioo (show (a:ℝ) < (b:ℝ) from hab))
        let inc : Set.Ioo (a:ℝ) (b:ℝ) → Set.Ioo (-1:ℝ) 1 := fun x =>
          ⟨x.val,⟨a.property.1.trans x.property.1,x.property.2.trans b.property.2⟩⟩
        have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
        have hr : Set.range inc = Set.Ioo a b := by
          ext x
          constructor
          · rintro ⟨y,rfl⟩
            exact y.property
          · intro hx
            exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
        rw [← hr]
        exact isConnected_range hinc
      have hP : IsPreconnected P :=
        ((hInterval w0 wp h0p).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
      have hQ : IsPreconnected Q :=
        ((hInterval wn w0 hn0).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
      have hO : IsOpen O := he.isOpenMap _ (isOpen_Ioo.prod isOpen_univ)
      have hOcenter (z : Circle) : e (w0,z) ∈ O :=
        ⟨(w0,z),⟨⟨hn0,h0p⟩,Set.mem_univ _⟩,rfl⟩
      have hAvoid (w : Set.Ioo (-1:ℝ) 1) (hw : |(w:ℝ)| < ε)
          (hn : (w:ℝ) ≠ 0) (z : Circle) : e (w,z) ∉ frontier U := by
        intro hx
        rw [← hfront] at hx
        rcases hx with ⟨v,hv⟩ | hx
        · have hh : e (w,z) = e (w0,v) := by rw [hcenter]; exact hv.symm
          have heq := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ))
            (he.injective hh)
          exact hn heq
        · exact Set.disjoint_left.mp hclear ⟨(w,z),hw,rfl⟩ hx
      have hPavoid : P ⊆ (frontier U)ᶜ := by
        rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
        have hw0 : 0 < (w:ℝ) := hw.1
        have hwε : (w:ℝ) < ε := hw.2
        exact hAvoid w (by rw [abs_of_pos hw0]; exact hwε) hw0.ne' z
      have hQavoid : Q ⊆ (frontier U)ᶜ := by
        rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
        have hw0 : (w:ℝ) < 0 := hw.2
        have hwε : -ε < (w:ℝ) := hw.1
        exact hAvoid w (by rw [abs_of_neg hw0]; linarith) hw0.ne z
      have hsub (D : Set E) (hD : D ⊆ (frontier U)ᶜ) : D ⊆ interior U ∪ Uᶜ := by
        intro x hx
        by_cases hxu : x ∈ U
        · apply Or.inl
          by_contra hn
          exact hD hx ((mem_frontier_iff_notMem_interior hxu).mpr hn)
        · exact Or.inr hxu
      have hid : Disjoint (interior U) Uᶜ := Set.disjoint_left.mpr
        (fun x hx hn => hn (interior_subset hx))
      have hPd : P ⊆ interior U ∨ P ⊆ Uᶜ :=
        IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub P hPavoid) hP
      have hQd : Q ⊆ interior U ∨ Q ⊆ Uᶜ :=
        IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub Q hQavoid) hQ
      have hcenterFront (z : Circle) : e (w0,z) ∈ frontier U := by
        rw [hcenter,← hfront]
        exact Or.inl (Set.mem_range_self z)
      have hsplit (x : E) (hx : x ∈ O) : x ∈ P ∨ x ∈ Q ∨ ∃ z, x = e (w0,z) := by
        obtain ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩ := hx
        rcases lt_trichotomy w w0 with hh | hh | hh
        · exact Or.inr (Or.inl ⟨(w,z),⟨⟨hw.1,hh⟩,Set.mem_univ _⟩,rfl⟩)
        · exact Or.inr (Or.inr ⟨z,by rw [hh]⟩)
        · exact Or.inl ⟨(w,z),⟨⟨hh,hw.2⟩,Set.mem_univ _⟩,rfl⟩
      have hnotbothin : ¬ (P ⊆ interior U ∧ Q ⊆ interior U) := by
        rintro ⟨hp,hq⟩
        have hOU : O ⊆ U := by
          intro x hx
          rcases hsplit x hx with hx | hx | ⟨z,rfl⟩
          · exact interior_subset (hp hx)
          · exact interior_subset (hq hx)
          · rw [hcenter]
            exact (T (z,0)).property
        have hint : e (w0,1) ∈ interior U := hO.subset_interior_iff.mpr hOU (hOcenter 1)
        exact Set.disjoint_left.mp disjoint_interior_frontier hint (hcenterFront 1)
      have hnotbothout : ¬ (P ⊆ Uᶜ ∧ Q ⊆ Uᶜ) := by
        rintro ⟨hp,hq⟩
        have hcU : e (w0,1) ∈ U := by rw [hcenter]; exact (T (1,0)).property
        have hccl := hdense hcU
        obtain ⟨x,hxO,hxi⟩ := mem_closure_iff.mp hccl O hO (hOcenter 1)
        rcases hsplit x hxO with hx | hx | ⟨z,rfl⟩
        · exact hp hx (interior_subset hxi)
        · exact hq hx (interior_subset hxi)
        · exact Set.disjoint_left.mp disjoint_interior_frontier hxi (hcenterFront z)
      have hPmem (w : Set.Ioo (-1:ℝ) 1) (h0 : 0 < (w:ℝ)) (h1 : (w:ℝ) < ε) (z : Circle) :
          e (w,z) ∈ P := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
      have hQmem (w : Set.Ioo (-1:ℝ) 1) (h0 : -ε < (w:ℝ)) (h1 : (w:ℝ) < 0) (z : Circle) :
          e (w,z) ∈ Q := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
      rcases hPd with hp | hp <;> rcases hQd with hq | hq
      · exact False.elim (hnotbothin ⟨hp,hq⟩)
      · exact Or.inl ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
      · exact Or.inr ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
      · exact False.elim (hnotbothout ⟨hp,hq⟩)
    have exteriorHalf {E : Type} [TopologicalSpace E] [T2Space E]
      [ChartedSpace Schoenflies.Plane E] (U : Set E)
      (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
      (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
      (hchoice : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∨
        (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U)) :
      ∃ L : C(Circle × Interval,E), Topology.IsEmbedding L ∧
        (∀ z, L (z,0) = e (⟨0,by norm_num⟩,z)) ∧
        (∀ (z : Circle) (u : Interval), 0 < (u:ℝ) → L (z,u) ∉ U) ∧
        Set.range L ⊆ e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε} := by
    
      obtain ⟨sign,hσ,hout⟩ : ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
          ∀ w : Set.Ioo (-1:ℝ) 1, 0 < sign*(w:ℝ) → sign*(w:ℝ) < ε → ∀ z, e (w,z) ∉ U := by
        rcases hchoice with hp | hn
        · exact ⟨1,Or.inl rfl,fun w h0 h1 z => hp w (by simpa using h0) (by simpa using h1) z⟩
        · refine ⟨-1,Or.inr rfl,?_⟩
          intro w h0 h1 z
          exact hn w (by linarith) (by linarith) z
      let q : Interval → Set.Ioo (-1:ℝ) 1 := fun u =>
        ⟨sign*ε/2*(u:ℝ),by rcases hσ with hs | hs <;> rw [hs] <;>
          constructor <;> nlinarith [u.property.1,u.property.2]⟩
      have hqc : Continuous q := by dsimp [q]; fun_prop
      have hqi : Function.Injective q := by
        intro u v h
        apply Subtype.ext
        have hh := congrArg Subtype.val h
        change sign*ε/2*(u:ℝ) = sign*ε/2*(v:ℝ) at hh
        rcases hσ with hs | hs <;> rw [hs] at hh <;> nlinarith
      have hq0 : q 0 = ⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [q]; ring
      have hqabs (u : Interval) : |(q u:ℝ)| < ε := by
        rw [abs_lt]
        dsimp [q]
        rcases hσ with hs | hs <;> rw [hs] <;> constructor <;>
          nlinarith [u.property.1,u.property.2]
      let L : C(Circle × Interval,E) := ⟨fun p => e (q p.2,p.1),
        e.continuous.comp ((hqc.comp continuous_snd).prodMk continuous_fst)⟩
      have hLi : Function.Injective L := by
        intro p w h
        have hh := he.injective h
        apply Prod.ext
        · have hz := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => p.2) hh
          exact hz
        · exact hqi (congrArg Prod.fst hh)
      refine ⟨L,(L.continuous.isClosedEmbedding hLi).isEmbedding,?_,?_,?_⟩
      · intro z
        change e (q 0,z) = _
        rw [hq0]
      · intro z u hu
        apply hout (q u)
        · dsimp [q]
          rcases hσ with hs | hs <;> rw [hs] <;> nlinarith
        · dsimp [q]
          rcases hσ with hs | hs <;> rw [hs] <;> nlinarith [u.property.2]
      · rintro x ⟨p,rfl⟩
        exact ⟨(q p.2,p.1),hqabs p.2,rfl⟩
    have glueExterior {E : Type} [TopologicalSpace E] [T2Space E]
      [ChartedSpace Schoenflies.Plane E] (U : Set E)
      (T : Circle × Interval ≃ₜ U)
      (L R : C(Circle × Interval,E)) (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
      (hLzero : ∀ z, L (z,0) = (T (z,0)).val)
      (hRzero : ∀ z, R (z,0) = (T (z,1)).val)
      (hLoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∉ U)
      (hRoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → R (z,t) ∉ U)
      (hLR : Disjoint (Set.range L) (Set.range R)) :
      ∃ g : C(Circle × Set.Icc (-1:ℝ) 2,E), Topology.IsEmbedding g ∧
        (∀ z, g (z,⟨0,by norm_num⟩) = (T (z,0)).val) ∧
        (∀ z, g (z,⟨1,by norm_num⟩) = (T (z,1)).val) ∧
        ∀ p : Circle × Set.Icc (-1:ℝ) 2,
          ∀ hp0 : 0 ≤ (p.2:ℝ), ∀ hp1 : (p.2:ℝ) ≤ 1,
            g p = (T (p.1,⟨p.2.val,hp0,hp1⟩)).val := by
    
      let q : C(Circle × Interval,E) := ⟨fun p => (T p).val,continuous_subtype_val.comp T.continuous⟩
      have hq : Topology.IsEmbedding q := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
      have hLq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
          (he : L (z,t) = q (w,v)) : t = 0 ∧ v = 0 ∧ z = w := by
        by_cases ht : t = 0
        · rw [ht,hLzero] at he
          have hh := T.injective (Subtype.ext he)
          have hv := congrArg (fun p : Circle × Interval => p.2) hh
          have hz := congrArg (fun p : Circle × Interval => p.1) hh
          exact ⟨ht,hv.symm,hz⟩
        · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
          exact False.elim (hLoutside z t htp (he.symm ▸ (T (w,v)).property))
      have hRq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
          (he : R (z,t) = q (w,v)) : t = 0 ∧ v = 1 ∧ z = w := by
        by_cases ht : t = 0
        · rw [ht,hRzero] at he
          have hh := T.injective (Subtype.ext he)
          have hv := congrArg (fun p : Circle × Interval => p.2) hh
          have hz := congrArg (fun p : Circle × Interval => p.1) hh
          exact ⟨ht,hv.symm,hz⟩
        · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
          exact False.elim (hRoutside z t htp (he.symm ▸ (T (w,v)).property))
      let X := Set.Icc (-1 : ℝ) 2
      let τL : X → Interval := fun r => projIcc 0 1 zero_le_one (-(r:ℝ))
      let τQ : X → Interval := fun r => projIcc 0 1 zero_le_one (r:ℝ)
      let τR : X → Interval := fun r => projIcc 0 1 zero_le_one (((r:ℝ)-1))
      have hτL (r : X) (hr : (r:ℝ) ≤ 0) : (τL r:ℝ) = -(r:ℝ) := by
        dsimp only [τL]
        rw [projIcc_of_mem zero_le_one (show -(r:ℝ) ∈ Icc (0:ℝ) 1 by
          constructor <;> linarith [r.property.1])]
      have hτQ (r : X) (hr0 : 0 ≤ (r:ℝ)) (hr1 : (r:ℝ) ≤ 1) : (τQ r:ℝ) = r := by
        dsimp only [τQ]; rw [projIcc_of_mem zero_le_one ⟨hr0,hr1⟩]
      have hτR (r : X) (hr : 1 ≤ (r:ℝ)) : (τR r:ℝ) = ((r:ℝ)-1) := by
        dsimp only [τR]
        rw [projIcc_of_mem zero_le_one (show ((r:ℝ)-1) ∈ Icc (0:ℝ) 1 by
          constructor <;> linarith [r.property.2])]
      let ℓ : Circle × X → E := fun p => L (p.1,τL p.2)
      let m : Circle × X → E := fun p => q (p.1,τQ p.2)
      let r : Circle × X → E := fun p => R (p.1,τR p.2)
      have hℓcont : Continuous ℓ := L.continuous.comp
        (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
      have hmcont : Continuous m := q.continuous.comp
        (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
      have hrcont : Continuous r := R.continuous.comp
        (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
      let k : Circle × X → E := fun p => if (p.2:ℝ) ≤ 1 then m p else r p
      have hkcont : Continuous k := by
        apply continuous_if_le (by fun_prop) continuous_const hmcont.continuousOn hrcont.continuousOn
        intro p hp
        have hq1 : τQ p.2 = 1 := Subtype.ext (by rw [hτQ p.2 (by linarith) hp.le]; exact hp)
        have hr0 : τR p.2 = 0 := Subtype.ext (by rw [hτR p.2 hp.ge]; simp [hp])
        dsimp only [m,r]
        rw [hq1,hr0,hRzero]
        rfl
      let G : Circle × X → E := fun p => if (p.2:ℝ) ≤ 0 then ℓ p else k p
      have hGcont : Continuous G := by
        apply continuous_if_le (by fun_prop) continuous_const hℓcont.continuousOn hkcont.continuousOn
        intro p hp
        have hL0 : τL p.2 = 0 := Subtype.ext (by rw [hτL p.2 hp.le]; simp [hp])
        have hq0 : τQ p.2 = 0 := Subtype.ext (by rw [hτQ p.2 hp.ge (by linarith)]; exact hp)
        dsimp only [ℓ,k]
        rw [ite_eq_left (show (p.2:ℝ) ≤ 1 by linarith)]
        dsimp only [m]
        rw [hL0,hq0,hLzero]
        rfl
      have hℓinj (p s : Circle × X) (hp : (p.2:ℝ) ≤ 0) (hs : (s.2:ℝ) ≤ 0)
          (he : ℓ p = ℓ s) : p = s := by
        have hh := hL.injective he
        have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
        apply Prod.ext hz
        apply Subtype.ext
        have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
        change (τL p.2:ℝ) = (τL s.2:ℝ) at hval
        rw [hτL p.2 hp,hτL s.2 hs] at hval
        linarith
      have hminj (p s : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1)
          (hs0 : 0 ≤ (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) (he : m p = m s) : p = s := by
        have hh := hq.injective he
        have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
        apply Prod.ext hz
        apply Subtype.ext
        have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
        change (τQ p.2:ℝ) = (τQ s.2:ℝ) at hval
        rwa [hτQ p.2 hp0 hp1,hτQ s.2 hs0 hs1] at hval
      have hrinj (p s : Circle × X) (hp : 1 ≤ (p.2:ℝ)) (hs : 1 ≤ (s.2:ℝ))
          (he : r p = r s) : p = s := by
        have hh := hR.injective he
        have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
        apply Prod.ext hz
        apply Subtype.ext
        have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
        change (τR p.2:ℝ) = (τR s.2:ℝ) at hval
        rw [hτR p.2 hp,hτR s.2 hs] at hval
        linarith
      have hℓm (p s : Circle × X) (hs0 : 0 < (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) : ℓ p ≠ m s := by
        intro he
        have hh := (hLq p.1 (τL p.2) s.1 (τQ s.2) he).2.1
        have hv := congrArg Subtype.val hh
        change (τQ s.2:ℝ) = 0 at hv
        rw [hτQ s.2 hs0.le hs1] at hv
        linarith
      have hmr (p s : Circle × X) (hs : 1 < (s.2:ℝ)) : m p ≠ r s := by
        intro he
        have hh := (hRq s.1 (τR s.2) p.1 (τQ p.2) he.symm).1
        have hv := congrArg Subtype.val hh
        change (τR s.2:ℝ) = 0 at hv
        rw [hτR s.2 hs.le] at hv
        linarith
      have hℓr (p s : Circle × X) : ℓ p ≠ r s := by
        intro he
        exact Set.disjoint_left.mp hLR (Set.mem_range_self (p.1,τL p.2))
          ⟨(s.1,τR s.2),he.symm⟩
      have hGinj : Function.Injective G := by
        intro p s he
        dsimp only [G,k] at he
        by_cases hp0 : (p.2:ℝ) ≤ 0
        · rw [ite_eq_left hp0] at he
          by_cases hs0 : (s.2:ℝ) ≤ 0
          · rw [ite_eq_left hs0] at he; exact hℓinj p s hp0 hs0 he
          · rw [ite_eq_right hs0] at he
            by_cases hs1 : (s.2:ℝ) ≤ 1
            · rw [ite_eq_left hs1] at he; exact False.elim (hℓm p s (by linarith) hs1 he)
            · rw [ite_eq_right hs1] at he; exact False.elim (hℓr p s he)
        · rw [ite_eq_right hp0] at he
          by_cases hp1 : (p.2:ℝ) ≤ 1
          · rw [ite_eq_left hp1] at he
            by_cases hs0 : (s.2:ℝ) ≤ 0
            · rw [ite_eq_left hs0] at he; exact False.elim (hℓm s p (by linarith) hp1 he.symm)
            · rw [ite_eq_right hs0] at he
              by_cases hs1 : (s.2:ℝ) ≤ 1
              · rw [ite_eq_left hs1] at he; exact hminj p s (by linarith) hp1 (by linarith) hs1 he
              · rw [ite_eq_right hs1] at he; exact False.elim (hmr p s (by linarith) he)
          · rw [ite_eq_right hp1] at he
            by_cases hs0 : (s.2:ℝ) ≤ 0
            · rw [ite_eq_left hs0] at he; exact False.elim (hℓr s p he.symm)
            · rw [ite_eq_right hs0] at he
              by_cases hs1 : (s.2:ℝ) ≤ 1
              · rw [ite_eq_left hs1] at he; exact False.elim (hmr s p (by linarith) he.symm)
              · rw [ite_eq_right hs1] at he; exact hrinj p s (by linarith) (by linarith) he
      let g : C(Circle × X,E) := ⟨G,hGcont⟩
      have hg : Topology.IsEmbedding g := (hGcont.isClosedEmbedding hGinj).isEmbedding
      have hg0 (z : Circle) : g (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0) := by
        change G (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0)
        simp only [G,le_refl,if_true,ℓ,τL,neg_zero,
          projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
        exact hLzero z
      have hg1 (z : Circle) : g (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1) := by
        change G (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1)
        simp only [G,show ¬(1:ℝ)≤0 by norm_num,if_false,k,le_refl,if_true,m,τQ,
          projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)]
        congr 1
      have hgmid (p : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1) :
          g p = q (p.1,⟨p.2.val,hp0,hp1⟩) := by
        by_cases hp : (p.2:ℝ) = 0
        · have he : p.2 = ⟨0,by dsimp [X]; norm_num⟩ := Subtype.ext hp
          calc
            g p = g (p.1,⟨0,by dsimp [X]; norm_num⟩) := congrArg g (Prod.ext rfl he)
            _ = q (p.1,0) := hg0 p.1
            _ = q (p.1,⟨p.2.val,hp0,hp1⟩) := congrArg q (Prod.ext rfl (Subtype.ext hp.symm))
        · change G p = _
          have hpp : 0 < (p.2:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hp)
          dsimp only [G,k]
          rw [ite_eq_right (not_le_of_gt hpp),ite_eq_left hp1]
          change q (p.1,τQ p.2) = _
          congr 1
          apply Prod.ext
          · rfl
          · apply Subtype.ext; exact hτQ p.2 hp0 hp1
      exact ⟨g,hg,hg0,hg1,hgmid⟩
    let U := Set.range f
    let T : Circle × Interval ≃ₜ U := hf.toHomeomorph
    have hT (p : Circle × Interval) : (T p).val=f p := rfl
    have hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
        Set.range (fun z : Circle => (T (z,1)).val)=frontier U := annulusFrontier f hf
    have hcenter0 (z : Circle) : e0 (⟨0,by norm_num⟩,z)=(T (z,0)).val := hc0 z
    have hclear0 : Disjoint (e0 '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)|<1/2})
        (Set.range (fun z : Circle => (T (z,1)).val)) := by
      apply hdis.mono (Set.image_subset_range _ _)
      rintro _ ⟨z,rfl⟩
      exact ⟨(⟨0,by norm_num⟩,z),(hc1 z)⟩
    have hs0 := collarSide U T hfront e0 he0 hcenter0 (1/2) (by norm_num) (by norm_num) hclear0
    have ho0 : (∀ w : Set.Ioo (-1:ℝ) 1, 0<(w:ℝ) → (w:ℝ)<1/2 → ∀ z, e0 (w,z)∉U) ∨
        (∀ w : Set.Ioo (-1:ℝ) 1, -(1/2)<(w:ℝ) → (w:ℝ)<0 → ∀ z, e0 (w,z)∉U) := by
      rcases hs0 with h | h
      · exact Or.inr h.2
      · exact Or.inl h.1
    obtain ⟨L,hL,hLzero,hLoutside,hLrange⟩ := exteriorHalf U e0 he0 (1/2) (by norm_num) (by norm_num) ho0
    let flip : Circle × Interval ≃ₜ Circle × Interval :=
      (Homeomorph.refl Circle).prodCongr unitInterval.symmHomeomorph
    let Tflip := flip.trans T
    have hflip0 (z : Circle) : (Tflip (z,0)).val=(T (z,1)).val := by simp [Tflip,flip]
    have hflip1 (z : Circle) : (Tflip (z,1)).val=(T (z,0)).val := by simp [Tflip,flip]
    have hfrontFlip : Set.range (fun z : Circle => (Tflip (z,0)).val) ∪
        Set.range (fun z : Circle => (Tflip (z,1)).val)=frontier U := by
      simp only [hflip0,hflip1,union_comm]
      exact hfront
    have hcenter1 (z : Circle) : e1 (⟨0,by norm_num⟩,z)=(Tflip (z,0)).val :=
      (hc1 z).trans (hflip0 z).symm
    have hclear1 : Disjoint (e1 '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)|<1/2})
        (Set.range (fun z : Circle => (Tflip (z,1)).val)) := by
      apply hdis.symm.mono (Set.image_subset_range _ _)
      rintro _ ⟨z,rfl⟩
      exact ⟨(⟨0,by norm_num⟩,z),(hc0 z).trans (hflip1 z).symm⟩
    have hs1 := collarSide U Tflip hfrontFlip e1 he1 hcenter1 (1/2) (by norm_num) (by norm_num) hclear1
    have ho1 : (∀ w : Set.Ioo (-1:ℝ) 1, 0<(w:ℝ) → (w:ℝ)<1/2 → ∀ z, e1 (w,z)∉U) ∨
        (∀ w : Set.Ioo (-1:ℝ) 1, -(1/2)<(w:ℝ) → (w:ℝ)<0 → ∀ z, e1 (w,z)∉U) := by
      rcases hs1 with h | h
      · exact Or.inr h.2
      · exact Or.inl h.1
    obtain ⟨R,hR,hRzero,hRoutside,hRrange⟩ := exteriorHalf U e1 he1 (1/2) (by norm_num) (by norm_num) ho1
    have hLz (z : Circle) : L (z,0)=(T (z,0)).val := (hLzero z).trans (hc0 z)
    have hRz (z : Circle) : R (z,0)=(T (z,1)).val := (hRzero z).trans (hc1 z)
    have hLR : Disjoint (Set.range L) (Set.range R) :=
      hdis.mono (hLrange.trans (Set.image_subset_range _ _))
        (hRrange.trans (Set.image_subset_range _ _))
    obtain ⟨g,hg,hg0,hg1,hgiven⟩ := glueExterior U T L R hL hR hLz hRz hLoutside hRoutside hLR
    let clock : Interval → Set.Icc (-1:ℝ) 2 := fun u =>
      ⟨3*(u:ℝ)-1,by constructor <;> linarith [u.property.1,u.property.2]⟩
    have hclock : Continuous clock := (continuous_const.mul continuous_subtype_val |>.sub continuous_const).subtype_mk _
    let B : C(Circle × Interval,E) :=
      ⟨fun p => g (p.1,clock p.2),g.continuous.comp
        (continuous_fst.prodMk (hclock.comp continuous_snd))⟩
    have hBi : Function.Injective B := by
      intro x y he
      have hh := hg.injective he
      have hz : x.1=y.1 := by
        simpa only using congrArg (Prod.fst : Circle × Set.Icc (-1:ℝ) 2 → Circle) hh
      have hu : x.2=y.2 := by
        apply Subtype.ext
        have h := congrArg (fun p : Circle × Set.Icc (-1:ℝ) 2 => (p.2:ℝ)) hh
        change 3*(x.2:ℝ)-1=3*(y.2:ℝ)-1 at h
        linarith
      exact Prod.ext hz hu
    refine ⟨B,(B.continuous.isClosedEmbedding hBi).isEmbedding,?_⟩
    intro z u
    let v : Interval := ⟨((u:ℝ)+1)/3,by constructor <;> linarith [u.property.1,u.property.2]⟩
    have ht : (clock v:ℝ)=(u:ℝ) := by dsimp [clock,v];ring
    change g (z,clock v)=f (z,u)
    have h := hgiven (z,clock v) (by rw [ht];exact u.property.1) (by rw [ht];exact u.property.2)
    have hu : (⟨(clock v:ℝ),by rw [ht];exact u.property.1,by rw [ht];exact u.property.2⟩:Interval)=u := Subtype.ext ht
    simpa only [hu,hT] using h
  have actual_index_one_source_curves_have_collared_annulus (hindex : originalAxisNatIndex=1) :
      ∃ B : C(Circle × Interval,E), Topology.IsEmbedding B ∧
        Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))=a.image ∧
        Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))=b.image := by
    obtain ⟨F,hF,hF0,hF1⟩ := actual_index_one_embedded_annulus hindex
    let circleClock : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
    let param : Circle × Interval ≃ₜ AddCircle (1:ℝ) × Interval :=
      circleClock.symm.prodCongr (Homeomorph.refl Interval)
    let f : C(Circle × Interval,E) := ⟨F ∘ param,F.continuous.comp param.continuous⟩
    have hf : Topology.IsEmbedding f := hF.isEmbedding.comp param.isEmbedding
    let r0 : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp sourceParameter)
    let r1 : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp targetParameter)
    have hf0 (z : Circle) : f (z,0)=a.map (r0 z) := by
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (circleClock.symm z)
      have hz : Circle.exp (t*(2*Real.pi))=z := by
        have h := congrArg circleClock ht
        simpa only [circleClock,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,
          div_one,mul_comm,circleClock.apply_symm_apply] using h
      change F (circleClock.symm z,0)=_
      rw [←ht,hF0,Circle.exp_add,hz]
      rfl
    have hf1 (z : Circle) : f (z,1)=b.map (r1 z) := by
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (circleClock.symm z)
      have hz : Circle.exp (t*(2*Real.pi))=z := by
        have h := congrArg circleClock ht
        simpa only [circleClock,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,
          div_one,mul_comm,circleClock.apply_symm_apply] using h
      change F (circleClock.symm z,1)=_
      rw [←ht,hF1,Circle.exp_add,hz]
      rfl
    let p0 : Set.Ioo (-1:ℝ) 1 × Circle ≃ₜ Set.Ioo (-1:ℝ) 1 × Circle :=
      (Homeomorph.refl _).prodCongr r0
    let p1 : Set.Ioo (-1:ℝ) 1 × Circle ≃ₜ Set.Ioo (-1:ℝ) 1 × Circle :=
      (Homeomorph.refl _).prodCongr r1
    let e0 : C(Set.Ioo (-1:ℝ) 1 × Circle,E) := ⟨d0 ∘ p0,d0.continuous.comp p0.continuous⟩
    let e1 : C(Set.Ioo (-1:ℝ) 1 × Circle,E) := ⟨d1 ∘ p1,d1.continuous.comp p1.continuous⟩
    have he0 : Topology.IsOpenEmbedding e0 := hd0.comp p0.isOpenEmbedding
    have he1 : Topology.IsOpenEmbedding e1 := hd1.comp p1.isOpenEmbedding
    have hc0 (z : Circle) : e0 (⟨0,by norm_num⟩,z)=f (z,0) := by
      change d0 (⟨0,by norm_num⟩,r0 z)=_
      rw [hzero0,hcenter0,hf0]
    have hc1 (z : Circle) : e1 (⟨0,by norm_num⟩,z)=f (z,1) := by
      change d1 (⟨0,by norm_num⟩,r1 z)=_
      rw [hzero1,hcenter1,hf1]
    have heDis : Disjoint (Set.range e0) (Set.range e1) := by
      apply (hNdis.mono hrange0 hrange1).mono
      · rintro _ ⟨x,rfl⟩;exact Set.mem_range_self (p0 x)
      · rintro _ ⟨x,rfl⟩;exact Set.mem_range_self (p1 x)
    obtain ⟨B,hB,hgiven⟩ := actualFullCollarsExtendGivenAnnulus f hf e0 e1 he0 he1 hc0 hc1 heDis
    have hrow0 (z : Circle) : B (z,⟨1/3,by norm_num⟩)=a.map (r0 z) := by
      have h := hgiven z 0
      simpa only [show ((0:Interval):ℝ)=0 from rfl,zero_add,hf0] using h
    have hrow1 (z : Circle) : B (z,⟨2/3,by norm_num⟩)=b.map (r1 z) := by
      have h := hgiven z 1
      simpa only [show ((1:Interval):ℝ)=1 from rfl,show (1:ℝ)+1=2 by norm_num,hf1] using h
    refine ⟨B,hB,?_,?_⟩
    · change Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))=Set.range a.map
      simp_rw [hrow0]
      change Set.range (a.map ∘ r0)=Set.range a.map
      rw [Set.range_comp,Set.range_eq_univ.mpr r0.surjective,Set.image_univ]
    · change Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))=Set.range b.map
      simp_rw [hrow1]
      change Set.range (b.map ∘ r1)=Set.range b.map
      rw [Set.range_comp,Set.range_eq_univ.mpr r1.surjective,Set.image_univ]
  have actual_embedded_annulus_interior_isOpen
      (B : Circle × Interval → E) (hB : IsEmbedding B) :
      IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
    have hu0 : (0:ℝ) < (u : ℝ) := hu.1
    have hu1 : (u : ℝ) < 1 := hu.2
    let lo : ℝ := (u : ℝ)/2
    let hi : ℝ := ((u : ℝ)+1)/2
    have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
    have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
    have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
    have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
    have hlh : lo ≤ hi := (hlu.trans huh).le
    let width : ℝ → Interval := fun s =>
      ⟨(Set.projIcc lo hi hlh s : ℝ),
        ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
          le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
    have hwc : Continuous width :=
      (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
    let θ := Complex.arg (z : ℂ)
    let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
    have hfc : Continuous f := hB.continuous.comp
      ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
    let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
    have hΩ : IsOpen Ω :=
      (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
    have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
        (width (x 0) : ℝ) = x 0 :=
      congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
    have hfi : Set.InjOn f Ω := by
      intro x hx w hw he
      have hp := hB.injective he
      have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
        (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
        ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
      have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
      change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
      rw [hclip x hx,hclip w hw] at hwidth
      ext i
      fin_cases i
      · exact hwidth
      · exact hangle
    have hopen : IsOpen (f '' Ω) :=
      CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
    have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
      rintro q ⟨x,hx,rfl⟩
      refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
      · change 0 < (width (x 0) : ℝ)
        rw [hclip x hx]
        exact hl0.trans hx.1.1
      · change (width (x 0) : ℝ) < 1
        rw [hclip x hx]
        exact hx.1.2.trans hh1
    let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
    have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
    have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
    have hx : x ∈ Ω := by
      refine ⟨?_,?_⟩
      · rw [hx0]; exact ⟨hlu,huh⟩
      · rw [hx1]; constructor <;> linarith [Real.pi_pos]
    have hwu : width (u : ℝ) = u := by
      apply Subtype.ext
      change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
      exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
    have hpoint : f x = B (z,u) := by
      dsimp [f]
      rw [hx0,hx1,hwu,Circle.exp_arg]
    exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩

  have actual_index_one_original_disjoint_curves_are_ambient_isotopic
      (hindex : originalAxisNatIndex=1) : AmbientIsotopy.Rel a.image b.image := by
    obtain ⟨B,hB,hBa,hBb⟩ := actual_index_one_source_curves_have_collared_annulus hindex
    obtain ⟨K,J,hfinal,hfix,hleft,hright⟩ :=
      CurveComplex.G3Review.actual_collared_annulus_ambient_alignment a b B hB hBa hBb
        (actual_embedded_annulus_interior_isOpen B hB)
    exact ⟨K,hfinal⟩

  have actual_index_two_minimal_axis_generator_is_glide
      (hindex : originalAxisNatIndex=2) :
      ∀ z : H2, (minimalAxisIsometry z).re = -Real.exp minimalAxisPeriod*z.re ∧
        (minimalAxisIsometry z).im = Real.exp minimalAxisPeriod*z.im := by
    rcases translatedAxisDilationOrGlide minimalAxisIsometry minimalAxisPeriod
      minimal_axis_isometry_period with hd | hg
    · have hOne : originalAxisNatIndex=1 := by
        apply actual_source_monodromy_has_no_proper_dilation_root minimalAxisDeck.val
          originalAxisNatIndex original_axis_nat_index_positive original_monodromy_minimal_axis_nat_root
          sourceAxisCoordinate minimalAxisPeriod minimalAxisPeriod_positive.ne'
        intro z
        have h := dilationCoordinate minimalAxisIsometry minimalAxisPeriod hd
          (axisNormalizingIsometry.symm z)
        change logarithmicCoordinate (axisNormalizingIsometry.symm (developedDeckIsometry minimalAxisDeck.val z)) =
          logarithmicCoordinate (axisNormalizingIsometry.symm z)+(minimalAxisPeriod,0)
        simpa only [minimalAxisIsometry,sourceAxisCoordinate,Homeomorph.trans_apply,
          IsometryEquiv.trans_apply,axisNormalizingIsometry.apply_symm_apply] using h
      omega
    · exact hg
  have actual_index_two_minimal_generator_not_common_cyclic
      (hindex : originalAxisNatIndex=2) :
      ∀ n : ℤ, minimalAxisDeck.val ≠ monodromy^n := by
    intro n hn
    have hSub : minimalAxisDeck = originalAxisDeck^n := by
      apply Subtype.ext
      simpa only [Subgroup.coe_zpow,originalAxisDeck] using hn
    have he := congrArg (fun k => axisPeriodHom (Additive.ofMul k)) hSub
    rw [minimalAxisDeck_period,ofMul_zpow,map_zsmul,original_axis_deck_period,zsmul_eq_mul] at he
    have hi := congrArg (fun k => axisPeriodHom (Additive.ofMul k)) originalAxisIndex_power
    rw [original_axis_deck_period,ofMul_zpow,map_zsmul,minimalAxisDeck_period,zsmul_eq_mul] at hi
    have hInt : originalAxisIndex=2 := by rw [←original_axis_nat_index_cast,hindex];rfl
    rw [hInt] at hi
    have hnReal : (1:ℝ)=(n:ℝ)*2 := by
      apply mul_right_cancel₀ minimalAxisPeriod_positive.ne'
      calc
        (1:ℝ)*minimalAxisPeriod = (n:ℝ)*axisPeriod := by simpa using he
        _ = ((n:ℝ)*2)*minimalAxisPeriod := by rw [hi];ring
    have hnInt : (1:ℤ)=n*2 := by exact_mod_cast hnReal
    omega
  have actual_index_two_original_monodromy_is_glide_square
      (hindex : originalAxisNatIndex=2) : monodromy=minimalAxisDeck.val^2 := by
    rw [original_monodromy_minimal_axis_nat_root,hindex]
  let alternativeTargetLift : C(ℝ,H2) :=
    ⟨(developedDeck minimalAxisDeck.val) ∘ targetLift,
      (developedDeck minimalAxisDeck.val).continuous.comp targetLift.continuous⟩
  have actual_alternative_target_literal_projection (s : ℝ) :
      developedProjection (alternativeTargetLift s)=b.map (Circle.exp s) := by
    change developedProjection (developedDeck minimalAxisDeck.val (targetLift s)) = _
    rw [developedDeck_projection,targetLift_projection]
  have actual_alternative_target_closed_embedding : Topology.IsClosedEmbedding alternativeTargetLift :=
    (developedDeck minimalAxisDeck.val).isClosedEmbedding.comp actual_targetLift_closed_embedding
  have actual_alternative_target_common_monodromy (hindex : originalAxisNatIndex=2) (s : ℝ) :
      alternativeTargetLift (s+2*Real.pi)=developedDeck monodromy (alternativeTargetLift s) := by
    change developedDeck minimalAxisDeck.val (targetLift (s+2*Real.pi)) =
      developedDeck monodromy (developedDeck minimalAxisDeck.val (targetLift s))
    rw [targetLift_period,←actual_developedDeck_mul,←actual_developedDeck_mul]
    congr 2
    rw [actual_index_two_original_monodromy_is_glide_square hindex]
    exact (Commute.refl minimalAxisDeck.val).pow_right 2 |>.eq
  have actual_index_two_source_target_alternative_pair_disjoint (hindex : originalAxisNatIndex=2) :
      Disjoint (Set.range sourceLift) (Set.range alternativeTargetLift) := by
    have h := all_developed_source_target_translates_disjoint 1 minimalAxisDeck.val
    simpa only [actual_developedDeck_one,Set.image_id',alternativeTargetLift,
      ContinuousMap.coe_mk,Set.range_comp] using h
  have actual_index_two_target_alternative_disjoint (hindex : originalAxisNatIndex=2) :
      Disjoint (Set.range targetLift) (Set.range alternativeTargetLift) := by
    have h := (actual_noncyclic_source_and_target_translates_disjoint minimalAxisDeck.val
      (actual_index_two_minimal_generator_not_common_cyclic hindex)).2
    simpa only [alternativeTargetLift,ContinuousMap.coe_mk,Set.range_comp] using h.symm

  have horizontalBoundsAndEnds (F : C(ℝ,Plane)) (T L : ℝ) (hT : 0<T) (hL : 0<L)
    (hperiod : ∀ t, F (t+T)=F t+Plane.mk L 0) :
    ∃ B : ℝ, 0<B ∧ (∀ t, |F t 1|<B) ∧
      ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0 := by
  
    have hyperiod : Function.Periodic (fun t => F t 1) (T) := by
      intro t
      have h := congrArg (fun z : Plane => z 1) (hperiod t)
      simpa [Plane.mk] using h
    have hycompact : IsCompact (Set.range (fun t => F t 1)) := by
      rw [←hyperiod.image_Icc (by linarith : 0 < T) 0]
      exact isCompact_Icc.image ((EuclideanSpace.proj 1).continuous.comp F.continuous)
    obtain ⟨M,hM⟩ := (hycompact.image continuous_abs).bddAbove
    let B : ℝ := max M 0+1
    have hB : 0 < B := by dsimp [B];positivity
    have hbound (t : ℝ) : |F t 1| < B := by
      have h := hM ⟨F t 1,Set.mem_range_self t,rfl⟩
      dsimp [B]
      linarith [le_max_left M 0]
    have hnat (n : ℕ) (t : ℝ) : F (t+(n:ℝ)*(T)) = F t+Plane.mk ((n:ℝ)*(L)) 0 := by
      induction n with
      | zero => simp [Plane.mk]
      | succ n hn =>
        rw [Nat.cast_add,Nat.cast_one,show t+((n:ℝ)+1)*(T)=(t+(n:ℝ)*(T))+T by ring,hperiod,hn]
        ext i
        fin_cases i <;> simp [Plane.mk] <;> ring
    have hends (r : ℝ) : ∃ A : ℝ, F (-A) 0 < -r ∧ r < F A 0 := by
      obtain ⟨n,hn⟩ := exists_nat_gt ((r+|F 0 0|)/(L))
      have hnl := (div_lt_iff₀ (by positivity : 0 < L)).mp hn
      refine ⟨(n:ℝ)*(T),?_,?_⟩
      · have h := congrArg (fun z : Plane => z 0) (hnat n (-((n:ℝ)*(T))))
        simp only [neg_add_cancel] at h
        change F 0 0 = F (-((n:ℝ)*(T))) 0+(n:ℝ)*(L) at h
        linarith [le_abs_self (F 0 0)]
      · have h := congrArg (fun z : Plane => z 0) (hnat n 0)
        simp only [zero_add] at h
        change F ((n:ℝ)*(T)) 0 = F 0 0+(n:ℝ)*(L) at h
        linarith [neg_abs_le (F 0 0)]
    exact ⟨B,hB,hbound,hends⟩
  have glideAdjacentFacingBand {α : Type} (F : α → C(ℝ,Plane))
    (hproper : ∀ i, IsProperMap (F i)) (hinj : ∀ i, Function.Injective (F i))
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.range (F i)) (Set.range (F j)))
    (B : ℝ) (hB : 0<B) (hbound : ∀ i t, |F i t 1|<B)
    (hends : ∀ (i : α) (R : ℝ), ∃ A : ℝ, F i (-A) 0 < -R ∧ R < F i A 0)
    (e : Plane ≃ₜ Plane) (s : ℝ) (he : ∀ z, e z=Plane.mk (z 0+s) (-z 1))
    (bandPermutation : α → α) (hbandPermutation : Function.Involutive bandPermutation) (hnoFix : ∀ i, i ≠ bandPermutation i)
    (hmap : ∀ i, e '' Set.range (F i)=Set.range (F (bandPermutation i)))
    (x y : α) (hxy : x ≠ y) (hxbandPermutationy : x ≠ bandPermutation y) :
    ∃ j : α, (j=y ∨ j=bandPermutation y) ∧ ∃ U V : Set Plane,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      frontier U=Set.range (F x) ∧ frontier V=Set.range (F j) ∧
      Set.range (F j) ⊆ U ∧ Set.range (F x) ⊆ V ∧
      Disjoint (closure (U∩V)) (e '' closure (U∩V)) := by
  
    classical
    have normalizedRows (F : C(ℝ,Plane)) (hF : IsProperMap F) (hi : Function.Injective F)
      (B : ℝ) (hB : 0 < B) (hbound : ∀ t, |F t 1|<B)
      (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0) :
      ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U∪V=(Set.range F)ᶜ ∧ frontier U=Set.range F ∧ frontier V=Set.range F ∧
        (∀ x : ℝ, Plane.mk x (B+1)∈U) ∧ (∀ x : ℝ, Plane.mk x (-B-1)∈V) := by
    
      have normalizedSides (F : C(ℝ,Plane)) (hF : IsProperMap F) (hi : Function.Injective F)
        (B : ℝ) (hB : 0 < B) (hbound : ∀ t, |F t 1|<B)
        (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0) :
        ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
          Disjoint U V ∧ U∪V=(Set.range F)ᶜ ∧ frontier U=Set.range F ∧ frontier V=Set.range F ∧
          Plane.mk 0 (B+1)∈U ∧ Plane.mk 0 (-B-1)∈V := by
      
        have no_crossing (F : C(ℝ, Plane)) (B : ℝ) (hB : 0 < B)
            (hbound : ∀ x : ℝ, |F x 1| < B)
            (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
            (u w : Plane) (hu : u 1  ≤  -B) (hw : B  ≤  w 1) :
            ¬ JoinedIn (Set.range F)ᶜ u w := by
          have crossing_strip {a b c d : ℝ} (hab : a < b) (hcd : c < d)
              (h v : ℝ → Plane)
              (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
              (hhY : ∀ t ∈ Icc (-1 : ℝ) 1, c < h t 1 ∧ h t 1 < d)
              (hvX : ∀ t ∈ Icc (-1 : ℝ) 1, a < v t 0 ∧ v t 0 < b)
              (hh1 : h (-1) 0  ≤  a) (hh2 : b  ≤  h 1 0)
              (hv1 : v (-1) 1  ≤  c) (hv2 : d  ≤  v 1 1) :
              ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
            let H : ℝ → Plane := fun s => !₂[max a (min b (h s 0)), h s 1]
            let V : ℝ → Plane := fun t => !₂[v t 0, max c (min d (v t 1))]
            have hH : ContinuousOn H (Icc (-1) 1) := by
              apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
              apply continuousOn_pi.mpr
              intro i
              fin_cases i
              · exact (show Continuous (fun x : ℝ => max a (min b x)) by fun_prop).comp_continuousOn
                  ((EuclideanSpace.proj 0).continuous.comp_continuousOn hh)
              · exact (EuclideanSpace.proj 1).continuous.comp_continuousOn hh
            have hV : ContinuousOn V (Icc (-1) 1) := by
              apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
              apply continuousOn_pi.mpr
              intro i
              fin_cases i
              · exact (EuclideanSpace.proj 0).continuous.comp_continuousOn hv
              · exact (show Continuous (fun x : ℝ => max c (min d x)) by fun_prop).comp_continuousOn
                  ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv)
            have hHE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                H t 0 ∈ Icc a b ∧ H t 1 ∈ Icc c d := by
              exact ⟨⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩, (hhY t ht).1.le, (hhY t ht).2.le⟩
            have hVE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                V t 0 ∈ Icc a b ∧ V t 1 ∈ Icc c d := by
              exact ⟨⟨(hvX t ht).1.le, (hvX t ht).2.le⟩, le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
            have hH1 : H (-1) 0 = a := by
              dsimp [H]
              rw [min_eq_right (hh1.trans hab.le), max_eq_left hh1]
            have hH2 : H 1 0 = b := by
              dsimp [H]
              rw [min_eq_left hh2, max_eq_right hab.le]
            have hV1 : V (-1) 1 = c := by
              dsimp [V]
              rw [min_eq_right (hv1.trans hcd.le), max_eq_left hv1]
            have hV2 : V 1 1 = d := by
              dsimp [V]
              rw [min_eq_left hv2, max_eq_right hcd.le]
            obtain ⟨s, hs, t, ht, he⟩ := ClassificationJordanCurve.crossing ClassificationJordanCurve.Brouwer.brouwerFPT
              hab.le hcd.le H V hH hV hHE hVE hH1 hH2 hV1 hV2
            have clamp {l u x z : ℝ} (hlu : l < u) (hz : l < z ∧ z < u)
                (he : max l (min u x) = z) : x = z := by
              by_cases hx : x  ≤  l
              · rw [min_eq_right (hx.trans hlu.le), max_eq_left hx] at he
                linarith [hz.1]
              · by_cases hxu : u  ≤  x
                · rw [min_eq_left hxu, max_eq_right hlu.le] at he
                  linarith [hz.2]
                · rwa [min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hx)] at he
            refine ⟨s, hs, t, ht, ?_⟩
            have he0 := congrArg (fun p : Plane => p 0) he
            have he1 := congrArg (fun p : Plane => p 1) he
            ext i
            fin_cases i
            · exact clamp hab (hvX t ht) he0
            · exact (clamp hcd (hhY s hs) he1.symm).symm
          intro hjoin
          obtain ⟨v, hv, hv0, hv1, hvmem⟩ := ClassificationJordanCurve.arc_path hjoin
          have hvc : ContinuousOn (fun t : ℝ => |v t 0|) (Icc (-1) 1) :=
            continuous_abs.comp_continuousOn ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv)
          obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hvc).bddAbove
          let R := max M 0 + 1
          have hR : 0 < R := by dsimp [R]; positivity
          have hMv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |v t 0| < R := by
            have hm := hM (Set.mem_image_of_mem _ ht)
            dsimp [R]
            linarith [le_max_left M 0]
          obtain ⟨A, hA0, hA1⟩ := hends R
          let h : ℝ → Plane := fun s => F (A * s)
          have hhc : ContinuousOn h (Icc (-1) 1) :=
            (F.continuous.comp (by fun_prop : Continuous (fun s : ℝ => A * s))).continuousOn
          have hhY (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) : -B < h t 1 ∧ h t 1 < B :=
            abs_lt.mp (hbound (A * t))
          have hvX (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -R < v t 0 ∧ v t 0 < R :=
            abs_lt.mp (hMv t ht)
          have hh0 : h (-1) 0  ≤  -R := by simpa [h] using hA0.le
          have hh1 : R  ≤  h 1 0 := by simpa [h] using hA1.le
          have hv0' : v (-1) 1  ≤  -B := by simpa [hv0] using hu
          have hv1' : B  ≤  v 1 1 := by simpa [hv1] using hw
          obtain ⟨s, hs, t, ht, he⟩ := crossing_strip (by linarith : -R < R)
            (by linarith : -B < B) h v hhc hv hhY hvX hh0 hh1 hv0' hv1'
          exact hvmem t ht ⟨A * s, he⟩
        let p : Plane := Plane.mk 0 (B+1)
        let q : Plane := Plane.mk 0 (-B-1)
        have hp1 : p 1=B+1 := by simp [p,Plane.mk]
        have hq1 : q 1=-B-1 := by simp [q,Plane.mk]
        have hpL : p∉Set.range F := by
          rintro ⟨t,ht⟩
          have h := (abs_lt.mp (hbound t)).2
          have he := congrArg (fun x : Plane => x 1) ht
          rw [hp1] at he
          linarith
        have hqL : q∉Set.range F := by
          rintro ⟨t,ht⟩
          have h := (abs_lt.mp (hbound t)).1
          have he := congrArg (fun x : Plane => x 1) ht
          rw [hq1] at he
          linarith
        have hn : ¬JoinedIn (Set.range F)ᶜ q p :=
          no_crossing F B hB hbound hends q p (by rw [hq1];linarith) (by rw [hp1];linarith)
        have hj := proper_line_inversion_isJordanCurve F hF hi p hpL
        obtain ⟨U,V,hU,hV,hUc,hVc,hd,hpart,hfU,hfV⟩ :=
          proper_line_sides_of_inversion_jordan (Set.range F) p hpL hj
        have hp : p∈U∪V := hpart.symm ▸ hpL
        have hq : q∈U∪V := hpart.symm ▸ hqL
        have hUL : U ⊆ (Set.range F)ᶜ := fun x hx => hpart ▸ Or.inl hx
        have hVL : V ⊆ (Set.range F)ᶜ := fun x hx => hpart ▸ Or.inr hx
        have sameU : ¬(p∈U ∧ q∈U) := by
          rintro ⟨hp,hq⟩
          exact hn (((hU.isConnected_iff_isPathConnected.mp hUc).joinedIn q hq p hp).mono hUL)
        have sameV : ¬(p∈V ∧ q∈V) := by
          rintro ⟨hp,hq⟩
          exact hn (((hV.isConnected_iff_isPathConnected.mp hVc).joinedIn q hq p hp).mono hVL)
        rcases hp with hp | hp
        · rcases hq with hq | hq
          · exact False.elim (sameU ⟨hp,hq⟩)
          · exact ⟨U,V,hU,hV,hUc,hVc,hd,hpart,hfU,hfV,hp,hq⟩
        · rcases hq with hq | hq
          · exact ⟨V,U,hV,hU,hVc,hUc,hd.symm,(union_comm V U).trans hpart,hfV,hfU,hp,hq⟩
          · exact False.elim (sameV ⟨hp,hq⟩)
      obtain ⟨U,V,hU,hV,hUc,hVc,hd,hpart,hfU,hfV,hp,hq⟩ := normalizedSides F hF hi B hB hbound hends
      have rowContained (U V : Set Plane) (hU : IsOpen U) (hV : IsOpen V)
          (hd : Disjoint U V) (hpart : U∪V=(Set.range F)ᶜ)
          (y : ℝ) (hrow : ∀ x : ℝ, Plane.mk x y∉Set.range F) (h0 : Plane.mk 0 y∈U) :
          ∀ x : ℝ, Plane.mk x y∈U := by
        let row : C(ℝ,Plane) := ⟨fun x => Plane.mk x y,by
          apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
          apply continuous_pi
          intro i
          fin_cases i <;> simp only [Plane.mk,Matrix.vecCons,Matrix.vecEmpty,Fin.isValue] <;> fun_prop⟩
        have hrowSubset : Set.range row ⊆ U∪V := by
          rintro _ ⟨x,rfl⟩
          exact hpart.symm ▸ hrow x
        rcases (isConnected_range row.continuous).isPreconnected.subset_or_subset hU hV hd hrowSubset with h | h
        · intro x;exact h (Set.mem_range_self x)
        · exact False.elim (Set.disjoint_left.mp hd h0 (h (Set.mem_range_self 0)))
      have hu : ∀ x : ℝ, Plane.mk x (B+1)∈U := by
        apply rowContained U V hU hV hd hpart (B+1) ?_ hp
        intro x
        rintro ⟨t,ht⟩
        have h := (abs_lt.mp (hbound t)).2
        have he := congrArg (fun z : Plane => z 1) ht
        simp [Plane.mk] at he
        linarith
      have hv : ∀ x : ℝ, Plane.mk x (-B-1)∈V := by
        apply rowContained V U hV hU hd.symm ((union_comm V U).trans hpart) (-B-1) ?_ hq
        intro x
        rintro ⟨t,ht⟩
        have h := (abs_lt.mp (hbound t)).1
        have he := congrArg (fun z : Plane => z 1) ht
        simp [Plane.mk] at he
        linarith
      exact ⟨U,V,hU,hV,hUc,hVc,hd,hpart,hfU,hfV,hu,hv⟩
    have lineSideOrder {X : Type} [TopologicalSpace X]
      (L₁ L₂ U₁ V₁ U₂ V₂ : Set X)
        (hL₁ : L₁.Nonempty) (hL₂ : IsConnected L₂)
        (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
        (hcU₁ : IsConnected U₁) (hcV₁ : IsConnected V₁)
        (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
        (hp₁ : U₁ ∪ V₁ = L₁ᶜ) (hp₂ : U₂ ∪ V₂ = L₂ᶜ)
        (hfU₁ : frontier U₁ = L₁) (hfV₁ : frontier V₁ = L₁)
        (hdL : Disjoint L₁ L₂)
        (hcommonU : (U₁ ∩ U₂).Nonempty) (hcommonV : (V₁ ∩ V₂).Nonempty) :
        U₁ ⊂ U₂ ∨ U₂ ⊂ U₁ := by
    
    
      have hU₁L : Disjoint U₁ L₁ := by
        apply disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inl hx) hL
      have hV₁L : Disjoint V₁ L₁ := by
        apply disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inr hx) hL
      have hU₂L : Disjoint U₂ L₂ := by
        apply disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ L₂ᶜ from hp₂ ▸ Or.inl hx) hL
      have hclU : closure U₁ = U₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfU₁]
      have hclV : closure V₁ = V₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfV₁]
      have hsub : L₂ ⊆ U₁ ∪ V₁ := by
        rw [hp₁]
        exact fun x hx h => disjoint_left.mp hdL h hx
      rcases hL₂.isPreconnected.subset_or_subset hU₁ hV₁ hd₁ hsub with hLU | hLV
      · have hsubcl : closure V₁ ⊆ U₂ ∪ V₂ := by
          rw [hp₂, hclV]
          rintro x (hx | hx) hL
          · exact disjoint_left.mp hd₁ (hLU hL) hx
          · exact disjoint_left.mp hdL hx hL
        have hcl : closure V₁ ⊆ V₂ := by
          rcases hcV₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
          · obtain ⟨x, hx₁, hx₂⟩ := hcommonV
            exact False.elim (disjoint_left.mp hd₂ (h (subset_closure hx₁)) hx₂)
          · exact h
        have hUU : U₂ ⊆ U₁ := by
          intro x hx
          by_contra hx₁
          have hxcl : x ∈ closure V₁ := by
            rw [hclV]
            by_cases hxL : x ∈ L₁
            · exact Or.inr hxL
            · have hside : x ∈ U₁ ∪ V₁ := hp₁.symm ▸ hxL
              exact Or.inl (hside.resolve_left hx₁)
          exact disjoint_left.mp hd₂ hx (hcl hxcl)
        right
        apply Set.ssubset_iff_subset_ne.mpr
        refine ⟨hUU, ?_⟩
        intro he
        obtain ⟨x, hx⟩ := hL₂.nonempty
        exact disjoint_left.mp hU₂L (he.symm ▸ hLU hx) hx
      · have hsubcl : closure U₁ ⊆ U₂ ∪ V₂ := by
          rw [hp₂, hclU]
          rintro x (hx | hx) hL
          · exact disjoint_left.mp hd₁ hx (hLV hL)
          · exact disjoint_left.mp hdL hx hL
        have hcl : closure U₁ ⊆ U₂ := by
          rcases hcU₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
          · exact h
          · obtain ⟨x, hx₁, hx₂⟩ := hcommonU
            exact False.elim (disjoint_left.mp hd₂ hx₂ (h (subset_closure hx₁)))
        left
        apply Set.ssubset_iff_subset_ne.mpr
        refine ⟨subset_closure.trans hcl, ?_⟩
        intro he
        obtain ⟨x, hx⟩ := hL₁
        have hxc : x ∈ closure U₁ := hclU.symm ▸ Or.inr hx
        exact disjoint_left.mp hU₁L (he.symm ▸ hcl hxc) hx
    have glideSides (e : Plane ≃ₜ Plane) (s B : ℝ)
      (he : ∀ z, e z=Plane.mk (z 0+s) (-z 1))
      (L1 L2 U1 V1 U2 V2 : Set Plane)
      (hU1 : IsOpen U1) (hV1 : IsOpen V1) (hcU1 : IsConnected U1) (hcV1 : IsConnected V1)
      (hU2 : IsOpen U2) (hV2 : IsOpen V2) (hd2 : Disjoint U2 V2)
      (hp1 : U1∪V1=L1ᶜ) (hp2 : U2∪V2=L2ᶜ) (heL : e '' L1=L2)
      (hupper1 : ∀ x, Plane.mk x (B+1)∈U1) (hlower1 : ∀ x, Plane.mk x (-B-1)∈V1)
      (hupper2 : ∀ x, Plane.mk x (B+1)∈U2) (hlower2 : ∀ x, Plane.mk x (-B-1)∈V2) :
      e '' U1=V2 ∧ e '' V1=U2 := by
    
      have hpart : e '' U1 ∪ e '' V1=L2ᶜ := by
        rw [←Set.image_union,hp1,e.image_compl,heL]
      have hupper : e (Plane.mk 0 (B+1))=Plane.mk s (-B-1) := by
        rw [he]
        ext i
        fin_cases i <;> simp [Plane.mk] <;> ring
      have hlower : e (Plane.mk 0 (-B-1))=Plane.mk s (B+1) := by
        rw [he]
        ext i
        fin_cases i <;> simp [Plane.mk] <;> ring
      have hsubU : e '' U1 ⊆ U2∪V2 := by
        rw [hp2,←hpart]
        exact subset_union_left
      have hsubV : e '' V1 ⊆ U2∪V2 := by
        rw [hp2,←hpart]
        exact subset_union_right
      have hUV : e '' U1 ⊆ V2 := by
        rcases (hcU1.image e e.continuous.continuousOn).isPreconnected.subset_or_subset hU2 hV2 hd2 hsubU with h | h
        · have h := h (Set.mem_image_of_mem e (hupper1 0))
          rw [hupper] at h
          exact False.elim (Set.disjoint_left.mp hd2 h (hlower2 s))
        · exact h
      have hVU : e '' V1 ⊆ U2 := by
        rcases (hcV1.image e e.continuous.continuousOn).isPreconnected.subset_or_subset hU2 hV2 hd2 hsubV with h | h
        · exact h
        · have h := h (Set.mem_image_of_mem e (hlower1 0))
          rw [hlower] at h
          exact False.elim (Set.disjoint_left.mp hd2 (hupper2 s) h)
      constructor
      · apply Set.Subset.antisymm hUV
        intro z hz
        have hzc : z∈L2ᶜ := hp2 ▸ Or.inr hz
        have hzpart : z∈e '' U1 ∪ e '' V1 := hpart.symm ▸ hzc
        exact hzpart.resolve_right (fun h => Set.disjoint_left.mp hd2 (hVU h) hz)
      · apply Set.Subset.antisymm hVU
        intro z hz
        have hzc : z∈L2ᶜ := hp2 ▸ Or.inl hz
        have hzpart : z∈e '' U1 ∪ e '' V1 := hpart.symm ▸ hzc
        exact hzpart.resolve_left (fun h => Set.disjoint_left.mp hd2 hz (hUV h))
    have bandPairSelection {X : Type} [LinearOrder X] (g : X → X)
      (hinv : Function.Involutive g) (x y : X) (hx : x  ≠  g x) (hy : y  ≠  g y) :
      ∃ y' : X, (y'=y ∨ y'=g y) ∧
        (max x y' < g (max x y') ∨ g (min x y') < min x y') := by
    
      have below (u v : X) (hu : u<g u) (hv : v<g v) : max u v<g (max u v) := by
        rcases le_total u v with h | h
        · rw [max_eq_right h];exact hv
        · rw [max_eq_left h];exact hu
      have above (u v : X) (hu : g u<u) (hv : g v<v) : g (min u v)< min u v := by
        rcases le_total u v with h | h
        · rw [min_eq_left h];exact hu
        · rw [min_eq_right h];exact hv
      rcases lt_or_gt_of_ne hx with hx | hx
      · rcases lt_or_gt_of_ne hy with hy | hy
        · exact ⟨y,Or.inl rfl,Or.inl (below x y hx hy)⟩
        · exact ⟨g y,Or.inr rfl,Or.inl (below x (g y) hx (by simpa only [hinv y] using hy))⟩
      · rcases lt_or_gt_of_ne hy with hy | hy
        · exact ⟨g y,Or.inr rfl,Or.inr (above x (g y) hx (by simpa only [hinv y] using hy))⟩
        · exact ⟨y,Or.inl rfl,Or.inr (above x y hx hy)⟩
    choose upper lower hU hV hcU hcV hd hp hfU hfV hupper hlower using
      (fun i => normalizedRows (F i) (hproper i) (hinj i) B hB (hbound i) (hends i))
    have hUavoid (i : α) : Disjoint (upper i) (Set.range (F i)) := by
      apply Set.disjoint_left.mpr
      intro z hz hL
      exact (show z∈(Set.range (F i))ᶜ from hp i ▸ Or.inl hz) hL
    have hVavoid (i : α) : Disjoint (lower i) (Set.range (F i)) := by
      apply Set.disjoint_left.mpr
      intro z hz hL
      exact (show z∈(Set.range (F i))ᶜ from hp i ▸ Or.inr hz) hL
    have upper_eq (i : α) : upper i=(closure (lower i))ᶜ := by
      rw [closure_eq_self_union_frontier,hfV i]
      ext z
      constructor
      · intro hz
        rintro (hv | hL)
        · exact Set.disjoint_left.mp (hd i) hz hv
        · exact Set.disjoint_left.mp (hUavoid i) hz hL
      · intro hz
        have hL : z∉Set.range (F i) := fun h => hz (Or.inr h)
        have hside : z∈upper i ∪ lower i := (hp i).symm ▸ hL
        exact hside.resolve_right (fun h => hz (Or.inl h))
    have lower_eq (i : α) : lower i=(closure (upper i))ᶜ := by
      rw [closure_eq_self_union_frontier,hfU i]
      ext z
      constructor
      · intro hz
        rintro (hu | hL)
        · exact Set.disjoint_left.mp (hd i) hu hz
        · exact Set.disjoint_left.mp (hVavoid i) hz hL
      · intro hz
        have hL : z∉Set.range (F i) := fun h => hz (Or.inr h)
        have hside : z∈upper i ∪ lower i := (hp i).symm ▸ hL
        exact hside.resolve_left (fun h => hz (Or.inl h))
    have hLowerInjective : Function.Injective lower := by
      intro i j heq
      by_contra hn
      have hr : Set.range (F i)=Set.range (F j) :=
        (hfV i).symm.trans ((congrArg frontier heq).trans (hfV j))
      exact Set.disjoint_left.mp (hdis i j hn) (Set.mem_range_self 0)
        (hr ▸ Set.mem_range_self 0)
    letI : PartialOrder α := PartialOrder.lift lower hLowerInjective
    have hTotal (i j : α) : i ≤ j ∨ j ≤ i := by
      by_cases hij : i=j
      · subst j;exact Or.inl le_rfl
      have horder := lineSideOrder (Set.range (F i)) (Set.range (F j))
        (lower i) (upper i) (lower j) (upper j)
        ⟨F i 0,Set.mem_range_self 0⟩ (isConnected_range (F j).continuous)
        (hV i) (hU i) (hV j) (hU j) (hcV i) (hcU i) (hd i).symm (hd j).symm
        ((union_comm _ _).trans (hp i)) ((union_comm _ _).trans (hp j))
        (hfV i) (hfU i) (hdis i j hij)
        ⟨Plane.mk 0 (-B-1),hlower i 0,hlower j 0⟩ ⟨Plane.mk 0 (B+1),hupper i 0,hupper j 0⟩
      exact horder.elim (fun h => Or.inl h.subset) (fun h => Or.inr h.subset)
    letI : LinearOrder α := Relation.linearOrderOfSymmGen hTotal
    have strongOrder (i j : α) (hij : i<j) : closure (lower i) ⊆ lower j := by
      have hsub : lower i ⊆ lower j := hij.le
      have hneq : i ≠ j := hij.ne
      have hclavoid : closure (lower i) ⊆ upper j ∪ lower j := by
        rw [hp j,closure_eq_self_union_frontier,hfV i]
        rintro z (hz | hz) hLj
        · exact Set.disjoint_left.mp (hVavoid j) (hsub hz) hLj
        · exact Set.disjoint_left.mp (hdis i j hneq) hz hLj
      rcases (hcV i).closure.isPreconnected.subset_or_subset (hU j) (hV j) (hd j) hclavoid with h | h
      · exact False.elim (Set.disjoint_left.mp (hd j) (h (subset_closure (hlower i 0))) (hlower j 0))
      · exact h
    have hswap (i : α) : e '' upper i=lower (bandPermutation i) ∧ e '' lower i=upper (bandPermutation i) :=
      glideSides e s B he (Set.range (F i)) (Set.range (F (bandPermutation i)))
        (upper i) (lower i) (upper (bandPermutation i)) (lower (bandPermutation i))
        (hU i) (hV i) (hcU i) (hcV i) (hU (bandPermutation i)) (hV (bandPermutation i)) (hd (bandPermutation i))
        (hp i) (hp (bandPermutation i)) (hmap i) (hupper i) (hlower i) (hupper (bandPermutation i)) (hlower (bandPermutation i))
    obtain ⟨j,hj,hbelow | habove⟩ := bandPairSelection bandPermutation hbandPermutation x y (hnoFix x) (hnoFix y)
    all_goals
      have hxj : x ≠ j := by rcases hj with rfl | rfl;exact hxy;exact hxbandPermutationy
      let m : α := max x j
      let l : α := min x j
      let D := closure (lower m) ∩ closure (upper l)
      have hDdis : Disjoint D (e '' D) := by
        apply Set.disjoint_left.mpr
        rintro z hz ⟨w,hw,rfl⟩
        first
        | have hnest : closure (lower m) ⊆ lower (bandPermutation m) := strongOrder m (bandPermutation m) hbelow
          have hlow := hnest hz.1
          have heup : e w∈closure (upper (bandPermutation m)) := by
            rw [←(hswap m).2,←e.image_closure]
            exact Set.mem_image_of_mem e hw.1
          rw [lower_eq (bandPermutation m)] at hlow
          exact hlow heup
        | have hnest : closure (lower (bandPermutation l)) ⊆ lower l := strongOrder (bandPermutation l) l habove
          have helow : e w∈closure (lower (bandPermutation l)) := by
            rw [←(hswap l).1,←e.image_closure]
            exact Set.mem_image_of_mem e hw.2
          have hlow := hnest helow
          rw [lower_eq l] at hlow
          exact hlow hz.2
      have hclosedDis (A C : Set Plane) (hsub : closure (A∩C) ⊆ D) :
          Disjoint (closure (A∩C)) (e '' closure (A∩C)) :=
        hDdis.mono hsub (Set.image_mono hsub)
      by_cases hxjle : x ≤ j
      · have hxjlt : x<j := lt_of_le_of_ne hxjle hxj
        have hnest := strongOrder x j hxjlt
        have hFx : Set.range (F x) ⊆ lower j := by
          intro z hz
          exact hnest (by rw [closure_eq_self_union_frontier,hfV x];exact Or.inr hz)
        have hFj : Set.range (F j) ⊆ upper x := by
          rw [upper_eq x]
          intro z hz hcl
          exact Set.disjoint_left.mp (hVavoid j) (hnest hcl) hz
        refine ⟨j,hj,upper x,lower j,hU x,hV j,hcU x,hcV j,hfU x,hfV j,hFj,hFx,?_⟩
        apply hclosedDis
        have h : closure (upper x ∩ lower j) ⊆ closure (upper x) ∩ closure (lower j) := closure_inter_subset
        simpa only [D,m,l,max_eq_right hxjle,min_eq_left hxjle,inter_comm] using h
      · have hjx : j<x := lt_of_not_ge hxjle
        have hnest := strongOrder j x hjx
        have hFj : Set.range (F j) ⊆ lower x := by
          intro z hz
          exact hnest (by rw [closure_eq_self_union_frontier,hfV j];exact Or.inr hz)
        have hFx : Set.range (F x) ⊆ upper j := by
          rw [upper_eq j]
          intro z hz hcl
          exact Set.disjoint_left.mp (hVavoid x) (hnest hcl) hz
        refine ⟨j,hj,lower x,upper j,hV x,hU j,hcV x,hcU j,hfV x,hfU j,hFj,hFx,?_⟩
        apply hclosedDis
        have h : closure (lower x ∩ upper j) ⊆ closure (lower x) ∩ closure (upper j) := closure_inter_subset
        simpa only [D,m,l,max_eq_left hjx.le,min_eq_right hjx.le] using h

  let prodPlane : (ℝ × ℝ) ≃ₜ Schoenflies.Plane :=
    { toFun := fun x => Schoenflies.Plane.mk x.1 x.2
      invFun := fun z => (z 0,z 1)
      left_inv := by intro x;rfl
      right_inv := by intro z;ext i;fin_cases i <;> rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let axisPlane : H2 ≃ₜ Schoenflies.Plane := sourceAxisCoordinate.trans prodPlane
  let minimalGlidePlane : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (axisPlane.symm.trans (developedDeck minimalAxisDeck.val)).trans axisPlane
  let normalizedSource : C(ℝ,Schoenflies.Plane) := ⟨axisPlane ∘ sourceLift,axisPlane.continuous.comp sourceLift.continuous⟩
  let normalizedTarget : C(ℝ,Schoenflies.Plane) := ⟨axisPlane ∘ targetLift,axisPlane.continuous.comp targetLift.continuous⟩
  let glideSource : C(ℝ,Schoenflies.Plane) := ⟨minimalGlidePlane ∘ normalizedSource,
    minimalGlidePlane.continuous.comp normalizedSource.continuous⟩
  let glideTarget : C(ℝ,Schoenflies.Plane) := ⟨minimalGlidePlane ∘ normalizedTarget,
    minimalGlidePlane.continuous.comp normalizedTarget.continuous⟩
  let fourBoundaryLifts : Fin 4 → C(ℝ,Schoenflies.Plane) := ![normalizedSource,normalizedTarget,glideSource,glideTarget]
  let boundaryPermutation : Fin 4 → Fin 4 := ![2,3,0,1]
  have actual_index_two_source_lifts_admit_glide_disjoint_facing_band
      (hindex : originalAxisNatIndex=2) :
      ∃ j : Fin 4, (j=1 ∨ j=3) ∧ ∃ U V : Set Schoenflies.Plane,
        IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        frontier U=Set.range normalizedSource ∧ frontier V=Set.range (fourBoundaryLifts j) ∧
        Set.range (fourBoundaryLifts j) ⊆ U ∧ Set.range normalizedSource ⊆ V ∧
        Disjoint (closure (U∩V)) (minimalGlidePlane '' closure (U∩V)) := by
    have hmono := actual_index_two_original_monodromy_is_glide_square hindex
    have hg := actual_index_two_minimal_axis_generator_is_glide hindex
    have hkcoord (z : H2) : sourceAxisCoordinate (developedDeck minimalAxisDeck.val z) =
        ((sourceAxisCoordinate z).1+minimalAxisPeriod,-(sourceAxisCoordinate z).2) := by
      have h := glideCoordinate minimalAxisIsometry minimalAxisPeriod hg (axisNormalizingIsometry.symm z)
      change logarithmicCoordinate (axisNormalizingIsometry.symm (developedDeckIsometry minimalAxisDeck.val z)) =
        ((logarithmicCoordinate (axisNormalizingIsometry.symm z)).1+minimalAxisPeriod,
          -(logarithmicCoordinate (axisNormalizingIsometry.symm z)).2)
      simpa only [minimalAxisIsometry,sourceAxisCoordinate,Homeomorph.trans_apply,
        IsometryEquiv.trans_apply,axisNormalizingIsometry.apply_symm_apply] using h
    have hGcoord (z : H2) : minimalGlidePlane (axisPlane z)=axisPlane (developedDeck minimalAxisDeck.val z) := by
      change axisPlane (developedDeck minimalAxisDeck.val (axisPlane.symm (axisPlane z))) = _
      rw [axisPlane.symm_apply_apply]
    have hG (z : Schoenflies.Plane) : minimalGlidePlane z =
        Schoenflies.Plane.mk (z 0+minimalAxisPeriod) (-z 1) := by
      change prodPlane (sourceAxisCoordinate (developedDeck minimalAxisDeck.val (axisPlane.symm z))) = _
      rw [hkcoord]
      have hh : sourceAxisCoordinate (axisPlane.symm z)=(z 0,z 1) := by
        change sourceAxisCoordinate (sourceAxisCoordinate.symm (prodPlane.symm z)) = _
        exact sourceAxisCoordinate.apply_symm_apply _
      rw [hh]
      rfl
    have hG2 (z : Schoenflies.Plane) : minimalGlidePlane (minimalGlidePlane z)=
        z+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by
      rw [hG,hG]
      ext i
      fin_cases i <;> simp [Schoenflies.Plane.mk] <;> ring
    have hGcomm (z : Schoenflies.Plane) : minimalGlidePlane (z+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0)=
        minimalGlidePlane z+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by
      rw [hG,hG]
      ext i
      fin_cases i <;> simp [Schoenflies.Plane.mk] <;> ring
    have hSsq (t : ℝ) : normalizedSource (t+2*Real.pi)=minimalGlidePlane (minimalGlidePlane (normalizedSource t)) := by
      change axisPlane (sourceLift (t+2*Real.pi)) =
        minimalGlidePlane (minimalGlidePlane (axisPlane (sourceLift t)))
      rw [hGcoord,hGcoord,sourceLift_period,←actual_developedDeck_mul,←pow_two,←hmono]
    have hTsq (t : ℝ) : normalizedTarget (t+2*Real.pi)=minimalGlidePlane (minimalGlidePlane (normalizedTarget t)) := by
      change axisPlane (targetLift (t+2*Real.pi)) =
        minimalGlidePlane (minimalGlidePlane (axisPlane (targetLift t)))
      rw [hGcoord,hGcoord,targetLift_period,←actual_developedDeck_mul,←pow_two,←hmono]
    have hSp (t : ℝ) : normalizedSource (t+2*Real.pi)=normalizedSource t+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by rw [hSsq,hG2]
    have hTp (t : ℝ) : normalizedTarget (t+2*Real.pi)=normalizedTarget t+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by rw [hTsq,hG2]
    have hGSp (t : ℝ) : glideSource (t+2*Real.pi)=glideSource t+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by
      change minimalGlidePlane (normalizedSource (t+2*Real.pi)) = _
      rw [hSp,hGcomm]
      rfl
    have hGTp (t : ℝ) : glideTarget (t+2*Real.pi)=glideTarget t+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by
      change minimalGlidePlane (normalizedTarget (t+2*Real.pi)) = _
      rw [hTp,hGcomm]
      rfl
    have hFperiod (i : Fin 4) (t : ℝ) : fourBoundaryLifts i (t+2*Real.pi)=
        fourBoundaryLifts i t+Schoenflies.Plane.mk (2*minimalAxisPeriod) 0 := by
      fin_cases i <;> first | exact hSp t | exact hTp t | exact hGSp t | exact hGTp t
    have hSclosed : Topology.IsClosedEmbedding normalizedSource := axisPlane.isClosedEmbedding.comp actual_sourceLift_closed_embedding
    have hTclosed : Topology.IsClosedEmbedding normalizedTarget := axisPlane.isClosedEmbedding.comp actual_targetLift_closed_embedding
    have hGSclosed : Topology.IsClosedEmbedding glideSource := minimalGlidePlane.isClosedEmbedding.comp hSclosed
    have hGTclosed : Topology.IsClosedEmbedding glideTarget := minimalGlidePlane.isClosedEmbedding.comp hTclosed
    have hproper (i : Fin 4) : IsProperMap (fourBoundaryLifts i) := by
      fin_cases i <;> first | exact hSclosed.isProperMap | exact hTclosed.isProperMap | exact hGSclosed.isProperMap | exact hGTclosed.isProperMap
    have hinjective (i : Fin 4) : Function.Injective (fourBoundaryLifts i) := by
      fin_cases i <;> first | exact hSclosed.injective | exact hTclosed.injective | exact hGSclosed.injective | exact hGTclosed.injective
    have hrS : Set.range normalizedSource=axisPlane '' Set.range sourceLift := by
      change Set.range (axisPlane ∘ sourceLift)=_
      rw [Set.range_comp]
    have hrT : Set.range normalizedTarget=axisPlane '' Set.range targetLift := by
      change Set.range (axisPlane ∘ targetLift)=_
      rw [Set.range_comp]
    have hrGS : Set.range glideSource=minimalGlidePlane '' Set.range normalizedSource := by
      change Set.range (minimalGlidePlane ∘ normalizedSource)=_
      rw [Set.range_comp]
    have hrGT : Set.range glideTarget=minimalGlidePlane '' Set.range normalizedTarget := by
      change Set.range (minimalGlidePlane ∘ normalizedTarget)=_
      rw [Set.range_comp]
    have hImgS : minimalGlidePlane '' (axisPlane '' Set.range sourceLift)=
        axisPlane '' (developedDeck minimalAxisDeck.val '' Set.range sourceLift) := by
      rw [Set.image_image,Set.image_image]
      congr 1
      funext z
      exact hGcoord z
    have hImgT : minimalGlidePlane '' (axisPlane '' Set.range targetLift)=
        axisPlane '' (developedDeck minimalAxisDeck.val '' Set.range targetLift) := by
      rw [Set.image_image,Set.image_image]
      congr 1
      funext z
      exact hGcoord z
    have h01 : Disjoint (Set.range normalizedSource) (Set.range normalizedTarget) := by
      rw [hrS,hrT]
      exact (Set.disjoint_image_iff axisPlane.injective).mpr actual_endpoint_lifts_disjoint
    have h02 : Disjoint (Set.range normalizedSource) (Set.range glideSource) := by
      rw [hrGS,hrS,hImgS]
      exact (Set.disjoint_image_iff axisPlane.injective).mpr
        ((actual_noncyclic_source_and_target_translates_disjoint minimalAxisDeck.val
          (actual_index_two_minimal_generator_not_common_cyclic hindex)).1.symm)
    have h13 : Disjoint (Set.range normalizedTarget) (Set.range glideTarget) := by
      rw [hrGT,hrT,hImgT]
      exact (Set.disjoint_image_iff axisPlane.injective).mpr
        ((actual_noncyclic_source_and_target_translates_disjoint minimalAxisDeck.val
          (actual_index_two_minimal_generator_not_common_cyclic hindex)).2.symm)
    have h03 : Disjoint (Set.range normalizedSource) (Set.range glideTarget) := by
      rw [hrGT,hrS,hrT,hImgT]
      apply (Set.disjoint_image_iff axisPlane.injective).mpr
      simpa only [actual_developedDeck_one,Set.image_id'] using all_developed_source_target_translates_disjoint 1 minimalAxisDeck.val
    have h12 : Disjoint (Set.range normalizedTarget) (Set.range glideSource) := by
      rw [hrGS,hrT,hrS,hImgS]
      apply (Set.disjoint_image_iff axisPlane.injective).mpr
      simpa only [actual_developedDeck_one,Set.image_id'] using
        (all_developed_source_target_translates_disjoint minimalAxisDeck.val 1).symm
    have h23 : Disjoint (Set.range glideSource) (Set.range glideTarget) := by
      rw [hrGS,hrGT]
      exact (Set.disjoint_image_iff minimalGlidePlane.injective).mpr h01
    have hPairDisjoint (i j : Fin 4) (hij : i ≠ j) :
        Disjoint (Set.range (fourBoundaryLifts i)) (Set.range (fourBoundaryLifts j)) := by
      fin_cases i <;> fin_cases j <;> norm_num at hij
      all_goals
        first
        | exact h01
        | exact h01.symm
        | exact h02
        | exact h02.symm
        | exact h03
        | exact h03.symm
        | exact h12
        | exact h12.symm
        | exact h13
        | exact h13.symm
        | exact h23
        | exact h23.symm
    have rangeSquare (K : C(ℝ,Schoenflies.Plane))
        (hK : ∀ t, K (t+2*Real.pi)=minimalGlidePlane (minimalGlidePlane (K t))) :
        minimalGlidePlane '' (minimalGlidePlane '' Set.range K)=Set.range K := by
      apply Set.Subset.antisymm
      · rintro _ ⟨_,⟨_,⟨t,rfl⟩,rfl⟩,rfl⟩
        exact ⟨t+2*Real.pi,hK t⟩
      · rintro _ ⟨t,rfl⟩
        refine ⟨minimalGlidePlane (K (t-2*Real.pi)),?_,?_⟩
        · exact Set.mem_image_of_mem _ (Set.mem_range_self _)
        · rw [←hK,sub_add_cancel]
    have hmap (i : Fin 4) : minimalGlidePlane '' Set.range (fourBoundaryLifts i)=
        Set.range (fourBoundaryLifts (boundaryPermutation i)) := by
      fin_cases i
      · exact hrGS.symm
      · exact hrGT.symm
      · change minimalGlidePlane '' Set.range glideSource=Set.range normalizedSource
        rw [hrGS]
        exact rangeSquare normalizedSource hSsq
      · change minimalGlidePlane '' Set.range glideTarget=Set.range normalizedTarget
        rw [hrGT]
        exact rangeSquare normalizedTarget hTsq
    have hPermutation : Function.Involutive boundaryPermutation := by intro i;fin_cases i <;> rfl
    have hNoFix (i : Fin 4) : i ≠ boundaryPermutation i := by fin_cases i <;> norm_num [boundaryPermutation]
    choose bounds boundsPositive boundsControl boundsEnds using (fun i => horizontalBoundsAndEnds
      (fourBoundaryLifts i) (2*Real.pi) (2*minimalAxisPeriod) (by positivity) (by positivity) (hFperiod i))
    let commonBound : ℝ := Finset.univ.sup' Finset.univ_nonempty bounds
    have boundsLe (i : Fin 4) : bounds i ≤ commonBound := Finset.le_sup' bounds (Finset.mem_univ i)
    have commonBoundPositive : 0<commonBound := (boundsPositive 0).trans_le (boundsLe 0)
    have hBound (i : Fin 4) (t : ℝ) : |fourBoundaryLifts i t 1|<commonBound := (boundsControl i t).trans_le (boundsLe i)
    obtain ⟨j,hj,U,V,hU,hV,hUc,hVc,hfrontU,hfrontV,hjU,h0V,hBand⟩ :=
      glideAdjacentFacingBand fourBoundaryLifts hproper hinjective hPairDisjoint commonBound commonBoundPositive
        hBound boundsEnds minimalGlidePlane minimalAxisPeriod hG boundaryPermutation hPermutation hNoFix hmap
        0 1 (by norm_num) (by norm_num [boundaryPermutation])
    refine ⟨j,?_,U,V,hU,hV,hUc,hVc,hfrontU,hfrontV,hjU,h0V,hBand⟩
    simpa only [boundaryPermutation,Matrix.cons_val_one,Matrix.cons_val_zero] using hj

  have selected_target_glide_separated_collared_annulus
      (targetLift : C(ℝ,H2))
      (targetLift_projection : ∀ s, developedProjection (targetLift s)=b.map (Circle.exp s))
      (targetLift_period : ∀ s, targetLift (s+2*Real.pi)=developedDeck monodromy (targetLift s))
      (U V : Set H2) (hU : IsOpen U) (hV : IsOpen V)
      (hcU : IsConnected U) (hcV : IsConnected V)
      (hfU : frontier U=Set.range sourceLift) (hfV : frontier V=Set.range targetLift)
      (hTU : Set.range targetLift ⊆ U) (hSV : Set.range sourceLift ⊆ V)
      (hindex : originalAxisNatIndex=2)
      (hBand : Disjoint (developedDeck minimalAxisDeck.val '' closure (U∩V)) (closure (U∩V))) :
      ∃ B : C(Circle × Interval,E), Topology.IsEmbedding B ∧
        Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))=a.image ∧
        Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))=b.image ∧
        IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
    have connected_facing_side_unique {X : Type} [TopologicalSpace X] (F J A B U : Set X)
        (hA : IsOpen A) (hB : IsOpen B) (hcA : IsConnected A)
        (hd : Disjoint A B) (hp : A∪B=Fᶜ)
        (hJ : J.Nonempty) (hJA : J ⊆ A)
        (hU : IsOpen U) (hcU : IsConnected U) (hfU : frontier U=F) (hJU : J ⊆ U) :
        U=A := by
      have hUF : Disjoint U F := by
        apply Set.disjoint_left.mpr
        intro z hz hF
        have hfz : z∈frontier U := hfU.symm ▸ hF
        rw [hU.frontier_eq] at hfz
        exact hfz.2 hz
      have hUsides : U ⊆ A∪B := by
        rw [hp]
        intro z hz hF
        exact Set.disjoint_left.mp hUF hz hF
      have hUA : U ⊆ A := by
        rcases hcU.isPreconnected.subset_or_subset hA hB hd hUsides with h | h
        · exact h
        · obtain ⟨z,hz⟩ := hJ
          exact False.elim (Set.disjoint_left.mp hd (hJA hz) (h (hJU hz)))
      have hAavoid : A ⊆ Fᶜ := fun z hz => hp ▸ Or.inl hz
      have hCl : closure U=U∪F := by rw [closure_eq_self_union_frontier,hfU]
      have hApart : A ⊆ U∪(closure U)ᶜ := by
        intro z hz
        by_cases hu : z∈U
        · exact Or.inl hu
        · right
          rw [hCl]
          rintro (h | h)
          · exact hu h
          · exact hAavoid hz h
      have hUComp : Disjoint U (closure U)ᶜ := Set.disjoint_left.mpr (fun z hu hc => hc (subset_closure hu))
      have hAU : A ⊆ U := by
        rcases hcA.isPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl hUComp hApart with h | h
        · exact h
        · obtain ⟨z,hz⟩ := hJ
          exact False.elim (h (hJA hz) (subset_closure (hJU hz)))
      exact Set.Subset.antisymm hUA hAU
    have actual_targetLift_closed_embedding : Topology.IsClosedEmbedding targetLift :=
      actual_axis_periodic_curve_lift_closed_embedding developedProjection b targetLift
        (developedDeckIsometry monodromy) (developedDeckIsometry monodromy).isometry
        actualAxis hactualAxis axisPeriod haxisPeriod haxisTranslate targetLift_projection targetLift_period
    have all_developed_source_target_translates_disjoint
        (k l : deck (Sigma.fst : P → A)) :
        Disjoint ((developedDeck k) '' Set.range sourceLift)
          ((developedDeck l) '' Set.range targetLift) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨_,⟨s,rfl⟩,hs⟩ ⟨_,⟨t,rfl⟩,ht⟩
      have he : a.map (Circle.exp s) = b.map (Circle.exp t) := by
        calc
          a.map (Circle.exp s) = developedProjection (sourceLift s) :=
            (sourceLift_projection s).symm
          _ = developedProjection (developedDeck k (sourceLift s)) :=
            (developedDeck_projection k _).symm
          _ = developedProjection (developedDeck l (targetLift t)) := by rw [hs,ht]
          _ = developedProjection (targetLift t) := developedDeck_projection l _
          _ = b.map (Circle.exp t) := targetLift_projection t
      exact Set.disjoint_left.mp hdis ⟨Circle.exp s,rfl⟩ ⟨Circle.exp t,he.symm⟩
    have actual_endpoint_lifts_disjoint : Disjoint (Set.range sourceLift) (Set.range targetLift) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs⟩ ⟨t,ht⟩
      apply Set.disjoint_left.mp sourcePreimage_disjoint_target
      · change developedProjection z ∈ a.image
        rw [← hs,sourceLift_projection]
        exact Set.mem_range_self _
      · change developedProjection z ∈ b.image
        rw [← ht,targetLift_projection]
        exact Set.mem_range_self _
    obtain ⟨sourceInner,sourceOuter,hSourceInnerOpen,hSourceOuterOpen,hSourceInnerConn,hSourceOuterConn,
      hSourceSidesDisjoint,hSourceSidesPartition,hSourceInnerFrontier,hSourceOuterFrontier,hTargetInSourceInner⟩ :=
      actual_facing_line_sides sourceLift targetLift actual_sourceLift_closed_embedding actual_endpoint_lifts_disjoint
    obtain ⟨targetInner,targetOuter,hTargetInnerOpen,hTargetOuterOpen,hTargetInnerConn,hTargetOuterConn,
      hTargetSidesDisjoint,hTargetSidesPartition,hTargetInnerFrontier,hTargetOuterFrontier,hSourceInTargetInner⟩ :=
      actual_facing_line_sides targetLift sourceLift actual_targetLift_closed_embedding actual_endpoint_lifts_disjoint.symm
    have hSourceMonodromyRange := actual_periodic_lift_range_invariant sourceLift sourceLift_period
    have hTargetMonodromyRange := actual_periodic_lift_range_invariant targetLift targetLift_period
    have actual_source_facing_sides_invariant := actual_invariant_facing_side (developedDeck monodromy)
      (Set.range sourceLift) (Set.range targetLift) sourceInner sourceOuter
      hSourceInnerOpen hSourceOuterOpen hSourceInnerConn.isPreconnected hSourceSidesDisjoint
      hSourceSidesPartition ⟨targetLift 0,Set.mem_range_self 0⟩ hTargetInSourceInner
      hSourceMonodromyRange hTargetMonodromyRange
    have actual_target_facing_sides_invariant := actual_invariant_facing_side (developedDeck monodromy)
      (Set.range targetLift) (Set.range sourceLift) targetInner targetOuter
      hTargetInnerOpen hTargetOuterOpen hTargetInnerConn.isPreconnected hTargetSidesDisjoint
      hTargetSidesPartition ⟨sourceLift 0,Set.mem_range_self 0⟩ hSourceInTargetInner
      hTargetMonodromyRange hSourceMonodromyRange
    let facingRegion : Set H2 := sourceInner ∩ targetInner
    have actual_facing_region_geometry : IsOpen facingRegion ∧ facingRegion.Nonempty ∧
        frontier facingRegion = Set.range sourceLift ∪ Set.range targetLift :=
      actual_between_region_frontier sourceInner targetInner (Set.range sourceLift)
        (Set.range targetLift) hSourceInnerOpen hTargetInnerOpen
        hSourceInnerFrontier hTargetInnerFrontier hSourceInTargetInner hTargetInSourceInner
        ⟨sourceLift 0,Set.mem_range_self 0⟩
    have actual_facing_region_monodromy : developedDeck monodromy '' facingRegion = facingRegion := by
      dsimp [facingRegion]
      rw [Set.image_inter (developedDeck monodromy).injective,
        actual_source_facing_sides_invariant.1,actual_target_facing_sides_invariant.1]
    have actual_monodromy_cannot_reverse_source_sides :
        ¬ Set.MapsTo (developedDeck monodromy) sourceInner sourceOuter := by
      intro hflip
      have hx := hTargetInSourceInner (Set.mem_range_self (0:ℝ))
      have hy : developedDeck monodromy (targetLift 0) ∈ sourceInner := by
        rw [← targetLift_period]
        exact hTargetInSourceInner (Set.mem_range_self _)
      exact Set.disjoint_left.mp hSourceSidesDisjoint hy (hflip hx)
    obtain ⟨facingSeamSource,hFacingSeamSource,facingSeamTarget,hFacingSeamTarget,
      hFacingSeamDistance,hFacingSeamMinimum⟩ := actual_periodic_closed_line_shortest_connector
        sourceLift targetLift (developedDeckIsometry monodromy) (2*Real.pi) (by positivity)
        sourceLift_period targetLift_period actual_targetLift_closed_embedding.isClosed_range
        actual_endpoint_lifts_disjoint
    have hFacingSeamEndpoints : facingSeamSource ≠ facingSeamTarget := dist_pos.mp hFacingSeamDistance
    obtain ⟨facingSeam,hFacingSeamContinuous,hFacingSeamInjective,hFacingSeam0,hFacingSeam1,hFacingSeamRange⟩ :=
      metric_segment_has_parametrization facingSeamSource facingSeamTarget hFacingSeamEndpoints
    have hFacingSeamAdd (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
        dist facingSeamSource (facingSeam t) + dist (facingSeam t) facingSeamTarget =
          dist facingSeamSource facingSeamTarget := by
      have hh : facingSeam t ∈ facingSeam '' Set.Icc 0 1 := ⟨t,ht,rfl⟩
      rwa [hFacingSeamRange] at hh
    have hFacingSeamAvoid (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
        facingSeam t ∉ Set.range sourceLift ∧ facingSeam t ∉ Set.range targetLift := by
      have hti : t ∈ Set.Icc 0 1 := ⟨ht.1.le,ht.2.le⟩
      apply actual_shortest_connector_interior_avoids_boundaries (Set.range sourceLift)
        (Set.range targetLift) facingSeamSource facingSeamTarget (facingSeam t)
        hFacingSeamMinimum hFacingSeamSource hFacingSeamTarget (hFacingSeamAdd t hti)
      · intro he
        have hh := hFacingSeamInjective (by simp) hti (hFacingSeam0.trans he)
        linarith [ht.1]
      · intro he
        have hh := hFacingSeamInjective hti (by simp) (he.trans hFacingSeam1.symm)
        linarith [ht.2]
    let facingSeamMap : C(ℝ,H2) := ⟨facingSeam,hFacingSeamContinuous⟩
    have actual_compatible_seam_in_facing_region : facingSeam '' Set.Ioo 0 1 ⊆ facingRegion := by
      have hSourceSide := actual_clear_path_in_facing_side facingSeamMap
        (Set.range sourceLift) sourceInner sourceOuter hSourceInnerOpen hSourceOuterOpen
        hSourceSidesDisjoint hSourceSidesPartition (fun t ht => (hFacingSeamAvoid t ht).1)
        1 (by norm_num) (by change facingSeam 1 ∈ sourceInner
                            rw [hFacingSeam1]; exact hTargetInSourceInner hFacingSeamTarget)
      have hTargetSide := actual_clear_path_in_facing_side facingSeamMap
        (Set.range targetLift) targetInner targetOuter hTargetInnerOpen hTargetOuterOpen
        hTargetSidesDisjoint hTargetSidesPartition (fun t ht => (hFacingSeamAvoid t ht).2)
        0 (by norm_num) (by change facingSeam 0 ∈ targetInner
                            rw [hFacingSeam0]; exact hSourceInTargetInner hFacingSeamSource)
      exact Set.subset_inter hSourceSide hTargetSide
    have actual_compatible_seam_stabilizer_translate_disjoint
        (k : deck (Sigma.fst : P → A)) (hk : k ≠ 1)
        (hkSource : developedDeck k '' Set.range sourceLift = Set.range sourceLift)
        (hkTarget : developedDeck k '' Set.range targetLift = Set.range targetLift) :
        Disjoint (facingSeam '' Set.Icc 0 1)
          (developedDeck k '' (facingSeam '' Set.Icc 0 1)) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨t,ht,htz⟩ ⟨_,⟨r,hr,rfl⟩,hrz⟩
      have hxk : developedDeck k facingSeamSource ∈ Set.range sourceLift :=
        hkSource ▸ Set.mem_image_of_mem _ hFacingSeamSource
      have hyk : developedDeck k facingSeamTarget ∈ Set.range targetLift :=
        hkTarget ▸ Set.mem_image_of_mem _ hFacingSeamTarget
      have hadd1 : dist facingSeamSource z + dist z facingSeamTarget = dist facingSeamSource facingSeamTarget := by
        rw [← htz]
        exact hFacingSeamAdd t ht
      have hadd2 : dist (developedDeck k facingSeamSource) z +
          dist z (developedDeck k facingSeamTarget) = dist facingSeamSource facingSeamTarget := by
        rw [← hrz]
        rw [(all_developed_decks_isometric k).dist_eq,
          (all_developed_decks_isometric k).dist_eq]
        exact hFacingSeamAdd r hr
      have hcross1 := hFacingSeamMinimum facingSeamSource hFacingSeamSource (developedDeck k facingSeamTarget) hyk
      have hcross2 := hFacingSeamMinimum (developedDeck k facingSeamSource) hxk facingSeamTarget hFacingSeamTarget
      have htri1 := dist_triangle facingSeamSource z (developedDeck k facingSeamTarget)
      have htri2 := dist_triangle (developedDeck k facingSeamSource) z facingSeamTarget
      have hleft : dist facingSeamSource z = dist (developedDeck k facingSeamSource) z := by
        linarith
      have hright : dist z facingSeamTarget = dist z (developedDeck k facingSeamTarget) := by
        linarith
      have hcrossdist : dist facingSeamSource (developedDeck k facingSeamTarget) =
          dist facingSeamSource facingSeamTarget := by linarith
      by_cases hxz : facingSeamSource = z
      · have he : developedDeck k facingSeamSource = z := by
          apply dist_eq_zero.mp
          rw [← hleft,← hxz]
          exact dist_self _
        exact hk (all_developed_decks_fixed_implies_one k facingSeamSource (he.trans hxz.symm))
      · have hcrossadd : dist facingSeamSource z + dist z (developedDeck k facingSeamTarget) =
            dist facingSeamSource (developedDeck k facingSeamTarget) := by linarith
        have he := actual_h2_geodesic_continuation_unique facingSeamSource z facingSeamTarget
          (developedDeck k facingSeamTarget) hxz hadd1 hcrossadd hcrossdist.symm
        exact hk (all_developed_decks_fixed_implies_one k facingSeamTarget he.symm)
    have actual_facing_seam_disjoint_monodromy :=
      actual_compatible_seam_stabilizer_translate_disjoint monodromy monodromy_ne_one
        hSourceMonodromyRange hTargetMonodromyRange
    have hFacingBoundaryIntersections := actual_clear_seam_boundary_intersections facingSeam
      (Set.range sourceLift) (Set.range targetLift) actual_endpoint_lifts_disjoint
      (hFacingSeam0.symm ▸ hFacingSeamSource) (hFacingSeam1.symm ▸ hFacingSeamTarget) hFacingSeamAvoid
    have hShiftedSeamSourceIntersection
        (z : H2) (hz : z ∈ developedDeck monodromy '' (facingSeam '' Set.Icc 0 1))
        (hF : z ∈ Set.range sourceLift) : z = developedDeck monodromy facingSeamSource := by
      obtain ⟨u,hu,rfl⟩ := hz
      have huF := (monodromy_range_membership _ hSourceMonodromyRange u).mp hF
      have he := (hFacingBoundaryIntersections.1 u hu huF).trans hFacingSeam0
      exact congrArg (developedDeck monodromy) he
    have hShiftedSeamTargetIntersection
        (z : H2) (hz : z ∈ developedDeck monodromy '' (facingSeam '' Set.Icc 0 1))
        (hJ : z ∈ Set.range targetLift) : z = developedDeck monodromy facingSeamTarget := by
      obtain ⟨u,hu,rfl⟩ := hz
      have huJ := (monodromy_range_membership _ hTargetMonodromyRange u).mp hJ
      have he := (hFacingBoundaryIntersections.2 u hu huJ).trans hFacingSeam1
      exact congrArg (developedDeck monodromy) he
    obtain ⟨sourceParameter,hSourceParameter⟩ := hFacingSeamSource
    obtain ⟨targetParameter,hTargetParameter⟩ := hFacingSeamTarget
    let sourceArc : Set H2 := sourceLift '' Set.Icc sourceParameter (sourceParameter+2*Real.pi)
    let targetArc : Set H2 := targetLift '' Set.Icc targetParameter (targetParameter+2*Real.pi)
    let firstSeam : Set H2 := facingSeam '' Set.Icc 0 1
    let secondSeam : Set H2 := developedDeck monodromy '' firstSeam
    have hSourceArcSubset : sourceArc ⊆ Set.range sourceLift := by
      rintro _ ⟨s,hs,rfl⟩; exact Set.mem_range_self _
    have hTargetArcSubset : targetArc ⊆ Set.range targetLift := by
      rintro _ ⟨s,hs,rfl⟩; exact Set.mem_range_self _
    let sourcePlaneMap : C(ℝ,Schoenflies.Plane) :=
      ⟨planeCoordinate ∘ sourceLift,planeCoordinate.continuous.comp sourceLift.continuous⟩
    let targetPlaneMap : C(ℝ,Schoenflies.Plane) :=
      ⟨planeCoordinate ∘ targetLift,planeCoordinate.continuous.comp targetLift.continuous⟩
    have hSourceArcPlane : Schoenflies.IsArcBetween (planeCoordinate '' sourceArc)
        (planeCoordinate facingSeamSource) (planeCoordinate (developedDeck monodromy facingSeamSource)) := by
      have h := continuous_injective_interval_isArcBetween sourcePlaneMap
        (planeCoordinate.injective.comp actual_sourceLift_closed_embedding.injective)
        (show sourceParameter < sourceParameter+2*Real.pi by linarith [Real.pi_pos])
      have hEnd : sourceLift (sourceParameter+2*Real.pi) = developedDeck monodromy facingSeamSource := by
        rw [sourceLift_period,hSourceParameter]
      simpa only [sourcePlaneMap,ContinuousMap.coe_mk,Function.comp_def,sourceArc,
        Set.image_image,hSourceParameter,hEnd] using h
    have hTargetArcPlane : Schoenflies.IsArcBetween (planeCoordinate '' targetArc)
        (planeCoordinate facingSeamTarget) (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
      have h := continuous_injective_interval_isArcBetween targetPlaneMap
        (planeCoordinate.injective.comp actual_targetLift_closed_embedding.injective)
        (show targetParameter < targetParameter+2*Real.pi by linarith [Real.pi_pos])
      have hEnd : targetLift (targetParameter+2*Real.pi) = developedDeck monodromy facingSeamTarget := by
        rw [targetLift_period,hTargetParameter]
      simpa only [targetPlaneMap,ContinuousMap.coe_mk,Function.comp_def,targetArc,
        Set.image_image,hTargetParameter,hEnd] using h
    have hFirstSeamPlane : Schoenflies.IsArcBetween (planeCoordinate '' firstSeam)
        (planeCoordinate facingSeamSource) (planeCoordinate facingSeamTarget) := by
      refine ⟨planeCoordinate ∘ facingSeam,?_,?_,?_,?_,?_⟩
      · exact (planeCoordinate.continuous.comp hFacingSeamContinuous).continuousOn
      · intro s hs t ht he
        exact hFacingSeamInjective hs ht (planeCoordinate.injective he)
      · change (planeCoordinate ∘ facingSeam) '' Set.Icc 0 1 =
          planeCoordinate '' (facingSeam '' Set.Icc 0 1)
        rw [Set.image_image]
        rfl
      · change planeCoordinate (facingSeam 0) = _
        rw [hFacingSeam0]
      · change planeCoordinate (facingSeam 1) = _
        rw [hFacingSeam1]
    have hSecondSeamPlane : Schoenflies.IsArcBetween (planeCoordinate '' secondSeam)
        (planeCoordinate (developedDeck monodromy facingSeamSource))
        (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
      refine ⟨fun s => planeCoordinate (developedDeck monodromy (facingSeam s)),?_,?_,?_,?_,?_⟩
      · exact (planeCoordinate.continuous.comp
          ((developedDeck monodromy).continuous.comp hFacingSeamContinuous)).continuousOn
      · intro s hs t ht he
        exact hFacingSeamInjective hs ht
          ((developedDeck monodromy).injective (planeCoordinate.injective he))
      · change (fun s => planeCoordinate (developedDeck monodromy (facingSeam s))) '' Set.Icc 0 1 =
          planeCoordinate '' (developedDeck monodromy '' (facingSeam '' Set.Icc 0 1))
        rw [Set.image_image,Set.image_image]
      · change planeCoordinate (developedDeck monodromy (facingSeam 0)) = _
        rw [hFacingSeam0]
      · change planeCoordinate (developedDeck monodromy (facingSeam 1)) = _
        rw [hFacingSeam1]
    have hSourceSecondMeet (z : Schoenflies.Plane) (hzP : z ∈ planeCoordinate '' sourceArc)
        (hzR : z ∈ planeCoordinate '' secondSeam) :
        z = planeCoordinate (developedDeck monodromy facingSeamSource) := by
      obtain ⟨u,hu,huz⟩ := hzP
      obtain ⟨v,hv,hvz⟩ := hzR
      have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
      have hvF : v ∈ Set.range sourceLift := huv ▸ hSourceArcSubset hu
      have hvEq := hShiftedSeamSourceIntersection v hv hvF
      exact hvz.symm.trans (congrArg planeCoordinate hvEq)
    have hFirstTargetMeet (z : Schoenflies.Plane) (hzE : z ∈ planeCoordinate '' firstSeam)
        (hzQ : z ∈ planeCoordinate '' targetArc) : z = planeCoordinate facingSeamTarget := by
      obtain ⟨u,hu,huz⟩ := hzE
      obtain ⟨v,hv,hvz⟩ := hzQ
      have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
      have huJ : u ∈ Set.range targetLift := huv.symm ▸ hTargetArcSubset hv
      have huEq := (hFacingBoundaryIntersections.2 u hu huJ).trans hFacingSeam1
      exact huz.symm.trans (congrArg planeCoordinate huEq)
    have hSourceFirstMeet (z : Schoenflies.Plane) (hzP : z ∈ planeCoordinate '' sourceArc)
        (hzE : z ∈ planeCoordinate '' firstSeam) : z = planeCoordinate facingSeamSource := by
      obtain ⟨u,hu,huz⟩ := hzP
      obtain ⟨v,hv,hvz⟩ := hzE
      have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
      have hvF : v ∈ Set.range sourceLift := huv ▸ hSourceArcSubset hu
      have hvEq := (hFacingBoundaryIntersections.1 v hv hvF).trans hFacingSeam0
      exact hvz.symm.trans (congrArg planeCoordinate hvEq)
    have hSecondTargetMeet (z : Schoenflies.Plane) (hzR : z ∈ planeCoordinate '' secondSeam)
        (hzQ : z ∈ planeCoordinate '' targetArc) :
        z = planeCoordinate (developedDeck monodromy facingSeamTarget) := by
      obtain ⟨u,hu,huz⟩ := hzR
      obtain ⟨v,hv,hvz⟩ := hzQ
      have huv : u = v := planeCoordinate.injective (huz.trans hvz.symm)
      have huJ : u ∈ Set.range targetLift := huv.symm ▸ hTargetArcSubset hv
      have huEq := hShiftedSeamTargetIntersection u hu huJ
      exact huz.symm.trans (congrArg planeCoordinate huEq)
    have hSourceTargetArcDisjoint : Disjoint (planeCoordinate '' sourceArc) (planeCoordinate '' targetArc) :=
      (actual_endpoint_lifts_disjoint.mono hSourceArcSubset hTargetArcSubset).image
        planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
    have hSecondFirstSeamDisjoint : Disjoint (planeCoordinate '' secondSeam) (planeCoordinate '' firstSeam) :=
      actual_facing_seam_disjoint_monodromy.symm.image
        planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
    let fundamentalBoundary : Set Schoenflies.Plane :=
      ((planeCoordinate '' sourceArc) ∪ (planeCoordinate '' secondSeam)) ∪
        ((planeCoordinate '' firstSeam) ∪ (planeCoordinate '' targetArc))
    have actual_fundamental_boundary_jordan : Schoenflies.IsJordanCurve fundamentalBoundary := by
      have hfirst := hSourceArcPlane.concatenate hSecondSeamPlane hSourceSecondMeet
      have hsecond := hFirstSeamPlane.concatenate hTargetArcPlane hFirstTargetMeet
      apply Schoenflies.IsJordanCurve.of_two_arcs hfirst hsecond.reverse
      intro z hz hz'
      rcases hz with hzP | hzR <;> rcases hz' with hzE | hzQ
      · exact Or.inl (hSourceFirstMeet z hzP hzE)
      · exact False.elim (Set.disjoint_left.mp hSourceTargetArcDisjoint hzP hzQ)
      · exact False.elim (Set.disjoint_left.mp hSecondFirstSeamDisjoint hzR hzE)
      · exact Or.inr (hSecondTargetMeet z hzR hzQ)
    let markedSourceEdge (u : Interval) : Schoenflies.Plane :=
      planeCoordinate (sourceLift (sourceParameter + (u:ℝ)*(2*Real.pi)))
    let markedTargetEdge (u : Interval) : Schoenflies.Plane :=
      planeCoordinate (targetLift (targetParameter + (u:ℝ)*(2*Real.pi)))
    let markedFirstSeam (u : Interval) : Schoenflies.Plane := planeCoordinate (facingSeam u)
    let markedSecondSeam (u : Interval) : Schoenflies.Plane :=
      planeCoordinate (developedDeck monodromy (facingSeam u))
    have hMarkedSourceEmbedding : Topology.IsEmbedding markedSourceEdge :=
      planeCoordinate.isEmbedding.comp (actual_sourceLift_closed_embedding.isEmbedding.comp
        (actual_affine_interval_embedding sourceParameter))
    have hMarkedTargetEmbedding : Topology.IsEmbedding markedTargetEdge :=
      planeCoordinate.isEmbedding.comp (actual_targetLift_closed_embedding.isEmbedding.comp
        (actual_affine_interval_embedding targetParameter))
    have hMarkedFirstEmbedding : Topology.IsEmbedding markedFirstSeam := by
      refine ((show Continuous markedFirstSeam from
        planeCoordinate.continuous.comp (hFacingSeamContinuous.comp continuous_subtype_val)).isClosedEmbedding ?_).isEmbedding
      intro u v h
      apply Subtype.ext
      exact hFacingSeamInjective u.property v.property (planeCoordinate.injective h)
    have hMarkedSecondEmbedding : Topology.IsEmbedding markedSecondSeam := by
      refine ((show Continuous markedSecondSeam from planeCoordinate.continuous.comp
        ((developedDeck monodromy).continuous.comp
          (hFacingSeamContinuous.comp continuous_subtype_val))).isClosedEmbedding ?_).isEmbedding
      intro u v h
      apply Subtype.ext
      exact hFacingSeamInjective u.property v.property
        ((developedDeck monodromy).injective (planeCoordinate.injective h))
    have hMarkedSource0 : markedSourceEdge 0 = planeCoordinate facingSeamSource := by
      simp [markedSourceEdge,hSourceParameter]
    have hMarkedSource1 : markedSourceEdge 1 = planeCoordinate (developedDeck monodromy facingSeamSource) := by
      simp only [markedSourceEdge]
      simp
      rw [sourceLift_period,hSourceParameter]
    have hMarkedTarget0 : markedTargetEdge 0 = planeCoordinate facingSeamTarget := by
      simp [markedTargetEdge,hTargetParameter]
    have hMarkedTarget1 : markedTargetEdge 1 = planeCoordinate (developedDeck monodromy facingSeamTarget) := by
      simp only [markedTargetEdge]
      simp
      rw [targetLift_period,hTargetParameter]
    have hMarkedFirst0 : markedFirstSeam 0 = planeCoordinate facingSeamSource := by
      change planeCoordinate (facingSeam 0) = _; rw [hFacingSeam0]
    have hMarkedFirst1 : markedFirstSeam 1 = planeCoordinate facingSeamTarget := by
      change planeCoordinate (facingSeam 1) = _; rw [hFacingSeam1]
    have hMarkedSecond0 : markedSecondSeam 0 = planeCoordinate (developedDeck monodromy facingSeamSource) := by
      change planeCoordinate (developedDeck monodromy (facingSeam 0)) = _; rw [hFacingSeam0]
    have hMarkedSecond1 : markedSecondSeam 1 = planeCoordinate (developedDeck monodromy facingSeamTarget) := by
      change planeCoordinate (developedDeck monodromy (facingSeam 1)) = _; rw [hFacingSeam1]
    have hMarkedSourceMem (u : Interval) : markedSourceEdge u ∈ planeCoordinate '' sourceArc := by
      refine ⟨_,⟨_,?_,rfl⟩,rfl⟩
      constructor <;> nlinarith [u.property.1,u.property.2,Real.pi_pos]
    have hMarkedTargetMem (u : Interval) : markedTargetEdge u ∈ planeCoordinate '' targetArc := by
      refine ⟨_,⟨_,?_,rfl⟩,rfl⟩
      constructor <;> nlinarith [u.property.1,u.property.2,Real.pi_pos]
    have hMarkedFirstMem (u : Interval) : markedFirstSeam u ∈ planeCoordinate '' firstSeam :=
      ⟨_,⟨u,u.property,rfl⟩,rfl⟩
    have hMarkedSecondMem (u : Interval) : markedSecondSeam u ∈ planeCoordinate '' secondSeam :=
      ⟨_,⟨_,⟨u,u.property,rfl⟩,rfl⟩,rfl⟩
    obtain ⟨markedFundamentalDisk,hMarkedFundamentalDiskEmbedding,
        hMarkedFundamentalBottom,hMarkedFundamentalTop,
        hMarkedFundamentalLeft,hMarkedFundamentalRight⟩ :=
      CurveComplex.G3Review.actual_four_arc_cycle_has_prescribed_embedded_square
        markedSourceEdge markedTargetEdge markedFirstSeam markedSecondSeam
        hMarkedSourceEmbedding hMarkedTargetEmbedding hMarkedFirstEmbedding hMarkedSecondEmbedding
        (hMarkedSource0.trans hMarkedFirst0.symm) (hMarkedSource1.trans hMarkedSecond0.symm)
        (hMarkedTarget0.trans hMarkedFirst1.symm) (hMarkedTarget1.trans hMarkedSecond1.symm)
        (by intro s t h
            have he := hSourceFirstMeet _ (hMarkedSourceMem s) (h ▸ hMarkedFirstMem t)
            exact ⟨hMarkedSourceEmbedding.injective (he.trans hMarkedSource0.symm),
              hMarkedFirstEmbedding.injective (h.symm.trans (he.trans hMarkedFirst0.symm))⟩)
        (by intro s t h
            have he := hSourceSecondMeet _ (hMarkedSourceMem s) (h ▸ hMarkedSecondMem t)
            exact ⟨hMarkedSourceEmbedding.injective (he.trans hMarkedSource1.symm),
              hMarkedSecondEmbedding.injective (h.symm.trans (he.trans hMarkedSecond0.symm))⟩)
        (by intro s t h
            have he := hFirstTargetMeet _ (h ▸ hMarkedFirstMem t) (hMarkedTargetMem s)
            exact ⟨hMarkedTargetEmbedding.injective (he.trans hMarkedTarget0.symm),
              hMarkedFirstEmbedding.injective (h.symm.trans (he.trans hMarkedFirst1.symm))⟩)
        (by intro s t h
            have he := hSecondTargetMeet _ (h ▸ hMarkedSecondMem t) (hMarkedTargetMem s)
            exact ⟨hMarkedTargetEmbedding.injective (he.trans hMarkedTarget1.symm),
              hMarkedSecondEmbedding.injective (h.symm.trans (he.trans hMarkedSecond1.symm))⟩)
        (hSourceTargetArcDisjoint.mono (Set.range_subset_iff.mpr hMarkedSourceMem)
          (Set.range_subset_iff.mpr hMarkedTargetMem))
        (hSecondFirstSeamDisjoint.symm.mono (Set.range_subset_iff.mpr hMarkedFirstMem)
          (Set.range_subset_iff.mpr hMarkedSecondMem))
    have actual_marked_fundamental_seam_compatibility (v : Interval) :
        markedFundamentalDisk (1,v) =
          planeCoordinate (developedDeck monodromy (planeCoordinate.symm (markedFundamentalDisk (0,v)))) := by
      rw [hMarkedFundamentalRight,hMarkedFundamentalLeft]
      simp only [markedFirstSeam,markedSecondSeam,Homeomorph.symm_apply_apply]
    have actual_affine_period_arc_range (F : ℝ → H2) (p : ℝ) :
        Set.range (fun u : Interval => F (p+(u:ℝ)*(2*Real.pi))) =
          F '' Set.Icc p (p+2*Real.pi) := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        refine ⟨_,?_,rfl⟩
        constructor <;> nlinarith [u.property.1,u.property.2,Real.pi_pos]
      · rintro ⟨s,hs,rfl⟩
        let u : Interval := ⟨(s-p)/(2*Real.pi),by
          constructor
          · exact div_nonneg (sub_nonneg.mpr hs.1) (by positivity)
          · apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
            linarith [hs.2]⟩
        refine ⟨u,?_⟩
        congr 1
        dsimp [u]
        field_simp
        ring
    have hMarkedSourceRange : Set.range markedSourceEdge = planeCoordinate '' sourceArc := by
      change Set.range (planeCoordinate ∘ (fun u : Interval => sourceLift (sourceParameter+(u:ℝ)*(2*Real.pi)))) = _
      rw [Set.range_comp,actual_affine_period_arc_range]
    have hMarkedTargetRange : Set.range markedTargetEdge = planeCoordinate '' targetArc := by
      change Set.range (planeCoordinate ∘ (fun u : Interval => targetLift (targetParameter+(u:ℝ)*(2*Real.pi)))) = _
      rw [Set.range_comp,actual_affine_period_arc_range]
    have hMarkedFirstRange : Set.range markedFirstSeam = planeCoordinate '' firstSeam := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩;exact hMarkedFirstMem u
      · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩;exact ⟨⟨t,ht⟩,rfl⟩
    have hMarkedSecondRange : Set.range markedSecondSeam = planeCoordinate '' secondSeam := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩;exact hMarkedSecondMem u
      · rintro ⟨_,⟨_,⟨t,ht,rfl⟩,rfl⟩,rfl⟩;exact ⟨⟨t,ht⟩,rfl⟩
    let markedSquareBoundary : Set (Interval × Interval) :=
      {uv | uv.1 = 0 ∨ uv.1 = 1 ∨ uv.2 = 0 ∨ uv.2 = 1}
    have actual_marked_fundamental_boundary_image :
        markedFundamentalDisk '' markedSquareBoundary = fundamentalBoundary := by
      have he : markedFundamentalDisk '' markedSquareBoundary =
          (Set.range markedSourceEdge ∪ Set.range markedSecondSeam) ∪
          (Set.range markedFirstSeam ∪ Set.range markedTargetEdge) := by
        ext z
        constructor
        · rintro ⟨uv,huv,rfl⟩
          rcases huv with hl | hr | hb | ht
          · exact Or.inr (Or.inl ⟨uv.2,by rw [show uv = (0,uv.2) from Prod.ext hl rfl]; exact (hMarkedFundamentalLeft uv.2).symm⟩)
          · exact Or.inl (Or.inr ⟨uv.2,by rw [show uv = (1,uv.2) from Prod.ext hr rfl]; exact (hMarkedFundamentalRight uv.2).symm⟩)
          · exact Or.inl (Or.inl ⟨uv.1,by rw [show uv = (uv.1,0) from Prod.ext rfl hb]; exact (hMarkedFundamentalBottom uv.1).symm⟩)
          · exact Or.inr (Or.inr ⟨uv.1,by rw [show uv = (uv.1,1) from Prod.ext rfl ht]; exact (hMarkedFundamentalTop uv.1).symm⟩)
        · rintro ((⟨u,rfl⟩|⟨v,rfl⟩)|(⟨v,rfl⟩|⟨u,rfl⟩))
          · exact ⟨(u,0),Or.inr (Or.inr (Or.inl rfl)),hMarkedFundamentalBottom u⟩
          · exact ⟨(1,v),Or.inr (Or.inl rfl),hMarkedFundamentalRight v⟩
          · exact ⟨(0,v),Or.inl rfl,hMarkedFundamentalLeft v⟩
          · exact ⟨(u,1),Or.inr (Or.inr (Or.inr rfl)),hMarkedFundamentalTop u⟩
      rw [he,hMarkedSourceRange,hMarkedTargetRange,hMarkedFirstRange,hMarkedSecondRange]
    have actual_marked_fundamental_disk_closed_carrier :
        Set.range markedFundamentalDisk = Schoenflies.inside fundamentalBoundary ∪ fundamentalBoundary :=
      actual_embedded_square_closed_carrier markedFundamentalDisk hMarkedFundamentalDiskEmbedding
        fundamentalBoundary actual_fundamental_boundary_jordan actual_marked_fundamental_boundary_image
    obtain ⟨fundamentalDisk,hFundamentalDiskEmbedding,hFundamentalDiskBoundary⟩ :=
      CurveComplex.exists_embedded_square_disc_of_jordan actual_fundamental_boundary_jordan
    have actual_proper_line_side_unbounded (K : C(ℝ,Schoenflies.Plane))
        (hK : IsProperMap K) (V : Set Schoenflies.Plane) (hfront : frontier V = Set.range K) :
        ¬ Bornology.IsBounded V := by
      intro hbounded
      have hcompactLine : IsCompact (Set.range K) := by
        rw [← hfront]
        exact hbounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
      have hcompactPreimage := hK.isCompact_preimage hcompactLine
      have hcompactReal : IsCompact (Set.univ : Set ℝ) := by
        convert hcompactPreimage using 1
        ext x
        simp
      obtain ⟨M,hM⟩ := hcompactReal.bddAbove
      have hh : M+1 ≤ M := hM (Set.mem_univ _)
      linarith
    have hFirstSeamFacingClosure : firstSeam ⊆ closure facingRegion := by
      rintro _ ⟨t,ht,rfl⟩
      have htclosure : t ∈ closure (Set.Ioo (0:ℝ) 1) := by
        rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
        exact ht
      exact closure_mono actual_compatible_seam_in_facing_region
        (mem_closure_image hFacingSeamContinuous.continuousAt htclosure)
    have hSecondSeamFacingClosure : secondSeam ⊆ closure facingRegion := by
      have hmono := Set.image_mono hFirstSeamFacingClosure (f := developedDeck monodromy)
      rw [(developedDeck monodromy).image_closure,actual_facing_region_monodromy] at hmono
      exact hmono
    have hClosureFacingSource : closure facingRegion ⊆ sourceInner ∪ Set.range sourceLift := by
      have hh := closure_mono (Set.inter_subset_left : facingRegion ⊆ sourceInner)
      rw [closure_eq_self_union_frontier sourceInner,hSourceInnerFrontier] at hh
      exact hh
    have hClosureFacingTarget : closure facingRegion ⊆ targetInner ∪ Set.range targetLift := by
      have hh := closure_mono (Set.inter_subset_right : facingRegion ⊆ targetInner)
      rw [closure_eq_self_union_frontier targetInner,hTargetInnerFrontier] at hh
      exact hh
    have hFundamentalBoundarySourceSide : fundamentalBoundary ⊆
        (planeCoordinate '' sourceInner) ∪ (planeCoordinate '' Set.range sourceLift) := by
      rintro z ((⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩) | (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩))
      · exact Or.inr (Set.mem_image_of_mem _ (hSourceArcSubset hx))
      · rw [← Set.image_union]
        exact Set.mem_image_of_mem _ (hClosureFacingSource (hSecondSeamFacingClosure hx))
      · rw [← Set.image_union]
        exact Set.mem_image_of_mem _ (hClosureFacingSource (hFirstSeamFacingClosure hx))
      · exact Or.inl (Set.mem_image_of_mem _ (hTargetInSourceInner (hTargetArcSubset hx)))
    have hFundamentalBoundaryTargetSide : fundamentalBoundary ⊆
        (planeCoordinate '' targetInner) ∪ (planeCoordinate '' Set.range targetLift) := by
      rintro z ((⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩) | (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩))
      · exact Or.inl (Set.mem_image_of_mem _ (hSourceInTargetInner (hSourceArcSubset hx)))
      · rw [← Set.image_union]
        exact Set.mem_image_of_mem _ (hClosureFacingTarget (hSecondSeamFacingClosure hx))
      · rw [← Set.image_union]
        exact Set.mem_image_of_mem _ (hClosureFacingTarget (hFirstSeamFacingClosure hx))
      · exact Or.inr (Set.mem_image_of_mem _ (hTargetArcSubset hx))
    have hSourcePlaneRange : planeCoordinate '' Set.range sourceLift = Set.range sourcePlaneMap := by
      change planeCoordinate '' Set.range sourceLift = Set.range (planeCoordinate ∘ sourceLift)
      rw [Set.range_comp]
    have hTargetPlaneRange : planeCoordinate '' Set.range targetLift = Set.range targetPlaneMap := by
      change planeCoordinate '' Set.range targetLift = Set.range (planeCoordinate ∘ targetLift)
      rw [Set.range_comp]
    have hSourceOuterPlaneFrontier : frontier (planeCoordinate '' sourceOuter) = Set.range sourcePlaneMap := by
      rw [← planeCoordinate.image_frontier,hSourceOuterFrontier,hSourcePlaneRange]
    have hTargetOuterPlaneFrontier : frontier (planeCoordinate '' targetOuter) = Set.range targetPlaneMap := by
      rw [← planeCoordinate.image_frontier,hTargetOuterFrontier,hTargetPlaneRange]
    have hSourceOuterPlaneUnbounded := actual_proper_line_side_unbounded sourcePlaneMap
      (planeCoordinate.isClosedEmbedding.comp actual_sourceLift_closed_embedding).isProperMap
      (planeCoordinate '' sourceOuter) hSourceOuterPlaneFrontier
    have hTargetOuterPlaneUnbounded := actual_proper_line_side_unbounded targetPlaneMap
      (planeCoordinate.isClosedEmbedding.comp actual_targetLift_closed_embedding).isProperMap
      (planeCoordinate '' targetOuter) hTargetOuterPlaneFrontier
    have hInsideSourceSide : Schoenflies.inside fundamentalBoundary ⊆ planeCoordinate '' sourceInner := by
      apply jordan_inside_contained_in_proper_line_side actual_fundamental_boundary_jordan
        (planeCoordinate.isOpenMap _ hSourceInnerOpen) (planeCoordinate.isOpenMap _ hSourceOuterOpen)
        (hSourceOuterConn.image _ planeCoordinate.continuous.continuousOn)
        (hSourceSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
      · rw [← Set.image_union,hSourceSidesPartition,planeCoordinate.image_compl]
      · rw [← planeCoordinate.image_frontier,hSourceOuterFrontier]
      · exact hSourceOuterPlaneUnbounded
      · exact hFundamentalBoundarySourceSide
    have hInsideTargetSide : Schoenflies.inside fundamentalBoundary ⊆ planeCoordinate '' targetInner := by
      apply jordan_inside_contained_in_proper_line_side actual_fundamental_boundary_jordan
        (planeCoordinate.isOpenMap _ hTargetInnerOpen) (planeCoordinate.isOpenMap _ hTargetOuterOpen)
        (hTargetOuterConn.image _ planeCoordinate.continuous.continuousOn)
        (hTargetSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
      · rw [← Set.image_union,hTargetSidesPartition,planeCoordinate.image_compl]
      · rw [← planeCoordinate.image_frontier,hTargetOuterFrontier]
      · exact hTargetOuterPlaneUnbounded
      · exact hFundamentalBoundaryTargetSide
    have actual_fundamental_cell_inside_facing_region :
        Schoenflies.inside fundamentalBoundary ⊆ planeCoordinate '' facingRegion := by
      rw [Set.image_inter planeCoordinate.injective]
      exact Set.subset_inter hInsideSourceSide hInsideTargetSide
    have actual_same_curve_deck_overlap_reparametrizes
        (c : Curve E) (F : C(ℝ,H2))
        (hFproj : ∀ s, developedProjection (F s) = c.map (Circle.exp s))
        (k : deck (Sigma.fst : P → A)) (r s : ℝ)
        (hmeet : developedDeck k (F r) = F s) :
        ∀ u : ℝ, developedDeck k (F u) = F (u + (s-r)) := by
      have hangle : Circle.exp r = Circle.exp s := by
        apply c.embedded.injective
        rw [← hFproj, ← hFproj, ← hmeet, developedDeck_projection]
      have hangleShift (u : ℝ) : Circle.exp u = Circle.exp (u + (s-r)) := by
        obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hangle.symm
        apply Circle.exp_eq_exp.mpr
        refine ⟨-n,?_⟩
        push_cast
        linarith
      let f₁ : ℝ → P := fun u => k • development.symm (F u)
      let f₂ : ℝ → P := fun u => development.symm (F (u+(s-r)))
      have hc₁ : Continuous f₁ := (hqc.continuous_const_smul k).comp
        (development.symm.continuous.comp F.continuous)
      have hc₂ : Continuous f₂ := development.symm.continuous.comp
        (F.continuous.comp (continuous_id.add continuous_const))
      have hcomp : (Sigma.fst : P → A) ∘ f₁ = (Sigma.fst : P → A) ∘ f₂ := by
        funext u
        apply Subtype.ext
        change (k • development.symm (F u)).1.val =
          (development.symm (F (u+(s-r)))).1.val
        rw [congrArg Subtype.val (hqc.map_smul k)]
        change developedProjection (F u) = developedProjection (F (u+(s-r)))
        rw [hFproj,hFproj,hangleShift]
      have hbase : f₁ r = f₂ r := by
        apply development.injective
        change development (k • development.symm (F r)) =
          development (development.symm (F (r+(s-r))))
        rw [development.apply_symm_apply]
        change developedDeck k (F r) = F (r+(s-r))
        convert hmeet using 1 <;> congr 1 <;> ring
      have he := hqc.isCoveringMap.eq_of_comp_eq hc₁ hc₂ hcomp r hbase
      intro u
      have h := congrArg (fun f : ℝ → P => development (f u)) he
      simpa only [f₁,f₂,developedDeck,Homeomorph.trans_apply,
        development.apply_symm_apply,Subgroup.smul_def,Homeomorph.smul_def] using h
    have actual_same_curve_deck_lifts_equal_or_disjoint
        (c : Curve E) (F : C(ℝ,H2))
        (hFproj : ∀ s, developedProjection (F s) = c.map (Circle.exp s))
        (k : deck (Sigma.fst : P → A)) :
        developedDeck k '' Set.range F = Set.range F ∨
          Disjoint (developedDeck k '' Set.range F) (Set.range F) := by
      by_cases hd : Disjoint (developedDeck k '' Set.range F) (Set.range F)
      · exact Or.inr hd
      left
      obtain ⟨z,hz₁,hz₂⟩ := Set.not_disjoint_iff.mp hd
      obtain ⟨_,⟨r,rfl⟩,hr⟩ := hz₁
      obtain ⟨s,hs⟩ := hz₂
      have hparam := actual_same_curve_deck_overlap_reparametrizes c F hFproj k r s
        (hr.trans hs.symm)
      ext z
      constructor
      · rintro ⟨_,⟨u,rfl⟩,rfl⟩
        exact ⟨u+(s-r),(hparam u).symm⟩
      · rintro ⟨u,rfl⟩
        refine ⟨F (u-(s-r)),Set.mem_range_self _,?_⟩
        rw [hparam]
        congr 1
        ring
    have actual_all_source_deck_lifts_equal_or_disjoint :=
      actual_same_curve_deck_lifts_equal_or_disjoint a sourceLift sourceLift_projection
    have actual_all_target_deck_lifts_equal_or_disjoint :=
      actual_same_curve_deck_lifts_equal_or_disjoint b targetLift targetLift_projection
    have actual_developedDeck_mul (k l : deck (Sigma.fst : P → A)) (z : H2) :
        developedDeck (k*l) z = developedDeck k (developedDeck l z) := by
      simp only [developedDeck,Homeomorph.trans_apply,development.symm_apply_apply,
        Subgroup.coe_mul,Homeomorph.mul_apply]
    have actual_developedDeck_one (z : H2) : developedDeck 1 z = z := by
      simp only [developedDeck,Homeomorph.trans_apply,Subgroup.coe_one,
        Homeomorph.one_apply,development.apply_symm_apply]
    have actual_developedDeck_point_injective
        (k l : deck (Sigma.fst : P → A)) (z : H2)
        (he : developedDeck k z = developedDeck l z) : k = l := by
      letI : IsCancelSMul (deck (Sigma.fst : P → A)) P := hqc.isCancelSMul
      apply IsCancelSMul.right_cancel k l (development.symm z)
      apply development.injective
      simpa only [developedDeck,Homeomorph.trans_apply,Subgroup.smul_def,
        Homeomorph.smul_def] using he
    have actual_common_monodromy_integer_period
        (F : ℝ → H2) (hFperiod : ∀ s, F (s+2*Real.pi) = developedDeck monodromy (F s))
        (n : ℤ) : ∀ s, F (s + n*(2*Real.pi)) = developedDeck (monodromy^n) (F s) := by
      have hinvperiod (s : ℝ) : F (s-2*Real.pi) = developedDeck monodromy⁻¹ (F s) := by
        have hp := hFperiod (s-2*Real.pi)
        have harg : s-2*Real.pi+2*Real.pi = s := by ring
        rw [harg] at hp
        have hh := congrArg (developedDeck monodromy⁻¹) hp
        rw [← actual_developedDeck_mul,inv_mul_cancel,actual_developedDeck_one] at hh
        exact hh.symm
      induction n using Int.induction_on with
      | zero => intro s; simpa using (actual_developedDeck_one (F s)).symm
      | succ n ih =>
        intro s
        have harg : s + (((n : ℤ)+1 : ℤ):ℝ)*(2*Real.pi) =
            (s+2*Real.pi)+(n:ℤ)*(2*Real.pi) := by push_cast; ring
        rw [harg,ih,hFperiod,_root_.zpow_add_one,actual_developedDeck_mul]
      | pred n ih =>
        intro s
        have harg : s + ((-(n : ℤ)-1 : ℤ):ℝ)*(2*Real.pi) =
            (s-2*Real.pi)+((-(n:ℤ):ℤ):ℝ)*(2*Real.pi) := by push_cast; ring
        rw [harg,ih,hinvperiod,_root_.zpow_sub_one,actual_developedDeck_mul]
    have actual_source_integer_period := actual_common_monodromy_integer_period
      sourceLift sourceLift_period
    have actual_target_integer_period := actual_common_monodromy_integer_period
      targetLift targetLift_period
    have actual_monodromy_integer_range_invariant
        (F : ℝ → H2) (hFperiod : ∀ s, F (s+2*Real.pi) = developedDeck monodromy (F s))
        (n : ℤ) : developedDeck (monodromy^n) '' Set.range F = Set.range F := by
      have hp := actual_common_monodromy_integer_period F hFperiod n
      ext z
      constructor
      · rintro ⟨_,⟨s,rfl⟩,rfl⟩
        exact ⟨s+n*(2*Real.pi),hp s⟩
      · rintro ⟨s,rfl⟩
        refine ⟨F (s-n*(2*Real.pi)),Set.mem_range_self _,?_⟩
        rw [← hp]
        congr 1
        ring
    have actual_source_stabilizer_is_common_cyclic
        (k : deck (Sigma.fst : P → A))
        (hk : developedDeck k '' Set.range sourceLift = Set.range sourceLift) :
        ∃ n : ℤ, k = monodromy^n := by
      have hmem : developedDeck k (sourceLift 0) ∈ Set.range sourceLift :=
        hk ▸ Set.mem_image_of_mem _ (Set.mem_range_self _)
      obtain ⟨s,hs⟩ := hmem
      have he : Circle.exp s = Circle.exp 0 := by
        apply a.embedded.injective
        rw [← sourceLift_projection, ← sourceLift_projection,hs,developedDeck_projection]
      obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
      refine ⟨n,actual_developedDeck_point_injective k (monodromy^n) (sourceLift 0) ?_⟩
      rw [← actual_source_integer_period,← hn]
      exact hs.symm
    have actual_target_stabilizer_is_common_cyclic
        (k : deck (Sigma.fst : P → A))
        (hk : developedDeck k '' Set.range targetLift = Set.range targetLift) :
        ∃ n : ℤ, k = monodromy^n := by
      have hmem : developedDeck k (targetLift 0) ∈ Set.range targetLift :=
        hk ▸ Set.mem_image_of_mem _ (Set.mem_range_self _)
      obtain ⟨s,hs⟩ := hmem
      have he : Circle.exp s = Circle.exp 0 := by
        apply b.embedded.injective
        rw [← targetLift_projection, ← targetLift_projection,hs,developedDeck_projection]
      obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
      refine ⟨n,actual_developedDeck_point_injective k (monodromy^n) (targetLift 0) ?_⟩
      rw [← actual_target_integer_period,← hn]
      exact hs.symm
    have actual_common_monodromy_powers_injective : Function.Injective (fun n : ℤ => monodromy^n) := by
      intro n m hnm
      change monodromy^n = monodromy^m at hnm
      have he : sourceLift (0+n*(2*Real.pi)) = sourceLift (0+m*(2*Real.pi)) := by
        rw [actual_source_integer_period,actual_source_integer_period,hnm]
      have ha := actual_sourceLift_closed_embedding.injective he
      have hnreal : (n:ℝ) = (m:ℝ) := by nlinarith [Real.pi_pos]
      exact_mod_cast hnreal
    have actual_noncyclic_source_and_target_translates_disjoint
        (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ, k ≠ monodromy^n) :
        Disjoint (developedDeck k '' Set.range sourceLift) (Set.range sourceLift) ∧
        Disjoint (developedDeck k '' Set.range targetLift) (Set.range targetLift) := by
      constructor
      · rcases actual_all_source_deck_lifts_equal_or_disjoint k with he | hd
        · obtain ⟨n,hn⟩ := actual_source_stabilizer_is_common_cyclic k he
          exact False.elim (hk n hn)
        · exact hd
      · rcases actual_all_target_deck_lifts_equal_or_disjoint k with he | hd
        · obtain ⟨n,hn⟩ := actual_target_stabilizer_is_common_cyclic k he
          exact False.elim (hk n hn)
        · exact hd
    have actual_facing_seam_disjoint_all_nonzero_monodromy_powers
        (n : ℤ) (hn : n ≠ 0) :
        Disjoint (facingSeam '' Set.Icc 0 1)
          (developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)) := by
      have hp : monodromy^n ≠ 1 := by
        intro he
        have hzero : monodromy^n = monodromy^(0:ℤ) := by simpa using he
        exact hn (actual_common_monodromy_powers_injective hzero)
      exact actual_compatible_seam_stabilizer_translate_disjoint _ hp
        (actual_monodromy_integer_range_invariant sourceLift sourceLift_period n)
        (actual_monodromy_integer_range_invariant targetLift targetLift_period n)
    have actual_all_integer_seams_pairwise_disjoint
        (n m : ℤ) (hnm : n ≠ m) :
        Disjoint (developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1))
          (developedDeck (monodromy^m) '' (facingSeam '' Set.Icc 0 1)) := by
      have hdiff : m-n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnm)
      have hd := actual_facing_seam_disjoint_all_nonzero_monodromy_powers (m-n) hdiff
      have hpow : monodromy^n * monodromy^(m-n) = monodromy^m := by
        rw [← _root_.zpow_add]
        congr 1
        ring
      have himage : developedDeck (monodromy^n) ''
          (developedDeck (monodromy^(m-n)) '' (facingSeam '' Set.Icc 0 1)) =
          developedDeck (monodromy^m) '' (facingSeam '' Set.Icc 0 1) := by
        rw [Set.image_image]
        congr 1
        funext z
        rw [← actual_developedDeck_mul,hpow]
      have h := hd.image (developedDeck (monodromy^n)).injective.injOn
        (Set.subset_univ _) (Set.subset_univ _)
      rwa [himage] at h
    have actual_facing_region_all_integer_monodromy_invariant
        (n : ℤ) : developedDeck (monodromy^n) '' facingRegion = facingRegion := by
      have hF := actual_monodromy_integer_range_invariant sourceLift sourceLift_period n
      have hJ := actual_monodromy_integer_range_invariant targetLift targetLift_period n
      have hsource := actual_invariant_facing_side (developedDeck (monodromy^n))
        (Set.range sourceLift) (Set.range targetLift) sourceInner sourceOuter
        hSourceInnerOpen hSourceOuterOpen hSourceInnerConn.isPreconnected hSourceSidesDisjoint
        hSourceSidesPartition ⟨targetLift 0,Set.mem_range_self 0⟩ hTargetInSourceInner hF hJ
      have htarget := actual_invariant_facing_side (developedDeck (monodromy^n))
        (Set.range targetLift) (Set.range sourceLift) targetInner targetOuter
        hTargetInnerOpen hTargetOuterOpen hTargetInnerConn.isPreconnected hTargetSidesDisjoint
        hTargetSidesPartition ⟨sourceLift 0,Set.mem_range_self 0⟩ hSourceInTargetInner hJ hF
      change developedDeck (monodromy^n) '' (sourceInner ∩ targetInner) = sourceInner ∩ targetInner
      rw [Set.image_inter (developedDeck (monodromy^n)).injective,hsource.1,htarget.1]
    let periodicSourceArc (n : ℤ) : Set H2 := sourceLift ''
      Set.Icc (sourceParameter+n*(2*Real.pi)) (sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi))
    let periodicTargetArc (n : ℤ) : Set H2 := targetLift ''
      Set.Icc (targetParameter+n*(2*Real.pi)) (targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi))
    let periodicSeam (n : ℤ) : Set H2 := developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)
    let periodicCellBoundary (n : ℤ) : Set H2 :=
      (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1))
    have actual_integer_seam_source_intersection (n : ℤ) (z : H2)
        (hz : z ∈ periodicSeam n) (hF : z ∈ Set.range sourceLift) :
        z = sourceLift (sourceParameter+n*(2*Real.pi)) := by
      obtain ⟨u,hu,rfl⟩ := hz
      have huF : u ∈ Set.range sourceLift := by
        rw [← actual_monodromy_integer_range_invariant sourceLift sourceLift_period n] at hF
        obtain ⟨v,hv,he⟩ := hF
        exact (developedDeck (monodromy^n)).injective he ▸ hv
      have he := (hFacingBoundaryIntersections.1 u hu huF).trans hFacingSeam0
      rw [he,← hSourceParameter,← actual_source_integer_period]
    have actual_integer_seam_target_intersection (n : ℤ) (z : H2)
        (hz : z ∈ periodicSeam n) (hJ : z ∈ Set.range targetLift) :
        z = targetLift (targetParameter+n*(2*Real.pi)) := by
      obtain ⟨u,hu,rfl⟩ := hz
      have huJ : u ∈ Set.range targetLift := by
        rw [← actual_monodromy_integer_range_invariant targetLift targetLift_period n] at hJ
        obtain ⟨v,hv,he⟩ := hJ
        exact (developedDeck (monodromy^n)).injective he ▸ hv
      have he := (hFacingBoundaryIntersections.2 u hu huJ).trans hFacingSeam1
      rw [he,← hTargetParameter,← actual_target_integer_period]
    have actual_source_arc_seam_index_separation (n j : ℤ)
        (hj : j < n ∨ n+1 < j) : Disjoint (periodicSourceArc n) (periodicSeam j) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs,rfl⟩ hz
      have he := actual_integer_seam_source_intersection j _ hz (Set.mem_range_self _)
      have hsEq := actual_sourceLift_closed_embedding.injective he
      change sourceParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
        s ≤ sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
      rcases hj with hj | hj
      · have hjreal : (j:ℝ) < (n:ℝ) := by exact_mod_cast hj
        nlinarith [Real.pi_pos]
      · have hjreal : ((n+1:ℤ):ℝ) < (j:ℝ) := by exact_mod_cast hj
        nlinarith [Real.pi_pos]
    have actual_target_arc_seam_index_separation (n j : ℤ)
        (hj : j < n ∨ n+1 < j) : Disjoint (periodicTargetArc n) (periodicSeam j) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs,rfl⟩ hz
      have he := actual_integer_seam_target_intersection j _ hz (Set.mem_range_self _)
      have hsEq := actual_targetLift_closed_embedding.injective he
      change targetParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
        s ≤ targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
      rcases hj with hj | hj
      · have hjreal : (j:ℝ) < (n:ℝ) := by exact_mod_cast hj
        nlinarith [Real.pi_pos]
      · have hjreal : ((n+1:ℤ):ℝ) < (j:ℝ) := by exact_mod_cast hj
        nlinarith [Real.pi_pos]
    have actual_nonadjacent_source_arcs_disjoint (n m : ℤ) (hnm : n+1 < m) :
        Disjoint (periodicSourceArc n) (periodicSourceArc m) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
      have hst := actual_sourceLift_closed_embedding.injective he
      have hreal : ((n+1:ℤ):ℝ) < (m:ℝ) := by exact_mod_cast hnm
      change sourceParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
        s ≤ sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
      change sourceParameter+(m:ℝ)*(2*Real.pi) ≤ t ∧
        t ≤ sourceParameter+((m+1:ℤ):ℝ)*(2*Real.pi) at ht
      nlinarith [Real.pi_pos]
    have actual_nonadjacent_target_arcs_disjoint (n m : ℤ) (hnm : n+1 < m) :
        Disjoint (periodicTargetArc n) (periodicTargetArc m) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
      have hst := actual_targetLift_closed_embedding.injective he
      have hreal : ((n+1:ℤ):ℝ) < (m:ℝ) := by exact_mod_cast hnm
      change targetParameter+(n:ℝ)*(2*Real.pi) ≤ s ∧
        s ≤ targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi) at hs
      change targetParameter+(m:ℝ)*(2*Real.pi) ≤ t ∧
        t ≤ targetParameter+((m+1:ℤ):ℝ)*(2*Real.pi) at ht
      nlinarith [Real.pi_pos]
    have actual_all_source_target_periodic_arcs_disjoint (n m : ℤ) :
        Disjoint (periodicSourceArc n) (periodicTargetArc m) := by
      exact actual_endpoint_lifts_disjoint.mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
    have actual_nonadjacent_periodic_cell_boundaries_disjoint (n m : ℤ) (hnm : n+1 < m) :
        Disjoint (periodicCellBoundary n) (periodicCellBoundary m) := by
      have hnm' : n < m := by omega
      have hnm1 : n ≠ m := by omega
      have hnmp1 : n ≠ m+1 := by omega
      have hnp1m : n+1 ≠ m := by omega
      have hnp1mp1 : n+1 ≠ m+1 := by omega
      have h1 : Disjoint (periodicSourceArc n) (periodicCellBoundary m) := by
        exact Set.disjoint_union_right.mpr
          ⟨Set.disjoint_union_right.mpr ⟨actual_nonadjacent_source_arcs_disjoint n m hnm,
            actual_all_source_target_periodic_arcs_disjoint n m⟩,
           Set.disjoint_union_right.mpr
            ⟨actual_source_arc_seam_index_separation n m (Or.inr hnm),
             actual_source_arc_seam_index_separation n (m+1) (Or.inr (by omega))⟩⟩
      have h2 : Disjoint (periodicTargetArc n) (periodicCellBoundary m) := by
        exact Set.disjoint_union_right.mpr
          ⟨Set.disjoint_union_right.mpr ⟨(actual_all_source_target_periodic_arcs_disjoint m n).symm,
            actual_nonadjacent_target_arcs_disjoint n m hnm⟩,
           Set.disjoint_union_right.mpr
            ⟨actual_target_arc_seam_index_separation n m (Or.inr hnm),
             actual_target_arc_seam_index_separation n (m+1) (Or.inr (by omega))⟩⟩
      have h3 : Disjoint (periodicSeam n) (periodicCellBoundary m) := by
        exact Set.disjoint_union_right.mpr
          ⟨Set.disjoint_union_right.mpr
            ⟨(actual_source_arc_seam_index_separation m n (Or.inl hnm')).symm,
             (actual_target_arc_seam_index_separation m n (Or.inl hnm')).symm⟩,
           Set.disjoint_union_right.mpr
            ⟨actual_all_integer_seams_pairwise_disjoint n m hnm1,
             actual_all_integer_seams_pairwise_disjoint n (m+1) hnmp1⟩⟩
      have h4 : Disjoint (periodicSeam (n+1)) (periodicCellBoundary m) := by
        exact Set.disjoint_union_right.mpr
          ⟨Set.disjoint_union_right.mpr
            ⟨(actual_source_arc_seam_index_separation m (n+1) (Or.inl hnm)).symm,
             (actual_target_arc_seam_index_separation m (n+1) (Or.inl hnm)).symm⟩,
           Set.disjoint_union_right.mpr
            ⟨actual_all_integer_seams_pairwise_disjoint (n+1) m hnp1m,
             actual_all_integer_seams_pairwise_disjoint (n+1) (m+1) hnp1mp1⟩⟩
      exact Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨h1,h2⟩,Set.disjoint_union_left.mpr ⟨h3,h4⟩⟩
    have actual_integer_periodic_arc_translate
        (F : ℝ → H2) (hFperiod : ∀ s, F (s+2*Real.pi) = developedDeck monodromy (F s))
        (p : ℝ) (n : ℤ) :
        developedDeck (monodromy^n) '' (F '' Set.Icc p (p+2*Real.pi)) =
          F '' Set.Icc (p+n*(2*Real.pi)) (p+((n+1:ℤ):ℝ)*(2*Real.pi)) := by
      have hp := actual_common_monodromy_integer_period F hFperiod n
      ext z
      constructor
      · rintro ⟨_,⟨s,hs,rfl⟩,rfl⟩
        refine ⟨s+n*(2*Real.pi),?_,hp s⟩
        push_cast
        constructor <;> linarith [hs.1,hs.2]
      · rintro ⟨s,hs,rfl⟩
        refine ⟨F (s-n*(2*Real.pi)),⟨s-n*(2*Real.pi),?_,rfl⟩,?_⟩
        · push_cast at hs
          constructor <;> linarith [hs.1,hs.2]
        · rw [← hp]
          congr 1
          ring
    have hPeriodicSourceArcZero : periodicSourceArc 0 = sourceArc := by
      simp [periodicSourceArc,sourceArc]
    have hPeriodicTargetArcZero : periodicTargetArc 0 = targetArc := by
      simp [periodicTargetArc,targetArc]
    have hPeriodicSeamZero : periodicSeam 0 = firstSeam := by
      ext z
      simp only [periodicSeam,_root_.zpow_zero,Set.mem_image,actual_developedDeck_one,firstSeam]
      simp
    have hPeriodicSeamOne : periodicSeam 1 = secondSeam := by
      simp only [periodicSeam,_root_.zpow_one,secondSeam,firstSeam]
    have hFundamentalBoundaryCellZero : fundamentalBoundary = planeCoordinate '' periodicCellBoundary 0 := by
      change fundamentalBoundary = planeCoordinate ''
        ((periodicSourceArc 0 ∪ periodicTargetArc 0) ∪ (periodicSeam 0 ∪ periodicSeam 1))
      rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,
        hPeriodicSeamZero,hPeriodicSeamOne,Set.image_union,Set.image_union,Set.image_union]
      change (planeCoordinate '' sourceArc ∪ planeCoordinate '' secondSeam) ∪
        (planeCoordinate '' firstSeam ∪ planeCoordinate '' targetArc) = _
      ac_rfl
    have hPeriodicCellTranslate (n : ℤ) :
        developedDeck (monodromy^n) '' periodicCellBoundary 0 = periodicCellBoundary n := by
      have hsource := actual_integer_periodic_arc_translate sourceLift sourceLift_period sourceParameter n
      have htarget := actual_integer_periodic_arc_translate targetLift targetLift_period targetParameter n
      have hseams (j : ℤ) : developedDeck (monodromy^n) '' periodicSeam j = periodicSeam (n+j) := by
        change developedDeck (monodromy^n) ''
          (developedDeck (monodromy^j) '' (facingSeam '' Set.Icc 0 1)) =
          developedDeck (monodromy^(n+j)) '' (facingSeam '' Set.Icc 0 1)
        rw [Set.image_image]
        change (fun z => developedDeck (monodromy^n) (developedDeck (monodromy^j) z)) ''
          (facingSeam '' Set.Icc 0 1) = _
        have he : (fun z => developedDeck (monodromy^n) (developedDeck (monodromy^j) z)) =
            developedDeck (monodromy^(n+j)) := by
          funext z
          rw [← actual_developedDeck_mul,← _root_.zpow_add]
        rw [he]
      change developedDeck (monodromy^n) ''
        ((periodicSourceArc 0 ∪ periodicTargetArc 0) ∪ (periodicSeam 0 ∪ periodicSeam 1)) =
        (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1))
      rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,
        Set.image_union,Set.image_union,Set.image_union,hsource,htarget,hseams,hseams]
      simp only [add_zero]
      rfl
    let periodicPlaneDeck (n : ℤ) : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
      (planeCoordinate.symm.trans (developedDeck (monodromy^n))).trans planeCoordinate
    have hPeriodicPlaneBoundary (n : ℤ) :
        periodicPlaneDeck n '' fundamentalBoundary = planeCoordinate '' periodicCellBoundary n := by
      rw [hFundamentalBoundaryCellZero,Set.image_image]
      have he : (fun z => periodicPlaneDeck n (planeCoordinate z)) =
          fun z => planeCoordinate (developedDeck (monodromy^n) z) := by
        funext z
        simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      rw [he,← Set.image_image,hPeriodicCellTranslate]
    have actual_all_periodic_boundaries_jordan (n : ℤ) :
        Schoenflies.IsJordanCurve (planeCoordinate '' periodicCellBoundary n) := by
      rw [← hPeriodicPlaneBoundary]
      exact CurveComplex.jordan_curve_homeomorph_image actual_fundamental_boundary_jordan (periodicPlaneDeck n)
    have actual_all_periodic_cell_insides_in_facing_region (n : ℤ) :
        Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ⊆ planeCoordinate '' facingRegion := by
      rw [← hPeriodicPlaneBoundary,← CurveComplex.jordan_inside_homeomorph_image]
      rintro z ⟨y,hy,rfl⟩
      obtain ⟨u,hu,rfl⟩ := actual_fundamental_cell_inside_facing_region hy
      refine ⟨developedDeck (monodromy^n) u,?_,?_⟩
      · exact actual_facing_region_all_integer_monodromy_invariant n ▸ Set.mem_image_of_mem _ hu
      · simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
    have actual_each_periodic_cell_boundary_has_point_outside_facing_region (n : ℤ) :
        ∃ x : Schoenflies.Plane, x ∈ planeCoordinate '' periodicCellBoundary n ∧
          x ∉ planeCoordinate '' facingRegion := by
      let p := sourceParameter+n*(2*Real.pi)
      have hp : sourceLift p ∈ periodicSourceArc n := by
        refine ⟨p,⟨le_rfl,?_⟩,rfl⟩
        dsimp [p]
        push_cast
        linarith [Real.pi_pos]
      refine ⟨planeCoordinate (sourceLift p),
        Set.mem_image_of_mem _ (Or.inl (Or.inl hp)),?_⟩
      rintro ⟨u,hu,he⟩
      have he' := planeCoordinate.injective he
      have hinner : sourceLift p ∈ sourceInner := (he' ▸ hu).1
      have hcompl : sourceLift p ∈ (Set.range sourceLift)ᶜ := by
        rw [← hSourceSidesPartition]
        exact Or.inl hinner
      exact hcompl (Set.mem_range_self p)
    have actual_nonadjacent_closed_periodic_jordan_cells_disjoint (n m : ℤ) (hnm : n+1 < m) :
        Disjoint (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
            (planeCoordinate '' periodicCellBoundary n))
          (Schoenflies.inside (planeCoordinate '' periodicCellBoundary m) ∪
            (planeCoordinate '' periodicCellBoundary m)) := by
      have hboundaries := (actual_nonadjacent_periodic_cell_boundaries_disjoint n m hnm).image
        planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
      have no_nesting (i j : ℤ)
          (hd : Disjoint (planeCoordinate '' periodicCellBoundary i) (planeCoordinate '' periodicCellBoundary j)) :
          ¬ (Schoenflies.inside (planeCoordinate '' periodicCellBoundary i) ∪
            (planeCoordinate '' periodicCellBoundary i) ⊆
            Schoenflies.inside (planeCoordinate '' periodicCellBoundary j) ∪
            (planeCoordinate '' periodicCellBoundary j)) := by
        intro hnest
        obtain ⟨x,hx,hxNot⟩ := actual_each_periodic_cell_boundary_has_point_outside_facing_region i
        rcases hnest (Or.inr hx) with hinside | hboundary
        · exact hxNot (actual_all_periodic_cell_insides_in_facing_region j hinside)
        · exact Set.disjoint_left.mp hd hx hboundary
      rcases CurveComplex.jordan_curve_closed_regions_disjoint_or_nested
        (actual_all_periodic_boundaries_jordan n) (actual_all_periodic_boundaries_jordan m) hboundaries with
        hd | hnested | hnested
      · exact hd
      · exact False.elim (no_nesting n m hboundaries hnested)
      · exact False.elim (no_nesting m n hboundaries.symm hnested)
    obtain ⟨fundamentalBoundaryHomeomorph⟩ :=
      Schoenflies.IsJordanCurve.modelCurve_homeomorph actual_fundamental_boundary_jordan
    obtain ⟨fundamentalPlaneHomeomorph,hFundamentalPlaneBoundary⟩ :=
      Schoenflies.jordan_schoenflies_of_homeomorph Schoenflies.isJordanCurve_modelCurve
        actual_fundamental_boundary_jordan fundamentalBoundaryHomeomorph
    have hFundamentalPlaneBoundaryImage : fundamentalPlaneHomeomorph '' Schoenflies.modelCurve = fundamentalBoundary := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [hFundamentalPlaneBoundary ⟨x,hx⟩]
        exact (fundamentalBoundaryHomeomorph ⟨x,hx⟩).property
      · intro hz
        let w := fundamentalBoundaryHomeomorph.symm ⟨z,hz⟩
        refine ⟨w.val,w.property,?_⟩
        rw [hFundamentalPlaneBoundary w]
        exact congrArg Subtype.val (fundamentalBoundaryHomeomorph.apply_symm_apply ⟨z,hz⟩)
    let actualFilledFundamentalDisk : C(Schoenflies.Plane.closedSquare 0 1,Schoenflies.Plane) :=
      ⟨fun x => fundamentalPlaneHomeomorph x,
        fundamentalPlaneHomeomorph.continuous.comp continuous_subtype_val⟩
    have actual_filled_fundamental_disk_embedding : Topology.IsEmbedding actualFilledFundamentalDisk :=
      fundamentalPlaneHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have actual_filled_fundamental_disk_range :
        Set.range actualFilledFundamentalDisk = fundamentalBoundary ∪ Schoenflies.inside fundamentalBoundary := by
      have hrange : Set.range actualFilledFundamentalDisk =
          fundamentalPlaneHomeomorph '' Schoenflies.Plane.closedSquare 0 1 := by
        ext z
        constructor
        · rintro ⟨x,rfl⟩; exact ⟨x,x.property,rfl⟩
        · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
      rw [hrange,← Schoenflies.modelCurve_union_inside,Set.image_union,
        CurveComplex.jordan_inside_homeomorph_image,hFundamentalPlaneBoundaryImage]
    have actual_filled_fundamental_disk_interior_in_facing_region :
        actualFilledFundamentalDisk '' {x | (x : Schoenflies.Plane) ∈ Schoenflies.Plane.openSquare 0 1} ⊆
          planeCoordinate '' facingRegion := by
      rintro z ⟨x,hx,rfl⟩
      apply actual_fundamental_cell_inside_facing_region
      rw [← hFundamentalPlaneBoundaryImage,← CurveComplex.jordan_inside_homeomorph_image]
      refine ⟨x,?_,rfl⟩
      rw [Schoenflies.inside_modelCurve]
      exact hx
    have actual_integer_source_corner_on_seam (n : ℤ) :
        sourceLift (sourceParameter+n*(2*Real.pi)) ∈ periodicSeam n := by
      change sourceLift (sourceParameter+n*(2*Real.pi)) ∈
        developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)
      rw [actual_source_integer_period,hSourceParameter]
      exact Set.mem_image_of_mem _ ⟨0,⟨le_rfl,zero_le_one⟩,hFacingSeam0⟩
    have actual_integer_target_corner_on_seam (n : ℤ) :
        targetLift (targetParameter+n*(2*Real.pi)) ∈ periodicSeam n := by
      change targetLift (targetParameter+n*(2*Real.pi)) ∈
        developedDeck (monodromy^n) '' (facingSeam '' Set.Icc 0 1)
      rw [actual_target_integer_period,hTargetParameter]
      exact Set.mem_image_of_mem _ ⟨1,⟨zero_le_one,le_rfl⟩,hFacingSeam1⟩
    have actual_adjacent_source_arc_intersection (n : ℤ) (z : H2)
        (hz : z ∈ periodicSourceArc n) (hz' : z ∈ periodicSourceArc (n+1)) :
        z = sourceLift (sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi)) := by
      obtain ⟨s,hs,rfl⟩ := hz
      obtain ⟨t,ht,he⟩ := hz'
      have hts := actual_sourceLift_closed_embedding.injective he
      have hsEnd : s = sourceParameter+((n+1:ℤ):ℝ)*(2*Real.pi) :=
        le_antisymm hs.2 (hts ▸ ht.1)
      rw [hsEnd]
    have actual_adjacent_target_arc_intersection (n : ℤ) (z : H2)
        (hz : z ∈ periodicTargetArc n) (hz' : z ∈ periodicTargetArc (n+1)) :
        z = targetLift (targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi)) := by
      obtain ⟨s,hs,rfl⟩ := hz
      obtain ⟨t,ht,he⟩ := hz'
      have hts := actual_targetLift_closed_embedding.injective he
      have hsEnd : s = targetParameter+((n+1:ℤ):ℝ)*(2*Real.pi) :=
        le_antisymm hs.2 (hts ▸ ht.1)
      rw [hsEnd]
    have actual_adjacent_periodic_cell_boundaries_intersection (n : ℤ) :
        periodicCellBoundary n ∩ periodicCellBoundary (n+1) = periodicSeam (n+1) := by
      ext z
      constructor
      · intro hz
        rcases hz.1 with (hS | hT) | (hE | hShared)
        · rcases hz.2 with (hS' | hT') | (hShared' | hFar)
          · rw [actual_adjacent_source_arc_intersection n z hS hS']
            exact actual_integer_source_corner_on_seam (n+1)
          · exact False.elim (Set.disjoint_left.mp
              (actual_all_source_target_periodic_arcs_disjoint n (n+1)) hS hT')
          · exact hShared'
          · exact False.elim (Set.disjoint_left.mp
              (actual_source_arc_seam_index_separation n (n+1+1) (Or.inr (by omega))) hS hFar)
        · rcases hz.2 with (hS' | hT') | (hShared' | hFar)
          · exact False.elim (Set.disjoint_left.mp
              (actual_all_source_target_periodic_arcs_disjoint (n+1) n).symm hT hS')
          · rw [actual_adjacent_target_arc_intersection n z hT hT']
            exact actual_integer_target_corner_on_seam (n+1)
          · exact hShared'
          · exact False.elim (Set.disjoint_left.mp
              (actual_target_arc_seam_index_separation n (n+1+1) (Or.inr (by omega))) hT hFar)
        · rcases hz.2 with (hS' | hT') | (hShared' | hFar)
          · exact False.elim (Set.disjoint_left.mp
              (actual_source_arc_seam_index_separation (n+1) n (Or.inl (by omega))).symm hE hS')
          · exact False.elim (Set.disjoint_left.mp
              (actual_target_arc_seam_index_separation (n+1) n (Or.inl (by omega))).symm hE hT')
          · exact False.elim (Set.disjoint_left.mp
              (actual_all_integer_seams_pairwise_disjoint n (n+1) (by omega)) hE hShared')
          · exact False.elim (Set.disjoint_left.mp
              (actual_all_integer_seams_pairwise_disjoint n (n+1+1) (by omega)) hE hFar)
        · exact hShared
      · intro hz
        exact ⟨Or.inr (Or.inr hz),Or.inr (Or.inl hz)⟩
    let periodicComplement (n j : ℤ) : Set H2 :=
      (periodicSourceArc n ∪ periodicSeam (n+j)) ∪ periodicTargetArc n
    let sourceCorner (n : ℤ) : Schoenflies.Plane := planeCoordinate
      (sourceLift (sourceParameter+n*(2*Real.pi)))
    let targetCorner (n : ℤ) : Schoenflies.Plane := planeCoordinate
      (targetLift (targetParameter+n*(2*Real.pi)))
    have hBaseLeftComplementArc : Schoenflies.IsArcBetween
        ((planeCoordinate '' sourceArc ∪ planeCoordinate '' secondSeam) ∪ planeCoordinate '' targetArc)
        (planeCoordinate facingSeamSource) (planeCoordinate facingSeamTarget) := by
      apply (hSourceArcPlane.concatenate hSecondSeamPlane hSourceSecondMeet).concatenate hTargetArcPlane.reverse
      intro z hz hzQ
      rcases hz with hzS | hzR
      · exact False.elim (Set.disjoint_left.mp hSourceTargetArcDisjoint hzS hzQ)
      · exact hSecondTargetMeet z hzR hzQ
    have hBaseRightComplementArc : Schoenflies.IsArcBetween
        ((planeCoordinate '' sourceArc ∪ planeCoordinate '' firstSeam) ∪ planeCoordinate '' targetArc)
        (planeCoordinate (developedDeck monodromy facingSeamSource))
        (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
      have hfirst := hSourceArcPlane.reverse.concatenate hFirstSeamPlane hSourceFirstMeet
      apply hfirst.concatenate hTargetArcPlane
      intro z hz hzQ
      rcases hz with hzS | hzE
      · exact False.elim (Set.disjoint_left.mp hSourceTargetArcDisjoint hzS hzQ)
      · exact hFirstTargetMeet z hzE hzQ
    have actual_periodic_complement_translate (n j : ℤ) :
        developedDeck (monodromy^n) '' periodicComplement 0 j = periodicComplement n j := by
      have hsource := actual_integer_periodic_arc_translate sourceLift sourceLift_period sourceParameter n
      have htarget := actual_integer_periodic_arc_translate targetLift targetLift_period targetParameter n
      have hseam : developedDeck (monodromy^n) '' periodicSeam j = periodicSeam (n+j) := by
        change developedDeck (monodromy^n) ''
          (developedDeck (monodromy^j) '' (facingSeam '' Set.Icc 0 1)) =
          developedDeck (monodromy^(n+j)) '' (facingSeam '' Set.Icc 0 1)
        rw [Set.image_image]
        congr 1
        funext z
        rw [← actual_developedDeck_mul,← _root_.zpow_add]
      change developedDeck (monodromy^n) ''
        ((periodicSourceArc 0 ∪ periodicSeam (0+j)) ∪ periodicTargetArc 0) = _
      rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,zero_add,Set.image_union,
        Set.image_union,hsource,htarget,hseam]
    have actual_periodic_complement_plane_translate (n j : ℤ) :
        periodicPlaneDeck n '' (planeCoordinate '' periodicComplement 0 j) =
          planeCoordinate '' periodicComplement n j := by
      rw [Set.image_image]
      have he : (fun z => periodicPlaneDeck n (planeCoordinate z)) =
          fun z => planeCoordinate (developedDeck (monodromy^n) z) := by
        funext z
        simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      rw [he,← Set.image_image,actual_periodic_complement_translate]
    have hPlaneSourceCorner (n : ℤ) :
        periodicPlaneDeck n (planeCoordinate facingSeamSource) = sourceCorner n := by
      simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      rw [← hSourceParameter,← actual_source_integer_period]
    have hPlaneTargetCorner (n : ℤ) :
        periodicPlaneDeck n (planeCoordinate facingSeamTarget) = targetCorner n := by
      simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      rw [← hTargetParameter,← actual_target_integer_period]
    have hPlaneFarSourceCorner (n : ℤ) :
        periodicPlaneDeck n (planeCoordinate (developedDeck monodromy facingSeamSource)) = sourceCorner (n+1) := by
      simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      rw [← actual_developedDeck_mul,← _root_.zpow_add_one]
      simpa only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
        using (hPlaneSourceCorner (n+1))
    have hPlaneFarTargetCorner (n : ℤ) :
        periodicPlaneDeck n (planeCoordinate (developedDeck monodromy facingSeamTarget)) = targetCorner (n+1) := by
      simp only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
      rw [← actual_developedDeck_mul,← _root_.zpow_add_one]
      simpa only [periodicPlaneDeck,Homeomorph.trans_apply,planeCoordinate.symm_apply_apply]
        using (hPlaneTargetCorner (n+1))
    have actual_left_periodic_complement_arc (n : ℤ) : Schoenflies.IsArcBetween
        (planeCoordinate '' periodicComplement n 1) (sourceCorner n) (targetCorner n) := by
      have hbase : Schoenflies.IsArcBetween (planeCoordinate '' periodicComplement 0 1)
          (planeCoordinate facingSeamSource) (planeCoordinate facingSeamTarget) := by
        change Schoenflies.IsArcBetween
          (planeCoordinate '' ((periodicSourceArc 0 ∪ periodicSeam (0+1)) ∪ periodicTargetArc 0)) _ _
        simp only [zero_add]
        rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,hPeriodicSeamOne,Set.image_union,Set.image_union]
        exact hBaseLeftComplementArc
      have h := hbase.image_of_injOn (Set.subset_univ _)
        (periodicPlaneDeck n).continuous.continuousOn (periodicPlaneDeck n).injective.injOn
      rwa [actual_periodic_complement_plane_translate,hPlaneSourceCorner,hPlaneTargetCorner] at h
    have actual_right_periodic_complement_arc (n : ℤ) : Schoenflies.IsArcBetween
        (planeCoordinate '' periodicComplement n 0) (sourceCorner (n+1)) (targetCorner (n+1)) := by
      have hbase : Schoenflies.IsArcBetween (planeCoordinate '' periodicComplement 0 0)
          (planeCoordinate (developedDeck monodromy facingSeamSource))
          (planeCoordinate (developedDeck monodromy facingSeamTarget)) := by
        change Schoenflies.IsArcBetween
          (planeCoordinate '' ((periodicSourceArc 0 ∪ periodicSeam (0+0)) ∪ periodicTargetArc 0)) _ _
        simp only [add_zero]
        rw [hPeriodicSourceArcZero,hPeriodicTargetArcZero,hPeriodicSeamZero,Set.image_union,Set.image_union]
        exact hBaseRightComplementArc
      have h := hbase.image_of_injOn (Set.subset_univ _)
        (periodicPlaneDeck n).continuous.continuousOn (periodicPlaneDeck n).injective.injOn
      rwa [actual_periodic_complement_plane_translate,hPlaneFarSourceCorner,hPlaneFarTargetCorner] at h
    have actual_arc_on_outside_from_one_excluded_inside_point
        {C A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
        (hC : Schoenflies.IsSeparating C) (hA : Schoenflies.IsArcBetween A p q)
        (hend : p ∈ C ∧ q ∈ C)
        (hmeet : ∀ z ∈ A, z ∈ C → z = p ∨ z = q)
        (hpoint : ∃ z, z ∈ A \ ({p,q} : Set Schoenflies.Plane) ∧ z ∉ Schoenflies.inside C) :
        A ⊆ Schoenflies.outside C ∪ C := by
      have hcover : A \ ({p,q} : Set Schoenflies.Plane) ⊆
          Schoenflies.inside C ∪ Schoenflies.outside C := by
        rw [Schoenflies.inside_union_outside]
        intro z hz hzC
        rcases hmeet z hz.1 hzC with he | he
        · exact hz.2 (by simp [he])
        · exact hz.2 (by simp [he])
      have hout : A \ ({p,q} : Set Schoenflies.Plane) ⊆ Schoenflies.outside C := by
        rcases hA.isPreconnected_diff.subset_or_subset hC.isOpen_inside hC.isOpen_outside
          Schoenflies.disjoint_inside_outside hcover with hin | hout
        · obtain ⟨z,hz,hzNot⟩ := hpoint
          exact False.elim (hzNot (hin hz))
        · exact hout
      intro z hz
      by_cases hp : z = p
      · exact Or.inr (hp ▸ hend.1)
      by_cases hq : z = q
      · exact Or.inr (hq ▸ hend.2)
      exact Or.inl (hout ⟨hz,by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; exact fun h => h.elim hp hq⟩)
    have actual_jordan_insides_disjoint_from_closed_outside_boundary
        {C K : Set Schoenflies.Plane} (hC : Schoenflies.IsSeparating C)
        (hK : Schoenflies.IsSeparating K)
        (hKC : K ⊆ Schoenflies.outside C ∪ C)
        (hpoint : (C ∩ Schoenflies.outside K).Nonempty) :
        Disjoint (Schoenflies.inside C) (Schoenflies.inside K) := by
      have hcover : Schoenflies.inside C ⊆ Schoenflies.inside K ∪ Schoenflies.outside K := by
        rw [Schoenflies.inside_union_outside]
        intro z hz hzK
        rcases hKC hzK with hout | hboundary
        · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz hout
        · exact Schoenflies.inside_subset_compl hz hboundary
      have hout : Schoenflies.inside C ⊆ Schoenflies.outside K := by
        rcases hC.isConnected_inside.isPreconnected.subset_or_subset hK.isOpen_inside hK.isOpen_outside
          Schoenflies.disjoint_inside_outside hcover with hin | hout
        · obtain ⟨z,hzC,hzOut⟩ := hpoint
          have hzClosure : z ∈ closure (Schoenflies.inside C) := by
            apply frontier_subset_closure
            rw [hC.frontier_inside]
            exact hzC
          have hzKClosure := closure_mono hin hzClosure
          have hinter := hK.isOpen_outside.inter_closure ⟨hzOut,hzKClosure⟩
          obtain ⟨w,hwOut,hwIn⟩ := Set.Nonempty.of_closure ⟨z,hinter⟩
          exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hwIn hwOut)
        · exact hout
      exact Schoenflies.disjoint_inside_outside.symm.mono hout (Set.Subset.refl _)
    have actual_periodic_complement_source_midpoint (n j k : ℤ) (hk : k = n ∨ k = n+1) :
        ∃ x, x ∈ (planeCoordinate '' periodicComplement n j) \ ({sourceCorner k,targetCorner k} : Set Schoenflies.Plane) ∧
          ∀ i : ℤ, x ∉ Schoenflies.inside (planeCoordinate '' periodicCellBoundary i) := by
      let s := sourceParameter+(n:ℝ)*(2*Real.pi)+Real.pi
      have hsArc : sourceLift s ∈ periodicSourceArc n := by
        refine ⟨s,⟨?_,?_⟩,rfl⟩
        · dsimp [s]; linarith [Real.pi_pos]
        · dsimp [s]; push_cast; linarith [Real.pi_pos]
      have hxComplement : planeCoordinate (sourceLift s) ∈ planeCoordinate '' periodicComplement n j :=
        Set.mem_image_of_mem _ (Or.inl (Or.inl hsArc))
      have hneSource : planeCoordinate (sourceLift s) ≠ sourceCorner k := by
        intro he
        change planeCoordinate (sourceLift s) = planeCoordinate
          (sourceLift (sourceParameter+k*(2*Real.pi))) at he
        have hsEq := actual_sourceLift_closed_embedding.injective (planeCoordinate.injective he)
        rcases hk with rfl | rfl
        · dsimp [s] at hsEq; linarith [Real.pi_pos]
        · dsimp [s] at hsEq; push_cast at hsEq; linarith [Real.pi_pos]
      have hneTarget : planeCoordinate (sourceLift s) ≠ targetCorner k := by
        intro he
        change planeCoordinate (sourceLift s) = planeCoordinate
          (targetLift (targetParameter+k*(2*Real.pi))) at he
        have hst := planeCoordinate.injective he
        exact Set.disjoint_left.mp actual_endpoint_lifts_disjoint (Set.mem_range_self s)
          (hst.symm ▸ Set.mem_range_self (targetParameter+k*(2*Real.pi)))
      refine ⟨planeCoordinate (sourceLift s),⟨hxComplement,?_⟩,?_⟩
      · simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
        exact not_or.mpr ⟨hneSource,hneTarget⟩
      · intro i hxInside
        obtain ⟨u,hu,he⟩ := actual_all_periodic_cell_insides_in_facing_region i hxInside
        have he' := planeCoordinate.injective he
        have hinner : sourceLift s ∈ sourceInner := (he' ▸ hu).1
        have hcompl : sourceLift s ∈ (Set.range sourceLift)ᶜ := by
          rw [← hSourceSidesPartition]
          exact Or.inl hinner
        exact hcompl (Set.mem_range_self s)
    have actual_complement_subset_cell (n j : ℤ) (hj : j = 0 ∨ j = 1) :
        periodicComplement n j ⊆ periodicCellBoundary n := by
      intro z hz
      rcases hz with (hS | hE) | hT
      · exact Or.inl (Or.inl hS)
      · rcases hj with rfl | rfl
        · exact Or.inr (Or.inl (by simpa only [add_zero] using hE))
        · exact Or.inr (Or.inr hE)
      · exact Or.inl (Or.inr hT)
    have actual_left_complement_meets_previous_at_endpoints (n : ℤ)
        (z : Schoenflies.Plane) (hz : z ∈ planeCoordinate '' periodicComplement n 1)
        (hzPrev : z ∈ planeCoordinate '' periodicCellBoundary (n-1)) :
        z = sourceCorner n ∨ z = targetCorner n := by
      obtain ⟨u,hu,heU⟩ := hz
      obtain ⟨v,hv,heV⟩ := hzPrev
      have huPrev : u ∈ periodicCellBoundary (n-1) := planeCoordinate.injective (heV.trans heU.symm) ▸ hv
      have huOwn := actual_complement_subset_cell n 1 (Or.inr rfl) hu
      have hidx : n-1+1 = n := by ring
      have hinter := actual_adjacent_periodic_cell_boundaries_intersection (n-1)
      rw [hidx] at hinter
      have huSeam : u ∈ periodicSeam n := by
        rw [← hinter]
        exact ⟨huPrev,huOwn⟩
      rcases hu with (hS | hFar) | hT
      · have he := actual_integer_seam_source_intersection n u huSeam (Set.image_subset_range _ _ hS)
        exact Or.inl (heU.symm.trans (congrArg planeCoordinate he))
      · exact False.elim (Set.disjoint_left.mp
          (actual_all_integer_seams_pairwise_disjoint (n+1) n (by omega)) hFar huSeam)
      · have he := actual_integer_seam_target_intersection n u huSeam (Set.image_subset_range _ _ hT)
        exact Or.inr (heU.symm.trans (congrArg planeCoordinate he))
    have actual_right_complement_meets_next_at_endpoints (n : ℤ)
        (z : Schoenflies.Plane) (hz : z ∈ planeCoordinate '' periodicComplement n 0)
        (hzNext : z ∈ planeCoordinate '' periodicCellBoundary (n+1)) :
        z = sourceCorner (n+1) ∨ z = targetCorner (n+1) := by
      obtain ⟨u,hu,heU⟩ := hz
      obtain ⟨v,hv,heV⟩ := hzNext
      have huNext : u ∈ periodicCellBoundary (n+1) := planeCoordinate.injective (heV.trans heU.symm) ▸ hv
      have huOwn := actual_complement_subset_cell n 0 (Or.inl rfl) hu
      have huSeam : u ∈ periodicSeam (n+1) := by
        rw [← actual_adjacent_periodic_cell_boundaries_intersection n]
        exact ⟨huOwn,huNext⟩
      rcases hu with (hS | hFirst) | hT
      · have he := actual_integer_seam_source_intersection (n+1) u huSeam (Set.image_subset_range _ _ hS)
        exact Or.inl (heU.symm.trans (congrArg planeCoordinate he))
      · have hFirst' : u ∈ periodicSeam n := by simpa only [add_zero] using hFirst
        exact False.elim (Set.disjoint_left.mp
          (actual_all_integer_seams_pairwise_disjoint n (n+1) (by omega)) hFirst' huSeam)
      · have he := actual_integer_seam_target_intersection (n+1) u huSeam (Set.image_subset_range _ _ hT)
        exact Or.inr (heU.symm.trans (congrArg planeCoordinate he))
    have actual_left_complement_outside_previous (n : ℤ) :
        planeCoordinate '' periodicComplement n 1 ⊆
          Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n-1)) ∪
            (planeCoordinate '' periodicCellBoundary (n-1)) := by
      have hSeamSubset : periodicSeam n ⊆ periodicCellBoundary (n-1) := by
        intro z hz
        refine Or.inr (Or.inr ?_)
        have hidx : n-1+1 = n := by ring
        rw [hidx]
        exact hz
      have hend : sourceCorner n ∈ planeCoordinate '' periodicCellBoundary (n-1) ∧
          targetCorner n ∈ planeCoordinate '' periodicCellBoundary (n-1) :=
        ⟨Set.mem_image_of_mem _ (hSeamSubset (actual_integer_source_corner_on_seam n)),
         Set.mem_image_of_mem _ (hSeamSubset (actual_integer_target_corner_on_seam n))⟩
      obtain ⟨x,hx,hxNot⟩ := actual_periodic_complement_source_midpoint n 1 n (Or.inl rfl)
      exact actual_arc_on_outside_from_one_excluded_inside_point
        (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan (n-1)))
        (actual_left_periodic_complement_arc n) hend
        (actual_left_complement_meets_previous_at_endpoints n) ⟨x,hx,hxNot (n-1)⟩
    have actual_right_complement_outside_next (n : ℤ) :
        planeCoordinate '' periodicComplement n 0 ⊆
          Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n+1)) ∪
            (planeCoordinate '' periodicCellBoundary (n+1)) := by
      have hSeamSubset : periodicSeam (n+1) ⊆ periodicCellBoundary (n+1) := by
        intro z hz
        exact Or.inr (Or.inl hz)
      have hend : sourceCorner (n+1) ∈ planeCoordinate '' periodicCellBoundary (n+1) ∧
          targetCorner (n+1) ∈ planeCoordinate '' periodicCellBoundary (n+1) :=
        ⟨Set.mem_image_of_mem _ (hSeamSubset (actual_integer_source_corner_on_seam (n+1))),
         Set.mem_image_of_mem _ (hSeamSubset (actual_integer_target_corner_on_seam (n+1)))⟩
      obtain ⟨x,hx,hxNot⟩ := actual_periodic_complement_source_midpoint n 0 (n+1) (Or.inr rfl)
      exact actual_arc_on_outside_from_one_excluded_inside_point
        (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan (n+1)))
        (actual_right_periodic_complement_arc n) hend
        (actual_right_complement_meets_next_at_endpoints n) ⟨x,hx,hxNot (n+1)⟩
    have actual_cell_boundary_left_complement_union_seam (n : ℤ) :
        periodicCellBoundary n = periodicComplement n 1 ∪ periodicSeam n := by
      change (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1)) =
        ((periodicSourceArc n ∪ periodicSeam (n+1)) ∪ periodicTargetArc n) ∪ periodicSeam n
      ac_rfl
    have actual_cell_boundary_right_complement_union_seam (n : ℤ) :
        periodicCellBoundary n = periodicComplement n 0 ∪ periodicSeam (n+1) := by
      change (periodicSourceArc n ∪ periodicTargetArc n) ∪ (periodicSeam n ∪ periodicSeam (n+1)) =
        ((periodicSourceArc n ∪ periodicSeam (n+0)) ∪ periodicTargetArc n) ∪ periodicSeam (n+1)
      simp only [add_zero]
      ac_rfl
    have actual_next_boundary_outside_previous_closed (n : ℤ) :
        planeCoordinate '' periodicCellBoundary (n+1) ⊆
          Schoenflies.outside (planeCoordinate '' periodicCellBoundary n) ∪
            (planeCoordinate '' periodicCellBoundary n) := by
      rw [actual_cell_boundary_left_complement_union_seam,Set.image_union]
      apply Set.union_subset
      · have h := actual_left_complement_outside_previous (n+1)
        have hi : n+1-1 = n := by ring
        rwa [hi] at h
      · rintro z ⟨u,hu,rfl⟩
        exact Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inr hu)))
    have actual_previous_boundary_point_outside_next (n : ℤ) :
        ((planeCoordinate '' periodicCellBoundary n) ∩
          Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n+1))).Nonempty := by
      obtain ⟨x,hx,hxNot⟩ := actual_periodic_complement_source_midpoint n 0 (n+1) (Or.inr rfl)
      have hxCell : x ∈ planeCoordinate '' periodicCellBoundary n :=
        Set.image_mono (actual_complement_subset_cell n 0 (Or.inl rfl)) hx.1
      have hxNotNext : x ∉ planeCoordinate '' periodicCellBoundary (n+1) := by
        intro hxNext
        rcases actual_right_complement_meets_next_at_endpoints n x hx.1 hxNext with he | he
        · exact hx.2 (by simp [he])
        · exact hx.2 (by simp [he])
      rcases actual_right_complement_outside_next n hx.1 with hxOut | hxBoundary
      · exact ⟨x,hxCell,hxOut⟩
      · exact False.elim (hxNotNext hxBoundary)
    have actual_adjacent_periodic_jordan_cell_interiors_disjoint (n : ℤ) :
        Disjoint (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n))
          (Schoenflies.inside (planeCoordinate '' periodicCellBoundary (n+1))) := by
      exact actual_jordan_insides_disjoint_from_closed_outside_boundary
        (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan n))
        (Schoenflies.jordan_curve_theorem (actual_all_periodic_boundaries_jordan (n+1)))
        (actual_next_boundary_outside_previous_closed n)
        (actual_previous_boundary_point_outside_next n)
    have actual_all_distinct_periodic_jordan_cell_interiors_disjoint (n m : ℤ) (hnm : n ≠ m) :
        Disjoint (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n))
          (Schoenflies.inside (planeCoordinate '' periodicCellBoundary m)) := by
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · by_cases hnext : m = n+1
        · rw [hnext]
          exact actual_adjacent_periodic_jordan_cell_interiors_disjoint n
        · have hgap : n+1 < m := by omega
          exact (actual_nonadjacent_closed_periodic_jordan_cells_disjoint n m hgap).mono
            Set.subset_union_left Set.subset_union_left
      · by_cases hnext : n = m+1
        · rw [hnext]
          exact (actual_adjacent_periodic_jordan_cell_interiors_disjoint m).symm
        · have hgap : m+1 < n := by omega
          exact (actual_nonadjacent_closed_periodic_jordan_cells_disjoint m n hgap).symm.mono
            Set.subset_union_left Set.subset_union_left
    let markedPeriodicDisk (n : ℤ) (uv : Interval × Interval) : H2 :=
      developedDeck (monodromy^n) (planeCoordinate.symm (markedFundamentalDisk uv))
    have actual_marked_periodic_disk_embedding (n : ℤ) : Topology.IsEmbedding (markedPeriodicDisk n) :=
      (developedDeck (monodromy^n)).isEmbedding.comp
        (planeCoordinate.symm.isEmbedding.comp hMarkedFundamentalDiskEmbedding)
    have actual_marked_periodic_disk_neighbor_gluing (n : ℤ) (v : Interval) :
        markedPeriodicDisk n (1,v) = markedPeriodicDisk (n+1) (0,v) := by
      simp only [markedPeriodicDisk,actual_marked_fundamental_seam_compatibility,
        Homeomorph.symm_apply_apply]
      rw [← actual_developedDeck_mul,← _root_.zpow_add_one]
    have actual_marked_periodic_disk_monodromy (n : ℤ) (uv : Interval × Interval) :
        markedPeriodicDisk (n+1) uv = developedDeck monodromy (markedPeriodicDisk n uv) := by
      change developedDeck (monodromy^(n+1)) _ = developedDeck monodromy (developedDeck (monodromy^n) _)
      have hp : monodromy^(n+1) = monodromy * monodromy^n := by
        calc
          monodromy^(n+1) = monodromy^((1:ℤ)+n) := by congr 1; omega
          _ = monodromy * monodromy^n := by rw [_root_.zpow_add,_root_.zpow_one]
      rw [hp,actual_developedDeck_mul]
    have actual_marked_periodic_disk_bottom (n : ℤ) (u : Interval) :
        markedPeriodicDisk n (u,0) = sourceLift (sourceParameter+(u:ℝ)*(2*Real.pi)+(n:ℝ)*(2*Real.pi)) := by
      simp only [markedPeriodicDisk,hMarkedFundamentalBottom,markedSourceEdge,
        Homeomorph.symm_apply_apply]
      exact (actual_source_integer_period n _).symm
    have actual_marked_periodic_disk_top (n : ℤ) (u : Interval) :
        markedPeriodicDisk n (u,1) = targetLift (targetParameter+(u:ℝ)*(2*Real.pi)+(n:ℝ)*(2*Real.pi)) := by
      simp only [markedPeriodicDisk,hMarkedFundamentalTop,markedTargetEdge,
        Homeomorph.symm_apply_apply]
      exact (actual_target_integer_period n _).symm
    have actual_marked_periodic_disk_plane_carrier (n : ℤ) :
        Set.range (planeCoordinate ∘ markedPeriodicDisk n) =
          Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
            (planeCoordinate '' periodicCellBoundary n) := by
      have he : planeCoordinate ∘ markedPeriodicDisk n = periodicPlaneDeck n ∘ markedFundamentalDisk := by
        funext uv
        simp only [Function.comp_apply,markedPeriodicDisk,periodicPlaneDeck,Homeomorph.trans_apply]
      rw [he,Set.range_comp,actual_marked_fundamental_disk_closed_carrier,
        Set.image_union,CurveComplex.jordan_inside_homeomorph_image,hPeriodicPlaneBoundary]
    have actual_previous_boundary_outside_next_closed (n : ℤ) :
        planeCoordinate '' periodicCellBoundary n ⊆
          Schoenflies.outside (planeCoordinate '' periodicCellBoundary (n+1)) ∪
            (planeCoordinate '' periodicCellBoundary (n+1)) := by
      rw [actual_cell_boundary_right_complement_union_seam,Set.image_union]
      apply Set.union_subset
      · exact actual_right_complement_outside_next n
      · rintro z ⟨u,hu,rfl⟩
        exact Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inl hu)))
    have actual_adjacent_closed_periodic_cells_intersection (n : ℤ) :
        (Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
          planeCoordinate '' periodicCellBoundary n) ∩
        (Schoenflies.inside (planeCoordinate '' periodicCellBoundary (n+1)) ∪
          planeCoordinate '' periodicCellBoundary (n+1)) = planeCoordinate '' periodicSeam (n+1) := by
      ext z
      constructor
      · rintro ⟨hz,hz'⟩
        rcases hz with hi | hb <;> rcases hz' with hi' | hb'
        · exact False.elim (Set.disjoint_left.mp (actual_adjacent_periodic_jordan_cell_interiors_disjoint n) hi hi')
        · rcases actual_next_boundary_outside_previous_closed n hb' with ho | he
          · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hi ho)
          · exact False.elim (Schoenflies.inside_subset_compl hi he)
        · rcases actual_previous_boundary_outside_next_closed n hb with ho | he
          · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hi' ho)
          · exact False.elim (Schoenflies.inside_subset_compl hi' he)
        · obtain ⟨u,hu,huEq⟩ := hb
          obtain ⟨v,hv,hvEq⟩ := hb'
          have huv : u = v := planeCoordinate.injective (huEq.trans hvEq.symm)
          refine ⟨u,?_,huEq⟩
          rw [← actual_adjacent_periodic_cell_boundaries_intersection]
          exact ⟨hu,huv.symm ▸ hv⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inr hu))),
          Or.inr (Set.mem_image_of_mem _ (Or.inr (Or.inl hu)))⟩
    have actual_marked_periodic_disk_left (n : ℤ) (v : Interval) :
        markedPeriodicDisk n (0,v) = developedDeck (monodromy^n) (facingSeam v) := by
      simp only [markedPeriodicDisk,hMarkedFundamentalLeft,markedFirstSeam,
        Homeomorph.symm_apply_apply]
    have actual_marked_periodic_disk_point_mem_carrier (n : ℤ) (uv : Interval × Interval) :
        planeCoordinate (markedPeriodicDisk n uv) ∈
          Schoenflies.inside (planeCoordinate '' periodicCellBoundary n) ∪
            (planeCoordinate '' periodicCellBoundary n) := by
      rw [← actual_marked_periodic_disk_plane_carrier]
      exact ⟨uv,rfl⟩
    have actual_marked_periodic_disk_overlap_indices (n m : ℤ) (u v : Interval × Interval)
        (he : markedPeriodicDisk n u = markedPeriodicDisk m v) :
        n = m ∨ m = n+1 ∨ n = m+1 := by
      have hn := actual_marked_periodic_disk_point_mem_carrier n u
      have hm := actual_marked_periodic_disk_point_mem_carrier m v
      rw [← he] at hm
      rcases lt_trichotomy n m with hlt | hnm | hgt
      · by_cases hnext : m = n+1
        · exact Or.inr (Or.inl hnext)
        · have hfar : n+1 < m := by omega
          exact False.elim (Set.disjoint_left.mp (actual_nonadjacent_closed_periodic_jordan_cells_disjoint n m hfar) hn hm)
      · exact Or.inl hnm
      · by_cases hprev : n = m+1
        · exact Or.inr (Or.inr hprev)
        · have hfar : m+1 < n := by omega
          exact False.elim (Set.disjoint_left.mp (actual_nonadjacent_closed_periodic_jordan_cells_disjoint m n hfar) hm hn)
    have actual_marked_periodic_disk_neighbor_parameters (n : ℤ) (u v : Interval × Interval)
        (he : markedPeriodicDisk n u = markedPeriodicDisk (n+1) v) : u.1 = 1 ∧ v.1 = 0 := by
      have hn := actual_marked_periodic_disk_point_mem_carrier n u
      have hm := actual_marked_periodic_disk_point_mem_carrier (n+1) v
      rw [← he] at hm
      have hz : planeCoordinate (markedPeriodicDisk n u) ∈ planeCoordinate '' periodicSeam (n+1) := by
        rw [← actual_adjacent_closed_periodic_cells_intersection]
        exact ⟨hn,hm⟩
      obtain ⟨_,⟨_,⟨t,ht,rfl⟩,rfl⟩,htEq⟩ := hz
      have htEq' : developedDeck (monodromy^(n+1)) (facingSeam t) = markedPeriodicDisk n u :=
        planeCoordinate.injective htEq
      let w : Interval := ⟨t,ht⟩
      have hnext : markedPeriodicDisk (n+1) (0,w) = markedPeriodicDisk n u := by
        rw [actual_marked_periodic_disk_left]
        exact htEq'
      have hcurrent : markedPeriodicDisk n (1,w) = markedPeriodicDisk n u :=
        (actual_marked_periodic_disk_neighbor_gluing n w).trans hnext
      have hu : (1,w) = u := (actual_marked_periodic_disk_embedding n).injective hcurrent
      have hv : (0,w) = v := (actual_marked_periodic_disk_embedding (n+1)).injective (hnext.trans he)
      exact ⟨(congrArg Prod.fst hu).symm,(congrArg Prod.fst hv).symm⟩
    let stripCell (n : ℤ) : Set (ℝ × Interval) :=
      Prod.fst ⁻¹' Set.Icc (n:ℝ) ((n:ℝ)+1)
    let stripCellMap (n : ℤ) (x : ℝ × Interval) : H2 :=
      markedPeriodicDisk n (Set.projIcc 0 1 (by norm_num) (x.1-(n:ℝ)),x.2)
    have hStripCellMapContinuous (n : ℤ) : Continuous (stripCellMap n) := by
      exact (actual_marked_periodic_disk_embedding n).continuous.comp
        (((continuous_projIcc (a := (0:ℝ)) (b := 1) (h := by norm_num)).comp
          (continuous_fst.sub continuous_const)).prodMk continuous_snd)
    have hStripCellClosed (n : ℤ) : IsClosed (stripCell n) := isClosed_Icc.preimage continuous_fst
    have hStripCellCover (x : ℝ × Interval) : x ∈ stripCell ⌊x.1⌋ := by
      exact ⟨Int.floor_le _,(Int.lt_floor_add_one _).le⟩
    have hStripCellLocallyFinite : LocallyFinite stripCell := by
      intro x
      let U : Set (ℝ × Interval) := Prod.fst ⁻¹' Set.Ioo (x.1-1) (x.1+1)
      have hU : U ∈ 𝓝 x := (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨by linarith,by linarith⟩
      obtain ⟨N,hN⟩ := exists_nat_gt (|x.1|+3)
      refine ⟨U,hU,(Set.finite_Icc (-(N:ℤ)) (N:ℤ)).subset ?_⟩
      rintro n ⟨y,hy,hyU⟩
      have hy' : (n:ℝ) ≤ y.1 ∧ y.1 ≤ (n:ℝ)+1 := hy
      have hyU' : x.1-1 < y.1 ∧ y.1 < x.1+1 := hyU
      have hlo : -(N:ℝ) ≤ (n:ℝ) := by linarith [neg_abs_le x.1]
      have hhi : (n:ℝ) ≤ (N:ℝ) := by linarith [le_abs_self x.1]
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    have hStripCellMapNeighbor (n : ℤ) (x : ℝ × Interval)
        (hn : x ∈ stripCell n) (hn' : x ∈ stripCell (n+1)) :
        stripCellMap n x = stripCellMap (n+1) x := by
      have ht : x.1 = (n:ℝ)+1 := by
        have hlo : ((n+1:ℤ):ℝ) ≤ x.1 := hn'.1
        push_cast at hlo
        linarith [hn.2]
      have hl : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) (x.1-(n:ℝ)) = (1:Interval) := by
        apply Subtype.ext
        simp [ht]
      have hr : Set.projIcc 0 1 (by norm_num : (0:ℝ) ≤ 1) (x.1-((n+1:ℤ):ℝ)) = (0:Interval) := by
        apply Subtype.ext
        simp [ht]
      simp only [stripCellMap,hl,hr]
      exact actual_marked_periodic_disk_neighbor_gluing n x.2
    have hStripCellMapMatch (n m : ℤ) (x : ℝ × Interval)
        (hn : x ∈ stripCell n) (hm : x ∈ stripCell m) : stripCellMap n x = stripCellMap m x := by
      have hnmReal : (n:ℝ) ≤ (m:ℝ)+1 := hn.1.trans hm.2
      have hmnReal : (m:ℝ) ≤ (n:ℝ)+1 := hm.1.trans hn.2
      have hnm : n ≤ m+1 := by exact_mod_cast hnmReal
      have hmn : m ≤ n+1 := by exact_mod_cast hmnReal
      rcases lt_trichotomy n m with hlt | rfl | hgt
      · have hmEq : m = n+1 := by omega
        subst m
        exact hStripCellMapNeighbor n x hn hm
      · rfl
      · have hnEq : n = m+1 := by omega
        subst n
        exact (hStripCellMapNeighbor m x hm hn).symm
    let actualMarkedStrip (x : ℝ × Interval) : H2 := stripCellMap ⌊x.1⌋ x
    have actual_marked_strip_cell_formula (n : ℤ) (x : ℝ × Interval) (hx : x ∈ stripCell n) :
        actualMarkedStrip x = stripCellMap n x := hStripCellMapMatch _ _ x (hStripCellCover x) hx
    have actual_marked_strip_continuous : Continuous actualMarkedStrip := by
      apply hStripCellLocallyFinite.continuous
      · ext x
        simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
        exact ⟨_,hStripCellCover x⟩
      · exact hStripCellClosed
      · intro n
        apply (hStripCellMapContinuous n).continuousOn.congr
        intro x hx
        exact actual_marked_strip_cell_formula n x hx
    have actual_marked_strip_monodromy (x : ℝ × Interval) :
        actualMarkedStrip (x.1+1,x.2) = developedDeck monodromy (actualMarkedStrip x) := by
      let n : ℤ := ⌊x.1⌋
      have hx : x ∈ stripCell n := hStripCellCover x
      have hx' : (x.1+1,x.2) ∈ stripCell (n+1) := by
        change ((n+1:ℤ):ℝ) ≤ x.1+1 ∧ x.1+1 ≤ ((n+1:ℤ):ℝ)+1
        push_cast
        constructor <;> linarith [hx.1,hx.2]
      rw [actual_marked_strip_cell_formula n x hx,
        actual_marked_strip_cell_formula (n+1) (x.1+1,x.2) hx']
      have hu : (x.1+1)-((n+1:ℤ):ℝ) = x.1-(n:ℝ) := by push_cast; ring
      simp only [stripCellMap,hu]
      exact actual_marked_periodic_disk_monodromy n _
    have actual_marked_strip_bottom (t : ℝ) :
        actualMarkedStrip (t,0) = sourceLift (sourceParameter+t*(2*Real.pi)) := by
      let n : ℤ := ⌊t⌋
      have hn : t-(n:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · linarith [Int.floor_le t]
        · linarith [Int.lt_floor_add_one t]
      rw [actual_marked_strip_cell_formula n (t,0) (hStripCellCover (t,0))]
      simp only [stripCellMap,Set.projIcc_of_mem _ hn]
      rw [actual_marked_periodic_disk_bottom]
      congr 1
      change sourceParameter+(t-(n:ℝ))*(2*Real.pi)+(n:ℝ)*(2*Real.pi) = _
      ring
    have actual_marked_strip_top (t : ℝ) :
        actualMarkedStrip (t,1) = targetLift (targetParameter+t*(2*Real.pi)) := by
      let n : ℤ := ⌊t⌋
      have hn : t-(n:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · linarith [Int.floor_le t]
        · linarith [Int.lt_floor_add_one t]
      rw [actual_marked_strip_cell_formula n (t,1) (hStripCellCover (t,1))]
      simp only [stripCellMap,Set.projIcc_of_mem _ hn]
      rw [actual_marked_periodic_disk_top]
      congr 1
      change targetParameter+(t-(n:ℝ))*(2*Real.pi)+(n:ℝ)*(2*Real.pi) = _
      ring
    have actual_half_open_cell_pasting_injective {X : Type} [TopologicalSpace X]
        (B : ℤ → Interval × Interval → X)
        (hB : ∀ n, Function.Injective (B n))
        (hoverlap : ∀ n m u v, B n u = B m v → n=m ∨ m=n+1 ∨ n=m+1)
        (hneighbor : ∀ n u v, B n u = B (n+1) v → u.1=1 ∧ v.1=0) :
        Function.Injective (fun x : ℝ × Interval =>
          B ⌊x.1⌋ (⟨x.1-(⌊x.1⌋:ℝ),by
            constructor
            · linarith [Int.floor_le x.1]
            · linarith [Int.lt_floor_add_one x.1]⟩,x.2)) := by
      intro x y he
      let n := ⌊x.1⌋
      let m := ⌊y.1⌋
      let u : Interval := ⟨x.1-(n:ℝ),by
        constructor
        · linarith [Int.floor_le x.1]
        · linarith [Int.lt_floor_add_one x.1]⟩
      let v : Interval := ⟨y.1-(m:ℝ),by
        constructor
        · linarith [Int.floor_le y.1]
        · linarith [Int.lt_floor_add_one y.1]⟩
      have he' : B n (u,x.2) = B m (v,y.2) := he
      have huLt : (u:ℝ) < 1 := by change x.1-(⌊x.1⌋:ℝ)<1;linarith [Int.lt_floor_add_one x.1]
      have hvLt : (v:ℝ) < 1 := by change y.1-(⌊y.1⌋:ℝ)<1;linarith [Int.lt_floor_add_one y.1]
      rcases hoverlap n m (u,x.2) (v,y.2) he' with hnm | hnext | hprev
      · have huv : (u,x.2) = (v,y.2) := hB n (hnm ▸ he')
        have huEq : (u:ℝ) = (v:ℝ) := congrArg (fun z : Interval × Interval => (z.1:ℝ)) huv
        apply Prod.ext
        · change x.1-(n:ℝ) = y.1-(m:ℝ) at huEq
          rw [hnm] at huEq
          linarith
        · exact congrArg (fun z : Interval × Interval => z.2) huv
      · have huEq := (hneighbor n (u,x.2) (v,y.2) (hnext ▸ he')).1
        have hval := congrArg Subtype.val huEq
        change (u:ℝ)=1 at hval
        exact False.elim ((ne_of_lt huLt) hval)
      · have hvEq := (hneighbor m (v,y.2) (u,x.2) (hprev ▸ he'.symm)).1
        have hval := congrArg Subtype.val hvEq
        change (v:ℝ)=1 at hval
        exact False.elim ((ne_of_lt hvLt) hval)
    have actual_marked_strip_injective : Function.Injective actualMarkedStrip := by
      have h := actual_half_open_cell_pasting_injective markedPeriodicDisk
        (fun n => (actual_marked_periodic_disk_embedding n).injective)
        actual_marked_periodic_disk_overlap_indices actual_marked_periodic_disk_neighbor_parameters
      have he : actualMarkedStrip = (fun x : ℝ × Interval =>
        markedPeriodicDisk ⌊x.1⌋ (⟨x.1-(⌊x.1⌋:ℝ),by
          constructor
          · linarith [Int.floor_le x.1]
          · linarith [Int.lt_floor_add_one x.1]⟩,x.2)) := by
        funext x
        change markedPeriodicDisk ⌊x.1⌋ (Set.projIcc 0 1 (by norm_num) (x.1-(⌊x.1⌋:ℝ)),x.2) = _
        have hx : x.1-(⌊x.1⌋:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · linarith [Int.floor_le x.1]
          · linarith [Int.lt_floor_add_one x.1]
        rw [Set.projIcc_of_mem _ hx]
      rw [he]
      exact h
    have actual_axis_periodic_strip_proper {X : Type} [MetricSpace X]
        (F : C(ℝ × Interval,X)) (g : X → X) (hg : Isometry g)
        (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
        (htranslate : ∀ t, g (axis t) = axis (t+τ))
        (hperiod : ∀ x : ℝ × Interval, F (x.1+1,x.2) = g (F x)) :
        IsProperMap F := by
      let δ : ℝ × Interval → ℝ := fun x => dist (F x) (axis (x.1*τ))
      have hδcont : Continuous δ := F.continuous.dist
        (haxis.continuous.comp (continuous_fst.mul continuous_const))
      have hδperiod (v : Interval) : Function.Periodic (fun s => δ (s,v)) 1 := by
        intro s
        dsimp [δ]
        have ht : (s+1)*τ = s*τ+τ := by ring
        rw [hperiod (s,v),ht,← htranslate,hg.dist_eq]
      have hcompact : IsCompact (δ '' (Set.Icc (0:ℝ) 1 ×ˢ (Set.univ : Set Interval))) :=
        (isCompact_Icc.prod isCompact_univ).image hδcont
      obtain ⟨M,hM⟩ := hcompact.bddAbove
      have hbound (x : ℝ × Interval) : δ x ≤ M := by
        have hrange : δ x ∈ Set.range (fun s => δ (s,x.2)) := ⟨x.1,rfl⟩
        rw [← (hδperiod x.2).image_Icc (by norm_num : (0:ℝ)<1) 0] at hrange
        obtain ⟨s,hs,hsEq⟩ := hrange
        exact hM ⟨(s,x.2),⟨by simpa using hs,Set.mem_univ _⟩,hsEq⟩
      have hlower (x : ℝ × Interval) : |x.1| * τ-M ≤ dist (F x) (axis 0) := by
        have htri := dist_triangle (axis (x.1*τ)) (F x) (axis 0)
        rw [haxis.dist_eq,Real.dist_eq,sub_zero,abs_mul,abs_of_pos hτ,
          dist_comm (axis (x.1*τ)) (F x)] at htri
        have hb := hbound x
        dsimp [δ] at hb
        linarith
      have hfst : Filter.Tendsto (Prod.fst : ℝ × Interval → ℝ) (Filter.cocompact (ℝ × Interval)) (Filter.cocompact ℝ) :=
        (isProperMap_iff_tendsto_cocompact.mp isProperMap_fst_of_compactSpace).2
      have habs : Filter.Tendsto (fun x : ℝ × Interval => |x.1|) (Filter.cocompact (ℝ × Interval)) Filter.atTop := by
        have hreal : Filter.Tendsto (fun t : ℝ => |t|) (Filter.cocompact ℝ) Filter.atTop := by
          convert tendsto_dist_right_cocompact_atTop (0:ℝ) using 1
          ext t
          simp [Real.dist_eq]
        exact hreal.comp hfst
      have hdist : Filter.Tendsto (fun x : ℝ × Interval => dist (F x) (axis 0)) (Filter.cocompact (ℝ × Interval)) Filter.atTop := by
        apply Filter.tendsto_atTop.mpr
        intro R
        filter_upwards [(Filter.tendsto_atTop.mp habs) ((R+M)/τ)] with x hx
        have h := (div_le_iff₀ hτ).mp hx
        linarith [hlower x]
      exact isProperMap_iff_tendsto_cocompact.mpr
        ⟨F.continuous,tendsto_cocompact_of_tendsto_dist_comp_atTop (axis 0) hdist⟩
    let actualMarkedStripMap : C(ℝ × Interval,H2) := ⟨actualMarkedStrip,actual_marked_strip_continuous⟩
    have actual_marked_strip_proper : IsProperMap actualMarkedStrip :=
      actual_axis_periodic_strip_proper actualMarkedStripMap (developedDeck monodromy)
        (all_developed_decks_isometric monodromy) actualAxis hactualAxis axisPeriod haxisPeriod
        haxisTranslate actual_marked_strip_monodromy
    have actual_marked_strip_closed_embedding : Topology.IsClosedEmbedding actualMarkedStrip :=
      Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
        ⟨actual_marked_strip_continuous,actual_marked_strip_injective,actual_marked_strip_proper.isClosedMap⟩
    have actual_periodic_seam_in_facing_closure (n : ℤ) : periodicSeam n ⊆ closure facingRegion := by
      have h := Set.image_mono hFirstSeamFacingClosure (f := developedDeck (monodromy^n))
      rw [(developedDeck (monodromy^n)).image_closure,
        actual_facing_region_all_integer_monodromy_invariant] at h
      exact h
    have actual_periodic_boundary_in_facing_closure (n : ℤ) : periodicCellBoundary n ⊆ closure facingRegion := by
      intro z hz
      rcases hz with (hs | ht) | (hl | hr)
      · apply frontier_subset_closure
        rw [actual_facing_region_geometry.2.2]
        exact Or.inl (Set.image_subset_range _ _ hs)
      · apply frontier_subset_closure
        rw [actual_facing_region_geometry.2.2]
        exact Or.inr (Set.image_subset_range _ _ ht)
      · exact actual_periodic_seam_in_facing_closure n hl
      · exact actual_periodic_seam_in_facing_closure (n+1) hr
    have actual_marked_strip_range_in_facing_closure : Set.range actualMarkedStrip ⊆ closure facingRegion := by
      rintro z ⟨x,rfl⟩
      have hc := actual_marked_periodic_disk_point_mem_carrier ⌊x.1⌋
        (Set.projIcc 0 1 (by norm_num) (x.1-(⌊x.1⌋:ℝ)),x.2)
      change planeCoordinate (actualMarkedStrip x) ∈ _ at hc
      rcases hc with hi | hb
      · obtain ⟨u,hu,he⟩ := actual_all_periodic_cell_insides_in_facing_region _ hi
        have heu := planeCoordinate.injective he
        exact subset_closure (heu ▸ hu)
      · obtain ⟨u,hu,he⟩ := hb
        have heu := planeCoordinate.injective he
        exact heu ▸ actual_periodic_boundary_in_facing_closure _ hu
    let markedStripInteriorDomain : Set (ℝ × Interval) := {x | (0:ℝ) < x.2.val ∧ x.2.val < 1}
    let markedStripInterior : Set H2 := actualMarkedStrip '' markedStripInteriorDomain
    have actual_marked_strip_interior_avoids_boundary :
        Disjoint markedStripInterior (Set.range sourceLift ∪ Set.range targetLift) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,rfl⟩ (⟨s,hs⟩ | ⟨s,hs⟩)
      · let t : ℝ := (s-sourceParameter)/(2*Real.pi)
        have ht : sourceParameter+t*(2*Real.pi) = s := by dsimp [t]; field_simp; ring
        have he : actualMarkedStrip (t,0) = actualMarkedStrip x := by rw [actual_marked_strip_bottom,ht];exact hs
        have hzero := congrArg (fun y : ℝ × Interval => (y.2:ℝ)) (actual_marked_strip_injective he)
        change 0 = (x.2:ℝ) at hzero
        exact (ne_of_gt hx.1) hzero.symm
      · let t : ℝ := (s-targetParameter)/(2*Real.pi)
        have ht : targetParameter+t*(2*Real.pi) = s := by dsimp [t]; field_simp; ring
        have he : actualMarkedStrip (t,1) = actualMarkedStrip x := by rw [actual_marked_strip_top,ht];exact hs
        have hone := congrArg (fun y : ℝ × Interval => (y.2:ℝ)) (actual_marked_strip_injective he)
        change 1 = (x.2:ℝ) at hone
        exact (ne_of_lt hx.2) hone.symm
    have actual_marked_strip_interior_in_facing : markedStripInterior ⊆ facingRegion := by
      intro z hz
      have hc := actual_marked_strip_range_in_facing_closure (Set.image_subset_range _ _ hz)
      rw [closure_eq_self_union_frontier,actual_facing_region_geometry.2.2] at hc
      rcases hc with hf | hb
      · exact hf
      · exact False.elim (Set.disjoint_left.mp actual_marked_strip_interior_avoids_boundary hz hb)
    have actual_marked_strip_interior_open : IsOpen markedStripInterior := by
      have h := actual_embedded_open_strip_interior (planeCoordinate ∘ actualMarkedStrip)
        (planeCoordinate.isEmbedding.comp actual_marked_strip_closed_embedding.isEmbedding)
      change IsOpen ((planeCoordinate ∘ actualMarkedStrip) '' markedStripInteriorDomain) at h
      rw [Set.image_comp] at h
      exact planeCoordinate.isOpen_image.mp h
    have actual_facing_region_disjoint_lifts : Disjoint facingRegion (Set.range sourceLift ∪ Set.range targetLift) := by
      rw [← actual_facing_region_geometry.2.2]
      exact (disjoint_frontier_iff_isOpen.mpr actual_facing_region_geometry.1).symm
    have actual_marked_strip_range_inter_facing : Set.range actualMarkedStrip ∩ facingRegion = markedStripInterior := by
      ext z
      constructor
      · rintro ⟨⟨x,rfl⟩,hf⟩
        refine ⟨x,?_,rfl⟩
        have hzero : x.2 ≠ 0 := by
          intro he
          have hz : actualMarkedStrip x ∈ Set.range sourceLift := by
            rw [show x = (x.1,0) from Prod.ext rfl he,actual_marked_strip_bottom]
            exact Set.mem_range_self _
          exact Set.disjoint_left.mp actual_facing_region_disjoint_lifts hf (Or.inl hz)
        have hone : x.2 ≠ 1 := by
          intro he
          have hz : actualMarkedStrip x ∈ Set.range targetLift := by
            rw [show x = (x.1,1) from Prod.ext rfl he,actual_marked_strip_top]
            exact Set.mem_range_self _
          exact Set.disjoint_left.mp actual_facing_region_disjoint_lifts hf (Or.inr hz)
        have hzeroVal : (x.2:ℝ) ≠ 0 := fun he => hzero (Subtype.ext he)
        have honeVal : (x.2:ℝ) ≠ 1 := fun he => hone (Subtype.ext he)
        exact ⟨lt_of_le_of_ne x.2.property.1 hzeroVal.symm,lt_of_le_of_ne x.2.property.2 honeVal⟩
      · intro hz
        exact ⟨Set.image_subset_range _ _ hz,actual_marked_strip_interior_in_facing hz⟩
    have actual_marked_strip_interior_relatively_clopen :
        IsClopen ((Subtype.val : facingRegion → H2) ⁻¹' markedStripInterior) := by
      constructor
      · have he : (Subtype.val : facingRegion → H2) ⁻¹' markedStripInterior =
            (Subtype.val : facingRegion → H2) ⁻¹' Set.range actualMarkedStrip := by
          ext z
          rw [← actual_marked_strip_range_inter_facing]
          simp only [Set.mem_preimage,Set.mem_inter_iff,and_iff_left z.property]
        rw [he]
        exact actual_marked_strip_closed_embedding.isClosed_range.preimage continuous_subtype_val
      · exact actual_marked_strip_interior_open.preimage continuous_subtype_val
    have actual_marked_strip_covers_facing_of_connected (hconn : IsConnected facingRegion) :
        markedStripInterior = facingRegion := by
      letI : ConnectedSpace facingRegion := isConnected_iff_connectedSpace.mp hconn
      let x : ℝ × Interval := (0,⟨1/2,by norm_num⟩)
      have hx : actualMarkedStrip x ∈ markedStripInterior := by
        refine ⟨x,?_,rfl⟩
        change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1
        norm_num
      have hne : ((Subtype.val : facingRegion → H2) ⁻¹' markedStripInterior).Nonempty :=
        ⟨⟨actualMarkedStrip x,actual_marked_strip_interior_in_facing hx⟩,hx⟩
      have hall := actual_marked_strip_interior_relatively_clopen.eq_univ hne
      apply Set.Subset.antisymm actual_marked_strip_interior_in_facing
      intro z hz
      have hm : (⟨z,hz⟩ : facingRegion) ∈ (Set.univ : Set facingRegion) := Set.mem_univ _
      rw [← hall] at hm
      exact hm
    open Schoenflies CurveComplexGenusTwo.Topology.PuncturedTorusCandidate Metric Filter in
    have actual_facing_region_connected : IsConnected facingRegion := by
      let PF : C(ℝ,Schoenflies.Plane) := ⟨planeCoordinate ∘ sourceLift,planeCoordinate.continuous.comp sourceLift.continuous⟩
      let PG : C(ℝ,Schoenflies.Plane) := ⟨planeCoordinate ∘ targetLift,planeCoordinate.continuous.comp targetLift.continuous⟩
      have hPFRange : Set.range PF = planeCoordinate '' Set.range sourceLift := by
        exact Set.range_comp (planeCoordinate : H2 → Schoenflies.Plane) (sourceLift : ℝ → H2)
      have hPGRange : Set.range PG = planeCoordinate '' Set.range targetLift := by
        exact Set.range_comp (planeCoordinate : H2 → Schoenflies.Plane) (targetLift : ℝ → H2)
      have hPlaneConn := actual_two_proper_lines_facing_connected PF PG
        (planeCoordinate.isClosedEmbedding.comp actual_targetLift_closed_embedding)
        (planeCoordinate '' sourceInner) (planeCoordinate '' sourceOuter)
        (planeCoordinate '' targetInner) (planeCoordinate '' targetOuter)
        (planeCoordinate.isOpenMap _ hSourceInnerOpen) (planeCoordinate.isOpenMap _ hSourceOuterOpen)
        (planeCoordinate.isOpenMap _ hTargetInnerOpen) (planeCoordinate.isOpenMap _ hTargetOuterOpen)
        (hSourceInnerConn.image _ planeCoordinate.continuous.continuousOn)
        (hSourceOuterConn.image _ planeCoordinate.continuous.continuousOn)
        (hTargetInnerConn.image _ planeCoordinate.continuous.continuousOn)
        (hTargetOuterConn.image _ planeCoordinate.continuous.continuousOn)
        (hSourceSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
        (hTargetSidesDisjoint.image planeCoordinate.injective.injOn (Set.subset_univ _) (Set.subset_univ _))
        (by rw [← Set.image_union,hSourceSidesPartition,planeCoordinate.image_compl,← hPFRange])
        (by rw [← Set.image_union,hTargetSidesPartition,planeCoordinate.image_compl,← hPGRange])
        (by rw [← planeCoordinate.image_frontier,hSourceInnerFrontier,← hPFRange])
        (by rw [← planeCoordinate.image_frontier,hSourceOuterFrontier,← hPFRange])
        (by rw [← planeCoordinate.image_frontier,hTargetInnerFrontier,← hPGRange])
        (by rw [← planeCoordinate.image_frontier,hTargetOuterFrontier,← hPGRange])
        (by rw [hPGRange];exact Set.image_mono hTargetInSourceInner)
        (by rw [hPFRange];exact Set.image_mono hSourceInTargetInner)
        (planeCoordinate.isClosedEmbedding.comp actual_sourceLift_closed_embedding)
      have himage : planeCoordinate '' facingRegion = (planeCoordinate '' sourceInner) ∩ (planeCoordinate '' targetInner) :=
        Set.image_inter planeCoordinate.injective
      rw [← himage] at hPlaneConn
      have hback := hPlaneConn.image planeCoordinate.symm planeCoordinate.symm.continuous.continuousOn
      simpa only [Set.image_image,Function.comp_def,Homeomorph.symm_apply_apply,Set.image_id'] using hback
    have actual_marked_strip_interior_eq_facing : markedStripInterior = facingRegion :=
      actual_marked_strip_covers_facing_of_connected actual_facing_region_connected
    have actual_marked_strip_range_eq_facing_closure : Set.range actualMarkedStrip = closure facingRegion := by
      apply Set.Subset.antisymm actual_marked_strip_range_in_facing_closure
      intro z hz
      rw [closure_eq_self_union_frontier,actual_facing_region_geometry.2.2] at hz
      rcases hz with hf | ⟨t,ht⟩ | ⟨t,ht⟩
      · rw [← actual_marked_strip_interior_eq_facing] at hf
        exact Set.image_subset_range _ _ hf
      · let s : ℝ := (t-sourceParameter)/(2*Real.pi)
        have he : sourceParameter+s*(2*Real.pi) = t := by dsimp [s];field_simp;ring
        refine ⟨(s,0),?_⟩
        rw [actual_marked_strip_bottom,he]
        exact ht
      · let s : ℝ := (t-targetParameter)/(2*Real.pi)
        have he : targetParameter+s*(2*Real.pi) = t := by dsimp [s];field_simp;ring
        refine ⟨(s,1),?_⟩
        rw [actual_marked_strip_top,he]
        exact ht
    have hUS : U=sourceInner := connected_facing_side_unique
      (Set.range sourceLift) (Set.range targetLift) sourceInner sourceOuter U
      hSourceInnerOpen hSourceOuterOpen hSourceInnerConn hSourceSidesDisjoint hSourceSidesPartition
      (Set.range_nonempty targetLift) hTargetInSourceInner hU hcU hfU hTU
    have hVT : V=targetInner := connected_facing_side_unique
      (Set.range targetLift) (Set.range sourceLift) targetInner targetOuter V
      hTargetInnerOpen hTargetOuterOpen hTargetInnerConn hTargetSidesDisjoint hTargetSidesPartition
      (Set.range_nonempty sourceLift) hSourceInTargetInner hV hcV hfV hSV
    obtain ⟨stripAxisBound,stripAxisBound_nonnegative,stripAxisBound_control⟩ :=
      actual_axis_periodic_strip_bounded actualMarkedStripMap (developedDeck monodromy)
        (all_developed_decks_isometric monodromy) actualAxis hactualAxis axisPeriod haxisPeriod
        haxisTranslate actual_marked_strip_monodromy
    have actual_connected_translate_meeting_facing_is_inside
        (R : Set H2) (hconn : IsPreconnected R)
        (hdS : Disjoint R (Set.range sourceLift)) (hdT : Disjoint R (Set.range targetLift))
        (hmeet : (R ∩ facingRegion).Nonempty) : R ⊆ Set.range actualMarkedStrip := by
      have hS : R ⊆ sourceInner ∪ sourceOuter := by
        rw [hSourceSidesPartition]
        exact Set.disjoint_left.mp hdS
      have hT : R ⊆ targetInner ∪ targetOuter := by
        rw [hTargetSidesPartition]
        exact Set.disjoint_left.mp hdT
      obtain ⟨z,hzR,hzFacing⟩ := hmeet
      have hSin : R ⊆ sourceInner := by
        rcases hconn.subset_or_subset hSourceInnerOpen hSourceOuterOpen hSourceSidesDisjoint hS with h | h
        · exact h
        · exact False.elim (Set.disjoint_left.mp hSourceSidesDisjoint hzFacing.1 (h hzR))
      have hTin : R ⊆ targetInner := by
        rcases hconn.subset_or_subset hTargetInnerOpen hTargetOuterOpen hTargetSidesDisjoint hT with h | h
        · exact h
        · exact False.elim (Set.disjoint_left.mp hTargetSidesDisjoint hzFacing.2 (h hzR))
      intro w hw
      have hwf : w ∈ facingRegion := ⟨hSin hw,hTin hw⟩
      rw [←actual_marked_strip_interior_eq_facing] at hwf
      exact Set.image_subset_range _ _ hwf
    have actual_bottom_line_range_in_strip : Set.range sourceLift ⊆ Set.range actualMarkedStrip := by
      rintro z ⟨t,rfl⟩
      refine ⟨((t-sourceParameter)/(2*Real.pi),0),?_⟩
      rw [actual_marked_strip_bottom]
      congr 1
      field_simp
      ring
    have actual_top_line_range_in_strip : Set.range targetLift ⊆ Set.range actualMarkedStrip := by
      rintro z ⟨t,rfl⟩
      refine ⟨((t-targetParameter)/(2*Real.pi),1),?_⟩
      rw [actual_marked_strip_top]
      congr 1
      field_simp
      ring
    have actual_bottom_translate_in_strip_axis
        (k : deck (Sigma.fst : P → A))
        (hk : developedDeck k '' Set.range sourceLift ⊆ Set.range actualMarkedStrip) :
        developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
      apply translated_horizontal_line_stabilizes_axis actualMarkedStrip actualAxis axisNormalizingIsometry
        axisNormalizer_control axisPeriod stripAxisBound haxisPeriod stripAxisBound_nonnegative
        stripAxisBound_control (developedDeckIsometry k) 0
      intro t
      apply hk
      refine Set.mem_image_of_mem _ ?_
      rw [actual_marked_strip_bottom]
      exact Set.mem_range_self _
    have actual_top_translate_in_strip_axis
        (k : deck (Sigma.fst : P → A))
        (hk : developedDeck k '' Set.range targetLift ⊆ Set.range actualMarkedStrip) :
        developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
      apply translated_horizontal_line_stabilizes_axis actualMarkedStrip actualAxis axisNormalizingIsometry
        axisNormalizer_control axisPeriod stripAxisBound haxisPeriod stripAxisBound_nonnegative
        stripAxisBound_control (developedDeckIsometry k) 1
      intro t
      apply hk
      refine Set.mem_image_of_mem _ ?_
      rw [actual_marked_strip_top]
      exact Set.mem_range_self _
    have actual_noncyclic_any_facing_overlap_stabilizes_axis
        (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ, k ≠ monodromy^n)
        (hmeet : (developedDeck k '' facingRegion ∩ facingRegion).Nonempty) :
        developedDeck k '' Set.range actualAxis = Set.range actualAxis := by
      by_cases hs : ((developedDeck k '' Set.range sourceLift) ∩ facingRegion).Nonempty
      · apply actual_bottom_translate_in_strip_axis k
        apply actual_connected_translate_meeting_facing_is_inside _
          ((isConnected_range sourceLift.continuous).image (developedDeck k)
            (developedDeck k).continuous.continuousOn).isPreconnected
          (actual_noncyclic_source_and_target_translates_disjoint k hk).1
        · simpa only [actual_developedDeck_one,Set.image_id'] using
            all_developed_source_target_translates_disjoint k 1
        · exact hs
      by_cases ht : ((developedDeck k '' Set.range targetLift) ∩ facingRegion).Nonempty
      · apply actual_top_translate_in_strip_axis k
        apply actual_connected_translate_meeting_facing_is_inside _
          ((isConnected_range targetLift.continuous).image (developedDeck k)
            (developedDeck k).continuous.continuousOn).isPreconnected
        · simpa only [actual_developedDeck_one,Set.image_id'] using
            (all_developed_source_target_translates_disjoint 1 k).symm
        · exact (actual_noncyclic_source_and_target_translates_disjoint k hk).2
        · exact ht
      have sidecontain (sideIn sideOut : Set H2) (hI : IsOpen sideIn) (hO : IsOpen sideOut) (hd : Disjoint sideIn sideOut)
          (hp : sideIn ∪ sideOut = (Set.range sourceLift)ᶜ)
          (havoid : ¬ ((developedDeck k '' Set.range sourceLift) ∩ facingRegion).Nonempty)
          (hw : (developedDeck k '' sideIn ∩ facingRegion).Nonempty) :
          facingRegion ⊆ developedDeck k '' sideIn := by
        have hsub : facingRegion ⊆ developedDeck k '' sideIn ∪ developedDeck k '' sideOut := by
          rw [←Set.image_union,hp,(developedDeck k).image_compl]
          intro z hz hzb
          exact havoid ⟨z,hzb,hz⟩
        rcases actual_facing_region_connected.isPreconnected.subset_or_subset
          ((developedDeck k).isOpenMap _ hI) ((developedDeck k).isOpenMap _ hO)
          (hd.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _)) hsub with h | h
        · exact h
        · obtain ⟨z,hzI,hzf⟩ := hw
          exact False.elim (Set.disjoint_left.mp
            (hd.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _)) hzI (h hzf))
      have sourcecontain : facingRegion ⊆ developedDeck k '' sourceInner := by
        apply sidecontain sourceInner sourceOuter hSourceInnerOpen hSourceOuterOpen
          hSourceSidesDisjoint hSourceSidesPartition hs
        obtain ⟨z,⟨w,hw,rfl⟩,hz⟩ := hmeet
        exact ⟨developedDeck k w,⟨w,hw.1,rfl⟩,hz⟩
      have targetcontain : facingRegion ⊆ developedDeck k '' targetInner := by
        have hsub : facingRegion ⊆ developedDeck k '' targetInner ∪ developedDeck k '' targetOuter := by
          rw [←Set.image_union,hTargetSidesPartition,(developedDeck k).image_compl]
          intro z hz hzb
          exact ht ⟨z,hzb,hz⟩
        rcases actual_facing_region_connected.isPreconnected.subset_or_subset
          ((developedDeck k).isOpenMap _ hTargetInnerOpen) ((developedDeck k).isOpenMap _ hTargetOuterOpen)
          (hTargetSidesDisjoint.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _)) hsub with h | h
        · exact h
        · obtain ⟨z,⟨w,hw,he⟩,hz⟩ := hmeet
          exact False.elim (Set.disjoint_left.mp
            (hTargetSidesDisjoint.image (developedDeck k).injective.injOn (Set.subset_univ _) (Set.subset_univ _))
            ⟨w,hw.2,he⟩ (h hz))
      have hf : facingRegion ⊆ developedDeck k '' facingRegion := by
        intro z hz
        obtain ⟨s,hsI,hsz⟩ := sourcecontain hz
        obtain ⟨t,htI,htz⟩ := targetcontain hz
        have hst : s = t := (developedDeck k).injective (hsz.trans htz.symm)
        exact ⟨s,⟨hsI,hst ▸ htI⟩,hsz⟩
      have hclosed : Set.range actualMarkedStrip ⊆ developedDeck k '' Set.range actualMarkedStrip := by
        rw [actual_marked_strip_range_eq_facing_closure,(developedDeck k).image_closure]
        exact closure_mono hf
      have hinverse : developedDeck k⁻¹ '' Set.range sourceLift ⊆ Set.range actualMarkedStrip := by
        rintro _ ⟨z,hz,rfl⟩
        obtain ⟨w,hw,hwe⟩ := hclosed (actual_bottom_line_range_in_strip hz)
        have hmul := actual_developedDeck_mul k⁻¹ k w
        rw [inv_mul_cancel] at hmul
        rw [actual_developedDeck_one] at hmul
        rw [←hwe]
        exact hmul ▸ hw
      have haxisinv := actual_bottom_translate_in_strip_axis k⁻¹ hinverse
      have him := congrArg (fun S : Set H2 => developedDeck k '' S) haxisinv
      rw [Set.image_image] at him
      have hcomp : (developedDeck k) ∘ (developedDeck k⁻¹) = id := by
        funext z
        have h := actual_developedDeck_mul k k⁻¹ z
        rw [mul_inv_cancel,actual_developedDeck_one] at h
        exact h.symm
      change ((developedDeck k) ∘ (developedDeck k⁻¹)) '' Set.range actualAxis = developedDeck k '' Set.range actualAxis at him
      rw [hcomp,Set.image_id] at him
      exact him.symm
    have actual_strip_point_in_facing_or_boundary (x : ℝ × Interval) :
        actualMarkedStrip x ∈ facingRegion ∨ actualMarkedStrip x ∈ Set.range sourceLift ∨
          actualMarkedStrip x ∈ Set.range targetLift := by
      by_cases h0 : x.2=0
      · right;left
        rw [show x=(x.1,0) from Prod.ext rfl h0,actual_marked_strip_bottom]
        exact Set.mem_range_self _
      by_cases h1 : x.2=1
      · right;right
        rw [show x=(x.1,1) from Prod.ext rfl h1,actual_marked_strip_top]
        exact Set.mem_range_self _
      left
      apply actual_marked_strip_interior_in_facing
      refine ⟨x,?_,rfl⟩
      constructor
      · change (0:ℝ)<(x.2:ℝ)
        by_contra h
        have he : (x.2:ℝ)=0 := le_antisymm (le_of_not_gt h) x.2.property.1
        exact h0 (Subtype.ext he)
      · change (x.2:ℝ)<1
        by_contra h
        have he : (x.2:ℝ)=1 := le_antisymm x.2.property.2 (le_of_not_gt h)
        exact h1 (Subtype.ext he)
    have actual_noncyclic_closed_strip_overlap_stabilizes_axis
        (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ, k ≠ monodromy^n)
        (hmeet : (developedDeck k '' Set.range actualMarkedStrip ∩ Set.range actualMarkedStrip).Nonempty) :
        developedDeck k '' Set.range actualAxis=Set.range actualAxis := by
      have hkInv : ∀ n : ℤ, k⁻¹ ≠ monodromy^n := by
        intro n hn
        apply hk (-n)
        have h := congrArg Inv.inv hn
        simpa only [inv_inv,←_root_.zpow_neg] using h
      have boundaryMeetingAxis (l : deck (Sigma.fst : P → A)) (hl : ∀ n : ℤ,l ≠ monodromy^n)
          (K : C(ℝ,H2)) (hc : IsConnected (Set.range K))
          (hdS : Disjoint (developedDeck l '' Set.range K) (Set.range sourceLift))
          (hdT : Disjoint (developedDeck l '' Set.range K) (Set.range targetLift))
          (hrow : K=sourceLift ∨ K=targetLift)
          (h : (developedDeck l '' Set.range K ∩ facingRegion).Nonempty) :
          developedDeck l '' Set.range actualAxis=Set.range actualAxis := by
        have hin := actual_connected_translate_meeting_facing_is_inside _
          (hc.image (developedDeck l) (developedDeck l).continuous.continuousOn).isPreconnected hdS hdT h
        rcases hrow with rfl | rfl
        · exact actual_bottom_translate_in_strip_axis l hin
        · exact actual_top_translate_in_strip_axis l hin
      have inverseAxis (h : developedDeck k⁻¹ '' Set.range actualAxis=Set.range actualAxis) :
          developedDeck k '' Set.range actualAxis=Set.range actualAxis := by
        have hh := congrArg (fun A : Set H2 => developedDeck k '' A) h
        rw [Set.image_image] at hh
        have he : (developedDeck k) ∘ (developedDeck k⁻¹)=id := by
          funext z
          have hm := actual_developedDeck_mul k k⁻¹ z
          rw [mul_inv_cancel,actual_developedDeck_one] at hm
          exact hm.symm
        change ((developedDeck k) ∘ (developedDeck k⁻¹)) '' Set.range actualAxis=developedDeck k '' Set.range actualAxis at hh
        rw [he,Set.image_id] at hh
        exact hh.symm
      have crossST (l : deck (Sigma.fst : P → A)) :
          Disjoint (developedDeck l '' Set.range sourceLift) (Set.range targetLift) := by
        simpa only [actual_developedDeck_one,Set.image_id'] using all_developed_source_target_translates_disjoint l 1
      have crossTS (l : deck (Sigma.fst : P → A)) :
          Disjoint (developedDeck l '' Set.range targetLift) (Set.range sourceLift) := by
        simpa only [actual_developedDeck_one,Set.image_id'] using (all_developed_source_target_translates_disjoint 1 l).symm
      obtain ⟨z,⟨_,⟨x,rfl⟩,hx⟩,⟨y,hy⟩⟩ := hmeet
      have hxy : developedDeck k (actualMarkedStrip x)=actualMarkedStrip y := hx.trans hy.symm
      have hinv : developedDeck k⁻¹ (actualMarkedStrip y)=actualMarkedStrip x := by
        have h := actual_developedDeck_mul k⁻¹ k (actualMarkedStrip x)
        rw [inv_mul_cancel,actual_developedDeck_one,hxy] at h
        exact h.symm
      rcases actual_strip_point_in_facing_or_boundary x with hxf | hxs | hxt
      · rcases actual_strip_point_in_facing_or_boundary y with hyf | hys | hyt
        · exact actual_noncyclic_any_facing_overlap_stabilizes_axis k hk ⟨_,⟨_,hxf,hxy⟩,hyf⟩
        · apply inverseAxis
          exact boundaryMeetingAxis k⁻¹ hkInv sourceLift (isConnected_range sourceLift.continuous)
            (actual_noncyclic_source_and_target_translates_disjoint k⁻¹ hkInv).1 (crossST k⁻¹)
            (Or.inl rfl) ⟨_,⟨_,hys,hinv⟩,hxf⟩
        · apply inverseAxis
          exact boundaryMeetingAxis k⁻¹ hkInv targetLift (isConnected_range targetLift.continuous)
            (crossTS k⁻¹) (actual_noncyclic_source_and_target_translates_disjoint k⁻¹ hkInv).2
            (Or.inr rfl) ⟨_,⟨_,hyt,hinv⟩,hxf⟩
      · rcases actual_strip_point_in_facing_or_boundary y with hyf | hys | hyt
        · exact boundaryMeetingAxis k hk sourceLift (isConnected_range sourceLift.continuous)
            (actual_noncyclic_source_and_target_translates_disjoint k hk).1 (crossST k)
            (Or.inl rfl) ⟨_,⟨_,hxs,hxy⟩,hyf⟩
        · exact False.elim (Set.disjoint_left.mp (actual_noncyclic_source_and_target_translates_disjoint k hk).1 ⟨_,hxs,hxy⟩ hys)
        · exact False.elim (Set.disjoint_left.mp (crossST k) ⟨_,hxs,hxy⟩ hyt)
      · rcases actual_strip_point_in_facing_or_boundary y with hyf | hys | hyt
        · exact boundaryMeetingAxis k hk targetLift (isConnected_range targetLift.continuous)
            (crossTS k) (actual_noncyclic_source_and_target_translates_disjoint k hk).2
            (Or.inr rfl) ⟨_,⟨_,hxt,hxy⟩,hyf⟩
        · exact False.elim (Set.disjoint_left.mp (crossTS k) ⟨_,hxt,hxy⟩ hys)
        · exact False.elim (Set.disjoint_left.mp (actual_noncyclic_source_and_target_translates_disjoint k hk).2 ⟨_,hxt,hxy⟩ hyt)
    have actual_index_two_glide_separated_strip_has_full_deck_separation
        (hindex : originalAxisNatIndex=2)
        (hglide : Disjoint (developedDeck minimalAxisDeck.val '' Set.range actualMarkedStrip)
          (Set.range actualMarkedStrip))
        (k : deck (Sigma.fst : P → A)) (hk : ∀ n : ℤ,k ≠ monodromy^n) :
        Disjoint (developedDeck k '' Set.range actualMarkedStrip) (Set.range actualMarkedStrip) := by
      apply Set.disjoint_left.mpr
      intro z hz1 hz2
      have haxis := actual_noncyclic_closed_strip_overlap_stabilizes_axis k hk ⟨z,hz1,hz2⟩
      let kAxis : axisStabilizer := ⟨k,actual_axis_preserving_deck_in_stabilizer k haxis⟩
      obtain ⟨n,hn⟩ := actual_every_axis_stabilizer_is_minimal_generator_power kAxis
      have hpower : k=minimalAxisDeck.val^n := congrArg Subtype.val hn
      have hmono : monodromy=minimalAxisDeck.val^2 := by
        rw [original_monodromy_minimal_axis_nat_root,hindex]
      obtain ⟨m,hm | hm⟩ := square_generator_cosets monodromy minimalAxisDeck.val hmono n
      · exact hk m (hpower.trans hm)
      · have hcoset : k=minimalAxisDeck.val*monodromy^m := by
          rw [hpower,hm]
          have hc : Commute minimalAxisDeck.val monodromy := by
            rw [hmono]
            exact (Commute.refl minimalAxisDeck.val).pow_right 2
          exact (hc.zpow_right m).symm.eq
        have hperiodRange : developedDeck (monodromy^m) '' Set.range actualMarkedStrip=Set.range actualMarkedStrip := by
          rw [actual_marked_strip_range_eq_facing_closure,(developedDeck (monodromy^m)).image_closure,
            actual_facing_region_all_integer_monodromy_invariant]
        have hImg : developedDeck k '' Set.range actualMarkedStrip=
            developedDeck minimalAxisDeck.val '' Set.range actualMarkedStrip := by
          rw [hcoset]
          have hcomp : (developedDeck (minimalAxisDeck.val*monodromy^m))=
              (developedDeck (monodromy^m)).trans (developedDeck minimalAxisDeck.val) := by
            apply Homeomorph.ext
            intro w
            exact actual_developedDeck_mul minimalAxisDeck.val (monodromy^m) w
          rw [hcomp]
          change ((developedDeck minimalAxisDeck.val) ∘ developedDeck (monodromy^m)) '' _=_
          exact (Set.image_image (developedDeck minimalAxisDeck.val) (developedDeck (monodromy^m))
          (Set.range actualMarkedStrip)).symm.trans
            (congrArg (fun A : Set H2 => developedDeck minimalAxisDeck.val '' A) hperiodRange)
        rw [hImg] at hz1
        exact Set.disjoint_left.mp hglide hz1 hz2
    have hglide : Disjoint (developedDeck minimalAxisDeck.val '' Set.range actualMarkedStrip)
        (Set.range actualMarkedStrip) := by
      rw [actual_marked_strip_range_eq_facing_closure]
      simpa only [hUS,hVT] using hBand
    have descent {Y : Type} [TopologicalSpace Y] (f : C(ℝ × unitInterval,Y))
        (hperiod : ∀ x : ℝ × unitInterval, f (x.1+1,x.2) = f x) :
        ∃ F : C(AddCircle (1:ℝ) × unitInterval,Y), ∀ x : ℝ × unitInterval,
          F ((x.1 : AddCircle (1:ℝ)),x.2) = f x := by
      have hp : Function.Periodic f.curry (1:ℝ) := by
        intro t
        apply ContinuousMap.ext
        intro u
        exact hperiod (t,u)
      let L : AddCircle (1:ℝ) → C(unitInterval,Y) := hp.lift
      have hL : Continuous L := by
        exact f.curry.continuous.quotient_lift _
      let F : C(AddCircle (1:ℝ) × unitInterval,Y) := ContinuousMap.uncurry ⟨L,hL⟩
      refine ⟨F,?_⟩
      intro x
      change hp.lift (x.1 : AddCircle (1:ℝ)) x.2 = f x
      rw [hp.lift_coe]
      rfl
    have actual_marked_strip_integer_monodromy (n : ℤ) (t : ℝ) (u : Interval) :
        actualMarkedStrip (t+(n:ℝ),u)=developedDeck (monodromy^n) (actualMarkedStrip (t,u)) := by
      let f : ℝ → H2 := fun s => actualMarkedStrip (s/(2*Real.pi),u)
      have hp (s : ℝ) : f (s+2*Real.pi)=developedDeck monodromy (f s) := by
        change actualMarkedStrip ((s+2*Real.pi)/(2*Real.pi),u) = _
        rw [show (s+2*Real.pi)/(2*Real.pi)=s/(2*Real.pi)+1 by field_simp <;> ring]
        exact actual_marked_strip_monodromy (s/(2*Real.pi),u)
      have h := actual_common_monodromy_integer_period f hp n (t*(2*Real.pi))
      have ha : (t*(2*Real.pi)+(n:ℝ)*(2*Real.pi))/(2*Real.pi)=t+(n:ℝ) := by field_simp <;> ring
      have hb : (t*(2*Real.pi))/(2*Real.pi)=t := mul_div_cancel_right₀ t (by positivity)
      simpa only [f,ha,hb] using h
    have actual_glide_separated_embedded_annulus :
        ∃ F : C(AddCircle (1:ℝ) × Interval,E), Topology.IsClosedEmbedding F ∧
          (∀ t : ℝ, F ((t:AddCircle (1:ℝ)),0)=a.map (Circle.exp (sourceParameter+t*(2*Real.pi)))) ∧
          (∀ t : ℝ, F ((t:AddCircle (1:ℝ)),1)=b.map (Circle.exp (targetParameter+t*(2*Real.pi)))) := by
      let projectedStrip : C(ℝ × Interval,E) :=
        ⟨developedProjection ∘ actualMarkedStrip,
          developedProjection_continuous.comp actual_marked_strip_continuous⟩
      have hp (x : ℝ × Interval) : projectedStrip (x.1+1,x.2)=projectedStrip x := by
        change developedProjection (actualMarkedStrip (x.1+1,x.2)) = _
        rw [actual_marked_strip_monodromy,developedDeck_projection]
        rfl
      obtain ⟨F,hclock⟩ := descent projectedStrip hp
      have hF : Function.Injective F := by
        rintro ⟨x,u⟩ ⟨y,v⟩ he
        obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective x
        obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective y
        subst x
        subst y
        rw [hclock (t,u),hclock (s,v)] at he
        have hproj : (development.symm (actualMarkedStrip (t,u))).1 =
            (development.symm (actualMarkedStrip (s,v))).1 := Subtype.ext he
        obtain ⟨k,hk⟩ := hqc.apply_eq_iff_mem_orbit.mp hproj
        change k • development.symm (actualMarkedStrip (s,v)) =
          development.symm (actualMarkedStrip (t,u)) at hk
        have heDeck : developedDeck k (actualMarkedStrip (s,v)) = actualMarkedStrip (t,u) := by
          change development (k • development.symm (actualMarkedStrip (s,v))) = _
          rw [hk,development.apply_symm_apply]
        have hcyclic : ∃ n : ℤ, k=monodromy^n := by
          by_contra h
          have hkout : ∀ n : ℤ, k≠monodromy^n := by simpa using h
          exact Set.disjoint_left.mp (actual_index_two_glide_separated_strip_has_full_deck_separation hindex hglide k hkout)
            ⟨actualMarkedStrip (s,v),Set.mem_range_self _,heDeck⟩ (Set.mem_range_self _)
        obtain ⟨n,rfl⟩ := hcyclic
        rw [←actual_marked_strip_integer_monodromy] at heDeck
        have hePair := actual_marked_strip_injective heDeck
        have heFirst : s+(n:ℝ)=t := congrArg Prod.fst hePair
        have heSecond : v=u := congrArg Prod.snd hePair
        apply Prod.ext
        · rw [←heFirst,AddCircle.coe_add]
          have hn : ((n:ℝ):AddCircle (1:ℝ))=0 := by
            have h := AddCircle.coe_zsmul (p:=(1:ℝ)) (n:=n) (x:=(1:ℝ))
            simpa only [zsmul_eq_mul,mul_one,AddCircle.coe_period,smul_zero] using h
          rw [hn,add_zero]
        · exact heSecond.symm
      refine ⟨F,F.continuous.isClosedEmbedding hF,?_,?_⟩
      · intro t
        rw [hclock (t,0)]
        change developedProjection (actualMarkedStrip (t,0)) = _
        rw [actual_marked_strip_bottom,sourceLift_projection]
      · intro t
        rw [hclock (t,1)]
        change developedProjection (actualMarkedStrip (t,1)) = _
        rw [actual_marked_strip_top,targetLift_projection]
    have actual_glide_separated_source_curves_have_collared_annulus :
        ∃ B : C(Circle × Interval,E), Topology.IsEmbedding B ∧
          Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))=a.image ∧
          Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))=b.image := by
      obtain ⟨F,hF,hF0,hF1⟩ := actual_glide_separated_embedded_annulus
      let circleClock : AddCircle (1:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
      let param : Circle × Interval ≃ₜ AddCircle (1:ℝ) × Interval :=
        circleClock.symm.prodCongr (Homeomorph.refl Interval)
      let f : C(Circle × Interval,E) := ⟨F ∘ param,F.continuous.comp param.continuous⟩
      have hf : Topology.IsEmbedding f := hF.isEmbedding.comp param.isEmbedding
      let r0 : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp sourceParameter)
      let r1 : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp targetParameter)
      have hf0 (z : Circle) : f (z,0)=a.map (r0 z) := by
        obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (circleClock.symm z)
        have hz : Circle.exp (t*(2*Real.pi))=z := by
          have h := congrArg circleClock ht
          simpa only [circleClock,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,
            div_one,mul_comm,circleClock.apply_symm_apply] using h
        change F (circleClock.symm z,0)=_
        rw [←ht,hF0,Circle.exp_add,hz]
        rfl
      have hf1 (z : Circle) : f (z,1)=b.map (r1 z) := by
        obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (circleClock.symm z)
        have hz : Circle.exp (t*(2*Real.pi))=z := by
          have h := congrArg circleClock ht
          simpa only [circleClock,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk,
            div_one,mul_comm,circleClock.apply_symm_apply] using h
        change F (circleClock.symm z,1)=_
        rw [←ht,hF1,Circle.exp_add,hz]
        rfl
      let p0 : Set.Ioo (-1:ℝ) 1 × Circle ≃ₜ Set.Ioo (-1:ℝ) 1 × Circle :=
        (Homeomorph.refl _).prodCongr r0
      let p1 : Set.Ioo (-1:ℝ) 1 × Circle ≃ₜ Set.Ioo (-1:ℝ) 1 × Circle :=
        (Homeomorph.refl _).prodCongr r1
      let e0 : C(Set.Ioo (-1:ℝ) 1 × Circle,E) := ⟨d0 ∘ p0,d0.continuous.comp p0.continuous⟩
      let e1 : C(Set.Ioo (-1:ℝ) 1 × Circle,E) := ⟨d1 ∘ p1,d1.continuous.comp p1.continuous⟩
      have he0 : Topology.IsOpenEmbedding e0 := hd0.comp p0.isOpenEmbedding
      have he1 : Topology.IsOpenEmbedding e1 := hd1.comp p1.isOpenEmbedding
      have hc0 (z : Circle) : e0 (⟨0,by norm_num⟩,z)=f (z,0) := by
        change d0 (⟨0,by norm_num⟩,r0 z)=_
        rw [hzero0,hcenter0,hf0]
      have hc1 (z : Circle) : e1 (⟨0,by norm_num⟩,z)=f (z,1) := by
        change d1 (⟨0,by norm_num⟩,r1 z)=_
        rw [hzero1,hcenter1,hf1]
      have heDis : Disjoint (Set.range e0) (Set.range e1) := by
        apply (hNdis.mono hrange0 hrange1).mono
        · rintro _ ⟨x,rfl⟩;exact Set.mem_range_self (p0 x)
        · rintro _ ⟨x,rfl⟩;exact Set.mem_range_self (p1 x)
      obtain ⟨B,hB,hgiven⟩ := actualFullCollarsExtendGivenAnnulus f hf e0 e1 he0 he1 hc0 hc1 heDis
      have hrow0 (z : Circle) : B (z,⟨1/3,by norm_num⟩)=a.map (r0 z) := by
        have h := hgiven z 0
        simpa only [show ((0:Interval):ℝ)=0 from rfl,zero_add,hf0] using h
      have hrow1 (z : Circle) : B (z,⟨2/3,by norm_num⟩)=b.map (r1 z) := by
        have h := hgiven z 1
        simpa only [show ((1:Interval):ℝ)=1 from rfl,show (1:ℝ)+1=2 by norm_num,hf1] using h
      refine ⟨B,hB,?_,?_⟩
      · change Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))=Set.range a.map
        simp_rw [hrow0]
        change Set.range (a.map ∘ r0)=Set.range a.map
        rw [Set.range_comp,Set.range_eq_univ.mpr r0.surjective,Set.image_univ]
      · change Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))=Set.range b.map
        simp_rw [hrow1]
        change Set.range (b.map ∘ r1)=Set.range b.map
        rw [Set.range_comp,Set.range_eq_univ.mpr r1.surjective,Set.image_univ]
    obtain ⟨B,hB,hBa,hBb⟩ := actual_glide_separated_source_curves_have_collared_annulus
    exact ⟨B,hB,hBa,hBb,actual_embedded_annulus_interior_isOpen B hB⟩

  have actual_index_two_original_disjoint_curves_have_collared_annulus
      (hindex : originalAxisNatIndex=2) :
      ∃ B : C(Circle × Interval,E), Topology.IsEmbedding B ∧
        Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))=a.image ∧
        Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))=b.image ∧
        IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
    obtain ⟨j,hj,U,V,hU,hV,hUc,hVc,hfrontU,hfrontV,hjU,h0V,hBand⟩ :=
      actual_index_two_source_lifts_admit_glide_disjoint_facing_band hindex
    have hSourceRange : axisPlane '' Set.range sourceLift=Set.range normalizedSource := by
      exact (Set.range_comp axisPlane sourceLift).symm
    obtain ⟨K,hKproj,hKperiod,hKrange⟩ :
        ∃ K : C(ℝ,H2), (∀ t,developedProjection (K t)=b.map (Circle.exp t)) ∧
          (∀ t,K (t+2*Real.pi)=developedDeck monodromy (K t)) ∧
          axisPlane '' Set.range K=Set.range (fourBoundaryLifts j) := by
      rcases hj with rfl | rfl
      · refine ⟨targetLift,targetLift_projection,targetLift_period,?_⟩
        change axisPlane '' Set.range targetLift=Set.range normalizedTarget
        exact (Set.range_comp axisPlane targetLift).symm
      · refine ⟨alternativeTargetLift,actual_alternative_target_literal_projection,
          actual_alternative_target_common_monodromy hindex,?_⟩
        change axisPlane '' Set.range alternativeTargetLift=Set.range glideTarget
        ext z
        constructor
        · rintro ⟨_,⟨t,rfl⟩,rfl⟩
          refine ⟨t,?_⟩
          change minimalGlidePlane (axisPlane (targetLift t))=
            axisPlane (developedDeck minimalAxisDeck.val (targetLift t))
          simp only [minimalGlidePlane,Homeomorph.trans_apply,axisPlane.symm_apply_apply]
        · rintro ⟨t,rfl⟩
          refine ⟨alternativeTargetLift t,Set.mem_range_self t,?_⟩
          change axisPlane (developedDeck minimalAxisDeck.val (targetLift t))=
            minimalGlidePlane (axisPlane (targetLift t))
          simp only [minimalGlidePlane,Homeomorph.trans_apply,axisPlane.symm_apply_apply]
    let UH : Set H2 := axisPlane.symm '' U
    let VH : Set H2 := axisPlane.symm '' V
    have hUH : IsOpen UH := axisPlane.symm.isOpenMap U hU
    have hVH : IsOpen VH := axisPlane.symm.isOpenMap V hV
    have hcUH : IsConnected UH := hUc.image axisPlane.symm axisPlane.symm.continuous.continuousOn
    have hcVH : IsConnected VH := hVc.image axisPlane.symm axisPlane.symm.continuous.continuousOn
    have hBackSource : axisPlane.symm '' Set.range normalizedSource=Set.range sourceLift := by
      rw [←hSourceRange,Set.image_image]
      simp only [Function.comp_def,axisPlane.symm_apply_apply,Set.image_id']
    have hBackTarget : axisPlane.symm '' Set.range (fourBoundaryLifts j)=Set.range K := by
      rw [←hKrange,Set.image_image]
      simp only [Function.comp_def,axisPlane.symm_apply_apply,Set.image_id']
    have hfUH : frontier UH=Set.range sourceLift := by
      rw [←axisPlane.symm.image_frontier,hfrontU,hBackSource]
    have hfVH : frontier VH=Set.range K := by
      rw [←axisPlane.symm.image_frontier,hfrontV,hBackTarget]
    have hKUH : Set.range K ⊆ UH := by
      rw [←hBackTarget]
      exact Set.image_mono hjU
    have hSVH : Set.range sourceLift ⊆ VH := by
      rw [←hBackSource]
      exact Set.image_mono h0V
    have hImageBand : axisPlane '' closure (UH∩VH)=closure (U∩V) := by
      rw [axisPlane.image_closure]
      have hInter : UH∩VH=axisPlane.symm '' (U∩V) :=
        (Set.image_inter axisPlane.symm.injective).symm
      rw [hInter,Set.image_image]
      simp only [Function.comp_def,axisPlane.apply_symm_apply,Set.image_id']
    have hConjugate (x : H2) : axisPlane (developedDeck minimalAxisDeck.val x)=
        minimalGlidePlane (axisPlane x) := by
      simp only [minimalGlidePlane,Homeomorph.trans_apply,axisPlane.symm_apply_apply]
    have hClosedBand : Disjoint (developedDeck minimalAxisDeck.val '' closure (UH∩VH))
        (closure (UH∩VH)) := by
      apply (Set.disjoint_image_iff axisPlane.injective).mp
      have hGlideImg : axisPlane '' (developedDeck minimalAxisDeck.val '' closure (UH∩VH))=
          minimalGlidePlane '' closure (U∩V) := by
        rw [Set.image_image,←hImageBand,Set.image_image]
        congr 1
        funext x
        exact hConjugate x
      rw [hGlideImg,hImageBand]
      exact hBand.symm
    exact selected_target_glide_separated_collared_annulus K hKproj hKperiod UH VH
      hUH hVH hcUH hcVH hfUH hfVH hKUH hSVH hindex hClosedBand

  rcases actual_source_minimal_axis_index_one_or_two with hindex | hindex
  · obtain ⟨B,hB,hBa,hBb⟩ := actual_index_one_source_curves_have_collared_annulus hindex
    exact ⟨B,hB,hBa,hBb,actual_embedded_annulus_interior_isOpen B hB⟩
  · obtain ⟨B,hB,hBa,hBb,hopen⟩ := actual_index_two_original_disjoint_curves_have_collared_annulus hindex
    exact ⟨B,hB,hBa,hBb,hopen⟩

end CurveComplex.Hyperbolic
