import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasPrescribedV
import CurveComplexGenusTwo.Topology.ActualCircleReflectionHomotopy.ActualCircleConjugatedReflectionFreeHomotopyPrivate
import CurveComplexGenusTwo.Hyperbolic.ActualHaasSourceBridges.HaasActualPrimitiveAxisOtherLiftUnionClosedReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.TopologicalPrescribedV
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCutStabilizerQuotientSameActionReviewRequest
import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceSidesTransport
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualInternalSurfaceSides
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualFreeHomotopyIntegerMeridianSuppliedRootSameComponentReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasPantsLocalMetricDescentReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasPantsFixedPointReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasNormalizedBoundaryGeometryReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasNormalizedBoundaryHullCenterInteriorReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasH2MetricConvexClosureReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasSourceBridges.PantsAlgebra
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasHalfTurnReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualSuppliedDeckPositiveUniformDisplacement
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualSimultaneousSeparatedAxesNormalization
import CurveComplexGenusTwo.Hyperbolic.ActualHaasSourceBridges.HaasActualOriginalCutSuppliedAxisFrameSignedSLActionSourceReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOriginalLiteralCylinderFreeGeneratorsSameComponentPrimitiveAxesSourceReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualLiteralThreePrimitiveBoundaryAxisOrbitsDistinctReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOriginalCutPrimitiveBoundaryAxisThreeOrbitDictionarySourceReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualSameFreeBasisSameComplexChartPeripheralMonodromySourceScaffold
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualSameComplexChartMeridianCutClockIdentificationReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualSuppliedPeripheralMonodromySameComponentConjugacyReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOriginalSeparatingCSidePrimitiveBoundaryMonodromyFrontierSourceReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPuncturedCylinderDoublePlaneProof
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2TranslatedAxesUniqueComposablePROVED
import CurveComplexGenusTwo.Topology.PrimitiveEssential
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOriginalSeparatingCSideLiteralMeridianUnitPrimitiveAxisSameComponentSourceReviewRequest
import CurveComplexGenusTwo.Topology.ActualCutRecognition.SharedActualCut
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualSimpleClosedGeodesicEssentialPROVED
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualNondividingCutSideMarkedStraighteningReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOriginalCutDeckAmbientMonodromyReviewRequest
-- Static identifier bridge to the pinned canonical private kernel declaration.
open Lean in
macro:max "haasFrozenCircleReflection%" : term => do
  let mut n := Name.mkStr Name.anonymous "_private"
  for c in "CurveComplexGenusTwo.Topology.ActualCircleReflectionHomotopy.ActualCircleConjugatedReflectionFreeHomotopyPrivate".splitOn "." do
    n := Name.mkStr n c
  n := Name.mkNum n 0
  for c in "CurveComplex.Hyperbolic.actual_circle_homeomorph_conjugated_rotated_inverse_free_homotopic_inverse".splitOn "." do
    n := Name.mkStr n c
  `(term| @$(mkIdent n):ident)
open Set Topology Filter Metric
open scoped Pointwise UpperHalfPlane MatrixGroups unitInterval
open CurveComplex CurveComplex.Hyperbolic CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
set_option maxHeartbeats 24000000
set_option maxRecDepth 12000
open Schoenflies CurveComplexGenusTwo.Topology
theorem haas_both_orientations_with_v {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
    (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
    (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
    (hcdiv : DividingCurve c) (hdnondiv : ¬DividingCurve d) (hcd : Disjoint c.image d.image) :
    ∃J : E ≃ₜ E,Function.Involutive J ∧
    (∀x : E,∃W : Set E,IsOpen W ∧ x∈W ∧ ∀y∈W,∀z∈W,
      @dist E H.metric.toDist (J y) (J z)=@dist E H.metric.toDist y z) ∧
    J '' c.image=c.image ∧ J '' d.image=d.image ∧
    ∃F : Finset E,F.card=6 ∧ (F:Set E)={x | J x=x} ∧
    ∃φc : Circle ≃ₜ Circle,(∀z : Circle,J (c.map z)=c.map (φc z)) ∧
      FreeHomotopic ⟨φc,φc.continuous⟩ ⟨id,continuous_id⟩ ∧
    ∃ud : Circle,∃ed φd : Circle ≃ₜ Circle,
      (∀z : Circle,φd z=ed.symm (ud*(ed z)⁻¹)) ∧
      (∀z : Circle,J (d.map z)=d.map (φd z)) ∧
      FreeHomotopic ⟨φd,φd.continuous⟩ ⟨fun z : Circle=>z⁻¹,continuous_inv⟩ := by
  have hReflectionHom (ed φd : Circle ≃ₜ Circle) (ud : Circle)
      (hclock : ∀z : Circle,φd z=ed.symm (ud*(ed z)⁻¹)) :
      FreeHomotopic ⟨φd,φd.continuous⟩ ⟨fun z : Circle=>z⁻¹,continuous_inv⟩ := by
    have h := haasFrozenCircleReflection% ed.symm ud
    have heq : (⟨fun z : Circle=>ed.symm (ud*(ed z)⁻¹),by fun_prop⟩ : C(Circle,Circle))=
        ⟨φd,φd.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      exact (hclock z).symm
    change FreeHomotopic ⟨fun z : Circle=>ed.symm (ud*(ed z)⁻¹),by fun_prop⟩
      ⟨fun z : Circle=>z⁻¹,continuous_inv⟩ at h
    rwa [heq] at h
  have hReflection {E : Type} [TopologicalSpace E] (d : Curve E)
      (eD : Circle ≃ₜ d.image) (τ : d.image ≃ₜ d.image)
      (J : E → E) (hJ : ∀y : d.image,J y.val=(τ y).val)
      (u : Circle) (hclock : ∀z : Circle,τ (eD z)=eD (u*z⁻¹)) :
      ∃e φ : Circle ≃ₜ Circle,(∀z : Circle,φ z=e.symm (u*(e z)⁻¹)) ∧
        (∀z : Circle,J (d.map z)=d.map (φ z)) := by
    let ec : Circle ≃ₜ d.image := d.embedded.toHomeomorph
    let e : Circle ≃ₜ Circle := ec.trans eD.symm
    let φ : Circle ≃ₜ Circle := e.trans ((Homeomorph.inv Circle).trans ((Homeomorph.mulLeft u).trans e.symm))
    have he (z : Circle) : eD (e z)=ec z := eD.apply_symm_apply (ec z)
    have hes (z : Circle) : ec (e.symm z)=eD z := by
      change ec (ec.symm (eD z))=eD z
      exact ec.apply_symm_apply _
    refine ⟨e,φ,fun _=>rfl,?_⟩
    intro z
    change J (ec z).val=(ec (e.symm (u*(e z)⁻¹))).val
    rw [hJ,hes,←he z,hclock]
  have hFresh {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
      (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
      (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
      (hcdiv : DividingCurve c) (hdnondiv : ¬DividingCurve d) (hcd : Disjoint c.image d.image) :
      ∃p : H2 → E,∃G : Type,∃mG : Group G,letI:=mG
      ∃a : MulAction G H2,letI:=a
      IsQuotientCoveringMap p G ∧
      (∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
        ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z) := by
    letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
    letI : ClosedSurface E := M.genusTwo.2.1.some
    obtain ⟨U,V,hU,hV,hUV,hunion,hfrU,hfrV,heU,heV⟩ :=
      actual_dividing_essential_curve_two_one_holed_tori M c
        (actual_simple_closed_geodesic_essential H c hcgeo) hcdiv
    have houtside : d.image⊆c.imageᶜ := by
      intro x hx hc
      exact disjoint_left.mp hcd hc hx
    have hsubset : d.image⊆U∪V := hunion.symm ▸ houtside
    have hpre : IsPreconnected d.image := (isConnected_range d.embedded.continuous).isPreconnected
    have hu : ∃u : E,u∈(c.image∪d.image)ᶜ := by
      have hpt : (Circle.exp Real.pi, (1 : Circle)) ≠ (1,1) := by
        intro hh
        exact Circle.exp_pi_ne_one (congrArg Prod.fst hh)
      rcases hsubset (show d.map 1∈d.image from ⟨1,rfl⟩) with hdU|hdV
      · have hDU := hpre.subset_left_of_subset_union hU hV hUV hsubset ⟨d.map 1,⟨1,rfl⟩,hdU⟩
        let u : V := heV.some.symm ⟨(Circle.exp Real.pi,1),hpt⟩
        refine ⟨u.val,?_⟩
        have hc : u.val∈c.imageᶜ := hunion ▸ (show u.val∈U∪V from Or.inr u.property)
        exact fun hh=>hh.elim hc (fun hd=>disjoint_left.mp hUV (hDU hd) u.property)
      · have hDV := hpre.subset_right_of_subset_union hU hV hUV hsubset ⟨d.map 1,⟨1,rfl⟩,hdV⟩
        let u : U := heU.some.symm ⟨(Circle.exp Real.pi,1),hpt⟩
        refine ⟨u.val,?_⟩
        have hc : u.val∈c.imageᶜ := hunion ▸ (show u.val∈U∪V from Or.inl u.property)
        exact fun hh=>hh.elim hc (fun hd=>disjoint_left.mp hUV u.property (hDV hd))
    obtain ⟨u,hu⟩ := hu
    have hCut := actual_original_two_geodesic_cut_monodromy_is_ambient_deck_action M H c d hcgeo hdgeo u hu
    dsimp only at hCut
    obtain ⟨p,G,mG,rest⟩ := hCut
    letI:=mG
    obtain ⟨a,rest⟩ := rest
    letI:=a
    obtain ⟨hp,hm,rest⟩ := rest
    exact ⟨p,G,mG,a,hp,hm⟩
  have hGlobalSource {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
      (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
      (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
      (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
      (hcdiv : DividingCurve c) (hdnondiv : ¬DividingCurve d) (hcd : Disjoint c.image d.image)
      (a : MulAction G H2) (p : H2 → E) (hp : letI:=a;IsQuotientCoveringMap p G)
      (hm : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
        ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z) :
      ∃J : E ≃ₜ E,Function.Involutive J ∧
      (∀x : E,∃W : Set E,IsOpen W ∧ x∈W ∧ ∀y∈W,∀z∈W,
        @dist E H.metric.toDist (J y) (J z)=@dist E H.metric.toDist y z) ∧
      J '' c.image=c.image ∧ J '' d.image=d.image ∧
      ∃F : Finset E,F.card=6 ∧ (F:Set E)={x | J x=x} ∧
      ∃φc : Circle ≃ₜ Circle,(∀z : Circle,J (c.map z)=c.map (φc z)) ∧
        FreeHomotopic ⟨φc,φc.continuous⟩ ⟨id,continuous_id⟩ ∧
    ∃ud : Circle,∃ed φd : Circle ≃ₜ Circle,
      (∀z : Circle,φd z=ed.symm (ud*(ed z)⁻¹)) ∧
      (∀z : Circle,J (d.map z)=d.map (φd z)) ∧
      FreeHomotopic ⟨φd,φd.continuous⟩ ⟨fun z : Circle=>z⁻¹,continuous_inv⟩ := by
    have hGiven {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
        (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
        (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
        (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
        (hcdiv : DividingCurve c) (hdnondiv : ¬DividingCurve d) (hcd : Disjoint c.image d.image)
        (a : MulAction G H2) (p : H2 → E) (hp0 : letI:=a;IsQuotientCoveringMap p G)
        (hm0 : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
          ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z) :
        ∃U V : Set E,IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
          U∪V=c.imageᶜ ∧ frontier U=c.image ∧ frontier V=c.image ∧
          Nonempty (U ≃ₜ {z : Circle×Circle // z≠(1,1)}) ∧
          Nonempty (V ≃ₜ {z : Circle×Circle // z≠(1,1)}) ∧ d.image⊆U ∧
        ∃α : ℝ → H2,∃T : ℝ,Isometry α ∧ 0<T ∧ p '' range α=c.image ∧
          (∀s t : ℝ,p (α s)=p (α t) ↔∃n : ℤ,s=t+n*T) ∧
        ∃F : H2 ≃ᵢ H2,∃τ : ↥(U∪c.image) ≃ₜ ↥(U∪c.image),Function.Involutive τ ∧
        ∃τd : d.image ≃ₜ d.image,Function.Involutive τd ∧
        ∃Fd : Finset d.image,Fd.card=2 ∧ (Fd:Set d.image)={y | τd y=y} ∧
          (∀y : d.image,∃hy : y.val∈U∪c.image,(τ ⟨y.val,hy⟩).val=(τd y).val) ∧
        ∃eD : Circle ≃ₜ d.image,∃uD : Circle,(∀z : Circle,τd (eD z)=eD (uD*z⁻¹)) ∧
          (∀t : ℝ,∃W : Set H2,IsOpen W ∧ α t∈W ∧
            ∀w∈W,∀hpw : p w∈U∪c.image,(τ ⟨p w,hpw⟩).val=p (F w)) ∧
          (∀t : ℝ,p (F (α t))=p (α (t+T/2))) ∧
          (∀y : ↥(U∪c.image),∃z : H2,p z=y.val ∧ ∃W : Set H2,∃hW : IsOpen W,
            z∈W ∧ ∀w : H2,∀hw : w∈W,∀hpw : p w∈U∪c.image,(τ ⟨p w,hpw⟩).val=p (F w)) ∧
          (∀y : ↥(U∪c.image),y.val∈c.image →τ y≠y) ∧
        ∃Sfixed : Finset ↥(U∪c.image),Sfixed.card=3 ∧ (Sfixed:Set ↥(U∪c.image))={y | τ y=y} ∧
          (∀t : ℝ,∃ht : p (α t)∈U∪c.image,(τ ⟨p (α t),ht⟩).val=p (α (t+T/2))) ∧
          (∀y : ↥(U∪c.image),∃W : Set ↥(U∪c.image),IsOpen W ∧ y∈W ∧
            ∀u∈W,∀v∈W,@dist E H.metric.toDist (τ u).val (τ v).val=@dist E H.metric.toDist u.val v.val) ∧
        ∃φ : Circle ≃ₜ Circle,
          (∀z : Circle,∃hz : c.map z∈U∪c.image,(τ ⟨c.map z,hz⟩).val=c.map (φ z)) ∧
          FreeHomotopic ⟨φ,φ.continuous⟩ ⟨id,continuous_id⟩ := by
      have embedded_curve_local_sides_within_open
          {E : Type} [TopologicalSpace E]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
          (d : Curve E) (v : E) (hv : v ∈ d.image)
          (O : Set E) (hO : IsOpen O) (hvO : v ∈ O) :
          ∃ C : SurfaceLocalSides O d.image, v ∈ C.nbhd := by
        obtain ⟨U₀, V, hvU, h, hU, hV, hzero, haxis⟩ :=
          CurveComplex.LocalSurgery.embedded_curve_has_local_axis_chart d v hv
        let Q : Set U₀ := {x | x.val ∈ O}
        have hQ : IsOpen Q := hO.preimage continuous_subtype_val
        let A : Set (ℝ × ℝ) := Subtype.val '' (h '' Q)
        have hA : IsOpen A := hV.isOpenMap_subtype_val _ (h.isOpen_image.mpr hQ)
        have h0A : ((0, 0) : ℝ × ℝ) ∈ A := by
          refine ⟨h ⟨v, hvU⟩, ⟨⟨v, hvU⟩, hvO, rfl⟩, ?_⟩
          exact hzero
        obtain ⟨rad, hrad, hradA⟩ := Metric.isOpen_iff.mp hA (0, 0) h0A
        let δ : ℝ := rad / 2
        have hδ : 0 < δ := half_pos hrad
        let J : Set ℝ := Icc (-δ) δ
        have hqA (z : J × J) : ((z.2 : ℝ), (z.1 : ℝ)) ∈ A := by
          apply hradA
          rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
            sub_zero, sub_zero, max_lt_iff]
          have hz0 : |(z.1 : ℝ)| ≤ δ := abs_le.mpr z.1.property
          have hz1 : |(z.2 : ℝ)| ≤ δ := abs_le.mpr z.2.property
          constructor <;> dsimp [δ] at * <;> linarith
        have hqV (z : J × J) : ((z.2 : ℝ), (z.1 : ℝ)) ∈ V := by
          obtain ⟨w, _, hw⟩ := hqA z
          exact hw ▸ w.property
        let q : J × J → V := fun z => ⟨((z.2 : ℝ), (z.1 : ℝ)), hqV z⟩
        have hq : Continuous q := (by fun_prop : Continuous (fun z : J × J =>
          ((z.2 : ℝ), (z.1 : ℝ)))).subtype_mk _
        have hqi : Function.Injective q := by
          intro x y he
          have hh := congrArg Subtype.val he
          exact Prod.ext (Subtype.ext (congrArg Prod.snd hh))
            (Subtype.ext (congrArg Prod.fst hh))
        let B : J × J → E := fun z => (h.symm (q z)).val
        have hB : IsEmbedding B := by
          have hcont : Continuous B := continuous_subtype_val.comp (h.symm.continuous.comp hq)
          have hinj : Function.Injective B :=
            Subtype.val_injective.comp (h.symm.injective.comp hqi)
          exact (hcont.isClosedEmbedding hinj).isEmbedding
        have hBO : range B ⊆ O := by
          rintro _ ⟨z, rfl⟩
          obtain ⟨w, ⟨x, hxQ, hxw⟩, hw⟩ := hqA z
          have hqw : q z = w := Subtype.ext hw.symm
          change (h.symm (q z)).val ∈ O
          rw [hqw, ←hxw, h.symm_apply_apply]
          exact hxQ
        have hBP (z : J × J) : B z ∈ d.image ↔ (z.2 : ℝ) = 0 := by
          have hh := haxis (B z) (h.symm (q z)).property
          have he : h ⟨B z, (h.symm (q z)).property⟩ = q z := h.apply_symm_apply (q z)
          rw [he] at hh
          exact hh
        obtain ⟨C, hCn⟩ := source_embedded_rectangle_local_sides
          (by linarith : -δ < δ) (neg_lt_zero.mpr hδ) hδ B hB O d.image hBO hBP
        refine ⟨C, ?_⟩
        let z : J := ⟨0, ⟨by linarith, by linarith⟩⟩
        have hBv : B (z, z) = v := by
          have he : q (z, z) = h ⟨v, hvU⟩ := by
            apply Subtype.ext
            exact hzero.symm
          dsimp [B]
          rw [he, h.symm_apply_apply]
        exact hBv ▸ hCn z (by dsimp [z]; linarith) (by dsimp [z]; linarith)
      
      have covering_embedded_curve_local_sides
          {X E : Type} [TopologicalSpace X] [TopologicalSpace E]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
          (p : X → E) (hp : IsLocalHomeomorph p) (d : Curve E)
          (U : Set E) (hU : IsOpen U) (z : X)
          (hzU : p z ∈ U) (hzd : p z ∈ d.image) :
          ∃ C : SurfaceLocalSides (p ⁻¹' U) (p ⁻¹' d.image), z ∈ C.nbhd := by
        obtain ⟨e, hze, he⟩ := hp z
        have hpzt : p z ∈ e.target := by
          rw [he]
          exact e.map_source hze
        let O := e.target ∩ U
        have hO : IsOpen O := e.open_target.inter hU
        obtain ⟨C, hzC⟩ := embedded_curve_local_sides_within_open
          d (p z) hzd O hO ⟨hpzt, hzU⟩
        have ht : C.nbhd ⊆ e.target := fun x hx => (C.nbhd_subset hx).1
        let C' : SurfaceLocalSides (p ⁻¹' U) (p ⁻¹' d.image) :=
          C.pullbackChart e ht (by
            rintro _ ⟨y, hy, rfl⟩
            change p (e.symm y) ∈ U
            rw [he, e.right_inv (ht hy)]
            exact (C.nbhd_subset hy).2) (by
            intro y hy
            change p (e.symm y) ∈ d.image ↔ y ∈ d.image
            rw [he, e.right_inv (ht hy)])
        refine ⟨C', ?_⟩
        refine ⟨p z, hzC, ?_⟩
        change e.symm (p z) = z
        rw [he, e.left_inv hze]
      
      have two_distinct_local_side_components_cover
          {X : Type} [TopologicalSpace X]
          (F P : Set X) (C : SurfaceLocalSides F P) (z x₀ x₁ : X)
          (hz : z ∈ C.nbhd ∩ P) (hx₀ : x₀ ∈ F \ P) (hx₁ : x₁ ∈ F \ P)
          (hdistinct : connectedComponentIn (F \ P) x₀ ≠ connectedComponentIn (F \ P) x₁)
          (hz₀ : z ∈ closure (connectedComponentIn (F \ P) x₀))
          (hz₁ : z ∈ closure (connectedComponentIn (F \ P) x₁)) :
          C.nbhd ⊆ closure (connectedComponentIn (F \ P) x₀) ∪
            closure (connectedComponentIn (F \ P) x₁) := by
        let D₀ := connectedComponentIn (F \ P) x₀
        let D₁ := connectedComponentIn (F \ P) x₁
        have hassign (x : X) (hx : x ∈ F \ P) (hcl : z ∈ closure (connectedComponentIn (F \ P) x)) :
            (C.left.Nonempty ∧ C.left ⊆ connectedComponentIn (F \ P) x) ∨
            (C.right.Nonempty ∧ C.right ⊆ connectedComponentIn (F \ P) x) := by
          obtain ⟨w, hwC, hwD⟩ := mem_closure_iff.mp hcl C.nbhd C.isOpen_nbhd hz.1
          have hwDiff : w ∈ C.nbhd \ P :=
            ⟨hwC, (connectedComponentIn_subset (F \ P) x hwD).2⟩
          rw [C.nbhd_diff] at hwDiff
          rcases hwDiff with hwL | hwR
          · left
            refine ⟨⟨w, hwL⟩, ?_⟩
            have heq := connectedComponentIn_eq hwD
            have hsub := C.connected_left.isPreconnected.subset_connectedComponentIn
              hwL C.left_subset_diff
            intro y hy
            rw [heq]
            exact hsub hy
          · right
            refine ⟨⟨w, hwR⟩, ?_⟩
            have heq := connectedComponentIn_eq hwD
            have hsub := C.connected_right.isPreconnected.subset_connectedComponentIn
              hwR C.right_subset_diff
            intro y hy
            rw [heq]
            exact hsub hy
        have h₀ := hassign x₀ hx₀ hz₀
        have h₁ := hassign x₁ hx₁ hz₁
        have hcomponent_disjoint : Disjoint D₀ D₁ := by
          apply Set.disjoint_left.mpr
          intro y hy₀ hy₁
          exact hdistinct ((connectedComponentIn_eq hy₀).trans (connectedComponentIn_eq hy₁).symm)
        have hcoverSides : (C.left ⊆ D₀ ∧ C.right ⊆ D₁) ∨
            (C.left ⊆ D₁ ∧ C.right ⊆ D₀) := by
          rcases h₀ with ⟨hne₀, hsub₀⟩ | ⟨hne₀, hsub₀⟩
          · rcases h₁ with ⟨hne₁, hsub₁⟩ | ⟨hne₁, hsub₁⟩
            · exact False.elim (Set.disjoint_left.mp hcomponent_disjoint (hsub₀ hne₀.some_mem)
                (hsub₁ hne₀.some_mem))
            · exact Or.inl ⟨hsub₀, hsub₁⟩
          · rcases h₁ with ⟨hne₁, hsub₁⟩ | ⟨hne₁, hsub₁⟩
            · exact Or.inr ⟨hsub₁, hsub₀⟩
            · exact False.elim (Set.disjoint_left.mp hcomponent_disjoint (hsub₀ hne₀.some_mem)
                (hsub₁ hne₀.some_mem))
        intro y hyC
        by_cases hyP : y ∈ P
        · rcases hcoverSides with ⟨hL, _⟩ | ⟨_, hR⟩
          · exact Or.inl (closure_mono hL (C.limit_left ⟨hyC, hyP⟩))
          · exact Or.inl (closure_mono hR (C.limit_right ⟨hyC, hyP⟩))
        · have hyDiff : y ∈ C.nbhd \ P := ⟨hyC, hyP⟩
          rw [C.nbhd_diff] at hyDiff
          rcases hcoverSides with ⟨hL, hR⟩ | ⟨hL, hR⟩
          · rcases hyDiff with hyL | hyR
            · exact Or.inl (subset_closure (hL hyL))
            · exact Or.inr (subset_closure (hR hyR))
          · rcases hyDiff with hyL | hyR
            · exact Or.inr (subset_closure (hL hyL))
            · exact Or.inl (subset_closure (hR hyR))
      
      
      have actual_deck_axis_range_of_normalized_seam
          {G : Type} [Group G] (a : MulAction G H2)
          (eN gSeam : H2 ≃ᵢ H2) (γ : G) (α₀ α₁ ψ₀ ψ₁ : ℝ → H2)
          (hg₀ : eN '' range α₀ = range ψ₀)
          (hg₁ : eN '' range α₁ = range ψ₁)
          (hgSeam : ∀ z : H2, gSeam (eN z) =
            eN (@SMul.smul G H2 a.toSMul γ z))
          (hSeamRange : gSeam '' range ψ₀ = range ψ₁) :
          (fun z => @SMul.smul G H2 a.toSMul γ z) '' range α₀ = range α₁ := by
        apply (Set.image_injective.mpr eN.injective)
        rw [Set.image_image]
        have hmap : (eN ∘ fun z => @SMul.smul G H2 a.toSMul γ z) = gSeam ∘ eN := by
          funext z
          exact (hgSeam z).symm
        change (eN ∘ fun z => @SMul.smul G H2 a.toSMul γ z) '' range α₀ =
          eN '' range α₁
        rw [hmap]
        calc
          (gSeam ∘ eN) '' range α₀ = gSeam '' (eN '' range α₀) := by
            ext z
            simp only [Set.mem_image, Function.comp_apply]
            constructor
            · rintro ⟨w, hw, rfl⟩
              exact ⟨eN w, ⟨w, hw, rfl⟩, rfl⟩
            · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
              exact ⟨w, hw, rfl⟩
          _ = eN '' range α₁ := by rw [hg₀, hSeamRange, hg₁]
      
      
      have actual_closed_cut_local_seam_coverage
          {E G : Type} [TopologicalSpace E]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E] [Group G]
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a; IsQuotientCoveringMap p G)
          (U : Set E) (hU : IsOpen U) (d : Curve E) (hdU : d.image ⊆ U)
          (x : H2) (hx : p x ∈ U \ d.image) :
          letI := a
          let D := connectedComponentIn (p ⁻¹' (U \ d.image)) x
          let K := MulAction.stabilizer G D
          ∀ α₀ α₁ : ℝ → H2,
            range α₀ ⊆ frontier D → range α₁ ⊆ frontier D →
            p '' range α₀ = d.image → p '' range α₁ = d.image →
            (∀ k : K, (fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀ ≠ range α₁) →
            ∀ γ : G,
            (fun z => @SMul.smul G H2 a.toSMul γ z) '' range α₀ = range α₁ →
            (∀ z ∈ range α₀, ∃ W : Set H2, IsOpen W ∧ z ∈ W ∧ W ⊆ p ⁻¹' U ∧
              W ⊆ closure D ∪
                (fun y => @SMul.smul G H2 a.toSMul γ⁻¹ y) '' closure D) ∧
            (∀ z ∈ range α₁, ∃ W : Set H2, IsOpen W ∧ z ∈ W ∧ W ⊆ p ⁻¹' U ∧
              W ⊆ closure D ∪
                (fun y => @SMul.smul G H2 a.toSMul γ y) '' closure D) := by
        letI := a
        intro D K α₀ α₁ hfront₀ hfront₁ himage₀ himage₁ hnotK γ hγrange
        letI : ContinuousConstSMul G H2 := hq.toContinuousConstSMul
        let F : H2 ≃ₜ H2 := Homeomorph.smul γ
        let Finv : H2 ≃ₜ H2 := Homeomorph.smul γ⁻¹
        let cut : Set H2 := p ⁻¹' (U \ d.image)
        have hcut (g : G) : (Homeomorph.smul g : H2 ≃ₜ H2) '' cut = cut := by
          ext y
          constructor
          · rintro ⟨w, hw, rfl⟩
            change p (@SMul.smul G H2 a.toSMul g w) ∈ U \ d.image
            have hp : p (@SMul.smul G H2 a.toSMul g w) = p w := hq.map_smul g
            rw [hp]
            exact hw
          · intro hy
            refine ⟨@SMul.smul G H2 a.toSMul g⁻¹ y, ?_, ?_⟩
            · change p (@SMul.smul G H2 a.toSMul g⁻¹ y) ∈ U \ d.image
              have hp : p (@SMul.smul G H2 a.toSMul g⁻¹ y) = p y := hq.map_smul g⁻¹
              rw [hp]
              exact hy
            · exact smul_inv_smul g y
        have hDinv : Finv '' D = connectedComponentIn cut (Finv x) := by
          change Finv '' connectedComponentIn cut x = _
          rw [Finv.image_connectedComponentIn hx, show Finv '' cut = cut from hcut γ⁻¹]
        have hxin : Finv x ∈ cut := by
          rw [←hcut γ⁻¹]
          exact ⟨x, hx, rfl⟩
        have hdistinct : D ≠ Finv '' D := by
          intro he
          have hstabInv : γ⁻¹ ∈ K := MulAction.mem_stabilizer_iff.mpr he.symm
          have hstab : γ ∈ K := by
            have hh := K.inv_mem hstabInv
            simpa using hh
          let k : K := ⟨γ, hstab⟩
          exact hnotK k (by simpa only [k] using hγrange)
        have hfirst : ∀ z ∈ range α₀, ∃ W : Set H2, IsOpen W ∧ z ∈ W ∧
            W ⊆ p ⁻¹' U ∧ W ⊆ closure D ∪ Finv '' closure D := by
          intro z hzα
          have hzd : p z ∈ d.image := by
            rw [←himage₀]
            exact ⟨z, hzα, rfl⟩
          have hzU : p z ∈ U := hdU hzd
          obtain ⟨C, hzC⟩ := covering_embedded_curve_local_sides
            p hq.isLocalHomeomorph d U hU z hzU hzd
          have hzP : z ∈ p ⁻¹' d.image := hzd
          have hzD : z ∈ closure D := frontier_subset_closure (hfront₀ hzα)
          have hzInv : z ∈ closure (Finv '' D) := by
            have hγz : F z ∈ range α₁ := by
              rw [←hγrange]
              exact ⟨z, hzα, rfl⟩
            have hFz : F z ∈ closure D := frontier_subset_closure (hfront₁ hγz)
            rw [←Finv.image_closure]
            exact ⟨F z, hFz, by simp [F, Finv]⟩
          have hcover := two_distinct_local_side_components_cover
            (p ⁻¹' U) (p ⁻¹' d.image) C z x (Finv x)
            ⟨hzC, hzP⟩ hx hxin (by
              change D ≠ connectedComponentIn cut (Finv x)
              rwa [←hDinv]) hzD (by
              change z ∈ closure (connectedComponentIn cut (Finv x))
              rwa [←hDinv])
          refine ⟨C.nbhd, C.isOpen_nbhd, hzC, C.nbhd_subset, ?_⟩
          change C.nbhd ⊆ closure D ∪ closure (connectedComponentIn cut (Finv x)) at hcover
          rwa [←hDinv, ←Finv.image_closure] at hcover
        constructor
        · intro z hz
          obtain ⟨W, hWo, hzW, hWU, hWcover⟩ := hfirst z hz
          exact ⟨W, hWo, hzW, hWU, hWcover⟩
        · intro z hz
          obtain ⟨w, hw, hwz⟩ : z ∈ F '' range α₀ := hγrange ▸ hz
          obtain ⟨W, hWo, hwW, hWU, hWcover⟩ := hfirst w hw
          refine ⟨F '' W, F.isOpen_image.mpr hWo, ⟨w, hwW, hwz⟩, ?_, ?_⟩
          · rintro y ⟨v, hvW, rfl⟩
            change p (F v) ∈ U
            have hp : p (F v) = p v := hq.map_smul γ
            rw [hp]
            exact hWU hvW
          · rintro y ⟨v, hvW, rfl⟩
            rcases hWcover hvW with hvD | hvInv
            · right
              exact ⟨v, hvD, rfl⟩
            · left
              obtain ⟨u, huD, huv⟩ := hvInv
              have heq : F (Finv u) = u := by simp [F, Finv]
              rw [←huv, heq]
              exact huD
      
      have hContinuousWindows {X E : Type} [TopologicalSpace X] [TopologicalSpace E]
          (p : X → E) (hp : IsCoveringMap p) (U : Set E) (τ : U → U)
          (F : X → X) (hF : Continuous F)
          (hWindow : ∀y : U,∃z : X,p z=y.val ∧ ∃W : Set X,∃hW : IsOpen W,
            z∈W ∧ ∃hWU : W⊆p ⁻¹' U,∀w : X,∀hw : w∈W,(τ ⟨p w,hWU hw⟩).val=p (F w)) :
          Continuous τ := by
        have hcovU : IsCoveringMap (U.restrictPreimage p) :=
          (show IsCoveringMapOn p U from fun y _=>hp y).isCoveringMap_restrictPreimage
        apply IsInducing.subtypeVal.continuous_iff.mpr
        apply continuous_iff_continuousAt.mpr
        intro y
        obtain ⟨z,hzy,W,hW,hzW,hWU,hLift⟩ := hWindow y
        let x : p ⁻¹' U := ⟨z,hWU hzW⟩
        have hxy : U.restrictPreimage p x=y := Subtype.ext hzy
        rw [←hxy]
        let Ws : Set ↥(p ⁻¹' U) := {u | u.val∈W}
        have hWs : IsOpen Ws := hW.preimage continuous_subtype_val
        have hxWs : x∈Ws := hzW
        have hf : Continuous (fun u : p ⁻¹' U=>p (F u.val)) :=
          hp.continuous.comp (hF.comp continuous_subtype_val)
        have hcomp : ContinuousAt ((fun y : U=>(τ y).val) ∘ U.restrictPreimage p) x :=
          hf.continuousAt.congr (Filter.eventually_of_mem (hWs.mem_nhds hxWs)
            (fun u hu=>(hLift u.val hu).symm))
        exact (Filter.tendsto_map'_iff.mpr hcomp).mono_left (hcovU.isOpenMap.nhds_le x)
      have hLocalMetricWindows {X E : Type} [MetricSpace X] [MetricSpace E]
          (p : X → E) (hp : IsCoveringMap p) (U : Set E) (τ : U → U)
          (F : X ≃ᵢ X)
          (hmetric : ∀z : X,∃W : Set X,IsOpen W ∧ z∈W ∧ ∀u∈W,∀v∈W,dist (p u) (p v)=dist u v)
          (hWindow : ∀y : U,∃z : X,p z=y.val ∧ ∃W : Set X,∃hW : IsOpen W,
            z∈W ∧ ∃hWU : W⊆p ⁻¹' U,∀w : X,∀hw : w∈W,(τ ⟨p w,hWU hw⟩).val=p (F w)) :
          ∀y : U,∃V : Set U,IsOpen V ∧ y∈V ∧ ∀u∈V,∀v∈V,dist (τ u).val (τ v).val=dist u.val v.val := by
        have hcovU : IsCoveringMap (U.restrictPreimage p) :=
          (show IsCoveringMapOn p U from fun y _=>hp y).isCoveringMap_restrictPreimage
        intro y
        obtain ⟨z,hzy,W,hW,hzW,hWU,hLift⟩ := hWindow y
        obtain ⟨Wz,hWz,hzWz,hMz⟩ := hmetric z
        obtain ⟨WF,hWF,hFz,hMF⟩ := hmetric (F z)
        let W2 : Set X := W∩Wz∩F ⁻¹' WF
        have hW2 : IsOpen W2 := (hW.inter hWz).inter (hWF.preimage F.continuous)
        let Ws : Set ↥(p ⁻¹' U) := {x | x.val∈W2}
        have hWs : IsOpen Ws := hW2.preimage continuous_subtype_val
        let q := U.restrictPreimage p
        refine ⟨q '' Ws,hcovU.isOpenMap _ hWs,?_,?_⟩
        · exact ⟨⟨z,hWU hzW⟩,⟨⟨hzW,hzWz⟩,hFz⟩,Subtype.ext hzy⟩
        · rintro u ⟨uz,huz,rfl⟩ v ⟨vz,hvz,rfl⟩
          have hLu : (τ (q uz)).val=p (F uz.val) := hLift uz.val huz.1.1
          have hLv : (τ (q vz)).val=p (F vz.val) := hLift vz.val hvz.1.1
          rw [hLu,hLv,hMF _ huz.2 _ hvz.2,F.dist_eq]
          exact (hMz _ huz.1.2 _ hvz.1.2).symm
      have hConjClock {G P : Type} [Group G] (a : MulAction G P) (α β : ℝ → P)
          (g δ W : G) (T : ℝ) (n : ℤ) (hn : n=1 ∨ n=-1)
          (hgen : g*δ*g⁻¹=W^(-n))
          (hβ : ∀t : ℝ,β t=@SMul.smul G P a.toSMul g (α t))
          (hshift : (∀t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) ∨
            (∀t : ℝ,@SMul.smul G P a.toSMul δ⁻¹ (α t)=α (t+T))) :
          (∀t : ℝ,@SMul.smul G P a.toSMul W (β t)=β (t+T)) ∨
            (∀t : ℝ,@SMul.smul G P a.toSMul W⁻¹ (β t)=β (t+T)) := by
        letI := a
        have hfwd (δ : G) (hs : ∀t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
            ∀t : ℝ,@SMul.smul G P a.toSMul (g*δ*g⁻¹) (β t)=β (t+T) := by
          intro t
          rw [hβ]
          calc
            @SMul.smul G P a.toSMul (g*δ*g⁻¹) (@SMul.smul G P a.toSMul g (α t)) =
                @SMul.smul G P a.toSMul ((g*δ*g⁻¹)*g) (α t) := (@mul_smul G P _ a.toSemigroupAction _ _ _).symm
            _ = @SMul.smul G P a.toSMul (g*δ) (α t) := by congr 1;group
            _ = @SMul.smul G P a.toSMul g (@SMul.smul G P a.toSMul δ (α t)) :=
              @mul_smul G P _ a.toSemigroupAction _ _ _
            _ = β (t+T) := (congrArg (fun z=>@SMul.smul G P a.toSMul g z) (hs t)).trans (hβ (t+T)).symm
        have hinv : g*δ⁻¹*g⁻¹=(g*δ*g⁻¹)⁻¹ := by group
        rcases hn with rfl|rfl <;> rcases hshift with hs|hs
        · right
          have hh := hfwd δ hs
          simpa only [hgen,neg_neg,zpow_neg_one] using hh
        · left
          have hh := hfwd δ⁻¹ hs
          simpa only [hinv,hgen,zpow_neg_one,inv_inv] using hh
        · left
          have hh := hfwd δ hs
          simpa only [hgen,neg_neg,zpow_one] using hh
        · right
          have hh := hfwd δ⁻¹ hs
          simpa only [hinv,hgen,neg_neg,zpow_one] using hh
      have hPrimitiveAxisKernel {G P E : Type} [Group G] [MulAction G P]
          (p : P → E) (F : P → P) (α : ℝ → P) (T : ℝ) (δ : G)
          (hshift : ∀t : ℝ,δ • α t=α (t+T))
          (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
          (hF : ∀g : G,∀z : P,p (F (g • z))=p (F z)) :
          ∀z∈range α,∀w∈range α,p z=p w →p (F z)=p (F w) := by
        have hClock {G P : Type} [Group G] [MulAction G P] (δ : G) (α : ℝ → P) (T : ℝ)
            (hs : ∀t : ℝ,δ • α t=α (t+T)) :
            ∀n : ℤ,∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
          have hNat (δ : G) (T : ℝ) (hs : ∀t : ℝ,δ • α t=α (t+T)) :
              ∀n : ℕ,∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
            intro n
            induction n with
            | zero => intro t;simp
            | succ n ih =>
                intro t
                rw [pow_succ,mul_smul,hs,ih]
                congr 1
                push_cast
                ring
          have hinv (t : ℝ) : δ⁻¹ • α t=α (t+(-T)) := by
            have hh := congrArg (fun z : P => δ⁻¹ • z) (hs (t-T))
            have hh' : δ⁻¹ • α t=α (t-T) := by simpa only [sub_add_cancel,inv_smul_smul] using hh.symm
            simpa only [sub_eq_add_neg] using hh'
          intro n t
          cases n with
          | ofNat n =>
              change δ^(n:ℤ) • α t=α (t+(n:ℝ)*T)
              simpa only [zpow_natCast] using hNat δ T hs n t
          | negSucc n =>
              have hh := hNat δ⁻¹ (-T) hinv (n+1) t
              simpa only [zpow_negSucc,inv_pow,Int.cast_negSucc,Nat.cast_add,Nat.cast_one,
                mul_neg,neg_mul] using hh
        rintro z ⟨s,rfl⟩ w ⟨t,rfl⟩ hh
        obtain ⟨n,rfl⟩ := (hfibre s t).mp hh
        rw [←hClock δ α T hshift n t,hF]
      have hPrimitiveAxisFibreOrbit {G P E : Type} [Group G] [MulAction G P]
          (p : P → E) (α : ℝ → P) (T : ℝ) (δ : G)
          (hshift : ∀t : ℝ,δ • α t=α (t+T))
          (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
          (hp : ∀g : G,∀z : P,p (g • z)=p z) :
          ∀z∈⋃g : G,(fun x : P=>g • x) '' range α,
            ∀w∈⋃g : G,(fun x : P=>g • x) '' range α,p z=p w →∃k : G,k • w=z := by
        have hClock {G P : Type} [Group G] [MulAction G P] (δ : G) (α : ℝ → P) (T : ℝ)
            (hs : ∀t : ℝ,δ • α t=α (t+T)) :
            ∀n : ℤ,∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
          have hNat (δ : G) (T : ℝ) (hs : ∀t : ℝ,δ • α t=α (t+T)) :
              ∀n : ℕ,∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
            intro n
            induction n with
            | zero => intro t;simp
            | succ n ih =>
                intro t
                rw [pow_succ,mul_smul,hs,ih]
                congr 1
                push_cast
                ring
          have hinv (t : ℝ) : δ⁻¹ • α t=α (t+(-T)) := by
            have hh := congrArg (fun z : P => δ⁻¹ • z) (hs (t-T))
            have hh' : δ⁻¹ • α t=α (t-T) := by simpa only [sub_add_cancel,inv_smul_smul] using hh.symm
            simpa only [sub_eq_add_neg] using hh'
          intro n t
          cases n with
          | ofNat n =>
              change δ^(n:ℤ) • α t=α (t+(n:ℝ)*T)
              simpa only [zpow_natCast] using hNat δ T hs n t
          | negSucc n =>
              have hh := hNat δ⁻¹ (-T) hinv (n+1) t
              simpa only [zpow_negSucc,inv_pow,Int.cast_negSucc,Nat.cast_add,Nat.cast_one,
                mul_neg,neg_mul] using hh
        intro z hz w hw hzw
        obtain ⟨g,_,⟨s,rfl⟩,rfl⟩ := Set.mem_iUnion.mp hz
        obtain ⟨h,_,⟨t,rfl⟩,rfl⟩ := Set.mem_iUnion.mp hw
        rw [hp,hp] at hzw
        obtain ⟨n,rfl⟩ := (hfibre s t).mp hzw
        refine ⟨g*δ^n*h⁻¹,?_⟩
        rw [mul_smul,mul_smul,inv_smul_smul,hClock δ α T hshift]
      have hMeetLines {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
          (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
          (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
          (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
          (himage : p '' range β⊆p '' range α)
          (hmeet : (range α∩range β).Nonempty) : range β=range α := by
        have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
            (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
            (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
            (himage : p '' range β⊆p '' range α)
            (hmeet : (range α∩range β).Nonempty) : range β=range α := by
          have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
              (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
            have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                ∃f : C(Circle,E),IsEmbedding f ∧
                  (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                  range f=p '' range α := by
              classical
              let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
              have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
              let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
              have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                apply (hfibre _ _).mpr
                refine ⟨k,?_⟩
                rw [hk]
                field_simp
              have hψ : Continuous ψ := by
                apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                rw [heq]
                fun_prop
              let f : C(Circle,E) := ⟨ψ,hψ⟩
              have hfinj : Function.Injective f := by
                intro z w hzw
                obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                  have hπ : (2*Real.pi)≠0 := by positivity
                  have hT' : T≠0 := hT.ne'
                  field_simp at hk
                  nlinarith
                rw [←hθ z,←hθ w]
                exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
              have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                change _=ψ _
                rw [hfac]
                congr 2
                field_simp
              refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
              apply Subset.antisymm
              · rintro y ⟨z,rfl⟩
                exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
              · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
            obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
            change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
            let e : Circle ≃ₜ range f := hf.toHomeomorph
            let g : C(ℝ,Circle) :=
              ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
            let θ₀ := 2*Real.pi*s₀/T
            have hbase : Circle.exp θ₀=g t₀ := by
              apply e.injective
              apply Subtype.ext
              change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
              rw [e.apply_symm_apply]
              change f (Circle.exp θ₀)=p (β t₀)
              rw [←hparam,hmeet]
            obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
            have hL0 : L t₀=θ₀ := hL.1
            have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
            let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
            have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
              intro t
              change p (α (T*L t/(2*Real.pi)))=_
              rw [hparam]
              have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
              rw [harg,hLe]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
            have hℓbase : ℓ t₀=β t₀ := by
              change α (T*L t₀/(2*Real.pi))=β t₀
              rw [hL0]
              have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
              rw [harg,hmeet]
            have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
              (funext hℓproj) t₀ hℓbase
            rintro y ⟨t,rfl⟩
            exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
          have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
              range β=range α := by
            let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
            let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
            have hfac (t : ℝ) : α (f t)=β t :=
              congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
            have hf : Isometry f := by
              apply isometry_iff_dist_eq.mpr
              intro s t
              rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
            let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
            have hLin : Function.Injective A.toAffineMap.linear :=
              A.toAffineMap.linear_injective_iff.mpr hf.injective
            have hSur : Function.Surjective A.toAffineMap.linear :=
              LinearMap.surjective_of_injective hLin
            have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
            apply Subset.antisymm hsub
            rintro y ⟨t,rfl⟩
            obtain ⟨s,hs⟩ := hfsur t
            exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
          obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
          have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
            s t (hs.trans ht.symm)
          exact hLine α β hα hβ hsub
        exact hMeet p hp α β hα hβ T hT hfibre himage hmeet
      have hSignedPhase {P : Type} [MetricSpace P] (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
          (g : P ≃ᵢ P) (hr : g '' range α=range β) :
          ∃phase : ℝ,(∀t : ℝ,g (α t)=β (t+phase)) ∨ (∀t : ℝ,g (α t)=β (phase-t)) := by
        have hReal (f : ℝ → ℝ) (hf : Isometry f) :
            (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
          let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
          let k : ℝ := A.toAffineMap.linear 1
          have hfac (t : ℝ) : f t=t*k+f 0 := by
            have h := A.toAffineMap.map_vadd 0 t
            have hlin : A.toAffineMap.linear t=t*k := by
              have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
              simpa [k,smul_eq_mul] using hh
            change f (t+0)=A.toAffineMap.linear t+f 0 at h
            simpa only [add_zero,hlin] using h
          have hk : |k|=1 := by
            have h := hf.dist_eq 1 0
            rw [hfac 1,hfac 0] at h
            simpa [Real.dist_eq] using h
          rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
          · left;intro t;rw [hfac,he];ring
          · right;intro t;rw [hfac,he];ring
        have hExists (t : ℝ) : ∃s : ℝ,β s=g (α t) := by
          have hh : g (α t)∈g '' range α := ⟨α t,mem_range_self t,rfl⟩
          have hm : g (α t)∈range β := (Set.ext_iff.mp hr (g (α t))).mp hh
          obtain ⟨s,hs⟩ := hm
          exact ⟨s,hs⟩
        let f : ℝ → ℝ := fun t => Classical.choose (hExists t)
        have hf (t : ℝ) : β (f t)=g (α t) := Classical.choose_spec (hExists t)
        have hfi : Isometry f := by
          apply Isometry.of_dist_eq
          intro s t
          rw [←hβ.dist_eq,hf,hf,g.dist_eq,hα.dist_eq]
        rcases hReal f hfi with hp|hm
        · refine ⟨f 0,Or.inl ?_⟩
          intro t
          rw [←hf,hp]
          congr 1
          ring
        · refine ⟨f 0,Or.inr ?_⟩
          intro t
          rw [←hf,hm]
      have hHalfPeriod {E : Type} (p : ℝ → E) (τ : E → E) (T phase : ℝ)
          (hfibre : ∀s t : ℝ,p s=p t ↔ ∃n : ℤ,s=t+n*T)
          (hclock : ∀t : ℝ,τ (p t)=p (t+phase))
          (hτ : Function.Involutive τ) (hno : ∀t : ℝ,τ (p t)≠p t) :
          ∀t : ℝ,τ (p t)=p (t+T/2) := by
        have hphase0 : τ (p 0)=p phase := by simpa only [zero_add] using hclock 0
        have hh : p (2*phase)=p 0 := by
          calc
            p (2*phase)=p (phase+phase) := by congr 1;ring
            _ = τ (p phase) := (hclock phase).symm
            _ = τ (τ (p 0)) := congrArg τ hphase0.symm
            _ = p 0 := hτ (p 0)
        obtain ⟨n,hn⟩ := (hfibre (2*phase) 0).mp hh
        let m : ℤ := n/2
        have hrem : n%2=1 := by
          have hlo := Int.emod_nonneg n (by norm_num : (2:ℤ)≠0)
          have hhi := Int.emod_lt_of_pos n (by norm_num : (0:ℤ)<2)
          by_contra hne
          have hzero : n%2=0 := by omega
          have hnm : n=2*m := by dsimp [m];omega
          have hreal : (n:ℝ)=2*(m:ℝ) := by exact_mod_cast hnm
          have heq : phase=(m:ℝ)*T := by rw [hreal] at hn;nlinarith [hn]
          have hp0 : p phase=p 0 := (hfibre _ _).mpr ⟨m,by rw [heq];ring⟩
          exact hno 0 (hphase0.trans hp0)
        have hnm : n=2*m+1 := by dsimp [m];omega
        have hreal : (n:ℝ)=2*(m:ℝ)+1 := by exact_mod_cast hnm
        have heq : phase=T/2+(m:ℝ)*T := by rw [hreal] at hn;nlinarith [hn]
        intro t
        rw [hclock]
        exact (hfibre _ _).mpr ⟨m,by rw [heq];ring⟩
      have actual_c_relative_closure_window
          {E G : Type} [TopologicalSpace E]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E] [Group G]
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a; IsQuotientCoveringMap p G)
          (c d : Curve E) (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
          (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
          (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image)
          (hdU : d.image ⊆ U) (hcd : Disjoint c.image d.image)
          (x : H2) (hx : p x ∈ U \ d.image) :
          let D := connectedComponentIn (p ⁻¹' (U \ d.image)) x
          ∀ z ∈ frontier D, p z ∈ c.image →
            ∃ W : Set H2, IsOpen W ∧ z ∈ W ∧ W ⊆ p ⁻¹' d.imageᶜ ∧
              ∀ w ∈ W, p w ∈ closure U → w ∈ closure D := by
        intro D z hzfront hzc
        let O : Set E := d.imageᶜ
        have hdclosed : IsClosed d.image := (isCompact_range d.embedded.continuous).isClosed
        have hO : IsOpen O := hdclosed.isOpen_compl
        have hzO : p z ∈ O := (Set.disjoint_left.mp hcd hzc)
        obtain ⟨C, hzC⟩ := covering_embedded_curve_local_sides
          p hq.isLocalHomeomorph c O hO z hzO hzc
        let A : Set H2 := p ⁻¹' U
        let B : Set H2 := p ⁻¹' V
        let P : Set H2 := p ⁻¹' c.image
        let Q : Set H2 := p ⁻¹' (U \ d.image)
        have hA : IsOpen A := hU.preimage hq.continuous
        have hB : IsOpen B := hV.preimage hq.continuous
        have hAB : Disjoint A B := hUV.preimage p
        have hP : z ∈ P := hzc
        have hzD : z ∈ closure D := frontier_subset_closure hzfront
        have hzB : z ∈ closure B := by
          have hh : p z ∈ closure V := by
            exact frontier_subset_closure (hfrontV.symm ▸ hzc)
          rw [←hq.isLocalHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage hq.continuous]
          exact hh
        have hsidepart : C.nbhd \ P ⊆ A ∪ B := by
          intro w hw
          have hwc : p w ∈ c.imageᶜ := hw.2
          change p w ∈ U ∪ V
          rw [hcover]
          exact hwc
        have hleftpart := C.connected_left.isPreconnected.subset_or_subset
          hA hB hAB (by
            intro w hw
            exact hsidepart (by rw [C.nbhd_diff]; exact Or.inl hw))
        have hrightpart := C.connected_right.isPreconnected.subset_or_subset
          hA hB hAB (by
            intro w hw
            exact hsidepart (by rw [C.nbhd_diff]; exact Or.inr hw))
        obtain ⟨wD, hwCn, hwD⟩ := mem_closure_iff.mp hzD C.nbhd C.isOpen_nbhd hzC
        have hwDQ : wD ∈ Q := connectedComponentIn_subset Q x hwD
        have hwDP : wD ∉ P := by
          intro hwp
          have hnotc : p wD ∉ c.image := by
            have hh : p wD ∈ U ∪ V := Or.inl hwDQ.1
            rw [hcover] at hh
            exact hh
          exact hnotc hwp
        have hwDsides : wD ∈ C.left ∪ C.right := by
          rw [←C.nbhd_diff]
          exact ⟨hwCn, hwDP⟩
        obtain ⟨wB, hwBCn, hwB⟩ := mem_closure_iff.mp hzB C.nbhd C.isOpen_nbhd hzC
        have hwBP : wB ∉ P := by
          intro hw
          have hwc : p wB ∈ c.image := hw
          have hnotc : p wB ∉ c.image := by
            have hh : p wB ∈ U ∪ V := Or.inr hwB
            rw [hcover] at hh
            exact hh
          exact hnotc hwc
        have hwBsides : wB ∈ C.left ∪ C.right := by
          rw [←C.nbhd_diff]
          exact ⟨hwBCn, hwBP⟩
        have hDside (S : Set H2) (hconn : IsConnected S) (hsub : S ⊆ p ⁻¹' O \ P)
            (hSA : S ⊆ A) (hw : wD ∈ S) : S ⊆ D := by
          have hSQ : S ⊆ Q := by
            intro t ht
            exact ⟨hSA ht, (hsub ht).1⟩
          have heq := connectedComponentIn_eq hwD
          have hcomp := hconn.isPreconnected.subset_connectedComponentIn hw hSQ
          intro t ht
          change t ∈ connectedComponentIn Q x
          rw [heq]
          exact hcomp ht
        have hleft : C.left ⊆ p ⁻¹' O \ P := C.left_subset_diff
        have hright : C.right ⊆ p ⁻¹' O \ P := C.right_subset_diff
        have hassign : (C.left ⊆ D ∧ C.right ⊆ B) ∨
            (C.right ⊆ D ∧ C.left ⊆ B) := by
          rcases hwDsides with hwDL | hwDR
          · have hLA : C.left ⊆ A := hleftpart.resolve_right (by
              intro hLB
              exact (Set.disjoint_left.mp hAB (hwDQ.1) (hLB hwDL)))
            have hLD := hDside C.left C.connected_left hleft hLA hwDL
            have hRB : C.right ⊆ B := hrightpart.resolve_left (by
              intro hRA
              rcases hwBsides with hwBL | hwBR
              · exact (Set.disjoint_left.mp hAB (hLA hwBL) hwB)
              · exact (Set.disjoint_left.mp hAB (hRA hwBR) hwB))
            exact Or.inl ⟨hLD, hRB⟩
          · have hRA : C.right ⊆ A := hrightpart.resolve_right (by
              intro hRB
              exact (Set.disjoint_left.mp hAB hwDQ.1 (hRB hwDR)))
            have hRD := hDside C.right C.connected_right hright hRA hwDR
            have hLB : C.left ⊆ B := hleftpart.resolve_left (by
              intro hLA
              rcases hwBsides with hwBL | hwBR
              · exact (Set.disjoint_left.mp hAB (hLA hwBL) hwB)
              · exact (Set.disjoint_left.mp hAB (hRA hwBR) hwB))
            exact Or.inr ⟨hRD, hLB⟩
        refine ⟨C.nbhd, C.isOpen_nbhd, hzC, C.nbhd_subset, ?_⟩
        intro w hwW hwClU
        have hwUorC : p w ∈ U ∪ c.image := by
          rw [closure_eq_self_union_frontier, hfrontU] at hwClU
          exact hwClU
        rcases hwUorC with hwU | hwC
        · have hwSide : w ∈ C.left ∪ C.right := by
            rw [←C.nbhd_diff]
            refine ⟨hwW, ?_⟩
            intro hwp
            have hNo : p w ∉ c.image := by
              have hh : p w ∈ U ∪ V := Or.inl hwU
              rw [hcover] at hh
              exact hh
            exact hNo hwp
          rcases hassign with ⟨hLD, hRB⟩ | ⟨hRD, hLB⟩
          · rcases hwSide with hwL | hwR
            · exact subset_closure (hLD hwL)
            · exact False.elim (Set.disjoint_left.mp hAB hwU (hRB hwR))
          · rcases hwSide with hwL | hwR
            · exact False.elim (Set.disjoint_left.mp hAB hwU (hLB hwL))
            · exact subset_closure (hRD hwR)
        · have hwP : w ∈ P := hwC
          rcases hassign with ⟨hLD, _⟩ | ⟨hRD, _⟩
          · exact closure_mono hLD (C.limit_left ⟨hwW, hwP⟩)
          · exact closure_mono hRD (C.limit_right ⟨hwW, hwP⟩)
      
      have hContinuousRelativeWindows {X E : Type} [TopologicalSpace X] [TopologicalSpace E]
          (p : X → E) (hp : IsCoveringMap p) (U : Set E) (τ : U → U)
          (F : X → X) (hF : Continuous F)
          (hWindow : ∀y : U,∃z : X,p z=y.val ∧ ∃W : Set X,∃hW : IsOpen W,
            z∈W ∧ ∀w : X,∀hw : w∈W,∀hpw : p w∈U,(τ ⟨p w,hpw⟩).val=p (F w)) :
          Continuous τ := by
        have hcovU : IsCoveringMap (U.restrictPreimage p) :=
          (show IsCoveringMapOn p U from fun y _=>hp y).isCoveringMap_restrictPreimage
        apply IsInducing.subtypeVal.continuous_iff.mpr
        apply continuous_iff_continuousAt.mpr
        intro y
        obtain ⟨z,hzy,W,hW,hzW,hLift⟩ := hWindow y
        let x : p ⁻¹' U := ⟨z,by change p z∈U;rw [hzy];exact y.property⟩
        have hxy : U.restrictPreimage p x=y := Subtype.ext hzy
        rw [←hxy]
        let Ws : Set ↥(p ⁻¹' U) := {u | u.val∈W}
        have hWs : IsOpen Ws := hW.preimage continuous_subtype_val
        have hxWs : x∈Ws := hzW
        have hf : Continuous (fun u : p ⁻¹' U=>p (F u.val)) :=
          hp.continuous.comp (hF.comp continuous_subtype_val)
        have hcomp : ContinuousAt ((fun y : U=>(τ y).val) ∘ U.restrictPreimage p) x :=
          hf.continuousAt.congr (Filter.eventually_of_mem (hWs.mem_nhds hxWs)
            (fun u hu=>(hLift u.val hu u.property).symm))
        exact (Filter.tendsto_map'_iff.mpr hcomp).mono_left (hcovU.isOpenMap.nhds_le x)
      have hMetricRelativeWindows {X E : Type} [MetricSpace X] [MetricSpace E]
          (p : X → E) (hp : IsCoveringMap p) (U : Set E) (τ : U → U)
          (F : X ≃ᵢ X)
          (hmetric : ∀z : X,∃W : Set X,IsOpen W ∧ z∈W ∧ ∀u∈W,∀v∈W,dist (p u) (p v)=dist u v)
          (hWindow : ∀y : U,∃z : X,p z=y.val ∧ ∃W : Set X,∃hW : IsOpen W,
            z∈W ∧ ∀w : X,∀hw : w∈W,∀hpw : p w∈U,(τ ⟨p w,hpw⟩).val=p (F w)) :
          ∀y : U,∃V : Set U,IsOpen V ∧ y∈V ∧ ∀u∈V,∀v∈V,dist (τ u).val (τ v).val=dist u.val v.val := by
        have hcovU : IsCoveringMap (U.restrictPreimage p) :=
          (show IsCoveringMapOn p U from fun y _=>hp y).isCoveringMap_restrictPreimage
        intro y
        obtain ⟨z,hzy,W,hW,hzW,hLift⟩ := hWindow y
        obtain ⟨Wz,hWz,hzWz,hMz⟩ := hmetric z
        obtain ⟨WF,hWF,hFz,hMF⟩ := hmetric (F z)
        let W2 : Set X := W∩Wz∩F ⁻¹' WF
        have hW2 : IsOpen W2 := (hW.inter hWz).inter (hWF.preimage F.continuous)
        let Ws : Set ↥(p ⁻¹' U) := {x | x.val∈W2}
        have hWs : IsOpen Ws := hW2.preimage continuous_subtype_val
        let q := U.restrictPreimage p
        refine ⟨q '' Ws,hcovU.isOpenMap _ hWs,?_,?_⟩
        · exact ⟨⟨z,by change p z∈U;rw [hzy];exact y.property⟩,⟨⟨hzW,hzWz⟩,hFz⟩,Subtype.ext hzy⟩
        · rintro u ⟨uz,huz,rfl⟩ v ⟨vz,hvz,rfl⟩
          have hLu : (τ (q uz)).val=p (F uz.val) := hLift uz.val huz.1.1 uz.property
          have hLv : (τ (q vz)).val=p (F vz.val) := hLift vz.val hvz.1.1 vz.property
          rw [hLu,hLv,hMF _ huz.2 _ hvz.2,F.dist_eq]
          exact (hMz _ huz.1.2 _ hvz.1.2).symm
      have hSuppliedCut {E G : Type} [MetricSpace E] [LocallyPathConnectedSpace E] [Group G]
          (c d : Curve E) (hcgeo : IsClosedGeodesic c.image) (hdgeo : IsClosedGeodesic d.image)
          (a : MulAction G H2) (p : H2 → E) (hp : letI:=a;IsQuotientCoveringMap p G)
          (hm : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧ ∀y∈W,∀z∈W,dist (p y) (p z)=dist y z)
          (x : H2) (hx : p x∈(c.image∪d.image)ᶜ) :
          letI := a
          let U := connectedComponentIn (c.image∪d.image)ᶜ (p x)
          let D := connectedComponentIn (p ⁻¹' U) x
          let K := MulAction.stabilizer G D
          ∃b : MulAction K D,letI:=b
            ∃q : D → U,IsQuotientCoveringMap q K ∧
              (∀z,(q z).val=p z.val) ∧
              (∀k : K,∀z : D,(@SMul.smul K D b.toSMul k z).val=@SMul.smul G H2 a.toSMul k.val z.val) ∧
              (∀z : D,∃W : Set D,IsOpen W ∧ z∈W ∧ ∀y∈W,∀z∈W,dist (q y).val (q z).val=dist y z) ∧
              ContractibleSpace D ∧ SimplyConnectedSpace D ∧ IsOpen D ∧ interior (closure D)=D ∧
              (∀y∈D,∀z∈D,∀w : H2,dist y w+dist w z=dist y z →w∈D) := by
        have hRegular {E : Type} [MetricSpace E] [LocallyConnectedSpace E] (c d : Curve E)
            (hcgeo : IsClosedGeodesic c.image) (hdgeo : IsClosedGeodesic d.image)
            (p : H2 → E) (hp : IsCoveringMap p)
            (hmetric : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
              ∀y∈W,∀z∈W,dist (p y) (p z)=dist y z)
            (x : H2) (hx : p x∈(c.image∪d.image)ᶜ) :
            let U := connectedComponentIn (c.image∪d.image)ᶜ (p x)
            let C := connectedComponentIn (p ⁻¹' U) x
            IsOpen C ∧ interior (closure C)=C ∧
              (∀y∈C,∀z∈C,∀w : H2,dist y w+dist w z=dist y z → w∈C) := by
          have hregular {ι : Type} (a : ι → ℝ → H2) (ha : ∀ i,Isometry (a i))
              (x : H2) (hx : x∈(⋃ i,range (a i))ᶜ)
              (hF : IsOpen (⋃ i,range (a i))ᶜ) :
              let C := connectedComponentIn (⋃ i,range (a i))ᶜ x
              interior (closure C)=C := by
            let F := (⋃ i,range (a i))ᶜ
            let C := connectedComponentIn F x
            have hnormalize (a : ℝ → H2) (ha : Isometry a) :
                ∃ e : H2 ≃ᵢ H2,∀ t,a t=e (verticalPath t) := by
              obtain ⟨e,he0,he1⟩ := exists_ordered_pair_isometry (a 0) (a 1) (by
                rw [ha.dist_eq];norm_num [Real.dist_eq])
              have h0 : e (verticalPath 0)=a 0 := by
                have hv : verticalPath 0=UpperHalfPlane.I := by
                  apply UpperHalfPlane.ext
                  apply Complex.ext <;> simp [verticalPath,UpperHalfPlane.I]
                rw [hv];exact he0
              have hf : Isometry (fun t : ℝ => e.symm (a t)) := e.symm.isometry.comp ha
              have hf0 : e.symm (a 0)=verticalPath 0 := by rw [←h0,e.symm_apply_apply]
              have hf1 : e.symm (a 1)=verticalPath 1 := by rw [←he1,e.symm_apply_apply]
              refine ⟨e,?_⟩
              intro t
              simpa only [e.apply_symm_apply] using congrArg e
                (isometry_eq_vertical_of_values _ hf hf0 hf1 t)
            have hopen : IsOpen C := hF.connectedComponentIn
            have hsub : interior (closure C)⊆F := by
              intro y hy hline
              obtain ⟨i,⟨t,ht⟩⟩ := mem_iUnion.mp hline
              obtain ⟨e,he⟩ := hnormalize (a i) (ha i)
              have hz : (e.symm y).re=0 := by rw [←ht,he,e.symm_apply_apply];simp [verticalPath]
              have hn (z : H2) (hzC : z∈C) : (e.symm z).re≠0 := by
                intro hz0
                have hza : z∈range (a i) := by
                  refine ⟨Real.log (e.symm z).im,?_⟩
                  rw [he]
                  apply e.symm.injective
                  rw [e.symm_apply_apply]
                  apply UpperHalfPlane.ext_re_im
                  · simpa [verticalPath] using hz0.symm
                  · simp [verticalPath,Real.exp_log (e.symm z).im_pos]
                exact (connectedComponentIn_subset F x hzC) (mem_iUnion.mpr ⟨i,hza⟩)
              have hc : IsPreconnected C := isPreconnected_connectedComponentIn
              have hcont : Continuous (fun z : H2 => (e.symm z).re) :=
                UpperHalfPlane.continuous_re.comp e.symm.continuous
              have hxC : x∈C := mem_connectedComponentIn hx
              rcases lt_or_gt_of_ne (hn x hxC) with hxneg|hxpos
              · have hhalf : closure C⊆{z : H2 | (e.symm z).re≤0} := by
                  apply closure_minimal
                  · intro z hzC
                    exact le_of_lt (hc.gt_of_ne hcont.continuousOn hn ⟨x,hxC,hxneg⟩ hzC)
                  · exact isClosed_le hcont continuous_const
                let f : ℝ → H2 := fun r => e ⟨(r : ℂ)+(e.symm y).im*Complex.I,by
                  simpa using (e.symm y).im_pos⟩
                have hfc : Continuous f := by dsimp [f];fun_prop
                have hf0 : f 0=y := by
                  apply e.symm.injective
                  simp only [f,e.symm_apply_apply]
                  apply UpperHalfPlane.ext_re_im <;> simp [hz]
                have hnb : f ⁻¹' interior (closure C)∈nhds (0 : ℝ) :=
                  hfc.continuousAt.preimage_mem_nhds (by rw [hf0];exact isOpen_interior.mem_nhds hy)
                obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnb
                have hmem := hhalf (interior_subset (hball (show ε/2∈Metric.ball (0 : ℝ) ε by
                  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<ε/2)]
                  linarith)))
                have hfRe : (e.symm (f (ε/2))).re=ε/2 := by simp [f]
                change (e.symm (f (ε/2))).re≤0 at hmem
                rw [hfRe] at hmem
                linarith
              · have hhalf : closure C⊆{z : H2 | 0≤(e.symm z).re} := by
                  apply closure_minimal
                  · intro z hzC
                    exact le_of_lt (hc.lt_of_ne hcont.continuousOn hn ⟨x,hxC,hxpos⟩ hzC)
                  · exact isClosed_le continuous_const hcont
                let f : ℝ → H2 := fun r => e ⟨(-(r : ℂ))+(e.symm y).im*Complex.I,by
                  simpa using (e.symm y).im_pos⟩
                have hfc : Continuous f := by dsimp [f];fun_prop
                have hf0 : f 0=y := by
                  apply e.symm.injective
                  simp only [f,e.symm_apply_apply]
                  apply UpperHalfPlane.ext_re_im <;> simp [hz]
                have hnb : f ⁻¹' interior (closure C)∈nhds (0 : ℝ) :=
                  hfc.continuousAt.preimage_mem_nhds (by rw [hf0];exact isOpen_interior.mem_nhds hy)
                obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnb
                have hmem := hhalf (interior_subset (hball (show ε/2∈Metric.ball (0 : ℝ) ε by
                  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<ε/2)]
                  linarith)))
                have hfRe : (e.symm (f (ε/2))).re= -(ε/2) := by simp [f]
                change 0≤(e.symm (f (ε/2))).re at hmem
                rw [hfRe] at hmem
                linarith
            apply subset_antisymm
            · intro y hy
              have hyF : y∈F := hsub hy
              by_contra hyC
              have hdis : Disjoint C (connectedComponentIn F y) := by
                apply disjoint_left.mpr
                intro z hzC hzy
                have he := connectedComponentIn_eq hzy
                have hyy : y∈connectedComponentIn F z := by
                  rw [←he];exact mem_connectedComponentIn hyF
                rw [←connectedComponentIn_eq hzC] at hyy
                exact hyC hyy
              have hny : connectedComponentIn F y∈nhds y := (hF.connectedComponentIn).mem_nhds
                (mem_connectedComponentIn hyF)
              obtain ⟨z,hzy,hzC⟩ := mem_closure_iff_nhds.mp (interior_subset hy) _ hny
              exact disjoint_left.mp hdis hzC hzy
            · exact hopen.subset_interior_iff.mpr subset_closure
          have hid {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
              (p : P → E) (hp : Continuous p) (F : Set E) (x : P) :
              connectedComponentIn (p ⁻¹' connectedComponentIn F (p x)) x=
                connectedComponentIn (p ⁻¹' F) x := by
            apply subset_antisymm
            · exact connectedComponentIn_mono x (Set.preimage_mono (connectedComponentIn_subset F (p x)))
            · by_cases hx : p x∈F
              · have hx' : x∈p ⁻¹' F := hx
                have hmaps : p '' connectedComponentIn (p ⁻¹' F) x⊆connectedComponentIn F (p x) :=
                  (hp.continuousOn.image_connectedComponentIn_subset hx').trans
                    (connectedComponentIn_mono (p x) (Set.image_preimage_subset p F))
                apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hx')
                intro z hz
                exact hmaps ⟨z,hz,rfl⟩
              · rw [connectedComponentIn_eq_empty (show x∉p ⁻¹' F from hx)]
                exact empty_subset _
          classical
          let F := (c.image∪d.image)ᶜ
          let U := connectedComponentIn F (p x)
          let C := connectedComponentIn (p ⁻¹' U) x
          have hF : IsOpen F :=
            ((isCompact_range c.embedded.continuous).isClosed.union
              (isCompact_range d.embedded.continuous).isClosed).isOpen_compl
          have hU : IsOpen U := hF.connectedComponentIn
          have hxU : p x∈U := mem_connectedComponentIn hx
          obtain ⟨γc,Tc,hTc,hγc,hperiodc,hrangec,hunitc⟩ := hcgeo
          obtain ⟨γd,Td,hTd,hγd,hperiodd,hranged,hunitd⟩ := hdgeo
          let γcC : ContinuousMap ℝ E := ⟨γc,hγc⟩
          let γdC : ContinuousMap ℝ E := ⟨γd,hγd⟩
          obtain ⟨aC,haC,heqC⟩ := actual_developed_geodesic_preimage_is_union_complete_lines
            p hp hmetric γcC hunitc
          obtain ⟨aD,haD,heqD⟩ := actual_developed_geodesic_preimage_is_union_complete_lines
            p hp hmetric γdC hunitd
          let lines : ({z : H2 // p z∈Set.range γcC} ⊕ {z : H2 // p z∈Set.range γdC}) → ℝ → H2 :=
            Sum.elim aC aD
          have hlines : ∀ i,Isometry (lines i) := by
            intro i
            cases i with
            | inl i => exact haC i
            | inr i => exact haD i
          have hunion : p ⁻¹' (c.image ∪ d.image)=⋃ i,Set.range (lines i) := by
            rw [←hrangec,←hranged,Set.preimage_union]
            change p ⁻¹' Set.range γcC ∪ p ⁻¹' Set.range γdC = _
            rw [heqC,heqD]
            simp only [Set.iUnion_sum,lines,Sum.elim_inl,Sum.elim_inr]
          have hCeq : C=connectedComponentIn (p ⁻¹' F) x := hid p hp.continuous F x
          have hxF : x∈p ⁻¹' F := hx
          have hFopen : IsOpen (p ⁻¹' F) := hF.preimage hp.continuous
          have hreg : interior (closure C)=C := by
            rw [hCeq]
            dsimp only [F] at hxF hFopen ⊢
            rw [Set.preimage_compl,hunion] at hxF hFopen ⊢
            exact hregular lines hlines x hxF hFopen
          have hconv : ∀y∈C,∀z∈C,∀w : H2,dist y w+dist w z=dist y z → w∈C := by
            rw [hCeq]
            dsimp only [F]
            rw [Set.preimage_compl,hunion]
            exact actual_complete_geodesic_complement_component_metric_convex lines hlines x
          exact ⟨(hU.preimage hp.continuous).connectedComponentIn,hreg,hconv⟩
        have hcontract (C : Set H2) (o : C)
          (hC : ∀ a∈C,∀ b∈C,∀ z : H2,dist a z+dist z b=dist a b → z∈C) :
          ContractibleSpace C := by
          have hinterp : ∃ f : C(unitInterval × H2 × H2,H2),
              ∀ x, dist x.2.1 (f x)+dist (f x) x.2.2=dist x.2.1 x.2.2 ∧
                dist x.2.1 (f x)=(x.1:ℝ)*dist x.2.1 x.2.2 := by
            classical
            have hpoint (a b : H2) (t : unitInterval) :
                ∃! z : H2,dist a z+dist z b=dist a b ∧ dist a z=(t:ℝ)*dist a b := by
              obtain ⟨e,ha,hb⟩ := exists_pair_vertical_isometry a b
              let α := Real.log (e a).im
              let β := Real.log (e b).im
              let s := (1-(t:ℝ))*α+(t:ℝ)*β
              let z := e.symm (verticalPath s)
              have hs : s∈Set.uIcc α β := by
                rw [←segment_eq_uIcc,segment_eq_image]
                exact ⟨t,t.property,by simp only [smul_eq_mul];rfl⟩
              have hezre : (e z).re=0 := by simp [z,verticalPath]
              have hezlog : Real.log (e z).im=s := by simp [z,verticalPath]
              have hseg : dist a z+dist z b=dist a b :=
                (metric_segment_iff_in_vertical_interval e a b z ha hb).mpr ⟨hezre,by simpa [hezlog] using hs⟩
              have hdist : dist a z=(t:ℝ)*dist a b := by
                rw [←e.dist_eq a z,←e.dist_eq a b,UpperHalfPlane.dist_of_re_eq (ha.trans hezre.symm),
                  UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm),hezlog]
                change |α-s|=(t:ℝ)*|α-β|
                rw [show α-s=(t:ℝ)*(α-β) by dsimp [s];ring,abs_mul,abs_of_nonneg t.property.1]
              refine ⟨z,⟨hseg,hdist⟩,?_⟩
              intro u hu
              obtain ⟨hure,hulog⟩ := (metric_segment_iff_in_vertical_interval e a b u ha hb).mp hu.1
              have huDist := hu.2
              rw [←e.dist_eq a u,←e.dist_eq a b,UpperHalfPlane.dist_of_re_eq (ha.trans hure.symm),
                UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm)] at huDist
              have hlog : Real.log (e u).im=s := by
                change |α-Real.log (e u).im|=(t:ℝ)*|α-β| at huDist
                change Real.log (e u).im∈Set.uIcc α β at hulog
                rcases le_total α β with hab | hba
                · rw [Set.uIcc_of_le hab,Set.mem_Icc] at hulog
                  rw [abs_of_nonpos (by linarith : α-Real.log (e u).im≤0),
                    abs_of_nonpos (by linarith : α-β≤0)] at huDist
                  dsimp [s]
                  nlinarith
                · rw [Set.uIcc_of_ge hba,Set.mem_Icc] at hulog
                  rw [abs_of_nonneg (by linarith : 0≤α-Real.log (e u).im),
                    abs_of_nonneg (by linarith : 0≤α-β)] at huDist
                  dsimp [s]
                  nlinarith
              apply e.injective
              change e u=e (e.symm (verticalPath s))
              rw [e.apply_symm_apply]
              apply UpperHalfPlane.ext_re_im
              · simpa [verticalPath] using hure
              · have hh := congrArg Real.exp hlog
                simpa [verticalPath,Real.exp_log (e u).im_pos] using hh
            let f : unitInterval × H2 × H2 → H2 := fun x => (hpoint x.2.1 x.2.2 x.1).exists.choose
            have hf : ∀ x, dist x.2.1 (f x)+dist (f x) x.2.2=dist x.2.1 x.2.2 ∧
                dist x.2.1 (f x)=(x.1:ℝ)*dist x.2.1 x.2.2 := by
              intro x
              exact (hpoint x.2.1 x.2.2 x.1).exists.choose_spec
            have hu : ∀ x z, dist x.2.1 z+dist z x.2.2=dist x.2.1 x.2.2 →
                dist x.2.1 z=(x.1:ℝ)*dist x.2.1 x.2.2 → z=f x := by
              intro x z hz1 hz2
              exact (hpoint x.2.1 x.2.2 x.1).unique ⟨hz1,hz2⟩ (hf x)
            have hc : Continuous f := by
              have hlocal (o : H2) (R : ℝ) :
                  ContinuousOn f {x | dist o x.2.1 ≤ R ∧ dist o x.2.2 ≤ R} := by
                let S : Set (unitInterval × H2 × H2) := {x | dist o x.2.1 ≤ R ∧ dist o x.2.2 ≤ R}
                let T : Set H2 := Metric.closedBall o (3*R)
                have hbound (x : S) : f x.val ∈ T := by
                  have hab := dist_triangle x.val.2.1 o x.val.2.2
                  have haz := dist_triangle o x.val.2.1 (f x.val)
                  have hbz := dist_nonneg (x := f x.val) (y := x.val.2.2)
                  have hz := (hf x.val).1
                  have ha := x.property.1
                  have hb := x.property.2
                  rw [dist_comm x.val.2.1 o] at hab
                  change dist (f x.val) o ≤ 3*R
                  rw [dist_comm]
                  linarith
                let g : S → T := fun x => ⟨f x.val, hbound x⟩
                have hgraph : IsClosed g.graph := by
                  have h1 : Continuous (fun p : S × T => dist p.1.val.2.1 p.2.val +
                      dist p.2.val p.1.val.2.2) := by fun_prop
                  have h2 : Continuous (fun p : S × T => dist p.1.val.2.1 p.1.val.2.2) := by fun_prop
                  have h3 : Continuous (fun p : S × T => dist p.1.val.2.1 p.2.val) := by fun_prop
                  have h4 : Continuous (fun p : S × T => (p.1.val.1 : ℝ) *
                      dist p.1.val.2.1 p.1.val.2.2) := by fun_prop
                  convert (isClosed_eq h1 h2).inter (isClosed_eq h3 h4) using 1
                  ext p
                  change g p.1 = p.2 ↔ _
                  constructor
                  · intro h
                    have he : f p.1.val = p.2.val := congrArg Subtype.val h
                    simpa [he] using hf p.1.val
                  · intro h
                    apply Subtype.ext
                    exact (hu p.1.val p.2.val h.1 h.2).symm
                letI : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_closedBall o (3*R))
                have hg : Continuous g := continuous_of_isClosed_graph hgraph
                exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hg)
              rw [continuous_iff_continuousAt]
              intro x
              let R := max (dist x.2.1 x.2.1) (dist x.2.1 x.2.2) + 1
              apply (hlocal x.2.1 R).continuousAt
              have ha : dist x.2.1 x.2.1 < R := by dsimp [R]; linarith [le_max_left (dist x.2.1 x.2.1) (dist x.2.1 x.2.2)]
              have hb : dist x.2.1 x.2.2 < R := by dsimp [R]; linarith [le_max_right (dist x.2.1 x.2.1) (dist x.2.1 x.2.2)]
              have hca : Continuous (fun y : unitInterval × H2 × H2 => dist x.2.1 y.2.1) := by fun_prop
              have hcb : Continuous (fun y : unitInterval × H2 × H2 => dist x.2.1 y.2.2) := by fun_prop
              apply Filter.mem_of_superset (Filter.inter_mem ((hca.isOpen_preimage _ isOpen_Iio).mem_nhds ha) ((hcb.isOpen_preimage _ isOpen_Iio).mem_nhds hb))
              intro y hy
              exact ⟨hy.1.le,hy.2.le⟩
            exact ⟨⟨f,hc⟩,hf⟩
          obtain ⟨f,hf⟩ := hinterp
          let g : unitInterval × C → C := fun x =>
            ⟨f (x.1,x.2.val,o.val),hC x.2.val x.2.property o.val o.property (f (x.1,x.2.val,o.val)) (hf (x.1,x.2.val,o.val)).1⟩
          have hg : Continuous g := by
            apply Continuous.subtype_mk
            exact f.continuous.comp (by fun_prop)
          apply (contractible_iff_id_nullhomotopic C).mpr
          refine ⟨o,⟨{toFun := g,continuous_toFun := hg,map_zero_left := ?_,map_one_left := ?_}⟩⟩
          · intro x
            apply Subtype.ext
            have h := (hf (0,x.val,o.val)).2
            change dist x.val (f (0,x.val,o.val)) = 0 * dist x.val o.val at h
            have hz : dist x.val (f (0,x.val,o.val))=0 := by simpa only [zero_mul] using h
            exact (dist_eq_zero.mp hz).symm
          · intro x
            apply Subtype.ext
            have h := (hf (1,x.val,o.val)).1
            have h1 := (hf (1,x.val,o.val)).2
            change dist x.val (f (1,x.val,o.val)) = 1 * dist x.val o.val at h1
            change dist x.val (f (1,x.val,o.val)) + dist (f (1,x.val,o.val)) o.val = dist x.val o.val at h
            rw [one_mul] at h1
            have hz : dist (f (1,x.val,o.val)) o.val=0 := by linarith
            exact dist_eq_zero.mp hz
        letI := a
        intro U D K
        have hclosed : IsClosed (c.image∪d.image) :=
          (isCompact_range c.embedded.continuous).isClosed.union (isCompact_range d.embedded.continuous).isClosed
        have hUopen : IsOpen U := hclosed.isOpen_compl.connectedComponentIn
        have hUconn : IsConnected U := isConnected_connectedComponentIn_iff.mpr hx
        have hxU : p x∈U := mem_connectedComponentIn hx
        obtain ⟨b,q,hq,hproj,hact⟩ := actual_open_cut_component_deck_stabilizer_quotient_cover_same_action p hp U hUopen hUconn x hxU
        letI := b
        have hreg := hRegular c d hcgeo hdgeo p hp.isCoveringMap hm x hx
        have hconv : ∀y∈D,∀z∈D,∀w : H2,dist y w+dist w z=dist y z →w∈D := hreg.2.2
        have hcontractD : ContractibleSpace D := hcontract D ⟨x,mem_connectedComponentIn hxU⟩ hconv
        letI := hcontractD
        refine ⟨b,q,hq,hproj,hact,?_,hcontractD,inferInstance,hreg.1,hreg.2.1,hconv⟩
        intro z
        obtain ⟨W,hW,hzW,hmetric⟩ := hm z.val
        refine ⟨Subtype.val ⁻¹' W,hW.preimage continuous_subtype_val,hzW,?_⟩
        intro u hu v hv
        change dist (q u).val (q v).val=dist u.val v.val
        rw [hproj,hproj]
        exact hmetric u.val hu v.val hv
      have hOriginalHalfPeriodOrientation {E : Type} [TopologicalSpace E] (c : Curve E) (U : Set E)
          (p : ℝ → E) (T : ℝ) (hT : 0<T) (e : Circle ≃ₜ c.image)
          (he : ∀t : ℝ,(e (Circle.exp (2*Real.pi*t/T))).val=p t)
          (τ : ↥(U∪c.image) → ↥(U∪c.image))
          (hhalf : ∀t : ℝ,∃ht : p t∈U∪c.image,(τ ⟨p t,ht⟩).val=p (t+T/2)) :
          ∃φ : Circle ≃ₜ Circle,
            (∀z : Circle,∃hz : c.map z∈U∪c.image,(τ ⟨c.map z,hz⟩).val=c.map (φ z)) ∧
            FreeHomotopic ⟨φ,φ.continuous⟩ ⟨id,continuous_id⟩ := by
        have hOriginalOrientation {E : Type} [TopologicalSpace E] (c : Curve E)
            (f : C(Circle,E)) (hf : IsEmbedding f) (hrange : range f=c.image)
            (J : E → E) (u : Circle) (hclock : ∀z : Circle,J (f z)=f (u*z)) :
            ∃φ : Circle ≃ₜ Circle,(∀z : Circle,J (c.map z)=c.map (φ z)) ∧
              FreeHomotopic ⟨φ,φ.continuous⟩ ⟨id,continuous_id⟩ := by
          have hRotation (e : Circle ≃ₜ Circle) (u : Circle) :
              FreeHomotopic
                ⟨fun z=>e (u*e.symm z),by fun_prop⟩
                ⟨id,continuous_id⟩ := by
            obtain ⟨θ,hθ⟩ := Circle.exp_surjective u
            let H : C(Circle × CurveComplex.Interval,Circle) :=
              ⟨fun x=>e (Circle.exp ((1-(x.2:ℝ))*θ)*e.symm x.1),by fun_prop⟩
            refine ⟨H,?_,?_⟩
            · intro z
              change e (Circle.exp ((1-(0:ℝ))*θ)*e.symm z)=e (u*e.symm z)
              simp only [sub_zero,one_mul,hθ]
            · intro z
              change e (Circle.exp ((1-(1:ℝ))*θ)*e.symm z)=z
              simp only [sub_self,zero_mul,Circle.exp_zero,one_mul,e.apply_symm_apply]
          let ec : Circle ≃ₜ c.image := c.embedded.toHomeomorph
          let ef : Circle ≃ₜ c.image := hf.toHomeomorph.trans (Homeomorph.setCongr hrange)
          let e : Circle ≃ₜ Circle := ec.trans ef.symm
          let φ : Circle ≃ₜ Circle := e.trans ((Homeomorph.mulLeft u).trans e.symm)
          have hec (z : Circle) : (ec z).val=c.map z := rfl
          have hef (z : Circle) : (ef z).val=f z := rfl
          have he (z : Circle) : f (e z)=c.map z := by
            change (ef (ef.symm (ec z))).val=(ec z).val
            rw [ef.apply_symm_apply]
          have hes (z : Circle) : c.map (e.symm z)=f z := by
            exact (he (e.symm z)).symm.trans (congrArg f (e.apply_symm_apply z))
          refine ⟨φ,?_,?_⟩
          · intro z
            rw [←he,hclock]
            change f (u*e z)=c.map (e.symm (u*e z))
            exact (hes _).symm
          · exact hRotation e.symm u
        classical
        let J : E → E := fun y=>if h : y∈U∪c.image then (τ ⟨y,h⟩).val else y
        let f : C(Circle,E) := ⟨fun z=>(e z).val,continuous_subtype_val.comp e.continuous⟩
        have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp e.isEmbedding
        have hrange : range f=c.image := by
          ext y
          constructor
          · rintro ⟨z,rfl⟩;exact (e z).property
          · intro hy
            exact ⟨e.symm ⟨y,hy⟩,congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)⟩
        have hJp (t : ℝ) : J (p t)=p (t+T/2) := by
          obtain ⟨ht,hh⟩ := hhalf t
          simpa only [J,dif_pos ht] using hh
        have hclock (z : Circle) : J (f z)=f (Circle.exp Real.pi*z) := by
          obtain ⟨θ,rfl⟩ := Circle.exp_surjective z
          let t : ℝ := T*θ/(2*Real.pi)
          have harg : 2*Real.pi*t/T=θ := by dsimp [t];field_simp
          have harg2 : 2*Real.pi*(t+T/2)/T=Real.pi+θ := by dsimp [t];field_simp;ring
          have hft : f (Circle.exp θ)=p t := by change (e (Circle.exp θ)).val=p t;rw [←harg];exact he t
          rw [hft,hJp,←Circle.exp_add,←harg2]
          exact (he (t+T/2)).symm
        obtain ⟨φ,hφ,hhom⟩ := hOriginalOrientation c f hf hrange J (Circle.exp Real.pi) hclock
        refine ⟨φ,?_,hhom⟩
        intro z
        have hz : c.map z∈U∪c.image := Or.inr ⟨z,rfl⟩
        refine ⟨hz,?_⟩
        simpa only [J,dif_pos hz] using hφ z
      have hFibreEquivDescent {X Y : Type} (p : X → Y) (F : X → X)
          (hp : Function.Surjective p) (hF : Function.Involutive F)
          (hfibre : ∀x y : X,p x=p y →p (F x)=p (F y)) :
          ∃τ : Y ≃ Y,Function.Involutive τ ∧ ∀x : X,τ (p x)=p (F x) := by
        classical
        let t : Y → Y := fun y=>p (F (Classical.choose (hp y)))
        have ht (x : X) : t (p x)=p (F x) :=
          hfibre (Classical.choose (hp (p x))) x (Classical.choose_spec (hp (p x)))
        have hinv (y : Y) : t (t y)=y := by
          obtain ⟨x,rfl⟩ := hp y
          calc
            t (t (p x))=t (p (F x)) := congrArg t (ht x)
            _=p (F (F x)) := ht (F x)
            _=p x := congrArg p (hF x)
        let τ : Y ≃ Y := {toFun:=t,invFun:=t,left_inv:=hinv,right_inv:=hinv}
        exact ⟨τ,hinv,ht⟩
      have hThreeFixedAssembly {X Y : Type} (t : X → X) (u : Y → Y) (f : Y → X) (hf : Function.Injective f)
          (center : X) (hc : center∉range f)
          (hrestrict : ∀y,t (f y)=f (u y))
          (hoff : ∀x,x∉range f → (t x=x ↔ x=center))
          (F : Finset Y) (hCard : F.card=2) (hSet : (F:Set Y)={y | u y=y}) :
          ∃T : Finset X,T.card=3 ∧ (T:Set X)={x | t x=x} := by
        classical
        let e : Y ↪ X := ⟨f,hf⟩
        let Fa : Finset X := F.map e
        have hcFa : center∉Fa := by
          intro hh
          obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hh
          exact hc ⟨y,he⟩
        let T : Finset X := insert center Fa
        have hTCard : T.card=3 := by
          rw [show T=insert center Fa from rfl,Finset.card_insert_of_notMem hcFa]
          simpa only [Fa,Finset.card_map,hCard]
        have hTSet : (T:Set X)={x | t x=x} := by
          ext x
          change x∈insert center Fa ↔ t x=x
          by_cases hx : x∈range f
          · obtain ⟨y,rfl⟩ := hx
            have hneq : f y≠center := fun hh=>hc ⟨y,hh⟩
            rw [Finset.mem_insert,or_iff_right hneq,hrestrict]
            constructor
            · intro hh
              obtain ⟨z,hz,hzy⟩ := Finset.mem_map.mp hh
              have he : z=y := hf hzy
              subst z
              exact congrArg f ((Set.ext_iff.mp hSet y).mp hz)
            · intro hh
              exact Finset.mem_map.mpr ⟨y,(Set.ext_iff.mp hSet y).mpr (hf hh),rfl⟩
          · have hxFa : x∉Fa := by
              intro hh
              obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hh
              exact hx ⟨y,he⟩
            rw [Finset.mem_insert,or_iff_left hxFa,hoff x hx]
        exact ⟨T,hTCard,hTSet⟩
      have hOrbitKernelTransport {G X Y : Type} [Group G] (a : MulAction G X) (K : Subgroup G)
          (p : X → Y) (F : X → X) (A : Set X)
          (hproj : ∀k : K,∀z : X,p (@SMul.smul G X a.toSMul k.val z)=p z)
          (hFproj : ∀k : K,∀z : X,p (F (@SMul.smul G X a.toSMul k.val z))=p (F z))
          (hkernel : ∀z∈A,∀w∈A,p z=p w →p (F z)=p (F w)) :
          ∀z∈⋃k : K,(fun x=>@SMul.smul G X a.toSMul k.val x) '' A,
            ∀w∈⋃k : K,(fun x=>@SMul.smul G X a.toSMul k.val x) '' A,
              p z=p w →p (F z)=p (F w) := by
        intro z hz w hw hzw
        obtain ⟨k,x,hx,rfl⟩ := Set.mem_iUnion.mp hz
        obtain ⟨l,y,hy,rfl⟩ := Set.mem_iUnion.mp hw
        rw [hFproj,hFproj]
        rw [hproj,hproj] at hzw
        exact hkernel x hx y hy hzw
      have hCutKernelAssembly {X Y : Type} (p : X → Y) (F : X → X) (D B : Set X) (d : Set Y)
          (hD : ∀z∈D,p z∉d) (hB : ∀z∈B,p z∈d)
          (hDD : ∀z∈D,∀w∈D,p z=p w →p (F z)=p (F w))
          (hBB : ∀z∈B,∀w∈B,p z=p w →p (F z)=p (F w)) :
          ∀z∈D∪B,∀w∈D∪B,p z=p w →p (F z)=p (F w) := by
        intro z hz w hw hzw
        rcases hz with hz|hz <;> rcases hw with hw|hw
        · exact hDD z hz w hw hzw
        · exact False.elim (hD z hz (hzw.symm ▸ hB w hw))
        · exact False.elim (hD w hw (hzw ▸ hB z hz))
        · exact hBB z hz w hw hzw
      have hActualSeamKernel {P E : Type} (α β : ℝ → P) (p : P → E) (j : P → P) (s T : ℝ)
          (hproj : ∀t,p (α t)=p (β (t+s)))
          (hfibre : ∀t u,p (α t)=p (α u) ↔ ∃n : ℤ,t=u+n*T)
          (h₀ : ∀t,j (α t)=β (-t)) (h₁ : ∀t,j (β t)=α (-t)) :
          ∀x∈range α∪range β,∀y∈range α∪range β,p x=p y → p (j x)=p (j y) := by
        have hβ (t : ℝ) : p (β t)=p (α (t-s)) := by
          have hh := hproj (t-s)
          simpa only [sub_add_cancel] using hh.symm
        let f : ℝ → ℝ := fun t => -t-s
        have hreflect {t u : ℝ} (hh : p (α t)=p (α u)) : p (α (f t))=p (α (f u)) := by
          obtain ⟨n,hn⟩ := (hfibre t u).mp hh
          apply (hfibre (f t) (f u)).mpr
          refine ⟨-n,?_⟩
          dsimp only [f]
          rw [hn]
          push_cast
          ring
        have hparam {x : P} (hx : x∈range α∪range β) :
            ∃t : ℝ,p x=p (α t) ∧ p (j x)=p (α (f t)) := by
          rcases hx with ⟨t,rfl⟩|⟨t,rfl⟩
          · refine ⟨t,rfl,?_⟩
            rw [h₀,hβ]
          · refine ⟨t-s,hβ t,?_⟩
            rw [h₁]
            congr 2
            dsimp only [f]
            ring
        intro x hx y hy hxy
        obtain ⟨t,hxt,hjxt⟩ := hparam hx
        obtain ⟨u,hyu,hjyu⟩ := hparam hy
        rw [hjxt,hjyu]
        exact hreflect (hxt.symm.trans (hxy.trans hyu))
      have hAxisPeriodTransport {X Y : Type} [MetricSpace X] (p : X → Y) (α β : ℝ → X)
          (hα : Isometry α) (hβ : Isometry β) (hr : range β=range α)
          (T : ℝ) (hαfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+(n:ℝ)*T) :
          ∀s t : ℝ,p (β s)=p (β t) ↔ ∃n : ℤ,s=t+(n:ℝ)*T := by
        classical
        have hReal (f : ℝ → ℝ) (hf : Isometry f) :
            (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
          let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
          let k : ℝ := A.toAffineMap.linear 1
          have hfac (t : ℝ) : f t=t*k+f 0 := by
            have h := A.toAffineMap.map_vadd 0 t
            have hlin : A.toAffineMap.linear t=t*k := by
              have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
              simpa [k,smul_eq_mul] using hh
            change f (t+0)=A.toAffineMap.linear t+f 0 at h
            simpa only [add_zero,hlin] using h
          have hk : |k|=1 := by
            have h := hf.dist_eq 1 0
            rw [hfac 1,hfac 0] at h
            simpa [Real.dist_eq] using h
          rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
          · left;intro t;rw [hfac,he];ring
          · right;intro t;rw [hfac,he];ring
        have hex (t : ℝ) : ∃s : ℝ,α s=β t := by
          have hx : β t∈range α := by rw [←hr];exact mem_range_self t
          exact hx
        let f : ℝ → ℝ := fun t=>Classical.choose (hex t)
        have hf (t : ℝ) : α (f t)=β t := Classical.choose_spec (hex t)
        have hfi : Isometry f := by
          apply Isometry.of_dist_eq
          intro s t
          rw [←hα.dist_eq,hf,hf,hβ.dist_eq]
        rcases hReal f hfi with hpos|hneg
        · intro s t
          rw [←hf s,←hf t,hαfibre]
          constructor
          · rintro ⟨n,hn⟩
            rw [hpos s,hpos t] at hn
            exact ⟨n,by linarith⟩
          · rintro ⟨n,hn⟩
            refine ⟨n,?_⟩
            rw [hpos s,hpos t]
            linarith
        · intro s t
          rw [←hf s,←hf t,hαfibre]
          constructor
          · rintro ⟨n,hn⟩
            rw [hneg s,hneg t] at hn
            refine ⟨-n,?_⟩
            push_cast
            linarith
          · rintro ⟨n,hn⟩
            refine ⟨-n,?_⟩
            rw [hneg s,hneg t]
            push_cast
            linarith
      have hActualProjectedReflectionTwoFixed {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
          (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
          (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T) (phase : ℝ) :
          ∃e : Circle ≃ₜ ↥(p '' range α),(∀t : ℝ,(e (Circle.exp (2*Real.pi*t/T))).val=p (α t)) ∧
          ∃τ : ↥(p '' range α) ≃ₜ ↥(p '' range α),Function.Involutive τ ∧
            (∀t : ℝ,τ (e (Circle.exp (2*Real.pi*t/T)))=e (Circle.exp (2*Real.pi*(-t-phase)/T))) ∧
            ∃F : Finset ↥(p '' range α),F.card=2 ∧ (F:Set ↥(p '' range α))={y | τ y=y} := by
        have hParam {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
            (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
            ∃f : C(Circle,E),IsEmbedding f ∧
              (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
              range f=p '' range α := by
          classical
          let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
          have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
          let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
          have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
            obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
            apply (hfibre _ _).mpr
            refine ⟨k,?_⟩
            rw [hk]
            field_simp
          have hψ : Continuous ψ := by
            apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
            have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
            rw [heq]
            fun_prop
          let f : C(Circle,E) := ⟨ψ,hψ⟩
          have hfinj : Function.Injective f := by
            intro z w hzw
            obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
            have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
              have hπ : (2*Real.pi)≠0 := by positivity
              have hT' : T≠0 := hT.ne'
              field_simp at hk
              nlinarith
            rw [←hθ z,←hθ w]
            exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
          have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
            change _=ψ _
            rw [hfac]
            congr 2
            field_simp
          refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
          apply Subset.antisymm
          · rintro y ⟨z,rfl⟩
            exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
          · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
            exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
        have hCircleTwo (u : Circle) :
            Function.Involutive (fun z : Circle => u * z⁻¹) ∧
            ∃ F : Finset Circle, F.card = 2 ∧ (F : Set Circle) = {z | u * z⁻¹ = z} := by
          classical
          constructor
          · intro z
            simp [mul_comm]
          · obtain ⟨θ,rfl⟩ := Circle.exp_surjective u
            let a : Circle := Circle.exp (θ/2)
            have ha : a^2 = Circle.exp θ := by
              dsimp [a]
              rw [pow_two,←Circle.exp_add]
              congr 1
              ring
            have hiff (z : Circle) : Circle.exp θ * z⁻¹ = z ↔ z = a ∨ z = -a := by
              constructor
              · intro h
                have ht := congrArg (fun w : Circle => w*z) h
                simp only [mul_assoc,inv_mul_cancel,mul_one] at ht
                have hs : (z : ℂ)^2 = (a : ℂ)^2 := by
                  have hh : z^2 = a^2 := by rw [pow_two,←ht,ha]
                  simpa only [Circle.coe_pow] using congrArg (fun z : Circle => (z : ℂ)) hh
                rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
                · exact Or.inl (Circle.coe_injective he)
                · exact Or.inr (Circle.coe_injective (by simpa using he))
              · rintro (rfl | rfl)
                · rw [←ha,pow_two]
                  group
                · apply Circle.coe_injective
                  rw [←ha]
                  simp only [Circle.coe_mul,Circle.coe_inv,Circle.coe_pow,Circle.coe_neg]
                  field_simp [Circle.coe_ne_zero a]
                  <;> ring
            refine ⟨{a,-a},?_,?_⟩
            · simp [Circle.neg_ne_self a,(Circle.neg_ne_self a).symm]
            · ext z
              simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,Set.mem_setOf_eq]
              exact (hiff z).symm
        classical
        obtain ⟨f,hf,hparam,hrange⟩ := hParam p α T hT hfibre
        let e : Circle ≃ₜ ↥(p '' range α) := hf.toHomeomorph.trans (Homeomorph.setCongr hrange)
        have he (t : ℝ) : (e (Circle.exp (2*Real.pi*t/T))).val=p (α t) := (hparam t).symm
        let u : Circle := Circle.exp (-2*Real.pi*phase/T)
        obtain ⟨hinv,Fc,hFcCard,hFc⟩ := hCircleTwo u
        let φ : Circle ≃ₜ Circle := {
          toFun := fun z => u*z⁻¹
          invFun := fun z => u*z⁻¹
          left_inv := hinv
          right_inv := hinv
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
        let τ : ↥(p '' range α) ≃ₜ ↥(p '' range α) := (e.symm.trans φ).trans e
        have hτe (z : Circle) : τ (e z)=e (u*z⁻¹) := by
          change e (φ (e.symm (e z)))=e (u*z⁻¹)
          rw [e.symm_apply_apply]
          rfl
        have hτinv : Function.Involutive τ := by
          intro y
          obtain ⟨z,rfl⟩ := e.surjective y
          rw [hτe,hτe]
          exact congrArg e (hinv z)
        have hτclock (t : ℝ) : τ (e (Circle.exp (2*Real.pi*t/T)))=e (Circle.exp (2*Real.pi*(-t-phase)/T)) := by
          rw [hτe]
          congr 1
          dsimp only [u]
          rw [←Circle.exp_neg,←Circle.exp_add]
          congr 1
          ring
        let F : Finset ↥(p '' range α) := Fc.map e.toEquiv.toEmbedding
        have hCard : F.card=2 := by simpa only [F,Finset.card_map] using hFcCard
        have hSet : (F:Set ↥(p '' range α))={y | τ y=y} := by
          ext y
          obtain ⟨z,rfl⟩ := e.surjective y
          change e z∈F ↔ τ (e z)=e z
          rw [hτe]
          constructor
          · intro hz
            obtain ⟨x,hx,hex⟩ := Finset.mem_map.mp hz
            have hxe : x=z := e.injective hex
            subst x
            apply congrArg e
            exact (Set.ext_iff.mp hFc z).mp hx
          · intro hz
            have hfix : u*z⁻¹=z := e.injective hz
            apply Finset.mem_map.mpr
            exact ⟨z,(Set.ext_iff.mp hFc z).mpr hfix,rfl⟩
        exact ⟨e,he,τ,hτinv,hτclock,F,hCard,hSet⟩
      have hDeckNormalize {G E : Type} [Group G] (a : MulAction G H2) (p : H2 → E)
          (hiso : ∀g : G,Isometry (fun z : H2=>@SMul.smul G H2 a.toSMul g z))
          (hproj : ∀g : G,∀z : H2,p (@SMul.smul G H2 a.toSMul g z)=p z)
          (e : H2 ≃ᵢ H2) (δ₀ δ₁ γ : G) (P Q : SL(2,ℝ))
          (hconj : γ*δ₀*γ⁻¹=δ₁)
          (h₀ : ∀z : H2,e (@SMul.smul G H2 a.toSMul δ₀ z)=P • e z)
          (h₁ : ∀z : H2,e (@SMul.smul G H2 a.toSMul δ₁ z)=Q • e z) :
          ∃g : H2 ≃ᵢ H2,
            (∀z : H2,g (e z)=e (@SMul.smul G H2 a.toSMul γ z)) ∧
            (∀z : H2,g (P • z)=Q • g z) ∧
            (∀z : H2,p (e.symm (g z))=p (e.symm z)) := by
        letI := a
        letI : SMul G H2 := a.toSMul
        let γiso : H2 ≃ᵢ H2 := {toEquiv:=MulAction.toPerm γ,isometry_toFun:=hiso γ}
        let g : H2 ≃ᵢ H2 := e.symm.trans (γiso.trans e)
        have hcomm : γ*δ₀=δ₁*γ := by
          have hh := congrArg (fun x : G=>x*γ) hconj
          simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
        refine ⟨g,?_,?_,?_⟩
        · intro z
          change e (γ • e.symm (e z))=e (γ • z)
          rw [e.symm_apply_apply]
        · intro z
          have hz : P • z=e (δ₀ • e.symm z) := by
            change P • z=e (@SMul.smul G H2 a.toSMul δ₀ (e.symm z))
            rw [h₀,e.apply_symm_apply]
          change e (γ • e.symm (P • z))=Q • e (γ • e.symm z)
          rw [hz,e.symm_apply_apply,←mul_smul,hcomm,mul_smul]
          exact h₁ (γ • e.symm z)
        · intro z
          change p (e.symm (e (γ • e.symm z)))=p (e.symm z)
          rw [e.symm_apply_apply]
          exact hproj γ (e.symm z)
      have hLiteralClock (d L : ℝ) :
          let D : ℝ → SL(2,ℝ) := fun s =>
            ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          let A := D (-d/2)*R*D L*R⁻¹*D (d/2)
          let B := D (d/2)*R*D L*R⁻¹*D (-d/2)
          (∀t : ℝ,A • (D (-d/2) • (R • verticalPath t))=D (-d/2) • (R • verticalPath (t+L))) ∧
          (∀t : ℝ,B • (D (d/2) • (R • verticalPath t))=D (d/2) • (R • verticalPath (t+L))) := by
        intro D R A B
        have Dv (s t : ℝ) : D s • verticalPath t=verticalPath (t+s) := by
          apply UpperHalfPlane.ext
          rw [UpperHalfPlane.coe_specialLinearGroup_apply]
          simp [D,verticalPath,UpperHalfPlane.num,UpperHalfPlane.denom]
          rw [div_eq_mul_inv,←Complex.exp_neg]
          simp only [neg_neg]
          rw [mul_right_comm,←Complex.exp_add]
          rw [show (s:ℂ)/2+(s:ℂ)/2=(s:ℂ) by ring]
          apply Complex.ext <;> simp [Complex.exp_re,Complex.exp_im,Real.exp_add,mul_comm]
        have hDadd (s t : ℝ) : D s*D t=D (s+t) := by
          apply Subtype.ext
          change (D s).val*(D t).val=(D (s+t)).val
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [D,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,add_div,neg_add,mul_comm]
        have hDzero : D 0=1 := by
          apply Subtype.ext
          change (D 0).val=(1 : Matrix (Fin 2) (Fin 2) ℝ)
          ext i j
          fin_cases i <;> fin_cases j <;> simp [D]
        have hDinv (s : ℝ) : (D s)⁻¹=D (-s) := by
          apply inv_eq_of_mul_eq_one_right
          rw [hDadd,add_neg_cancel,hDzero]
        have hi0 : D (d/2)=(D (-d/2))⁻¹ := by
          rw [hDinv]
          congr 1
          ring
        have hi1 : D (-d/2)=(D (d/2))⁻¹ := by
          rw [hDinv]
          congr 1
          ring
        constructor
        · intro t
          dsimp only [A]
          simp only [mul_smul]
          rw [hi0,inv_smul_smul,inv_smul_smul,Dv]
        · intro t
          dsimp only [B]
          simp only [mul_smul]
          rw [hi1,inv_smul_smul,inv_smul_smul,Dv]
      have hConjugateAxisRange (δ₀ δ₁ γ : H2 ≃ᵢ H2) (α β : ℝ → H2) (hα : Isometry α) (hβ : Isometry β)
          (L U ε : ℝ) (hL : L≠0) (hU : U≠0) (hε : 0<ε)
          (hdisp : ∀z : H2,ε≤dist z (δ₁ z))
          (hαclock : ∀t,δ₀ (α t)=α (t+L)) (hβclock : ∀t,δ₁ (β t)=β (t+U))
          (hconj : ∀z,γ (δ₀ z)=δ₁ (γ z)) : γ '' range α=range β := by
        let η : ℝ → H2 := fun t => γ (α t)
        have hη : Isometry η := γ.isometry.comp hα
        have hηclock (t : ℝ) : δ₁ (η t)=η (t+L) := by
          change δ₁ (γ (α t))=γ (α (t+L))
          rw [←hconj,hαclock]
        have hr := actual_h2_translated_isometric_lines_same_range δ₁ β η hβ hη ε hε hdisp
          U L hU hL hβclock hηclock
        exact (Set.range_comp γ α).symm.trans hr.symm
      have hDirectionClock {P : Type} [MetricSpace P] (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
          (g : P ≃ᵢ P) (hr : g '' range α=range β) (δ₀ δ₁ : P → P)
          (L : ℝ) (hL : L≠0)
          (h₀ : ∀t,δ₀ (α t)=α (t+L)) (h₁ : ∀t,δ₁ (β t)=β (t+L))
          (hcomm : ∀z,g (δ₀ z)=δ₁ (g z)) :
          ∃s : ℝ,∀t : ℝ,g (α t)=β (t+s) := by
        classical
        have hReal (f : ℝ → ℝ) (hf : Isometry f) :
            (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
          let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
          let k : ℝ := A.toAffineMap.linear 1
          have hfac (t : ℝ) : f t=t*k+f 0 := by
            have h := A.toAffineMap.map_vadd 0 t
            have hlin : A.toAffineMap.linear t=t*k := by
              have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
              simpa [k,smul_eq_mul] using hh
            change f (t+0)=A.toAffineMap.linear t+f 0 at h
            simpa only [add_zero,hlin] using h
          have hk : |k|=1 := by
            have h := hf.dist_eq 1 0
            rw [hfac 1,hfac 0] at h
            simpa [Real.dist_eq] using h
          rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
          · left;intro t;rw [hfac,he];ring
          · right;intro t;rw [hfac,he];ring
        have hExists (t : ℝ) : ∃s : ℝ,β s=g (α t) := by
          have hh : g (α t)∈g '' range α := ⟨α t,mem_range_self t,rfl⟩
          have hm : g (α t)∈range β := (Set.ext_iff.mp hr (g (α t))).mp hh
          obtain ⟨s,hs⟩ := hm
          exact ⟨s,hs⟩
        let f : ℝ → ℝ := fun t => Classical.choose (hExists t)
        have hf (t : ℝ) : β (f t)=g (α t) := Classical.choose_spec (hExists t)
        have hfi : Isometry f := by
          apply Isometry.of_dist_eq
          intro s t
          rw [←hβ.dist_eq,hf,hf,g.dist_eq,hα.dist_eq]
        have hclock (t : ℝ) : f (t+L)=f t+L := by
          apply hβ.injective
          rw [hf,←h₀,hcomm,←hf,h₁]
        rcases hReal f hfi with hp|hm
        · refine ⟨f 0,?_⟩
          intro t
          rw [←hf,hp]
          congr 1
          ring
        · exfalso
          have hh := hclock 0
          rw [zero_add,hm L,hm 0] at hh
          have hz : L=0 := by linarith
          exact hL hz
      have hSeamProjection {X Y : Type} (p : X → Y) (g : X ≃ X) (F : X → X)
          (hF : Function.Involutive F) (hrev : ∀x,g (F (g (F x)))=x)
          (hp : ∀x,p (g x)=p x) :
          (∀x,F (g x)=g.symm (F x)) ∧ (∀x,p (F (g x))=p (F x)) := by
        have hcomm (x : X) : F (g x)=g.symm (F x) := by
          apply g.injective
          rw [g.apply_symm_apply]
          have hh := hrev (F x)
          rw [hF] at hh
          exact hh
        have hpinv (x : X) : p (g.symm x)=p x := by
          have hh := hp (g.symm x)
          rw [g.apply_symm_apply] at hh
          exact hh.symm
        exact ⟨hcomm,fun x => by rw [hcomm,hpinv]⟩
      have verticalClockTwoBranches (g : H2 ≃ᵢ H2) (L : ℝ) (hclock : ∀t : ℝ,g (verticalPath t)=verticalPath (t+L)) :
          let D : SL(2,ℝ) := ⟨!![Real.exp (L/2),0;0,Real.exp (-(L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let ref : H2 → H2 := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
          (∀z : H2,g z=D • z) ∨ (∀z : H2,g z=D • ref z) := by
        intro D ref
        have hRigid (g : H2 → H2) (hg : Isometry g)
            (h0 : g (verticalPath 0)=verticalPath 0)
            (h1 : g (verticalPath 1)=verticalPath 1)
            (z₀ : H2) (hz₀ : z₀.re≠0) (hfix : g z₀=z₀) : ∀z : H2,g z=z := by
          have hCoordinates (z w : H2)
              (h0 : dist (verticalPath 0) z=dist (verticalPath 0) w)
              (h1 : dist (verticalPath 1) z=dist (verticalPath 1) w) :
              z.im=w.im ∧ z.re^2=w.re^2 := by
            have hc0 := congrArg Real.cosh h0
            have hc1 := congrArg Real.cosh h1
            rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc0 hc1
            simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
              Real.exp_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub,neg_sq,zero_add,mul_one] at hc0 hc1
            have hz : 0<z.im := z.im_pos
            have hw : 0<w.im := w.im_pos
            have hb : 1<Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
            have he0 : w.im*(z.re^2+z.im^2+1)=z.im*(w.re^2+w.im^2+1) := by
              field_simp at hc0
              nlinarith [hc0]
            have he1 : w.im*(z.re^2+z.im^2+(Real.exp (1:ℝ))^2)=
                z.im*(w.re^2+w.im^2+(Real.exp (1:ℝ))^2) := by
              field_simp at hc1
              nlinarith [hc1]
            have him : z.im=w.im := by
              have hp : 0<(Real.exp (1:ℝ))^2-1 := by nlinarith
              have hf : ((Real.exp (1:ℝ))^2-1)*(z.im-w.im)=0 := by nlinarith [he0,he1]
              have hh := (mul_eq_zero.mp hf).resolve_left hp.ne'
              exact sub_eq_zero.mp hh
            refine ⟨him,?_⟩
            rw [him] at he0
            have hh : w.im*(z.re^2-w.re^2)=0 := by nlinarith [he0]
            exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw.ne')
          intro z
          have hc := hCoordinates (g z) z (by simpa only [h0] using hg.dist_eq (verticalPath 0) z)
            (by simpa only [h1] using hg.dist_eq (verticalPath 1) z)
          have hd := congrArg Real.cosh (hg.dist_eq z z₀)
          rw [hfix,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hd
          rw [hc.1] at hd
          have hp : z₀.re*((g z).re-z.re)=0 := by
            field_simp at hd
            nlinarith [hc.2]
          have hre : (g z).re=z.re := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hz₀)
          exact UpperHalfPlane.ext_re_im hre hc.1
        have hCoordinates (z w : H2)
            (h0 : dist (verticalPath 0) z=dist (verticalPath 0) w)
            (h1 : dist (verticalPath 1) z=dist (verticalPath 1) w) :
            z.im=w.im ∧ z.re^2=w.re^2 := by
          have hc0 := congrArg Real.cosh h0
          have hc1 := congrArg Real.cosh h1
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc0 hc1
          simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
            Real.exp_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub,neg_sq,zero_add,mul_one] at hc0 hc1
          have hz : 0<z.im := z.im_pos
          have hw : 0<w.im := w.im_pos
          have hb : 1<Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
          have he0 : w.im*(z.re^2+z.im^2+1)=z.im*(w.re^2+w.im^2+1) := by
            field_simp at hc0
            nlinarith [hc0]
          have he1 : w.im*(z.re^2+z.im^2+(Real.exp (1:ℝ))^2)=
              z.im*(w.re^2+w.im^2+(Real.exp (1:ℝ))^2) := by
            field_simp at hc1
            nlinarith [hc1]
          have him : z.im=w.im := by
            have hp : 0<(Real.exp (1:ℝ))^2-1 := by nlinarith
            have hf : ((Real.exp (1:ℝ))^2-1)*(z.im-w.im)=0 := by nlinarith [he0,he1]
            have hh := (mul_eq_zero.mp hf).resolve_left hp.ne'
            exact sub_eq_zero.mp hh
          refine ⟨him,?_⟩
          rw [him] at he0
          have hh : w.im*(z.re^2-w.re^2)=0 := by nlinarith [he0]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw.ne')
        have hDiagonal (s : ℝ) :
            let D : SL(2,ℝ) := ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            ∀z : H2,(D • z).re=Real.exp s*z.re ∧ (D • z).im=Real.exp s*z.im := by
          intro D
          intro z
          have hc : ((D • z : H2) : ℂ)=
              (Real.exp s : ℂ)*(z:ℂ) := by
            rw [UpperHalfPlane.coe_specialLinearGroup_apply]
            simp [D,UpperHalfPlane.num,UpperHalfPlane.denom]
            rw [div_eq_mul_inv,←Complex.exp_neg]
            simp only [neg_neg]
            rw [mul_right_comm,←Complex.exp_add]
            congr 2
            ring
          constructor
          · simpa [Complex.mul_re,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.re hc
          · simpa [Complex.mul_im,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.im hc
        let Dm : SL(2,ℝ) := ⟨!![Real.exp (-L/2),0;0,Real.exp (-(-L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
        let g' : H2 ≃ᵢ H2 := g.trans (IsometryEquiv.constSMul Dm)
        have hDm (z : H2) : (Dm • z).re=Real.exp (-L)*z.re ∧ (Dm • z).im=Real.exp (-L)*z.im :=
          hDiagonal (-L) z
        have hD (z : H2) : (D • z).re=Real.exp L*z.re ∧ (D • z).im=Real.exp L*z.im :=
          hDiagonal L z
        have hnormclock (t : ℝ) : g' (verticalPath t)=verticalPath t := by
          change Dm • g (verticalPath t)=verticalPath t
          rw [hclock]
          apply UpperHalfPlane.ext_re_im
          · rw [(hDm _).1];simp [verticalPath]
          · rw [(hDm _).2]
            simp only [verticalPath,UpperHalfPlane.mk_im]
            rw [←Real.exp_add]
            congr 1;ring
        have hrefInv (z : H2) : ref (ref z)=z := by
          apply UpperHalfPlane.ext_re_im
          · change -(-z.re)=z.re
            ring
          · rfl
        have hrefIso : Isometry ref := by
          apply Isometry.of_dist_eq
          intro z w
          apply Real.cosh_injOn dist_nonneg dist_nonneg
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
          simp only [ref,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im]
          congr 1
          ring
        let refIso : H2 ≃ᵢ H2 := {
          toFun := ref
          invFun := ref
          left_inv := hrefInv
          right_inv := hrefInv
          isometry_toFun := hrefIso }
        have hrefVertical (t : ℝ) : ref (verticalPath t)=verticalPath t := by
          apply UpperHalfPlane.ext_re_im
          · simp [ref,verticalPath]
          · rfl
        have hUnwind (r : H2 → H2) (hh : ∀z,g' z=r z) : ∀w,g w=D • r w := by
          intro w
          have hwre : Real.exp (-L)*(g w).re=(r w).re :=
            (hDm (g w)).1.symm.trans (congrArg UpperHalfPlane.re (hh w))
          have hwim : Real.exp (-L)*(g w).im=(r w).im :=
            (hDm (g w)).2.symm.trans (congrArg UpperHalfPlane.im (hh w))
          have hprod : Real.exp L*Real.exp (-L)=1 := by rw [←Real.exp_add];simp
          have hr := congrArg (fun r : ℝ => Real.exp L*r) hwre
          have hi := congrArg (fun r : ℝ => Real.exp L*r) hwim
          simp only [←mul_assoc,hprod,one_mul] at hr hi
          exact UpperHalfPlane.ext_re_im (hr.trans (hD (r w)).1.symm) (hi.trans (hD (r w)).2.symm)
        let z₀ : H2 := ⟨⟨1,1⟩,by norm_num⟩
        have hz₀ : z₀.re≠0 := by norm_num [z₀]
        have hc := hCoordinates (g' z₀) z₀
          (by simpa only [hnormclock] using g'.isometry.dist_eq (verticalPath 0) z₀)
          (by simpa only [hnormclock] using g'.isometry.dist_eq (verticalPath 1) z₀)
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc.2 with hp|hm
        · left
          have hh : ∀z,g' z=z := hRigid g' g'.isometry (hnormclock 0) (hnormclock 1) z₀ hz₀
            (UpperHalfPlane.ext_re_im hp hc.1)
          exact hUnwind id hh
        · right
          let g'' : H2 ≃ᵢ H2 := g'.trans refIso
          have hv (t : ℝ) : g'' (verticalPath t)=verticalPath t := by
            change ref (g' (verticalPath t))=verticalPath t
            rw [hnormclock,hrefVertical]
          have hfix : g'' z₀=z₀ := by
            apply UpperHalfPlane.ext_re_im
            · change -(g' z₀).re=z₀.re
              rw [hm]
              ring
            · exact hc.1
          have hh : ∀z,g'' z=z := hRigid g'' g''.isometry (hv 0) (hv 1) z₀ hz₀ hfix
          apply hUnwind ref
          intro z
          have hz := congrArg ref (hh z)
          change ref (ref (g' z))=ref z at hz
          rw [hrefInv] at hz
          exact hz
      
      have verticalClockHalfTurnReversal (g : H2 ≃ᵢ H2) (L : ℝ) (hclock : ∀t : ℝ,g (verticalPath t)=verticalPath (t+L)) :
          let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
          ∀z : H2,g (J • (g (J • z)))=z := by
        intro J
        let D : ℝ → SL(2,ℝ) := fun s => ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
        let ref : H2 → H2 := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
        have hJD (s : ℝ) : J * D s = D (-s) * J := by
          apply Subtype.ext
          change J.val * (D s).val = (D (-s)).val * J.val
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [J,D,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
        have hDD (s : ℝ) : D s * D (-s)=1 := by
          apply Subtype.ext
          change (D s).val * (D (-s)).val = (1 : Matrix (Fin 2) (Fin 2) ℝ)
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [D,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,←Real.exp_add] <;> ring_nf <;> simp
        have hDiagonal (s : ℝ) :
            let D : SL(2,ℝ) := ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            ∀z : H2,(D • z).re=Real.exp s*z.re ∧ (D • z).im=Real.exp s*z.im := by
          intro D
          intro z
          have hc : ((D • z : H2) : ℂ)=
              (Real.exp s : ℂ)*(z:ℂ) := by
            rw [UpperHalfPlane.coe_specialLinearGroup_apply]
            simp [D,UpperHalfPlane.num,UpperHalfPlane.denom]
            rw [div_eq_mul_inv,←Complex.exp_neg]
            simp only [neg_neg]
            rw [mul_right_comm,←Complex.exp_add]
            congr 2
            ring
          constructor
          · simpa [Complex.mul_re,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.re hc
          · simpa [Complex.mul_im,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.im hc
        have hJcoe (z : H2) : ((J • z : H2) : ℂ) = -1 / (z : ℂ) := by
          rw [UpperHalfPlane.coe_specialLinearGroup_apply]
          norm_num [J,UpperHalfPlane.num,UpperHalfPlane.denom]
        have hJJ (z : H2) : J • (J • z)=z := by
          apply UpperHalfPlane.coe_injective
          rw [hJcoe,hJcoe]
          field_simp [UpperHalfPlane.ne_zero z]
        have hrefJ (z : H2) : ref (J • z)=J • ref z := by
          apply UpperHalfPlane.ext_re_im
          · change -(J • z).re=(J • ref z).re
            have h1 := congrArg Complex.re (hJcoe z)
            have h2 := congrArg Complex.re (hJcoe (ref z))
            simp only [Complex.div_re,Complex.neg_re,Complex.one_re,Complex.neg_im,Complex.one_im,neg_zero,zero_mul,add_zero,Complex.normSq_apply,ref,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at h1 h2
            change -(↑(J • z) : ℂ).re=(↑(J • ref z) : ℂ).re
            rw [h1,h2]
            simp only [zero_div,add_zero]
            change -(-1*z.re/(z.re*z.re+z.im*z.im)) = -1*(-z.re)/((-z.re)*(-z.re)+z.im*z.im)
            ring
          · change (J • z).im=(J • ref z).im
            have h1 := congrArg Complex.im (hJcoe z)
            have h2 := congrArg Complex.im (hJcoe (ref z))
            simp only [Complex.div_im,Complex.neg_re,Complex.one_re,Complex.neg_im,Complex.one_im,neg_zero,zero_mul,zero_sub,Complex.normSq_apply,ref,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at h1 h2
            change (↑(J • z) : ℂ).im=(↑(J • ref z) : ℂ).im
            rw [h1,h2]
            change 0/(z.re*z.re+z.im*z.im)-(-1)*z.im/(z.re*z.re+z.im*z.im) = 0/((-z.re)*(-z.re)+z.im*z.im)-(-1)*z.im/((-z.re)*(-z.re)+z.im*z.im)
            ring
        have hrefD (s : ℝ) (z : H2) : ref (D s • z)=D s • ref z := by
          apply UpperHalfPlane.ext_re_im
          · change -(D s • z).re=(D s • ref z).re
            rw [(hDiagonal s z).1,(hDiagonal s (ref z)).1]
            change -(Real.exp s*z.re)=Real.exp s*(-z.re)
            ring
          · change (D s • z).im=(D s • ref z).im
            rw [(hDiagonal s z).2,(hDiagonal s (ref z)).2]
            rfl
        have hrefref (z : H2) : ref (ref z)=z := by
          apply UpperHalfPlane.ext_re_im <;> simp [ref]
        have hcancel (z : H2) : D L • (J • (D L • (J • z)))=z := by
          rw [←mul_smul J (D L),hJD,mul_smul,hJJ,←mul_smul,hDD,one_smul]
        rcases verticalClockTwoBranches g L hclock with hpos|hneg
        · intro z
          change ∀z : H2,g z=D L • z at hpos
          rw [hpos,hpos,hcancel]
        · intro z
          change ∀z : H2,g z=D L • ref z at hneg
          simp only [hneg,hrefJ,hrefD,hrefref]
          exact hcancel z
      
      have normalizedClockFrameHalfTurnReversal (g S₀ S₁ : H2 ≃ᵢ H2) (L : ℝ)
          (hclock : ∀t : ℝ,g (S₀ (verticalPath t))=S₁ (verticalPath (t+L))) :
          let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
          (∀z : H2,J • S₀ z=S₁ (J • z)) →
          (∀z : H2,J • S₁ z=S₀ (J • z)) →
          ∀z : H2,g (J • g (J • z))=z := by
        intro J h₀ h₁
        let n : H2 ≃ᵢ H2 := S₀.trans (g.trans S₁.symm)
        have hnclock (t : ℝ) : n (verticalPath t)=verticalPath (t+L) := by
          change S₁.symm (g (S₀ (verticalPath t)))=verticalPath (t+L)
          rw [hclock,S₁.symm_apply_apply]
        have hnrev : ∀z : H2,n (J • n (J • z))=z := verticalClockHalfTurnReversal n L hnclock
        have hinv₀ (z : H2) : S₀.symm (J • z)=J • S₁.symm z := by
          have hh := congrArg S₀.symm (h₁ (S₁.symm z))
          simpa only [S₁.apply_symm_apply,S₀.symm_apply_apply] using hh
        have hg (z : H2) : g z=S₁ (n (S₀.symm z)) := by
          change g z=S₁ (S₁.symm (g (S₀ (S₀.symm z))))
          rw [S₀.apply_symm_apply,S₁.apply_symm_apply]
        intro z
        rw [hg,hinv₀,hg,S₁.symm_apply_apply,hinv₀,hnrev,S₁.apply_symm_apply]
      
      have hLiteralSeam (g : H2 ≃ᵢ H2) (d L : ℝ) :
          let D : ℝ → SL(2,ℝ) := fun s => ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          (∀t : ℝ,g (D (-d/2) • (R • verticalPath t))=D (d/2) • (R • verticalPath (t+L))) →
          ∀z : H2,g (J • g (J • z))=z := by
        intro D J R hclock
        have hJD (s : ℝ) : J * D s = D (-s) * J := by
          apply Subtype.ext
          change J.val * (D s).val = (D (-s)).val * J.val
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [J,D,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
        have hJR : J * R=R * J := by
          apply Subtype.ext
          change J.val * R.val=R.val * J.val
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [J,R,stabilizerRotation,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,one_div] <;> ring
        let S₀ : H2 ≃ᵢ H2 := (IsometryEquiv.constSMul R).trans (IsometryEquiv.constSMul (D (-d/2)))
        let S₁ : H2 ≃ᵢ H2 := (IsometryEquiv.constSMul R).trans (IsometryEquiv.constSMul (D (d/2)))
        apply normalizedClockFrameHalfTurnReversal g S₀ S₁ L hclock
        · intro z
          change J • (D (-d/2) • (R • z))=D (d/2) • (R • (J • z))
          rw [←mul_smul J (D (-d/2)),hJD,mul_smul,←mul_smul J R,hJR,mul_smul]
          congr 2
          congr 1
          ring
        · intro z
          change J • (D (d/2) • (R • z))=D (-d/2) • (R • (J • z))
          rw [←mul_smul J (D (d/2)),hJD,mul_smul,←mul_smul J R,hJR,mul_smul]
          congr 2
          congr 1
          ring
      have hClosureOverComponent {X Y : Type} [TopologicalSpace X] (p : X → Y)
          (D Ac A₀ A₁ : Set X) (U c : Set Y) (hDopen : IsOpen D)
          (hfront : frontier D=Ac∪A₀∪A₁)
          (hD : p '' D⊆U) (hc : p '' Ac⊆c) (hUc : Disjoint U c)
          (h₀ : p '' A₀⊆U) (h₁ : p '' A₁⊆U) :
          closure D∩p ⁻¹' U=D∪A₀∪A₁ := by
        have hfd : frontier D=closure D\D := by
          rw [frontier,hDopen.interior_eq]
        ext x
        constructor
        · rintro ⟨hx,hpx⟩
          by_cases hd : x∈D
          · exact Or.inl (Or.inl hd)
          · have hf : x∈frontier D := by rw [hfd];exact ⟨hx,hd⟩
            rw [hfront] at hf
            rcases hf with (hcx|h₀x)|h₁x
            · exact False.elim (Set.disjoint_left.mp hUc hpx (hc ⟨x,hcx,rfl⟩))
            · exact Or.inl (Or.inr h₀x)
            · exact Or.inr h₁x
        · intro hx
          rcases hx with (hd|h₀x)|h₁x
          · exact ⟨subset_closure hd,hD ⟨x,hd,rfl⟩⟩
          · have hf : x∈frontier D := by rw [hfront];exact Or.inl (Or.inr h₀x)
            exact ⟨frontier_subset_closure hf,h₀ ⟨x,h₀x,rfl⟩⟩
          · have hf : x∈frontier D := by rw [hfront];exact Or.inr h₁x
            exact ⟨frontier_subset_closure hf,h₁ ⟨x,h₁x,rfl⟩⟩
      have hAxisExchange {X : Type} (e : X ≃ X) (J : X → X) (hJ : Function.Involutive J)
          (α₀ α₁ ψ₀ ψ₁ : ℝ → X)
          (h₀ : e '' range α₀=range ψ₀) (h₁ : e '' range α₁=range ψ₁)
          (hψ : ∀t,J (ψ₀ t)=ψ₁ (-t)) :
          let F : X → X := fun z => e.symm (J (e z))
          F '' range α₀=range α₁ ∧ F '' range α₁=range α₀ := by
        intro F
        have hψ₁ (t : ℝ) : J (ψ₁ t)=ψ₀ (-t) := by
          have hh := congrArg J (hψ (-t))
          rw [hJ,neg_neg] at hh
          exact hh.symm
        have hmap (α β ψ χ : ℝ → X) (ha : e '' range α=range ψ)
            (hb : e '' range β=range χ) (hψχ : ∀t,J (ψ t)=χ (-t)) :
            F '' range α⊆range β := by
          rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          have hx : e (α t)∈range ψ := by rw [←ha];exact ⟨α t,mem_range_self t,rfl⟩
          obtain ⟨s,hs⟩ := hx
          have hy : J (e (α t))∈e '' range β := by
            rw [hb,←hs,hψχ]
            exact mem_range_self (-s)
          obtain ⟨y,hy,hye⟩ := hy
          change e.symm (J (e (α t)))∈range β
          rw [←hye,e.symm_apply_apply]
          exact hy
        have hF (x : X) : F (F x)=x := by
          change e.symm (J (e (e.symm (J (e x)))))=x
          rw [e.apply_symm_apply,hJ,e.symm_apply_apply]
        have hm₀ := hmap α₀ α₁ ψ₀ ψ₁ h₀ h₁ hψ
        have hm₁ := hmap α₁ α₀ ψ₁ ψ₀ h₁ h₀ hψ₁
        constructor
        · apply subset_antisymm hm₀
          intro x hx
          refine ⟨F x,hm₁ ⟨x,hx,rfl⟩,hF x⟩
        · apply subset_antisymm hm₁
          intro x hx
          refine ⟨F x,hm₀ ⟨x,hx,rfl⟩,hF x⟩
      have hBoundaryCircle {G E : Type} [Group G] [TopologicalSpace E]
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (hIsoG : ∀g : G,Isometry (fun z : H2 => @SMul.smul G H2 a.toSMul g z)) (D : Set H2) :
          letI := a
          let K := MulAction.stabilizer G D
          ∀bc : MulAction K ↥(closure D),
          (∀k : K,∀z : closure D,(@SMul.smul K ↥(closure D) bc.toSMul k z).val=
            @SMul.smul G H2 a.toSMul k.val z.val) →
          letI := bc
          let qcl : ↥(closure D) → Quotient (MulAction.orbitRel K ↥(closure D)) := Quotient.mk _
          ∀hqcl : IsQuotientCoveringMap qcl K,
          ∀α : C(ℝ,H2),∀hfront : range α⊆closure D,
          ∀T : ℝ,0<T →
          (∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T) →
          ∀δ : K,
          ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ.val (α t)=α (t+T)) ∨
            (∀t : ℝ,@SMul.smul G H2 a.toSMul δ.val⁻¹ (α t)=α (t+T))) →
          ∃hT2 : T2Space (Quotient (MulAction.orbitRel K ↥(closure D))),letI := hT2
          ∃f : C(Circle,Quotient (MulAction.orbitRel K ↥(closure D))),IsEmbedding f ∧
            (∀s : ℝ,qcl ⟨α s,hfront (mem_range_self s)⟩=f (Circle.exp (2*Real.pi*s/T))) ∧
            range f=qcl '' range (fun s : ℝ => (⟨α s,hfront (mem_range_self s)⟩ : closure D)) := by
        have hHausdorff {G P E : Type} [Group G] [MetricSpace P] [TopologicalSpace E] [MulAction G P]
            (q : P → E) (hq : IsQuotientCoveringMap q G)
            (hIso : ∀g : G,Isometry (fun z : P => g • z)) : T2Space E := by
          have hOrbitClosed (x : P) : IsClosed (MulAction.orbit G x) := by
            obtain ⟨U,hU,hDis⟩ := hq.disjoint x
            obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hU
            apply Metric.isClosed_of_pairwise_le_dist hr
            rintro u ⟨g,rfl⟩ v ⟨h,rfl⟩ huv
            by_contra hlarge
            have hsmall : dist (g • x) (h • x)<r := lt_of_not_ge hlarge
            have hd : dist ((h⁻¹*g) • x) x=dist (g • x) (h • x) := by
              rw [←(hIso h).dist_eq]
              simp only [mul_smul,smul_inv_smul]
            have hx : x∈U := mem_of_mem_nhds hU
            have hh : (h⁻¹*g) • x∈U := hBall (by simpa only [Metric.mem_ball,hd] using hsmall)
            have he := hDis (h⁻¹*g) ⟨(h⁻¹*g) • x,⟨x,hx,rfl⟩,hh⟩
            have hgh : g=h := (inv_mul_eq_one.mp he).symm
            exact huv (hgh ▸ rfl)
          rw [t2Space_iff_nhds]
          intro u v huv
          obtain ⟨x,rfl⟩ := hq.surjective u
          obtain ⟨y,rfl⟩ := hq.surjective v
          have hy : y∈(MulAction.orbit G x)ᶜ := by
            intro hh
            exact huv (hq.apply_eq_iff_mem_orbit.mpr hh).symm
          obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp (hOrbitClosed x).isOpen_compl y hy
          let U := q '' Metric.ball x (r/3)
          let V := q '' Metric.ball y (r/3)
          have hr3 : 0<r/3 := by positivity
          have hU : U∈𝓝 (q x) :=
            (hq.isOpenQuotientMap.isOpenMap _ Metric.isOpen_ball).mem_nhds ⟨x,Metric.mem_ball_self hr3,rfl⟩
          have hV : V∈𝓝 (q y) :=
            (hq.isOpenQuotientMap.isOpenMap _ Metric.isOpen_ball).mem_nhds ⟨y,Metric.mem_ball_self hr3,rfl⟩
          refine ⟨U,hU,V,hV,Set.disjoint_left.mpr ?_⟩
          rintro z ⟨a,ha,hea⟩ ⟨b,hb,heb⟩
          obtain ⟨g,hg⟩ := hq.apply_eq_iff_mem_orbit.mp (hea.trans heb.symm)
          have hpoint : g⁻¹ • a=b := by
            rw [←hg,inv_smul_smul]
          have hdist : dist (g⁻¹ • x) y<r := by
            have htri := dist_triangle (g⁻¹ • x) (g⁻¹ • a) y
            rw [(hIso g⁻¹).dist_eq,hpoint] at htri
            have ha' : dist x a<r/3 := by simpa only [Metric.mem_ball,dist_comm] using ha
            have hb' : dist b y<r/3 := hb
            linarith
          have hout : g⁻¹ • x∉MulAction.orbit G x := hBall (by simpa only [Metric.mem_ball] using hdist)
          exact hout ⟨g⁻¹,rfl⟩
        have hFibre {K X E Q : Type} [Group K] [MulAction K X]
            [TopologicalSpace X] [TopologicalSpace Q]
            (q : X → Q) (hq : IsQuotientCoveringMap q K) (p : X → E)
            (hp : ∀k : K,∀x : X,p (k • x)=p x)
            (α : ℝ → X) (T : ℝ)
            (hpf : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
            (δ : K) (hs : ∀t : ℝ,δ • α t=α (t+T)) :
            ∀s t : ℝ,q (α s)=q (α t) ↔ ∃n : ℤ,s=t+n*T := by
          have hClock {G P : Type} [Group G] [MulAction G P] (δ : G) (α : ℝ → P) (T : ℝ)
              (hs : ∀t : ℝ,δ • α t=α (t+T)) :
              ∀n : ℤ,∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
            have hNat (δ : G) (T : ℝ) (hs : ∀t : ℝ,δ • α t=α (t+T)) :
                ∀n : ℕ,∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
              intro n
              induction n with
              | zero => intro t;simp
              | succ n ih =>
                  intro t
                  rw [pow_succ,mul_smul,hs,ih]
                  congr 1
                  push_cast
                  ring
            have hinv (t : ℝ) : δ⁻¹ • α t=α (t+(-T)) := by
              have hh := congrArg (fun z : P => δ⁻¹ • z) (hs (t-T))
              have hh' : δ⁻¹ • α t=α (t-T) := by simpa only [sub_add_cancel,inv_smul_smul] using hh.symm
              simpa only [sub_eq_add_neg] using hh'
            intro n t
            cases n with
            | ofNat n =>
                change δ^(n:ℤ) • α t=α (t+(n:ℝ)*T)
                simpa only [zpow_natCast] using hNat δ T hs n t
            | negSucc n =>
                have hh := hNat δ⁻¹ (-T) hinv (n+1) t
                simpa only [zpow_negSucc,inv_pow,Int.cast_negSucc,Nat.cast_add,Nat.cast_one,
                  mul_neg,neg_mul] using hh
          intro s t
          constructor
          · intro hst
            obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp hst
            apply (hpf s t).mp
            rw [←hk,hp]
          · rintro ⟨n,hn⟩
            apply hq.apply_eq_iff_mem_orbit.mpr
            refine ⟨δ^n,?_⟩
            change δ^n • α t=α s
            rw [hClock δ α T hs n t,hn]
        have hCircle {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
            (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
            ∃f : C(Circle,E),IsEmbedding f ∧
              (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
              range f=p '' range α := by
          classical
          let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
          have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
          let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
          have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
            obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
            apply (hfibre _ _).mpr
            refine ⟨k,?_⟩
            rw [hk]
            field_simp
          have hψ : Continuous ψ := by
            apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
            have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
            rw [heq]
            fun_prop
          let f : C(Circle,E) := ⟨ψ,hψ⟩
          have hfinj : Function.Injective f := by
            intro z w hzw
            obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
            have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
              have hπ : (2*Real.pi)≠0 := by positivity
              have hT' : T≠0 := hT.ne'
              field_simp at hk
              nlinarith
            rw [←hθ z,←hθ w]
            exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
          have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
            change _=ψ _
            rw [hfac]
            congr 2
            field_simp
          refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
          apply Subset.antisymm
          · rintro y ⟨z,rfl⟩
            exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
          · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
            exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
        letI := a
        intro K bc hCompat
        letI := bc
        intro qcl hqcl α hfront T hT hpf δ hs
        have hIsoCl (k : K) : Isometry (fun z : closure D => k • z) := by
          apply Isometry.of_dist_eq
          intro z w
          change dist ((@SMul.smul K ↥(closure D) bc.toSMul k z).val)
            ((@SMul.smul K ↥(closure D) bc.toSMul k w).val)=dist z.val w.val
          rw [hCompat,hCompat]
          exact (hIsoG k.val).dist_eq z.val w.val
        let hT2 := hHausdorff qcl hqcl hIsoCl
        letI := hT2
        let αcl : C(ℝ,↥(closure D)) := ⟨fun t => ⟨α t,hfront (mem_range_self t)⟩,α.continuous.subtype_mk _⟩
        let pcl : ↥(closure D) → E := fun z => p z.val
        have hpcl (k : K) (z : closure D) : pcl (k • z)=pcl z := by
          change p ((@SMul.smul K ↥(closure D) bc.toSMul k z).val)=p z.val
          rw [hCompat]
          exact hq.map_smul k.val
        have hpfcl : ∀s t : ℝ,pcl (αcl s)=pcl (αcl t) ↔ ∃n : ℤ,s=t+n*T := hpf
        have hShift : ∃δ' : K,∀t : ℝ,δ' • αcl t=αcl (t+T) := by
          rcases hs with hs|hs
          · refine ⟨δ,?_⟩
            intro t
            apply Subtype.ext
            change (@SMul.smul K ↥(closure D) bc.toSMul δ (αcl t)).val=α (t+T)
            rw [hCompat]
            exact hs t
          · refine ⟨δ⁻¹,?_⟩
            intro t
            apply Subtype.ext
            change (@SMul.smul K ↥(closure D) bc.toSMul δ⁻¹ (αcl t)).val=α (t+T)
            rw [hCompat]
            exact hs t
        obtain ⟨δ',hδ'⟩ := hShift
        have hqf := hFibre qcl hqcl pcl hpcl αcl T hpfcl δ' hδ'
        obtain ⟨f,hf,hparam,hrange⟩ := hCircle ⟨qcl,hqcl.continuous⟩ αcl T hT hqf
        exact ⟨hT2,f,hf,hparam,hrange⟩
      have hDistinctBoundaryAxes {P E G : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E] [Group G]
          (a : MulAction G P) (p : P → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (hIso : ∀g : G,Isometry (fun z : P => @SMul.smul G P a.toSMul g z))
          (hproj : ∀g : G,∀z : P,p (@SMul.smul G P a.toSMul g z)=p z)
          (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
          (T : ℝ) (hT : 0<T)
          (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
          (himage : p '' range α=p '' range β) (K : Subgroup G)
          (hneq : ∀k : K,(fun z : P => @SMul.smul G P a.toSMul k.val z) '' range α≠range β) :
          ∀k : K,∀s t : ℝ,@SMul.smul G P a.toSMul k.val (α s)≠β t := by
        have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
            (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
            (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
            (himage : p '' range β⊆p '' range α)
            (hmeet : (range α∩range β).Nonempty) : range β=range α := by
          have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
              (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
            have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                ∃f : C(Circle,E),IsEmbedding f ∧
                  (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                  range f=p '' range α := by
              classical
              let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
              have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
              let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
              have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                apply (hfibre _ _).mpr
                refine ⟨k,?_⟩
                rw [hk]
                field_simp
              have hψ : Continuous ψ := by
                apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                rw [heq]
                fun_prop
              let f : C(Circle,E) := ⟨ψ,hψ⟩
              have hfinj : Function.Injective f := by
                intro z w hzw
                obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                  have hπ : (2*Real.pi)≠0 := by positivity
                  have hT' : T≠0 := hT.ne'
                  field_simp at hk
                  nlinarith
                rw [←hθ z,←hθ w]
                exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
              have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                change _=ψ _
                rw [hfac]
                congr 2
                field_simp
              refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
              apply Subset.antisymm
              · rintro y ⟨z,rfl⟩
                exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
              · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
            obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
            change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
            let e : Circle ≃ₜ range f := hf.toHomeomorph
            let g : C(ℝ,Circle) :=
              ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
            let θ₀ := 2*Real.pi*s₀/T
            have hbase : Circle.exp θ₀=g t₀ := by
              apply e.injective
              apply Subtype.ext
              change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
              rw [e.apply_symm_apply]
              change f (Circle.exp θ₀)=p (β t₀)
              rw [←hparam,hmeet]
            obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
            have hL0 : L t₀=θ₀ := hL.1
            have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
            let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
            have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
              intro t
              change p (α (T*L t/(2*Real.pi)))=_
              rw [hparam]
              have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
              rw [harg,hLe]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
            have hℓbase : ℓ t₀=β t₀ := by
              change α (T*L t₀/(2*Real.pi))=β t₀
              rw [hL0]
              have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
              rw [harg,hmeet]
            have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
              (funext hℓproj) t₀ hℓbase
            rintro y ⟨t,rfl⟩
            exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
          have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
              range β=range α := by
            let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
            let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
            have hfac (t : ℝ) : α (f t)=β t :=
              congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
            have hf : Isometry f := by
              apply isometry_iff_dist_eq.mpr
              intro s t
              rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
            let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
            have hLin : Function.Injective A.toAffineMap.linear :=
              A.toAffineMap.linear_injective_iff.mpr hf.injective
            have hSur : Function.Surjective A.toAffineMap.linear :=
              LinearMap.surjective_of_injective hLin
            have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
            apply Subset.antisymm hsub
            rintro y ⟨t,rfl⟩
            obtain ⟨s,hs⟩ := hfsur t
            exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
          obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
          have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
            s t (hs.trans ht.symm)
          exact hLine α β hα hβ hsub
        letI := a
        intro k s t hst
        let γ : ℝ → P := fun u => k.val • α u
        have hγ : Isometry γ := (hIso k.val).comp hα
        have hγfibre : ∀s t : ℝ,p (γ s)=p (γ t) ↔ ∃n : ℤ,s=t+n*T := by
          intro s t
          change p (@SMul.smul G P a.toSMul k.val (α s))=p (@SMul.smul G P a.toSMul k.val (α t)) ↔ ∃n : ℤ,s=t+n*T
          rw [hproj,hproj]
          exact hfibre s t
        have hγimage : p '' range β⊆p '' range γ := by
          rintro _ ⟨_,⟨u,rfl⟩,rfl⟩
          have hh : p (β u)∈p '' range α := himage ▸ ⟨β u,mem_range_self u,rfl⟩
          obtain ⟨_,⟨v,rfl⟩,hv⟩ := hh
          exact ⟨γ v,mem_range_self v,(hproj k.val (α v)).trans hv⟩
        have hr := hMeet p hq.isCoveringMap γ β hγ hβ T hT hγfibre hγimage
          ⟨β t,⟨s,hst⟩,mem_range_self t⟩
        apply hneq k
        exact (Set.range_comp (fun z : P => k.val • z) α).symm.trans hr.symm
      have hOpenQuotientEmbedding {K X Y B C : Type} [Group K]
          [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B] [TopologicalSpace C]
          [MulAction K X] [MulAction K Y]
          (q : X → B) (r : Y → C) (hq : IsQuotientCoveringMap q K) (hr : IsQuotientCoveringMap r K)
          (ι : X → Y) (hi : IsOpenEmbedding ι) (hequiv : ∀k : K,∀x : X,ι (k • x)=k • ι x) :
          ∃j : B → C,IsOpenEmbedding j ∧ ∀x,j (q x)=r (ι x) := by
        classical
        choose s hs using hq.surjective
        let j : B → C := fun b => r (ι (s b))
        have hfac (x : X) : j (q x)=r (ι x) := by
          obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp (hs (q x))
          change r (ι (s (q x)))=r (ι x)
          rw [←hk,hequiv,hr.map_smul]
        have hcont : Continuous j := by
          apply hq.toIsQuotientMap.continuous_iff.mpr
          have heq : j ∘ q=r ∘ ι := funext hfac
          rw [heq]
          exact hr.continuous.comp hi.continuous
        have hinj : Function.Injective j := by
          intro b c hbc
          obtain ⟨k,hk⟩ := hr.apply_eq_iff_mem_orbit.mp hbc
          have he : k • s c=s b := hi.injective ((hequiv k (s c)).trans hk)
          calc
            b=q (s b) := (hs b).symm
            _=q (k • s c) := by rw [he]
            _=q (s c) := hq.map_smul k
            _=c := hs c
        have hopen : IsOpenMap j := by
          intro U hU
          have hImage : j '' U=r '' (ι '' (q ⁻¹' U)) := by
            ext z
            constructor
            · rintro ⟨b,hb,rfl⟩
              refine ⟨ι (s b),⟨s b,?_,rfl⟩,rfl⟩
              change q (s b)∈U
              rw [hs]
              exact hb
            · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
              exact ⟨q x,hx,hfac x⟩
          rw [hImage]
          exact hr.isOpenQuotientMap.isOpenMap _ (hi.isOpenMap _ (hU.preimage hq.continuous))
        exact ⟨j,IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen,hfac⟩
      have hOpenClosureInclusion {P : Type} [TopologicalSpace P] (D : Set P) (hD : IsOpen D) :
          let ι : D → ↥(closure D) := fun z => ⟨z.val,subset_closure z.property⟩
          IsOpenEmbedding ι := by
        intro ι
        have hc : Continuous ι := continuous_subtype_val.subtype_mk _
        have hi : Function.Injective ι := by
          intro z w h
          exact Subtype.ext (congrArg (fun v : closure D => v.val) h)
        have ho : IsOpenMap ι := by
          intro U hU
          have heq : ι '' U=Subtype.val ⁻¹' ((Subtype.val : D → P) '' U) := by
            ext z
            constructor
            · rintro ⟨w,hw,rfl⟩
              exact ⟨w,hw,rfl⟩
            · rintro ⟨w,hw,he⟩
              exact ⟨w,hw,Subtype.ext he⟩
          rw [heq]
          exact (hD.isOpenEmbedding_subtypeVal.isOpenMap U hU).preimage continuous_subtype_val
        exact IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi ho
      have hClosureQuotient {E G : Type} [TopologicalSpace E] [Group G]
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (D : Set H2) :
          letI := a
          let K := MulAction.stabilizer G D
          ∀e : H2 ≃ᵢ H2,∀ρ : K →* SL(2,ℝ),
          (∀k : K,∀z : H2,e (@SMul.smul G H2 a.toSMul k.val z)=ρ k • e z) →
          ∀J : SL(2,ℝ),J∈Subgroup.normalizer (ρ.range:Set SL(2,ℝ)) →
          (∀z : H2,J • (J • z)=z) →
          (fun z : H2 => e.symm (J • e z)) '' D=D →
          ∃bc : MulAction K ↥(closure D),letI := bc
        (∀k : K,∀z : closure D,(@SMul.smul K ↥(closure D) bc.toSMul k z).val=
          @SMul.smul G H2 a.toSMul k.val z.val) ∧
          ∃hqcl : IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel K ↥(closure D))) K,
          ∃τcl : Quotient (MulAction.orbitRel K ↥(closure D)) ≃ₜ Quotient (MulAction.orbitRel K ↥(closure D)),
            Function.Involutive τcl ∧
            ∀z w : closure D,w.val=e.symm (J • e z.val) →
              τcl (Quotient.mk _ z)=Quotient.mk _ w := by
        have hClosureAction {P G : Type} [TopologicalSpace P] [Group G] [MulAction G P]
            [ContinuousConstSMul G P] (D : Set P) :
            let K := MulAction.stabilizer G D
            ∃b : MulAction K ↥(closure D),letI := b
              ∀k : K,∀z : closure D,(k • z).val=k.val • z.val := by
          intro K
          have hpres (k : K) : (fun z : P => k.val • z) '' D=D :=
            MulAction.mem_stabilizer_iff.mp k.property
          have hcl (k : K) : (fun z : P => k.val • z) '' closure D=closure D := by
            calc
              (fun z : P => k.val • z) '' closure D=closure ((fun z : P => k.val • z) '' D) :=
                (Homeomorph.smul k.val).image_closure D
              _=closure D := by rw [hpres]
          have hm (k : K) (z : closure D) : k.val • z.val∈closure D := by
            have hh : k.val • z.val∈(fun z : P => k.val • z) '' closure D := ⟨z.val,z.property,rfl⟩
            exact (Set.ext_iff.mp (hcl k) (k.val • z.val)).mp hh
          let b : MulAction K ↥(closure D) := {
            smul := fun k z => ⟨k.val • z.val,hm k z⟩
            one_smul := fun z => Subtype.ext (one_smul G z.val)
            mul_smul := fun k l z => Subtype.ext (mul_smul k.val l.val z.val) }
          exact ⟨b,fun _ _ => rfl⟩
        have hCarrierCover {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
            (a : MulAction G P) (p : P → E) (hq : letI := a;IsQuotientCoveringMap p G)
            (K : Subgroup G) (S : Set P) (b : MulAction K S)
            (hcompat : letI := a;letI := b;∀k : K,∀z : S,(k • z).val=k.val • z.val) :
            letI := b
            IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel K S)) K := by
          letI := a
          letI := b
          letI : ContinuousConstSMul G P := hq.toContinuousConstSMul
          have hcont (k : K) : Continuous (fun z : S => k • z) := by
            apply Continuous.subtype_mk
            change Continuous (fun z : S => (@SMul.smul K S b.toSMul k z).val)
            have heq : (fun z : S => (@SMul.smul K S b.toSMul k z).val)=(fun z : S => @SMul.smul G P a.toSMul k.val z.val) := funext (hcompat k)
            rw [heq]
            exact (continuous_const_smul k.val).comp continuous_subtype_val
          letI : ContinuousConstSMul K S := ⟨hcont⟩
          refine { toIsQuotientMap := isQuotientMap_quotient_mk'
                   apply_eq_iff_mem_orbit := ?_
                   disjoint := ?_ }
          · intro z w
            exact Quotient.eq''
          · intro z
            obtain ⟨U,hU,hd⟩ := hq.disjoint z.val
            let V : Set S := Subtype.val ⁻¹' U
            have hV : V∈𝓝 z := continuous_subtype_val.continuousAt.preimage_mem_nhds hU
            refine ⟨V,hV,?_⟩
            intro k hk
            apply Subtype.ext
            change k.val=1
            apply hd k.val
            obtain ⟨w,⟨v,hv,rfl⟩,hw⟩ := hk
            refine ⟨(k • v).val,?_,hw⟩
            exact ⟨v.val,hv,(hcompat k v).symm⟩
        have hDescent {K Q : Type} [Group K] [TopologicalSpace Q] [MulAction K H2]
            (C : Set H2) (b : MulAction K C) (q : C → Q)
            (hq : letI := b;IsQuotientCoveringMap q K)
            (hcompat : letI := b;∀k : K,∀z : C,(k • z).val=k • z.val)
            (e : H2 ≃ᵢ H2) (ρ : K →* SL(2,ℝ))
            (hρ : ∀k z,e (k • z)=ρ k • e z)
            (j : SL(2,ℝ)) (hnorm : j∈Subgroup.normalizer (ρ.range:Set SL(2,ℝ)))
            (hinv : ∀z : H2,j • (j • z)=z)
            (hpres : (fun z : H2 => e.symm (j • e z)) '' C=C) :
            ∃τ : Q ≃ₜ Q, Function.Involutive τ ∧
              ∀z w : C,w.val=e.symm (j • e z.val) → τ (q z)=q w := by
          letI := b
          let f : H2 → H2 := fun z => e.symm (j • e z)
          have hf (z : H2) : f (f z)=z := by
            dsimp only [f]
            rw [e.apply_symm_apply,hinv,e.symm_apply_apply]
          have hmem (z : C) : f z.val∈C := by
            have h : f z.val∈(fun z : H2 => e.symm (j • e z)) '' C := ⟨z.val,z.property,rfl⟩
            rw [hpres] at h
            exact h
          let lift : C ≃ₜ C := {
            toFun := fun z => ⟨f z.val,hmem z⟩
            invFun := fun z => ⟨f z.val,hmem z⟩
            left_inv := fun z => Subtype.ext (hf z.val)
            right_inv := fun z => Subtype.ext (hf z.val)
            continuous_toFun := by
              apply Continuous.subtype_mk
              exact e.symm.continuous.comp ((IsometryEquiv.constSMul j).continuous.comp
                (e.continuous.comp continuous_subtype_val))
            continuous_invFun := by
              apply Continuous.subtype_mk
              exact e.symm.continuous.comp ((IsometryEquiv.constSMul j).continuous.comp
                (e.continuous.comp continuous_subtype_val)) }
          have hFib (z w : C) (hzw : q z=q w) : q (lift z)=q (lift w) := by
            obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp hzw
            have hkg : j*ρ k*j⁻¹∈ρ.range := (Subgroup.mem_normalizer_iff.mp hnorm (ρ k)).mp ⟨k,rfl⟩
            obtain ⟨k',hk'⟩ := hkg
            apply hq.apply_eq_iff_mem_orbit.mpr
            refine ⟨k',?_⟩
            apply Subtype.ext
            rw [hcompat]
            apply e.injective
            change e (k' • f w.val)=e (f z.val)
            rw [hρ,hk']
            dsimp only [f]
            rw [e.apply_symm_apply,e.apply_symm_apply,mul_smul,mul_smul,inv_smul_smul]
            have hw : z.val=k • w.val := by
              have hh := congrArg Subtype.val hk
              simpa only [hcompat] using hh.symm
            rw [hw,hρ]
          have hSquare (z : C) : q (lift (lift z))=q z := by
            congr 1
            exact Subtype.ext (hf z.val)
          obtain ⟨τ,hτ,hτinv⟩ := pants_actual_quotient_involution_descends q hq.toIsQuotientMap lift hFib hSquare
          refine ⟨τ,hτinv,?_⟩
          intro z w hw
          rw [hτ]
          congr 1
          exact Subtype.ext hw.symm
        letI := a
        intro K e ρ hρ J hNorm hInv hPres
        letI : ContinuousConstSMul G H2 := hq.toContinuousConstSMul
        obtain ⟨bc,hbc⟩ := hClosureAction (G:=G) D
        letI := bc
        have hCover := hCarrierCover a p hq K (closure D) bc hbc
        let qcl : ↥(closure D) → Quotient (MulAction.orbitRel K ↥(closure D)) := Quotient.mk _
        let F : H2 ≃ᵢ H2 := (e.trans (IsometryEquiv.constSMul J)).trans e.symm
        have hFpres : F '' D=D := hPres
        have hClPres : F '' closure D=closure D := by
          calc
            F '' closure D=closure (F '' D) := F.toHomeomorph.image_closure D
            _=closure D := by rw [hFpres]
        have hClPres' : (fun z : H2 => e.symm (J • e z)) '' closure D=closure D := hClPres
        have hCompat : ∀k : K,∀z : closure D,(k • z).val=k • z.val := hbc
        have hRho : ∀k : K,∀z : H2,e (k • z)=ρ k • e z := hρ
        obtain ⟨τ,hτ,hLift⟩ := hDescent (closure D) bc qcl hCover hCompat e ρ hRho J hNorm hInv hClPres'
        exact ⟨bc,hbc,hCover,τ,hτ,hLift⟩
      have hEqualSignedClocks (d T L₀ L₁ : ℝ) (h₀ : L₀=T ∨ L₀=-T) (h₁ : L₁=T ∨ L₁=-T)
          (C : Set H2) (hopen : IsOpen C) (hcenter : UpperHalfPlane.I∈C)
          (α : ℝ → H2) (hα : Isometry α) (hfront : range α⊆frontier C)
          (Lc ε : ℝ) (hLc : Lc≠0) (hε : 0 < ε) :
          let D : ℝ → SL(2,ℝ) := fun s =>
            ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          let P := fun L : ℝ => D (-d/2)*R*D L*R⁻¹*D (d/2)
          let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
          (∀z : H2,ε≤dist z (((Q L₁)⁻¹*P L₀) • z)) →
          (∀t : ℝ,((Q L₁)⁻¹*P L₀) • α t=α (t+Lc)) → L₁=L₀ := by
        have hNoDirect (C : Set H2) (hopen : IsOpen C) (hcenter : UpperHalfPlane.I∈C)
            (a b : SL(2,ℝ)) (α : ℝ → H2) (hα : Isometry α)
            (hfront : range α⊆frontier C) (L ε : ℝ) (hL : L≠0) (hε : 0 < ε)
            (hdisp : ∀z : H2,ε≤dist z ((b⁻¹*a) • z))
            (hclock : ∀t : ℝ,(b⁻¹*a) • α t=α (t+L)) :
            let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
            ¬(J*a*J⁻¹=b ∧ J*b*J⁻¹=a) := by
          have hDirect (a b j : SL(2,ℝ)) (α : ℝ → H2) (hα : Isometry α)
              (L ε : ℝ) (hL : L≠0) (hε : 0 < ε)
              (hdisp : ∀z : H2,ε ≤ dist z ((b⁻¹*a) • z))
              (hclock : ∀t : ℝ,(b⁻¹*a) • α t=α (t+L))
              (hex : j*a*j⁻¹=b ∧ j*b*j⁻¹=a) :
              (fun z : H2 => j • z) '' range α=range α := by
            let c := b⁻¹*a
            have hcclock (t : ℝ) : c • α t=α (t+L) := hclock t
            have hinvclock (t : ℝ) : c⁻¹ • α t=α (t-L) := by
              have h := congrArg (fun z : H2 => c⁻¹ • z) (hcclock (t-L))
              simpa only [inv_smul_smul,sub_add_cancel] using h.symm
            have hpres (k : SL(2,ℝ)) (hkc : k*c*k⁻¹=c) :
                (fun z : H2 => k • z) '' range α=range α := by
              have hcomm : c*k=k*c := by
                calc
                  c*k=(k*c*k⁻¹)*k := by rw [hkc]
                  _=k*c := by group
              let β : ℝ → H2 := fun t => k • α t
              have hβ : Isometry β := (IsometryEquiv.constSMul k).isometry.comp hα
              have hβclock (t : ℝ) : c • β t=β (t+L) := by
                change c • (k • α t)=k • α (t+L)
                rw [←mul_smul,hcomm,mul_smul,hcclock]
              have hr := actual_h2_translated_isometric_lines_same_range
                (IsometryEquiv.constSMul c) α β hα hβ ε hε hdisp L L hL hL hcclock hβclock
              simpa only [β,←range_comp',Function.comp_def] using hr.symm
            rcases hex with ⟨ha,hb⟩
            have hconj : j*c*j⁻¹=c⁻¹ := by
              calc
                j*c*j⁻¹=(j*b*j⁻¹)⁻¹*(j*a*j⁻¹) := by dsimp only [c];group
                _=c⁻¹ := by rw [ha,hb];dsimp only [c];group
            have hconji : j*c⁻¹*j⁻¹=c := by
              have h := congrArg (fun x : SL(2,ℝ) => x⁻¹) hconj
              simpa only [_root_.mul_inv_rev,inv_inv,mul_assoc] using h
            have hrel : c*j=j*c⁻¹ := by
              calc
                c*j=(j*c⁻¹*j⁻¹)*j := by rw [hconji]
                _=j*c⁻¹ := by group
            let β : ℝ → H2 := fun t => j • α t
            have hβ : Isometry β := (IsometryEquiv.constSMul j).isometry.comp hα
            have hβclock (t : ℝ) : c • β t=β (t+(-L)) := by
              change c • (j • α t)=j • α (t+(-L))
              rw [←mul_smul,hrel,mul_smul,hinvclock]
              rfl
            have hr := actual_h2_translated_isometric_lines_same_range
              (IsometryEquiv.constSMul c) α β hα hβ ε hε hdisp L (-L) hL (neg_ne_zero.mpr hL) hcclock hβclock
            simpa only [β,←range_comp',Function.comp_def] using hr.symm
          have hNoStable (C : Set H2) (hopen : IsOpen C) (hcenter : UpperHalfPlane.I∈C)
              (α : ℝ → H2) (hα : Isometry α) (hfront : range α⊆frontier C) :
              let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
              (fun z : H2 => J • z) '' range α≠range α := by
            have hAxisFixed (g : H2 ≃ᵢ H2) (hinv : Function.Involutive g)
                (α : ℝ → H2) (hα : Isometry α) (hpres : g '' range α=range α) :
                ∃t : ℝ,g (α t)=α t := by
              classical
              have hReal (f : ℝ → ℝ) (hf : Isometry f) :
                  (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
                let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
                let k : ℝ := A.toAffineMap.linear 1
                have hfac (t : ℝ) : f t=t*k+f 0 := by
                  have h := A.toAffineMap.map_vadd 0 t
                  have hlin : A.toAffineMap.linear t=t*k := by
                    have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
                    simpa [k,smul_eq_mul] using hh
                  change f (t+0)=A.toAffineMap.linear t+f 0 at h
                  simpa only [add_zero,hlin] using h
                have hk : |k|=1 := by
                  have h := hf.dist_eq 1 0
                  rw [hfac 1,hfac 0] at h
                  simpa [Real.dist_eq] using h
                rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
                · left;intro t;rw [hfac,he];ring
                · right;intro t;rw [hfac,he];ring
              have hExists (t : ℝ) : ∃s : ℝ,α s=g (α t) := by
                have hmem : g (α t)∈range α := hpres ▸ ⟨α t,mem_range_self t,rfl⟩
                exact hmem
              let f : ℝ → ℝ := fun t => Classical.choose (hExists t)
              have hf (t : ℝ) : α (f t)=g (α t) := Classical.choose_spec (hExists t)
              have hfi : Isometry f := by
                apply Isometry.of_dist_eq
                intro s t
                rw [←hα.dist_eq,hf,hf,g.dist_eq,hα.dist_eq]
              have hff (t : ℝ) : f (f t)=t := by
                apply hα.injective
                rw [hf,hf,hinv]
              rcases hReal f hfi with hplus|hminus
              · have hz : f 0=0 := by
                  have h := hff 0
                  rw [hplus] at h
                  linarith
                refine ⟨0,?_⟩
                rw [←hf,hz]
              · refine ⟨f 0/2,?_⟩
                rw [←hf,hminus]
                congr 1;ring
            intro J hpres
            obtain ⟨hinv,hfixed⟩ := hyperbolic_normalized_half_turn
            obtain ⟨t,ht⟩ := hAxisFixed (IsometryEquiv.constSMul J) hinv α hα hpres
            have hI : α t=UpperHalfPlane.I := (hfixed (α t)).mp ht
            have hIf : UpperHalfPlane.I∈frontier C := hI ▸ hfront (mem_range_self t)
            have hdis : Disjoint C (frontier C) := by
              rw [frontier,hopen.interior_eq]
              exact disjoint_sdiff_right
            exact Set.disjoint_left.mp hdis hcenter hIf
          intro J hEx
          exact hNoStable C hopen hcenter α hα hfront (hDirect a b J α hα L ε hL hε hdisp hclock hEx)
        intro D R P Q hdisp hclock
        have hRel : L₁=L₀ ∨ L₁=-L₀ := by
          rcases h₀ with h0|h0 <;> rcases h₁ with h1|h1 <;> simp [h0,h1]
        rcases hRel with hRel|hRel
        · exact hRel
        · exfalso
          have hEx := actual_normalized_equal_boundary_generator_exchange d L₀
          have hEx' :
              let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
              J*P L₀*J⁻¹=Q L₁ ∧ J*Q L₁*J⁻¹=P L₀ := by
            rw [hRel]
            exact hEx
          exact hNoDirect C hopen hcenter (P L₀) (Q L₁) α hα hfront Lc ε hLc hε hdisp hclock hEx'
      have hLocalMetric {Q : Type} [MetricSpace Q] (C : Set H2)
          (q : C → Q) (hq : IsCoveringMap q) (hs : Function.Surjective q)
          (hm : ∀z : C,∃U : Set C,IsOpen U ∧ z∈U ∧ ∀y∈U,∀w∈U,dist (q y) (q w)=dist y w)
          (e : H2 ≃ᵢ H2) (J : SL(2,ℝ))
          (hi : ∀z : H2,J • (J • z)=z)
          (hp : (fun z : H2 => e.symm (J • e z)) '' C=C)
          (τ : Q ≃ₜ Q)
          (hd : ∀z w : C,w.val=e.symm (J • e z.val) → τ (q z)=q w) :
          ∀x : Q,∃U : Set Q,IsOpen U ∧ x∈U ∧ ∀y∈U,∀z∈U,dist (τ y) (τ z)=dist y z := by
        let f : H2 ≃ᵢ H2 := (e.trans (IsometryEquiv.constSMul J)).trans e.symm
        have hf (z : H2) : f (f z)=z := by
          change e.symm (J • e (e.symm (J • e z)))=z
          rw [e.apply_symm_apply,hi,e.symm_apply_apply]
        have hmem (z : C) : f z.val∈C := by
          have hh : f z.val∈(fun z : H2 => e.symm (J • e z)) '' C := ⟨z.val,z.property,rfl⟩
          exact (Set.ext_iff.mp hp (f z.val)).mp hh
        let j : C ≃ᵢ C := {
          toFun := fun z => ⟨f z.val,hmem z⟩
          invFun := fun z => ⟨f z.val,hmem z⟩
          left_inv := fun z => Subtype.ext (hf z.val)
          right_inv := fun z => Subtype.ext (hf z.val)
          isometry_toFun := by
            intro y z
            exact f.isometry y.val z.val }
        have hdesc (z : C) : τ (q z)=q (j z) := hd z (j z) rfl
        exact actual_pants_cover_isometry_descends_locally_isometrically q hq hs hm j τ hdesc
      have hSignedMarking {K : Type} [Group K] (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ)
          (ρ : K →* SL(2,ℝ)) (d T L₀ L₁ : ℝ)
          (h₀ : L₀=T ∨ L₀=-T) (h₁ : L₁=T ∨ L₁=-T) :
          let D : ℝ → SL(2,ℝ) := fun s =>
            ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          let P := fun L : ℝ => D (-d/2)*R*D L*R⁻¹*D (d/2)
          let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
          ρ (B (FreeGroup.of 0)).unop=P L₀ → ρ (B (FreeGroup.of 1)).unop=Q L₁ →
          ∃E : FreeGroup Bool ≃* K,ρ (E (FreeGroup.of false))=P L₀ ∧
            ρ (E (FreeGroup.of true))=Q (-L₀) := by
        have hBasis {ι K : Type} [Group K] (B : FreeGroup ι ≃* Kᵐᵒᵖ) (s : ι → Bool) :
            ∃E : FreeGroup ι ≃* K,∀i,
              E (FreeGroup.of i)=if s i then (B (FreeGroup.of i)).unop else ((B (FreeGroup.of i)).unop)⁻¹ := by
          let signFlip : FreeGroup ι →* FreeGroup ι := FreeGroup.lift
            (fun i => if s i then (FreeGroup.of i)⁻¹ else FreeGroup.of i)
          have hsignFlipsignFlip : signFlip.comp signFlip=MonoidHom.id (FreeGroup ι) := by
            apply FreeGroup.ext_hom
            intro i
            cases h : s i <;> simp [signFlip,h]
          have hinv (w : FreeGroup ι) : signFlip (signFlip w)=w := by
            exact DFunLike.congr_fun hsignFlipsignFlip w
          let A : FreeGroup ι ≃* FreeGroup ι := {
            toFun := signFlip
            invFun := signFlip
            left_inv := hinv
            right_inv := hinv
            map_mul' := signFlip.map_mul }
          let E : FreeGroup ι ≃* K := A.trans (B.trans (MulEquiv.inv' K).symm)
          refine ⟨E,?_⟩
          intro i
          cases h : s i <;>
            simp [E,A,signFlip,h,MulEquiv.inv']
        have hQinverse (d : ℝ) :
            let D : ℝ → SL(2,ℝ) := fun s =>
              ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
            let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
            ∀L : ℝ,Q (-L)=(Q L)⁻¹ := by
          intro D R Q
          have hDadd (s t : ℝ) : D s*D t=D (s+t) := by
            apply Subtype.ext
            change (D s).val*(D t).val=(D (s+t)).val
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [D,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,add_div,neg_add,mul_comm]
          have hDzero : D 0=1 := by
            apply Subtype.ext
            change (D 0).val=(1 : Matrix (Fin 2) (Fin 2) ℝ)
            ext i j
            fin_cases i <;> fin_cases j <;> simp [D]
          have hDinv (s : ℝ) : (D s)⁻¹=D (-s) := by
            apply inv_eq_of_mul_eq_one_right
            rw [hDadd,add_neg_cancel,hDzero]
          intro L
          dsimp only [Q]
          simp only [_root_.mul_inv_rev,hDinv,inv_inv,neg_div,neg_neg]
          group
        intro D R P Q hρ₀ hρ₁
        have hBool (E₀ : FreeGroup (Fin 2) ≃* K)
            (hf : ρ (E₀ (FreeGroup.of 0))=P L₀) (ht : ρ (E₀ (FreeGroup.of 1))=Q (-L₀)) :
            ∃E : FreeGroup Bool ≃* K,ρ (E (FreeGroup.of false))=P L₀ ∧
              ρ (E (FreeGroup.of true))=Q (-L₀) := by
          refine ⟨(FreeGroup.freeGroupCongr finTwoEquiv.symm).trans E₀,?_,?_⟩
          · change ρ (E₀ (FreeGroup.of 0))=P L₀
            exact hf
          · change ρ (E₀ (FreeGroup.of 1))=Q (-L₀)
            exact ht
        have hRel : L₁=L₀ ∨ L₁=-L₀ := by
          rcases h₀ with h0|h0 <;> rcases h₁ with h1|h1 <;> simp [h0,h1]
        rcases hRel with hRel|hRel
        · obtain ⟨E₀,hE₀⟩ := hBasis B (fun i => i==0)
          apply hBool E₀
          · have hf : E₀ (FreeGroup.of 0)=(B (FreeGroup.of 0)).unop := by simpa using hE₀ 0
            rw [hf,hρ₀]
          · have ht : E₀ (FreeGroup.of 1)=((B (FreeGroup.of 1)).unop)⁻¹ := by simpa using hE₀ 1
            rw [ht,map_inv,hρ₁,hRel]
            exact (hQinverse d L₀).symm
        · obtain ⟨E₀,hE₀⟩ := hBasis B (fun _ => true)
          apply hBool E₀
          · have hf : E₀ (FreeGroup.of 0)=(B (FreeGroup.of 0)).unop := by simpa using hE₀ 0
            rw [hf,hρ₀]
          · have ht : E₀ (FreeGroup.of 1)=(B (FreeGroup.of 1)).unop := by simpa using hE₀ 1
            rw [ht,hρ₁,hRel]
      have hOneFixed {K Q : Type} [Group K] [TopologicalSpace Q] [MulAction K H2]
          (C : Set H2) (b : MulAction K C) (q : C → Q)
          (hq : letI := b;IsQuotientCoveringMap q K)
          (hcompat : letI := b;∀k : K,∀z : C,(k • z).val=k • z.val)
          (e : H2 ≃ᵢ H2) (ρ : K →* SL(2,ℝ))
          (hρ : ∀k z,e (k • z)=ρ k • e z)
          (a bmat j : SL(2,ℝ)) (E : FreeGroup Bool ≃* K)
          (hρ₀ : ρ (E (FreeGroup.of false))=a) (hρ₁ : ρ (E (FreeGroup.of true))=bmat)
          (hja : j*a*j⁻¹=bmat) (hjb : j*bmat*j⁻¹=a)
          (hinv : ∀z : H2,j • (j • z)=z)
          (hfix : ∀z : H2,j • z=z ↔ z=UpperHalfPlane.I)
          (hc : e.symm UpperHalfPlane.I∈C)
          (hpres : (fun z : H2 => e.symm (j • e z)) '' C=C)
          (τ : Q ≃ₜ Q)
          (hdesc : ∀z w : C,w.val=e.symm (j • e z.val) → τ (q z)=q w) :
          ∀y,τ y=y ↔ y=q ⟨e.symm UpperHalfPlane.I,hc⟩ := by
        have hClassifier {K X Y : Type} [Group K] [TopologicalSpace X] [TopologicalSpace Y] [MulAction K X]
            (q : X → Y) (hq : IsQuotientCoveringMap q K) (E : FreeGroup Bool ≃* K)
            (j : X ≃ₜ X) (hinv : Function.Involutive j)
            (hgen : ∀i : Bool,∀x : X,j (E (FreeGroup.of i) • x)=E (FreeGroup.of (!i)) • j x)
            (c : X) (hcenter : ∀x,j x=x ↔ x=c)
            (τ : Y ≃ₜ Y) (hdesc : ∀x,τ (q x)=q (j x)) :
            ∀y,τ y=y ↔ y=q c := by
          have htw : ∀w : FreeGroup Bool,∀x : X,j (E w • x)=E (FreeGroup.map Bool.not w) • j x := by
            intro w
            induction w using FreeGroup.induction_on with
            | one => intro x;simp
            | of i => intro x;simpa using hgen i x
            | inv_of i ih =>
                intro x
                have h := congrArg (fun y : X => (E (FreeGroup.map Bool.not (FreeGroup.of i)))⁻¹ • y)
                  (ih ((E (FreeGroup.of i))⁻¹ • x))
                simpa only [map_inv,smul_inv_smul,inv_smul_smul] using h.symm
            | mul w v hw hv =>
                intro x
                simp only [map_mul,mul_smul,hw,hv]
          letI : IsCancelSMul K X := hq.isCancelSMul
          letI : MulAction (FreeGroup Bool) X := MulAction.compHom X E.toMonoidHom
          have hfib (x z : X) : q x=q z ↔ ∃w : FreeGroup Bool,w • x=z := by
            constructor
            · intro he
              obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp he
              refine ⟨E.symm k⁻¹,?_⟩
              change E (E.symm k⁻¹) • x=z
              rw [E.apply_symm_apply,←hk,inv_smul_smul]
            · rintro ⟨w,hw⟩
              change E w • x=z at hw
              rw [←hw,hq.map_smul]
          have hfree (w : FreeGroup Bool) (x : X) (he : w • x=x) : w=1 := by
            change E w • x=x at he
            have hk : E w=1 := IsCancelSMul.right_cancel (E w) 1 x (by simpa using he)
            apply E.injective
            simpa only [map_one] using hk
          exact pants_actual_free_quotient_has_one_fixed_point q hq.surjective hfib hfree j hinv htw c hcenter τ hdesc
        letI := b
        let f : H2 → H2 := fun z => e.symm (j • e z)
        have hf (z : H2) : f (f z)=z := by
          dsimp only [f]
          rw [e.apply_symm_apply,hinv,e.symm_apply_apply]
        have hmem (z : C) : f z.val∈C := by
          have h : f z.val∈(fun z : H2 => e.symm (j • e z)) '' C := ⟨z.val,z.property,rfl⟩
          rw [hpres] at h
          exact h
        let lift : C ≃ₜ C := {
          toFun := fun z => ⟨f z.val,hmem z⟩
          invFun := fun z => ⟨f z.val,hmem z⟩
          left_inv := fun z => Subtype.ext (hf z.val)
          right_inv := fun z => Subtype.ext (hf z.val)
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact e.symm.continuous.comp ((IsometryEquiv.constSMul j).continuous.comp
              (e.continuous.comp continuous_subtype_val))
          continuous_invFun := by
            apply Continuous.subtype_mk
            exact e.symm.continuous.comp ((IsometryEquiv.constSMul j).continuous.comp
              (e.continuous.comp continuous_subtype_val)) }
        have hLiftInv : Function.Involutive lift := fun z => Subtype.ext (hf z.val)
        have hja' : j*a=bmat*j := by
          calc
            j*a=(j*a*j⁻¹)*j := by group
            _=bmat*j := by rw [hja]
        have hjb' : j*bmat=a*j := by
          calc
            j*bmat=(j*bmat*j⁻¹)*j := by group
            _=a*j := by rw [hjb]
        have hpoint (i : Bool) (z : H2) :
            f (E (FreeGroup.of i) • z)=E (FreeGroup.of (!i)) • f z := by
          apply e.injective
          dsimp only [f]
          rw [e.apply_symm_apply,hρ,hρ,e.apply_symm_apply]
          cases i
          · change j • ρ (E (FreeGroup.of false)) • e z = ρ (E (FreeGroup.of true)) • j • e z
            rw [hρ₀,hρ₁,←mul_smul,hja',mul_smul]
          · change j • ρ (E (FreeGroup.of true)) • e z = ρ (E (FreeGroup.of false)) • j • e z
            rw [hρ₀,hρ₁,←mul_smul,hjb',mul_smul]
        have hGen (i : Bool) (z : C) : lift (E (FreeGroup.of i) • z)=E (FreeGroup.of (!i)) • lift z := by
          apply Subtype.ext
          change f ((E (FreeGroup.of i) • z).val)=(E (FreeGroup.of (!i)) • lift z).val
          rw [hcompat,hcompat]
          exact hpoint i z.val
        let center : C := ⟨e.symm UpperHalfPlane.I,hc⟩
        have hCenter (z : C) : lift z=z ↔ z=center := by
          constructor
          · intro he
            have hh := congrArg (fun z : C => e z.val) he
            change e (e.symm (j • e z.val))=e z.val at hh
            rw [e.apply_symm_apply] at hh
            have hi : e z.val=UpperHalfPlane.I := (hfix (e z.val)).mp hh
            apply Subtype.ext
            apply e.injective
            change e z.val=e (e.symm UpperHalfPlane.I)
            rw [e.apply_symm_apply]
            exact hi
          · rintro rfl
            apply Subtype.ext
            change e.symm (j • e (e.symm UpperHalfPlane.I))=e.symm UpperHalfPlane.I
            rw [e.apply_symm_apply,(hfix UpperHalfPlane.I).mpr rfl]
        have hDesc (z : C) : τ (q z)=q (lift z) := hdesc z (lift z) rfl
        exact hClassifier q hq E lift hLiftInv hGen center hCenter τ hDesc
      have hSignedExchange (d T L₀ L₁ : ℝ) (h₀ : L₀=T ∨ L₀=-T) (h₁ : L₁=T ∨ L₁=-T) :
          let D : ℝ → SL(2,ℝ) := fun s =>
            ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
          let P := fun L : ℝ => D (-d/2)*R*D L*R⁻¹*D (d/2)
          let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
          (J*P L₀*J⁻¹=Q L₁ ∧ J*Q L₁*J⁻¹=P L₀) ∨
            (J*P L₀*J⁻¹=(Q L₁)⁻¹ ∧ J*Q L₁*J⁻¹=(P L₀)⁻¹) := by
        have hQinverse (d : ℝ) :
            let D : ℝ → SL(2,ℝ) := fun s =>
              ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
            let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
            ∀L : ℝ,Q (-L)=(Q L)⁻¹ := by
          intro D R Q
          have hDadd (s t : ℝ) : D s*D t=D (s+t) := by
            apply Subtype.ext
            change (D s).val*(D t).val=(D (s+t)).val
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [D,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,add_div,neg_add,mul_comm]
          have hDzero : D 0=1 := by
            apply Subtype.ext
            change (D 0).val=(1 : Matrix (Fin 2) (Fin 2) ℝ)
            ext i j
            fin_cases i <;> fin_cases j <;> simp [D]
          have hDinv (s : ℝ) : (D s)⁻¹=D (-s) := by
            apply inv_eq_of_mul_eq_one_right
            rw [hDadd,add_neg_cancel,hDzero]
          intro L
          dsimp only [Q]
          simp only [_root_.mul_inv_rev,hDinv,inv_inv,neg_div,neg_neg]
          group
        intro D R J P Q
        have hQi (L : ℝ) : Q (-L)=(Q L)⁻¹ := hQinverse d L
        have hPi (L : ℝ) : P (-L)=(P L)⁻¹ := by
          have h := hQinverse (-d) L
          dsimp only at h
          simpa [P,D,R,neg_div] using h
        have hex (L : ℝ) : J*P L*J⁻¹=Q (-L) ∧ J*Q (-L)*J⁻¹=P L :=
          actual_normalized_equal_boundary_generator_exchange d L
        rcases h₀ with h0|h0 <;> rcases h₁ with h1|h1
        all_goals rw [h0,h1]
        · right
          refine ⟨(hex T).1.trans (hQi T),?_⟩
          simpa only [neg_neg] using (hex (-T)).2.trans (hPi T)
        · left;exact hex T
        · left;simpa only [neg_neg] using hex (-T)
        · right
          constructor
          · simpa only [neg_neg] using (hex (-T)).1.trans (hQi (-T))
          · exact (hex T).2.trans (by simpa only [neg_neg] using hPi (-T))
      have hGroupNormalizer {G : Type} [Group G] (a b j : G)
          (hex : (j*a*j⁻¹=b ∧ j*b*j⁻¹=a) ∨
            (j*a*j⁻¹=b⁻¹ ∧ j*b*j⁻¹=a⁻¹)) :
          j∈Subgroup.normalizer (Subgroup.closure ({a,b}:Set G):Set G) := by
        rcases hex with ⟨ha,hb⟩|⟨ha,hb⟩
        · exact pants_boundary_exchange_normalizes_group a b j ha hb
        · have hi : Subgroup.closure ({b⁻¹,a⁻¹}:Set G)=Subgroup.closure ({a,b}:Set G) := by
            apply le_antisymm
            · apply (Subgroup.closure_le _).mpr
              intro g hg
              simp only [mem_insert_iff,mem_singleton_iff] at hg
              rcases hg with hg|hg
              · subst g
                exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
              · subst g
                exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
            · apply (Subgroup.closure_le _).mpr
              intro g hg
              simp only [mem_insert_iff,mem_singleton_iff] at hg
              rcases hg with hg|hg
              · subst g
                have hh : a⁻¹∈Subgroup.closure ({b⁻¹,a⁻¹}:Set G) := Subgroup.subset_closure (by simp)
                simpa using Subgroup.inv_mem _ hh
              · subst g
                have hh : b⁻¹∈Subgroup.closure ({b⁻¹,a⁻¹}:Set G) := Subgroup.subset_closure (by simp)
                simpa using Subgroup.inv_mem _ hh
          rw [Subgroup.mem_normalizer_iff_map_conj_eq,MonoidHom.map_closure]
          change Subgroup.closure (Set.image (fun x => j*x*j⁻¹) ({a,b}:Set G)) = _
          simpa only [Set.image_insert_eq,Set.image_singleton,ha,hb] using hi
      have hQuotientDescent {K Q : Type} [Group K] [TopologicalSpace Q] [MulAction K H2]
          (C : Set H2) (b : MulAction K C) (q : C → Q)
          (hq : letI := b;IsQuotientCoveringMap q K)
          (hcompat : letI := b;∀k : K,∀z : C,(k • z).val=k • z.val)
          (e : H2 ≃ᵢ H2) (ρ : K →* SL(2,ℝ))
          (hρ : ∀k z,e (k • z)=ρ k • e z)
          (j : SL(2,ℝ)) (hnorm : j∈Subgroup.normalizer (ρ.range:Set SL(2,ℝ)))
          (hinv : ∀z : H2,j • (j • z)=z)
          (hpres : (fun z : H2 => e.symm (j • e z)) '' C=C) :
          ∃τ : Q ≃ₜ Q, Function.Involutive τ ∧
            ∀z w : C,w.val=e.symm (j • e z.val) → τ (q z)=q w := by
        letI := b
        let f : H2 → H2 := fun z => e.symm (j • e z)
        have hf (z : H2) : f (f z)=z := by
          dsimp only [f]
          rw [e.apply_symm_apply,hinv,e.symm_apply_apply]
        have hmem (z : C) : f z.val∈C := by
          have h : f z.val∈(fun z : H2 => e.symm (j • e z)) '' C := ⟨z.val,z.property,rfl⟩
          rw [hpres] at h
          exact h
        let lift : C ≃ₜ C := {
          toFun := fun z => ⟨f z.val,hmem z⟩
          invFun := fun z => ⟨f z.val,hmem z⟩
          left_inv := fun z => Subtype.ext (hf z.val)
          right_inv := fun z => Subtype.ext (hf z.val)
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact e.symm.continuous.comp ((IsometryEquiv.constSMul j).continuous.comp
              (e.continuous.comp continuous_subtype_val))
          continuous_invFun := by
            apply Continuous.subtype_mk
            exact e.symm.continuous.comp ((IsometryEquiv.constSMul j).continuous.comp
              (e.continuous.comp continuous_subtype_val)) }
        have hFib (z w : C) (hzw : q z=q w) : q (lift z)=q (lift w) := by
          obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp hzw
          have hkg : j*ρ k*j⁻¹∈ρ.range := (Subgroup.mem_normalizer_iff.mp hnorm (ρ k)).mp ⟨k,rfl⟩
          obtain ⟨k',hk'⟩ := hkg
          apply hq.apply_eq_iff_mem_orbit.mpr
          refine ⟨k',?_⟩
          apply Subtype.ext
          rw [hcompat]
          apply e.injective
          change e (k' • f w.val)=e (f z.val)
          rw [hρ,hk']
          dsimp only [f]
          rw [e.apply_symm_apply,e.apply_symm_apply,mul_smul,mul_smul,inv_smul_smul]
          have hw : z.val=k • w.val := by
            have hh := congrArg Subtype.val hk
            simpa only [hcompat] using hh.symm
          rw [hw,hρ]
        have hSquare (z : C) : q (lift (lift z))=q z := by
          congr 1
          exact Subtype.ext (hf z.val)
        obtain ⟨τ,hτ,hτinv⟩ := pants_actual_quotient_involution_descends q hq.toIsQuotientMap lift hFib hSquare
        refine ⟨τ,hτinv,?_⟩
        intro z w hw
        rw [hτ]
        congr 1
        exact Subtype.ext hw.symm
      have hActionRepresentation {ι K : Type} [Group K] [MulAction K H2]
          (B : FreeGroup ι ≃* Kᵐᵒᵖ) (M : ι → SL(2,ℝ)) (e : H2 ≃ᵢ H2)
          (hgen : ∀i z,e ((B (FreeGroup.of i)).unop • z)=M i • e z) :
          ∃ρ : K →* SL(2,ℝ),
            (∀i,ρ (B (FreeGroup.of i)).unop=M i) ∧
            (∀k z,e (k • z)=ρ k • e z) ∧
            ρ.range=Subgroup.closure (range M) := by
        let E : FreeGroup ι ≃* K := B.trans (MulEquiv.inv' K).symm
        let F : FreeGroup ι →* SL(2,ℝ) := FreeGroup.lift (fun i => (M i)⁻¹)
        let ρ : K →* SL(2,ℝ) := F.comp E.symm.toMonoidHom
        have hE (i : ι) : E (FreeGroup.of i)=((B (FreeGroup.of i)).unop)⁻¹ := rfl
        have hword (w : FreeGroup ι) : ∀z,e (E w • z)=F w • e z := by
          induction w using FreeGroup.induction_on with
          | one => intro z;simp
          | of i =>
              intro z
              rw [hE]
              have h := congrArg (fun w : H2 => (M i)⁻¹ • w)
                (hgen i (((B (FreeGroup.of i)).unop)⁻¹ • z))
              simpa only [smul_inv_smul,inv_smul_smul,F,FreeGroup.lift_apply_of] using h.symm
          | inv_of i ih =>
              intro z
              have h := congrArg (fun w : H2 => (F (FreeGroup.of i))⁻¹ • w)
                (ih ((E (FreeGroup.of i))⁻¹ • z))
              simpa only [map_inv,smul_inv_smul,inv_smul_smul] using h.symm
          | mul x y hx hy =>
              intro z
              rw [map_mul,map_mul,mul_smul,mul_smul,hx,hy]
        refine ⟨ρ,?_,?_,?_⟩
        · intro i
          have hi : E.symm (B (FreeGroup.of i)).unop=(FreeGroup.of i)⁻¹ := by
            apply E.injective
            rw [E.apply_symm_apply,map_inv,hE,inv_inv]
          change F (E.symm (B (FreeGroup.of i)).unop)=M i
          rw [hi,map_inv]
          simp only [F,FreeGroup.lift_apply_of,inv_inv]
        · intro k z
          have h := hword (E.symm k) z
          change e (k • z)=F (E.symm k) • e z
          simpa only [E.apply_symm_apply] using h
        · have heRange : E.symm.toMonoidHom.range=⊤ := MonoidHom.range_eq_top.mpr E.symm.surjective
          have hRange : ρ.range=F.range := by
            dsimp only [ρ]
            rw [MonoidHom.range_comp,heRange,Subgroup.map_top]
          rw [hRange,FreeGroup.range_lift_eq_closure]
          apply le_antisymm
          · apply (Subgroup.closure_le _).mpr
            rintro g ⟨i,rfl⟩
            exact Subgroup.inv_mem _ (Subgroup.subset_closure (mem_range_self i))
          · apply (Subgroup.closure_le _).mpr
            rintro g ⟨i,rfl⟩
            have h : (M i)⁻¹∈Subgroup.closure (range (fun i => (M i)⁻¹)) :=
              Subgroup.subset_closure (mem_range_self i)
            change M i∈Subgroup.closure (range (fun i : ι => (M i)⁻¹))
            simpa only [inv_inv] using Subgroup.inv_mem _ h
      have hDomainTransport (C : Set H2) (e : H2 ≃ᵢ H2)
          (hopen : IsOpen C) (hconn : IsPreconnected C)
          (hreg : interior (closure C)=C)
          (hconv : ∀x∈C,∀y∈C,∀w : H2,dist x w+dist w y=dist x y → w∈C) :
          IsOpen (e '' C) ∧ IsPreconnected (e '' C) ∧
          interior (closure (e '' C))=e '' C ∧
          (∀x∈e '' C,∀y∈e '' C,∀w : H2,dist x w+dist w y=dist x y → w∈e '' C) ∧
          frontier (e '' C)=e '' frontier C := by
        refine ⟨e.toHomeomorph.isOpenMap C hopen,hconn.image e e.continuous.continuousOn,?_,?_,?_⟩
        · change interior (closure (e.toHomeomorph '' C))=e.toHomeomorph '' C
          rw [←e.toHomeomorph.image_closure,←e.toHomeomorph.image_interior,hreg]
        · rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩ w hs
          have ht : dist u (e.symm w)+dist (e.symm w) v=dist u v := by
            rw [←e.dist_eq u (e.symm w),←e.dist_eq (e.symm w) v,←e.dist_eq u v,e.apply_symm_apply]
            exact hs
          exact ⟨e.symm w,hconv u hu v hv (e.symm w) ht,e.apply_symm_apply w⟩
        · exact (e.toHomeomorph.image_frontier C).symm
      have hFrontierTransport {K : Type} [Group K] [MulAction K H2]
          (C S₀ S₁ Sc : Set H2) (e : H2 ≃ᵢ H2) (ρ : K →* SL(2,ℝ))
          (hρ : ∀k z,e (k • z)=ρ k • e z)
          (hfront : frontier C=(⋃k : K,(fun z : H2 => k • z) '' Sc) ∪
            (⋃k : K,(fun z : H2 => k • z) '' S₀) ∪
            (⋃k : K,(fun z : H2 => k • z) '' S₁)) :
          frontier (e '' C)=(⋃g : ρ.range,(fun z : H2 => g.val • z) '' (e '' Sc)) ∪
            (⋃g : ρ.range,(fun z : H2 => g.val • z) '' (e '' S₀)) ∪
            (⋃g : ρ.range,(fun z : H2 => g.val • z) '' (e '' S₁)) := by
        have hOrbit (S : Set H2) : e '' (⋃k : K,(fun z : H2 => k • z) '' S)=
            ⋃g : ρ.range,(fun z : H2 => g.val • z) '' (e '' S) := by
          ext z
          simp only [mem_image,mem_iUnion]
          constructor
          · rintro ⟨u,⟨k,v,hv,rfl⟩,rfl⟩
            exact ⟨⟨ρ k,⟨k,rfl⟩⟩,e v,⟨v,hv,rfl⟩,(hρ k v).symm⟩
          · rintro ⟨g,v,⟨u,hu,rfl⟩,he⟩
            obtain ⟨k,hk⟩ := g.property
            refine ⟨k • u,⟨k,u,hu,rfl⟩,?_⟩
            rw [hρ,hk]
            exact he
        have hefront : e '' frontier C=frontier (e '' C) := e.toHomeomorph.image_frontier C
        rw [←hefront,hfront,image_union,image_union,hOrbit,hOrbit,hOrbit]
      have hThreeOrbitHalfTurn (d T L₀ L₁ : ℝ) (hd : 0 < d)
          (h₀ : L₀=T ∨ L₀=-T) (h₁ : L₁=T ∨ L₁=-T)
          (C : Set H2) (hopen : IsOpen C) (hconn : IsPreconnected C)
          (hreg : interior (closure C)=C)
          (hconv : ∀x∈C,∀y∈C,∀w : H2,dist x w+dist w y=dist x y → w∈C)
          (αc : ℝ → H2) (hαc : Isometry αc) (hαfront : range αc⊆frontier C)
          (Lc ε : ℝ) (hLc : Lc≠0) (hε : 0 < ε) :
          let D : ℝ → SL(2,ℝ) := fun s =>
            ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
          let A := D (-d/2)*R*D L₀*R⁻¹*D (d/2)
          let B := D (d/2)*R*D L₁*R⁻¹*D (-d/2)
          let Γ := Subgroup.closure ({A,B}:Set SL(2,ℝ))
          let α₀ := fun t : ℝ => D (-d/2) • (R • verticalPath t)
          let α₁ := fun t : ℝ => D (d/2) • (R • verticalPath t)
          A • C=C → B • C=C → range α₀⊆frontier C → range α₁⊆frontier C →
          (∀z : H2,ε ≤ dist z ((B⁻¹*A) • z)) →
          (∀t : ℝ,(B⁻¹*A) • αc t=αc (t+Lc)) →
          frontier C=(⋃g : Γ,(fun z : H2 => g.val • z) '' range αc) ∪
            (⋃g : Γ,(fun z : H2 => g.val • z) '' range α₀) ∪
            (⋃g : Γ,(fun z : H2 => g.val • z) '' range α₁) →
          UpperHalfPlane.I∈C ∧ (fun z : H2 => J • z) '' C=C := by
        have hCenter (d T L₀ L₁ : ℝ) (hd : 0 < d)
            (h₀ : L₀=T ∨ L₀=-T) (h₁ : L₁=T ∨ L₁=-T)
            (C : Set H2) (hreg : interior (closure C)=C)
            (hconv : ∀x∈C,∀y∈C,∀w : H2,dist x w+dist w y=dist x y → w∈C) :
            let D : ℝ → SL(2,ℝ) := fun s =>
              ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
            let P := fun L : ℝ => D (-d/2)*R*D L*R⁻¹*D (d/2)
            let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
            P L₀ • C=C → Q L₁ • C=C →
            range (fun t : ℝ => D (-d/2) • (R • verticalPath t))⊆closure C →
            range (fun t : ℝ => D (d/2) • (R • verticalPath t))⊆closure C →
            UpperHalfPlane.I∈C := by
          have hQinverse (d : ℝ) :
              let D : ℝ → SL(2,ℝ) := fun s =>
                ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
              let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
              let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
              ∀L : ℝ,Q (-L)=(Q L)⁻¹ := by
            intro D R Q
            have hDadd (s t : ℝ) : D s*D t=D (s+t) := by
              apply Subtype.ext
              change (D s).val*(D t).val=(D (s+t)).val
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [D,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,add_div,neg_add,mul_comm]
            have hDzero : D 0=1 := by
              apply Subtype.ext
              change (D 0).val=(1 : Matrix (Fin 2) (Fin 2) ℝ)
              ext i j
              fin_cases i <;> fin_cases j <;> simp [D]
            have hDinv (s : ℝ) : (D s)⁻¹=D (-s) := by
              apply inv_eq_of_mul_eq_one_right
              rw [hDadd,add_neg_cancel,hDzero]
            intro L
            dsimp only [Q]
            simp only [_root_.mul_inv_rev,hDinv,inv_inv,neg_div,neg_neg]
            group
          have hOldCenter (d L : ℝ) (hd : 0<d) (C : Set H2)
              (hreg : interior (closure C)=C)
              (hconv : ∀ x∈C,∀ y∈C,∀ w : H2,dist x w+dist w y=dist x y → w∈C) :
              let D : ℝ → SL(2,ℝ) := fun s =>
                ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
              let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
              let A := D (-d/2)*R*D L*R⁻¹*D (d/2)
              let B := D (d/2)*R*D (-L)*R⁻¹*D (-d/2)
              A • C=C → B • C=C →
              range (fun t : ℝ => D (-d/2) • (R • verticalPath t))⊆closure C →
              range (fun t : ℝ => D (d/2) • (R • verticalPath t))⊆closure C →
              UpperHalfPlane.I∈C := by
            dsimp only
            let D : ℝ → SL(2,ℝ) := fun s =>
              ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
            let A := D (-d/2)*R*D L*R⁻¹*D (d/2)
            let B := D (d/2)*R*D (-L)*R⁻¹*D (-d/2)
            let Γ := Subgroup.closure ({A,B} : Set SL(2,ℝ))
            let axes := range (fun t : ℝ => D (-d/2) • (R • verticalPath t)) ∪
              range (fun t : ℝ => D (d/2) • (R • verticalPath t))
            let seed := {z : H2 | ∃ g : SL(2,ℝ),g∈Γ ∧ ∃ x∈axes,z=g • x}
            let Ω := {z : H2 | ∀ K : Set H2,IsClosed K → seed⊆K →
              (∀ x∈K,∀ y∈K,∀ w : H2,dist x w+dist w y=dist x y → w∈K) → z∈K}
            intro hA hB hinner houter
            have hΓ : Γ≤MulAction.stabilizer SL(2,ℝ) C := by
              apply (Subgroup.closure_le _).mpr
              intro g hg
              rcases hg with rfl|hg
              · exact MulAction.mem_stabilizer_iff.mpr hA
              · have he : g=B := mem_singleton_iff.mp hg
                subst g
                exact MulAction.mem_stabilizer_iff.mpr hB
            have hseed : seed⊆closure C := by
              rintro z ⟨g,hg,x,hx,rfl⟩
              have hgc : g • C=C := MulAction.mem_stabilizer_iff.mp (hΓ hg)
              have hcl : g • closure C=closure C := by rw [←closure_smul,hgc]
              rw [←hcl]
              exact smul_mem_smul_set ((union_subset hinner houter) hx)
            have hsub : Ω⊆closure C := by
              intro z hz
              exact hz (closure C) isClosed_closure hseed
                (actual_h2_metric_convex_subset_closure_metric_convex C hconv)
            have hcenter : UpperHalfPlane.I∈interior Ω :=
              actual_normalized_boundary_orbit_hull_center_interior d L hd
            rw [←hreg]
            exact interior_mono hsub hcenter
          intro D R P Q hP hQ hinner houter
          have hRel : L₁=L₀ ∨ L₁=-L₀ := by
            rcases h₀ with h0|h0 <;> rcases h₁ with h1|h1 <;> simp [h0,h1]
          have hQnegative : Q (-L₀) • C=C := by
            rcases hRel with hRel|hRel
            · subst L₁
              have hInv : (Q L₀)⁻¹ • C=C := by
                have h := congrArg (fun S : Set H2 => (Q L₀)⁻¹ • S) hQ
                simpa only [inv_smul_smul] using h.symm
              have hQi : Q (-L₀)=(Q L₀)⁻¹ := hQinverse d L₀
              rw [hQi]
              exact hInv
            · rw [←hRel]
              exact hQ
          exact hOldCenter d L₀ hd C hreg hconv hP hQnegative hinner houter
        have hExchange (d T L₀ L₁ : ℝ) (h₀ : L₀=T ∨ L₀=-T) (h₁ : L₁=T ∨ L₁=-T) :
            let D : ℝ → SL(2,ℝ) := fun s =>
              ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
            let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
            let P := fun L : ℝ => D (-d/2)*R*D L*R⁻¹*D (d/2)
            let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
            (J*P L₀*J⁻¹=Q L₁ ∧ J*Q L₁*J⁻¹=P L₀) ∨
              (J*P L₀*J⁻¹=(Q L₁)⁻¹ ∧ J*Q L₁*J⁻¹=(P L₀)⁻¹) := by
          have hQinverse (d : ℝ) :
              let D : ℝ → SL(2,ℝ) := fun s =>
                ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
              let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
              let Q := fun L : ℝ => D (d/2)*R*D L*R⁻¹*D (-d/2)
              ∀L : ℝ,Q (-L)=(Q L)⁻¹ := by
            intro D R Q
            have hDadd (s t : ℝ) : D s*D t=D (s+t) := by
              apply Subtype.ext
              change (D s).val*(D t).val=(D (s+t)).val
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [D,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,add_div,neg_add,mul_comm]
            have hDzero : D 0=1 := by
              apply Subtype.ext
              change (D 0).val=(1 : Matrix (Fin 2) (Fin 2) ℝ)
              ext i j
              fin_cases i <;> fin_cases j <;> simp [D]
            have hDinv (s : ℝ) : (D s)⁻¹=D (-s) := by
              apply inv_eq_of_mul_eq_one_right
              rw [hDadd,add_neg_cancel,hDzero]
            intro L
            dsimp only [Q]
            simp only [_root_.mul_inv_rev,hDinv,inv_inv,neg_div,neg_neg]
            group
          intro D R J P Q
          have hQi (L : ℝ) : Q (-L)=(Q L)⁻¹ := hQinverse d L
          have hPi (L : ℝ) : P (-L)=(P L)⁻¹ := by
            have h := hQinverse (-d) L
            dsimp only at h
            simpa [P,D,R,neg_div] using h
          have hex (L : ℝ) : J*P L*J⁻¹=Q (-L) ∧ J*Q (-L)*J⁻¹=P L :=
            actual_normalized_equal_boundary_generator_exchange d L
          rcases h₀ with h0|h0 <;> rcases h₁ with h1|h1
          all_goals rw [h0,h1]
          · right
            refine ⟨(hex T).1.trans (hQi T),?_⟩
            simpa only [neg_neg] using (hex (-T)).2.trans (hPi T)
          · left;exact hex T
          · left;simpa only [neg_neg] using hex (-T)
          · right
            constructor
            · simpa only [neg_neg] using (hex (-T)).1.trans (hQi (-T))
            · exact (hex T).2.trans (by simpa only [neg_neg] using hPi (-T))
        have hPeripheral (a b j : SL(2,ℝ)) (α : ℝ → H2) (hα : Isometry α)
            (L ε : ℝ) (hL : L≠0) (hε : 0 < ε)
            (hdisp : ∀z : H2,ε ≤ dist z ((b⁻¹*a) • z))
            (hclock : ∀t : ℝ,(b⁻¹*a) • α t=α (t+L))
            (hex : (j*a*j⁻¹=b ∧ j*b*j⁻¹=a) ∨
              (j*a*j⁻¹=b⁻¹ ∧ j*b*j⁻¹=a⁻¹)) :
            (fun z : H2 => j • z) '' range α=range α ∨
              (fun z : H2 => j • z) '' range α=(fun z : H2 => a • z) '' range α := by
          let c := b⁻¹*a
          have hcclock (t : ℝ) : c • α t=α (t+L) := hclock t
          have hinvclock (t : ℝ) : c⁻¹ • α t=α (t-L) := by
            have h := congrArg (fun z : H2 => c⁻¹ • z) (hcclock (t-L))
            simpa only [inv_smul_smul,sub_add_cancel] using h.symm
          have hpres (k : SL(2,ℝ)) (hkc : k*c*k⁻¹=c) :
              (fun z : H2 => k • z) '' range α=range α := by
            have hcomm : c*k=k*c := by
              calc
                c*k=(k*c*k⁻¹)*k := by rw [hkc]
                _=k*c := by group
            let β : ℝ → H2 := fun t => k • α t
            have hβ : Isometry β := (IsometryEquiv.constSMul k).isometry.comp hα
            have hβclock (t : ℝ) : c • β t=β (t+L) := by
              change c • (k • α t)=k • α (t+L)
              rw [←mul_smul,hcomm,mul_smul,hcclock]
            have hr := actual_h2_translated_isometric_lines_same_range
              (IsometryEquiv.constSMul c) α β hα hβ ε hε hdisp L L hL hL hcclock hβclock
            simpa only [β,←range_comp',Function.comp_def] using hr.symm
          rcases hex with ⟨ha,hb⟩|⟨ha,hb⟩
          · left
            have hconj : j*c*j⁻¹=c⁻¹ := by
              calc
                j*c*j⁻¹=(j*b*j⁻¹)⁻¹*(j*a*j⁻¹) := by dsimp only [c];group
                _=c⁻¹ := by rw [ha,hb];dsimp only [c];group
            have hconji : j*c⁻¹*j⁻¹=c := by
              have h := congrArg (fun x : SL(2,ℝ) => x⁻¹) hconj
              simpa only [_root_.mul_inv_rev,inv_inv,mul_assoc] using h
            have hrel : c*j=j*c⁻¹ := by
              calc
                c*j=(j*c⁻¹*j⁻¹)*j := by rw [hconji]
                _=j*c⁻¹ := by group
            let β : ℝ → H2 := fun t => j • α t
            have hβ : Isometry β := (IsometryEquiv.constSMul j).isometry.comp hα
            have hβclock (t : ℝ) : c • β t=β (t+(-L)) := by
              change c • (j • α t)=j • α (t+(-L))
              rw [←mul_smul,hrel,mul_smul,hinvclock]
              rfl
            have hr := actual_h2_translated_isometric_lines_same_range
              (IsometryEquiv.constSMul c) α β hα hβ ε hε hdisp L (-L) hL (neg_ne_zero.mpr hL) hcclock hβclock
            simpa only [β,←range_comp',Function.comp_def] using hr.symm
          · right
            have hconj : j*c*j⁻¹=a*c*a⁻¹ := by
              calc
                j*c*j⁻¹=(j*b*j⁻¹)⁻¹*(j*a*j⁻¹) := by dsimp only [c];group
                _=a*c*a⁻¹ := by rw [ha,hb];dsimp only [c];group
            have hkconj : (a⁻¹*j)*c*(a⁻¹*j)⁻¹=c := by
              calc
                (a⁻¹*j)*c*(a⁻¹*j)⁻¹=a⁻¹*(j*c*j⁻¹)*a := by group
                _=c := by rw [hconj];group
            have hk := hpres (a⁻¹*j) hkconj
            have hh := congrArg (fun S : Set H2 => (fun z : H2 => a • z) '' S) hk
            rw [image_image] at hh
            simpa only [mul_smul,smul_inv_smul] using hh
        have hNoStable (C : Set H2) (hopen : IsOpen C) (hcenter : UpperHalfPlane.I∈C)
            (α : ℝ → H2) (hα : Isometry α) (hfront : range α⊆frontier C) :
            let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
            (fun z : H2 => J • z) '' range α≠range α := by
          have hAxisFixed (g : H2 ≃ᵢ H2) (hinv : Function.Involutive g)
              (α : ℝ → H2) (hα : Isometry α) (hpres : g '' range α=range α) :
              ∃t : ℝ,g (α t)=α t := by
            classical
            have hReal (f : ℝ → ℝ) (hf : Isometry f) :
                (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
              let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
              let k : ℝ := A.toAffineMap.linear 1
              have hfac (t : ℝ) : f t=t*k+f 0 := by
                have h := A.toAffineMap.map_vadd 0 t
                have hlin : A.toAffineMap.linear t=t*k := by
                  have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
                  simpa [k,smul_eq_mul] using hh
                change f (t+0)=A.toAffineMap.linear t+f 0 at h
                simpa only [add_zero,hlin] using h
              have hk : |k|=1 := by
                have h := hf.dist_eq 1 0
                rw [hfac 1,hfac 0] at h
                simpa [Real.dist_eq] using h
              rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
              · left;intro t;rw [hfac,he];ring
              · right;intro t;rw [hfac,he];ring
            have hExists (t : ℝ) : ∃s : ℝ,α s=g (α t) := by
              have hmem : g (α t)∈range α := hpres ▸ ⟨α t,mem_range_self t,rfl⟩
              exact hmem
            let f : ℝ → ℝ := fun t => Classical.choose (hExists t)
            have hf (t : ℝ) : α (f t)=g (α t) := Classical.choose_spec (hExists t)
            have hfi : Isometry f := by
              apply Isometry.of_dist_eq
              intro s t
              rw [←hα.dist_eq,hf,hf,g.dist_eq,hα.dist_eq]
            have hff (t : ℝ) : f (f t)=t := by
              apply hα.injective
              rw [hf,hf,hinv]
            rcases hReal f hfi with hplus|hminus
            · have hz : f 0=0 := by
                have h := hff 0
                rw [hplus] at h
                linarith
              refine ⟨0,?_⟩
              rw [←hf,hz]
            · refine ⟨f 0/2,?_⟩
              rw [←hf,hminus]
              congr 1;ring
          intro J hpres
          obtain ⟨hinv,hfixed⟩ := hyperbolic_normalized_half_turn
          obtain ⟨t,ht⟩ := hAxisFixed (IsometryEquiv.constSMul J) hinv α hα hpres
          have hI : α t=UpperHalfPlane.I := (hfixed (α t)).mp ht
          have hIf : UpperHalfPlane.I∈frontier C := hI ▸ hfront (mem_range_self t)
          have hdis : Disjoint C (frontier C) := by
            rw [frontier,hopen.interior_eq]
            exact disjoint_sdiff_right
          exact Set.disjoint_left.mp hdis hcenter hIf
        have hOrbit {G X : Type} [Group G] [MulAction G X] (Γ : Subgroup G) (j : G)
            (hnorm : j∈Subgroup.normalizer (Γ:Set G))
            (hinv : ∀x : X,j • (j • x)=x) (seed : Set X)
            (hseed : ∀x∈seed,∃g : Γ,∃y∈seed,j • x=g.val • y) :
            let F := {z : X | ∃g : Γ,∃y∈seed,z=g.val • y}
            (fun z : X => j • z) '' F=F := by
          intro F
          have hsub : (fun z : X => j • z) '' F⊆F := by
            rintro z ⟨x,⟨g,y,hy,rfl⟩,rfl⟩
            obtain ⟨h,w,hw,he⟩ := hseed y hy
            have hmem : j*g.val*j⁻¹∈Γ := (Subgroup.mem_normalizer_iff.mp hnorm g.val).mp g.property
            refine ⟨⟨(j*g.val*j⁻¹)*h.val,Γ.mul_mem hmem h.property⟩,w,hw,?_⟩
            rw [mul_smul,mul_smul,mul_smul,←he,inv_smul_smul]
          apply subset_antisymm hsub
          intro z hz
          refine ⟨j • z,hsub ⟨z,hz,rfl⟩,hinv z⟩
        have hNormalizer {G : Type} [Group G] (a b j : G)
            (hex : (j*a*j⁻¹=b ∧ j*b*j⁻¹=a) ∨
              (j*a*j⁻¹=b⁻¹ ∧ j*b*j⁻¹=a⁻¹)) :
            j∈Subgroup.normalizer (Subgroup.closure ({a,b}:Set G):Set G) := by
          rcases hex with ⟨ha,hb⟩|⟨ha,hb⟩
          · exact pants_boundary_exchange_normalizes_group a b j ha hb
          · have hi : Subgroup.closure ({b⁻¹,a⁻¹}:Set G)=Subgroup.closure ({a,b}:Set G) := by
              apply le_antisymm
              · apply (Subgroup.closure_le _).mpr
                intro g hg
                simp only [mem_insert_iff,mem_singleton_iff] at hg
                rcases hg with hg|hg
                · subst g
                  exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
                · subst g
                  exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
              · apply (Subgroup.closure_le _).mpr
                intro g hg
                simp only [mem_insert_iff,mem_singleton_iff] at hg
                rcases hg with hg|hg
                · subst g
                  have hh : a⁻¹∈Subgroup.closure ({b⁻¹,a⁻¹}:Set G) := Subgroup.subset_closure (by simp)
                  simpa using Subgroup.inv_mem _ hh
                · subst g
                  have hh : b⁻¹∈Subgroup.closure ({b⁻¹,a⁻¹}:Set G) := Subgroup.subset_closure (by simp)
                  simpa using Subgroup.inv_mem _ hh
            rw [Subgroup.mem_normalizer_iff_map_conj_eq,MonoidHom.map_closure]
            change Subgroup.closure (Set.image (fun x => j*x*j⁻¹) ({a,b}:Set G)) = _
            simpa only [Set.image_insert_eq,Set.image_singleton,ha,hb] using hi
        have hDomain {X : Type} [TopologicalSpace X] (C : Set X) (hopen : IsOpen C)
            (hconn : IsPreconnected C) (j : X ≃ₜ X) (hinv : Function.Involutive j)
            (hfront : j '' frontier C = frontier C) (x : X) (hx : x∈C) (hfix : j x=x) :
            j '' C=C := by
          have hdis : Disjoint C (frontier C) := by
            rw [frontier, hopen.interior_eq]
            exact disjoint_sdiff_right
          have hjdis : Disjoint (j '' C) (frontier C) := by
            rw [←hfront]
            apply Set.disjoint_left.mpr
            rintro z ⟨u,hu,he⟩ ⟨v,hv,hvEq⟩
            have huv : u=v := j.injective (he.trans hvEq.symm)
            exact Set.disjoint_left.mp hdis hu (huv.symm ▸ hv)
          have hsub : j '' C⊆C := by
            apply (hconn.image j j.continuous.continuousOn).subset_of_closure_inter_subset hopen
            · exact ⟨x,⟨x,hx,hfix⟩,hx⟩
            · intro z hz
              by_contra hn
              have hf : z∈frontier C := by
                rw [frontier,hopen.interior_eq]
                exact ⟨hz.1,hn⟩
              exact Set.disjoint_left.mp hjdis hz.2 hf
          apply subset_antisymm hsub
          intro z hz
          refine ⟨j z,hsub ⟨z,hz,rfl⟩,hinv z⟩
        intro D R J A B Γ α₀ α₁ hA hB hf₀ hf₁ hdisp hclock hfrontier
        have hcenter : UpperHalfPlane.I∈C :=
          hCenter d T L₀ L₁ hd h₀ h₁ C hreg hconv hA hB
            (hf₀.trans frontier_subset_closure) (hf₁.trans frontier_subset_closure)
        have hex : (J*A*J⁻¹=B ∧ J*B*J⁻¹=A) ∨
            (J*A*J⁻¹=B⁻¹ ∧ J*B*J⁻¹=A⁻¹) := hExchange d T L₀ L₁ h₀ h₁
        have hnorm : J∈Subgroup.normalizer (Γ:Set SL(2,ℝ)) := hNormalizer A B J hex
        have hcimage : (fun z : H2 => J • z) '' range αc=(fun z : H2 => A • z) '' range αc := by
          have hp := hPeripheral A B J αc hαc Lc ε hLc hε hdisp hclock hex
          exact hp.resolve_left (hNoStable C hopen hcenter αc hαc hαfront)
        obtain ⟨hinv,hfixed⟩ := hyperbolic_normalized_half_turn
        have hjinv (z : H2) : J • (J • z)=z := hinv z
        obtain ⟨ha,hb,hswap,hsep,hdist⟩ := actual_normalized_boundary_axes_common_perpendicular d hd.le
        have hs₀ (t : ℝ) : J • α₀ t=α₁ (-t) := hswap t
        have hs₁ (t : ℝ) : J • α₁ t=α₀ (-t) := by
          have h := congrArg (fun z : H2 => J • z) (hs₀ (-t))
          simpa only [hjinv,neg_neg] using h.symm
        let seed := range αc ∪ range α₀ ∪ range α₁
        let F := {z : H2 | ∃g : Γ,∃y∈seed,z=g.val • y}
        have hseed : ∀x∈seed,∃g : Γ,∃y∈seed,J • x=g.val • y := by
          intro x hx
          rcases hx with (hx|hx)|hx
          · have hm : J • x∈(fun z : H2 => A • z) '' range αc := by
              rw [←hcimage]
              exact ⟨x,hx,rfl⟩
            obtain ⟨y,hy,he⟩ := hm
            refine ⟨⟨A,Subgroup.subset_closure (by simp)⟩,y,Or.inl (Or.inl hy),he.symm⟩
          · obtain ⟨t,rfl⟩ := hx
            exact ⟨1,α₁ (-t),Or.inr (mem_range_self (-t)),by simpa using hs₀ t⟩
          · obtain ⟨t,rfl⟩ := hx
            exact ⟨1,α₀ (-t),Or.inl (Or.inr (mem_range_self (-t))),by simpa using hs₁ t⟩
        have hF : F=frontier C := by
          rw [hfrontier]
          ext z
          simp only [F,seed,mem_setOf_eq,mem_union,mem_iUnion,mem_image]
          constructor
          · rintro ⟨g,y,hy,he⟩
            rcases hy with (hc|h0)|h1
            · exact Or.inl (Or.inl ⟨g,y,hc,he.symm⟩)
            · exact Or.inl (Or.inr ⟨g,y,h0,he.symm⟩)
            · exact Or.inr ⟨g,y,h1,he.symm⟩
          · rintro ((⟨g,y,hy,he⟩|⟨g,y,hy,he⟩)|⟨g,y,hy,he⟩)
            · exact ⟨g,y,Or.inl (Or.inl hy),he.symm⟩
            · exact ⟨g,y,Or.inl (Or.inr hy),he.symm⟩
            · exact ⟨g,y,Or.inr hy,he.symm⟩
        have hFr : (fun z : H2 => J • z) '' frontier C=frontier C := by
          have h := hOrbit Γ J hnorm hinv seed hseed
          change (fun z : H2 => J • z) '' F=F at h
          simpa only [hF] using h
        have hpres := hDomain C hopen hconn (IsometryEquiv.constSMul J).toHomeomorph
          hinv hFr UpperHalfPlane.I hcenter ((hfixed UpperHalfPlane.I).mpr rfl)
        exact ⟨hcenter,hpres⟩
      have hFreeClock (g : H2 ≃ᵢ H2) (α : ℝ → H2) (hα : Isometry α)
          (hpres : g '' range α=range α) (hfree : ∀z : H2,g z≠z) :
          ∃L : ℝ,L≠0 ∧ ∀t : ℝ,g (α t)=α (t+L) := by
        classical
        have hReal (f : ℝ → ℝ) (hf : Isometry f) :
            (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
          let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
          let k : ℝ := A.toAffineMap.linear 1
          have hfac (t : ℝ) : f t=t*k+f 0 := by
            have h := A.toAffineMap.map_vadd 0 t
            have hlin : A.toAffineMap.linear t=t*k := by
              have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
              simpa [k,smul_eq_mul] using hh
            change f (t+0)=A.toAffineMap.linear t+f 0 at h
            simpa only [add_zero,hlin] using h
          have hk : |k|=1 := by
            have h := hf.dist_eq 1 0
            rw [hfac 1,hfac 0] at h
            simpa [Real.dist_eq] using h
          rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
          · left;intro t;rw [hfac,he];ring
          · right;intro t;rw [hfac,he];ring
        have hExists (t : ℝ) : ∃s : ℝ,α s=g (α t) := by
          have hmem : g (α t)∈range α := hpres ▸ ⟨α t,mem_range_self t,rfl⟩
          exact hmem
        let f : ℝ → ℝ := fun t => Classical.choose (hExists t)
        have hf (t : ℝ) : α (f t)=g (α t) := Classical.choose_spec (hExists t)
        have hfi : Isometry f := by
          apply Isometry.of_dist_eq
          intro s t
          rw [←hα.dist_eq,hf,hf,g.dist_eq,hα.dist_eq]
        rcases hReal f hfi with hplus|hminus
        · refine ⟨f 0,?_,?_⟩
          · intro he
            apply hfree (α 0)
            rw [←hf 0,he]
          · intro t
            rw [←hf t,hplus t]
            congr 1;ring
        · exfalso
          apply hfree (α (f 0/2))
          rw [←hf,hminus]
          congr 1;ring
      have hWordNonidentity {G : Type} [Group G] (K : Subgroup G)
          (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ) :
          (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val≠1 := by
        have hw : (FreeGroup.of (0:Fin 2)*(FreeGroup.of 1)⁻¹)≠1 := by
          let φ : FreeGroup (Fin 2) →* Multiplicative ℤ :=
            FreeGroup.lift (fun i => Multiplicative.ofAdd (if i=0 then (1:ℤ) else 0))
          intro he
          have h := congrArg (fun w => Multiplicative.toAdd (φ w)) he
          norm_num [φ] at h
        intro he
        apply hw
        apply B.injective
        apply MulOpposite.unop_injective
        apply Subtype.ext
        simpa only [map_one,MulOpposite.unop_one,Subgroup.coe_one] using he
      have hTwoNormalize {E G : Type} [MetricSpace E] [Group G]
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (hmetric : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
            ∀y∈W,∀z∈W,dist (p y) (p z)=dist y z)
          (Q : Set E) (hQ : IsOpen Q) (x : H2) (hx : p x∈Q)
          (α β : ℝ → H2) (hα : Isometry α) (hβ : Isometry β)
          (T₀ T₁ : ℝ) (δ₀ δ₁ : G)
          (hδ₀ : letI := a;δ₀∈MulAction.stabilizer G (connectedComponentIn (p ⁻¹' Q) x))
          (hδ₁ : letI := a;δ₁∈MulAction.stabilizer G (connectedComponentIn (p ⁻¹' Q) x))
          (hfront₀ : range α⊆frontier (connectedComponentIn (p ⁻¹' Q) x))
          (hfront₁ : range β⊆frontier (connectedComponentIn (p ⁻¹' Q) x))
          (hshift₀ : (∀t : ℝ,@SMul.smul G H2 a.toSMul δ₀ (α t)=α (t+T₀)) ∨
            (∀t : ℝ,@SMul.smul G H2 a.toSMul δ₀⁻¹ (α t)=α (t+T₀)))
          (hshift₁ : (∀t : ℝ,@SMul.smul G H2 a.toSMul δ₁ (β t)=β (t+T₁)) ∨
            (∀t : ℝ,@SMul.smul G H2 a.toSMul δ₁⁻¹ (β t)=β (t+T₁)))
          (hsep : ∃ε : ℝ,0 < ε ∧ ∀s t : ℝ,ε ≤ dist (α s) (β t)) :
          let D : ℝ → SL(2,ℝ) := fun s =>
            ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
          let R : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
          ∃d : ℝ,0 < d ∧ ∃g : SL(2,ℝ),∃L₀ L₁ : ℝ,
            (L₀=T₀ ∨ L₀=-T₀) ∧ (L₁=T₁ ∨ L₁=-T₁) ∧
            (fun z : H2 => g • z) '' range α=range (fun t => D (-d/2) • (R • verticalPath t)) ∧
            (fun z : H2 => g • z) '' range β=range (fun t => D (d/2) • (R • verticalPath t)) ∧
            (∀z : H2,g • (@SMul.smul G H2 a.toSMul δ₀ z)=
              ((D (-d/2)*R)*D L₀*(D (-d/2)*R)⁻¹) • (g • z)) ∧
            (∀z : H2,g • (@SMul.smul G H2 a.toSMul δ₁ z)=
              ((D (d/2)*R)*D L₁*(D (d/2)*R)⁻¹) • (g • z)) := by
        intro D R
        letI := a
        obtain ⟨d,hd,g,h₀,h₁⟩ := actual_positively_separated_complete_axes_simultaneous_sl_range_normalization α β hα hβ hsep
        change (fun z : H2 => g • z) '' range α=range (fun t : ℝ => D (-d/2) • (R • verticalPath t)) at h₀
        change (fun z : H2 => g • z) '' range β=range (fun t : ℝ => D (d/2) • (R • verticalPath t)) at h₁
        let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
        let F₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul (D (-d/2)*R)
        let F₁ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul (D (d/2)*R)
        have hf₀ : (F₀.trans e.symm).symm '' range α=range verticalPath := by
          change (fun z : H2 => (D (-d/2)*R)⁻¹ • (g • z)) '' range α=range verticalPath
          rw [←image_image,h₀]
          simp only [←range_comp',←mul_smul,inv_mul_cancel,one_smul]
        have hf₁ : (F₁.trans e.symm).symm '' range β=range verticalPath := by
          change (fun z : H2 => (D (d/2)*R)⁻¹ • (g • z)) '' range β=range verticalPath
          rw [←image_image,h₁]
          simp only [←range_comp',←mul_smul,inv_mul_cancel,one_smul]
        obtain ⟨L₀,hL₀,hact₀⟩ := actual_original_cut_supplied_axis_frame_signed_sl_action_source
          a p hq hmetric Q hQ x hx α hα T₀ δ₀ hδ₀ hfront₀ hshift₀ (F₀.trans e.symm) hf₀
        obtain ⟨L₁,hL₁,hact₁⟩ := actual_original_cut_supplied_axis_frame_signed_sl_action_source
          a p hq hmetric Q hQ x hx β hβ T₁ δ₁ hδ₁ hfront₁ hshift₁ (F₁.trans e.symm) hf₁
        have hUnwind (F : SL(2,ℝ)) (δ : G) (L : ℝ)
            (hact : ∀z : H2,((IsometryEquiv.constSMul F).trans e.symm).symm
              (δ • (((IsometryEquiv.constSMul F).trans e.symm) z))=D L • z) :
            ∀z : H2,g • (δ • z)=(F*D L*F⁻¹) • (g • z) := by
          let f : H2 ≃ᵢ H2 := IsometryEquiv.constSMul F
          intro z
          have h := congrArg f (hact (f.symm (e z)))
          change f (f.symm (e (δ • e.symm (f (f.symm (e z))))))=
            f (D L • f.symm (e z)) at h
          simp only [f.apply_symm_apply,e.symm_apply_apply] at h
          change g • (δ • z)=F • (D L • (F⁻¹ • (g • z))) at h
          simpa only [mul_smul] using h
        exact ⟨d,hd,g,L₀,L₁,hL₀,hL₁,h₀,h₁,hUnwind _ _ _ hact₀,hUnwind _ _ _ hact₁⟩
      have hRegular {E : Type} [MetricSpace E] [LocallyConnectedSpace E] (c d : Curve E)
          (hcgeo : IsClosedGeodesic c.image) (hdgeo : IsClosedGeodesic d.image)
          (p : H2 → E) (hp : IsCoveringMap p)
          (hmetric : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧
            ∀y∈W,∀z∈W,dist (p y) (p z)=dist y z)
          (x : H2) (hx : p x∈(c.image∪d.image)ᶜ) :
          let U := connectedComponentIn (c.image∪d.image)ᶜ (p x)
          let C := connectedComponentIn (p ⁻¹' U) x
          IsOpen C ∧ interior (closure C)=C ∧
            (∀y∈C,∀z∈C,∀w : H2,dist y w+dist w z=dist y z → w∈C) := by
        have hregular {ι : Type} (a : ι → ℝ → H2) (ha : ∀ i,Isometry (a i))
            (x : H2) (hx : x∈(⋃ i,range (a i))ᶜ)
            (hF : IsOpen (⋃ i,range (a i))ᶜ) :
            let C := connectedComponentIn (⋃ i,range (a i))ᶜ x
            interior (closure C)=C := by
          let F := (⋃ i,range (a i))ᶜ
          let C := connectedComponentIn F x
          have hnormalize (a : ℝ → H2) (ha : Isometry a) :
              ∃ e : H2 ≃ᵢ H2,∀ t,a t=e (verticalPath t) := by
            obtain ⟨e,he0,he1⟩ := exists_ordered_pair_isometry (a 0) (a 1) (by
              rw [ha.dist_eq];norm_num [Real.dist_eq])
            have h0 : e (verticalPath 0)=a 0 := by
              have hv : verticalPath 0=UpperHalfPlane.I := by
                apply UpperHalfPlane.ext
                apply Complex.ext <;> simp [verticalPath,UpperHalfPlane.I]
              rw [hv];exact he0
            have hf : Isometry (fun t : ℝ => e.symm (a t)) := e.symm.isometry.comp ha
            have hf0 : e.symm (a 0)=verticalPath 0 := by rw [←h0,e.symm_apply_apply]
            have hf1 : e.symm (a 1)=verticalPath 1 := by rw [←he1,e.symm_apply_apply]
            refine ⟨e,?_⟩
            intro t
            simpa only [e.apply_symm_apply] using congrArg e
              (isometry_eq_vertical_of_values _ hf hf0 hf1 t)
          have hopen : IsOpen C := hF.connectedComponentIn
          have hsub : interior (closure C)⊆F := by
            intro y hy hline
            obtain ⟨i,⟨t,ht⟩⟩ := mem_iUnion.mp hline
            obtain ⟨e,he⟩ := hnormalize (a i) (ha i)
            have hz : (e.symm y).re=0 := by rw [←ht,he,e.symm_apply_apply];simp [verticalPath]
            have hn (z : H2) (hzC : z∈C) : (e.symm z).re≠0 := by
              intro hz0
              have hza : z∈range (a i) := by
                refine ⟨Real.log (e.symm z).im,?_⟩
                rw [he]
                apply e.symm.injective
                rw [e.symm_apply_apply]
                apply UpperHalfPlane.ext_re_im
                · simpa [verticalPath] using hz0.symm
                · simp [verticalPath,Real.exp_log (e.symm z).im_pos]
              exact (connectedComponentIn_subset F x hzC) (mem_iUnion.mpr ⟨i,hza⟩)
            have hc : IsPreconnected C := isPreconnected_connectedComponentIn
            have hcont : Continuous (fun z : H2 => (e.symm z).re) :=
              UpperHalfPlane.continuous_re.comp e.symm.continuous
            have hxC : x∈C := mem_connectedComponentIn hx
            rcases lt_or_gt_of_ne (hn x hxC) with hxneg|hxpos
            · have hhalf : closure C⊆{z : H2 | (e.symm z).re≤0} := by
                apply closure_minimal
                · intro z hzC
                  exact le_of_lt (hc.gt_of_ne hcont.continuousOn hn ⟨x,hxC,hxneg⟩ hzC)
                · exact isClosed_le hcont continuous_const
              let f : ℝ → H2 := fun r => e ⟨(r : ℂ)+(e.symm y).im*Complex.I,by
                simpa using (e.symm y).im_pos⟩
              have hfc : Continuous f := by dsimp [f];fun_prop
              have hf0 : f 0=y := by
                apply e.symm.injective
                simp only [f,e.symm_apply_apply]
                apply UpperHalfPlane.ext_re_im <;> simp [hz]
              have hnb : f ⁻¹' interior (closure C)∈nhds (0 : ℝ) :=
                hfc.continuousAt.preimage_mem_nhds (by rw [hf0];exact isOpen_interior.mem_nhds hy)
              obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnb
              have hmem := hhalf (interior_subset (hball (show ε/2∈Metric.ball (0 : ℝ) ε by
                simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<ε/2)]
                linarith)))
              have hfRe : (e.symm (f (ε/2))).re=ε/2 := by simp [f]
              change (e.symm (f (ε/2))).re≤0 at hmem
              rw [hfRe] at hmem
              linarith
            · have hhalf : closure C⊆{z : H2 | 0≤(e.symm z).re} := by
                apply closure_minimal
                · intro z hzC
                  exact le_of_lt (hc.lt_of_ne hcont.continuousOn hn ⟨x,hxC,hxpos⟩ hzC)
                · exact isClosed_le continuous_const hcont
              let f : ℝ → H2 := fun r => e ⟨(-(r : ℂ))+(e.symm y).im*Complex.I,by
                simpa using (e.symm y).im_pos⟩
              have hfc : Continuous f := by dsimp [f];fun_prop
              have hf0 : f 0=y := by
                apply e.symm.injective
                simp only [f,e.symm_apply_apply]
                apply UpperHalfPlane.ext_re_im <;> simp [hz]
              have hnb : f ⁻¹' interior (closure C)∈nhds (0 : ℝ) :=
                hfc.continuousAt.preimage_mem_nhds (by rw [hf0];exact isOpen_interior.mem_nhds hy)
              obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hnb
              have hmem := hhalf (interior_subset (hball (show ε/2∈Metric.ball (0 : ℝ) ε by
                simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0<ε/2)]
                linarith)))
              have hfRe : (e.symm (f (ε/2))).re= -(ε/2) := by simp [f]
              change 0≤(e.symm (f (ε/2))).re at hmem
              rw [hfRe] at hmem
              linarith
          apply subset_antisymm
          · intro y hy
            have hyF : y∈F := hsub hy
            by_contra hyC
            have hdis : Disjoint C (connectedComponentIn F y) := by
              apply disjoint_left.mpr
              intro z hzC hzy
              have he := connectedComponentIn_eq hzy
              have hyy : y∈connectedComponentIn F z := by
                rw [←he];exact mem_connectedComponentIn hyF
              rw [←connectedComponentIn_eq hzC] at hyy
              exact hyC hyy
            have hny : connectedComponentIn F y∈nhds y := (hF.connectedComponentIn).mem_nhds
              (mem_connectedComponentIn hyF)
            obtain ⟨z,hzy,hzC⟩ := mem_closure_iff_nhds.mp (interior_subset hy) _ hny
            exact disjoint_left.mp hdis hzC hzy
          · exact hopen.subset_interior_iff.mpr subset_closure
        have hid {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
            (p : P → E) (hp : Continuous p) (F : Set E) (x : P) :
            connectedComponentIn (p ⁻¹' connectedComponentIn F (p x)) x=
              connectedComponentIn (p ⁻¹' F) x := by
          apply subset_antisymm
          · exact connectedComponentIn_mono x (Set.preimage_mono (connectedComponentIn_subset F (p x)))
          · by_cases hx : p x∈F
            · have hx' : x∈p ⁻¹' F := hx
              have hmaps : p '' connectedComponentIn (p ⁻¹' F) x⊆connectedComponentIn F (p x) :=
                (hp.continuousOn.image_connectedComponentIn_subset hx').trans
                  (connectedComponentIn_mono (p x) (Set.image_preimage_subset p F))
              apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hx')
              intro z hz
              exact hmaps ⟨z,hz,rfl⟩
            · rw [connectedComponentIn_eq_empty (show x∉p ⁻¹' F from hx)]
              exact empty_subset _
        classical
        let F := (c.image∪d.image)ᶜ
        let U := connectedComponentIn F (p x)
        let C := connectedComponentIn (p ⁻¹' U) x
        have hF : IsOpen F :=
          ((isCompact_range c.embedded.continuous).isClosed.union
            (isCompact_range d.embedded.continuous).isClosed).isOpen_compl
        have hU : IsOpen U := hF.connectedComponentIn
        have hxU : p x∈U := mem_connectedComponentIn hx
        obtain ⟨γc,Tc,hTc,hγc,hperiodc,hrangec,hunitc⟩ := hcgeo
        obtain ⟨γd,Td,hTd,hγd,hperiodd,hranged,hunitd⟩ := hdgeo
        let γcC : ContinuousMap ℝ E := ⟨γc,hγc⟩
        let γdC : ContinuousMap ℝ E := ⟨γd,hγd⟩
        obtain ⟨aC,haC,heqC⟩ := actual_developed_geodesic_preimage_is_union_complete_lines
          p hp hmetric γcC hunitc
        obtain ⟨aD,haD,heqD⟩ := actual_developed_geodesic_preimage_is_union_complete_lines
          p hp hmetric γdC hunitd
        let lines : ({z : H2 // p z∈Set.range γcC} ⊕ {z : H2 // p z∈Set.range γdC}) → ℝ → H2 :=
          Sum.elim aC aD
        have hlines : ∀ i,Isometry (lines i) := by
          intro i
          cases i with
          | inl i => exact haC i
          | inr i => exact haD i
        have hunion : p ⁻¹' (c.image ∪ d.image)=⋃ i,Set.range (lines i) := by
          rw [←hrangec,←hranged,Set.preimage_union]
          change p ⁻¹' Set.range γcC ∪ p ⁻¹' Set.range γdC = _
          rw [heqC,heqD]
          simp only [Set.iUnion_sum,lines,Sum.elim_inl,Sum.elim_inr]
        have hCeq : C=connectedComponentIn (p ⁻¹' F) x := hid p hp.continuous F x
        have hxF : x∈p ⁻¹' F := hx
        have hFopen : IsOpen (p ⁻¹' F) := hF.preimage hp.continuous
        have hreg : interior (closure C)=C := by
          rw [hCeq]
          dsimp only [F] at hxF hFopen ⊢
          rw [Set.preimage_compl,hunion] at hxF hFopen ⊢
          exact hregular lines hlines x hxF hFopen
        have hconv : ∀y∈C,∀z∈C,∀w : H2,dist y w+dist w z=dist y z → w∈C := by
          rw [hCeq]
          dsimp only [F]
          rw [Set.preimage_compl,hunion]
          exact actual_complete_geodesic_complement_component_metric_convex lines hlines x
        exact ⟨(hU.preimage hp.continuous).connectedComponentIn,hreg,hconv⟩
      have hHorizontal
          {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
          (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
          (hc : Essential c) (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
          (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
          (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image)
          (hcd : Disjoint c.image d.image)
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (hmetric : ∀x : H2,∃W : Set H2,IsOpen W ∧ x∈W ∧
            ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z)
          (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
          (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
          (hpunct : h (1,1)=r) (hr : r.2≠1)
          (f : {x : U // x.val∉d.image} ≃ₜ ActualPuncturedCylinder)
          (q : {z : Circle // z≠1} ≃ₜ ℝ)
          (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
            (f x).val=(r.1⁻¹*(h (e x.val).val).1,
              q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
          (x : H2) (hx : p x∈U\d.image) :
          letI := a
          let D := connectedComponentIn (p ⁻¹' (U\d.image)) x
          let K := MulAction.stabilizer G D
          ∀b : MulAction K D,
          ∀cov : D → {z : U // z.val∉d.image},
          ∀hcov : letI := b;IsQuotientCoveringMap cov K,
          ∀hproj : ∀z,(cov z).val.val=p z.val,
          ∀hact : ∀k z,(@SMul.smul K D b.toSMul k z).val=
            @SMul.smul G H2 a.toSMul k.val z.val,
          ∀hsc : SimplyConnectedSpace D,
          ∀o : cov ⁻¹' {f.symm actualPantsBase},
          ∀B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,
          (∀i : Fin 2,
            let ε : ℝ := if i=0 then -1 else 1
            let hε : ε≠0 := by dsimp [ε];split <;> norm_num
            let chart : C(ActualPuncturedCylinder,{z : U // z.val∉d.image}) := ⟨f.symm,f.symm.continuous⟩
            let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
            let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
            @SMul.smul K D b.toSMul (B (FreeGroup.of i)).unop
              (hcov.isCoveringMap.monodromy stem o).val=
              (hcov.isCoveringMap.monodromy loop (hcov.isCoveringMap.monodromy stem o)).val) →
          ∃γ : G,γ*(B (FreeGroup.of 0)).unop.val*γ⁻¹=(B (FreeGroup.of 1)).unop.val := by
        letI := a
        intro D K b cov hcov hproj hact hsc o B hB
        letI := b
        let chartPoint (z : ActualPuncturedCylinder) : Circle × Circle :=
          h (e (f.symm z).val).val
        have hcoord (z : ActualPuncturedCylinder) :
            (chartPoint z).1 = r.1 * z.val.1 ∧
            ∃hz : (chartPoint z).2 ≠ 1,
              q ⟨(chartPoint z).2, hz⟩ - q ⟨r.2, hr⟩ = z.val.2 := by
          obtain ⟨hz,heq⟩ := hf (f.symm z)
          have heq' : z.val = (r.1⁻¹ * (chartPoint z).1,
              q ⟨(chartPoint z).2, hz⟩ - q ⟨r.2, hr⟩) := by
            simpa only [f.apply_symm_apply] using heq
          constructor
          · have hh := congrArg Prod.fst heq'
            dsimp only at hh
            calc
              (chartPoint z).1 = r.1 * (r.1⁻¹ * (chartPoint z).1) := by group
              _ = r.1 * z.val.1 := by rw [← hh]
          · exact ⟨hz, (congrArg Prod.snd heq').symm⟩
        let v (ε : ℝ) (hε : ε ≠ 0) : Circle :=
          (chartPoint (actualPantsLevelPoint ε hε)).2
        have hv (ε : ℝ) (hε : ε ≠ 0) : v ε hε ≠ r.2 := by
          obtain ⟨_, hz, heq⟩ := hcoord (actualPantsLevelPoint ε hε)
          intro he
          have hqeq : q ⟨v ε hε, hz⟩ = q ⟨r.2, hr⟩ :=
            congrArg q (Subtype.ext he)
          have heps : (actualPantsLevelPoint ε hε).val.2 = ε := rfl
          dsimp only [v] at hqeq heq
          rw [hqeq, sub_self] at heq
          exact hε (heps ▸ heq.symm)
        let ε₀ : ℝ := -1
        let ε₁ : ℝ := 1
        have hε₀ : ε₀ ≠ 0 := by norm_num [ε₀]
        have hε₁ : ε₁ ≠ 0 := by norm_num [ε₁]
        have hjoin : JoinedIn ({r.2}ᶜ : Set Circle) (v ε₀ hε₀) (v ε₁ hε₁) :=
          (Circle.isPathConnected_compl_singleton r.2).joinedIn _
            (by simpa using hv ε₀ hε₀) _ (by simpa using hv ε₁ hε₁)
        let θ : Path (v ε₀ hε₀) (v ε₁ hε₁) := hjoin.somePath
        have hθ (s : unitInterval) : θ s ≠ r.2 := by
          change hjoin.somePath s ≠ r.2
          exact hjoin.somePath_mem s
        let T : C(Circle × unitInterval, {z : Circle × Circle // z ≠ r}) :=
          ⟨fun zs => ⟨(r.1 * (-(1 : Circle) * zs.1), θ zs.2), by
            intro he
            exact hθ zs.2 (congrArg Prod.snd he)⟩, by fun_prop⟩
        have hrback (z : {z : Circle × Circle // z ≠ r}) : h.symm z.val ≠ (1, 1) := by
          intro he
          apply z.property
          calc
            z.val = h (h.symm z.val) := (h.apply_symm_apply _).symm
            _ = r := by rw [he, hpunct]
        let back : C({z : Circle × Circle // z ≠ r},
            {z : Circle × Circle // z ≠ (1, 1)}) :=
          ⟨fun z => ⟨h.symm z.val, hrback z⟩, by fun_prop⟩
        let J : C({z : Circle × Circle // z ≠ r}, E) :=
          ⟨fun z => (e.symm (back z)).val, by fun_prop⟩
        let movie : C(Circle × unitInterval, E) := J.comp T
        have hmovieU (z : Circle) (s : unitInterval) : movie (z, s) ∈ U := by
          change (e.symm (back (T (z, s)))).val ∈ U
          exact (e.symm (back (T (z, s)))).property
        have hloopcoord (ε : ℝ) (hε : ε ≠ 0) (t : unitInterval) :
            chartPoint (actualPantsHorizontalLoop ε hε t) =
              (r.1 * (-(1 : Circle) * Circle.exp (2 * Real.pi * (t : ℝ))), v ε hε) := by
          obtain ⟨hfirst, hz, heq⟩ := hcoord (actualPantsHorizontalLoop ε hε t)
          obtain ⟨_, hz₀, heq₀⟩ := hcoord (actualPantsLevelPoint ε hε)
          have heq' : q ⟨(chartPoint (actualPantsHorizontalLoop ε hε t)).2, hz⟩ =
              q ⟨v ε hε, hz₀⟩ := by
            dsimp only [v] at heq₀ ⊢
            change q ⟨_, hz⟩ - q ⟨r.2, hr⟩ = ε at heq
            change q ⟨_, hz₀⟩ - q ⟨r.2, hr⟩ = ε at heq₀
            linarith
          have hsecond : (chartPoint (actualPantsHorizontalLoop ε hε t)).2 = v ε hε :=
            congrArg Subtype.val (q.injective heq')
          apply Prod.ext
          · convert hfirst using 1 <;> rfl
          · exact hsecond
        have hJ (z : ActualPuncturedCylinder) (w : {z : Circle × Circle // z ≠ r})
            (hw : w.val = chartPoint z) : J w = (f.symm z).val.val := by
          have he : back w = e (f.symm z).val := by
            apply Subtype.ext
            change h.symm w.val = (e (f.symm z).val).val
            rw [hw]
            exact h.symm_apply_apply _
          change (e.symm (back w)).val = (f.symm z).val.val
          rw [he, e.symm_apply_apply]
        have hmovie₀ (t : unitInterval) :
            movie (Circle.exp (2 * Real.pi * (t : ℝ)), 0) =
              (f.symm (actualPantsHorizontalLoop ε₀ hε₀ t)).val.val := by
          apply hJ
          change (r.1 * (-(1 : Circle) * Circle.exp (2 * Real.pi * (t : ℝ))), θ 0) =
            chartPoint (actualPantsHorizontalLoop ε₀ hε₀ t)
          rw [θ.source]
          exact (hloopcoord ε₀ hε₀ t).symm
        have hmovie₁ (t : unitInterval) :
            movie (Circle.exp (2 * Real.pi * (t : ℝ)), 1) =
              (f.symm (actualPantsHorizontalLoop ε₁ hε₁ t)).val.val := by
          apply hJ
          change (r.1 * (-(1 : Circle) * Circle.exp (2 * Real.pi * (t : ℝ))), θ 1) =
            chartPoint (actualPantsHorizontalLoop ε₁ hε₁ t)
          rw [θ.target]
          exact (hloopcoord ε₁ hε₁ t).symm
        let inc : C({z : U // z.val ∉ d.image}, E) :=
          ⟨fun z => z.val.val, by fun_prop⟩
        let lift : C(D, H2) := ⟨Subtype.val, continuous_subtype_val⟩
        have hcomm (z : D) : p (lift z) = inc (cov z) := (hproj z).symm
        have hnat {v : {z : U // z.val ∉ d.image}}
            (z : D) (P : Path.Homotopic.Quotient (cov z) v) :
            (hq.isCoveringMap.monodromy (P.map inc) ⟨z.val, hcomm z⟩).val =
              (hcov.isCoveringMap.monodromy P ⟨z, rfl⟩).val.val := by
          obtain ⟨P⟩ := P
          let L := hcov.isCoveringMap.liftPath P z P.source
          have heq : lift ∘ L = hq.isCoveringMap.liftPath (P.map inc.continuous) z.val
              ((P.map inc.continuous).source.trans (hcomm z).symm) := by
            apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
            refine ⟨lift.continuous.comp L.continuous, ?_, ?_⟩
            · funext t
              change p (L t).val = (P t).val.val
              rw [←hproj (L t)]
              exact congrArg (fun z : {z : U // z.val ∉ d.image} => z.val.val)
                (congrFun (hcov.isCoveringMap.liftPath_lifts P z P.source) t)
            · change (L 0).val = z.val
              rw [hcov.isCoveringMap.liftPath_zero]
          change hq.isCoveringMap.liftPath (P.map inc.continuous) z.val _ 1 = (L 1).val
          exact (congrFun heq 1).symm
        have hnat' {u v : {z : U // z.val ∉ d.image}}
            (z : D) (P : Path.Homotopic.Quotient u v) (hz : cov z = u) :
            (hq.isCoveringMap.monodromy (P.map inc)
              ⟨z.val, by rw [←hz]; exact hcomm z⟩).val =
              (hcov.isCoveringMap.monodromy P ⟨z, hz⟩).val.val := by
          subst u
          exact hnat z P
        have hmono (i : Fin 2) :
            let ε : ℝ := if i = 0 then -1 else 1
            let hε : ε ≠ 0 := by dsimp [ε]; split <;> norm_num
            let chart : C(ActualPuncturedCylinder, {z : U // z.val ∉ d.image}) :=
              ⟨f.symm, f.symm.continuous⟩
            let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
            let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
            let z := (hcov.isCoveringMap.monodromy stem o).val
            @SMul.smul G H2 a.toSMul (B (FreeGroup.of i)).unop.val z.val =
              (hq.isCoveringMap.monodromy (loop.map inc)
                ⟨z.val, by
                  have hz : cov z = f.symm (actualPantsLevelPoint ε hε) := by
                    have hp := (hcov.isCoveringMap.monodromy stem o).property
                    change cov z = f.symm (actualPantsLevelPoint ε hε) at hp
                    exact hp
                  exact (hcomm z).trans (congrArg inc hz)⟩).val := by
          intro ε hε chart stem loop z
          have hz : cov z = f.symm (actualPantsLevelPoint ε hε) := by
            have hp := (hcov.isCoveringMap.monodromy stem o).property
            change cov z = f.symm (actualPantsLevelPoint ε hε) at hp
            exact hp
          have hi := hB i
          change @SMul.smul K D b.toSMul (B (FreeGroup.of i)).unop z =
            (hcov.isCoveringMap.monodromy loop ⟨z, hz⟩).val at hi
          calc
            @SMul.smul G H2 a.toSMul (B (FreeGroup.of i)).unop.val z.val =
                (@SMul.smul K D b.toSMul (B (FreeGroup.of i)).unop z).val :=
              (hact _ z).symm
            _ = (hcov.isCoveringMap.monodromy loop ⟨z, hz⟩).val.val :=
              congrArg Subtype.val hi
            _ = (hq.isCoveringMap.monodromy (loop.map inc)
                ⟨z.val, (hcomm z).trans (congrArg inc hz)⟩).val :=
              (hnat' z loop hz).symm
        let f₀ : C(Circle, E) := ⟨fun z => movie (z, 0), by fun_prop⟩
        let f₁ : C(Circle, E) := ⟨fun z => movie (z, 1), by fun_prop⟩
        let chart : C(ActualPuncturedCylinder, {z : U // z.val ∉ d.image}) :=
          ⟨f.symm, f.symm.continuous⟩
        let stem₀ := Path.Homotopic.Quotient.map ⟦actualPantsStem ε₀ hε₀⟧ chart
        let stem₁ := Path.Homotopic.Quotient.map ⟦actualPantsStem ε₁ hε₁⟧ chart
        let z₀ := (hcov.isCoveringMap.monodromy stem₀ o).val
        let z₁ := (hcov.isCoveringMap.monodromy stem₁ o).val
        have hz₀ : cov z₀ = f.symm (actualPantsLevelPoint ε₀ hε₀) := by
          have hp := (hcov.isCoveringMap.monodromy stem₀ o).property
          change cov z₀ = f.symm (actualPantsLevelPoint ε₀ hε₀) at hp
          exact hp
        have hz₁ : cov z₁ = f.symm (actualPantsLevelPoint ε₁ hε₁) := by
          have hp := (hcov.isCoveringMap.monodromy stem₁ o).property
          change cov z₁ = f.symm (actualPantsLevelPoint ε₁ hε₁) at hp
          exact hp
        have hstart₀ : f₀ 1 = inc (f.symm (actualPantsLevelPoint ε₀ hε₀)) := by
          simpa [f₀, inc, actualPantsHorizontalLoop] using hmovie₀ 0
        have hstart₁ : f₁ 1 = inc (f.symm (actualPantsLevelPoint ε₁ hε₁)) := by
          simpa [f₁, inc, actualPantsHorizontalLoop] using hmovie₁ 0
        have hp₀ : p z₀.val = f₀ 1 := by
          calc
            p z₀.val = inc (cov z₀) := hcomm z₀
            _ = inc (f.symm (actualPantsLevelPoint ε₀ hε₀)) := congrArg inc hz₀
            _ = f₀ 1 := hstart₀.symm
        obtain ⟨δ, η, y, hy, _, heq, hδmono, hηmono⟩ :=
          actual_free_homotopy_integer_meridian_supplied_root_same_component
            a p hq f₀ f₁ 1 movie (by intro z; rfl)
            (by intro z; simp [f₁]) U hmovieU z₀.val hp₀
        have hcast {u w : E} (hu : u = w) (P : Path w w) (v : H2) (hv : p v = w) :
            (hq.isCoveringMap.monodromy ⟦P.cast hu hu⟧ ⟨v, hv.trans hu.symm⟩).val =
              (hq.isCoveringMap.monodromy ⟦P⟧ ⟨v, hv⟩).val := by
          cases hu
          rfl
        let raw₀ : Path (inc (f.symm (actualPantsLevelPoint ε₀ hε₀)))
            (inc (f.symm (actualPantsLevelPoint ε₀ hε₀))) :=
          (actualPantsHorizontalLoop ε₀ hε₀).map (inc.comp chart).continuous
        let raw₁ : Path (inc (f.symm (actualPantsLevelPoint ε₁ hε₁)))
            (inc (f.symm (actualPantsLevelPoint ε₁ hε₁))) :=
          (actualPantsHorizontalLoop ε₁ hε₁).map (inc.comp chart).continuous
        have hraw₀ (t : unitInterval) :
            (raw₀.cast hstart₀ hstart₀) t = f₀ (Circle.exp (2 * Real.pi * (t : ℝ))) := by
          exact (hmovie₀ t).symm
        have hraw₁ (t : unitInterval) :
            (raw₁.cast hstart₁ hstart₁) t = f₁ (Circle.exp (2 * Real.pi * (t : ℝ))) := by
          exact (hmovie₁ t).symm
        have hδpoint := hδmono (raw₀.cast hstart₀ hstart₀) hraw₀
        have hηpoint := hηmono (raw₁.cast hstart₁ hstart₁) hraw₁
        have hz₀ambient : p z₀.val = inc (f.symm (actualPantsLevelPoint ε₀ hε₀)) :=
          (hcomm z₀).trans (congrArg inc hz₀)
        have hz₁ambient : p z₁.val = inc (f.symm (actualPantsLevelPoint ε₁ hε₁)) :=
          (hcomm z₁).trans (congrArg inc hz₁)
        have hm₀ :
            @SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z₀.val =
              (hq.isCoveringMap.monodromy ⟦raw₀⟧ ⟨z₀.val, hz₀ambient⟩).val := by
          have hh := hmono 0
          change @SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z₀.val =
            (hq.isCoveringMap.monodromy ⟦raw₀⟧ ⟨z₀.val, hz₀ambient⟩).val at hh
          exact hh
        have hm₁ :
            @SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val z₁.val =
              (hq.isCoveringMap.monodromy ⟦raw₁⟧ ⟨z₁.val, hz₁ambient⟩).val := by
          have hh := hmono 1
          change @SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val z₁.val =
            (hq.isCoveringMap.monodromy ⟦raw₁⟧ ⟨z₁.val, hz₁ambient⟩).val at hh
          exact hh
        have hδaction :
            @SMul.smul G H2 a.toSMul δ z₀.val =
              @SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z₀.val := by
          calc
            @SMul.smul G H2 a.toSMul δ z₀.val =
                (hq.isCoveringMap.monodromy ⟦raw₀.cast hstart₀ hstart₀⟧ ⟨z₀.val, hp₀⟩).val :=
              hδpoint
            _ = (hq.isCoveringMap.monodromy ⟦raw₀⟧ ⟨z₀.val, hz₀ambient⟩).val :=
              hcast hstart₀ raw₀ z₀.val hz₀ambient
            _ = @SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z₀.val := hm₀.symm
        have hδeq : δ = (B (FreeGroup.of 0)).unop.val := by
          letI := hq.isCancelSMul
          exact IsCancelSMul.right_cancel' δ _ z₀.val hδaction
        have hyambient : p y = inc (f.symm (actualPantsLevelPoint ε₁ hε₁)) :=
          hy.trans hstart₁
        have hηaction :
            @SMul.smul G H2 a.toSMul η y =
              (hq.isCoveringMap.monodromy ⟦raw₁⟧ ⟨y, hyambient⟩).val := by
          calc
            @SMul.smul G H2 a.toSMul η y =
                (hq.isCoveringMap.monodromy ⟦raw₁.cast hstart₁ hstart₁⟧ ⟨y, hy⟩).val :=
              hηpoint
            _ = (hq.isCoveringMap.monodromy ⟦raw₁⟧ ⟨y, hyambient⟩).val :=
              hcast hstart₁ raw₁ y hyambient
        obtain ⟨γ, hγ⟩ := hq.exists_toPermFiber_eq ⟨y, hyambient⟩ ⟨z₁.val, hz₁ambient⟩
        have hγval : @SMul.smul G H2 a.toSMul γ y = z₁.val :=
          congrArg Subtype.val hγ
        have htransport :
            @SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val
                (@SMul.smul G H2 a.toSMul γ y) =
              @SMul.smul G H2 a.toSMul γ (@SMul.smul G H2 a.toSMul η y) := by
          calc
            @SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val
                (@SMul.smul G H2 a.toSMul γ y) =
                (hq.isCoveringMap.monodromy ⟦raw₁⟧ ⟨z₁.val, hz₁ambient⟩).val := by
              rw [hγval]
              exact hm₁
            _ = @SMul.smul G H2 a.toSMul γ
                (hq.isCoveringMap.monodromy ⟦raw₁⟧ ⟨y, hyambient⟩).val := by
              have hh := hq.monodromy_toPermFiber (g := γ)
                (γ := (⟦raw₁⟧ : Path.Homotopic.Quotient _ _))
                (e := (⟨y, hyambient⟩ : p ⁻¹' {inc (f.symm (actualPantsLevelPoint ε₁ hε₁))}))
              rw [hγ] at hh
              exact congrArg Subtype.val hh
            _ = @SMul.smul G H2 a.toSMul γ (@SMul.smul G H2 a.toSMul η y) := by
              rw [hηaction]
        have hgroup : (B (FreeGroup.of 1)).unop.val * γ = γ * η := by
          letI := hq.isCancelSMul
          apply IsCancelSMul.right_cancel' _ _ y
          change @SMul.smul G H2 a.toSMul ((B (FreeGroup.of 1)).unop.val * γ) y =
            @SMul.smul G H2 a.toSMul (γ * η) y
          calc
            @SMul.smul G H2 a.toSMul ((B (FreeGroup.of 1)).unop.val * γ) y =
                @SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val
                  (@SMul.smul G H2 a.toSMul γ y) := a.mul_smul _ _ _
            _ = @SMul.smul G H2 a.toSMul γ (@SMul.smul G H2 a.toSMul η y) := htransport
            _ = @SMul.smul G H2 a.toSMul (γ * η) y := (a.mul_smul _ _ _).symm
        have hηδ : η = δ := by simpa using heq
        refine ⟨γ, ?_⟩
        calc
          γ * (B (FreeGroup.of 0)).unop.val * γ⁻¹ = γ * η * γ⁻¹ := by
            rw [←hδeq, ←hηδ]
          _ = (B (FreeGroup.of 1)).unop.val := by
            calc
              γ * η * γ⁻¹ = ((B (FreeGroup.of 1)).unop.val * γ) * γ⁻¹ := by rw [hgroup]
              _ = (B (FreeGroup.of 1)).unop.val := by group
      have hDictionary {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
          (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
          (hc : Essential c) (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
          (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
          (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image)
          (hcd : Disjoint c.image d.image)
          (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (hmetric : ∀x : H2,∃W : Set H2,IsOpen W ∧ x∈W ∧
            ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z)
          (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
          (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
          (hpunct : h (1,1)=r) (hr : r.2≠1)
          (f : {x : U // x.val∉d.image} ≃ₜ ActualPuncturedCylinder)
          (q : {z : Circle // z≠1} ≃ₜ ℝ)
          (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
            (f x).val=(r.1⁻¹*(h (e x.val).val).1,
              q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
          (hcdiv : DividingCurve c)
          (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
          (hdnondiv : ¬DividingCurve d) (hfrontV : frontier V=c.image) (hdU : d.image⊆U)
          (hcore : h '' ((fun x : U => (e x).val) '' {x : U | x.val∈d.image})=
            {z : Circle×Circle | z.2=1})
          (x : H2) (hx : p x∈U\d.image) :
          letI := a
          let D := connectedComponentIn (p ⁻¹' (U\d.image)) x
          let K := MulAction.stabilizer G D
          ∀b : MulAction K D,
          ∀cov : D → {z : U // z.val∉d.image},
          ∀hcov : letI := b;IsQuotientCoveringMap cov K,
          ∀hproj : ∀z,(cov z).val.val=p z.val,
          ∀hact : ∀k z,(@SMul.smul K D b.toSMul k z).val=
            @SMul.smul G H2 a.toSMul k.val z.val,
          ∀hsc : SimplyConnectedSpace D,
          ∀hreg : interior (closure D)=D,
          ∀hconv : ∀y∈D,∀z∈D,∀w : H2,dist y w+dist w z=dist y z → w∈D,
          ∀o : cov ⁻¹' {f.symm actualPantsBase},
          ∃B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,
          ∃αc α₀ α₁ : C(ℝ,H2),Isometry αc ∧ Isometry α₀ ∧ Isometry α₁ ∧
          ∃Tc T₀ T₁ : ℝ,0<Tc ∧ 0<T₀ ∧ 0<T₁ ∧
            range αc⊆frontier D ∧ range α₀⊆frontier D ∧ range α₁⊆frontier D ∧
            p '' range αc=c.image ∧ p '' range α₀=d.image ∧ p '' range α₁=d.image ∧
            (∀s t : ℝ,p (αc s)=p (αc t) ↔ ∃k : ℤ,s=t+k*Tc) ∧
            (∀s t : ℝ,p (α₀ s)=p (α₀ t) ↔ ∃k : ℤ,s=t+k*T₀) ∧
            (∀s t : ℝ,p (α₁ s)=p (α₁ t) ↔ ∃k : ℤ,s=t+k*T₁) ∧
            (fun z => @SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z) '' range α₀=range α₀ ∧
            (fun z => @SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val z) '' range α₁=range α₁ ∧
            (fun z => @SMul.smul G H2 a.toSMul
              (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val z) '' range αc=range αc ∧
            (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α₀=range α₀ →
              ∃n : ℤ,g=((B (FreeGroup.of 0)).unop.val)^n) ∧
            (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α₁=range α₁ →
              ∃n : ℤ,g=((B (FreeGroup.of 1)).unop.val)^n) ∧
            (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range αc=range αc →
              ∃n : ℤ,g=((B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val)^n) ∧
            ((∀t : ℝ,@SMul.smul G H2 a.toSMul (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val (αc t)=αc (t+Tc)) ∨
              (∀t : ℝ,@SMul.smul G H2 a.toSMul ((B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val)⁻¹ (αc t)=αc (t+Tc))) ∧
            (∀k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀≠range α₁) ∧
            (∀k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀≠range αc) ∧
            (∀k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₁≠range αc) ∧
            frontier D=(⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range αc) ∪
              (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀) ∪
              (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₁) ∧ T₀=T₁ ∧
            ∃ε : ℝ,0<ε ∧ (∀s t : ℝ,ε ≤ dist (α₀ s) (α₁ t)) ∧
            ((∀t : ℝ,@SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val (α₀ t)=α₀ (t+T₀)) ∨
             (∀t : ℝ,@SMul.smul G H2 a.toSMul ((B (FreeGroup.of 0)).unop.val)⁻¹ (α₀ t)=α₀ (t+T₀))) ∧
            ((∀t : ℝ,@SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val (α₁ t)=α₁ (t+T₁)) ∨
             (∀t : ℝ,@SMul.smul G H2 a.toSMul ((B (FreeGroup.of 1)).unop.val)⁻¹ (α₁ t)=α₁ (t+T₁))) ∧
            let Dmat : ℝ → SL(2,ℝ) := fun s =>
              ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let Rmat : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
            ∃dn : ℝ,0 < dn ∧ ∃g : SL(2,ℝ),∃L₀ L₁ : ℝ,
              (L₀=T₀ ∨ L₀=-T₀) ∧ (L₁=T₁ ∨ L₁=-T₁) ∧
              (fun z : H2 => g • z) '' range α₀=range (fun t => Dmat (-dn/2) • (Rmat • verticalPath t)) ∧
              (fun z : H2 => g • z) '' range α₁=range (fun t => Dmat (dn/2) • (Rmat • verticalPath t)) ∧
              (∀z : H2,g • (@SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z)=
                ((Dmat (-dn/2)*Rmat)*Dmat L₀*(Dmat (-dn/2)*Rmat)⁻¹) • (g • z)) ∧
              (∀z : H2,g • (@SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val z)=
                ((Dmat (dn/2)*Rmat)*Dmat L₁*(Dmat (dn/2)*Rmat)⁻¹) • (g • z)) ∧
              ∃Lc εc : ℝ,Lc≠0 ∧ 0 < εc ∧
                (∀t : ℝ,@SMul.smul G H2 a.toSMul
                  (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val (αc t)=αc (t+Lc)) ∧
                (∀z : H2,εc ≤ dist z (@SMul.smul G H2 a.toSMul
                  (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val z)) ∧
              let eN : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
              let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
              let Anorm := Dmat (-dn/2)*Rmat*Dmat L₀*Rmat⁻¹*Dmat (dn/2)
              let Bnorm := Dmat (dn/2)*Rmat*Dmat L₁*Rmat⁻¹*Dmat (-dn/2)
              L₁=L₀ ∧ ∃ρ : K →* SL(2,ℝ),ρ (B (FreeGroup.of 0)).unop=Anorm ∧
                ρ (B (FreeGroup.of 1)).unop=Bnorm ∧
                ρ.range=Subgroup.closure ({Anorm,Bnorm}:Set SL(2,ℝ)) ∧
                (∀k : K,∀z : H2,eN (@SMul.smul G H2 a.toSMul k.val z)=ρ k • eN z) ∧
                eN.symm UpperHalfPlane.I∈D ∧
                (fun z : H2 => eN.symm (J • eN z)) '' D=D ∧
                ∃γ : G,γ*(B (FreeGroup.of 0)).unop.val*γ⁻¹=(B (FreeGroup.of 1)).unop.val := by
        have hPeriods {P E G : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E] [Group G]
            (a : MulAction G P) (p : P → E)
            (hq : letI := a;IsQuotientCoveringMap p G)
            (hiso : ∀g : G,Isometry (fun z => @SMul.smul G P a.toSMul g z))
            (hproj : ∀g : G,∀z : P,p (@SMul.smul G P a.toSMul g z)=p z)
            (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
            (T U : ℝ) (hT : 0<T) (hU : 0<U)
            (hαfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
            (hβfibre : ∀s t : ℝ,p (β s)=p (β t) ↔ ∃n : ℤ,s=t+n*U)
            (himage : p '' range α=p '' range β) : T=U := by
          letI := a
          have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (hmeet : (range α∩range β).Nonempty) : range β=range α := by
            have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
                (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
                (himage : p '' range β⊆p '' range α)
                (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
              have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                  (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                  (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                  ∃f : C(Circle,E),IsEmbedding f ∧
                    (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                    range f=p '' range α := by
                classical
                let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
                have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
                let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
                have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                  apply (hfibre _ _).mpr
                  refine ⟨k,?_⟩
                  rw [hk]
                  field_simp
                have hψ : Continuous ψ := by
                  apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                  have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                  rw [heq]
                  fun_prop
                let f : C(Circle,E) := ⟨ψ,hψ⟩
                have hfinj : Function.Injective f := by
                  intro z w hzw
                  obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                  have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                    have hπ : (2*Real.pi)≠0 := by positivity
                    have hT' : T≠0 := hT.ne'
                    field_simp at hk
                    nlinarith
                  rw [←hθ z,←hθ w]
                  exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
                have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                  change _=ψ _
                  rw [hfac]
                  congr 2
                  field_simp
                refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
                apply Subset.antisymm
                · rintro y ⟨z,rfl⟩
                  exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
                · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                  exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
              obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
              change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
              let e : Circle ≃ₜ range f := hf.toHomeomorph
              let g : C(ℝ,Circle) :=
                ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                  exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
              let θ₀ := 2*Real.pi*s₀/T
              have hbase : Circle.exp θ₀=g t₀ := by
                apply e.injective
                apply Subtype.ext
                change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
                rw [e.apply_symm_apply]
                change f (Circle.exp θ₀)=p (β t₀)
                rw [←hparam,hmeet]
              obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
              have hL0 : L t₀=θ₀ := hL.1
              have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
              let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
              have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
                intro t
                change p (α (T*L t/(2*Real.pi)))=_
                rw [hparam]
                have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
                rw [harg,hLe]
                exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                  rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
              have hℓbase : ℓ t₀=β t₀ := by
                change α (T*L t₀/(2*Real.pi))=β t₀
                rw [hL0]
                have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
                rw [harg,hmeet]
              have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
                (funext hℓproj) t₀ hℓbase
              rintro y ⟨t,rfl⟩
              exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
            have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
                (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
                range β=range α := by
              let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
              let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
              have hfac (t : ℝ) : α (f t)=β t :=
                congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
              have hf : Isometry f := by
                apply isometry_iff_dist_eq.mpr
                intro s t
                rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
              let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
              have hLin : Function.Injective A.toAffineMap.linear :=
                A.toAffineMap.linear_injective_iff.mpr hf.injective
              have hSur : Function.Surjective A.toAffineMap.linear :=
                LinearMap.surjective_of_injective hLin
              have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
              apply Subset.antisymm hsub
              rintro y ⟨t,rfl⟩
              obtain ⟨s,hs⟩ := hfsur t
              exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
            obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
            have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
              s t (hs.trans ht.symm)
            exact hLine α β hα hβ hsub
          have hPeriodLe (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
              (T U : ℝ) (hT : 0<T) (hU : 0<U)
              (hf : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
              (hb : p (β U)=p (β 0)) (hr : range α=range β) : T≤U := by
            have hmU : β U∈range α := by rw [hr];exact mem_range_self U
            have hm0 : β 0∈range α := by rw [hr];exact mem_range_self 0
            obtain ⟨s,hs⟩ := hmU
            obtain ⟨t,ht⟩ := hm0
            have heq : p (α s)=p (α t) := by rw [hs,ht];exact hb
            obtain ⟨n,hn⟩ := (hf s t).mp heq
            have hdist : |s-t|=U := by
              have hd := hα.dist_eq s t
              rw [hs,ht,hβ.dist_eq] at hd
              simpa [Real.dist_eq,abs_of_nonneg hU.le] using hd.symm
            have habs : |(n:ℝ)| * T=U := by
              rw [hn,add_sub_cancel_left,abs_mul,abs_of_pos hT] at hdist
              exact hdist
            have hnzero : n≠0 := by intro hn0;subst n;norm_num at habs;linarith
            have hnOne : (1:ℤ) ≤ |n| := by
              have hh : (0:ℤ) < |n| := abs_pos.mpr hnzero
              omega
            have hnOneReal : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast hnOne
            nlinarith
          have hpoint : p (β 0)∈p '' range α := himage ▸ ⟨β 0,mem_range_self 0,rfl⟩
          obtain ⟨_,⟨s,rfl⟩,hs⟩ := hpoint
          obtain ⟨g,hg⟩ := hq.exists_toPermFiber_eq
            (⟨α s,hs⟩ : p ⁻¹' {p (β 0)}) ⟨β 0,rfl⟩
          have hgpoint : @SMul.smul G P a.toSMul g (α s)=β 0 := congrArg Subtype.val hg
          let γ : ℝ → P := fun t => @SMul.smul G P a.toSMul g (α t)
          have hγ : Isometry γ := (hiso g).comp hα
          have hγfibre : ∀s t : ℝ,p (γ s)=p (γ t) ↔ ∃n : ℤ,s=t+n*T := by
            intro s t;simpa only [γ,hproj] using hαfibre s t
          have hγimage : p '' range β⊆p '' range γ := by
            rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
            have hh : p (β t)∈p '' range α := himage ▸ ⟨β t,mem_range_self t,rfl⟩
            obtain ⟨_,⟨r,rfl⟩,hr⟩ := hh
            exact ⟨γ r,mem_range_self r,(hproj g (α r)).trans hr⟩
          have hr : range β=range γ := hMeet p hq.isCoveringMap γ β hγ hβ T hT hγfibre hγimage
            ⟨β 0,⟨s,hgpoint⟩,mem_range_self 0⟩
          apply le_antisymm
          · exact hPeriodLe γ β hγ hβ T U hT hU hγfibre
              ((hβfibre U 0).mpr ⟨1,by ring⟩) hr.symm
          · exact hPeriodLe β γ hβ hγ U T hU hT hβfibre
              ((hγfibre T 0).mpr ⟨1,by ring⟩) hr
        have hSeparation {P E G : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E] [Group G]
            (a : MulAction G P) (p : P → E)
            (hq : letI := a;IsQuotientCoveringMap p G)
            (hiso : ∀g : G,Isometry (fun z => @SMul.smul G P a.toSMul g z))
            (hproj : ∀g : G,∀z : P,p (@SMul.smul G P a.toSMul g z)=p z)
            (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
            (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
            (δ : G) (hδ : ∀t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T))
            (himage : p '' range β=p '' range α) (hne : range β≠range α) :
            ∃ε : ℝ,0<ε ∧ ∀s t : ℝ,ε≤dist (α s) (β t) := by
          letI := a
          have hClosed {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α : ℝ → P) (hα : Isometry α)
              (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T) :
              IsClosed (p ⁻¹' (p '' range α) \ range α) := by
            have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                ∃f : C(Circle,E),IsEmbedding f ∧
                  (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                  range f=p '' range α := by
              classical
              let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
              have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
              let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
              have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                apply (hfibre _ _).mpr
                refine ⟨k,?_⟩
                rw [hk]
                field_simp
              have hψ : Continuous ψ := by
                apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                rw [heq]
                fun_prop
              let f : C(Circle,E) := ⟨ψ,hψ⟩
              have hfinj : Function.Injective f := by
                intro z w hzw
                obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                  have hπ : (2*Real.pi)≠0 := by positivity
                  have hT' : T≠0 := hT.ne'
                  field_simp at hk
                  nlinarith
                rw [←hθ z,←hθ w]
                exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
              have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                change _=ψ _
                rw [hfac]
                congr 2
                field_simp
              refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
              apply Subset.antisymm
              · rintro y ⟨z,rfl⟩
                exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
              · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
            obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ ⟨α,hα.continuous⟩ T hT hfibre
            change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
            change range f=p '' range α at hrange
            let S := p ⁻¹' range f
            let e : Circle ≃ₜ range f := hf.toHomeomorph
            let pS : S → range f := (range f).restrictPreimage p
            have hpS : IsCoveringMap pS := hp.restrictPreimage (range f)
            let q : S → Circle := e.symm ∘ pS
            have hq : IsCoveringMap q := hpS.homeomorph_comp e.symm
            let αS : ℝ → S := fun t => ⟨α t,by
              change p (α t)∈range f
              rw [hrange]
              exact ⟨α t,mem_range_self t,rfl⟩⟩
            have hαS : Continuous αS := hα.continuous.subtype_mk _
            have hqα (t : ℝ) : q (αS t)=Circle.exp (2*Real.pi*t/T) := by
              apply e.injective
              dsimp only [q,Function.comp_apply]
              rw [e.apply_symm_apply]
              apply Subtype.ext
              change p (α t)=f (Circle.exp (2*Real.pi*t/T))
              exact hparam t
            let c : ℝ := 2*Real.pi/T
            have hc : c≠0 := by dsimp [c];positivity
            let scale : ℝ ≃ₜ ℝ := Homeomorph.mulRight₀ c hc
            have hclock : IsCoveringMap (fun t : ℝ => Circle.exp (2*Real.pi*t/T)) := by
              have hh := Circle.isAddQuotientCoveringMap_exp.isCoveringMap.comp_homeomorph scale
              convert hh using 1
              funext t
              congr 1
              change 2*Real.pi*t/T=t*c
              dsimp [c];ring
            have hcomp : IsLocalHomeomorph (q ∘ αS) := by
              have heq : q ∘ αS=(fun t : ℝ => Circle.exp (2*Real.pi*t/T)) := funext hqα
              rw [heq];exact hclock.isLocalHomeomorph
            have hopen : IsOpen (range αS) :=
              (hcomp.of_comp hq.isLocalHomeomorph hαS).isOpenMap.isOpen_range
            have hSclosed : IsClosed S := (isCompact_range f.continuous).isClosed.preimage hp.continuous
            have hresclosed : IsClosed ((Subtype.val : S → P) '' (range αS)ᶜ) :=
              hSclosed.isClosedMap_subtype_val _ hopen.isClosed_compl
            convert hresclosed using 1
            rw [←hrange]
            ext z
            constructor
            · rintro ⟨hz,hnot⟩
              refine ⟨⟨z,hz⟩,?_,rfl⟩
              rintro ⟨t,ht⟩
              exact hnot ⟨t,congrArg Subtype.val ht⟩
            · rintro ⟨z,hz,rfl⟩
              refine ⟨z.property,?_⟩
              rintro ⟨t,ht⟩
              apply hz
              refine ⟨t,?_⟩
              exact Subtype.ext ht
          have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (hmeet : (range α∩range β).Nonempty) : range β=range α := by
            have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
                (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
                (himage : p '' range β⊆p '' range α)
                (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
              have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                  (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                  (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                  ∃f : C(Circle,E),IsEmbedding f ∧
                    (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                    range f=p '' range α := by
                classical
                let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
                have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
                let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
                have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                  apply (hfibre _ _).mpr
                  refine ⟨k,?_⟩
                  rw [hk]
                  field_simp
                have hψ : Continuous ψ := by
                  apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                  have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                  rw [heq]
                  fun_prop
                let f : C(Circle,E) := ⟨ψ,hψ⟩
                have hfinj : Function.Injective f := by
                  intro z w hzw
                  obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                  have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                    have hπ : (2*Real.pi)≠0 := by positivity
                    have hT' : T≠0 := hT.ne'
                    field_simp at hk
                    nlinarith
                  rw [←hθ z,←hθ w]
                  exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
                have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                  change _=ψ _
                  rw [hfac]
                  congr 2
                  field_simp
                refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
                apply Subset.antisymm
                · rintro y ⟨z,rfl⟩
                  exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
                · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                  exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
              obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
              change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
              let e : Circle ≃ₜ range f := hf.toHomeomorph
              let g : C(ℝ,Circle) :=
                ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                  exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
              let θ₀ := 2*Real.pi*s₀/T
              have hbase : Circle.exp θ₀=g t₀ := by
                apply e.injective
                apply Subtype.ext
                change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
                rw [e.apply_symm_apply]
                change f (Circle.exp θ₀)=p (β t₀)
                rw [←hparam,hmeet]
              obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
              have hL0 : L t₀=θ₀ := hL.1
              have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
              let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
              have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
                intro t
                change p (α (T*L t/(2*Real.pi)))=_
                rw [hparam]
                have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
                rw [harg,hLe]
                exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                  rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
              have hℓbase : ℓ t₀=β t₀ := by
                change α (T*L t₀/(2*Real.pi))=β t₀
                rw [hL0]
                have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
                rw [harg,hmeet]
              have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
                (funext hℓproj) t₀ hℓbase
              rintro y ⟨t,rfl⟩
              exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
            have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
                (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
                range β=range α := by
              let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
              let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
              have hfac (t : ℝ) : α (f t)=β t :=
                congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
              have hf : Isometry f := by
                apply isometry_iff_dist_eq.mpr
                intro s t
                rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
              let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
              have hLin : Function.Injective A.toAffineMap.linear :=
                A.toAffineMap.linear_injective_iff.mpr hf.injective
              have hSur : Function.Surjective A.toAffineMap.linear :=
                LinearMap.surjective_of_injective hLin
              have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
              apply Subset.antisymm hsub
              rintro y ⟨t,rfl⟩
              obtain ⟨s,hs⟩ := hfsur t
              exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
            obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
            have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
              s t (hs.trans ht.symm)
            exact hLine α β hα hβ hsub
          let F := p ⁻¹' (p '' range α) \ range α
          have hFclosed : IsClosed F := hClosed p hq.isCoveringMap α hα T hT hfibre
          have hβF (t : ℝ) : β t∈F := by
            refine ⟨himage ▸ ⟨β t,mem_range_self t,rfl⟩,?_⟩
            intro hm
            apply hne
            exact hMeet p hq.isCoveringMap α β hα hβ T hT hfibre himage.le
              ⟨β t,hm,mem_range_self t⟩
          have hδ' (t : ℝ) : δ • α t=α (t+T) := hδ t
          have hproj' (g : G) (z : P) : p (g • z)=p z := hproj g z
          have hinv (t : ℝ) : δ⁻¹ • α t=α (t-T) := by
            have hh := congrArg (fun z => δ⁻¹ • z) (hδ' (t-T))
            simpa only [inv_smul_smul,sub_add_cancel] using hh.symm
          have hpow (n : ℤ) : ∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
            refine Int.induction_on n ?_ ?_ ?_
            · intro t;simp
            · intro m ih t
              rw [zpow_add,zpow_one,mul_smul,hδ',ih]
              congr 1;push_cast;ring
            · intro m ih t
              rw [zpow_sub,zpow_one,mul_smul,hinv,ih]
              congr 1;push_cast;ring
          have hFpow (n : ℤ) (z : P) (hz : z∈F) : δ^n • z∈F := by
            refine ⟨?_,?_⟩
            · change p (δ^n • z)∈p '' range α
              rw [hproj'];exact hz.1
            · rintro ⟨t,ht⟩
              have hh := congrArg (fun w => δ^(-n) • w) ht
              rw [hpow] at hh
              have hprod : δ^(-n) • (δ^n • z)=z := by rw [←mul_smul,←zpow_add];simp
              rw [hprod] at hh
              exact hz.2 ⟨t+(-n:ℤ)*T,hh⟩
          let Q := α '' Icc 0 T
          have hQcompact : IsCompact Q := isCompact_Icc.image hα.continuous
          have hQne : Q.Nonempty := ⟨α 0,⟨0,⟨le_rfl,hT.le⟩,rfl⟩⟩
          have hQnot (z : P) (hz : z∈Q) : z∉F := by
            obtain ⟨t,ht,rfl⟩ := hz
            exact fun hh => hh.2 (mem_range_self t)
          obtain ⟨z,hz,hmin⟩ := hQcompact.exists_isMinOn hQne (show Continuous (fun z : P => infDist z F) from continuous_infDist_pt F).continuousOn
          have hε : 0 < infDist z F := (hFclosed.notMem_iff_infDist_pos ⟨β 0,hβF 0⟩).mp (hQnot z hz)
          refine ⟨infDist z F,hε,?_⟩
          intro s t
          let n : ℤ := ⌊s/T⌋
          let r : ℝ := s-(n:ℝ)*T
          have hr : r∈Icc 0 T := by
            have hlo := Int.floor_le (s/T)
            have hhi := Int.lt_floor_add_one (s/T)
            change 0 ≤ s-(n:ℝ)*T ∧ s-(n:ℝ)*T ≤ T
            have hd : s/T*T=s := div_mul_cancel₀ s hT.ne'
            constructor <;> dsimp [n] <;> nlinarith
          have hαr : δ^(-n) • α s=α r := by
            rw [hpow];congr 1;dsimp [r];push_cast;ring
          have hbound := infDist_le_dist_of_mem (x := α r) (hFpow (-n) (β t) (hβF t))
          have hlow := hmin (show α r∈Q from ⟨r,hr,rfl⟩)
          have hd := (hiso (δ^(-n))).dist_eq (α s) (β t)
          change dist (δ^(-n) • α s) (δ^(-n) • β t)=dist (α s) (β t) at hd
          rw [hαr] at hd
          exact hlow.trans (hbound.trans_eq hd)
        have hCWord {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
            [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
            (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
            (hc : Essential c) (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
            (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
            (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image)
            (hcd : Disjoint c.image d.image)
            (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
            (hmetric : ∀x : H2,∃W : Set H2,IsOpen W ∧ x∈W ∧
              ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z)
            (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
            (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
            (hpunct : h (1,1)=r) (hr : r.2≠1)
            (f : {x : U // x.val∉d.image} ≃ₜ ActualPuncturedCylinder)
            (q : {z : Circle // z≠1} ≃ₜ ℝ)
            (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
              (f x).val=(r.1⁻¹*(h (e x.val).val).1,
                q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
            (x : H2) (hx : p x∈U\d.image) :
            letI := a
            let D := connectedComponentIn (p ⁻¹' (U\d.image)) x
            let K := MulAction.stabilizer G D
            ∀b : MulAction K D,
            ∀cov : D → {z : U // z.val∉d.image},
            ∀hcov : letI := b;IsQuotientCoveringMap cov K,
            ∀hproj : ∀z,(cov z).val.val=p z.val,
            ∀hact : ∀k z,(@SMul.smul K D b.toSMul k z).val=
              @SMul.smul G H2 a.toSMul k.val z.val,
            ∀hsc : SimplyConnectedSpace D,
            ∀o : cov ⁻¹' {f.symm actualPantsBase},
            ∀B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,
            (∀i : Fin 2,
              let ε : ℝ := if i=0 then -1 else 1
              let hε : ε≠0 := by dsimp [ε];split <;> norm_num
              let chart : C(ActualPuncturedCylinder,{z : U // z.val∉d.image}) := ⟨f.symm,f.symm.continuous⟩
              let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
              let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
              @SMul.smul K D b.toSMul (B (FreeGroup.of i)).unop
                (hcov.isCoveringMap.monodromy stem o).val=
                (hcov.isCoveringMap.monodromy loop (hcov.isCoveringMap.monodromy stem o)).val) →
            ∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
              range α⊆frontier D ∧ p '' range α=c.image ∧
              (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
              (fun z => @SMul.smul G H2 a.toSMul
                (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val z) '' D=D ∧
              (fun z => @SMul.smul G H2 a.toSMul
                (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val z) '' range α=range α ∧
              (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
                ∃n : ℤ,g=((B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val)^n) ∧
              ((∀t : ℝ,@SMul.smul G H2 a.toSMul (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val (α t)=α (t+T)) ∨
                (∀t : ℝ,@SMul.smul G H2 a.toSMul ((B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val)⁻¹ (α t)=α (t+T))) := by
          have hCSource {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
              [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
              (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
              (hc : Essential c) (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
              (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
              (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image)
              (hcd : Disjoint c.image d.image)
              (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
              (hmetric : ∀x : H2,∃W : Set H2,IsOpen W ∧ x∈W ∧
                ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z)
              (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
              (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
              (hpunct : h (1,1)=r) (hr : r.2≠1)
              (f : {x : U // x.val∉d.image} ≃ₜ ActualPuncturedCylinder)
              (q : {z : Circle // z≠1} ≃ₜ ℝ)
              (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
                (f x).val=(r.1⁻¹*(h (e x.val).val).1,
                  q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
              (x : H2) (hx : p x∈U\d.image) :
              letI := a
              let D := connectedComponentIn (p ⁻¹' (U\d.image)) x
              let K := MulAction.stabilizer G D
              ∀b : MulAction K D,
              ∀cov : D → {z : U // z.val∉d.image},
              ∀hcov : letI := b;IsQuotientCoveringMap cov K,
              ∀hproj : ∀z,(cov z).val.val=p z.val,
              ∀hact : ∀k z,(@SMul.smul K D b.toSMul k z).val=
                @SMul.smul G H2 a.toSMul k.val z.val,
              ∀hsc : SimplyConnectedSpace D,
              ∀o : cov ⁻¹' {f.symm actualPantsBase},
              ∀B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,
              (∀i : Fin 2,
                let ε : ℝ := if i=0 then -1 else 1
                let hε : ε≠0 := by dsimp [ε];split <;> norm_num
                let chart : C(ActualPuncturedCylinder,{z : U // z.val∉d.image}) := ⟨f.symm,f.symm.continuous⟩
                let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
                let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
                @SMul.smul K D b.toSMul (B (FreeGroup.of i)).unop
                  (hcov.isCoveringMap.monodromy stem o).val=
                  (hcov.isCoveringMap.monodromy loop (hcov.isCoveringMap.monodromy stem o)).val) →
              ∃δ : G,∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
                range α⊆frontier D ∧ p '' range α=c.image ∧
                (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
                (fun z => @SMul.smul G H2 a.toSMul δ z) '' D=D ∧
                ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
                 (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
                (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
                  ∃n : ℤ,g=δ^n) ∧
                ∃n : ℤ,∃η : K,(n=1 ∨ n=-1) ∧ η.val^n=δ ∧
                  ∃k : K,(B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0)).unop=k⁻¹*η⁻¹*k := by
            letI := a
            intro D K b cov hcov hproj hact hsc o B hB
            letI := a
            letI := b
            letI := hsc
            obtain ⟨ep,hep,F,hin,havoid,hF1,hEmb,t,ht,g,j,hjg,hj,hg,hsource⟩ :=
              actual_original_separating_c_side_literal_meridian_unit_primitive_axis_same_component_source
                M H c d hc hcgeo U V hU hV hUV hcover hfrontU hcd a p hq hmetric e h r hpunct hr f q hf
            let F₀ : {z : U // z.val∉d.image} :=
              ⟨⟨F (0,1),hin 0 (by norm_num) 1⟩,havoid 0 (by norm_num) 1⟩
            obtain ⟨x₀,hx₀⟩ := hcov.surjective F₀
            have hx₀p : p x₀.val=F (0,1) :=
              (hproj x₀).symm.trans (congrArg (fun z : {z : U // z.val∉d.image} => z.val.val) hx₀)
            have hD : connectedComponentIn (p ⁻¹' (U\d.image)) x₀.val=D :=
              (connectedComponentIn_eq x₀.property).symm
            specialize hsource x₀.val hx₀p
            dsimp only at hsource
            rw [hD] at hsource
            obtain ⟨δ,α,hα,T,hT,hαfront,hαimage,hαfibre,hδD,hδshift,hδstab,hδmono,
              n,η,y,hy,hyD,hn,hroot,hηmono⟩ := hsource
            have hδK : δ∈K := by
              apply MulAction.mem_stabilizer_iff.mpr
              exact hδD
            have hηK : η∈K := by
              rcases hn with hn|hn
              · subst n
                simp only [zpow_one] at hroot
                rw [hroot]
                exact hδK
              · subst n
                simp only [zpow_neg_one] at hroot
                have hh : η=δ⁻¹ := by rw [←hroot,inv_inv]
                rw [hh]
                exact K.inv_mem hδK
            let ηK : K := ⟨η,hηK⟩
          
            obtain ⟨z,hz,γ,hγ,stem,hword⟩ :=
              actual_same_free_basis_same_complex_chart_peripheral_monodromy_source
                b cov hcov f o B hB ep hep
            let inc : C({z : U // z.val∉d.image},E) :=
              ⟨fun z => z.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
            let m : C(Circle,E) := j.comp ⟨fun z => ⟨((1/4:ℝ):ℂ)*(z:ℂ),by
              constructor
              · exact mul_ne_zero (by norm_num) (Circle.coe_ne_zero _)
              · simp [norm_mul];norm_num⟩,by fun_prop⟩
            change p y=m 1 at hy
            have hclock (t : unitInterval) : inc (f.symm (γ t))=
                m (Circle.exp (2*Real.pi*(t:ℝ))) :=
              actual_same_complex_chart_meridian_cut_clock_identification U d.image f ep j hj
                (1/4) (by norm_num) (by norm_num) z γ hγ t
            have hbase : inc (f.symm z)=m 1 := by
              simpa using hclock 0
            let Y₀ : D := ⟨y,hyD⟩
            have hYq : cov Y₀=f.symm z := by
              apply Subtype.ext
              apply Subtype.ext
              exact (hproj Y₀).trans (hy.trans hbase.symm)
            let Y : cov ⁻¹' {f.symm z} := ⟨Y₀,hYq⟩
            let Γ : Path (f.symm z) (f.symm z) := γ.map f.symm.continuous
            let β : Path (m 1) (m 1) := (Γ.map inc.continuous).cast hbase.symm hbase.symm
            have hβ : ∀t : unitInterval,β t=m (Circle.exp (2*Real.pi*(t:ℝ))) := hclock
            have hηambient := hηmono β hβ
            change @SMul.smul G H2 a.toSMul η y=
              hq.isCoveringMap.liftPath β y (β.source.trans hy.symm) 1 at hηambient
            have hηlocal : @SMul.smul K D b.toSMul ηK Y.val=
                (hcov.isCoveringMap.monodromy ⟦Γ⟧ Y).val := by
              apply Subtype.ext
              rw [hact]
              let L := hcov.isCoveringMap.liftPath Γ Y.val (Γ.source.trans hYq.symm)
              have heq : (fun t : unitInterval => (L t).val)=
                  hq.isCoveringMap.liftPath β y (β.source.trans hy.symm) := by
                apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
                refine ⟨continuous_subtype_val.comp L.continuous,?_,?_⟩
                · funext t
                  change p (L t).val=β t
                  rw [←hproj]
                  have hh := congrArg inc
                    (congrFun (hcov.isCoveringMap.liftPath_lifts Γ Y.val (Γ.source.trans hYq.symm)) t)
                  change inc (cov (L t))=β t
                  exact hh
                · change (L 0).val=y
                  rw [hcov.isCoveringMap.liftPath_zero]
              change @SMul.smul G H2 a.toSMul η y=(L 1).val
              exact hηambient.trans (congrFun heq 1).symm
            obtain ⟨k,hk⟩ := actual_supplied_peripheral_monodromy_same_component_conjugacy
              b cov hcov (f.symm actualPantsBase) (f.symm z) o Y
              ⟦stem⟧ ⟦Γ⟧ (B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0)).unop ηK hword hηlocal
            exact ⟨δ,α,hα,T,hT,hαfront,hαimage,hαfibre,hδD,hδshift,hδstab,n,ηK,hn,hroot,k,hk⟩
          have hTransport {K G P : Type} [Group K] [Group G]
              (a : MulAction G P) (ι : K →* G) (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ)
              (S : Set P) (δ : G) (η k : K) (n : ℤ)
              (hn : n=1 ∨ n=-1) (hroot : (ι η)^n=δ)
              (hword : (B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0)).unop=k⁻¹*η⁻¹*k)
              (hpres : (fun z => @SMul.smul G P a.toSMul δ z) '' S=S)
              (hprim : ∀h : G,(fun z => @SMul.smul G P a.toSMul h z) '' S=S → ∃m : ℤ,h=δ^m) :
              let g := (B (FreeGroup.of 0)).unop⁻¹*k⁻¹
              let Sc := (fun z => @SMul.smul G P a.toSMul (ι g) z) '' S
              ι g*δ*(ι g)⁻¹=(ι (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop)^(-n) ∧
              (fun z => @SMul.smul G P a.toSMul
                (ι (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop) z) '' Sc=Sc ∧
              ∀h : G,(fun z => @SMul.smul G P a.toSMul h z) '' Sc=Sc →
                ∃m : ℤ,h=(ι (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop)^m := by
            letI := a
            intro g Sc
            let W := ι (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop
            have hw : W=ι g*(ι η)⁻¹*(ι g)⁻¹ := by
              have hwK : (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop=
                  (B (FreeGroup.of 0)).unop⁻¹*
                    (B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0)).unop*(B (FreeGroup.of 0)).unop := by
                simp only [map_mul,map_inv,MulOpposite.unop_mul,MulOpposite.unop_inv]
                group
              change ι (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop=_
              rw [hwK,hword]
              dsimp [g]
              simp only [map_mul,map_inv]
              group
            have hδpres : δ • S=S := hpres
            have hgen : ι g*δ*(ι g)⁻¹=W^(-n) := by
              rcases hn with rfl|rfl
              · simp only [zpow_one] at hroot
                rw [←hroot,hw]
                simp only [zpow_neg_one]
                group
              · simp only [zpow_neg_one] at hroot
                rw [←hroot,hw]
                simp
            have hwPres : W • Sc=Sc := by
              have hh : (ι g*δ*(ι g)⁻¹) • Sc=Sc := by
                change (ι g*δ*(ι g)⁻¹) • (ι g • S)=ι g • S
                rw [mul_smul,mul_smul,inv_smul_smul,hδpres]
              rw [hgen] at hh
              rcases hn with hn|hn
              · rw [hn] at hh
                simp only [neg_neg,zpow_neg_one] at hh
                exact ((inv_smul_eq_iff).mp hh).symm
              · rw [hn] at hh
                simpa using hh
            refine ⟨hgen,hwPres,?_⟩
            intro h hh
            have hh' : ((ι g)⁻¹*h*ι g) • S=S := by
              change h • (ι g • S)=ι g • S at hh
              rw [mul_smul,mul_smul,hh,inv_smul_smul]
            obtain ⟨m,hm⟩ := hprim ((ι g)⁻¹*h*ι g) hh'
            refine ⟨(-n)*m,?_⟩
            have hc : h=ι g*δ^m*(ι g)⁻¹ := by rw [←hm];group
            rw [hc]
            have hz := map_zpow (MulAut.conj (ι g)) δ m
            change ι g*δ^m*(ι g)⁻¹=(ι g*δ*(ι g)⁻¹)^m at hz
            rw [hz,hgen,←zpow_mul]
          have hGeometry {K G P E : Type} [Group K] [Group G] [MetricSpace P] [TopologicalSpace E]
              (a : MulAction G P) (ι : K →* G)
              (hiso : ∀k : K,Isometry (fun z => @SMul.smul G P a.toSMul (ι k) z))
              (D : Set P) (hD : ∀k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' D=D)
              (p : P → E) (hproj : ∀k : K,∀z : P,p (@SMul.smul G P a.toSMul (ι k) z)=p z)
              (A : Set E) (α : C(ℝ,P)) (hα : Isometry α)
              (hfront : range α⊆frontier D) (himage : p '' range α=A)
              (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T) (g : K) :
              ∃β : C(ℝ,P),
                (∀t : ℝ,β t=@SMul.smul G P a.toSMul (ι g) (α t)) ∧
                Isometry β ∧ range β⊆frontier D ∧ p '' range β=A ∧
                (∀s t : ℝ,p (β s)=p (β t) ↔ ∃n : ℤ,s=t+n*T) ∧
                range β=(fun z => @SMul.smul G P a.toSMul (ι g) z) '' range α := by
            letI := a
            let b : MulAction K P := MulAction.compHom P ι
            letI := b
            letI : ContinuousConstSMul K P := ⟨fun k => (hiso k).continuous⟩
            let β : C(ℝ,P) := ⟨fun t => @SMul.smul G P a.toSMul (ι g) (α t),
              (hiso g).continuous.comp α.continuous⟩
            have hFr : (fun z => @SMul.smul G P a.toSMul (ι g) z) '' frontier D=frontier D := by
              have hh := (Homeomorph.smul g : P ≃ₜ P).image_frontier D
              change (fun z => @SMul.smul G P a.toSMul (ι g) z) '' frontier D=
                frontier ((fun z => @SMul.smul G P a.toSMul (ι g) z) '' D) at hh
              rw [hD] at hh
              exact hh
            have hrange : range β=(fun z => @SMul.smul G P a.toSMul (ι g) z) '' range α :=
              Set.range_comp (fun z : P => @SMul.smul G P a.toSMul (ι g) z) (fun t : ℝ => α t)
            refine ⟨β,fun _ => rfl,(hiso g).comp hα,?_,?_,?_,hrange⟩
            · rw [hrange]
              exact image_subset_iff.mpr (fun z hz => hFr ▸ mem_image_of_mem _ (hfront hz))
            · rw [hrange,←image_comp]
              simpa only [Function.comp_def,hproj] using himage
            · intro s t
              simpa only [β,ContinuousMap.coe_mk,hproj] using hfibre s t
          letI := a
          intro D K b cov hcov hproj hact hsc o B hB
          letI := b
          letI := hsc
          obtain ⟨δ,α,hα,T,hT,hαfront,hαimage,hαfibre,hδD,hδshift,hδstab,n,η,hn,hroot,k,hk⟩ :=
            hCSource M H c d hc hcgeo U V hU hV hUV hcover hfrontU hcd a p hq hmetric
              e h r hpunct hr f q hf x hx b cov hcov hproj hact hsc o B hB
          let ι : K →* G := (MulAction.stabilizer G D).subtype
          have hShiftPres (δ : G) (hshift : ∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) :
              (fun z => @SMul.smul G H2 a.toSMul δ z) '' range α=range α := by
            ext z
            constructor
            · rintro ⟨_,⟨t,rfl⟩,rfl⟩
              exact ⟨t+T,(hshift t).symm⟩
            · rintro ⟨t,rfl⟩
              refine ⟨α (t-T),⟨t-T,rfl⟩,?_⟩
              change @SMul.smul G H2 a.toSMul δ (α (t-T))=α t
              rw [hshift]
              congr 1
              ring
          have hδpres : (fun z => @SMul.smul G H2 a.toSMul δ z) '' range α=range α := by
            rcases hδshift with hshift|hshift
            · exact hShiftPres δ hshift
            · have hh : δ⁻¹ • range α=range α := hShiftPres δ⁻¹ hshift
              exact ((inv_smul_eq_iff).mp hh).symm
          let g : K := (B (FreeGroup.of 0)).unop⁻¹*k⁻¹
          obtain ⟨hgen,hwPres,hwPrim⟩ := hTransport a ι B (range α) δ η k n hn hroot hk hδpres hδstab
          letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
          have hiso : ∀k : K,Isometry (fun z => @SMul.smul G H2 a.toSMul (ι k) z) := by
            intro k
            let b : H2 ≃ₜ H2 := {
              toFun := fun z => (ι k) • z
              invFun := fun z => (ι k)⁻¹ • z
              left_inv := inv_smul_smul (ι k)
              right_inv := smul_inv_smul (ι k)
              continuous_toFun := hq.continuous_const_smul (ι k)
              continuous_invFun := hq.continuous_const_smul (ι k)⁻¹ }
            exact actual_deck_development_isometry p (Homeomorph.refl H2) hmetric b (fun z=>hq.map_smul (ι k))
          have hD : ∀k : K,(fun z => @SMul.smul G H2 a.toSMul (ι k) z) '' D=D :=
            fun k => MulAction.mem_stabilizer_iff.mp k.property
          have hproj' : ∀k : K,∀z : H2,p (@SMul.smul G H2 a.toSMul (ι k) z)=p z :=
            fun k z=>hq.map_smul (ι k)
          obtain ⟨β,hβclock,hβ,hβfront,hβimage,hβfibre,hrange⟩ :=
            hGeometry a ι hiso D hD p hproj' c.image α hα hαfront hαimage T hT hαfibre g
          refine ⟨β,hβ,T,hT,hβfront,hβimage,hβfibre,?_,?_,?_,?_⟩
          · exact hD (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop
          · rw [hrange]
            exact hwPres
          · intro k hk
            apply hwPrim k
            simpa only [hrange] using hk
          · exact hConjClock a α β (ι g) δ (ι (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop) T n hn hgen hβclock hδshift
        letI := a
        intro D K b cov hcov hproj hact hsc hreg hconv o
        letI := b
        letI := hsc
        let inc : C({z : U // z.val∉d.image},E) :=
          ⟨fun z => z.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
        let lift : C(D,H2) := ⟨Subtype.val,continuous_subtype_val⟩
        let ι : K →* G := (MulAction.stabilizer G D).subtype
        obtain ⟨B,hBaxes⟩ := actual_original_literal_cylinder_free_generators_same_component_primitive_axes_source
          H d hdgeo a p hq hmetric U hdU e h r hr hpunct hcore f q hf
          b cov hcov o lift (fun z=>(hproj z).symm) ι hact
        have hD : connectedComponentIn (p ⁻¹' {z : E | z∈U ∧ z∉d.image}) (lift o.val)=D :=
          (connectedComponentIn_eq o.val.property).symm
        dsimp only at hBaxes
        rw [hD] at hBaxes
        have hBmono : ∀i : Fin 2,
            let ε : ℝ := if i=0 then -1 else 1
            let hε : ε≠0 := by dsimp [ε];split <;> norm_num
            let chart : C(ActualPuncturedCylinder,{z : U // z.val∉d.image}) := ⟨f.symm,f.symm.continuous⟩
            let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
            let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
            @SMul.smul K D b.toSMul (B (FreeGroup.of i)).unop
              (hcov.isCoveringMap.monodromy stem o).val=
              (hcov.isCoveringMap.monodromy loop (hcov.isCoveringMap.monodromy stem o)).val := by
          intro i
          obtain ⟨α,hα,T,hT,hfront,himage,hfibre,hpresD,hshift,hprim,hlocal,hambient⟩ := hBaxes i
          exact hlocal
        obtain ⟨γ,hγB⟩ := hHorizontal M H c d hc hcgeo U V hU hV hUV hcover hfrontU hcd
          a p hq hmetric e h r hpunct hr f q hf x hx b cov hcov hproj hact hsc o B hBmono
        obtain ⟨α₀,hα₀,T₀,hT₀,h₀front,h₀image,h₀fibre,h₀D,h₀shift,h₀prim,h₀mono,h₀ambient⟩ := hBaxes 0
        obtain ⟨α₁,hα₁,T₁,hT₁,h₁front,h₁image,h₁fibre,h₁D,h₁shift,h₁prim,h₁mono,h₁ambient⟩ := hBaxes 1
        obtain ⟨αc,hαc,Tc,hTc,hcfront,hcimage,hcfibre,hcD,hcpres,hcprim,hcshift⟩ :=
          hCWord M H c d hc hcgeo U V hU hV hUV hcover hfrontU hcd a p hq hmetric
            e h r hpunct hr f q hf x hx b cov hcov hproj hact hsc o B hBmono
        have hShiftPres (α : C(ℝ,H2)) (T : ℝ) (δ : G)
            (hshift : (∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
              (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) :
            (fun z => @SMul.smul G H2 a.toSMul δ z) '' range α=range α := by
          have hForward (δ : G) (hs : ∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) :
              (fun z => @SMul.smul G H2 a.toSMul δ z) '' range α=range α := by
            ext z
            constructor
            · rintro ⟨_,⟨t,rfl⟩,rfl⟩
              exact ⟨t+T,(hs t).symm⟩
            · rintro ⟨t,rfl⟩
              refine ⟨α (t-T),⟨t-T,rfl⟩,?_⟩
              change @SMul.smul G H2 a.toSMul δ (α (t-T))=α t
              rw [hs]
              congr 1
              ring
          rcases hshift with hs|hs
          · exact hForward δ hs
          · have hh : δ⁻¹ • range α=range α := hForward δ⁻¹ hs
            exact ((inv_smul_eq_iff).mp hh).symm
        have h₀pres := hShiftPres α₀ T₀ (ι (B (FreeGroup.of 0)).unop) h₀shift
        have h₁pres := hShiftPres α₁ T₁ (ι (B (FreeGroup.of 1)).unop) h₁shift
        have hcprim' : ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range αc=range αc →
            ∃n : ℤ,g=(ι (B ((FreeGroup.of 0*(FreeGroup.of 1)⁻¹)^(1:ℤ))).unop)^n := by
          simpa only [zpow_one,ι,Subgroup.subtype_apply] using hcprim
        obtain ⟨h01,h0c,h1c⟩ := actual_literal_three_primitive_boundary_axis_orbits_distinct
          a B ι Subtype.val_injective (range α₀) (range α₁) (range αc) 1 h₁prim hcprim' h₀pres h₁pres
        have hfrontier := actual_original_cut_primitive_boundary_axis_three_orbit_dictionary_source
          M H c d hc hcdiv hcgeo hdgeo hdnondiv hcd U V hU hV hUV hcover hfrontU hfrontV hdU
          a p hq hmetric x hx αc α₀ α₁ hαc hα₀ hα₁ hcfront h₀front h₁front hcimage h₀image h₁image
          Tc T₀ T₁ hTc hT₀ hT₁ hcfibre h₀fibre h₁fibre h01
        letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
        have hisoG : ∀g : G,Isometry (fun z => @SMul.smul G H2 a.toSMul g z) := by
          intro g
          let deck : H2 ≃ₜ H2 := {
            toFun := fun z => g • z
            invFun := fun z => g⁻¹ • z
            left_inv := inv_smul_smul g
            right_inv := smul_inv_smul g
            continuous_toFun := hq.continuous_const_smul g
            continuous_invFun := hq.continuous_const_smul g⁻¹ }
          exact actual_deck_development_isometry p (Homeomorph.refl H2) hmetric deck (fun z=>hq.map_smul g)
        have hprojG : ∀g : G,∀z : H2,p (@SMul.smul G H2 a.toSMul g z)=p z :=
          fun g z=>hq.map_smul g
        have hPeriodsEq : T₀=T₁ := hPeriods a p hq hisoG hprojG α₀ α₁ hα₀ hα₁ T₀ T₁
          hT₀ hT₁ h₀fibre h₁fibre (h₀image.trans h₁image.symm)
        have hneRanges : range α₁≠range α₀ := by
          have hh := h01 (1:K)
          change (fun z => (1:G) • z) '' range α₀≠range α₁ at hh
          have hh' : range α₀≠range α₁ := by simpa only [one_smul,image_id'] using hh
          exact Ne.symm hh'
        have hPositive : ∃ε : ℝ,0<ε ∧ ∀s t : ℝ,ε ≤ dist (α₀ s) (α₁ t) := by
          rcases h₀shift with hs|hs
          · exact hSeparation a p hq hisoG hprojG α₀ α₁ hα₀ hα₁ T₀ hT₀ h₀fibre
              (ι (B (FreeGroup.of 0)).unop) hs (h₁image.trans h₀image.symm) hneRanges
          · exact hSeparation a p hq hisoG hprojG α₀ α₁ hα₀ hα₁ T₀ hT₀ h₀fibre
              (ι (B (FreeGroup.of 0)).unop)⁻¹ hs (h₁image.trans h₀image.symm) hneRanges
        obtain ⟨ε,hε,hsep⟩ := hPositive
        have hQopen : IsOpen (U\d.image) := hU.sdiff ((isCompact_range d.embedded.continuous).isClosed)
        obtain ⟨dn,hdn,g,L₀,L₁,hL₀,hL₁,hg₀,hg₁,hact₀,hact₁⟩ :=
          hTwoNormalize a p hq hmetric (U\d.image) hQopen x hx α₀ α₁ hα₀ hα₁ T₀ T₁
            (B (FreeGroup.of 0)).unop.val (B (FreeGroup.of 1)).unop.val
            (B (FreeGroup.of 0)).unop.property (B (FreeGroup.of 1)).unop.property
            h₀front h₁front h₀shift h₁shift ⟨ε,hε,hsep⟩
        let δc : G := (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop.val
        have hδc : δc≠1 := hWordNonidentity K B
        letI : ClosedSurface E := M.genusTwo.2.1.some
        obtain ⟨εc,hεc,huniform⟩ := actual_supplied_deck_positive_uniform_displacement a p hq hmetric δc hδc
        let deckc : H2 ≃ᵢ H2 := {
          toEquiv := MulAction.toPerm δc
          isometry_toFun := hisoG δc }
        have hfree (z : H2) : deckc z≠z := by
          intro he
          have h := huniform z
          change εc ≤ dist z (deckc z) at h
          rw [he,dist_self] at h
          exact (not_le_of_gt hεc) h
        have hpresc : deckc '' range αc=range αc := hcpres
        obtain ⟨Lc,hLc,hclockc⟩ := hFreeClock deckc αc hαc hpresc hfree
        let Dmat : ℝ → SL(2,ℝ) := fun s =>
          ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
        let Rmat : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
        let eN : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
        let Anorm := Dmat (-dn/2)*Rmat*Dmat L₀*Rmat⁻¹*Dmat (dn/2)
        let Bnorm := Dmat (dn/2)*Rmat*Dmat L₁*Rmat⁻¹*Dmat (-dn/2)
        have hDadd (s t : ℝ) : Dmat s*Dmat t=Dmat (s+t) := by
          apply Subtype.ext
          change (Dmat s).val*(Dmat t).val=(Dmat (s+t)).val
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Dmat,Matrix.mul_apply,Fin.sum_univ_two,Real.exp_add,add_div,neg_add,mul_comm]
        have hDzero : Dmat 0=1 := by
          apply Subtype.ext
          change (Dmat 0).val=(1 : Matrix (Fin 2) (Fin 2) ℝ)
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Dmat]
        have hDinv (s : ℝ) : (Dmat s)⁻¹=Dmat (-s) := by
          apply inv_eq_of_mul_eq_one_right
          rw [hDadd,add_neg_cancel,hDzero]
        have hAForm : ((Dmat (-dn/2)*Rmat)*Dmat L₀*(Dmat (-dn/2)*Rmat)⁻¹)=Anorm := by
          simp only [Anorm,_root_.mul_inv_rev,hDinv,neg_div,neg_neg,mul_assoc]
        have hBForm : ((Dmat (dn/2)*Rmat)*Dmat L₁*(Dmat (dn/2)*Rmat)⁻¹)=Bnorm := by
          simp only [Bnorm,_root_.mul_inv_rev,hDinv,neg_div,neg_neg,mul_assoc]
        have hAct₀ (z : H2) : eN ((B (FreeGroup.of 0)).unop • z)=Anorm • eN z := by
          change g • (@SMul.smul G H2 a.toSMul (B (FreeGroup.of 0)).unop.val z)=Anorm • (g • z)
          rw [←hAForm]
          exact hact₀ z
        have hAct₁ (z : H2) : eN ((B (FreeGroup.of 1)).unop • z)=Bnorm • eN z := by
          change g • (@SMul.smul G H2 a.toSMul (B (FreeGroup.of 1)).unop.val z)=Bnorm • (g • z)
          rw [←hBForm]
          exact hact₁ z
        let Mk : Fin 2 → SL(2,ℝ) := fun i => if i=0 then Anorm else Bnorm
        have hgen : ∀i z,eN ((B (FreeGroup.of i)).unop • z)=Mk i • eN z := by
          intro i z
          fin_cases i
          · simpa [Mk] using hAct₀ z
          · simpa [Mk] using hAct₁ z
        obtain ⟨ρ,hρgen,hρ,hρrange⟩ := hActionRepresentation B Mk eN hgen
        have hMkRange : range Mk={Anorm,Bnorm} := by
          ext v
          constructor
          · rintro ⟨i,rfl⟩
            fin_cases i <;> simp [Mk]
          · rintro (rfl|hv)
            · exact ⟨0,by simp [Mk]⟩
            · have he : v=Bnorm := mem_singleton_iff.mp hv
              subst v
              exact ⟨1,by simp [Mk]⟩
        rw [hMkRange] at hρrange
        have hρ₀ : ρ (B (FreeGroup.of 0)).unop=Anorm := by simpa [Mk] using hρgen 0
        have hρ₁ : ρ (B (FreeGroup.of 1)).unop=Bnorm := by simpa [Mk] using hρgen 1
        have hcK : (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop=
            ((B (FreeGroup.of 1)).unop)⁻¹*(B (FreeGroup.of 0)).unop := by
          simp only [map_mul,map_inv,MulOpposite.unop_mul,MulOpposite.unop_inv]
        have hρc : ρ (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop=Bnorm⁻¹*Anorm := by
          rw [hcK,map_mul,map_inv,hρ₀,hρ₁]
        let Cn := eN '' D
        let γc : ℝ → H2 := fun t => eN (αc t)
        have hγc : Isometry γc := eN.isometry.comp hαc
        have hγcRange : range γc=eN '' range αc := Set.range_comp eN αc
        have hCopen : IsOpen D := (hQopen.preimage hq.isCoveringMap.continuous).connectedComponentIn
        obtain ⟨hCnOpen,hCnConn,hCnReg,hCnConv,hCnFront⟩ :=
          hDomainTransport D eN hCopen isPreconnected_connectedComponentIn hreg hconv
        have hEF : eN '' frontier D=frontier Cn := hCnFront.symm
        have hγcFront : range γc⊆frontier Cn := by
          rw [hγcRange,←hEF]
          exact Set.image_mono hcfront
        change eN '' range α₀=range (fun t : ℝ => Dmat (-dn/2) • (Rmat • verticalPath t)) at hg₀
        change eN '' range α₁=range (fun t : ℝ => Dmat (dn/2) • (Rmat • verticalPath t)) at hg₁
        have hγ₀Front : range (fun t : ℝ => Dmat (-dn/2) • (Rmat • verticalPath t))⊆frontier Cn := by
          rw [←hg₀,←hEF]
          exact Set.image_mono h₀front
        have hγ₁Front : range (fun t : ℝ => Dmat (dn/2) • (Rmat • verticalPath t))⊆frontier Cn := by
          rw [←hg₁,←hEF]
          exact Set.image_mono h₁front
        have hKpres (k : K) : (fun z : H2 => k • z) '' D=D :=
          MulAction.mem_stabilizer_iff.mp k.property
        have hMpres (k : K) : (ρ k) • Cn=Cn := by
          change (fun z : H2 => ρ k • z) '' (eN '' D)=eN '' D
          rw [image_image]
          rw [show (fun z : H2 => ρ k • eN z)=(fun z : H2 => eN (k • z)) from funext (fun z => (hρ k z).symm)]
          rw [←image_image,hKpres]
        have hAnormPres : Anorm • Cn=Cn := by rw [←hρ₀];exact hMpres _
        have hBnormPres : Bnorm • Cn=Cn := by rw [←hρ₁];exact hMpres _
        have hClockNorm (t : ℝ) : (Bnorm⁻¹*Anorm) • γc t=γc (t+Lc) := by
          have h := hρ (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop (αc t)
          rw [hρc] at h
          have hc : (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop • αc t=αc (t+Lc) := hclockc t
          rw [hc] at h
          exact h.symm
        have hDispNorm (z : H2) : εc ≤ dist z ((Bnorm⁻¹*Anorm) • z) := by
          have h := huniform (eN.symm z)
          change εc ≤ dist (eN.symm z) ((B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop • eN.symm z) at h
          have h' : εc ≤ dist (eN (eN.symm z))
              (eN ((B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop • eN.symm z)) := by
            simpa only [eN.dist_eq] using h
          rw [eN.apply_symm_apply,hρ,hρc,eN.apply_symm_apply] at h'
          exact h'
        have hFrontActual : frontier D=(⋃k : K,(fun z : H2 => k • z) '' range αc) ∪
            (⋃k : K,(fun z : H2 => k • z) '' range α₀) ∪
            (⋃k : K,(fun z : H2 => k • z) '' range α₁) := hfrontier
        have hFrontNorm := hFrontierTransport D (range α₀) (range α₁) (range αc) eN ρ hρ hFrontActual
        rw [hρrange,←hγcRange,hg₀,hg₁] at hFrontNorm
        have hL₁' : L₁=T₀ ∨ L₁=-T₀ := by simpa only [←hPeriodsEq] using hL₁
        obtain ⟨hCenterNorm,hPresNorm⟩ := hThreeOrbitHalfTurn dn T₀ L₀ L₁ hdn hL₀ hL₁'
          Cn hCnOpen hCnConn hCnReg hCnConv γc hγc hγcFront Lc εc hLc hεc
          hAnormPres hBnormPres hγ₀Front hγ₁Front hDispNorm hClockNorm hFrontNorm
        have hClockEq : L₁=L₀ := hEqualSignedClocks dn T₀ L₀ L₁ hL₀ hL₁'
          Cn hCnOpen hCenterNorm γc hγc hγcFront Lc εc hLc hεc hDispNorm hClockNorm
        let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
        obtain ⟨hJinv,hJfixed⟩ := hyperbolic_normalized_half_turn
        have hJinv' (z : H2) : J • (J • z)=z := hJinv z
        have hCenterActual : eN.symm UpperHalfPlane.I∈D := by
          obtain ⟨z,hz,he⟩ := hCenterNorm
          have he' : z=eN.symm UpperHalfPlane.I := by simpa only [eN.symm_apply_apply] using congrArg eN.symm he
          exact he' ▸ hz
        let fActual : H2 → H2 := fun z => eN.symm (J • eN z)
        have hfActual (z : H2) : fActual (fActual z)=z := by
          dsimp only [fActual]
          rw [eN.apply_symm_apply,hJinv',eN.symm_apply_apply]
        have hSubActual : fActual '' D⊆D := by
          rintro z ⟨w,hw,rfl⟩
          have hm : J • eN w∈Cn := by
            rw [←hPresNorm]
            exact ⟨eN w,⟨w,hw,rfl⟩,rfl⟩
          obtain ⟨v,hv,hve⟩ := hm
          have hvEq : v=fActual w := by
            apply eN.injective
            rw [eN.apply_symm_apply]
            exact hve
          exact hvEq ▸ hv
        have hPresActual : fActual '' D=D := by
          apply subset_antisymm hSubActual
          intro z hz
          exact ⟨fActual z,hSubActual ⟨z,hz,rfl⟩,hfActual z⟩
        exact ⟨B,αc,α₀,α₁,hαc,hα₀,hα₁,Tc,T₀,T₁,hTc,hT₀,hT₁,hcfront,h₀front,h₁front,
          hcimage,h₀image,h₁image,hcfibre,h₀fibre,h₁fibre,h₀pres,h₁pres,hcpres,h₀prim,h₁prim,hcprim,hcshift,
          h01,h0c,h1c,hfrontier,hPeriodsEq,ε,hε,hsep,h₀shift,h₁shift,
          dn,hdn,g,L₀,L₁,hL₀,hL₁,hg₀,hg₁,hact₀,hact₁,Lc,εc,hLc,hεc,hclockc,huniform,
          hClockEq,ρ,hρ₀,hρ₁,hρrange,hρ,hCenterActual,hPresActual,γ,hγB⟩
      have hModel {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
          (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
          (hcgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image)
          (hcdiv : DividingCurve c) (hdnondiv : ¬DividingCurve d)
          (hdisj : Disjoint c.image d.image) :
          ∃ U V : Set E,IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
            U∪V=c.imageᶜ ∧ frontier U=c.image ∧ frontier V=c.image ∧
            Nonempty (V ≃ₜ {z : Circle×Circle // z≠(1,1)}) ∧
            d.image⊆U ∧ ∃ e : U ≃ₜ {z : Circle×Circle // z≠(1,1)},
            ∃ r : Circle×Circle,∃ hr : r.2≠1,
            ∃ h : (Circle×Circle) ≃ₜ (Circle×Circle),h (1,1)=r ∧
            h '' ((fun x : U => (e x).val) '' {x : U | x.val∈d.image})=
              {z : Circle×Circle | z.2=1} ∧
            ∃ f : {x : U // x.val∉d.image} ≃ₜ {z : Circle×ℝ // z≠(1,0)},
              ∃ q : {z : Circle // z≠1} ≃ₜ ℝ,
                ∀ x,∃ hx : (h (e x.val).val).2≠1,
                  (f x).val=(r.1⁻¹*(h (e x.val).val).1,
                    q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩) := by
        letI : ClosedSurface E := M.genusTwo.2.1.some
        have hside : ∃ U V : Set E,IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
            U∪V=c.imageᶜ ∧ frontier U=c.image ∧ frontier V=c.image ∧
            Nonempty (U ≃ₜ {z : Circle×Circle // z≠(1,1)}) ∧
            Nonempty (V ≃ₜ {z : Circle×Circle // z≠(1,1)}) ∧
            d.image⊆U ∧ Uᶜ.Nonempty ∧ IsConnected d.imageᶜ := by
          obtain ⟨U,V,hU,hV,hUV,hunion,hfrU,hfrV,heU,heV⟩ :=
            actual_dividing_essential_curve_two_one_holed_tori M c
              (actual_simple_closed_geodesic_essential H c hcgeo) hcdiv
          have hdconn : IsConnected d.imageᶜ := Classical.not_not.mp hdnondiv
          have hdoutside : d.image⊆c.imageᶜ := by
            intro x hx hc
            exact disjoint_left.mp hdisj hc hx
          have hpre : IsPreconnected d.image := (isConnected_range d.embedded.continuous).isPreconnected
          have hsubset : d.image⊆U∪V := hunion.symm ▸ hdoutside
          have hout (A : Set E) (hA : A⊆c.imageᶜ) : Aᶜ.Nonempty := by
            refine ⟨c.map 1,?_⟩
            intro hcA
            exact hA hcA ⟨1,rfl⟩
          have hUVsubU : U⊆c.imageᶜ := by rw [←hunion];exact subset_union_left
          have hUVsubV : V⊆c.imageᶜ := by rw [←hunion];exact subset_union_right
          have hp := hsubset (show d.map 1∈d.image from ⟨1,rfl⟩)
          rcases hp with hp|hp
          · have hdU : d.image⊆U := hpre.subset_left_of_subset_union hU hV hUV hsubset
              ⟨d.map 1,⟨1,rfl⟩,hp⟩
            exact ⟨U,V,hU,hV,hUV,hunion,hfrU,hfrV,heU,heV,hdU,hout U hUVsubU,hdconn⟩
          · have hdV : d.image⊆V := hpre.subset_right_of_subset_union hU hV hUV hsubset
              ⟨d.map 1,⟨1,rfl⟩,hp⟩
            exact ⟨V,U,hV,hU,hUV.symm,by simpa [union_comm] using hunion,
              hfrV,hfrU,heV,heU,hdV,hout V hUVsubV,hdconn⟩
        obtain ⟨U,V,hU,hV,hUV,hunion,hfrU,hfrV,⟨e⟩,heV,hdU,houtside,hdconn⟩ := hside
        refine ⟨U,V,hU,hV,hUV,hunion,hfrU,hfrV,heV,hdU,e,?_⟩
        have hmodel : ∃ r : Circle×Circle,r.2≠1 ∧ ∃ h : (Circle×Circle) ≃ₜ (Circle×Circle),
            h (1,1)=r ∧
            h '' ((fun x : U => (e x).val) '' {x : U | x.val∈d.image})=
              {z : Circle×Circle | z.2=1} ∧ ∃ f : {x : U // x.val∉d.image} ≃ₜ
              {z : Circle×Circle // z≠r ∧ z.2≠1},
              ∀ x,(f x).val=h (e x.val).val := by
          obtain ⟨dY,hDY,hess,havoid,m,n,hgcd,a,H,hfix,himage⟩ :=
            actual_original_nondividing_cut_side_marked_primitive_straightening U hU houtside e d hdU hdconn
          let u := Int.gcdA m n
          let v := Int.gcdB m n
          have hbez : m*u+n*v=1 := by
            simpa [u,v,hgcd] using (Int.gcd_eq_gcd_ab m n).symm
          have hnorm : let en := actual_integer_basis_torus_homeomorph m n u v hbez
              ∃ k : (Circle×Circle) ≃ₜ (Circle×Circle),
                (∀ x,k x=(en a)⁻¹*en x) ∧
                (∀ z : Circle,k (a*torusWindingMap m n z)=(z,1)) ∧
                k '' range (fun z : Circle => a*torusWindingMap m n z)=
                  {x : Circle×Circle | x.2=1} := by
            dsimp only
            let e := actual_integer_basis_torus_homeomorph m n u v hbez
            let l : (Circle×Circle) ≃ₜ (Circle×Circle) :=
              { toFun := fun x => (e a)⁻¹*x
                invFun := fun x => e a*x
                left_inv := by intro x;simp
                right_inv := by intro x;simp
                continuous_toFun := by fun_prop
                continuous_invFun := by fun_prop }
            let h := e.trans l
            have hewind (z : Circle) : e (torusWindingMap m n z)=(z,1) := by
              apply Prod.ext
              · change (z^m)^u*(z^n)^v=z
                rw [←zpow_mul,←zpow_mul,←zpow_add,hbez];simp
              · change (z^m)^(-n)*(z^n)^m=1
                rw [←zpow_mul,←zpow_mul,←zpow_add]
                have hz : m*(-n)+n*m=0 := by ring
                rw [hz];simp
            have hemul (x y : Circle×Circle) : e (x*y)=e x*e y := by
              apply Prod.ext <;> simp [e,actual_integer_basis_torus_homeomorph,mul_zpow,mul_mul_mul_comm]
              all_goals ac_rfl
            have hh (z : Circle) : h (a*torusWindingMap m n z)=(z,1) := by
              change (e a)⁻¹*e (a*torusWindingMap m n z)=(z,1)
              rw [hemul,hewind];simp
            refine ⟨h,fun x => rfl,hh,?_⟩
          
            ext x
            constructor
            · rintro ⟨w,⟨z,rfl⟩,rfl⟩
              rw [hh]
              rfl
            · intro hx
              exact ⟨a*torusWindingMap m n x.1,⟨x.1,rfl⟩,(hh x.1).trans (Prod.ext rfl hx.symm)⟩
          obtain ⟨k,hk,hkparam,hkim⟩ := hnorm
          obtain ⟨hH,hHpoint⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
          let h := hH.trans k
          have him : h '' dY.image={z : Circle×Circle | z.2=1} := by
            change (k ∘ hH) '' dY.image=_
            rw [image_comp]
            rw [show hH '' dY.image=H.finalMap '' dY.image from by
              rw [show (hH : Circle×Circle → Circle×Circle)=H.finalMap from funext hHpoint]]
            rw [himage,hkim]
          have hpoint : (h (1,1)).2≠1 := by
            intro hp
            have hm : h (1,1)∈h '' dY.image := by rw [him];exact hp
            exact havoid (h.injective.mem_set_image.mp hm)
          refine ⟨h (1,1),hpoint,h,rfl,?_,?_⟩
          · rw [←hDY];exact him
          let D := d.image
          let Dtor := dY.image
          have hD : Dtor=(fun x : U => (e x).val) '' {x : U | x.val∈D} := hDY
          have hd (x : U) : (e x).val∈Dtor ↔ x.val∈D := by
            rw [hD]
            constructor
            · rintro ⟨u,hu,he⟩
              have hue : u=x := e.injective (Subtype.ext he)
              simpa [hue] using hu
            · intro hx;exact ⟨x,hx,rfl⟩
          have hh (z : Circle×Circle) : (h z).2=1 ↔ z∈Dtor := by
            change h z∈{w : Circle×Circle | w.2=1} ↔ z∈Dtor
            rw [←him]
            exact h.injective.mem_set_image
          let f : {x : U // x.val∉D} → {z : Circle×Circle // z≠h (1,1) ∧ z.2≠1} :=
            fun x => ⟨h (e x.val).val,by
              constructor
              · exact h.injective.ne ((e x.val).property)
              · intro he
                exact x.property ((hd x.val).mp ((hh _).mp he))⟩
          let g : {z : Circle×Circle // z≠h (1,1) ∧ z.2≠1} → {x : U // x.val∉D} :=
            fun z => ⟨e.symm ⟨h.symm z.val,by
              intro he
              apply z.property.1
              rw [←h.apply_symm_apply z.val,he]⟩,by
              intro he
              apply z.property.2
              have ht := (hd (e.symm ⟨h.symm z.val,by
                intro he
                apply z.property.1
                rw [←h.apply_symm_apply z.val,he]⟩)).mpr he
              simpa using (hh _).mpr ht⟩
          refine ⟨{ toFun := f
                    invFun := g
                    left_inv := ?_
                    right_inv := ?_
                    continuous_toFun := ?_
                    continuous_invFun := ?_ }, fun x => rfl⟩
          · intro x
            apply Subtype.ext
            apply e.injective
            apply Subtype.ext
            simp [f,g]
          · intro z
            apply Subtype.ext
            simp [f,g]
          · dsimp [f]
            fun_prop
          · dsimp [g]
            fun_prop
        obtain ⟨r,hr,h,hp,hcore,f,hf⟩ := hmodel
        have hq : Nonempty ({z : Circle // z≠1} ≃ₜ ℝ) := by
          letI : Fact (Module.finrank ℝ ℂ=1+1) := ⟨by simp⟩
          let v : Metric.sphere (0 : ℂ) 1 := (1 : Circle)
          let s := stereographic' 1 v
          have hs : s.source={z : Circle | z≠1} := by
            rw [stereographic'_source]
            ext z
            simp only [mem_compl_iff,mem_singleton_iff,mem_setOf_eq]
            rfl
          have ht : s.target=univ := stereographic'_target v
          let q : {z : Circle // z≠1} ≃ₜ EuclideanSpace ℝ (Fin 1) :=
            (Homeomorph.setCongr hs.symm).trans
              (s.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
          exact ⟨q.trans ((PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).trans
            (Homeomorph.funUnique (Fin 1) ℝ))⟩
        obtain ⟨q⟩ := hq
        have hchart : ∃ g : {z : Circle×Circle // z≠r ∧ z.2≠1} ≃ₜ
              {w : Circle×ℝ // w≠(1,0)},
            ∀ z,(g z).val=(r.1⁻¹*z.val.1,q ⟨z.val.2,z.property.2⟩-q ⟨r.2,hr⟩) := by
          let s := q ⟨r.2,hr⟩
          let f : {z : Circle×Circle // z≠r ∧ z.2≠1} → {w : Circle×ℝ // w≠(1,0)} :=
            fun z => ⟨(r.1⁻¹*z.val.1,q ⟨z.val.2,z.property.2⟩-s),by
              intro he
              have h1 : z.val.1=r.1 := by
                have h1 := congrArg Prod.fst he
                exact (inv_mul_eq_one.mp h1).symm
              have h2 : z.val.2=r.2 := by
                have h2 := congrArg Prod.snd he
                have hq : q ⟨z.val.2,z.property.2⟩=q ⟨r.2,hr⟩ := sub_eq_zero.mp h2
                exact congrArg Subtype.val (q.injective hq)
              exact z.property.1 (Prod.ext h1 h2)⟩
          let g : {w : Circle×ℝ // w≠(1,0)} → {z : Circle×Circle // z≠r ∧ z.2≠1} :=
            fun w => ⟨(r.1*w.val.1,(q.symm (w.val.2+s)).val),by
              constructor
              · intro he
                apply w.property
                have h1 : w.val.1=1 := by
                  have h1 := congrArg Prod.fst he
                  simpa [mul_eq_left] using h1
                have h2 : w.val.2=0 := by
                  have h2 := congrArg Prod.snd he
                  have hu : q.symm (w.val.2+s)=⟨r.2,hr⟩ := Subtype.ext h2
                  have hq := congrArg q hu
                  simp only [q.apply_symm_apply] at hq
                  change w.val.2+s=s at hq
                  linarith
                exact Prod.ext h1 h2
              · exact (q.symm _).property⟩
          refine ⟨{ toFun := f
                    invFun := g
                    left_inv := ?_
                    right_inv := ?_
                    continuous_toFun := ?_
                    continuous_invFun := ?_ },fun z => rfl⟩
          · intro z
            apply Subtype.ext
            apply Prod.ext
            · simp [f,g]
            · simp [f,g]
          · intro w
            apply Subtype.ext
            apply Prod.ext
            · simp [f,g]
            · simp [f,g]
          · dsimp [f]
            fun_prop
          · dsimp [g]
            fun_prop
        obtain ⟨g,hg⟩ := hchart
        refine ⟨r,hr,h,hp,hcore,f.trans g,q,?_⟩
        intro x
        have hx : (h (e x.val).val).2≠1 := by rw [←hf x];exact (f x).property.2
        refine ⟨hx,?_⟩
        change (g (f x)).val=_
        rw [hg]
        congr 1
        · exact congrArg (fun z : Circle×Circle => r.1⁻¹*z.1) (hf x)
        · congr 1
          apply congrArg q
          exact Subtype.ext (congrArg Prod.snd (hf x))
      have hComponent {E : Type} [TopologicalSpace E] (U V F : Set E)
          (hU : IsOpen U) (hV : IsOpen V) (hconn : IsConnected U)
          (hdis : Disjoint U V) (hcover : U∪V=F) (u : E) (hu : u∈U) :
          connectedComponentIn F u=U := by
        have hUF : U⊆F := hcover ▸ subset_union_left
        have hFu : u∈F := hUF hu
        apply Set.Subset.antisymm
        · exact IsPreconnected.subset_left_of_subset_union hU hV hdis
            ((connectedComponentIn_subset F u).trans (by rw [hcover]))
            ⟨u,mem_connectedComponentIn hFu,hu⟩ isPreconnected_connectedComponentIn
        · exact hconn.2.subset_connectedComponentIn hu hUF
      have hCylinder : PathConnectedSpace ActualPuncturedCylinder := by
        have hproduct {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
            [PathConnectedSpace A] [PathConnectedSpace B]
            (a₀ a₁ : A) (b₀ b₁ : B) (ha : a₁≠a₀) (hb : b₁≠b₀) :
            IsPathConnected ({(a₀,b₀)}ᶜ : Set (A×B)) := by
          classical
          let F : Set (A×B) := {(a₀,b₀)}ᶜ
          have hto (x : A×B) (hx : x∈F) : JoinedIn F x (a₁,b₁) := by
            by_cases hy : x.2=b₀
            · have hxn : x.1≠a₀ := by
                intro he
                apply hx
                exact Prod.ext he hy
              have hv : JoinedIn F x (x.1,b₁) := by
                refine ⟨(Path.refl x.1).prod (PathConnectedSpace.somePath x.2 b₁),?_⟩
                intro t
                change (x.1,(PathConnectedSpace.somePath x.2 b₁) t)≠(a₀,b₀)
                exact fun h => hxn (congrArg Prod.fst h)
              have hh : JoinedIn F (x.1,b₁) (a₁,b₁) := by
                refine ⟨(PathConnectedSpace.somePath x.1 a₁).prod (Path.refl b₁),?_⟩
                intro t
                change ((PathConnectedSpace.somePath x.1 a₁) t,b₁)≠(a₀,b₀)
                exact fun h => hb (congrArg Prod.snd h)
              exact hv.trans hh
            · have hh : JoinedIn F x (a₁,x.2) := by
                refine ⟨(PathConnectedSpace.somePath x.1 a₁).prod (Path.refl x.2),?_⟩
                intro t
                change ((PathConnectedSpace.somePath x.1 a₁) t,x.2)≠(a₀,b₀)
                exact fun h => hy (congrArg Prod.snd h)
              have hv : JoinedIn F (a₁,x.2) (a₁,b₁) := by
                refine ⟨(Path.refl a₁).prod (PathConnectedSpace.somePath x.2 b₁),?_⟩
                intro t
                change (a₁,(PathConnectedSpace.somePath x.2 b₁) t)≠(a₀,b₀)
                exact fun h => ha (congrArg Prod.fst h)
              exact hh.trans hv
          exact ⟨(a₁,b₁),fun h => ha (congrArg Prod.fst h),fun y hy => (hto y hy).symm⟩
        letI : PathConnectedSpace Circle := by
          have h : IsPathConnected (Metric.sphere (0 : ℂ) (1 : ℝ)) :=
            isPathConnected_sphere (by rw [Complex.rank_real_complex];norm_num) 0 (by norm_num)
          exact isPathConnected_iff_pathConnectedSpace.mp h
        let n : Circle := -(1:Circle)
        have hn : n≠1 := by
          intro h
          have hc := congrArg (fun z : Circle => (z:ℂ)) h
          norm_num [n] at hc
        exact isPathConnected_iff_pathConnectedSpace.mp (hproduct (1:Circle) n (0:ℝ) 1 hn (by norm_num))
      letI := hCylinder
      obtain ⟨U,V,hU,hV,hUV,hcover,hfrontU,hfrontV,heV,hdU,e,r,hr,h,hpunct,hcore,f,q,hf⟩ :=
        hModel M H c d hcgeo hcdiv hdnondiv hcd
      let Cut := {z : U // z.val∉d.image}
      let W := U\d.image
      let W' := V\d.image
      let eCut : W ≃ₜ Cut := {
        toFun := fun z => ⟨⟨z.val,z.property.1⟩,z.property.2⟩
        invFun := fun z => ⟨z.val.val,⟨z.val.property,z.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by
          exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
      letI : PathConnectedSpace Cut := f.symm.pathConnectedSpace
      letI : PathConnectedSpace W := eCut.symm.pathConnectedSpace
      have hWconn : IsConnected W := isConnected_iff_connectedSpace.mpr inferInstance
      letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
      have hdClosed : IsClosed d.image := isCompact_range d.embedded.continuous |>.isClosed
      have hWopen : IsOpen W := hU.sdiff hdClosed
      have hW'open : IsOpen W' := hV.sdiff hdClosed
      have hWW' : Disjoint W W' := hUV.mono diff_subset diff_subset
      have hcoverCut : W∪W'=(c.image∪d.image)ᶜ := by
        ext z
        have hh := Set.ext_iff.mp hcover z
        simp only [mem_union,mem_compl_iff] at hh
        simp only [W,W',mem_union,mem_diff,mem_compl_iff]
        tauto
      let u : E := (f.symm actualPantsBase).val.val
      have huW : u∈W := ⟨(f.symm actualPantsBase).val.property,(f.symm actualPantsBase).property⟩
      have hu : u∈(c.image∪d.image)ᶜ := hcoverCut ▸ Or.inl huW
      have hIdentity : connectedComponentIn (c.image∪d.image)ᶜ u=W :=
        hComponent W W' (c.image∪d.image)ᶜ hWopen hW'open hWconn hWW' hcoverCut u huW
      letI := a
      have hq := hp0
      have hmetric := hm0
      obtain ⟨x,hx⟩ := hq.surjective u
      letI : LocallyPathConnectedSpace E := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
      have hActualCut := hSuppliedCut c d hcgeo hdgeo a p hq hmetric x (hx ▸ hu)
      dsimp only at hActualCut
      rw [hx,hIdentity] at hActualCut
      let D := connectedComponentIn (p ⁻¹' W) x
      let K := MulAction.stabilizer G D
      obtain ⟨b,cov,hcov,hproj,hact,hcovmetric,hcontract,hsc,hDopen,hDregular,hconv⟩ := hActualCut
      letI := b
      letI := hsc
      let covCut : D → Cut := eCut ∘ cov
      have hcovCut : IsQuotientCoveringMap covCut K := hcov.homeomorph_comp eCut
      have hprojCut : ∀z : D,(covCut z).val.val=p z.val := hproj
      obtain ⟨o,ho⟩ := hcovCut.surjective (f.symm actualPantsBase)
      have hxW : p x∈U\d.image := hx ▸ huW
      letI : LocallyPathConnectedSpace E := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
      have hRegularD := hRegular c d hcgeo hdgeo p hq.isCoveringMap hmetric x (hx ▸ hu)
      dsimp only at hRegularD
      rw [hx,hIdentity] at hRegularD
      have hResult := hDictionary M H c d
        (actual_simple_closed_geodesic_essential H c hcgeo) hcgeo U V hU hV hUV hcover hfrontU hcd
        a p hq hmetric e h r hpunct hr f q hf hcdiv hdgeo hdnondiv hfrontV hdU hcore x hxW
        b covCut hcovCut hprojCut hact hsc hRegularD.2.1 hRegularD.2.2 ⟨o,ho⟩
      rcases hResult with ⟨B,αc,α₀,α₁,hαc,hα₀,hα₁,Tc,T₀,T₁,hTc,hT₀,hT₁,hcfront,h₀front,h₁front,
        hcimage,h₀image,h₁image,hcfibre,h₀fibre,h₁fibre,h₀pres,h₁pres,hcpres,h₀prim,h₁prim,hcprim,hcshift,
        h01,h0c,h1c,hfrontier,hPeriodsEq,ε,hε,hsep,h₀shift,h₁shift,
        dn,hdn,g,L₀,L₁,hL₀,hL₁,hg₀,hg₁,hact₀,hact₁,Lc,εc,hLc,hεc,hclockc,huniform,
        hClockEq,ρ,hρgen0,hρgen1,hρrange,hρ,hCenterActual,hPresActual,γ,hγB⟩
      let Dmat : ℝ → SL(2,ℝ) := fun s =>
        ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
      let Rmat : SL(2,ℝ) := stabilizerRotation 1 1 (by norm_num)
      let eN : H2 ≃ᵢ H2 := IsometryEquiv.constSMul g
      let J : SL(2,ℝ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩
      let Anorm := Dmat (-dn/2)*Rmat*Dmat L₀*Rmat⁻¹*Dmat (dn/2)
      let Bnorm := Dmat (dn/2)*Rmat*Dmat L₁*Rmat⁻¹*Dmat (-dn/2)
      have hL₁' : L₁=T₀ ∨ L₁=-T₀ := by simpa only [←hPeriodsEq] using hL₁
      have hEx : (J*Anorm*J⁻¹=Bnorm ∧ J*Bnorm*J⁻¹=Anorm) ∨
          (J*Anorm*J⁻¹=Bnorm⁻¹ ∧ J*Bnorm*J⁻¹=Anorm⁻¹) :=
        hSignedExchange dn T₀ L₀ L₁ hL₀ hL₁'
      have hNormΓ : J∈Subgroup.normalizer (Subgroup.closure ({Anorm,Bnorm}:Set SL(2,ℝ)):Set SL(2,ℝ)) :=
        hGroupNormalizer Anorm Bnorm J hEx
      have hρrange' : ρ.range=Subgroup.closure ({Anorm,Bnorm}:Set SL(2,ℝ)) := hρrange
      have hNormρ : J∈Subgroup.normalizer (ρ.range:Set SL(2,ℝ)) := by
        rw [hρrange']
        exact hNormΓ
      have hρ' : ∀k : K,∀z : H2,eN (k • z)=ρ k • eN z := hρ
      have hCompat : ∀k : K,∀z : D,(@SMul.smul K D b.toSMul k z).val=k • z.val := hact
      have hJinv (z : H2) : J • (J • z)=z := hyperbolic_normalized_half_turn.1 z
      have hPresActual' : (fun z : H2 => eN.symm (J • eN z)) '' D=D := hPresActual
      obtain ⟨τ,hτinv,hτ⟩ := hQuotientDescent D b cov hcov hCompat eN ρ hρ' J hNormρ hJinv hPresActual'
      obtain ⟨Ebool,hE0,hE1⟩ := hSignedMarking B ρ dn T₀ L₀ L₁ hL₀ hL₁' hρgen0 hρgen1
      let Bswap := Dmat (dn/2)*Rmat*Dmat (-L₀)*Rmat⁻¹*Dmat (-dn/2)
      have hSwap : J*Anorm*J⁻¹=Bswap ∧ J*Bswap*J⁻¹=Anorm :=
        actual_normalized_equal_boundary_generator_exchange dn L₀
      have hCenterActual' : eN.symm UpperHalfPlane.I∈D := hCenterActual
      have hUnique : ∀y,τ y=y ↔ y=cov ⟨eN.symm UpperHalfPlane.I,hCenterActual'⟩ :=
        hOneFixed D b cov hcov hCompat eN ρ hρ' Anorm Bswap J Ebool hE0 hE1
          hSwap.1 hSwap.2 hJinv hyperbolic_normalized_half_turn.2
          hCenterActual' hPresActual' τ hτ
      letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
      have hCovMetric : ∀z : D,∃W : Set D,IsOpen W ∧ z∈W ∧
          ∀y∈W,∀z∈W,dist (cov y) (cov z)=dist y z := hcovmetric
      have hTauMetric := hLocalMetric D cov hcov.isCoveringMap hcov.surjective
        hCovMetric eN J hJinv hPresActual' τ hτ
      obtain ⟨bc,hbcCl,hqcl,τcl,hτcl,hLiftCl⟩ := hClosureQuotient a p hq D eN ρ hρ' J hNormρ hJinv hPresActual'
      letI := bc
      let qcl : ↥(closure D) → Quotient (MulAction.orbitRel K ↥(closure D)) := Quotient.mk _
      have hCompatCl : ∀k : K,∀z : closure D,(k • z).val=k • z.val := hbcCl
      have hCenterCl : eN.symm UpperHalfPlane.I∈closure D := subset_closure hCenterActual'
      let Factual : H2 ≃ᵢ H2 := (eN.trans (IsometryEquiv.constSMul J)).trans eN.symm
      have hFpres : Factual '' D=D := hPresActual'
      have hClPres : Factual '' closure D=closure D := by
        calc
          Factual '' closure D=closure (Factual '' D) := Factual.toHomeomorph.image_closure D
          _=closure D := by rw [hFpres]
      have hClPres' : (fun z : H2 => eN.symm (J • eN z)) '' closure D=closure D := hClPres
      have hUniqueCl : ∀y,τcl y=y ↔ y=qcl ⟨eN.symm UpperHalfPlane.I,hCenterCl⟩ :=
        hOneFixed (closure D) bc qcl hqcl hCompatCl eN ρ hρ' Anorm Bswap J Ebool hE0 hE1
          hSwap.1 hSwap.2 hJinv hyperbolic_normalized_half_turn.2 hCenterCl hClPres' τcl hLiftCl
      letI := b
      let incl : D → ↥(closure D) := fun z => ⟨z.val,subset_closure z.property⟩
      have hIncl : IsOpenEmbedding incl := hOpenClosureInclusion D hRegularD.1
      have hInclEquiv (k : K) (z : D) :
          incl (@SMul.smul K D b.toSMul k z)=@SMul.smul K ↥(closure D) bc.toSMul k (incl z) := by
        apply Subtype.ext
        change (@SMul.smul K D b.toSMul k z).val=(@SMul.smul K ↥(closure D) bc.toSMul k (incl z)).val
        exact (hact k z).trans (hbcCl k (incl z)).symm
      obtain ⟨emb,hEmb,hEmbCover⟩ := hOpenQuotientEmbedding cov qcl hcov hqcl incl hIncl hInclEquiv
      have hIntertwine (y : ↥(U\d.image)) : emb (τ y)=τcl (emb y) := by
        obtain ⟨z,rfl⟩ := hcov.surjective y
        have hw : Factual z.val∈D := by
          have hh : Factual z.val∈Factual '' D := ⟨z.val,z.property,rfl⟩
          exact (Set.ext_iff.mp hFpres (Factual z.val)).mp hh
        let w : D := ⟨Factual z.val,hw⟩
        have hτzw : τ (cov z)=cov w := hτ z w rfl
        rw [hτzw,hEmbCover,hEmbCover]
        exact (hLiftCl (incl z) (incl w) rfl).symm
      have hisoG : ∀g : G,Isometry (fun z => @SMul.smul G H2 a.toSMul g z) := by
        intro g
        let deck : H2 ≃ₜ H2 := {
          toFun := fun z => g • z
          invFun := fun z => g⁻¹ • z
          left_inv := inv_smul_smul g
          right_inv := smul_inv_smul g
          continuous_toFun := hq.continuous_const_smul g
          continuous_invFun := hq.continuous_const_smul g⁻¹ }
        exact actual_deck_development_isometry p (Homeomorph.refl H2) hmetric deck (fun z=>hq.map_smul g)
      have hprojG : ∀g : G,∀z : H2,p (@SMul.smul G H2 a.toSMul g z)=p z := fun g z=>hq.map_smul g
      have hc₀ : range α₀⊆closure D := h₀front.trans frontier_subset_closure
      have hc₁ : range α₁⊆closure D := h₁front.trans frontier_subset_closure
      obtain ⟨hT2,f₀,hf₀,hparam₀,hrange₀⟩ := hBoundaryCircle a p hq hisoG D bc hbcCl hqcl α₀ hc₀ T₀ hT₀ h₀fibre
        (B (FreeGroup.of 0)).unop h₀shift
      letI := hT2
      obtain ⟨hT2',f₁,hf₁,hparam₁,hrange₁⟩ := hBoundaryCircle a p hq hisoG D bc hbcCl hqcl α₁ hc₁ T₁ hT₁ h₁fibre
        (B (FreeGroup.of 1)).unop h₁shift
      let cl₀ : C(ℝ,↥(closure D)) := ⟨fun s => ⟨α₀ s,hc₀ (mem_range_self s)⟩,α₀.continuous.subtype_mk _⟩
      let cl₁ : C(ℝ,↥(closure D)) := ⟨fun s => ⟨α₁ s,hc₁ (mem_range_self s)⟩,α₁.continuous.subtype_mk _⟩
      have hParam₀ (s : ℝ) : qcl (cl₀ s)=f₀ (Circle.exp (2*Real.pi*s/T₀)) := hparam₀ s
      have hParam₁ (s : ℝ) : qcl (cl₁ s)=f₁ (Circle.exp (2*Real.pi*s/T₁)) := hparam₁ s
      have hRange₀ : range f₀=qcl '' range cl₀ := hrange₀
      have hRange₁ : range f₁=qcl '' range cl₁ := hrange₁
      have hNoMeet := hDistinctBoundaryAxes a p hq hisoG hprojG α₀ α₁ hα₀ hα₁ T₀ hT₀ h₀fibre
        (h₀image.trans h₁image.symm) K h01
      have hDisjoint : Disjoint (range f₀) (range f₁) := by
        apply Set.disjoint_left.mpr
        intro y hy₀ hy₁
        have hy₀' : y∈qcl '' range cl₀ := (Set.ext_iff.mp hRange₀ y).mp hy₀
        have hy₁' : y∈qcl '' range cl₁ := (Set.ext_iff.mp hRange₁ y).mp hy₁
        obtain ⟨_,⟨s,rfl⟩,hs⟩ := hy₀'
        obtain ⟨_,⟨t,rfl⟩,ht⟩ := hy₁'
        obtain ⟨k,hk⟩ := hqcl.apply_eq_iff_mem_orbit.mp (hs.trans ht.symm)
        have hg : @SMul.smul G H2 a.toSMul k.val (α₁ t)=α₀ s :=
          (hbcCl k (cl₁ t)).symm.trans (congrArg (fun z : closure D => z.val) hk)
        have hp : @SMul.smul G H2 a.toSMul k.val⁻¹ (α₀ s)=α₁ t := by
          rw [←hg]
          exact inv_smul_smul k.val (α₁ t)
        exact hNoMeet k⁻¹ s t hp
      obtain ⟨_,_,hJaxis,_,_⟩ := actual_normalized_boundary_axes_common_perpendicular dn hdn.le
      have hActualAxisSwap : Factual '' range α₀=range α₁ ∧ Factual '' range α₁=range α₀ :=
        hAxisExchange eN.toEquiv (fun z : H2=>J • z) hJinv α₀ α₁
          (fun t=>Dmat (-dn/2) • (Rmat • verticalPath t))
          (fun t=>Dmat (dn/2) • (Rmat • verticalPath t)) hg₀ hg₁ hJaxis
      have hCircleMap (α β : C(ℝ,↥(closure D))) (f h : C(Circle,Quotient (MulAction.orbitRel K ↥(closure D))))
          (hf : range f=qcl '' range α) (hh : range h=qcl '' range β)
          (hαβ : ∀t : ℝ,∃s : ℝ,(β s).val=Factual (α t).val) :
          τcl '' range f⊆range h := by
        rintro y ⟨z,hz,rfl⟩
        rw [hf] at hz
        obtain ⟨_,⟨t,rfl⟩,rfl⟩ := hz
        obtain ⟨s,hs⟩ := hαβ t
        rw [hLiftCl (α t) (β s) hs,hh]
        exact ⟨β s,mem_range_self s,rfl⟩
      have hCircleMap₀ : τcl '' range f₀⊆range f₁ :=
        hCircleMap cl₀ cl₁ f₀ f₁ hRange₀ hRange₁ (fun t=>by
          have hh : Factual (α₀ t)∈range α₁ := by
            rw [←hActualAxisSwap.1]
            exact ⟨α₀ t,mem_range_self t,rfl⟩
          obtain ⟨s,hs⟩ := hh
          exact ⟨s,hs⟩)
      have hCircleMap₁ : τcl '' range f₁⊆range f₀ :=
        hCircleMap cl₁ cl₀ f₁ f₀ hRange₁ hRange₀ (fun t=>by
          have hh : Factual (α₁ t)∈range α₀ := by
            rw [←hActualAxisSwap.2]
            exact ⟨α₁ t,mem_range_self t,rfl⟩
          obtain ⟨s,hs⟩ := hh
          exact ⟨s,hs⟩)
      have hCircleSwap₀ : τcl '' range f₀=range f₁ := by
        apply subset_antisymm hCircleMap₀
        intro y hy
        exact ⟨τcl y,hCircleMap₁ ⟨y,hy,rfl⟩,hτcl y⟩
      have hCircleSwap₁ : τcl '' range f₁=range f₀ := by
        apply subset_antisymm hCircleMap₁
        intro y hy
        exact ⟨τcl y,hCircleMap₀ ⟨y,hy,rfl⟩,hτcl y⟩
      have hpD : p '' D⊆U := by
        rintro y ⟨z,hz,rfl⟩
        rw [←hproj ⟨z,hz⟩]
        exact (cov ⟨z,hz⟩).property.1
      have hUc : Disjoint U c.image := by
        apply Set.disjoint_left.mpr
        intro y hy hc
        have hh : y∈c.imageᶜ := by rw [←hcover];exact Or.inl hy
        exact hh hc
      have hOrbitProjection (α : C(ℝ,H2)) (A : Set E) (himage : p '' range α=A) :
          p '' (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α)⊆A := by
        rintro y ⟨z,hz,rfl⟩
        obtain ⟨k,w,⟨t,rfl⟩,rfl⟩ := Set.mem_iUnion.mp hz
        rw [hprojG]
        rw [←himage]
        exact ⟨α t,mem_range_self t,rfl⟩
      have hClosureOverU := hClosureOverComponent p D
        (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range αc)
        (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀)
        (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₁)
        U c.image hRegularD.1 hfrontier hpD (hOrbitProjection αc c.image hcimage) hUc
        ((hOrbitProjection α₀ d.image h₀image).trans hdU)
        ((hOrbitProjection α₁ d.image h₁image).trans hdU)
      let δ₀ : G := (B (FreeGroup.of 0)).unop.val
      let δ₁ : G := (B (FreeGroup.of 1)).unop.val
      have hNorm₀ (z : H2) : eN (@SMul.smul G H2 a.toSMul δ₀ z)=Anorm • eN z := by
        have hh := hρ (B (FreeGroup.of 0)).unop z
        rw [hρgen0] at hh
        exact hh
      have hNorm₁ (z : H2) : eN (@SMul.smul G H2 a.toSMul δ₁ z)=Bnorm • eN z := by
        have hh := hρ (B (FreeGroup.of 1)).unop z
        rw [hρgen1] at hh
        exact hh
      obtain ⟨gSeam,hgSeam,hgComm,hgProj⟩ := hDeckNormalize a p hisoG hprojG eN δ₀ δ₁ γ Anorm Bnorm hγB hNorm₀ hNorm₁
      have hL₀ne : L₀≠0 := by
        rcases hL₀ with hh|hh <;> rw [hh] <;> intro hz <;> linarith
      have hδ₁ne : δ₁≠1 := by
        intro hh
        rcases h₁shift with hs|hs
        · have h0 := hs 0
          change @SMul.smul G H2 a.toSMul δ₁ (α₁ 0)=α₁ (0+T₁) at h0
          rw [hh] at h0
          have hz : @SMul.smul G H2 a.toSMul (1 : G) (α₁ 0)=α₁ 0 := a.one_smul (α₁ 0)
          rw [hz] at h0
          have hn := hα₁.injective h0
          linarith
        · have h0 := hs 0
          change @SMul.smul G H2 a.toSMul δ₁⁻¹ (α₁ 0)=α₁ (0+T₁) at h0
          rw [hh,inv_one] at h0
          have hz : @SMul.smul G H2 a.toSMul (1 : G) (α₁ 0)=α₁ 0 := a.one_smul (α₁ 0)
          rw [hz] at h0
          have hn := hα₁.injective h0
          linarith
      letI : ClosedSurface E := M.genusTwo.2.1.some
      obtain ⟨ε₁,hε₁,huniform₁⟩ := actual_supplied_deck_positive_uniform_displacement a p hq hmetric δ₁ hδ₁ne
      have hBdisp (z : H2) : ε₁≤dist z (Bnorm • z) := by
        have hh := huniform₁ (eN.symm z)
        have hd := eN.dist_eq (eN.symm z) (@SMul.smul G H2 a.toSMul δ₁ (eN.symm z))
        rw [eN.apply_symm_apply,hNorm₁,eN.apply_symm_apply] at hd
        exact hh.trans_eq hd.symm
      let ψ₀ : ℝ → H2 := fun t=>Dmat (-dn/2) • (Rmat • verticalPath t)
      let ψ₁ : ℝ → H2 := fun t=>Dmat (dn/2) • (Rmat • verticalPath t)
      obtain ⟨hψ₀,hψ₁,_,_,_⟩ := actual_normalized_boundary_axes_common_perpendicular dn hdn.le
      obtain ⟨hClock₀,hClock₁⟩ := hLiteralClock dn L₀
      have hClock₁' : ∀t : ℝ,Bnorm • ψ₁ t=ψ₁ (t+L₀) := by
        dsimp only [Bnorm]
        rw [hClockEq]
        exact hClock₁
      let Paxis : H2 ≃ᵢ H2 := IsometryEquiv.constSMul Anorm
      let Qaxis : H2 ≃ᵢ H2 := IsometryEquiv.constSMul Bnorm
      have hSeamRange : gSeam '' range ψ₀=range ψ₁ :=
        hConjugateAxisRange Paxis Qaxis gSeam ψ₀ ψ₁ hψ₀ hψ₁ L₀ L₀ ε₁ hL₀ne hL₀ne hε₁ hBdisp hClock₀ hClock₁' hgComm
      obtain ⟨phase,hphase⟩ := hDirectionClock ψ₀ ψ₁ hψ₀ hψ₁ gSeam hSeamRange
        (fun z=>Anorm • z) (fun z=>Bnorm • z) L₀ hL₀ne hClock₀ hClock₁' hgComm
      have hSeamReverse : ∀z : H2,gSeam (J • gSeam (J • z))=z := hLiteralSeam gSeam dn phase hphase
      let pN : C(H2,E) := ⟨fun z=>p (eN.symm z),hq.continuous.comp eN.symm.continuous⟩
      let αN : ℝ → H2 := fun t=>eN (α₀ t)
      have hαN : Isometry αN := eN.isometry.comp hα₀
      have hαNfibre : ∀s t : ℝ,pN (αN s)=pN (αN t) ↔ ∃n : ℤ,s=t+(n:ℝ)*T₀ := by
        intro s t
        change p (eN.symm (eN (α₀ s)))=p (eN.symm (eN (α₀ t))) ↔ _
        rw [eN.symm_apply_apply,eN.symm_apply_apply]
        exact h₀fibre s t
      have hψRange : range ψ₀=range αN := hg₀.symm.trans (Set.range_comp eN α₀).symm
      have hψFibre : ∀s t : ℝ,pN (ψ₀ s)=pN (ψ₀ t) ↔ ∃n : ℤ,s=t+(n:ℝ)*T₀ :=
        hAxisPeriodTransport pN αN ψ₀ hαN hψ₀ hψRange T₀ hαNfibre
      have hψImage : pN '' range ψ₀=d.image := by
        rw [hψRange]
        change pN '' range (eN ∘ α₀)=d.image
        rw [Set.range_comp,Set.image_image]
        have hh : (pN ∘ eN : H2 → E)=p := by
          funext z
          change p (eN.symm (eN z))=p z
          rw [eN.symm_apply_apply]
        change (pN ∘ eN) '' range α₀=d.image
        rw [hh]
        exact h₀image
      obtain ⟨eAxis,heAxis,τAxis,hτAxis,hτAxisClock,Faxis,hFaxisCard,hFaxis⟩ :=
        hActualProjectedReflectionTwoFixed pN ⟨ψ₀,hψ₀.continuous⟩ T₀ hT₀ hψFibre phase
      let eSet : (pN '' range ψ₀) ≃ₜ d.image := Homeomorph.setCongr hψImage
      let eD : Circle ≃ₜ d.image := eAxis.trans eSet
      let τd : d.image ≃ₜ d.image := eSet.symm.trans (τAxis.trans eSet)
      have heD (t : ℝ) : (eD (Circle.exp (2*Real.pi*t/T₀))).val=pN (ψ₀ t) := heAxis t
      have hτDClock (t : ℝ) : τd (eD (Circle.exp (2*Real.pi*t/T₀)))=eD (Circle.exp (2*Real.pi*(-t-phase)/T₀)) := by
        change eSet (τAxis (eSet.symm (eSet (eAxis (Circle.exp (2*Real.pi*t/T₀))))))=eSet (eAxis (Circle.exp (2*Real.pi*(-t-phase)/T₀)))
        rw [eSet.symm_apply_apply,hτAxisClock]
      have hτd (y : d.image) : τd (τd y)=y := by
        change eSet (τAxis (eSet.symm (eSet (τAxis (eSet.symm y)))))=y
        rw [eSet.symm_apply_apply,hτAxis,eSet.apply_symm_apply]
      have hPPhase (t : ℝ) : pN (ψ₀ t)=pN (ψ₁ (t+phase)) := by
        have hh := hgProj (ψ₀ t)
        change pN (gSeam (ψ₀ t))=pN (ψ₀ t) at hh
        rw [hphase] at hh
        exact hh.symm
      have hτdlift (t : ℝ) : ∃ht : pN (ψ₀ t)∈d.image,
          (τd ⟨pN (ψ₀ t),ht⟩).val=pN (J • ψ₀ t) := by
        have ht : pN (ψ₀ t)∈d.image := by rw [←hψImage];exact ⟨ψ₀ t,mem_range_self t,rfl⟩
        refine ⟨ht,?_⟩
        have hh : eD (Circle.exp (2*Real.pi*t/T₀))=⟨pN (ψ₀ t),ht⟩ := Subtype.ext (heD t)
        rw [←hh,hτDClock,heD,hJaxis]
        have hp := hPPhase (-t-phase)
        simpa only [sub_add_cancel] using hp
      let Fd : Finset d.image := Faxis.map eSet.toEquiv.toEmbedding
      have hFdCard : Fd.card=2 := by simpa only [Fd,Finset.card_map] using hFaxisCard
      have hFd : (Fd:Set d.image)={y | τd y=y} := by
        ext y
        obtain ⟨z,rfl⟩ := eSet.surjective y
        have hτE : τd (eSet z)=eSet (τAxis z) := by
          change eSet (τAxis (eSet.symm (eSet z)))=eSet (τAxis z)
          rw [eSet.symm_apply_apply]
        rw [Set.mem_setOf_eq,hτE]
        constructor
        · intro hz
          obtain ⟨x,hx,hxz⟩ := Finset.mem_map.mp hz
          have he : x=z := eSet.injective hxz
          subst x
          exact congrArg eSet ((Set.ext_iff.mp hFaxis z).mp hx)
        · intro hz
          apply Finset.mem_map.mpr
          exact ⟨z,(Set.ext_iff.mp hFaxis z).mpr (eSet.injective hz),rfl⟩
      have hpS : p '' (closure D∩p ⁻¹' U)=U := by
        apply subset_antisymm
        · rintro y ⟨z,hz,rfl⟩
          exact hz.2
        · intro y hy
          by_cases hd : y∈d.image
          · have hh : y∈p '' range α₀ := by rw [h₀image];exact hd
            obtain ⟨z,hz,hzy⟩ := hh
            exact ⟨z,⟨hc₀ hz,(by change p z∈U;rw [hzy];exact hy)⟩,hzy⟩
          · obtain ⟨z,hz⟩ := hcov.surjective (⟨y,hy,hd⟩ : ↥(U\d.image))
            have hpy : p z.val=y := (hproj z).symm.trans (congrArg Subtype.val hz)
            exact ⟨z.val,⟨subset_closure z.property,(by change p z.val∈U;rw [hpy];exact hy)⟩,hpy⟩
      have hKProjection (k : K) (z : H2) : p (Factual (@SMul.smul G H2 a.toSMul k.val z))=p (Factual z) := by
        have hk : J*ρ k*J⁻¹∈ρ.range := (Subgroup.mem_normalizer_iff.mp hNormρ (ρ k)).mp ⟨k,rfl⟩
        obtain ⟨k',hk'⟩ := hk
        have heq : Factual (@SMul.smul G H2 a.toSMul k.val z)=@SMul.smul G H2 a.toSMul k'.val (Factual z) := by
          apply eN.injective
          change eN (eN.symm (J • eN (@SMul.smul G H2 a.toSMul k.val z)))=
            eN (@SMul.smul G H2 a.toSMul k'.val (eN.symm (J • eN z)))
          rw [eN.apply_symm_apply,hρ,hρ,eN.apply_symm_apply,hk',mul_smul,mul_smul,inv_smul_smul]
        rw [heq,hprojG]
      have hJaxis₁ (t : ℝ) : J • ψ₁ t=ψ₀ (-t) := by
        have hh := congrArg (fun z : H2=>J • z) (hJaxis (-t))
        rw [hJinv,neg_neg] at hh
        exact hh.symm
      have hNKernel := hActualSeamKernel ψ₀ ψ₁ pN (fun z : H2=>J • z) phase T₀ hPPhase hψFibre hJaxis hJaxis₁
      have hOriginalAxisKernel : ∀z∈range α₀∪range α₁,∀w∈range α₀∪range α₁,p z=p w →p (Factual z)=p (Factual w) := by
        have hNormMem (z : H2) (hz : z∈range α₀∪range α₁) : eN z∈range ψ₀∪range ψ₁ := by
          rcases hz with hz|hz
          · left
            rw [←hg₀]
            exact ⟨z,hz,rfl⟩
          · right
            rw [←hg₁]
            exact ⟨z,hz,rfl⟩
        have hPN (z : H2) : pN (eN z)=p z := by
          change p (eN.symm (eN z))=p z
          rw [eN.symm_apply_apply]
        intro z hz w hw hzw
        have hh : pN (eN z)=pN (eN w) := by rw [hPN,hPN];exact hzw
        exact hNKernel (eN z) (hNormMem z hz) (eN w) (hNormMem w hw) hh
      let gammaIso : H2 ≃ᵢ H2 := {toEquiv:=MulAction.toPerm γ,isometry_toFun:=hisoG γ}
      have hFInv (z : H2) : Factual (Factual z)=z := by
        change eN.symm (J • eN (eN.symm (J • eN z)))=z
        rw [eN.apply_symm_apply,hJinv,eN.symm_apply_apply]
      have hGamma (z : H2) : eN (gammaIso z)=gSeam (eN z) := (hgSeam z).symm
      have hGammaReverse (z : H2) : gammaIso (Factual (gammaIso (Factual z)))=z := by
        apply eN.injective
        change eN (gammaIso (eN.symm (J • eN (gammaIso (eN.symm (J • eN z))))))=eN z
        rw [hGamma,eN.apply_symm_apply,hGamma,eN.apply_symm_apply,hSeamReverse]
      have hGammaProject (z : H2) : p (gammaIso z)=p z := hprojG γ z
      have hGammaFProjection : ∀z : H2,p (Factual (@SMul.smul G H2 a.toSMul γ z))=p (Factual z) :=
        (hSeamProjection p gammaIso.toEquiv Factual hFInv hGammaReverse hGammaProject).2
      let Bnd : Set H2 := ⋃k : K,(fun z=>@SMul.smul G H2 a.toSMul k.val z) '' (range α₀∪range α₁)
      have hSDecomp : closure D∩p ⁻¹' U=D∪Bnd := by
        simpa only [Bnd,Set.image_union,Set.iUnion_union_distrib,Set.union_assoc] using hClosureOverU
      have hDKernel : ∀z∈D,∀w∈D,p z=p w →p (Factual z)=p (Factual w) := by
        intro z hz w hw hzw
        have hc : cov ⟨z,hz⟩=cov ⟨w,hw⟩ := by
          apply Subtype.ext
          rw [hproj,hproj]
          exact hzw
        obtain ⟨k,hk⟩ := hcov.apply_eq_iff_mem_orbit.mp hc
        have hk' : @SMul.smul G H2 a.toSMul k.val w=z :=
          (hact k ⟨w,hw⟩).symm.trans (congrArg (fun z : D=>z.val) hk)
        rw [←hk']
        exact hKProjection k w
      have hBKernel : ∀z∈Bnd,∀w∈Bnd,p z=p w →p (Factual z)=p (Factual w) :=
        hOrbitKernelTransport a K p Factual (range α₀∪range α₁) (fun k z=>hprojG k.val z) hKProjection hOriginalAxisKernel
      have hDNot (z : H2) (hz : z∈D) : p z∉d.image := by
        rw [←hproj ⟨z,hz⟩]
        exact (cov ⟨z,hz⟩).property.2
      have hBIn (z : H2) (hz : z∈Bnd) : p z∈d.image := by
        obtain ⟨k,w,hw,rfl⟩ := Set.mem_iUnion.mp hz
        rw [hprojG]
        rcases hw with hw|hw
        · rw [←h₀image];exact ⟨w,hw,rfl⟩
        · rw [←h₁image];exact ⟨w,hw,rfl⟩
      have hFullSeamKernel : ∀z∈closure D∩p ⁻¹' U,∀w∈closure D∩p ⁻¹' U,p z=p w →p (Factual z)=p (Factual w) := by
        rw [hSDecomp]
        exact hCutKernelAssembly p Factual D Bnd d.image hDNot hBIn hDKernel hBKernel
      let Sactual : Set H2 := closure D∩p ⁻¹' U
      have hFIntoU (z : H2) (hz : z∈Sactual) : p (Factual z)∈U := by
        change z∈closure D∩p ⁻¹' U at hz
        rw [hSDecomp] at hz
        rcases hz with hz|hz
        · have hfz : Factual z∈D := by
            rw [←hFpres]
            exact ⟨z,hz,rfl⟩
          rw [←hproj ⟨Factual z,hfz⟩]
          exact (cov ⟨Factual z,hfz⟩).property.1
        · obtain ⟨k,w,hw,rfl⟩ := Set.mem_iUnion.mp hz
          rw [hKProjection]
          rcases hw with hw|hw
          · have hf : Factual w∈range α₁ := by rw [←hActualAxisSwap.1];exact ⟨w,hw,rfl⟩
            apply hdU
            rw [←h₁image]
            exact ⟨Factual w,hf,rfl⟩
          · have hf : Factual w∈range α₀ := by rw [←hActualAxisSwap.2];exact ⟨w,hw,rfl⟩
            apply hdU
            rw [←h₀image]
            exact ⟨Factual w,hf,rfl⟩
      have hFS (z : Sactual) : Factual z.val∈Sactual := by
        refine ⟨?_,hFIntoU z.val z.property⟩
        rw [←hClPres]
        exact ⟨z.val,z.property.1,rfl⟩
      let Ps : Sactual → U := fun z=>⟨p z.val,z.property.2⟩
      let Fs : Sactual → Sactual := fun z=>⟨Factual z.val,hFS z⟩
      have hPs : Function.Surjective Ps := by
        intro y
        have hy : y.val∈p '' Sactual := by rw [hpS];exact y.property
        obtain ⟨z,hz,hzy⟩ := hy
        exact ⟨⟨z,hz⟩,Subtype.ext hzy⟩
      have hFs : Function.Involutive Fs := fun z=>Subtype.ext (hFInv z.val)
      have hPsKernel (z w : Sactual) (hzw : Ps z=Ps w) : Ps (Fs z)=Ps (Fs w) :=
        Subtype.ext (hFullSeamKernel z.val z.property w.val w.property (congrArg Subtype.val hzw))
      obtain ⟨τU,hτU,hτULift⟩ := hFibreEquivDescent Ps Fs hPs hFs hPsKernel
      have hτULiftVal (z : H2) (hz : z∈Sactual) : ∃hpz : p z∈U,(τU ⟨p z,hpz⟩).val=p (Factual z) :=
        ⟨hz.2,congrArg Subtype.val (hτULift ⟨z,hz⟩)⟩
      let cutIncl : ↥(U\d.image) → U := fun y=>⟨y.val,y.property.1⟩
      have hCutInj : Function.Injective cutIncl := fun y z hh=>Subtype.ext (congrArg (fun u : U=>u.val) hh)
      have hCutSquare (y : ↥(U\d.image)) : τU (cutIncl y)=cutIncl (τ y) := by
        obtain ⟨z,rfl⟩ := hcov.surjective y
        have hfz : Factual z.val∈D := by rw [←hFpres];exact ⟨z.val,z.property,rfl⟩
        let w : D := ⟨Factual z.val,hfz⟩
        have hτzw : τ (cov z)=cov w := hτ z w rfl
        have hzS : z.val∈Sactual := ⟨subset_closure z.property,by change p z.val∈U;rw [←hproj z];exact (cov z).property.1⟩
        have hInclP : cutIncl (cov z)=Ps ⟨z.val,hzS⟩ := Subtype.ext (hproj z)
        apply Subtype.ext
        rw [hτzw]
        change (τU (cutIncl (cov z))).val=(cov w).val
        rw [hproj]
        rw [hInclP,hτULift]
      let fD : d.image → U := fun y=>⟨y.val,hdU y.property⟩
      have hfD : Function.Injective fD := fun y z hh=>Subtype.ext (congrArg (fun u : U=>u.val) hh)
      have hDSquare (y : d.image) : τU (fD y)=fD (τd y) := by
        have hy : y.val∈pN '' range ψ₀ := by rw [hψImage];exact y.property
        obtain ⟨_,⟨t,rfl⟩,hyt⟩ := hy
        have hzα : eN.symm (ψ₀ t)∈range α₀ := by
          have hh : ψ₀ t∈eN '' range α₀ := by
            have hGN : eN '' range α₀=range ψ₀ := hg₀
            rw [hGN]
            exact mem_range_self t
          obtain ⟨z,hz,hze⟩ := hh
          rw [←hze,eN.symm_apply_apply]
          exact hz
        have hzS : eN.symm (ψ₀ t)∈Sactual := ⟨hc₀ hzα,by change pN (ψ₀ t)∈U;rw [hyt];exact hdU y.property⟩
        have hPy : Ps ⟨eN.symm (ψ₀ t),hzS⟩=fD y := Subtype.ext hyt
        obtain ⟨ht,hτdt⟩ := hτdlift t
        have hyEq : (⟨pN (ψ₀ t),ht⟩ : d.image)=y := Subtype.ext hyt
        have hDy : (τd y).val=pN (J • ψ₀ t) := by rw [←hyEq];exact hτdt
        have hUy : (τU (fD y)).val=pN (J • ψ₀ t) := by
          rw [←hPy,hτULift]
          change p (eN.symm (J • eN (eN.symm (ψ₀ t))))=p (eN.symm (J • ψ₀ t))
          rw [eN.apply_symm_apply]
        exact Subtype.ext (hUy.trans hDy.symm)
      let centerCut : ↥(U\d.image) := cov ⟨eN.symm UpperHalfPlane.I,hCenterActual'⟩
      let centerU : U := cutIncl centerCut
      have hCenterNot : centerU∉range fD := by
        rintro ⟨y,hy⟩
        have hh : y.val=centerCut.val := congrArg Subtype.val hy
        exact centerCut.property.2 (hh ▸ y.property)
      have hOffFix (y : U) (hy : y∉range fD) : τU y=y ↔ y=centerU := by
        have hyd : y.val∉d.image := by
          intro hh
          exact hy ⟨⟨y.val,hh⟩,rfl⟩
        let cy : ↥(U\d.image) := ⟨y.val,y.property,hyd⟩
        have hcy : cutIncl cy=y := rfl
        have hsquare : τU y=cutIncl (τ cy) := by rw [←hcy];exact hCutSquare cy
        constructor
        · intro hh
          have hcfix : τ cy=cy := hCutInj (hsquare.symm.trans (hh.trans hcy.symm))
          have hcenter : cy=centerCut := (hUnique cy).mp hcfix
          exact hcy.symm.trans (congrArg cutIncl hcenter)
        · intro hh
          have hcfix : τ centerCut=centerCut := (hUnique centerCut).mpr rfl
          rw [hh]
          change τU (cutIncl centerCut)=cutIncl centerCut
          rw [hCutSquare,hcfix]
      obtain ⟨FU,hFUCard,hFU⟩ := hThreeFixedAssembly τU τd fD hfD centerU hCenterNot hDSquare hOffFix Fd hFdCard hFd
      have hγrange := actual_deck_axis_range_of_normalized_seam a eN gSeam γ α₀ α₁ ψ₀ ψ₁ hg₀ hg₁ hgSeam hSeamRange
      obtain ⟨hCollar₀,hCollar₁⟩ := actual_closed_cut_local_seam_coverage a p hq U hU d hdU x hxW α₀ α₁ h₀front h₁front h₀image h₁image h01 γ hγrange
      have hWindow : ∀y : U,∃z : H2,p z=y.val ∧ ∃W : Set H2,∃hW : IsOpen W,
          z∈W ∧ ∃hWU : W⊆p ⁻¹' U,∀w : H2,∀hw : w∈W,(τU ⟨p w,hWU hw⟩).val=p (Factual w) := by
        intro y
        by_cases hyd : y.val∈d.image
        · have hyimage : y.val∈p '' range α₀ := by rw [h₀image];exact hyd
          obtain ⟨z,hz,hzy⟩ := hyimage
          obtain ⟨W,hW,hzW,hWU,hCover⟩ := hCollar₀ z hz
          refine ⟨z,hzy,W,hW,hzW,hWU,?_⟩
          intro w hw
          rcases hCover hw with hwCl|hwInv
          · obtain ⟨hpw,hh⟩ := hτULiftVal w ⟨hwCl,hWU hw⟩
            exact hh
          · obtain ⟨u,huCl,rfl⟩ := hwInv
            have hpwu : p (@SMul.smul G H2 a.toSMul γ⁻¹ u)=p u := hprojG γ⁻¹ u
            have huU : p u∈U := by rw [←hpwu];exact hWU hw
            obtain ⟨hpu,huLift⟩ := hτULiftVal u ⟨huCl,huU⟩
            have hsub : (⟨p (@SMul.smul G H2 a.toSMul γ⁻¹ u),hWU hw⟩ : U)=⟨p u,hpu⟩ := Subtype.ext hpwu
            rw [hsub,huLift]
            have hh := hGammaFProjection (@SMul.smul G H2 a.toSMul γ⁻¹ u)
            have hcancel : @SMul.smul G H2 a.toSMul γ (@SMul.smul G H2 a.toSMul γ⁻¹ u)=u := by
              exact @smul_inv_smul G H2 _ a γ u
            exact (congrArg (fun z=>p (Factual z)) hcancel).symm.trans hh
        · let cy : ↥(U\d.image) := ⟨y.val,y.property,hyd⟩
          obtain ⟨z,hz⟩ := hcov.surjective cy
          have hzy : p z.val=y.val := (hproj z).symm.trans (congrArg Subtype.val hz)
          have hDU : D⊆p ⁻¹' U := fun w hw=>(connectedComponentIn_subset _ _ hw).1
          refine ⟨z.val,hzy,D,hRegularD.1,z.property,hDU,?_⟩
          intro w hw
          obtain ⟨hpw,hh⟩ := hτULiftVal w ⟨subset_closure hw,hDU hw⟩
          exact hh
      have hContU : Continuous τU := hContinuousWindows p hq.isCoveringMap U τU Factual Factual.continuous hWindow
      have hτUInverse : (τU.symm : U → U)=τU := by
        funext y
        apply τU.injective
        exact (τU.apply_symm_apply y).trans (hτU y).symm
      let τUH : U ≃ₜ U := { toEquiv := τU,continuous_toFun := hContU,continuous_invFun := by change Continuous (τU.symm : U → U);rw [hτUInverse];exact hContU }
      have hUOriginalMetric := hLocalMetricWindows p hq.isCoveringMap U τU Factual hmetric hWindow
      let Ccarrier : Set H2 := ⋃k : K,(fun z=>@SMul.smul G H2 a.toSMul k.val z) '' range αc
      have hClImage (z : H2) (hz : z∈closure D) : p z∈U∪c.image := by
        rw [closure_eq_self_union_frontier,hfrontier] at hz
        rcases hz with hz|((hz|hz)|hz)
        · exact Or.inl (hpD ⟨z,hz,rfl⟩)
        · exact Or.inr (hOrbitProjection αc c.image hcimage ⟨z,hz,rfl⟩)
        · exact Or.inl (hdU (hOrbitProjection α₀ d.image h₀image ⟨z,hz,rfl⟩))
        · exact Or.inl (hdU (hOrbitProjection α₁ d.image h₁image ⟨z,hz,rfl⟩))
      have hCOnly (z : H2) (hz : z∈closure D) (hnot : p z∉U) : z∈Ccarrier := by
        rw [closure_eq_self_union_frontier,hfrontier] at hz
        rcases hz with hz|((hz|hz)|hz)
        · exact (hnot (hpD ⟨z,hz,rfl⟩)).elim
        · exact hz
        · exact (hnot (hdU (hOrbitProjection α₀ d.image h₀image ⟨z,hz,rfl⟩))).elim
        · exact (hnot (hdU (hOrbitProjection α₁ d.image h₁image ⟨z,hz,rfl⟩))).elim
      let bK : MulAction K H2 := MulAction.compHom H2 K.subtype
      have hKProjection' : ∀k : K,∀z : H2,p (Factual (@SMul.smul K H2 bK.toSMul k z))=p (Factual z) := hKProjection
      let δcK : K := (B (FreeGroup.of 0*(FreeGroup.of 1)⁻¹)).unop
      have hCBaseKernel : ∀z∈range αc,∀w∈range αc,p z=p w →p (Factual z)=p (Factual w) := by
        rcases hcshift with hs|hs
        · have hs' : ∀t : ℝ,@SMul.smul K H2 bK.toSMul δcK (αc t)=αc (t+Tc) := hs
          exact @hPrimitiveAxisKernel K H2 E _ bK p Factual αc Tc δcK hs' hcfibre hKProjection'
        · have hs' : ∀t : ℝ,@SMul.smul K H2 bK.toSMul δcK⁻¹ (αc t)=αc (t+Tc) := hs
          exact @hPrimitiveAxisKernel K H2 E _ bK p Factual αc Tc δcK⁻¹ hs' hcfibre hKProjection'
      have hCKernel : ∀z∈Ccarrier,∀w∈Ccarrier,p z=p w →p (Factual z)=p (Factual w) :=
        hOrbitKernelTransport a K p Factual (range αc) (fun k z=>hprojG k.val z) hKProjection hCBaseKernel
      have hEntireClosureKernel : ∀z∈closure D,∀w∈closure D,p z=p w →p (Factual z)=p (Factual w) := by
        intro z hz w hw hzw
        by_cases hzu : p z∈U
        · have hwu : p w∈U := hzw ▸ hzu
          exact hFullSeamKernel z ⟨hz,hzu⟩ w ⟨hw,hwu⟩ hzw
        · have hwu : p w∉U := hzw ▸ hzu
          exact hCKernel z (hCOnly z hz hzu) w (hCOnly w hw hwu) hzw
      let Pbar : ↥(closure D) → ↥(U∪c.image) := fun z=>⟨p z.val,hClImage z.val z.property⟩
      let Fbar : ↥(closure D) → ↥(closure D) := fun z=>⟨Factual z.val,by exact hClPres.subset ⟨z.val,z.property,rfl⟩⟩
      have hPbar : Function.Surjective Pbar := by
        intro y
        rcases y.property with hy|hy
        · have hh : y.val∈p '' Sactual := by change y.val∈p '' (closure D∩p ⁻¹' U);rw [hpS];exact hy
          obtain ⟨z,hz,hzy⟩ := hh
          exact ⟨⟨z,hz.1⟩,Subtype.ext hzy⟩
        · have hh : y.val∈p '' range αc := by rw [hcimage];exact hy
          obtain ⟨z,hz,hzy⟩ := hh
          exact ⟨⟨z,frontier_subset_closure (hcfront hz)⟩,Subtype.ext hzy⟩
      have hFbar : Function.Involutive Fbar := fun z=>Subtype.ext (hFInv z.val)
      have hPbarKernel : ∀z w : ↥(closure D),Pbar z=Pbar w →Pbar (Fbar z)=Pbar (Fbar w) := by
        intro z w hzw
        exact Subtype.ext (hEntireClosureKernel z.val z.property w.val w.property (congrArg (fun y : ↥(U∪c.image)=>y.val) hzw))
      obtain ⟨τUbar,hτUbar,hτUbarLift⟩ := hFibreEquivDescent Pbar Fbar hPbar hFbar hPbarKernel
      have hτUbarLiftVal (z : H2) (hz : z∈closure D) : ∃hpz : p z∈U∪c.image,(τUbar ⟨p z,hpz⟩).val=p (Factual z) :=
        ⟨hClImage z hz,congrArg (fun y : ↥(U∪c.image)=>y.val) (hτUbarLift ⟨z,hz⟩)⟩
      have hCOrbitActual : ∀z∈Ccarrier,∀w∈Ccarrier,p z=p w →∃k : K,@SMul.smul G H2 a.toSMul k.val w=z := by
        have hpK : ∀k : K,∀z : H2,p (@SMul.smul K H2 bK.toSMul k z)=p z := fun k z=>hprojG k.val z
        rcases hcshift with hs|hs
        · have hs' : ∀t : ℝ,@SMul.smul K H2 bK.toSMul δcK (αc t)=αc (t+Tc) := hs
          exact @hPrimitiveAxisFibreOrbit K H2 E _ bK p αc Tc δcK hs' hcfibre hpK
        · have hs' : ∀t : ℝ,@SMul.smul K H2 bK.toSMul δcK⁻¹ (αc t)=αc (t+Tc) := hs
          exact @hPrimitiveAxisFibreOrbit K H2 E _ bK p αc Tc δcK⁻¹ hs' hcfibre hpK
      have hNoCFixed (y : ↥(U∪c.image)) (hy : y.val∈c.image) : τUbar y≠y := by
        intro hfix
        obtain ⟨z,hzy⟩ := hPbar y
        have hpz : p z.val=y.val := congrArg (fun v : ↥(U∪c.image)=>v.val) hzy
        have hnotU : p z.val∉U := fun hu=>Set.disjoint_left.mp hUc hu (hpz ▸ hy)
        have hzC : z.val∈Ccarrier := hCOnly z.val z.property hnotU
        have hfzCl : Factual z.val∈closure D := (Fbar z).property
        have hFnotU : p (Factual z.val)∉U := by
          intro hu
          have hh := hFS ⟨Factual z.val,⟨hfzCl,hu⟩⟩
          change Factual (Factual z.val)∈closure D∩p ⁻¹' U at hh
          rw [hFInv] at hh
          exact hnotU hh.2
        have hfzC : Factual z.val∈Ccarrier := hCOnly _ hfzCl hFnotU
        have hfixz : τUbar (Pbar z)=Pbar z := by rw [hzy];exact hfix
        have hpFix : p (Factual z.val)=p z.val :=
          congrArg (fun v : ↥(U∪c.image)=>v.val) ((hτUbarLift z).symm.trans hfixz)
        obtain ⟨k,hk⟩ := hCOrbitActual (Factual z.val) hfzC z.val hzC hpFix
        have hqFix : qcl (Fbar z)=qcl z := by
          apply hqcl.apply_eq_iff_mem_orbit.mpr
          refine ⟨k,?_⟩
          apply Subtype.ext
          change (@SMul.smul K ↥(closure D) bc.toSMul k z).val=Factual z.val
          rw [hbcCl]
          exact hk
        have hclFix : τcl (qcl z)=qcl z := (hLiftCl z (Fbar z) rfl).trans hqFix
        have hcEq := (hUniqueCl (qcl z)).mp hclFix
        obtain ⟨k,hk⟩ := hqcl.apply_eq_iff_mem_orbit.mp hcEq
        have hzEq : @SMul.smul G H2 a.toSMul k.val (eN.symm UpperHalfPlane.I)=z.val :=
          (hbcCl k ⟨eN.symm UpperHalfPlane.I,hCenterCl⟩).symm.trans (congrArg (fun v : ↥(closure D)=>v.val) hk)
        have hKD : (fun v=>@SMul.smul G H2 a.toSMul k.val v) '' D=D := MulAction.mem_stabilizer_iff.mp k.property
        have hzD : z.val∈D := by exact hKD.subset ⟨eN.symm UpperHalfPlane.I,hCenterActual',hzEq⟩
        exact hnotU (hpD ⟨z.val,hzD,rfl⟩)
      let incU : U → ↥(U∪c.image) := fun y=>⟨y.val,Or.inl y.property⟩
      have hincU : Function.Injective incU := fun y z hh=>Subtype.ext (congrArg (fun v : ↥(U∪c.image)=>v.val) hh)
      have hIncSquare (y : U) : τUbar (incU y)=incU (τUH y) := by
        obtain ⟨z,hzy⟩ := hPs y
        have hh : Pbar ⟨z.val,z.property.1⟩=incU (Ps z) := rfl
        rw [←hzy,←hh,hτUbarLift]
        apply Subtype.ext
        exact (congrArg (fun v : U=>v.val) (hτULift z)).symm
      let embU : U ↪ ↥(U∪c.image) := ⟨incU,hincU⟩
      let FbarFixed : Finset ↥(U∪c.image) := FU.map embU
      have hFbarCard : FbarFixed.card=3 := by rw [Finset.card_map];exact hFUCard
      have hFbarSet : (FbarFixed:Set ↥(U∪c.image))={y | τUbar y=y} := by
        ext y
        change y∈FU.map embU ↔ τUbar y=y
        constructor
        · intro hy
          obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hy
          have hufix : τUH u=u := by change u∈(FU:Set U) at hu;rw [hFU] at hu;exact hu
          change τUbar (incU u)=incU u
          rw [hIncSquare,hufix]
        · intro hy
          by_cases hyU : y.val∈U
          · let u : U := ⟨y.val,hyU⟩
            have hiy : incU u=y := rfl
            have hufix : τUH u=u := hincU ((hIncSquare u).symm.trans (by rw [hiy];exact hy))
            have hu : u∈FU := by change u∈(FU:Set U);rw [hFU];exact hufix
            exact Finset.mem_map.mpr ⟨u,hu,hiy⟩
          · exact (hNoCFixed y (y.property.resolve_left hyU) hy).elim
      have hPC : ∀y : ↥(U∪c.image),y.val∈c.image →(τUbar y).val∈c.image := by
        intro y hy
        by_contra hnot
        have hτUin : (τUbar y).val∈U := (τUbar y).property.resolve_right hnot
        let u : U := ⟨(τUbar y).val,hτUin⟩
        have hui : incU u=τUbar y := rfl
        have hback : τUbar (incU u)=y := by rw [hui,hτUbar]
        have hyU : y.val∈U := by rw [←hback,hIncSquare];exact (τUH u).property
        exact Set.disjoint_left.mp hUc hyU hy
      have hFcp (t : ℝ) : p (Factual (αc t))∈c.image := by
        let z : ↥(closure D) := ⟨αc t,frontier_subset_closure (hcfront (mem_range_self t))⟩
        have hpz : (Pbar z).val∈c.image := by change p (αc t)∈c.image;rw [←hcimage];exact ⟨αc t,mem_range_self t,rfl⟩
        have hh := hPC (Pbar z) hpz
        rw [hτUbarLift] at hh
        exact hh
      have hFcImage : p '' range (fun t : ℝ=>Factual (αc t))⊆p '' range αc := by
        rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
        rw [hcimage]
        exact hFcp t
      have hf0cl : Factual (αc 0)∈closure D :=
        hClPres.subset ⟨αc 0,frontier_subset_closure (hcfront (mem_range_self 0)),rfl⟩
      have hnotU0 : p (Factual (αc 0))∉U := fun hu=>Set.disjoint_left.mp hUc hu (hFcp 0)
      obtain ⟨k,_,⟨s₀,rfl⟩,hks⟩ := Set.mem_iUnion.mp (hCOnly _ hf0cl hnotU0)
      let kIso : H2 ≃ᵢ H2 := {toEquiv:=@MulAction.toPerm G H2 _ a k.val,isometry_toFun:=hisoG k.val}
      let Hc : H2 ≃ᵢ H2 := Factual.trans kIso.symm
      have hHcp (t : ℝ) : p (Hc (αc t))=p (Factual (αc t)) := by
        change p (@SMul.smul G H2 a.toSMul k.val⁻¹ (Factual (αc t)))=p (Factual (αc t))
        exact hprojG k.val⁻¹ _
      have hHc0 : Hc (αc 0)=αc s₀ := by
        apply kIso.injective
        change kIso (kIso.symm (Factual (αc 0)))=kIso (αc s₀)
        rw [kIso.apply_symm_apply]
        exact hks.symm
      have hHcImage : p '' range (fun t : ℝ=>Hc (αc t))⊆p '' range αc := by
        rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
        rw [hHcp,hcimage]
        exact hFcp t
      have hHcRange : Hc '' range αc=range αc := by
        have hh := hMeetLines p hq.isCoveringMap αc (fun t : ℝ=>Hc (αc t)) hαc (Hc.isometry.comp hαc) Tc hTc hcfibre hHcImage
          ⟨αc s₀,mem_range_self s₀,⟨0,hHc0⟩⟩
        exact (Set.range_comp Hc αc).symm.trans hh
      obtain ⟨cphase,hcphase⟩ := hSignedPhase αc αc hαc hαc Hc hHcRange
      let Pclock : ℝ → ↥(U∪c.image) := fun t=>⟨p (αc t),Or.inr (by rw [←hcimage];exact ⟨αc t,mem_range_self t,rfl⟩)⟩
      have hPclockFibre : ∀s t : ℝ,Pclock s=Pclock t ↔∃n : ℤ,s=t+n*Tc := by
        intro s t
        rw [Subtype.ext_iff]
        exact hcfibre s t
      have hPclockLift (t : ℝ) : (τUbar (Pclock t)).val=p (Factual (αc t)) := by
        obtain ⟨hp,hh⟩ := hτUbarLiftVal (αc t) (frontier_subset_closure (hcfront (mem_range_self t)))
        exact hh
      have hPclockNo (t : ℝ) : τUbar (Pclock t)≠Pclock t := hNoCFixed _ (by change p (αc t)∈c.image;rw [←hcimage];exact ⟨αc t,mem_range_self t,rfl⟩)
      have hPosClock : ∀t : ℝ,τUbar (Pclock t)=Pclock (t+cphase) := by
        rcases hcphase with hp|hm
        · intro t
          apply Subtype.ext
          rw [hPclockLift,←hHcp,hp]
        · exfalso
          apply hPclockNo (cphase/2)
          apply Subtype.ext
          rw [hPclockLift,←hHcp,hm]
          change p (αc (cphase-cphase/2))=p (αc (cphase/2))
          congr 2
          ring
      have hCPrimitiveHalfPeriod (t : ℝ) : ∃ht : p (αc t)∈U∪c.image,
          (τUbar ⟨p (αc t),ht⟩).val=p (αc (t+Tc/2)) :=
        ⟨(Pclock t).property,congrArg (fun v : ↥(U∪c.image)=>v.val)
          (hHalfPeriod Pclock τUbar Tc cphase hPclockFibre hPosClock hτUbar hPclockNo t)⟩
      have hUbarClosure : closure U=U∪c.image := by rw [closure_eq_self_union_frontier,hfrontU]
      have hRelativeWindow : ∀y : ↥(U∪c.image),∃z : H2,p z=y.val ∧ ∃W : Set H2,∃hW : IsOpen W,
          z∈W ∧ ∀w : H2,∀hw : w∈W,∀hpw : p w∈U∪c.image,(τUbar ⟨p w,hpw⟩).val=p (Factual w) := by
        intro y
        by_cases hyU : y.val∈U
        · obtain ⟨z,hzy,W,hW,hzW,hWU,hLift⟩ := hWindow ⟨y.val,hyU⟩
          refine ⟨z,hzy,W,hW,hzW,?_⟩
          intro w hw hpw
          have hwU : p w∈U := hWU hw
          have hh := hIncSquare ⟨p w,hwU⟩
          have hv := congrArg (fun v : ↥(U∪c.image)=>v.val) hh
          exact hv.trans (hLift w hw)
        · have hyc : y.val∈c.image := y.property.resolve_left hyU
          have hyimage : y.val∈p '' range αc := by rw [hcimage];exact hyc
          obtain ⟨z,hz,hzy⟩ := hyimage
          obtain ⟨W,hW,hzW,hWd,hWcl⟩ := actual_c_relative_closure_window a p hq c d U V hU hV hUV hcover hfrontU hfrontV hdU hcd x hxW z (hcfront hz) (hzy ▸ hyc)
          refine ⟨z,hzy,W,hW,hzW,?_⟩
          intro w hw hpw
          have hwCl : w∈closure D := hWcl w hw (by rw [hUbarClosure];exact hpw)
          obtain ⟨hpu,hh⟩ := hτUbarLiftVal w hwCl
          exact hh
      have hUbarContinuous : Continuous τUbar := hContinuousRelativeWindows p hq.isCoveringMap (U∪c.image) τUbar Factual Factual.continuous hRelativeWindow
      have hUbarInverse : (τUbar.symm : ↥(U∪c.image) → ↥(U∪c.image))=τUbar := by
        funext y
        apply τUbar.injective
        exact (τUbar.apply_symm_apply y).trans (hτUbar y).symm
      let τUbarH : ↥(U∪c.image) ≃ₜ ↥(U∪c.image) := {
        toEquiv := τUbar,continuous_toFun := hUbarContinuous,
        continuous_invFun := by change Continuous (τUbar.symm : ↥(U∪c.image) → ↥(U∪c.image));rw [hUbarInverse];exact hUbarContinuous }
      have hUbarMetric := hMetricRelativeWindows p hq.isCoveringMap (U∪c.image) τUbar Factual hmetric hRelativeWindow
      obtain ⟨eClock,hClockParam,hClockRest⟩ := hActualProjectedReflectionTwoFixed
        ⟨p,hq.isCoveringMap.continuous⟩ ⟨αc,hαc.continuous⟩ Tc hTc hcfibre 0
      let eC : Circle ≃ₜ c.image := eClock.trans (Homeomorph.setCongr hcimage)
      have heC (t : ℝ) : (eC (Circle.exp (2*Real.pi*t/Tc))).val=p (αc t) := hClockParam t
      obtain ⟨φc,hφc,hφcHom⟩ := hOriginalHalfPeriodOrientation c U (fun t=>p (αc t)) Tc hTc eC heC τUbarH hCPrimitiveHalfPeriod
      have hDbarSquare (y : d.image) : ∃hy : y.val∈U∪c.image,
          (τUbarH ⟨y.val,hy⟩).val=(τd y).val := by
        refine ⟨Or.inl (hdU y.property),?_⟩
        exact (congrArg (fun z : ↥(U∪c.image)=>z.val) (hIncSquare (fD y))).trans
          (congrArg (fun z : U=>z.val) (hDSquare y))
      let uD : Circle := Circle.exp (-2*Real.pi*phase/T₀)
      have hDfullClock (z : Circle) : τd (eD z)=eD (uD*z⁻¹) := by
        obtain ⟨θ,rfl⟩ := Circle.exp_surjective z
        let t : ℝ := T₀*θ/(2*Real.pi)
        have harg : 2*Real.pi*t/T₀=θ := by dsimp [t];field_simp
        have harg2 : 2*Real.pi*(-t-phase)/T₀=(-2*Real.pi*phase/T₀)+(-θ) := by dsimp [t];field_simp;ring
        rw [←harg,hτDClock,harg,harg2,Circle.exp_add,Circle.exp_neg]
      have hCExplicitWindows (t : ℝ) : ∃W : Set H2,IsOpen W ∧ αc t∈W ∧
          ∀w∈W,∀hpw : p w∈U∪c.image,(τUbarH ⟨p w,hpw⟩).val=p (Factual w) := by
        have hpc : p (αc t)∈c.image := by rw [←hcimage];exact ⟨αc t,mem_range_self t,rfl⟩
        obtain ⟨W,hW,hzW,hWd,hWcl⟩ := actual_c_relative_closure_window a p hq c d U V hU hV hUV hcover hfrontU hfrontV hdU hcd x hxW (αc t) (hcfront (mem_range_self t)) hpc
        refine ⟨W,hW,hzW,?_⟩
        intro w hw hpw
        have hwCl : w∈closure D := hWcl w hw (by rw [hUbarClosure];exact hpw)
        exact (hτUbarLiftVal w hwCl).2
      have hFCClock (t : ℝ) : p (Factual (αc t))=p (αc (t+Tc/2)) := by
        obtain ⟨ht,hh⟩ := hCPrimitiveHalfPeriod t
        exact (hτUbarLiftVal (αc t) (frontier_subset_closure (hcfront (mem_range_self t)))).2.symm.trans hh
      exact ⟨U,V,hU,hV,hUV,hcover,hfrontU,hfrontV,⟨e⟩,heV,hdU,
        αc,Tc,hαc,hTc,hcimage,hcfibre,Factual,τUbarH,hτUbar,τd,hτd,Fd,hFdCard,hFd,hDbarSquare,eD,uD,hDfullClock,hCExplicitWindows,hFCClock,hRelativeWindow,hNoCFixed,
        FbarFixed,hFbarCard,hFbarSet,hCPrimitiveHalfPeriod,hUbarMetric,φc,hφc,hφcHom⟩
    have hGlobalMetric {E G : Type} [MetricSpace E] [Group G]
        (a : MulAction G H2) (p : H2 → E) (hq : letI:=a;IsQuotientCoveringMap p G)
        (hiso : ∀g : G,Isometry (@SMul.smul G H2 a.toSMul g))
        (hm : ∀z : H2,∃W : Set H2,IsOpen W ∧ z∈W ∧ ∀u∈W,∀v∈W,dist (p u) (p v)=dist u v)
        (U V C : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
        (hunion : U∪V=Cᶜ) (hfrontU : frontier U=C) (hfrontV : frontier V=C)
        (α β : ℝ → H2) (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
        (hfα : ∀s t : ℝ,p (α s)=p (α t) ↔∃n : ℤ,s=t+n*T)
        (hαimage : p '' range α=C) (hβimage : p '' range β=C)
        (F₀ F₁ : H2 ≃ᵢ H2) (τ₀ : ↥(U∪C) ≃ₜ ↥(U∪C)) (τ₁ : ↥(V∪C) ≃ₜ ↥(V∪C))
        (hW₀ : ∀t : ℝ,∃W : Set H2,IsOpen W ∧ α t∈W ∧ ∀w∈W,∀hw : p w∈U∪C,(τ₀ ⟨p w,hw⟩).val=p (F₀ w))
        (hW₁ : ∀t : ℝ,∃W : Set H2,IsOpen W ∧ β t∈W ∧ ∀w∈W,∀hw : p w∈V∪C,(τ₁ ⟨p w,hw⟩).val=p (F₁ w))
        (hM₀ : ∀x : ↥(U∪C),∃W : Set ↥(U∪C),IsOpen W ∧ x∈W ∧ ∀u∈W,∀v∈W,dist (τ₀ u).val (τ₀ v).val=dist u.val v.val)
        (hM₁ : ∀x : ↥(V∪C),∃W : Set ↥(V∪C),IsOpen W ∧ x∈W ∧ ∀u∈W,∀v∈W,dist (τ₁ u).val (τ₁ v).val=dist u.val v.val)
        (J : E ≃ₜ E) (hJ₀ : ∀x : ↥(U∪C),J x.val=(τ₀ x).val) (hJ₁ : ∀x : ↥(V∪C),J x.val=(τ₁ x).val) :
        ∀y : E,∃N : Set E,IsOpen N ∧ y∈N ∧ ∀u∈N,∀v∈N,dist (J u) (J v)=dist u v := by
      have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
          (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
          (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
          (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
          (himage : p '' range β⊆p '' range α)
          (hmeet : (range α∩range β).Nonempty) : range β=range α := by
        have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
            (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
            (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
            (himage : p '' range β⊆p '' range α)
            (hmeet : (range α∩range β).Nonempty) : range β=range α := by
          have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
              (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
            have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                ∃f : C(Circle,E),IsEmbedding f ∧
                  (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                  range f=p '' range α := by
              classical
              let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
              have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
              let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
              have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                apply (hfibre _ _).mpr
                refine ⟨k,?_⟩
                rw [hk]
                field_simp
              have hψ : Continuous ψ := by
                apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                rw [heq]
                fun_prop
              let f : C(Circle,E) := ⟨ψ,hψ⟩
              have hfinj : Function.Injective f := by
                intro z w hzw
                obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                  have hπ : (2*Real.pi)≠0 := by positivity
                  have hT' : T≠0 := hT.ne'
                  field_simp at hk
                  nlinarith
                rw [←hθ z,←hθ w]
                exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
              have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                change _=ψ _
                rw [hfac]
                congr 2
                field_simp
              refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
              apply Subset.antisymm
              · rintro y ⟨z,rfl⟩
                exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
              · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
            obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
            change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
            let e : Circle ≃ₜ range f := hf.toHomeomorph
            let g : C(ℝ,Circle) :=
              ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
            let θ₀ := 2*Real.pi*s₀/T
            have hbase : Circle.exp θ₀=g t₀ := by
              apply e.injective
              apply Subtype.ext
              change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
              rw [e.apply_symm_apply]
              change f (Circle.exp θ₀)=p (β t₀)
              rw [←hparam,hmeet]
            obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
            have hL0 : L t₀=θ₀ := hL.1
            have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
            let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
            have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
              intro t
              change p (α (T*L t/(2*Real.pi)))=_
              rw [hparam]
              have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
              rw [harg,hLe]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
            have hℓbase : ℓ t₀=β t₀ := by
              change α (T*L t₀/(2*Real.pi))=β t₀
              rw [hL0]
              have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
              rw [harg,hmeet]
            have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
              (funext hℓproj) t₀ hℓbase
            rintro y ⟨t,rfl⟩
            exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
          have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
              range β=range α := by
            let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
            let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
            have hfac (t : ℝ) : α (f t)=β t :=
              congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
            have hf : Isometry f := by
              apply isometry_iff_dist_eq.mpr
              intro s t
              rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
            let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
            have hLin : Function.Injective A.toAffineMap.linear :=
              A.toAffineMap.linear_injective_iff.mpr hf.injective
            have hSur : Function.Surjective A.toAffineMap.linear :=
              LinearMap.surjective_of_injective hLin
            have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
            apply Subset.antisymm hsub
            rintro y ⟨t,rfl⟩
            obtain ⟨s,hs⟩ := hfsur t
            exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
          obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
          have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
            s t (hs.trans ht.symm)
          exact hLine α β hα hβ hsub
        exact hMeet p hp α β hα hβ T hT hfibre himage hmeet
      have hAway {E : Type} [MetricSpace E] (U C : Set E) (hU : IsOpen U)
          (τ : ↥(U∪C) → ↥(U∪C)) (J : E → E)
          (hJ : ∀x : ↥(U∪C),J x.val=(τ x).val)
          (hmetric : ∀x : ↥(U∪C),∃W : Set ↥(U∪C),IsOpen W ∧ x∈W ∧
            ∀u∈W,∀v∈W,dist (τ u).val (τ v).val=dist u.val v.val) :
          ∀y∈U,∃N : Set E,IsOpen N ∧ y∈N ∧ ∀u∈N,∀v∈N,dist (J u) (J v)=dist u v := by
        let inc : U → ↥(U∪C) := fun x=>⟨x.val,Or.inl x.property⟩
        have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
        intro y hy
        obtain ⟨W,hW,hyW,hM⟩ := hmetric (inc ⟨y,hy⟩)
        let Q : Set U := inc ⁻¹' W
        have hQ : IsOpen Q := hW.preimage hinc
        refine ⟨Subtype.val '' Q,hU.isOpenMap_subtype_val _ hQ,⟨⟨y,hy⟩,hyW,rfl⟩,?_⟩
        rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
        rw [hJ (inc u),hJ (inc v)]
        exact hM _ hu _ hv
      have hBranches {E : Type} [TopologicalSpace E] [T2Space E]
          (p : H2 → E) (hp : IsCoveringMap p) (α : ℝ → H2) (hα : Isometry α)
          (T : ℝ) (hT : 0<T) (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔∃n : ℤ,s=t+n*T)
          (U V C : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
          (hunion : U∪V=Cᶜ) (hfrontU : frontier U=C) (hfrontV : frontier V=C)
          (himage : p '' range α=C) (t₀ : ℝ) (N : Set H2) (hN : IsOpen N) (htN : α t₀∈N) :
          ∃eN : H2 ≃ᵢ H2,(∀t : ℝ,eN (α t)=verticalPath t) ∧
          ∃eH : H2 ≃ₜ ℝ×ℝ,(∀z : H2,eH z=(z.re,Real.log z.im)) ∧
          ∃δ : ℝ,0<δ ∧
            let B := eN.toHomeomorph.trans eH
            let q : ℝ×ℝ → E := p ∘ B.symm
            let R := Ioo (-δ) δ ×ˢ Ioo (t₀-δ) (t₀+δ)
            (∀x∈R,B.symm x∈N) ∧ (∀x∈R,q x∈C ↔x.1=0) ∧
            (((∀x∈R,0<x.1 →q x∈U) ∧ (∀x∈R,x.1<0 →q x∈V)) ∨
             ((∀x∈R,0<x.1 →q x∈V) ∧ (∀x∈R,x.1<0 →q x∈U))) := by
        have hRealChart : ∃e : H2 ≃ₜ ℝ×ℝ,
            (∀z : H2,e z=(z.re,Real.log z.im)) ∧
            (∀t : ℝ,e (verticalPath t)=(0,t)) := by
          let e : H2 ≃ₜ ℝ×ℝ := {
            toFun := fun z=>(z.re,Real.log z.im)
            invFun := fun x=>⟨⟨x.1,Real.exp x.2⟩,Real.exp_pos x.2⟩
            left_inv := by
              intro z
              apply UpperHalfPlane.ext_re_im
              · rfl
              · exact Real.exp_log z.im_pos
            right_inv := by
              intro x
              apply Prod.ext
              · rfl
              · exact Real.log_exp x.2
            continuous_toFun := UpperHalfPlane.continuous_re.prodMk
              (UpperHalfPlane.continuous_im.log (fun z=>z.im_pos.ne'))
            continuous_invFun := by
              have hc : Continuous (fun x : ℝ×ℝ=>(x.1:ℂ)+(Real.exp x.2:ℂ)*Complex.I) := by fun_prop
              have hc' : Continuous (fun x : ℝ×ℝ=>(⟨x.1,Real.exp x.2⟩ : ℂ)) :=
                hc.congr (fun x=>by apply Complex.ext <;> simp [Complex.exp_ofReal_re])
              exact hc'.upperHalfPlaneMk (fun x=>Real.exp_pos x.2) }
          refine ⟨e,fun _=>rfl,?_⟩
          intro t
          change (0,Real.log (Real.exp t))=(0,t)
          rw [Real.log_exp]
        have hAxisNormalize (α : ℝ → H2) (hα : Isometry α) :
            ∃e : H2 ≃ᵢ H2,∀t : ℝ,e (α t)=verticalPath t := by
          have hd : dist (α 0) (α 1)=1 := by rw [hα.dist_eq,Real.dist_eq];norm_num
          obtain ⟨A,hA0,hA1⟩ := axis_exists_ordered_pair_matrix (α 0) (α 1) hd
          let g : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
          have hzero : verticalPath 0=UpperHalfPlane.I := by
            apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
          have hg0 : g (verticalPath 0)=α 0 := hzero ▸ hA0
          have hg1 : g (verticalPath 1)=α 1 := hA1
          refine ⟨g.symm,?_⟩
          exact isometry_eq_vertical_of_values (fun t=>g.symm (α t)) (g.symm.isometry.comp hα)
            (by rw [←hg0,g.symm_apply_apply]) (by rw [←hg1,g.symm_apply_apply])
        have hOppositeSides {E : Type} [TopologicalSpace E]
            (q : ℝ×ℝ → E) (hq : Continuous q) (hqo : IsOpenMap q)
            (U V C : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
            (hunion : U∪V=Cᶜ) (hfrontU : frontier U=C) (hfrontV : frontier V=C)
            (O : Set (ℝ×ℝ)) (hO : IsOpen O) (t : ℝ) (h0 : (0,t)∈O)
            (hline : ∀x∈O,q x∈C ↔x.1=0) :
            ∃δ : ℝ,0<δ ∧
              (Ioo (-δ) δ ×ˢ Ioo (t-δ) (t+δ))⊆O ∧
              (((∀x∈Ioo (-δ) δ ×ˢ Ioo (t-δ) (t+δ),0<x.1 →q x∈U) ∧
                (∀x∈Ioo (-δ) δ ×ˢ Ioo (t-δ) (t+δ),x.1<0 →q x∈V)) ∨
               ((∀x∈Ioo (-δ) δ ×ˢ Ioo (t-δ) (t+δ),0<x.1 →q x∈V) ∧
                (∀x∈Ioo (-δ) δ ×ˢ Ioo (t-δ) (t+δ),x.1<0 →q x∈U))) := by
          obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO (0,t) h0
          let δ : ℝ := ε/2
          have hδ : 0<δ := by dsimp [δ];linarith
          have hδε : δ<ε := by dsimp [δ];linarith
          let R : Set (ℝ×ℝ) := Ioo (-δ) δ ×ˢ Ioo (t-δ) (t+δ)
          have hR : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
          have h0R : (0,t)∈R := ⟨⟨by linarith, hδ⟩,⟨by linarith,by linarith⟩⟩
          have hRO : R⊆O := by
            intro x hx
            apply hball
            rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero]
            apply max_lt
            · exact lt_trans (abs_lt.mpr hx.1) hδε
            · exact lt_trans (abs_lt.mpr ⟨by linarith [hx.2.1],by linarith [hx.2.2]⟩) hδε
          let P : Set (ℝ×ℝ) := Ioo 0 δ ×ˢ Ioo (t-δ) (t+δ)
          let N : Set (ℝ×ℝ) := Ioo (-δ) 0 ×ˢ Ioo (t-δ) (t+δ)
          have hPc : IsConnected P := (isConnected_Ioo hδ).prod (isConnected_Ioo (by linarith : t-δ<t+δ))
          have hNc : IsConnected N := (isConnected_Ioo (by linarith : -δ<0)).prod (isConnected_Ioo (by linarith : t-δ<t+δ))
          have hPR : P⊆R := fun x hx=>⟨⟨by linarith [hx.1.1],hx.1.2⟩,hx.2⟩
          have hNR : N⊆R := fun x hx=>⟨⟨hx.1.1,by linarith [hx.1.2]⟩,hx.2⟩
          have hpart (x : ℝ×ℝ) (hx : x∈R) (hx0 : x.1≠0) : q x∈U∪V := by
            rw [hunion]
            exact fun hc=>hx0 ((hline x (hRO hx)).mp hc)
          have hPpart : P⊆q ⁻¹' U ∪ q ⁻¹' V := by
            intro x hx
            exact hpart x (hPR hx) hx.1.1.ne'
          have hNpart : N⊆q ⁻¹' U ∪ q ⁻¹' V := by
            intro x hx
            exact hpart x (hNR hx) hx.1.2.ne
          have hassign (S : Set (ℝ×ℝ)) (hS : IsConnected S) (hpart : S⊆q ⁻¹' U ∪q ⁻¹' V) :
              S⊆q ⁻¹' U ∨ S⊆q ⁻¹' V := by
            obtain ⟨x,hx⟩ := hS.nonempty
            rcases hpart hx with hxU|hxV
            · exact Or.inl (hS.isPreconnected.subset_left_of_subset_union (hU.preimage hq) (hV.preimage hq)
                (hUV.preimage q) hpart ⟨x,hx,hxU⟩)
            · exact Or.inr (hS.isPreconnected.subset_right_of_subset_union (hU.preimage hq) (hV.preimage hq)
                (hUV.preimage q) hpart ⟨x,hx,hxV⟩)
          have hmeet (A : Set E) (hfrontA : frontier A=C) (hA : A⊆Cᶜ) : ∃x∈P∪N,q x∈A := by
            have hc : q (0,t)∈C := (hline (0,t) h0).mpr rfl
            have hcl : (0,t)∈closure (q ⁻¹' A) := hqo.preimage_closure_subset_closure_preimage
              (frontier_subset_closure (hfrontA.symm ▸ hc))
            obtain ⟨x,hxR,hxA⟩ := mem_closure_iff.mp hcl R hR h0R
            have hx0 : x.1≠0 := fun hz=>(hA hxA) ((hline x (hRO hxR)).mpr hz)
            rcases lt_or_gt_of_ne hx0 with hn|hp
            · exact ⟨x,Or.inr ⟨⟨hxR.1.1,hn⟩,hxR.2⟩,hxA⟩
            · exact ⟨x,Or.inl ⟨⟨hp,hxR.1.2⟩,hxR.2⟩,hxA⟩
          have hUs : U⊆Cᶜ := hunion ▸ subset_union_left
          have hVs : V⊆Cᶜ := hunion ▸ subset_union_right
          obtain ⟨u,hu,huU⟩ := hmeet U hfrontU hUs
          obtain ⟨v,hv,hvV⟩ := hmeet V hfrontV hVs
          have hnotU (hP : P⊆q ⁻¹' U) (hN : N⊆q ⁻¹' U) : False := by
            rcases hv with hvP|hvN
            · exact disjoint_left.mp hUV (hP hvP) hvV
            · exact disjoint_left.mp hUV (hN hvN) hvV
          have hnotV (hP : P⊆q ⁻¹' V) (hN : N⊆q ⁻¹' V) : False := by
            rcases hu with huP|huN
            · exact disjoint_left.mp hUV huU (hP huP)
            · exact disjoint_left.mp hUV huU (hN huN)
          have hpos (x : ℝ×ℝ) (hx : x∈R) (hp : 0<x.1) : x∈P := ⟨⟨hp,hx.1.2⟩,hx.2⟩
          have hneg (x : ℝ×ℝ) (hx : x∈R) (hn : x.1<0) : x∈N := ⟨⟨hx.1.1,hn⟩,hx.2⟩
          refine ⟨δ,hδ,hRO,?_⟩
          rcases hassign P hPc hPpart with hP|hP
          · rcases hassign N hNc hNpart with hN|hN
            · exact False.elim (hnotU hP hN)
            · exact Or.inl ⟨fun x hx hp=>hP (hpos x hx hp),fun x hx hn=>hN (hneg x hx hn)⟩
          · rcases hassign N hNc hNpart with hN|hN
            · exact Or.inr ⟨fun x hx hp=>hP (hpos x hx hp),fun x hx hn=>hN (hneg x hx hn)⟩
            · exact False.elim (hnotV hP hN)
        obtain ⟨eN,hNorm⟩ := hAxisNormalize α hα
        obtain ⟨eH,hE,hVert⟩ := hRealChart
        let B : H2 ≃ₜ ℝ×ℝ := eN.toHomeomorph.trans eH
        let q : ℝ×ℝ → E := p ∘ B.symm
        have hBα (t : ℝ) : B (α t)=(0,t) := by
          change eH (eN (α t))=(0,t)
          rw [hNorm,hVert]
        have hBsym (t : ℝ) : B.symm (0,t)=α t := by
          apply B.injective
          rw [B.apply_symm_apply,hBα]
        have hBad : IsClosed (p ⁻¹' C \ range α) := by
          rw [←himage]
          exact actual_primitive_axis_other_lift_union_is_closed p hp α hα T hT hfibre
        let O : Set (ℝ×ℝ) := B.symm ⁻¹' ((p ⁻¹' C \ range α)ᶜ ∩ N)
        have hO : IsOpen O := (hBad.isOpen_compl.inter hN).preimage B.symm.continuous
        have h0 : (0,t₀)∈O := by
          change B.symm (0,t₀)∈(p ⁻¹' C \ range α)ᶜ ∩ N
          rw [hBsym]
          exact ⟨fun hh=>hh.2 (mem_range_self t₀),htN⟩
        have hline (x : ℝ×ℝ) (hx : x∈O) : q x∈C ↔x.1=0 := by
          constructor
          · intro hxc
            have hrange : B.symm x∈range α := by
              by_contra hnot
              exact hx.1 ⟨hxc,hnot⟩
            obtain ⟨s,hs⟩ := hrange
            have hh := congrArg B hs
            rw [B.apply_symm_apply,hBα] at hh
            exact (congrArg Prod.fst hh).symm
          · intro hx0
            have hxs : x=(0,x.2) := by apply Prod.ext <;> simp [hx0]
            change p (B.symm x)∈C
            rw [hxs,hBsym,←himage]
            exact ⟨α x.2,mem_range_self x.2,rfl⟩
        have hqcont : Continuous q := hp.continuous.comp B.symm.continuous
        have hqopen : IsOpenMap q := hp.isOpenMap.comp B.symm.isOpenMap
        obtain ⟨δ,hδ,hRO,hSides⟩ := hOppositeSides q hqcont hqopen U V C hU hV hUV hunion hfrontU hfrontV O hO t₀ h0 hline
        refine ⟨eN,hNorm,eH,hE,δ,hδ,?_,?_,hSides⟩
        · intro x hx
          exact (hRO hx).2
        · intro x hx
          exact hline x (hRO hx)
      have hSeamMetric {E G : Type} [MetricSpace E] [Group G]
          (a : MulAction G H2) (p : H2 → E) (hq : letI:=a;IsQuotientCoveringMap p G) (p₀ : H2 → E)
          (hiso : ∀g : G,Isometry (@SMul.smul G H2 a.toSMul g))
          (hp₀ : IsCoveringMap p₀)
          (hmetric₀ : ∀v : H2,∃N : Set H2,IsOpen N ∧ v∈N ∧
            ∀u∈N,∀w∈N,dist (p₀ u) (p₀ w)=dist u w)
          (hmetric : ∀v : H2,∃N : Set H2,IsOpen N ∧ v∈N ∧
            ∀u∈N,∀w∈N,dist (p u) (p w)=dist u w)
          (f₀ f₁ : H2 ≃ᵢ H2)
          (hboundary : ∀t : ℝ,p (f₀ (verticalPath t))=p (f₁ (verticalPath t)))
          (J : E → E) (hJinj : Function.Injective J) (W : Set H2) (hW : IsOpen W)
          (hpW : Set.InjOn p₀ W) (v : H2) (hv : v∈W)
          (z : H2) (hzpos : 0<z.re) (hzW : z∈W)
          (hrefW : (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2)∈W)
          (hj₀ : ∀w∈W,0<w.re → J (p₀ w)=p (f₀ w))
          (hj₁ : ∀w∈W,w.re≤0 → J (p₀ w)=p (f₁ w)) :
          ∃N : Set E,IsOpen N ∧ p₀ v∈N ∧
            ∀u∈N,∀w∈N,dist (J u) (J w)=dist u w := by
        have hAlign {E G : Type} [TopologicalSpace E] [T2Space E] [Group G]
            (a : MulAction G H2) (p : H2 → E) (hq : letI:=a;IsQuotientCoveringMap p G) (p₀ : H2 → E)
            (hiso : ∀g : G,Isometry (@SMul.smul G H2 a.toSMul g))
            (f₀ f₁ : H2 ≃ᵢ H2)
            (hboundary : ∀t : ℝ,p (f₀ (verticalPath t))=p (f₁ (verticalPath t)))
            (J : E → E) (hJinj : Function.Injective J) (W : Set H2) (hpW : Set.InjOn p₀ W)
            (z : H2) (hzpos : 0<z.re) (hzW : z∈W)
            (hrefW : (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2)∈W)
            (hj₀ : ∀w∈W,0<w.re → J (p₀ w)=p (f₀ w))
            (hj₁ : ∀w∈W,w.re≤0 → J (p₀ w)=p (f₁ w)) :
            ∃η : G,∀w : H2,@SMul.smul G H2 a.toSMul η (f₁ w)=f₀ w := by
          have hRigid (f₀ f₁ : H2 ≃ᵢ H2) (haxis : ∀t : ℝ,f₀ (verticalPath t)=f₁ (verticalPath t))
              (W : Set H2) (j : H2 → H2) (hjinj : Set.InjOn j W)
              (z : H2) (hzpos : 0<z.re) (hzW : z∈W)
              (hrefW : (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2)∈W)
              (hj₀ : j z=f₀ z) (hj₁ : j (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2)=f₁ (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2)) :
              f₀=f₁ := by
            have hBranches (g : H2 ≃ᵢ H2) (L : ℝ) (hclock : ∀t : ℝ,g (verticalPath t)=verticalPath (t+L)) :
                let D : SL(2,ℝ) := ⟨!![Real.exp (L/2),0;0,Real.exp (-(L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
                let ref : H2 → H2 := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
                (∀z : H2,g z=D • z) ∨ (∀z : H2,g z=D • ref z) := by
              intro D ref
              have hRigid (g : H2 → H2) (hg : Isometry g)
                  (h0 : g (verticalPath 0)=verticalPath 0)
                  (h1 : g (verticalPath 1)=verticalPath 1)
                  (z₀ : H2) (hz₀ : z₀.re≠0) (hfix : g z₀=z₀) : ∀z : H2,g z=z := by
                have hCoordinates (z w : H2)
                    (h0 : dist (verticalPath 0) z=dist (verticalPath 0) w)
                    (h1 : dist (verticalPath 1) z=dist (verticalPath 1) w) :
                    z.im=w.im ∧ z.re^2=w.re^2 := by
                  have hc0 := congrArg Real.cosh h0
                  have hc1 := congrArg Real.cosh h1
                  rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc0 hc1
                  simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
                    Real.exp_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub,neg_sq,zero_add,mul_one] at hc0 hc1
                  have hz : 0<z.im := z.im_pos
                  have hw : 0<w.im := w.im_pos
                  have hb : 1<Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
                  have he0 : w.im*(z.re^2+z.im^2+1)=z.im*(w.re^2+w.im^2+1) := by
                    field_simp at hc0
                    nlinarith [hc0]
                  have he1 : w.im*(z.re^2+z.im^2+(Real.exp (1:ℝ))^2)=
                      z.im*(w.re^2+w.im^2+(Real.exp (1:ℝ))^2) := by
                    field_simp at hc1
                    nlinarith [hc1]
                  have him : z.im=w.im := by
                    have hp : 0<(Real.exp (1:ℝ))^2-1 := by nlinarith
                    have hf : ((Real.exp (1:ℝ))^2-1)*(z.im-w.im)=0 := by nlinarith [he0,he1]
                    have hh := (mul_eq_zero.mp hf).resolve_left hp.ne'
                    exact sub_eq_zero.mp hh
                  refine ⟨him,?_⟩
                  rw [him] at he0
                  have hh : w.im*(z.re^2-w.re^2)=0 := by nlinarith [he0]
                  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw.ne')
                intro z
                have hc := hCoordinates (g z) z (by simpa only [h0] using hg.dist_eq (verticalPath 0) z)
                  (by simpa only [h1] using hg.dist_eq (verticalPath 1) z)
                have hd := congrArg Real.cosh (hg.dist_eq z z₀)
                rw [hfix,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hd
                rw [hc.1] at hd
                have hp : z₀.re*((g z).re-z.re)=0 := by
                  field_simp at hd
                  nlinarith [hc.2]
                have hre : (g z).re=z.re := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hz₀)
                exact UpperHalfPlane.ext_re_im hre hc.1
              have hCoordinates (z w : H2)
                  (h0 : dist (verticalPath 0) z=dist (verticalPath 0) w)
                  (h1 : dist (verticalPath 1) z=dist (verticalPath 1) w) :
                  z.im=w.im ∧ z.re^2=w.re^2 := by
                have hc0 := congrArg Real.cosh h0
                have hc1 := congrArg Real.cosh h1
                rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc0 hc1
                simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
                  Real.exp_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_sub,neg_sq,zero_add,mul_one] at hc0 hc1
                have hz : 0<z.im := z.im_pos
                have hw : 0<w.im := w.im_pos
                have hb : 1<Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
                have he0 : w.im*(z.re^2+z.im^2+1)=z.im*(w.re^2+w.im^2+1) := by
                  field_simp at hc0
                  nlinarith [hc0]
                have he1 : w.im*(z.re^2+z.im^2+(Real.exp (1:ℝ))^2)=
                    z.im*(w.re^2+w.im^2+(Real.exp (1:ℝ))^2) := by
                  field_simp at hc1
                  nlinarith [hc1]
                have him : z.im=w.im := by
                  have hp : 0<(Real.exp (1:ℝ))^2-1 := by nlinarith
                  have hf : ((Real.exp (1:ℝ))^2-1)*(z.im-w.im)=0 := by nlinarith [he0,he1]
                  have hh := (mul_eq_zero.mp hf).resolve_left hp.ne'
                  exact sub_eq_zero.mp hh
                refine ⟨him,?_⟩
                rw [him] at he0
                have hh : w.im*(z.re^2-w.re^2)=0 := by nlinarith [he0]
                exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw.ne')
              have hDiagonal (s : ℝ) :
                  let D : SL(2,ℝ) := ⟨!![Real.exp (s/2),0;0,Real.exp (-(s/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
                  ∀z : H2,(D • z).re=Real.exp s*z.re ∧ (D • z).im=Real.exp s*z.im := by
                intro D
                intro z
                have hc : ((D • z : H2) : ℂ)=
                    (Real.exp s : ℂ)*(z:ℂ) := by
                  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
                  simp [D,UpperHalfPlane.num,UpperHalfPlane.denom]
                  rw [div_eq_mul_inv,←Complex.exp_neg]
                  simp only [neg_neg]
                  rw [mul_right_comm,←Complex.exp_add]
                  congr 2
                  ring
                constructor
                · simpa [Complex.mul_re,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.re hc
                · simpa [Complex.mul_im,Complex.exp_ofReal_re,Complex.exp_ofReal_im] using congrArg Complex.im hc
              let Dm : SL(2,ℝ) := ⟨!![Real.exp (-L/2),0;0,Real.exp (-(-L/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
              let g' : H2 ≃ᵢ H2 := g.trans (IsometryEquiv.constSMul Dm)
              have hDm (z : H2) : (Dm • z).re=Real.exp (-L)*z.re ∧ (Dm • z).im=Real.exp (-L)*z.im :=
                hDiagonal (-L) z
              have hD (z : H2) : (D • z).re=Real.exp L*z.re ∧ (D • z).im=Real.exp L*z.im :=
                hDiagonal L z
              have hnormclock (t : ℝ) : g' (verticalPath t)=verticalPath t := by
                change Dm • g (verticalPath t)=verticalPath t
                rw [hclock]
                apply UpperHalfPlane.ext_re_im
                · rw [(hDm _).1];simp [verticalPath]
                · rw [(hDm _).2]
                  simp only [verticalPath,UpperHalfPlane.mk_im]
                  rw [←Real.exp_add]
                  congr 1;ring
              have hrefInv (z : H2) : ref (ref z)=z := by
                apply UpperHalfPlane.ext_re_im
                · change -(-z.re)=z.re
                  ring
                · rfl
              have hrefIso : Isometry ref := by
                apply Isometry.of_dist_eq
                intro z w
                apply Real.cosh_injOn dist_nonneg dist_nonneg
                rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
                simp only [ref,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im]
                congr 1
                ring
              let refIso : H2 ≃ᵢ H2 := {
                toFun := ref
                invFun := ref
                left_inv := hrefInv
                right_inv := hrefInv
                isometry_toFun := hrefIso }
              have hrefVertical (t : ℝ) : ref (verticalPath t)=verticalPath t := by
                apply UpperHalfPlane.ext_re_im
                · simp [ref,verticalPath]
                · rfl
              have hUnwind (r : H2 → H2) (hh : ∀z,g' z=r z) : ∀w,g w=D • r w := by
                intro w
                have hwre : Real.exp (-L)*(g w).re=(r w).re :=
                  (hDm (g w)).1.symm.trans (congrArg UpperHalfPlane.re (hh w))
                have hwim : Real.exp (-L)*(g w).im=(r w).im :=
                  (hDm (g w)).2.symm.trans (congrArg UpperHalfPlane.im (hh w))
                have hprod : Real.exp L*Real.exp (-L)=1 := by rw [←Real.exp_add];simp
                have hr := congrArg (fun r : ℝ => Real.exp L*r) hwre
                have hi := congrArg (fun r : ℝ => Real.exp L*r) hwim
                simp only [←mul_assoc,hprod,one_mul] at hr hi
                exact UpperHalfPlane.ext_re_im (hr.trans (hD (r w)).1.symm) (hi.trans (hD (r w)).2.symm)
              let z₀ : H2 := ⟨⟨1,1⟩,by norm_num⟩
              have hz₀ : z₀.re≠0 := by norm_num [z₀]
              have hc := hCoordinates (g' z₀) z₀
                (by simpa only [hnormclock] using g'.isometry.dist_eq (verticalPath 0) z₀)
                (by simpa only [hnormclock] using g'.isometry.dist_eq (verticalPath 1) z₀)
              rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc.2 with hp|hm
              · left
                have hh : ∀z,g' z=z := hRigid g' g'.isometry (hnormclock 0) (hnormclock 1) z₀ hz₀
                  (UpperHalfPlane.ext_re_im hp hc.1)
                exact hUnwind id hh
              · right
                let g'' : H2 ≃ᵢ H2 := g'.trans refIso
                have hv (t : ℝ) : g'' (verticalPath t)=verticalPath t := by
                  change ref (g' (verticalPath t))=verticalPath t
                  rw [hnormclock,hrefVertical]
                have hfix : g'' z₀=z₀ := by
                  apply UpperHalfPlane.ext_re_im
                  · change -(g' z₀).re=z₀.re
                    rw [hm]
                    ring
                  · exact hc.1
                have hh : ∀z,g'' z=z := hRigid g'' g''.isometry (hv 0) (hv 1) z₀ hz₀ hfix
                apply hUnwind ref
                intro z
                have hz := congrArg ref (hh z)
                change ref (ref (g' z))=ref z at hz
                rw [hrefInv] at hz
                exact hz
            let g : H2 ≃ᵢ H2 := f₁.trans f₀.symm
            have hgclock (t : ℝ) : g (verticalPath t)=verticalPath (t+0) := by
              change f₀.symm (f₁ (verticalPath t))=verticalPath (t+0)
              rw [←haxis,f₀.symm_apply_apply,add_zero]
            let D : SL(2,ℝ) := ⟨!![Real.exp (0/2),0;0,Real.exp (-(0/2))],by simp [Matrix.det_fin_two,←Real.exp_add]⟩
            let ref : H2 → H2 := fun w=>⟨⟨-w.re,w.im⟩,w.im_pos⟩
            have hD : D=1 := by apply Subtype.ext;ext i k;fin_cases i <;> fin_cases k <;> norm_num [D]
            have hrefref : ref (ref z)=z := by apply UpperHalfPlane.ext;apply Complex.ext <;> simp [ref]
            rcases hBranches g 0 hgclock with hid|href
            · apply DFunLike.ext
              intro w
              have hh := congrArg f₀ (hid w)
              change f₀ (f₀.symm (f₁ w))=f₀ (D • w) at hh
              rw [f₀.apply_symm_apply,hD,one_smul] at hh
              exact hh.symm
            · exfalso
              have hh := congrArg f₀ (href (ref z))
              change f₀ (f₀.symm (f₁ (ref z)))=f₀ (D • ref (ref z)) at hh
              rw [f₀.apply_symm_apply,hD,one_smul,hrefref] at hh
              have heq : j z=j (ref z) := hj₀.trans (hh.symm.trans hj₁.symm)
              have hzref : z=ref z := hjinj hzW hrefW heq
              have hre := congrArg UpperHalfPlane.re hzref
              change z.re= -z.re at hre
              linarith
          letI := a
          obtain ⟨η,hη⟩ := hq.apply_eq_iff_mem_orbit.mp (hboundary 0)
          have hproj (t : ℝ) : p (@SMul.smul G H2 a.toSMul η (f₁ (verticalPath t)))=p (f₀ (verticalPath t)) := by
            exact (hq.map_smul η).trans (hboundary t).symm
          have heq := hq.isCoveringMap.eq_of_comp_eq
            ((hiso η).continuous.comp (f₁.continuous.comp verticalPath_isometry.continuous))
            (f₀.continuous.comp verticalPath_isometry.continuous) (funext hproj) 0 hη
          have haxis : ∀t : ℝ,@SMul.smul G H2 a.toSMul η (f₁ (verticalPath t))=f₀ (verticalPath t) := fun t=>congrFun heq t
        
          let ηIso : H2 ≃ᵢ H2 := {toEquiv:=@MulAction.toPerm G H2 _ a η,isometry_toFun:=hiso η}
          let fη : H2 ≃ᵢ H2 := f₁.trans ηIso
          let j : H2 → H2 := fun w=>if 0<w.re then f₀ w else fη w
          have hjproj : ∀w∈W,p (j w)=J (p₀ w) := by
            intro w hw
            by_cases hpos : 0<w.re
            · simp only [j,if_pos hpos]
              exact (hj₀ w hw hpos).symm
            · simp only [j,if_neg hpos]
              exact (hq.map_smul η).trans (hj₁ w hw (le_of_not_gt hpos)).symm
          have hjinj : Set.InjOn j W := by
            intro u hu v hv huv
            apply hpW hu hv
            apply hJinj
            rw [←hjproj u hu,←hjproj v hv,huv]
          have hrefnonpos : (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2).re≤0 := by change -z.re≤0;linarith
          have heqIso : f₀=fη := hRigid f₀ fη (fun t=>(haxis t).symm) W j hjinj z hzpos hzW hrefW
            (by simp only [j,if_pos hzpos]) (by simp only [j,if_neg (not_lt.mpr hrefnonpos)])
          refine ⟨η,fun w=>?_⟩
          exact (congrArg (fun f : H2 ≃ᵢ H2=>f w) heqIso).symm
        letI := a
        obtain ⟨η,hη⟩ := hAlign a p hq p₀ hiso f₀ f₁ hboundary J hJinj W hpW z hzpos hzW hrefW hj₀ hj₁
        have hLift (w : H2) (hw : w∈W) : J (p₀ w)=p (f₀ w) := by
          by_cases hpos : 0<w.re
          · exact hj₀ w hw hpos
          · exact (hj₁ w hw (le_of_not_gt hpos)).trans
              ((hq.map_smul η).symm.trans (congrArg p (hη w)))
        obtain ⟨Nv,hNv,hvNv,hMv⟩ := hmetric₀ v
        obtain ⟨Nf,hNf,hfNf,hMf⟩ := hmetric (f₀ v)
        let N : Set H2 := W∩Nv∩f₀ ⁻¹' Nf
        have hN : IsOpen N := (hW.inter hNv).inter (hNf.preimage f₀.continuous)
        refine ⟨p₀ '' N,hp₀.isOpenMap _ hN,⟨v,⟨⟨hv,hvNv⟩,hfNf⟩,rfl⟩,?_⟩
        rintro _ ⟨u,hu,rfl⟩ _ ⟨w,hw,rfl⟩
        rw [hLift u hu.1.1,hLift w hw.1.1,hMf _ hu.2 _ hw.2,f₀.dist_eq]
        exact (hMv _ hu.1.2 _ hw.1.2).symm
      have hReflected (W : Set H2) (hW : IsOpen W) (v : H2) (hv : v∈W) (hvaxis : v.re=0) :
          ∃z : H2,0<z.re ∧ z∈W ∧ (⟨⟨-z.re,z.im⟩,z.im_pos⟩ : H2)∈W := by
        let ζ : ℝ → H2 := fun s=>⟨⟨s,v.im⟩,v.im_pos⟩
        have hζ : Continuous ζ := by
          have hc : Continuous (fun s : ℝ=>(s:ℂ)+(v.im:ℂ)*Complex.I) := by fun_prop
          have hc' : Continuous (fun s : ℝ=>(⟨s,v.im⟩ : ℂ)) := hc.congr (fun s=>by apply Complex.ext <;> simp)
          exact hc'.upperHalfPlaneMk (fun _=>v.im_pos)
        have hzero : ζ 0=v := by apply UpperHalfPlane.ext_re_im <;> simp [ζ,hvaxis]
        have hO : IsOpen (ζ ⁻¹' W) := hW.preimage hζ
        have h0 : (0:ℝ)∈ζ ⁻¹' W := by change ζ 0∈W;rw [hzero];exact hv
        obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO 0 h0
        have hpos : 0<ε/2 := by linarith
        have hzW : ζ (ε/2)∈W := hball (by simp [Metric.mem_ball,Real.dist_eq,abs_of_pos hε];linarith)
        have hnW : ζ (-ε/2)∈W := hball (by simp [Metric.mem_ball,Real.dist_eq,neg_div,abs_neg,abs_of_pos hε];linarith)
        refine ⟨ζ (ε/2),hpos,hzW,?_⟩
        convert hnW using 1
        apply UpperHalfPlane.ext_re_im <;> simp [ζ,neg_div]
      letI := a
      have hpG (g : G) (z : H2) : p (@SMul.smul G H2 a.toSMul g z)=p z := hq.map_smul g
      have hFaxis₀ (t : ℝ) : p (F₀ (α t))=J (p (α t)) := by
        obtain ⟨W,hW,ht,hL⟩ := hW₀ t
        have hc : p (α t)∈C := hαimage ▸ ⟨α t,mem_range_self t,rfl⟩
        exact (hL (α t) ht (Or.inr hc)).symm.trans (hJ₀ ⟨p (α t),Or.inr hc⟩).symm
      have hFaxis₁ (t : ℝ) : p (F₁ (β t))=J (p (β t)) := by
        obtain ⟨W,hW,ht,hL⟩ := hW₁ t
        have hc : p (β t)∈C := hβimage ▸ ⟨β t,mem_range_self t,rfl⟩
        exact (hL (β t) ht (Or.inr hc)).symm.trans (hJ₁ ⟨p (β t),Or.inr hc⟩).symm
      intro y
      by_cases hyU : y∈U
      · exact hAway U C hU τ₀ J hJ₀ hM₀ y hyU
      by_cases hyV : y∈V
      · exact hAway V C hV τ₁ J hJ₁ hM₁ y hyV
      have hyC : y∈C := by
        by_contra hnc
        have hh : y∈U∪V := hunion.symm ▸ hnc
        exact hh.elim hyU hyV
      have hyα : y∈p '' range α := hαimage.symm ▸ hyC
      have hyβ : y∈p '' range β := hβimage.symm ▸ hyC
      obtain ⟨_,⟨t₀,rfl⟩,hαy⟩ := hyα
      obtain ⟨_,⟨r₀,rfl⟩,hβy⟩ := hyβ
      obtain ⟨γ,hγpoint⟩ := hq.apply_eq_iff_mem_orbit.mp (hαy.trans hβy.symm)
      let γIso : H2 ≃ᵢ H2 := {toEquiv:=@MulAction.toPerm G H2 _ a γ,isometry_toFun:=hiso γ}
      let βγ : ℝ → H2 := fun t=>γIso (β t)
      have hβγ : Isometry βγ := γIso.isometry.comp hβ
      have hβγimage : p '' range βγ⊆p '' range α := by
        rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
        change p (@SMul.smul G H2 a.toSMul γ (β t))∈p '' range α
        rw [hpG, hαimage]
        exact hβimage ▸ ⟨β t,mem_range_self t,rfl⟩
      have hγrange : γIso '' range β=range α :=
        (Set.range_comp γIso β).symm.trans (hMeet p hq.isCoveringMap α βγ hα hβγ T hT hfα hβγimage
          ⟨α t₀,mem_range_self t₀,⟨r₀,hγpoint⟩⟩)
      have hPull (t : ℝ) : γIso.symm (α t)∈range β := by
        have hh : α t∈γIso '' range β := hγrange.symm ▸ mem_range_self t
        obtain ⟨z,hz,hze⟩ := hh
        rw [←hze,γIso.symm_apply_apply]
        exact hz
      have hPγsym (z : H2) : p (γIso.symm z)=p z := hpG γ⁻¹ z
      have hFpull (t : ℝ) : p (F₁ (γIso.symm (α t)))=J (p (α t)) := by
        obtain ⟨s,hs⟩ := hPull t
        rw [←hs,hFaxis₁]
        rw [hs,hPγsym]
      obtain ⟨W₀,hW₀open,htW₀,hL₀⟩ := hW₀ t₀
      obtain ⟨W₁,hW₁open,hrW₁,hL₁⟩ := hW₁ r₀
      obtain ⟨eloc,htloc,heloc⟩ := hq.isCoveringMap.isLocalHomeomorph (α t₀)
      have hpinj : Set.InjOn p eloc.source := by rw [heloc];exact eloc.injOn
      let N : Set H2 := W₀∩γIso.symm ⁻¹' W₁∩eloc.source
      have hN : IsOpen N := (hW₀open.inter (hW₁open.preimage γIso.symm.continuous)).inter eloc.open_source
      have hγbase : γIso.symm (α t₀)=β r₀ := by
        apply γIso.injective
        rw [γIso.apply_symm_apply]
        exact hγpoint.symm
      have htN : α t₀∈N := ⟨⟨htW₀,by change γIso.symm (α t₀)∈W₁;rw [hγbase];exact hrW₁⟩,htloc⟩
      obtain ⟨eN,hNorm,eH,hE,δ,hδ,hInside,hCurve,hSides⟩ := hBranches p hq.isCoveringMap α hα T hT hfα
        U V C hU hV hUV hunion hfrontU hfrontV hαimage t₀ N hN htN
      let B : H2 ≃ₜ ℝ×ℝ := eN.toHomeomorph.trans eH
      let q : ℝ×ℝ → E := p ∘ B.symm
      let R : Set (ℝ×ℝ) := Ioo (-δ) δ ×ˢ Ioo (t₀-δ) (t₀+δ)
      let W : Set H2 := eH ⁻¹' R
      let p₀ : H2 → E := p ∘ eN.symm
      let f₀ : H2 ≃ᵢ H2 := eN.symm.trans F₀
      let f₁ : H2 ≃ᵢ H2 := (eN.symm.trans γIso.symm).trans F₁
      have hcoord (z : H2) : (eH z).1=z.re := congrArg Prod.fst (hE z)
      have hBs (z : H2) : B.symm (eH z)=eN.symm z := by simp [B]
      have hqmatch (z : H2) : q (eH z)=p₀ z := by change p (B.symm (eH z))=p (eN.symm z);rw [hBs]
      have hInsideN (z : H2) (hz : z∈W) : eN.symm z∈N := by
        have hh := hInside (eH z) hz
        change B.symm (eH z)∈N at hh
        rw [hBs] at hh
        exact hh
      have hW : IsOpen W := (isOpen_Ioo.prod isOpen_Ioo).preimage eH.continuous
      have hvW : verticalPath t₀∈W := by
        change eH (verticalPath t₀)∈R
        rw [hE]
        simpa [R,verticalPath,Real.log_exp] using (show (0,t₀)∈R from ⟨⟨by linarith,hδ⟩,⟨by linarith,by linarith⟩⟩)
      have hNormInv (t : ℝ) : eN.symm (verticalPath t)=α t := by rw [←hNorm t,eN.symm_apply_apply]
      have hp₀ : IsCoveringMap p₀ := hq.isCoveringMap.comp_homeomorph eN.symm.toHomeomorph
      have hpinj₀ : Set.InjOn p₀ W := by
        intro z hz w hw hh
        apply eN.symm.injective
        exact hpinj (hInsideN z hz).2 (hInsideN w hw).2 hh
      have hm₀ : ∀z : H2,∃A : Set H2,IsOpen A ∧ z∈A ∧ ∀u∈A,∀v∈A,dist (p₀ u) (p₀ v)=dist u v := by
        intro z
        obtain ⟨A,hA,hzA,hMA⟩ := hm (eN.symm z)
        refine ⟨eN.symm ⁻¹' A,hA.preimage eN.symm.continuous,hzA,?_⟩
        intro u hu v hv
        exact (hMA _ hu _ hv).trans (eN.symm.dist_eq u v)
      have hBoundary (t : ℝ) : p (f₀ (verticalPath t))=p (f₁ (verticalPath t)) := by
        change p (F₀ (eN.symm (verticalPath t)))=p (F₁ (γIso.symm (eN.symm (verticalPath t))))
        rw [hNormInv,hFaxis₀,hFpull]
      have hLift₀ (z : H2) (hz : z∈W) (hc : p₀ z∈U∪C) : J (p₀ z)=p (f₀ z) :=
        (hJ₀ ⟨p₀ z,hc⟩).trans (hL₀ (eN.symm z) (hInsideN z hz).1.1 hc)
      have hLift₁ (z : H2) (hz : z∈W) (hc : p₀ z∈V∪C) : J (p₀ z)=p (f₁ z) := by
        have hg : p (γIso.symm (eN.symm z))=p₀ z := hPγsym (eN.symm z)
        have hgC : p (γIso.symm (eN.symm z))∈V∪C := hg.symm ▸ hc
        have hh := hL₁ (γIso.symm (eN.symm z)) (hInsideN z hz).1.2 hgC
        have he : (⟨p (γIso.symm (eN.symm z)),hgC⟩ : ↥(V∪C)) = ⟨p₀ z,hc⟩ := Subtype.ext hg
        rw [he] at hh
        exact (hJ₁ ⟨p₀ z,hc⟩).trans hh
      have hzeroC (z : H2) (hz : z∈W) (hzero : z.re=0) : p₀ z∈C := by
        have hh := hCurve (eH z) hz
        change q (eH z)∈C ↔(eH z).1=0 at hh
        rw [hqmatch,hcoord] at hh
        exact hh.mpr hzero
      obtain ⟨z,hzpos,hzW,hrefW⟩ := hReflected W hW (verticalPath t₀) hvW (by rfl)
      have hResult : ∃A : Set E,IsOpen A ∧ p₀ (verticalPath t₀)∈A ∧ ∀u∈A,∀v∈A,dist (J u) (J v)=dist u v := by
        rcases hSides with ⟨hposU,hnegV⟩|⟨hposV,hnegU⟩
        · apply hSeamMetric a p hq p₀ hiso hp₀ hm₀ hm f₀ f₁ hBoundary J J.injective W hW hpinj₀
            (verticalPath t₀) hvW z hzpos hzW hrefW
          · intro w hw hp
            have hh := hposU (eH w) hw (by rw [hcoord];exact hp)
            change q (eH w)∈U at hh
            rw [hqmatch] at hh
            exact hLift₀ w hw (Or.inl hh)
          · intro w hw hn
            rcases lt_or_eq_of_le hn with hneg|hzero
            · have hh := hnegV (eH w) hw (by rw [hcoord];exact hneg)
              change q (eH w)∈V at hh
              rw [hqmatch] at hh
              exact hLift₁ w hw (Or.inl hh)
            · exact hLift₁ w hw (Or.inr (hzeroC w hw hzero))
        · apply hSeamMetric a p hq p₀ hiso hp₀ hm₀ hm f₁ f₀ (fun t=>(hBoundary t).symm) J J.injective W hW hpinj₀
            (verticalPath t₀) hvW z hzpos hzW hrefW
          · intro w hw hp
            have hh := hposV (eH w) hw (by rw [hcoord];exact hp)
            change q (eH w)∈V at hh
            rw [hqmatch] at hh
            exact hLift₁ w hw (Or.inl hh)
          · intro w hw hn
            rcases lt_or_eq_of_le hn with hneg|hzero
            · have hh := hnegU (eH w) hw (by rw [hcoord];exact hneg)
              change q (eH w)∈U at hh
              rw [hqmatch] at hh
              exact hLift₀ w hw (Or.inl hh)
            · exact hLift₀ w hw (Or.inr (hzeroC w hw hzero))
      obtain ⟨A,hA,hyA,hMA⟩ := hResult
      refine ⟨A,hA,?_,hMA⟩
      rw [←hαy]
      simpa only [p₀,Function.comp_apply,hNormInv] using hyA
    have hGlobalSew {E G : Type} [MetricSpace E] [Group G]
        (a : MulAction G H2) (p : H2 → E) (hq : letI:=a;IsQuotientCoveringMap p G)
        (hiso : ∀g : G,Isometry (@SMul.smul G H2 a.toSMul g))
        (U V C : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
        (hunion : U∪V=Cᶜ) (hfrontU : frontier U=C) (hfrontV : frontier V=C)
        (α β : ℝ → H2) (hα : Isometry α) (hβ : Isometry β)
        (T S : ℝ) (hT : 0<T) (hS : 0<S)
        (hfα : ∀s t : ℝ,p (α s)=p (α t) ↔∃n : ℤ,s=t+n*T)
        (hfβ : ∀s t : ℝ,p (β s)=p (β t) ↔∃n : ℤ,s=t+n*S)
        (hαimage : p '' range α=C) (hβimage : p '' range β=C)
        (τ₀ : ↥(U∪C) ≃ₜ ↥(U∪C)) (τ₁ : ↥(V∪C) ≃ₜ ↥(V∪C))
        (hτ₀ : Function.Involutive τ₀) (hτ₁ : Function.Involutive τ₁)
        (hclock₀ : ∀t : ℝ,∃ht : p (α t)∈U∪C,(τ₀ ⟨p (α t),ht⟩).val=p (α (t+T/2)))
        (hclock₁ : ∀t : ℝ,∃ht : p (β t)∈V∪C,(τ₁ ⟨p (β t),ht⟩).val=p (β (t+S/2)))
        (F₀ : Finset ↥(U∪C)) (F₁ : Finset ↥(V∪C))
        (hc₀ : F₀.card=3) (hc₁ : F₁.card=3)
        (hfix₀ : (F₀:Set ↥(U∪C))={x | τ₀ x=x}) (hfix₁ : (F₁:Set ↥(V∪C))={x | τ₁ x=x})
        (hno₀ : ∀x : ↥(U∪C),x.val∈C →τ₀ x≠x) (hno₁ : ∀x : ↥(V∪C),x.val∈C →τ₁ x≠x) :
        ∃J : E ≃ₜ E,Function.Involutive J ∧
          (∀x : ↥(U∪C),J x.val=(τ₀ x).val) ∧ (∀x : ↥(V∪C),J x.val=(τ₁ x).val) ∧
        ∃F : Finset E,F.card=6 ∧ (F:Set E)={x | J x=x} ∧
        ∃s₀ : ℝ,∃γ : G,@SMul.smul G H2 a.toSMul γ (β 0)=α s₀ ∧
          (fun z=>@SMul.smul G H2 a.toSMul γ z) '' range β=range α := by
      have hHalfAgreement {G P E : Type} [Group G] [MetricSpace P] [TopologicalSpace E] [T2Space E]
          (a : MulAction G P) (p : P → E) (hq : letI:=a;IsQuotientCoveringMap p G)
          (hiso : ∀g : G,Isometry (fun z=>@SMul.smul G P a.toSMul g z))
          (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
          (T U : ℝ) (hT : 0<T) (hU : 0<U)
          (hfα : ∀s t : ℝ,p (α s)=p (α t) ↔∃n : ℤ,s=t+n*T)
          (hfβ : ∀s t : ℝ,p (β s)=p (β t) ↔∃n : ℤ,s=t+n*U)
          (hrange : p '' range α=p '' range β)
          (j₀ j₁ : E → E)
          (h₀ : ∀t : ℝ,j₀ (p (α t))=p (α (t+T/2)))
          (h₁ : ∀t : ℝ,j₁ (p (β t))=p (β (t+U/2))) :
          ∀y∈p '' range α,j₀ y=j₁ y := by
        have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
            (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
            (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
            (himage : p '' range β⊆p '' range α)
            (hmeet : (range α∩range β).Nonempty) : range β=range α := by
          have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (hmeet : (range α∩range β).Nonempty) : range β=range α := by
            have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
                (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
                (himage : p '' range β⊆p '' range α)
                (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
              have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                  (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                  (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                  ∃f : C(Circle,E),IsEmbedding f ∧
                    (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                    range f=p '' range α := by
                classical
                let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
                have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
                let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
                have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                  apply (hfibre _ _).mpr
                  refine ⟨k,?_⟩
                  rw [hk]
                  field_simp
                have hψ : Continuous ψ := by
                  apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                  have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                  rw [heq]
                  fun_prop
                let f : C(Circle,E) := ⟨ψ,hψ⟩
                have hfinj : Function.Injective f := by
                  intro z w hzw
                  obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                  have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                    have hπ : (2*Real.pi)≠0 := by positivity
                    have hT' : T≠0 := hT.ne'
                    field_simp at hk
                    nlinarith
                  rw [←hθ z,←hθ w]
                  exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
                have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                  change _=ψ _
                  rw [hfac]
                  congr 2
                  field_simp
                refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
                apply Subset.antisymm
                · rintro y ⟨z,rfl⟩
                  exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
                · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                  exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
              obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
              change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
              let e : Circle ≃ₜ range f := hf.toHomeomorph
              let g : C(ℝ,Circle) :=
                ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                  exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
              let θ₀ := 2*Real.pi*s₀/T
              have hbase : Circle.exp θ₀=g t₀ := by
                apply e.injective
                apply Subtype.ext
                change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
                rw [e.apply_symm_apply]
                change f (Circle.exp θ₀)=p (β t₀)
                rw [←hparam,hmeet]
              obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
              have hL0 : L t₀=θ₀ := hL.1
              have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
              let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
              have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
                intro t
                change p (α (T*L t/(2*Real.pi)))=_
                rw [hparam]
                have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
                rw [harg,hLe]
                exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                  rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
              have hℓbase : ℓ t₀=β t₀ := by
                change α (T*L t₀/(2*Real.pi))=β t₀
                rw [hL0]
                have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
                rw [harg,hmeet]
              have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
                (funext hℓproj) t₀ hℓbase
              rintro y ⟨t,rfl⟩
              exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
            have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
                (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
                range β=range α := by
              let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
              let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
              have hfac (t : ℝ) : α (f t)=β t :=
                congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
              have hf : Isometry f := by
                apply isometry_iff_dist_eq.mpr
                intro s t
                rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
              let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
              have hLin : Function.Injective A.toAffineMap.linear :=
                A.toAffineMap.linear_injective_iff.mpr hf.injective
              have hSur : Function.Surjective A.toAffineMap.linear :=
                LinearMap.surjective_of_injective hLin
              have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
              apply Subset.antisymm hsub
              rintro y ⟨t,rfl⟩
              obtain ⟨s,hs⟩ := hfsur t
              exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
            obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
            have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
              s t (hs.trans ht.symm)
            exact hLine α β hα hβ hsub
          exact hMeet p hp α β hα hβ T hT hfibre himage hmeet
        have hPhase {P : Type} [MetricSpace P] (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
            (g : P ≃ᵢ P) (hr : g '' range α=range β) :
            ∃phase : ℝ,(∀t : ℝ,g (α t)=β (t+phase)) ∨ (∀t : ℝ,g (α t)=β (phase-t)) := by
          have hReal (f : ℝ → ℝ) (hf : Isometry f) :
              (∀t : ℝ,f t=f 0+t) ∨ (∀t : ℝ,f t=f 0-t) := by
            let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
            let k : ℝ := A.toAffineMap.linear 1
            have hfac (t : ℝ) : f t=t*k+f 0 := by
              have h := A.toAffineMap.map_vadd 0 t
              have hlin : A.toAffineMap.linear t=t*k := by
                have hh := A.toAffineMap.linear.map_smul t (1:ℝ)
                simpa [k,smul_eq_mul] using hh
              change f (t+0)=A.toAffineMap.linear t+f 0 at h
              simpa only [add_zero,hlin] using h
            have hk : |k|=1 := by
              have h := hf.dist_eq 1 0
              rw [hfac 1,hfac 0] at h
              simpa [Real.dist_eq] using h
            rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp hk with he|he
            · left;intro t;rw [hfac,he];ring
            · right;intro t;rw [hfac,he];ring
          have hExists (t : ℝ) : ∃s : ℝ,β s=g (α t) := by
            have hh : g (α t)∈g '' range α := ⟨α t,mem_range_self t,rfl⟩
            have hm : g (α t)∈range β := (Set.ext_iff.mp hr (g (α t))).mp hh
            obtain ⟨s,hs⟩ := hm
            exact ⟨s,hs⟩
          let f : ℝ → ℝ := fun t => Classical.choose (hExists t)
          have hf (t : ℝ) : β (f t)=g (α t) := Classical.choose_spec (hExists t)
          have hfi : Isometry f := by
            apply Isometry.of_dist_eq
            intro s t
            rw [←hβ.dist_eq,hf,hf,g.dist_eq,hα.dist_eq]
          rcases hReal f hfi with hp|hm
          · refine ⟨f 0,Or.inl ?_⟩
            intro t
            rw [←hf,hp]
            congr 1
            ring
          · refine ⟨f 0,Or.inr ?_⟩
            intro t
            rw [←hf,hm]
        have hAgree {G P E : Type} [Group G] [MulAction G P] [MetricSpace P]
            (p : P → E) (α β : ℝ → P) (T : ℝ) (γ : G)
            (hp : ∀g : G,∀z : P,p (g • z)=p z)
            (phase : ℝ) (hphase : (∀t : ℝ,γ • α t=β (t+phase)) ∨
              (∀t : ℝ,γ • α t=β (phase-t)))
            (hfibre : ∀s t : ℝ,p (β s)=p (β t) ↔∃n : ℤ,s=t+n*T)
            (j₀ j₁ : E → E)
            (h₀ : ∀t : ℝ,j₀ (p (α t))=p (α (t+T/2)))
            (h₁ : ∀t : ℝ,j₁ (p (β t))=p (β (t+T/2))) :
            ∀y∈p '' range α,j₀ y=j₁ y := by
          rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          rcases hphase with hpos|hneg
          · have heq (s : ℝ) : p (α s)=p (β (s+phase)) := by
              rw [←hpos,hp]
            rw [h₀,heq,heq t,h₁]
            congr 2
            ring
          · have heq (s : ℝ) : p (α s)=p (β (phase-s)) := by
              rw [←hneg,hp]
            rw [h₀,heq,heq t,h₁]
            exact (hfibre _ _).mpr ⟨-1,by norm_num;ring⟩
        have hPeriods {P E G : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E] [Group G]
            (a : MulAction G P) (p : P → E)
            (hq : letI := a;IsQuotientCoveringMap p G)
            (hiso : ∀g : G,Isometry (fun z => @SMul.smul G P a.toSMul g z))
            (hproj : ∀g : G,∀z : P,p (@SMul.smul G P a.toSMul g z)=p z)
            (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
            (T U : ℝ) (hT : 0<T) (hU : 0<U)
            (hαfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
            (hβfibre : ∀s t : ℝ,p (β s)=p (β t) ↔ ∃n : ℤ,s=t+n*U)
            (himage : p '' range α=p '' range β) : T=U := by
          letI := a
          have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (hmeet : (range α∩range β).Nonempty) : range β=range α := by
            have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
                (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
                (himage : p '' range β⊆p '' range α)
                (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
              have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                  (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                  (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                  ∃f : C(Circle,E),IsEmbedding f ∧
                    (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                    range f=p '' range α := by
                classical
                let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
                have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
                let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
                have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                  apply (hfibre _ _).mpr
                  refine ⟨k,?_⟩
                  rw [hk]
                  field_simp
                have hψ : Continuous ψ := by
                  apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                  have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                  rw [heq]
                  fun_prop
                let f : C(Circle,E) := ⟨ψ,hψ⟩
                have hfinj : Function.Injective f := by
                  intro z w hzw
                  obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                  have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                    have hπ : (2*Real.pi)≠0 := by positivity
                    have hT' : T≠0 := hT.ne'
                    field_simp at hk
                    nlinarith
                  rw [←hθ z,←hθ w]
                  exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
                have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                  change _=ψ _
                  rw [hfac]
                  congr 2
                  field_simp
                refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
                apply Subset.antisymm
                · rintro y ⟨z,rfl⟩
                  exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
                · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                  exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
              obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
              change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
              let e : Circle ≃ₜ range f := hf.toHomeomorph
              let g : C(ℝ,Circle) :=
                ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                  exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
              let θ₀ := 2*Real.pi*s₀/T
              have hbase : Circle.exp θ₀=g t₀ := by
                apply e.injective
                apply Subtype.ext
                change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
                rw [e.apply_symm_apply]
                change f (Circle.exp θ₀)=p (β t₀)
                rw [←hparam,hmeet]
              obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
              have hL0 : L t₀=θ₀ := hL.1
              have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
              let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
              have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
                intro t
                change p (α (T*L t/(2*Real.pi)))=_
                rw [hparam]
                have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
                rw [harg,hLe]
                exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                  rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
              have hℓbase : ℓ t₀=β t₀ := by
                change α (T*L t₀/(2*Real.pi))=β t₀
                rw [hL0]
                have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
                rw [harg,hmeet]
              have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
                (funext hℓproj) t₀ hℓbase
              rintro y ⟨t,rfl⟩
              exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
            have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
                (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
                range β=range α := by
              let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
              let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
              have hfac (t : ℝ) : α (f t)=β t :=
                congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
              have hf : Isometry f := by
                apply isometry_iff_dist_eq.mpr
                intro s t
                rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
              let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
              have hLin : Function.Injective A.toAffineMap.linear :=
                A.toAffineMap.linear_injective_iff.mpr hf.injective
              have hSur : Function.Surjective A.toAffineMap.linear :=
                LinearMap.surjective_of_injective hLin
              have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
              apply Subset.antisymm hsub
              rintro y ⟨t,rfl⟩
              obtain ⟨s,hs⟩ := hfsur t
              exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
            obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
            have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
              s t (hs.trans ht.symm)
            exact hLine α β hα hβ hsub
          have hPeriodLe (α β : ℝ → P) (hα : Isometry α) (hβ : Isometry β)
              (T U : ℝ) (hT : 0<T) (hU : 0<U)
              (hf : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
              (hb : p (β U)=p (β 0)) (hr : range α=range β) : T≤U := by
            have hmU : β U∈range α := by rw [hr];exact mem_range_self U
            have hm0 : β 0∈range α := by rw [hr];exact mem_range_self 0
            obtain ⟨s,hs⟩ := hmU
            obtain ⟨t,ht⟩ := hm0
            have heq : p (α s)=p (α t) := by rw [hs,ht];exact hb
            obtain ⟨n,hn⟩ := (hf s t).mp heq
            have hdist : |s-t|=U := by
              have hd := hα.dist_eq s t
              rw [hs,ht,hβ.dist_eq] at hd
              simpa [Real.dist_eq,abs_of_nonneg hU.le] using hd.symm
            have habs : |(n:ℝ)| * T=U := by
              rw [hn,add_sub_cancel_left,abs_mul,abs_of_pos hT] at hdist
              exact hdist
            have hnzero : n≠0 := by intro hn0;subst n;norm_num at habs;linarith
            have hnOne : (1:ℤ) ≤ |n| := by
              have hh : (0:ℤ) < |n| := abs_pos.mpr hnzero
              omega
            have hnOneReal : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast hnOne
            nlinarith
          have hpoint : p (β 0)∈p '' range α := himage ▸ ⟨β 0,mem_range_self 0,rfl⟩
          obtain ⟨_,⟨s,rfl⟩,hs⟩ := hpoint
          obtain ⟨g,hg⟩ := hq.exists_toPermFiber_eq
            (⟨α s,hs⟩ : p ⁻¹' {p (β 0)}) ⟨β 0,rfl⟩
          have hgpoint : @SMul.smul G P a.toSMul g (α s)=β 0 := congrArg Subtype.val hg
          let γ : ℝ → P := fun t => @SMul.smul G P a.toSMul g (α t)
          have hγ : Isometry γ := (hiso g).comp hα
          have hγfibre : ∀s t : ℝ,p (γ s)=p (γ t) ↔ ∃n : ℤ,s=t+n*T := by
            intro s t;simpa only [γ,hproj] using hαfibre s t
          have hγimage : p '' range β⊆p '' range γ := by
            rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
            have hh : p (β t)∈p '' range α := himage ▸ ⟨β t,mem_range_self t,rfl⟩
            obtain ⟨_,⟨r,rfl⟩,hr⟩ := hh
            exact ⟨γ r,mem_range_self r,(hproj g (α r)).trans hr⟩
          have hr : range β=range γ := hMeet p hq.isCoveringMap γ β hγ hβ T hT hγfibre hγimage
            ⟨β 0,⟨s,hgpoint⟩,mem_range_self 0⟩
          apply le_antisymm
          · exact hPeriodLe γ β hγ hβ T U hT hU hγfibre
              ((hβfibre U 0).mpr ⟨1,by ring⟩) hr.symm
          · exact hPeriodLe β γ hβ hγ U T hU hT hβfibre
              ((hγfibre T 0).mpr ⟨1,by ring⟩) hr
        have hp : ∀g : G,∀z : P,p (@SMul.smul G P a.toSMul g z)=p z := fun g z=>hq.map_smul g
        have hTU := hPeriods a p hq hiso hp α β hα hβ T U hT hU hfα hfβ hrange
        subst U
        have hβ0 : p (β 0)∈p '' range α := hrange.symm ▸ ⟨β 0,mem_range_self 0,rfl⟩
        obtain ⟨_,⟨s₀,rfl⟩,hps⟩ := hβ0
        obtain ⟨η,hη⟩ := hq.apply_eq_iff_mem_orbit.mp hps
        let γ := η⁻¹
        have hγ : @SMul.smul G P a.toSMul γ (α s₀)=β 0 := by
          have hh := congrArg (fun z=>@SMul.smul G P a.toSMul η⁻¹ z) hη
          exact hh.symm.trans (@inv_smul_smul G P _ a η (β 0))
        let γIso : P ≃ᵢ P := {toEquiv:=@MulAction.toPerm G P _ a γ,isometry_toFun:=hiso γ}
        have hγrange : γIso '' range α=range β := by
          have hγfibre : ∀s t : ℝ,p (γIso (α s))=p (γIso (α t)) ↔∃n : ℤ,s=t+n*T := by
            intro s t
            change p (@SMul.smul G P a.toSMul γ (α s))=p (@SMul.smul G P a.toSMul γ (α t)) ↔_
            rw [hp,hp]
            exact hfα s t
          have hγimage : p '' range β⊆p '' range (fun t=>γIso (α t)) := by
            rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
            have hh : p (β t)∈p '' range α := hrange.symm ▸ ⟨β t,mem_range_self t,rfl⟩
            obtain ⟨_,⟨s,rfl⟩,hs⟩ := hh
            exact ⟨γIso (α s),mem_range_self s,(hp γ _).trans hs⟩
          have hr := hMeet p hq.isCoveringMap (fun t=>γIso (α t)) β (γIso.isometry.comp hα) hβ T hT hγfibre hγimage
            ⟨β 0,⟨s₀,hγ⟩,mem_range_self 0⟩
          exact (Set.range_comp γIso α).symm.trans hr.symm
        obtain ⟨phase,hphase⟩ := hPhase α β hα hβ γIso hγrange
        exact @hAgree G P E _ a _ p α β T γ hp phase hphase hfβ j₀ j₁ h₀ h₁
      have hSix {E : Type} (U V C : Set E) (hUV : Disjoint U V) (hUC : Disjoint U C)
          (hVC : Disjoint V C) (hcover : U∪V∪C=univ)
          (j₀ : ↥(U∪C) ≃ ↥(U∪C)) (j₁ : ↥(V∪C) ≃ ↥(V∪C))
          (h₀ : Function.Involutive j₀) (h₁ : Function.Involutive j₁)
          (hkeep₀ : ∀x : ↥(U∪C),x.val∈C →(j₀ x).val∈C)
          (hkeep₁ : ∀x : ↥(V∪C),x.val∈C →(j₁ x).val∈C)
          (hagree : ∀x : C,(j₀ ⟨x.val,Or.inr x.property⟩).val=(j₁ ⟨x.val,Or.inr x.property⟩).val)
          (F₀ : Finset ↥(U∪C)) (F₁ : Finset ↥(V∪C))
          (hc₀ : F₀.card=3) (hc₁ : F₁.card=3)
          (hfix₀ : (F₀:Set ↥(U∪C))={x | j₀ x=x})
          (hfix₁ : (F₁:Set ↥(V∪C))={x | j₁ x=x})
          (hno₀ : ∀x : ↥(U∪C),x.val∈C →j₀ x≠x)
          (hno₁ : ∀x : ↥(V∪C),x.val∈C →j₁ x≠x) :
          ∃j : E ≃ E,Function.Involutive j ∧
            (∀x : ↥(U∪C),j x.val=(j₀ x).val) ∧
            (∀x : ↥(V∪C),j x.val=(j₁ x).val) ∧
            ∃F : Finset E,F.card=6 ∧ (F:Set E)={x | j x=x} := by
        classical
        have hcases (x : E) : x∈U∪C ∨ x∈V∪C := by
          have hx : x∈U∪V∪C := by rw [hcover];exact mem_univ x
          rcases hx with (hx|hx)|hx
          · exact Or.inl (Or.inl hx)
          · exact Or.inr (Or.inl hx)
          · exact Or.inl (Or.inr hx)
        let f : E → E := fun x=>if hx : x∈U∪C then (j₀ ⟨x,hx⟩).val else (j₁ ⟨x,(hcases x).resolve_left hx⟩).val
        have hf₀ (x : ↥(U∪C)) : f x.val=(j₀ x).val := by simp only [f,dif_pos x.property]
        have hf₁ (x : ↥(V∪C)) : f x.val=(j₁ x).val := by
          by_cases hx : x.val∈U∪C
          · have hxC : x.val∈C := by
              rcases hx with hx|hx
              · rcases x.property with hv|hc
                · exact (Set.disjoint_left.mp hUV hx hv).elim
                · exact hc
              · exact hx
            rw [hf₀ ⟨x.val,hx⟩]
            exact hagree ⟨x.val,hxC⟩
          · simp only [f,dif_neg hx]
        have hfinv : Function.Involutive f := by
          intro x
          rcases hcases x with hx|hx
          · rw [hf₀ ⟨x,hx⟩,hf₀,h₀]
          · rw [hf₁ ⟨x,hx⟩,hf₁,h₁]
        let j : E ≃ E := Function.Involutive.toPerm f hfinv
        let e₀ : ↥(U∪C) ↪ E := ⟨Subtype.val,Subtype.val_injective⟩
        let e₁ : ↥(V∪C) ↪ E := ⟨Subtype.val,Subtype.val_injective⟩
        have hF₀ (x : ↥(U∪C)) : x∈F₀ ↔j₀ x=x := by change x∈(F₀:Set ↥(U∪C)) ↔_;rw [hfix₀];rfl
        have hF₁ (x : ↥(V∪C)) : x∈F₁ ↔j₁ x=x := by change x∈(F₁:Set ↥(V∪C)) ↔_;rw [hfix₁];rfl
        have hdis : Disjoint (F₀.map e₀) (F₁.map e₁) := by
          apply Finset.disjoint_left.mpr
          intro x hx hy
          obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
          obtain ⟨v,hv,he⟩ := Finset.mem_map.mp hy
          have huv : v.val=u.val := he
          have huC : u.val∈C := by
            rcases u.property with huU|huC
            · have hvS : u.val∈V∪C := huv ▸ v.property
              rcases hvS with hvV|hvC
              · exact (Set.disjoint_left.mp hUV huU hvV).elim
              · exact hvC
            · exact huC
          exact hno₀ u huC ((hF₀ u).mp hu)
        let F := F₀.map e₀∪F₁.map e₁
        refine ⟨j,hfinv,hf₀,hf₁,F,?_,?_⟩
        · rw [Finset.card_union_of_disjoint hdis,Finset.card_map,Finset.card_map,hc₀,hc₁]
        · ext x
          change x∈F₀.map e₀∪F₁.map e₁ ↔f x=x
          rw [Finset.mem_union]
          constructor
          · rintro (hx|hx)
            · obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
              change f u.val=u.val
              rw [hf₀,(hF₀ u).mp hu]
            · obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
              change f u.val=u.val
              rw [hf₁,(hF₁ u).mp hu]
          · intro hx
            rcases hcases x with hu|hv
            · left
              let u : ↥(U∪C) := ⟨x,hu⟩
              exact Finset.mem_map.mpr ⟨u,(hF₀ u).mpr (Subtype.ext ((hf₀ u).symm.trans hx)),rfl⟩
            · right
              let u : ↥(V∪C) := ⟨x,hv⟩
              exact Finset.mem_map.mpr ⟨u,(hF₁ u).mpr (Subtype.ext ((hf₁ u).symm.trans hx)),rfl⟩
      have hHomeo {E : Type} [TopologicalSpace E] (A B : Set E)
          (hA : IsClosed A) (hB : IsClosed B) (hcover : A∪B=univ)
          (j : E ≃ E) (hji : Function.Involutive j)
          (jA : A ≃ₜ A) (jB : B ≃ₜ B)
          (hJA : ∀x : A,j x.val=(jA x).val)
          (hJB : ∀x : B,j x.val=(jB x).val) :
          ∃J : E ≃ₜ E,(J : E → E)=j ∧ Function.Involutive J := by
        have hcontA : ContinuousOn (j : E → E) A := by
          rw [continuousOn_iff_continuous_restrict]
          exact (continuous_subtype_val.comp jA.continuous).congr (fun x=>(hJA x).symm)
        have hcontB : ContinuousOn (j : E → E) B := by
          rw [continuousOn_iff_continuous_restrict]
          exact (continuous_subtype_val.comp jB.continuous).congr (fun x=>(hJB x).symm)
        have hcont : Continuous (j : E → E) := by
          apply continuousOn_univ.mp
          rw [←hcover]
          exact hcontA.union_of_isClosed hcontB hA hB
        have hinverse : (j.symm : E → E)=j := by
          funext x
          apply j.injective
          exact (j.apply_symm_apply x).trans (hji x).symm
        let J : E ≃ₜ E := {
          toEquiv := j
          continuous_toFun := hcont
          continuous_invFun := by
            change Continuous (j.symm : E → E)
            rw [hinverse]
            exact hcont }
        exact ⟨J,rfl,hji⟩
      have hAxisTransport {E G : Type} [TopologicalSpace E] [T2Space E] [Group G]
          (a : MulAction G H2) (p : H2 → E) (hq : letI:=a;IsQuotientCoveringMap p G)
          (hiso : ∀g : G,Isometry (@SMul.smul G H2 a.toSMul g))
          (α β : ℝ → H2) (hα : Isometry α) (hβ : Isometry β)
          (T : ℝ) (hT : 0<T) (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔∃n : ℤ,s=t+n*T)
          (himage : p '' range α=p '' range β) :
          ∃s₀ : ℝ,∃γ : G,
            @SMul.smul G H2 a.toSMul γ (β 0)=α s₀ ∧
            (fun z=>@SMul.smul G H2 a.toSMul γ z) '' range β=range α := by
        have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
            (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
            (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
            (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
            (himage : p '' range β⊆p '' range α)
            (hmeet : (range α∩range β).Nonempty) : range β=range α := by
          have hMeet {P E : Type} [MetricSpace P] [TopologicalSpace E] [T2Space E]
              (p : P → E) (hp : IsCoveringMap p) (α β : ℝ → P)
              (hα : Isometry α) (hβ : Isometry β) (T : ℝ) (hT : 0<T)
              (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
              (himage : p '' range β⊆p '' range α)
              (hmeet : (range α∩range β).Nonempty) : range β=range α := by
            have hContain {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                (p : P → E) (hp : IsCoveringMap p) (α β : C(ℝ,P))
                (T : ℝ) (hT : 0<T)
                (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
                (himage : p '' range β⊆p '' range α)
                (s₀ t₀ : ℝ) (hmeet : α s₀=β t₀) : range β⊆range α := by
              have hDescent {P E : Type} [TopologicalSpace P] [TopologicalSpace E] [T2Space E]
                  (p : C(P,E)) (α : C(ℝ,P)) (T : ℝ) (hT : 0<T)
                  (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) :
                  ∃f : C(Circle,E),IsEmbedding f ∧
                    (∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T))) ∧
                    range f=p '' range α := by
                classical
                let θ : Circle → ℝ := fun z => Classical.choose (Circle.exp_surjective z)
                have hθ (z : Circle) : Circle.exp (θ z)=z := Classical.choose_spec (Circle.exp_surjective z)
                let ψ : Circle → E := fun z => p (α (T*θ z/(2*Real.pi)))
                have hfac (s : ℝ) : ψ (Circle.exp s)=p (α (T*s/(2*Real.pi))) := by
                  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (hθ (Circle.exp s))
                  apply (hfibre _ _).mpr
                  refine ⟨k,?_⟩
                  rw [hk]
                  field_simp
                have hψ : Continuous ψ := by
                  apply Circle.isAddQuotientCoveringMap_exp.toIsQuotientMap.continuous_iff.mpr
                  have heq : ψ ∘ Circle.exp=(fun s : ℝ => p (α (T*s/(2*Real.pi)))) := funext hfac
                  rw [heq]
                  fun_prop
                let f : C(Circle,E) := ⟨ψ,hψ⟩
                have hfinj : Function.Injective f := by
                  intro z w hzw
                  obtain ⟨k,hk⟩ := (hfibre _ _).mp hzw
                  have ht : θ z=θ w+(k:ℝ)*(2*Real.pi) := by
                    have hπ : (2*Real.pi)≠0 := by positivity
                    have hT' : T≠0 := hT.ne'
                    field_simp at hk
                    nlinarith
                  rw [←hθ z,←hθ w]
                  exact Circle.exp_eq_exp.mpr ⟨k,ht⟩
                have hparam (s : ℝ) : p (α s)=f (Circle.exp (2*Real.pi*s/T)) := by
                  change _=ψ _
                  rw [hfac]
                  congr 2
                  field_simp
                refine ⟨f,(hψ.isClosedEmbedding hfinj).isEmbedding,hparam,?_⟩
                apply Subset.antisymm
                · rintro y ⟨z,rfl⟩
                  exact ⟨α (T*θ z/(2*Real.pi)),mem_range_self _,rfl⟩
                · rintro y ⟨_,⟨s,rfl⟩,rfl⟩
                  exact ⟨Circle.exp (2*Real.pi*s/T),(hparam s).symm⟩
              obtain ⟨f,hf,hparam,hrange⟩ := hDescent ⟨p,hp.continuous⟩ α T hT hfibre
              change ∀s : ℝ,p (α s)=f (Circle.exp (2*Real.pi*s/T)) at hparam
              let e : Circle ≃ₜ range f := hf.toHomeomorph
              let g : C(ℝ,Circle) :=
                ⟨fun t => e.symm ⟨p (β t),by rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩,by
                  exact e.symm.continuous.comp ((hp.continuous.comp β.continuous).subtype_mk _)⟩
              let θ₀ := 2*Real.pi*s₀/T
              have hbase : Circle.exp θ₀=g t₀ := by
                apply e.injective
                apply Subtype.ext
                change (e (Circle.exp θ₀)).val=(e (e.symm ⟨p (β t₀),_⟩)).val
                rw [e.apply_symm_apply]
                change f (Circle.exp θ₀)=p (β t₀)
                rw [←hparam,hmeet]
              obtain ⟨L,hL,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g t₀ θ₀ hbase
              have hL0 : L t₀=θ₀ := hL.1
              have hLe : ∀t : ℝ,Circle.exp (L t)=g t := fun t => congrFun hL.2 t
              let ℓ : C(ℝ,P) := ⟨fun t => α (T*L t/(2*Real.pi)),by fun_prop⟩
              have hℓproj : ∀t : ℝ,p (ℓ t)=p (β t) := by
                intro t
                change p (α (T*L t/(2*Real.pi)))=_
                rw [hparam]
                have harg : 2*Real.pi*(T*L t/(2*Real.pi))/T=L t := by field_simp
                rw [harg,hLe]
                exact congrArg Subtype.val (e.apply_symm_apply ⟨p (β t),by
                  rw [hrange];exact himage ⟨β t,mem_range_self t,rfl⟩⟩)
              have hℓbase : ℓ t₀=β t₀ := by
                change α (T*L t₀/(2*Real.pi))=β t₀
                rw [hL0]
                have harg : T*θ₀/(2*Real.pi)=s₀ := by dsimp [θ₀];field_simp
                rw [harg,hmeet]
              have heq : (ℓ:ℝ→P)=(β:ℝ→P) := hp.eq_of_comp_eq ℓ.continuous β.continuous
                (funext hℓproj) t₀ hℓbase
              rintro y ⟨t,rfl⟩
              exact ⟨T*L t/(2*Real.pi),(congrFun heq t)⟩
            have hLine {P : Type} [MetricSpace P] (α β : ℝ → P)
                (hα : Isometry α) (hβ : Isometry β) (hsub : range β⊆range α) :
                range β=range α := by
              let e : ℝ ≃ₜ range α := hα.isEmbedding.toHomeomorph
              let f : ℝ → ℝ := fun t => e.symm ⟨β t,hsub (mem_range_self t)⟩
              have hfac (t : ℝ) : α (f t)=β t :=
                congrArg Subtype.val (e.apply_symm_apply ⟨β t,hsub (mem_range_self t)⟩)
              have hf : Isometry f := by
                apply isometry_iff_dist_eq.mpr
                intro s t
                rw [←hα.dist_eq,hfac,hfac,hβ.dist_eq]
              let A : ℝ →ᵃⁱ[ℝ] ℝ := hf.affineIsometryOfStrictConvexSpace
              have hLin : Function.Injective A.toAffineMap.linear :=
                A.toAffineMap.linear_injective_iff.mpr hf.injective
              have hSur : Function.Surjective A.toAffineMap.linear :=
                LinearMap.surjective_of_injective hLin
              have hfsur : Function.Surjective f := A.toAffineMap.linear_surjective_iff.mp hSur
              apply Subset.antisymm hsub
              rintro y ⟨t,rfl⟩
              obtain ⟨s,hs⟩ := hfsur t
              exact ⟨s,(hfac s).symm.trans (congrArg α hs)⟩
            obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hmeet
            have hsub := hContain p hp ⟨α,hα.continuous⟩ ⟨β,hβ.continuous⟩ T hT hfibre himage
              s t (hs.trans ht.symm)
            exact hLine α β hα hβ hsub
          exact hMeet p hp α β hα hβ T hT hfibre himage hmeet
        letI := a
        have hpβ : p (β 0)∈p '' range α := himage.symm ▸ ⟨β 0,mem_range_self 0,rfl⟩
        obtain ⟨_,⟨s₀,rfl⟩,hps⟩ := hpβ
        obtain ⟨γ,hγ⟩ := hq.apply_eq_iff_mem_orbit.mp hps
        let βγ : ℝ → H2 := fun t=>@SMul.smul G H2 a.toSMul γ (β t)
        have hβγ : Isometry βγ := (hiso γ).comp hβ
        have hImage : p '' range βγ⊆p '' range α := by
          rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
          have hh : p (β t)∈p '' range α := himage.symm ▸ ⟨β t,mem_range_self t,rfl⟩
          exact (hq.map_smul γ).symm ▸ hh
        have hRanges : range βγ=range α := hMeet p hq.isCoveringMap α βγ hα hβγ T hT hfibre hImage
          ⟨α s₀,mem_range_self s₀,⟨0,hγ⟩⟩
        refine ⟨s₀,γ,hγ,?_⟩
        exact (Set.range_comp (fun z=>@SMul.smul G H2 a.toSMul γ z) β).symm.trans hRanges
      classical
      letI := a
      let j₀ : E → E := fun x=>if hx : x∈U∪C then (τ₀ ⟨x,hx⟩).val else x
      let j₁ : E → E := fun x=>if hx : x∈V∪C then (τ₁ ⟨x,hx⟩).val else x
      have hcl₀ (t : ℝ) : j₀ (p (α t))=p (α (t+T/2)) := by
        obtain ⟨ht,hh⟩ := hclock₀ t
        simpa only [j₀,dif_pos ht] using hh
      have hcl₁ (t : ℝ) : j₁ (p (β t))=p (β (t+S/2)) := by
        obtain ⟨ht,hh⟩ := hclock₁ t
        simpa only [j₁,dif_pos ht] using hh
      have himage : p '' range α=p '' range β := hαimage.trans hβimage.symm
      have hagree (x : C) : (τ₀ ⟨x.val,Or.inr x.property⟩).val=(τ₁ ⟨x.val,Or.inr x.property⟩).val := by
        have hx : x.val∈p '' range α := hαimage.symm ▸ x.property
        have hh := hHalfAgreement a p hq hiso α β hα hβ T S hT hS hfα hfβ himage j₀ j₁ hcl₀ hcl₁ x.val hx
        have hx₀ : x.val∈U∪C := Or.inr x.property
        have hx₁ : x.val∈V∪C := Or.inr x.property
        simpa only [j₀,j₁,dif_pos hx₀,dif_pos hx₁] using hh
      have hkeep₀ (x : ↥(U∪C)) (hx : x.val∈C) : (τ₀ x).val∈C := by
        have hi : x.val∈p '' range α := hαimage.symm ▸ hx
        obtain ⟨_,⟨t,rfl⟩,ht⟩ := hi
        obtain ⟨hpt,hh⟩ := hclock₀ t
        have hxx : (⟨p (α t),hpt⟩ : ↥(U∪C))=x := Subtype.ext ht
        rw [←hxx,hh,←hαimage]
        exact ⟨α (t+T/2),mem_range_self _,rfl⟩
      have hkeep₁ (x : ↥(V∪C)) (hx : x.val∈C) : (τ₁ x).val∈C := by
        have hi : x.val∈p '' range β := hβimage.symm ▸ hx
        obtain ⟨_,⟨t,rfl⟩,ht⟩ := hi
        obtain ⟨hpt,hh⟩ := hclock₁ t
        have hxx : (⟨p (β t),hpt⟩ : ↥(V∪C))=x := Subtype.ext ht
        rw [←hxx,hh,←hβimage]
        exact ⟨β (t+S/2),mem_range_self _,rfl⟩
      have hUC : Disjoint U C := disjoint_left.mpr (by
        intro x hx hc
        have hm : x∈U∪V := Or.inl hx
        have hn : x∈Cᶜ := hunion ▸ hm
        exact hn hc)
      have hVC : Disjoint V C := disjoint_left.mpr (by
        intro x hx hc
        have hm : x∈U∪V := Or.inr hx
        have hn : x∈Cᶜ := hunion ▸ hm
        exact hn hc)
      have hcover : U∪V∪C=univ := by rw [hunion,compl_union_self]
      obtain ⟨j,hji,hj₀,hj₁,F,hFcard,hFset⟩ := hSix U V C hUV hUC hVC hcover τ₀.toEquiv τ₁.toEquiv hτ₀ hτ₁ hkeep₀ hkeep₁ hagree F₀ F₁ hc₀ hc₁ hfix₀ hfix₁ hno₀ hno₁
      have hA : IsClosed (U∪C) := by rw [←hfrontU,←closure_eq_self_union_frontier];exact isClosed_closure
      have hB : IsClosed (V∪C) := by rw [←hfrontV,←closure_eq_self_union_frontier];exact isClosed_closure
      have hAB : (U∪C)∪(V∪C)=univ := by
        rw [show (U∪C)∪(V∪C)=U∪V∪C by ext x;simp only [mem_union];tauto,hcover]
      obtain ⟨J,hJ,hJinv⟩ := hHomeo (U∪C) (V∪C) hA hB hAB j hji τ₀ τ₁ hj₀ hj₁
      obtain ⟨s₀,γ,hγ,hγrange⟩ := hAxisTransport a p hq hiso α β hα hβ T hT hfα himage
      refine ⟨J,hJinv,?_,?_,F,hFcard,?_,s₀,γ,hγ,hγrange⟩
      · intro x;rw [hJ];exact hj₀ x
      · intro x;rw [hJ];exact hj₁ x
      · rw [hJ];exact hFset
    have hIdentifySide {E : Type} [TopologicalSpace E] (F U₀ V₀ U₁ V₁ : Set E)
        (hU₀ : IsOpen U₀) (hV₀ : IsOpen V₀) (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁)
        (hconn₀ : IsConnected U₀) (hconn₁ : IsConnected U₁)
        (hdis₀ : Disjoint U₀ V₀) (hdis₁ : Disjoint U₁ V₁)
        (hcover₀ : U₀∪V₀=F) (hcover₁ : U₁∪V₁=F)
        (x : E) (hx₀ : x∈U₀) (hx₁ : x∈U₁) : U₀=U₁ := by
      have hComponent {E : Type} [TopologicalSpace E] (U V F : Set E)
          (hU : IsOpen U) (hV : IsOpen V) (hconn : IsConnected U)
          (hdis : Disjoint U V) (hcover : U∪V=F) (u : E) (hu : u∈U) :
          connectedComponentIn F u=U := by
        have hUF : U⊆F := hcover ▸ subset_union_left
        have hFu : u∈F := hUF hu
        apply Set.Subset.antisymm
        · exact IsPreconnected.subset_left_of_subset_union hU hV hdis
            ((connectedComponentIn_subset F u).trans (by rw [hcover]))
            ⟨u,mem_connectedComponentIn hFu,hu⟩ isPreconnected_connectedComponentIn
        · exact hconn.2.subset_connectedComponentIn hu hUF
      exact (hComponent U₀ V₀ F hU₀ hV₀ hconn₀ hdis₀ hcover₀ x hx₀).symm.trans
        (hComponent U₁ V₁ F hU₁ hV₁ hconn₁ hdis₁ hcover₁ x hx₁)
    letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
    letI : ClosedSurface E := M.genusTwo.2.1.some
    letI := a
    obtain ⟨U,V,hU,hV,hUV,hunion,hfrontU,hfrontV,heU,heV,hdU,
      α,T,hα,hT,hαimage,hfα,F₀,τ₀,hτ₀,τd,hτd,Fd,hFdcard,hFdset,hDrestrict,
      eD,uD,hDclock,hW₀,hFc₀,hRel₀,hno₀,Ffix₀,hfixcard₀,hfixset₀,hclock₀,hmetric₀,
      φc,hφc,hφcHom⟩ := hGiven M H c d hcgeo hdgeo hcdiv hdnondiv hcd a p hp hm
    -- Exact independently-owned original prescribed-V geodesic leaf; not a certificate input.
    have hVActual : ∃dV : Curve E,(letI : MetricSpace E:=H.metric;IsClosedGeodesic dV.image) ∧
        ¬DividingCurve dV ∧ dV.image⊆V := by
      exact haas_prescribed_v_geodesic_consumer M H c hcgeo hcdiv
        U V hU hV hUV hunion hfrontU hfrontV heV
    obtain ⟨dV,hdVgeo,hdVnondiv,hdVV⟩ := hVActual
    have hcdV : Disjoint c.image dV.image := disjoint_left.mpr (by
      intro y hyc hyd
      have hyV : y∈V := hdVV hyd
      have huV : y∈U∪V := Or.inr hyV
      have hnc : y∈c.imageᶜ := hunion ▸ huV
      exact hnc hyc)
    obtain ⟨U₁,V₁,hU₁,hV₁,hUV₁,hunion₁,hfrontU₁,hfrontV₁,heU₁,heV₁,hdVU₁,
      β,S,hβ,hS,hβimage,hfβ,F₁,τ₁,hτ₁,τdV,hτdV,FdV,hFdVcard,hFdVset,hDVrestrict,
      eDV,uDV,hDVclock,hW₁,hFc₁,hRel₁,hno₁,Ffix₁,hfixcard₁,hfixset₁,hclock₁,hmetric₁,
      φc₁,hφc₁,hφc₁Hom⟩ := hGiven M H c dV hcgeo hdVgeo hcdiv hdVnondiv hcdV a p hp hm
    have hSide : U₁=V := hIdentifySide c.imageᶜ U₁ V₁ V U hU₁ hV₁ hV hU
      (punctured_torus_side_connected U₁ heU₁.some) (punctured_torus_side_connected V heV.some)
      hUV₁ hUV.symm hunion₁ (by simpa only [union_comm] using hunion) (dV.map 1)
      (hdVU₁ ⟨1,rfl⟩) (hdVV ⟨1,rfl⟩)
    subst U₁
    have hisoG : ∀g : G,Isometry (fun z=>@SMul.smul G H2 a.toSMul g z) := by
      intro g
      letI : ContinuousConstSMul G H2 := hp.toContinuousConstSMul
      let deck : H2 ≃ₜ H2 := Homeomorph.smul g
      exact actual_deck_development_isometry p (Homeomorph.refl H2) hm deck (fun z=>hp.map_smul g)
    obtain ⟨J,hJinv,hJ₀,hJ₁,F,hFcard,hFset,s₀,γ,hγ,hγrange⟩ := hGlobalSew a p hp hisoG U V c.image hU hV hUV hunion hfrontU hfrontV
      α β hα hβ T S hT hS hfα hfβ hαimage hβimage τ₀ τ₁ hτ₀ hτ₁
      hclock₀ hclock₁ Ffix₀ Ffix₁ hfixcard₀ hfixcard₁ hfixset₀ hfixset₁ hno₀ hno₁
    have hJmetric := hGlobalMetric a p hp hisoG hm U V c.image hU hV hUV hunion hfrontU hfrontV
      α β hα hβ T hT hfα hαimage hβimage F₀ F₁ τ₀ τ₁ hW₀ hW₁ hmetric₀ hmetric₁ J hJ₀ hJ₁
    have hJc (z : Circle) : J (c.map z)=c.map (φc z) := by
      obtain ⟨hz,hh⟩ := hφc z
      exact (hJ₀ ⟨c.map z,hz⟩).trans hh
    have hJcImage : J '' c.image=c.image := by
      apply subset_antisymm
      · rintro _ ⟨_,⟨z,rfl⟩,rfl⟩
        exact ⟨φc z,(hJc z).symm⟩
      · rintro _ ⟨z,rfl⟩
        refine ⟨c.map (φc.symm z),⟨φc.symm z,rfl⟩,?_⟩
        rw [hJc,φc.apply_symm_apply]
    have hJd (y : d.image) : J y.val=(τd y).val := by
      obtain ⟨hy,hh⟩ := hDrestrict y
      exact (hJ₀ ⟨y.val,hy⟩).trans hh
    have hJdImage : J '' d.image=d.image := by
      apply subset_antisymm
      · rintro _ ⟨y,hy,rfl⟩
        rw [hJd ⟨y,hy⟩]
        exact (τd ⟨y,hy⟩).property
      · intro y hy
        refine ⟨(τd.symm ⟨y,hy⟩).val,(τd.symm ⟨y,hy⟩).property,?_⟩
        rw [hJd]
        exact congrArg Subtype.val (τd.apply_symm_apply ⟨y,hy⟩)
    obtain ⟨ed,φd,hclockd,hactd⟩ := hReflection d eD τd J hJd uD hDclock
    exact ⟨J,hJinv,hJmetric,hJcImage,hJdImage,F,hFcard,hFset,φc,hJc,hφcHom,uD,ed,φd,hclockd,hactd,hReflectionHom ed φd uD hclockd⟩
  obtain ⟨p,G,mG,a,hp,hm⟩ := hFresh M H c d hcgeo hdgeo hcdiv hdnondiv hcd
  letI:=mG
  exact hGlobalSource M H c d hcgeo hdgeo hcdiv hdnondiv hcd a p hp hm

#print axioms haas_both_orientations_with_v
