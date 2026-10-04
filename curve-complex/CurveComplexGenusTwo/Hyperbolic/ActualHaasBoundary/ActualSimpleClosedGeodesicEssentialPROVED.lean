import CurveComplexGenusTwo.Topology.ActualCutRecognition.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualTopologicalUniversalCoverPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualComponentHyperbolicDevelopmentPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2LocalUnitGeodesicPROVED

namespace CurveComplex.Hyperbolic
open Set Topology Filter
open scoped unitInterval
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Negative curvature excludes an embedded disc bounded by an actual closed
geodesic. This supplies essentiality absent from the protected Haas input. -/
theorem actual_simple_closed_geodesic_essential
    (H : ClosedHyperbolicMetric E) (c : Curve E)
    (hgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image) :
    Essential c := by
  classical
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  intro hdisc
  obtain ⟨f,hf,hboundary⟩ := hdisc
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hex (z : Circle) : ∃ x : D, f x = c.map z := by
    have hz : c.map z ∈ f '' {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} :=
      hboundary.symm ▸ Set.mem_range_self z
    obtain ⟨x,_,hx⟩ := hz
    exact ⟨x,hx⟩
  let u : Circle → D := fun z => (hex z).choose
  have hu (z : Circle) : f (u z) = c.map z := (hex z).choose_spec
  have hcu : Continuous u := hf.continuous_iff.mpr (by
    have heq : (f : D → E) ∘ u = c.map := funext hu
    rw [heq]
    exact c.embedded.continuous)
  let U : C(Circle,D) := ⟨u,hcu⟩
  letI : ContractibleSpace D := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace ⟨0,by simp [D]⟩
  have hn := ((id_nullhomotopic D).comp_left U).comp_right f
  have heq : f.comp ((ContinuousMap.id D).comp U) = ⟨c.map,c.embedded.continuous⟩ := by
    ext z
    exact hu z
  rw [heq] at hn
  obtain ⟨x,⟨K⟩⟩ := hn
  let A := connectedComponent (c.map 1)
  have hcrange : c.image ⊆ A :=
    (isConnected_range c.embedded.continuous).subset_connectedComponent (Set.mem_range_self 1)
  have hkrange : Set.range K ⊆ A := by
    apply (isConnected_range K.continuous).subset_connectedComponent
    exact ⟨(0,1),K.map_zero_left 1⟩
  let ca : Curve A := {
    map := fun z => ⟨c.map z,hcrange (Set.mem_range_self z)⟩
    embedded := Topology.IsEmbedding.subtypeVal.of_comp_iff.mp c.embedded }
  have hxa : x ∈ A := by
    have hm := hkrange (Set.mem_range_self (1,1))
    have hx : K (1,1) = x := K.map_one_left 1
    rw [← hx]
    exact hm
  let Ka : C(unitInterval × Circle,A) :=
    ⟨fun p => ⟨K p,hkrange (Set.mem_range_self p)⟩,K.continuous.subtype_mk _⟩
  have hna : (⟨ca.map,ca.embedded.continuous⟩ : C(Circle,A)).Nullhomotopic := by
    refine ⟨⟨x,hxa⟩,⟨{
      toFun := Ka
      continuous_toFun := Ka.continuous
      map_zero_left := ?_
      map_one_left := ?_ }⟩⟩
    · intro z; exact Subtype.ext (K.map_zero_left z)
    · intro z; exact Subtype.ext (K.map_one_left z)
  letI : CompactSpace E := H.compact
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  let AO : TopologicalSpace.Opens E := ⟨A,isOpen_connectedComponent⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A := TopologicalSpace.Opens.instChartedSpace AO
  let base : A := ⟨c.map 1,mem_connectedComponent⟩
  let P := Σ z : A, Path.Homotopic.Quotient base z
  obtain ⟨tp,hsecond,ht2p,hchart,hsc,hqc,hsurj,hlift⟩ := actual_topological_universal_cover base
  letI : TopologicalSpace P := tp
  letI : SimplyConnectedSpace P := hsc
  obtain ⟨g,hg,hgem,hgn⟩ := hlift ca hna
  obtain ⟨development,development_metric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H (c.map 1)
      (Sigma.fst : P → A) hqc.isCoveringMap hsurj
  obtain ⟨path,T,hT,hpath,hperiod,hrange,hunit⟩ := hgeo
  have hcoord (t : ℝ) : ∃ z : Circle, c.map z = path t := by
    have hm : path t ∈ c.image := hrange ▸ Set.mem_range_self t
    exact hm
  let coord : ℝ → Circle := fun t => (hcoord t).choose
  have coord_spec (t : ℝ) : c.map (coord t) = path t := (hcoord t).choose_spec
  have coord_continuous : Continuous coord := c.embedded.continuous_iff.mpr (by
    have heq : c.map ∘ coord = path := funext coord_spec
    rw [heq]
    exact hpath)
  have coord_periodic (t : ℝ) : coord (t+T) = coord t :=
    c.embedded.injective ((coord_spec (t+T)).trans ((hperiod t).trans (coord_spec t).symm))
  let lift : C(ℝ,P) := ⟨fun t => g (coord t),g.continuous.comp coord_continuous⟩
  have projection (t : ℝ) : (lift t).1.val = path t :=
    (congrArg Subtype.val (hg (coord t))).trans (coord_spec t)
  let developed : C(ℝ,H2) :=
    ⟨fun t => development (lift t),development.continuous.comp lift.continuous⟩
  have locally_unit (t : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ s v : ℝ,
      |s-t| < ε → |v-t| < ε → dist (developed s) (developed v) = |s-v| := by
    obtain ⟨ε₀,hε₀,hmetric0⟩ := hunit t
    obtain ⟨V,hV,htV,hmetric⟩ := development_metric (lift t)
    have hopen : IsOpen (lift ⁻¹' V) := hV.preimage lift.continuous
    obtain ⟨ε₁,hε₁,hball⟩ := Metric.isOpen_iff.mp hopen t htV
    refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,?_⟩
    intro s v hs hv
    have hsV : lift s ∈ V := hball (by
      simpa only [Metric.mem_ball,Real.dist_eq] using hs.trans_le (min_le_right _ _))
    have hvV : lift v ∈ V := hball (by
      simpa only [Metric.mem_ball,Real.dist_eq] using hv.trans_le (min_le_right _ _))
    change dist (development (lift s)) (development (lift v)) = |s-v|
    rw [← hmetric (lift s) hsV (lift v) hvV,projection,projection]
    exact hmetric0 s v (hs.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))
  have hiso : Isometry developed :=
    actual_h2_local_unit_geodesic_isometry developed developed.continuous locally_unit
  have hsame : developed T = developed 0 := by
    change development (g (coord T)) = development (g (coord 0))
    have hp := coord_periodic 0
    simpa using congrArg (fun z => development (g z)) hp
  have htzero := hiso.injective hsame
  exact (ne_of_gt hT) htzero

end CurveComplex.Hyperbolic
