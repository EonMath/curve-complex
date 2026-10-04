import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.TorusTransport
import CurveComplexGenusTwo.Hyperbolic.OriginalG2.ActualDistinctClosedGeodesicsDisjointPROVED
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualSimpleClosedGeodesicEssentialPROVED
open Set Topology CurveComplex CurveComplex.Hyperbolic
private theorem prescribed_v_geodesic_consumer {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c : Curve E)
    (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
    (hcdiv : DividingCurve c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image) (hfrontV : frontier V=c.image)
    (eV : Nonempty (V ≃ₜ {z : Circle×Circle // z≠(1,1)})) :
    ∃dV : Curve E,(letI : MetricSpace E:=H.metric;IsClosedGeodesic dV.image) ∧
      ¬DividingCurve dV ∧ dV.image⊆V := by
  obtain ⟨e,d,Q,hdessential,hdnondiv,hdV,hUconn,hVconn,hdQ,hQV,hQout⟩ :=
    actual_topological_essential_in_prescribed_side M H c hcdiv
      U V hU hV hUV hcover hfrontU hfrontV eV
  let q : C(E,Circle) := ⟨fun x => (Q x).1,continuous_fst.comp Q.continuous⟩
  have hdq (z : Circle) : q (d.map z)=z :=
    congrArg Prod.fst (hdQ z)
  have hqout (x : E) (hx : x ∉ V) : q x=1 :=
    congrArg Prod.fst (hQout x hx)
  have hcd : Disjoint c.image d.image := by
    apply Set.disjoint_left.mpr
    intro x hxc hxd
    have hxV : x ∈ V := hdV hxd
    have hxcompl : x ∈ c.imageᶜ := by
      rw [←hcover]
      exact Or.inr hxV
    exact hxcompl hxc
  obtain ⟨g,hgessential,hgfree,hggeo,hgunique⟩ :=
    essential_curve_geodesic_exists_unique_genus_two H d hdessential M.genusTwo
  have hnondiv_of_disjoint (hdis : Disjoint d.image g.image) :
      ¬ DividingCurve g :=
    actual_nondividing_of_disjoint_free_homotopy
      H d g hdnondiv hdessential hgessential hgfree hdis
  have hc_g_distinct : c.image ≠ g.image := by
    intro heq
    have hdg : Disjoint d.image g.image := by
      rw [←heq]
      exact hcd.symm
    have hcgdiv : DividingCurve g := by
      change ¬ IsConnected g.imageᶜ
      rw [←heq]
      exact hcdiv
    exact hnondiv_of_disjoint hdg hcgdiv
  have hc_essential : Essential c :=
    actual_simple_closed_geodesic_essential H c hcgeo
  have hcc_free : FreeHomotopic
      ⟨c.map,c.embedded.continuous⟩
      ⟨c.map,c.embedded.continuous⟩ :=
    actual_free_homotopic_refl _
  have hgd_free : FreeHomotopic
      ⟨g.map,g.embedded.continuous⟩
      ⟨d.map,d.embedded.continuous⟩ :=
    actual_free_homotopic_symm _ _ hgfree
  have hside_of_cg_disjoint (hcg : Disjoint c.image g.image) :
      g.image ⊆ U ∨ g.image ⊆ V :=
    actual_geodesic_lies_in_one_given_cut_side
      c g U V hU hV hUV hcover hcg
  have hV_of_cg_disjoint (hcg : Disjoint c.image g.image) :
      g.image ⊆ V := by
    rcases hside_of_cg_disjoint hcg with hgU | hgV
    · exfalso
      apply actual_horizontal_loop_cannot_homotope_to_constant_coordinate
        d g q hdq 1
      · intro z
        apply hqout
        intro hzV
        exact Set.disjoint_left.mp hUV
          (hgU ⟨z,rfl⟩) hzV
      · exact hgfree
    · exact hgV
  have hnondiv_of_contained (hgV : g.image ⊆ V) :
      ¬ DividingCurve g := by
    obtain ⟨td,tg,htd,htg,F,hfix,himage⟩ :=
      actual_literal_side_horizontal_and_geodesic_marked_alignment
        V e d g hdV hgV Q hQV hdQ hgfree
    have hVgconn : IsConnected (V \ g.image) :=
      actual_marked_torus_alignment_preserves_side_complement_connected
        V e d g hdV hgV Q hQV td tg htd htg F hfix himage hVconn
    have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
      letI : MetricSpace E := H.metric
      infer_instance
    rw [H.compatible] at ht2
    letI : T2Space E := ht2
    have hgconn : IsConnected g.imageᶜ :=
      glued_curve_complement_connected c g U V hUV hcover hfrontU hfrontV
        hgV hUconn hVgconn
    intro hdiv
    exact hdiv hgconn
  have hcg : Disjoint c.image g.image := by
    exact actual_distinct_closed_geodesics_disjoint_of_disjoint_classes
      H c g c d hc_essential hgessential hcgeo hggeo hc_g_distinct
      hcc_free hgd_free hcd
  have hgV : g.image ⊆ V := hV_of_cg_disjoint hcg
  exact ⟨g,hggeo,hnondiv_of_contained hgV,hgV⟩

theorem haas_prescribed_v_geodesic_consumer {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c : Curve E)
    (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
    (hcdiv : DividingCurve c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image) (hfrontV : frontier V=c.image)
    (eV : Nonempty (V ≃ₜ {z : Circle×Circle // z≠(1,1)})) :
    ∃dV : Curve E,(letI : MetricSpace E:=H.metric;IsClosedGeodesic dV.image) ∧
      ¬DividingCurve dV ∧ dV.image⊆V := by
  exact prescribed_v_geodesic_consumer M H c hcgeo hcdiv
    U V hU hV hUV hcover hfrontU hfrontV eV

#print axioms haas_prescribed_v_geodesic_consumer
