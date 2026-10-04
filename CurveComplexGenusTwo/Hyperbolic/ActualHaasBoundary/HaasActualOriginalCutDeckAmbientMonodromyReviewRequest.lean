import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualTopologicalUniversalCoverPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualComponentHyperbolicDevelopmentPROVED
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCoverDomainTransportHeader
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualDevelopedGeodesicLinesReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualLiftComponentConvexReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOpenCutComponentCoverReviewRequest
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
namespace CurveComplex.Hyperbolic
open Set Topology
open scoped Pointwise unitInterval
set_option maxHeartbeats 8000000
theorem actual_original_two_geodesic_cut_monodromy_is_ambient_deck_action {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
    (hcgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image)
    (hdgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic d.image)
    (u : E) (hu : u∈(c.image ∪ d.image)ᶜ) :
    let U := connectedComponentIn (c.image ∪ d.image)ᶜ u
    ∃ p : H2 → E,∃ (G : Type) (m : Group G),letI := m
      ∃ a : MulAction G H2,letI := a
        ∃ hp : IsQuotientCoveringMap p G,
        (∀ z : H2,∃ V : Set H2,IsOpen V ∧ z∈V ∧
          ∀ y∈V,∀ z∈V,@dist E H.metric.toDist (p y) (p z)=dist y z) ∧
        ∃ x : H2,p x=u ∧
          let C := connectedComponentIn (p ⁻¹' U) x
          let K := MulAction.stabilizer G C
          ∃ b : MulAction K C,letI := b
            ∃ (q : C → U) (hq : IsQuotientCoveringMap q K),
              ∃ hproj : ∀ z,(q z).val=p z.val,
              (∀ (g : K) (z : C),(@SMul.smul K C b.toSMul g z).val=g.val • z.val) ∧
              (∀ z : C,∃ V : Set C,IsOpen V ∧ z∈V ∧
                ∀ y∈V,∀ z∈V,@dist E H.metric.toDist (q y).val (q z).val=dist y z) ∧
              (∀ y∈C,∀ z∈C,∀ w : H2,dist y w+dist w z=dist y z → w∈C) ∧
              ContractibleSpace C ∧ SimplyConnectedSpace C ∧
              ∀ o : C,∃ e : FundamentalGroup U (q o) ≃* Kᵐᵒᵖ,
                ∀ γ : FundamentalGroup U (q o),
                  (@SMul.smul K C b.toSMul (e γ).unop o = hq.isCoveringMap.monodromy γ ⟨o,rfl⟩) ∧
                  @SMul.smul G H2 a.toSMul (e γ).unop.val o.val=
                    (hp.isCoveringMap.monodromy
                      (γ.toPath.map (⟨Subtype.val,continuous_subtype_val⟩ : C(U,E)))
                      ⟨o.val,(hproj o).symm⟩).val := by
  have hnat {B U E C : Type} [TopologicalSpace B] [TopologicalSpace U]
      [TopologicalSpace E] [TopologicalSpace C]
      (p : E → B) (q : C → U) (hp : IsCoveringMap p) (hq : IsCoveringMap q)
      (i : C(U,B)) (j : C(C,E)) (hcomm : ∀ z,p (j z)=i (q z))
      (x : C) (γ : Path.Homotopic.Quotient (q x) (q x)) :
      (hp.monodromy (γ.map i) ⟨j x,hcomm x⟩).val=
        j (hq.monodromy γ ⟨x,rfl⟩).val := by
    obtain ⟨γ⟩ := γ
    let L := hq.liftPath γ x γ.source
    have heq : j ∘ L=hp.liftPath (γ.map i.continuous) (j x)
        ((γ.map i.continuous).source.trans (hcomm x).symm) := by
      apply (hp.eq_liftPath_iff _).mpr
      refine ⟨j.continuous.comp L.continuous,?_,?_⟩
      · funext t
        change p (j (L t))=i (γ t)
        rw [hcomm]
        exact congrArg i (congrFun (hq.liftPath_lifts γ x γ.source) t)
      · change j (L 0)=j x
        rw [hq.liftPath_zero]
    change hp.liftPath (γ.map i.continuous) (j x)
        ((γ.map i.continuous).source.trans (hcomm x).symm) 1=j (L 1)
    exact (congrFun heq 1).symm
  have hsource :
    let U := connectedComponentIn (c.image ∪ d.image)ᶜ u
      ∃ p : H2 → E,∃ (G : Type) (m : Group G),letI := m
        ∃ a : MulAction G H2,letI := a
          IsQuotientCoveringMap p G ∧
          (∀ z : H2,∃ V : Set H2,IsOpen V ∧ z∈V ∧
            ∀ y∈V,∀ z∈V,@dist E H.metric.toDist (p y) (p z)=dist y z) ∧
          ∃ x : H2,p x=u ∧
            let C := connectedComponentIn (p ⁻¹' U) x
            let K := MulAction.stabilizer G C
            ∃ b : MulAction K C,letI := b
              ∃ q : C → U,IsQuotientCoveringMap q K ∧
                (∀ z,(q z).val=p z.val) ∧
                (∀ (g : K) (z : C),(@SMul.smul K C b.toSMul g z).val=g.val • z.val) ∧
                (∀ z : C,∃ V : Set C,IsOpen V ∧ z∈V ∧
                  ∀ y∈V,∀ z∈V,@dist E H.metric.toDist (q y).val (q z).val=dist y z) ∧
                (∀ y∈C,∀ z∈C,∀ w : H2,dist y w+dist w z=dist y z → w∈C) ∧
                ContractibleSpace C ∧ SimplyConnectedSpace C := by
    have hcover :
      let U := connectedComponentIn (c.image ∪ d.image)ᶜ u
        ∃ p : H2 → E,∃ (G : Type) (m : Group G),letI := m
          ∃ a : MulAction G H2,letI := a
            IsQuotientCoveringMap p G ∧
            (∀ z : H2,∃ V : Set H2,IsOpen V ∧ z∈V ∧
              ∀ y∈V,∀ z∈V,@dist E H.metric.toDist (p y) (p z)=dist y z) ∧
            ∃ x : H2,p x=u ∧
              let C := connectedComponentIn (p ⁻¹' U) x
              let K := MulAction.stabilizer G C
              ∃ b : MulAction K C,letI := b
                ∃ q : C → U,IsQuotientCoveringMap q K ∧
                  (∀ z,(q z).val=p z.val) ∧
                  (∀ (g : K) (z : C),(@SMul.smul K C b.toSMul g z).val=g.val • z.val) ∧
                  (∀ z : C,∃ V : Set C,IsOpen V ∧ z∈V ∧
                    ∀ y∈V,∀ z∈V,@dist E H.metric.toDist (q y).val (q z).val=dist y z) ∧
                  ∀ y∈C,∀ z∈C,∀ w : H2,dist y w+dist w z=dist y z → w∈C := by
      classical
      have hcanonical {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
          (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (base : E) :
          ∃ p : H2 → E,∃ (G : Type) (m : Group G),letI := m
            ∃ a : MulAction G H2,letI := a
              IsQuotientCoveringMap p G ∧
              ∀ x : H2,∃ U : Set H2,IsOpen U ∧ x∈U ∧
                ∀ y∈U,∀ z∈U,@dist E H.metric.toDist (p y) (p z)=dist y z := by
        classical
        letI : ClosedSurface E := M.genusTwo.2.1.some
        letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
        let A := connectedComponent base
        letI : CompactSpace A := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
        letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
        letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
        let AO : TopologicalSpace.Opens E := ⟨A,isOpen_connectedComponent⟩
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A := TopologicalSpace.Opens.instChartedSpace AO
        let baseA : A := ⟨base,mem_connectedComponent⟩
        let P := Σ z : A,Path.Homotopic.Quotient baseA z
        obtain ⟨tp,hsecond,ht2p,hchart,hsc,hqc,hsurj,hlift⟩ := actual_topological_universal_cover baseA
        letI : TopologicalSpace P := tp
        letI : SimplyConnectedSpace P := hsc
        obtain ⟨development,hdev⟩ := actual_hyperbolic_component_simply_connected_cover_develops
          H base (Sigma.fst : P → A) hqc.isCoveringMap hsurj
        let G := deck (Sigma.fst : P → A)
        obtain ⟨a,hQa⟩ := CurveComplex.LocalSurgery.actual_quotient_cover_domain_homeomorph_transport
          (Sigma.fst : P → A) hqc development.symm
        letI : MulAction G H2 := a
        let pA : H2 → A := (Sigma.fst : P → A) ∘ development.symm
        have hA : A=Set.univ := PreconnectedSpace.connectedComponent_eq_univ base
        let eA : A ≃ₜ E := (Homeomorph.setCongr hA).trans (Homeomorph.Set.univ E)
        let p : H2 → E := eA ∘ pA
        have hQ : IsQuotientCoveringMap p G := {
          toIsQuotientMap := eA.isQuotientMap.comp hQa.toIsQuotientMap
          continuous_const_smul := hQa.continuous_const_smul
          disjoint := hQa.disjoint
          apply_eq_iff_mem_orbit := by
            intro x y
            change eA (pA x)=eA (pA y) ↔ x∈MulAction.orbit G y
            rw [eA.injective.eq_iff]
            exact hQa.apply_eq_iff_mem_orbit }
        refine ⟨p,G,inferInstance,a,hQ,?_⟩
        intro x
        obtain ⟨V,hV,hxV,hmetric⟩ := hdev (development.symm x)
        refine ⟨development.symm ⁻¹' V,hV.preimage development.symm.continuous,hxV,?_⟩
        intro y hy z hz
        change @dist E H.metric.toDist (Sigma.fst (development.symm y)).val
          (Sigma.fst (development.symm z)).val=dist y z
        rw [hmetric _ hy _ hz,development.apply_symm_apply,development.apply_symm_apply]
      have hrestricted {E P G : Type} [TopologicalSpace E] [TopologicalSpace P]
          [LocallyPathConnectedSpace E] [Group G] [MulAction G P]
          (p : P → E) (hp : IsQuotientCoveringMap p G)
          (U : Set E) (hU : IsOpen U) (hconn : IsConnected U) (x : P) (hx : p x∈U) :
          let C := connectedComponentIn (p ⁻¹' U) x
          let K := MulAction.stabilizer G C
          ∃ a : MulAction K C,letI := a
            ∃ q : C → U,IsQuotientCoveringMap q K ∧
              (∀ z,(q z).val=p z.val) ∧
              ∀ (g : K) (z : C),(@SMul.smul K C a.toSMul g z).val=g.val • z.val := by
        classical
        let C := connectedComponentIn (p ⁻¹' U) x
        let K := MulAction.stabilizer G C
        letI : ContinuousConstSMul G P := hp.toContinuousConstSMul
        have hmaps (g : K) (z : C) : g.val • z.val∈C := by
          have hs : g.val • C=C := MulAction.mem_stabilizer_iff.mp g.property
          exact (Set.ext_iff.mp hs (g.val • z.val)).mp (Set.mem_smul_set.mpr ⟨z.val,z.property,rfl⟩)
        let a : MulAction K C := {
          smul := fun g z => ⟨g.val • z.val,hmaps g z⟩
          one_smul := fun z => Subtype.ext (one_smul G z.val)
          mul_smul := fun g h z => Subtype.ext (mul_smul g.val h.val z.val) }
        letI := a
        obtain ⟨q,hq,hqs,hqpoint⟩ := actual_open_cut_lift_component_is_original_component_cover
          p hp.isCoveringMap U hU hconn x hx
        have hfix (g : G) (z : P) : p (g • z)=p z := hp.map_smul g
        let F := p ⁻¹' U
        have hxF : x∈F := hx
        have hF (g : G) : (g • ·) '' F=F := by
          ext z
          constructor
          · rintro ⟨y,hy,rfl⟩
            change p (g • y)∈U
            rw [hfix]
            exact hy
          · intro hz
            refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
            change p (g⁻¹ • z)∈U
            rw [hfix]
            exact hz
        have htrans (g : G) : (g • ·) '' C=connectedComponentIn F (g • x) := by
          have ht := (Homeomorph.smul g).image_connectedComponentIn hxF
          change (g • ·) '' connectedComponentIn F x=connectedComponentIn ((g • ·) '' F) (g • x) at ht
          rw [hF] at ht
          exact ht
        have hquot : IsQuotientCoveringMap q K := {
          toIsQuotientMap := hq.isQuotientMap hqs
          continuous_const_smul := by
            intro g
            exact ((hp.continuous_const_smul g.val).comp continuous_subtype_val).subtype_mk _
          apply_eq_iff_mem_orbit := by
            intro z w
            constructor
            · intro hzw
              have hpzw : p z.val=p w.val := by
                rw [←hqpoint,←hqpoint]
                exact congrArg Subtype.val hzw
              obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp hpzw
              change g • w.val=z.val at hg
              have hzimage : z.val∈(g • ·) '' C := ⟨w.val,w.property,hg⟩
              have hzcomp : z.val∈connectedComponentIn F (g • x) := htrans g ▸ hzimage
              have hcomp : connectedComponentIn F (g • x)=C :=
                (connectedComponentIn_eq hzcomp).trans (connectedComponentIn_eq z.property).symm
              have hgK : g∈K := by
                apply MulAction.mem_stabilizer_iff.mpr
                change (g • ·) '' C=C
                exact (htrans g).trans hcomp
              exact ⟨⟨g,hgK⟩,Subtype.ext hg⟩
            · rintro ⟨g,hg⟩
              apply Subtype.ext
              rw [hqpoint,hqpoint]
              have he := congrArg Subtype.val hg
              change g.val • w.val=z.val at he
              rw [←he,hfix]
          disjoint := by
            intro z
            obtain ⟨V,hV,hdis⟩ := hp.disjoint z.val
            refine ⟨Subtype.val ⁻¹' V,continuous_subtype_val.continuousAt.preimage_mem_nhds hV,?_⟩
            intro g hg
            apply Subtype.ext
            apply hdis g.val
            obtain ⟨y,⟨w,hw,rfl⟩,hy⟩ := hg
            exact ⟨g.val • w.val,⟨w.val,hw,rfl⟩,hy⟩ }
        exact ⟨a,q,hquot,hqpoint,fun g z => rfl⟩
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
      letI : ClosedSurface E := M.genusTwo.2.1.some
      letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
      letI : LocallyPathConnectedSpace E := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
      let F := (c.image ∪ d.image)ᶜ
      let U := connectedComponentIn F u
      have hF : IsOpen F :=
        ((isCompact_range c.embedded.continuous).isClosed.union
          (isCompact_range d.embedded.continuous).isClosed).isOpen_compl
      have hU : IsOpen U := hF.connectedComponentIn
      have hUconn : IsConnected U := isConnected_connectedComponentIn_iff.mpr hu
      obtain ⟨p,G,m,a,hQ,hm⟩ := hcanonical M H u
      letI : Group G := m
      letI : MulAction G H2 := a
      obtain ⟨x,hxu⟩ := hQ.toIsQuotientMap.surjective u
      have hxU : p x∈U := hxu.symm ▸ mem_connectedComponentIn hu
      obtain ⟨b,q,hq,hqpoint,hact⟩ := hrestricted p hQ U hU hUconn x hxU
      let C := connectedComponentIn (p ⁻¹' U) x
      let K := MulAction.stabilizer G C
      letI : MulAction K C := b
      obtain ⟨γc,Tc,hTc,hγc,hperiodc,hrangec,hunitc⟩ := hcgeo
      obtain ⟨γd,Td,hTd,hγd,hperiodd,hranged,hunitd⟩ := hdgeo
      let γcC : ContinuousMap ℝ E := ⟨γc,hγc⟩
      let γdC : ContinuousMap ℝ E := ⟨γd,hγd⟩
      obtain ⟨aC,haC,heqC⟩ := actual_developed_geodesic_preimage_is_union_complete_lines
        p hQ.isCoveringMap hm γcC hunitc
      obtain ⟨aD,haD,heqD⟩ := actual_developed_geodesic_preimage_is_union_complete_lines
        p hQ.isCoveringMap hm γdC hunitd
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
      have hC : C=connectedComponentIn (p ⁻¹' F) x := by
        dsimp only [C,U]
        rw [←hxu]
        exact hid p hQ.toIsQuotientMap.continuous F x
      refine ⟨p,G,m,a,hQ,hm,x,hxu,b,q,hq,hqpoint,hact,?_,?_⟩
      · intro z
        obtain ⟨V,hV,hzV,hmV⟩ := hm z.val
        refine ⟨Subtype.val ⁻¹' V,hV.preimage continuous_subtype_val,hzV,?_⟩
        intro y hy z hz
        change @dist E H.metric.toDist (q y).val (q z).val=dist y.val z.val
        rw [hqpoint,hqpoint]
        exact hmV y.val hy z.val hz
      · change ∀ y∈C,∀ z∈C,∀ w : H2,dist y w+dist w z=dist y z → w∈C
        rw [hC]
        dsimp only [F]
        rw [Set.preimage_compl,hunion]
        exact actual_complete_geodesic_complement_component_metric_convex lines hlines x
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
    dsimp only at hcover
    obtain ⟨p,G,m,rest⟩ := hcover
    letI := m
    obtain ⟨a,rest⟩ := rest
    letI := a
    obtain ⟨hp,hm,x,hx,b,rest⟩ := rest
    let U := connectedComponentIn (c.image ∪ d.image)ᶜ u
    let C := connectedComponentIn (p ⁻¹' U) x
    letI := b
    obtain ⟨q,hq,hproj,hact,hqm,hconv⟩ := rest
    have hxU : x∈p ⁻¹' U := by
      change p x∈U
      rw [hx]
      exact mem_connectedComponentIn hu
    have hc : ContractibleSpace C := hcontract C ⟨x,mem_connectedComponentIn hxU⟩ hconv
    letI := hc
    exact ⟨p,G,m,a,hp,hm,x,hx,b,q,hq,hproj,hact,hqm,hconv,hc,inferInstance⟩
  dsimp only at hsource
  obtain ⟨p,G,m,rest⟩ := hsource
  letI := m
  obtain ⟨a,rest⟩ := rest
  letI := a
  obtain ⟨hp,hm,x,hx,b,rest⟩ := rest
  letI := b
  obtain ⟨q,hq,hproj,hact,hqm,hconv,hc,hsc⟩ := rest
  letI := hsc
  refine ⟨p,G,m,a,hp,hm,x,hx,b,q,hq,hproj,hact,hqm,hconv,hc,hsc,?_⟩
  intro o
  refine ⟨hq.fundamentalGroupEquiv ⟨o,rfl⟩,?_⟩
  intro γ
  have hlocal : @SMul.smul _ _ b.toSMul
      (hq.fundamentalGroupEquiv ⟨o,rfl⟩ γ).unop o=
      hq.isCoveringMap.monodromy γ ⟨o,rfl⟩ :=
    hq.unop_fundamentalGroupToMulOpposite_smul (e:=⟨o,rfl⟩) (γ:=γ)
  refine ⟨hlocal,?_⟩
  calc
    _ = (@SMul.smul _ _ b.toSMul (hq.fundamentalGroupEquiv ⟨o,rfl⟩ γ).unop o).val :=
      (hact (hq.fundamentalGroupEquiv ⟨o,rfl⟩ γ).unop o).symm
    _ = (hq.isCoveringMap.monodromy γ ⟨o,rfl⟩).val.val := congrArg Subtype.val hlocal
    _ = _ := (hnat p q hp.isCoveringMap hq.isCoveringMap
    (⟨Subtype.val,continuous_subtype_val⟩ : C(_,E))
    (⟨Subtype.val,continuous_subtype_val⟩ : C(_,H2))
    (fun z => (hproj z).symm) o γ.toPath).symm
end CurveComplex.Hyperbolic
