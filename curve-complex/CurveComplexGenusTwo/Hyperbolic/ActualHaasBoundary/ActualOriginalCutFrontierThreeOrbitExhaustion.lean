import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2LocalUnitGeodesicPROVED
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1EmbeddedTraversalComposablePROVED
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualSimpleClosedGeodesicEssentialPROVED
namespace CurveComplex.Hyperbolic
open Set Topology
open scoped Pointwise UpperHalfPlane unitInterval

set_option maxHeartbeats 16000000
set_option maxRecDepth 16000

/-- Exhaust the frontier of the original cut lift by the stabilizer orbits of
its three actual collar ends. The two d axes retain opposite collar signs. -/
theorem actual_original_cut_frontier_three_orbit_exhaustion
    {E S G : Type} [TopologicalSpace E] [TopologicalSpace S] [Group G]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E)
    (c d : Curve E) (hc : Essential c) (hcdiv : DividingCurve c)
    (hcgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image)
    (hdgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic d.image)
    (hdnondiv : ¬ DividingCurve d) (hcd : Disjoint c.image d.image)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image)
    (hdU : d.image ⊆ U)
    (a : MulAction G H2) (p : H2 → E)
    (hq : letI := a; IsQuotientCoveringMap p G)
    (hmetric : ∀ z : H2, ∃ W : Set H2, IsOpen W ∧ z ∈ W ∧
      ∀ y ∈ W, ∀ z ∈ W, @dist E H.metric.toDist (p y) (p z) = dist y z)
    (x : H2) (hx : p x ∈ U \ d.image) :
    letI := a
    let D : Set E := U \ d.image
    let C : Set H2 := connectedComponentIn (p ⁻¹' D) x
    let K := MulAction.stabilizer G C
    ∃ αc αd0 αd1 : ℝ → H2,
      Isometry αc ∧ Isometry αd0 ∧ Isometry αd1 ∧
      Set.range αc ⊆ frontier C ∧ Set.range αd0 ⊆ frontier C ∧
      Set.range αd1 ⊆ frontier C ∧
      p '' Set.range αc = c.image ∧ p '' Set.range αd0 = d.image ∧
      p '' Set.range αd1 = d.image ∧
      frontier C =
        (⋃ k : K, (fun z => @SMul.smul G H2 a.toSMul k.val z) '' Set.range αc) ∪
        (⋃ k : K, (fun z => @SMul.smul G H2 a.toSMul k.val z) '' Set.range αd0) ∪
        (⋃ k : K, (fun z => @SMul.smul G H2 a.toSMul k.val z) '' Set.range αd1) ∧
    ∃ Fc Fd0 Fd1 : C(Interval × Circle, E),
      (∀ z, Fc (1,z) = c.map z ∧ Fd0 (1,z) = d.map z ∧ Fd1 (1,z) = d.map z) ∧
      (∀ t : Interval, (t:ℝ) < 1 → ∀ z,
        Fc (t,z) ∈ D ∧ Fd0 (t,z) ∈ D ∧ Fd1 (t,z) ∈ D) ∧
      (∀ t : Interval, IsEmbedding (fun z => Fc (t,z)) ∧
        IsEmbedding (fun z => Fd0 (t,z)) ∧ IsEmbedding (fun z => Fd1 (t,z))) ∧
    ∃ e : C(Ioo (-1 : ℝ) 1 × Circle, E), IsOpenEmbedding e ∧
      (∀ z, e (⟨0,by norm_num⟩,z) = d.map z) ∧
    ∃ ε : ℝ, ∃ hε : 0 < ε ∧ ε < 1,
      (∀ t z, Fd0 (t,z) = e (⟨-ε*(1-(t:ℝ)), by
        constructor <;> nlinarith [hε.1,hε.2,t.property.1,t.property.2]⟩,z)) ∧
      (∀ t z, Fd1 (t,z) = e (⟨ε*(1-(t:ℝ)), by
        constructor <;> nlinarith [hε.1,hε.2,t.property.1,t.property.2]⟩,z)) ∧
    ∃ Lc Ld0 Ld1 : C(Interval × ℝ, H2),
      (∀ t s, p (Lc (t,s)) = Fc (t,Circle.exp (2*Real.pi*s)) ∧
        p (Ld0 (t,s)) = Fd0 (t,Circle.exp (2*Real.pi*s)) ∧
        p (Ld1 (t,s)) = Fd1 (t,Circle.exp (2*Real.pi*s))) ∧
      (∀ t : Interval, (t:ℝ) < 1 → ∀ s,
        Lc (t,s) ∈ C ∧ Ld0 (t,s) ∈ C ∧ Ld1 (t,s) ∈ C) ∧
      Set.range (fun s => Lc (1,s)) = Set.range αc ∧
      Set.range (fun s => Ld0 (1,s)) = Set.range αd0 ∧
      Set.range (fun s => Ld1 (1,s)) = Set.range αd1 := by
  classical
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 16000 in
  exact (by
    have hSecond {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
        (M : HyperellipticModel E S) (c d : Curve E) (hc : Essential c)
        (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
        (hUV : Disjoint U V) (hcover : U∪V=c.imageᶜ)
        (hfrontU : frontier U=c.image) (hfrontV : frontier V=c.image)
        (hdnondiv : ¬DividingCurve d) (hcd : Disjoint c.image d.image) :
        IsConnected (U\d.image) := by
      classical
      letI : ClosedSurface E := M.genusTwo.2.1.some
      letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
      have hsigns {E : Type} [TopologicalSpace E]
          (c : Curve E) (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
          (hzero : ∀ z,e (⟨0,by norm_num⟩,z)=c.map z)
          (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
          (hUV : Disjoint U V) (hcover : U∪V=c.imageᶜ)
          (hfrontU : frontier U=c.image) (hfrontV : frontier V=c.image) :
          ∃ sgn : ℝ,(sgn=1 ∨ sgn=-1) ∧
            (∀ r : Ioo (0:ℝ) 1,∀ z : Circle,
              ∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈U) ∧
            (∀ r : Ioo (0:ℝ) 1,∀ z : Circle,
              ∃ hr : -sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨-sgn*(r:ℝ),hr⟩,z)∈V) := by
        classical
        let o : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
        have hzero' (z : Circle) : e (o,z) = c.map z := hzero z
        have hoff (r : Set.Ioo (-1:ℝ) 1) (z : Circle) (hr : (r:ℝ) ≠ 0) :
            e (r,z) ∈ U ∪ V := by
          rw [hcover]
          rintro ⟨w,hw⟩
          have hp : (o,w) = (r,z) := he.injective ((hzero' w).trans hw)
          exact hr (congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ)) hp).symm
        have select (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
            (hUV : Disjoint U V) (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image) :
            ∃ sgn : ℝ,(sgn=1 ∨ sgn=-1) ∧
              ∀ r : Ioo (0:ℝ) 1,∀ z : Circle,
                ∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈U := by
          have hoff (r : Set.Ioo (-1:ℝ) 1) (z : Circle) (hr : (r:ℝ) ≠ 0) :
              e (r,z) ∈ U ∪ V := by
            rw [hcover]
            rintro ⟨w,hw⟩
            have hp : (o,w) = (r,z) := he.injective ((hzero' w).trans hw)
            exact hr (congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ)) hp).symm
          have hcl : e (o,1) ∈ closure U := by
            apply frontier_subset_closure
            rw [hfrontU,hzero']
            exact ⟨1,rfl⟩
          obtain ⟨y,hyRange,hyU⟩ := mem_closure_iff.mp hcl (range e) he.isOpen_range ⟨(o,1),rfl⟩
          obtain ⟨⟨r,z⟩,rfl⟩ := hyRange
          have hr : (r:ℝ) ≠ 0 := by
            intro h
            have hro : r = o := Subtype.ext h
            subst r
            have hu : e (o,z) ∈ c.imageᶜ := by rw [←hcover];exact Or.inl hyU
            exact hu (by rw [hzero'];exact ⟨z,rfl⟩)
          let P := Set.Ioo (0:ℝ) 1
          letI : PreconnectedSpace P := Subtype.preconnectedSpace isPreconnected_Ioo
          have side (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
              (hw : ∃ a : P, ∃ z : Circle, e (⟨sgn*(a:ℝ),by rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U) :
              ∀ a : P, ∀ z : Circle,
                e (⟨sgn*(a:ℝ),by rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
            let f : P × Circle → E := fun p => e (⟨sgn*(p.1:ℝ),by
              rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [p.1.property.1,p.1.property.2]⟩,p.2)
            have hf : Continuous f := by dsimp [f];fun_prop
            have hp : IsPreconnected (range f) := by
              simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
            have hsub : range f ⊆ U ∪ V := by
              rintro _ ⟨⟨a,z⟩,rfl⟩
              apply hoff
              rcases hsgn with rfl|rfl <;> nlinarith [a.property.1]
            have hmeet : (range f ∩ U).Nonempty := by
              obtain ⟨a,z,haz⟩ := hw
              exact ⟨f (a,z),⟨(a,z),rfl⟩,haz⟩
            have hleft := hp.subset_left_of_subset_union hU hV hUV hsub hmeet
            intro a z
            exact hleft ⟨(a,z),rfl⟩
          have hex : ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧
              ∀ a : P, ∀ z : Circle,
                ∃ h : sgn*(a:ℝ) ∈ Set.Ioo (-1:ℝ) 1, e (⟨sgn*(a:ℝ),h⟩,z) ∈ U := by
            rcases lt_or_gt_of_ne hr with hrneg|hrpos
            · refine ⟨-1,Or.inr rfl,?_⟩
              have hw : ∃ a : P,∃ z : Circle,e (⟨-1*(a:ℝ),by constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
                let a : P := ⟨-(r:ℝ),by constructor <;> linarith [r.property.1]⟩
                refine ⟨a,z,?_⟩
                convert hyU using 1
                congr 2
                apply Subtype.ext
                dsimp [a];ring
              intro a z
              exact ⟨_,side (-1) (Or.inr rfl) hw a z⟩
            · refine ⟨1,Or.inl rfl,?_⟩
              have hw : ∃ a : P,∃ z : Circle,e (⟨1*(a:ℝ),by constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
                refine ⟨⟨(r:ℝ),hrpos,r.property.2⟩,z,?_⟩
                simpa using hyU
              intro a z
              exact ⟨_,side 1 (Or.inl rfl) hw a z⟩
          exact hex
        obtain ⟨sgn,hsgn,hsgnU⟩ := select U V hU hV hUV hcover hfrontU
        obtain ⟨τ,hτ,hτV⟩ := select V U hV hU hUV.symm (by simpa only [union_comm] using hcover) hfrontV
        have hτeq : τ=-sgn := by
          have ha : (1/2:ℝ)∈Ioo (0:ℝ) 1 := by norm_num
          obtain ⟨hs,hu⟩ := hsgnU ⟨1/2,ha⟩ 1
          obtain ⟨ht,hv⟩ := hτV ⟨1/2,ha⟩ 1
          have hne : sgn≠τ := by
            intro heq
            subst τ
            exact disjoint_left.mp hUV hu hv
          rcases hsgn with rfl|rfl <;> rcases hτ with rfl|rfl <;> norm_num at *
        subst τ
        exact ⟨sgn,hsgn,hsgnU,hτV⟩
      have hconnect {E : Type} [TopologicalSpace E] [LocallyConnectedSpace E]
          (A U N : Set E) (hA : IsOpen A) (hcA : IsConnected A) (hU : IsOpen U)
          (hN : IsOpen N) (hboundary : A ∩ frontier U ⊆ N)
          (q : E) (hq : q∈A∩U)
          (hcollar : A ∩ N ∩ U ⊆ connectedComponentIn (A∩U) q) :
          connectedComponentIn (A∩U) q=A∩U := by
        let F := connectedComponentIn (A∩U) q
        have hF : IsOpen F := (hA.inter hU).connectedComponentIn
        let O := F ∪ (A ∩ (closure U)ᶜ) ∪ (A ∩ N)
        let T := (A∩U) \ F
        have hO : IsOpen O := (hF.union (hA.inter isClosed_closure.isOpen_compl)).union (hA.inter hN)
        have hT : IsOpen T := by
          rw [isOpen_iff_forall_mem_open]
          intro y hy
          refine ⟨connectedComponentIn (A∩U) y,?_,(hA.inter hU).connectedComponentIn,mem_connectedComponentIn hy.1⟩
          intro z hz
          refine ⟨connectedComponentIn_subset _ _ hz,?_⟩
          intro hzF
          have heq := (connectedComponentIn_eq hz).trans (connectedComponentIn_eq hzF).symm
          apply hy.2
          change y∈connectedComponentIn (A∩U) q
          rw [←heq]
          exact mem_connectedComponentIn hy.1
        have hcover : A ⊆ O∪T := by
          intro y hyA
          by_cases hyU : y∈U
          · by_cases hyF : y∈F
            · exact Or.inl (Or.inl (Or.inl hyF))
            · exact Or.inr ⟨⟨hyA,hyU⟩,hyF⟩
          · by_cases hycl : y∈closure U
            · have hyfr : y∈frontier U := by rw [frontier,hU.interior_eq];exact ⟨hycl,hyU⟩
              exact Or.inl (Or.inr ⟨hyA,hboundary ⟨hyA,hyfr⟩⟩)
            · exact Or.inl (Or.inl (Or.inr ⟨hyA,hycl⟩))
        have hdis : Disjoint O T := by
          rw [disjoint_left]
          rintro y ((hyF|hyout)|hyN) hyT
          · exact hyT.2 hyF
          · exact hyout.2 (subset_closure hyT.1.2)
          · exact hyT.2 (hcollar ⟨⟨hyN.1,hyN.2⟩,hyT.1.2⟩)
        have hmeet : (A∩O).Nonempty := ⟨q,hq.1,Or.inl (Or.inl (mem_connectedComponentIn hq))⟩
        have hsub : A⊆O := hcA.isPreconnected.subset_left_of_subset_union hO hT hdis hcover hmeet
        apply Subset.antisymm (connectedComponentIn_subset _ _)
        intro y hy
        rcases hsub hy.1 with (hyF|hyout)|hyN
        · exact hyF
        · exact False.elim (hyout.2 (subset_closure hy.2))
        · exact hcollar ⟨⟨hyN.1,hyN.2⟩,hy.2⟩
      obtain ⟨e,he,hzero⟩ := CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
        E 2 (by omega) M.genusTwo ⟨c,hc⟩
      obtain ⟨sgn,hsgn,hsgnU,hsgnV⟩ := hsigns c e he hzero U V hU hV hUV hcover hfrontU hfrontV
      let o : Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
      have hcenter : {o} ×ˢ (univ : Set Circle) ⊆ e ⁻¹' d.imageᶜ := by
        rintro ⟨r,z⟩ ⟨hr,_⟩
        have hr' : r=o := hr
        subst r
        rw [mem_preimage,hzero]
        exact disjoint_left.mp hcd ⟨z,rfl⟩
      obtain ⟨A,B,hA,hB,hoA,hallB,hAB⟩ := generalized_tube_lemma
        isCompact_singleton (isCompact_univ : IsCompact (univ : Set Circle))
        ((isCompact_range d.embedded.continuous).isClosed.isOpen_compl.preimage e.continuous) hcenter
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hoA (mem_singleton o)))
      let δ := min (ε/2) (1/2)
      have hδ : 0<δ := lt_min (by linarith) (by norm_num)
      have hδ1 : δ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hδε : δ<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      let J := Ioo (0:ℝ) δ
      letI : PreconnectedSpace J := Subtype.preconnectedSpace isPreconnected_Ioo
      let f : J × Circle → E := fun q => e (⟨sgn*(q.1:ℝ),by
        rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [q.1.property.1,q.1.property.2]⟩,q.2)
      have hf : Continuous f := by dsimp [f];fun_prop
      have hfconn : IsPreconnected (range f) := by
        simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
      have hfsub : range f ⊆ d.imageᶜ∩U := by
        rintro _ ⟨⟨r,z⟩,rfl⟩
        obtain ⟨hr,hU'⟩ := hsgnU ⟨(r:ℝ),r.property.1,lt_trans r.property.2 hδ1⟩ z
        refine ⟨hAB ⟨hball ?_,hallB (mem_univ z)⟩,hU'⟩
        change |sgn*(r:ℝ)-0|<ε
        rcases hsgn with rfl|rfl
        · rw [one_mul,sub_zero,abs_of_pos r.property.1]
          exact lt_trans r.property.2 hδε
        · rw [neg_one_mul,sub_zero,abs_neg,abs_of_pos r.property.1]
          exact lt_trans r.property.2 hδε
      let j : J := ⟨δ/2,by constructor <;> linarith⟩
      let q := f (j,1)
      have hq : q∈d.imageᶜ∩U := hfsub (mem_range_self (j,1))
      have hfcomponent : range f ⊆ connectedComponentIn (d.imageᶜ∩U) q :=
        hfconn.subset_connectedComponentIn (mem_range_self (j,1)) hfsub
      let W : Set (Ioo (-1:ℝ) 1 × Circle) := {q | |(q.1:ℝ)|<δ}
      let N := e '' W
      have hW : IsOpen W := by
        exact isOpen_Iio.preimage (continuous_abs.comp (continuous_subtype_val.comp continuous_fst))
      have hN : IsOpen N := he.isOpenMap W hW
      have hboundary : d.imageᶜ ∩ frontier U ⊆ N := by
        rintro y ⟨_,hy⟩
        rw [hfrontU] at hy
        obtain ⟨z,rfl⟩ := hy
        refine ⟨(o,z),?_,hzero z⟩
        change |(o:ℝ)|<δ
        simpa [o] using hδ
      have hcollar : d.imageᶜ ∩ N ∩ U ⊆ connectedComponentIn (d.imageᶜ∩U) q := by
        rintro y ⟨⟨_,⟨⟨r,z⟩,hrW,rfl⟩⟩,hyU⟩
        have hr0 : (r:ℝ)≠0 := by
          intro hr0
          have heq : r=o := Subtype.ext hr0
          have hoU : e (o,z)∈c.imageᶜ := by rw [←hcover];exact Or.inl (heq ▸ hyU)
          exact hoU ⟨z,(hzero z).symm⟩
        have hsame : 0<sgn*(r:ℝ) := by
          rcases hsgn with rfl|rfl
          · simp only [one_mul]
            rcases lt_or_gt_of_ne hr0 with hneg|hpos
            · obtain ⟨ht,hV'⟩ := hsgnV ⟨-(r:ℝ),by constructor <;> linarith [r.property.1]⟩ z
              have heq : (⟨-(1:ℝ)* -(r:ℝ),ht⟩ : Ioo (-1:ℝ) 1)=r := by apply Subtype.ext;ring
              rw [heq] at hV'
              exact False.elim (disjoint_left.mp hUV hyU hV')
            · exact hpos
          · simp only [neg_one_mul]
            rcases lt_or_gt_of_ne hr0 with hneg|hpos
            · linarith
            · obtain ⟨ht,hV'⟩ := hsgnV ⟨(r:ℝ),hpos,r.property.2⟩ z
              have heq : (⟨-(-1:ℝ)*(r:ℝ),ht⟩ : Ioo (-1:ℝ) 1)=r := by apply Subtype.ext;ring
              rw [heq] at hV'
              exact False.elim (disjoint_left.mp hUV hyU hV')
        have hsmall : sgn*(r:ℝ)<δ := by
          change |(r:ℝ)|<δ at hrW
          rcases hsgn with rfl|rfl <;> nlinarith [(abs_lt.mp hrW).1,(abs_lt.mp hrW).2]
        apply hfcomponent
        refine ⟨(⟨sgn*(r:ℝ),hsame,hsmall⟩,z),?_⟩
        dsimp [f]
        congr 2
        apply Subtype.ext
        rcases hsgn with rfl|rfl <;> ring
      have hAconn : IsConnected d.imageᶜ := Classical.not_not.mp hdnondiv
      have hcomp := hconnect d.imageᶜ U N (isCompact_range d.embedded.continuous).isClosed.isOpen_compl
        hAconn hU hN hboundary q hq hcollar
      have hccomp : IsConnected (connectedComponentIn (d.imageᶜ∩U) q) :=
        isConnected_connectedComponentIn_iff.mpr hq
      rw [hcomp] at hccomp
      simpa only [sdiff_eq_compl_inter,inter_comm] using hccomp
    have hShrink {E : Type} [TopologicalSpace E]
        (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
        (O : Set E) (hO : IsOpen O)
        (hcenter : ∀ z,e (⟨0,by norm_num⟩,z)∈O) :
        ∃ e' : C(Ioo (-1:ℝ) 1 × Circle,E),IsOpenEmbedding e' ∧
          (∀ z,e' (⟨0,by norm_num⟩,z)=e (⟨0,by norm_num⟩,z)) ∧ range e'⊆O := by
      have hscale {E : Type} [TopologicalSpace E]
          (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
          (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
          ∃ e' : C(Ioo (-1:ℝ) 1 × Circle,E),IsOpenEmbedding e' ∧
            ∀ r : Ioo (-1:ℝ) 1,∀ z : Circle,∃ hr : δ*(r:ℝ)∈Ioo (-1:ℝ) 1,e' (r,z)=e (⟨δ*(r:ℝ),hr⟩,z) := by
        let R : Ioo (-1:ℝ) 1 → Ioo (-1:ℝ) 1 := fun r => ⟨δ*(r:ℝ),by
          constructor <;> nlinarith [r.property.1,r.property.2]⟩
        have hR : IsOpenEmbedding R := by
          apply IsOpenEmbedding.of_continuous_injective_isOpenMap
          · dsimp [R];fun_prop
          · intro r s h
            apply Subtype.ext
            have heq := congrArg Subtype.val h
            exact mul_left_cancel₀ hδ.ne' heq
          · have ho : IsOpenMap (fun r : Ioo (-1:ℝ) 1 => δ*(r:ℝ)) :=
              (Homeomorph.mulLeft₀ δ hδ.ne').isOpenMap.comp isOpen_Ioo.isOpenMap_subtype_val
            exact ho.codRestrict (fun r => (R r).property)
        let e' : C(Ioo (-1:ℝ) 1 × Circle,E) := ⟨fun q => e (R q.1,q.2),by dsimp [R];fun_prop⟩
        refine ⟨e',he.comp (hR.prodMap (Homeomorph.refl Circle).isOpenEmbedding),?_⟩
        intro r z
        exact ⟨_,rfl⟩
      let o : Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
      have hzero : {o} ×ˢ (univ : Set Circle) ⊆ e ⁻¹' O := by
        rintro ⟨r,z⟩ ⟨hr,_⟩
        have hr' : r=o := hr
        subst r
        exact hcenter z
      obtain ⟨A,B,hA,hB,hoA,hallB,hAB⟩ := generalized_tube_lemma
        isCompact_singleton (isCompact_univ : IsCompact (univ : Set Circle))
        (hO.preimage e.continuous) hzero
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hoA (mem_singleton o)))
      let δ := min (ε/2) (1/2)
      have hδ : 0<δ := lt_min (by linarith) (by norm_num)
      have hδ1 : δ≤1 := le_trans (min_le_right _ _) (by norm_num)
      have hδε : δ<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      obtain ⟨e',he',hparam⟩ := hscale e he δ hδ hδ1
      refine ⟨e',he',?_,?_⟩
      · intro z
        obtain ⟨hr,hh⟩ := hparam o z
        have heq : (⟨δ*(o:ℝ),hr⟩ : Ioo (-1:ℝ) 1)=o := by apply Subtype.ext;simp [o]
        rw [heq] at hh
        exact hh
      · rintro y ⟨⟨r,z⟩,rfl⟩
        obtain ⟨hr,hh⟩ := hparam r z
        rw [hh]
        apply hAB
        refine ⟨hball ?_,hallB (mem_univ z)⟩
        change |δ*(r:ℝ)-0|<ε
        rw [sub_zero,abs_mul,abs_of_pos hδ]
        have hsmall : |(r:ℝ)|<1 := abs_lt.mpr r.property
        have hle := mul_lt_mul_of_pos_left hsmall hδ
        linarith
    have hSigns {E : Type} [TopologicalSpace E]
        (c : Curve E) (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
        (hzero : ∀ z,e (⟨0,by norm_num⟩,z)=c.map z)
        (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
        (hUV : Disjoint U V) (hcover : U∪V=c.imageᶜ)
        (hfrontU : frontier U=c.image) (hfrontV : frontier V=c.image) :
        ∃ sgn : ℝ,(sgn=1 ∨ sgn=-1) ∧
          (∀ r : Ioo (0:ℝ) 1,∀ z : Circle,
            ∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈U) ∧
          (∀ r : Ioo (0:ℝ) 1,∀ z : Circle,
            ∃ hr : -sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨-sgn*(r:ℝ),hr⟩,z)∈V) := by
      classical
      let o : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
      have hzero' (z : Circle) : e (o,z) = c.map z := hzero z
      have hoff (r : Set.Ioo (-1:ℝ) 1) (z : Circle) (hr : (r:ℝ) ≠ 0) :
          e (r,z) ∈ U ∪ V := by
        rw [hcover]
        rintro ⟨w,hw⟩
        have hp : (o,w) = (r,z) := he.injective ((hzero' w).trans hw)
        exact hr (congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ)) hp).symm
      have select (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
          (hUV : Disjoint U V) (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image) :
          ∃ sgn : ℝ,(sgn=1 ∨ sgn=-1) ∧
            ∀ r : Ioo (0:ℝ) 1,∀ z : Circle,
              ∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈U := by
        have hoff (r : Set.Ioo (-1:ℝ) 1) (z : Circle) (hr : (r:ℝ) ≠ 0) :
            e (r,z) ∈ U ∪ V := by
          rw [hcover]
          rintro ⟨w,hw⟩
          have hp : (o,w) = (r,z) := he.injective ((hzero' w).trans hw)
          exact hr (congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ)) hp).symm
        have hcl : e (o,1) ∈ closure U := by
          apply frontier_subset_closure
          rw [hfrontU,hzero']
          exact ⟨1,rfl⟩
        obtain ⟨y,hyRange,hyU⟩ := mem_closure_iff.mp hcl (range e) he.isOpen_range ⟨(o,1),rfl⟩
        obtain ⟨⟨r,z⟩,rfl⟩ := hyRange
        have hr : (r:ℝ) ≠ 0 := by
          intro h
          have hro : r = o := Subtype.ext h
          subst r
          have hu : e (o,z) ∈ c.imageᶜ := by rw [←hcover];exact Or.inl hyU
          exact hu (by rw [hzero'];exact ⟨z,rfl⟩)
        let P := Set.Ioo (0:ℝ) 1
        letI : PreconnectedSpace P := Subtype.preconnectedSpace isPreconnected_Ioo
        have side (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
            (hw : ∃ a : P, ∃ z : Circle, e (⟨sgn*(a:ℝ),by rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U) :
            ∀ a : P, ∀ z : Circle,
              e (⟨sgn*(a:ℝ),by rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
          let f : P × Circle → E := fun p => e (⟨sgn*(p.1:ℝ),by
            rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [p.1.property.1,p.1.property.2]⟩,p.2)
          have hf : Continuous f := by dsimp [f];fun_prop
          have hp : IsPreconnected (range f) := by
            simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
          have hsub : range f ⊆ U ∪ V := by
            rintro _ ⟨⟨a,z⟩,rfl⟩
            apply hoff
            rcases hsgn with rfl|rfl <;> nlinarith [a.property.1]
          have hmeet : (range f ∩ U).Nonempty := by
            obtain ⟨a,z,haz⟩ := hw
            exact ⟨f (a,z),⟨(a,z),rfl⟩,haz⟩
          have hleft := hp.subset_left_of_subset_union hU hV hUV hsub hmeet
          intro a z
          exact hleft ⟨(a,z),rfl⟩
        have hex : ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧
            ∀ a : P, ∀ z : Circle,
              ∃ h : sgn*(a:ℝ) ∈ Set.Ioo (-1:ℝ) 1, e (⟨sgn*(a:ℝ),h⟩,z) ∈ U := by
          rcases lt_or_gt_of_ne hr with hrneg|hrpos
          · refine ⟨-1,Or.inr rfl,?_⟩
            have hw : ∃ a : P,∃ z : Circle,e (⟨-1*(a:ℝ),by constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
              let a : P := ⟨-(r:ℝ),by constructor <;> linarith [r.property.1]⟩
              refine ⟨a,z,?_⟩
              convert hyU using 1
              congr 2
              apply Subtype.ext
              dsimp [a];ring
            intro a z
            exact ⟨_,side (-1) (Or.inr rfl) hw a z⟩
          · refine ⟨1,Or.inl rfl,?_⟩
            have hw : ∃ a : P,∃ z : Circle,e (⟨1*(a:ℝ),by constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
              refine ⟨⟨(r:ℝ),hrpos,r.property.2⟩,z,?_⟩
              simpa using hyU
            intro a z
            exact ⟨_,side 1 (Or.inl rfl) hw a z⟩
        exact hex
      obtain ⟨sgn,hsgn,hsgnU⟩ := select U V hU hV hUV hcover hfrontU
      obtain ⟨τ,hτ,hτV⟩ := select V U hV hU hUV.symm (by simpa only [union_comm] using hcover) hfrontV
      have hτeq : τ=-sgn := by
        have ha : (1/2:ℝ)∈Ioo (0:ℝ) 1 := by norm_num
        obtain ⟨hs,hu⟩ := hsgnU ⟨1/2,ha⟩ 1
        obtain ⟨ht,hv⟩ := hτV ⟨1/2,ha⟩ 1
        have hne : sgn≠τ := by
          intro heq
          subst τ
          exact disjoint_left.mp hUV hu hv
        rcases hsgn with rfl|rfl <;> rcases hτ with rfl|rfl <;> norm_num at *
      subst τ
      exact ⟨sgn,hsgn,hsgnU,hτV⟩
    have hBaseline {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
        [LocallyPathConnectedSpace E]
        (p : P → E) (hp : IsCoveringMap p)
        (D : Set E) (hDo : IsOpen D) (hDconn : IsConnected D)
        (x : P) (hx : p x∈D)
        (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
        (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
        (hinside : ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈D) :
        ∃ L : C(Ioo (-1:ℝ) 1 × ℝ,P),
          (∀ r s,p (L (r,s))=e (r,Circle.exp s)) ∧
          ∀ r : Ioo (0:ℝ) 1,∀ s,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,
            L (⟨sgn*(r:ℝ),hr⟩,s)∈connectedComponentIn (p ⁻¹' D) x := by
      have hprojection {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
          [LocallyPathConnectedSpace E] (p : P → E) (hp : IsCoveringMap p)
          (U : Set E) (hU : IsOpen U) (x : P) :
          p '' connectedComponentIn (p ⁻¹' U) x=connectedComponentIn U (p x) := by
        classical
        by_cases hx : p x∈U
        · let F := p ⁻¹' U
          have hxF : x∈F := hx
          apply subset_antisymm
          · exact (hp.continuous.continuousOn.image_connectedComponentIn_subset hxF).trans
              (connectedComponentIn_mono (p x) (Set.image_preimage_subset p U))
          · intro z hz
            rw [connectedComponentIn_eq_image hx] at hz
            obtain ⟨zU,hzU,rfl⟩ := hz
            letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
            have hjoined : Joined (⟨p x,hx⟩ : U) zU := by
              rw [←mem_pathComponent_iff,pathComponent_eq_connectedComponent]
              exact hzU
            obtain ⟨γ⟩ := hjoined
            let q := U.restrictPreimage p
            let xF : p ⁻¹' U := ⟨x,hx⟩
            obtain ⟨δ,hδp,hδ0⟩ := (hp.restrictPreimage U).exists_path_lifts
              γ.toContinuousMap xF γ.source
            have hδrange : Set.range (fun t : unitInterval => (δ t).val)⊆connectedComponentIn F x := by
              apply (isConnected_range (continuous_subtype_val.comp δ.continuous)).isPreconnected.subset_connectedComponentIn
              · exact ⟨0,congrArg Subtype.val hδ0⟩
              · rintro v ⟨t,rfl⟩
                exact (δ t).property
            refine ⟨(δ 1).val,hδrange ⟨1,rfl⟩,?_⟩
            exact (congrArg Subtype.val (congrFun hδp 1)).trans (congrArg Subtype.val γ.target)
        · have hxF : x∉p ⁻¹' U := hx
          rw [connectedComponentIn_eq_empty hxF,Set.image_empty,connectedComponentIn_eq_empty hx]
      have hlift {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
          (p : P → E) (hp : IsCoveringMap p)
          (e : C(Ioo (-1:ℝ) 1 × Circle,E))
          (he : IsOpenEmbedding e) (r : Ioo (-1:ℝ) 1) (s : ℝ)
          (y : P) (hy : p y=e (r,Circle.exp s)) :
          ∃ L : C(Ioo (-1:ℝ) 1 × ℝ,P),
            L (r,s)=y ∧ (∀ r s,p (L (r,s))=e (r,Circle.exp s)) ∧ IsOpenMap L := by
        letI : PreconnectedSpace (Ioo (-1:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
        letI : ContractibleSpace (Ioo (-1:ℝ) 1) := (convex_Ioo (-1:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
        letI : LocallyPathConnectedSpace (Ioo (-1:ℝ) 1) := isOpen_Ioo.locallyPathConnectedSpace
        let f : C(Ioo (-1:ℝ) 1 × ℝ,E) := ⟨fun q => e (q.1,Circle.exp q.2),by fun_prop⟩
        obtain ⟨L,⟨hstart,hlift⟩,_⟩ := hp.existsUnique_continuousMap_lifts f (r,s) y hy
        refine ⟨L,hstart,fun r s => congrFun hlift (r,s),?_⟩
        have hclock : IsLocalHomeomorph (fun q : Ioo (-1:ℝ) 1 × ℝ => (q.1,Circle.exp q.2)) := by
          intro q
          obtain ⟨b,hq,hb⟩ := isLocalHomeomorph_circleExp q.2
          refine ⟨(Homeomorph.refl (Ioo (-1:ℝ) 1)).toOpenPartialHomeomorph.prod b,?_,?_⟩
          · exact ⟨mem_univ _,hq⟩
          · funext q
            exact Prod.ext rfl (congrFun hb q.2)
        have hf : IsLocalHomeomorph f := he.isLocalHomeomorph.comp hclock
        have hcomp : IsLocalHomeomorph (p ∘ L) := hlift.symm ▸ hf
        exact (hcomp.of_comp hp.isLocalHomeomorph L.continuous).isOpenMap
      classical
      let r0 : Ioo (-1:ℝ) 1 := ⟨sgn*(1/2),by rcases hsgn with rfl|rfl <;> constructor <;> norm_num⟩
      obtain ⟨hr,hbase⟩ := hinside ⟨1/2,by norm_num⟩ 1
      have hcomp : connectedComponentIn D (p x)=D := by
        apply Subset.antisymm (connectedComponentIn_subset _ _)
        exact hDconn.isPreconnected.subset_connectedComponentIn hx subset_rfl
      have hproj := hprojection p hp D hDo x
      rw [hcomp] at hproj
      obtain ⟨y,hyC,hyp⟩ : ∃y,y∈connectedComponentIn (p ⁻¹' D) x ∧ p y=e (r0,1) := by
        have hm : e (r0,1)∈p '' connectedComponentIn (p ⁻¹' D) x := by rw [hproj];exact hbase
        exact hm
      obtain ⟨L,hLstart,hLp,hLopen⟩ := hlift p hp e he r0 0 y (by simpa using hyp)
      refine ⟨L,hLp,?_⟩
      let J := Ioo (0:ℝ) 1
      letI : PreconnectedSpace J := Subtype.preconnectedSpace isPreconnected_Ioo
      let f : J × ℝ → P := fun q => L (⟨sgn*(q.1:ℝ),by
        rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [q.1.property.1,q.1.property.2]⟩,q.2)
      have hf : Continuous f := by dsimp [f];fun_prop
      have hc : IsPreconnected (range f) := by
        simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
      have hsub : range f ⊆ p ⁻¹' D := by
        rintro _ ⟨⟨r,s⟩,rfl⟩
        obtain ⟨hr,hh⟩ := hinside r (Circle.exp s)
        change p (L _)∈D
        rw [hLp]
        exact hh
      have hmeet : y∈range f := ⟨(⟨1/2,by dsimp [J];norm_num⟩,0),hLstart⟩
      have hsubC := hc.subset_connectedComponentIn hmeet hsub
      rw [←connectedComponentIn_eq hyC] at hsubC
      intro r s
      exact ⟨_,hsubC (mem_range_self (r,s))⟩
    have hCoverC {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (D : Set E) (x : P) (hx : p x∈D)
        (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
        (hcenter : ∀ z,e (⟨0,by norm_num⟩,z)∉D)
        (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
        (hinside : ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈D)
        (houtside : ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : -sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨-sgn*(r:ℝ),hr⟩,z)∉D)
        (L0 : C(Ioo (-1:ℝ) 1 × ℝ,P))
        (hproj0 : ∀ r s,p (L0 (r,s))=e (r,Circle.exp s))
        (hhalf0 : ∀ r : Ioo (0:ℝ) 1,∀ s,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,
          L0 (⟨sgn*(r:ℝ),hr⟩,s)∈connectedComponentIn (p ⁻¹' D) x)
        (y : P) (hy : y∈frontier (connectedComponentIn (p ⁻¹' D) x))
        (hybase : ∃ z : Circle,p y=e (⟨0,by norm_num⟩,z)) :
        letI := a
        let C := connectedComponentIn (p ⁻¹' D) x
        ∃ k : MulAction.stabilizer G C,
          y∈(fun z => k.val • z) '' range (fun s => L0 (⟨0,by norm_num⟩,s)) := by
      have hlift {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
          (p : P → E) (hp : IsCoveringMap p)
          (e : C(Ioo (-1:ℝ) 1 × Circle,E))
          (he : IsOpenEmbedding e) (r : Ioo (-1:ℝ) 1) (s : ℝ)
          (y : P) (hy : p y=e (r,Circle.exp s)) :
          ∃ L : C(Ioo (-1:ℝ) 1 × ℝ,P),
            L (r,s)=y ∧ (∀ r s,p (L (r,s))=e (r,Circle.exp s)) ∧ IsOpenMap L := by
        letI : PreconnectedSpace (Ioo (-1:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
        letI : ContractibleSpace (Ioo (-1:ℝ) 1) := (convex_Ioo (-1:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
        letI : LocallyPathConnectedSpace (Ioo (-1:ℝ) 1) := isOpen_Ioo.locallyPathConnectedSpace
        let f : C(Ioo (-1:ℝ) 1 × ℝ,E) := ⟨fun q => e (q.1,Circle.exp q.2),by fun_prop⟩
        obtain ⟨L,⟨hstart,hlift⟩,_⟩ := hp.existsUnique_continuousMap_lifts f (r,s) y hy
        refine ⟨L,hstart,fun r s => congrFun hlift (r,s),?_⟩
        have hclock : IsLocalHomeomorph (fun q : Ioo (-1:ℝ) 1 × ℝ => (q.1,Circle.exp q.2)) := by
          intro q
          obtain ⟨b,hq,hb⟩ := isLocalHomeomorph_circleExp q.2
          refine ⟨(Homeomorph.refl (Ioo (-1:ℝ) 1)).toOpenPartialHomeomorph.prod b,?_,?_⟩
          · exact ⟨mem_univ _,hq⟩
          · funext q
            exact Prod.ext rfl (congrFun hb q.2)
        have hf : IsLocalHomeomorph f := he.isLocalHomeomorph.comp hclock
        have hcomp : IsLocalHomeomorph (p ∘ L) := hlift.symm ▸ hf
        exact (hcomp.of_comp hp.isLocalHomeomorph L.continuous).isOpenMap
      have haccess {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
          (p : P → E) (D : Set E) (x : P)
          (L : C(Ioo (-1:ℝ) 1 × ℝ,P)) (hLopen : IsOpenMap L)
          (hcenter : ∀ s : ℝ, p (L (⟨0,by norm_num⟩,s))∉D)
          (hinvariant : ∀ sgn : ℝ,∀ hsgn : sgn=1 ∨ sgn=-1,
            (∃ r : Ioo (0:ℝ) 1,∃ s : ℝ,p (L (⟨sgn*(r:ℝ),by
              rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s))∈D) →
            ∀ r : Ioo (0:ℝ) 1,∀ s : ℝ,p (L (⟨sgn*(r:ℝ),by
              rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s))∈D)
          (s₀ : ℝ) (hy : L (⟨0,by norm_num⟩,s₀)∈frontier (connectedComponentIn (p ⁻¹' D) x)) :
          ∃ sgn : ℝ, (sgn=1 ∨ sgn=-1) ∧
            ∀ r : Ioo (0:ℝ) 1, ∀ s : ℝ,
              ∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,
                L (⟨sgn*(r:ℝ),hr⟩,s)∈connectedComponentIn (p ⁻¹' D) x := by
        let C := connectedComponentIn (p ⁻¹' D) x
        have hopen : IsOpen (range L) := by
          simpa only [image_univ] using hLopen univ isOpen_univ
        obtain ⟨w,⟨⟨r,s⟩,rfl⟩,hwC⟩ := mem_closure_iff.mp hy.1 (range L) hopen ⟨(⟨0,by norm_num⟩,s₀),rfl⟩
        have hr : (r:ℝ)≠0 := by
          intro hr
          have he : r=⟨0,by norm_num⟩ := Subtype.ext hr
          apply hcenter s
          exact connectedComponentIn_subset (p ⁻¹' D) x (he ▸ hwC)
        let J := Ioo (0:ℝ) 1
        letI : PreconnectedSpace J := Subtype.preconnectedSpace isPreconnected_Ioo
        have half (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
            (hmeet : ∃ r : J,∃ s : ℝ,L (⟨sgn*(r:ℝ),by
              rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s)∈C) :
            ∀ r : J,∀ s : ℝ,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,L (⟨sgn*(r:ℝ),hr⟩,s)∈C := by
          let f : J × ℝ → P := fun q => L (⟨sgn*(q.1:ℝ),by
            rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [q.1.property.1,q.1.property.2]⟩,q.2)
          have hf : Continuous f := by dsimp [f];fun_prop
          have hconn : IsPreconnected (range f) := by
            simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
          obtain ⟨r,s,hinsideC⟩ := hmeet
          have hbase : ∃ r : Ioo (0:ℝ) 1,∃ s : ℝ,p (L (⟨sgn*(r:ℝ),by
              rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s))∈D :=
            ⟨r,s,connectedComponentIn_subset (p ⁻¹' D) x hinsideC⟩
          have hsub : range f ⊆ p ⁻¹' D := by
            rintro _ ⟨⟨r,s⟩,rfl⟩
            exact hinvariant sgn hsgn hbase r s
          have hcomponent := hconn.subset_connectedComponentIn (show f (r,s)∈range f from mem_range_self _) hsub
          have heq := connectedComponentIn_eq hinsideC
          rw [←heq] at hcomponent
          intro r s
          exact ⟨_,hcomponent (mem_range_self (r,s))⟩
        rcases lt_or_gt_of_ne hr with hneg|hpos
        · refine ⟨-1,Or.inr rfl,half (-1) (Or.inr rfl) ?_⟩
          let r' : J := ⟨-(r:ℝ),by constructor <;> linarith [r.property.1]⟩
          refine ⟨r',s,?_⟩
          convert hwC using 1
          congr 2
          apply Subtype.ext
          dsimp [r'];ring
        · refine ⟨1,Or.inl rfl,half 1 (Or.inl rfl) ?_⟩
          refine ⟨⟨(r:ℝ),hpos,r.property.2⟩,s,?_⟩
          simpa using hwC
      
      have htrans {P E G A : Type} [TopologicalSpace P] [TopologicalSpace E]
          [TopologicalSpace A] [PreconnectedSpace A] [Group G]
          (a : MulAction G P) (p : P → E)
          (hq : letI := a; IsQuotientCoveringMap p G)
          (D : Set E) (x : P) (hx : p x ∈ D)
          (L L' : C(A,P)) (hproj : ∀ u, p (L u)=p (L' u))
          (u : A) (hL : L u ∈ connectedComponentIn (p ⁻¹' D) x)
          (hL' : L' u ∈ connectedComponentIn (p ⁻¹' D) x) :
          letI := a
          let C := connectedComponentIn (p ⁻¹' D) x
          ∃ g : MulAction.stabilizer G C, ∀ v, g.val • L v = L' v := by
        letI := a
        letI : ContinuousConstSMul G P := hq.toContinuousConstSMul
        let F := p ⁻¹' D
        let C := connectedComponentIn F x
        have hF (g : G) : (g • ·) '' F=F := by
          ext z
          constructor
          · rintro ⟨w,hw,rfl⟩
            change p (g • w)∈D
            rw [hq.map_smul]
            exact hw
          · intro hz
            refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
            change p (g⁻¹ • z)∈D
            rw [hq.map_smul]
            exact hz
        have htrans (g : G) : (g • ·) '' C=connectedComponentIn F (g • x) := by
          have ht := (Homeomorph.smul g).image_connectedComponentIn (show x∈F from hx)
          change (g • ·) '' connectedComponentIn F x=connectedComponentIn ((g • ·) '' F) (g • x) at ht
          rw [hF] at ht
          exact ht
        obtain ⟨g,hg⟩ := hq.apply_eq_iff_mem_orbit.mp (hproj u).symm
        have himage : L' u∈(g • ·) '' C := ⟨L u,hL,hg⟩
        have hcomp : connectedComponentIn F (g • x)=C :=
          (connectedComponentIn_eq (htrans g ▸ himage)).trans (connectedComponentIn_eq hL').symm
        have hgK : g∈MulAction.stabilizer G C := by
          apply MulAction.mem_stabilizer_iff.mpr
          change (g • ·) '' C=C
          exact (htrans g).trans hcomp
        refine ⟨⟨g,hgK⟩,?_⟩
        have heq : (fun v => g • L v)=(fun v => L' v) :=
          hq.isCoveringMap.eq_of_comp_eq
            ((hq.continuous_const_smul g).comp L.continuous) L'.continuous
            (by funext v;exact (hq.map_smul g).trans (hproj v)) u hg
        exact congrFun heq
      letI := a
      letI : PreconnectedSpace (Ioo (-1:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
      obtain ⟨z,hz⟩ := hybase
      obtain ⟨s₀,hs₀⟩ := Circle.exp_surjective z
      obtain ⟨L,hLzero,hLproj,hLopen⟩ := hlift p hq.isCoveringMap e he ⟨0,by norm_num⟩ s₀ y (by rw [hs₀];exact hz)
      have hc : ∀ s,p (L (⟨0,by norm_num⟩,s))∉D := by
        intro s
        rw [hLproj]
        exact hcenter _
      have hinvariant (τ : ℝ) (hτ : τ=1 ∨ τ=-1)
          (hbase : ∃ r : Ioo (0:ℝ) 1,∃ s : ℝ,p (L (⟨τ*(r:ℝ),by
            rcases hτ with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s))∈D) :
          ∀ r : Ioo (0:ℝ) 1,∀ s : ℝ,p (L (⟨τ*(r:ℝ),by
            rcases hτ with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s))∈D := by
        have heq : τ=sgn := by
          by_contra hne
          have heq : τ=-sgn := by
            rcases hτ with rfl|rfl <;> rcases hsgn with rfl|rfl <;> norm_num at *
          obtain ⟨r,s,hh⟩ := hbase
          obtain ⟨hr,hout⟩ := houtside r (Circle.exp s)
          rw [hLproj] at hh
          subst τ
          exact hout hh
        subst τ
        intro r s
        obtain ⟨hr,hi⟩ := hinside r (Circle.exp s)
        rw [hLproj]
        exact hi
      obtain ⟨τ,hτ,hhalf⟩ := haccess p D x L hLopen hc hinvariant s₀ (hLzero.symm ▸ hy)
      have heq : τ=sgn := by
        by_contra hne
        have heq : τ=-sgn := by
          rcases hτ with rfl|rfl <;> rcases hsgn with rfl|rfl <;> norm_num at *
        obtain ⟨hr,hh⟩ := hhalf ⟨1/2,by norm_num⟩ 0
        have hb := connectedComponentIn_subset (p ⁻¹' D) x hh
        change p (L (⟨τ*(1/2:ℝ),hr⟩,0))∈D at hb
        rw [hLproj] at hb
        obtain ⟨ht,hout⟩ := houtside ⟨1/2,by norm_num⟩ (Circle.exp 0)
        subst τ
        exact hout hb
      subst τ
      obtain ⟨hr,hLr⟩ := hhalf ⟨1/2,by norm_num⟩ 0
      obtain ⟨hr0,hL0r⟩ := hhalf0 ⟨1/2,by norm_num⟩ 0
      obtain ⟨k,hk⟩ := htrans a p hq D x hx L0 L
        (fun q => (hproj0 q.1 q.2).trans (hLproj q.1 q.2).symm)
        (⟨sgn*(1/2:ℝ),hr⟩,0) hL0r hLr
      refine ⟨k,L0 (⟨0,by norm_num⟩,s₀),mem_range_self s₀,?_⟩
      exact (hk (⟨0,by norm_num⟩,s₀)).trans hLzero
    have hCoverD {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (D : Set E) (x : P) (hx : p x∈D)
        (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
        (hcenter : ∀ z,p (x)∈D → e (⟨0,by norm_num⟩,z)∉D)
        (hinside : ∀ r : Ioo (-1:ℝ) 1,(r:ℝ)≠0 → ∀ z,e (r,z)∈D)
        (L0 L1 : C(Ioo (-1:ℝ) 1 × ℝ,P))
        (hproj0 : ∀ r s,p (L0 (r,s))=e (r,Circle.exp s))
        (hproj1 : ∀ r s,p (L1 (r,s))=e (r,Circle.exp s))
        (hneg : ∀ r : Ioo (-1:ℝ) 1,(r:ℝ)<0 → ∀ s,L0 (r,s)∈connectedComponentIn (p ⁻¹' D) x)
        (hpos : ∀ r : Ioo (-1:ℝ) 1,0<(r:ℝ) → ∀ s,L1 (r,s)∈connectedComponentIn (p ⁻¹' D) x)
        (y : P) (hy : y∈frontier (connectedComponentIn (p ⁻¹' D) x))
        (hybase : ∃ z : Circle,p y=e (⟨0,by norm_num⟩,z)) :
        letI := a
        let C := connectedComponentIn (p ⁻¹' D) x
        ∃ k : MulAction.stabilizer G C,
          y∈(fun z => k.val • z) '' range (fun s => L0 (⟨0,by norm_num⟩,s)) ∨
          y∈(fun z => k.val • z) '' range (fun s => L1 (⟨0,by norm_num⟩,s)) := by
      have hlift {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
          (p : P → E) (hp : IsCoveringMap p)
          (e : C(Ioo (-1:ℝ) 1 × Circle,E))
          (he : IsOpenEmbedding e) (r : Ioo (-1:ℝ) 1) (s : ℝ)
          (y : P) (hy : p y=e (r,Circle.exp s)) :
          ∃ L : C(Ioo (-1:ℝ) 1 × ℝ,P),
            L (r,s)=y ∧ (∀ r s,p (L (r,s))=e (r,Circle.exp s)) ∧ IsOpenMap L := by
        letI : PreconnectedSpace (Ioo (-1:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
        letI : ContractibleSpace (Ioo (-1:ℝ) 1) := (convex_Ioo (-1:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
        letI : LocallyPathConnectedSpace (Ioo (-1:ℝ) 1) := isOpen_Ioo.locallyPathConnectedSpace
        let f : C(Ioo (-1:ℝ) 1 × ℝ,E) := ⟨fun q => e (q.1,Circle.exp q.2),by fun_prop⟩
        obtain ⟨L,⟨hstart,hlift⟩,_⟩ := hp.existsUnique_continuousMap_lifts f (r,s) y hy
        refine ⟨L,hstart,fun r s => congrFun hlift (r,s),?_⟩
        have hclock : IsLocalHomeomorph (fun q : Ioo (-1:ℝ) 1 × ℝ => (q.1,Circle.exp q.2)) := by
          intro q
          obtain ⟨b,hq,hb⟩ := isLocalHomeomorph_circleExp q.2
          refine ⟨(Homeomorph.refl (Ioo (-1:ℝ) 1)).toOpenPartialHomeomorph.prod b,?_,?_⟩
          · exact ⟨mem_univ _,hq⟩
          · funext q
            exact Prod.ext rfl (congrFun hb q.2)
        have hf : IsLocalHomeomorph f := he.isLocalHomeomorph.comp hclock
        have hcomp : IsLocalHomeomorph (p ∘ L) := hlift.symm ▸ hf
        exact (hcomp.of_comp hp.isLocalHomeomorph L.continuous).isOpenMap
      have haccess {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
          (p : P → E) (D : Set E) (x : P)
          (L : C(Ioo (-1:ℝ) 1 × ℝ,P)) (hLopen : IsOpenMap L)
          (hcenter : ∀ s : ℝ, p (L (⟨0,by norm_num⟩,s))∉D)
          (hinside : ∀ r : Ioo (-1:ℝ) 1, (r:ℝ)≠0 → ∀ s, p (L (r,s))∈D)
          (s₀ : ℝ) (hy : L (⟨0,by norm_num⟩,s₀)∈frontier (connectedComponentIn (p ⁻¹' D) x)) :
          ∃ sgn : ℝ, (sgn=1 ∨ sgn=-1) ∧
            ∀ r : Ioo (0:ℝ) 1, ∀ s : ℝ,
              ∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,
                L (⟨sgn*(r:ℝ),hr⟩,s)∈connectedComponentIn (p ⁻¹' D) x := by
        let C := connectedComponentIn (p ⁻¹' D) x
        have hopen : IsOpen (range L) := by
          simpa only [image_univ] using hLopen univ isOpen_univ
        obtain ⟨w,⟨⟨r,s⟩,rfl⟩,hwC⟩ := mem_closure_iff.mp hy.1 (range L) hopen ⟨(⟨0,by norm_num⟩,s₀),rfl⟩
        have hr : (r:ℝ)≠0 := by
          intro hr
          have he : r=⟨0,by norm_num⟩ := Subtype.ext hr
          apply hcenter s
          exact connectedComponentIn_subset (p ⁻¹' D) x (he ▸ hwC)
        let J := Ioo (0:ℝ) 1
        letI : PreconnectedSpace J := Subtype.preconnectedSpace isPreconnected_Ioo
        have half (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
            (hmeet : ∃ r : J,∃ s : ℝ,L (⟨sgn*(r:ℝ),by
              rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]⟩,s)∈C) :
            ∀ r : J,∀ s : ℝ,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,L (⟨sgn*(r:ℝ),hr⟩,s)∈C := by
          let f : J × ℝ → P := fun q => L (⟨sgn*(q.1:ℝ),by
            rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [q.1.property.1,q.1.property.2]⟩,q.2)
          have hf : Continuous f := by dsimp [f];fun_prop
          have hconn : IsPreconnected (range f) := by
            simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
          have hsub : range f ⊆ p ⁻¹' D := by
            rintro _ ⟨⟨r,s⟩,rfl⟩
            apply hinside
            rcases hsgn with rfl|rfl <;> nlinarith [r.property.1]
          obtain ⟨r,s,hinsideC⟩ := hmeet
          have hcomponent := hconn.subset_connectedComponentIn (show f (r,s)∈range f from mem_range_self _) hsub
          have heq := connectedComponentIn_eq hinsideC
          rw [←heq] at hcomponent
          intro r s
          exact ⟨_,hcomponent (mem_range_self (r,s))⟩
        rcases lt_or_gt_of_ne hr with hneg|hpos
        · refine ⟨-1,Or.inr rfl,half (-1) (Or.inr rfl) ?_⟩
          let r' : J := ⟨-(r:ℝ),by constructor <;> linarith [r.property.1]⟩
          refine ⟨r',s,?_⟩
          convert hwC using 1
          congr 2
          apply Subtype.ext
          dsimp [r'];ring
        · refine ⟨1,Or.inl rfl,half 1 (Or.inl rfl) ?_⟩
          refine ⟨⟨(r:ℝ),hpos,r.property.2⟩,s,?_⟩
          simpa using hwC
      
      have htrans {P E G A : Type} [TopologicalSpace P] [TopologicalSpace E]
          [TopologicalSpace A] [PreconnectedSpace A] [Group G]
          (a : MulAction G P) (p : P → E)
          (hq : letI := a; IsQuotientCoveringMap p G)
          (D : Set E) (x : P) (hx : p x ∈ D)
          (L L' : C(A,P)) (hproj : ∀ u, p (L u)=p (L' u))
          (u : A) (hL : L u ∈ connectedComponentIn (p ⁻¹' D) x)
          (hL' : L' u ∈ connectedComponentIn (p ⁻¹' D) x) :
          letI := a
          let C := connectedComponentIn (p ⁻¹' D) x
          ∃ g : MulAction.stabilizer G C, ∀ v, g.val • L v = L' v := by
        letI := a
        letI : ContinuousConstSMul G P := hq.toContinuousConstSMul
        let F := p ⁻¹' D
        let C := connectedComponentIn F x
        have hF (g : G) : (g • ·) '' F=F := by
          ext z
          constructor
          · rintro ⟨w,hw,rfl⟩
            change p (g • w)∈D
            rw [hq.map_smul]
            exact hw
          · intro hz
            refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
            change p (g⁻¹ • z)∈D
            rw [hq.map_smul]
            exact hz
        have htrans (g : G) : (g • ·) '' C=connectedComponentIn F (g • x) := by
          have ht := (Homeomorph.smul g).image_connectedComponentIn (show x∈F from hx)
          change (g • ·) '' connectedComponentIn F x=connectedComponentIn ((g • ·) '' F) (g • x) at ht
          rw [hF] at ht
          exact ht
        obtain ⟨g,hg⟩ := hq.apply_eq_iff_mem_orbit.mp (hproj u).symm
        have himage : L' u∈(g • ·) '' C := ⟨L u,hL,hg⟩
        have hcomp : connectedComponentIn F (g • x)=C :=
          (connectedComponentIn_eq (htrans g ▸ himage)).trans (connectedComponentIn_eq hL').symm
        have hgK : g∈MulAction.stabilizer G C := by
          apply MulAction.mem_stabilizer_iff.mpr
          change (g • ·) '' C=C
          exact (htrans g).trans hcomp
        refine ⟨⟨g,hgK⟩,?_⟩
        have heq : (fun v => g • L v)=(fun v => L' v) :=
          hq.isCoveringMap.eq_of_comp_eq
            ((hq.continuous_const_smul g).comp L.continuous) L'.continuous
            (by funext v;exact (hq.map_smul g).trans (hproj v)) u hg
        exact congrFun heq
      letI := a
      letI : PreconnectedSpace (Ioo (-1:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
      obtain ⟨z,hz⟩ := hybase
      obtain ⟨s₀,hs₀⟩ := Circle.exp_surjective z
      obtain ⟨L,hLzero,hLproj,hLopen⟩ := hlift p hq.isCoveringMap e he ⟨0,by norm_num⟩ s₀ y (by rw [hs₀];exact hz)
      have hc : ∀ s,p (L (⟨0,by norm_num⟩,s))∉D := by
        intro s
        rw [hLproj]
        exact hcenter _ hx
      have hi : ∀ r : Ioo (-1:ℝ) 1,(r:ℝ)≠0 → ∀ s,p (L (r,s))∈D := by
        intro r hr s
        rw [hLproj]
        exact hinside r hr _
      obtain ⟨sgn,hsgn,hhalf⟩ := haccess p D x L hLopen hc hi s₀ (hLzero.symm ▸ hy)
      let r0 : Ioo (-1:ℝ) 1 := ⟨sgn*(1/2),by rcases hsgn with rfl|rfl <;> constructor <;> norm_num⟩
      have hLr : L (r0,0)∈connectedComponentIn (p ⁻¹' D) x := by
        obtain ⟨hr,hh⟩ := hhalf ⟨1/2,by norm_num⟩ 0
        exact hh
      rcases hsgn with rfl|rfl
      · have hL1r : L1 (r0,0)∈connectedComponentIn (p ⁻¹' D) x := hpos r0 (by dsimp [r0];norm_num) 0
        obtain ⟨k,hk⟩ := htrans a p hq D x hx L1 L
          (fun q => (hproj1 q.1 q.2).trans (hLproj q.1 q.2).symm) (r0,0) hL1r hLr
        refine ⟨k,Or.inr ?_⟩
        refine ⟨L1 (⟨0,by norm_num⟩,s₀),mem_range_self s₀,?_⟩
        exact (hk (⟨0,by norm_num⟩,s₀)).trans hLzero
      · have hL0r : L0 (r0,0)∈connectedComponentIn (p ⁻¹' D) x := hneg r0 (by dsimp [r0];norm_num) 0
        obtain ⟨k,hk⟩ := htrans a p hq D x hx L0 L
          (fun q => (hproj0 q.1 q.2).trans (hLproj q.1 q.2).symm) (r0,0) hL0r hLr
        refine ⟨k,Or.inl ?_⟩
        refine ⟨L0 (⟨0,by norm_num⟩,s₀),mem_range_self s₀,?_⟩
        exact (hk (⟨0,by norm_num⟩,s₀)).trans hLzero
    have hUnion {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (C Lc L0 L1 : Set P)
        (hc : Lc⊆frontier C) (h0 : L0⊆frontier C) (h1 : L1⊆frontier C)
        (hcover : letI := a;∀ y∈frontier C,∃ k : MulAction.stabilizer G C,
          y∈(fun z => k.val • z) '' Lc ∨ y∈(fun z => k.val • z) '' L0 ∨ y∈(fun z => k.val • z) '' L1) :
        letI := a
        let K := MulAction.stabilizer G C
        frontier C = (⋃ k : K,(fun z => k.val • z) '' Lc) ∪
          (⋃ k : K,(fun z => k.val • z) '' L0) ∪ (⋃ k : K,(fun z => k.val • z) '' L1) := by
      letI := a
      letI : ContinuousConstSMul G P := hq.toContinuousConstSMul
      let K := MulAction.stabilizer G C
      have hp (k : K) : (fun z => k.val • z) '' frontier C=frontier C := by
        have heq := (Homeomorph.smul k.val).image_frontier C
        have hk : (fun z => k.val • z) '' C=C := MulAction.mem_stabilizer_iff.mp k.property
        change (fun z => k.val • z) '' frontier C=frontier ((fun z => k.val • z) '' C) at heq
        rwa [hk] at heq
      apply Subset.antisymm
      · intro y hy
        obtain ⟨k,hk⟩ := hcover y hy
        rcases hk with hk|hk|hk
        · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨k,hk⟩))
        · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨k,hk⟩))
        · exact Or.inr (mem_iUnion.mpr ⟨k,hk⟩)
      · have hsub (L : Set P) (hL : L⊆frontier C) :
            (⋃ k : K,(fun z => k.val • z) '' L)⊆frontier C := by
          intro y hy
          obtain ⟨k,hy⟩ := mem_iUnion.mp hy
          rw [←hp k]
          exact image_mono hL hy
        exact union_subset (union_subset (hsub Lc hc) (hsub L0 h0)) (hsub L1 h1)
    have hAxis {E G : Type} [MetricSpace E] [Group G]
        (a : MulAction G H2) (p : H2 → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (hmetric : ∀x : H2,∃U : Set H2,IsOpen U ∧ x∈U ∧
          ∀y∈U,∀z∈U,dist (p y) (p z)=dist y z)
        (g : C(Circle,E)) (hg : IsEmbedding g) (hgeo : IsParametrizedClosedGeodesic g)
        (ell : C(ℝ,H2)) (hell : ∀t : ℝ,p (ell t)=g (Circle.exp (2*Real.pi*t))) :
        ∃ α : C(ℝ,H2),Isometry α ∧ range α=range ell := by
      have actual_circle_homeomorphism_lift (φ : Circle ≃ₜ Circle) :
          ∃ ψ : ℝ ≃ₜ ℝ, ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t) := by
        let f : C(ℝ, Circle) := ⟨fun t => φ (Circle.exp t),
          φ.continuous.comp Circle.exp.continuous⟩
        obtain ⟨a, ha⟩ := Circle.exp_surjective (f 0)
        obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 a ha
        let g : C(ℝ, Circle) := ⟨fun t => φ.symm (Circle.exp t),
          φ.symm.continuous.comp Circle.exp.continuous⟩
        have hg : Circle.exp 0 = g a := by
          change Circle.exp 0 = φ.symm (Circle.exp a)
          rw [ha]
          exact (φ.symm_apply_apply (Circle.exp 0)).symm
        obtain ⟨G, hG, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g a 0 hg
        have hFl (t : ℝ) : Circle.exp (F t) = φ (Circle.exp t) := congrFun hF.2 t
        have hGl (t : ℝ) : Circle.exp (G t) = φ.symm (Circle.exp t) := congrFun hG.2 t
        have hGF : (fun t => G (F t)) = id := by
          refine Circle.isCoveringMap_exp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id ?_ 0 ?_
          · funext t
            change Circle.exp (G (F t)) = Circle.exp t
            rw [hGl, hFl]
            exact φ.symm_apply_apply _
          · change G (F 0) = 0
            rw [hF.1, hG.1]
        have hFG : (fun t => F (G t)) = id := by
          refine Circle.isCoveringMap_exp.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id ?_ a ?_
          · funext t
            change Circle.exp (F (G t)) = Circle.exp t
            rw [hFl, hGl]
            exact φ.apply_symm_apply _
          · change F (G a) = a
            rw [hG.1, hF.1]
        let ψ : ℝ ≃ₜ ℝ :=
          { toFun := F
            invFun := G
            left_inv := fun t => congrFun hGF t
            right_inv := fun t => congrFun hFG t
            continuous_toFun := F.continuous
            continuous_invFun := G.continuous }
        exact ⟨ψ, fun t => congrFun hF.2 t⟩
    
      letI := a
      obtain ⟨path,T,φ,hT,hpath,hpathper,hparam,hunit⟩ := hgeo
      obtain ⟨ψ,hψ⟩ := actual_circle_homeomorphism_lift φ
      let τ (t : ℝ) := ψ (2*Real.pi*t/T)/(2*Real.pi)
      have hτcont : Continuous τ := by dsimp [τ];fun_prop
      let α : C(ℝ,H2) := ⟨fun t => ell (τ t),ell.continuous.comp hτcont⟩
      have hproj (t : ℝ) : p (α t)=path t := by
        change p (ell (τ t))=path t
        rw [hell,hparam]
        congr 1
        change Circle.exp (2*Real.pi*(ψ (2*Real.pi*t/T)/(2*Real.pi)))=φ (Circle.exp (2*Real.pi*t/T))
        rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi)≠0)]
        exact hψ _
      have hlocal (t : ℝ) : ∃ε : ℝ,0<ε ∧ ∀s u : ℝ,
          |s-t|<ε → |u-t|<ε → dist (α s) (α u)=|s-u| := by
        obtain ⟨ε₀,hε₀,h₀⟩ := hunit t
        obtain ⟨U,hU,hαU,hm⟩ := hmetric (α t)
        obtain ⟨ε₁,hε₁,hball⟩ := Metric.isOpen_iff.mp (hU.preimage α.continuous) t hαU
        refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,?_⟩
        intro s u hs hu
        have hsU : α s∈U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hs.trans_le (min_le_right _ _))
        have huU : α u∈U := hball (by simpa only [Metric.mem_ball,Real.dist_eq] using hu.trans_le (min_le_right _ _))
        rw [←hm (α s) hsU (α u) huU,hproj s,hproj u]
        exact h₀ s u (hs.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))
      have hτsurj : Function.Surjective τ := by
        intro u
        refine ⟨ψ.symm (u*(2*Real.pi))*T/(2*Real.pi),?_⟩
        dsimp [τ]
        have ht : 2*Real.pi*(ψ.symm (u*(2*Real.pi))*T/(2*Real.pi))/T=ψ.symm (u*(2*Real.pi)) := by
          field_simp [hT.ne',Real.pi_ne_zero]
        rw [ht,ψ.apply_symm_apply]
        field_simp [Real.pi_ne_zero]
      have himage : range α=range ell := by
        change range (ell ∘ τ)=range ell
        rw [range_comp,hτsurj.range_eq,image_univ]
      exact ⟨α,actual_h2_local_unit_geodesic_isometry α α.continuous hlocal,himage⟩
    have hFrontier {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
        (p : P → E) (U : Set E) (L : C(unitInterval×ℝ,P))
        (hinside : ∀s : unitInterval,∀t : ℝ,s<1 → p (L (s,t))∈U)
        (houtside : ∀t : ℝ,p (L (1,t))∉U) :
        (∀s : unitInterval,∀t : ℝ,s<1 →
          L (s,t)∈connectedComponentIn (p ⁻¹' U) (L (0,0))) ∧
        ∀t : ℝ,L (1,t)∈frontier (connectedComponentIn (p ⁻¹' U) (L (0,0))) := by
      let V : Set (unitInterval×ℝ) := Iio (1:unitInterval) ×ˢ univ
      have hVconn : IsPreconnected V := isPreconnected_Iio.prod isPreconnected_univ
      have hLVconn : IsPreconnected (L '' V) := hVconn.image L L.continuous.continuousOn
      have hzero : L (0,0)∈L '' V := ⟨(0,0),⟨by norm_num,mem_univ _⟩,rfl⟩
      have hLVsub : L '' V⊆p ⁻¹' U := by
        rintro _ ⟨⟨s,t⟩,hst,rfl⟩
        exact hinside s t hst.1
      have hCsub : L '' V⊆connectedComponentIn (p ⁻¹' U) (L (0,0)) :=
        hLVconn.subset_connectedComponentIn hzero hLVsub
      refine ⟨?_,?_⟩
      · intro s t hs
        exact hCsub ⟨(s,t),⟨hs,mem_univ _⟩,rfl⟩
      · intro t
        have hclV : (1,t)∈closure V := by
          change (1,t)∈closure (Iio (1:unitInterval) ×ˢ (univ:Set ℝ))
          rw [closure_prod_eq,closure_Iio' (show (Iio (1:unitInterval)).Nonempty from ⟨0,by norm_num⟩)]
          exact ⟨by simp,subset_closure (mem_univ _)⟩
        have hcl : L (1,t)∈closure (connectedComponentIn (p ⁻¹' U) (L (0,0))) :=
          (closure_mono hCsub) (image_closure_subset_closure_image L.continuous ⟨(1,t),hclV,rfl⟩)
        refine ⟨hcl,?_⟩
        intro hi
        exact houtside t ((connectedComponentIn_subset (p ⁻¹' U) (L (0,0))) (interior_subset hi))
    have hSame {E : Type} [TopologicalSpace E] (m : MetricSpace E)
        (f g : C(Circle,E)) (hf : IsEmbedding f) (hg : IsEmbedding g)
        (him : range f=range g) (hgeo : letI := m; IsParametrizedClosedGeodesic g) :
        letI := m; IsParametrizedClosedGeodesic f := by
      letI : MetricSpace E := m
      let k := hg.toHomeomorph.trans
        ((Homeomorph.setCongr him.symm).trans hf.toHomeomorph.symm)
      have hk (z : Circle) : f (k z)=g z := by
        have hpoint := hf.toHomeomorph.apply_symm_apply
          ((Homeomorph.setCongr him.symm) (hg.toHomeomorph z))
        exact congrArg Subtype.val hpoint
      obtain ⟨path,T,φ,hT,hcont,hperiod,hparam,hunit⟩ := hgeo
      refine ⟨path,T,φ.trans k,hT,hcont,hperiod,?_,hunit⟩
      intro t
      exact (hparam t).trans (hk _).symm
    have hFrontierBase {E P : Type} [TopologicalSpace E] [TopologicalSpace P] [LocallyConnectedSpace P]
        (p : P → E) (hp : Continuous p) (hpo : IsOpenMap p) (U : Set E) (hU : IsOpen U)
        (x : P) : frontier (connectedComponentIn (p ⁻¹' U) x) ⊆ p ⁻¹' frontier U := by
      let F := p ⁻¹' U
      have hF : IsOpen F := hU.preimage hp
      have hsub : frontier (connectedComponentIn F x)⊆frontier F := by
        by_cases hx : x∈F
        · let C := connectedComponentIn F x
          have hC : IsOpen C := hF.connectedComponentIn
          have hclosed : IsClosed (Subtype.val ⁻¹' C : Set F) := by
            have heq : (Subtype.val ⁻¹' C : Set F)=connectedComponent (⟨x,hx⟩ : F) := by
              dsimp only [C]
              rw [connectedComponentIn_eq_image hx,Set.preimage_image_eq _ Subtype.val_injective]
            rw [heq]
            exact isClosed_connectedComponent
          intro z hz
          change z∈frontier C at hz
          rw [frontier,hC.interior_eq] at hz
          have hznot : z∉F := by
            intro hzF
            have hm : (⟨z,hzF⟩ : F)∈closure (Subtype.val ⁻¹' C : Set F) := by
              rw [←hF.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val]
              exact hz.1
            rw [hclosed.closure_eq] at hm
            exact hz.2 hm
          rw [frontier,hF.interior_eq]
          exact ⟨closure_mono (connectedComponentIn_subset F x) hz.1,hznot⟩
        · rw [connectedComponentIn_eq_empty hx,frontier_empty]
          exact empty_subset _
      rw [hpo.preimage_frontier_eq_frontier_preimage hp U]
      exact hsub
    have hFamily {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
        (p : P → E) (D : Set E) (x : P)
        (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
        (N : C(Ioo (-1:ℝ) 1 × ℝ,P)) (hNp : ∀ r s,p (N (r,s))=e (r,Circle.exp s))
        (sgn : ℝ) (hsgn : sgn=1 ∨ sgn=-1)
        (hin : ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,e (⟨sgn*(r:ℝ),hr⟩,z)∈D)
        (hhalf : ∀ r : Ioo (0:ℝ) 1,∀ s,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,
          N (⟨sgn*(r:ℝ),hr⟩,s)∈connectedComponentIn (p ⁻¹' D) x)
        (hout : ∀ z,e (⟨0,by norm_num⟩,z)∉D) :
        ∃ F : C(unitInterval × Circle,E),∃ Q : C(unitInterval × ℝ,P),
          (∀ t : unitInterval,∀ z : Circle,∃ hr : sgn*((1/2)*(1-(t:ℝ)))∈Ioo (-1:ℝ) 1,
            F (t,z)=e (⟨sgn*((1/2)*(1-(t:ℝ))),hr⟩,z)) ∧
          (∀ z,F (1,z)=e (⟨0,by norm_num⟩,z)) ∧
          (∀ t : unitInterval,(t:ℝ)<1 → ∀ z,F (t,z)∈D) ∧
          (∀ t,IsEmbedding (fun z => F (t,z))) ∧
          (∀ t s,p (Q (t,s))=F (t,Circle.exp (2*Real.pi*s))) ∧
          (∀ t : unitInterval,(t:ℝ)<1 → ∀ s,Q (t,s)∈connectedComponentIn (p ⁻¹' D) x) ∧
          range (fun s => Q (1,s))=range (fun s => N (⟨0,by norm_num⟩,s)) ∧
          range (fun s => Q (1,s))⊆frontier (connectedComponentIn (p ⁻¹' D) x) := by
      have hFrontier {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
          (p : P → E) (U : Set E) (L : C(unitInterval×ℝ,P))
          (hinside : ∀s : unitInterval,∀t : ℝ,s<1 → p (L (s,t))∈U)
          (houtside : ∀t : ℝ,p (L (1,t))∉U) :
          (∀s : unitInterval,∀t : ℝ,s<1 →
            L (s,t)∈connectedComponentIn (p ⁻¹' U) (L (0,0))) ∧
          ∀t : ℝ,L (1,t)∈frontier (connectedComponentIn (p ⁻¹' U) (L (0,0))) := by
        let V : Set (unitInterval×ℝ) := Iio (1:unitInterval) ×ˢ univ
        have hVconn : IsPreconnected V := isPreconnected_Iio.prod isPreconnected_univ
        have hLVconn : IsPreconnected (L '' V) := hVconn.image L L.continuous.continuousOn
        have hzero : L (0,0)∈L '' V := ⟨(0,0),⟨by norm_num,mem_univ _⟩,rfl⟩
        have hLVsub : L '' V⊆p ⁻¹' U := by
          rintro _ ⟨⟨s,t⟩,hst,rfl⟩
          exact hinside s t hst.1
        have hCsub : L '' V⊆connectedComponentIn (p ⁻¹' U) (L (0,0)) :=
          hLVconn.subset_connectedComponentIn hzero hLVsub
        refine ⟨?_,?_⟩
        · intro s t hs
          exact hCsub ⟨(s,t),⟨hs,mem_univ _⟩,rfl⟩
        · intro t
          have hclV : (1,t)∈closure V := by
            change (1,t)∈closure (Iio (1:unitInterval) ×ˢ (univ:Set ℝ))
            rw [closure_prod_eq,closure_Iio' (show (Iio (1:unitInterval)).Nonempty from ⟨0,by norm_num⟩)]
            exact ⟨by simp,subset_closure (mem_univ _)⟩
          have hcl : L (1,t)∈closure (connectedComponentIn (p ⁻¹' U) (L (0,0))) :=
            (closure_mono hCsub) (image_closure_subset_closure_image L.continuous ⟨(1,t),hclV,rfl⟩)
          refine ⟨hcl,?_⟩
          intro hi
          exact houtside t ((connectedComponentIn_subset (p ⁻¹' U) (L (0,0))) (interior_subset hi))
      let R : unitInterval → Ioo (-1:ℝ) 1 := fun t => ⟨sgn*((1/2)*(1-(t:ℝ))),by
        rcases hsgn with rfl|rfl <;> constructor <;> nlinarith [t.property.1,t.property.2]⟩
      let F : C(unitInterval × Circle,E) := ⟨fun q => e (R q.1,q.2),by dsimp [R];fun_prop⟩
      let Q : C(unitInterval × ℝ,P) := ⟨fun q => N (R q.1,2*Real.pi*q.2),by dsimp [R];fun_prop⟩
      have hR1 : R 1=⟨0,by norm_num⟩ := by apply Subtype.ext;dsimp [R];simp
      have hFin : ∀ t : unitInterval,(t:ℝ)<1 → ∀ z,F (t,z)∈D := by
        intro t ht z
        have ha : (1/2:ℝ)*(1-(t:ℝ))∈Ioo (0:ℝ) 1 := by constructor <;> nlinarith [t.property.1]
        obtain ⟨hr,hh⟩ := hin ⟨_,ha⟩ z
        exact hh
      have hQin : ∀ t : unitInterval,(t:ℝ)<1 → ∀ s,Q (t,s)∈connectedComponentIn (p ⁻¹' D) x := by
        intro t ht s
        have ha : (1/2:ℝ)*(1-(t:ℝ))∈Ioo (0:ℝ) 1 := by constructor <;> nlinarith [t.property.1]
        obtain ⟨hr,hh⟩ := hhalf ⟨_,ha⟩ (2*Real.pi*s)
        exact hh
      have hQp : ∀ t s,p (Q (t,s))=F (t,Circle.exp (2*Real.pi*s)) := fun t s => hNp (R t) _
      have hF1 : ∀ z,F (1,z)=e (⟨0,by norm_num⟩,z) := by intro z;change e (R 1,z)=_;rw [hR1]
      have hQout : ∀ s,p (Q (1,s))∉D := by intro s;rw [hQp,hF1];exact hout _
      obtain ⟨hinner,hfront⟩ := hFrontier p D Q
        (fun t s ht => hQp t s ▸ hFin t ht _) hQout
      have hCeq : connectedComponentIn (p ⁻¹' D) (Q (0,0))=connectedComponentIn (p ⁻¹' D) x :=
        (connectedComponentIn_eq (hQin 0 (by norm_num) 0)).symm
      refine ⟨F,Q,fun t z => ⟨_,rfl⟩,hF1,hFin,?_,hQp,hQin,?_,?_⟩
      · intro t
        exact he.isEmbedding.comp (isEmbedding_prodMkRight (R t))
      · apply Subset.antisymm
        · rintro y ⟨s,rfl⟩
          refine ⟨2*Real.pi*s,?_⟩
          change N (⟨0,by norm_num⟩,_) = N (R 1,_)
          rw [hR1]
        · rintro y ⟨s,rfl⟩
          refine ⟨s/(2*Real.pi),?_⟩
          change N (R 1,2*Real.pi*(s/(2*Real.pi))) = _
          rw [hR1,mul_div_cancel₀ _ (by positivity : 2*Real.pi≠0)]
      · rintro y ⟨s,rfl⟩
        rw [←hCeq]
        exact hfront s
    letI := a
    letI : ClosedSurface E := M.genusTwo.2.1.some
    letI : LocallyPathConnectedSpace E := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
    letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
    let D := U\d.image
    let C := connectedComponentIn (p ⁻¹' D) x
    have hdclosed : IsClosed d.image := (isCompact_range d.embedded.continuous).isClosed
    have hDo : IsOpen D := hU.sdiff hdclosed
    have hDconn : IsConnected D := hSecond M c d hc U V hU hV hUV hcover hfrontU hfrontV hdnondiv hcd
    have hdess : Essential d := actual_simple_closed_geodesic_essential H d hdgeo
    obtain ⟨ec0,hec0,hc0⟩ := CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
      E 2 (by omega) M.genusTwo ⟨c,hc⟩
    obtain ⟨ec,hec,hcpoint,hecrange⟩ := hShrink ec0 hec0 d.imageᶜ hdclosed.isOpen_compl
      (fun z => (hc0 z).symm ▸ disjoint_left.mp hcd (mem_range_self z))
    have hcz (z : Circle) : ec (⟨0,by norm_num⟩,z)=c.map z := (hcpoint z).trans (hc0 z)
    obtain ⟨sgn,hsgn,hsgnU,hsgnV⟩ := hSigns c ec hec hcz U V hU hV hUV hcover hfrontU hfrontV
    obtain ⟨ed0,hed0,hd0⟩ := CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
      E 2 (by omega) M.genusTwo ⟨d,hdess⟩
    obtain ⟨ed,hed,hdpoint,hedrange⟩ := hShrink ed0 hed0 U hU
      (fun z => (hd0 z).symm ▸ hdU (mem_range_self z))
    have hdz (z : Circle) : ed (⟨0,by norm_num⟩,z)=d.map z := (hdpoint z).trans (hd0 z)
    have hcin : ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,ec (⟨sgn*(r:ℝ),hr⟩,z)∈D := by
      intro r z
      obtain ⟨hr,hu⟩ := hsgnU r z
      exact ⟨hr,hu,hecrange (mem_range_self _)⟩
    have hcoutsign : ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : -sgn*(r:ℝ)∈Ioo (-1:ℝ) 1,ec (⟨-sgn*(r:ℝ),hr⟩,z)∉D := by
      intro r z
      obtain ⟨hr,hv⟩ := hsgnV r z
      exact ⟨hr,fun hh => disjoint_left.mp hUV hh.1 hv⟩
    have hoffd (r : Ioo (-1:ℝ) 1) (hr : (r:ℝ)≠0) (z : Circle) : ed (r,z)∈D := by
      refine ⟨hedrange (mem_range_self _),?_⟩
      rintro ⟨w,hw⟩
      have hp := hed.injective ((hdz w).trans hw)
      exact hr (congrArg (fun q : Ioo (-1:ℝ) 1 × Circle => (q.1:ℝ)) hp).symm
    have hdinsign (τ : ℝ) (hτ : τ=1 ∨ τ=-1) :
        ∀ r : Ioo (0:ℝ) 1,∀ z,∃ hr : τ*(r:ℝ)∈Ioo (-1:ℝ) 1,ed (⟨τ*(r:ℝ),hr⟩,z)∈D := by
      intro r z
      have hr : τ*(r:ℝ)∈Ioo (-1:ℝ) 1 := by
        rcases hτ with rfl|rfl <;> constructor <;> nlinarith [r.property.1,r.property.2]
      refine ⟨hr,hoffd _ ?_ z⟩
      rcases hτ with rfl|rfl <;> nlinarith [r.property.1]
    have hcout (z : Circle) : ec (⟨0,by norm_num⟩,z)∉D := by
      rw [hcz]
      intro hh
      have hcU : U⊆c.imageᶜ := by rw [←hcover];exact subset_union_left
      exact hcU hh.1 (mem_range_self z)
    have hdout (z : Circle) : ed (⟨0,by norm_num⟩,z)∉D := by
      rw [hdz]
      exact fun hh => hh.2 (mem_range_self z)
    obtain ⟨Nc,hNcp,hNc⟩ := hBaseline p hq.isCoveringMap D hDo hDconn x hx ec hec sgn hsgn hcin
    obtain ⟨Nd0,hNd0p,hNd0⟩ := hBaseline p hq.isCoveringMap D hDo hDconn x hx ed hed (-1) (Or.inr rfl) (hdinsign (-1) (Or.inr rfl))
    obtain ⟨Nd1,hNd1p,hNd1⟩ := hBaseline p hq.isCoveringMap D hDo hDconn x hx ed hed 1 (Or.inl rfl) (hdinsign 1 (Or.inl rfl))
    obtain ⟨Fc,Lc,hFcdef,hFc1,hFcin,hFcemb,hLcp,hLcC,hLcrange,hLcfront⟩ :=
      hFamily p D x ec hec Nc hNcp sgn hsgn hcin hNc hcout
    obtain ⟨Fd0,Ld0,hFd0def,hFd01,hFd0in,hFd0emb,hLd0p,hLd0C,hLd0range,hLd0front⟩ :=
      hFamily p D x ed hed Nd0 hNd0p (-1) (Or.inr rfl) (hdinsign (-1) (Or.inr rfl)) hNd0 hdout
    obtain ⟨Fd1,Ld1,hFd1def,hFd11,hFd1in,hFd1emb,hLd1p,hLd1C,hLd1range,hLd1front⟩ :=
      hFamily p D x ed hed Nd1 hNd1p 1 (Or.inl rfl) (hdinsign 1 (Or.inl rfl)) hNd1 hdout
    have hfcterm (z : Circle) : Fc (1,z)=c.map z := (hFc1 z).trans (hcz z)
    have hfd0term (z : Circle) : Fd0 (1,z)=d.map z := (hFd01 z).trans (hdz z)
    have hfd1term (z : Circle) : Fd1 (1,z)=d.map z := (hFd11 z).trans (hdz z)
    letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
    let cf : C(Circle,E) := ⟨c.map,c.embedded.continuous⟩
    let df : C(Circle,E) := ⟨d.map,d.embedded.continuous⟩
    obtain ⟨cg,hcg,hcgg,hcggeo,hcgim⟩ := embedded_geodesic_image_has_parametrized_representative H c hcgeo
    obtain ⟨dg,hdg,hdgg,hdggeo,hdgim⟩ := embedded_geodesic_image_has_parametrized_representative H d hdgeo
    have hcparam : IsParametrizedClosedGeodesic cf := hSame (H.metric.replaceTopology H.compatible.symm) cf cg c.embedded hcg hcgim.symm hcggeo
    have hdparam : IsParametrizedClosedGeodesic df := hSame (H.metric.replaceTopology H.compatible.symm) df dg d.embedded hdg hdgim.symm hdggeo
    let lc : C(ℝ,H2) := ⟨fun s => Lc (1,s),Lc.continuous.comp (continuous_const.prodMk continuous_id)⟩
    let ld0 : C(ℝ,H2) := ⟨fun s => Ld0 (1,s),Ld0.continuous.comp (continuous_const.prodMk continuous_id)⟩
    let ld1 : C(ℝ,H2) := ⟨fun s => Ld1 (1,s),Ld1.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hlc (s : ℝ) : p (lc s)=cf (Circle.exp (2*Real.pi*s)) := (hLcp 1 s).trans (hfcterm _)
    have hld0 (s : ℝ) : p (ld0 s)=df (Circle.exp (2*Real.pi*s)) := (hLd0p 1 s).trans (hfd0term _)
    have hld1 (s : ℝ) : p (ld1 s)=df (Circle.exp (2*Real.pi*s)) := (hLd1p 1 s).trans (hfd1term _)
    obtain ⟨αc,hαc,hαcrange⟩ := hAxis a p hq hmetric cf c.embedded hcparam lc hlc
    obtain ⟨αd0,hαd0,hαd0range⟩ := hAxis a p hq hmetric df d.embedded hdparam ld0 hld0
    obtain ⟨αd1,hαd1,hαd1range⟩ := hAxis a p hq hmetric df d.embedded hdparam ld1 hld1
    have hrc : range αc=range (fun s => Nc (⟨0,by norm_num⟩,s)) := hαcrange.trans hLcrange
    have hrd0 : range αd0=range (fun s => Nd0 (⟨0,by norm_num⟩,s)) := hαd0range.trans hLd0range
    have hrd1 : range αd1=range (fun s => Nd1 (⟨0,by norm_num⟩,s)) := hαd1range.trans hLd1range
    have hαcfront : range αc⊆frontier C := hαcrange ▸ hLcfront
    have hαd0front : range αd0⊆frontier C := hαd0range ▸ hLd0front
    have hαd1front : range αd1⊆frontier C := hαd1range ▸ hLd1front
    have hImage (f : C(Circle,E)) (ell : C(ℝ,H2))
        (hell : ∀ s,p (ell s)=f (Circle.exp (2*Real.pi*s))) : p '' range ell=range f := by
      apply Subset.antisymm
      · rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
        exact ⟨Circle.exp (2*Real.pi*s),(hell s).symm⟩
      · rintro _ ⟨z,rfl⟩
        obtain ⟨s,hs⟩ := Circle.exp_surjective z
        refine ⟨ell (s/(2*Real.pi)),mem_range_self _,?_⟩
        rw [hell,mul_div_cancel₀ _ (by positivity : 2*Real.pi≠0),hs]
    have hcimage : p '' range αc=c.image := by rw [hαcrange];exact hImage cf lc hlc
    have hd0image : p '' range αd0=d.image := by rw [hαd0range];exact hImage df ld0 hld0
    have hd1image : p '' range αd1=d.image := by rw [hαd1range];exact hImage df ld1 hld1
    have hbasetrace (y : H2) (hy : y∈frontier C) : p y∈c.image ∨ p y∈d.image := by
      have hb : p y∈frontier D := hFrontierBase p hq.continuous hq.isCoveringMap.isOpenMap D hDo x hy
      by_cases hdy : p y∈d.image
      · exact Or.inr hdy
      · left
        have hcl : p y∈closure U := closure_mono sdiff_subset hb.1
        by_contra hcy
        have hyU : p y∈U := by
          by_contra hyU
          have hfr : p y∈frontier U := by rw [frontier,hU.interior_eq];exact ⟨hcl,hyU⟩
          rw [hfrontU] at hfr
          exact hcy hfr
        have hyD : p y∈D := ⟨hyU,hdy⟩
        exact hb.2 (hDo.interior_eq.symm ▸ hyD)
    have hneg0 : ∀ r : Ioo (-1:ℝ) 1,(r:ℝ)<0 → ∀ s,Nd0 (r,s)∈C := by
      intro r hr s
      obtain ⟨ht,hh⟩ := hNd0 ⟨-(r:ℝ),by constructor <;> linarith [r.property.1]⟩ s
      have heq : (⟨(-1:ℝ)* -(r:ℝ),ht⟩ : Ioo (-1:ℝ) 1)=r := by apply Subtype.ext;ring
      rwa [heq] at hh
    have hpos1 : ∀ r : Ioo (-1:ℝ) 1,0<(r:ℝ) → ∀ s,Nd1 (r,s)∈C := by
      intro r hr s
      obtain ⟨ht,hh⟩ := hNd1 ⟨(r:ℝ),hr,r.property.2⟩ s
      simpa only [one_mul] using hh
    have hcoverActual : ∀ y∈frontier C,∃ k : MulAction.stabilizer G C,
        y∈(fun z => k.val • z) '' range αc ∨
        y∈(fun z => k.val • z) '' range αd0 ∨ y∈(fun z => k.val • z) '' range αd1 := by
      intro y hy
      rcases hbasetrace y hy with hcy|hdy
      · obtain ⟨z,hz⟩ := hcy
        obtain ⟨k,hk⟩ := hCoverC a p hq D x hx ec hec hcout sgn hsgn hcin hcoutsign Nc hNcp hNc y hy
          ⟨z,hz.symm.trans (hcz z).symm⟩
        rw [←hrc] at hk
        exact ⟨k,Or.inl hk⟩
      · obtain ⟨z,hz⟩ := hdy
        obtain ⟨k,hk⟩ := hCoverD a p hq D x hx ed hed (fun z _ => hdout z) hoffd
          Nd0 Nd1 hNd0p hNd1p hneg0 hpos1 y hy ⟨z,hz.symm.trans (hdz z).symm⟩
        rw [←hrd0,←hrd1] at hk
        exact ⟨k,hk.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))⟩
    have hfrontEq := hUnion a p hq C (range αc) (range αd0) (range αd1) hαcfront hαd0front hαd1front hcoverActual
    refine ⟨αc,αd0,αd1,hαc,hαd0,hαd1,hαcfront,hαd0front,hαd1front,hcimage,hd0image,hd1image,hfrontEq,
      Fc,Fd0,Fd1,fun z => ⟨hfcterm z,hfd0term z,hfd1term z⟩,
      fun t ht z => ⟨hFcin t ht z,hFd0in t ht z,hFd1in t ht z⟩,
      fun t => ⟨hFcemb t,hFd0emb t,hFd1emb t⟩,ed,hed,hdz,(1/2),⟨by norm_num,by norm_num⟩,?_,?_,
      Lc,Ld0,Ld1,fun t s => ⟨hLcp t s,hLd0p t s,hLd1p t s⟩,
      fun t ht s => ⟨hLcC t ht s,hLd0C t ht s,hLd1C t ht s⟩,hαcrange.symm,hαd0range.symm,hαd1range.symm⟩
    · intro t z
      obtain ⟨hr,hh⟩ := hFd0def t z
      rw [hh]
      congr 2
      apply Subtype.ext
      ring
    · intro t z
      obtain ⟨hr,hh⟩ := hFd1def t z
      rw [hh]
      congr 2
      apply Subtype.ext
      ring
  )
end CurveComplex.Hyperbolic
