import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2LocalUnitGeodesicPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1EmbeddedTraversalComposablePROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualParametrizedClosedGeodesicG1GenusTwo
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasEmbeddedAxisSuppliedPrimitiveGeneratorReviewRequest
open Set Topology
open scoped Pointwise UpperHalfPlane MatrixGroups
namespace CurveComplex.Hyperbolic
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000
theorem actual_original_separating_c_side_primitive_boundary_monodromy_frontier_source {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) (c d : Curve E)
    (hc : Essential c) (hcgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic c.image)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : U∪V=c.imageᶜ) (hfrontU : frontier U=c.image)
    (hcd : Disjoint c.image d.image)
    (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
    (hmetric : ∀x : H2,∃W : Set H2,IsOpen W ∧ x∈W ∧
      ∀y∈W,∀z∈W,@dist E H.metric.toDist (p y) (p z)=dist y z) :
    ∃F : C(unitInterval×Circle,E),
      (∀z,F (1,z)=c.map z) ∧
      (∀t : unitInterval,t<1 → ∀z,F (t,z)∈U\d.image) ∧
      (∀t : unitInterval,IsEmbedding (fun z => F (t,z))) ∧
      ∀x : H2,∀hx : p x=F (0,1),
        let D := connectedComponentIn (p ⁻¹' (U\d.image)) x
        ∃δ : G,∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
          range α⊆frontier D ∧ p '' range α=c.image ∧
          (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
          (fun z => @SMul.smul G H2 a.toSMul δ z) '' D=D ∧
          ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
           (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
          (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
            ∃n : ℤ,g=δ^n) ∧
          ∀β : Path (F (0,1)) (F (0,1)),
            (∀t : unitInterval,β t=F (0,Circle.exp (2*Real.pi*(t:ℝ)))) →
            @SMul.smul G H2 a.toSMul δ x=
              (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
  have hCollar
      {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (M : HyperellipticModel E S) (c d : Curve E) (hc : Essential c)
      (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
      (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
      (hfrontU : frontier U = c.image)
      (hdcompact : IsCompact d.image) (hcd : Disjoint c.image d.image) :
      ∃ F : C(Interval × Circle, E),
        (∀ z : Circle, F (1, z) = c.map z) ∧
        (∀ t : Interval, (t : ℝ) < 1 → ∀ z : Circle,
          F (t, z) ∈ U \ d.image) ∧
        (∀ t : Interval, Topology.IsEmbedding (fun z : Circle => F (t, z))) := by
    classical
    letI : ClosedSurface E := M.genusTwo.2.1.some
    obtain ⟨e, he, hzero⟩ := CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
      E 2 (by omega) M.genusTwo ⟨c,hc⟩
    let o : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
    have hzero' (z : Circle) : e (o,z) = c.map z := hzero z
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
    have side (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
        (hw : ∃ a : P, ∃ z : Circle, e (⟨σ*(a:ℝ),by rcases hσ with rfl|rfl <;> constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U) :
        ∀ a : P, ∀ z : Circle,
          e (⟨σ*(a:ℝ),by rcases hσ with rfl|rfl <;> constructor <;> nlinarith [a.property.1,a.property.2]⟩,z) ∈ U := by
      let f : P × Circle → E := fun p => e (⟨σ*(p.1:ℝ),by
        rcases hσ with rfl|rfl <;> constructor <;> nlinarith [p.1.property.1,p.1.property.2]⟩,p.2)
      have hf : Continuous f := by dsimp [f];fun_prop
      have hp : IsPreconnected (range f) := by
        simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
      have hsub : range f ⊆ U ∪ V := by
        rintro _ ⟨⟨a,z⟩,rfl⟩
        apply hoff
        rcases hσ with rfl|rfl <;> nlinarith [a.property.1]
      have hmeet : (range f ∩ U).Nonempty := by
        obtain ⟨a,z,haz⟩ := hw
        exact ⟨f (a,z),⟨(a,z),rfl⟩,haz⟩
      have hleft := hp.subset_left_of_subset_union hU hV hUV hsub hmeet
      intro a z
      exact hleft ⟨(a,z),rfl⟩
    have hex : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ a : P, ∀ z : Circle,
          ∃ h : σ*(a:ℝ) ∈ Set.Ioo (-1:ℝ) 1, e (⟨σ*(a:ℝ),h⟩,z) ∈ U := by
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
    obtain ⟨σ,hσ,hside⟩ := hex
    have hopen : IsOpen (e ⁻¹' d.imageᶜ) := hdcompact.isClosed.isOpen_compl.preimage e.continuous
    have hcenter : ({o} ×ˢ (univ : Set Circle)) ⊆ e ⁻¹' d.imageᶜ := by
      rintro ⟨r,z⟩ ⟨hr,_⟩
      have hr' : r=o := hr
      subst r
      rw [mem_preimage,hzero']
      exact disjoint_left.mp hcd ⟨z,rfl⟩
    obtain ⟨A,B,hA,hB,hoA,hallB,hAB⟩ := generalized_tube_lemma
      isCompact_singleton (isCompact_univ : IsCompact (univ : Set Circle)) hopen hcenter
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hoA (mem_singleton o)))
    let δ : ℝ := min (ε/2) (1/2)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let R : Interval → Set.Ioo (-1:ℝ) 1 := fun t => ⟨σ*(δ*(1-(t:ℝ))),by
      have ht0 := t.property.1
      have ht1 := t.property.2
      rcases hσ with rfl|rfl <;> constructor <;> nlinarith⟩
    let F : C(Interval × Circle,E) := ⟨fun p => e (R p.1,p.2),by dsimp [R];fun_prop⟩
    refine ⟨F,?_,?_,?_⟩
    · intro z
      change e (R 1,z) = c.map z
      have hR : R 1=o := by apply Subtype.ext;dsimp [R,o];simp
      rw [hR,hzero']
    · intro t ht z
      have ha : δ*(1-(t:ℝ)) ∈ P := by
        constructor <;> nlinarith [t.property.1,t.property.2]
      obtain ⟨h,hU'⟩ := hside ⟨_,ha⟩ z
      refine ⟨hU',?_⟩
      apply hAB
      refine ⟨hball ?_,hallB (mem_univ z)⟩
      change dist (R t) o < ε
      change |σ*(δ*(1-(t:ℝ)))-0| < ε
      rcases hσ with rfl|rfl
      · rw [one_mul,sub_zero,abs_of_nonneg (by nlinarith [t.property.2])]
        nlinarith [t.property.1]
      · rw [neg_one_mul,sub_zero,abs_neg,abs_of_nonneg (by nlinarith [t.property.2])]
        nlinarith [t.property.1]
    · intro t
      exact he.isEmbedding.comp (isEmbedding_prodMkRight (R t))
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
  have hCut {E G : Type} [MetricSpace E] [Group G]
      (a : MulAction G H2) (p : H2 → E)
      (hq : letI := a;IsQuotientCoveringMap p G)
      (hmetric : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
        ∀y∈V,∀z∈V,dist (p y) (p z)=dist y z)
      (U : Set E) (H : C(Circle×unitInterval,E))
      (hinside : ∀s : unitInterval,s<1 → ∀z : Circle,H (z,s)∈U)
      (houtside : ∀z : Circle,H (z,1)∉U)
      (hgeo : IsParametrizedClosedGeodesic
        (⟨fun z => H (z,1),H.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(Circle,E)))
      (hemb : IsEmbedding (fun z : Circle => H (z,1)))
      (x : H2) (hx : p x=H (1,0)) :
      let C := connectedComponentIn (p ⁻¹' U) x
      ∃δ : G,∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
        range α⊆frontier C ∧
        p '' range α=range (fun z : Circle => H (z,1)) ∧
        (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
        (fun z => @SMul.smul G H2 a.toSMul δ z) '' C=C ∧
        ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
         (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
        ∀β : Path (H (1,0)) (H (1,0)),
          (∀t : unitInterval,β t=H (Circle.exp (2*Real.pi*(t:ℝ)),0)) →
          @SMul.smul G H2 a.toSMul δ x=
            (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
    have hClock {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (f g : C(Circle,E)) (H : C(Circle×unitInterval,E))
        (hH0 : ∀ z : Circle,H (z,0)=f z) (hH1 : ∀ z : Circle,H (z,1)=g z)
        (x : P) (hx : p x=f 1) :
        ∃ L : C(unitInterval×ℝ,P),∃ δ : G,
          L (0,0)=x ∧
          (∀s : unitInterval,∀t : ℝ,p (L (s,t))=H (Circle.exp (2*Real.pi*t),s)) ∧
          (∀ t : ℝ,p (L (0,t))=f (Circle.exp (2*Real.pi*t))) ∧
          (∀ t : ℝ,p (L (1,t))=g (Circle.exp (2*Real.pi*t))) ∧
          (∀ s : unitInterval,∀ t : ℝ,
            @SMul.smul G P a.toSMul δ (L (s,t))=L (s,t+1)) ∧
          ∀ β : Path (f 1) (f 1),
            (∀ t : unitInterval,β t=f (Circle.exp (2*Real.pi*(t:ℝ)))) →
            @SMul.smul G P a.toSMul δ x=
              (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
      have hPeriodic {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
          (a : MulAction G P) (p : P → E)
          (hq : letI := a; IsQuotientCoveringMap p G)
          (α : ℝ → P) (hα : Continuous α) (T : ℝ)
          (hperiod : ∀ t : ℝ,p (α (t+T))=p (α t)) :
          ∃ δ : G,
            (∀ t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) ∧
            (letI := a;δ∈MulAction.stabilizer G (range α)) ∧
            ∀ β : Path (p (α 0)) (p (α 0)),
              (∀ t : unitInterval,β t=p (α ((t:ℝ)*T))) →
              @SMul.smul G P a.toSMul δ (α 0)=
                (hq.isCoveringMap.monodromy ⟦β⟧ ⟨α 0,rfl⟩).val := by
        letI := a
        have hend : p (α T)=p (α 0) := by simpa using hperiod 0
        obtain ⟨δ,hδ⟩ := hq.apply_eq_iff_mem_orbit.mp hend
        have hshift : ∀ t : ℝ,δ • α t=α (t+T) := by
          have heq : (fun t : ℝ => δ • α t)=(fun t : ℝ => α (t+T)) :=
            hq.isCoveringMap.eq_of_comp_eq
              ((hq.continuous_const_smul δ).comp hα)
              (hα.comp (continuous_id.add continuous_const))
              (by funext t;exact (hq.map_smul δ).trans (hperiod t).symm)
              0 (by simpa using hδ)
          exact congrFun heq
        refine ⟨δ,hshift,?_,?_⟩
        · apply MulAction.mem_stabilizer_iff.mpr
          change (fun z : P => δ • z) '' range α=range α
          apply Subset.antisymm
          · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
            exact ⟨t+T,(hshift t).symm⟩
          · rintro _ ⟨t,rfl⟩
            refine ⟨α (t-T),mem_range_self _,?_⟩
            change δ • α (t-T)=α t
            rw [hshift,sub_add_cancel]
        · intro β hβ
          have heq : (fun t : unitInterval => α ((t:ℝ)*T))=
              hq.isCoveringMap.liftPath β (α 0) β.source := by
            apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
            refine ⟨hα.comp (continuous_subtype_val.mul continuous_const),?_,?_⟩
            · funext t;exact (hβ t).symm
            · simp
          change δ • α 0=hq.isCoveringMap.liftPath β (α 0) β.source 1
          rw [←heq,hshift]
          simp
      have hHomotopy {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
          (a : MulAction G P) (p : P → E)
          (hq : letI := a;IsQuotientCoveringMap p G)
          (F : C(unitInterval×ℝ,E)) (T : ℝ)
          (hperiod : ∀ s : unitInterval,∀ t : ℝ,F (s,t+T)=F (s,t))
          (α : C(ℝ,P)) (hzero : ∀ t : ℝ,F (0,t)=p (α t))
          (δ : G)
          (hδ : ∀ t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
          ∃ L : C(unitInterval×ℝ,P),
            (∀ s t,p (L (s,t))=F (s,t)) ∧
            (∀ t,L (0,t)=α t) ∧
            (∀ s t,@SMul.smul G P a.toSMul δ (L (s,t))=L (s,t+T)) := by
        letI := a
        let L := hq.isCoveringMap.liftHomotopy F α hzero
        have hlift (s : unitInterval) (t : ℝ) : p (L (s,t))=F (s,t) :=
          congrFun (hq.isCoveringMap.liftHomotopy_lifts F α hzero) (s,t)
        have hstart (t : ℝ) : L (0,t)=α t :=
          hq.isCoveringMap.liftHomotopy_zero F α hzero t
        refine ⟨L,hlift,hstart,?_⟩
        have he : (fun x : unitInterval×ℝ => δ • L x)=
            (fun x : unitInterval×ℝ => L (x.1,x.2+T)) := by
          exact hq.isCoveringMap.eq_of_comp_eq
            ((hq.continuous_const_smul δ).comp L.continuous)
            (L.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))
            (by
              funext x
              exact (hq.map_smul δ).trans ((hlift x.1 x.2).trans
                ((hperiod x.1 x.2).symm.trans (hlift x.1 (x.2+T)).symm)))
            (0,0) (by
              change δ • L (0,0)=L (0,0+T)
              rw [hstart,hstart]
              exact hδ 0)
        intro s t
        exact congrFun he (s,t)
      letI := a
      let γ : C(ℝ,E) := ⟨fun t => f (Circle.exp (2*Real.pi*t)),by fun_prop⟩
      have hγ0 : γ 0=p x := by simp [γ,hx]
      obtain ⟨α,⟨hα0,hαproj⟩,_⟩ := hq.isCoveringMap.existsUnique_continuousMap_lifts γ 0 x hγ0.symm
      have hproj (t : ℝ) : p (α t)=f (Circle.exp (2*Real.pi*t)) := congrFun hαproj t
      have hclock (t : ℝ) : Circle.exp (2*Real.pi*(t+1))=Circle.exp (2*Real.pi*t) := by
        rw [mul_add,mul_one,Circle.exp_add_two_pi]
      have hper : ∀t : ℝ,p (α (t+1))=p (α t) := by intro t;rw [hproj,hproj,hclock]
      obtain ⟨δ,hδ,hstab,hmono⟩ := hPeriodic a p hq α α.continuous 1 hper
      let F : C(unitInterval×ℝ,E) := ⟨fun st => H (Circle.exp (2*Real.pi*st.2),st.1),by fun_prop⟩
      have hFper : ∀s : unitInterval,∀t : ℝ,F (s,t+1)=F (s,t) := by
        intro s t
        change H (Circle.exp (2*Real.pi*(t+1)),s)=H (Circle.exp (2*Real.pi*t),s)
        rw [hclock]
      have hF0 : ∀t : ℝ,F (0,t)=p (α t) := by
        intro t
        exact (hH0 _).trans (hproj t).symm
      obtain ⟨L,hLp,hL0,hLeq⟩ := hHomotopy a p hq F 1 hFper α hF0 δ hδ
      refine ⟨L,δ,(hL0 0).trans hα0,hLp,?_,?_,hLeq,?_⟩
      · intro t;rw [hLp];exact hH0 _
      · intro t;rw [hLp];exact hH1 _
      · intro β hβ
        have heq : (fun t : unitInterval => α (t:ℝ))=
            hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) := by
          apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
          refine ⟨α.continuous.comp continuous_subtype_val,?_,?_⟩
          · funext t;exact (hproj (t:ℝ)).trans (hβ t).symm
          · exact hα0
        change δ • x=hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) 1
        rw [←heq,←hα0]
        change @SMul.smul G P a.toSMul δ (α 0)=α 1
        simpa using hδ 0
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
    have hAxis {E G : Type} [MetricSpace E] [Group G]
        (a : MulAction G H2) (p : H2 → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (hmetric : ∀x : H2,∃U : Set H2,IsOpen U ∧ x∈U ∧
          ∀y∈U,∀z∈U,dist (p y) (p z)=dist y z)
        (g : C(Circle,E)) (hg : IsEmbedding g) (hgeo : IsParametrizedClosedGeodesic g)
        (ell : C(ℝ,H2)) (hell : ∀t : ℝ,p (ell t)=g (Circle.exp (2*Real.pi*t)))
        (δ : G) (hδ : ∀t : ℝ,@SMul.smul G H2 a.toSMul δ (ell t)=ell (t+1)) :
        ∃ α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧ range α=range ell ∧
          (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
          ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
           (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) := by
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
    
      have circle_lift_integer_drift (φ : Circle ≃ₜ Circle) (ψ : ℝ ≃ₜ ℝ)
          (hψ : ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t)) :
          ∃ n : ℤ, ∀ t : ℝ, ψ (t+2*Real.pi) = ψ t + (n:ℝ)*(2*Real.pi) := by
        have hbase : Circle.exp (ψ (2*Real.pi)) = Circle.exp (ψ 0) := by
          rw [hψ,hψ,Circle.exp_two_pi,Circle.exp_zero]
        obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hbase
        refine ⟨n,?_⟩
        have heq : (fun t : ℝ => ψ (t+2*Real.pi)) =
            (fun t : ℝ => ψ t+(n:ℝ)*(2*Real.pi)) := by
          refine Circle.isCoveringMap_exp.eq_of_comp_eq
            (ψ.continuous.comp (continuous_id.add continuous_const))
            (ψ.continuous.add continuous_const) ?_ 0 ?_
          · funext t
            change Circle.exp (ψ (t+2*Real.pi)) = Circle.exp (ψ t+(n:ℝ)*(2*Real.pi))
            rw [hψ,Circle.exp_add_two_pi,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one,hψ]
          · simpa only [zero_add] using hn
        exact fun t => congrFun heq t
    
      have actual_circle_lift_unit_degree (φ : Circle ≃ₜ Circle) (ψ : ℝ ≃ₜ ℝ)
          (hψ : ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t)) :
          ∃ n : ℤ, (n = 1 ∨ n = -1) ∧
            ∀ t : ℝ, ψ (t+2*Real.pi) = ψ t+(n:ℝ)*(2*Real.pi) := by
        obtain ⟨n,hn⟩ := circle_lift_integer_drift φ ψ hψ
        have hinverse (t : ℝ) : Circle.exp (ψ.symm t) = φ.symm (Circle.exp t) := by
          have h := congrArg φ.symm (hψ (ψ.symm t))
          simpa only [ψ.apply_symm_apply,φ.symm_apply_apply] using h.symm
        obtain ⟨m,hm⟩ := circle_lift_integer_drift φ.symm ψ.symm hinverse
        let error (t : ℝ) := ψ t-(n:ℝ)*t
        have hperiodic : Function.Periodic error (2*Real.pi) := by
          intro t
          dsimp [error]
          rw [hn]
          ring
        have hshift := hperiodic.zsmul m (ψ.symm 0)
        have hshift' : ψ (ψ.symm 0+(m:ℝ)*(2*Real.pi)) =
            ψ (ψ.symm 0)+(n:ℝ)*(m:ℝ)*(2*Real.pi) := by
          dsimp [error] at hshift
          simp only [zsmul_eq_mul] at hshift
          linarith
        have hone : (n:ℝ)*(m:ℝ) = 1 := by
          rw [← hm 0,ψ.apply_symm_apply,ψ.apply_symm_apply] at hshift'
          have hp := Real.pi_pos
          nlinarith
        have hint : n*m=1 := by exact_mod_cast hone
        have hnunit : n=1 ∨ n= -1 := by
          rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hint with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
        exact ⟨n,hnunit,hn⟩
      letI := a
      obtain ⟨path,T,φ,hT,hpath,hpathper,hparam,hunit⟩ := hgeo
      obtain ⟨ψ,hψ⟩ := actual_circle_homeomorphism_lift φ
      obtain ⟨n,hn,hdrift⟩ := actual_circle_lift_unit_degree φ ψ hψ
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
      have hτdrift (t : ℝ) : τ (t+T)=τ t+(n:ℝ) := by
        dsimp [τ]
        have ht : 2*Real.pi*(t+T)/T=2*Real.pi*t/T+2*Real.pi := by field_simp [hT.ne']
        rw [ht,hdrift]
        field_simp [Real.pi_ne_zero]
      refine ⟨α,actual_h2_local_unit_geodesic_isometry α α.continuous hlocal,T,hT,himage,?_,?_⟩
      · intro s t
        rw [hproj s,hproj t,hparam s,hparam t,hg.injective.eq_iff,φ.injective.eq_iff,Circle.exp_eq_exp]
        constructor
        · rintro ⟨k,hk⟩
          refine ⟨k,?_⟩
          have h := congrArg (fun x : ℝ => x*T/(2*Real.pi)) hk
          field_simp [hT.ne',Real.pi_ne_zero] at h
          simpa [mul_comm] using h
        · rintro ⟨k,rfl⟩
          refine ⟨k,?_⟩
          field_simp [hT.ne',Real.pi_ne_zero]
      · rcases hn with hn | hn
        · left
          intro t
          change @SMul.smul G H2 a.toSMul δ (ell (τ t))=ell (τ (t+T))
          rw [hδ,hτdrift,hn]
          simp
        · right
          intro t
          have hi (u : ℝ) : @SMul.smul G H2 a.toSMul δ⁻¹ (ell u)=ell (u-1) := by
            have hh := congrArg (fun z => @SMul.smul G H2 a.toSMul δ⁻¹ z) (hδ (u-1))
            rw [sub_add_cancel] at hh
            exact hh.symm.trans (@inv_smul_smul G H2 _ a δ (ell (u-1)))
          change @SMul.smul G H2 a.toSMul δ⁻¹ (ell (τ t))=ell (τ (t+T))
          rw [hi,hτdrift,hn]
          simp [sub_eq_add_neg]
    letI := a
    let C := connectedComponentIn (p ⁻¹' U) x
    let f : C(Circle,E) := ⟨fun z => H (z,0),H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    let g : C(Circle,E) := ⟨fun z => H (z,1),H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    obtain ⟨L,δ,hLzero,hLproj,hLf,hLg,hLeq,hmono⟩ :=
      hClock a p hq f g H (fun z => rfl) (fun z => rfl) x hx
    have hLin : ∀s : unitInterval,∀t : ℝ,s<1 → p (L (s,t))∈U := by
      intro s t hs;rw [hLproj];exact hinside s hs _
    have hLout : ∀t : ℝ,p (L (1,t))∉U := by
      intro t;rw [hLproj];exact houtside _
    obtain ⟨hLC,hLfront⟩ := hFrontier p U L hLin hLout
    rw [hLzero] at hLC hLfront
    let ell : C(ℝ,H2) := ⟨fun t => L (1,t),L.continuous.comp (continuous_const.prodMk continuous_id)⟩
    obtain ⟨α,hα,T,hT,him,hfibre,hshift⟩ := hAxis a p hq hmetric g hemb hgeo ell hLg δ (hLeq 1)
    have hxF : x∈p ⁻¹' U := by change p x∈U;rw [hx];exact hinside 0 (by norm_num) 1
    have hδx : @SMul.smul G H2 a.toSMul δ x∈C := by
      rw [←hLzero,hLeq]
      simpa only [zero_add] using hLC 0 1 (by norm_num)
    let eδ : H2 ≃ₜ H2 :=
      { toFun := fun z => @SMul.smul G H2 a.toSMul δ z
        invFun := fun z => @SMul.smul G H2 a.toSMul δ⁻¹ z
        left_inv := @inv_smul_smul G H2 _ a δ
        right_inv := @smul_inv_smul G H2 _ a δ
        continuous_toFun := hq.continuous_const_smul δ
        continuous_invFun := hq.continuous_const_smul δ⁻¹ }
    have hfix (g : G) (z : H2) : p (@SMul.smul G H2 a.toSMul g z)=p z :=
      @IsQuotientCoveringMap.map_smul H2 E _ _ p G _ a hq g z
    have hpreimage : eδ '' (p ⁻¹' U)=p ⁻¹' U := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        change p (@SMul.smul G H2 a.toSMul δ w)∈U
        rw [hfix]
        exact hw
      · intro hz
        refine ⟨@SMul.smul G H2 a.toSMul δ⁻¹ z,?_,@smul_inv_smul G H2 _ a δ z⟩
        change p (@SMul.smul G H2 a.toSMul δ⁻¹ z)∈U
        rw [hfix]
        exact hz
    have hpreserve : (fun z => @SMul.smul G H2 a.toSMul δ z) '' C=C := by
      have he := eδ.image_connectedComponentIn hxF
      rw [hpreimage] at he
      exact he.trans (connectedComponentIn_eq hδx).symm
    refine ⟨δ,α,hα,T,hT,?_,?_,hfibre,hpreserve,hshift,hmono⟩
    · rw [him]
      rintro _ ⟨t,rfl⟩
      exact hLfront t
    · rw [him]
      ext y
      constructor
      · rintro ⟨_,⟨t,rfl⟩,rfl⟩
        exact ⟨Circle.exp (2*Real.pi*t),(hLg t).symm⟩
      · rintro ⟨z,rfl⟩
        obtain ⟨θ,hθ⟩ := Circle.exp_surjective z
        refine ⟨ell (θ/(2*Real.pi)),mem_range_self _,?_⟩
        have hc : Circle.exp (2*Real.pi*(θ/(2*Real.pi)))=z := by
          rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi)≠0)]
          exact hθ
        change p (L (1,θ/(2*Real.pi)))=H (z,1)
        rw [hLg,hc]
        rfl
  have hPrimitive {E G : Type} [MetricSpace E] [Group G]
      (a : MulAction G H2) (p : H2 → E)
      (hq : letI := a;IsQuotientCoveringMap p G)
      (hmetric : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
        ∀y∈V,∀z∈V,dist (p y) (p z)=dist y z)
      (α : ℝ → H2) (hα : Isometry α) (T : ℝ) (hT : 0<T)
      (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T)
      (δ : G) (hδ : ∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) :
      ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
        ∃n : ℤ,g=δ^n := by
    have hPeriod {E P G : Type} [MetricSpace E] [TopologicalSpace P] [PreconnectedSpace P]
        [Group G] (a : MulAction G P) (p : P → E)
        (hq : letI := a; IsQuotientCoveringMap p G)
        (eP : P ≃ₜ H2)
        (hmetric : ∀x : P, ∃U : Set P, IsOpen U ∧ x∈U ∧
          ∀y∈U,∀z∈U,dist (p y) (p z)=dist (eP y) (eP z))
        (δ : G) (period : ℝ) (hperiod : 0<period)
        (hδ : ∀t : ℝ,eP (@SMul.smul G P a.toSMul δ (eP.symm (verticalPath t)))=
          verticalPath (t+period)) :
        letI := a
        let α : ℝ → P := fun t => eP.symm (verticalPath t)
        let K := MulAction.stabilizer G (range (fun t : ℝ => eP.symm (verticalPath t)))
        ∃ σ : Additive K →+ ℝ,Function.Injective σ ∧
          (∀η : K,∀t : ℝ,eP (@SMul.smul G P a.toSMul η.val (α t))=
            verticalPath (t+σ (Additive.ofMul η))) ∧
          ∃ℓ : ℝ,0<ℓ ∧ ∃η : K,σ (Additive.ofMul η)=ℓ ∧
            σ.range=AddSubgroup.zmultiples ℓ := by
      have hEquiv {P E G : Type} [TopologicalSpace P] [TopologicalSpace E]
        [PreconnectedSpace P] [Group G] (a : MulAction G P) (p : P → E)
        (hq : letI := a; IsQuotientCoveringMap p G) (x : P) :
        ∃ e : G ≃* deck p, ∀ g : G, ∀ z : P,
          e g • z = @SMul.smul G P a.toSMul g z := by
        letI := a
        let h (g : G) : P ≃ₜ P :=
          { toFun := fun z => g • z
            invFun := fun z => g⁻¹ • z
            left_inv := inv_smul_smul g
            right_inv := smul_inv_smul g
            continuous_toFun := hq.continuous_const_smul g
            continuous_invFun := hq.continuous_const_smul g⁻¹ }
        let φ : G →* deck p :=
          { toFun := fun g => ⟨h g,by funext z;exact hq.map_smul g⟩
            map_one' := by apply Subtype.ext;ext z;exact one_smul G z
            map_mul' := by intro g k;apply Subtype.ext;ext z;exact mul_smul g k z }
        have hi : Function.Injective φ := by
          intro g k he
          letI := hq.isCancelSMul
          have hx : g • x=k • x := congrArg (fun d : deck p => d • x) he
          exact IsCancelSMul.right_cancel g k x hx
        have hs : Function.Surjective φ := by
          intro δ
          obtain ⟨g,hg⟩ := hq.apply_eq_iff_mem_orbit.mp (deck.proj_smul δ x)
          refine ⟨g,?_⟩
          apply Subtype.ext
          apply Homeomorph.ext
          have he : (h g : P → P)=(δ.val : P → P) :=
            hq.isCoveringMap.eq_of_comp_eq (h g).continuous δ.val.continuous
              (by funext z;exact (hq.map_smul g).trans (deck.proj_smul δ z).symm) x hg
          exact congrFun he
        exact ⟨MulEquiv.ofBijective φ ⟨hi,hs⟩,fun g z => rfl⟩
      have hDeckCover {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (e : G ≃* deck p)
        (he : ∀ g z,e g • z=@SMul.smul G P a.toSMul g z) :
        IsQuotientCoveringMap p (deck p) := by
        letI := a
        refine { toIsQuotientMap := hq.toIsQuotientMap
                 continuous_const_smul := fun δ => δ.val.continuous
                 apply_eq_iff_mem_orbit := ?_
                 disjoint := ?_ }
        · intro x y
          constructor
          · intro hxy
            obtain ⟨g,hg⟩ := hq.apply_eq_iff_mem_orbit.mp hxy
            exact ⟨e g,(he g y).trans hg⟩
          · rintro ⟨δ,hδ⟩
            rw [←hδ]
            exact deck.proj_smul δ y
        · intro x
          obtain ⟨V,hV,hdis⟩ := hq.disjoint x
          refine ⟨V,hV,?_⟩
          intro δ hmeet
          have hmeetG : ((e.symm δ) • V ∩ V).Nonempty := by
            have hf : (fun z : P => δ • z)=(fun z : P => e.symm δ • z) := by
              funext z
              have ht := he (e.symm δ) z
              rw [e.apply_symm_apply] at ht
              exact ht
            change ((fun z => δ • z) '' V ∩ V).Nonempty at hmeet
            change ((fun z => e.symm δ • z) '' V ∩ V).Nonempty
            rwa [←hf]
          have hδ : e.symm δ=1 := hdis _ hmeetG
          have ht := congrArg e hδ
          simpa using ht
      have hStabilizer {P E G : Type} [TopologicalSpace P] [Group G]
        (a : MulAction G P) (p : P → E) (e : G ≃* deck p)
        (he : ∀ g z, e g • z=@SMul.smul G P a.toSMul g z) (S : Set P) :
        letI := a
        ∃ k : MulAction.stabilizer G S ≃* MulAction.stabilizer (deck p) S,
          ∀ g, e g.val=(k g).val := by
        letI := a
        let K := MulAction.stabilizer G S
        let D := MulAction.stabilizer (deck p) S
        have hm (g : G) : e g∈D ↔ g∈K := by
          rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
          change ((fun z => e g • z) '' S=S) ↔ ((fun z => g • z) '' S=S)
          have hf : (fun z => e g • z)=(fun z => g • z) := funext (he g)
          rw [hf]
        let k : K ≃* D :=
          { toFun := fun g => ⟨e g.val,(hm g.val).mpr g.property⟩
            invFun := fun g => ⟨e.symm g.val,(hm (e.symm g.val)).mp (by simpa using g.property)⟩
            left_inv := by intro g;apply Subtype.ext;exact e.symm_apply_apply g.val
            right_inv := by intro g;apply Subtype.ext;exact e.apply_symm_apply g.val
            map_mul' := by intro g h;apply Subtype.ext;exact e.map_mul g.val h.val }
        exact ⟨k,fun g => rfl⟩
      have hPeriodTransport {K D : Type} [Group K] [Group D] (k : K ≃* D)
        (ρ : Additive D →+ ℝ) (hρ : Function.Injective ρ)
        (ℓ : ℝ) (hℓ : 0<ℓ) (η : D) (hη : ρ (Additive.ofMul η)=ℓ)
        (hrange : ρ.range=AddSubgroup.zmultiples ℓ) :
        ∃ σ : Additive K →+ ℝ, Function.Injective σ ∧
          (∀ g, σ (Additive.ofMul g)=ρ (Additive.ofMul (k g))) ∧
          σ (Additive.ofMul (k.symm η))=ℓ ∧
          σ.range=AddSubgroup.zmultiples ℓ := by
        let σ : Additive K →+ ℝ := ρ.comp k.toMonoidHom.toAdditive
        have hs : Function.Injective σ := by
          intro x y h
          have hxy : Additive.ofMul (k x.toMul)=Additive.ofMul (k y.toMul) := hρ h
          have hmul : k x.toMul=k y.toMul := congrArg Additive.toMul hxy
          exact congrArg Additive.ofMul (k.injective hmul)
        refine ⟨σ,hs,fun g => rfl,?_,?_⟩
        · change ρ (Additive.ofMul (k (k.symm η)))=ℓ
          rwa [k.apply_symm_apply]
        · rw [←hrange]
          ext r
          constructor
          · rintro ⟨g,hg⟩
            exact ⟨Additive.ofMul (k g.toMul),hg⟩
          · rintro ⟨g,hg⟩
            refine ⟨Additive.ofMul (k.symm g.toMul),?_⟩
            change ρ (Additive.ofMul (k (k.symm g.toMul)))=r
            simpa using hg
      letI := a
      obtain ⟨e,he⟩ := hEquiv a p hq (eP.symm UpperHalfPlane.I)
      have hqd : IsQuotientCoveringMap p (deck p) := hDeckCover a p hq e he
      have hδd : ∀t : ℝ,eP (e δ • eP.symm (verticalPath t))=verticalPath (t+period) := by
        intro t
        rw [he]
        exact hδ t
      obtain ⟨ρ,hρ,htranslate,ℓ,hℓ,η,hη,hrange⟩ :=
        actual_canonical_deck_axis_minimal_period p hqd eP hmetric (e δ) period hperiod hδd
      obtain ⟨k,hk⟩ := hStabilizer a p e he (range (fun t => eP.symm (verticalPath t)))
      obtain ⟨σ,hσ,hvalues,hprimitive,hrangeσ⟩ := hPeriodTransport k ρ hρ ℓ hℓ η hη hrange
      refine ⟨σ,hσ,?_,ℓ,hℓ,k.symm η,hprimitive,hrangeσ⟩
      intro g t
      have ht := htranslate (k g) t
      rw [←hk g,he] at ht
      rw [hvalues]
      exact ht
    letI := a
    have hdist : dist (α 0) (α 1)=1 := by simpa using hα.dist_eq 0 1
    obtain ⟨e,he0,he1⟩ := exists_ordered_pair_isometry (α 0) (α 1) hdist
    have hzero : verticalPath 0=UpperHalfPlane.I := by
      apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
    have hα0 : e.symm (α 0)=verticalPath 0 := by rw [←he0,e.symm_apply_apply,hzero]
    have hα1 : e.symm (α 1)=verticalPath 1 := by rw [←he1,e.symm_apply_apply]
    have hnorm := isometry_eq_vertical_of_values (fun t => e.symm (α t))
      (e.symm.isometry.comp hα) hα0 hα1
    let eP : H2 ≃ₜ H2 := e.symm.toHomeomorph
    have hn (t : ℝ) : eP (α t)=verticalPath t := hnorm t
    have ha (t : ℝ) : eP.symm (verticalPath t)=α t := by
      apply eP.injective
      rw [eP.apply_symm_apply,hn]
    have hm : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
        ∀y∈V,∀z∈V,dist (p y) (p z)=dist (eP y) (eP z) := by
      intro x
      obtain ⟨V,hV,hx,h⟩ := hmetric x
      exact ⟨V,hV,hx,fun y hy z hz => (h y hy z hz).trans (e.symm.isometry.dist_eq y z).symm⟩
    have hd : ∀t : ℝ,eP (@SMul.smul G H2 a.toSMul δ (eP.symm (verticalPath t)))=verticalPath (t+T) := by
      intro t;rw [ha,hδ,hn]
    have hpkg := hPeriod a p hq eP hm δ T hT hd
    have heq : (fun t : ℝ => eP.symm (verticalPath t))=α := funext ha
    obtain ⟨σ,hσ,htranslate,ℓ,hℓ,η,hη,hrange⟩ := hpkg
    let K := MulAction.stabilizer G (range (fun t : ℝ => eP.symm (verticalPath t)))
    let b : MulAction K H2 :=
      { smul := fun g z => @SMul.smul G H2 a.toSMul g.val z
        one_smul := fun z => @one_smul G H2 _ a z
        mul_smul := fun g h z => @mul_smul G H2 _ a.toSemigroupAction g.val h.val z }
    have hδK : δ∈K := by
      apply MulAction.mem_stabilizer_iff.mpr
      change (fun z => @SMul.smul G H2 a.toSMul δ z) '' range (fun t : ℝ => eP.symm (verticalPath t))=range (fun t : ℝ => eP.symm (verticalPath t))
      rw [heq]
      apply Subset.antisymm
      · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
        exact ⟨t+T,(hδ t).symm⟩
      · rintro _ ⟨t,rfl⟩
        refine ⟨α (t-T),mem_range_self _,?_⟩
        change @SMul.smul G H2 a.toSMul δ (α (t-T))=α t
        rw [hδ,sub_add_cancel]
    let δK : K := ⟨δ,hδK⟩
    have hfix (g : K) (z : H2) : p (@SMul.smul K H2 b.toSMul g z)=p z :=
      @IsQuotientCoveringMap.map_smul H2 E _ _ p G _ a hq g.val z
    have htr (g : K) (t : ℝ) : @SMul.smul K H2 b.toSMul g (α t)=α (t+σ (Additive.ofMul g)) := by
      apply eP.injective
      have ht := htranslate g t
      change eP (@SMul.smul G H2 a.toSMul g.val (eP.symm (verticalPath t)))=verticalPath (t+σ (Additive.ofMul g)) at ht
      rw [ha] at ht
      exact ht.trans (hn _).symm
    have hdK (t : ℝ) : @SMul.smul K H2 b.toSMul δK (α t)=α (t+T) := hδ t
    obtain ⟨hgenerated,hfullrange⟩ := actual_embedded_axis_supplied_translation_is_primitive
      b p α hα.injective T hT hfix hfibre σ hσ htr δK hdK
    intro g hg
    have hgK : g∈K := by
      apply MulAction.mem_stabilizer_iff.mpr
      change (fun z => @SMul.smul G H2 a.toSMul g z) '' range (fun t : ℝ => eP.symm (verticalPath t))=range (fun t : ℝ => eP.symm (verticalPath t))
      rw [heq]
      exact hg
    obtain ⟨n,hn⟩ := hgenerated ⟨g,hgK⟩
    refine ⟨n,?_⟩
    exact congrArg Subtype.val hn
  have hdcompact : IsCompact d.image := isCompact_range d.embedded.continuous
  obtain ⟨F,hF1,hFin,hFemb⟩ := hCollar M c d hc U V hU hV hUV hcover hfrontU hdcompact hcd
  refine ⟨F,hF1,hFin,hFemb,?_⟩
  intro x hx
  letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
  obtain ⟨g,hg,hcg,hggeo,hgim⟩ := embedded_geodesic_image_has_parametrized_representative H c hcgeo
  let cf : C(Circle,E) := ⟨c.map,c.embedded.continuous⟩
  have hcparam : IsParametrizedClosedGeodesic cf :=
    hSame (H.metric.replaceTopology H.compatible.symm) cf g c.embedded hg hgim.symm hggeo
  let A : C(Circle×unitInterval,E) :=
    ⟨fun zt => F (zt.2,zt.1),F.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
  have hAin : ∀t : unitInterval,t<1 → ∀z : Circle,A (z,t)∈U\d.image := hFin
  have hAout : ∀z : Circle,A (z,1)∉U\d.image := by
    intro z hz
    have hcU : U⊆c.imageᶜ := by
      rw [←hcover];exact subset_union_left
    exact (hcU hz.1) (by change F (1,z)∈c.image;rw [hF1];exact mem_range_self z)
  have hAgeo : IsParametrizedClosedGeodesic
      (⟨fun z => A (z,1),A.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(Circle,E)) := by
    have heq : (⟨fun z => A (z,1),A.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(Circle,E))=cf := by
      ext z;exact hF1 z
    rw [heq];exact hcparam
  obtain ⟨δ,α,hα,T,hT,hfront,himage,hfibre,hpres,hshift,hmono⟩ :=
    hCut a p hq hmetric (U\d.image) A hAin hAout hAgeo (hFemb 1) x hx
  have hprim : ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
      ∃n : ℤ,g=δ^n := by
    rcases hshift with hshift|hshift
    · exact hPrimitive a p hq hmetric α hα T hT hfibre δ hshift
    · intro g hg
      obtain ⟨n,hn⟩ := hPrimitive a p hq hmetric α hα T hT hfibre δ⁻¹ hshift g hg
      exact ⟨-n,by simpa only [inv_zpow,zpow_neg] using hn⟩
  have him : range (fun z : Circle => A (z,1))=c.image := by
    congr 1;funext z;exact hF1 z
  rw [him] at himage
  exact ⟨δ,α,hα,T,hT,hfront,himage,hfibre,hpres,hshift,hprim,hmono⟩
end CurveComplex.Hyperbolic
