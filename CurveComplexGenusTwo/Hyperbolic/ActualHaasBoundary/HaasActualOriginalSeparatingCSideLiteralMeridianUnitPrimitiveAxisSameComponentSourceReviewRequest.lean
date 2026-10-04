import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOriginalSeparatingCSidePrimitiveBoundaryMonodromyFrontierSourceReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPuncturedCylinderDoublePlaneProof
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2TranslatedAxesUniqueComposablePROVED
import CurveComplexGenusTwo.Topology.PrimitiveEssential
open Set Topology Filter
open scoped Pointwise UpperHalfPlane MatrixGroups unitInterval
open CurveComplex CurveComplex.Hyperbolic CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
set_option maxHeartbeats 24000000
set_option maxRecDepth 12000
theorem actual_original_separating_c_side_literal_meridian_unit_primitive_axis_same_component_source {E S G : Type} [TopologicalSpace E] [TopologicalSpace S]
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
        q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩)) :
    ∃ep : ActualPuncturedCylinder ≃ₜ {z : ℂ // z≠0 ∧ z≠1},
      (∀z,(ep z).val=(Real.exp z.val.2 : ℂ)*(z.val.1 : ℂ)) ∧
      ∃F : C(unitInterval×Circle,E),
      ∃hin : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∈U,
      ∃havoid : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∉d.image,
      (∀z,F (1,z)=c.map z) ∧ (∀t : unitInterval,IsEmbedding (fun z => F (t,z))) ∧
      ∃t : unitInterval,∃ht : t<1,
      ∃g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<(1/2:ℝ)}),
      ∃j : C({z : ℂ // z≠0 ∧ ‖z‖<(1/2:ℝ)},E),
        (∀z,j (g z)=F (t,z)) ∧
        (∀z,∃hz : (z.val+1:ℂ)≠0 ∧ (z.val+1:ℂ)≠1,
          j z=(f.symm (ep.symm ⟨z.val+1,hz⟩)).val.val) ∧
        (∀z,(g z).val=(ep (f ⟨⟨F (t,z),hin t ht z⟩,havoid t ht z⟩)).val-1) ∧
      ∀x : H2,∀hx : p x=F (0,1),
        let D := connectedComponentIn (p ⁻¹' (U\d.image)) x
        let m : C(Circle,E) := j.comp ⟨fun z => ⟨((1/4:ℝ):ℂ)*(z:ℂ),by
          constructor
          · exact mul_ne_zero (by norm_num) (Circle.coe_ne_zero _)
          · simp [norm_mul];norm_num⟩,by fun_prop⟩
        ∃δ : G,∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
          range α⊆frontier D ∧ p '' range α=c.image ∧
          (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
          (fun z => @SMul.smul G H2 a.toSMul δ z) '' D=D ∧
          ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
           (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
          (∀k : G,(fun z => @SMul.smul G H2 a.toSMul k z) '' range α=range α →
            ∃n : ℤ,k=δ^n) ∧
          (∀β : Path (F (0,1)) (F (0,1)),
            (∀s : unitInterval,β s=F (0,Circle.exp (2*Real.pi*(s:ℝ)))) →
            @SMul.smul G H2 a.toSMul δ x=
              (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val) ∧
          ∃n : ℤ,∃η : G,∃y : H2,∃hy : p y=m 1,y∈D ∧ (n=1 ∨ n=-1) ∧ η^n=δ ∧
            ∀β : Path (m 1) (m 1),
              (∀s : unitInterval,β s=m (Circle.exp (2*Real.pi*(s:ℝ)))) →
              @SMul.smul G H2 a.toSMul η y=
                (hq.isCoveringMap.monodromy ⟦β⟧ ⟨y,hy⟩).val := by
  have hEnd {E : Type} [TopologicalSpace E] [T2Space E]
      (c : Curve E) (U V : Set E) (hcover : U∪V=c.imageᶜ) (d : Set E)
      (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
      (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
      (hpunct : h (1,1)=r) (hr : r.2≠1)
      (f : {x : U // x.val∉d} ≃ₜ ActualPuncturedCylinder)
      (q : {z : Circle // z≠1} ≃ₜ ℝ)
      (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
        (f x).val=(r.1⁻¹*(h (e x.val).val).1,
          q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
      (F : C(unitInterval×Circle,E)) (hF1 : ∀z,F (1,z)=c.map z)
      (hin : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∈U)
      (havoid : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∉d) :
      ∀W : Set (Circle×ℝ),IsOpen W → (1,0)∈W →
        ∃τ : ℝ,0≤τ ∧ τ<1 ∧ ∀t : unitInterval,τ<(t:ℝ) → ∀ht : t<1,
          ∀z : Circle,(f ⟨⟨F (t,z),hin t ht z⟩,havoid t ht z⟩).val∈W := by
    have hEnd {E X Z : Type} [TopologicalSpace E] [T2Space E]
        [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Z] [CompactSpace Z]
        (U : Set E) (r : X) (e : U ≃ₜ {x : X // x≠r})
        (F : C(unitInterval×Z,E))
        (hinside : ∀t : unitInterval,t<1 → ∀z : Z,F (t,z)∈U)
        (houtside : ∀z : Z,F (1,z)∉U)
        (N : Set X) (hN : IsOpen N) (hrN : r∈N) :
        ∃τ : ℝ,0≤τ ∧ τ<1 ∧ ∀t : unitInterval,τ<(t:ℝ) → ∀ht : t<1,
          ∀z : Z,(e ⟨F (t,z),hinside t ht z⟩).val∈N := by
      let K := Nᶜ
      have hK : IsCompact K := hN.isClosed_compl.isCompact
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let κ : C(K,E) :=
        ⟨fun z => (e.symm ⟨z.val,by intro he;apply z.property;rw [he];exact hrN⟩).val,by
          apply continuous_subtype_val.comp
          apply e.symm.continuous.comp
          exact continuous_subtype_val.subtype_mk _⟩
      have hκ : IsCompact (range κ) := isCompact_range κ.continuous
      have hP : ∀z : Z,∀ᶠtz : unitInterval×Z in 𝓝 (1,z),F tz∉range κ := by
        intro z
        have hz : F (1,z)∉range κ := by
          rintro ⟨w,hw⟩
          exact houtside z (hw ▸ (e.symm ⟨w.val,by intro he;apply w.property;rw [he];exact hrN⟩).property)
        exact F.continuous.continuousAt.preimage_mem_nhds (hκ.isClosed.isOpen_compl.mem_nhds hz)
      have hnear : ∀ᶠt : unitInterval in 𝓝 1,∀z : Z,F (t,z)∉range κ := by
        simpa only [mem_univ,true_implies] using
          isCompact_univ.eventually_forall_of_forall_eventually (fun z _ => hP z)
      obtain ⟨ε,hε,hεnear⟩ := Metric.eventually_nhds_iff.mp hnear
      let η := min (ε/2) (1/2 : ℝ)
      have hη : 0<η := lt_min (by positivity) (by norm_num)
      have hηε : η<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      refine ⟨1-η,by dsimp [η];linarith [min_le_right (ε/2) (1/2:ℝ)],by linarith,?_⟩
      intro t ht htone z
      have hclose : dist t (1:unitInterval)<ε := by
        change dist (t:ℝ) (1:ℝ)<ε
        rw [Real.dist_eq,abs_of_nonpos (by linarith [t.property.2])]
        linarith
      have hav := hεnear hclose z
      by_contra hn
      let y : U := ⟨F (t,z),hinside t htone z⟩
      let w : K := ⟨(e y).val,hn⟩
      apply hav
      refine ⟨w,?_⟩
      change (e.symm ⟨(e y).val,_⟩).val=F (t,z)
      have he : (⟨(e y).val,_⟩ : {x : X // x≠r})=e y := rfl
      rw [he,e.symm_apply_apply]
    have hChart (r : Circle×Circle) (hr : r.2≠1) (q : {z : Circle // z≠1} ≃ₜ ℝ)
        (W : Set (Circle×ℝ)) (hW : IsOpen W) (hp : (1,0)∈W) :
        ∃N : Set (Circle×Circle),IsOpen N ∧ r∈N ∧
          ∀z∈N,∃hz : z.2≠1,
            (r.1⁻¹*z.1,q ⟨z.2,hz⟩-q ⟨r.2,hr⟩)∈W := by
      let V : Set (Circle×Circle) := {z | z.2≠1}
      have hV : IsOpen V := isOpen_ne_fun continuous_snd continuous_const
      let J : C(V,Circle×ℝ) :=
        ⟨fun z => (r.1⁻¹*z.val.1,q ⟨z.val.2,z.property⟩-q ⟨r.2,hr⟩),by fun_prop⟩
      let N := Subtype.val '' (J ⁻¹' W)
      have hN : IsOpen N := hV.isOpenMap_subtype_val _ (hW.preimage J.continuous)
      refine ⟨N,hN,?_,?_⟩
      · refine ⟨⟨r,hr⟩,?_,rfl⟩
        change (r.1⁻¹*r.1,q ⟨r.2,hr⟩-q ⟨r.2,hr⟩)∈W
        simpa using hp
      · rintro z ⟨v,hv,rfl⟩
        exact ⟨v.property,hv⟩
    have hout : ∀z : Circle,F (1,z)∉U := by
      intro z hz
      have hu : U⊆c.imageᶜ := by rw [←hcover];exact subset_union_left
      exact hu hz (by rw [hF1];exact mem_range_self z)
    let en : U ≃ₜ {z : Circle×Circle // z≠r} :=
      { toFun := fun x => ⟨h (e x).val,by
          intro heq;apply (e x).property;apply h.injective;exact heq.trans hpunct.symm⟩
        invFun := fun z => e.symm ⟨h.symm z.val,by
          intro heq;apply z.property
          rw [←h.apply_symm_apply z.val,heq,hpunct]⟩
        left_inv := by intro x;apply e.injective;apply Subtype.ext;simp
        right_inv := by intro z;apply Subtype.ext;simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
  
    intro W hW hpW
    obtain ⟨N,hN,hrN,hNW⟩ := hChart r hr q W hW hpW
    obtain ⟨τ,hτ,hτone,hτN⟩ := hEnd U r en F hin hout N hN hrN
    refine ⟨τ,hτ,hτone,?_⟩
    intro t ht htone z
    obtain ⟨hz,hzW⟩ := hNW _ (hτN t ht htone z)
    obtain ⟨hx,hfx⟩ := hf ⟨⟨F (t,z),hin t htone z⟩,havoid t htone z⟩
    rw [hfx]
    exact hzW
  have hSmall {E : Type} [TopologicalSpace E] (U d : Set E)
      (f : {x : U // x.val∉d} ≃ₜ ActualPuncturedCylinder)
      (e : ActualPuncturedCylinder ≃ₜ {z : ℂ // z≠0 ∧ z≠1})
      (he : ∀z,(e z).val=(Real.exp z.val.2 : ℂ)*(z.val.1 : ℂ))
      (F : C(unitInterval×Circle,E))
      (hin : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∈U)
      (havoid : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∉d)
      (hend : ∀W : Set (Circle×ℝ),IsOpen W → (1,0)∈W →
        ∃τ : ℝ,0≤τ ∧ τ<1 ∧ ∀t : unitInterval,τ<(t:ℝ) → ∀ht : t<1,
          ∀z : Circle,(f ⟨⟨F (t,z),hin t ht z⟩,havoid t ht z⟩).val∈W)
      (R : ℝ) (hR : 0<R) (hR1 : R≤1) :
      ∃t : unitInterval,∃ht : t<1,
        ∃g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}),
        ∃j : C({z : ℂ // z≠0 ∧ ‖z‖<R},E),
          (∀z,j (g z)=F (t,z)) ∧
          (∀z,∃hz : (z.val+1:ℂ)≠0 ∧ (z.val+1:ℂ)≠1,
            j z=(f.symm (e.symm ⟨z.val+1,hz⟩)).val.val) ∧
          (∀z,(g z).val=(e (f ⟨⟨F (t,z),hin t ht z⟩,havoid t ht z⟩)).val-1) := by
    let φ : C(Circle×ℝ,ℂ) := ⟨fun z => (Real.exp z.2 : ℂ)*(z.1 : ℂ)-1,by fun_prop⟩
    let W : Set (Circle×ℝ) := φ ⁻¹' Metric.ball 0 R
    have hW : IsOpen W := Metric.isOpen_ball.preimage φ.continuous
    have hWbase : ((1:Circle),(0:ℝ))∈W := by
      change dist ((Real.exp 0:ℂ)*(1:ℂ)-1) 0<R
      simpa using hR
    obtain ⟨τ,hτ0,hτ1,hτ⟩ := hend W hW hWbase
    let t : unitInterval := ⟨(τ+1)/2,by constructor <;> linarith⟩
    have ht : t<1 := by change (τ+1)/2<1;linarith
    have hτt : τ<(t:ℝ) := by change τ<(τ+1)/2;linarith
    let k : C(Circle,{x : U // x.val∉d}) :=
      ⟨fun z => ⟨⟨F (t,z),hin t ht z⟩,havoid t ht z⟩,by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hnorm (z : Circle) : ‖(e (f (k z))).val-1‖<R := by
      have hz := hτ t hτt ht z
      change dist (φ (f (k z)).val) 0<R at hz
      rw [dist_zero_right] at hz
      simpa only [φ,ContinuousMap.coe_mk,he] using hz
    let g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}) :=
      ⟨fun z => ⟨(e (f (k z))).val-1,
        ⟨sub_ne_zero.mpr (e (f (k z))).property.2,hnorm z⟩⟩,by
          apply Continuous.subtype_mk
          exact (continuous_subtype_val.comp (e.continuous.comp
            (f.continuous.comp k.continuous))).sub continuous_const⟩
    have hzplus (z : {z : ℂ // z≠0 ∧ ‖z‖<R}) :
        (z.val+1:ℂ)≠0 ∧ (z.val+1:ℂ)≠1 := by
      constructor
      · intro hz
        have heq : z.val=-1 := by linear_combination hz
        have hn := z.property.2
        rw [heq] at hn
        norm_num at hn
        linarith
      · intro hz
        apply z.property.1
        linear_combination hz
    let l : C({z : ℂ // z≠0 ∧ ‖z‖<R},{z : ℂ // z≠0 ∧ z≠1}) :=
      ⟨fun z => ⟨z.val+1,hzplus z⟩,by fun_prop⟩
    let j : C({z : ℂ // z≠0 ∧ ‖z‖<R},E) :=
      ⟨fun z => (f.symm (e.symm (l z))).val.val,by fun_prop⟩
    refine ⟨t,ht,g,j,?_,?_,fun z => rfl⟩
    · intro z
      have hl : l (g z)=e (f (k z)) := by
        apply Subtype.ext
        change (e (f (k z))).val-1+1=(e (f (k z))).val
        ring
      change (f.symm (e.symm (l (g z)))).val.val=F (t,z)
      rw [hl,e.symm_apply_apply,f.symm_apply_apply]
      rfl
    · intro z
      exact ⟨hzplus z,rfl⟩
  have hUnit {E G : Type} [MetricSpace E] [CompactSpace E] [Group G]
      (a : MulAction G H2) (p : H2 → E) (hq : letI := a;IsQuotientCoveringMap p G)
      (hmetric : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
        ∀y∈V,∀z∈V,dist (p y) (p z)=dist y z)
      (R ρ : ℝ) (hρ : 0<ρ) (hρR : ρ<R)
      (j : C({z : ℂ // z≠0 ∧ ‖z‖<R},E))
      (g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}))
      (F : C(unitInterval×Circle,E)) (t : unitInterval)
      (hFt : ∀z,j (g z)=F (t,z))
      (W : Set E) (hFin : ∀s : unitInterval,s<1 → ∀z : Circle,F (s,z)∈W)
      (hjin : ∀z : {z : ℂ // z≠0 ∧ ‖z‖<R},j z∈W) (ht : t<1)
      (x : H2) (hx : p x=F (0,1)) (δ : G)
      (α : ℝ → H2) (hα : Isometry α) (T : ℝ) (hT : 0<T)
      (hshift : (∀s : ℝ,@SMul.smul G H2 a.toSMul δ (α s)=α (s+T)) ∨
        (∀s : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α s)=α (s+T)))
      (hprimitive : ∀k : G,(fun z => @SMul.smul G H2 a.toSMul k z) '' range α=range α →
        ∃m : ℤ,k=δ^m)
      (hδmono : ∀β : Path (F (0,1)) (F (0,1)),
        (∀s : unitInterval,β s=F (0,Circle.exp (2*Real.pi*(s:ℝ)))) →
        @SMul.smul G H2 a.toSMul δ x=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val) :
      let m : C(Circle,E) := j.comp ⟨fun z => ⟨(ρ:ℂ)*(z:ℂ),by
        constructor
        · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') (Circle.coe_ne_zero _)
        · simpa [norm_mul,abs_of_pos hρ] using hρR⟩,by fun_prop⟩
      ∃n : ℤ,∃η : G,∃y : H2,∃hy : p y=m 1,y∈connectedComponentIn (p ⁻¹' W) x ∧ (n=1 ∨ n=-1) ∧ η^n=δ ∧
        ∀β : Path (m 1) (m 1),
          (∀s : unitInterval,β s=m (Circle.exp (2*Real.pi*(s:ℝ)))) →
          @SMul.smul G H2 a.toSMul η y=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨y,hy⟩).val := by
    have hInitial {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
        (a : MulAction G P) (p : P → E) (hq : letI := a; IsQuotientCoveringMap p G)
        (R ρ : ℝ) (hρ : 0<ρ) (hρR : ρ<R)
        (j : C({z : ℂ // z≠0 ∧ ‖z‖<R},E))
        (g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}))
        (F : C(unitInterval×Circle,E)) (c : C(Circle,E))
        (hF0 : ∀z,F (0,z)=c z) (t : unitInterval)
        (hFt : ∀z,j (g z)=F (t,z))
        (W : Set E) (hFin : ∀s : unitInterval,s<1 → ∀z : Circle,F (s,z)∈W)
        (hjin : ∀z : {z : ℂ // z≠0 ∧ ‖z‖<R},j z∈W) (ht : t<1)
        (x : P) (hx : p x=c 1) :
        let m : C(Circle,E) := j.comp ⟨fun z => ⟨(ρ:ℂ)*(z:ℂ),by
          constructor
          · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') (Circle.coe_ne_zero _)
          · simpa [norm_mul,abs_of_pos hρ] using hρR⟩,by fun_prop⟩
        ∃n : ℤ,∃δ η : G,∃y : P,∃hy : p y=m 1,y∈connectedComponentIn (p ⁻¹' W) x ∧ η^n=δ ∧
          (∀β : Path (c 1) (c 1),
            (∀s : unitInterval,β s=c (Circle.exp (2*Real.pi*(s:ℝ)))) →
            @SMul.smul G P a.toSMul δ x=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val) ∧
          (∀β : Path (m 1) (m 1),
            (∀s : unitInterval,β s=m (Circle.exp (2*Real.pi*(s:ℝ)))) →
            @SMul.smul G P a.toSMul η y=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨y,hy⟩).val) := by
      have hDisk (R ρ : ℝ) (hρ : 0<ρ) (hρR : ρ<R)
          (f : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R})) :
          ∃n : ℤ,∃g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}),
            (∀z,(g z).val=(ρ:ℂ)*(z^n:Circle)) ∧ f.Homotopic g := by
        have hRad (R ρ : ℝ) (hρ : 0<ρ) (hρR : ρ<R)
            (f : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R})) :
            ∃u : C(Circle,Circle),
              ∃g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}),
                (∀z,(g z).val=(ρ:ℂ)*(u z:ℂ)) ∧ f.Homotopic g := by
          let u : C(Circle,Circle) :=
            ⟨fun z => ⟨(f z).val/(‖(f z).val‖:ℂ),by
              change (f z).val/(‖(f z).val‖:ℂ)∈Metric.sphere (0:ℂ) 1
              rw [mem_sphere_zero_iff_norm]
              rw [norm_div,Complex.norm_real,Real.norm_eq_abs,
                abs_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr (f z).property.1)]⟩,by
              apply Continuous.subtype_mk
              exact (continuous_subtype_val.comp f.continuous).div
                ((Complex.continuous_ofReal).comp (continuous_norm.comp
                  (continuous_subtype_val.comp f.continuous)))
                (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (f z).property.1))⟩
          let g : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}) :=
            ⟨fun z => ⟨(ρ:ℂ)*(u z:ℂ),by
              constructor
              · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') (Circle.coe_ne_zero _)
              · simpa [norm_mul,abs_of_pos hρ] using hρR⟩,by fun_prop⟩
          refine ⟨u,g,(fun z => rfl),⟨?_⟩⟩
          let s (t : unitInterval) (z : Circle) : ℝ :=
            (1-(t:ℝ))*‖(f z).val‖+(t:ℝ)*ρ
          have hspos (t : unitInterval) (z : Circle) : 0<s t z := by
            have hfpos : 0<‖(f z).val‖ := norm_pos_iff.mpr (f z).property.1
            dsimp [s]
            by_cases ht : (t:ℝ)=0
            · simp [ht,hfpos]
            · have htp : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
              nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) hfpos.le,mul_pos htp hρ]
          have hsR (t : unitInterval) (z : Circle) : s t z<R := by
            have hfR := (f z).property.2
            dsimp [s]
            by_cases ht : (t:ℝ)=0
            · simpa [ht] using hfR
            · have htp : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
              nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hfR.le),
                mul_pos htp (sub_pos.mpr hρR)]
          refine { toContinuousMap := ⟨fun tz => ⟨(s tz.1 tz.2:ℂ)*(u tz.2:ℂ),?_⟩,?_⟩
                   map_zero_left := ?_
                   map_one_left := ?_ }
          · constructor
            · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hspos _ _).ne') (Circle.coe_ne_zero _)
            · simpa [norm_mul,abs_of_pos (hspos _ _)] using hsR tz.1 tz.2
          · dsimp [s];fun_prop
          · intro z;apply Subtype.ext
            dsimp [s,u]
            norm_num only [sub_zero,one_mul,zero_mul,add_zero]
            exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (f z).property.1))
          · intro z;apply Subtype.ext
            simp [g,s]
        have hWind (f : C(Circle,Circle)) :
            ∃n : ℤ,f.Homotopic ⟨fun z => z^n,continuous_zpow n⟩ := by
          let g : C(ℝ,Circle) := ⟨fun t => f (Circle.exp t),f.continuous.comp Circle.exp.continuous⟩
          obtain ⟨a,ha⟩ := Circle.exp_surjective (g 0)
          obtain ⟨F,hF,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 a ha
          have hFl (t : ℝ) : Circle.exp (F t)=f (Circle.exp t) := congrFun hF.2 t
          have hbase : Circle.exp (F (2*Real.pi))=Circle.exp (F 0) := by
            rw [hFl,hFl,Circle.exp_two_pi,Circle.exp_zero]
          obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hbase
          have hp : ∀t : ℝ,F (t+2*Real.pi)=F t+(n:ℝ)*(2*Real.pi) := by
            have heq : (fun t : ℝ => F (t+2*Real.pi))=
                (fun t : ℝ => F t+(n:ℝ)*(2*Real.pi)) := by
              refine Circle.isCoveringMap_exp.eq_of_comp_eq
                (F.continuous.comp (continuous_id.add continuous_const))
                (F.continuous.add continuous_const) ?_ 0 ?_
              · funext t
                change Circle.exp (F (t+2*Real.pi))=Circle.exp (F t+(n:ℝ)*(2*Real.pi))
                rw [hFl,Circle.exp_add_two_pi,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one,hFl]
              · simpa only [zero_add] using hn
            exact fun t => congrFun heq t
          exact ⟨n,circle_map_homotopic_winding_of_lift f n F hFl hp⟩
        obtain ⟨u,g,hg,hfg⟩ := hRad R ρ hρ hρR f
        obtain ⟨n,hu⟩ := hWind u
        let j : C(Circle,{z : ℂ // z≠0 ∧ ‖z‖<R}) :=
          ⟨fun z => ⟨(ρ:ℂ)*(z:ℂ),by
            constructor
            · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hρ.ne') (Circle.coe_ne_zero _)
            · simpa [norm_mul,abs_of_pos hρ] using hρR⟩,by fun_prop⟩
        have heq : g=j.comp u := by
          ext z;exact hg z
        refine ⟨n,j.comp ⟨fun z => z^n,continuous_zpow n⟩,(fun z => rfl),?_⟩
        rw [heq] at hfg
        exact hfg.trans ((ContinuousMap.Homotopic.refl j).comp hu)
      have hRoot {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
          (a : MulAction G P) (p : P → E) (hq : letI := a;IsQuotientCoveringMap p G)
          (f m : C(Circle,E)) (n : ℤ) (H : C(Circle×unitInterval,E))
          (hH0 : ∀z,H (z,0)=f z) (hH1 : ∀z,H (z,1)=m (z^n))
          (W : Set E) (hinside : ∀z : Circle,∀s : unitInterval,H (z,s)∈W)
          (x : P) (hx : p x=f 1) :
          ∃δ η : G,∃y : P,∃hy : p y=m 1,y∈connectedComponentIn (p ⁻¹' W) x ∧ η^n=δ ∧
            (∀β : Path (f 1) (f 1),
              (∀t : unitInterval,β t=f (Circle.exp (2*Real.pi*(t:ℝ)))) →
              @SMul.smul G P a.toSMul δ x=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val) ∧
            (∀β : Path (m 1) (m 1),
              (∀t : unitInterval,β t=m (Circle.exp (2*Real.pi*(t:ℝ)))) →
              @SMul.smul G P a.toSMul η y=(hq.isCoveringMap.monodromy ⟦β⟧ ⟨y,hy⟩).val) := by
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
        have hInteger {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
            (a : MulAction G P) (p : P → E) (hq : letI := a;IsQuotientCoveringMap p G)
            (f : C(Circle,E)) (x : P) (hx : p x=f 1) :
            ∃η : G,∀n : ℤ,∀β : Path (f 1) (f 1),
              (∀t : unitInterval,β t=f (Circle.exp (2*Real.pi*(n:ℝ)*(t:ℝ)))) →
              @SMul.smul G P a.toSMul (η^n) x=
                (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
          have hPeriod {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
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
          have hPowers {G P : Type} [Group G] (a : MulAction G P) (δ : G)
              (α : ℝ → P) (T : ℝ)
              (hδ : ∀t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
              ∀n : ℤ,∀t : ℝ,@SMul.smul G P a.toSMul (δ^n) (α t)=α (t+(n:ℝ)*T) := by
            letI := a
            have hδ' (t : ℝ) : δ • α t=α (t+T) := hδ t
            have hinv (t : ℝ) : δ⁻¹ • α t=α (t-T) := by
              have h := congrArg (fun z => δ⁻¹ • z) (hδ' (t-T))
              simpa only [inv_smul_smul,sub_add_cancel] using h.symm
            have hpow (n : ℤ) : ∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
              refine Int.induction_on n ?_ ?_ ?_
              · intro t;simp
              · intro m ih t
                rw [zpow_add,zpow_one,mul_smul,hδ',ih]
                congr 1
                push_cast
                ring
              · intro m ih t
                rw [zpow_sub,zpow_one,mul_smul,hinv,ih]
                congr 1
                push_cast
                ring
            exact hpow
          let clock : C(ℝ,E) :=
            ⟨fun t => f (Circle.exp (2*Real.pi*t)),by fun_prop⟩
          have hxclock : p x=clock 0 := by simpa [clock] using hx
          obtain ⟨α,hα,_⟩ := hq.isCoveringMap.existsUnique_continuousMap_lifts clock 0 x hxclock
          have hproj (t : ℝ) : p (α t)=f (Circle.exp (2*Real.pi*t)) := congrFun hα.2 t
          have hperiod : ∀t : ℝ,p (α (t+1))=p (α t) := by
            intro t;rw [hproj,hproj]
            congr 1
            have he : 2*Real.pi*(t+1)=2*Real.pi*t+2*Real.pi := by ring
            rw [he,Circle.exp_add_two_pi]
          obtain ⟨η,hη,hstab,hmono⟩ := hPeriod a p hq α α.continuous 1 hperiod
          refine ⟨η,?_⟩
          intro n β hβ
          have hlift : (fun t : unitInterval => α ((n:ℝ)*(t:ℝ)))=
              hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) := by
            apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
            refine ⟨α.continuous.comp (continuous_const.mul continuous_subtype_val),?_,?_⟩
            · funext t
              change p (α ((n:ℝ)*(t:ℝ)))=β t
              rw [hproj,hβ]
              congr 2;ring
            · simpa using hα.1
          change @SMul.smul G P a.toSMul (η^n) x=
            hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) 1
          rw [←hlift,←hα.1]
          simpa using hPowers a η α 1 hη n 0
        let g : C(Circle,E) := ⟨fun z => m (z^n),by fun_prop⟩
        obtain ⟨L,δ,hL0,hLproj,hLinitial,hLterminal,hδ,hδmono⟩ :=
          hClock a p hq f g H hH0 hH1 x hx
        let y := L (1,0)
        have hy : p y=m 1 := by simpa [y,g] using hLterminal 0
        have hconn : IsPreconnected (range (fun s : unitInterval => L (s,0))) :=
          isPreconnected_range (L.continuous.comp (continuous_id.prodMk continuous_const))
        have hxrange : x∈range (fun s : unitInterval => L (s,0)) := ⟨0,hL0⟩
        have hsub : range (fun s : unitInterval => L (s,0))⊆p ⁻¹' W := by
          rintro _ ⟨s,rfl⟩
          change p (L (s,0))∈W
          rw [hLproj]
          exact hinside _ s
        have hyC : y∈connectedComponentIn (p ⁻¹' W) x :=
          hconn.subset_connectedComponentIn hxrange hsub (mem_range_self 1)
        obtain ⟨η,hη⟩ := hInteger a p hq m y hy
        let β : Path (m 1) (m 1) :=
          { toFun := fun t => m (Circle.exp (2*Real.pi*(n:ℝ)*(t:ℝ)))
            continuous_toFun := by fun_prop
            source' := by simp
            target' := by simp [mul_comm (2*Real.pi) (n:ℝ),Circle.exp_int_mul_two_pi] }
        have hβlift : (fun t : unitInterval => L (1,(t:ℝ)))=
            hq.isCoveringMap.liftPath β y (β.source.trans hy.symm) := by
          apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
          refine ⟨L.continuous.comp (continuous_const.prodMk continuous_subtype_val),?_,rfl⟩
          funext t
          change p (L (1,(t:ℝ)))=m (Circle.exp (2*Real.pi*(n:ℝ)*(t:ℝ)))
          rw [hLterminal]
          change m ((Circle.exp (2*Real.pi*(t:ℝ)))^n)=_
          rw [←Circle.exp_zsmul]
          congr 2
          simp only [zsmul_eq_mul]
          ring
        have hηn := hη n β (fun t => rfl)
        change @SMul.smul G P a.toSMul (η^n) y=
          hq.isCoveringMap.liftPath β y (β.source.trans hy.symm) 1 at hηn
        rw [←hβlift] at hηn
        have hroot : η^n=δ := by
          letI := a
          letI := hq.isCancelSMul
          apply IsCancelSMul.right_cancel' (η^n) δ y
          change @SMul.smul G P a.toSMul (η^n) y = @SMul.smul G P a.toSMul δ y
          exact hηn.trans (by simpa [y] using (hδ 1 0).symm)
        refine ⟨δ,η,y,hy,hyC,hroot,hδmono,?_⟩
        intro γ hγ
        simpa only [zpow_one,Int.cast_one,mul_one] using hη 1 γ (by simpa only [Int.cast_one,mul_one] using hγ)
      intro m
      let k : C(unitInterval,unitInterval) :=
        ⟨fun s => ⟨(t:ℝ)*(s:ℝ),by
          have ht0 := t.property.1
          have ht1 := t.property.2
          have hs0 := s.property.1
          have hs1 := s.property.2
          constructor <;> nlinarith⟩,by fun_prop⟩
      let C0 : ContinuousMap.Homotopy c (j.comp g) := by
        refine ⟨⟨fun sz => F (k sz.1,sz.2),F.continuous.comp
          ((k.continuous.comp continuous_fst).prodMk continuous_snd)⟩,?_,?_⟩
        · intro z
          change F (k 0,z)=c z
          have hk0 : k 0=0 := by apply Subtype.ext;simp [k]
          rw [hk0,hF0]
        · intro z
          change F (k 1,z)=j (g z)
          have hk1 : k 1=t := by apply Subtype.ext;simp [k]
          rw [hk1,hFt]
      obtain ⟨n,gn,hgn,hg⟩ := hDisk R ρ hρ hρR g
      obtain ⟨Q⟩ := hg
      let C1 := (ContinuousMap.Homotopy.refl j).comp Q
      let K := C0.trans C1
      have hC0 : ∀s : unitInterval,∀z : Circle,C0 (s,z)∈W := by
        intro s z
        change F (k s,z)∈W
        apply hFin (k s) _ z
        change (t:ℝ)*(s:ℝ)<1
        have ht0 := t.property.1
        have hs0 := s.property.1
        have hs1 := s.property.2
        have ht' : (t:ℝ)<1 := ht
        nlinarith
      have hC1 : ∀s : unitInterval,∀z : Circle,C1 (s,z)∈W := by
        intro s z
        exact hjin (Q (s,z))
      have hK : ∀s : unitInterval,∀z : Circle,K (s,z)∈W := by
        intro s z
        rw [ContinuousMap.Homotopy.trans_apply]
        split_ifs
        · exact hC0 _ z
        · exact hC1 _ z
      let H : C(Circle×unitInterval,E) :=
        ⟨fun z => K (z.2,z.1),K.continuous.comp (continuous_snd.prodMk continuous_fst)⟩
      have hH0 : ∀z,H (z,0)=c z := by intro z;exact K.apply_zero z
      have hH1 : ∀z,H (z,1)=m (z^n) := by
        intro z
        change K (1,z)=j _
        rw [K.apply_one]
        change j (gn z)=j _
        congr 1
        apply Subtype.ext
        exact hgn z
      obtain ⟨δ,η,y,hy,hyC,hroot,hδ,hη⟩ := hRoot a p hq c m n H hH0 hH1 W (fun z s=>hK s z) x hx
      exact ⟨n,δ,η,y,hy,hyC,hroot,hδ,hη⟩
    have hUnit {G : Type} [Group G] (a : MulAction G H2)
        (hiso : ∀g : G,Isometry (fun z => @SMul.smul G H2 a.toSMul g z))
        (δ η : G) (n : ℤ) (hroot : η^n=δ)
        (α : ℝ → H2) (hα : Isometry α) (T : ℝ) (hT : 0<T)
        (hdisp : ∀g : G,g≠1 → ∃ε : ℝ,0<ε ∧ ∀z : H2,
          ε≤dist z (@SMul.smul G H2 a.toSMul g z))
        (hshift : (∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
          (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T)))
        (hprimitive : ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
          ∃m : ℤ,g=δ^m) : n=1 ∨ n=-1 := by
      have hUnit {G : Type} [Group G] (a : MulAction G H2)
          (hiso : ∀g : G,Isometry (fun z => @SMul.smul G H2 a.toSMul g z))
          (δ η : G) (n : ℤ) (hroot : η^n=δ)
          (α : ℝ → H2) (hα : Isometry α) (T ε : ℝ) (hT : 0<T) (hε : 0<ε)
          (hdisp : ∀z : H2,ε≤dist z (@SMul.smul G H2 a.toSMul δ z))
          (hshift : ∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T))
          (hprimitive : ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
            ∃m : ℤ,g=δ^m) : n=1 ∨ n=-1 := by
        have hPreserve {G : Type} [Group G] (a : MulAction G H2)
            (hiso : ∀g : G,Isometry (fun z => @SMul.smul G H2 a.toSMul g z))
            (δ η : G) (n : ℤ) (hroot : η^n=δ)
            (α : ℝ → H2) (hα : Isometry α) (T ε : ℝ) (hT : 0<T) (hε : 0<ε)
            (hdisp : ∀z : H2,ε≤dist z (@SMul.smul G H2 a.toSMul δ z))
            (hshift : ∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) :
            (fun z => @SMul.smul G H2 a.toSMul η z) '' range α=range α := by
          letI := a
          let g : H2 ≃ᵢ H2 :=
            { toEquiv := MulAction.toPerm δ
              isometry_toFun := hiso δ }
          let β : ℝ → H2 := fun t => @SMul.smul G H2 a.toSMul η (α t)
          have hβ : Isometry β := (hiso η).comp hα
          have hcomm : δ*η=η*δ := by
            rw [←hroot]
            exact (Commute.zpow_self η n).eq
          have hβshift : ∀t : ℝ,g (β t)=β (t+T) := by
            intro t
            change δ • (η • α t)=η • α (t+T)
            rw [←mul_smul,hcomm,mul_smul]
            exact congrArg (fun z => η • z) (hshift t)
          have heq := actual_h2_translated_isometric_lines_same_range g α β hα hβ
            ε hε hdisp T T hT.ne' hT.ne' hshift hβshift
          rw [←Set.range_comp]
          exact heq.symm
        have hInject {G P : Type} [Group G] (a : MulAction G P) (δ : G)
            (α : ℝ → P) (hα : Function.Injective α) (T : ℝ) (hT : T≠0)
            (hδ : ∀t : ℝ,@SMul.smul G P a.toSMul δ (α t)=α (t+T)) :
            Function.Injective (fun n : ℤ => δ^n) := by
          letI := a
          have hδ' (t : ℝ) : δ • α t=α (t+T) := hδ t
          have hinv (t : ℝ) : δ⁻¹ • α t=α (t-T) := by
            have h := congrArg (fun z => δ⁻¹ • z) (hδ' (t-T))
            simpa only [inv_smul_smul,sub_add_cancel] using h.symm
          have hpow (n : ℤ) : ∀t : ℝ,δ^n • α t=α (t+(n:ℝ)*T) := by
            refine Int.induction_on n ?_ ?_ ?_
            · intro t;simp
            · intro m ih t
              rw [zpow_add,zpow_one,mul_smul,hδ',ih]
              congr 1
              push_cast
              ring
            · intro m ih t
              rw [zpow_sub,zpow_one,mul_smul,hinv,ih]
              congr 1
              push_cast
              ring
          intro m n hmn
          have hm : α ((m:ℝ)*T)=α ((n:ℝ)*T) := by
            simpa only [zero_add] using (hpow m 0).symm.trans
              ((congrArg (fun g => g • α 0) hmn).trans (hpow n 0))
          have he := mul_right_cancel₀ hT (hα hm)
          exact_mod_cast he
        have hUnit {G : Type} [Group G] (δ η : G) (n : ℤ)
            (hδ : Function.Injective (fun k : ℤ => δ^k))
            (hn : η^n=δ) (hη : ∃m : ℤ,η=δ^m) : n=1 ∨ n=-1 := by
          obtain ⟨m,rfl⟩ := hη
          have hprod : m*n=1 := hδ (by simpa only [zpow_mul,zpow_one] using hn)
          have hdiv : n∣1 := ⟨m,by linarith⟩
          exact Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [mul_comm] using hprod)
        have hη := hPreserve a hiso δ η n hroot α hα T ε hT hε hdisp hshift
        exact hUnit δ η n (hInject a δ α hα.injective T hT.ne' hshift) hroot
          (hprimitive η hη)
      letI := a
      have hne (g : G) (hs : ∀t : ℝ,@SMul.smul G H2 a.toSMul g (α t)=α (t+T)) : g≠1 := by
        intro hg
        have hx := hs 0
        rw [hg] at hx
        change (1:G) • α 0=α (0+T) at hx
        have ht := hα.injective (by simpa only [one_smul,zero_add] using hx)
        linarith
      rcases hshift with hs|hs
      · obtain ⟨ε,hε,hd⟩ := hdisp δ (hne δ hs)
        exact hUnit a hiso δ η n hroot α hα T ε hT hε hd hs hprimitive
      · obtain ⟨ε,hε,hd⟩ := hdisp δ⁻¹ (hne δ⁻¹ hs)
        have hr : (η⁻¹)^n=δ⁻¹ := by rw [inv_zpow,hroot]
        have hp : ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
            ∃m : ℤ,g=(δ⁻¹)^m := by
          intro g hg
          obtain ⟨m,hm⟩ := hprimitive g hg
          refine ⟨-m,?_⟩
          simpa only [inv_zpow,zpow_neg,inv_inv] using hm
        exact hUnit a hiso δ⁻¹ η⁻¹ n hr α hα T ε hT hε hd hs hp
    have hUniform
        {E G : Type} [MetricSpace E] [CompactSpace E] [Group G]
        (a : MulAction G H2) (p : H2 → E)
        (hq : letI := a; IsQuotientCoveringMap p G)
        (hmetric : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
          ∀ y ∈ U, ∀ z ∈ U, dist (p y) (p z) = dist y z)
        (δ : G) (hδ : δ ≠ 1) :
        ∃ ε : ℝ, 0 < ε ∧ ∀ z : H2,
          ε ≤ dist z (@SMul.smul G H2 a.toSMul δ z) := by
      exact open Matrix in
      open scoped MatrixGroups unitInterval in
      by
        classical
        letI := a
        let actualCoveringMap := hq.isCoveringMap
        have fiber_nonempty (x : E) : Nonempty (p ⁻¹' {x}) := by
          obtain ⟨z,hz⟩ := hq.surjective x
          exact ⟨⟨z,hz⟩⟩
        letI (x : E) : Nonempty (p ⁻¹' {x}) := fiber_nonempty x
        let actualTrivialization (x : E) := (actualCoveringMap x).toTrivialization
        have uniform_evenly_covered_radius : ∃ ε : ℝ, 0 < ε ∧ ∀ x : E,
            ∃ b : E, Metric.ball x ε ⊆ (actualTrivialization b).baseSet := by
          obtain ⟨ε,hε,hcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
            (fun x => (actualTrivialization x).open_baseSet)
            (show Set.univ ⊆ ⋃ x, (actualTrivialization x).baseSet from
              fun x _ => Set.mem_iUnion.mpr ⟨x,(actualCoveringMap x).mem_toTrivialization_baseSet⟩)
          exact ⟨ε,hε,fun x => hcover x (Set.mem_univ x)⟩
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
        have p_nonexpanding (x y : H2) :
            dist (p x) (p y) ≤ dist x y := by
          obtain ⟨γ,hγ⟩ := actual_segment x y
          choose U hU hxU hmetric using hmetric
          let V : unitInterval → Set unitInterval := fun t => γ ⁻¹' U (γ t)
          have hV (t : unitInterval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
          have hcover : Set.univ ⊆ ⋃ t, V t := by
            intro t ht
            exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
          obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
            exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
          have hstep (n : ℕ) :
              dist (p (γ (t n))) (p (γ (t (n+1)))) =
                dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
            obtain ⟨j,hj⟩ := hsub n
            have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
            have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
            have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
            rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
              abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
            simp only [neg_sub]
          have hbound (n : ℕ) :
              dist (p (γ (t 0))) (p (γ (t n))) ≤
                dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
            induction n with
            | zero => simp
            | succ n ih =>
              have htri := dist_triangle (p (γ (t 0)))
                (p (γ (t n))) (p (γ (t (n+1))))
              have hsn := hstep n
              nlinarith
          have h := hbound N
          rw [ht0,hN N le_rfl] at h
          simpa using h
        obtain ⟨coverRadius,coverRadius_pos,coverRadius_control⟩ := uniform_evenly_covered_radius
        refine ⟨coverRadius,coverRadius_pos,?_⟩
        intro z
        by_contra hle
        have hshort : dist z (δ • z) < coverRadius := lt_of_not_ge hle
        obtain ⟨b,hb⟩ := coverRadius_control (p z)
        obtain ⟨γ,hγ⟩ := actual_segment z (δ • z)
        let Γ : C(unitInterval,H2) := ⟨γ,γ.continuous⟩
        let T := actualTrivialization b
        letI : DiscreteTopology (p ⁻¹' {b}) := (actualCoveringMap b).discreteTopology_fiber
        have hsource (t : unitInterval) : Γ t ∈ T.source := by
          apply T.mem_source.mpr
          apply hb
          change dist (p (γ t)) (p z) < coverRadius
          have hπ := p_nonexpanding (γ t) z
          have hseg : dist (γ t) z = dist z (δ • z) * (t : ℝ) := by
            have h := hγ 0 t
            simpa [Real.dist_eq,abs_of_nonneg t.property.1,dist_comm] using h
          have hbound := mul_le_of_le_one_right (dist_nonneg (x := z) (y := δ • z)) t.property.2
          rw [hseg] at hπ
          exact lt_of_le_of_lt (hπ.trans hbound) hshort
        let label : unitInterval → (p ⁻¹' {b}) := fun t => (T (Γ t)).2
        have hlabel : Continuous label := continuous_snd.comp
          (T.toOpenPartialHomeomorph.continuousOn.comp_continuous Γ.continuous hsource)
        have hlabels : label 0 = label 1 :=
          (isPreconnected_range hlabel).subsingleton (mem_range_self 0) (mem_range_self 1)
        have hprojection : p (Γ 0) = p (Γ 1) := by
          change p (γ 0) = p (γ 1)
          rw [γ.source,γ.target]
          exact (hq.map_smul δ).symm
        have hcoords : T (Γ 0) = T (Γ 1) := by
          apply Prod.ext
          · change (T.toOpenPartialHomeomorph (Γ 0)).1 = (T.toOpenPartialHomeomorph (Γ 1)).1
            rw [T.proj_toFun _ (hsource 0),T.proj_toFun _ (hsource 1)]
            exact hprojection
          · exact hlabels
        have hend : Γ 0 = Γ 1 := T.injOn (hsource 0) (hsource 1) hcoords
        have hfixed : δ • z = z := by
          change γ 0 = γ 1 at hend
          simpa only [γ.source,γ.target] using hend.symm
        letI := hq.isCancelSMul
        apply hδ
        exact IsCancelSMul.right_cancel δ 1 z (by simpa using hfixed)
    intro m
    let c : C(Circle,E) := ⟨fun z => F (0,z),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    obtain ⟨n,δ',η,y,hy,hyC,hroot,hδ',hη⟩ := hInitial a p hq R ρ hρ hρR j g F c (fun z=>rfl) t hFt W hFin hjin ht x hx
    let β : Path (F (0,1)) (F (0,1)) := {
      toFun := fun s => F (0,Circle.exp (2*Real.pi*(s:ℝ)))
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp [Circle.exp_two_pi] }
    have heq : δ'=δ := by
      letI := a
      letI := hq.isCancelSMul
      apply IsCancelSMul.right_cancel' δ' δ x
      change @SMul.smul G H2 a.toSMul δ' x=@SMul.smul G H2 a.toSMul δ x
      exact (hδ' β (fun s=>rfl)).trans (hδmono β (fun s=>rfl)).symm
    rw [heq] at hroot
    have hiso : ∀k : G,Isometry (fun z => @SMul.smul G H2 a.toSMul k z) := by
      intro k
      letI := a
      let b : H2 ≃ₜ H2 := {
        toFun := fun z => k • z
        invFun := fun z => k⁻¹ • z
        left_inv := inv_smul_smul k
        right_inv := smul_inv_smul k
        continuous_toFun := hq.continuous_const_smul k
        continuous_invFun := hq.continuous_const_smul k⁻¹ }
      exact actual_deck_development_isometry p (Homeomorph.refl H2) hmetric b (fun z=>hq.map_smul k)
    have hn := hUnit a hiso δ η n hroot α hα T hT
      (fun k hk => hUniform a p hq hmetric k hk) hshift hprimitive
    exact ⟨n,η,y,hy,hyC,hn,hroot,hη⟩
  obtain ⟨ep,hep,_⟩ := actual_punctured_cylinder_double_punctured_plane_homeomorph
  obtain ⟨F,hF1,hFin,hFemb,hAxes⟩ :=
    actual_original_separating_c_side_primitive_boundary_monodromy_frontier_source
      M H c d hc hcgeo U V hU hV hUV hcover hfrontU hcd a p hq hmetric
  letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
  letI : CompactSpace E := H.compact
  have hin : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∈U := fun t ht z => (hFin t ht z).1
  have ha : ∀t : unitInterval,t<1 → ∀z : Circle,F (t,z)∉d.image := fun t ht z => (hFin t ht z).2
  have hend := hEnd c U V hcover d.image e h r hpunct hr f q hf F hF1 hin ha
  obtain ⟨t,ht,g,j,hjg,hj,hg⟩ := hSmall U d.image f ep hep F hin ha hend (1/2) (by norm_num) (by norm_num)
  have hjin : ∀z : {z : ℂ // z≠0 ∧ ‖z‖<(1/2:ℝ)},j z∈U\d.image := by
    intro z
    obtain ⟨hz,hjz⟩ := hj z
    rw [hjz]
    exact ⟨(f.symm (ep.symm ⟨z.val+1,hz⟩)).val.property,
      (f.symm (ep.symm ⟨z.val+1,hz⟩)).property⟩
  refine ⟨ep,hep,F,hin,ha,hF1,hFemb,t,ht,g,j,hjg,hj,hg,?_⟩
  intro x hx D m
  obtain ⟨δ,α,hα,T,hT,hfront,himage,hfib,hpres,hshift,hprim,hmono⟩ := hAxes x hx
  obtain ⟨n,η,y,hy,hyC,hn,hroot,hη⟩ := hUnit a p hq hmetric (1/2) (1/4)
    (by norm_num) (by norm_num) j g F t hjg (U\d.image) hFin hjin ht x hx δ α hα T hT hshift hprim hmono
  exact ⟨δ,α,hα,T,hT,hfront,himage,hfib,hpres,hshift,hprim,hmono,n,η,y,hy,hyC,hn,hroot,hη⟩
