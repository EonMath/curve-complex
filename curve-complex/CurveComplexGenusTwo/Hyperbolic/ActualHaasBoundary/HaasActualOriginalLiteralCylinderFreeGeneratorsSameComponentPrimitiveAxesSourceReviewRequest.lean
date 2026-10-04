import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2LocalUnitGeodesicPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1EmbeddedTraversalComposablePROVED
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasEmbeddedAxisSuppliedPrimitiveGeneratorReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualPuncturedCylinderBoundaryBasisProof
open Set Topology
open scoped Pointwise UpperHalfPlane MatrixGroups
namespace CurveComplex.Hyperbolic
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000
theorem actual_original_literal_cylinder_free_generators_same_component_primitive_axes_source {E G C K : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G] [TopologicalSpace C] [Group K]
    (H : ClosedHyperbolicMetric E) (d : Curve E)
    (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
    (a : MulAction G H2) (p : H2 → E)
    (hq : letI := a;IsQuotientCoveringMap p G)
    (hmetric : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
      ∀y∈V,∀z∈V,@dist E H.metric.toDist (p y) (p z)=dist y z)
    (U : Set E) (hdU : d.image⊆U) (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
    (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
    (hr : r.2≠1) (hpunct : h (1,1)=r)
    (hcore : h '' ((fun x : U => (e x).val) '' {x : U | x.val∈d.image})=
      {z : Circle×Circle | z.2=1})
    (f : {x : U // x.val∉d.image} ≃ₜ ActualPuncturedCylinder)
    (q : {z : Circle // z≠1} ≃ₜ ℝ)
    (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
      (f x).val=(r.1⁻¹*(h (e x.val).val).1,
        q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
    (b : MulAction K C) (cov : C → {x : U // x.val∉d.image})
    (hcov : letI := b;IsQuotientCoveringMap cov K) [SimplyConnectedSpace C]
    (o : cov ⁻¹' {f.symm actualPantsBase}) (lift : C(C,H2))
    (hcomm : ∀z,p (lift z)=(cov z).val.val) (ι : K →* G)
    (haction : ∀k z,lift (@SMul.smul K C b.toSMul k z)=
      @SMul.smul G H2 a.toSMul (ι k) (lift z)) :
    let inc : C({x : U // x.val∉d.image},E) :=
      ⟨fun x => x.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
    let chart : C(ActualPuncturedCylinder,{x : U // x.val∉d.image}) :=
      ⟨f.symm,f.symm.continuous⟩
    ∃ B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,∀i : Fin 2,
      let ε : ℝ := if i=0 then -1 else 1
      let hε : ε≠0 := by dsimp [ε];split <;> norm_num
      let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
      let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
      let xo := hcov.isCoveringMap.monodromy stem o
      let x := lift xo.val
      let hx : p x=inc (f.symm (actualPantsLevelPoint ε hε)) :=
        (hcomm xo.val).trans (congrArg inc xo.property)
      let β := (actualPantsHorizontalLoop ε hε).map (inc.continuous.comp f.symm.continuous)
      let δ := ι (B (FreeGroup.of i)).unop
      let D := connectedComponentIn (p ⁻¹' {z : E | z∈U ∧ z∉d.image}) (lift o.val)
      ∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
        range α⊆frontier D ∧ p '' range α=d.image ∧
        (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
        (fun z => @SMul.smul G H2 a.toSMul δ z) '' D=D ∧
        ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
         (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
        (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
          ∃n : ℤ,g=δ^n) ∧
        (@SMul.smul K C b.toSMul (B (FreeGroup.of i)).unop xo.val=
          (hcov.isCoveringMap.monodromy loop xo).val) ∧
        @SMul.smul G H2 a.toSMul δ x=
          (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
  have hLiteral {E G : Type} [TopologicalSpace E]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
      (H : ClosedHyperbolicMetric E) (d : Curve E)
      (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
      (a : MulAction G H2) (p : H2 → E)
      (hq : letI := a;IsQuotientCoveringMap p G)
      (hmetric : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
        ∀y∈V,∀z∈V,@dist E H.metric.toDist (p y) (p z)=dist y z)
      (U : Set E) (hdU : d.image⊆U) (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
      (h : (Circle×Circle) ≃ₜ (Circle×Circle)) (r : Circle×Circle)
      (hr : r.2≠1) (hpunct : h (1,1)=r)
      (hcore : h '' ((fun x : U => (e x).val) '' {x : U | x.val∈d.image})=
        {z : Circle×Circle | z.2=1})
      (f : {x : U // x.val∉d.image} ≃ₜ ActualPuncturedCylinder)
      (q : {z : Circle // z≠1} ≃ₜ ℝ)
      (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
        (f x).val=(r.1⁻¹*(h (e x.val).val).1,
          q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
      (ε : ℝ) (hε : ε≠0) :
      let j : C({x : U // x.val∉d.image},E) :=
        ⟨fun x => x.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
      let β := (actualPantsHorizontalLoop ε hε).map (j.continuous.comp f.symm.continuous)
      ∀x : H2,∀hx : p x=j (f.symm (actualPantsLevelPoint ε hε)),
        let C := connectedComponentIn (p ⁻¹' {z : E | z∈U ∧ z∉d.image}) x
        ∃δ : G,∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
          range α⊆frontier C ∧ p '' range α=d.image ∧
          (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
          (fun z => @SMul.smul G H2 a.toSMul δ z) '' C=C ∧
          ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
           (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
          (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
            ∃n : ℤ,g=δ^n) ∧
          @SMul.smul G H2 a.toSMul δ x=
            (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
    have hSource {E G : Type} [TopologicalSpace E]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [Group G]
        (H : ClosedHyperbolicMetric E) (d : Curve E)
        (hdgeo : letI : MetricSpace E:=H.metric;IsClosedGeodesic d.image)
        (a : MulAction G H2) (p : H2 → E)
        (hq : letI := a;IsQuotientCoveringMap p G)
        (hmetric : ∀x : H2,∃V : Set H2,IsOpen V ∧ x∈V ∧
          ∀y∈V,∀z∈V,@dist E H.metric.toDist (p y) (p z)=dist y z)
        (U : Set E) (hdU : d.image⊆U) (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
        (h : (Circle×Circle) ≃ₜ (Circle×Circle))
        (hpunct : (h (1,1)).2≠1)
        (hcore : h '' ((fun x : U => (e x).val) '' {x : U | x.val∈d.image})=
          {z : Circle×Circle | z.2=1})
        (q : {z : Circle // z≠1} ≃ₜ ℝ)
        (s : Circle) (hs : s≠(h (1,1)).2) (hsone : s≠1) (ζ : Circle) :
        ∃f : C(Circle,E),
          (∀z,∃hz : f z∈U,h (e ⟨f z,hz⟩).val=(-ζ*z,s)) ∧
          ∀x : H2,∀hx : p x=f 1,
          let C := connectedComponentIn (p ⁻¹' {z : E | z∈U ∧ z∉d.image}) x
          ∃δ : G,∃α : C(ℝ,H2),Isometry α ∧ ∃T : ℝ,0<T ∧
            range α⊆frontier C ∧
            p '' range α=d.image ∧
            (∀s t : ℝ,p (α s)=p (α t) ↔ ∃k : ℤ,s=t+k*T) ∧
            (fun z => @SMul.smul G H2 a.toSMul δ z) '' C=C ∧
            ((∀t : ℝ,@SMul.smul G H2 a.toSMul δ (α t)=α (t+T)) ∨
             (∀t : ℝ,@SMul.smul G H2 a.toSMul δ⁻¹ (α t)=α (t+T))) ∧
            (∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
              ∃n : ℤ,g=δ^n) ∧
            ∀β : Path (f 1) (f 1),
              (∀t : unitInterval,β t=f (Circle.exp (2*Real.pi*(t:ℝ)))) →
              @SMul.smul G H2 a.toSMul δ x=
                (hq.isCoveringMap.monodromy ⟦β⟧ ⟨x,hx⟩).val := by
      have hApproach {E : Type} [TopologicalSpace E] (U : Set E)
          (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)}) (D : Set E)
          (h : (Circle×Circle) ≃ₜ (Circle×Circle))
          (hpunct : (h (1,1)).2≠1)
          (hcore : h '' ((fun x : U => (e x).val) '' {x : U | x.val∈D})=
            {z : Circle×Circle | z.2=1})
          (q : {z : Circle // z≠1} ≃ₜ ℝ) (s : Circle) (hs : s≠(h (1,1)).2) (hsone : s≠1) :
          ∃ p : Path s 1,(∀ t,p t≠(h (1,1)).2) ∧ ∃ F : C(unitInterval×Circle,U),
            (∀ t z,h (e (F (t,z))).val=(z,p t)) ∧
            (∀ z,h (e (F (0,z))).val=(z,s)) ∧
            (∀ z,h (e (F (1,z))).val=(z,1)) ∧
            (∀ t,IsEmbedding (fun z : Circle => F (t,z))) ∧
            range (fun z : Circle => F (1,z))={x : U | x.val∈D} ∧
            (∀t : unitInterval,t<1 → ∀z : Circle,(F (t,z)).val∉D) := by
        classical
        have hApproach (r s : Circle) (hr : (1:Circle)≠r) (hs : s≠r) (hsone : s≠1)
            (e : {z : Circle // z≠r} ≃ₜ ℝ) :
            ∃ p : Path s 1,(∀t,p t≠r) ∧ (∀t : unitInterval,t<1 → p t≠1) := by
          let a := e ⟨s,hs⟩
          let b := e ⟨1,hr⟩
          let f (t : unitInterval) : Circle :=
            (e.symm ((1-(t:ℝ))*a+(t:ℝ)*b)).val
          have hcont : Continuous f := by dsimp [f];fun_prop
          have hzero : f 0=s := by simp [f,a]
          have hone : f 1=1 := by simp [f,b]
          let p : Path s 1 := ⟨⟨f,hcont⟩,hzero,hone⟩
          refine ⟨p,fun t => (e.symm _).property,?_⟩
          intro t ht he
          have hh : e.symm ((1-(t:ℝ))*a+(t:ℝ)*b)=⟨1,hr⟩ := Subtype.ext he
          have hlin : (1-(t:ℝ))*a+(t:ℝ)*b=b := by
            have h := congrArg e hh
            simpa [b] using h
          have hz : (1-(t:ℝ))*(a-b)=0 := by nlinarith [hlin]
          have htn : 1-(t:ℝ)≠0 := by
            have hlt : (t:ℝ)<1 := ht
            linarith
          have hab : a=b := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left htn)
          have heq : (⟨s,hs⟩ : {z : Circle // z≠r})=⟨1,hr⟩ := e.injective hab
          exact hsone (congrArg Subtype.val heq)
        let r := (h (1,1)).2
        have h1 : (1 : Circle)≠r := Ne.symm hpunct
        have hpath : ∃ p : Path s 1,(∀ t,p t≠r) ∧ (∀t : unitInterval,t<1 → p t≠1) := by
          let rot := Homeomorph.mulLeft r⁻¹
          have hi : ∀ z : Circle,z≠r ↔ rot z≠1 := by
            intro z
            change z≠r ↔ r⁻¹*z≠1
            simp only [ne_eq,inv_mul_eq_one]
            exact not_congr eq_comm
          let e : {z : Circle // z≠r} ≃ₜ ℝ := (rot.subtype hi).trans q
          exact hApproach r s h1 hs hsone e
        obtain ⟨p,hp,havoid⟩ := hpath
        have hr : (h (1,1)).2=r := rfl
        have hfamily : ∃ F : C(unitInterval×Circle,U),
            (∀ t z,h (e (F (t,z))).val=(z,p t)) ∧
            (∀ z,h (e (F (0,z))).val=(z,s)) ∧
            (∀ z,h (e (F (1,z))).val=(z,1)) ∧
            ∀ t,IsEmbedding (fun z : Circle => F (t,z)) := by
          have hn (t : unitInterval) (z : Circle) : h.symm (z,p t)≠(1,1) := by
            intro he
            have hh := congrArg h he
            have hs : p t=r := by
              simpa [hr] using congrArg Prod.snd hh
            exact hp t hs
          let F : unitInterval×Circle → U := fun x => e.symm ⟨h.symm (x.2,p x.1),hn x.1 x.2⟩
          have hF : Continuous F := by dsimp [F];fun_prop
          have heq (t : unitInterval) (z : Circle) : h (e (F (t,z))).val=(z,p t) := by simp [F]
          refine ⟨⟨F,hF⟩,heq,?_,?_,?_⟩
          · intro z;simpa using heq 0 z
          · intro z;simpa using heq 1 z
          · intro t
            letI : T2Space U := e.symm.t2Space
            have hc : Continuous (fun z : Circle => F (t,z)) := hF.comp (continuous_const.prodMk continuous_id)
            apply (hc.isClosedEmbedding ?_).isEmbedding
            intro z w he
            have hhe := congrArg (fun x : U => h (e x).val) he
            rw [heq,heq] at hhe
            exact congrArg Prod.fst hhe
        obtain ⟨F,hF,hFzero,hFone,hFemb⟩ := hfamily
        refine ⟨p,hp,F,hF,hFzero,hFone,hFemb,?_,?_⟩
        · ext x
          constructor
          · rintro ⟨z,rfl⟩
            have hm : h (e (F (1,z))).val∈h '' ((fun x : U => (e x).val) '' {x : U | x.val∈D}) := by
              rw [hcore,hFone];rfl
            obtain ⟨w,⟨u,hu,rfl⟩,he⟩ := hm
            have hue : u=F (1,z) := e.injective (Subtype.ext (h.injective he))
            simpa [hue] using hu
          · intro hx
            have hm : h (e x).val∈{z : Circle×Circle | z.2=1} := by
              rw [←hcore]
              exact ⟨(e x).val,⟨x,hx,rfl⟩,rfl⟩
            refine ⟨(h (e x).val).1,?_⟩
            apply e.injective
            apply Subtype.ext
            apply h.injective
            rw [hFone]
            exact Prod.ext rfl hm.symm
        · intro t ht z hzD
          have hm : h (e (F (t,z))).val∈{z : Circle×Circle | z.2=1} := by
            rw [←hcore]
            exact ⟨(e (F (t,z))).val,⟨F (t,z),hzD,rfl⟩,rfl⟩
          rw [hF] at hm
          exact havoid t ht hm
      have hSameParam {E : Type} [TopologicalSpace E] (m : MetricSpace E)
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
      letI : MetricSpace E := H.metric.replaceTopology H.compatible.symm
      obtain ⟨path,hpath,F,hF,hF0,hF1,hFemb,hFrange,hFavoid⟩ :=
        hApproach U e d.image h hpunct hcore q s hs hsone
      let rot := Homeomorph.mulLeft (-ζ)
      let A : C(Circle×unitInterval,E) :=
        ⟨fun zt => (F (zt.2,rot zt.1)).val,
          continuous_subtype_val.comp (F.continuous.comp
            (continuous_snd.prodMk (rot.continuous.comp continuous_fst)))⟩
      let b : Curve E := ⟨fun z => A (z,1),
        IsEmbedding.subtypeVal.comp ((hFemb 1).comp rot.isEmbedding)⟩
      have hbim : b.image=d.image := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          have hz : F (1,rot z)∈{x : U | x.val∈d.image} := by
            rw [←hFrange];exact ⟨rot z,rfl⟩
          exact hz
        · intro hy
          have hUy : y∈U := hdU hy
          obtain ⟨z,hz⟩ := (show (⟨y,hUy⟩ : U)∈range (fun z => F (1,z)) by rw [hFrange];exact hy)
          exact ⟨rot.symm z,by
            change (F (1,rot (rot.symm z))).val=y
            rw [rot.apply_symm_apply]
            exact congrArg Subtype.val hz⟩
      have hbgeo : IsClosedGeodesic b.image := by rw [hbim];exact hdgeo
      obtain ⟨g,hg,hbg,hggeo,hgim⟩ := embedded_geodesic_image_has_parametrized_representative H b hbgeo
      let bf : C(Circle,E) := ⟨b.map,b.embedded.continuous⟩
      have him : range bf=range g := hgim.symm
      have hbparam : IsParametrizedClosedGeodesic bf :=
        hSameParam (H.metric.replaceTopology H.compatible.symm) bf g b.embedded hg him hggeo
      have hAin : ∀t : unitInterval,t<1 → ∀z : Circle,A (z,t)∈{y : E | y∈U ∧ y∉d.image} := by
        intro t ht z
        exact ⟨(F (t,rot z)).property,hFavoid t ht (rot z)⟩
      have hAout : ∀z : Circle,A (z,1)∉{y : E | y∈U ∧ y∉d.image} := by
        intro z hz
        exact hz.2 (by rw [←hbim];exact mem_range_self z)
      let f : C(Circle,E) := ⟨fun z => A (z,0),A.continuous.comp (continuous_id.prodMk continuous_const)⟩
      refine ⟨f,?_,?_⟩
      · intro z
        exact ⟨(F (0,rot z)).property,hF0 (rot z)⟩
      · intro x hx
        obtain ⟨δ,α,hα,T,hT,hfront,himage,hfibre,hpreserve,hshift,hmono⟩ :=
          hCut a p hq hmetric {z : E | z∈U ∧ z∉d.image} A hAin hAout hbparam b.embedded x hx
        have hprimitive : ∀g : G,(fun z => @SMul.smul G H2 a.toSMul g z) '' range α=range α →
            ∃n : ℤ,g=δ^n := by
          rcases hshift with hpositive | hnegative
          · exact hPrimitive a p hq hmetric α hα T hT hfibre δ hpositive
          · intro g hg
            obtain ⟨n,hn⟩ := hPrimitive a p hq hmetric α hα T hT hfibre δ⁻¹ hnegative g hg
            refine ⟨-n,?_⟩
            simpa only [inv_zpow,zpow_neg] using hn
        exact ⟨δ,α,hα,T,hT,hfront,himage.trans hbim,hfibre,hpreserve,hshift,hprimitive,hmono⟩
    have hCoordinate {E : Type} [TopologicalSpace E] (U D : Set E)
        (e : U ≃ₜ {z : Circle×Circle // z≠(1,1)})
        (h : (Circle×Circle) ≃ₜ (Circle×Circle))
        (r : Circle×Circle) (hr : r.2≠1)
        (hcore : h '' ((fun x : U => (e x).val) '' {x : U | x.val∈D})=
          {z : Circle×Circle | z.2=1})
        (f : {x : U // x.val∉D} ≃ₜ {z : Circle×ℝ // z≠(1,0)})
        (q : {z : Circle // z≠1} ≃ₜ ℝ)
        (hf : ∀x,∃hx : (h (e x.val).val).2≠1,
          (f x).val=(r.1⁻¹*(h (e x.val).val).1,
            q ⟨(h (e x.val).val).2,hx⟩-q ⟨r.2,hr⟩))
        (ε : ℝ) (hε : ε≠0) (s : Circle) (hs : s≠1)
        (hsval : q ⟨s,hs⟩=q ⟨r.2,hr⟩+ε)
        (b : C(Circle,E))
        (hb : ∀z,∃hz : b z∈U,h (e ⟨b z,hz⟩).val=(-r.1*z,s)) :
        ∀z : Circle,
          (f.symm ⟨(-(1:Circle)*z,ε),by intro he;exact hε (congrArg Prod.snd he)⟩).val.val=b z := by
      intro z
      obtain ⟨hz,hcoord⟩ := hb z
      have hnot : b z∉D := by
        intro hD
        have hm : h (e ⟨b z,hz⟩).val∈{w : Circle×Circle | w.2=1} := by
          rw [←hcore]
          exact ⟨(e ⟨b z,hz⟩).val,⟨⟨b z,hz⟩,hD,rfl⟩,rfl⟩
        rw [hcoord] at hm
        exact hs hm
      let x : {x : U // x.val∉D} := ⟨⟨b z,hz⟩,hnot⟩
      obtain ⟨hne,hpoint⟩ := hf x
      have hfx : f x=⟨(-(1:Circle)*z,ε),by intro he;exact hε (congrArg Prod.snd he)⟩ := by
        apply Subtype.ext
        rw [hpoint]
        apply Prod.ext
        · change r.1⁻¹*(h (e ⟨b z,hz⟩).val).1=-(1:Circle)*z
          rw [hcoord]
          have hneg : -r.1=r.1*-(1:Circle) := by
            apply Subtype.ext
            simp
          rw [hneg,←mul_assoc,←mul_assoc,inv_mul_cancel,one_mul]
        · change q ⟨(h (e ⟨b z,hz⟩).val).2,hne⟩-q ⟨r.2,hr⟩=ε
          have he : (⟨(h (e ⟨b z,hz⟩).val).2,hne⟩ : {w : Circle // w≠1})=⟨s,hs⟩ :=
            Subtype.ext (congrArg Prod.snd hcoord)
          rw [he,hsval]
          ring
      have he := congrArg (fun w : {x : U // x.val∉D} => w.val.val)
        (congrArg f.symm hfx)
      simpa [x] using he.symm
    let j : C({x : U // x.val∉d.image},E) :=
      ⟨fun x => x.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
    let β := (actualPantsHorizontalLoop ε hε).map (j.continuous.comp f.symm.continuous)
    let s : Circle := (q.symm (q ⟨r.2,hr⟩+ε)).val
    have hsone : s≠1 := (q.symm _).property
    have hsval : q ⟨s,hsone⟩=q ⟨r.2,hr⟩+ε := q.apply_symm_apply _
    have hsr : s≠r.2 := by
      intro he
      have hqeq := congrArg q (show (⟨s,hsone⟩ : {z : Circle // z≠1})=⟨r.2,hr⟩ from Subtype.ext he)
      rw [hsval] at hqeq
      exact hε (by linarith)
    have hsp : s≠(h (1,1)).2 := by rw [hpunct];exact hsr
    have hp2 : (h (1,1)).2≠1 := by rw [hpunct];exact hr
    obtain ⟨b,hb,haxes⟩ := hSource H d hdgeo a p hq hmetric U hdU e h hp2 hcore q s hsp hsone r.1
    have hcoord := hCoordinate U d.image e h r hr hcore f q hf ε hε s hsone hsval b hb
    have hfoot : j (f.symm (actualPantsLevelPoint ε hε))=b 1 := by
      have hh := hcoord 1
      simpa [actualPantsLevelPoint,mul_one,j] using hh
    dsimp only
    intro x hx
    have hxb : p x=b 1 := hx.trans hfoot
    obtain ⟨δ,α,hα,T,hT,hfront,himage,hfibre,hpreserve,hshift,hprimitive,hmono⟩ := haxes x hxb
    let β' : Path (b 1) (b 1) := β.cast hfoot.symm hfoot.symm
    have hβ : ∀t : unitInterval,β' t=b (Circle.exp (2*Real.pi*(t:ℝ))) := by
      intro t
      exact hcoord _
    have hm := hmono β' hβ
    change @SMul.smul G H2 a.toSMul δ x=
      hq.isCoveringMap.liftPath β x (β.source.trans hx.symm) 1 at hm
    exact ⟨δ,α,hα,T,hT,hfront,himage,hfibre,hpreserve,hshift,hprimitive,hm⟩
  have hAmbient {U C E P K G : Type} [TopologicalSpace U] [TopologicalSpace C]
      [TopologicalSpace E] [TopologicalSpace P] [Group K] [Group G]
      (b : MulAction K C) (q : C → U)
      (hq : letI := b; IsQuotientCoveringMap q K) [SimplyConnectedSpace C]
      (a : MulAction G P) (p : P → E)
      (hp : letI := a; IsQuotientCoveringMap p G)
      (f : U ≃ₜ ActualPuncturedCylinder) (o : q ⁻¹' {f.symm actualPantsBase})
      (j : C(C,P)) (inc : C(U,E)) (hcomm : ∀z,p (j z)=inc (q z))
      (ι : K →* G)
      (haction : ∀k z,j (@SMul.smul K C b.toSMul k z)=@SMul.smul G P a.toSMul (ι k) (j z)) :
      letI := b
      let g : C(ActualPuncturedCylinder,U) := ⟨f.symm,f.symm.continuous⟩
      ∃ e : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,
        ∀ i : Fin 2,
          let ε : ℝ := if i=0 then -1 else 1
          let hε : ε≠0 := by dsimp [ε];split <;> norm_num
          let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ g
          let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ g
          let x := hq.isCoveringMap.monodromy stem o
          (@SMul.smul K C b.toSMul (e (FreeGroup.of i)).unop x.val =
            (hq.isCoveringMap.monodromy loop x).val) ∧
          @SMul.smul G P a.toSMul (ι (e (FreeGroup.of i)).unop) (j x.val) =
            (hp.isCoveringMap.monodromy (loop.map inc)
              ⟨j x.val,(hcomm x.val).trans (congrArg inc x.property)⟩).val := by
    have hBasis {U C K : Type} [TopologicalSpace U] [TopologicalSpace C]
        [Group K] (a : MulAction K C) (q : C → U)
        (hq : letI := a; IsQuotientCoveringMap q K) [SimplyConnectedSpace C]
        (f : U ≃ₜ ActualPuncturedCylinder) (o : q ⁻¹' {f.symm actualPantsBase}) :
        letI := a
        let g : C(ActualPuncturedCylinder,U) := ⟨f.symm,f.symm.continuous⟩
        ∃ e : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ,
          ∀ i : Fin 2,
            let ε : ℝ := if i=0 then -1 else 1
            let hε : ε≠0 := by dsimp [ε]; split <;> norm_num
            let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ g
            let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ g
            @SMul.smul K C a.toSMul (e (FreeGroup.of i)).unop
                (hq.isCoveringMap.monodromy stem o).val =
              (hq.isCoveringMap.monodromy loop (hq.isCoveringMap.monodromy stem o)).val := by
      have hwhisker {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
          (a : MulAction G P) (p : P → E)
          (hq : letI := a;IsQuotientCoveringMap p G)
          {u v : E} (stem : Path.Homotopic.Quotient u v)
          (loop : Path.Homotopic.Quotient v v) (o : p ⁻¹' {u}) (δ : G)
       :
          (@SMul.smul G P a.toSMul δ o.val=
            (hq.isCoveringMap.monodromy (stem.trans (loop.trans stem.symm)) o).val) ↔
          (@SMul.smul G P a.toSMul δ (hq.isCoveringMap.monodromy stem o).val=
            (hq.isCoveringMap.monodromy loop (hq.isCoveringMap.monodromy stem o)).val) := by
        have hForward {P E G : Type} [TopologicalSpace P] [TopologicalSpace E] [Group G]
            (a : MulAction G P) (p : P → E)
            (hq : letI := a;IsQuotientCoveringMap p G)
            {u v : E} (stem : Path.Homotopic.Quotient u v)
            (loop : Path.Homotopic.Quotient v v) (o : p ⁻¹' {u}) (δ : G)
            (hδ : @SMul.smul G P a.toSMul δ (hq.isCoveringMap.monodromy stem o).val=
              (hq.isCoveringMap.monodromy loop (hq.isCoveringMap.monodromy stem o)).val) :
            @SMul.smul G P a.toSMul δ o.val=
              (hq.isCoveringMap.monodromy (stem.trans (loop.trans stem.symm)) o).val := by
          letI := a
          have hComm {u v : E} (γ : Path.Homotopic.Quotient u v) (o : p ⁻¹' {u}) (δ : G) :
              (hq.isCoveringMap.monodromy γ
                ⟨@SMul.smul G P a.toSMul δ o.val,(hq.map_smul δ).trans o.property⟩).val=
              @SMul.smul G P a.toSMul δ (hq.isCoveringMap.monodromy γ o).val := by
            obtain ⟨γ⟩ := γ
            let L := hq.isCoveringMap.liftPath γ o.val (γ.source.trans o.property.symm)
            have heq : (fun t : unitInterval => δ • L t)=
                hq.isCoveringMap.liftPath γ (δ • o.val)
                  (γ.source.trans ((hq.map_smul δ).trans o.property).symm) := by
              apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
              refine ⟨(hq.continuous_const_smul δ).comp L.continuous,?_,?_⟩
              · funext t
                exact (hq.map_smul δ).trans (congrFun (hq.isCoveringMap.liftPath_lifts γ o.val _) t)
              · change δ • hq.isCoveringMap.liftPath γ o.val _ 0=δ • o.val
                rw [hq.isCoveringMap.liftPath_zero]
            exact (congrFun heq 1).symm
          let δo : p ⁻¹' {u} := ⟨δ • o.val,(hq.map_smul δ).trans o.property⟩
          let total := stem.trans (loop.trans stem.symm)
          have hpath : total.trans stem=stem.trans loop := by
            simp [total,Path.Homotopic.Quotient.trans_assoc]
          have he : δo=hq.isCoveringMap.monodromy total o := by
            apply (hq.isCoveringMap.monodromy_bijective stem).injective
            calc
              hq.isCoveringMap.monodromy stem δo=
                  hq.isCoveringMap.monodromy loop (hq.isCoveringMap.monodromy stem o) := by
                apply Subtype.ext
                exact (hComm stem o δ).trans hδ
              _=hq.isCoveringMap.monodromy stem (hq.isCoveringMap.monodromy total o) := by
                rw [←hq.isCoveringMap.monodromy_trans_apply total stem,hpath,
                  hq.isCoveringMap.monodromy_trans_apply stem loop]
          exact congrArg Subtype.val he
        letI := a
        have hComm {u v : E} (γ : Path.Homotopic.Quotient u v) (o : p ⁻¹' {u}) (δ : G) :
            (hq.isCoveringMap.monodromy γ
              ⟨@SMul.smul G P a.toSMul δ o.val,(hq.map_smul δ).trans o.property⟩).val=
            @SMul.smul G P a.toSMul δ (hq.isCoveringMap.monodromy γ o).val := by
          obtain ⟨γ⟩ := γ
          let L := hq.isCoveringMap.liftPath γ o.val (γ.source.trans o.property.symm)
          have heq : (fun t : unitInterval => δ • L t)=
              hq.isCoveringMap.liftPath γ (δ • o.val)
                (γ.source.trans ((hq.map_smul δ).trans o.property).symm) := by
            apply (hq.isCoveringMap.eq_liftPath_iff _).mpr
            refine ⟨(hq.continuous_const_smul δ).comp L.continuous,?_,?_⟩
            · funext t
              exact (hq.map_smul δ).trans (congrFun (hq.isCoveringMap.liftPath_lifts γ o.val _) t)
            · change δ • hq.isCoveringMap.liftPath γ o.val _ 0=δ • o.val
              rw [hq.isCoveringMap.liftPath_zero]
          exact (congrFun heq 1).symm
        constructor
        · intro hδ
          let δo : p ⁻¹' {u} := ⟨δ • o.val,(hq.map_smul δ).trans o.property⟩
          let total := stem.trans (loop.trans stem.symm)
          have hpath : total.trans stem=stem.trans loop := by
            simp [total,Path.Homotopic.Quotient.trans_assoc]
          have hb : δo=hq.isCoveringMap.monodromy total o := Subtype.ext hδ
          have hh := congrArg (hq.isCoveringMap.monodromy stem) hb
          have ht : hq.isCoveringMap.monodromy stem (hq.isCoveringMap.monodromy total o)=
              hq.isCoveringMap.monodromy loop (hq.isCoveringMap.monodromy stem o) := by
            rw [←hq.isCoveringMap.monodromy_trans_apply total stem,hpath,
              hq.isCoveringMap.monodromy_trans_apply stem loop]
          exact (hComm stem o δ).symm.trans (congrArg Subtype.val (hh.trans ht))
        · exact hForward a p hq stem loop o δ
      letI := a
      dsimp only
      let g : C(ActualPuncturedCylinder,U) := ⟨f.symm,f.symm.continuous⟩
      let F := FundamentalGroupoid.map g
      let Equ := FundamentalGroupoidFunctor.equivOfHomotopyEquiv f.symm.toHomotopyEquiv
      have hb : Function.Bijective (FundamentalGroup.map g actualPantsBase) := by
        letI : F.Full := Equ.full_functor
        letI : F.Faithful := Equ.faithful_functor
        exact ⟨F.map_injective,F.map_surjective⟩
      let β := MulEquiv.ofBijective (FundamentalGroup.map g actualPantsBase) hb
      obtain ⟨α,hα₀,hα₁⟩ := actual_punctured_cylinder_boundary_loops_fundamental_group_free_basis
      let κ := hq.fundamentalGroupEquiv o
      refine ⟨α.trans (β.trans κ),?_⟩
      intro i
      apply (hwhisker a q hq _ _ o _).mp
      have hi : α (FreeGroup.of i) = FundamentalGroup.fromPath
          ⟦actualPantsBoundaryLoop (if i=0 then -1 else 1) (by split <;> norm_num)⟧ := by
        fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] <;> assumption
      change @SMul.smul K C a.toSMul (κ (β (α (FreeGroup.of i)))).unop o.val = _
      rw [hi]
      have he := hq.unop_fundamentalGroupToMulOpposite_smul (e := o)
        (γ := β (FundamentalGroup.fromPath
          ⟦actualPantsBoundaryLoop (if i=0 then -1 else 1) (by split <;> norm_num)⟧))
      change @SMul.smul K C a.toSMul
          (κ (β (FundamentalGroup.fromPath
            ⟦actualPantsBoundaryLoop (if i=0 then -1 else 1) (by split <;> norm_num)⟧))).unop o.val =
          (hq.isCoveringMap.monodromy
            ⟦(actualPantsBoundaryLoop (if i=0 then -1 else 1) (by split <;> norm_num)).map
              g.continuous⟧ o).val at he
      convert he using 1
      congr 2
      change ⟦((actualPantsStem (if i=0 then -1 else 1) _).map g.continuous).trans
        (((actualPantsHorizontalLoop (if i=0 then -1 else 1) _).map g.continuous).trans
          ((actualPantsStem (if i=0 then -1 else 1) _).map g.continuous).symm)⟧ = _
      congr 1
      simp only [actualPantsBoundaryLoop, Path.map_trans, Path.map_symm]
    have hNat {U C E P : Type} [TopologicalSpace U] [TopologicalSpace C]
        [TopologicalSpace E] [TopologicalSpace P]
        (p : P → E) (q : C → U) (hp : IsCoveringMap p) (hq : IsCoveringMap q)
        (inc : C(U,E)) (j : C(C,P)) (hcomm : ∀ z,p (j z)=inc (q z))
        {v : U} (o : q ⁻¹' {v}) (γ : Path.Homotopic.Quotient v v) :
        (hp.monodromy (γ.map inc)
          ⟨j o.val,(hcomm o.val).trans (congrArg inc o.property)⟩).val =
          j (hq.monodromy γ o).val := by
      obtain ⟨γ⟩ := γ
      let L := hq.liftPath γ o.val (γ.source.trans o.property.symm)
      have heq : j ∘ L=hp.liftPath (γ.map inc.continuous) (j o.val)
          ((γ.map inc.continuous).source.trans
            ((hcomm o.val).trans (congrArg inc o.property)).symm) := by
        apply (hp.eq_liftPath_iff _).mpr
        refine ⟨j.continuous.comp L.continuous,?_,?_⟩
        · funext t
          change p (j (L t))=inc (γ t)
          rw [hcomm]
          exact congrArg inc (congrFun (hq.liftPath_lifts γ o.val _) t)
        · change j (L 0)=j o.val
          rw [hq.liftPath_zero]
      exact (congrFun heq 1).symm
    dsimp only
    obtain ⟨e,he⟩ := hBasis b q hq f o
    refine ⟨e,?_⟩
    intro i
    have hi := he i
    refine ⟨hi,?_⟩
    rw [←haction,hi]
    exact (hNat p q hp.isCoveringMap hq.isCoveringMap inc j hcomm _ _).symm
  dsimp only
  let inc : C({x : U // x.val∉d.image},E) :=
    ⟨fun x => x.val.val,continuous_subtype_val.comp continuous_subtype_val⟩
  let chart : C(ActualPuncturedCylinder,{x : U // x.val∉d.image}) :=
    ⟨f.symm,f.symm.continuous⟩
  obtain ⟨B,hB⟩ := hAmbient b cov hcov a p hq f o lift inc hcomm ι haction
  refine ⟨B,?_⟩
  intro i
  let ε : ℝ := if i=0 then -1 else 1
  have hε : ε≠0 := by dsimp [ε];split <;> norm_num
  let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
  let xo := hcov.isCoveringMap.monodromy stem o
  have hx : p (lift xo.val)=inc (f.symm (actualPantsLevelPoint ε hε)) :=
    (hcomm xo.val).trans (congrArg inc xo.property)
  obtain ⟨δ,α,hα,T,hT,hfront,himage,hfibre,hpres,hshift,hprim,hmono⟩ :=
    hLiteral H d hdgeo a p hq hmetric U hdU e h r hr hpunct hcore f q hf ε hε (lift xo.val) hx
  have hgen := (hB i).2
  have hcutmon := (hB i).1
  have heq : δ=ι (B (FreeGroup.of i)).unop := by
    letI := a
    letI := hq.isCancelSMul
    apply IsCancelSMul.right_cancel' δ (ι (B (FreeGroup.of i)).unop) (lift xo.val)
    have hpath : Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart) inc =
        ⟦(actualPantsHorizontalLoop ε hε).map (inc.continuous.comp f.symm.continuous)⟧ := by
      change ⟦((actualPantsHorizontalLoop ε hε).map chart.continuous).map inc.continuous⟧ = _
      congr 1
    rw [hpath] at hgen
    exact hmono.trans hgen.symm
  subst δ
  have hset : range lift⊆p ⁻¹' {z : E | z∈U ∧ z∉d.image} := by
    rintro z ⟨v,rfl⟩
    change p (lift v)∈{z : E | z∈U ∧ z∉d.image}
    rw [hcomm]
    exact ⟨(cov v).val.property,(cov v).property⟩
  have hpre : IsPreconnected (range lift) := by
    simpa only [image_univ] using isPreconnected_univ.image lift lift.continuous.continuousOn
  have hmem : lift xo.val∈connectedComponentIn
      (p ⁻¹' {z : E | z∈U ∧ z∉d.image}) (lift o.val) :=
    (hpre.subset_connectedComponentIn (mem_range_self o.val) hset) (mem_range_self xo.val)
  have hc := connectedComponentIn_eq hmem
  rw [←hc] at hfront hpres
  exact ⟨α,hα,T,hT,hfront,himage,hfibre,hpres,hshift,hprim,hcutmon,hmono⟩
end CurveComplex.Hyperbolic
