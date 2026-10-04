import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.ActualOriginalCutFrontierThreeOrbitExhaustion
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
open Set Topology
open scoped Pointwise UpperHalfPlane unitInterval
open CurveComplex CurveComplex.Hyperbolic
set_option maxHeartbeats 18000000
set_option maxRecDepth 10000
theorem actual_original_cut_primitive_boundary_axis_three_orbit_dictionary_source
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
    (x : H2) (hx : p x ∈ U \ d.image)
    (αc α₀ α₁ : ℝ → H2) (hαc : Isometry αc) (hα₀ : Isometry α₀) (hα₁ : Isometry α₁)
    (hcfront : range αc⊆frontier (connectedComponentIn (p ⁻¹' (U\d.image)) x))
    (h₀front : range α₀⊆frontier (connectedComponentIn (p ⁻¹' (U\d.image)) x))
    (h₁front : range α₁⊆frontier (connectedComponentIn (p ⁻¹' (U\d.image)) x))
    (hcimage : p '' range αc=c.image) (h₀image : p '' range α₀=d.image) (h₁image : p '' range α₁=d.image)
    (Tc T₀ T₁ : ℝ) (hTc : 0<Tc) (hT₀ : 0<T₀) (hT₁ : 0<T₁)
    (hcfibre : ∀s t : ℝ,p (αc s)=p (αc t) ↔ ∃n : ℤ,s=t+n*Tc)
    (h₀fibre : ∀s t : ℝ,p (α₀ s)=p (α₀ t) ↔ ∃n : ℤ,s=t+n*T₀)
    (h₁fibre : ∀s t : ℝ,p (α₁ s)=p (α₁ t) ↔ ∃n : ℤ,s=t+n*T₁)
    (hdist : letI := a
      ∀k : MulAction.stabilizer G (connectedComponentIn (p ⁻¹' (U\d.image)) x),
        (fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀≠range α₁) :
    letI := a
    let C := connectedComponentIn (p ⁻¹' (U\d.image)) x
    let K := MulAction.stabilizer G C
    frontier C=(⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range αc) ∪
      (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₀) ∪
      (⋃k : K,(fun z => @SMul.smul G H2 a.toSMul k.val z) '' range α₁) := by
  have hRecognizeC {K G P E : Type} [Group K] [Group G] [MetricSpace P]
      [TopologicalSpace E] [T2Space E]
      (a : MulAction G P) (ι : K →* G) (p : P → E) (hp : IsCoveringMap p)
      (hiso : ∀k : K,Isometry (fun z => @SMul.smul G P a.toSMul (ι k) z))
      (hproj : ∀k : K,∀z : P,p (@SMul.smul G P a.toSMul (ι k) z)=p z)
      (F : Set P) (A B : Set E) (hAB : Disjoint A B)
      (α βc β₀ β₁ : ℝ → P) (hα : Isometry α)
      (hβc : Isometry βc) (hβ₀ : Isometry β₀) (hβ₁ : Isometry β₁)
      (hfront : range α⊆F) (himage : p '' range α=A)
      (hc : p '' range βc=A) (h₀ : p '' range β₀=B) (h₁ : p '' range β₁=B)
      (T : ℝ) (hT : 0<T)
      (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
      (hcover : F=(⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range βc) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range β₀) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range β₁)) :
      ∃k : K,range α=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range βc := by
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
    have hA : p (α 0)∈A := himage ▸ ⟨α 0,mem_range_self 0,rfl⟩
    have hpoint := hfront (mem_range_self 0)
    rw [hcover] at hpoint
    rcases hpoint with (hpoint|hpoint)|hpoint
    · obtain ⟨k,_,⟨s,rfl⟩,hs⟩ := mem_iUnion.mp hpoint
      let γ : ℝ → P := fun t => @SMul.smul G P a.toSMul (ι k) (βc t)
      have hγ : Isometry γ := (hiso k).comp hβc
      have hγimage : p '' range γ⊆p '' range α := by
        rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
        rw [hproj,himage]
        exact hc ▸ ⟨βc s,mem_range_self s,rfl⟩
      have heq := hMeet p hp α γ hα hγ T hT hfibre hγimage
        ⟨α 0,⟨0,rfl⟩,⟨s,hs⟩⟩
      refine ⟨k,?_⟩
      rw [←range_comp]
      exact heq.symm
    · obtain ⟨k,_,⟨s,rfl⟩,hs⟩ := mem_iUnion.mp hpoint
      have hB : p (α 0)∈B := by
        rw [←hs,hproj]
        exact h₀ ▸ ⟨β₀ s,mem_range_self s,rfl⟩
      exact (disjoint_left.mp hAB hA hB).elim
    · obtain ⟨k,_,⟨s,rfl⟩,hs⟩ := mem_iUnion.mp hpoint
      have hB : p (α 0)∈B := by
        rw [←hs,hproj]
        exact h₁ ▸ ⟨β₁ s,mem_range_self s,rfl⟩
      exact (disjoint_left.mp hAB hA hB).elim
  have hRecognizeD {K G P E : Type} [Group K] [Group G] [MetricSpace P]
      [TopologicalSpace E] [T2Space E]
      (a : MulAction G P) (ι : K →* G) (p : P → E) (hp : IsCoveringMap p)
      (hiso : ∀k : K,Isometry (fun z => @SMul.smul G P a.toSMul (ι k) z))
      (hproj : ∀k : K,∀z : P,p (@SMul.smul G P a.toSMul (ι k) z)=p z)
      (F : Set P) (A B : Set E) (hAB : Disjoint A B)
      (α βc β₀ β₁ : ℝ → P) (hα : Isometry α)
      (hβc : Isometry βc) (hβ₀ : Isometry β₀) (hβ₁ : Isometry β₁)
      (hfront : range α⊆F) (himage : p '' range α=B)
      (hc : p '' range βc=A) (h₀ : p '' range β₀=B) (h₁ : p '' range β₁=B)
      (T : ℝ) (hT : 0<T)
      (hfibre : ∀s t : ℝ,p (α s)=p (α t) ↔ ∃n : ℤ,s=t+n*T)
      (hcover : F=(⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range βc) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range β₀) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range β₁)) :
      ∃k : K,range α=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range β₀ ∨
        range α=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' range β₁ := by
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
    have hB : p (α 0)∈B := himage ▸ ⟨α 0,mem_range_self 0,rfl⟩
    have hpoint := hfront (mem_range_self 0)
    rw [hcover] at hpoint
    rcases hpoint with (hpoint|hpoint)|hpoint
    · obtain ⟨k,_,⟨s,rfl⟩,hs⟩ := mem_iUnion.mp hpoint
      have hA : p (α 0)∈A := by
        rw [←hs,hproj]
        exact hc ▸ ⟨βc s,mem_range_self s,rfl⟩
      exact (disjoint_left.mp hAB hA hB).elim
    · obtain ⟨k,_,⟨s,rfl⟩,hs⟩ := mem_iUnion.mp hpoint
      let γ : ℝ → P := fun t => @SMul.smul G P a.toSMul (ι k) (β₀ t)
      have hγ : Isometry γ := (hiso k).comp hβ₀
      have hγimage : p '' range γ⊆p '' range α := by
        rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
        rw [hproj,himage]
        exact h₀ ▸ ⟨β₀ s,mem_range_self s,rfl⟩
      have heq := hMeet p hp α γ hα hγ T hT hfibre hγimage
        ⟨α 0,⟨0,rfl⟩,⟨s,hs⟩⟩
      refine ⟨k,Or.inl ?_⟩
      rw [←range_comp]
      exact heq.symm
    · obtain ⟨k,_,⟨s,rfl⟩,hs⟩ := mem_iUnion.mp hpoint
      let γ : ℝ → P := fun t => @SMul.smul G P a.toSMul (ι k) (β₁ t)
      have hγ : Isometry γ := (hiso k).comp hβ₁
      have hγimage : p '' range γ⊆p '' range α := by
        rintro _ ⟨_,⟨s,rfl⟩,rfl⟩
        rw [hproj,himage]
        exact h₁ ▸ ⟨β₁ s,mem_range_self s,rfl⟩
      have heq := hMeet p hp α γ hα hγ T hT hfibre hγimage
        ⟨α 0,⟨0,rfl⟩,⟨s,hs⟩⟩
      refine ⟨k,Or.inr ?_⟩
      rw [←range_comp]
      exact heq.symm
  have hReplace {K G P : Type} [Group K] [Group G]
      (a : MulAction G P) (ι : K →* G) (F Sc S₀ S₁ Tc T₀ T₁ : Set P)
      (hcover : F=(⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' Tc) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T₀) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T₁))
      (hc : ∃k : K,Sc=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' Tc)
      (h₀ : ∃k : K,S₀=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T₀ ∨
        S₀=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T₁)
      (h₁ : ∃k : K,S₁=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T₀ ∨
        S₁=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T₁)
      (hdist : ∀k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₀≠S₁) :
      F=(⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' Sc) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₀) ∪
        (⋃k : K,(fun z => @SMul.smul G P a.toSMul (ι k) z) '' S₁) := by
    have hOrbit {K G P : Type} [Group K] [Group G]
        (a : MulAction G P) (ι : K →* G) (S T : Set P) (k : K)
        (hS : S=(fun z => @SMul.smul G P a.toSMul (ι k) z) '' T) :
        (⋃g : K,(fun z => @SMul.smul G P a.toSMul (ι g) z) '' S)=
          ⋃g : K,(fun z => @SMul.smul G P a.toSMul (ι g) z) '' T := by
      letI := a
      change (⋃g : K,ι g • S)=⋃g : K,ι g • T
      have hS' : S=ι k • T := hS
      apply Subset.antisymm
      · intro z hz
        obtain ⟨g,hg⟩ := mem_iUnion.mp hz
        apply mem_iUnion.mpr
        refine ⟨g*k,?_⟩
        rw [map_mul,mul_smul,←hS']
        exact hg
      · intro z hz
        obtain ⟨g,hg⟩ := mem_iUnion.mp hz
        apply mem_iUnion.mpr
        refine ⟨g*k⁻¹,?_⟩
        rw [hS',←mul_smul,←map_mul]
        simpa only [mul_assoc,inv_mul_cancel,mul_one] using hg
    have hSame (T : Set P) (k₀ k₁ : K)
        (h₀ : S₀=(fun z => @SMul.smul G P a.toSMul (ι k₀) z) '' T)
        (h₁ : S₁=(fun z => @SMul.smul G P a.toSMul (ι k₁) z) '' T) : False := by
      apply hdist (k₁*k₀⁻¹)
      letI := a
      change ι (k₁*k₀⁻¹) • S₀=S₁
      have h₀' : S₀=ι k₀ • T := h₀
      have h₁' : S₁=ι k₁ • T := h₁
      rw [h₀',h₁',map_mul,map_inv,mul_smul,inv_smul_smul]
    obtain ⟨kc,hc⟩ := hc
    obtain ⟨k₀,h₀|h₀⟩ := h₀
    · obtain ⟨k₁,h₁|h₁⟩ := h₁
      · exact (hSame T₀ k₀ k₁ h₀ h₁).elim
      · rw [hOrbit a ι Sc Tc kc hc,hOrbit a ι S₀ T₀ k₀ h₀,hOrbit a ι S₁ T₁ k₁ h₁]
        exact hcover
    · obtain ⟨k₁,h₁|h₁⟩ := h₁
      · rw [hOrbit a ι Sc Tc kc hc,hOrbit a ι S₀ T₁ k₀ h₀,hOrbit a ι S₁ T₀ k₁ h₁,hcover]
        ac_rfl
      · exact (hSame T₁ k₀ k₁ h₀ h₁).elim
  letI := a
  intro C K
  let ι : K →* G := (MulAction.stabilizer G C).subtype
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
  have hproj : ∀k : K,∀z : H2,p (@SMul.smul G H2 a.toSMul (ι k) z)=p z :=
    fun k z=>hq.map_smul (ι k)
  obtain ⟨βc,β₀,β₁,hβc,hβ₀,hβ₁,hβcfront,hβ₀front,hβ₁front,hβcimage,hβ₀image,hβ₁image,hcoverβ,_⟩ :=
    actual_original_cut_frontier_three_orbit_exhaustion M H c d hc hcdiv hcgeo hdgeo hdnondiv hcd
      U V hU hV hUV hcover hfrontU hfrontV hdU a p hq hmetric x hx
  have hrecC := hRecognizeC a ι p hq.isCoveringMap hiso hproj (frontier C) c.image d.image hcd
    αc βc β₀ β₁ hαc hβc hβ₀ hβ₁ hcfront hcimage hβcimage hβ₀image hβ₁image Tc hTc hcfibre hcoverβ
  have hrec₀ := hRecognizeD a ι p hq.isCoveringMap hiso hproj (frontier C) c.image d.image hcd
    α₀ βc β₀ β₁ hα₀ hβc hβ₀ hβ₁ h₀front h₀image hβcimage hβ₀image hβ₁image T₀ hT₀ h₀fibre hcoverβ
  have hrec₁ := hRecognizeD a ι p hq.isCoveringMap hiso hproj (frontier C) c.image d.image hcd
    α₁ βc β₀ β₁ hα₁ hβc hβ₀ hβ₁ h₁front h₁image hβcimage hβ₀image hβ₁image T₁ hT₁ h₁fibre hcoverβ
  exact hReplace a ι (frontier C) (range αc) (range α₀) (range α₁)
    (range βc) (range β₀) (range β₁) hcoverβ hrecC hrec₀ hrec₁ hdist

