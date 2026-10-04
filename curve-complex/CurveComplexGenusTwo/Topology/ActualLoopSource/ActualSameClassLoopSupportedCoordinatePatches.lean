import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopFiniteEndpointContactGraphs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSmallSupportedLogarithmicPatch
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual source loop patches preserve both outer seams and time boundaries, with finite inner contacts. -/
theorem actual_same_class_loop_supported_coordinate_patches
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (hfinite : (crossings M a b).Finite) (p : S) (hp : p ∈ crossings M a b) :
    ∃ K : C(Interval × Interval,S),
      (∀ t, K (0,t)=b.val.map t) ∧
      (∀ τ s t, K (τ,s)=K (τ,t) → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      (∀ τ, K (τ,0)=a.val.map 0 ∧ K (τ,1)=a.val.map 0) ∧
      (∀ τ t, t≠0 → t≠1 → K (τ,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ t, t≠0 → t≠1 → K (1,t) ∉ a.val.image) ∧
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
      Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}) ∧
      (∀ q : U, q.val ∈ a.val.image ↔ (e q).val 1=0) ∧
    ∃ ε : ℝ, 0<ε ∧ ε<1/2 ∧
    ∃ l r : C(Interval,Interval),
      (∀ t, (l t:ℝ)=ε*(t:ℝ)) ∧ (∀ t, (r t:ℝ)=1-ε*(t:ℝ)) ∧
      (∀ τ t, K (τ,l t) ∈ U ∧ K (τ,r t) ∈ U) ∧
      (∀ t : Interval, (t:ℝ)≤ε ∨ 1-ε≤(t:ℝ) → b.val.map t ∉ crossings M a b) ∧
    ∃ L R : C(Interval × Interval,Plane),
      (∀ τ t (ht : K (τ,l t) ∈ U), L (τ,t)=(e ⟨K (τ,l t),ht⟩).val) ∧
      (∀ τ t (ht : K (τ,r t) ∈ U), R (τ,t)=(e ⟨K (τ,r t),ht⟩).val) ∧
      (∀ τ, L (τ,0)=0 ∧ R (τ,0)=0) ∧
      (∀ τ t, 0<t → L (τ,t)≠0 ∧ R (τ,t)≠0) ∧
      (∀ τ t, L (τ,t) 1=0 ↔ K (τ,l t) ∈ a.val.image) ∧
      (∀ τ t, R (τ,t) 1=0 ↔ K (τ,r t) ∈ a.val.image) ∧
    ∃ Λ₀ Λ₁ : C(Interval × Ioc (0:ℝ) 1,ℂ),
      (∀ z, Complex.exp (Λ₀ z)=ArcFinitePosition.planeComplexLinearEquiv
        (L (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))) ∧
      (∀ z, Complex.exp (Λ₁ z)=ArcFinitePosition.planeComplexLinearEquiv
        (R (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))) ∧
    ∃ n₀₀ n₀₁ n₁₀ n₁₁ : ℤ,
      (∀ t, (Λ₀ (0,t)).im ∈ Ioo ((n₀₀:ℝ)*Real.pi) (((n₀₀:ℝ)+1)*Real.pi)) ∧
      (∀ t, (Λ₀ (1,t)).im ∈ Ioo ((n₀₁:ℝ)*Real.pi) (((n₀₁:ℝ)+1)*Real.pi)) ∧
      (∀ t, (Λ₁ (0,t)).im ∈ Ioo ((n₁₀:ℝ)*Real.pi) (((n₁₀:ℝ)+1)*Real.pi)) ∧
      (∀ t, (Λ₁ (1,t)).im ∈ Ioo ((n₁₁:ℝ)*Real.pi) (((n₁₁:ℝ)+1)*Real.pi)) ∧
    ∃ levels₀ levels₁ : Finset ℤ,
    ∃ γ₀ : ↑levels₀ → C(Ioc (0:ℝ) 1,Interval),
    ∃ γ₁ : ↑levels₁ → C(Ioc (0:ℝ) 1,Interval),
      (∀ k t, 0<(γ₀ k t:ℝ) ∧ (γ₀ k t:ℝ)<1) ∧
      (∀ k t, 0<(γ₁ k t:ℝ) ∧ (γ₁ k t:ℝ)<1) ∧
      (∀ k, IsEmbedding (fun t => (γ₀ k t,t))) ∧
      (∀ k, IsEmbedding (fun t => (γ₁ k t,t))) ∧
      (∀ k j, k≠j → ∀ t, γ₀ k t≠γ₀ j t) ∧
      (∀ k j, k≠j → ∀ t, γ₁ k t≠γ₁ j t) ∧
      (∀ t (τ : Interval),
        (Complex.exp ((1-(τ:ℝ)) • Λ₀ (0,t)+(τ:ℝ) • Λ₀ (1,t))).im=0 ↔
          ∃ k : ↑levels₀, τ=γ₀ k t) ∧
      (∀ t (τ : Interval),
        (Complex.exp ((1-(τ:ℝ)) • Λ₁ (0,t)+(τ:ℝ) • Λ₁ (1,t))).im=0 ↔
          ∃ k : ↑levels₁, τ=γ₁ k t) ∧
    ∃ d₀ d₁ : ℝ, 0<d₀ ∧ d₀<1/2 ∧ 0<d₁ ∧ d₁<1/2 ∧
    ∃ c₀ c₁ : C(Interval,Interval),
    ∃ cp₀ cp₁ : C(Ioc (0:ℝ) 1,Ioc (0:ℝ) 1),
      (∀ t, (c₀ t:ℝ)=d₀*(t:ℝ)) ∧ (∀ t, (c₁ t:ℝ)=d₁*(t:ℝ)) ∧
      (∀ t, (cp₀ t).val=d₀*t.val) ∧ (∀ t, (cp₁ t).val=d₁*t.val) ∧
    ∃ P₀ P₁ : C((Interval × Interval) × Interval,Plane),
      (∀ s τ, P₀ ((s,τ),0)=0 ∧ P₁ ((s,τ),0)=0) ∧
      (∀ τ t, P₀ ((0,τ),t)=L (τ,c₀ t) ∧ P₁ ((0,τ),t)=R (τ,c₁ t)) ∧
      (∀ s τ, P₀ ((s,τ),1)=L (τ,c₀ 1) ∧ P₁ ((s,τ),1)=R (τ,c₁ 1)) ∧
      (∀ s t, P₀ ((s,0),t)=L (0,c₀ t) ∧ P₀ ((s,1),t)=L (1,c₀ t) ∧
        P₁ ((s,0),t)=R (0,c₁ t) ∧ P₁ ((s,1),t)=R (1,c₁ t)) ∧
      (∀ z, P₀ z ∈ V ∧ P₁ z ∈ V) ∧
      (∀ (τ t : Interval) (ht : 0<(t:ℝ)), (t:ℝ)≤1/2 →
        P₀ ((1,τ),t)=ArcFinitePosition.planeComplexLinearEquiv.symm
          (Complex.exp ((1-(τ:ℝ)) • Λ₀ (0,cp₀ ⟨t.val,ht,t.property.2⟩)+
            (τ:ℝ) • Λ₀ (1,cp₀ ⟨t.val,ht,t.property.2⟩))) ∧
        P₁ ((1,τ),t)=ArcFinitePosition.planeComplexLinearEquiv.symm
          (Complex.exp ((1-(τ:ℝ)) • Λ₁ (0,cp₁ ⟨t.val,ht,t.property.2⟩)+
            (τ:ℝ) • Λ₁ (1,cp₁ ⟨t.val,ht,t.property.2⟩)))) ∧
      (∀ (τ t : Interval) (ht : 0<(t:ℝ)), (t:ℝ)≤1/2 →
        (P₀ ((1,τ),t) 1=0 ↔ ∃ k : ↑levels₀,τ=γ₀ k (cp₀ ⟨t.val,ht,t.property.2⟩)) ∧
        (P₁ ((1,τ),t) 1=0 ↔ ∃ k : ↑levels₁,τ=γ₁ k (cp₁ ⟨t.val,ht,t.property.2⟩))) ∧
      (∀ (s τ t : Interval), 0<(t:ℝ) → P₀ ((s,τ),t)≠0 ∧ P₁ ((s,τ),t)≠0) := by
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁⟩ :=
      actual_same_class_loop_finite_endpoint_contact_graphs M a b ha hclass hfinite p hp
  let g₀ : C(Interval × Interval,ℂ) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv (L z),by fun_prop⟩
  let g₁ : C(Interval × Interval,ℂ) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv (R z),by fun_prop⟩
  have hg₀ (τ : Interval) : g₀ (τ,0)=0 := by
    change ArcFinitePosition.planeComplexLinearEquiv (L (τ,0))=0
    rw [(hzeroCharts τ).1]; exact map_zero _
  have hg₁ (τ : Interval) : g₁ (τ,0)=0 := by
    change ArcFinitePosition.planeComplexLinearEquiv (R (τ,0))=0
    rw [(hzeroCharts τ).2]; exact map_zero _
  obtain ⟨d₀,hdpos₀,hh₀,c₀,cp₀,hcscale₀,hcpscale₀,H₀,hHzero₀,hHstart₀,hHouter₀,hHboundary₀,hHinner₀,hHsmall₀,hHnz₀⟩ :=
    actual_small_supported_logarithmic_patch g₀ hg₀ Λ₀ hΛ₀
  obtain ⟨d₁,hdpos₁,hh₁,c₁,cp₁,hcscale₁,hcpscale₁,H₁,hHzero₁,hHstart₁,hHouter₁,hHboundary₁,hHinner₁,hHsmall₁,hHnz₁⟩ :=
    actual_small_supported_logarithmic_patch g₁ hg₁ Λ₁ hΛ₁
  let P₀ : C((Interval × Interval) × Interval,Plane) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv.symm (H₀ z),by fun_prop⟩
  let P₁ : C((Interval × Interval) × Interval,Plane) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv.symm (H₁ z),by fun_prop⟩
  have hPinner (τ t : Interval) (ht : 0<(t:ℝ)) (hh : (t:ℝ)≤1/2) :
      P₀ ((1,τ),t)=ArcFinitePosition.planeComplexLinearEquiv.symm
        (Complex.exp ((1-(τ:ℝ)) • Λ₀ (0,cp₀ ⟨t.val,ht,t.property.2⟩)+
          (τ:ℝ) • Λ₀ (1,cp₀ ⟨t.val,ht,t.property.2⟩))) ∧
      P₁ ((1,τ),t)=ArcFinitePosition.planeComplexLinearEquiv.symm
        (Complex.exp ((1-(τ:ℝ)) • Λ₁ (0,cp₁ ⟨t.val,ht,t.property.2⟩)+
          (τ:ℝ) • Λ₁ (1,cp₁ ⟨t.val,ht,t.property.2⟩))) :=
    ⟨congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHinner₀ τ t ht hh),
      congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHinner₁ τ t ht hh)⟩
  refine ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,?_,?_,?_,?_,?_,hPinner,?_,?_⟩
  · intro s τ
    change ArcFinitePosition.planeComplexLinearEquiv.symm (H₀ ((s,τ),0))=0 ∧
      ArcFinitePosition.planeComplexLinearEquiv.symm (H₁ ((s,τ),0))=0
    rw [hHzero₀,hHzero₁,map_zero]
    exact ⟨rfl,rfl⟩
  · intro τ t
    constructor
    · simpa only [P₀,P₁,g₀,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHstart₀ τ t)
    · simpa only [P₀,P₁,g₁,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHstart₁ τ t)
  · intro s τ
    constructor
    · simpa only [P₀,P₁,g₀,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHouter₀ s τ)
    · simpa only [P₀,P₁,g₁,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHouter₁ s τ)
  · intro s t
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [P₀,P₁,g₀,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHboundary₀ s t).1
    · simpa only [P₀,P₁,g₀,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHboundary₀ s t).2
    · simpa only [P₀,P₁,g₁,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHboundary₁ s t).1
    · simpa only [P₀,P₁,g₁,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using
        congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hHboundary₁ s t).2
  · intro z
    exact ⟨hCV (actual_complex_unit_ball_plane_square _ (hHsmall₀ z.1.1 z.1.2 z.2).le),
      hCV (actual_complex_unit_ball_plane_square _ (hHsmall₁ z.1.1 z.1.2 z.2).le)⟩
  · intro τ t ht hh
    rw [(hPinner τ t ht hh).1,(hPinner τ t ht hh).2]
    exact ⟨hc₀ (cp₀ ⟨t.val,ht,t.property.2⟩) τ,hc₁ (cp₁ ⟨t.val,ht,t.property.2⟩) τ⟩
  · intro s τ t ht
    constructor
    · intro hz
      have hh := congrArg ArcFinitePosition.planeComplexLinearEquiv hz
      simp only [P₀,ContinuousMap.coe_mk,ContinuousLinearEquiv.apply_symm_apply,map_zero] at hh
      exact hHnz₀ s τ t ht hh
    · intro hz
      have hh := congrArg ArcFinitePosition.planeComplexLinearEquiv hz
      simp only [P₁,ContinuousMap.coe_mk,ContinuousLinearEquiv.apply_symm_apply,map_zero] at hh
      exact hHnz₁ s τ t ht hh
end CurveComplex.HyperellipticModel
