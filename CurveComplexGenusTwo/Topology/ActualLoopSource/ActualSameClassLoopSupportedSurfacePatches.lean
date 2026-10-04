import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopSupportedCoordinatePatches
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkedChartZeroGermLift
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Source-only BOTH marked-free supported surface patches, literal outer seams and actual finite inner contact graphs. -/
theorem actual_same_class_loop_supported_surface_patches
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
      (∀ (s τ t : Interval), 0<(t:ℝ) → P₀ ((s,τ),t)≠0 ∧ P₁ ((s,τ),t)≠0) ∧
    ∃ J₀ J₁ : C((Interval × Interval) × Interval,S),
      (∀ z, J₀ z ∈ U ∧ J₁ z ∈ U) ∧
      (∀ z (h₀ : J₀ z ∈ U) (h₁ : J₁ z ∈ U),
        (e ⟨J₀ z,h₀⟩).val=P₀ z ∧ (e ⟨J₁ z,h₁⟩).val=P₁ z) ∧
      (∀ s τ, J₀ ((s,τ),0)=a.val.map 0 ∧ J₁ ((s,τ),0)=a.val.map 0) ∧
      (∀ (s τ t : Interval), 0<(t:ℝ) →
        J₀ ((s,τ),t) ∉ (M.cover.branch : Set S) ∧ J₁ ((s,τ),t) ∉ (M.cover.branch : Set S)) ∧
      (∀ τ t, J₀ ((0,τ),t)=K (τ,l (c₀ t)) ∧ J₁ ((0,τ),t)=K (τ,r (c₁ t))) ∧
      (∀ s τ, J₀ ((s,τ),1)=K (τ,l (c₀ 1)) ∧ J₁ ((s,τ),1)=K (τ,r (c₁ 1))) ∧
      (∀ (τ t : Interval) (ht : 0<(t:ℝ)), (t:ℝ)≤1/2 →
        (J₀ ((1,τ),t) ∈ a.val.image ↔ ∃ k : ↑levels₀,τ=γ₀ k (cp₀ ⟨t.val,ht,t.property.2⟩)) ∧
        (J₁ ((1,τ),t) ∈ a.val.image ↔ ∃ k : ↑levels₁,τ=γ₁ k (cp₁ ⟨t.val,ht,t.property.2⟩))) ∧
      (∀ s t,J₀ ((s,0),t)=K (0,l (c₀ t)) ∧ J₀ ((s,1),t)=K (1,l (c₀ t)) ∧
        J₁ ((s,0),t)=K (0,r (c₁ t)) ∧ J₁ ((s,1),t)=K (1,r (c₁ t))) := by
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,hPzero,hPstart,hPouter,hPboundary,hPV,hPinner,hPcontacts,hPnz⟩ :=
      actual_same_class_loop_supported_coordinate_patches M a b ha hclass hfinite p hp
  have hlzero : l 0=0 := by apply Subtype.ext; rw [hl]; simp
  have hbU : a.val.map 0 ∈ U := by
    have he : K (0,l 0)=a.val.map 0 := by rw [hlzero,(hbase 0).1]
    exact he ▸ (hin 0 0).1
  have hbcoord : (e ⟨a.val.map 0,hbU⟩).val=0 := by
    have he : (⟨K (0,l 0),(hin 0 0).1⟩ : U)=⟨a.val.map 0,hbU⟩ := by
      apply Subtype.ext
      change K (0,l 0)=a.val.map 0
      rw [hlzero,(hbase 0).1]
    have hv := congrArg (fun q : U => (e q).val) he
    exact hv.symm.trans ((hL 0 0 (hin 0 0).1).symm.trans (hzeroCharts 0).1)
  obtain ⟨J₀,hJU₀,hcoord₀,hbase₀,hmarks₀,haxis₀⟩ :=
    actual_marked_chart_zero_germ_lift M a U V e hUmarks hbU hbcoord haxis P₀
      (fun z => (hPV z).1) (fun x => (hPzero x.1 x.2).1)
      (fun x t ht => (hPnz x.1 x.2 t ht).1)
  obtain ⟨J₁,hJU₁,hcoord₁,hbase₁,hmarks₁,haxis₁⟩ :=
    actual_marked_chart_zero_germ_lift M a U V e hUmarks hbU hbcoord haxis P₁
      (fun z => (hPV z).2) (fun x => (hPzero x.1 x.2).2)
      (fun x t ht => (hPnz x.1 x.2 t ht).2)
  have hfaithful (J : C((Interval × Interval) × Interval,S))
      (hJU : ∀ z,J z ∈ U) (P : C((Interval × Interval) × Interval,Plane))
      (hcoord : ∀ z (h : J z ∈ U),(e ⟨J z,h⟩).val=P z)
      (z : (Interval × Interval) × Interval) (q : S) (hq : q ∈ U)
      (he : P z=(e ⟨q,hq⟩).val) : J z=q := by
    have hh : e ⟨J z,hJU z⟩=e ⟨q,hq⟩ := Subtype.ext ((hcoord z (hJU z)).trans he)
    exact congrArg Subtype.val (e.injective hh)
  refine ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,hPzero,hPstart,hPouter,hPboundary,hPV,hPinner,hPcontacts,hPnz,
    J₀,J₁,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z; exact ⟨hJU₀ z,hJU₁ z⟩
  · intro z h₀ h₁; exact ⟨hcoord₀ z h₀,hcoord₁ z h₁⟩
  · intro s τ; exact ⟨hbase₀ (s,τ),hbase₁ (s,τ)⟩
  · intro s τ t ht; exact ⟨hmarks₀ (s,τ) t ht,hmarks₁ (s,τ) t ht⟩
  · intro τ t
    exact ⟨hfaithful J₀ hJU₀ P₀ hcoord₀ ((0,τ),t) _ (hin τ (c₀ t)).1
        ((hPstart τ t).1.trans (hL τ (c₀ t) (hin τ (c₀ t)).1)),
      hfaithful J₁ hJU₁ P₁ hcoord₁ ((0,τ),t) _ (hin τ (c₁ t)).2
        ((hPstart τ t).2.trans (hR τ (c₁ t) (hin τ (c₁ t)).2))⟩
  · intro s τ
    exact ⟨hfaithful J₀ hJU₀ P₀ hcoord₀ ((s,τ),1) _ (hin τ (c₀ 1)).1
        ((hPouter s τ).1.trans (hL τ (c₀ 1) (hin τ (c₀ 1)).1)),
      hfaithful J₁ hJU₁ P₁ hcoord₁ ((s,τ),1) _ (hin τ (c₁ 1)).2
        ((hPouter s τ).2.trans (hR τ (c₁ 1) (hin τ (c₁ 1)).2))⟩
  · intro τ t ht hh
    exact ⟨(haxis₀ ((1,τ),t)).trans (hPcontacts τ t ht hh).1,
      (haxis₁ ((1,τ),t)).trans (hPcontacts τ t ht hh).2⟩
  · intro s t
    refine ⟨?_,?_,?_,?_⟩
    · exact hfaithful J₀ hJU₀ P₀ hcoord₀ ((s,0),t) _ (hin 0 (c₀ t)).1
        ((hPboundary s t).1.trans (hL 0 (c₀ t) (hin 0 (c₀ t)).1))
    · exact hfaithful J₀ hJU₀ P₀ hcoord₀ ((s,1),t) _ (hin 1 (c₀ t)).1
        ((hPboundary s t).2.1.trans (hL 1 (c₀ t) (hin 1 (c₀ t)).1))
    · exact hfaithful J₁ hJU₁ P₁ hcoord₁ ((s,0),t) _ (hin 0 (c₁ t)).2
        ((hPboundary s t).2.2.1.trans (hR 0 (c₁ t) (hin 0 (c₁ t)).2))
    · exact hfaithful J₁ hJU₁ P₁ hcoord₁ ((s,1),t) _ (hin 1 (c₁ t)).2
        ((hPboundary s t).2.2.2.trans (hR 1 (c₁ t) (hin 1 (c₁ t)).2))
end CurveComplex.HyperellipticModel
