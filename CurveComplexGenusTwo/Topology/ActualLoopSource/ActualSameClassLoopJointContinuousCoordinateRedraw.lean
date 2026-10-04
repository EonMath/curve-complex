import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopFiniteEndpointContactGraphs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopBoundaryPiStripes
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteUnorderedPiContactGraphs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualComplexLogAffineNorm
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLogarithmicGermContinuousRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual jointly continuous redraw at the marked base, preserving both time boundaries. -/
theorem actual_same_class_loop_joint_continuous_coordinate_redraw
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
    ∃ D₀ D₁ : C(Interval × Interval,Plane),
      (∀ τ, D₀ (τ,0)=0 ∧ D₁ (τ,0)=0) ∧
      (∀ (τ t : Interval) (ht : 0<(t:ℝ)),
        D₀ (τ,t)=ArcFinitePosition.planeComplexLinearEquiv.symm
          (Complex.exp ((1-(τ:ℝ)) • Λ₀ (0,⟨t.val,ht,t.property.2⟩)+
            (τ:ℝ) • Λ₀ (1,⟨t.val,ht,t.property.2⟩))) ∧
        D₁ (τ,t)=ArcFinitePosition.planeComplexLinearEquiv.symm
          (Complex.exp ((1-(τ:ℝ)) • Λ₁ (0,⟨t.val,ht,t.property.2⟩)+
            (τ:ℝ) • Λ₁ (1,⟨t.val,ht,t.property.2⟩)))) ∧
      (∀ t, D₀ (0,t)=L (0,t) ∧ D₀ (1,t)=L (1,t) ∧
        D₁ (0,t)=R (0,t) ∧ D₁ (1,t)=R (1,t)) := by
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
  obtain ⟨E₀,hE₀zero,hE₀pos,hE₀boundary⟩ :=
    actual_logarithmic_germ_continuous_redraw g₀ hg₀ Λ₀ hΛ₀
  obtain ⟨E₁,hE₁zero,hE₁pos,hE₁boundary⟩ :=
    actual_logarithmic_germ_continuous_redraw g₁ hg₁ Λ₁ hΛ₁
  let D₀ : C(Interval × Interval,Plane) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv.symm (E₀ z),by fun_prop⟩
  let D₁ : C(Interval × Interval,Plane) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv.symm (E₁ z),by fun_prop⟩
  refine ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,D₀,D₁,?_,?_,?_⟩
  · intro τ
    change ArcFinitePosition.planeComplexLinearEquiv.symm (E₀ (τ,0))=0 ∧
      ArcFinitePosition.planeComplexLinearEquiv.symm (E₁ (τ,0))=0
    rw [hE₀zero,hE₁zero,map_zero]
    exact ⟨rfl,rfl⟩
  · intro τ t ht
    exact ⟨congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hE₀pos τ t ht),
      congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hE₁pos τ t ht)⟩
  · intro t
    change ArcFinitePosition.planeComplexLinearEquiv.symm (E₀ (0,t))=L (0,t) ∧
      ArcFinitePosition.planeComplexLinearEquiv.symm (E₀ (1,t))=L (1,t) ∧
      ArcFinitePosition.planeComplexLinearEquiv.symm (E₁ (0,t))=R (0,t) ∧
      ArcFinitePosition.planeComplexLinearEquiv.symm (E₁ (1,t))=R (1,t)
    rw [(hE₀boundary t).1,(hE₀boundary t).2,(hE₁boundary t).1,(hE₁boundary t).2]
    simp only [g₀,g₁,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply,and_self]
end CurveComplex.HyperellipticModel
