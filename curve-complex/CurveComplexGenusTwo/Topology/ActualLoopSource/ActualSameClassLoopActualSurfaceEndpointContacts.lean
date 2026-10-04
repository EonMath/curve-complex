import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopJointContinuousSurfaceRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual surface endpoint contacts are precisely the produced finite disjoint graphs, away from the fixed base. -/
theorem actual_same_class_loop_actual_surface_endpoint_contacts
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
        D₁ (0,t)=R (0,t) ∧ D₁ (1,t)=R (1,t)) ∧
    ∃ δ : ℝ, ∃ hδ : 0<δ, ∃ hh : δ<1/2,
    ∃ J₀ J₁ : C(Interval × Icc (0:ℝ) δ,S),
      (∀ z, J₀ z ∈ U ∧ J₁ z ∈ U) ∧
      (∀ z (h₀ : J₀ z ∈ U) (h₁ : J₁ z ∈ U),
        (e ⟨J₀ z,h₀⟩).val=D₀ (z.1,⟨z.2.val,z.2.property.1,
          z.2.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩) ∧
        (e ⟨J₁ z,h₁⟩).val=D₁ (z.1,⟨z.2.val,z.2.property.1,
          z.2.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩)) ∧
      (∀ τ, J₀ (τ,⟨0,le_rfl,hδ.le⟩)=a.val.map 0 ∧
        J₁ (τ,⟨0,le_rfl,hδ.le⟩)=a.val.map 0) ∧
      (∀ (τ : Interval) (t : Icc (0:ℝ) δ) (ht : 0<t.val),
        (J₀ (τ,t) ∈ a.val.image ↔ ∃ k : ↑levels₀,
          τ=γ₀ k ⟨t.val,ht,t.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩) ∧
        (J₁ (τ,t) ∈ a.val.image ↔ ∃ k : ↑levels₁,
          τ=γ₁ k ⟨t.val,ht,t.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩)) := by
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    D₀,D₁,hDzero,hDpos,hDboundary,δ,hδ,hh,J₀,J₁,hJU,hcoord,hJbase⟩ :=
      actual_same_class_loop_joint_continuous_surface_redraw M a b ha hclass hfinite p hp
  refine ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    D₀,D₁,hDzero,hDpos,hDboundary,δ,hδ,hh,J₀,J₁,hJU,hcoord,hJbase,?_⟩
  intro τ t ht
  let u : Interval := ⟨t.val,t.property.1,t.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩
  let v : Ioc (0:ℝ) 1 := ⟨t.val,ht,t.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩
  have hco := hcoord (τ,t) (hJU (τ,t)).1 (hJU (τ,t)).2
  constructor
  · have hx := haxis ⟨J₀ (τ,t),(hJU (τ,t)).1⟩
    rw [hco.1] at hx
    change J₀ (τ,t) ∈ a.val.image ↔ D₀ (τ,u) 1=0 at hx
    rw [(hDpos τ u ht).1] at hx
    change J₀ (τ,t) ∈ a.val.image ↔
      (Complex.exp ((1-(τ:ℝ)) • Λ₀ (0,v)+(τ:ℝ) • Λ₀ (1,v))).im=0 at hx
    exact hx.trans (hc₀ v τ)
  · have hx := haxis ⟨J₁ (τ,t),(hJU (τ,t)).2⟩
    rw [hco.2] at hx
    change J₁ (τ,t) ∈ a.val.image ↔ D₁ (τ,u) 1=0 at hx
    rw [(hDpos τ u ht).2] at hx
    change J₁ (τ,t) ∈ a.val.image ↔
      (Complex.exp ((1-(τ:ℝ)) • Λ₁ (0,v)+(τ:ℝ) • Λ₁ (1,v))).im=0 at hx
    exact hx.trans (hc₁ v τ)
end CurveComplex.HyperellipticModel
