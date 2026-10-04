import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopLogarithmicGerms
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualNonrealLogarithmPiStripe
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- ORIGINAL same-class loop data construct a literal exact old-base chart
and continuous TWO-ended movie germs in it. Both germs are zero at the base,
nonzero away from it, and detect the ENTIRE original loop as the real axis.
Original crossing-free tails are chosen from actual source finite contacts.
No chart, movie, germ, finite seam, or log-lift certificate is supplied. -/
theorem actual_same_class_loop_boundary_pi_stripes
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
      (∀ t, (Λ₁ (1,t)).im ∈ Ioo ((n₁₁:ℝ)*Real.pi) (((n₁₁:ℝ)+1)*Real.pi)) := by
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,Λ₀,Λ₁,hΛ₀,hΛ₁⟩ :=
    actual_same_class_loop_logarithmic_germs M a b ha hclass hfinite p hp
  let q : Bool → C(Interval,Interval) := fun j => if j then r else l
  let C : Bool → C(Interval × Interval,Plane) := fun j => if j then R else L
  let A : Bool → C(Interval × Ioc (0:ℝ) 1,ℂ) := fun j => if j then Λ₁ else Λ₀
  let param : C(Ioc (0:ℝ) 1,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2⟩,by fun_prop⟩
  have hqe (j : Bool) (t : Ioc (0:ℝ) 1) : 0<(q j (param t):ℝ) ∧ (q j (param t):ℝ)<1 := by
    cases j
    · change 0<(l (param t):ℝ) ∧ (l (param t):ℝ)<1
      rw [hl]; change 0<ε*t.val ∧ ε*t.val<1
      constructor <;> nlinarith [t.property.1,t.property.2]
    · change 0<(r (param t):ℝ) ∧ (r (param t):ℝ)<1
      rw [hr]; change 0<1-ε*t.val ∧ 1-ε*t.val<1
      constructor <;> nlinarith [t.property.1,t.property.2]
  have htailOff (j : Bool) (t : Ioc (0:ℝ) 1) : b.val.map (q j (param t)) ∉ crossings M a b := by
    apply htails
    cases j
    · apply Or.inl
      change (l (param t):ℝ)≤ε
      rw [hl]; change ε*t.val≤ε; nlinarith [t.property.2]
    · apply Or.inr
      change 1-ε≤(r (param t):ℝ)
      rw [hr]; change 1-ε≤1-ε*t.val; nlinarith [t.property.2]
  have hCa (j : Bool) (τ t : Interval) : C j (τ,t) 1=0 ↔ K (τ,q j t) ∈ a.val.image := by
    cases j
    · exact hLaxis τ t
    · exact hRaxis τ t
  have hlog (j : Bool) (z : Interval × Ioc (0:ℝ) 1) :
      Complex.exp (A j z)=ArcFinitePosition.planeComplexLinearEquiv (C j (z.1,param z.2)) := by
    cases j
    · exact hΛ₀ z
    · exact hΛ₁ z
  have hnonreal (j : Bool) (τ : Interval) (hτ : τ=0 ∨ τ=1) (t : Ioc (0:ℝ) 1) :
      (Complex.exp (A j (τ,t))).im≠0 := by
    rw [hlog]
    change C j (τ,param t) 1≠0
    intro he
    have hhit := (hCa j τ (param t)).mp he
    have hq := hqe j t
    rcases hτ with rfl | rfl
    · have hm : K (0,q j (param t)) ∉ (M.cover.branch : Set S) :=
        hmarks 0 _ (ne_of_gt hq.1) (ne_of_lt hq.2)
      rw [hzero] at hhit hm
      exact htailOff j t ⟨⟨hhit,hm⟩,⟨mem_range_self _,hm⟩⟩
    · exact htop _ (ne_of_gt hq.1) (ne_of_lt hq.2) hhit
  let slice (j : Bool) (τ : Interval) : C(Ioc (0:ℝ) 1,ℂ) :=
    ⟨fun t => A j (τ,t),(A j).continuous.comp (continuous_const.prodMk continuous_id)⟩
  obtain ⟨n₀₀,hn₀₀⟩ := actual_nonreal_logarithm_pi_stripe 1 (by norm_num) (slice false 0)
    (hnonreal false 0 (Or.inl rfl))
  obtain ⟨n₀₁,hn₀₁⟩ := actual_nonreal_logarithm_pi_stripe 1 (by norm_num) (slice false 1)
    (hnonreal false 1 (Or.inr rfl))
  obtain ⟨n₁₀,hn₁₀⟩ := actual_nonreal_logarithm_pi_stripe 1 (by norm_num) (slice true 0)
    (hnonreal true 0 (Or.inl rfl))
  obtain ⟨n₁₁,hn₁₁⟩ := actual_nonreal_logarithm_pi_stripe 1 (by norm_num) (slice true 1)
    (hnonreal true 1 (Or.inr rfl))
  exact ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,Λ₀,Λ₁,hΛ₀,hΛ₁,
    n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁⟩
end CurveComplex.HyperellipticModel
