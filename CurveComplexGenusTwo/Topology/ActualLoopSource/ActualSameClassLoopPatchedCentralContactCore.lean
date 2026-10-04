import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopWholeMovieInnerContacts
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkFreeMovieExactContactCore
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual central core of the SAME patched original loop movie: both boundary contact sets finite and all old-loop contacts lie in a produced exact-axis strip. -/
theorem actual_same_class_loop_patched_central_contact_core
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
        J₁ ((s,0),t)=K (0,r (c₁ t)) ∧ J₁ ((s,1),t)=K (1,r (c₁ t))) ∧
    ∃ A B : ℝ, A=ε*d₀ ∧ B=ε*d₁ ∧ 0<A ∧ 0<B ∧ A+B<1 ∧
    ∃ q₀ q₁ : C(Interval,Interval),
      (∀ t,(q₀ t:ℝ)=min 1 ((t:ℝ)/A)) ∧ (∀ t,(q₁ t:ℝ)=min 1 ((1-(t:ℝ))/B)) ∧
    ∃ W : C((Interval × Interval) × Interval,S),
      (∀ s τ t : Interval,(t:ℝ)≤A → W ((s,τ),t)=J₀ ((s,τ),q₀ t)) ∧
      (∀ s τ t : Interval,1-B≤(t:ℝ) → W ((s,τ),t)=J₁ ((s,τ),q₁ t)) ∧
      (∀ s τ t : Interval,A<(t:ℝ) → (t:ℝ)<1-B → W ((s,τ),t)=K (τ,t)) ∧
      (∀ τ t,W ((0,τ),t)=K (τ,t)) ∧
      (∀ s τ,W ((s,τ),0)=a.val.map 0 ∧ W ((s,τ),1)=a.val.map 0) ∧
      (∀ s τ t : Interval,0<(t:ℝ) → (t:ℝ)<1 → W ((s,τ),t) ∉ (M.cover.branch : Set S)) ∧
      (∀ s t,W ((s,0),t)=b.val.map t) ∧
      (∀ s t : Interval,0<(t:ℝ) → (t:ℝ)<1 → W ((s,1),t) ∉ a.val.image) ∧
      (∀ τ t : Interval, 0<(t:ℝ) → (t:ℝ)≤A/2 →
        ∃ u : Ioc (0:ℝ) 1,u.val=(q₀ t:ℝ) ∧
          (W ((1,τ),t) ∈ a.val.image ↔ ∃ k : ↑levels₀,τ=γ₀ k (cp₀ u))) ∧
      (∀ τ t : Interval, (t:ℝ)<1 → 1-B/2≤(t:ℝ) →
        ∃ u : Ioc (0:ℝ) 1,u.val=(q₁ t:ℝ) ∧
          (W ((1,τ),t) ∈ a.val.image ↔ ∃ k : ↑levels₁,τ=γ₁ k (cp₁ u))) ∧
    ∃ r₀ r₁ : ℝ,r₀=A/4 ∧ r₁=1-B/4 ∧ 0<r₀ ∧ r₀<r₁ ∧ r₁<1 ∧
    ∃ φ : C(Interval,Interval),IsEmbedding φ ∧
      (∀ t,(φ t:ℝ)=r₀+(r₁-r₀)*(t:ℝ)) ∧
    ∃ G : C(Interval × Interval,S),
      (∀ z,G z=W ((1,z.1),φ z.2)) ∧
      (∀ z,G z ∉ (M.cover.branch : Set S)) ∧
      (∀ z : Interval × Interval,z.1=1 → G z ∉ a.val.image) ∧
      {τ : Interval | G (τ,0) ∈ a.val.image}.Finite ∧
      {τ : Interval | G (τ,1) ∈ a.val.image}.Finite ∧
    ∃ BC : Interval × Set.Icc (-1:ℝ) 1 → S, ∃ hBC : IsEmbedding BC,
      (∀ z,BC z ∉ (M.cover.branch : Set S)) ∧
      (∀ z,BC z ∈ a.val.image ↔ z.2.val=0) ∧
    ∃ T : Set (Interval × Interval),IsOpen T ∧ G ⁻¹' a.val.image ⊆ T ∧
    ∃ Q : C(T,Set.range BC),(∀ z : T,(Q z).val=G z.val) ∧
    ∃ ψ : C(T,ℝ),
      (∀ z : T,ψ z=((hBC.toHomeomorph.symm (Q z)).2:ℝ)) ∧
      (∀ z : T,0<((hBC.toHomeomorph.symm (Q z)).1:ℝ) ∧
        ((hBC.toHomeomorph.symm (Q z)).1:ℝ)<1 ∧ -1<ψ z ∧ ψ z<1) ∧
      (∀ z : T,ψ z=0 ↔ G z.val ∈ a.val.image) ∧
      (∀ z : T,z.val.1=1 → ψ z≠0) := by
  classical
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,hPzero,hPstart,hPouter,hPboundary,hPV,hPinner,hPcontacts,hPnz,
    J₀,J₁,hJU,hcoord,hJbase,hJmarks,hJstart,hJouter,hJcontacts,hJboundary,
    A,B,hAeq,hBeq,hA,hB,hAB,q₀,q₁,hq₀,hq₁,W,hwleft,hwright,hwmiddle,
    hwstart,hwbase,hwmarks,hwbottom,hwtop,hWinner₀,hWinner₁⟩ :=
      actual_same_class_loop_whole_movie_inner_contacts M a b ha hclass hfinite p hp
  let r₀ := A/4
  let r₁ := 1-B/4
  have hr₀ : 0<r₀ := by dsimp [r₀]; positivity
  have horder : r₀<r₁ := by dsimp [r₀,r₁]; linarith
  have hr₁ : r₁<1 := by dsimp [r₁]; linarith
  let φ : C(Interval,Interval) :=
    ⟨fun t => ⟨r₀+(r₁-r₀)*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩,by fun_prop⟩
  have hφinj : Function.Injective φ := by
    intro s t he
    have hh := congrArg Subtype.val he
    change r₀+(r₁-r₀)*(s:ℝ)=r₀+(r₁-r₀)*(t:ℝ) at hh
    apply Subtype.ext
    nlinarith
  have hφbounds (t : Interval) : 0<(φ t:ℝ) ∧ (φ t:ℝ)<1 := by
    change 0<r₀+(r₁-r₀)*(t:ℝ) ∧ r₀+(r₁-r₀)*(t:ℝ)<1
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hφzero : (φ 0:ℝ)=A/4 := by change r₀+(r₁-r₀)*0=A/4; simp [r₀]
  have hφone : (φ 1:ℝ)=1-B/4 := by change r₀+(r₁-r₀)*1=1-B/4; simp [r₁]
  let G : C(Interval × Interval,S) := ⟨fun z => W ((1,z.1),φ z.2),by fun_prop⟩
  have hGmarks (z : Interval × Interval) : G z ∉ (M.cover.branch : Set S) :=
    hwmarks 1 z.1 (φ z.2) (hφbounds z.2).1 (hφbounds z.2).2
  have hGtop (z : Interval × Interval) (hz : z.1=1) : G z ∉ a.val.image := by
    change W ((1,z.1),φ z.2) ∉ a.val.image
    rw [hz]
    exact hwtop 1 (φ z.2) (hφbounds z.2).1 (hφbounds z.2).2
  let u : Ioc (0:ℝ) 1 := ⟨1/4,by norm_num,by norm_num⟩
  have hqzero : (q₀ (φ 0):ℝ)=1/4 := by
    rw [hq₀,hφzero]
    have hh : (A/4)/A=1/4 := by field_simp
    rw [hh]; norm_num
  have hqone : (q₁ (φ 1):ℝ)=1/4 := by
    rw [hq₁,hφone]
    have hh : (1-(1-B/4))/B=1/4 := by field_simp; ring
    rw [hh]; norm_num
  have hleft (τ : Interval) : G (τ,0) ∈ a.val.image ↔ ∃ k : ↑levels₀,τ=γ₀ k (cp₀ u) := by
    obtain ⟨v,hv,hcontact⟩ := hWinner₀ τ (φ 0) (hφbounds 0).1 (by rw [hφzero]; linarith)
    have he : v=u := Subtype.ext (hv.trans hqzero)
    rw [he] at hcontact
    exact hcontact
  have hright (τ : Interval) : G (τ,1) ∈ a.val.image ↔ ∃ k : ↑levels₁,τ=γ₁ k (cp₁ u) := by
    obtain ⟨v,hv,hcontact⟩ := hWinner₁ τ (φ 1) (hφbounds 1).2 (by rw [hφone]; linarith)
    have he : v=u := Subtype.ext (hv.trans hqone)
    rw [he] at hcontact
    exact hcontact
  have hfiniteLeft : {τ : Interval | G (τ,0) ∈ a.val.image}.Finite := by
    apply (Set.finite_range (fun k : ↑levels₀ => γ₀ k (cp₀ u))).subset
    intro τ ht
    obtain ⟨k,hk⟩ := (hleft τ).mp ht
    exact ⟨k,hk.symm⟩
  have hfiniteRight : {τ : Interval | G (τ,1) ∈ a.val.image}.Finite := by
    apply (Set.finite_range (fun k : ↑levels₁ => γ₁ k (cp₁ u))).subset
    intro τ ht
    obtain ⟨k,hk⟩ := (hright τ).mp ht
    exact ⟨k,hk.symm⟩
  obtain ⟨BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hψbounds,hψzero,hψtop⟩ :=
    actual_mark_free_movie_exact_contact_core M a G hGmarks hGtop
  exact ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,hPzero,hPstart,hPouter,hPboundary,hPV,hPinner,hPcontacts,hPnz,
    J₀,J₁,hJU,hcoord,hJbase,hJmarks,hJstart,hJouter,hJcontacts,hJboundary,
    A,B,hAeq,hBeq,hA,hB,hAB,q₀,q₁,hq₀,hq₁,W,hwleft,hwright,hwmiddle,
    hwstart,hwbase,hwmarks,hwbottom,hwtop,hWinner₀,hWinner₁,
    r₀,r₁,rfl,rfl,hr₀,horder,hr₁,φ,(φ.continuous.isClosedEmbedding hφinj).isEmbedding,
    (fun _ => rfl),G,(fun _ => rfl),hGmarks,hGtop,hfiniteLeft,hfiniteRight,
    BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hψbounds,hψzero,hψtop⟩
end CurveComplex.HyperellipticModel
