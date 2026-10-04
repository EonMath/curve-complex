import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopFiniteEndpointContactGraphs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopBoundaryPiStripes
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteUnorderedPiContactGraphs
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualComplexLogAffineNorm
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLogarithmicGermContinuousRedraw
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSmallPlaneZeroGermSquare
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopJointContinuousCoordinateRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Source-only jointly continuous inverse-chart loop redraw, including the fixed marked base. -/
theorem actual_same_class_loop_joint_continuous_surface_redraw
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
        J₁ (τ,⟨0,le_rfl,hδ.le⟩)=a.val.map 0) := by
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    D₀,D₁,hDzero,hDpos,hDboundary⟩ :=
      actual_same_class_loop_joint_continuous_coordinate_redraw M a b ha hclass hfinite p hp
  obtain ⟨δ₀,hδ₀,hh₀,hs₀⟩ := actual_small_plane_zero_germ_square D₀ (fun τ => (hDzero τ).1)
  obtain ⟨δ₁,hδ₁,hh₁,hs₁⟩ := actual_small_plane_zero_germ_square D₁ (fun τ => (hDzero τ).2)
  let δ := min δ₀ δ₁
  have hδ : 0<δ := lt_min hδ₀ hδ₁
  have hh : δ<1/2 := (min_le_left δ₀ δ₁).trans_lt hh₀
  let param : C(Icc (0:ℝ) δ,Interval) :=
    ⟨fun t => ⟨t.val,t.property.1,t.property.2.trans (le_of_lt (hh.trans (by norm_num)))⟩,by fun_prop⟩
  let F₀ : C(Interval × Icc (0:ℝ) δ,Plane) :=
    ⟨fun z => D₀ (z.1,param z.2),by fun_prop⟩
  let F₁ : C(Interval × Icc (0:ℝ) δ,Plane) :=
    ⟨fun z => D₁ (z.1,param z.2),by fun_prop⟩
  have hF₀ (z : Interval × Icc (0:ℝ) δ) : F₀ z ∈ V :=
    hCV (hs₀ z.1 (param z.2) (z.2.property.2.trans (min_le_left δ₀ δ₁)))
  have hF₁ (z : Interval × Icc (0:ℝ) δ) : F₁ z ∈ V :=
    hCV (hs₁ z.1 (param z.2) (z.2.property.2.trans (min_le_right δ₀ δ₁)))
  let J₀ : C(Interval × Icc (0:ℝ) δ,S) :=
    ⟨fun z => (e.symm ⟨F₀ z,hF₀ z⟩).val,
      continuous_subtype_val.comp (e.symm.continuous.comp (F₀.continuous.subtype_mk hF₀))⟩
  let J₁ : C(Interval × Icc (0:ℝ) δ,S) :=
    ⟨fun z => (e.symm ⟨F₁ z,hF₁ z⟩).val,
      continuous_subtype_val.comp (e.symm.continuous.comp (F₁.continuous.subtype_mk hF₁))⟩
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
  have hinverseZero (hv : (0:Plane) ∈ V) : (e.symm ⟨0,hv⟩).val=a.val.map 0 := by
    have he : e ⟨a.val.map 0,hbU⟩=⟨0,hv⟩ := Subtype.ext hbcoord
    have hh := congrArg (fun q : V => (e.symm q).val) he
    rw [e.symm_apply_apply] at hh
    exact hh.symm
  refine ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    D₀,D₁,hDzero,hDpos,hDboundary,δ,hδ,hh,J₀,J₁,?_,?_,?_⟩
  · intro z
    exact ⟨(e.symm ⟨F₀ z,hF₀ z⟩).property,(e.symm ⟨F₁ z,hF₁ z⟩).property⟩
  · intro z h₀ h₁
    constructor
    · change (e (e.symm ⟨F₀ z,hF₀ z⟩)).val=F₀ z
      rw [e.apply_symm_apply]
    · change (e (e.symm ⟨F₁ z,hF₁ z⟩)).val=F₁ z
      rw [e.apply_symm_apply]
  · intro τ
    have hpzero : param ⟨0,le_rfl,hδ.le⟩=0 := Subtype.ext rfl
    have hz₀ : F₀ (τ,⟨0,le_rfl,hδ.le⟩)=0 := by
      change D₀ (τ,param ⟨0,le_rfl,hδ.le⟩)=0
      rw [hpzero]; exact (hDzero τ).1
    have hz₁ : F₁ (τ,⟨0,le_rfl,hδ.le⟩)=0 := by
      change D₁ (τ,param ⟨0,le_rfl,hδ.le⟩)=0
      rw [hpzero]; exact (hDzero τ).2
    constructor
    · change (e.symm ⟨F₀ (τ,⟨0,le_rfl,hδ.le⟩),hF₀ _⟩).val=a.val.map 0
      have he : (⟨F₀ (τ,⟨0,le_rfl,hδ.le⟩),hF₀ _⟩ : V)=⟨0,hz₀ ▸ hF₀ _⟩ := Subtype.ext hz₀
      rw [he]; exact hinverseZero _
    · change (e.symm ⟨F₁ (τ,⟨0,le_rfl,hδ.le⟩),hF₁ _⟩).val=a.val.map 0
      have he : (⟨F₁ (τ,⟨0,le_rfl,hδ.le⟩),hF₁ _⟩ : V)=⟨0,hz₁ ▸ hF₁ _⟩ := Subtype.ext hz₁
      rw [he]; exact hinverseZero _
end CurveComplex.HyperellipticModel
