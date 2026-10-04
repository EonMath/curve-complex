import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualLogarithmicContactWedgeChartLift
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual corner fillings for a whole family of constructed phase graphs.
The chart target is checked against the supplied actual redraw coordinates;
no time-graph corner limit, filling, or extension is assumed. -/
theorem actual_scaled_logarithmic_contact_corner_family
    {ι : Type} (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (hbase : a.val.map 0 ∈ U) (hbasecoord : (e ⟨a.val.map 0,hbase⟩).val=0)
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (C : C(Interval × Interval,Plane)) (hCzero : ∀ τ,C (τ,0)=0)
    (c : C(Interval,Interval)) (cp : C(Ioc (0:ℝ) 1,Ioc (0:ℝ) 1)) (hczero : c 0=0)
    (hcompat : ∀ t,(⟨(cp t).val,(cp t).property.1.le,(cp t).property.2⟩ : Interval)=
      c ⟨t.val,t.property.1.le,t.property.2⟩)
    (Λ : C(Interval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z,Complex.exp (Λ z)=ArcFinitePosition.planeComplexLinearEquiv
      (C (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩)))
    (γ : ι → C(Ioc (0:ℝ) 1,Interval))
    (hγ : ∀ k t,(Complex.exp ((1-(γ k (cp t):ℝ)) • Λ (0,cp t)+
      (γ k (cp t):ℝ) • Λ (1,cp t))).im=0)
    (P : C((Interval × Interval) × Interval,Plane)) (hP : ∀ z,P z ∈ V)
    (hinner : ∀ (τ t : Interval) (ht : 0<(t:ℝ)),(t:ℝ)≤1/2 →
      P ((1,τ),t)=ArcFinitePosition.planeComplexLinearEquiv.symm
        (Complex.exp ((1-(τ:ℝ)) • Λ (0,cp ⟨t.val,ht,t.property.2⟩)+
          (τ:ℝ) • Λ (1,cp ⟨t.val,ht,t.property.2⟩)))) :
    ∃ κ : ι → C(Ioc (0:ℝ) (1/2),Interval),
      (∀ k t,κ k t=γ k (cp ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)) ∧
    ∃ time : ι → C(Interval × Ioc (0:ℝ) (1/2),Interval),
      (∀ k z,(time k z:ℝ)=(z.1:ℝ)*(κ k z.2:ℝ)) ∧
    ∃ F : ι → C(Interval × Icc (0:ℝ) (1/2),S),
      (∀ k z,F k z ∈ U) ∧
      (∀ k s,F k (s,⟨0,le_rfl,by norm_num⟩)=a.val.map 0) ∧
      (∀ k s t,0<t.val → F k (s,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ k t,F k (1,t) ∈ a.val.image) ∧
      (∀ k t (h : F k (0,t) ∈ U),(e ⟨F k (0,t),h⟩).val=
        C (0,c ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)) ∧
      (∀ k (s : Interval) t (ht : 0<t.val) (h : F k (s,t) ∈ U),
        (e ⟨F k (s,t),h⟩).val=P ((1,time k (s,⟨t.val,ht,t.property.2⟩)),
          ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)) := by
  classical
  let param : C(Ioc (0:ℝ) (1/2),Ioc (0:ℝ) 1) :=
    ⟨fun t => ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩,by fun_prop⟩
  let κ : ι → C(Ioc (0:ℝ) (1/2),Interval) := fun k => (γ k).comp (cp.comp param)
  let time : ι → C(Interval × Ioc (0:ℝ) (1/2),Interval) := fun k =>
    ⟨fun z => ⟨(z.1:ℝ)*(κ k z.2:ℝ),mul_nonneg z.1.property.1 (κ k z.2).property.1,
      (mul_le_mul_of_nonneg_left (κ k z.2).property.2 z.1.property.1).trans
        (by simpa using z.1.property.2)⟩,by fun_prop⟩
  let g : C(Interval × Interval,ℂ) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv (C (z.1,c z.2)),by fun_prop⟩
  let A : C(Interval × Ioc (0:ℝ) 1,ℂ) := ⟨fun z => Λ (z.1,cp z.2),by fun_prop⟩
  have hg (τ : Interval) : g (τ,0)=0 := by
    change ArcFinitePosition.planeComplexLinearEquiv (C (τ,c 0))=0
    rw [hczero,hCzero,map_zero]
  have hA (z : Interval × Ioc (0:ℝ) 1) : Complex.exp (A z)=g
      (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩) := by
    change Complex.exp (Λ (z.1,cp z.2))=ArcFinitePosition.planeComplexLinearEquiv
      (C (z.1,c ⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))
    rw [hΛ,hcompat]
  have htarget (τ : Interval) (t : Ioc (0:ℝ) (1/2)) :
      ArcFinitePosition.planeComplexLinearEquiv.symm
        (Complex.exp ((1-(τ:ℝ)) • A (0,param t)+(τ:ℝ) • A (1,param t))) ∈ V := by
    have hh := hinner τ ⟨t.val,t.property.1.le,t.property.2.trans (by norm_num)⟩ t.property.1 t.property.2
    exact hh ▸ hP ((1,τ),⟨t.val,t.property.1.le,t.property.2.trans (by norm_num)⟩)
  have hexists (k : ι) := actual_logarithmic_contact_wedge_chart_lift M a U V e hmarks hbase hbasecoord haxis
    g hg A hA (κ k) (fun t => hγ k (param t)) htarget
  choose F hFU hFzero hFmarks hFtop hFstart hFcoord using hexists
  refine ⟨κ,(fun _ _ => rfl),time,(fun _ _ => rfl),F,hFU,hFzero,hFmarks,hFtop,?_,?_⟩
  · intro k t h
    have hh := hFstart k t h
    simpa only [g,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using hh
  · intro k s t ht h
    have hh := hFcoord k s t ht h
    have hp := hinner (time k (s,⟨t.val,ht,t.property.2⟩))
      ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩ ht t.property.2
    exact hh.trans hp.symm
end CurveComplex.HyperellipticModel.ArcSurgery
