import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopBaseAxisChartProof
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassTargetAvoidingLoopSweep
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopClosureInvariant
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopCrossingWindow
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopOriginalFirstContactBoundary
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- ORIGINAL same-class loop data construct a literal exact old-base chart
and continuous TWO-ended movie germs in it. Both germs are zero at the base,
nonzero away from it, and detect the ENTIRE original loop as the real axis.
Original crossing-free tails are chosen from actual source finite contacts.
No chart, movie, germ, finite seam, or log-lift certificate is supplied. -/
theorem actual_same_class_loop_chart_germs
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
      (∀ τ t, R (τ,t) 1=0 ↔ K (τ,r t) ∈ a.val.image) := by
  obtain ⟨U,V,hU,e,hCV,hUmarks,haxis,hbase,hbase0⟩ := actual_loop_base_axis_chart M a ha
  obtain ⟨K,hzero,hcollision,hends,hmarks,htop⟩ := actual_same_class_target_avoiding_loop_sweep M a b ha hclass
  have hbaseEq := actual_same_class_loop_literal_base M a b ha hclass
  have hb := (actual_same_class_loop_closure_invariant M a b hclass).mp ha
  have hKbase (τ : Interval) : K (τ,0)=a.val.map 0 ∧ K (τ,1)=a.val.map 0 :=
    ⟨(hends τ).1.trans hbaseEq.symm,(hends τ).2.trans (hb.symm.trans hbaseEq.symm)⟩
  have hnear (c : Interval) (hc : c=0 ∨ c=1) :
      ∃ δ : ℝ, 0<δ ∧ ∀ τ t : Interval, dist t c<δ → K (τ,t) ∈ U := by
    have hN : IsOpen (K ⁻¹' U) := hU.preimage K.continuous
    have hline : (univ : Set Interval) ×ˢ {c} ⊆ K ⁻¹' U := by
      rintro ⟨τ,t⟩ ⟨_,ht⟩
      rw [mem_singleton_iff] at ht
      change t=c at ht
      subst t
      change K (τ,c) ∈ U
      rcases hc with rfl | rfl
      · exact (hKbase τ).1.symm ▸ hbase
      · exact (hKbase τ).2.symm ▸ hbase
    obtain ⟨A,B,_,hB,hA,hcB,hAB⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hN hline
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (hcB (mem_singleton c)))
    exact ⟨δ,hδ,fun τ t ht => hAB ⟨hA (mem_univ τ),hball ht⟩⟩
  obtain ⟨δ₀,hδ₀,hleft⟩ := hnear 0 (Or.inl rfl)
  obtain ⟨δ₁,hδ₁,hright⟩ := hnear 1 (Or.inr rfl)
  obtain ⟨η,hη,hηhalf,_,_,_,_,_,htails⟩ := actual_loop_allowed_crossing_window M a b hfinite p hp
  let ε : ℝ := min (min δ₀ δ₁) η /2
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεδ₀ : ε<δ₀ := by
    have hh := (min_le_left (min δ₀ δ₁) η).trans (min_le_left δ₀ δ₁)
    dsimp [ε]; linarith
  have hεδ₁ : ε<δ₁ := by
    have hh := (min_le_left (min δ₀ δ₁) η).trans (min_le_right δ₀ δ₁)
    dsimp [ε]; linarith
  have hεη : ε<η := by have hh := min_le_right (min δ₀ δ₁) η; dsimp [ε]; linarith
  have hεhalf : ε<1/2 := hεη.trans hηhalf
  let l : C(Interval,Interval) := ⟨fun t => ⟨ε*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩,by fun_prop⟩
  let r : C(Interval,Interval) := ⟨fun t => ⟨1-ε*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩,by fun_prop⟩
  have hlin (τ t : Interval) : K (τ,l t) ∈ U := by
    apply hleft τ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |ε*(t:ℝ)-0|<δ₀
    rw [sub_zero,abs_of_nonneg (mul_nonneg hε.le t.property.1)]
    nlinarith [t.property.2]
  have hrin (τ t : Interval) : K (τ,r t) ∈ U := by
    apply hright τ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |1-ε*(t:ℝ)-1|<δ₁
    rw [abs_of_nonpos (by nlinarith [t.property.1])]
    nlinarith [t.property.2]
  let L : C(Interval × Interval,Plane) := ⟨fun z => (e ⟨K (z.1,l z.2),hlin _ _⟩).val,
    continuous_subtype_val.comp (e.continuous.comp
      ((K.continuous.comp (continuous_fst.prodMk (l.continuous.comp continuous_snd))).subtype_mk (fun z => hlin z.1 z.2)))⟩
  let R : C(Interval × Interval,Plane) := ⟨fun z => (e ⟨K (z.1,r z.2),hrin _ _⟩).val,
    continuous_subtype_val.comp (e.continuous.comp
      ((K.continuous.comp (continuous_fst.prodMk (r.continuous.comp continuous_snd))).subtype_mk (fun z => hrin z.1 z.2)))⟩
  have hl0 : l 0=0 := Subtype.ext (by simp [l])
  have hr0 : r 0=1 := Subtype.ext (by simp [r])
  have hzeroCharts (τ : Interval) : L (τ,0)=0 ∧ R (τ,0)=0 := by
    constructor
    · have hh : (⟨K (τ,l 0),hlin τ 0⟩ : U)=⟨a.val.map 0,hbase⟩ := Subtype.ext (by change K (τ,l 0)=a.val.map 0; rw [hl0]; exact (hKbase τ).1)
      change (e _).val=0
      rw [hh]; exact hbase0
    · have hh : (⟨K (τ,r 0),hrin τ 0⟩ : U)=⟨a.val.map 0,hbase⟩ := Subtype.ext (by change K (τ,r 0)=a.val.map 0; rw [hr0]; exact (hKbase τ).2)
      change (e _).val=0
      rw [hh]; exact hbase0
  have hoffBase (τ q : Interval) (hq : 0<(q:ℝ) ∧ (q:ℝ)<1) : K (τ,q)≠a.val.map 0 := by
    intro he
    rcases hcollision τ q 0 (he.trans (hKbase τ).1.symm) with hh | hh | hh
    · exact (ne_of_gt hq.1) (congrArg Subtype.val hh)
    · exact (ne_of_gt hq.1) (congrArg Subtype.val hh.1)
    · exact (ne_of_lt hq.2) (congrArg Subtype.val hh.1)
  refine ⟨K,hzero,hcollision,hKbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,ε,hε,hεhalf,l,r,
    (fun _ => rfl),(fun _ => rfl),(fun τ t => ⟨hlin τ t,hrin τ t⟩),?_,L,R,
    (fun _ _ _ => rfl),(fun _ _ _ => rfl),hzeroCharts,?_,?_,?_⟩
  · intro t ht
    apply htails t
    rcases ht with ht | ht <;> [exact Or.inl (ht.trans hεη.le); exact Or.inr (by linarith)]
  · intro τ t ht
    change (0:ℝ)<(t:ℝ) at ht
    have hlt : 0<(l t:ℝ) ∧ (l t:ℝ)<1 := by change 0<ε*(t:ℝ) ∧ ε*(t:ℝ)<1; constructor <;> nlinarith [t.property.2]
    have hrt : 0<(r t:ℝ) ∧ (r t:ℝ)<1 := by change 0<1-ε*(t:ℝ) ∧ 1-ε*(t:ℝ)<1; constructor <;> nlinarith [t.property.2]
    constructor
    · intro he
      have hh : e ⟨K (τ,l t),hlin τ t⟩=e ⟨a.val.map 0,hbase⟩ := Subtype.ext (he.trans hbase0.symm)
      exact hoffBase τ (l t) hlt (congrArg Subtype.val (e.injective hh))
    · intro he
      have hh : e ⟨K (τ,r t),hrin τ t⟩=e ⟨a.val.map 0,hbase⟩ := Subtype.ext (he.trans hbase0.symm)
      exact hoffBase τ (r t) hrt (congrArg Subtype.val (e.injective hh))
  · intro τ t; exact (haxis ⟨K (τ,l t),hlin τ t⟩).symm
  · intro τ t; exact (haxis ⟨K (τ,r t),hrin τ t⟩).symm
end CurveComplex.HyperellipticModel
