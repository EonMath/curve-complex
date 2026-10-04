import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualLogarithmicContactWedgeZeroExtension
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkedChartZeroGermLift
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual one-corner filling BELOW a contact graph in the produced chart.
The time graph has no endpoint-limit hypothesis; the whole zero end and the
marked-free positive filling are constructed from the actual logarithms. -/
theorem actual_logarithmic_contact_wedge_chart_lift
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (hbase : a.val.map 0 ∈ U) (hbasecoord : (e ⟨a.val.map 0,hbase⟩).val=0)
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (g : C(Interval × Interval,ℂ)) (hg : ∀ τ,g (τ,0)=0)
    (Λ : C(Interval × Ioc (0:ℝ) 1,ℂ))
    (hΛ : ∀ z,Complex.exp (Λ z)=g (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2⟩))
    (γ : C(Ioc (0:ℝ) (1/2),Interval))
    (hγ : ∀ t,(Complex.exp ((1-(γ t:ℝ)) •
      Λ (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)+
      (γ t:ℝ) • Λ (1,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩))).im=0)
    (htarget : ∀ (τ : Interval) (t : Ioc (0:ℝ) (1/2)),
      ArcFinitePosition.planeComplexLinearEquiv.symm
        (Complex.exp ((1-(τ:ℝ)) • Λ (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)+
          (τ:ℝ) • Λ (1,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩))) ∈ V) :
    ∃ F : C(Interval × Icc (0:ℝ) (1/2),S),
      (∀ z,F z ∈ U) ∧ (∀ s,F (s,⟨0,le_rfl,by norm_num⟩)=a.val.map 0) ∧
      (∀ s t,0<t.val → F (s,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ t,F (1,t) ∈ a.val.image) ∧
      (∀ t (h : F (0,t) ∈ U),(e ⟨F (0,t),h⟩).val=
        ArcFinitePosition.planeComplexLinearEquiv.symm
          (g (0,⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩))) ∧
      (∀ (s : Interval) t (ht : 0<t.val) (h : F (s,t) ∈ U),
        (e ⟨F (s,t),h⟩).val=ArcFinitePosition.planeComplexLinearEquiv.symm
          (Complex.exp ((1-(s:ℝ)*(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
            Λ (0,⟨t.val,ht,t.property.2.trans (by norm_num)⟩)+
            ((s:ℝ)*(γ ⟨t.val,ht,t.property.2⟩:ℝ)) •
            Λ (1,⟨t.val,ht,t.property.2.trans (by norm_num)⟩)))) := by
  obtain ⟨Z,hZzero,hZpos,hZstart,hZtop,hZnz,_⟩ :=
    actual_logarithmic_contact_wedge_zero_extension g hg Λ hΛ γ hγ
  let P : C(Interval × Icc (0:ℝ) (1/2),Plane) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv.symm (Z z),by fun_prop⟩
  have hPV (z : Interval × Icc (0:ℝ) (1/2)) : P z ∈ V := by
    by_cases ht : 0<z.2.val
    · let w : Interval := ⟨(z.1:ℝ)*(γ ⟨z.2.val,ht,z.2.property.2⟩:ℝ),
        mul_nonneg z.1.property.1 (γ ⟨z.2.val,ht,z.2.property.2⟩).property.1,
        (mul_le_mul_of_nonneg_left (γ ⟨z.2.val,ht,z.2.property.2⟩).property.2 z.1.property.1).trans
          (by simpa using z.1.property.2)⟩
      change ArcFinitePosition.planeComplexLinearEquiv.symm (Z (z.1,z.2)) ∈ V
      rw [hZpos z.1 z.2 ht]
      exact htarget w ⟨z.2.val,ht,z.2.property.2⟩
    · have hz : z.2=⟨0,le_rfl,by norm_num⟩ :=
        Subtype.ext (le_antisymm (le_of_not_gt ht) z.2.property.1)
      change ArcFinitePosition.planeComplexLinearEquiv.symm (Z (z.1,z.2)) ∈ V
      rw [hz,hZzero,map_zero]
      exact hbasecoord ▸ (e ⟨a.val.map 0,hbase⟩).property
  let F : C(Interval × Icc (0:ℝ) (1/2),S) :=
    ⟨fun z => (e.symm ⟨P z,hPV z⟩).val,
      continuous_subtype_val.comp (e.symm.continuous.comp (P.continuous.subtype_mk hPV))⟩
  have hFU (z : Interval × Icc (0:ℝ) (1/2)) : F z ∈ U := (e.symm ⟨P z,hPV z⟩).property
  have hcoord (z : Interval × Icc (0:ℝ) (1/2)) (h : F z ∈ U) : (e ⟨F z,h⟩).val=P z := by
    change (e (e.symm ⟨P z,hPV z⟩)).val=P z
    rw [e.apply_symm_apply]
  refine ⟨F,hFU,?_,?_,?_,?_,?_⟩
  · intro s
    have hc : P (s,⟨0,le_rfl,by norm_num⟩)=0 := by
      change ArcFinitePosition.planeComplexLinearEquiv.symm (Z (s,⟨0,le_rfl,by norm_num⟩))=0
      rw [hZzero,map_zero]
    have he : e ⟨F (s,⟨0,le_rfl,by norm_num⟩),hFU _⟩=e ⟨a.val.map 0,hbase⟩ :=
      Subtype.ext ((hcoord _ (hFU _)).trans (hc.trans hbasecoord.symm))
    exact congrArg Subtype.val (e.injective he)
  · intro s t ht hm
    have hb : F (s,t)=a.val.map 0 := by
      by_contra hn
      exact Set.disjoint_left.mp hmarks (hFU (s,t)) ⟨hm,hn⟩
    have he : (⟨F (s,t),hFU (s,t)⟩ : U)=⟨a.val.map 0,hbase⟩ := Subtype.ext hb
    have hh := congrArg (fun q : U => (e q).val) he
    rw [hcoord,hbasecoord] at hh
    have hz := congrArg ArcFinitePosition.planeComplexLinearEquiv hh
    simp only [P,ContinuousMap.coe_mk,ContinuousLinearEquiv.apply_symm_apply,map_zero] at hz
    exact hZnz s t ht hz
  · intro t
    have hh := haxis ⟨F (1,t),hFU (1,t)⟩
    rw [hcoord] at hh
    apply hh.mpr
    exact hZtop t
  · intro t h
    rw [hcoord]
    exact congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hZstart t)
  · intro s t ht h
    rw [hcoord]
    exact congrArg ArcFinitePosition.planeComplexLinearEquiv.symm (hZpos s t ht)
end CurveComplex.HyperellipticModel.ArcSurgery
