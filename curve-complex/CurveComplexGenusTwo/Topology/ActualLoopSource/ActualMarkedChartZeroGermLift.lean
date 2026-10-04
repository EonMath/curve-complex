import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopActualSurfaceEndpointContacts
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual inverse-chart lift of a joint nonzero positive germ. The entire
marked set is avoided at positive germ parameter, and the base is fixed. -/
theorem actual_marked_chart_zero_germ_lift
    {X : Type} [TopologicalSpace X]
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (hbase : a.val.map 0 ∈ U) (hbasecoord : (e ⟨a.val.map 0,hbase⟩).val=0)
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (P : C(X × Interval,Plane)) (hP : ∀ z,P z ∈ V)
    (hzero : ∀ x,P (x,0)=0) (hnz : ∀ (x : X) (t : Interval),0<(t:ℝ) → P (x,t)≠0) :
    ∃ J : C(X × Interval,S),
      (∀ z,J z ∈ U) ∧ (∀ z (h : J z ∈ U),(e ⟨J z,h⟩).val=P z) ∧
      (∀ x,J (x,0)=a.val.map 0) ∧
      (∀ (x : X) (t : Interval),0<(t:ℝ) → J (x,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ z,J z ∈ a.val.image ↔ P z 1=0) := by
  let J : C(X × Interval,S) :=
    ⟨fun z => (e.symm ⟨P z,hP z⟩).val,
      continuous_subtype_val.comp (e.symm.continuous.comp (P.continuous.subtype_mk hP))⟩
  have hJU (z : X × Interval) : J z ∈ U := (e.symm ⟨P z,hP z⟩).property
  have hcoord (z : X × Interval) (h : J z ∈ U) : (e ⟨J z,h⟩).val=P z := by
    change (e (e.symm ⟨P z,hP z⟩)).val=P z
    rw [e.apply_symm_apply]
  refine ⟨J,hJU,hcoord,?_,?_,?_⟩
  · intro x
    have hc : e ⟨J (x,0),hJU (x,0)⟩=e ⟨a.val.map 0,hbase⟩ := by
      apply Subtype.ext
      rw [hcoord,hzero,hbasecoord]
    exact congrArg Subtype.val (e.injective hc)
  · intro x t ht hm
    have hb : J (x,t)=a.val.map 0 := by
      by_contra hn
      exact Set.disjoint_left.mp hmarks (hJU (x,t)) ⟨hm,hn⟩
    have he : (⟨J (x,t),hJU (x,t)⟩ : U)=⟨a.val.map 0,hbase⟩ := Subtype.ext hb
    have hh := congrArg (fun q : U => (e q).val) he
    rw [hcoord,hbasecoord] at hh
    exact hnz x t ht hh
  · intro z
    have hh := haxis ⟨J z,hJU z⟩
    rw [hcoord] at hh
    exact hh
end CurveComplex.HyperellipticModel.ArcSurgery
