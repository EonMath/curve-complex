import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopMarkedParallelSweep
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCompactFiberwiseContinuousDescent
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
/-- The original loop produces a continuous parallel motion of its IMAGE,
including its identified marked endpoint. -/
theorem actual_loop_parallel_image_sweep
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) :
    ∃ P : C(Interval × a.val.image,S),
      (∀ x, P (0,x)=x.val) ∧
      (∀ τ, Function.Injective (fun x => P (τ,x))) ∧
      (∀ τ, P (τ,⟨a.val.map 0,mem_range_self 0⟩)=a.val.map 0) ∧
      (∀ τ x, x.val≠a.val.map 0 → P (τ,x) ∉ (M.cover.branch : Set S)) ∧
      ∀ x, x.val≠a.val.map 0 → P (1,x) ∉ a.val.image := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨F,hzero,hinj,hends,hmarks,hfiber,htop⟩ := actual_loop_marked_parallel_sweep M a ha
  let q : C(Interval × Interval,Interval × a.val.image) :=
    ⟨fun z => (z.1,⟨a.val.map z.2,mem_range_self z.2⟩),
      continuous_fst.prodMk ((a.val.continuous.comp continuous_snd).subtype_mk _)⟩
  have hsurj : Function.Surjective q := by
    rintro ⟨τ,x,hx⟩
    obtain ⟨t,ht⟩ := hx
    exact ⟨(τ,t),Prod.ext rfl (Subtype.ext ht)⟩
  have hcoherent : ∀ z w, q z=q w → F z=F w := by
    rintro ⟨τ,s⟩ ⟨σ,t⟩ he
    have hτ : τ=σ := congrArg Prod.fst he
    have ht : a.val.map s=a.val.map t := congrArg (fun z => z.2.val) he
    subst σ
    exact hfiber τ s t ht
  obtain ⟨P,hP⟩ := CurveComplex.actual_compact_fiberwise_continuous_descent q hsurj F hcoherent
  have hp (τ t : Interval) : P (τ,⟨a.val.map t,mem_range_self t⟩)=F (τ,t) := hP (τ,t)
  refine ⟨P,?_,?_,?_,?_,?_⟩
  · rintro ⟨x,⟨t,rfl⟩⟩
    exact (hp 0 t).trans (hzero t)
  · intro τ x y he
    obtain ⟨s,hs⟩ := x.property
    obtain ⟨t,ht⟩ := y.property
    have hx : x=⟨a.val.map s,mem_range_self s⟩ := Subtype.ext hs.symm
    have hy : y=⟨a.val.map t,mem_range_self t⟩ := Subtype.ext ht.symm
    change P (τ,x)=P (τ,y) at he
    rw [hx,hy] at he
    have heF : F (τ,s)=F (τ,t) := (hp τ s).symm.trans (he.trans (hp τ t))
    apply Subtype.ext
    rw [← hs,← ht]
    rcases hinj τ s t heF with h | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [h]
    · exact ha
    · exact ha.symm
  · intro τ
    exact (hp τ 0).trans (hends τ).1
  · rintro τ ⟨x,⟨t,rfl⟩⟩ hn
    rw [hp]
    apply hmarks τ t
    · intro ht; exact hn (ht ▸ rfl)
    · intro ht; exact hn (ht ▸ ha.symm)
  · rintro ⟨x,⟨t,rfl⟩⟩ hn
    rw [hp]
    apply htop t
    · intro ht; exact hn (ht ▸ rfl)
    · intro ht; exact hn (ht ▸ ha.symm)
end
end CurveComplex.HyperellipticModel
