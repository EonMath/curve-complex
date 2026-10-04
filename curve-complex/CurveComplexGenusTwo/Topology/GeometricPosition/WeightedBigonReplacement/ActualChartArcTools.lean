import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import Mathlib.Topology.Order.ProjIcc
import CurveComplexGenusTwo.Foundations.Definitions
open Set Topology Schoenflies
namespace CurveComplex

theorem actual_chart_continuous_arc
    {S : Type*} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S Plane) (f : C(Interval,S))
    (hf : Topology.IsEmbedding f) (hS : ∀ t, f t ∈ E.source) :
    IsArcBetween (E '' Set.range f) (E (f 0)) (E (f 1)) := by
  let g : C(Interval,Plane) := ⟨fun t => E (f t),
    E.continuousOn.comp_continuous f.continuous hS⟩
  let F : ℝ → Plane := Set.IccExtend (show (0 : ℝ) ≤ 1 by norm_num) g
  have hF (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : F t = g ⟨t,ht⟩ := by
    simp only [F,Set.IccExtend,Function.comp_apply,Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) ht]
  have hcont : Continuous F := g.continuous.Icc_extend'
  have hinj : Set.InjOn F unitInterval := by
    intro x hx y hy hxy
    rw [hF x hx,hF y hy] at hxy
    have hh := hf.injective (E.injOn (hS ⟨x,hx⟩) (hS ⟨y,hy⟩) hxy)
    exact congrArg Subtype.val hh
  have hrange : F '' unitInterval = E '' Set.range f := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨f ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,(hF t ht).symm⟩
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨t.val,t.property,hF t.val t.property⟩
  refine ⟨F,hcont.continuousOn,hinj,hrange,?_,?_⟩
  · exact hF 0 (by constructor <;> norm_num)
  · exact hF 1 (by constructor <;> norm_num)

theorem actual_pullback_chart_arc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane) (a b : S)
    (ha : a ∈ E.source) (hb : b ∈ E.source)
    (A : Set Plane) (hA : IsArcBetween A (E a) (E b)) (hAt : A ⊆ E.target) :
    ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
      Set.range f = E.symm '' A ∧ f 0 = a ∧ f 1 = b := by
  obtain ⟨F,hF,hFi,hFr,hF0,hF1⟩ := hA
  have hFt (t : Interval) : F t.val ∈ E.target :=
    hAt (hFr ▸ ⟨t.val,t.property,rfl⟩)
  have hFc : Continuous (fun t : Interval => F t.val) :=
    continuousOn_iff_continuous_domRestrict.mp hF
  let f : C(Interval,S) := ⟨fun t => E.symm (F t.val),
    E.symm.continuousOn.comp_continuous hFc hFt⟩
  have hfi : Function.Injective f := by
    intro x y he
    have hh := E.symm.injOn (hFt x) (hFt y) he
    exact Subtype.ext (hFi x.property y.property hh)
  refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨F t.val,hFr ▸ ⟨t.val,t.property,rfl⟩,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      rw [←hFr] at hq
      obtain ⟨t,ht,rfl⟩ := hq
      exact ⟨⟨t,ht⟩,rfl⟩
  · change E.symm (F 0) = a
    rw [hF0,E.left_inv ha]
  · change E.symm (F 1) = b
    rw [hF1,E.left_inv hb]

theorem actual_finite_union_card_bound {X J : Type*} [Fintype J]
    (A : J → Set X) (hA : ∀ j, (A j).Finite) :
    (⋃ j, A j).Finite ∧ (⋃ j, A j).ncard ≤ ∑ j, (A j).ncard := by
  classical
  have hF (F : Finset J) : (⋃ j ∈ F, A j).Finite ∧
      (⋃ j ∈ F, A j).ncard ≤ ∑ j ∈ F, (A j).ncard := by
    induction F using Finset.induction with
    | empty => simp
    | @insert j F hj ih =>
        have he : (⋃ k ∈ insert j F, A k) = A j ∪ ⋃ k ∈ F, A k := by
          ext x
          simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
          aesop
        rw [he,Finset.sum_insert hj]
        exact ⟨(hA j).union ih.1,(Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih.2 _)⟩
  simpa using hF Finset.univ

theorem actual_filter_indicator_card {J : Type*} [Fintype J]
    (p : J → Prop) [DecidablePred p] :
    (∑ j, if p j then 1 else 0) = Nat.card {j : J // p j} := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp

end CurveComplex
