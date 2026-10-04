import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualSuppliedAnnulusEmbeddedTwoTraceSourceLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E : Type} [TopologicalSpace E] [T2Space E]

-- Actual labeled paired trace, including both components and the original time.
-- The inverse below is jointly continuous on this exact compact space-time image.
example (F0 F1 : C(Interval × Circle,E))
    (he : ∀ t, Topology.IsEmbedding (fun z => F0 (t,z)) ∧ Topology.IsEmbedding (fun z => F1 (t,z)))
    (hd : ∀ t, Disjoint (Set.range (fun z => F0 (t,z))) (Set.range (fun z => F1 (t,z)))) :
    let T : (Interval × Circle) ⊕ (Interval × Circle) → Interval × E :=
      Sum.elim (fun p => (p.1,F0 p)) (fun p => (p.1,F1 p))
    ∃ P : ((Interval × Circle) ⊕ (Interval × Circle)) ≃ₜ Set.range T,
      (∀ p, (P p).val = T p) ∧
      ∀ x, Sum.elim Prod.fst Prod.fst (P.symm x) = x.val.1 := by
  audit_main14_base3
    dsimp only
    let T : (Interval × Circle) ⊕ (Interval × Circle) → Interval × E :=
      Sum.elim (fun p => (p.1,F0 p)) (fun p => (p.1,F1 p))
    have hc : Continuous T :=
      (continuous_fst.prodMk F0.continuous).sumElim (continuous_fst.prodMk F1.continuous)
    have hi : Function.Injective T := by
      rintro (⟨t,z⟩ | ⟨t,z⟩) (⟨s,w⟩ | ⟨s,w⟩) hh
      all_goals have ht : t = s := congrArg Prod.fst hh
      all_goals subst s
      all_goals have hx := congrArg Prod.snd hh
      · have hz := (he t).1.injective hx
        subst w
        rfl
      · exact False.elim (Set.disjoint_left.mp (hd t) (Set.mem_range_self z) ⟨w,hx.symm⟩)
      · exact False.elim (Set.disjoint_left.mp (hd t) ⟨w,hx.symm⟩ (Set.mem_range_self z))
      · have hz := (he t).2.injective hx
        subst w
        rfl
    have hT : Topology.IsEmbedding T := (hc.isClosedEmbedding hi).isEmbedding
    let P := hT.toHomeomorph
    refine ⟨P,fun p => rfl,?_⟩
    intro x
    have hh : (P (P.symm x)).val = x.val := congrArg Subtype.val (P.apply_symm_apply x)
    have ht := congrArg Prod.fst hh
    change (T (P.symm x)).1 = x.val.1 at ht
    have htime (p : (Interval × Circle) ⊕ (Interval × Circle)) :
        (T p).1 = Sum.elim Prod.fst Prod.fst p := by cases p <;> rfl
    rw [htime] at ht
    exact ht
end CurveComplex.HyperellipticModel
