import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualSameClassNonloopTargetAvoidingSweepCanonicalImportsPrivate
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1200000

private theorem actual_rl_same_class_nonloop_endpoint_orientation_private
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hab : Quotient.mk (essentialArcSetoid M) a=Quotient.mk (essentialArcSetoid M) b)
    (ha : a.val.map 0≠a.val.map 1) :
    (a.val.map 0=b.val.map 0 ∧ a.val.map 1=b.val.map 1) ∨
      (a.val.map 0=b.val.map 1 ∧ a.val.map 1=b.val.map 0) := by
  classical
  have he := arcEndpoints_isotopy_invariant M a b (Quotient.exact hab)
  change ({a.val.map 0,a.val.map 1}:Finset S)={b.val.map 0,b.val.map 1} at he
  have hA0 : a.val.map 0=b.val.map 0 ∨ a.val.map 0=b.val.map 1 := by
    have h : a.val.map 0∈({b.val.map 0,b.val.map 1}:Finset S) :=
      he ▸ Finset.mem_insert_self _ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  have hA1 : a.val.map 1=b.val.map 0 ∨ a.val.map 1=b.val.map 1 := by
    have h : a.val.map 1∈({b.val.map 0,b.val.map 1}:Finset S) :=
      he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  rcases hA0 with h00 | h01 <;> rcases hA1 with h10 | h11
  · exact False.elim (ha (h00.trans h10.symm))
  · exact Or.inl ⟨h00,h11⟩
  · exact Or.inr ⟨h01,h10⟩
  · exact False.elim (ha (h01.trans h11.symm))

private theorem actual_rl_nonloop_reverse_parametrization_preserves_original_image_private
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (hb : b.val.map 0≠b.val.map 1) :
    ∃ c : EssentialMarkedArc M,
      (∀ t,c.val.map t=b.val.map (unitInterval.symm t)) ∧
      c.val.map 0=b.val.map 1 ∧ c.val.map 1=b.val.map 0 ∧
      c.val.image=b.val.image ∧
      Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b := by
  let c : MarkedArc M :=
    { map := fun t => b.val.map (unitInterval.symm t)
      continuous := b.val.continuous.comp unitInterval.continuous_symm
      injective_except_loop_closure := by
        intro s t he
        exact Or.inl (unitInterval.symm_bijective.injective
          (NonLoopArc.injective ⟨b.val,hb⟩ he))
      start_marked := by
        change b.val.map (unitInterval.symm 0)∈M.cover.branch
        rw [unitInterval.symm_zero]
        exact b.val.end_marked
      end_marked := by
        change b.val.map (unitInterval.symm 1)∈M.cover.branch
        rw [unitInterval.symm_one]
        exact b.val.start_marked
      marked_only_at_ends := by
        intro t ht
        rcases b.val.marked_only_at_ends _ ht with h0 | h1
        · right
          change t=(1:Interval)
          apply unitInterval.symm_bijective.injective
          change unitInterval.symm t=unitInterval.symm 1
          rw [unitInterval.symm_one]
          exact h0
        · left
          change t=(0:Interval)
          apply unitInterval.symm_bijective.injective
          change unitInterval.symm t=unitInterval.symm 0
          rw [unitInterval.symm_zero]
          exact h1 }
  have hc : IsEssentialMarkedArc M c := by
    left
    change b.val.map (unitInterval.symm 0)≠b.val.map (unitInterval.symm 1)
    simpa only [unitInterval.symm_zero,unitInterval.symm_one] using hb.symm
  have himage : c.image=b.val.image := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t,rfl⟩
      exact Set.mem_range_self _
    · rintro _ ⟨t,rfl⟩
      refine ⟨unitInterval.symm t,?_⟩
      change b.val.map (unitInterval.symm (unitInterval.symm t))=b.val.map t
      rw [unitInterval.symm_symm]
  refine ⟨⟨c,hc⟩,(fun t => rfl),?_,?_,himage,?_⟩
  · exact congrArg b.val.map unitInterval.symm_zero
  · exact congrArg b.val.map unitInterval.symm_one
  · apply Quotient.sound
    refine ⟨AmbientIsotopy.identity S,(fun t z hz => rfl),?_⟩
    change id '' c.image=b.val.image
    rw [Set.image_id,himage]

#print axioms actual_rl_same_class_nonloop_endpoint_orientation_private
#print axioms actual_rl_nonloop_reverse_parametrization_preserves_original_image_private
end CurveComplex.HyperellipticModel
