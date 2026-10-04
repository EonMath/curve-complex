import CurveComplexGenusTwo.CWHurewicz.SingularRealization.FiniteRealizationCW
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.CWFiniteNullhomotopy
open CategoryTheory Topology
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
theorem actual_lower_skeleton_map_nullhomotopic {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (S : SSet.{0}) [S.Finite] (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x))
    (f : C(SSet.toTop.obj S, X)) :
    Nonempty (ContinuousMap.Homotopy
      (f.comp (SSet.toTop.map (S.skeleton (k + 2)).ι).hom)
      (ContinuousMap.const (SSet.toTop.obj (S.skeleton (k + 2)).toSSet) x)) := by
  let A := (S.skeleton (k + 2)).toSSet
  have : A.Finite := inferInstance
  have : A.HasDimensionLT (k + 2) := ⟨fun n hn => by
    apply Set.eq_univ_of_forall
    intro a
    by_contra ha
    have hnd : a ∈ A.nonDegenerate n := ha
    have hS : (S.skeleton (k + 2)).ι.app _ a ∈ S.nonDegenerate n :=
      (SSet.nonDegenerate_iff_of_mono (S.skeleton (k + 2)).ι a).mpr hnd
    have hlt := (S.mem_skeleton_obj_iff_of_nonDegenerate ⟨_, hS⟩ (k + 2)).mp a.property
    omega⟩
  obtain ⟨cw, ht2, hcompact, hdim⟩ := finite_realization_cw A (k + 2)
  let := cw
  let := ht2
  let := hcompact
  exact CWGeometricChains.finite_low_dimensional_map_nullhomotopic k x hlower hdim
    (f.comp (SSet.toTop.map (S.skeleton (k + 2)).ι).hom)
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier

#print axioms CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier.actual_lower_skeleton_map_nullhomotopic
