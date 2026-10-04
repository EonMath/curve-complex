import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRelativeDeformationVanishing
import CurveComplexGenusTwo.CWHurewicz.PairHomotopyInvariance

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

theorem actual_relativeHomology_zero_of_deformation_into_subspace
    {X : Type} [TopologicalSpace X] (A : Set X)
    (g : C(X, X)) (hrange : ∀ x, g x ∈ A)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ A)
    (n : ℕ) : IsZero (relativeHomology X A n) := by
  have heq := pairRelativeHomologyMap_homotopy A A (ContinuousMap.id X) g
    (fun _ hx => hx) (fun x _ => hrange x) H hH n
  rw [pairRelativeHomologyMap_id,
    actual_pairRelativeHomologyMap_zero_of_range_in_subspace A A g
      (fun x _ => hrange x) hrange n] at heq
  exact (IsZero.iff_id_eq_zero _).mpr heq

end CurveComplexGenusTwo.CWHurewicz
