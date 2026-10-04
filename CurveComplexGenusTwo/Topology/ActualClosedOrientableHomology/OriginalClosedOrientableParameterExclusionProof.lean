import CurveComplexGenusTwo.Topology.ActualClosedOrientableHomology.ActualClosedOrientableModelHomologyOneProof
open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Manifold ContDiff
open CurveComplex CurveComplexGenusTwo.CWHurewicz
open LeanEval.Topology.ClassificationOfSurfaces
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
theorem actual_original_genus_two_closed_orientable_parameter_exclusion
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (p : ℕ) (hp : 1 ≤ p)
    (hhomeomorph : Nonempty (S ≃ₜ Quot (OrientableRel p 0))) : p = 2 := by
  obtain ⟨e⟩ := hhomeomorph
  obtain ⟨eClosed⟩ := CurveComplex.Hyperbolic.actual_closed_orientable_model_homology_one p hp
  obtain ⟨eS⟩ := hS.2.2.2
  let eTransport := CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 1
  let eRank : ModuleCat.of ℤ (Fin (2*p) → ℤ) ≅ ModuleCat.of ℤ (Fin (2*2) → ℤ) :=
    eClosed.symm ≪≫ eTransport.symm ≪≫ eS
  have hRank : 2*p=4 := by
    simpa using eRank.toLinearEquiv.finrank_eq
  omega
