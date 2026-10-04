import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingGraphH1Proof

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Raw representative computation, independent of every original cut side.
The h-edge remains unglued; the actual interior has 2*p free integral H1
generators. This is reusable by the side-H1 owner and is not a rank-two
recognition assumption. -/
theorem actual_one_boundary_orientable_model_homology_one (p : ℕ) :
    Nonempty (integralHomology (ActualOneBoundaryOrientableOpenModel p) 1 ≅
      ModuleCat.of ℤ (Fin (2 * p) → ℤ)) := by
  obtain ⟨e⟩ := OneBoundaryRay.actual_one_boundary_surviving_graph_homology_one p
  exact ⟨CircleHomologyComputation.homotopyHomologyIso
    (OneBoundaryRay.actualModelHomotopyEquivSurvivingBoundary p) 1 ≪≫ e⟩

end CurveComplex.Hyperbolic
