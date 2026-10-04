import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.AnalyticCechAlgebra
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.DolbeaultDbar
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SerreIntegrationData
open TopologicalSpace
open scoped Manifold ContDiff Bundle
set_option maxHeartbeats 2000000
namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]
variable (U : OpenCover E)
/-- Local Čech-to-Dolbeault coefficient `Σ_j g_ij ∂̄ρ_j`. -/
noncomputable def chartCechDbarCoefficient [Fintype U.Index]
    (a : E) (ρ : U.Index → E → ℝ)
    (g : oneCocycles U) (i : U.Index) (x : E)
    (hxi : x ∈ U.opens i) : ℂ := by
  classical
  exact ∑ j, if hxj : x ∈ U.opens j then
    (g.1 i j).1 ⟨x, ⟨hxi, hxj⟩⟩ * chartDbarWeight a (ρ j) x
  else 0

noncomputable def coverIndex (x : E) : U.Index :=
  Classical.choose (coverIndex_exists U x)

theorem coverIndex_mem (x : E) : x ∈ U.opens (coverIndex U x) :=
  Classical.choose_spec (coverIndex_exists U x)

end SameAtlasAnalyticCohomology
