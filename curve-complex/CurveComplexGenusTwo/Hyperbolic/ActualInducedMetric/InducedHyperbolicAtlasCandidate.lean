import CurveComplexGenusTwo.Hyperbolic.Stabilizer
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace CurveComplex.Hyperbolic
open Set

noncomputable def complexEuclideanPlaneEquiv : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Complex.equivRealProdCLM.trans
    (LinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousLinearEquiv).trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm

noncomputable def upperHalfPlaneComplexChart : OpenPartialHomeomorph H2 ℂ :=
  UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : H2 → ℂ)

variable {E : Type} [TopologicalSpace E]

noncomputable def inducedEuclideanHyperbolicChart (e : OpenPartialHomeomorph E H2) :
    OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin 2)) :=
  (e.trans upperHalfPlaneComplexChart).transHomeomorph complexEuclideanPlaneEquiv.toHomeomorph

theorem inducedEuclideanHyperbolicChart_source (e : OpenPartialHomeomorph E H2) :
    (inducedEuclideanHyperbolicChart e).source = e.source := by
  simp [inducedEuclideanHyperbolicChart, upperHalfPlaneComplexChart]

/-- The actual chosen hyperbolic charts induce an atlas on the unchanged topology.
Smooth transition compatibility is a separate obligation. -/
noncomputable def inducedHyperbolicChartedSpace
    (charts : E → OpenPartialHomeomorph E H2) (hcover : ∀ x : E, x ∈ (charts x).source) :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) E where
  atlas := Set.range (fun x => inducedEuclideanHyperbolicChart (charts x))
  chartAt := fun x => inducedEuclideanHyperbolicChart (charts x)
  mem_chart_source := fun x => by
    rw [inducedEuclideanHyperbolicChart_source]
    exact hcover x
  chart_mem_atlas := fun x => ⟨x, rfl⟩

end CurveComplex.Hyperbolic
