import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.InducedHyperbolicSmoothAtlasCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ClosedHyperbolicCanonicalBridge
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace CurveComplex.Hyperbolic
open Set
open scoped Manifold ContDiff
variable {E : Type} [MetricSpace E]

theorem induced_hyperbolic_charted_space_smooth_hyperbolic
    (charts : E → OpenPartialHomeomorph E H2) (hcover : ∀ x : E, x ∈ (charts x).source)
    (hmetric : ∀ x : E, ∀ y ∈ (charts x).source, ∀ z ∈ (charts x).source,
      dist y z = dist (charts x y) (charts x z)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := inducedHyperbolicChartedSpace charts hcover
    SmoothLocallyHyperbolic E := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := inducedHyperbolicChartedSpace charts hcover
  letI : IsManifold (𝓡 2) ∞ E := induced_hyperbolic_charted_space_is_manifold charts hcover hmetric
  intro x
  let a := inducedEuclideanHyperbolicChart (charts x)
  let Φ : PartialDiffeomorph (𝓡 2) (𝓡 2) E (EuclideanSpace ℝ (Fin 2)) ∞ :=
    { a.toPartialEquiv with
      open_source := a.open_source
      open_target := a.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let Ψ := complexEuclideanPlaneEquiv.symm.toDiffeomorph.toPartialDiffeomorph
  let d := Φ.trans Ψ
  have hsource : d.source = (charts x).source := by
    change a.source ∩ a ⁻¹' Set.univ = (charts x).source
    rw [Set.preimage_univ, Set.inter_univ, inducedEuclideanHyperbolicChart_source]
  have hvalue (y : E) : (d y : ℂ) = (charts x y : ℂ) := by
    change complexEuclideanPlaneEquiv.symm
      (complexEuclideanPlaneEquiv (charts x y : ℂ)) = (charts x y : ℂ)
    exact complexEuclideanPlaneEquiv.symm_apply_apply _
  have hupper (y : E) (hy : y ∈ d.source) : 0 < (d y).im := by
    rw [hvalue]
    exact (charts x y).im_pos
  have hplane (y : E) (hy : y ∈ d.source) : (⟨d y, hupper y hy⟩ : H2) = charts x y :=
    UpperHalfPlane.coe_injective (hvalue y)
  refine ⟨⟨d, hupper, ?_⟩, ?_⟩
  · intro y z
    rw [hplane y y.property, hplane z z.property]
    exact hmetric x y (hsource ▸ y.property) z (hsource ▸ z.property)
  · change x ∈ d.source
    rw [hsource]
    exact hcover x

end CurveComplex.Hyperbolic
