import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartCutoffV2
import CurveComplexGenusTwo.Topology.ActualPunctureResidue.ActualCechResidueLocal
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualPlanarCutoffContour

open TopologicalSpace SameAtlasAnalyticCohomology SameAtlasRRLocal
open MeasureTheory Filter
open scoped Manifold ContDiff Bundle Distributions Topology

namespace CanonicalDimensionTwo

/-- The complete original chart cutoff-to-contour Prop, with explicit
compactness. Its Type-0 residue pairing API remains explicit and separate
from the universe-polymorphic cutoff constructor used by original088. -/
def ActualChartCutoffContourStatement
    {E : Type} [TopologicalSpace E] [CompactSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] : Prop :=
  ∀ (p : E) (ρ : E → ℝ)
    (hρ : ∀ a : E, ContDiffOn ℝ ∞
      (fun z : ℂ => ρ ((extChartAt 𝓘(ℂ) a).symm z)) (extChartAt 𝓘(ℂ) a).target)
    (hsupp : tsupport ρ ⊆ (chartAt ℂ p).source),
    (∀ᶠ x in 𝓝 p, ρ x = 1) →
    ∀ (h : HolOn (overlapOpen p (chartSourceOpen p)))
      (s : ActualCanonicalSection E) (R : ℝ) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target),
      (∫ z : ℂ, -(2 * Complex.I) *
        LocalDbar.dbar (fun w => (actualChartCutoffTest p ρ hρ hsupp w : ℂ)) z *
        (actualChartOverlapValue p h z *
          actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ)))) =
        actualOverlapContourPairing p R hR htarget h s

/-- The exact repaired chart contour contract, with no Hausdorff hypothesis. -/
theorem actualChartCutoffContour
    {E : Type} [TopologicalSpace E] [CompactSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualChartCutoffContourStatement (E := E) := by
  classical
  intro p ρ hρ hsupp hone h s R hR htarget
  have hcont := continuousAt_extChartAt_symm (I := 𝓘(ℂ)) p
  have hp : (extChartAt 𝓘(ℂ) p) p = (chartAt ℂ p) p := by simp
  have he : ∀ᶠ z in 𝓝 ((chartAt ℂ p) p), ρ ((extChartAt 𝓘(ℂ) p).symm z) = 1 := by
    have ht := hcont.eventually (by simpa using hone)
    simpa [hp] using ht
  have ht : (extChartAt 𝓘(ℂ) p).target ∈ 𝓝 ((chartAt ℂ p) p) := by
    simpa [hp] using extChartAt_target_mem_nhds (I := 𝓘(ℂ)) p
  have hχ : ∀ᶠ z in 𝓝 ((chartAt ℂ p) p), actualChartCutoffTest p ρ hρ hsupp z = 1 := by
    filter_upwards [he, ht] with z hz hzt
    change (if z ∈ (extChartAt 𝓘(ℂ) p).target then
      ρ ((extChartAt 𝓘(ℂ) p).symm z) else 0) = 1
    rw [ite_eq_left hzt, hz]
  apply LocalDbar.actualPlanarCutoffContour (actualChartTestOpen p)
    ((chartAt ℂ p) p) (by simp [actualChartTestOpen]) (actualChartCutoffTest p ρ hρ hsupp) hχ
    (fun z => actualChartOverlapValue p h z *
      actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ)))
  · intro z hz
    apply actualChartOverlap_times_section_analyticAt p h s z
    · simpa [actualChartTestOpen] using hz.1
    · simpa using hz.2
  · exact hR
  · simpa [actualChartTestOpen] using htarget

end CanonicalDimensionTwo
