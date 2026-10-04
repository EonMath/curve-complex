import CurveComplexGenusTwo.Topology.ActualTwoOpenCechBridge.ActualChartTestOpen

open TopologicalSpace SameAtlasAnalyticCohomology
open MeasureTheory Filter
open scoped Manifold ContDiff Bundle Distributions Topology

namespace CanonicalDimensionTwo

universe u

/-- Pull back a real smooth chart-supported weight and extend it by zero.
Compactness is an explicit binder of this universe-polymorphic constructor. -/
noncomputable def actualChartCutoffTest
    {E : Type u} [TopologicalSpace E] [CompactSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ : E → ℝ)
    (hρ : ∀ a : E, ContDiffOn ℝ ∞
      (fun z : ℂ => ρ ((extChartAt 𝓘(ℂ) a).symm z)) (extChartAt 𝓘(ℂ) a).target)
    (hsupp : tsupport ρ ⊆ (chartAt ℂ p).source) :
    TestFunction (actualChartTestOpen p) ℝ ⊤ := by
  classical
  let c := extChartAt 𝓘(ℂ) p
  let f : ℂ → ℝ := fun z => if z ∈ c.target then ρ (c.symm z) else 0
  have hs : tsupport ρ ⊆ c.source := by simpa [c] using hsupp
  have hK : IsCompact (c '' tsupport ρ) :=
    (isClosed_tsupport ρ).isCompact.image_of_continuousOn
      ((continuousOn_extChartAt p).mono hs)
  have hsub : tsupport f ⊆ c '' tsupport ρ := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_cases hzt : z ∈ c.target
    · refine ⟨c.symm z, subset_tsupport ρ ?_, c.right_inv hzt⟩
      simpa [f, hzt, Function.mem_support] using hz
    · simp [f, hzt, Function.mem_support] at hz
  have ht : tsupport f ⊆ c.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hsub hz
    exact c.map_source (hs hx)
  have hd : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ c.target
    · have he : f =ᶠ[𝓝 z] fun w => ρ (c.symm w) := by
        filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
        exact ite_eq_left (show w ∈ c.target from hw)
      exact ((hρ p).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).congr_of_eventuallyEq he
    · have he := notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (ht h))
      exact contDiffAt_const.congr_of_eventuallyEq he
  exact ⟨fun z => if z ∈ (extChartAt 𝓘(ℂ) p).target
    then ρ ((extChartAt 𝓘(ℂ) p).symm z) else 0,
    hd, hK.of_isClosed_subset (isClosed_tsupport f) hsub, ht⟩

/-- The original neighborhood value assertion, generalized from Type to
Type u together with its literal cutoff constructor. -/
theorem actualChartCutoffTest_one_near
    {E : Type u} [TopologicalSpace E] [T2Space E] [CompactSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (p : E) (ρ : E → ℝ)
    (hρ : ∀ a : E, ContDiffOn ℝ ∞
      (fun z : ℂ => ρ ((extChartAt 𝓘(ℂ) a).symm z)) (extChartAt 𝓘(ℂ) a).target)
    (hsupp : tsupport ρ ⊆ (chartAt ℂ p).source)
    (hone : ∀ᶠ x in 𝓝 p, ρ x = 1) :
    ∀ᶠ z in 𝓝 ((chartAt ℂ p) p), actualChartCutoffTest p ρ hρ hsupp z = 1 := by
  classical
  have hcont := continuousAt_extChartAt_symm (I := 𝓘(ℂ)) p
  have hp : (extChartAt 𝓘(ℂ) p) p = (chartAt ℂ p) p := by simp
  have he : ∀ᶠ z in 𝓝 ((chartAt ℂ p) p), ρ ((extChartAt 𝓘(ℂ) p).symm z) = 1 := by
    have h := hcont.eventually (by simpa using hone)
    simpa [hp] using h
  have ht : (extChartAt 𝓘(ℂ) p).target ∈ 𝓝 ((chartAt ℂ p) p) := by
    simpa [hp] using extChartAt_target_mem_nhds (I := 𝓘(ℂ)) p
  filter_upwards [he, ht] with z hz hzt
  change (if z ∈ (extChartAt 𝓘(ℂ) p).target then
    ρ ((extChartAt 𝓘(ℂ) p).symm z) else 0) = 1
  rw [ite_eq_left hzt, hz]

end CanonicalDimensionTwo
