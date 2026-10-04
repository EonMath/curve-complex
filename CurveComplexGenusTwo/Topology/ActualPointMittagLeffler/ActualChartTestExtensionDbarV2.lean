import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartTestFormExtensionV2
open TopologicalSpace SameAtlasAnalyticCohomology
open scoped Manifold ContDiff Bundle Distributions Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace CanonicalDimensionTwo
universe u
theorem actualChartTestExtension_dbar
    {E : Type u} [TopologicalSpace E] [T2Space E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (a b x : E)
    (hx : x ∈ (extChartAt 𝓘(ℂ) b).source)
    (φ : TestFunction (actualChartTestOpen a) ℂ ⊤) :
    chartDbar b (actualChartTestScalarExtension a φ).1 x =
      (actualChartTestFormExtension a (LocalDbar.testDbar _ φ)).1 b x := by
  classical
  let ca := extChartAt 𝓘(ℂ) a
  let cb := extChartAt 𝓘(ℂ) b
  let f : SmoothZero E := actualChartTestScalarExtension a φ
  by_cases ha : x ∈ ca.source
  · have hfa : chartDbar a f.1 x = LocalDbar.dbar φ (ca x) := by
      have he : (fun z => f.1 (ca.symm z)) =ᶠ[𝓝 (ca x)] (φ : ℂ → ℂ) := by
        filter_upwards [(isOpen_extChartAt_target a).mem_nhds (ca.map_source ha)] with z hz
        change (if ca.symm z ∈ ca.source then φ (ca (ca.symm z)) else 0) = φ z
        rw [ite_eq_left (ca.map_target hz), ca.right_inv hz]
      change ((fderiv ℝ (fun z => f.1 (ca.symm z)) (ca x)) 1 +
        Complex.I * (fderiv ℝ (fun z => f.1 (ca.symm z)) (ca x)) Complex.I) / 2 = _
      rw [he.fderiv_eq]
      rfl
    have hf : ContDiffAt ℝ 1 (fun z => f.1 (ca.symm z)) (ca x) :=
      ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds (ca.map_source ha))).of_le (by simp)
    change chartDbar b f.1 x = (if x ∈ ca.source ∧ x ∈ cb.source then
      (LocalDbar.testDbar _ φ) (ca x) / star (chartTransitionDerivative a b x) else 0)
    rw [ite_eq_left ⟨ha, hx⟩, chartDbar_transition a b x f.1 ha hx hf, hfa,
      LocalDbar.testDbar_apply]
  · have hK : IsCompact (ca.symm '' tsupport (φ : ℂ → ℂ)) :=
      φ.hasCompactSupport.image_of_continuousOn
        ((continuousOn_extChartAt_symm a).mono φ.tsupport_subset)
    have hk : x ∉ ca.symm '' tsupport (φ : ℂ → ℂ) := by
      rintro ⟨z, hz, he⟩
      apply ha
      rw [← he]
      exact ca.map_target (φ.tsupport_subset hz)
    have hcont := continuousAt_extChartAt_symm' (I := 𝓘(ℂ)) hx
    have hn : ∀ᶠ z in 𝓝 (cb x), cb.symm z ∉ ca.symm '' tsupport (φ : ℂ → ℂ) := by
      have ht : (ca.symm '' tsupport (φ : ℂ → ℂ))ᶜ ∈ 𝓝 (cb.symm (cb x)) := by
        simpa only [cb.left_inv hx] using hK.isClosed.isOpen_compl.mem_nhds hk
      exact hcont.preimage_mem_nhds ht
    have he : (fun z => f.1 (cb.symm z)) =ᶠ[𝓝 (cb x)] fun _ => (0 : ℂ) := by
      filter_upwards [hn] with z hz
      change (if cb.symm z ∈ ca.source then φ (ca (cb.symm z)) else 0) = 0
      split_ifs with hs
      · by_contra hv
        exact hz ⟨ca (cb.symm z), subset_tsupport (φ : ℂ → ℂ) hv, ca.left_inv hs⟩
      · rfl
    change chartDbar b f.1 x = (if x ∈ ca.source ∧ x ∈ cb.source then
      (LocalDbar.testDbar _ φ) (ca x) / star (chartTransitionDerivative a b x) else 0)
    simp only [ha, false_and, ite_false]
    change ((fderiv ℝ (fun z => f.1 (cb.symm z)) (cb x)) 1 +
      Complex.I * (fderiv ℝ (fun z => f.1 (cb.symm z)) (cb x)) Complex.I) / 2 = 0
    rw [he.fderiv_eq]
    simp

end CanonicalDimensionTwo
