import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SmoothJetTopology
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.ChartFrameTransition
import CurveComplexGenusTwo.Topology.ActualTwoOpenCechBridge.ActualChartTestOpen

open TopologicalSpace SameAtlasAnalyticCohomology
open scoped Manifold ContDiff Bundle Distributions Topology

namespace CanonicalDimensionTwo

universe u

/-- Literal scalar zero extension through the supplied complex chart.
Hausdorffness is an explicit constructor binder, retained with sorry proofs. -/
noncomputable def actualChartTestScalarExtension
    {E : Type u} [TopologicalSpace E] [T2Space E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] (a : E) :
    TestFunction (actualChartTestOpen a) ℂ ⊤ →ₗ[ℂ] SmoothZero E where
  toFun φ := by
    classical
    let c := extChartAt 𝓘(ℂ) a
    let f : E → ℂ := fun x => if x ∈ c.source then φ (c x) else 0
    have hK : IsCompact (c.symm '' tsupport (φ : ℂ → ℂ)) :=
      φ.hasCompactSupport.image_of_continuousOn
        ((continuousOn_extChartAt_symm a).mono φ.tsupport_subset)
    have hsub : tsupport f ⊆ c.symm '' tsupport (φ : ℂ → ℂ) := by
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_cases hxs : x ∈ c.source
      · refine ⟨c x, subset_tsupport (φ : ℂ → ℂ) ?_, c.left_inv hxs⟩
        simpa [f, hxs, Function.mem_support] using hx
      · simp [f, hxs, Function.mem_support] at hx
    have hs : tsupport f ⊆ c.source := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := hsub hx
      exact c.map_target (φ.tsupport_subset hz)
    exact ⟨fun x => if x ∈ (extChartAt 𝓘(ℂ) a).source
      then φ ((extChartAt 𝓘(ℂ) a) x) else 0, by
      intro b z hz
      have hcont := continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz
      by_cases ha : (extChartAt 𝓘(ℂ) b).symm z ∈ c.source
      · have htrans : ContDiffAt ℂ ∞
            (c ∘ (extChartAt 𝓘(ℂ) b).symm) z := by
          have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) a b
            (show z ∈ ((extChartAt 𝓘(ℂ) b).symm ≫ c).source from ⟨hz, ha⟩)
          simpa [c, contDiffWithinAt_univ] using h
        have he : (fun w => f ((extChartAt 𝓘(ℂ) b).symm w)) =ᶠ[𝓝 z]
            (φ ∘ c ∘ (extChartAt 𝓘(ℂ) b).symm) := by
          filter_upwards [hcont.preimage_mem_nhds (extChartAt_source_mem_nhds' ha)] with w hw
          exact ite_eq_left (show (extChartAt 𝓘(ℂ) b).symm w ∈ c.source from hw)
        exact ((φ.contDiff.contDiffAt.comp z (htrans.restrict_scalars ℝ)).congr_of_eventuallyEq he).contDiffWithinAt
      · have hn : (extChartAt 𝓘(ℂ) b).symm z ∉ tsupport f := fun hx => ha (hs hx)
        have he : (fun w => f ((extChartAt 𝓘(ℂ) b).symm w)) =ᶠ[𝓝 z] fun _ => 0 :=
          hcont.eventually (notMem_tsupport_iff_eventuallyEq.mp hn)
        exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt⟩
  map_add' := by
    classical
    intro φ ψ
    apply Subtype.ext
    funext x
    dsimp only
    split_ifs with hx <;> simp_all
  map_smul' := by
    classical
    intro r φ
    apply Subtype.ext
    funext x
    dsimp only
    split_ifs with hx <;> simp_all

end CanonicalDimensionTwo
