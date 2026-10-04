import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualComplexMorseExistence
import CurveComplexGenusTwo.Topology.ActualSmoothMorseNormalForm.ActualMorseChartPullbackSmooth
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open scoped Manifold ContDiff

/-!
Consumer for the ORIGINAL caller's charted-space datum.
Its proof depends on the smooth Morse existence theorem.
Source: Milnor, Morse Theory, §2, Lemma 2.2; atlas compatibility is the usual
closure under smooth coordinate changes, encoded by Mathlib's maximal atlas.
No replacement `ChartedSpace` is installed: every preferred `chartAt` below
uses the one literal input `A`.
-/

/-- Apply the real smooth Morse lemma to the pullback of this exact `F` through
this exact preferred chart of the input atlas `A`. The coordinate chart on `E`
is the composition `(chartAt ℂ p).trans e`, generally not `chartAt ℂ p` itself.
It belongs to the REAL smooth maximal atlas associated to `A` and retains
smoothness in both directions. Real Morse charts need not be holomorphic. -/
theorem actual_same_atlas_smooth_morse_coordinates
    (E : Type) [TopologicalSpace E]
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA;
    ∀ (F : E → ℝ), ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F →
      ∀ (p x : E), x ∈ (chartAt ℂ p).source →
        gradient (fun z => F ((chartAt ℂ p).symm z)) ((chartAt ℂ p) x) = 0 →
        (fderiv ℝ (gradient (fun z => F ((chartAt ℂ p).symm z)))
          ((chartAt ℂ p) x)).det ≠ 0 →
        ∃ (k : Fin 3) (e : OpenPartialHomeomorph ℂ ℂ),
          IsActualComplexSmoothMorseNormalForm
            (fun z => F ((chartAt ℂ p).symm z))
            (chartAt ℂ p).target ((chartAt ℂ p) x) k e ∧
          let c := (chartAt ℂ p).trans e;
          x ∈ c.source ∧ c x = 0 ∧
          c ∈ IsManifold.maximalAtlas 𝓘(ℝ,ℂ) ∞ E ∧
          ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source ∧
          ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target ∧
          ∀ y ∈ c.source, F y = F x + actualComplexMorseQuadratic k (c y) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := actual_same_atlas_complex_is_real_smooth E hA
  intro F hF p x hx hcritical hnondegenerate
  obtain ⟨k, e, he⟩ := actual_complex_smooth_morse_normal_form
    (fun z => F ((chartAt ℂ p).symm z)) (chartAt ℂ p).target ((chartAt ℂ p) x)
    (chartAt ℂ p).open_target ((chartAt ℂ p).map_source hx)
    (actual_smooth_scalar_chart_pullback_contDiffOn_infty p F hF)
    hcritical hnondegenerate
  refine ⟨k, e, he, ?_⟩
  let c := (chartAt ℂ p).trans e
  have hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source := by
    exact he.contDiffOn.contMDiffOn.comp
      (contMDiffOn_chart.mono (fun y hy => hy.1)) (fun y hy => hy.2)
  have hcs : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target := by
    exact contMDiffOn_chart_symm.comp
      (he.contDiffOn_symm.contMDiffOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)
  refine ⟨⟨hx, he.center_mem_source⟩, he.center_eq_zero,
    (IsManifold.mem_maximalAtlas_iff_contMDiffOn c).mpr ⟨hc, hcs⟩, hc, hcs, ?_⟩
  intro y hy
  change F y = F x + actualComplexMorseQuadratic k (e ((chartAt ℂ p) y))
  simpa only [(chartAt ℂ p).left_inv hy.1, (chartAt ℂ p).left_inv hx] using
    he.normal_form ((chartAt ℂ p) y) hy.2
