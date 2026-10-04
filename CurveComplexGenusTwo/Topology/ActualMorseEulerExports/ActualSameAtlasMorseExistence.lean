import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseOneCoreRegularization
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseOtherCoreStability
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualFiniteCoreInduction

open scoped Manifold ContDiff
open Set InnerProductSpace Filter Topology

theorem actual_same_atlas_morse_function_from_plateau_cover
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (K U : ι → Set E) (b : ι → E → ℝ)
    (hK : ∀ i, IsCompact (K i))
    (hsource : ∀ i, K i ⊆ (chartAt ℂ (p i)).source)
    (hUopen : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i)
    (hb : ∀ i, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b i))
    (hbsupport : ∀ i, tsupport (b i) ⊆ (chartAt ℂ (p i)).source)
    (hbone : ∀ i, ∀ x ∈ U i, b i x = 1)
    (hcover : ∀ x : E, ∃ i, x ∈ K i) :
    ∃ F : E → ℝ,
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F ∧
      (∀ i x, x ∈ K i →
        gradient (fun z => F ((chartAt ℂ (p i)).symm z))
          ((chartAt ℂ (p i)) x) = 0 →
        (fderiv ℝ (gradient (fun z => F ((chartAt ℂ (p i)).symm z)))
          ((chartAt ℂ (p i)) x)).det ≠ 0) ∧
      ∀ x : E, ∃ i, x ∈ K i ∧
      (
        gradient (fun z => F ((chartAt ℂ (p i)).symm z))
          ((chartAt ℂ (p i)) x) = 0 →
        (fderiv ℝ (gradient (fun z => F ((chartAt ℂ (p i)).symm z)))
          ((chartAt ℂ (p i)) x)).det ≠ 0) := by
  let X := {F : E → ℝ // ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F}
  let initial : X := ⟨fun _ => 0, contMDiff_const⟩
  let update (F : X) (i : ι) (c : ℂ) : X :=
    ⟨fun x => F.val x + b i x * (toDual ℝ ℂ c) ((chartAt ℂ (p i)) x),
      F.property.add (actual_chart_linear_bump_smooth (p i) (b i)
        (toDual ℝ ℂ c) (hb i) (hbsupport i))⟩
  let P (i : ι) (F : X) : Prop :=
    ∀ z ∈ (chartAt ℂ (p i)) '' K i,
    gradient (fun z => F.val ((chartAt ℂ (p i)).symm z))
      z = 0 →
    (fderiv ℝ (gradient (fun z => F.val ((chartAt ℂ (p i)).symm z)))
      z).det ≠ 0
  have hzero : ∀ F i, update F i 0 = F := by
    intro F i
    apply Subtype.ext
    funext x
    simp [update]
  have hlocal : ∀ F i (r : ℝ), 0 < r →
      ∃ c : ℂ, ‖c‖ < r ∧ P i (update F i c) := by
    intro F i r hr
    obtain ⟨c, hc, hreg⟩ := actual_morse_one_chart_core_nondegenerate
      (p i) F.val F.property (b i) (U i) (hUopen i) (hbone i) r hr
    refine ⟨c, hc, ?_⟩
    intro z hz hzero'
    obtain ⟨x, hx, rfl⟩ := hz
    let chart := chartAt ℂ (p i)
    have hxs : x ∈ chart.source := hsource i hx
    have hz : chart x ∈ chart.target := chart.map_source hxs
    have hzu : chart.symm (chart x) ∈ U i := by
      rw [chart.left_inv hxs]
      exact hKU i hx
    have hreg' := hreg (chart x) ⟨hz, hzu⟩
    change gradient (fun z =>
      F.val (chart.symm z) + b i (chart.symm z) *
        (toDual ℝ ℂ c) (chart (chart.symm z))) (chart x) = 0 at hzero'
    have heq : (fun z =>
      F.val (chart.symm z) + b i (chart.symm z) *
        (toDual ℝ ℂ c) (chart (chart.symm z))) =ᶠ[𝓝 (chart x)]
        (fun z => F.val (chart.symm z) + b i (chart.symm z) *
          (toDual ℝ ℂ c) z) := by
      filter_upwards [chart.open_target.mem_nhds hz] with z hz'
      rw [chart.right_inv hz']
    have hzero'' : gradient (fun z =>
        F.val (chart.symm z) + b i (chart.symm z) *
          (toDual ℝ ℂ c) z) (chart x) = 0 := by
      rw [← Filter.EventuallyEq.gradient_eq heq]
      exact hzero'
    have hdet := hreg' hzero''
    change (fderiv ℝ (gradient (fun z =>
      F.val (chart.symm z) + b i (chart.symm z) *
        (toDual ℝ ℂ c) (chart (chart.symm z)))) (chart x)).det ≠ 0
    rw [Filter.EventuallyEq.fderiv_eq (Filter.EventuallyEq.gradient heq)]
    exact hdet
  have hstable : ∀ F i j, IsOpen {c : ℂ | P j (update F i c)} := by
    intro F i j
    exact actual_morse_other_core_parameter_stability
      (p i) (p j) F.val (b i) F.property (hb i) (hbsupport i)
      (K j) (hK j) (hsource j)
  obtain ⟨F, hF⟩ := actual_finite_core_state_induction
    initial Finset.univ P update hzero hlocal hstable
  refine ⟨F.val, F.property, ?_, ?_⟩
  · intro i x hx
    exact hF i (Finset.mem_univ i)
      ((chartAt ℂ (p i)) x) ⟨x, hx, rfl⟩
  · intro x
    obtain ⟨i, hx⟩ := hcover x
    exact ⟨i, hx, hF i (Finset.mem_univ i)
      ((chartAt ℂ (p i)) x) ⟨x, hx, rfl⟩⟩

