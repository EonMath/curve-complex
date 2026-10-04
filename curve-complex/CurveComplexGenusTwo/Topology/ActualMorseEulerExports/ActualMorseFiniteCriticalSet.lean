import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSameAtlasMorseExistence
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualMorseFiniteCriticalCore

open scoped Manifold ContDiff
open Set InnerProductSpace

theorem actual_morse_finite_chart_core_critical_set
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [Fintype ι]
    (p : ι → E) (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i))
    (hsource : ∀ i, K i ⊆ (chartAt ℂ (p i)).source)
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (hregular : ∀ i x, x ∈ K i →
      gradient (fun z => F ((chartAt ℂ (p i)).symm z))
        ((chartAt ℂ (p i)) x) = 0 →
      (fderiv ℝ (gradient (fun z => F ((chartAt ℂ (p i)).symm z)))
        ((chartAt ℂ (p i)) x)).det ≠ 0) :
    {x : E | ∃ i, x ∈ K i ∧
      gradient (fun z => F ((chartAt ℂ (p i)).symm z))
        ((chartAt ℂ (p i)) x) = 0}.Finite := by
  have hfinite (i : ι) :
      {x : E | x ∈ K i ∧
        gradient (fun z => F ((chartAt ℂ (p i)).symm z))
          ((chartAt ℂ (p i)) x) = 0}.Finite := by
    let c := chartAt ℂ (p i)
    let f : ℂ → ℝ := fun z => F (c.symm z)
    let g : ℂ → ℂ := gradient f
    let Kc : Set ℂ := c '' K i
    have hKc : IsCompact Kc :=
      (hK i).image_of_continuousOn (c.continuousOn.mono (hsource i))
    have htarget : Kc ⊆ c.target := by
      rintro z ⟨x, hx, rfl⟩
      exact c.map_source (hsource i hx)
    have hf : ContDiffOn ℝ 2 f c.target :=
      actual_smooth_scalar_chart_pullback_contDiffOn (p i) F hF
    have hg : ContDiffOn ℝ 1 g c.target :=
      actual_gradient_contDiffOn_of_scalar_contDiffOn f c.target c.open_target hf
    have hregc : ∀ z ∈ Kc, g z = 0 → (fderiv ℝ g z).det ≠ 0 := by
      rintro z ⟨x, hx, rfl⟩ hz
      exact hregular i x hx hz
    have hfinitec : {z : ℂ | z ∈ Kc ∧ g z = 0}.Finite :=
      actual_compact_regular_zero_set_finite g c.target c.open_target hg
        Kc hKc htarget hregc
    have himage : (c.symm '' {z : ℂ | z ∈ Kc ∧ g z = 0}).Finite :=
      hfinitec.image c.symm
    convert himage using 1
    ext x
    constructor
    · intro hx
      have hxc : c x ∈ Kc := ⟨x, hx.1, rfl⟩
      have hxs : x ∈ c.source := hsource i hx.1
      exact ⟨c x, ⟨hxc, hx.2⟩, c.left_inv hxs⟩
    · rintro ⟨z, ⟨⟨y, hy, rfl⟩, hz⟩, rfl⟩
      have hys : y ∈ c.source := hsource i hy
      rw [c.left_inv hys]
      exact ⟨hy, hz⟩
  have hUnion : (⋃ i, {x : E | x ∈ K i ∧
      gradient (fun z => F ((chartAt ℂ (p i)).symm z))
        ((chartAt ℂ (p i)) x) = 0}).Finite :=
    Set.finite_iUnion hfinite
  convert hUnion using 1
  ext x
  simp [Set.mem_iUnion]

