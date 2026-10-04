import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualGlobalBumpStage
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualOneCoreTangentRegularization
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualTangentPriorCoreStability
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualFiniteCoreInduction
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

theorem actual_finite_bump_cover_regular_tangent_field
    {E ι : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [CompactSpace E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    [Fintype ι]
    (cover : SmoothBumpCovering ι 𝓘(ℝ,ℂ) E Set.univ)
    (hsource : ∀ i (x : E), cover i x = 1 →
      x ∈ (chartAt ℂ (cover.c i)).source) :
    ∃ V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x,
      ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (V x)) ∧
      ∀ i (x : E), cover i x = 1 → V x = 0 →
        (fderiv ℝ
          (fun z : ℂ =>
            let y := (chartAt ℂ (cover.c i)).symm z
            (trivializationAt ℂ (fun u : E => TangentSpace 𝓘(ℝ,ℂ) u) (cover.c i)
              (TotalSpace.mk' ℂ y (V y))).2)
          ((chartAt ℂ (cover.c i)) x)).det ≠ 0 := by
  let X := {V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x //
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x))}
  let a0 : X := ⟨fun _ => 0, contMDiff_zeroSection ℝ _⟩
  let update (a : X) (i : ι) (c : ℂ) : X :=
    ⟨fun x => a.val x + cover i x •
      (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (cover.c i)).symmL ℝ x c,
      (actual_global_bump_stage (cover.c i) (cover i) a.val a.property c).1⟩
  let P (i : ι) (a : X) : Prop :=
    ∀ x : E, cover i x = 1 → a.val x = 0 →
      (fderiv ℝ
        (fun z : ℂ =>
          let y := (chartAt ℂ (cover.c i)).symm z
          (trivializationAt ℂ (fun u : E => TangentSpace 𝓘(ℝ,ℂ) u) (cover.c i)
            (TotalSpace.mk' ℂ y (a.val y))).2)
        ((chartAt ℂ (cover.c i)) x)).det ≠ 0
  have hzero (a : X) (i : ι) : update a i 0 = a := by
    apply Subtype.ext
    funext x
    simp [update]
  have hlocal (a : X) (i : ι) (r : ℝ) (hr : 0 < r) :
      ∃ c : ℂ, ‖c‖ < r ∧ P i (update a i c) := by
    obtain ⟨c, hc, hreg⟩ := actual_one_core_tangent_regularization
      (cover.c i) (cover i) a.val a.property r hr
    exact ⟨c, hc, hreg⟩
  have hstable (a : X) (i j : ι) : IsOpen {c : ℂ | P j (update a i c)} := by
    let chart := chartAt ℂ (cover.c j)
    let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (cover.c j)
    let K : Set ℂ := chart '' {x : E | cover j x = 1}
    have hcore : IsCompact {x : E | cover j x = 1} :=
      (isClosed_eq (cover j).continuous continuous_const).isCompact
    have hK : IsCompact K :=
      hcore.image_of_continuousOn (chart.continuousOn.mono
        (fun x hx => hsource j x hx))
    have hKU : K ⊆ chart.target := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact chart.map_source (hsource j x hx)
    rw [isOpen_iff_mem_nhds]
    intro c0 hc0
    let W0 : X := update a i c0
    have hregK : ∀ z ∈ K,
        (e (TotalSpace.mk' ℂ (chart.symm z) (W0.val (chart.symm z)))).2 = 0 →
        (fderiv ℝ
          (fun w : ℂ => (e (TotalSpace.mk' ℂ (chart.symm w)
            (W0.val (chart.symm w)))).2) z).det ≠ 0 := by
      intro z hz hz0
      obtain ⟨x, hx, rfl⟩ := hz
      have hxsource : x ∈ chart.source := hsource j x hx
      have hxbase : x ∈ e.baseSet := by simpa [e] using hxsource
      have hlocalzero : W0.val x = 0 := by
        have hmap : e.continuousLinearMapAt ℝ x (W0.val x) = 0 := by
          rw [e.continuousLinearMapAt_apply_of_mem (R := ℝ) hxbase]
          rw [chart.left_inv hxsource] at hz0
          exact hz0
        have hinv := congrArg (e.symmL ℝ x) hmap
        simpa only [e.symmL_continuousLinearMapAt hxbase, map_zero] using hinv
      have hp := hc0 x hx hlocalzero
      simpa only [chart.left_inv hxsource] using hp
    obtain ⟨r, hr, hpreserve⟩ := actual_tangent_prior_core_stability
      (cover.c j) (cover.c i) (cover i) W0.val W0.property K hK hKU hregK
    have hball : Metric.ball c0 r ⊆ {c : ℂ | P j (update a i c)} := by
      intro c hc
      let d := c - c0
      have hd : ‖d‖ < r := by
        simpa only [Metric.mem_ball, dist_eq_norm, d] using hc
      have hupdate : update a i c = update W0 i d := by
        apply Subtype.ext
        funext x
        simp only [update, W0, d, Subtype.coe_mk]
        have hlin :
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y)
              (cover.c i)).symmL ℝ x (c0 + (c - c0)) =
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y)
              (cover.c i)).symmL ℝ x c0 +
            (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y)
              (cover.c i)).symmL ℝ x (c - c0) := by rw [map_add]
        have hadd : c0 + (c - c0) = c := by abel
        rw [hadd] at hlin
        rw [hlin, smul_add]
        abel
      change P j (update a i c)
      rw [hupdate]
      intro x hx hx0
      have hz : chart x ∈ K := ⟨x, hx, rfl⟩
      have hz0 :
          (e (TotalSpace.mk' ℂ (chart.symm (chart x))
            ((update W0 i d).val (chart.symm (chart x))))).2 = 0 := by
        have hxsource : x ∈ chart.source := hsource j x hx
        have hxbase : x ∈ e.baseSet := by simpa [e] using hxsource
        rw [chart.left_inv hxsource]
        rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hxbase, hx0, map_zero]
      have hp := hpreserve d hd (chart x) hz hz0
      have hxsource : x ∈ chart.source := hsource j x hx
      simpa only [chart.left_inv hxsource] using hp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds c0 hr) hball
  obtain ⟨a, ha⟩ := actual_finite_core_state_induction
    a0 Finset.univ P update hzero hlocal hstable
  exact ⟨a.val, a.property, fun i x => ha i (Finset.mem_univ i) x⟩

#print axioms actual_finite_bump_cover_regular_tangent_field
