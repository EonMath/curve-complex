import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseCompleteContinuousFlow
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseNormalizedRegularBand

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function Metric Filter

theorem actual_scalar_solution_height_on_open_band
    (f d : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (d t) t)
    (a b : ℝ) (ha : a < f 0) (hb : f 0 < b)
    (hunit : ∀ t, f t ∈ Icc a b → d t = 1) :
    ∀ t ∈ Ioo (a - f 0) (b - f 0), f t = f 0 + t := by
  let g : ℝ → ℝ := fun t => f 0 + t
  let T : Set ℝ := Ioo (a - f 0) (b - f 0)
  let S : Set ℝ := {t | f t = g t} ∩ T
  have hfc : Continuous f := continuous_iff_continuousAt.mpr
    (fun t => (hf t).continuousAt)
  have hgc : Continuous g := continuous_const.add continuous_id
  have hzero : (0 : ℝ) ∈ T := ⟨by linarith, by linarith⟩
  have hsub : T ⊆ S := by
    apply isPreconnected_Ioo.subset_of_closure_inter_subset (u := S)
      (s := T) ?_ ⟨0, hzero, by simp [S, g, hzero]⟩ (by
      intro t ht
      have hclosed : IsClosed {t | f t = g t} := isClosed_eq hfc hgc
      exact ⟨(closure_minimal inter_subset_left hclosed) ht.1, ht.2⟩)
    · rw [isOpen_iff_mem_nhds]
      intro t ht
      have hint : f t ∈ Ioo a b := by
        rw [ht.1]
        dsimp [g]
        exact ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
      have hnear : ∀ᶠ u in 𝓝 t, f u ∈ Ioo a b :=
        hfc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hint)
      have heq : f =ᶠ[𝓝 t] g := by
        apply ODE_solution_unique_of_eventually
          (v := fun (_ : ℝ) (_ : ℝ) => (1 : ℝ)) (s := fun _ => univ)
          (K := 0)
        · exact .of_forall (fun _ => (LipschitzWith.const (1 : ℝ)).lipschitzOnWith)
        · filter_upwards [hnear] with u hu
          exact ⟨by simpa only [hunit u (Ioo_subset_Icc_self hu)] using hf u, mem_univ _⟩
        · exact .of_forall (fun u => ⟨by simpa [g, Pi.add_def, Function.id_def] using
            (hasDerivAt_const u (f 0)).add (hasDerivAt_id u), mem_univ _⟩)
        · exact ht.1
      exact (heq.and (isOpen_Ioo.mem_nhds ht.2)).mono (fun u hu => hu)
  intro t ht
  exact (hsub ht).1

theorem actual_scalar_solution_height_on_closed_band
    (f d : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (d t) t)
    (a b : ℝ) (ha : a < f 0) (hb : f 0 < b)
    (hunit : ∀ t, f t ∈ Icc a b → d t = 1) :
    ∀ t ∈ Icc (a - f 0) (b - f 0), f t = f 0 + t := by
  have heq := actual_scalar_solution_height_on_open_band f d hf a b ha hb hunit
  have hclosed : IsClosed {t | f t = f 0 + t} :=
    isClosed_eq (continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt))
      (continuous_const.add continuous_id)
  have hs : closure (Ioo (a - f 0) (b - f 0)) ⊆ {t | f t = f 0 + t} :=
    closure_minimal heq hclosed
  rw [closure_Ioo (by linarith : a - f 0 ≠ b - f 0)] at hs
  exact hs

theorem actual_normalized_complete_flow_height_on_band
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Y : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (φ : Flow ℝ E) (hcurve : ∀ x, IsMIntegralCurve (fun t => φ t x) Y)
    (a b : ℝ)
    (hunit : ∀ x, F x ∈ Icc a b →
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x)) = 1)
    (x : E) (ha : a < F x) (hb : F x < b) :
    ∀ t ∈ Icc (a - F x) (b - F x), F (φ t x) = F x + t := by
  let f : ℝ → ℝ := fun t => F (φ t x)
  let d : ℝ → ℝ := fun t =>
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F (φ t x)))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F (φ t x)) (Y (φ t x)))
  have hf : ∀ t, HasDerivAt f (d t) t := fun t =>
    actual_integral_curve_scalar_height_derivative F hF Y (fun s => φ s x)
      t ((hcurve x).isMIntegralCurveAt t)
  have h0 : f 0 = F x := by simp [f]
  simpa only [h0] using actual_scalar_solution_height_on_closed_band
    f d hf a b (by simpa only [h0] using ha) (by simpa only [h0] using hb)
    (fun t ht => hunit (φ t x) ht)
