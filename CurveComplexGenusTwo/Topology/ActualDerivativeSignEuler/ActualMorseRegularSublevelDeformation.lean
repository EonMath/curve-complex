import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseFlowBandHeight
import Mathlib.Topology.Homotopy.Equiv

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function Metric Filter

theorem actual_normalized_regular_band_sublevel_deformation
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (Y : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (φ : Flow ℝ E) (hcurve : ∀ x, IsMIntegralCurve (fun t => φ t x) Y)
    (a₀ a b b₀ : ℝ) (ha : a₀ < a) (hab : a ≤ b) (hb : b < b₀)
    (hunit : ∀ x, F x ∈ Icc a₀ b₀ →
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x)) = 1) :
    ∃ (r : C({x : E // F x ≤ b}, {x : E // F x ≤ a}))
      (H : ContinuousMap.Homotopy (ContinuousMap.id {x : E // F x ≤ b})
        (ContinuousMap.comp
          ⟨fun x => ⟨x.1, x.2.trans hab⟩, continuous_subtype_val.subtype_mk _⟩ r)),
      (∀ (x : E) (hx : F x ≤ a), (r ⟨x, hx.trans hab⟩).1 = x) ∧
      (∀ u x, F x.1 ≤ a → (H (u, x)).1 = x.1) := by
  let τ : E → ℝ := fun x => max (F x - a) 0
  let D : unitInterval × {x : E // F x ≤ b} → E :=
    fun q => φ (-((q.1 : ℝ) * τ q.2.1)) q.2.1
  have hτ : Continuous τ := (hF.continuous.sub continuous_const).max continuous_const
  have hD : Continuous D := φ.continuous
    (((continuous_subtype_val.comp continuous_fst).mul
      (hτ.comp (continuous_subtype_val.comp continuous_snd))).neg)
    (continuous_subtype_val.comp continuous_snd)
  have hfixed (u : unitInterval) (x : E) (hx : F x ≤ a) :
      φ (-((u : ℝ) * τ x)) x = x := by
    have ht : τ x = 0 := max_eq_right (sub_nonpos.mpr hx)
    simp [ht]
  have hheight (u : unitInterval) (x : E) (hx : F x ≤ b) (hxa : a < F x) :
      F (φ (-((u : ℝ) * τ x)) x) = F x - (u : ℝ) * (F x - a) := by
    have ht : τ x = F x - a := max_eq_left (sub_nonneg.mpr hxa.le)
    have hlo : a₀ < F x := lt_trans ha hxa
    have hhi : F x < b₀ := lt_of_le_of_lt hx hb
    have hnon : 0 ≤ F x - a := sub_nonneg.mpr hxa.le
    have hu₀ := u.2.1
    have hu₁ := u.2.2
    have hmul₀ : 0 ≤ (u : ℝ) * (F x - a) := mul_nonneg hu₀ hnon
    have hmul₁ : (u : ℝ) * (F x - a) ≤ F x - a := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu₁ hnon
    have hh := actual_normalized_complete_flow_height_on_band F hF Y φ hcurve
      a₀ b₀ hunit x hlo hhi (-((u : ℝ) * τ x))
      ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
    rw [ht] at hh
    rw [ht]
    simpa only [sub_eq_add_neg] using hh
  have hstay (q : unitInterval × {x : E // F x ≤ b}) : F (D q) ≤ b := by
    by_cases hx : F q.2.1 ≤ a
    · dsimp [D]
      rw [hfixed q.1 q.2.1 hx]
      exact q.2.2
    · dsimp [D]
      rw [hheight q.1 q.2.1 q.2.2 (lt_of_not_ge hx)]
      have hn : 0 ≤ (q.1 : ℝ) * (F q.2.1 - a) :=
        mul_nonneg q.1.2.1 (sub_nonneg.mpr (lt_of_not_ge hx).le)
      linarith [q.2.2]
  have hend (x : {x : E // F x ≤ b}) : F (D (1, x)) ≤ a := by
    by_cases hx : F x.1 ≤ a
    · have hh : D (1, x) = x.1 := hfixed 1 x.1 hx
      rwa [hh]
    · have hh : F (D (1, x)) = a := by
        simpa [D] using hheight 1 x.1 x.2 (lt_of_not_ge hx)
      exact hh.le
  let r : C({x : E // F x ≤ b}, {x : E // F x ≤ a}) :=
    ⟨fun x => ⟨D (1, x), hend x⟩,
      (hD.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let i : C({x : E // F x ≤ a}, {x : E // F x ≤ b}) :=
    ⟨fun x => ⟨x.1, x.2.trans hab⟩, continuous_subtype_val.subtype_mk _⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id {x : E // F x ≤ b})
      (i.comp r) := {
    toContinuousMap := ⟨fun q => ⟨D q, hstay q⟩, hD.subtype_mk _⟩
    map_zero_left := by intro x; apply Subtype.ext; simp [D]
    map_one_left := by intro x; rfl
  }
  refine ⟨r, H, ?_, ?_⟩
  · intro x hx
    exact hfixed 1 x hx
  · intro u x hx
    exact hfixed u x.1 hx
