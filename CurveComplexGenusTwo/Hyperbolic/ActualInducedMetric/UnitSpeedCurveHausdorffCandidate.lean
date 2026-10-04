import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.StrictUnitSpeedLocalMetricCandidate
import CurveComplexGenusTwo.Hyperbolic.LocalToGlobal

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped NNReal ENNReal

set_option maxHeartbeats 800000 in
theorem unit_speed_curve_hausdorff_length {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (f : ℝ → F) (a b : ℝ) (hab : a < b)
    (hinj : InjOn f (Ioo a b))
    (hstrict : ∀ x ∈ Ioo a b, ∃ v : F, HasStrictDerivAt f v x ∧ ‖v‖ = 1) :
    Measure.hausdorffMeasure 1 (f '' Ioo a b) = ENNReal.ofReal (b-a) := by
  classical
  let J := Ioo a b
  let g : J → F := J.domRestrict f
  letI : Nonempty J := ⟨⟨(a+b)/2, by dsimp [J]; constructor <;> linarith⟩⟩
  have hcont : ContinuousOn f J := by
    intro x hx
    obtain ⟨v, hv, _⟩ := hstrict x hx
    exact hv.hasDerivAt.continuousAt.continuousWithinAt
  have hemb : MeasurableEmbedding g := hcont.measurableEmbedding measurableSet_Ioo hinj
  let ρ : Measure J := (Measure.hausdorffMeasure 1 : Measure F).comap g
  let ν : Measure J := Measure.hausdorffMeasure 1
  have hρ (s : Set J) (hs : MeasurableSet s) : ρ s = Measure.hausdorffMeasure 1 (g '' s) := by
    exact Measure.comap_apply g hemb.injective
      (fun t ht => hemb.measurableSet_image.mpr ht) _ hs
  have hlocal (c : ℝ≥0) (hc : 1 < (c : ℝ)) (x : J) :
      ∃ V : Set J, IsOpen V ∧ x ∈ V ∧ ∀ s : Set J, MeasurableSet s → s ⊆ V →
        ρ s ≤ (c : ℝ≥0∞) * ν s ∧ ν s ≤ (c : ℝ≥0∞) * ρ s := by
    have hcpos : (0 : ℝ) < c := by linarith
    have hcipos : (0 : ℝ) < (c : ℝ)⁻¹ := inv_pos.mpr hcpos
    have hci : (c : ℝ)⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
    let δ : ℝ := min ((c : ℝ)-1) (1-(c : ℝ)⁻¹) / 2
    have hδpos : 0 < δ := div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
    have hδa : δ ≤ (c : ℝ)-1 := by
      dsimp [δ]; linarith [min_le_left ((c : ℝ)-1) (1-(c : ℝ)⁻¹)]
    have hδb : δ ≤ 1-(c : ℝ)⁻¹ := by
      dsimp [δ]; linarith [min_le_right ((c : ℝ)-1) (1-(c : ℝ)⁻¹)]
    have hδone : δ < 1 := by linarith
    let ε : ℝ≥0 := ⟨δ, hδpos.le⟩
    have hεpos : 0 < ε := hδpos
    have hεone : ε < 1 := hδone
    have hupper : 1 + ε ≤ c := by exact_mod_cast (show (1:ℝ)+δ ≤ c by linarith)
    have hlower : (1-ε)⁻¹ ≤ c := by
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_inv, NNReal.coe_sub hεone.le, NNReal.coe_one]
      change (1-δ)⁻¹ ≤ (c : ℝ)
      rw [← one_div]
      apply (one_div_le (by linarith : 0 < 1-δ) hcpos).mpr
      rw [one_div]
      linarith
    obtain ⟨v, hv, hvnorm⟩ := hstrict x x.property
    obtain ⟨U, hU, hxU, hL, hA⟩ := strict_unit_speed_local_metric_bounds hv hvnorm ε hεpos hεone
    let V : Set J := Subtype.val ⁻¹' U
    refine ⟨V, hU.preimage continuous_subtype_val, hxU, ?_⟩
    intro s hs hsV
    let k : s → U := fun y => ⟨y.val.val, hsV y.property⟩
    have hk : Isometry k := fun y z => rfl
    let l : s → F := fun y => g y.val
    have hLl : LipschitzWith (1+ε) l := by
      simpa only [mul_one, Function.comp_def, l, k, g, domRestrict_apply] using! hL.comp hk.lipschitzWith
    have hAl : AntilipschitzWith (1-ε)⁻¹ l := fun y z => hA (k y) (k z)
    have himage : l '' univ = g '' s := by
      ext z; constructor
      · rintro ⟨y, _, rfl⟩; exact ⟨y, y.property, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    have hsν : (Measure.hausdorffMeasure 1 : Measure s) univ = ν s := by
      have h := (isometry_subtype_coe : Isometry (Subtype.val : s → J)).hausdorffMeasure_image
        (d := 1) (Or.inl (by norm_num)) univ
      simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using h.symm
    have hu := hLl.hausdorffMeasure_image_le (d := 1) (by norm_num) univ
    have hl := hAl.le_hausdorffMeasure_image (d := 1) (by norm_num) univ
    simp only [ENNReal.rpow_one, himage, hsν, ← hρ s hs] at hu hl
    exact ⟨hu.trans ((mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hupper) (by positivity))),
      hl.trans ((mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr hlower) (by positivity)))⟩
  have hfactor (c : ℝ≥0) (hc : 1 < (c : ℝ)) : ρ ≤ (c : ℝ≥0∞) • ν ∧ ν ≤ (c : ℝ≥0∞) • ρ := by
    constructor
    · apply measure_le_smul_of_local_measurable_le
      intro x; obtain ⟨V, hV, hx, h⟩ := hlocal c hc x
      exact ⟨V, hV, hx, fun s hs hsV => (h s hs hsV).1⟩
    · apply measure_le_smul_of_local_measurable_le
      intro x; obtain ⟨V, hV, hx, h⟩ := hlocal c hc x
      exact ⟨V, hV, hx, fun s hs hsV => (h s hs hsV).2⟩
  have hcancel (μ τ : Measure J)
      (h : ∀ c : ℝ≥0, 1 < (c : ℝ) → μ ≤ (c : ℝ≥0∞) • τ) : μ ≤ τ := by
    refine Measure.le_iff.mpr fun s hs => ?_
    apply ENNReal.le_of_forall_lt_one_mul_le
    intro α hα
    by_cases hα0 : α = 0
    · simp [hα0]
    have hαtop : α ≠ ∞ := ne_top_of_lt hα
    let β : ℝ≥0 := α.toNNReal
    have hβ0 : β ≠ 0 := ne_of_gt (ENNReal.toNNReal_pos hα0 hαtop)
    have hβcast : (β : ℝ≥0∞) = α := ENNReal.coe_toNNReal hαtop
    have hβ1 : β < 1 := by exact_mod_cast (hβcast ▸ hα)
    have hc : (1 : ℝ) < (β⁻¹ : ℝ≥0) := by
      exact_mod_cast (one_lt_inv₀ (ENNReal.toNNReal_pos hα0 hαtop)).mpr hβ1
    have hm : μ s ≤ ((β⁻¹ : ℝ≥0) : ℝ≥0∞) * τ s := by
      simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff.mp (h β⁻¹ hc) s hs
    calc
      α * μ s ≤ α * (((β⁻¹ : ℝ≥0) : ℝ≥0∞) * τ s) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = τ s := by
        rw [ENNReal.coe_inv hβ0, hβcast, ← mul_assoc, ENNReal.mul_inv_cancel hα0 hαtop, one_mul]
  have heq : ρ = ν := le_antisymm (hcancel ρ ν fun c hc => (hfactor c hc).1)
    (hcancel ν ρ fun c hc => (hfactor c hc).2)
  have hν : ν univ = ENNReal.ofReal (b-a) := by
    have h := (isometry_subtype_coe : Isometry (Subtype.val : J → ℝ)).hausdorffMeasure_image
      (d := 1) (Or.inl (by norm_num)) univ
    have hh : (Measure.hausdorffMeasure 1 : Measure ℝ) J = ν univ := by
      simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using h
    rw [← hh, hausdorffMeasure_real]
    exact Real.volume_Ioo
  have hrange : g '' univ = f '' Ioo a b := by
    ext z; constructor
    · rintro ⟨x, _, rfl⟩; exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [← hrange, ← hρ univ MeasurableSet.univ, heq, hν]

end CurveComplex.Hyperbolic
