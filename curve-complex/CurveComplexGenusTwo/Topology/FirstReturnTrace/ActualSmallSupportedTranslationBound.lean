import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSmallSupportedTranslation
namespace CurveComplex
open Set Topology Schoenflies Metric
open scoped NNReal
/-- Internal exact refinement of the existing actual plane translation.
The additional conclusion bounds displacement on the ENTIRE plane, at EVERY time. -/
theorem source_small_supported_plane_translation_with_displacement
    (v : Plane) (hv : ‖v‖ < 1/4) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t x, ‖x‖ ≤ 1/4 → H.map (t,x) = x+(t:ℝ) • v) ∧
      (∀ t x, 1/2 ≤ ‖x‖ → H.map (t,x)=x) ∧
      ∀ t x, ‖H.map (t,x)-x‖ ≤ ‖v‖ := by
  have hsmall (f : Plane → Plane)
        (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
        ∃ H : AmbientIsotopy Plane,
          (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
          (∀ t x, f x = 0 → H.map (t, x) = x) := by
    classical
    let F : Interval × Plane → Plane :=
      fun p => p.2 + (p.1 : ℝ) • f p.2
    have hF : Continuous F := continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hf.continuous.comp continuous_snd))
    refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
      fun t x => rfl, ?_⟩
    · intro t
      have happ : ApproximatesLinearOn (fun x => F (t, x))
          (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
          Set.univ c := by
        intro x _ y _
        have heq : F (t, x) - F (t, y) - (x - y) =
            (t : ℝ) • (f x - f y) := by dsimp [F]; module
        change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        calc
          (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
            mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
          _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
      let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
      exact ⟨e, fun x => rfl⟩
    · intro x
      simp [F]
    · intro t x hx
      change x + (t : ℝ) • f x = x
      simp [hx]
  
  let b : Plane → ℝ := fun x => min (max ((1/2:ℝ)-dist x 0) 0) (1/4)
  have hb0 : LipschitzWith 1 (fun x : Plane => (1/2:ℝ)-dist x 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm]
      using abs_dist_sub_le x y (0:Plane)
  have hb : LipschitzWith 1 b := (hb0.max_const 0).min_const (1/4)
  let V : Plane := (4:ℝ) • v
  have hV : ‖V‖ < 1 := by
    dsimp [V]
    rw [norm_smul,Real.norm_eq_abs]
    norm_num
    linarith
  let f : Plane → Plane := fun x => b x • V
  have hf : LipschitzWith ‖V‖₊ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖b x • V-b y • V‖ ≤ ‖V‖*dist x y
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    have hh := hb.dist_le_mul x y
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg V)).trans_eq (mul_comm _ _)
  obtain ⟨H,hH,hfix⟩ := hsmall f ‖V‖₊ hV hf
  refine ⟨H,?_,?_,?_⟩
  · intro t x hx
    have hb' : b x = 1/4 := by
      have hd : dist x (0:Plane)=‖x‖ := dist_zero_right x
      dsimp [b]
      rw [hd,min_eq_right]
      exact le_max_of_le_left (by linarith)
    rw [hH]
    dsimp [f,V]
    rw [hb',smul_smul]
    norm_num
    rw [smul_smul]
    congr 1
    ring
  · intro t x hx
    apply hfix
    have hb' : b x=0 := by
      dsimp [b]
      rw [dist_zero_right,max_eq_right (by linarith)]
      norm_num
    simp [f,hb']
  · intro t x
    rw [hH]
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1]
    have hbnon : 0 ≤ b x := by
      dsimp [b]
      exact le_min (le_max_right _ _) (by norm_num)
    have hble : b x ≤ 1/4 := by dsimp [b]; exact min_le_right _ _
    have hfn : ‖f x‖ ≤ ‖v‖ := by
      dsimp [f,V]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hbnon,norm_smul,Real.norm_eq_abs]
      norm_num
      nlinarith [norm_nonneg v]
    calc
      (t:ℝ)*‖f x‖ ≤ 1*‖f x‖ := mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
      _ ≤ ‖v‖ := by simpa using hfn
end CurveComplex

#print axioms CurveComplex.source_small_supported_plane_translation_with_displacement
