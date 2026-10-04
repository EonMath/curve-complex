import CurveComplexGenusTwo.Topology.ChartLift

open Set Topology unitInterval Schoenflies
open scoped NNReal
namespace CurveComplex.GenusOrientationCandidate

/-- An actual compactly supported translation isotopy, exactly affine on the
inner ball. The flat inner region retains a computable germ along the strip. -/
theorem plane_flat_bump_translation
    (R : ℝ) (hR : 0 < R) (v : EuclideanSpace ℝ (Fin 2))
    (hv : ‖v‖ < R / 2) :
    ∃ H : AmbientIsotopy (EuclideanSpace ℝ (Fin 2)),
      (∀ t x, x ∈ Metric.closedBall 0 (R/2) →
        H.map (t,x) = x + (t : ℝ) • v) ∧
      (∀ t x, x ∉ Metric.closedBall 0 R → H.map (t,x) = x) := by
  classical
  let V := EuclideanSpace ℝ (Fin 2)
  have hsmall (f : V → V)
        (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
        ∃ H : AmbientIsotopy V,
          (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
          (∀ t x, f x = 0 → H.map (t, x) = x) := by
    classical
    let F : Interval × V → V :=
      fun p => p.2 + (p.1 : ℝ) • f p.2
    have hF : Continuous F := continuous_snd.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hf.continuous.comp continuous_snd))
    refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
      fun t x => rfl, ?_⟩
    · intro t
      have happ : ApproximatesLinearOn (fun x => F (t, x))
          (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V)
          Set.univ c := by
        intro x _ y _
        have heq : F (t, x) - F (t, y) - (x - y) =
            (t : ℝ) • (f x - f y) := by dsimp [F]; module
        change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        calc
          (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
            mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
          _ ≤ c * ‖x - y‖ := by
            have hh := hf.dist_le_mul x y
            have hxy : dist x y = ‖x-y‖ := _root_.dist_eq_norm x y
            have hff : dist (f x) (f y) = ‖f x-f y‖ := _root_.dist_eq_norm (f x) (f y)
            rw [hxy,hff] at hh
            simpa only [one_mul] using hh
      let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
      exact ⟨e, fun x => rfl⟩
    · intro x
      simp [F]
    · intro t x hx
      change x + (t : ℝ) • f x = x
      simp [hx]
  
  let b : V → ℝ := fun x => min (R/2) (max (R-dist x 0) 0)
  let w : V := (R/2)⁻¹ • v
  have hR2 : 0 < R/2 := by positivity
  have hw : ‖w‖ < 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR2)]
    rw [inv_mul_lt_iff₀ hR2]
    simpa using hv
  have hb0 : LipschitzWith 1 (fun x : V => R-dist x 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le x y 0
  have hb : LipschitzWith 1 b := (hb0.max_const 0).const_min (R/2)
  let f : V → V := fun x => b x • w
  have hf : LipschitzWith ‖w‖₊ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖b x • w - b y • w‖ ≤ ‖w‖ * dist x y
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hh := hb.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hh
    calc
      |b x-b y| * ‖w‖ ≤ dist x y * ‖w‖ :=
        mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ = ‖w‖ * dist x y := mul_comm _ _
  obtain ⟨H,hH,hfix⟩ := hsmall f ‖w‖₊ hw hf
  refine ⟨H, ?_, ?_⟩
  · intro t x hx
    have hd : dist x 0 ≤ R/2 := Metric.mem_closedBall.mp hx
    have hbflat : b x = R/2 := by
      exact min_eq_left (le_max_of_le_left (by linarith))
    rw [hH]
    have hwflat : f x = v := by
      dsimp [f]
      rw [hbflat]
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hR2.ne', one_smul]
    rw [hwflat]
  · intro t x hx
    have hd : R < dist x 0 := lt_of_not_ge hx
    apply hfix
    have hbzero : b x = 0 := by
      dsimp only [b]
      rw [max_eq_right (show R-dist x 0 ≤ 0 by linarith)]
      exact min_eq_right hR2.le
    simp [f,hbzero]


end CurveComplex.GenusOrientationCandidate
