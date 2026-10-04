import CurveComplexGenusTwo.Topology.Smoothing.GraphShear

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies

/-- Rescale a centered surface chart so the unit square lies in its target and
its entire pullback stays in any prescribed local core ball. -/
theorem rescale_centered_chart_to_unit_square
    {S : Type} [TopologicalSpace S]
    (F₀ : OpenPartialHomeomorph S Plane) (p : S)
    (hp : p ∈ F₀.source) (hzero : F₀ p = 0)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ σ : ℝ, ∃ F : OpenPartialHomeomorph S Plane,
      0 < σ ∧ F.source = F₀.source ∧ F p = 0 ∧
      Plane.closedSquare 0 1 ⊆ F.target ∧
      (∀ x, F x = σ⁻¹ • F₀ x) ∧
      ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 → ‖F₀ x‖ < ρ := by
  have hzTarget : (0 : Plane) ∈ F₀.target := hzero ▸ F₀.map_source hp
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp F₀.open_target 0 hzTarget
  let σ : ℝ := min r ρ / 4
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσr : 2 * σ < r := by dsimp [σ]; linarith [min_le_left r ρ]
  have hσρ : 2 * σ < ρ := by dsimp [σ]; linarith [min_le_right r ρ]
  let e : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero σ⁻¹ (inv_ne_zero (ne_of_gt hσ))
  let F : OpenPartialHomeomorph S Plane := F₀.transHomeomorph e
  have hsource : F.source = F₀.source := rfl
  have hvalue (x : S) : F x = σ⁻¹ • F₀ x := rfl
  have hinv (y : Plane) : e.symm y = σ • y := by
    change (σ⁻¹)⁻¹ • y = σ • y
    rw [inv_inv]
  have hnorm (y : Plane) (hy : y ∈ Plane.closedSquare 0 1) : ‖y‖ ≤ 2 := by
    have hySup : Plane.supNorm y ≤ 1 := Schoenflies.mem_closedSquare_zero_one.mp hy
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      have hn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    calc
      ‖y‖ ≤ Real.sqrt 2 * Plane.supNorm y := Plane.norm_le_sqrt_two_mul_supNorm y
      _ ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_left hySup (Real.sqrt_nonneg 2)
      _ ≤ 2 := by simpa using hsqrt
  have hsmall (y : Plane) (hy : y ∈ Plane.closedSquare 0 1) :
      ‖e.symm y‖ < r ∧ ‖e.symm y‖ < ρ := by
    rw [hinv,norm_smul,Real.norm_eq_abs,abs_of_pos hσ]
    have hmul : σ * ‖y‖ ≤ 2 * σ := by
      nlinarith [hnorm y hy]
    exact ⟨hmul.trans_lt hσr,hmul.trans_lt hσρ⟩
  have hSquare : Plane.closedSquare 0 1 ⊆ F.target := by
    intro y hy
    change e.symm y ∈ F₀.target
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    exact (hsmall y hy).1
  refine ⟨σ,F,hσ,hsource,?_,hSquare,hvalue,?_⟩
  · change e (F₀ p) = 0
    rw [hzero]
    simp [e,Homeomorph.smulOfNeZero]
  · intro x hx hsq
    have he : e.symm (F x) = F₀ x := by
      change e.symm (e (F₀ x)) = F₀ x
      exact e.symm_apply_apply _
    rw [← he]
    exact (hsmall (F x) hsq).2

theorem segment_scaled_iff (σ : ℝ) (hσ : σ ≠ 0) (v z : Plane) :
    z ∈ segment ℝ (0 : Plane) v ↔
      σ⁻¹ • z ∈ segment ℝ (0 : Plane) (σ⁻¹ • v) := by
  constructor
  · intro hz
    rw [segment_eq_image'] at hz ⊢
    obtain ⟨t,ht,he⟩ := hz
    refine ⟨t,ht,?_⟩
    rw [← he]
    simp [smul_add,smul_smul,mul_comm,mul_left_comm,mul_assoc]
  · intro hz
    rw [segment_eq_image'] at hz ⊢
    obtain ⟨t,ht,he⟩ := hz
    refine ⟨t,ht,?_⟩
    have h := congrArg (fun z : Plane => σ • z) he
    have hc : σ * (t * σ⁻¹) = t := by
      field_simp [hσ]
    have hc' : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
    simpa [smul_add,smul_smul,hc,hc'] using h

theorem linear_scaled_segment_iff
    (T : Plane ≃L[ℝ] Plane) (σ : ℝ) (hσ : σ ≠ 0)
    (v z : Plane) :
    z ∈ segment ℝ (0 : Plane) v ↔
      σ⁻¹ • T z ∈ segment ℝ (0 : Plane) (σ⁻¹ • T v) := by
  have hi := image_segment ℝ T.toLinearMap.toAffineMap (0 : Plane) v
  change T '' segment ℝ (0 : Plane) v = segment ℝ (T 0) (T v) at hi
  rw [map_zero] at hi
  have hT : z ∈ segment ℝ (0 : Plane) v ↔
      T z ∈ segment ℝ (0 : Plane) (T v) := by
    rw [← hi]
    exact ⟨fun hz => ⟨z,hz,rfl⟩,
      fun ⟨w,hw,he⟩ => T.injective he ▸ hw⟩
  exact hT.trans (segment_scaled_iff σ hσ (T v) (T z))

theorem linear_scaled_disjoint_radial_segments
    (T : Plane ≃L[ℝ] Plane) (σ : ℝ) (hσ : σ ≠ 0)
    (v w : Plane)
    (h : Disjoint (segment ℝ (0 : Plane) v \ {0})
      (segment ℝ (0 : Plane) w \ {0})) :
    Disjoint
      (segment ℝ (0 : Plane) (σ⁻¹ • T v) \ {0})
      (segment ℝ (0 : Plane) (σ⁻¹ • T w) \ {0}) := by
  apply Set.disjoint_left.mpr
  intro x hxv hxw
  let y : Plane := T.symm (σ • x)
  have he : σ⁻¹ • T y = x := by
    change σ⁻¹ • T (T.symm (σ • x)) = x
    rw [T.apply_symm_apply,smul_smul]
    simp [inv_mul_cancel₀ hσ]
  have hy0 : y ≠ 0 := by
    intro hy
    have hx : x = 0 := by
      rw [hy,map_zero,smul_zero] at he
      exact he.symm
    exact hxv.2 hx
  have hyV : y ∈ segment ℝ (0 : Plane) v :=
    (linear_scaled_segment_iff T σ hσ v y).2 (he ▸ hxv.1)
  have hyW : y ∈ segment ℝ (0 : Plane) w :=
    (linear_scaled_segment_iff T σ hσ w y).2 (he ▸ hxw.1)
  exact Set.disjoint_left.mp h ⟨hyV,hy0⟩ ⟨hyW,hy0⟩

theorem scaled_chart_retains_radial_models
    {S J : Type} [TopologicalSpace S]
    (F₀ F : OpenPartialHomeomorph S Plane) (σ ρ : ℝ)
    (hσ : 0 < σ) (hsource : F.source = F₀.source)
    (hvalue : ∀ x, F x = σ⁻¹ • F₀ x)
    (hcore : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 → ‖F₀ x‖ < ρ)
    (c : Set S) (d : J → Set S) (v w : J → Plane)
    (haxis : ∀ x ∈ F₀.source, ‖F₀ x‖ < ρ →
      (x ∈ c ↔ F₀ x 1 = 0))
    (hmodel : ∀ j x, x ∈ F₀.source → ‖F₀ x‖ < ρ →
      (x ∈ d j ↔ F₀ x ∈ segment ℝ (0 : Plane) (v j) ∪
        segment ℝ (0 : Plane) (w j))) :
    (∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c ↔ F x 1 = 0)) ∧
      ∀ j x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
        (x ∈ d j ↔ F x ∈ segment ℝ (0 : Plane) (σ⁻¹ • v j) ∪
          segment ℝ (0 : Plane) (σ⁻¹ • w j)) := by
  have hsne : σ ≠ 0 := ne_of_gt hσ
  constructor
  · intro x hx hsq
    rw [haxis x (hsource ▸ hx) (hcore x hx hsq),hvalue]
    change F₀ x 1 = 0 ↔ σ⁻¹ * F₀ x 1 = 0
    exact ⟨fun hh => by rw [hh,mul_zero],fun hh =>
      (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hsne)⟩
  · intro j x hx hsq
    rw [hmodel j x (hsource ▸ hx) (hcore x hx hsq)]
    have hv := segment_scaled_iff σ hsne (v j) (F₀ x)
    have hw := segment_scaled_iff σ hsne (w j) (F₀ x)
    simpa only [hvalue x, Set.mem_union] using or_congr hv hw

end CurveComplex.HyperellipticModel.ArcSurgery

#print axioms CurveComplex.HyperellipticModel.ArcSurgery.rescale_centered_chart_to_unit_square
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.scaled_chart_retains_radial_models
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.linear_scaled_disjoint_radial_segments
