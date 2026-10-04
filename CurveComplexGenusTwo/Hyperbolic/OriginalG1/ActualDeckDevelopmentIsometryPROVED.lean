import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicAxisAllPROVED
import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex.Hyperbolic
open Filter Topology Set Matrix
open scoped UpperHalfPlane MatrixGroups unitInterval
/-- Exact abstraction of source G1 geometricDeck_isometry, lines 765–960.
Requires a global development onto H2; a proper pants developing image does not
satisfy this hypothesis merely by possessing local metric charts. -/
theorem actual_deck_development_isometry
    {E P : Type} [MetricSpace E] [TopologicalSpace P]
    (p : P → E) (development : P ≃ₜ UpperHalfPlane)
    (development_metric : ∀ x : P, ∃ U : Set P, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist (p y) (p z) = dist (development y) (development z))
    (deckTranslation : P ≃ₜ P) (projection_fixed : ∀ x, p (deckTranslation x) = p x) :
    Isometry ((development.symm.trans deckTranslation).trans development) := by
  classical
  let geometricDeck : H2 ≃ₜ H2 := (development.symm.trans deckTranslation).trans development
  have geometricDeck_locally_isometric (x : H2) :
      ∃ W : Set H2, IsOpen W ∧ x ∈ W ∧
        ∀ y ∈ W, ∀ z ∈ W, dist (geometricDeck y) (geometricDeck z)=dist y z := by
    obtain ⟨U,hU,hxU,hmetricU⟩ := development_metric (development.symm x)
    obtain ⟨V,hV,hxV,hmetricV⟩ := development_metric (deckTranslation (development.symm x))
    let W := development.symm ⁻¹' (U ∩ deckTranslation ⁻¹' V)
    have hW : IsOpen W := (hU.inter (hV.preimage deckTranslation.continuous)).preimage development.symm.continuous
    refine ⟨W,hW,⟨hxU,hxV⟩,?_⟩
    intro y hy z hz
    change dist (development (deckTranslation (development.symm y)))
      (development (deckTranslation (development.symm z)))=dist y z
    rw [← hmetricV _ hy.2 _ hz.2,projection_fixed,projection_fixed,hmetricU _ hy.1 _ hz.1]
    rw [development.apply_symm_apply,development.apply_symm_apply]
  have zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have vertical_radius_sphere (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r) :
      Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
        z.im * (1 + (Real.exp r) ^ 2) := by
    have hstd : dist (verticalPath 0) (verticalPath r) = r := by
      simpa [Real.dist_eq,abs_of_nonneg hr,abs_of_nonpos (neg_nonpos.mpr hr)] using
        verticalPath_isometry.dist_eq 0 r
    have hc := congrArg Real.cosh (h.trans (zero_eq_I ▸ hstd).symm)
    rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
    simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at hc
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,
      one_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
    field_simp at hc
    nlinarith [hc]
  have denominator_nonzero (a b : ℝ) (hab : 0 < a^2+b^2) (w : H2) :
      (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [Complex.mul_im] at him
    have hb : b = 0 := by
      rcases him with hb | hw
      · exact hb
      · exact (w.im_pos.ne' hw).elim
    have ha : a ≠ 0 := by
      intro ha
      rw [ha,hb] at hab
      norm_num at hab
    exact ha (by simpa [hb] using h)
  have rotation_maps_vertical_radius (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r)
      (hab : 0 < (1-Real.exp r*z.im)^2+z.re^2) :
      (stabilizerRotation (1-Real.exp r*z.im) z.re hab • verticalPath r : H2) = z := by
    let a := 1-Real.exp r*z.im
    let b := z.re
    have hsphere := vertical_radius_sphere r hr z h
    have hEim : (Complex.exp (r : ℂ)).im = 0 := by
      simpa using Complex.exp_ofReal_im r
    have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := by
      simpa using Complex.exp_ofReal_re r
    apply UpperHalfPlane.coe_injective
    rw [stabilizerRotation_coe_smul]
    apply (div_eq_iff (denominator_nonzero a b hab (verticalPath r))).2
    apply Complex.ext
    · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
        Complex.mul_im,Complex.neg_im]
      try rw [hEim]
      dsimp [a,b]
      ring
    · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
        Complex.mul_re,Complex.neg_re]
      try rw [hEre]
      dsimp [a,b]
      nlinarith [hsphere]
  have exists_stabilizer_radius (r : ℝ) (hr : 0 ≤ r) (z : H2) (h : dist UpperHalfPlane.I z = r) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧ e (verticalPath r) = z := by
    let a : ℝ := 1-Real.exp r*z.im
    let b : ℝ := z.re
    by_cases hpole : a = 0 ∧ b = 0
    · have him : z.im = Real.exp (-r) := by
        have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
        have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole;linarith [hpole.1]
        rw [Real.exp_neg,←one_div]
        exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
      have hz : z = verticalPath (-r) := by
        apply UpperHalfPlane.ext_re_im
        · simpa [verticalPath,b] using hpole.2
        · simpa [verticalPath] using him
      refine ⟨IsometryEquiv.constSMul
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
      · rw [←zero_eq_I]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
        have hh := modular_S_verticalPath 0
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
        simpa only [neg_zero] using hh
      · rw [hz]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
        exact modular_S_verticalPath r
    · have hab : 0 < a^2+b^2 := by
        by_contra hn
        have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        exact hpole ⟨ha,hb⟩
      refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),?_,?_⟩
      · exact stabilizerRotation_fixes_I a b hab
      · exact rotation_maps_vertical_radius r hr z h hab
  have ordered_pair_alignment (x y : H2) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = x ∧ e (verticalPath (dist x y)) = y := by
    let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
    have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
    let w := e0.symm y
    have hw : dist UpperHalfPlane.I w = dist x y := by
      have hd := e0.isometry.dist_eq UpperHalfPlane.I (e0.symm y)
      rw [e0.apply_symm_apply,he0] at hd
      exact hd.symm
    obtain ⟨s,hs0,hsr⟩ := exists_stabilizer_radius (dist x y) dist_nonneg w hw
    refine ⟨s.trans e0,?_,?_⟩
    · rw [IsometryEquiv.trans_apply,hs0,he0]
    · rw [IsometryEquiv.trans_apply,hsr]
      exact e0.apply_symm_apply y
  have actual_segment (x y : H2) :
      ∃ γ : Path x y, ∀ s t : unitInterval,
        dist (γ s) (γ t) = dist x y * dist (s : ℝ) (t : ℝ) := by
    obtain ⟨e,he0,he1⟩ := ordered_pair_alignment x y
    let γ : Path x y := {
      toFun := fun t => e (verticalPath ((t : ℝ) * dist x y))
      continuous_toFun := e.continuous.comp
        (verticalPath_isometry.continuous.comp (continuous_subtype_val.mul continuous_const))
      source' := by
        change e (verticalPath (0 * dist x y)) = x
        simpa only [zero_mul,zero_eq_I] using he0
      target' := by
        change e (verticalPath (1 * dist x y)) = y
        simpa only [one_mul] using he1 }
    refine ⟨γ,?_⟩
    intro s t
    change dist (e (verticalPath ((s : ℝ)*dist x y)))
      (e (verticalPath ((t : ℝ)*dist x y))) = _
    rw [e.isometry.dist_eq,verticalPath_isometry.dist_eq,Real.dist_eq,Real.dist_eq,
      ←sub_mul,abs_mul,abs_of_nonneg (dist_nonneg (x := x) (y := y)),mul_comm]
  have locally_isometric_homeomorph_nonexpanding (F : H2 ≃ₜ H2)
      (hF : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, dist (F y) (F z) = dist y z)
      (x y : H2) : dist (F x) (F y) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    choose U hU hxU hmetric using hF
    let V : Interval → Set Interval := fun t => γ ⁻¹' U (γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) : dist (F (γ (t n))) (F (γ (t (n+1)))) =
        dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
      simp only [neg_sub]
    have hbound (n : ℕ) : dist (F (γ (t 0))) (F (γ (t n))) ≤
        dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (F (γ (t 0))) (F (γ (t n))) (F (γ (t (n+1))))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  have geometricDeck_inverse_locally_isometric (x : H2) :
      ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          dist (geometricDeck.symm y) (geometricDeck.symm z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetric⟩ := geometricDeck_locally_isometric (geometricDeck.symm x)
    refine ⟨geometricDeck.symm ⁻¹' U,hU.preimage geometricDeck.symm.continuous,hxU,?_⟩
    intro y hy z hz
    have h := hmetric _ hy _ hz
    simpa only [geometricDeck.apply_symm_apply] using h.symm
  have geometricDeck_isometry : Isometry geometricDeck := by
    apply Isometry.of_dist_eq
    intro x y
    apply le_antisymm
    · exact locally_isometric_homeomorph_nonexpanding geometricDeck
        geometricDeck_locally_isometric x y
    · have h := locally_isometric_homeomorph_nonexpanding geometricDeck.symm
        geometricDeck_inverse_locally_isometric (geometricDeck x) (geometricDeck y)
      simpa only [geometricDeck.symm_apply_apply] using h
  exact geometricDeck_isometry
end CurveComplex.Hyperbolic
