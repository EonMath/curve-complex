import CurveComplexGenusTwo.Topology.AlternatingSphereCover

namespace AlternatingSphereCover
/-- Continuous choice on a closed half-plane; true is the upper half-plane.
Both roots have nonnegative imaginary part; the real part changes sign
between the two half-planes. The discontinuity of a global square root is
therefore placed on the positive real ray, exactly as in the slit gluing. -/
noncomputable def halfRoot (upper : Bool) (z : ℂ) : ℂ :=
  ⟨if upper then Real.sqrt ((‖z‖ + z.re)/2) else -Real.sqrt ((‖z‖ + z.re)/2),
    Real.sqrt ((‖z‖ - z.re)/2)⟩

theorem halfRoot_continuous (upper : Bool) : Continuous (halfRoot upper) := by
  unfold halfRoot
  change Continuous (fun z : ℂ => Complex.equivRealProdCLM.symm
    (if upper then Real.sqrt ((‖z‖ + z.re)/2) else -Real.sqrt ((‖z‖ + z.re)/2),
     Real.sqrt ((‖z‖ - z.re)/2)))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  apply Continuous.prodMk
  · cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  · fun_prop

theorem halfRoot_sq (upper : Bool) (z : ℂ)
    (hz : if upper then 0 ≤ z.im else z.im ≤ 0) : (halfRoot upper z)^2 = z := by
  have hA : 0 ≤ (‖z‖ + z.re)/2 := by
    have h := Complex.abs_re_le_norm z
    have h' := neg_abs_le z.re
    linarith
  have hB : 0 ≤ (‖z‖ - z.re)/2 := by
    have h := Complex.abs_re_le_norm z
    have h' := le_abs_self z.re
    linarith
  have hU := Real.sq_sqrt hA
  have hV := Real.sq_sqrt hB
  have hn := Complex.sq_norm_sub_sq_re z
  have hprod : (2 * Real.sqrt ((‖z‖ + z.re)/2) * Real.sqrt ((‖z‖ - z.re)/2))^2 = z.im^2 := by
    calc
      _ = 4 * (Real.sqrt ((‖z‖ + z.re)/2))^2 *
          (Real.sqrt ((‖z‖ - z.re)/2))^2 := by ring
      _ = z.im^2 := by rw [hU, hV]; nlinarith
  have hp : 2 * Real.sqrt ((‖z‖ + z.re)/2) * Real.sqrt ((‖z‖ - z.re)/2) = |z.im| := by
    apply (sq_eq_sq₀ (by positivity) (abs_nonneg z.im)).mp
    simpa only [sq_abs] using hprod
  cases upper
  · simp only [Bool.false_eq_true, ↓reduceIte] at hz
    rw [abs_of_nonpos hz] at hp
    apply Complex.ext <;> simp only [halfRoot, pow_two, Complex.mul_re, Complex.mul_im, Bool.false_eq_true, ↓reduceIte] <;>
      nlinarith
  · simp only [↓reduceIte] at hz
    rw [abs_of_nonneg hz] at hp
    apply Complex.ext <;> simp only [halfRoot, pow_two, Complex.mul_re, Complex.mul_im, Bool.false_eq_true, ↓reduceIte] <;>
      nlinarith

theorem halfRoot_agree_negative_ray (z : ℂ) (hi : z.im = 0) (hr : z.re ≤ 0) :
    halfRoot true z = halfRoot false z := by
  have hn : ‖z‖ = -z.re := by
    rw [← Complex.re_add_im z, hi]
    simpa using (abs_of_nonpos hr : |z.re| = -z.re)
  apply Complex.ext <;> simp [halfRoot, hn]

theorem halfRoot_opposite_positive_ray (z : ℂ) (hi : z.im = 0) (hr : 0 ≤ z.re) :
    halfRoot true z = -halfRoot false z := by
  have hn : ‖z‖ = z.re := by
    rw [← Complex.re_add_im z, hi]
    simpa using (abs_of_nonneg hr : |z.re| = z.re)
  apply Complex.ext <;> simp [halfRoot, hn]

def localPlane (x : Sphere) : ℂ := ⟨x.val 1, x.val 2⟩

def positivePatch : Set Sphere :=
  {x | 0 < x.val 0 ∧ 0 < 3 * x.val 0 ^ 2 - x.val 1 ^ 2}

noncomputable def rawRoot (x : Raw) : ℂ :=
  if x.val.2.2 then -halfRoot x.val.2.1 (localPlane x.val.1)
  else halfRoot x.val.2.1 (localPlane x.val.1)

theorem localPlane_continuous : Continuous localPlane := by
  unfold localPlane
  change Continuous (fun x : Sphere => Complex.equivRealProdCLM.symm (x.val 1, x.val 2))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  fun_prop

theorem positivePatch_isOpen : IsOpen positivePatch := by
  exact (isOpen_lt continuous_const (by fun_prop : Continuous (fun x : Sphere => x.val 0))).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun x : Sphere =>
      3 * x.val 0 ^ 2 - x.val 1 ^ 2)))

theorem rawRoot_continuous : Continuous rawRoot := by
  have hc : Continuous (fun p : Sphere × Bool × Bool =>
      if p.2.2 then -halfRoot p.2.1 (localPlane p.1) else halfRoot p.2.1 (localPlane p.1)) := by
    apply continuous_prod_of_discrete_right.mpr
    rintro ⟨h, s⟩
    cases s
    · change Continuous (halfRoot h ∘ localPlane)
      exact (halfRoot_continuous h).comp localPlane_continuous
    · change Continuous (fun x => -halfRoot h (localPlane x))
      exact ((halfRoot_continuous h).comp localPlane_continuous).neg
  exact hc.comp continuous_subtype_val

theorem rawRoot_sq (x : Raw) : (rawRoot x)^2 = localPlane x.val.1 := by
  have hs := halfRoot_sq x.val.2.1 (localPlane x.val.1) x.property
  cases h : x.val.2.2 <;> simpa [rawRoot, h] using hs

theorem rawRoot_deck (x : Raw) : rawRoot (rawDeck x) = -rawRoot x := by
  cases h : x.val.2.2 <;> simp [rawRoot, rawDeck, h]

theorem rawRoot_respects (x y : Raw) (hx : x.val.1 ∈ positivePatch) (h : Rel x y) :
    rawRoot x = rawRoot y := by
  rcases x with ⟨⟨b, a, s⟩, px⟩
  rcases y with ⟨⟨c, d, t⟩, py⟩
  rcases h with ⟨he, h⟩
  change b = c at he
  subst c
  change 0 < b.val 0 ∧ 0 < 3 * b.val 0 ^ 2 - b.val 1 ^ 2 at hx
  rcases h with hb | hl
  · have hz : localPlane b = 0 := by
      apply Complex.ext
      · change b.val 1 = 0
        rcases hb with ⟨_, hb⟩
        exact (mul_eq_zero.mp hb).resolve_right (ne_of_gt hx.2)
      · exact hb.1
    cases s <;> cases t <;> apply Complex.ext <;> simp [rawRoot, hz, halfRoot]
  · have hl' : (s ^^ (a && decide (0 < seamPolynomial b))) =
        (t ^^ (d && decide (0 < seamPolynomial b))) := hl
    clear hl
    have hl := hl'
    have px' : if a then 0 ≤ height b else height b ≤ 0 := px
    have py' : if d then 0 ≤ height b else height b ≤ 0 := py
    by_cases had : a = d
    · subst d
      have hst : s = t := by
        change (s ^^ (a && decide (0 < seamPolynomial b))) =
          (t ^^ (a && decide (0 < seamPolynomial b))) at hl
        exact Bool.xor_left_inj.mp hl
      subst t
      rfl
    · have hi : (localPlane b).im = 0 := by
        change height b = 0
        cases a <;> cases d <;> simp_all <;> linarith
      by_cases hp : 0 < seamPolynomial b
      · have hr : 0 ≤ (localPlane b).re := by
          change 0 ≤ b.val 1
          unfold seamPolynomial at hp
          have := (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2])
          exact le_of_lt this.1
        have hray := halfRoot_opposite_positive_ray (localPlane b) hi hr
        change (s ^^ (a && decide (0 < seamPolynomial b))) =
          (t ^^ (d && decide (0 < seamPolynomial b))) at hl
        cases a <;> cases d <;> cases s <;> cases t <;>
          simp_all [rawRoot, hp] <;> linarith
      · have hr : (localPlane b).re ≤ 0 := by
          change b.val 1 ≤ 0
          unfold seamPolynomial at hp
          exact le_of_not_gt (fun hy => hp (mul_pos hy hx.2))
        have hray := halfRoot_agree_negative_ray (localPlane b) hi hr
        change (s ^^ (a && decide (0 < seamPolynomial b))) =
          (t ^^ (d && decide (0 < seamPolynomial b))) at hl
        cases a <;> cases d <;> cases s <;> cases t <;>
          simp_all [rawRoot, hp] <;> linarith

theorem rawRoot_eq_iff_rel (x y : Raw)
    (hx : x.val.1 ∈ positivePatch) (hy : y.val.1 ∈ positivePatch) :
    rawRoot x = rawRoot y ↔ Rel x y := by
  constructor
  · intro h
    have hp : localPlane x.val.1 = localPlane y.val.1 := by
      exact (rawRoot_sq x).symm.trans ((congrArg (fun z : ℂ => z^2) h).trans (rawRoot_sq y))
    have h1 := congrArg Complex.re hp
    have h2 := congrArg Complex.im hp
    change x.val.1.val 1 = y.val.1.val 1 at h1
    change x.val.1.val 2 = y.val.1.val 2 at h2
    have hn (b : Sphere) : b.val 0 ^ 2 + b.val 1 ^ 2 + b.val 2 ^ 2 = 1 := by
      have hb : ‖b.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using b.property
      have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) b.val
      rw [hb] at hn
      simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
    have h0 : x.val.1.val 0 = y.val.1.val 0 := by
      apply (sq_eq_sq₀ (le_of_lt hx.1) (le_of_lt hy.1)).mp
      have hxnorm := hn x.val.1
      have hynorm := hn y.val.1
      rw [h1, h2] at hxnorm
      linarith
    have hb : x.val.1 = y.val.1 := by
      apply Subtype.ext
      ext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    by_cases hr : Rel x y
    · exact hr
    · have hl : label x ≠ label y := fun he => hr ⟨hb, Or.inr he⟩
      have hd : Rel (rawDeck x) y := by
        refine ⟨hb, Or.inr ?_⟩
        rw [label_rawDeck]
        cases he : label x <;> cases he' : label y <;> simp_all
      have hh := rawRoot_respects (rawDeck x) y hx hd
      rw [rawRoot_deck] at hh
      have hz : rawRoot x = 0 := by linear_combination (h - hh) / 2
      have hp0 : localPlane x.val.1 = 0 := by rw [← rawRoot_sq, hz]; simp
      have hz1 : x.val.1.val 1 = 0 := congrArg Complex.re hp0
      have hz2 : x.val.1.val 2 = 0 := congrArg Complex.im hp0
      exact ⟨hb, Or.inl ⟨hz2, by simp [seamPolynomial, hz1]⟩⟩
  · exact rawRoot_respects x y hx

end AlternatingSphereCover
