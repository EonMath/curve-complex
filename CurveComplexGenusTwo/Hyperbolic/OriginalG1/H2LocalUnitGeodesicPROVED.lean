import CurveComplexGenusTwo.Hyperbolic.Cayley
import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import Mathlib.Topology.LocallyConstant.Basic

namespace CurveComplex.Hyperbolic
open Set Filter Topology

private theorem localGeodesic_equal_distance_cross (z w a : H2)
    (h : dist z a = dist w a) :
    ((z.re-a.re)^2+z.im^2+a.im^2)*w.im =
      ((w.re-a.re)^2+w.im^2+a.im^2)*z.im := by
  have hc := congrArg Real.cosh h
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
  have hc' := (div_eq_div_iff
    (by positivity : 2*z.im*a.im ≠ 0)
    (by positivity : 2*w.im*a.im ≠ 0)).mp hc
  apply mul_right_cancel₀ a.im_ne_zero
  nlinarith only [hc']

private theorem localGeodesic_two_vertical_anchor_unique (a b t : ℝ) (hab : a ≠ b)
    (z : H2)
    (ha : dist z (verticalPath a) = dist (verticalPath t) (verticalPath a))
    (hb : dist z (verticalPath b) = dist (verticalPath t) (verticalPath b)) :
    z = verticalPath t := by
  have hA := localGeodesic_equal_distance_cross z (verticalPath t) (verticalPath a) ha
  have hB := localGeodesic_equal_distance_cross z (verticalPath t) (verticalPath b) hb
  simp only [verticalPath, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, sub_zero,
    sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at hA hB
  have hn : (Real.exp b)^2-(Real.exp a)^2 ≠ 0 := by
    intro hn
    have heq : Real.exp b = Real.exp a := by
      nlinarith [Real.exp_pos a, Real.exp_pos b]
    exact hab (Real.exp_injective heq).symm
  have hprod : ((Real.exp b)^2-(Real.exp a)^2)*(Real.exp t-z.im) = 0 := by
    nlinarith only [hA,hB]
  have him : z.im = Real.exp t := by
    have h := (mul_eq_zero.mp hprod).resolve_left hn
    linarith
  rw [him] at hA
  have hre : z.re = 0 := by
    have hsq : z.re^2 = 0 := by
      nlinarith [Real.exp_pos t, sq_nonneg z.re]
    nlinarith only [hsq]
  apply UpperHalfPlane.ext_re_im
  · simpa [verticalPath] using hre
  · simpa [verticalPath] using him

private theorem localGeodesic_isometric_lines_eq_of_two_values
    (f k : ℝ → H2) (hf : Isometry f) (hk : Isometry k)
    (a b : ℝ) (hab : a ≠ b) (ha : f a = k a) (hb : f b = k b) : f = k := by
  have hdist : dist (f 0) (f 1) = 1 := by simpa using hf.dist_eq 0 1
  obtain ⟨e,he0,he1⟩ := exists_ordered_pair_isometry (f 0) (f 1) hdist
  have hzero : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have hF : Isometry (fun t => e.symm (f t)) := e.symm.isometry.comp hf
  have hF0 : e.symm (f 0) = verticalPath 0 := by
    rw [← he0,e.symm_apply_apply,hzero]
  have hF1 : e.symm (f 1) = verticalPath 1 := by rw [← he1,e.symm_apply_apply]
  have hFv := isometry_eq_vertical_of_values _ hF hF0 hF1
  have hKv (t : ℝ) : e.symm (k t) = verticalPath t := by
    apply localGeodesic_two_vertical_anchor_unique a b t hab
    · rw [← hFv a, ha, e.symm.isometry.dist_eq]
      rw [hk.dist_eq, ← verticalPath_isometry.dist_eq]
      rw [← ha,hFv a]
    · rw [← hFv b, hb, e.symm.isometry.dist_eq]
      rw [hk.dist_eq, ← verticalPath_isometry.dist_eq]
      rw [← hb,hFv b]
  funext t
  apply e.symm.injective
  exact (hFv t).trans (hKv t).symm

private theorem localGeodesic_local_extension (γ : ℝ → H2) (t ε : ℝ) (hε : 0 < ε)
    (hmetric : ∀ s u : ℝ, |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u|) :
    ∃ f : ℝ → H2, Isometry f ∧ ∀ s : ℝ, |s-t| < ε/2 → γ s = f s := by
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht : |t-t| < ε := by simpa using hε
  have htδ : |(t+δ)-t| < ε := by
    rw [add_sub_cancel_left, abs_of_pos hδ]
    dsimp [δ]
    linarith
  obtain ⟨e,he0,he1⟩ := exists_pair_vertical_isometry (γ t) (γ (t+δ))
  let A := Real.log (e (γ t)).im
  let B := Real.log (e (γ (t+δ))).im
  have hA : e (γ t) = verticalPath A := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using he0
    · simp [verticalPath,A,Real.exp_log (e (γ t)).im_pos]
  have hB : e (γ (t+δ)) = verticalPath B := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using he1
    · simp [verticalPath,B,Real.exp_log (e (γ (t+δ))).im_pos]
  have hAB : |B-A| = δ := by
    have h := e.isometry.dist_eq (γ (t+δ)) (γ t)
    rw [hB,hA,verticalPath_isometry.dist_eq,hmetric (t+δ) t htδ ht] at h
    simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hδ] using h
  let σ : ℝ := if A ≤ B then 1 else -1
  have hσ : |σ| = 1 := by dsimp [σ]; split_ifs <;> norm_num
  have hBσ : B = A+σ*δ := by
    dsimp [σ]
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hAB
      linarith
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at hAB
      linarith
  let L : ℝ → ℝ := fun s => A+σ*(s-t)
  have hL : Isometry L := by
    apply Isometry.of_dist_eq
    intro s u
    change |(A+σ*(s-t))-(A+σ*(u-t))| = |s-u|
    rw [show (A+σ*(s-t))-(A+σ*(u-t)) = σ*(s-u) by ring,abs_mul,hσ,one_mul]
  have hLt : L t = A := by simp [L]
  have hLtδ : L (t+δ) = B := by simpa [L] using hBσ.symm
  let f : ℝ → H2 := fun s => e.symm (verticalPath (L s))
  have hf : Isometry f := e.symm.isometry.comp (verticalPath_isometry.comp hL)
  refine ⟨f,hf,?_⟩
  intro s hs
  have hsε : |s-t| < ε := lt_of_lt_of_le hs (by linarith)
  have hds (u : ℝ) (hu : |u-t| < ε) :
      dist (e (γ s)) (e (γ u)) = dist (verticalPath (L s)) (verticalPath (L u)) := by
    rw [e.isometry.dist_eq,verticalPath_isometry.dist_eq,hL.dist_eq,hmetric s u hsε hu]
    rfl
  have h0 := hds t ht
  have h1 := hds (t+δ) htδ
  rw [hA,hLt] at h0
  rw [hB,hLtδ] at h1
  have hne : A ≠ B := by intro h; rw [h,sub_self,abs_zero] at hAB; linarith
  have heq := localGeodesic_two_vertical_anchor_unique A B (L s) hne (e (γ s)) h0 h1
  have heq' := congrArg e.symm heq
  simpa only [e.symm_apply_apply] using heq'

/-- Elementary complete simply connected hyperbolic-plane geometry: a continuous
path locally preserving all unit-speed pair distances is a global isometric
geodesic line. The codomain is the actual canonical hyperbolic upper half-plane. -/
theorem actual_h2_local_unit_geodesic_isometry
    (γ : ℝ → H2) (hcontinuous : Continuous γ)
    (hlocal : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s u : ℝ, |s - t| < ε → |u - t| < ε →
        dist (γ s) (γ u) = |s - u|) :
    Isometry γ := by
  classical
  choose ε hε hm using hlocal
  have hmodels (t : ℝ) : ∃ f : ℝ → H2, Isometry f ∧
      ∀ s : ℝ, |s-t| < ε t/2 → γ s = f s :=
    localGeodesic_local_extension γ t (ε t) (hε t) (hm t)
  choose F hF hmatch using hmodels
  have hconstant : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_exists_open F).mpr
    intro t
    refine ⟨Metric.ball t (ε t/4), Metric.isOpen_ball, ?_, ?_⟩
    · simp only [Metric.mem_ball,dist_self]
      linarith [hε t]
    · intro u hu
      have hut : |u-t| < ε t/4 := by simpa only [Metric.mem_ball,Real.dist_eq] using hu
      let ρ := min (ε t/4) (ε u/4)
      have hρ : 0 < ρ := lt_min (by linarith [hε t]) (by linarith [hε u])
      have hρt : ρ ≤ ε t/4 := min_le_left _ _
      have hρu : ρ ≤ ε u/4 := min_le_right _ _
      have hu0 : |u-u| < ε u/2 := by simp; linarith [hε u]
      have hut0 : |u-t| < ε t/2 := by linarith [hε t]
      have hu1 : |(u+ρ)-u| < ε u/2 := by
        rw [add_sub_cancel_left,abs_of_pos hρ]
        linarith [hε u]
      have hut1 : |(u+ρ)-t| < ε t/2 := by
        have htri : |(u+ρ)-t| ≤ |u-t|+ρ := by
          calc
            |(u+ρ)-t| = |(u-t)+ρ| := by congr 1; ring
            _ ≤ |u-t|+|ρ| := abs_add_le _ _
            _ = |u-t|+ρ := by rw [abs_of_pos hρ]
        linarith
      apply localGeodesic_isometric_lines_eq_of_two_values (F u) (F t) (hF u) (hF t)
        u (u+ρ) (by linarith)
      · exact (hmatch u u hu0).symm.trans (hmatch t u hut0)
      · exact (hmatch u (u+ρ) hu1).symm.trans (hmatch t (u+ρ) hut1)
  have hglobal : γ = F 0 := by
    funext t
    have h := hmatch t t (by simp; linarith [hε t])
    rw [hconstant.apply_eq_of_preconnectedSpace t 0] at h
    exact h
  rw [hglobal]
  exact hF 0

end CurveComplex.Hyperbolic
