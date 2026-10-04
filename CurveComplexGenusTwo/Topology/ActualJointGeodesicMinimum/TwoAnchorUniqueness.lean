import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import CurveComplexGenusTwo.Hyperbolic.Stabilizer

namespace CurveComplex.Hyperbolic.JointMinimum.TwoAnchor

open Set
open scoped UpperHalfPlane

private theorem equal_distance_cross (z w a : H2)
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

private theorem two_vertical_anchor_unique (a b t : ℝ) (hab : a ≠ b)
    (z : H2)
    (ha : dist z (verticalPath a) = dist (verticalPath t) (verticalPath a))
    (hb : dist z (verticalPath b) = dist (verticalPath t) (verticalPath b)) :
    z = verticalPath t := by
  have hA := equal_distance_cross z (verticalPath t) (verticalPath a) ha
  have hB := equal_distance_cross z (verticalPath t) (verticalPath b) hb
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

private theorem isometric_lines_eq_of_two_values
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
    apply two_vertical_anchor_unique a b t hab
      (e.symm (k t))
    · rw [← hFv a, ha, e.symm.isometry.dist_eq]
      rw [hk.dist_eq, ← verticalPath_isometry.dist_eq]
      rw [← ha,hFv a]
    · rw [← hFv b, hb, e.symm.isometry.dist_eq]
      rw [hk.dist_eq, ← verticalPath_isometry.dist_eq]
      rw [← hb,hFv b]
  funext t
  apply e.symm.injective
  exact (hFv t).trans (hKv t).symm

theorem isometric_lines_same_range_of_two_meetings
    (f g : ℝ → H2) (hf : Isometry f) (hg : Isometry g)
    (s₀ s₁ t₀ t₁ : ℝ) (hs : s₀ ≠ s₁)
    (h₀ : f s₀ = g t₀) (h₁ : f s₁ = g t₁) :
    Set.range f = Set.range g := by
  have habs : |s₁-s₀| = |t₁-t₀| := by
    calc
      |s₁-s₀| = dist (f s₁) (f s₀) := by rw [hf.dist_eq, Real.dist_eq]
      _ = dist (g t₁) (g t₀) := by rw [h₀, h₁]
      _ = |t₁-t₀| := by rw [hg.dist_eq, Real.dist_eq]
  by_cases hpositive : s₁-s₀ = t₁-t₀
  · let k : ℝ → H2 := fun s => g (t₀+(s-s₀))
    have hk : Isometry k := by
      apply Isometry.of_dist_eq
      intro s u
      change dist (g (t₀+(s-s₀))) (g (t₀+(u-s₀))) = dist s u
      rw [hg.dist_eq, Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    have hk₀ : f s₀ = k s₀ := by simpa [k] using h₀
    have hk₁ : f s₁ = k s₁ := by
      change f s₁ = g (t₀+(s₁-s₀))
      rw [hpositive]
      simpa using h₁
    have hfk := isometric_lines_eq_of_two_values f k hf hk s₀ s₁ hs hk₀ hk₁
    rw [hfk]
    ext z
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨t₀+(s-s₀),rfl⟩
    · rintro ⟨t,rfl⟩
      refine ⟨t-t₀+s₀,?_⟩
      change g (t₀+((t-t₀+s₀)-s₀)) = g t
      congr 1; ring
  · have hnegative : s₁-s₀ = -(t₁-t₀) := by
      have hsq₁ := sq_abs (s₁-s₀)
      have hsq₂ := sq_abs (t₁-t₀)
      rw [habs] at hsq₁
      have hsq : (s₁-s₀)^2 = (t₁-t₀)^2 := by linarith only [hsq₁, hsq₂]
      have hprod : ((s₁-s₀)-(t₁-t₀))*((s₁-s₀)+(t₁-t₀))=0 := by
        nlinarith only [hsq]
      rcases mul_eq_zero.mp hprod with hp | hn
      · exact False.elim (hpositive (sub_eq_zero.mp hp))
      · linarith
    let k : ℝ → H2 := fun s => g (t₀-(s-s₀))
    have hk : Isometry k := by
      apply Isometry.of_dist_eq
      intro s u
      change dist (g (t₀-(s-s₀))) (g (t₀-(u-s₀))) = dist s u
      rw [hg.dist_eq, Real.dist_eq, Real.dist_eq]
      rw [show (t₀-(s-s₀))-(t₀-(u-s₀)) = -(s-u) by ring, abs_neg]
    have hk₀ : f s₀ = k s₀ := by simpa [k] using h₀
    have hk₁ : f s₁ = k s₁ := by
      change f s₁ = g (t₀-(s₁-s₀))
      rw [hnegative]
      simpa using h₁
    have hfk := isometric_lines_eq_of_two_values f k hf hk s₀ s₁ hs hk₀ hk₁
    rw [hfk]
    ext z
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨t₀-(s-s₀),rfl⟩
    · rintro ⟨t,rfl⟩
      refine ⟨t₀+s₀-t,?_⟩
      change g (t₀-((t₀+s₀-t)-s₀)) = g t
      congr 1; ring

private theorem distinct_isometric_lines_meet_at_most_once
    (f g : ℝ → H2) (hf : Isometry f) (hg : Isometry g)
    (hne : Set.range f ≠ Set.range g) :
    (Set.range f ∩ Set.range g).Subsingleton := by
  intro x hx y hy
  obtain ⟨s₀,rfl⟩ := hx.1
  obtain ⟨t₀,h₀⟩ := hx.2
  obtain ⟨s₁,hyf⟩ := hy.1
  obtain ⟨t₁,hyg⟩ := hy.2
  by_contra hxy
  have hs : s₀ ≠ s₁ := by
    intro h
    exact hxy (by simpa [h] using hyf)
  have h₀' : f s₀ = g t₀ := h₀.symm
  have h₁' : f s₁ = g t₁ := hyf.trans hyg.symm
  exact hne (isometric_lines_same_range_of_two_meetings f g hf hg
    s₀ s₁ t₀ t₁ hs h₀' h₁')

#print axioms isometric_lines_eq_of_two_values
#print axioms isometric_lines_same_range_of_two_meetings
#print axioms distinct_isometric_lines_meet_at_most_once

end CurveComplex.Hyperbolic.JointMinimum.TwoAnchor
