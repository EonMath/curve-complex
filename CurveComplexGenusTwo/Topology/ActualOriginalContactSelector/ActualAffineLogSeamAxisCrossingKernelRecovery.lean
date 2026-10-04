import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
namespace CurveComplex.LocalSurgery
open Set

theorem actualOpenLogStripeExcludesEveryNegativeAxisLevel
    (x : ℝ) (n k : ℤ)
    (hx : x∈Ioo (-Real.pi+(n:ℝ)*(2*Real.pi)) (Real.pi+(n:ℝ)*(2*Real.pi))) :
    x≠Real.pi+(k:ℝ)*(2*Real.pi) := by
  intro he
  rw [he] at hx
  have hlo : (n:ℝ)<(k:ℝ)+1 := by nlinarith only [hx.1,Real.pi_pos]
  have hhi : (k:ℝ)<(n:ℝ) := by nlinarith only [hx.2,Real.pi_pos]
  have hloZ : n<k+1 := by exact_mod_cast hlo
  have hhiZ : k<n := by exact_mod_cast hhi
  omega

theorem actualAffineLogSeamSlopeNonzeroOfStripLevel
    (a b : ℂ) (u : ℝ) (n k : ℤ)
    (ha : a.im∈Ioo (-Real.pi+(n:ℝ)*(2*Real.pi)) (Real.pi+(n:ℝ)*(2*Real.pi)))
    (hu : (1-u)*a.im+u*b.im=Real.pi+(k:ℝ)*(2*Real.pi)) : b.im-a.im≠0 := by
  intro he
  have hab : b.im=a.im := sub_eq_zero.mp he
  have hlevel : a.im=Real.pi+(k:ℝ)*(2*Real.pi) := by rw [hab] at hu; nlinarith only [hu]
  exact actualOpenLogStripeExcludesEveryNegativeAxisLevel a.im n k ha hlevel

theorem actualAffineLogSeamImaginarySignAtNegativeAxisLevel
    (a b : ℂ) (u s : ℝ) (k : ℤ)
    (hu : (1-u)*a.im+u*b.im=Real.pi+(k:ℝ)*(2*Real.pi))
    (hδ : (s-u)*(b.im-a.im)∈Ioo (-Real.pi) Real.pi)
    (hne : (s-u)*(b.im-a.im)≠0) :
    (Complex.exp ((1-(s:ℂ))*a+(s:ℂ)*b)).im≠0 ∧
      ((Complex.exp ((1-(s:ℂ))*a+(s:ℂ)*b)).im<0 ↔ 0<(s-u)*(b.im-a.im)) := by
  let d := (s-u)*(b.im-a.im)
  have him : ((1-(s:ℂ))*a+(s:ℂ)*b).im=(1-s)*a.im+s*b.im := by
    simp [Complex.mul_im,Complex.sub_im]
  have hh : (1-s)*a.im+s*b.im=(d+Real.pi)+(k:ℝ)*(2*Real.pi) := by
    dsimp [d]
    nlinarith only [hu]
  have hsin : Real.sin (((1-(s:ℂ))*a+(s:ℂ)*b).im) = -Real.sin d := by
    rw [him,hh,Real.sin_add_int_mul_two_pi,Real.sin_add_pi]
  rw [Complex.exp_im,hsin]
  have hexp := Real.exp_pos (((1-(s:ℂ))*a+(s:ℂ)*b).re)
  rcases lt_or_gt_of_ne hne with hn | hp
  · have hsp : 0<Real.sin (-d) :=
      Real.sin_pos_of_pos_of_lt_pi (by dsimp [d];linarith only [hn])
        (by dsimp [d];linarith only [hδ.1])
    have hsn : Real.sin d<0 := by rw [Real.sin_neg] at hsp;linarith only [hsp]
    have he : 0<Real.exp (((1-(s:ℂ))*a+(s:ℂ)*b).re)* -Real.sin d :=
      mul_pos hexp (neg_pos.mpr hsn)
    exact ⟨ne_of_gt he,iff_of_false (not_lt_of_ge he.le) (not_lt_of_ge hn.le)⟩
  · have hsp : 0<Real.sin d := Real.sin_pos_of_pos_of_lt_pi hp hδ.2
    have he : Real.exp (((1-(s:ℂ))*a+(s:ℂ)*b).re)* -Real.sin d<0 :=
      mul_neg_of_pos_of_neg hexp (neg_neg_of_pos hsp)
    exact ⟨ne_of_lt he,iff_of_true he hp⟩

theorem actualAffineLogSeamCrossesNegativeAxisLocally
    (a b : ℂ) (u : ℝ) (k : ℤ) (hab : b.im-a.im≠0)
    (hu : (1-u)*a.im+u*b.im=Real.pi+(k:ℝ)*(2*Real.pi)) :
    ∃ δ : ℝ,0<δ ∧ ∀ v w : ℝ,u-δ<v → v<u → u<w → w<u+δ →
      (Complex.exp ((1-(v:ℂ))*a+(v:ℂ)*b)).im≠0 ∧
      (Complex.exp ((1-(w:ℂ))*a+(w:ℂ)*b)).im≠0 ∧
      ((Complex.exp ((1-(v:ℂ))*a+(v:ℂ)*b)).im<0 ↔
        ¬(Complex.exp ((1-(w:ℂ))*a+(w:ℂ)*b)).im<0) := by
  let D := |b.im-a.im|
  have hD : 0<D := abs_pos.mpr hab
  let δ := Real.pi/(2*D)
  have hδ : 0<δ := div_pos Real.pi_pos (mul_pos (by norm_num) hD)
  have hproduct : δ*D=Real.pi/2 := by
    dsimp [δ]
    field_simp
  have hnear (s : ℝ) (hlo : u-δ<s) (hhi : s<u+δ) (hs : s≠u) :
      (s-u)*(b.im-a.im)∈Ioo (-Real.pi) Real.pi ∧ (s-u)*(b.im-a.im)≠0 := by
    have ha : |s-u|<δ := abs_lt.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
    have hb := mul_lt_mul_of_pos_right ha hD
    rw [hproduct] at hb
    have hc : |(s-u)*(b.im-a.im)|<Real.pi := by
      rw [abs_mul]
      exact hb.trans (by linarith only [Real.pi_pos])
    exact ⟨abs_lt.mp hc,mul_ne_zero (sub_ne_zero.mpr hs) hab⟩
  refine ⟨δ,hδ,?_⟩
  intro v w hvlo hvu huw hwhi
  obtain ⟨hv,hvn⟩ := hnear v hvlo (hvu.trans (by linarith only [hδ])) (ne_of_lt hvu)
  obtain ⟨hw,hwn⟩ := hnear w (by linarith only [hδ,huw]) hwhi (ne_of_gt huw)
  obtain ⟨hvne,hvsign⟩ := actualAffineLogSeamImaginarySignAtNegativeAxisLevel a b u v k hu hv hvn
  obtain ⟨hwne,hwsign⟩ := actualAffineLogSeamImaginarySignAtNegativeAxisLevel a b u w k hu hw hwn
  refine ⟨hvne,hwne,hvsign.trans (Iff.trans ?_ (not_congr hwsign).symm)⟩
  rcases lt_or_gt_of_ne hab with hn | hp
  · have hvl : 0<(v-u)*(b.im-a.im) := mul_pos_of_neg_of_neg (sub_neg.mpr hvu) hn
    have hwr : (w-u)*(b.im-a.im)<0 := mul_neg_of_pos_of_neg (sub_pos.mpr huw) hn
    simp only [hvl,not_lt.mpr hwr.le,not_false_eq_true]
  · have hvl : (v-u)*(b.im-a.im)<0 := mul_neg_of_neg_of_pos (sub_neg.mpr hvu) hp
    have hwr : 0<(w-u)*(b.im-a.im) := mul_pos (sub_pos.mpr huw) hp
    simp only [not_lt.mpr hvl.le,hwr,not_true_eq_false]
end CurveComplex.LocalSurgery
