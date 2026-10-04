import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology
namespace CurveComplex.Hyperbolic.PantsTheta
theorem actual_paired_boundary_arc_interpolation_avoids_punctures :
    let A (i : Fin 6) : ℝ :=
      (match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 7 | _ => 8)*Real.pi/4
    let φ (i : Fin 5) (t : unitInterval) : ℝ := (1-t.val)*A i.castSucc+t.val*A i.succ
    let radius (outer : Bool) : ℝ := Real.exp (if outer then 1 else -1)
    let circ (outer : Bool) (i : Fin 5) (t : unitInterval) : ℝ×ℝ :=
      (-radius outer*Real.cos (φ i t),-radius outer*Real.sin (φ i t))
    let poly (outer : Bool) (i : Fin 5) (t : unitInterval) : ℝ×ℝ :=
      ((thetaLeg outer i t).val.1+1/2,(thetaLeg outer i t).val.2)
    ∀ (outer : Bool) (i : Fin 5) (t s : unitInterval),
      (1-s.val) • circ outer i t + s.val • poly outer i t ≠ ((0:ℝ),0) ∧
      (1-s.val) • circ outer i t + s.val • poly outer i t ≠ ((1:ℝ),0) := by
  intro A φ radius circ poly
  have hhalf {u : ℝ} (hu : |u| ≤ Real.pi/4) : 1/2 < Real.cos u := by
    have hlt : |u| < Real.pi/3 := by linarith [Real.pi_pos]
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg u)
      (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) hlt
    simpa only [Real.cos_pi_div_three,Real.cos_abs] using hc
  have hR : 2 < radius true := by
    dsimp [radius];linarith [Real.add_one_lt_exp (show (1:ℝ)≠0 by norm_num)]
  have hr : radius false < 1/2 := by
    have he : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1:ℝ)≠0 by norm_num)]
    dsimp [radius]
    rw [Real.exp_neg]
    have hh := (inv_lt_inv₀ (Real.exp_pos 1) (show (0:ℝ)<2 by norm_num)).mpr he
    simpa [one_div] using hh
  have hpos (outer : Bool) : 0 < radius outer := Real.exp_pos _
  intro outer i t s
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hs0 := s.property.1
  have hs1 := s.property.2
  have hnegative (x y : ℝ) (hx : x < 0) (hy : y < 0) : (1-s.val)*x+s.val*y < 0 := by
    by_cases hs : s.val=1
    · rw [hs];linarith
    · have := mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_le_of_ne hs1 hs)) hx
      have := mul_nonpos_of_nonneg_of_nonpos hs0 hy.le
      linarith
  have hpositive (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < (1-s.val)*x+s.val*y := by
    have := hnegative (-x) (-y) (by linarith) (by linarith)
    linarith
  have hgreater (x y : ℝ) (hx : 1 < x) (hy : 1 < y) : 1 < (1-s.val)*x+s.val*y := by
    have := hpositive (x-1) (y-1) (by linarith) (by linarith)
    nlinarith
  have hless (x y : ℝ) (hx : x < 1) (hy : y < 1) : (1-s.val)*x+s.val*y < 1 := by
    have := hpositive (1-x) (1-y) (by linarith) (by linarith)
    nlinarith
  have hleft {z w : ℝ×ℝ} (hz : z.1<0) (hw : w.1<0) :
      (1-s.val) • z+s.val • w ≠ ((0:ℝ),0) ∧ (1-s.val) • z+s.val • w ≠ ((1:ℝ),0) := by
    have hh := hnegative z.1 w.1 hz hw
    constructor <;> intro he <;> have he' := congrArg Prod.fst he <;> change (1-s.val)*z.1+s.val*w.1=_ at he' <;> linarith
  have hbottom {z w : ℝ×ℝ} (hz : z.2<0) (hw : w.2<0) :
      (1-s.val) • z+s.val • w ≠ ((0:ℝ),0) ∧ (1-s.val) • z+s.val • w ≠ ((1:ℝ),0) := by
    have hh := hnegative z.2 w.2 hz hw
    constructor <;> intro he <;> have he' := congrArg Prod.snd he <;> change (1-s.val)*z.2+s.val*w.2=_ at he' <;> linarith
  have htop {z w : ℝ×ℝ} (hz : 0<z.2) (hw : 0<w.2) :
      (1-s.val) • z+s.val • w ≠ ((0:ℝ),0) ∧ (1-s.val) • z+s.val • w ≠ ((1:ℝ),0) := by
    have hh := hpositive z.2 w.2 hz hw
    constructor <;> intro he <;> have he' := congrArg Prod.snd he <;> change (1-s.val)*z.2+s.val*w.2=_ at he' <;> linarith
  fin_cases i
  · apply hleft
    · have hc : 0 < Real.cos (φ 0 t) := Real.cos_pos_of_mem_Ioo ⟨by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos],by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos]⟩
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hpos outer)) hc
    · change (1-t.val)*(-1)+t.val*(-1)+1/2<0;linarith
  · apply hbottom
    · have hc : 0 < Real.sin (φ 1 t) := Real.sin_pos_of_pos_of_lt_pi
        (by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos])
        (by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos])
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hpos outer)) hc
    · change (1-t.val)*(-1)+t.val*(-1)<0;linarith
  · have hc : 1/2 < -Real.cos (φ 2 t) := by
      have hb : |φ 2 t-Real.pi| ≤ Real.pi/4 := abs_le.mpr ⟨by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos],by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos]⟩
      simpa only [Real.cos_sub_pi] using hhalf hb
    cases outer
    · have hx0 : 0 < (circ false 2 t).1 := by dsimp [circ];nlinarith [hpos false]
      have hx1 : (circ false 2 t).1 < 1 := by
        have hc1 := Real.neg_one_le_cos (φ 2 t)
        have hh : -radius false*Real.cos (φ 2 t) ≤ radius false := by nlinarith [hpos false]
        dsimp [circ];linarith
      have hp0 : 0 < (poly false 2 t).1 := by norm_num [poly,thetaLeg,thetaVertex]
      have hp1 : (poly false 2 t).1 < 1 := by norm_num [poly,thetaLeg,thetaVertex]
      have hh0 := hpositive _ _ hx0 hp0
      have hh1 := hless _ _ hx1 hp1
      constructor <;> intro he <;> have he' := congrArg Prod.fst he <;> change (1-s.val)*(circ false 2 t).1+s.val*(poly false 2 t).1=_ at he' <;> linarith
    · have hx : 1 < (circ true 2 t).1 := by dsimp [circ];nlinarith [hR]
      have hp : 1 < (poly true 2 t).1 := by norm_num [poly,thetaLeg,thetaVertex]
      have hh := hgreater _ _ hx hp
      constructor <;> intro he <;> have he' := congrArg Prod.fst he <;> change (1-s.val)*(circ true 2 t).1+s.val*(poly true 2 t).1=_ at he' <;> linarith
  · apply htop
    · have hc : Real.sin (φ 3 t)<0 := by
        have hs := Real.sin_neg_of_neg_of_neg_pi_lt
          (show φ 3 t-2*Real.pi<0 by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos])
          (show -Real.pi<φ 3 t-2*Real.pi by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos])
        simpa only [Real.sin_sub_two_pi] using hs
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (hpos outer)) hc
    · change 0<(1-t.val)*1+t.val*1;linarith
  · apply hleft
    · have hc : 0<Real.cos (φ 4 t) := by
        have hh := hhalf (show |φ 4 t-2*Real.pi| ≤ Real.pi/4 from abs_le.mpr
          ⟨by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos],by dsimp [φ,A];norm_num;nlinarith [Real.pi_pos]⟩)
        rw [Real.cos_sub_two_pi] at hh
        linarith
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hpos outer)) hc
    · change (1-t.val)*(-1)+t.val*(-1)+1/2<0;linarith
end CurveComplex.Hyperbolic.PantsTheta
