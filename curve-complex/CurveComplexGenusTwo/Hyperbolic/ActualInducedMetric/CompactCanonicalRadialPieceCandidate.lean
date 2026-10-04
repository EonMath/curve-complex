import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalFirstSideCircleCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalCayleyWedgeCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalTriangleStripAreaCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem regular_hexagon_first_radial_piece_polynomial (z : H2) :
    (z ∈ regularHexagonRegion.interior ∧ 0 < (cayley z : ℂ).im ∧
      Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re) ↔
    (z.re < 0 ∧ 1 < z.re^2+z.im^2+2*Real.sqrt 3*z.re ∧
      z.re^2+z.im^2 < (Real.sqrt 3+Real.sqrt 2)^2+2*(Real.sqrt 3+Real.sqrt 2)*z.re) := by
  constructor
  · rintro ⟨hz,hy,hx⟩
    obtain ⟨hneg,hlo⟩ := (cayley_first_half_wedge_coordinate_iff z).mp ⟨hy,hx⟩
    exact ⟨hneg,hlo,(regular_hexagon_first_side_upper_circle_iff z).mp
      ((regular_hexagon_first_half_wedge_interior_iff z hy hx).mp hz)⟩
  · rintro ⟨hneg,hlo,hup⟩
    obtain ⟨hy,hx⟩ := (cayley_first_half_wedge_coordinate_iff z).mpr ⟨hneg,hlo⟩
    exact ⟨(regular_hexagon_first_half_wedge_interior_iff z hy hx).mpr
      ((regular_hexagon_first_side_upper_circle_iff z).mpr hup),hy,hx⟩

set_option maxHeartbeats 1000000 in
theorem compact_canonical_radial_piece_strip_iff (z : H2) :
    let t := Real.sqrt 3+Real.sqrt 2
    let a := -(Real.sqrt 3+2*Real.sqrt 2)/5
    (z.re < 0 ∧ 1 < z.re^2+z.im^2+2*Real.sqrt 3*z.re ∧
      z.re^2+z.im^2 < t^2+2*t*z.re) ↔
    (a < z.re ∧ z.re < 0 ∧ Real.sqrt (4-(z.re+Real.sqrt 3)^2) < z.im ∧
      z.im < Real.sqrt (2*t^2-(z.re-t)^2)) := by
  dsimp only
  let t := Real.sqrt 3+Real.sqrt 2
  let a := -(Real.sqrt 3+2*Real.sqrt 2)/5
  let L := 4-(z.re+Real.sqrt 3)^2
  let U := 2*t^2-(z.re-t)^2
  have hs₃ : (Real.sqrt 3)^2=3 := by norm_num
  have hs₂ : (Real.sqrt 2)^2=2 := by norm_num
  have hp₃ : 0<Real.sqrt 3 := by positivity
  have hp₂ : 0<Real.sqrt 2 := by positivity
  have h₂hi : Real.sqrt 2<3/2 := by nlinarith
  have h₃hi : Real.sqrt 3<7/4 := by nlinarith
  have h₃lo : 1<Real.sqrt 3 := by nlinarith
  have ht : 0<t := by dsimp [t]; positivity
  have ha : -1<a := by dsimp [a]; linarith
  have hmeet : t^2-1+2*(t+Real.sqrt 3)*a=0 := by dsimp [t,a]; nlinarith [hs₃,hs₂]
  have hLo : 1<z.re^2+z.im^2+2*Real.sqrt 3*z.re ↔ L<z.im^2 := by dsimp [L]; constructor <;> intro h <;> nlinarith [hs₃]
  have hUp : z.re^2+z.im^2<t^2+2*t*z.re ↔ z.im^2<U := by dsimp [U]; constructor <;> intro h <;> nlinarith
  have hLpos : ∀ (hax : a<z.re) (hx : z.re<0), 0<L := by
    intro hax hx
    have hxl : -1<z.re := by linarith
    have hb₁ : -2<z.re+Real.sqrt 3 := by linarith
    have hb₂ : z.re+Real.sqrt 3<2 := by linarith
    have hm := mul_pos (show 0<2-(z.re+Real.sqrt 3) by linarith)
      (show 0<2+(z.re+Real.sqrt 3) by linarith)
    dsimp [L]; nlinarith
  constructor
  · rintro ⟨hx,hlo,hup⟩
    have hax : a<z.re := by
      have hm : 0<2*(t+Real.sqrt 3) := by positivity
      have hd : 0<2*(t+Real.sqrt 3)*(z.re-a) := by nlinarith [hmeet]
      have hh := (mul_pos_iff_of_pos_left hm).mp hd
      linarith
    have hLp := hLpos hax hx
    have hLs := Real.sq_sqrt hLp.le
    have hUs := Real.sq_sqrt (show 0≤U by linarith [(hUp.mp hup),sq_nonneg z.im])
    refine ⟨hax,hx,?_,?_⟩
    · change Real.sqrt L<z.im
      nlinarith [hLo.mp hlo,Real.sqrt_nonneg L,z.im_pos]
    · change z.im<Real.sqrt U
      nlinarith [hUp.mp hup,Real.sqrt_nonneg U,z.im_pos]
  · rintro ⟨hax,hx,hlo,hup⟩
    change Real.sqrt L<z.im at hlo
    change z.im<Real.sqrt U at hup
    have hLp := hLpos hax hx
    have hLs := Real.sq_sqrt hLp.le
    have hUp' : 0<U := Real.sqrt_pos.mp (by linarith [z.im_pos])
    have hUs := Real.sq_sqrt hUp'.le
    refine ⟨hx,hLo.mpr ?_,hUp.mpr ?_⟩
    · nlinarith [Real.sqrt_nonneg L,z.im_pos]
    · nlinarith [Real.sqrt_nonneg U,z.im_pos]

theorem regular_hexagon_first_radial_piece_area :
    (μHE[2] : Measure H2) {z | z ∈ regularHexagonRegion.interior ∧
      0 < (cayley z : ℂ).im ∧ Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re} =
      ENNReal.ofReal (Real.pi/12) := by
  have he : {z : H2 | z ∈ regularHexagonRegion.interior ∧
      0 < (cayley z : ℂ).im ∧ Real.sqrt 3*(cayley z : ℂ).im < (cayley z : ℂ).re} =
    {z : H2 | -(Real.sqrt 3+2*Real.sqrt 2)/5 < z.re ∧ z.re < 0 ∧
      Real.sqrt (4-(z.re+Real.sqrt 3)^2) < z.im ∧
      z.im < Real.sqrt (2*(Real.sqrt 3+Real.sqrt 2)^2-(z.re-(Real.sqrt 3+Real.sqrt 2))^2)} := by
    ext z
    exact (regular_hexagon_first_radial_piece_polynomial z).trans
      (compact_canonical_radial_piece_strip_iff z)
  rw [he]
  exact compact_canonical_radial_triangle_strip_area

end CurveComplex.Hyperbolic
