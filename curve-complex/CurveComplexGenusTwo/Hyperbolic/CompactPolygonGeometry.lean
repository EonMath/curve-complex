import CurveComplexGenusTwo.Hyperbolic.HexagonAngles
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity

namespace CurveComplex.Hyperbolic
open Topology

theorem closedPolygon_isCompact {P : Hexagon} (R : HexagonRegion P) :
    IsCompact (closure R.interior) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure R.bounded_interior.closure

noncomputable instance closedPolygon_compactSpace {P : Hexagon}
    (R : HexagonRegion P) : CompactSpace (ClosedPolygon R) :=
  isCompact_iff_compactSpace.mp (closedPolygon_isCompact R)

theorem polygon_double_compact {P : Hexagon} (R : HexagonRegion P) :
    CompactSpace (Metric.GlueSpace (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R)) := by
  let L := Metric.toGlueL (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R)
  let Q := Metric.toGlueR (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R)
  have hL : IsCompact (Set.range L) :=
    isCompact_range (Metric.toGlueL_isometry _ _).continuous
  have hQ : IsCompact (Set.range Q) :=
    isCompact_range (Metric.toGlueR_isometry _ _).continuous
  apply isCompact_univ_iff.mp
  convert hL.union hQ using 1
  ext x
  simp only [Set.mem_univ, Set.mem_union, Set.mem_range, true_iff]
  refine Quotient.inductionOn x ?_
  intro p
  cases p with
  | inl p => exact Or.inl ⟨p, rfl⟩
  | inr p => exact Or.inr ⟨p, rfl⟩

theorem polygon_double_vertex_injective {P : Hexagon} (R : HexagonRegion P) :
    Function.Injective (fun i : Fin 6 =>
      Metric.toGlueL (boundaryInclusion_isometry R)
        (boundaryInclusion_isometry R)
        (⟨P.vertex i, hexagon_vertex_mem_closure P R i⟩ : ClosedPolygon R)) := by
  intro i j hij
  apply P.injective
  exact congrArg Subtype.val ((Metric.toGlueL_isometry _ _).injective hij)

theorem metric_segment_on_vertical {a b z : H2}
    (hab : a.re = b.re)
    (hz : dist a z + dist z b = dist a b) : z.re = a.re := by
  have h1 := UpperHalfPlane.dist_log_im_le a z
  have h2 := UpperHalfPlane.dist_log_im_le z b
  have ht := dist_triangle (Real.log a.im) (Real.log z.im) (Real.log b.im)
  have heq : dist (Real.log a.im) (Real.log z.im) = dist a z := by
    rw [UpperHalfPlane.dist_of_re_eq hab] at hz
    linarith
  exact (re_eq_of_dist_log_im_eq a z heq).symm

private theorem cosh_triangle_gram (u v : ℝ) :
    1 + 2 * Real.cosh u * Real.cosh v * Real.cosh (u + v) -
      (Real.cosh u) ^ 2 - (Real.cosh v) ^ 2 -
      (Real.cosh (u + v)) ^ 2 = 0 := by
  rw [Real.cosh_add]
  nlinarith [Real.cosh_sq_sub_sinh_sq u, Real.cosh_sq_sub_sinh_sq v,
    mul_self_nonneg (Real.sinh u * Real.sinh v),
    congrArg (fun t : ℝ => t * (Real.cosh v) ^ 2)
      (Real.cosh_sq_sub_sinh_sq u),
    congrArg (fun t : ℝ => t * (Real.sinh u) ^ 2)
      (Real.cosh_sq_sub_sinh_sq v)]

private theorem coordinate_gram_identity (a b z : H2) :
    1 + 2 *
      (((a.re - z.re) ^ 2 + a.im ^ 2 + z.im ^ 2) / (2 * a.im * z.im)) *
      (((z.re - b.re) ^ 2 + z.im ^ 2 + b.im ^ 2) / (2 * z.im * b.im)) *
      (((a.re - b.re) ^ 2 + a.im ^ 2 + b.im ^ 2) / (2 * a.im * b.im)) -
      (((a.re - z.re) ^ 2 + a.im ^ 2 + z.im ^ 2) / (2 * a.im * z.im)) ^ 2 -
      (((z.re - b.re) ^ 2 + z.im ^ 2 + b.im ^ 2) / (2 * z.im * b.im)) ^ 2 -
      (((a.re - b.re) ^ 2 + a.im ^ 2 + b.im ^ 2) / (2 * a.im * b.im)) ^ 2 =
    ((b.re - a.re) * (Complex.normSq (z : ℂ) - Complex.normSq (a : ℂ)) -
      (z.re - a.re) * (Complex.normSq (b : ℂ) - Complex.normSq (a : ℂ))) ^ 2 /
        (4 * a.im ^ 2 * b.im ^ 2 * z.im ^ 2) := by
  simp only [Complex.normSq_apply, UpperHalfPlane.re, UpperHalfPlane.im]
  have ha : (a : ℂ).im ≠ 0 := a.im_pos.ne'
  have hb : (b : ℂ).im ≠ 0 := b.im_pos.ne'
  have hz : (z : ℂ).im ≠ 0 := z.im_pos.ne'
  field_simp [ha, hb, hz]
  ring

theorem metric_segment_circle_equation {a b z : H2}
    (hz : dist a z + dist z b = dist a b) :
    (b.re - a.re) * (Complex.normSq (z : ℂ) - Complex.normSq (a : ℂ)) =
      (z.re - a.re) * (Complex.normSq (b : ℂ) - Complex.normSq (a : ℂ)) := by
  have hgram := cosh_triangle_gram (dist a z) (dist z b)
  rw [hz, UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist',
    UpperHalfPlane.cosh_dist', coordinate_gram_identity] at hgram
  have hden : 4 * a.im ^ 2 * b.im ^ 2 * z.im ^ 2 ≠ 0 := by positivity
  have hs := (div_eq_zero_iff).mp hgram |>.resolve_right hden
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

private theorem eq_of_re_normSq_eq {p z : H2}
    (hx : z.re = p.re) (hn : Complex.normSq (z : ℂ) = Complex.normSq (p : ℂ)) :
    z = p := by
  apply UpperHalfPlane.ext_re_im hx
  change z.re * z.re + z.im * z.im = p.re * p.re + p.im * p.im at hn
  rw [hx] at hn
  nlinarith [z.im_pos, p.im_pos]

private theorem right_angle_centres_ne {p q r : H2}
    (hq : p.re ≠ q.re) (hr : p.re ≠ r.re) (hangle : IsRightAngle q p r) :
    semicircleCentre p q ≠ semicircleCentre p r := by
  intro hc
  change (p : ℂ).re ≠ (q : ℂ).re at hq
  change (p : ℂ).re ≠ (r : ℂ).re at hr
  have ht :
      (p.re - semicircleCentre p q) * (p.re - semicircleCentre p r) + p.im ^ 2 = 0 := by
    simp only [IsRightAngle, geodesicTangent, if_neg hq, if_neg hr,
      star_mul', star_sub, Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      one_mul, mul_one, zero_add, add_zero, sub_zero, zero_sub, neg_mul,
      neg_neg, neg_add_rev] at hangle
    change ((p : ℂ).re - semicircleCentre p q) *
      ((p : ℂ).re - semicircleCentre p r) + (p : ℂ).im ^ 2 = 0
    convert hangle using 1 <;> ring
  rw [hc] at ht
  nlinarith [sq_nonneg (p.re - semicircleCentre p r), p.im_pos]

theorem right_angle_metric_segments_intersect_only_at_vertex {p q r z : H2}
    (hangle : IsRightAngle q p r)
    (hqz : dist p z + dist z q = dist p q)
    (hrz : dist p z + dist z r = dist p r) : z = p := by
  have hcircleq := metric_segment_circle_equation hqz
  have hcircler := metric_segment_circle_equation hrz
  by_cases hq : p.re = q.re
  · have hx := metric_segment_on_vertical hq hqz
    by_cases hr : p.re = r.re
    · have htq : geodesicTangent p q = Complex.I := if_pos hq
      have htr : geodesicTangent p r = Complex.I := if_pos hr
      unfold IsRightAngle at hangle
      rw [htq, htr] at hangle
      norm_num [Complex.star_def] at hangle
    · apply eq_of_re_normSq_eq hx
      rw [hx, sub_self, zero_mul] at hcircler
      exact sub_eq_zero.mp ((mul_eq_zero.mp hcircler).resolve_left
        (sub_ne_zero.mpr (Ne.symm hr)))
  · by_cases hr : p.re = r.re
    · have hx := metric_segment_on_vertical hr hrz
      apply eq_of_re_normSq_eq hx
      rw [hx, sub_self, zero_mul] at hcircleq
      exact sub_eq_zero.mp ((mul_eq_zero.mp hcircleq).resolve_left
        (sub_ne_zero.mpr (Ne.symm hq)))
    · have hcentres := right_angle_centres_ne hq hr hangle
      have hcoef :
          (q.re - p.re) * (Complex.normSq (r : ℂ) - Complex.normSq (p : ℂ)) -
          (r.re - p.re) * (Complex.normSq (q : ℂ) - Complex.normSq (p : ℂ)) ≠ 0 := by
        intro hc
        apply hcentres
        unfold semicircleCentre
        apply (div_eq_div_iff
          (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hq)))
          (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hr)))).mpr
        nlinarith [hc]
      have hproduct : (z.re - p.re) *
          ((q.re - p.re) * (Complex.normSq (r : ℂ) - Complex.normSq (p : ℂ)) -
          (r.re - p.re) * (Complex.normSq (q : ℂ) - Complex.normSq (p : ℂ))) = 0 := by
        linear_combination (r.re - p.re) * hcircleq - (q.re - p.re) * hcircler
      have hx : z.re = p.re := sub_eq_zero.mp
        ((mul_eq_zero.mp hproduct).resolve_right hcoef)
      apply eq_of_re_normSq_eq hx
      rw [hx, sub_self, zero_mul] at hcircleq
      exact sub_eq_zero.mp ((mul_eq_zero.mp hcircleq).resolve_left
        (sub_ne_zero.mpr (Ne.symm hq)))

theorem regularHexagon_pair_cosh_dist (i j : Fin 6) :
    Real.cosh (dist (regularHexagonH2Point i) (regularHexagonH2Point j)) =
      1 + 2 * Complex.normSq (regularHexagonDiscPoint i -
          regularHexagonDiscPoint j) /
        ((1 - regularHexagonRadius ^ 2) ^ 2) := by
  have h := cayleyInverse_cosh_dist
    (⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩)
    (⟨regularHexagonDiscPoint j, regularHexagonDiscPoint_mem_ball j⟩)
  change Real.cosh (dist (regularHexagonH2Point i)
    (regularHexagonH2Point j)) = _ at h
  rw [h]
  rw [show Complex.normSq (regularHexagonDiscPoint i) =
      regularHexagonRadius ^ 2 by
        rw [Complex.normSq_eq_norm_sq, regularHexagonDiscPoint_norm],
    show Complex.normSq (regularHexagonDiscPoint j) =
      regularHexagonRadius ^ 2 by
        rw [Complex.normSq_eq_norm_sq, regularHexagonDiscPoint_norm]]
  ring

theorem idealHexagon_nonadjacent_chord_gt (i j : Fin 6)
    (hij : i ≠ j) (hnext : i + 1 ≠ j) (hprev : j + 1 ≠ i) :
    1 < Complex.normSq (idealHexagonVertex i - idealHexagonVertex j) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  fin_cases i <;> fin_cases j <;>
    norm_num [idealHexagonVertex, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im] at * <;>
      ring_nf at * <;> nlinarith [show (Real.sqrt 3) ^ 2 = 3 by norm_num]

theorem regularHexagon_nonadjacent_dist_gt_side (i j k : Fin 6)
    (hij : i ≠ j) (hnext : i + 1 ≠ j) (hprev : j + 1 ≠ i) :
    dist (regularHexagonH2Point k) (regularHexagonH2Point (k + 1)) <
      dist (regularHexagonH2Point i) (regularHexagonH2Point j) := by
  have hr : 0 < regularHexagonRadius ^ 2 :=
    sq_pos_of_pos regularHexagonRadius_pos
  have hr1 : regularHexagonRadius ^ 2 < 1 := by
    nlinarith [regularHexagonRadius_pos, regularHexagonRadius_lt_one]
  have hden : 0 < (1 - regularHexagonRadius ^ 2) ^ 2 := by positivity
  have hchord := idealHexagon_nonadjacent_chord_gt i j hij hnext hprev
  have hscaled : regularHexagonRadius ^ 2 <
      Complex.normSq (regularHexagonDiscPoint i - regularHexagonDiscPoint j) := by
    rw [regularHexagonDiscPoint, regularHexagonDiscPoint, ← mul_sub,
      Complex.normSq_mul, Complex.normSq_ofReal]
    nlinarith
  have hcosh :
      Real.cosh (dist (regularHexagonH2Point k) (regularHexagonH2Point (k + 1))) <
      Real.cosh (dist (regularHexagonH2Point i) (regularHexagonH2Point j)) := by
    rw [regularHexagon_adjacent_cosh_dist, regularHexagon_pair_cosh_dist]
    apply add_lt_add_right
    apply (div_lt_div_iff_of_pos_right hden).mpr
    linarith
  have hc := Real.cosh_lt_cosh.mp hcosh
  simpa only [abs_of_nonneg dist_nonneg] using hc

theorem regularHexagon_nonadjacent_edges_disjoint (i j : Fin 6)
    (hij : i ≠ j) (hnext : i + 1 ≠ j) (hprev : j + 1 ≠ i) :
    Disjoint (regularHexagonCandidate.edge i) (regularHexagonCandidate.edge j) := by
  apply Hexagon.edges_disjoint_of_cross_sum_gt
  have h1 := regularHexagon_nonadjacent_dist_gt_side i j i hij hnext hprev
  have hij' : i + 1 ≠ j + 1 := by
    intro h
    exact hij (add_right_cancel h)
  have hnext' : i + 1 + 1 ≠ j + 1 := by
    intro h
    exact hnext (add_right_cancel h)
  have hprev' : j + 1 + 1 ≠ i + 1 := by
    intro h
    exact hprev (add_right_cancel h)
  have h2 := regularHexagon_nonadjacent_dist_gt_side (i + 1) (j + 1) j
    hij' hnext' hprev'
  change dist (regularHexagonH2Point i) (regularHexagonH2Point j) +
      dist (regularHexagonH2Point (i + 1)) (regularHexagonH2Point (j + 1)) >
      dist (regularHexagonH2Point i) (regularHexagonH2Point (i + 1)) +
      dist (regularHexagonH2Point j) (regularHexagonH2Point (j + 1))
  linarith

theorem regularHexagon_adjacent_edges_intersection (i : Fin 6) {z : H2}
    (hi : z ∈ regularHexagonCandidate.edge i)
    (hj : z ∈ regularHexagonCandidate.edge (i + 1)) :
    z = regularHexagonCandidate.vertex (i + 1) := by
  apply right_angle_metric_segments_intersect_only_at_vertex
    (q := regularHexagonCandidate.vertex i)
    (r := regularHexagonCandidate.vertex (i + 1 + 1))
  · simpa only [add_sub_cancel_right] using regularHexagonCandidate_right_angles (i + 1)
  · change dist (regularHexagonCandidate.vertex i) z +
      dist z (regularHexagonCandidate.vertex (i + 1)) =
      dist (regularHexagonCandidate.vertex i)
        (regularHexagonCandidate.vertex (i + 1)) at hi
    simpa only [dist_comm, add_comm] using hi
  · exact hj

theorem regularHexagonCandidate_embedded :
    ∀ i j : Fin 6, i ≠ j →
      regularHexagonCandidate.edge i ∩ regularHexagonCandidate.edge j ⊆
        ({regularHexagonCandidate.vertex i,
          regularHexagonCandidate.vertex (i + 1)} : Set H2) ∩
        ({regularHexagonCandidate.vertex j,
          regularHexagonCandidate.vertex (j + 1)} : Set H2) := by
  intro i j hij z hz
  by_cases hnext : i + 1 = j
  · have hzi := regularHexagon_adjacent_edges_intersection i hz.1 (hnext ▸ hz.2)
    rw [hzi]
    simp [hnext]
  · by_cases hprev : j + 1 = i
    · have hzj := regularHexagon_adjacent_edges_intersection j hz.2 (hprev ▸ hz.1)
      rw [hzj]
      simp [hprev]
    · exact False.elim ((Set.disjoint_left.mp
        (regularHexagon_nonadjacent_edges_disjoint i j hij hnext hprev)) hz.1 hz.2)

end CurveComplex.Hyperbolic
