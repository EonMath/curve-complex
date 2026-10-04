import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.CountControlledChordAndTails

open Set Schoenflies
namespace CurveComplex
noncomputable section

/-- Explicit anisotropic rectangle coordinates, with horizontal endpoints fixed. -/
def countCrosscutRectangleHomeomorph (lo hi r : ℝ) (hlohi : lo < hi) (hr : 0 < r) :
    Plane ≃ₜ Plane where
  toFun z := Plane.mk ((lo+hi)/2 + ((hi-lo)/2)*z 0) (r*z 1)
  invFun z := Plane.mk ((z 0-(lo+hi)/2)/((hi-lo)/2)) (z 1/r)
  left_inv z := by
    have hx : (hi-lo)/2 ≠ 0 := by linarith
    ext i
    fin_cases i <;> simp [Plane.mk,hx,hr.ne']
  right_inv z := by
    have hx : (hi-lo)/2 ≠ 0 := by linarith
    ext i
    fin_cases i <;> simp [Plane.mk] <;> field_simp [sub_ne_zero.mpr (ne_of_gt hlohi),hr.ne'] <;> ring
  continuous_toFun := by
    exact PiLp.continuous_toLp 2 _ |>.comp
      (continuous_pi (fun i => by fin_cases i <;> simp <;> fun_prop))
  continuous_invFun := by
    exact PiLp.continuous_toLp 2 _ |>.comp
      (continuous_pi (fun i => by fin_cases i <;> simp <;> fun_prop))

theorem countCrosscutRectangleCenterImage (lo hi r : ℝ) (hlohi : lo < hi) (hr : 0 < r) :
    (countCrosscutRectangleHomeomorph lo hi r hlohi hr) ''
      segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) = segment ℝ (Plane.mk lo 0) (Plane.mk hi 0) := by
  rw [segment_eq_image_lineMap,segment_eq_image_lineMap,Set.image_image]
  congr 1
  funext t
  ext i
  fin_cases i <;> simp [countCrosscutRectangleHomeomorph,AffineMap.lineMap_apply_module,Plane.mk] <;> ring

theorem countCrosscutRectangleClosedCoordinates (lo hi r : ℝ) (hlohi : lo < hi) (hr : 0 < r)
    (z : Plane) (hz : z ∈ Plane.closedSquare 0 1) :
    lo ≤ (countCrosscutRectangleHomeomorph lo hi r hlohi hr z) 0 ∧
      (countCrosscutRectangleHomeomorph lo hi r hlohi hr z) 0 ≤ hi ∧
      |(countCrosscutRectangleHomeomorph lo hi r hlohi hr z) 1| ≤ r := by
  have hz0 : |z 0| ≤ 1 := by simpa using (Plane.abs_sub_zero_le_supDist z 0 |>.trans hz)
  have hz1 : |z 1| ≤ 1 := by simpa using (Plane.abs_sub_one_le_supDist z 0 |>.trans hz)
  have hz0' := abs_le.mp hz0
  have hrx : 0 < (hi-lo)/2 := by linarith
  change lo ≤ (lo+hi)/2+((hi-lo)/2)*z 0 ∧
      (lo+hi)/2+((hi-lo)/2)*z 0 ≤ hi ∧ |r*z 1| ≤ r
  refine ⟨by nlinarith [hz0'.1],by nlinarith [hz0'.2],?_⟩
  rw [abs_mul,abs_of_pos hr]
  nlinarith

theorem countCrosscutRectangleOpenSquare (lo hi r : ℝ) (hlohi : lo < hi) (hr : 0 < r)
    (hlo : -1 ≤ lo) (hhi : hi ≤ 1) (hr1 : r ≤ 1) :
    (countCrosscutRectangleHomeomorph lo hi r hlohi hr) '' Plane.openSquare 0 1 ⊆ Plane.openSquare 0 1 := by
  rintro z ⟨w,hw,rfl⟩
  rw [Plane.mem_openSquare_iff] at hw ⊢
  have hw0 : |w 0| < 1 := by simpa using hw 0
  have hw1 : |w 1| < 1 := by simpa using hw 1
  have hw0' := abs_lt.mp hw0
  have hrx : 0 < (hi-lo)/2 := by linarith
  intro i
  simp only [PiLp.zero_apply,sub_zero]
  fin_cases i
  · change |(lo+hi)/2+((hi-lo)/2)*w 0| < 1
    rw [abs_lt]
    constructor <;> nlinarith [hw0'.1,hw0'.2]
  · change |r*w 1| < 1
    rw [abs_mul,abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left hw1 hr).trans_le (by simpa using hr1)

/-- Thin actual source rectangle around a retained center subsegment. The whole
closed rectangle avoids the prescribed finite actual target points. -/
theorem countCrosscutThinRectangleAvoidingFinite
    (E : OpenPartialHomeomorph Plane Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ E.source)
    (lo hi : ℝ) (hlohi : lo < hi) (hlo : -1 ≤ lo) (hhi : hi ≤ 1)
    (K : Set Plane) (hK : K.Finite) (hKt : K ⊆ E.target)
    (havoid : ∀ z ∈ segment ℝ (Plane.mk lo 0) (Plane.mk hi 0), E z ∉ K) :
    ∃ r : ℝ, ∃ hr : 0 < r, r ≤ 1 ∧
      (countCrosscutRectangleHomeomorph lo hi r hlohi hr) (Plane.mk (-1) 0) = Plane.mk lo 0 ∧
      (countCrosscutRectangleHomeomorph lo hi r hlohi hr) (Plane.mk 1 0) = Plane.mk hi 0 ∧
      (countCrosscutRectangleHomeomorph lo hi r hlohi hr) '' Plane.closedSquare 0 1 ⊆
        Plane.closedSquare 0 1 ∧
      ∀ z ∈ Plane.closedSquare 0 1,
        E ((countCrosscutRectangleHomeomorph lo hi r hlohi hr) z) ∉ K := by
  classical
  let A := segment ℝ (Plane.mk lo 0) (Plane.mk hi 0)
  let Q := E.symm '' K
  have hQ : Q.Finite := hK.image _
  have hASquare : A ⊆ Plane.closedSquare 0 1 := by
    intro z hz
    change z ∈ segment ℝ (Plane.mk lo 0) (Plane.mk hi 0) at hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    change Plane.supDist _ 0 ≤ 1
    simp only [Plane.supDist,Plane.supNorm,sub_zero,max_le_iff]
    constructor
    · have hc : (AffineMap.lineMap (Plane.mk lo 0) (Plane.mk hi 0) t) 0 = (1-t)*lo+t*hi := by
        simp [AffineMap.lineMap_apply_module,Plane.mk]
      rw [hc]
      rw [abs_le]
      constructor <;> nlinarith [ht.1,ht.2]
    · simp [AffineMap.lineMap_apply_module,Plane.mk]
  have hAQ : A ⊆ Qᶜ := by
    intro z hz hq
    obtain ⟨k,hk,hkz⟩ := hq
    apply havoid z hz
    rw [← hkz,E.right_inv (hKt hk)]
    exact hk
  obtain ⟨δ,hδ,hthick⟩ := (isCompact_segment (Plane.mk lo 0) (Plane.mk hi 0)).exists_thickening_subset_open
    hQ.isClosed.isOpen_compl hAQ
  let r := min δ 1/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_left δ 1]
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [min_le_right δ 1]
  let H := countCrosscutRectangleHomeomorph lo hi r hlohi hr
  have hHcoord (z : Plane) : H z=Plane.mk ((lo+hi)/2+((hi-lo)/2)*z 0) (r*z 1) := rfl
  have hends : H (Plane.mk (-1) 0)=Plane.mk lo 0 ∧ H (Plane.mk 1 0)=Plane.mk hi 0 := by
    constructor <;> ext i <;> fin_cases i <;> simp [hHcoord,Plane.mk] <;> ring
  have hcoordinates (z : Plane) (hz : z ∈ Plane.closedSquare 0 1) :
      lo ≤ (H z) 0 ∧ (H z) 0 ≤ hi ∧ |(H z) 1| ≤ r := by
    have hz0 : |z 0| ≤ 1 := by simpa using (Plane.abs_sub_zero_le_supDist z 0 |>.trans hz)
    have hz1 : |z 1| ≤ 1 := by simpa using (Plane.abs_sub_one_le_supDist z 0 |>.trans hz)
    simp only [PiLp.zero_apply,sub_zero] at hz0 hz1
    have hz0' := abs_le.mp hz0
    have hrx : 0 < (hi-lo)/2 := by linarith
    change lo ≤ (lo+hi)/2+((hi-lo)/2)*z 0 ∧
      (lo+hi)/2+((hi-lo)/2)*z 0 ≤ hi ∧ |r*z 1| ≤ r
    refine ⟨by nlinarith [hz0'.1],by nlinarith [hz0'.2],?_⟩
    rw [abs_mul,abs_of_pos hr]
    nlinarith
  have hHSquare : H '' Plane.closedSquare 0 1 ⊆ Plane.closedSquare 0 1 := by
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨hx0,hx1,hy⟩ := hcoordinates w hw
    change Plane.supDist _ 0 ≤ 1
    simp only [Plane.supDist,Plane.supNorm,sub_zero,max_le_iff]
    exact ⟨abs_le.mpr ⟨hlo.trans hx0,hx1.trans hhi⟩,hy.trans hr1⟩
  refine ⟨r,hr,hr1,hends.1,hends.2,hHSquare,?_⟩
  intro z hz hk
  have hcoord := hcoordinates z hz
  let w := Plane.mk ((H z) 0) 0
  have hwA : w ∈ A := by
    change w ∈ segment ℝ (Plane.mk lo 0) (Plane.mk hi 0)
    rw [segment_eq_image_lineMap]
    refine ⟨((H z) 0-lo)/(hi-lo),?_,?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hcoord.1) (by linarith)
      · apply (div_le_one (show 0 < hi-lo by linarith)).mpr
        linarith [hcoord.2.1]
    · ext i
      fin_cases i
      · change (AffineMap.lineMap (Plane.mk lo 0) (Plane.mk hi 0) (((H z) 0-lo)/(hi-lo))) 0 = (H z) 0
        have hc (t : ℝ) : (AffineMap.lineMap (Plane.mk lo 0) (Plane.mk hi 0) t) 0 = (1-t)*lo+t*hi := by
          simp [AffineMap.lineMap_apply_module,Plane.mk]
        rw [hc]
        field_simp [sub_ne_zero.mpr (ne_of_gt hlohi)]
        ring
      · simp [AffineMap.lineMap_apply_module,Plane.mk,w]
  have hdist : dist (H z) w = |(H z) 1| := by
    rw [dist_eq_norm]
    have he : H z-w=Plane.mk 0 ((H z) 1) := by
      ext i;fin_cases i <;> simp [w,Plane.mk]
    rw [he]
    simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,Real.sqrt_sq_eq_abs]
  have hzQ : H z ∉ Q := hthick (Metric.mem_thickening_iff.mpr
    ⟨w,hwA,hdist ▸ (hcoord.2.2.trans_lt hrδ)⟩)
  apply hzQ
  refine ⟨E (H z),hk,?_⟩
  exact E.left_inv (hSquare (hHSquare ⟨z,hz,rfl⟩))

end
end CurveComplex
