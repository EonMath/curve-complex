import CurveComplexGenusTwo.Dictionary.BranchedCover
open Set Topology Metric
namespace CurveComplex.BranchedDoubleCover
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
set_option maxHeartbeats 2000000

/-- The local disk parametrizations commute with the squaring map. -/
theorem square_chart_disk_projection (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) (r : ℝ) (hr : 0 < r)
    (hu : Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target)
    (hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    q.projection ((q.branch_chart w hw).upstairs.symm z) =
      (q.branch_chart w hw).downstairs.symm (z^2) := by
  let c := q.branch_chart w hw
  have hsrc := c.upstairs.map_target (hu hz)
  have hz2 : z^2 ∈ Metric.closedBall (0 : ℂ) (r^2) := by
    simp only [Metric.mem_closedBall,dist_zero_right] at hz ⊢
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  apply c.downstairs.injOn (c.image_mem _ hsrc) (c.downstairs.map_target (hd hz2))
  rw [c.square _ hsrc,c.upstairs.right_inv (hu hz),c.downstairs.right_inv (hd hz2)]

/-- A sufficiently small square branch chart contains the complete preimage
of its round downstairs disk; no other sheet remains outside the chart. -/
theorem square_chart_disk_preimage (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) (r : ℝ) (hr : 0 < r)
    (hu : Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target)
    (hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target) :
    q.projection ⁻¹' ((q.branch_chart w hw).downstairs.symm ''
      Metric.closedBall (0 : ℂ) (r^2)) =
      (q.branch_chart w hw).upstairs.symm '' Metric.closedBall (0 : ℂ) r := by
  let c := q.branch_chart w hw
  have lift (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
      q.projection (c.upstairs.symm z) = c.downstairs.symm (z^2) := by
    have hsrc := c.upstairs.map_target (hu hz)
    have hz2 : z^2 ∈ Metric.closedBall (0 : ℂ) (r^2) := by
      simp only [Metric.mem_closedBall,dist_zero_right] at hz ⊢
      rw [norm_pow]
      nlinarith [norm_nonneg z]
    apply c.downstairs.injOn (c.image_mem _ hsrc) (c.downstairs.map_target (hd hz2))
    rw [c.square _ hsrc,c.upstairs.right_inv (hu hz),c.downstairs.right_inv (hd hz2)]
  have hzero : c.upstairs.symm 0 = w := by
    rw [← c.upstairs_center]
    exact c.upstairs.left_inv c.upstairs_mem
  ext x
  constructor
  · rintro ⟨b,hb,hbx⟩
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq b (by norm_num : 0 < 2)
    have hzBall : z ∈ Metric.closedBall (0 : ℂ) r := by
      have hbNorm : ‖b‖ ≤ r^2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hb
      have hNorm : ‖z‖^2 = ‖b‖ := by rw [← norm_pow,hz]
      simp only [Metric.mem_closedBall,dist_zero_right]
      nlinarith [norm_nonneg z]
    have hnzBall : -z ∈ Metric.closedBall (0 : ℂ) r := by
      simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hzBall
    have hpz : q.projection (c.upstairs.symm z) = q.projection x := by
      rw [lift z hzBall,hz]
      exact hbx
    have hpnz : q.projection (c.upstairs.symm (-z)) = q.projection x := by
      rw [lift (-z) hnzBall,neg_sq,hz]
      exact hbx
    by_cases hz0 : z = 0
    · subst z
      have hxw : x = w := by
        rcases (q.fiber_pair (c.upstairs.symm 0) x).mp hpz with hh | hh
        · simpa only [hzero] using hh
        · simpa only [hzero,(q.fixed_iff_branch w).mpr hw] using hh
      exact ⟨0,hzBall,hzero.trans hxw.symm⟩
    · have hneq : c.upstairs.symm z ≠ c.upstairs.symm (-z) := by
        intro he
        have hcoord : z = -z := by
          calc z = c.upstairs (c.upstairs.symm z) := (c.upstairs.right_inv (hu hzBall)).symm
               _ = c.upstairs (c.upstairs.symm (-z)) := congrArg c.upstairs he
               _ = -z := c.upstairs.right_inv (hu hnzBall)
        exact hz0 (CharZero.eq_neg_self_iff.mp hcoord)
      have hnegative : c.upstairs.symm (-z) = q.deck (c.upstairs.symm z) := by
        rcases (q.fiber_pair (c.upstairs.symm z) (c.upstairs.symm (-z))).mp
          (hpz.trans hpnz.symm) with hh | hh
        · exact False.elim (hneq hh.symm)
        · exact hh
      rcases (q.fiber_pair (c.upstairs.symm z) x).mp hpz with hh | hh
      · exact ⟨z,hzBall,hh.symm⟩
      · exact ⟨-z,hnzBall,hnegative.trans hh.symm⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨z^2,?_,(lift z hz).symm⟩
    simp only [Metric.mem_closedBall,dist_zero_right] at hz ⊢
    rw [norm_pow]
    nlinarith [norm_nonneg z]

/-- The actual deck action on the full local disk is coordinate negation. -/
theorem square_chart_disk_deck (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) (r : ℝ) (hr : 0 < r)
    (hu : Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target)
    (hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    q.deck ((q.branch_chart w hw).upstairs.symm z) =
      (q.branch_chart w hw).upstairs.symm (-z) := by
  let c := q.branch_chart w hw
  have hnz : -z ∈ Metric.closedBall (0 : ℂ) r := by
    simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hz
  have hzero : c.upstairs.symm 0 = w := by
    rw [← c.upstairs_center]
    exact c.upstairs.left_inv c.upstairs_mem
  by_cases hz0 : z = 0
  · subst z
    change q.deck (c.upstairs.symm 0) = c.upstairs.symm (-0)
    simp only [neg_zero,hzero,(q.fixed_iff_branch w).mpr hw]
  · have hπ : q.projection (c.upstairs.symm z) = q.projection (c.upstairs.symm (-z)) := by
      rw [q.square_chart_disk_projection w hw r hr hu hd z hz,
        q.square_chart_disk_projection w hw r hr hu hd (-z) hnz,neg_sq]
    rcases (q.fiber_pair (c.upstairs.symm z) (c.upstairs.symm (-z))).mp hπ with hh | hh
    · have he : -z = z := by
        calc -z = c.upstairs (c.upstairs.symm (-z)) := (c.upstairs.right_inv (hu hnz)).symm
             _ = c.upstairs (c.upstairs.symm z) := congrArg c.upstairs hh
             _ = z := c.upstairs.right_inv (hu hz)
      exact False.elim (hz0 (CharZero.eq_neg_self_iff.mp he.symm))
    · exact hh.symm

/-- The complete local lifted disk has exactly one ramification point. -/
theorem square_chart_disk_branch_iff_zero (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) (r : ℝ) (hr : 0 < r)
    (hu : Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target)
    (hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    q.projection ((q.branch_chart w hw).upstairs.symm z) ∈ q.branch ↔ z = 0 := by
  let c := q.branch_chart w hw
  rw [← q.fixed_iff_branch, q.square_chart_disk_deck w hw r hr hu hd z hz]
  constructor
  · intro he
    have hnz : -z ∈ Metric.closedBall (0 : ℂ) r := by
      simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hz
    have hh : -z = z := by
      calc -z = c.upstairs (c.upstairs.symm (-z)) := (c.upstairs.right_inv (hu hnz)).symm
           _ = c.upstairs (c.upstairs.symm z) := congrArg c.upstairs he
           _ = z := c.upstairs.right_inv (hu hz)
    exact CharZero.eq_neg_self_iff.mp hh.symm
  · rintro rfl
    simp only [neg_zero]

/-- Boundary membership is preserved exactly by the local branched disk lift. -/
theorem square_chart_disk_boundary_iff (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) (r : ℝ) (hr : 0 < r)
    (hu : Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target)
    (hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) :
    q.projection ((q.branch_chart w hw).upstairs.symm z) ∈
      (q.branch_chart w hw).downstairs.symm '' Metric.sphere (0 : ℂ) (r^2) ↔
        ‖z‖ = r := by
  let c := q.branch_chart w hw
  rw [q.square_chart_disk_projection w hw r hr hu hd z hz]
  have hz2 : z^2 ∈ Metric.closedBall (0 : ℂ) (r^2) := by
    simp only [Metric.mem_closedBall,dist_zero_right] at hz ⊢
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  constructor
  · rintro ⟨b,hb,he⟩
    have hbBall : b ∈ Metric.closedBall (0 : ℂ) (r^2) := by
      simp only [Metric.mem_sphere,dist_zero_right] at hb
      simp only [Metric.mem_closedBall,dist_zero_right,hb,le_refl]
    have hbz : b = z^2 := c.downstairs.symm.injOn (hd hbBall) (hd hz2) he
    have hh : ‖z‖^2 = r^2 := by
      rw [hbz,Metric.mem_sphere,dist_zero_right,norm_pow] at hb
      exact hb
    nlinarith [norm_nonneg z]
  · intro he
    refine ⟨z^2,?_,rfl⟩
    simp only [Metric.mem_sphere,dist_zero_right,norm_pow,he]

/-- An actual disk homeomorphism for a complete local branched preimage,
constructed directly from the source's square branch chart. -/
theorem local_square_disk_lift_exists (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target ∧
      Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target ∧
      ∃ h : Metric.closedBall (0 : ℂ) r ≃ₜ
        (q.projection ⁻¹' ((q.branch_chart w hw).downstairs.symm ''
          Metric.closedBall (0 : ℂ) (r^2))),
        ∀ z, (h z).val = (q.branch_chart w hw).upstairs.symm z.val := by
  let c := q.branch_chart w hw
  have hzU : (0 : ℂ) ∈ c.upstairs.target := by
    simpa only [c.upstairs_center] using c.upstairs.map_source c.upstairs_mem
  have hzD : (0 : ℂ) ∈ c.downstairs.target := by
    simpa only [c.downstairs_center] using c.downstairs.map_source c.downstairs_mem
  obtain ⟨εu,hεu,hU⟩ := Metric.isOpen_iff.mp c.upstairs.open_target 0 hzU
  obtain ⟨εd,hεd,hD⟩ := Metric.isOpen_iff.mp c.downstairs.open_target 0 hzD
  let r := min εu (min εd 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hru : r < εu := by
    have hh := min_le_left εu (min εd 1)
    dsimp [r]; linarith
  have hrd : r < εd := by
    have hh := (min_le_right εu (min εd 1)).trans (min_le_left εd 1)
    dsimp [r]; linarith
  have hr1 : r ≤ 1 := by
    have hh := (min_le_right εu (min εd 1)).trans (min_le_right εd 1)
    dsimp [r]; linarith
  have hu : Metric.closedBall (0 : ℂ) r ⊆ c.upstairs.target := by
    intro z hz
    apply hU
    simp only [Metric.mem_closedBall,dist_zero_right] at hz
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_le_of_lt hz hru
  have hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ c.downstairs.target := by
    intro z hz
    apply hD
    simp only [Metric.mem_closedBall,dist_zero_right] at hz
    have hh : ‖z‖ < εd := by nlinarith
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hset := q.square_chart_disk_preimage w hw r hr hu hd
  let h := c.upstairs.symm.homeomorphOfImageSubsetSource hu hset.symm
  exact ⟨r,hr,hu,hd,h,fun _ => rfl⟩

/-- The complete local branched disk can be chosen inside any prescribed open
neighborhood of its branch value. This supplies interior pieces, not only a
parametrized boundary lift. -/
theorem local_square_disk_lift_exists_within (q : BranchedDoubleCover E S) (w : E)
    (hw : q.projection w ∈ q.branch) (O : Set S) (hO : IsOpen O)
    (hwO : q.projection w ∈ O) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (0 : ℂ) r ⊆ (q.branch_chart w hw).upstairs.target ∧
      Metric.closedBall (0 : ℂ) (r^2) ⊆ (q.branch_chart w hw).downstairs.target ∧
      (q.branch_chart w hw).downstairs.symm '' Metric.closedBall (0 : ℂ) (r^2) ⊆ O ∧
      ∃ h : Metric.closedBall (0 : ℂ) r ≃ₜ
        (q.projection ⁻¹' ((q.branch_chart w hw).downstairs.symm ''
          Metric.closedBall (0 : ℂ) (r^2))),
        ∀ z, (h z).val = (q.branch_chart w hw).upstairs.symm z.val := by
  let c := q.branch_chart w hw
  have hzU : (0 : ℂ) ∈ c.upstairs.target := by
    simpa only [c.upstairs_center] using c.upstairs.map_source c.upstairs_mem
  have hzD : (0 : ℂ) ∈ c.downstairs.target := by
    simpa only [c.downstairs_center] using c.downstairs.map_source c.downstairs_mem
  have hzero : c.downstairs.symm 0 = q.projection w := by
    rw [← c.downstairs_center]
    exact c.downstairs.left_inv c.downstairs_mem
  have hopen : IsOpen (c.downstairs.target ∩ c.downstairs.symm ⁻¹' O) :=
    c.downstairs.symm.isOpen_inter_preimage hO
  have hzO : (0 : ℂ) ∈ c.downstairs.target ∩ c.downstairs.symm ⁻¹' O := by
    refine ⟨hzD,?_⟩
    change c.downstairs.symm 0 ∈ O
    rw [hzero]
    exact hwO
  obtain ⟨εu,hεu,hU⟩ := Metric.isOpen_iff.mp c.upstairs.open_target 0 hzU
  obtain ⟨εd,hεd,hD⟩ := Metric.isOpen_iff.mp hopen 0 hzO
  let r := min εu (min εd 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hru : r < εu := by
    have hh := min_le_left εu (min εd 1)
    dsimp [r]; linarith
  have hrd : r < εd := by
    have hh := (min_le_right εu (min εd 1)).trans (min_le_left εd 1)
    dsimp [r]; linarith
  have hr1 : r ≤ 1 := by
    have hh := (min_le_right εu (min εd 1)).trans (min_le_right εd 1)
    dsimp [r]; linarith
  have hu : Metric.closedBall (0 : ℂ) r ⊆ c.upstairs.target := by
    intro z hz
    apply hU
    simp only [Metric.mem_closedBall,dist_zero_right] at hz
    simpa only [Metric.mem_ball,dist_zero_right] using lt_of_le_of_lt hz hru
  have hboth : Metric.closedBall (0 : ℂ) (r^2) ⊆
      c.downstairs.target ∩ c.downstairs.symm ⁻¹' O := by
    intro z hz
    apply hD
    simp only [Metric.mem_closedBall,dist_zero_right] at hz
    have hh : ‖z‖ < εd := by nlinarith
    simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hd : Metric.closedBall (0 : ℂ) (r^2) ⊆ c.downstairs.target :=
    fun z hz => (hboth hz).1
  have hsub : c.downstairs.symm '' Metric.closedBall (0 : ℂ) (r^2) ⊆ O := by
    rintro x ⟨z,hz,rfl⟩
    exact (hboth hz).2
  have hset := q.square_chart_disk_preimage w hw r hr hu hd
  let h := c.upstairs.symm.homeomorphOfImageSubsetSource hu hset.symm
  exact ⟨r,hr,hu,hd,hsub,h,fun _ => rfl⟩

end CurveComplex.BranchedDoubleCover
#print axioms CurveComplex.BranchedDoubleCover.local_square_disk_lift_exists
#print axioms CurveComplex.BranchedDoubleCover.local_square_disk_lift_exists_within
