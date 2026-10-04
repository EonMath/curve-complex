import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.Square
import Mathlib.Topology.OpenPartialHomeomorph.Defs

open CurveComplex Set Topology Schoenflies
set_option autoImplicit false

theorem actual_chart_two_ray_disk_sector
    {X : Type} [TopologicalSpace X]
    (E : OpenPartialHomeomorph X Plane)
    (D : Set X) (hD : IsClosed D) (hregular : D ⊆ closure (interior D))
    (e : Plane) (he : e 1 ≠ 0)
    (hTarget : Metric.closedBall (0 : Plane) 1 ⊆ E.target)
    (hFrontier : ∀ z ∈ Metric.ball (0 : Plane) 1,
      E.symm z ∈ frontier D ↔
        (z 1 = 0 ∧ 0 ≤ z 0) ∨
        (z 0 - (e 0 / e 1) * z 1 = 0 ∧ 0 ≤ z 1 / e 1))
    (hRetained : E.symm (Plane.mk (-1 / 2) 0) ∉ D) :
    ∀ z ∈ Metric.ball (0 : Plane) 1,
      E.symm z ∈ D ↔ 0 ≤ z 1 / e 1 ∧ 0 ≤ z 0 - (e 0 / e 1) * z 1 := by
  let theta : Plane → ℝ := fun z => z 1 / e 1
  let ell : Plane → ℝ := fun z => z 0 - (e 0 / e 1) * z 1
  let U : Set Plane := Metric.ball 0 1
  let pos : Set Plane := U ∩ ({z | 0 < theta z} ∩ {z | 0 < ell z})
  let negT : Set Plane := U ∩ {z | theta z < 0}
  let negL : Set Plane := U ∩ {z | ell z < 0}
  let neg : Set Plane := negT ∪ negL
  have hUT : U ⊆ E.target := Metric.ball_subset_closedBall.trans hTarget
  have htheta : IsLinearMap ℝ theta := by
    constructor
    · intro x y
      simp [theta, add_div]
    · intro c x
      simp [theta]
      ring
  have hell : IsLinearMap ℝ ell := by
    constructor
    · intro x y
      simp [ell]
      ring
    · intro c x
      simp [ell]
      ring
  have hPosConn : IsPreconnected pos :=
    ((convex_ball (0 : Plane) 1).inter
      ((convex_halfSpace_gt htheta 0).inter (convex_halfSpace_gt hell 0))).isPreconnected
  have hNegTConn : IsPreconnected negT :=
    ((convex_ball (0 : Plane) 1).inter (convex_halfSpace_lt htheta 0)).isPreconnected
  have hNegLConn : IsPreconnected negL :=
    ((convex_ball (0 : Plane) 1).inter (convex_halfSpace_lt hell 0)).isPreconnected
  have hNegOverlap : (negT ∩ negL).Nonempty := by
    let w : Plane := Plane.mk (-e 0 - 1) (-e 1)
    let r : ℝ := 1 / (2 * (‖w‖ + 1))
    have hr : 0 < r := by dsimp [r]; positivity
    have hrnorm : r * ‖w‖ < 1 := by
      dsimp [r]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖w‖ + 1))).mpr
      nlinarith [norm_nonneg w]
    have hwU : r • w ∈ U := by
      change dist (r • w) 0 < 1
      simpa [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr] using hrnorm
    have hwT : theta (r • w) < 0 := by
      rw [htheta.map_smul]
      have hw : theta w = -1 := by simp [theta, w, he]
      rw [hw]
      simpa using neg_neg_of_pos hr
    have hwL : ell (r • w) < 0 := by
      rw [hell.map_smul]
      have hw : ell w = -1 := by
        dsimp [ell, w]
        field_simp
        ring
      rw [hw]
      simpa using neg_neg_of_pos hr
    exact ⟨r • w, ⟨hwU, hwT⟩, ⟨hwU, hwL⟩⟩
  have hNegConn : IsPreconnected neg := hNegTConn.union' hNegOverlap hNegLConn
  have hPosU : pos ⊆ U := fun _ hz => hz.1
  have hNegU : neg ⊆ U := fun _ hz => hz.elim (fun h => h.1) (fun h => h.1)
  have hfront (z : Plane) (hz : z ∈ U) :
      E.symm z ∈ frontier D ↔
        (theta z = 0 ∧ 0 ≤ ell z) ∨ (ell z = 0 ∧ 0 ≤ theta z) := by
    rw [hFrontier z hz]
    constructor
    · rintro (⟨hy, hx⟩ | ⟨hl, ht⟩)
      · left
        simp [theta, ell, hy, hx]
      · exact Or.inr ⟨hl, ht⟩
    · rintro (⟨ht, hl⟩ | ⟨hl, ht⟩)
      · left
        have hy : z 1 = 0 := (div_eq_zero_iff.mp ht).resolve_right he
        exact ⟨hy, by simpa [ell, hy] using hl⟩
      · exact Or.inr ⟨hl, ht⟩
  let P : Set X := E.symm '' pos
  let N : Set X := E.symm '' neg
  have hPConn : IsPreconnected P :=
    hPosConn.image E.symm (E.symm.continuousOn.mono (hPosU.trans hUT))
  have hNConn : IsPreconnected N :=
    hNegConn.image E.symm (E.symm.continuousOn.mono (hNegU.trans hUT))
  have hPAvoid : Disjoint P (frontier D) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    rcases (hfront z hz.1).mp hx with ht | hl
    · exact (ne_of_gt hz.2.1) ht.1
    · exact (ne_of_gt hz.2.2) hl.1
  have hNAvoid : Disjoint N (frontier D) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    have hf := (hfront z (hNegU hz)).mp hx
    rcases hz with hz | hz <;> rcases hf with ht | hl
    · exact (ne_of_lt hz.2) ht.1
    · exact (not_le_of_gt hz.2) hl.2
    · exact (not_le_of_gt hz.2) ht.2
    · exact (ne_of_lt hz.2) hl.1
  have hClassify (C : Set X) (hc : IsPreconnected C) (ha : Disjoint C (frontier D)) :
      C ⊆ interior D ∨ C ⊆ Dᶜ := by
    have hcover : C ⊆ interior D ∪ Dᶜ := by
      intro x hx
      by_cases hxD : x ∈ D
      · left
        by_contra hn
        exact Set.disjoint_left.mp ha hx (hD.frontier_eq ▸ ⟨hxD, hn⟩)
      · exact Or.inr hxD
    exact hc.subset_or_subset isOpen_interior hD.isOpen_compl
      (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))) hcover
  have hqU : Plane.mk (-1 / 2) 0 ∈ U := by
    change dist (Plane.mk (-1 / 2) 0) 0 < 1
    rw [dist_zero_right]
    have hh := Plane.norm_sq_eq (Plane.mk (-1 / 2) 0)
    norm_num at hh
    nlinarith [norm_nonneg (Plane.mk (-1 / 2) 0)]
  have hqN : E.symm (Plane.mk (-1 / 2) 0) ∈ N := by
    refine ⟨Plane.mk (-1 / 2) 0, Or.inr ⟨hqU, ?_⟩, rfl⟩
    norm_num [ell]
  have hNOut : N ⊆ Dᶜ := by
    rcases hClassify N hNConn hNAvoid with hn | hn
    · exact False.elim (hRetained (interior_subset (hn hqN)))
    · exact hn
  have hSplit (z : Plane) (hz : z ∈ U) (hnf : E.symm z ∉ frontier D) :
      z ∈ pos ∨ z ∈ neg := by
    by_cases ht : theta z < 0
    · exact Or.inr (Or.inl ⟨hz, ht⟩)
    by_cases hl : ell z < 0
    · exact Or.inr (Or.inr ⟨hz, hl⟩)
    have ht' : 0 ≤ theta z := le_of_not_gt ht
    have hl' : 0 ≤ ell z := le_of_not_gt hl
    have htne : theta z ≠ 0 := fun h => hnf ((hfront z hz).mpr (Or.inl ⟨h, hl'⟩))
    have hlne : ell z ≠ 0 := fun h => hnf ((hfront z hz).mpr (Or.inr ⟨h, ht'⟩))
    exact Or.inl ⟨hz, lt_of_le_of_ne ht' (Ne.symm htne),
      lt_of_le_of_ne hl' (Ne.symm hlne)⟩
  have hPIn : P ⊆ interior D := by
    rcases hClassify P hPConn hPAvoid with hp | hp
    · exact hp
    have h0U : (0 : Plane) ∈ U := by simp [U]
    have h0front : E.symm (0 : Plane) ∈ frontier D := by
      apply (hfront 0 h0U).mpr
      simp [theta, ell]
    let O : Set X := E.symm '' U
    have hO : IsOpen O := E.symm.isOpen_image_of_subset_source Metric.isOpen_ball hUT
    have h0O : E.symm (0 : Plane) ∈ O := ⟨0, h0U, rfl⟩
    obtain ⟨x, hxO, hxi⟩ := mem_closure_iff_nhds.mp
      (hregular (hD.frontier_subset h0front)) O (hO.mem_nhds h0O)
    obtain ⟨z, hz, rfl⟩ := hxO
    have hnf : E.symm z ∉ frontier D := fun hf => (hD.frontier_eq ▸ hf).2 hxi
    rcases hSplit z hz hnf with hzP | hzN
    · exact False.elim (hp ⟨z, hzP, rfl⟩ (interior_subset hxi))
    · exact False.elim (hNOut ⟨z, hzN, rfl⟩ (interior_subset hxi))
  intro z hz
  change E.symm z ∈ D ↔ 0 ≤ theta z ∧ 0 ≤ ell z
  constructor
  · intro hd
    constructor
    · by_contra ht
      exact hNOut ⟨z, Or.inl ⟨hz, lt_of_not_ge ht⟩, rfl⟩ hd
    · by_contra hl
      exact hNOut ⟨z, Or.inr ⟨hz, lt_of_not_ge hl⟩, rfl⟩ hd
  · rintro ⟨ht, hl⟩
    by_cases ht0 : theta z = 0
    · exact hD.frontier_subset ((hfront z hz).mpr (Or.inl ⟨ht0, hl⟩))
    by_cases hl0 : ell z = 0
    · exact hD.frontier_subset ((hfront z hz).mpr (Or.inr ⟨hl0, ht⟩))
    exact interior_subset (hPIn ⟨z, ⟨hz, lt_of_le_of_ne ht (Ne.symm ht0),
      lt_of_le_of_ne hl (Ne.symm hl0)⟩, rfl⟩)
