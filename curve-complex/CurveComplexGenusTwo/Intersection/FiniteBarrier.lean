import Schoenflies.JordanClosed
import Mathlib.Analysis.Normed.Module.Connected

namespace Schoenflies

/-- A finite collection of points off a planar arc can be joined to one
common exterior point by polygonal paths. Their union is a closed barrier
avoiding the arc, so the arc has a compact neighborhood disjoint from every
path. This is the finite separation datum for an outer boundary polygon. -/
theorem IsArc.exists_finite_polygonal_barrier
    {A : Set Plane} (hA : IsArc A) (F : Finset Plane)
    (hF : ∀ x ∈ F, x ∉ A) (w : Plane) (hw : w ∉ A)
    (hwF : w ∉ F) (V : Set Plane) (hV : IsOpen V) (hAV : A ⊆ V) :
    ∃ P : {x : Plane // x ∈ F} → Set Plane, ∃ U : Set Plane,
      (∀ i, IsPolygonal (P i) ∧ IsArcBetween (P i) i.val w ∧ P i ⊆ Aᶜ) ∧
      (F.Nonempty → IsConnected (⋃ i, P i)) ∧
      IsOpen U ∧ A ⊆ U ∧ IsCompact (closure U) ∧
        closure U ⊆ V ∧ closure U ⊆ (⋃ i, P i)ᶜ := by
  classical
  have hpath (i : {x : Plane // x ∈ F}) :
      ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P i.val w ∧ P ⊆ Aᶜ :=
    arc_complement_poly hA (by
      intro he
      exact hwF (he ▸ i.property)) (hF i.val i.property) hw
  let P : {x : Plane // x ∈ F} → Set Plane := fun i => Classical.choose (hpath i)
  have hP (i : {x : Plane // x ∈ F}) :
      IsPolygonal (P i) ∧ IsArcBetween (P i) i.val w ∧ P i ⊆ Aᶜ :=
    Classical.choose_spec (hpath i)
  let B : Set Plane := ⋃ i, P i
  have hBconnected : F.Nonempty → IsConnected B := by
    intro hFn
    obtain ⟨x, hx⟩ := hFn
    let i : {x : Plane // x ∈ F} := ⟨x, hx⟩
    have hcommon : (⋂ j, P j).Nonempty := by
      refine ⟨w, Set.mem_iInter.mpr ?_⟩
      intro j
      exact (hP j).2.1.right_mem
    have hpre : IsPreconnected B :=
      isPreconnected_iUnion hcommon (fun j => (hP j).2.1.isArc.isConnected.isPreconnected)
    exact ⟨⟨w, Set.mem_iUnion.mpr ⟨i, (hP i).2.1.right_mem⟩⟩, hpre⟩
  have hBclosed : IsClosed B := by
    exact isClosed_iUnion_of_finite (fun i => (hP i).2.1.isArc.isClosed)
  have hAB : A ⊆ Bᶜ := by
    intro z hz hzB
    rcases Set.mem_iUnion.mp hzB with ⟨i, hi⟩
    exact (hP i).2.2 hi hz
  obtain ⟨U, hUopen, hAU, hClosure, hCompact⟩ :=
    exists_open_between_and_isCompact_closure hA.isCompact
      (hV.inter hBclosed.isOpen_compl) (Set.subset_inter hAV hAB)
  exact ⟨P, U, hP, hBconnected, hUopen, hAU, hCompact,
    (fun _ hx => (hClosure hx).1), (fun _ hx => (hClosure hx).2)⟩

/-- Choose the shared escape endpoint outside a ball already containing the
arc and every forbidden point. The barrier's compact neighborhood is kept
inside that same ball, avoiding any later dependence on a chosen boundary. -/
theorem IsArc.exists_bounded_finite_polygonal_barrier
    {A : Set Plane} (hA : IsArc A) (F : Finset Plane)
    (hF : ∀ x ∈ F, x ∉ A) :
    ∃ R : ℝ, ∃ w : Plane, ∃ P : {x : Plane // x ∈ F} → Set Plane,
      ∃ U : Set Plane,
      0 < R ∧ A ⊆ Metric.ball 0 R ∧
      (F : Set Plane) ⊆ Metric.ball 0 R ∧ w ∉ Metric.closedBall 0 R ∧
      (∀ i, IsPolygonal (P i) ∧ IsArcBetween (P i) i.val w ∧ P i ⊆ Aᶜ) ∧
      (F.Nonempty → IsConnected (⋃ i, P i)) ∧
      IsOpen U ∧ A ⊆ U ∧ IsCompact (closure U) ∧
        closure U ⊆ Metric.ball 0 R ∧
        closure U ⊆ (⋃ i, P i)ᶜ := by
  obtain ⟨R, hR, hball⟩ :=
    (hA.isCompact.isBounded.union F.finite_toSet.isBounded).subset_ball_lt 0 (0 : Plane)
  have hASealed : A ⊆ Metric.ball 0 R :=
    (Set.subset_union_left).trans hball
  have hFSealed : (F : Set Plane) ⊆ Metric.ball 0 R :=
    (Set.subset_union_right).trans hball
  obtain ⟨w, hwNorm⟩ := NormedSpace.exists_lt_norm ℝ Plane R
  have hwClosed : w ∉ Metric.closedBall 0 R := by
    simpa [Metric.mem_closedBall] using not_le.mpr hwNorm
  have hwA : w ∉ A := by
    intro hw
    exact hwClosed (Metric.ball_subset_closedBall (hASealed hw))
  have hwF : w ∉ F := by
    intro hw
    exact hwClosed (Metric.ball_subset_closedBall (hFSealed hw))
  obtain ⟨P, U, hP, hB, hU, hAU, hCompact, hUBall, hUBarrier⟩ :=
    hA.exists_finite_polygonal_barrier F hF w hwA hwF
      (Metric.ball 0 R) Metric.isOpen_ball hASealed
  exact ⟨R, w, P, U, hR, hASealed, hFSealed, hwClosed,
    hP, hB, hU, hAU, hCompact, hUBall, hUBarrier⟩

/-- Any set disjoint from the connected escape barrier leaves all forbidden
marks in the same unbounded complementary component as the shared endpoint. -/
theorem finite_barrier_marks_outside
    {C : Set Plane}
    {F : Finset Plane} (hFn : F.Nonempty) {w : Plane}
    (P : {x : Plane // x ∈ F} → Set Plane)
    (hPw : ∀ i, w ∈ P i) (hPi : ∀ i, i.val ∈ P i)
    (hB : IsConnected (⋃ i, P i))
    (hBC : Disjoint (⋃ i, P i) C)
    (hw : w ∈ outside C) :
    ∀ x ∈ F, x ∈ outside C := by
  let B : Set Plane := ⋃ i, P i
  have hwB : w ∈ B := by
    obtain ⟨x, hx⟩ := hFn
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hPw ⟨x, hx⟩⟩
  have hBsub : B ⊆ Cᶜ := fun _ hz => Set.disjoint_left.mp hBC hz
  have hBcomp : B ⊆ connectedComponentIn Cᶜ w :=
    hB.isPreconnected.subset_connectedComponentIn hwB hBsub
  intro x hx
  have hxB : x ∈ B := Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hPi ⟨x, hx⟩⟩
  have hwUnbounded := (mem_outside_iff.mp hw).2
  refine mem_outside_iff.mpr ⟨hBsub hxB, ?_⟩
  rw [← connectedComponentIn_eq (hBcomp hxB)]
  exact hwUnbounded

/-- The exterior of a closed Euclidean ball is connected in the plane. -/
private theorem connected_compl_closedBall (R : ℝ) (hR : 0 ≤ R) :
    IsConnected (Metric.closedBall (0 : Plane) R)ᶜ := by
  have hrank : 1 < Module.rank ℝ Plane := by
    have h : Module.rank ℝ Plane = 2 := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num
    rw [h]
    norm_num
  have hconn : IsConnected ((Metric.sphere (0 : Plane) 1) ×ˢ (Set.Ioi R)) :=
    (isConnected_sphere hrank 0 zero_le_one).prod isConnected_Ioi
  have himg := hconn.image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have hset : (Metric.closedBall (0 : Plane) R)ᶜ =
      (fun p : Plane × ℝ => p.2 • p.1) ''
        ((Metric.sphere (0 : Plane) 1) ×ˢ (Set.Ioi R)) := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff,
      not_le, Set.mem_image, Set.mem_prod, Set.mem_Ioi, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_norm, inv_mul_cancel₀ (ne_of_gt hxpos)]
      · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos), one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs,
        abs_of_pos (lt_of_le_of_lt hR ht)]
      exact ht
  rw [hset]
  exact himg

/-- If a Jordan boundary lies in a fixed ball, every point beyond that ball
belongs to its unbounded complementary component. -/
theorem outside_of_subset_ball
    {C : Set Plane} {R : ℝ} (hR : 0 ≤ R)
    (hCR : C ⊆ Metric.ball 0 R) {w : Plane}
    (hw : w ∉ Metric.closedBall 0 R) : w ∈ outside C := by
  have hCC : (Metric.closedBall (0 : Plane) R)ᶜ ⊆ Cᶜ := by
    intro z hz hzC
    exact hz (Metric.ball_subset_closedBall (hCR hzC))
  have hcomponent : (Metric.closedBall (0 : Plane) R)ᶜ ⊆
      connectedComponentIn Cᶜ w :=
    (connected_compl_closedBall R hR).isPreconnected.subset_connectedComponentIn
      hw hCC
  refine mem_outside_iff.mpr ⟨hCC hw, ?_⟩
  intro hb
  have hballBound : Bornology.IsBounded (Metric.closedBall (0 : Plane) R)ᶜ :=
    hb.subset hcomponent
  have hBallSquare : Metric.closedBall (0 : Plane) R ⊆
      Plane.closedSquare 0 R := by
    intro z hz
    change Plane.supDist z 0 ≤ R
    simpa [Plane.supDist] using
      (Plane.supNorm_le_norm z).trans (by simpa using hz)
  exact Plane.not_isBounded_compl_closedSquare 0 R
    (hballBound.subset (Set.compl_subset_compl.mpr hBallSquare))

end Schoenflies
