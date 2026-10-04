import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Intersection.FiniteBarrier

set_option maxHeartbeats 1000000

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The original marked arc in its selected puncture chart. -/
noncomputable def chartedArcMap
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image) : Interval → Schoenflies.Plane := fun t =>
  M.puncturedPlane p ⟨a.val.map t, by
    intro he
    exact hp (he ▸ Set.mem_range_self t)⟩

/-- The branch marks other than the puncture and the two arc endpoints,
expressed in the actual stereographic plane chart. -/
noncomputable def planeForbiddenMarks
    {M : HyperellipticModel E S} (a : NonLoopArc M) (p : S) :
    Finset Schoenflies.Plane := by
  classical
  let Q := M.cover.branch.filter (fun x =>
    x ≠ p ∧ x ≠ a.val.map ⟨0, by norm_num⟩ ∧
      x ≠ a.val.map ⟨1, by norm_num⟩)
  exact Q.image (fun x =>
    if hx : x ≠ p then M.puncturedPlane p ⟨x, hx⟩ else 0)

/-- No forbidden mark lands on the plane arc. -/
theorem NonLoopArc.planeForbiddenMarks_avoid_arc
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image) :
    ∀ y ∈ planeForbiddenMarks a p,
      y ∉ Set.range (chartedArcMap a p hp) := by
  classical
  let Q := M.cover.branch.filter (fun x =>
    x ≠ p ∧ x ≠ a.val.map ⟨0, by norm_num⟩ ∧
      x ≠ a.val.map ⟨1, by norm_num⟩)
  let e := M.puncturedPlane p
  intro y hy hya
  change y ∈ Q.image (fun x =>
    if hx : x ≠ p then e ⟨x, hx⟩ else 0) at hy
  obtain ⟨x, hxQ, rfl⟩ := Finset.mem_image.mp hy
  have hxQ' := (Finset.mem_filter.mp hxQ).2
  have hxp : x ≠ p := hxQ'.1
  have hcoord : (if hx : x ≠ p then e ⟨x, hx⟩ else 0) = e ⟨x, hxp⟩ := by
    simp [hxp]
  rw [hcoord] at hya
  obtain ⟨t, ht⟩ := hya
  have hxt : x = a.val.map t :=
    congrArg Subtype.val (e.injective ht.symm)
  have hxE : x ∈ ({a.val.map ⟨0, by norm_num⟩,
      a.val.map ⟨1, by norm_num⟩} : Set S) := by
    rw [← a.image_inter_branch]
    exact ⟨⟨t, hxt.symm⟩, (Finset.mem_filter.mp hxQ).1⟩
  rcases Set.mem_insert_iff.mp hxE with h | h
  · exact hxQ'.2.1 h
  · have h' : x = a.val.map ⟨1, by norm_num⟩ := by simpa using h
    exact hxQ'.2.2 h'

/-- Removing the chart puncture and the arc's two endpoints from six branch
marks still leaves planar marks to be excluded by the polygonal barrier. -/
theorem NonLoopArc.planeForbiddenMarks_nonempty
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) :
    (planeForbiddenMarks a p).Nonempty := by
  classical
  by_contra hEmpty
  have hSmall : M.cover.branch ⊆
      ({p, a.val.map ⟨0, by norm_num⟩,
        a.val.map ⟨1, by norm_num⟩} : Finset S) := by
    intro x hx
    by_contra hxThree
    have hxp : x ≠ p := by
      intro he
      exact hxThree (by simp [he])
    have hx0 : x ≠ a.val.map ⟨0, by norm_num⟩ := by
      intro he
      exact hxThree (by simp [he])
    have hx1 : x ≠ a.val.map ⟨1, by norm_num⟩ := by
      intro he
      exact hxThree (by simp [he])
    have hxF : M.puncturedPlane p ⟨x, hxp⟩ ∈ planeForbiddenMarks a p := by
      unfold planeForbiddenMarks
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_filter.mpr ⟨hx, hxp, hx0, hx1⟩, ?_⟩
      simp [hxp]
    exact hEmpty ⟨_, hxF⟩
  have hcard := Finset.card_le_card hSmall
  rw [M.cover.branch_card] at hcard
  have hthree : ({p, a.val.map ⟨0, by norm_num⟩,
      a.val.map ⟨1, by norm_num⟩} : Finset S).card ≤ 3 := Finset.card_le_three
  omega

/-- The four forbidden branch marks acquire polygonal escape paths to a
common exterior point. A compact arc neighborhood avoids the entire barrier. -/
theorem NonLoopArc.exists_marked_polygonal_barrier
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image)
    (w : Schoenflies.Plane)
    (hw : w ∉ Set.range (chartedArcMap a p hp))
    (hwF : w ∉ planeForbiddenMarks a p)
    (V : Set Schoenflies.Plane) (hV : IsOpen V)
    (hAV : Set.range (chartedArcMap a p hp) ⊆ V) :
    ∃ P : {x : Schoenflies.Plane // x ∈ planeForbiddenMarks a p} →
        Set Schoenflies.Plane,
      ∃ U : Set Schoenflies.Plane,
      (∀ i, Schoenflies.IsPolygonal (P i) ∧
        Schoenflies.IsArcBetween (P i) i.val w ∧
          P i ⊆ (Set.range (chartedArcMap a p hp))ᶜ) ∧
      ((planeForbiddenMarks a p).Nonempty → IsConnected (⋃ i, P i)) ∧
      IsOpen U ∧ Set.range (chartedArcMap a p hp) ⊆ U ∧
        IsCompact (closure U) ∧
        closure U ⊆ V ∧ closure U ⊆ (⋃ i, P i)ᶜ := by
  exact (a.plane_isArcBetween p hp).isArc.exists_finite_polygonal_barrier
    (planeForbiddenMarks a p) (a.planeForbiddenMarks_avoid_arc p hp)
    w hw hwF V hV hAV

/-- A bounded version fixes the common exterior endpoint before selecting
any polygonal neighborhood of the arc. -/
theorem NonLoopArc.exists_bounded_marked_barrier
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image) :
    ∃ R : ℝ, ∃ w : Schoenflies.Plane,
      ∃ P : {x : Schoenflies.Plane // x ∈ planeForbiddenMarks a p} →
        Set Schoenflies.Plane,
      ∃ U : Set Schoenflies.Plane,
      0 < R ∧ Set.range (chartedArcMap a p hp) ⊆ Metric.ball 0 R ∧
      (planeForbiddenMarks a p : Set Schoenflies.Plane) ⊆ Metric.ball 0 R ∧
      w ∉ Metric.closedBall 0 R ∧
      (∀ i, Schoenflies.IsPolygonal (P i) ∧
        Schoenflies.IsArcBetween (P i) i.val w ∧
          P i ⊆ (Set.range (chartedArcMap a p hp))ᶜ) ∧
      ((planeForbiddenMarks a p).Nonempty → IsConnected (⋃ i, P i)) ∧
      IsOpen U ∧ Set.range (chartedArcMap a p hp) ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ Metric.ball 0 R ∧
        closure U ⊆ (⋃ i, P i)ᶜ := by
  exact (a.plane_isArcBetween p hp).isArc.exists_bounded_finite_polygonal_barrier
    (planeForbiddenMarks a p) (a.planeForbiddenMarks_avoid_arc p hp)

end CurveComplex.HyperellipticModel
