import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalDiskSelfIntrusionCrosscut
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- A genuine interior crosscut and a disk-boundary subarc enclose an actual
    smaller embedded disk, with its open interior in the old open interior. -/
theorem regional_disk_crosscut_bounds_interior_subdisk
    {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : Plane) 1,S))
    (hd : Topology.IsEmbedding d)
    (q g : C(Interval,S))
    (hq : Topology.IsEmbedding q) (hg : Topology.IsEmbedding g)
    (hq0 : q 0 = g 0) (hq1 : q 1 = g 1)
    (hgBoundary : Set.range g ⊆
      d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1})
    (hqInside : q '' Set.Ioo (0 : Interval) 1 ⊆
      d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}) :
    ∃ e : C(Metric.closedBall (0 : Plane) 1,S),
      Topology.IsEmbedding e ∧
      e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
        Set.range q ∪ Set.range g ∧
      Set.range e ⊆ Set.range d ∧
      e '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ⊆
        d '' {z | z.val ∈ Metric.ball (0 : Plane) 1} := by
  let U := d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}
  let C := d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}
  have hfree : Disjoint U C := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv : u = v := hd.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hcross (s t : Interval) (hst : q s = g t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    by_cases hs0 : s = 0
    · left
      refine ⟨hs0,hg.injective ?_⟩
      simpa only [hs0,hq0] using hst.symm
    by_cases hs1 : s = 1
    · right
      refine ⟨hs1,hg.injective ?_⟩
      simpa only [hs1,hq1] using hst.symm
    have hsI : s ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
       lt_of_le_of_ne s.property.2 hs1⟩
    exact False.elim (Set.disjoint_left.mp hfree
      (hqInside ⟨s,hsI,rfl⟩) (hgBoundary ⟨t,hst.symm⟩))
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs
    q g hq.injective hg.injective hq0 hq1 hcross
  have hcD : c.image ⊆ Set.range d := by
    rw [hc]
    apply Set.union_subset
    · rintro x ⟨s,rfl⟩
      by_cases hs0 : s = 0
      · subst s
        exact Set.image_subset_range _ _ (hgBoundary ⟨0,hq0.symm⟩)
      by_cases hs1 : s = 1
      · subst s
        exact Set.image_subset_range _ _ (hgBoundary ⟨1,hq1.symm⟩)
      have hsI : s ∈ Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
         lt_of_le_of_ne s.property.2 hs1⟩
      exact Set.image_subset_range _ _ (hqInside ⟨s,hsI,rfl⟩)
    · exact fun x hx => Set.image_subset_range _ _ (hgBoundary hx)
  obtain ⟨e,he,heB,heD⟩ :=
    CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
      c d hd hcD
  have heOpen : e '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ⊆ U := by
    change e '' {z | z.val ∈ Metric.ball (0 : Plane) 1} ⊆
      d '' {z | z.val ∈ Metric.ball (0 : Plane) 1}
    rw [← CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
    exact (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen e he).subset_interior_iff.mpr
      ((Set.image_subset_range _ _).trans heD)
  exact ⟨e,he,heB.trans hc,heD,heOpen⟩

end RegionalEmbeddedFamily
