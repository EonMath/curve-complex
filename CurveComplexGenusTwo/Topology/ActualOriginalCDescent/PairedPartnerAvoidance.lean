import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.FourComponentDeckDisk

namespace CurveComplex.LocalSurgery
open Set Topology

theorem globally_empty_disk_misses_paired_partners
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (D : TwoCurveDisk a0.val b0.val)
    (hclean : Disjoint D.openInterior
      ((a0.val.image ∪ a1.val.image) ∪
        (b0.val.image ∪ b1.val.image))) :
    Disjoint (range D.disk) (a1.val.image ∪ b1.val.image) := by
  have hclean01 : Disjoint D.openInterior (a0.val.image ∪ b1.val.image) := by
    apply hclean.mono_right
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have hNoFirst : Disjoint (range D.firstSide) b1.val.image :=
    third_component_misses_clean_disk_side a0 b1 b0 ht01 D hBd.symm hclean01
  let R : TwoCurveDisk b0.val a0.val := {
    firstCorner := D.firstCorner, secondCorner := D.secondCorner,
    corners_ne := D.corners_ne, firstSide := D.secondSide, secondSide := D.firstSide,
    first_embedded := D.second_embedded, second_embedded := D.first_embedded,
    first_zero := D.second_zero, second_zero := D.first_zero,
    first_one := D.second_one, second_one := D.first_one,
    first_on_curve := D.second_on_curve, second_on_curve := D.first_on_curve,
    sides_inter := by rw [Set.inter_comm]; exact D.sides_inter,
    disk := D.disk, disk_embedded := D.disk_embedded,
    boundary_eq := by rw [D.boundary_eq, Set.union_comm] }
  have hclean10 : Disjoint R.openInterior (b0.val.image ∪ a1.val.image) := by
    apply hclean.mono_right
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inl (Or.inr hx)
  have hNoSecond : Disjoint (range D.secondSide) a1.val.image :=
    third_component_misses_clean_disk_side b0 a1 a0
      (transverse_symm_of_chart ht10) R hAd.symm hclean10
  have boundaryMem {x : E} (hx : x ∈ range D.disk)
      (hxi : x ∉ D.openInterior) :
      x ∈ range D.firstSide ∪ range D.secondSide := by
    rw [← D.frontier_range]
    have hclosed : IsClosed (range D.disk) := by
      simpa only [Set.image_univ] using (isCompact_univ.image D.disk.continuous).isClosed
    rw [frontier, hclosed.closure_eq,
      embedded_surface_disk_interior_eq D.disk D.disk_embedded]
    exact ⟨hx, hxi⟩
  apply Set.disjoint_left.mpr
  intro x hx hxPartner
  by_cases hxi : x ∈ D.openInterior
  · exact Set.disjoint_left.mp hclean hxi
      (by rcases hxPartner with hxPartner | hxPartner
          · exact Or.inl (Or.inr hxPartner)
          · exact Or.inr (Or.inr hxPartner))
  · rcases boundaryMem hx hxi with hfirst | hsecond
    · rcases hxPartner with hxA | hxB
      · exact Set.disjoint_left.mp hAd (D.first_on_curve hfirst) hxA
      · exact Set.disjoint_left.mp hNoFirst hfirst hxB
    · rcases hxPartner with hxA | hxB
      · exact Set.disjoint_left.mp hNoSecond hsecond hxA
      · exact Set.disjoint_left.mp hBd (D.second_on_curve hsecond) hxB

end CurveComplex.LocalSurgery
