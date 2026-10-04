import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14BigonNonInvariant

namespace CurveComplex.LocalSurgery

theorem TwoCurveDisk.closure_openInterior
    {E : Type} [TopologicalSpace E] [T2Space E]
    {a b : Curve E} (B : TwoCurveDisk a b) :
    closure B.openInterior = Set.range B.disk := by
  have hclosed : IsClosed (Set.range B.disk) := by
    simpa only [Set.image_univ] using (isCompact_univ.image B.disk.continuous).isClosed
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.image_subset_range _ _) hclosed
  · rintro x ⟨w,rfl⟩
    let radial : C(Interval, Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      ⟨fun t => ⟨t.val • w.val, by
        simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg t.property.1]
        have hw : ‖w.val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall,dist_zero_right] using w.property
        exact (mul_le_mul_of_nonneg_left hw t.property.1).trans (by simpa using t.property.2)⟩,
        by fun_prop⟩
    have hone : (1 : Interval) ∈ closure (Set.Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      exact ⟨by norm_num,le_rfl⟩
    have hsubset : (B.disk ∘ radial) '' Set.Ioo (0 : Interval) 1 ⊆ B.openInterior := by
      rintro z ⟨t,ht,rfl⟩
      refine ⟨radial t,?_,rfl⟩
      change t.val • w.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      simp only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1]
      have hw : ‖w.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using w.property
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hw t.property.1)
        (by simpa using ht.2)
    apply closure_mono hsubset
    apply image_closure_subset_closure_image (B.disk.continuous.comp radial.continuous)
    refine ⟨1,hone,?_⟩
    have hr : radial 1 = w := by apply Subtype.ext; simp [radial]
    change B.disk (radial 1) = B.disk w
    rw [hr]

theorem TwoCurveDisk.isPreconnected_openInterior
    {E : Type} [TopologicalSpace E] {a b : Curve E} (B : TwoCurveDisk a b) :
    IsPreconnected B.openInterior := by
  apply IsPreconnected.image _ B.disk B.disk.continuous.continuousOn
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  have heq : Subtype.val ''
      {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        x.val ∈ Metric.ball 0 1} = Metric.ball 0 1 := by
    apply Set.Subset.antisymm
    · rintro z ⟨u,hu,rfl⟩; exact hu
    · intro z hz
      exact ⟨⟨z,Metric.ball_subset_closedBall hz⟩,hz,rfl⟩
  rw [heq]
  exact (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) 1).isPreconnected

/-- Source Lemma 4.5, Step 2, for actual embedded disks: two innermost
disks on the same curves either have disjoint open interiors or coincide. -/
theorem innermost_two_curve_disks_disjoint_or_equal
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    {a b : Curve E} (B C : TwoCurveDisk a b)
    (hB : Disjoint B.openInterior (a.image ∪ b.image))
    (hC : Disjoint C.openInterior (a.image ∪ b.image)) :
    Disjoint B.openInterior C.openInterior ∨ Set.range B.disk = Set.range C.disk := by
  by_cases hdis : Disjoint B.openInterior C.openInterior
  · exact Or.inl hdis
  · right
    have hnon : (B.openInterior ∩ C.openInterior).Nonempty :=
      Set.not_disjoint_iff_nonempty_inter.mp hdis
    have subsetInterior (B C : TwoCurveDisk a b)
        (hB : Disjoint B.openInterior (a.image ∪ b.image))
        (hnon : (B.openInterior ∩ C.openInterior).Nonempty) :
        B.openInterior ⊆ C.openInterior := by
      apply B.isPreconnected_openInterior.subset_of_closure_inter_subset
        (embedded_surface_disk_interior_isOpen C.disk C.disk_embedded) hnon
      rintro x ⟨hx,hxB⟩
      by_contra hxnot
      have hxF : x ∈ frontier (Set.range C.disk) := by
        change x ∈ closure C.openInterior at hx
        rw [C.closure_openInterior] at hx
        change x ∈ closure (Set.range C.disk) \ interior (Set.range C.disk)
        have hclosed : IsClosed (Set.range C.disk) := by
          simpa only [Set.image_univ] using (isCompact_univ.image C.disk.continuous).isClosed
        rw [hclosed.closure_eq,embedded_surface_disk_interior_eq C.disk C.disk_embedded]
        exact ⟨hx,hxnot⟩
      rw [C.frontier_range] at hxF
      apply Set.disjoint_left.mp hB hxB
      rcases hxF with hxF | hxF
      · exact Or.inl (C.first_on_curve hxF)
      · exact Or.inr (C.second_on_curve hxF)
    have heq : B.openInterior = C.openInterior := Set.Subset.antisymm
      (subsetInterior B C hB hnon)
      (subsetInterior C B hC (by simpa only [Set.inter_comm] using hnon))
    rw [← B.closure_openInterior,← C.closure_openInterior,heq]

end CurveComplex.LocalSurgery
