import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14ClosedBranchCoverSide
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14SphereSingleCrossing

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source Lemma 4.5's corner-exchange case is impossible. If the projected
corners agreed, angular lifting would force each side to traverse its whole
downstairs circle; clean sides then force a single transverse sphere crossing. -/
theorem innermost_full_preimage_disk_projected_corners_ne
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    M.cover.projection B.firstCorner ≠ M.cover.projection B.secondCorner := by
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : T2Space S := M.sphere.symm.t2Space
  change a.val.image = M.cover.projection ⁻¹' c.curve.image at ha
  change b.val.image = M.cover.projection ⁻¹' d.curve.image at hb
  intro hcorners
  have hclosed : M.cover.projection (B.firstSide 0) = M.cover.projection (B.firstSide 1) := by
    rw [B.first_zero,B.first_one]
    exact hcorners
  have hside : Set.range (M.cover.projection ∘ B.firstSide) = c.curve.image :=
    M.cover.embedded_lifted_interval_closed_projection_covers_circle
      c.curve c.avoids_branch B.firstSide B.first_embedded
      (by rw [← ha]; exact B.first_on_curve) hclosed
  have hclean := (LocalSurgery.empty_two_curve_disk_has_clean_sides a b ht B hempty).1
  have hinter : c.curve.image ∩ d.curve.image = {M.cover.projection B.firstCorner} := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨t,htz⟩ := hside.symm ▸ hz.1
      change M.cover.projection (B.firstSide t) = z at htz
      have hm : B.firstSide t ∈ Set.range B.firstSide ∩ b.val.image := by
        refine ⟨⟨t,rfl⟩,?_⟩
        rw [hb]
        change M.cover.projection (B.firstSide t) ∈ d.image
        rw [htz]
        exact hz.2
      rw [hclean] at hm
      rcases Set.mem_insert_iff.mp hm with he | he
      · exact Set.mem_singleton_iff.mpr (htz.symm.trans (congrArg M.cover.projection he))
      · exact Set.mem_singleton_iff.mpr (htz.symm.trans
          ((congrArg M.cover.projection (Set.mem_singleton_iff.mp he)).trans hcorners.symm))
    · intro z hz
      have he := Set.mem_singleton_iff.mp hz
      subst z
      constructor
      · have h : B.firstCorner ∈ a.val.image := B.first_on_curve ⟨0,B.first_zero⟩
        rwa [ha] at h
      · have h : B.firstCorner ∈ b.val.image := B.second_on_curve ⟨0,B.second_zero⟩
        rwa [hb] at h
  have hpoint : M.cover.projection B.firstCorner ∈ c.curve.image ∩ d.curve.image := by
    rw [hinter]
    simp
  have hpCross := htbase.2 _ hpoint
  have hnonempty : M.cover.branch.Nonempty := Finset.card_pos.mp (by rw [M.cover.branch_card]; norm_num)
  obtain ⟨pole,hpole⟩ := hnonempty
  have hc : pole ∉ c.curve.image := fun h => Set.disjoint_left.mp c.avoids_branch h hpole
  have hd : pole ∉ d.curve.image := fun h => Set.disjoint_left.mp d.avoids_branch h hpole
  exact M.sphere_curves_cannot_cross_once pole c.curve d.curve hc hd
    (M.cover.projection B.firstCorner) hpCross hinter

end CurveComplex.HyperellipticModel
