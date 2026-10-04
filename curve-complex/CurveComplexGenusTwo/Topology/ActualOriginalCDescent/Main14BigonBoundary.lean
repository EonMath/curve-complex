import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14BigonProjectedCorners
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14BigonProjection

open Set Topology

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem innermost_full_preimage_disk_projection_injOn
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    Set.InjOn M.cover.projection (Set.range B.disk) := by
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : T2Space S := M.sphere.symm.t2Space
  change a.val.image = M.cover.projection ⁻¹' c.curve.image at ha
  change b.val.image = M.cover.projection ⁻¹' d.curve.image at hb
  have hcorners := M.innermost_full_preimage_disk_projected_corners_ne a b ht B c d ha hb htbase hempty
  have hclean := LocalSurgery.empty_two_curve_disk_has_clean_sides a b ht B hempty
  have hfirst : IsEmbedding ((⟨M.cover.projection,M.cover.projection_continuous⟩ : C(E,S)).comp B.firstSide) :=
    M.cover.clean_lifted_side_projection_embedding c.curve d.curve c.avoids_branch d.avoids_branch
      B.firstSide B.first_embedded (by rw [← ha]; exact B.first_on_curve)
      (by rw [← hb,B.first_zero,B.first_one]; exact hclean.1)
      (by rw [B.first_zero,B.first_one]; exact hcorners)
  have hsecond : IsEmbedding ((⟨M.cover.projection,M.cover.projection_continuous⟩ : C(E,S)).comp B.secondSide) :=
    M.cover.clean_lifted_side_projection_embedding d.curve c.curve d.avoids_branch c.avoids_branch
      B.secondSide B.second_embedded (by rw [← hb]; exact B.second_on_curve)
      (by rw [← ha,B.second_zero,B.second_one]; exact hclean.2)
      (by rw [B.second_zero,B.second_one]; exact hcorners)
  have sideInj (α : C(Interval,E))
      (hi : IsEmbedding ((⟨M.cover.projection,M.cover.projection_continuous⟩ : C(E,S)).comp α)) :
      Set.InjOn M.cover.projection (Set.range α) := by
    rintro x ⟨t,rfl⟩ y ⟨u,rfl⟩ he
    exact congrArg α (hi.injective he)
  have cornerInj : Set.InjOn M.cover.projection ({B.firstCorner,B.secondCorner} : Set E) := by
    intro x hx y hy he
    rcases Set.mem_insert_iff.mp hx with hx | hx <;>
      rcases Set.mem_insert_iff.mp hy with hy | hy
    · exact hx.trans hy.symm
    · have hy' := Set.mem_singleton_iff.mp hy
      exact False.elim (hcorners (by simpa only [hx,hy'] using he))
    · have hx' := Set.mem_singleton_iff.mp hx
      exact False.elim (hcorners (by simpa only [hx',hy] using he.symm))
    · exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
  have crossInj {x y : E} (hx : x ∈ Set.range B.firstSide) (hy : y ∈ Set.range B.secondSide)
      (he : M.cover.projection x = M.cover.projection y) : x = y := by
    have hxB : x ∈ b.val.image := by
      rw [hb]
      change M.cover.projection x ∈ d.image
      rw [he]
      have h := B.second_on_curve hy
      rwa [hb] at h
    have hyA : y ∈ a.val.image := by
      rw [ha]
      change M.cover.projection y ∈ c.image
      rw [← he]
      have h := B.first_on_curve hx
      rwa [ha] at h
    exact cornerInj (hclean.1 ▸ ⟨hx,hxB⟩) (hclean.2 ▸ ⟨hy,hyA⟩) he
  have hboundary : Set.InjOn M.cover.projection (frontier (Set.range B.disk)) := by
    rw [B.frontier_range]
    intro x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact sideInj B.firstSide hfirst hx hy he
    · exact crossInj hx hy he
    · exact (crossInj hy hx he.symm).symm
    · exact sideInj B.secondSide hsecond hx hy he
  have hdis := LocalSurgery.innermost_two_curve_disk_deck_interiors_disjoint
    M.cover a b ht B c.curve d.curve ha hb c.avoids_branch hempty
  have hinterior := M.cover.projection_injOn_of_disjoint_deck hdis
  have boundaryMem {x : E} (hx : x ∈ Set.range B.disk) (hxi : x ∉ B.openInterior) :
      x ∈ frontier (Set.range B.disk) := by
    have hclosed : IsClosed (Set.range B.disk) := by
      simpa only [Set.image_univ] using (isCompact_univ.image B.disk.continuous).isClosed
    rw [frontier,hclosed.closure_eq,LocalSurgery.embedded_surface_disk_interior_eq B.disk B.disk_embedded]
    exact ⟨hx,hxi⟩
  have crossInteriorImpossible {x y : E} (hx : x ∈ B.openInterior)
      (hy : y ∈ frontier (Set.range B.disk))
      (he : M.cover.projection x = M.cover.projection y) : False := by
    rw [B.frontier_range] at hy
    apply Set.disjoint_left.mp hempty hx
    rcases hy with hy | hy
    · left
      rw [ha]
      change M.cover.projection x ∈ c.image
      rw [he]
      have h := B.first_on_curve hy
      rwa [ha] at h
    · right
      rw [hb]
      change M.cover.projection x ∈ d.image
      rw [he]
      have h := B.second_on_curve hy
      rwa [hb] at h
  intro x hx y hy he
  by_cases hxi : x ∈ B.openInterior <;> by_cases hyi : y ∈ B.openInterior
  · exact hinterior hxi hyi he
  · exact False.elim (crossInteriorImpossible hxi (boundaryMem hy hyi) he)
  · exact False.elim (crossInteriorImpossible hyi (boundaryMem hx hxi) he.symm)
  · exact hboundary (boundaryMem hx hxi) (boundaryMem hy hyi) he

/-- Full closed-disk/deck disjointness from the actual sphere, actual transverse
full preimages, and actual innermostness. No disjointness certificate is input. -/
theorem innermost_full_preimage_disk_disjoint_deck
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    Disjoint (Set.range B.disk) (M.cover.deck '' Set.range B.disk) := by
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hi := M.innermost_full_preimage_disk_projection_injOn a b ht B c d ha hb htbase hempty
  have hfree := LocalSurgery.innermost_two_curve_disk_image_disjoint_branch
    M.cover a b ht B c.curve d.curve ha hb c.avoids_branch d.avoids_branch hempty
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y,hy,hyx⟩
  have he : y = x := hi hy hx (by rw [← hyx,M.cover.projection_deck])
  have hfix : M.cover.deck x = x := he ▸ hyx
  exact Set.disjoint_left.mp hfree ⟨x,hx,rfl⟩ ((M.cover.fixed_iff_branch x).mp hfix)

end CurveComplex.HyperellipticModel
