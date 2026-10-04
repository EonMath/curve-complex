import ClassificationOfSurfaces.Moise.Brouwer
import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapSide
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Connected.Clopen

open Set Topology
namespace CurveComplex

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def diskInterior : Set UnitDisk :=
  {x | (x : Plane) ∈ Metric.ball 0 1}
private def innerDisk : Set UnitDisk :=
  {x | (x : Plane) ∈ Metric.closedBall 0 (1 / 2)}

open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

/-- The interior image of a bounding disk is open in a charted surface. -/
theorem embedded_disk_interior_isOpen
    {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    IsOpen (f '' diskInterior) := by
  let g : Metric.ball (0 : Plane) 1 → S :=
    fun x => f ⟨x.1, Metric.ball_subset_closedBall x.2⟩
  have hg : IsEmbedding g := by
    have hinc : IsEmbedding (fun x : Metric.ball (0 : Plane) 1 =>
        (⟨x.1, Metric.ball_subset_closedBall x.2⟩ : UnitDisk)) :=
      IsEmbedding.inclusion Metric.ball_subset_closedBall
    exact hf.comp hinc
  have hopen : IsOpen (Set.range g) :=
    isOpen_range_of_isOpen_of_isEmbedding (modelWithCornersSelf ℝ Plane)
      Metric.isOpen_ball g hg
  have heq : Set.range g = f '' diskInterior := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨⟨u.1, Metric.ball_subset_closedBall u.2⟩, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u.1, hu⟩, rfl⟩
  exact heq ▸ hopen

/-- An explicit open cover from an embedded disk: the cap is its interior;
the other side omits a smaller compact disk. -/
theorem embedded_disk_open_cover
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    IsOpen (f '' innerDisk)ᶜ ∧ IsOpen (f '' diskInterior) ∧
      (f '' innerDisk)ᶜ ∪ (f '' diskInterior) = Set.univ := by
  have hcompact : IsCompact (f '' innerDisk) := by
    letI : CompactSpace UnitDisk :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) 1)
    have hclosed : IsClosed innerDisk := by
      exact Metric.isClosed_closedBall.preimage continuous_subtype_val
    exact hclosed.isCompact.image f.continuous
  refine ⟨hcompact.isClosed.isOpen_compl,
    embedded_disk_interior_isOpen f hf, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hx : x ∈ f '' innerDisk
  · right
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨u, ?_, rfl⟩
    change dist (u : Plane) 0 ≤ (1 / 2 : ℝ) at hu
    change dist (u : Plane) 0 < (1 : ℝ)
    linarith
  · exact Or.inl hx

/-- The cap side of the explicit cover is contractible. -/
theorem embedded_disk_interior_contractible
    {S : Type*} [TopologicalSpace S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    ContractibleSpace ↥(f '' diskInterior) := by
  let g : Metric.ball (0 : Plane) 1 → S :=
    fun x => f ⟨x.1, Metric.ball_subset_closedBall x.2⟩
  have hg : IsEmbedding g :=
    hf.comp (IsEmbedding.inclusion Metric.ball_subset_closedBall)
  have heq : Set.range g = f '' diskInterior := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨⟨u.1, Metric.ball_subset_closedBall u.2⟩, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u.1, hu⟩, rfl⟩
  letI : ContractibleSpace (Metric.ball (0 : Plane) 1) :=
    Metric.contractibleSpace_ball (by norm_num)
  let e : Metric.ball (0 : Plane) 1 ≃ₜ ↥(f '' diskInterior) :=
    hg.toHomeomorph.trans (Homeomorph.setCongr heq)
  exact e.symm.contractibleSpace

/-- An actual disk-derived open cover with its cap located on one side of N. -/
theorem bounding_disk_literal_cover
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (N : Set S) (c : Curve S) (hfront : frontier N = c.image)
    (hbound : BoundsDisc c) :
    ∃ f : C(UnitDisk, S), IsEmbedding f ∧
      IsOpen (f '' innerDisk)ᶜ ∧ IsOpen (f '' diskInterior) ∧
      (f '' innerDisk)ᶜ ∪ (f '' diskInterior) = Set.univ ∧
      ContractibleSpace ↥(f '' diskInterior) ∧
      (f '' diskInterior ⊆ interior N ∨
        f '' diskInterior ⊆ interior Nᶜ) := by
  obtain ⟨f, hf, hside⟩ := bounding_disk_side N c hfront hbound
  change f '' diskInterior ⊆ interior N ∨
    f '' diskInterior ⊆ interior Nᶜ at hside
  obtain ⟨hU, hV, hcover⟩ := embedded_disk_open_cover f hf
  exact ⟨f, hf, hU, hV, hcover,
    embedded_disk_interior_contractible f hf, hside⟩

/-- The overlap of the literal cover is precisely the embedded annulus. -/
theorem embedded_disk_cover_overlap
    {S : Type*} [TopologicalSpace S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    (f '' innerDisk)ᶜ ∩ (f '' diskInterior) =
      f '' (diskInterior \ innerDisk) := by
  ext x
  constructor
  · rintro ⟨hx, u, hu, rfl⟩
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    intro huinner
    exact hx ⟨u, huinner, rfl⟩
  · rintro ⟨u, ⟨hu, huinner⟩, rfl⟩
    refine ⟨?_, ⟨u, hu, rfl⟩⟩
    rintro ⟨v, hvinner, heq⟩
    exact huinner (hf.injective heq.symm ▸ hvinner)

private def planeAnnulus : Set Plane :=
  {x | (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1}

private theorem planeAnnulus_pathConnected : IsPathConnected planeAnnulus := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hsphere : IsPathConnected (Metric.sphere (0 : Plane) 1) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  have hradii : IsPathConnected (Set.Ioo (1 / 2 : ℝ) 1) :=
    (convex_Ioo (1 / 2 : ℝ) 1).isPathConnected ⟨3 / 4, by norm_num⟩
  let F : Plane × ℝ → Plane := fun p => p.2 • p.1
  have hF : Continuous F := continuous_snd.smul continuous_fst
  have hprod := hsphere.prod hradii
  have himage : F '' (Metric.sphere (0 : Plane) 1 ×ˢ
      Set.Ioo (1 / 2 : ℝ) 1) = planeAnnulus := by
    ext x
    constructor
    · rintro ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa using hu
      have hr' : 0 < r := by linarith [hr.1]
      change (1 / 2 : ℝ) < ‖r • u‖ ∧ ‖r • u‖ < 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr', hu', mul_one]
      exact hr
    · intro hx
      obtain ⟨hlo, hhi⟩ : (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 1 := hx
      have hpos : 0 < ‖x‖ := by linarith
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, ⟨hlo, hhi⟩⟩, ?_⟩
      · change dist (‖x‖⁻¹ • x) 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos)]
        exact inv_mul_cancel₀ hpos.ne'
      · change ‖x‖ • ‖x‖⁻¹ • x = x
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [← himage]
  exact hprod.image hF

/-- The overlap is path-connected because it is the image of a planar annulus. -/
theorem embedded_disk_cover_overlap_pathConnected
    {S : Type*} [TopologicalSpace S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    PathConnectedSpace ↥((f '' innerDisk)ᶜ ∩ (f '' diskInterior)) := by
  have heq : (Subtype.val : UnitDisk → Plane) ''
      (diskInterior \ innerDisk) = planeAnnulus := by
    ext x
    constructor
    · rintro ⟨u, ⟨hu, hnot⟩, rfl⟩
      change dist (u : Plane) 0 < (1 : ℝ) at hu
      have hlo : (1 / 2 : ℝ) < ‖(u : Plane)‖ := by
        by_contra hh
        apply hnot
        change dist (u : Plane) 0 ≤ (1 / 2 : ℝ)
        simpa [dist_zero_right] using le_of_not_gt hh
      exact ⟨hlo, by simpa [dist_zero_right] using hu⟩
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨x, ?_⟩, ⟨?_, ?_⟩, rfl⟩
      · change dist x 0 ≤ (1 : ℝ)
        simpa [dist_zero_right] using le_of_lt hhi
      · change dist x 0 < (1 : ℝ)
        simpa [dist_zero_right] using hhi
      · intro hinner
        change dist x 0 ≤ (1 / 2 : ℝ) at hinner
        have hh : ‖x‖ ≤ (1 / 2 : ℝ) := by
          simpa [dist_zero_right] using hinner
        exact (not_le_of_gt hlo) hh
  have hsource : IsPathConnected (diskInterior \ innerDisk) := by
    apply IsInducing.subtypeVal.isPathConnected_iff.mpr
    rw [heq]
    exact planeAnnulus_pathConnected
  have himage := hsource.image f.continuous
  rw [← embedded_disk_cover_overlap f hf] at himage
  exact isPathConnected_iff_pathConnectedSpace.mp himage

/-- The image of the closed disk is the union of its interior and sphere image. -/
theorem embedded_disk_range_partition
    {S : Type*} [TopologicalSpace S] (f : C(UnitDisk, S)) :
    Set.range f = f '' diskInterior ∪
      f '' {x : UnitDisk | (x : Plane) ∈ Metric.sphere 0 1} := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hu : dist (u : Plane) 0 ≤ (1 : ℝ) := u.2
    rcases lt_or_eq_of_le hu with hlt | heq
    · exact Or.inl ⟨u, hlt, rfl⟩
    · exact Or.inr ⟨u, heq, rfl⟩
  · rintro (⟨u, -, rfl⟩ | ⟨u, -, rfl⟩)
    · exact ⟨u, rfl⟩
    · exact ⟨u, rfl⟩

/-- On the exterior side, the disk meets a closed band neighborhood only
along the common frontier. -/
theorem exterior_disk_meets_closed_neighborhood_at_frontier
    {S : Type*} [TopologicalSpace S]
    (N : Set S) (hNclosed : IsClosed N) (c : Curve S)
    (hfront : frontier N = c.image)
    (f : C(UnitDisk, S))
    (hboundary : f '' {x : UnitDisk |
      (x : Plane) ∈ Metric.sphere 0 1} = c.image)
    (houtside : f '' diskInterior ⊆ interior Nᶜ) :
    N ∩ Set.range f = c.image := by
  ext x
  constructor
  · rintro ⟨hxN, hxrange⟩
    rw [embedded_disk_range_partition] at hxrange
    rcases hxrange with hxint | hxboundary
    · exact False.elim ((interior_subset (houtside hxint)) hxN)
    · exact hboundary ▸ hxboundary
  · intro hxc
    have hxfront : x ∈ frontier N := hfront.symm ▸ hxc
    refine ⟨hNclosed.frontier_subset hxfront, ?_⟩
    rw [embedded_disk_range_partition]
    exact Or.inr (hboundary.symm ▸ hxc)

/-- The only possible frontier points of an embedded disk image come from
its sphere boundary. -/
theorem embedded_disk_frontier_subset_boundary
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    frontier (Set.range f) ⊆
      f '' {x : UnitDisk | (x : Plane) ∈ Metric.sphere 0 1} := by
  letI : CompactSpace UnitDisk :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) 1)
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range f.continuous).isClosed
  intro x hx
  have hxrange := hclosed.frontier_subset hx
  rw [embedded_disk_range_partition] at hxrange
  rcases hxrange with hxint | hxboundary
  · have hxopen : x ∈ interior (Set.range f) :=
      (embedded_disk_interior_isOpen f hf).subset_interior_iff.mpr
        (Set.image_subset_range f diskInterior) hxint
    exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hxopen hx)
  · exact hxboundary

/-- Local two-sided filling along the common frontier forces global filling
in a connected surface. -/
theorem disk_band_fill_of_local_frontier_cover
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Plane S] [PreconnectedSpace S]
    (N : Set S) (c : Curve S) (hfront : frontier N = c.image)
    (f : C(UnitDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' {x : UnitDisk |
      (x : Plane) ∈ Metric.sphere 0 1} = c.image)
    (hlocal : c.image ⊆ interior (N ∪ Set.range f)) :
    N ∪ Set.range f = Set.univ := by
  have hfrontunion : frontier (N ∪ Set.range f) ⊆ c.image := by
    apply (frontier_union_subset N (Set.range f)).trans
    intro x hx
    rcases hx with hxN | hxD
    · exact hfront ▸ hxN.1
    · exact hboundary ▸ embedded_disk_frontier_subset_boundary f hf hxD.2
  have hempty : frontier (N ∪ Set.range f) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxinside := hlocal (hfrontunion hx)
    exact Set.disjoint_left.mp disjoint_interior_frontier hxinside hx
  rcases frontier_eq_empty_iff.mp hempty with hzero | hfull
  · have hpoint : f ⟨0, by simp⟩ ∈ N ∪ Set.range f :=
      Or.inr ⟨⟨0, by simp⟩, rfl⟩
    rw [hzero] at hpoint
    exact False.elim hpoint
  · exact hfull

end CurveComplex

#print axioms CurveComplex.bounding_disk_literal_cover
#print axioms CurveComplex.embedded_disk_cover_overlap_pathConnected
#print axioms CurveComplex.exterior_disk_meets_closed_neighborhood_at_frontier
#print axioms CurveComplex.disk_band_fill_of_local_frontier_cover
