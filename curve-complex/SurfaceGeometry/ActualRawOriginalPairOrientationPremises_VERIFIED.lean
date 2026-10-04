import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedArcReverse
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
namespace CurveComplex.HyperellipticModel
open Set Topology ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
private def actualDiskWithSamePhysicalTraces
    (M : HyperellipticModel E S) (a b a' b' : EssentialMarkedArc M)
    (ha : a'.val.image=a.val.image) (hb : b'.val.image=b.val.image)
    (D : ActualMarkedTwoSideDisk M a' b') : ActualMarkedTwoSideDisk M a b where
  firstCorner := D.firstCorner
  secondCorner := D.secondCorner
  firstSide := D.firstSide
  secondSide := D.secondSide
  first_embedded := D.first_embedded
  second_embedded := D.second_embedded
  first_zero := D.first_zero
  first_one := D.first_one
  second_zero := D.second_zero
  second_one := D.second_one
  first_on_curve := ha ▸ D.first_on_curve
  second_on_curve := hb ▸ D.second_on_curve
  sides_inter := D.sides_inter
  disk := D.disk
  disk_embedded := D.disk_embedded
  boundary_eq := D.boundary_eq
  marks_are_corners := D.marks_are_corners
private theorem actualEmptyOriginalDiskPhysicalTraceTransfer
    (M : HyperellipticModel E S) (a b a' b' : EssentialMarkedArc M)
    (ha : a'.val.image=a.val.image) (hb : b'.val.image=b.val.image)
    (D : ActualMarkedTwoSideDisk M a' b')
    (hclear : Disjoint D.openInterior (a'.val.image ∪ b'.val.image))
    (hpositive : D.firstCorner∈crossings M a' b' ∨ D.secondCorner∈crossings M a' b') :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      B.disk=D.disk ∧ B.firstSide=D.firstSide ∧ B.secondSide=D.secondSide ∧
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner∈crossings M a b ∨ B.secondCorner∈crossings M a b) := by
  refine ⟨actualDiskWithSamePhysicalTraces M a b a' b' ha hb D,rfl,rfl,rfl,?_,?_⟩
  · simpa only [actualDiskWithSamePhysicalTraces,ActualMarkedTwoSideDisk.openInterior,ha,hb] using hclear
  · simpa only [actualDiskWithSamePhysicalTraces,crossings,arcInterior,ha,hb] using hpositive
private def actualDiskWithSwappedOriginalSides
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (D : ActualMarkedTwoSideDisk M b a) : ActualMarkedTwoSideDisk M a b where
  firstCorner := D.firstCorner
  secondCorner := D.secondCorner
  firstSide := D.secondSide
  secondSide := D.firstSide
  first_embedded := D.second_embedded
  second_embedded := D.first_embedded
  first_zero := D.second_zero
  first_one := D.second_one
  second_zero := D.first_zero
  second_one := D.first_one
  first_on_curve := D.second_on_curve
  second_on_curve := D.first_on_curve
  sides_inter := by rw [inter_comm]; exact D.sides_inter
  disk := D.disk
  disk_embedded := D.disk_embedded
  boundary_eq := by rw [union_comm]; exact D.boundary_eq
  marks_are_corners := D.marks_are_corners
private theorem actualEmptyOriginalDiskSwap
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (D : ActualMarkedTwoSideDisk M b a)
    (hclear : Disjoint D.openInterior (b.val.image ∪ a.val.image))
    (hpositive : D.firstCorner∈crossings M b a ∨ D.secondCorner∈crossings M b a) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      B.disk=D.disk ∧ B.firstSide=D.secondSide ∧ B.secondSide=D.firstSide ∧
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner∈crossings M a b ∨ B.secondCorner∈crossings M a b) := by
  refine ⟨actualDiskWithSwappedOriginalSides M a b D,rfl,rfl,rfl,?_,?_⟩
  · simpa only [actualDiskWithSwappedOriginalSides,ActualMarkedTwoSideDisk.openInterior,union_comm] using hclear
  · simpa only [actualDiskWithSwappedOriginalSides,crossings,inter_comm] using hpositive
private theorem actualReverseOriginalPairTraceData
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) :
    vertex M b.reverse=vertex M b ∧
    crossings M a b.reverse=crossings M a b ∧
    (∀ p,CrossesInDisk M a b.reverse p ↔ CrossesInDisk M a b p) := by
  refine ⟨b.reverse_class,?_,?_⟩
  · simp only [crossings,arcInterior,b.reverse_image]
  · intro p
    simp only [CrossesInDisk,b.reverse_image]

noncomputable local instance (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
private theorem actualRawOriginalPairReversalPremises
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : vertex M a≠vertex M b)
    (hc : IsArcSimplex M {vertex M a,vertex M b})
    (hf : (crossings M a b).Finite)
    (ht : ∀ p∈crossings M a b,CrossesInDisk M a b p)
    (hp : (crossings M a b).Nonempty) :
    vertex M a≠vertex M b.reverse ∧ IsArcSimplex M {vertex M a,vertex M b.reverse} ∧
    (crossings M a b.reverse).Finite ∧
    (∀ p∈crossings M a b.reverse,CrossesInDisk M a b.reverse p) ∧
    (crossings M a b.reverse).Nonempty := by
  obtain ⟨hv,hcross,hlocal⟩ := actualReverseOriginalPairTraceData M a b
  refine ⟨by simpa only [hv] using hne,by simpa only [hv] using hc,
    hcross.symm ▸ hf,?_,hcross.symm ▸ hp⟩
  intro p h
  exact (hlocal p).mpr (ht p (hcross ▸ h))
private theorem actualRawOriginalPairSwappedPremises
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : vertex M a≠vertex M b)
    (hc : IsArcSimplex M {vertex M a,vertex M b})
    (hf : (crossings M a b).Finite)
    (ht : ∀ p∈crossings M a b,CrossesInDisk M a b p)
    (hp : (crossings M a b).Nonempty) :
    vertex M b≠vertex M a ∧ IsArcSimplex M {vertex M b,vertex M a} ∧
    (crossings M b a).Finite ∧
    (∀ p∈crossings M b a,CrossesInDisk M b a p) ∧
    (crossings M b a).Nonempty := by
  have he : crossings M b a=crossings M a b := by simp only [crossings,inter_comm]
  refine ⟨hne.symm,?_,he.symm ▸ hf,?_,he.symm ▸ hp⟩
  · simpa only [Finset.pair_comm] using hc
  · intro p h
    exact actual_marked_crossesInDisk_symm M a b p (ht p (he ▸ h))
end CurveComplex.HyperellipticModel
