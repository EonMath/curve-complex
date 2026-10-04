import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.GeometricTraceObligationDrafts

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
variable {M : HyperellipticModel E S}

/-- Actual simultaneous transport retains the entire crossing set. -/
theorem actual_crossings_transport (a b : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hm : ∀ z, z ∈ M.cover.branch → h z = z) :
    crossings M (a.transport h hm) (b.transport h hm) = h '' crossings M a b := by
  unfold crossings
  rw [arcInterior_transport, arcInterior_transport, Set.image_inter h.injective]

/-- A local move away from the anchor retains its crossings pointwise, not only
as a cardinality or a parity class. -/
theorem actual_crossings_transport_fixing_anchor (a b : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (ha : ∀ z, z ∈ a.val.image → h z = z) :
    crossings M a (b.transport h hm) = crossings M a b := by
  have hi : arcInterior M (a.transport h hm) = arcInterior M a := by
    change (a.val.transport h hm).image \ (M.cover.branch : Set S) = _
    rw [MarkedArc.transport_image]
    have he : h '' a.val.image = a.val.image := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [ha y hy] using hy
      · intro hz
        exact ⟨z, hz, ha z hz⟩
    rw [he]
    rfl
  have hc := actual_crossings_transport a b h hm
  unfold crossings at hc ⊢
  rw [hi] at hc
  rw [hc]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [ha y hy.1.1] using hy
  · intro hz
    exact ⟨z, hz, ha z hz.1.1⟩

/-- Setwise anchor preservation permits the actual crossing locations to move,
while preserving the exact minimum cardinality. Pointwise fixation is unnecessary. -/
theorem actual_crossings_transport_preserving_anchor_image
    (a b : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (ha : h '' a.val.image = a.val.image) :
    crossings M a (b.transport h hm) = h '' crossings M a b := by
  have hi : arcInterior M (a.transport h hm) = arcInterior M a := by
    change (a.val.transport h hm).image \ (M.cover.branch : Set S) = _
    rw [MarkedArc.transport_image, ha]
    rfl
  have hc := actual_crossings_transport a b h hm
  unfold crossings at hc ⊢
  rw [hi] at hc
  exact hc

theorem actual_crossings_ncard_transport_preserving_anchor_image
    (a b : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (ha : h '' a.val.image = a.val.image) :
    (crossings M a (b.transport h hm)).ncard = (crossings M a b).ncard := by
  rw [actual_crossings_transport_preserving_anchor_image a b h hm ha]
  exact Set.ncard_image_of_injective _ h.injective

/-- Concrete anchor-complement moves preserve the source minimum-cardinality
inequality against every representative of the named class. -/
theorem actual_minimal_transport_fixing_anchor
    (anchor a : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (ha : ∀ z, z ∈ anchor.val.image → h z = z)
    (v : EssentialArcClass M)
    (hmin : ∀ b : EssentialMarkedArc M, vertex M b = v →
      (crossings M anchor b).Finite →
      (crossings M anchor a).ncard ≤ (crossings M anchor b).ncard) :
    ∀ b : EssentialMarkedArc M, vertex M b = v →
      (crossings M anchor b).Finite →
      (crossings M anchor (a.transport h hm)).ncard ≤ (crossings M anchor b).ncard := by
  rw [actual_crossings_transport_fixing_anchor anchor a h hm ha]
  exact hmin

theorem actual_minimal_transport_preserving_anchor_image
    (anchor a : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hm : ∀ z, z ∈ M.cover.branch → h z = z)
    (ha : h '' anchor.val.image = anchor.val.image)
    (v : EssentialArcClass M)
    (hmin : ∀ b : EssentialMarkedArc M, vertex M b = v →
      (crossings M anchor b).Finite →
      (crossings M anchor a).ncard ≤ (crossings M anchor b).ncard) :
    ∀ b : EssentialMarkedArc M, vertex M b = v →
      (crossings M anchor b).Finite →
      (crossings M anchor (a.transport h hm)).ncard ≤ (crossings M anchor b).ncard := by
  rw [actual_crossings_ncard_transport_preserving_anchor_image anchor a h hm ha]
  exact hmin

end CurveComplex.HyperellipticModel.ArcSurgery
