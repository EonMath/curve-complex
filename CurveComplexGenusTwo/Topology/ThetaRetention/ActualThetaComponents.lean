import CurveComplexGenusTwo.Topology.ThetaRetention.ActualInternalSurfaceSides
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches

namespace CurveComplex
open Set Topology Schoenflies

theorem source_first_return_open_arc_image
    {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : SourceFirstReturnBoundary a b) :
    b.imageᶜ ∩ Set.range D.first = D.first '' Ioo (0 : Interval) 1 := by
  ext x
  constructor
  · rintro ⟨hn,⟨t,rfl⟩⟩
    have h0 : t ≠ 0 := by intro he; exact hn (he ▸ D.first_zero.symm ▸ D.start_mem.2)
    have h1 : t ≠ 1 := by intro he; exact hn (he ▸ D.first_one.symm ▸ D.finish_mem.2)
    exact ⟨t,⟨lt_of_le_of_ne t.property.1 h0.symm,lt_of_le_of_ne t.property.2 h1⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨D.first_interior_avoids t (ne_of_gt ht.1) (ne_of_lt ht.2),Set.mem_range_self t⟩

/-- Actual component exhaustion for the theta complement on the source
surface. All local neighborhoods are produced; no collar is a premise. -/
theorem source_theta_complement_at_most_two
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b) (hns : Nonseparating b) :
    ∃ l ∈ b.imageᶜ \ Set.range D.first, ∃ r ∈ b.imageᶜ \ Set.range D.first,
      ∀ x ∈ b.imageᶜ \ Set.range D.first,
        x ∈ connectedComponentIn (b.imageᶜ \ Set.range D.first) l ∨
        x ∈ connectedComponentIn (b.imageᶜ \ Set.range D.first) r := by
  letI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
  have hDopen : IsOpen b.imageᶜ := (isCompact_range b.embedded.continuous).isClosed.isOpen_compl
  have hPclosed : IsClosed (Set.range D.first) := (isCompact_range D.first.continuous).isClosed
  have hK : IsConnected (b.imageᶜ ∩ Set.range D.first) := by
    rw [source_first_return_open_arc_image D]
    exact (isConnected_Ioo (show (0 : Interval) < 1 from zero_lt_one)).image D.first D.first.continuous.continuousOn
  apply theta_at_most_two_of_local_sides hDopen hns.isPreconnected hPclosed hK
  rintro x ⟨hn,⟨t,rfl⟩⟩
  have h0 : t ≠ 0 := by intro he; exact hn (he ▸ D.first_zero.symm ▸ D.start_mem.2)
  have h1 : t ≠ 1 := by intro he; exact hn (he ▸ D.first_one.symm ▸ D.finish_mem.2)
  let p : Path (D.first 0) (D.first 1) := ⟨D.first,rfl,rfl⟩
  exact source_embedded_path_internal_local_sides p D.first_embedded t
    (lt_of_le_of_ne t.property.1 h0.symm) (lt_of_le_of_ne t.property.2 h1)
    b.imageᶜ hDopen hn

end CurveComplex
#print axioms CurveComplex.source_theta_complement_at_most_two
