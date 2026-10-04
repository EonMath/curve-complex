import CurveComplexGenusTwo.Topology.CapBandGeometry.BandInteriorConnected

noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry

theorem actual_band_internal_disk_eq
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    {c : Curve S} (hfront : frontier (bandUnion D B) = c.image)
    (f : C(CapDisk,S)) (hf : IsEmbedding f) (hboundary : f '' capBoundary = c.image)
    (hinside : f '' capInterior ⊆ interior (bandUnion D B)) :
    bandUnion D B = Set.range f := by
  let N := bandUnion D B
  let C := f '' capInterior
  have hfclosed : IsClosed (Set.range f) := (isCompact_range f.continuous).isClosed
  have hcover : interior N ⊆ C ∪ (Set.range f)ᶜ := by
    intro x hx
    by_cases hxf : x ∈ Set.range f
    · rw [embedded_disk_range_partition] at hxf
      rcases hxf with hxi | hxb
      · exact Or.inl hxi
      · have hxc : x ∈ frontier N := hfront.symm ▸ (hboundary ▸ hxb)
        exact False.elim (hxc.2 hx)
    · exact Or.inr hxf
  have hd : Disjoint C (Set.range f)ᶜ :=
    Set.disjoint_left.mpr (fun _ hx hn => hn (Set.image_subset_range _ _ hx))
  have hside := (actual_band_interior_preconnected D B).subset_or_subset
    (embedded_disk_interior_isOpen f hf) hfclosed.isOpen_compl hd hcover
  have hint : interior N ⊆ C := by
    rcases hside with hi | ho
    · exact hi
    · have hz : f ⟨0,by simp⟩ ∈ C := ⟨⟨0,by simp⟩,by simp [capInterior],rfl⟩
      exact False.elim (ho (hinside hz) (Set.mem_range_self _))
  have hNsub : N ⊆ Set.range f := by
    have hreg : closure (interior N) = N := compatibleOutsideBands_regular_closed D B
    rw [← hreg]
    exact closure_minimal (hint.trans (Set.image_subset_range _ _)) hfclosed
  have hfsub : Set.range f ⊆ N := by
    rw [embedded_disk_range_partition]
    apply Set.union_subset
    · exact hinside.trans interior_subset
    · intro x hx
      exact (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed.frontier_subset
        (hfront.symm ▸ (hboundary ▸ hx))
  exact subset_antisymm hNsub hfsub

theorem actual_band_internal_disk_false
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    {c : Curve S} (hfront : frontier (bandUnion D B) = c.image)
    (f : C(CapDisk,S)) (hf : IsEmbedding f) (hboundary : f '' capBoundary = c.image)
    (hinside : f '' capInterior ⊆ interior (bandUnion D B)) : False := by
  have heq := actual_band_internal_disk_eq D B hfront f hf hboundary hinside
  letI : ContractibleSpace CapDisk := (convex_closedBall (0:CapPlane) 1).contractibleSpace
    ⟨0,by simp⟩
  let e : bandUnion D B ≃ₜ CapDisk := (Homeomorph.setCongr heq).trans hf.toHomeomorph.symm
  letI : ContractibleSpace (bandUnion D B) := e.contractibleSpace
  have hz := contractible_positive_homology (bandUnion D B) 1 (by omega)
  letI := ModuleCat.subsingleton_of_isZero hz
  let h := actual_band_HOne_coordinates D B
  have he : (0 : Fin 2 → ℤ) = (fun _ => 1) := h.symm.injective (Subsingleton.elim _ _)
  have h01 := congrFun he 0
  norm_num at h01

#print axioms actual_band_internal_disk_false
end CurveComplex.CapBandGeometry
