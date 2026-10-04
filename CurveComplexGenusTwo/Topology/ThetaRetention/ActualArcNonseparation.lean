import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSurfaceEndpointCap
import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceOneTrackPropagation

namespace CurveComplex
open Set Topology Schoenflies

/-- A compact embedded interval cannot separate a connected surface. Internal
local bands and genuine one-track endpoint caps are all produced here; no
connectivity or homology detection certificate is a premise. -/
theorem source_embedded_path_complement_connected
    {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace Plane S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p) :
    IsConnected (Set.range p)ᶜ := by
  let : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
  have hP : IsClosed (Set.range p) := (isCompact_range p.continuous).isClosed
  have hK : IsConnected ((Set.univ : Set S) ∩ Set.range p) := by
    rw [Set.univ_inter]
    exact isConnected_range p.continuous
  obtain ⟨C0,hC0,hOne⟩ := source_embedded_path_zero_endpoint_cap p hp Set.univ isOpen_univ (Set.mem_univ _)
  have hlocal : ∀ z ∈ (Set.univ : Set S) ∩ Set.range p,
      ∃ C : SurfaceLocalSides Set.univ (Set.range p), z ∈ C.nbhd := by
    rintro z ⟨_,⟨t,rfl⟩⟩
    by_cases h0 : t = 0
    · exact ⟨C0,h0 ▸ hC0⟩
    by_cases h1 : t = 1
    · have hex := source_embedded_path_zero_endpoint_cap p.symm
        (hp.comp unitInterval.symmHomeomorph.isEmbedding)
        Set.univ isOpen_univ (Set.mem_univ _)
      have heq : Set.range p.symm = Set.range p := Path.symm_range p
      rw [heq] at hex
      have hzero : p.symm 0 = p 1 := by
        change p (unitInterval.symm 0) = p 1
        rw [unitInterval.symm_zero]
      rw [hzero] at hex
      obtain ⟨C,hC,hOne⟩ := hex
      exact ⟨C,h1 ▸ hC⟩
    · exact source_embedded_path_internal_local_sides p hp t
        (lt_of_le_of_ne t.property.1 (Ne.symm h0)) (lt_of_le_of_ne t.property.2 h1)
        Set.univ isOpen_univ (Set.mem_univ _)
  have hc := theta_connected_complement_of_one_track_start isOpen_univ isPreconnected_univ hP hK hlocal
    C0 (p 0) ⟨Set.mem_univ _,Set.mem_range_self 0⟩ hC0 hOne
  simpa only [Set.compl_eq_univ_sdiff] using hc

end CurveComplex
#print axioms CurveComplex.source_embedded_path_complement_connected
