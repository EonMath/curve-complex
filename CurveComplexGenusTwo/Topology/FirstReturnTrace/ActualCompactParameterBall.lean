import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAxisSegmentSourcePrefix
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Uniform actual parameter-radius selection for a compact continuous family. -/
theorem source_compact_plane_parameter_uniform_open_ball
    (K : Type) [TopologicalSpace K] [CompactSpace K]
    (f : C(K × Plane,Plane)) (U : Set Plane) (hU : IsOpen U)
    (hzero : ∀ k, f (k,0) ∈ U) :
    ∃ r : ℝ, 0<r ∧ ∀ k v, ‖v‖<r → f (k,v) ∈ U := by
  obtain ⟨V,W,hV,hW,hall,h0,hVW⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (Set.univ : Set K)) (isCompact_singleton (x := (0:Plane)))
    (hU.preimage f.continuous) (by
      rintro ⟨k,v⟩ ⟨_hk,hv⟩
      have hv0 : v=0 := hv
      subst v
      exact hzero k)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW 0 (h0 (Set.mem_singleton 0))
  refine ⟨r,hr,?_⟩
  intro k v hv
  exact hVW ⟨hall (Set.mem_univ k),hball (by simpa only [mem_ball,dist_zero_right] using hv)⟩
end CurveComplex
#print axioms CurveComplex.source_compact_plane_parameter_uniform_open_ball
