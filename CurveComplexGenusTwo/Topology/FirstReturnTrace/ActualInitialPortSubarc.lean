import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualEndpointPortSelection
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Select an actual small port together with its ENTIRE preceding source
subarc in the same chart ball. This supplies the genuine ordered prefix used
by middle-crosscut attachment after the corner translation. -/
theorem source_embedded_arc_initial_small_port
    {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (E : OpenPartialHomeomorph S Plane) (hpE : f 0 ∈ E.source) (hp0 : E (f 0)=0)
    (η r : ℝ) (hη : 0<η) (hr : 0<r) :
    ∃ u : Interval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧ (u:ℝ)<η ∧ E (f u)≠0 ∧
      ∀ t : Interval, t≤u → f t ∈ E.source ∧ ‖E (f t)‖<r := by
  let W : Set S := E.source ∩ E ⁻¹' ball (0:Plane) r
  have hW : IsOpen W := E.isOpen_inter_preimage isOpen_ball
  have hpW : f 0 ∈ W := by
    refine ⟨hpE,?_⟩
    change dist (E (f 0)) 0<r
    rw [hp0,dist_self]
    exact hr
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hW.preimage f.continuous)
    (0:Interval) hpW
  obtain ⟨u,hu0,hu1,huη,huE,hunorm,hune⟩ :=
    source_embedded_arc_endpoint_small_port f hf E hpE hp0 (min η (δ/2)) r
      (lt_min hη (half_pos hδ)) hr
  have huδ : (u:ℝ)<δ := (huη.trans_le (min_le_right _ _)).trans (by linarith)
  refine ⟨u,hu0,hu1,huη.trans_le (min_le_left _ _),hune,?_⟩
  intro t ht
  have htδ : (t:ℝ)<δ := lt_of_le_of_lt ht huδ
  have htW : f t ∈ W := hball (by
    rw [mem_ball,Subtype.dist_eq,Real.dist_eq]
    change |(t:ℝ)-0|<δ
    simpa only [sub_zero,abs_of_nonneg t.property.1] using htδ)
  exact ⟨htW.1,by simpa only [mem_preimage,mem_ball,dist_zero_right] using htW.2⟩
end CurveComplex
#print axioms CurveComplex.source_embedded_arc_initial_small_port
