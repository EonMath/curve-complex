import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualFirstReturnPortCornerSquares
namespace CurveComplex
open Set Topology Schoenflies Metric
/-- Select an ACTUAL non-endpoint center port in any positive longitudinal
window and any positive chart ball. Existence follows from the real embedded
source arc; no small-port certificate is supplied. -/
theorem source_embedded_arc_endpoint_small_port
    {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (E : OpenPartialHomeomorph S Plane) (hpE : f 0 ∈ E.source) (hp0 : E (f 0)=0)
    (η r : ℝ) (hη : 0<η) (hr : 0<r) :
    ∃ u : Interval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧ (u:ℝ)<η ∧
      f u ∈ E.source ∧ ‖E (f u)‖<r ∧ E (f u)≠0 := by
  let W : Set S := E.source ∩ E ⁻¹' ball (0:Plane) r
  have hW : IsOpen W := E.isOpen_inter_preimage isOpen_ball
  have hpW : f 0 ∈ W := by
    refine ⟨hpE,?_⟩
    change dist (E (f 0)) 0<r
    rw [hp0,dist_self]
    exact hr
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hW.preimage f.continuous)
    (0:Interval) hpW
  let t : ℝ := min (δ/2) (min (η/2) (1/2))
  have ht : 0<t := lt_min (half_pos hδ) (lt_min (half_pos hη) (by norm_num))
  have htδ : t<δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htη : t<η := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have ht1 : t<1 := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  let u : Interval := ⟨t,ht.le,ht1.le⟩
  have huW : f u ∈ W := by
    apply hball
    change dist u (0:Interval)<δ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |t-0|<δ
    simpa only [sub_zero,abs_of_pos ht] using htδ
  refine ⟨u,ht,ht1,htη,huW.1,?_,?_⟩
  · simpa only [mem_preimage,mem_ball,dist_zero_right] using huW.2
  · intro he
    have hfu : f u=f 0 := E.injOn huW.1 hpE (he.trans hp0.symm)
    have hu0 : u=0 := hf.injective hfu
    have hz := congrArg (fun z : Interval => (z:ℝ)) hu0
    change t=0 at hz
    linarith
end CurveComplex
#print axioms CurveComplex.source_embedded_arc_endpoint_small_port
