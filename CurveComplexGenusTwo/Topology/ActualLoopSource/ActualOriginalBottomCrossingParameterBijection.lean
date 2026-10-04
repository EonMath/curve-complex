import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopPreparedMovieBoundary
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Literal bottom parameters biject onto the ORIGINAL mutual crossings.
The capture and source avoidance clauses are those of the actual preparation;
no graph, parity or chosen disk is supplied. -/
theorem actual_original_bottom_crossing_parameter_bijection
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (φ : C(Interval,Interval))
    (hcapture : ∀ t,b.val.map t ∈ crossings M a b → ∃ s,φ s=t)
    (G : C(Interval × Interval,S))
    (hbottom : ∀ t,G (0,t)=b.val.map (φ t))
    (hbottomEmbed : IsEmbedding (fun t => G (0,t)))
    (hmarks : ∀ z,G z ∉ (M.cover.branch : Set S)) :
    Set.BijOn (fun t : Interval => G (0,t))
      {t : Interval | G (0,t) ∈ a.val.image} (crossings M a b) := by
  refine ⟨?_,hbottomEmbed.injective.injOn,?_⟩
  · intro t ht
    refine ⟨⟨ht,hmarks (0,t)⟩,?_,hmarks (0,t)⟩
    change G (0,t) ∈ b.val.image
    rw [hbottom]
    exact mem_range_self (φ t)
  · intro x hx
    obtain ⟨t,ht⟩ := hx.2.1
    have hcross : b.val.map t ∈ crossings M a b := ht.symm ▸ hx
    obtain ⟨s,hs⟩ := hcapture t hcross
    have he : G (0,s)=x := by rw [hbottom,hs,ht]
    refine ⟨s,?_,he⟩
    change G (0,s) ∈ a.val.image
    rw [he]
    exact hx.1.1

/-- Exact finite count transfer to ORIGINAL crossings, retaining corner
parameters when present. -/
theorem actual_original_bottom_crossing_parameter_ncard
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (φ : C(Interval,Interval))
    (hcapture : ∀ t,b.val.map t ∈ crossings M a b → ∃ s,φ s=t)
    (G : C(Interval × Interval,S))
    (hbottom : ∀ t,G (0,t)=b.val.map (φ t))
    (hbottomEmbed : IsEmbedding (fun t => G (0,t)))
    (hmarks : ∀ z,G z ∉ (M.cover.branch : Set S)) :
    {t : Interval | G (0,t) ∈ a.val.image}.ncard=(crossings M a b).ncard := by
  exact (actual_original_bottom_crossing_parameter_bijection M a b φ hcapture
    G hbottom hbottomEmbed hmarks).ncard_eq
end CurveComplex.HyperellipticModel
