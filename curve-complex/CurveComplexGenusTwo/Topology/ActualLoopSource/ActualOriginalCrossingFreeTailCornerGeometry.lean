import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOriginalBottomCrossingParameterBijection
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual crossing-free ORIGINAL tail bounds clear the two corners of the
literal source affine window. These are source-tail clauses, not corner-degree
or contact-family assumptions, and are used only for a PRODUCED window. -/
theorem actual_original_crossing_free_tail_corner_geometry
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ε r₀ r₁ : ℝ)
    (htails : ∀ t : Interval,(t:ℝ)≤ε ∨ 1-ε≤(t:ℝ) →
      b.val.map t ∉ crossings M a b)
    (hleft : r₀≤ε) (hright : 1-ε≤r₁)
    (φ : C(Interval,Interval))
    (hφ : ∀ t,(φ t:ℝ)=r₀+(r₁-r₀)*(t:ℝ))
    (G : C(Interval × Interval,S))
    (hbottom : ∀ t,G (0,t)=b.val.map (φ t))
    (hmarks : ∀ z,G z ∉ (M.cover.branch : Set S)) :
    G (0,0) ∉ a.val.image ∧ G (0,1) ∉ a.val.image := by
  have hcross (t : Interval) (hcontact : G (0,t) ∈ a.val.image) :
      b.val.map (φ t) ∈ crossings M a b := by
    have hm : b.val.map (φ t) ∉ (M.cover.branch : Set S) := hbottom t ▸ hmarks (0,t)
    refine ⟨⟨hbottom t ▸ hcontact,hm⟩,mem_range_self (φ t),hm⟩
  constructor
  · intro h
    apply htails (φ 0) (Or.inl ?_) (hcross 0 h)
    have he : (φ 0:ℝ)=r₀ := by rw [hφ]; norm_num
    rw [he]
    exact hleft
  · intro h
    apply htails (φ 1) (Or.inr ?_) (hcross 1 h)
    have he : (φ 1:ℝ)=r₁ := by rw [hφ]; norm_num
    rw [he]
    exact hright
end CurveComplex.HyperellipticModel
