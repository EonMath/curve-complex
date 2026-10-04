import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripCellContactRedraw
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual finite closed-cell movies glue jointly in time when their literal
values agree on overlaps. This constructs the global movie, not just slices. -/
theorem actual_cell_movie_finite_gluing
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {I : Type} [Finite I] (cell : I → Set X) (hclosed : ∀ i,IsClosed (cell i))
    (hcover : ∀ x,∃ i,x ∈ cell i)
    (movie : I → C(X × Interval,Y))
    (hagree : ∀ i j x,x ∈ cell i → x ∈ cell j → ∀ σ,movie i (x,σ)=movie j (x,σ)) :
    ∃ R : C(X × Interval,Y),∀ i x,x ∈ cell i → ∀ σ,R (x,σ)=movie i (x,σ) := by
  let domains : I → Set (X × Interval) := fun i => Prod.fst ⁻¹' cell i
  have hdomains (i) : IsClosed (domains i) := (hclosed i).preimage continuous_fst
  have hdomainsCover (z : X × Interval) : ∃ i,z ∈ domains i := hcover z.1
  obtain ⟨R,hR⟩ := actual_finite_closed_cell_gluing domains hdomains hdomainsCover movie
    (fun i j z hi hj => hagree i j z.1 hi hj z.2)
  exact ⟨R,fun i x hx σ => hR i (x,σ) hx⟩
end CurveComplex.HyperellipticModel
