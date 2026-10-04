import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopBoundarySafeMoviePreparation
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_finite_closed_cell_gluing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {I : Type} [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i) (f : I → C(X,Y))
    (hagree : ∀ i j x, x ∈ C i → x ∈ C j → f i x = f j x) :
    ∃ G : C(X,Y), ∀ i x, x ∈ C i → G x = f i x := by
  classical
  choose index hindex using hcover
  let G : X → Y := fun x => f (index x) x
  have hG (i : I) (x : X) (hx : x ∈ C i) : G x = f i x :=
    hagree (index x) i x (hindex x) hx
  have hGc : Continuous G := continuous_iff_isClosed.mpr (by
    intro D hD
    have heq : G ⁻¹' D = ⋃ i, C i ∩ (f i) ⁻¹' D := by
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.mpr ⟨index x,hindex x,hx⟩
      · intro hx
        obtain ⟨i,hxi,hfix⟩ := Set.mem_iUnion.mp hx
        change G x ∈ D
        rw [hG i x hxi]
        exact hfix
    rw [heq]
    exact isClosed_iUnion_of_finite (fun i => (hC i).inter (hD.preimage (f i).continuous)))
  exact ⟨⟨G,hGc⟩,hG⟩
end CurveComplex.HyperellipticModel
