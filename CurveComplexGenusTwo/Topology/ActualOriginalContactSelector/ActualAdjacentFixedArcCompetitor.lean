import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source adjacency produces a same-class competitor disjoint from the
specified ACTUAL first arc. Both representatives in the adjacency witness
are transported by the actual marked isotopy, so the first arc is fixed
as an image without assuming an additional disjointness certificate. -/
theorem actual_adjacent_fixed_arc_disjoint_competitor
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hadj : ArcAdjacent M (Quotient.mk (essentialArcSetoid M) a)
      (Quotient.mk (essentialArcSetoid M) b)) :
    ∃ c : EssentialMarkedArc M,
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      Disjoint (arcInterior M a) (arcInterior M c) := by
  obtain ⟨_,_,_,_,α,β,hα,hβ,hd⟩ := hadj
  obtain ⟨H,hmarks,himage⟩ := Quotient.exact hα
  obtain ⟨g,hg⟩ := H.homeomorphism_at 1
  have hfix : ∀ p,p ∈ M.cover.branch → g p = p := fun p hp =>
    (hg p).trans (hmarks 1 p hp)
  let c := β.transport g hfix
  have hc : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) β := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    change H.finalMap '' β.val.image = (β.val.transport g hfix).image
    rw [MarkedArc.transport_image]
    congr 1
    exact funext (fun p => (hg p).symm)
  have hαimage : (α.transport g hfix).val.image = a.val.image := by
    change (α.val.transport g hfix).image = a.val.image
    rw [MarkedArc.transport_image]
    change g '' α.val.image = a.val.image
    have hmap : g = H.finalMap := funext hg
    rw [hmap]
    exact himage
  have hαinterior : arcInterior M (α.transport g hfix) = arcInterior M a := by
    change (α.transport g hfix).val.image \ (M.cover.branch : Set S) = _
    rw [hαimage]
    rfl
  have hd' := arcInterior_transport_disjoint α β g hfix hd
  rw [hαinterior] at hd'
  exact ⟨c,hc.trans hβ,hd'⟩

end CurveComplex.HyperellipticModel
