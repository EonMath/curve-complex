import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualTwoMarkDiskPathHomotopy
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedArcReverse

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- The actual unordered endpoint set determines the necessary orientation;
contractibility supplies actual punctured path homotopy without an arc class. -/
theorem actual_two_mark_disk_unoriented_arc_path_homotopy
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1}) :
    ∃ hu : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ hv : a.val.map 1 ∈ ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ,
    ∃ α β : Path (⟨a.val.map 0,hu⟩ : ↑((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ)
      ⟨a.val.map 1,hv⟩,
      (∀ t : Interval, (α t : S) = a.val.map t) ∧
      ((∀ t : Interval, (β t : S) = b.val.map t) ∨
        (∀ t : Interval, (β t : S) = b.val.map (unitInterval.symm t))) ∧ α.Homotopic β := by
  classical
  rcases Set.pair_eq_pair_iff.mp hends with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ :=
      M.actual_two_mark_disk_oriented_arc_path_homotopy a b N hb h0.symm h1.symm
    exact ⟨hu,hv,α,β,hα,Or.inl hβ,hhom⟩
  · let br : NonLoopArc M := ⟨b.val.reverse,by
      simpa [MarkedArc.reverse,Function.comp_def] using b.property.symm⟩
    have hbrimage : br.image = b.image := b.val.reverse_image
    have hbr0 : br.val.map 0 = a.val.map 0 := by
      simpa [br,MarkedArc.reverse,Function.comp_def] using h0.symm
    have hbr1 : br.val.map 1 = a.val.map 1 := by
      simpa [br,MarkedArc.reverse,Function.comp_def] using h1.symm
    obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ := M.actual_two_mark_disk_oriented_arc_path_homotopy
      a br N (hbrimage ▸ hb) hbr0 hbr1
    exact ⟨hu,hv,α,β,hα,Or.inr hβ,hhom⟩
end CurveComplex.HyperellipticModel
