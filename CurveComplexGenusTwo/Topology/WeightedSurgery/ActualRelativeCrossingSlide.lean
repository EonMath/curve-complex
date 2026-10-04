import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePlane
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkedCrossingTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.AmbientIsotopyPrefixHeaders

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Explicit crossing-slide producer in an actual marked-point-free chart.
The horizontal anchor trace is preserved setwise at EVERY time. -/
theorem actual_relative_crossing_slide (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (hU : IsOpen U) (e : U ≃ₜ V)
    (hCV : Plane.closedSquare 0 1 ⊆ V)
    (hm : Disjoint U (M.cover.branch : Set S))
    (haxis : ∀ p : U, p.val ∈ anchor.val.image ↔ (e p).val 1 = 0)
    (a : Amount) :
    ∃ K : AmbientIsotopy U, ∃ G : AmbientIsotopy S,
      (∀ t p, p ∈ M.cover.branch → G.map (t,p) = p) ∧
      (∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image) ∧
      (∀ t p, p ∉ U → G.map (t,p) = p) ∧
      (∀ t (p : U), G.map (t,p.val) = (K.map (t,p)).val) ∧
      (∀ t (p : U), (e (K.map (t,p))).val = (planeIsotopy a).map (t,(e p).val)) := by
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨K,G,hcoord,hGU,hout⟩ := position_surface_chart_lift S U V hU e
    (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV (planeIsotopy a)
    (planeIsotopy_fixed a)
  have hmarks : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p := by
    intro t p hp
    apply hout
    intro hpU
    exact Set.disjoint_left.mp hm hpU hp
  have hmem (t : Interval) (p : S) :
      G.map (t,p) ∈ anchor.val.image ↔ p ∈ anchor.val.image := by
    by_cases hp : p ∈ U
    · let q : U := ⟨p,hp⟩
      rw [hGU t q]
      rw [haxis (K.map (t,q)), haxis q, hcoord]
      rw [planeIsotopy_preserves_second]
    · rw [hout t p hp]
  have himage (t : Interval) :
      (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact (hmem t q).mpr hq
    · intro hp
      obtain ⟨g,hg⟩ := G.homeomorphism_at t
      refine ⟨g.symm p, ?_, ?_⟩
      · apply (hmem t (g.symm p)).mp
        rw [← hg, g.apply_symm_apply]
        exact hp
      · change G.map (t,g.symm p) = p
        rw [← hg, g.apply_symm_apply]
  exact ⟨K,G,hmarks,himage,hout,hGU,hcoord⟩

/-- The produced move genuinely relocates the central crossing along the
stationary anchor, with explicit coordinate t*a. -/
theorem actual_relative_crossing_slide_moves_origin (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (hU : IsOpen U) (e : U ≃ₜ V)
    (hCV : Plane.closedSquare 0 1 ⊆ V)
    (hm : Disjoint U (M.cover.branch : Set S))
    (haxis : ∀ p : U, p.val ∈ anchor.val.image ↔ (e p).val 1 = 0)
    (a : Amount) (p : U) (hp : planeCoordinates (e p).val = (0,0)) :
    ∃ K : AmbientIsotopy U, ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image) ∧
      (∀ t, G.map (t,p.val) = (K.map (t,p)).val) ∧
      ∀ t, planeCoordinates (e (K.map (t,p))).val = (t.val*a.val,0) := by
  obtain ⟨K,G,hmarks,hanchor,_,hGU,hcoord⟩ :=
    actual_relative_crossing_slide M anchor U V hU e hCV hm haxis a
  refine ⟨K,G,hmarks,hanchor,fun t => hGU t p,?_⟩
  intro t
  rw [hcoord, planeIsotopy_coordinate, hp, productIsotopy_moves_crossing]

end
end CurveComplex.HyperellipticModel.ArcSurgery
