import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualLocalizedContactClearance

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Actual minimum data PRODUCE a localized slide moving just the chosen
anchor contact and fixing every other original contact of the entire family.
The radius is derived from the finite original contacts, not supplied. -/
theorem actual_single_contact_slide
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (v : {v // v ∈ F}) (p : S) (hp : p ∈ crossings M anchor (P.rep v))
    (a : Amount) :
    ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image) ∧
      (∀ w q, q ∈ crossings M anchor (P.rep w) → q ≠ p →
        ∀ t, G.map (t,q) = q) ∧
      (a.val ≠ 0 → G.map (1,p) ≠ p) := by
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨U,V,hU,e,hCV,hm,haxis,hpU,hp0⟩ :=
    actual_crossing_disk_slide_chart M anchor (P.rep v) p (P.transverse v p hp)
  have hpPlane : (e ⟨p,hpU⟩).val = 0 := planeCoordinates.injective hp0
  obtain ⟨ε,hε,hε1,hmargin⟩ := actual_position_contact_coordinate_margin M anchor F P
    U V e haxis ⟨p,hpU⟩ hpPlane
  let H := scaledPlaneSlide ε hε a
  obtain ⟨K,G,hcoord,hGU,hout⟩ := position_surface_chart_lift S U V hU e
    (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV H
    (scaledPlaneSlide_fixed_outside_unit ε hε hε1.le a)
  have hmarks : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z := by
    intro t z hz
    exact hout t z (fun hzU => Set.disjoint_left.mp hm hzU hz)
  have hmem (t : Interval) (z : S) : G.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image := by
    by_cases hz : z ∈ U
    · rw [hGU t ⟨z,hz⟩,haxis (K.map (t,⟨z,hz⟩))]
      change _ ↔ (⟨z,hz⟩ : U).val ∈ anchor.val.image
      rw [haxis ⟨z,hz⟩,hcoord]
      rw [scaledPlaneSlide_second]
    · rw [hout t z hz]
  have hanchor : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image := by
    intro t
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩; exact (hmem t q).mpr hq
    · intro hz
      obtain ⟨g,hg⟩ := G.homeomorphism_at t
      refine ⟨g.symm z,?_,?_⟩
      · apply (hmem t (g.symm z)).mp
        rw [← hg,g.apply_symm_apply]
        exact hz
      · change G.map (t,g.symm z) = z
        rw [← hg,g.apply_symm_apply]
  refine ⟨G,hmarks,hanchor,?_,?_⟩
  · intro w q hq hne t
    by_cases hqU : q ∈ U
    · have hK : K.map (t,⟨q,hqU⟩) = ⟨q,hqU⟩ := by
        apply e.injective
        apply Subtype.ext
        rw [hcoord]
        exact scaledPlaneSlide_fixed ε hε a t _
          (Or.inl (hmargin w q hq hne hqU).le)
      rw [hGU t ⟨q,hqU⟩,hK]
    · exact hout t q hqU
  · intro ha heq
    have hK : K.map (1,⟨p,hpU⟩) = ⟨p,hpU⟩ :=
      Subtype.ext ((hGU 1 ⟨p,hpU⟩).symm.trans heq)
    have hc := hcoord (1:Interval) ⟨p,hpU⟩
    rw [hK,hpPlane,scaledPlaneSlide_origin] at hc
    have hc0 := congrArg (fun z : Plane => z 0) hc
    change 0 = ε*1*a.val at hc0
    exact ha ((mul_eq_zero.mp (by simpa using hc0.symm)).resolve_left (ne_of_gt hε))
end
end CurveComplex.HyperellipticModel.ArcSurgery
