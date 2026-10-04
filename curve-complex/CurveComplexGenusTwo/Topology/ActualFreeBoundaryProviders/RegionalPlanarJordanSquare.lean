import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.RegionalPlanarExcursion
import CurveComplexGenusTwo.Topology.ArcStraightening

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- The actual finite-contact Jordan excursion has a global planar square
    coordinate. It is not yet a chart downstairs on the surface. -/
theorem planar_finite_pair_has_jordan_square_coordinate
    (A B : C(Interval,Plane))
    (hA : Topology.IsEmbedding A) (hB : Topology.IsEmbedding B)
    (h0 : A 0 = B 0) (h1 : A 1 = B 1)
    (hfinite : (Set.range A ∩ Set.range B).Finite) :
    ∃ (P Q : Set Plane) (u v : Plane) (φ : Plane ≃ₜ Plane),
      u ≠ v ∧
      IsArcBetween P u v ∧ IsArcBetween Q u v ∧
      P ⊆ Set.range A ∧ Q ⊆ Set.range B ∧
      P ∩ Q = {u,v} ∧
      φ '' modelCurve = P ∪ Q ∧
      φ '' Plane.openSquare 0 1 = Schoenflies.inside (P ∪ Q) ∧
      ∃ l r : Interval, l < r ∧
        Q \ {u,v} ⊆ B '' Set.Ioo l r ∧
        ∀ t : Interval, l < t → t < r → B t ∉ Set.range A := by
  obtain ⟨P,Q,u,v,huv,hP,hQ,hPA,hQB,hmeet,hJ,l,r,hlr,hQi,hgap⟩ :=
    planar_finite_pair_has_jordan_excursion A B hA hB h0 h1 hfinite
  obtain ⟨ec⟩ := IsJordanCurve.modelCurve_homeomorph hJ
  obtain ⟨φ,hφ⟩ :=
    jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hJ ec
  have hφC : φ '' modelCurve = P ∪ Q := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hφ ⟨x,hx⟩]
      exact (ec ⟨x,hx⟩).property
    · intro hz
      let x := ec.symm ⟨z,hz⟩
      refine ⟨x.val,x.property,?_⟩
      rw [hφ x]
      exact congrArg Subtype.val (ec.apply_symm_apply _)
  have hφI : φ '' Plane.openSquare 0 1 =
      Schoenflies.inside (P ∪ Q) := by
    rw [← inside_modelCurve]
    simpa only [hφC] using
      CurveComplex.jordan_inside_homeomorph_image φ modelCurve
  exact ⟨P,Q,u,v,φ,huv,hP,hQ,hPA,hQB,hmeet,hφC,hφI,
    l,r,hlr,hQi,hgap⟩

end RegionalEmbeddedFamily
