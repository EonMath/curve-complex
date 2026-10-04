import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlideSystem
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Order.IntermediateValue

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

abbrev OpenAnchorParameter := Ioo (0 : ℝ) 1

def openAnchorInterval (r : OpenAnchorParameter) : Interval :=
  ⟨r.val,r.property.1.le,r.property.2.le⟩

theorem openAnchorInterval_continuous : Continuous openAnchorInterval :=
  continuous_subtype_val.subtype_mk _

theorem anchor_interior_parameter_bounds (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) (r : Interval) (hr : a.val.map r ∈ arcInterior M a) :
    0 < r.val ∧ r.val < 1 := by
  have hz : r.val ≠ 0 := by
    intro h
    apply hr.2
    have he : r = 0 := Subtype.ext h
    rw [he]
    exact a.val.start_marked
  have ho : r.val ≠ 1 := by
    intro h
    apply hr.2
    have he : r = 1 := Subtype.ext h
    rw [he]
    exact a.val.end_marked
  exact ⟨lt_of_le_of_ne r.property.1 (Ne.symm hz), lt_of_le_of_ne r.property.2 ho⟩

theorem openAnchorInterval_unmarked (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) (r : OpenAnchorParameter) :
    a.val.map (openAnchorInterval r) ∉ M.cover.branch := by
  intro hb
  rcases a.val.marked_only_at_ends (openAnchorInterval r) hb with h | h
  · have he := congrArg Subtype.val h
    change r.val = 0 at he
    linarith [r.property.1]
  · have he := congrArg Subtype.val h
    change r.val = 1 at he
    linarith [r.property.2]

def openAnchorDomain (M : HyperellipticModel E S) (a : EssentialMarkedArc M) :
    OpenAnchorParameter ≃ₜ (a.val.map ⁻¹' arcInterior M a) where
  toFun r := ⟨openAnchorInterval r,⟨⟨openAnchorInterval r,rfl⟩,openAnchorInterval_unmarked M a r⟩⟩
  invFun r := ⟨r.val.val,anchor_interior_parameter_bounds M a r.val r.property⟩
  left_inv _ := rfl
  right_inv r := by apply Subtype.ext; rfl
  continuous_toFun := openAnchorInterval_continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Actual interior anchor coordinates, including LOOP anchors: only the
identified marked endpoints are removed. -/
def anchorInteriorCoordinates (M : HyperellipticModel E S) (a : EssentialMarkedArc M) :
    OpenAnchorParameter ≃ₜ arcInterior M a := by
  let : T2Space S := M.sphere.symm.t2Space
  let f := (arcInterior M a).restrictPreimage a.val.map
  have hc : Continuous f := a.val.continuous.restrictPreimage
  have hclosed : IsClosedMap f := a.val.continuous.isClosedMap.restrictPreimage _
  have hi : Function.Injective f := by
    intro r s he
    have hh : a.val.map r.val = a.val.map s.val := congrArg Subtype.val he
    rcases a.val.injective_except_loop_closure r.val s.val hh with h | h | h
    · exact Subtype.ext h
    · have hb := anchor_interior_parameter_bounds M a r.val r.property
      have he := congrArg Subtype.val h.1
      change r.val.val = 0 at he
      exact False.elim (by linarith [hb.1])
    · have hb := anchor_interior_parameter_bounds M a r.val r.property
      have he := congrArg Subtype.val h.1
      change r.val.val = 1 at he
      exact False.elim (by linarith [hb.2])
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨r,hr⟩ := p.property.1
    refine ⟨⟨r,?_⟩,Subtype.ext hr⟩
    change a.val.map r ∈ arcInterior M a
    rw [hr]
    exact p.property
  exact (openAnchorDomain M a).trans ((Equiv.ofBijective f ⟨hi,hs⟩).toHomeomorphOfContinuousClosed hc hclosed)

theorem anchorInteriorCoordinates_apply (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) (r : OpenAnchorParameter) :
    (anchorInteriorCoordinates M a r).val = a.val.map (openAnchorInterval r) := rfl

end
end CurveComplex.HyperellipticModel.ArcSurgery
