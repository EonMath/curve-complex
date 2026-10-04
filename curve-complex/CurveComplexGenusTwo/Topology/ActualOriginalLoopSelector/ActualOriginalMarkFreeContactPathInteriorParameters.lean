import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorInteriorCoordinates
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkedArcCompactContactCore
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkFreeMovieExactContactCore
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAffineWindowLocalBounds
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Review-only bounded decoder for actual mark-free paths on an ORIGINAL arc.
Loop endpoints may coincide; no global inverse of the original loop is assumed. -/
theorem actual_original_mark_free_contact_path_interior_parameters
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (γ : C(Interval,S))
    (hcontact : ∀ t,γ t ∈ a.val.image)
    (hmarks : ∀ t,γ t ∉ (M.cover.branch : Set S)) :
    ∃ κ : C(Interval,Interval),
      (∀ t,a.val.map (κ t)=γ t) ∧
      ∀ t,0<(κ t:ℝ) ∧ (κ t:ℝ)<1 := by
  classical
  let contact : C(Interval,arcInterior M a) :=
    ⟨fun t => ⟨γ t,⟨hcontact t,hmarks t⟩⟩,by fun_prop⟩
  let coordinates := anchorInteriorCoordinates M a
  let parameter : C(Interval,OpenAnchorParameter) :=
    ⟨fun t => coordinates.symm (contact t),by fun_prop⟩
  let κ : C(Interval,Interval) :=
    ⟨fun t => openAnchorInterval (parameter t),
      openAnchorInterval_continuous.comp parameter.continuous⟩
  refine ⟨κ,?_,?_⟩
  · intro t
    change a.val.map (openAnchorInterval (coordinates.symm (contact t)))=γ t
    rw [← anchorInteriorCoordinates_apply M a]
    exact congrArg Subtype.val (coordinates.apply_symm_apply (contact t))
  · intro t
    exact (parameter t).property
end CurveComplex.HyperellipticModel
