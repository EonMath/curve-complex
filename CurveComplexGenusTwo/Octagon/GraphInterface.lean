import CurveComplexGenusTwo.Octagon.AttachingMap
namespace CurveComplex.Octagon.AttachingMap
def graphEdgeIndex (i : Fin 4) : Side := ![0,1,4,5] i
theorem sideLoop_four_cover (q : BoundaryGraph) :
    ∃ (i : Fin 4) (t : unitInterval), sideLoop (graphEdgeIndex i) t = q := by
  obtain ⟨q, i, t, rfl⟩ := q
  fin_cases i
  · exact ⟨0,t,Subtype.ext rfl⟩
  · exact ⟨1,t,Subtype.ext rfl⟩
  · refine ⟨0,unitInterval.symm t,?_⟩
    exact Subtype.ext (side_pairing_reverse 0 t).symm
  · refine ⟨1,unitInterval.symm t,?_⟩
    exact Subtype.ext (side_pairing_reverse 1 t).symm
  · exact ⟨2,t,Subtype.ext rfl⟩
  · exact ⟨3,t,Subtype.ext rfl⟩
  · refine ⟨2,unitInterval.symm t,?_⟩
    exact Subtype.ext (side_pairing_reverse 4 t).symm
  · refine ⟨3,unitInterval.symm t,?_⟩
    exact Subtype.ext (side_pairing_reverse 5 t).symm


noncomputable def graphEdgeMap : C((Fin 4) × unitInterval, BoundaryGraph) where
  toFun p := sideLoop (graphEdgeIndex p.1) p.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hf : ∀ᶠ i in nhds p.1, i = p.1 := by
      exact (isOpen_discrete (s := ({p.1} : Set (Fin 4))).mem_nhds (by simp))
    have h : ∀ᶠ x in nhds p, x.1 = p.1 :=
      (continuous_fst.continuousAt : Filter.Tendsto (Prod.fst : Fin 4 × unitInterval → Fin 4) (nhds p) (nhds p.1)).eventually hf
    have hc : ContinuousAt (fun x : Fin 4 × unitInterval => sideLoop (graphEdgeIndex p.1) x.2) p := ((sideLoop (graphEdgeIndex p.1)).continuous.continuousAt.comp
      continuous_snd.continuousAt)
    exact hc.congr_of_eventuallyEq (h.mono (fun x hx => by simp [hx]))

theorem graphEdgeMap_surjective : Function.Surjective graphEdgeMap := by
  intro q
  obtain ⟨i,t,h⟩ := sideLoop_four_cover q
  exact ⟨(i,t),h⟩

theorem graphEdgeMap_isQuotientMap : Topology.IsQuotientMap graphEdgeMap := by
  letI : T2Space Surface := quotient_t2
  exact graphEdgeMap.continuous.isClosedMap.isQuotientMap
    graphEdgeMap.continuous graphEdgeMap_surjective
end CurveComplex.Octagon.AttachingMap

namespace CurveComplex.Octagon.AttachingMap

/-- Equality of graph-edge path values is equivalent to equality of their quotient representatives. -/
theorem sideLoop_eq_iff_mk_side_eq (i j : Side) (t s : unitInterval) :
    sideLoop i t = sideLoop j s ↔ mk (side i t) = mk (side j s) := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- The graph map equality can be checked directly in the surface quotient. -/
theorem graphEdgeMap_eq_iff_mk_side_eq {i j : Fin 4} {t s : unitInterval} :
    graphEdgeMap (i, t) = graphEdgeMap (j, s) ↔
      mk (side (graphEdgeIndex i) t) = mk (side (graphEdgeIndex j) s) := by
  exact sideLoop_eq_iff_mk_side_eq _ _ _ _

end CurveComplex.Octagon.AttachingMap
