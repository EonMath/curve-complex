import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actualEndpointObject_contains_JordanCircle (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (v : EssentialArcClass M) (hc : 2 ≤ (actualEndpointFibre M σ v).card) :
    ∃ J : CurveComplex.SpherePort.JordanCurve,
      J.image ⊆ M.sphere '' actualObjectTrace M r (actualEndpointFibre M σ v) := by
  classical
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) hc)
  let U : {v // v ∈ σ} := ⟨u, actualEndpointFibre_subset M σ v hu⟩
  let W : {v // v ∈ σ} := ⟨w, actualEndpointFibre_subset M σ v hw⟩
  have hUn : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (r U)) := by
    rw [hr]; exact (Finset.mem_filter.mp hu).2.1
  have hWn : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (r W)) := by
    rw [hr]; exact (Finset.mem_filter.mp hw).2.1
  let a : NonLoopArc M := ⟨(r U).val, actualRepresentative_nonloop M (r U) hUn⟩
  let b : NonLoopArc M := ⟨(r W).val, actualRepresentative_nonloop M (r W) hWn⟩
  have he : markedArcEndset a.val = markedArcEndset b.val := by
    change markedArcEndset (r U).val = markedArcEndset (r W).val
    rw [markedArcEndset_eq_classEndpoints, markedArcEndset_eq_classEndpoints, hr, hr]
    exact (Finset.mem_filter.mp hu).2.2.trans (Finset.mem_filter.mp hw).2.2.symm
  have hUW : U ≠ W := fun h => huw (congrArg Subtype.val h)
  obtain ⟨c, hci⟩ := actual_parallel_pair_curve_unordered M a b he (hd U W hUW)
  obtain ⟨J, hJ⟩ := actualCurve_sphereJordan M c
  refine ⟨J, ?_⟩
  rw [hJ]
  apply image_mono
  rw [hci]
  intro x hx
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨U, mem_iUnion.mpr ⟨hu, hx⟩⟩
  · exact mem_iUnion.mpr ⟨W, mem_iUnion.mpr ⟨hw, hx⟩⟩

end CurveComplex.HyperellipticModel
