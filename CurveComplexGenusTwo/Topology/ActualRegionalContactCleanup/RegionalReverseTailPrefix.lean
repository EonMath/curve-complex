import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_reversed_anchor_tail_is_original_prefix
    {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (r : Interval) :
    (fun t : Interval => a (unitInterval.symm t)) ''
      Set.Icc (unitInterval.symm r) 1 =
    a '' Set.Icc 0 r := by
  ext y
  constructor
  · rintro ⟨t,⟨htlo,hthi⟩,rfl⟩
    refine ⟨unitInterval.symm t,⟨(unitInterval.symm t).property.1,?_⟩,rfl⟩
    have h : (unitInterval.symm r : ℝ) ≤ (t : ℝ) := htlo
    change 1-(r : ℝ) ≤ (t : ℝ) at h
    change (unitInterval.symm t : ℝ) ≤ (r : ℝ)
    change 1-(t : ℝ) ≤ (r : ℝ)
    linarith only [h]
  · rintro ⟨t,⟨htlo,hthi⟩,rfl⟩
    refine ⟨unitInterval.symm t,⟨?_,(unitInterval.symm t).property.2⟩,?_⟩
    · have h : (t : ℝ) ≤ (r : ℝ) := hthi
      change (unitInterval.symm r : ℝ) ≤ (unitInterval.symm t : ℝ)
      change 1-(r : ℝ) ≤ 1-(t : ℝ)
      linarith only [h]
    · change a (unitInterval.symm (unitInterval.symm t)) = a t
      rw [unitInterval.symm_involutive]

#print axioms regional_reversed_anchor_tail_is_original_prefix
