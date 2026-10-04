import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_prefix_first_contact_becomes_reversed_tail_first_contact
    {X : Type} [TopologicalSpace X]
    (anchor current : C(Interval,X)) (r u : Interval)
    (hprefix : ∀ s t : Interval, t ≤ r →
      current s = anchor t → s = u ∧ t = r) :
    ∀ s t : Interval, unitInterval.symm r ≤ t →
      current s = anchor (unitInterval.symm t) →
      s = u ∧ t = unitInterval.symm r := by
  intro s t ht he
  have htr : unitInterval.symm t ≤ r := by
    have h : (unitInterval.symm r : ℝ) ≤ (t : ℝ) := ht
    change 1-(r : ℝ) ≤ (t : ℝ) at h
    change (unitInterval.symm t : ℝ) ≤ (r : ℝ)
    change 1-(t : ℝ) ≤ (r : ℝ)
    linarith only [h]
  obtain ⟨hs,hr⟩ := hprefix s (unitInterval.symm t) htr he
  refine ⟨hs,?_⟩
  have hh := congrArg unitInterval.symm hr
  rwa [unitInterval.symm_involutive] at hh

#print axioms regional_prefix_first_contact_becomes_reversed_tail_first_contact
