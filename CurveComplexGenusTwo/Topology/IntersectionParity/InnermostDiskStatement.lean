import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData

namespace CurveComplex.LocalSurgery

/-- Strict finite crossing descent selects an actual innermost disk from an
existing original two-curve disk candidate. -/
theorem two_curve_disk_has_innermost_disk
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val)
    (B : TwoCurveDisk a.val b.val) :
    ∃ B' : TwoCurveDisk a.val b.val,
      Disjoint B'.openInterior (a.val.image ∪ b.val.image) := by
  classical
  let P : ℕ → Prop := fun n => ∃ D : TwoCurveDisk a.val b.val, D.crossingCount ht = n
  have hex : ∃ n, P n := ⟨B.crossingCount ht, B, rfl⟩
  obtain ⟨D, hD⟩ := Nat.find_spec hex
  refine ⟨D, ?_⟩
  apply Set.disjoint_iff_inter_eq_empty.mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨E, hE⟩ := nonempty_two_curve_disk_has_smaller_disk a b ht D ⟨x, hx⟩
  have hlt : E.crossingCount ht < Nat.find hex := hE.trans_eq hD
  exact Nat.find_min hex hlt ⟨E, rfl⟩

end CurveComplex.LocalSurgery
