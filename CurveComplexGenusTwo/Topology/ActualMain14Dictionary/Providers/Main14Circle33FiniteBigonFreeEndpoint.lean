import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14FullPreimageTransversalityLift

namespace CurveComplex.LocalSurgery
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

/-- Choose an actual innermost disk by minimizing the actual finite disk
crossing count; the existing source subdisk construction makes its interior
empty. No innermostness or emptiness certificate is supplied. -/
theorem actual_two_curve_disk_produces_empty_disk
    {E : Type} [TopologicalSpace E] [ChartedSpace Plane E] [ClosedSurface E]
    (a b : EssentialCurve E) (ht : Transverse a.val b.val)
    (B : TwoCurveDisk a.val b.val) :
    ∃ D : TwoCurveDisk a.val b.val, Disjoint D.openInterior (a.val.image ∪ b.val.image) := by
  classical
  have hex : ∃ n : ℕ, ∃ D : TwoCurveDisk a.val b.val, D.crossingCount ht = n :=
    ⟨B.crossingCount ht,B,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  refine ⟨D,?_⟩
  by_contra hdisjoint
  have hin : (D.openInterior ∩ (a.val.image ∪ b.val.image)).Nonempty := by
    exact Set.not_disjoint_iff.mp hdisjoint
  obtain ⟨D',hlt⟩ := nonempty_two_curve_disk_has_smaller_disk a b ht D hin
  have hmin : Nat.find hex ≤ D'.crossingCount ht := Nat.find_min' hex ⟨D',rfl⟩
  omega
end CurveComplex.LocalSurgery

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 8000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]

/-- Actual finite strict elimination reaches a literal full-preimage pair
admitting no TwoCurveDisk at all, while retaining the arbitrary original
upstairs isotopy and both actual marked downstairs isotopies. -/
theorem circle33_isotopic_actual_finite_bigon_free_endpoint
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ht : Transverse a.val b.val)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (htbase : Transverse c.val.curve d.val.curve)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image) :
    ∃ a' b' : EssentialCurve E, ∃ c' d' : Circle33 M,
      a'.val.image = M.cover.projection ⁻¹' c'.val.image ∧
      b'.val.image = M.cover.projection ⁻¹' d'.val.image ∧
      MarkedIsotopyRel M c.val.image c'.val.image ∧
      MarkedIsotopyRel M d.val.image d'.val.image ∧
      AmbientIsotopy.Rel a'.val.image b'.val.image ∧
      Transverse a'.val b'.val ∧ Transverse c'.val.curve d'.val.curve ∧
      IsEmpty (LocalSurgery.TwoCurveDisk a'.val b'.val) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨a',b',c',d',ha',hb',hci,hdi,hiso',ht',htbase',hfree⟩ :=
    M.circle33_isotopic_actual_finite_empty_bigon_elimination a b c d ht ha hb htbase hiso
  refine ⟨a',b',c',d',ha',hb',hci,hdi,hiso',ht',htbase',⟨?_⟩⟩
  intro B
  exact hfree (LocalSurgery.actual_two_curve_disk_produces_empty_disk a' b' ht' B)
end CurveComplex.HyperellipticModel
