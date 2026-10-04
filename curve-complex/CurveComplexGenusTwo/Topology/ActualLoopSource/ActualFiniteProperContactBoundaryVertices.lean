import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellFiniteContactFamily
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Proper interior placement and full contact coverage retain every actual
boundary contact as a vertex, including all four original corners. -/
theorem actual_finite_proper_contact_boundary_vertices
    {S A : Type} [TopologicalSpace S]
    (G : C(Interval × Interval,S)) (old : Set S)
    (vertices : Finset (Interval × Interval)) (arc : A → C(Interval,Interval × Interval))
    (hends : ∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices)
    (hcoverage : ∀ z,G z ∈ old ↔ z ∈ vertices ∨ ∃ e t,arc e t=z)
    (hinterior : ∀ e t,0<t.val → t.val<1 →
      0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧
        0<(arc e t).2.val ∧ (arc e t).2.val<1) :
    ∀ z,G z ∈ old → z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z ∈ vertices := by
  intro z hz hb
  rcases (hcoverage z).mp hz with hv | ⟨e,t,he⟩
  · exact hv
  · by_cases ht0 : t=0
    · subst t
      exact he ▸ (hends e).1
    · by_cases ht1 : t=1
      · subst t
        exact he ▸ (hends e).2
      · have ht0R : 0<t.val := lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
        have ht1R : t.val<1 := lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
        obtain ⟨hx0,hx1,hy0,hy1⟩ := hinterior e t ht0R ht1R
        rw [he] at hx0 hx1 hy0 hy1
        rcases hb with h | h | h | h
        · simp [h] at hx0
        · simp [h] at hx1
        · simp [h] at hy0
        · simp [h] at hy1
end CurveComplex.HyperellipticModel
