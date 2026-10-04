import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceParameterizedSimpleLoop

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Set Topology

theorem two_embedded_arcs_parameterized_curve
    {S : Type} [TopologicalSpace S] [T2Space S] {x y : S}
    (p q : Path x y) (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t : CurveComplex.Interval, p s = q t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ c : Curve S, c.image = Set.range p ∪ Set.range q ∧
      ∀ t : CurveComplex.Interval,
        c.map (Circle.exp (2 * Real.pi * t.val)) = (p.trans q.symm) t := by
  have hcross' (s t : CurveComplex.Interval) (he : p s = q.symm t) :
      (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) := by
    have hh := hcross s (unitInterval.symm t) he
    rcases hh with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · right
      refine ⟨hs,?_⟩
      apply Subtype.ext
      have hv := congrArg Subtype.val ht
      change 1 - t.val = 0 at hv
      change t.val = 1
      linarith
    · left
      refine ⟨hs,?_⟩
      apply Subtype.ext
      have hv := congrArg Subtype.val ht
      change 1 - t.val = 1 at hv
      change t.val = 0
      linarith
  obtain ⟨c,hc,hparam⟩ := simple_loop_gives_parameterized_curve x (p.trans q.symm)
    (embedded_arcs_closing_loop_collision p q.symm hp
      (hq.comp unitInterval.symm_involutive.injective) hcross')
  refine ⟨c,?_,hparam⟩
  rw [hc,Path.trans_range,Path.symm_range]

end CurveComplexGenusTwo.SourceTopology
