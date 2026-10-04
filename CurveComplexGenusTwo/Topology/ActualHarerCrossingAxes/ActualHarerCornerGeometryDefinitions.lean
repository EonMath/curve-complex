import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.Square
import Mathlib.Topology.OpenPartialHomeomorph.Defs

open CurveComplex Set Topology Schoenflies

namespace ActualHarerCornerGeometry

/-- The original parameter at the selected endpoint. Only v = 0 or v = 1
is used by the contracts. The value at other v is immaterial. -/
noncomputable def endpointParameter (v p₀ p₁ : Interval) : Interval :=
  if v = 0 then p₀ else p₁

/-- Sign of the direction from the selected original parameter to the other
original endpoint parameter. It refers to the original arc clock. -/
noncomputable def inwardParameterSign (v p₀ p₁ : Interval) : ℝ :=
  if v = 0 then (if p₀ < p₁ then 1 else -1)
  else (if p₁ < p₀ then 1 else -1)

/-- An actual two-axis chart, ordered by BOTH original whole-arc clocks.
This is a transparent property bundle for a supplied chart, not a disk-bank
or collar existence certificate. -/
structure OrderedWholePairAxes {S : Type*} [TopologicalSpace S]
    (f m : Interval → S) (s t l h : Interval)
    (E : OpenPartialHomeomorph S Plane) : Prop where
  center_mem : f s ∈ E.source
  center_zero : E (f s) = 0
  square_subset : Plane.closedSquare 0 1 ⊆ E.target
  anchor_axis : ∀ x ∈ E.source, x ∈ range f ↔ (E x) 1 = 0
  moving_axis : ∀ x ∈ E.source, x ∈ range m ↔ (E x) 0 = 0
  anchor_order : ∀ u : Interval, f u ∈ E.source →
    u ∈ Ioo l h ∧ ((E (f u)) 0 < 0 ↔ u < s) ∧
      (0 < (E (f u)) 0 ↔ s < u)
  moving_order : ∀ u : Interval, m u ∈ E.source →
    ((E (m u)) 1 < 0 ↔ u < t) ∧ (0 < (E (m u)) 1 ↔ t < u)

end ActualHarerCornerGeometry
