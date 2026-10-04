import CurveComplexGenusTwo.Topology.CurveCombinatorics
import CurveComplexGenusTwo.Topology.TorusDeckLift
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
/-- Literal source direction definition from PuncturedTorusRepresentative.lean.
The canonical TorusDeckLift already owns the source's identical Torus alias. -/
def slopeDirection : FareySlope → ℤ × ℤ
  | none => (1, 0)
  | some q => (q.num, q.den)
end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
