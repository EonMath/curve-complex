import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualClosedTorusExistenceStatements
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex
/-- Literal original source puncture-complement definition. -/
abbrev Punctured (p : Torus) := {x : Torus // x ≠ p}
/-- Literal original source filling definition. -/
def fill {p : Torus} (c : Curve (Punctured p)) : Curve Torus where
  map z := (c.map z).val
  embedded := Topology.IsEmbedding.subtypeVal.comp c.embedded
/-- Literal original source admissibility definition. -/
def Admissible {p : Torus} (c : Curve (Punctured p)) : Prop :=
  Essential (fill c)
end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
