import CurveComplexGenusTwo.Foundations.ConeRealization
import CurveComplexGenusTwo.Topology.CurveCombinatorics

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The filled Farey complex, including exactly its nonempty flag faces. -/
def fareyComplex : AbstractSimplicialComplex FareySlope where
  faces := {s | s.Nonempty ∧ FareyFace s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hs.2.mono hts⟩
  singleton_mem := by
    intro v
    refine ⟨Finset.singleton_nonempty v, ?_⟩
    intro a ha b hb hab
    have hae : a = v := Finset.mem_singleton.mp ha
    have hbe : b = v := Finset.mem_singleton.mp hb
    exact False.elim (hab (hae.trans hbe.symm))

end CurveComplexGenusTwo.Topology
