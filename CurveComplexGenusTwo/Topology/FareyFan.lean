import CurveComplexGenusTwo.Foundations.ConeRealization
import CurveComplexGenusTwo.Topology.FareyArithmetic

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- Integer slopes together with infinity. -/
def fareyFanSlope : Option ℤ → FareySlope
  | none => none
  | some n => some (n : ℚ)

/-- The actual full Farey subcomplex on denominator-one slopes and infinity. -/
def fareyFanComplex : AbstractSimplicialComplex (Option ℤ) where
  faces := {s | s.Nonempty ∧
    (s : Set (Option ℤ)).Pairwise
      (fun a b => FareyAdjacent (fareyFanSlope a) (fareyFanSlope b))}
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

theorem fareyFan_hasConeApex : HasConeApex fareyFanComplex none := by
  intro s hs
  refine ⟨Finset.insert_nonempty none s, ?_⟩
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with ha | ha
  · subst a
    rcases Finset.mem_insert.mp hb with hb | hb
    · exact False.elim (hab hb.symm)
    · cases b with
      | none => exact False.elim (hab rfl)
      | some n => exact fareyAdjacent_none_int n
  · rcases Finset.mem_insert.mp hb with hb | hb
    · subst b
      cases a with
      | none => exact False.elim (hab rfl)
      | some n => exact fareyAdjacent_int_none n
    · exact hs.2 ha hb hab

theorem fareyFan_contractible :
    ContractibleSpace (RealizationPoint fareyFanComplex) := by
  exact coneApex_contractible fareyFanComplex none fareyFan_hasConeApex

end CurveComplexGenusTwo.Topology
