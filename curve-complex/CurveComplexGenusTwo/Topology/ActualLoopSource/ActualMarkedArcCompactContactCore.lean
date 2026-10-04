import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
import Mathlib.Topology.Order.Compact
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- A genuine compact branch-free movie contact carrier lies within an
embedded interior core of the original arc, including original loops. -/
theorem actual_marked_arc_compact_contact_core
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (C : Set S) (hC : IsCompact C)
    (hmarks : Disjoint C (M.cover.branch : Set S)) :
    ∃ l u : ℝ, 0<l ∧ l<u ∧ u<1 ∧
      ∀ t : Interval, a.val.map t ∈ C → l<(t:ℝ) ∧ (t:ℝ)<u := by
  let : T2Space S := M.sphere.symm.t2Space
  let K : Set Interval := a.val.map ⁻¹' C
  have hK : IsCompact K := (hC.isClosed.preimage a.val.continuous).isCompact
  have hKbounds (t : Interval) (ht : t ∈ K) : 0<(t:ℝ) ∧ (t:ℝ)<1 := by
    constructor
    · apply lt_of_le_of_ne t.property.1
      intro he
      have ht0 : t=0 := Subtype.ext he.symm
      exact Set.disjoint_left.mp hmarks ht (ht0 ▸ a.val.start_marked)
    · apply lt_of_le_of_ne t.property.2
      intro he
      have ht1 : t=1 := Subtype.ext he
      exact Set.disjoint_left.mp hmarks ht (ht1 ▸ a.val.end_marked)
  by_cases hn : K.Nonempty
  · obtain ⟨s,hs,hmin⟩ := hK.exists_isMinOn hn continuous_subtype_val.continuousOn
    obtain ⟨t,ht,hmax⟩ := hK.exists_isMaxOn hn continuous_subtype_val.continuousOn
    refine ⟨(s:ℝ)/2,((t:ℝ)+1)/2,?_,?_,?_,?_⟩
    · linarith [(hKbounds s hs).1]
    · have hst : (s:ℝ)≤(t:ℝ) := hmin ht
      linarith [(hKbounds t ht).2]
    · linarith [(hKbounds t ht).2]
    · intro r hr
      have hlo : (s:ℝ)≤(r:ℝ) := hmin hr
      have hhi : (r:ℝ)≤(t:ℝ) := hmax hr
      constructor <;> linarith [(hKbounds s hs).1,(hKbounds t ht).2]
  · refine ⟨1/4,3/4,by norm_num,by norm_num,by norm_num,?_⟩
    intro t ht
    exact False.elim (hn ⟨t,ht⟩)
end CurveComplex.HyperellipticModel
