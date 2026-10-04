import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualLogarithmicContactCurveZeroExtension
import Mathlib.Topology.Order.IntermediateValue
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- An actual nonzero real contact trace cannot switch between the two loop
branches at positive parameters. No limit of its contact-time graph is used. -/
theorem actual_real_contact_trace_single_branch
    (C : C(Icc (0:ℝ) (1/2),ℂ))
    (hreal : ∀ t,(C t).im=0)
    (hnz : ∀ t,0<t.val → C t≠0) :
    (∀ t,0<t.val → 0<(C t).re) ∨ (∀ t,0<t.val → (C t).re<0) := by
  let D : C(Ioc (0:ℝ) (1/2),ℝ) :=
    ⟨fun t => (C ⟨t.val,t.property.1.le,t.property.2⟩).re,by fun_prop⟩
  let : PreconnectedSpace (Ioc (0:ℝ) (1/2)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  have hd (t : Ioc (0:ℝ) (1/2)) : D t≠0 := by
    intro h
    apply hnz ⟨t.val,t.property.1.le,t.property.2⟩ t.property.1
    apply Complex.ext
    · exact h
    · exact hreal _
  let q : Ioc (0:ℝ) (1/2) := ⟨1/2,by norm_num,le_rfl⟩
  rcases lt_or_gt_of_ne (hd q) with hneg | hpos
  · right
    intro t ht
    let u : Ioc (0:ℝ) (1/2) := ⟨t.val,ht,t.property.2⟩
    have hu : D u<0 := by
      by_contra h
      have hge : 0≤D u := le_of_not_gt h
      obtain ⟨v,hv⟩ := intermediate_value_univ q u D.continuous ⟨hneg.le,hge⟩
      exact hd v hv
    exact hu
  · left
    intro t ht
    let u : Ioc (0:ℝ) (1/2) := ⟨t.val,ht,t.property.2⟩
    have hu : 0<D u := by
      by_contra h
      have hle : D u≤0 := le_of_not_gt h
      obtain ⟨v,hv⟩ := intermediate_value_univ u q D.continuous ⟨hle,hpos.le⟩
      exact hd v hv
    exact hu
end CurveComplex.HyperellipticModel
