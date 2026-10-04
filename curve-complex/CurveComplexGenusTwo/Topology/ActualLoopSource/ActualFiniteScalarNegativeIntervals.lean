import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOrderedScalarMeshCover
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_finite_scalar_negative_intervals (g : C(Interval,ℝ)) (hf : (g ⁻¹' {0}).Finite) :
    ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval, ∃ negative : Fin (m+1) → Prop,
      StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
      (∀ j,mesh j=0 ∨ mesh j=1 ∨ g (mesh j)=0) ∧
      (∀ (j : Fin (m+1)) (t : Interval),mesh j.castSucc < t → t < mesh j.succ → g t≠0) ∧
      (∀ j,negative j → ∀ t∈Set.Icc (mesh j.castSucc) (mesh j.succ),g t≤0) ∧
      ∀ t,g t≤0 ↔ g t=0 ∨ ∃ j,negative j ∧ t∈Set.Icc (mesh j.castSucc) (mesh j.succ) := by
  obtain ⟨m,mesh,hm,h0,h1,hnodes,hno⟩ := actual_finite_scalar_zero_mesh g hf
  let midpoint (j : Fin (m+1)) : Interval :=
    ⟨((mesh j.castSucc).val+(mesh j.succ).val)/2,by
      constructor <;> linarith only [(mesh j.castSucc).property.1,(mesh j.castSucc).property.2,
        (mesh j.succ).property.1,(mesh j.succ).property.2]⟩
  have hmid (j : Fin (m+1)) : mesh j.castSucc < midpoint j ∧ midpoint j < mesh j.succ := by
    have hs : (mesh j.castSucc).val < (mesh j.succ).val := hm (by change j.val < j.val+1; omega)
    constructor
    · change (mesh j.castSucc).val < ((mesh j.castSucc).val+(mesh j.succ).val)/2
      linarith only [hs]
    · change ((mesh j.castSucc).val+(mesh j.succ).val)/2 < (mesh j.succ).val
      linarith only [hs]
  let negative (j : Fin (m+1)) : Prop := g (midpoint j)<0
  have hnegative (j : Fin (m+1)) (hj : negative j) :
      ∀ t∈Set.Icc (mesh j.castSucc) (mesh j.succ),g t≤0 :=
    actual_zero_free_scalar_interval_sign g _ _ (midpoint j) (hmid j).1 (hmid j).2 hj (hno j)
  refine ⟨m,mesh,negative,hm,h0,h1,hnodes,hno,hnegative,?_⟩
  intro t
  constructor
  · intro ht
    by_cases hz : g t=0
    · exact Or.inl hz
    right
    obtain ⟨j,hj0,hj1⟩ := actual_ordered_scalar_mesh_cover mesh hm h0 h1 t
    refine ⟨j,?_,hj0,hj1⟩
    by_contra hn
    have hmidpos : 0<g (midpoint j) :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hno j _ (hmid j).1 (hmid j).2))
    let ng : C(Interval,ℝ) := ⟨fun s => -g s,g.continuous.neg⟩
    have hngmid : ng (midpoint j)<0 := neg_neg_of_pos hmidpos
    have hngno (s : Interval) (hs0 : mesh j.castSucc < s) (hs1 : s < mesh j.succ) : ng s≠0 :=
      neg_ne_zero.mpr (hno j s hs0 hs1)
    have hnonpos := actual_zero_free_scalar_interval_sign ng _ _ (midpoint j) (hmid j).1 (hmid j).2
      hngmid hngno t ⟨hj0,hj1⟩
    change -g t≤0 at hnonpos
    exact hz (le_antisymm ht (neg_nonpos.mp hnonpos))
  · rintro (hz | ⟨j,hj,ht⟩)
    · exact hz.le
    · exact hnegative j hj t ht
end CurveComplex.HyperellipticModel
