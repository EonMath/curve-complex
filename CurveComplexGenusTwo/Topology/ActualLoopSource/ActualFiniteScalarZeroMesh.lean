import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeCompleteZeroRadials
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_finite_scalar_zero_mesh (g : C(Interval,ℝ)) (hf : (g ⁻¹' {0}).Finite) :
    ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,
      StrictMono mesh ∧ mesh 0 = 0 ∧ mesh (Fin.last (m+1)) = 1 ∧
      (∀ j, mesh j=0 ∨ mesh j=1 ∨ g (mesh j)=0) ∧
      ∀ (i : Fin (m+1)) (t : Interval),
        mesh i.castSucc < t → t < mesh i.succ → g t ≠ 0 := by
  let P : Finset Interval := hf.toFinset ∪ {0,1}
  have h0 : (0 : Interval) ∈ P := Finset.mem_union_right _ (by simp)
  have h1 : (1 : Interval) ∈ P := Finset.mem_union_right _ (by simp)
  have hcard : 2 ≤ P.card := by
    have hsub : ({0,1} : Finset Interval) ⊆ P := Finset.subset_union_right
    have hc := Finset.card_le_card hsub
    norm_num at hc
    exact hc
  let m := P.card-2
  have hm : P.card = m+2 := by dsimp [m]; omega
  let e := P.orderEmbOfFin hm
  have hmono : StrictMono e := e.strictMono
  have hz : e 0 = 0 := by
    have hr : (0 : Interval) ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact h0
    obtain ⟨j,hj⟩ := hr
    exact le_antisymm (hj ▸ hmono.monotone (Fin.zero_le j)) (e 0).property.1
  have ho : e (Fin.last (m+1)) = 1 := by
    have hr : (1 : Interval) ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact h1
    obtain ⟨j,hj⟩ := hr
    exact le_antisymm (e _).property.2 (hj ▸ hmono.monotone (Fin.le_last j))
  have hnodes (j : Fin (m+2)) : e j=0 ∨ e j=1 ∨ g (e j)=0 := by
    have hj : e j ∈ P := by
      have hr : e j ∈ Set.range e := ⟨j,rfl⟩
      rw [Finset.range_orderEmbOfFin] at hr
      exact hr
    rcases Finset.mem_union.mp hj with hj | hj
    · right; right
      exact hf.mem_toFinset.mp hj
    · have hh : e j=0 ∨ e j=1 := by simpa using hj
      exact hh.elim Or.inl (fun h => Or.inr (Or.inl h))
  refine ⟨m,e,hmono,hz,ho,hnodes,?_⟩
  intro i t ht0 ht1 hgt
  have htP : t ∈ P := Finset.mem_union_left _ (hf.mem_toFinset.mpr hgt)
  have hr : t ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact htP
  obtain ⟨j,hj⟩ := hr
  have hj0 := hmono.lt_iff_lt.mp (hj ▸ ht0)
  have hj1 := hmono.lt_iff_lt.mp (hj ▸ ht1)
  change i.val < j.val at hj0
  change j.val < i.val+1 at hj1
  omega
end CurveComplex.HyperellipticModel
