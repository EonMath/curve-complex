import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualProperCrosscutJoinedTailKernelRecovery
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

/-- The selected central path and the selected tail are joined, retaining both ranges. -/
theorem actualSameEmbeddedSquareTailProducesProperCrosscut
    (ρ : C(unitInterval × unitInterval, unitInterval × unitInterval))
    (hρ : IsEmbedding ρ) {w z x y : unitInterval × unitInterval}
    (q : Path w z) (hq : IsEmbedding q) (Q : Path x y) (hQ : IsEmbedding Q)
    (hend : Q 1 = ρ z)
    (hattach : range Q ∩ range ρ = {Q 1})
    (hqinside : ∀ t : unitInterval,t≠0 →
      (ρ (q t)).1∈Ioo (0 : unitInterval) 1 ∧ (ρ (q t)).2∈Ioo (0 : unitInterval) 1)
    (hQinside : ∀ t : unitInterval,t≠0 →
      (Q t).1∈Ioo (0 : unitInterval) 1 ∧ (Q t).2∈Ioo (0 : unitInterval) 1) :
    ∃ J : Path (ρ w) x, IsEmbedding J ∧
      range J = range (fun t => ρ (q t)) ∪ range Q ∧
      ∀ t : unitInterval,t∈Ioo (0 : unitInterval) 1 →
        (J t).1∈Ioo (0 : unitInterval) 1 ∧ (J t).2∈Ioo (0 : unitInterval) 1 := by
  have hy : y=ρ z := (Path.target Q).symm.trans hend
  let p : Path (ρ w) y := (q.map ρ.continuous).cast rfl hy
  have hp : IsEmbedding p := hρ.comp hq
  have hQs : IsEmbedding Q.symm := by
    apply Q.symm.continuous.isClosedEmbedding _ |>.isEmbedding
    intro t u he
    exact unitInterval.symm_inj.mp (hQ.injective he)
  have hinter : range p∩range Q.symm={y} := by
    rw [Path.symm_range]
    ext v
    constructor
    · rintro ⟨⟨t,rfl⟩,hmem⟩
      have hρmem : p t∈range ρ := ⟨q t,rfl⟩
      have hm : p t∈range Q∩range ρ := ⟨hmem,hρmem⟩
      rw [hattach] at hm
      exact mem_singleton_iff.mpr ((mem_singleton_iff.mp hm).trans (Path.target Q))
    · intro hv
      have he := mem_singleton_iff.mp hv
      subst v
      exact ⟨p.target_mem_range,Q.target_mem_range⟩
  refine ⟨p.trans Q.symm,actualEmbeddedContactPathTrans p Q.symm hp hQs hinter,?_,?_⟩
  · rw [Path.trans_range,Path.symm_range]
    rfl
  · apply actualJoinedPathInteriorOfPositiveFirstAndNonterminalSecond p Q.symm
    · exact hqinside
    · intro t ht
      apply hQinside
      intro he
      have hh := congrArg unitInterval.symm he
      exact ht (by simpa using hh)
end CurveComplex.LocalSurgery
