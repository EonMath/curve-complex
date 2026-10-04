import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteBoundaryAvoidingPhase
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A finite set of ACTUAL normal coordinates and actual supported weights
produces a small shift removing every zero. The weight condition is discharged
by the constructed contact cutoff and the interior wall in the loop caller. -/
theorem actual_finite_normal_coordinate_shift
    {ι : Type} [Finite ι] (normal weight : ι → ℝ)
    (hzero : ∀ i,normal i=0 → weight i≠0)
    (margin : ℝ) (hmargin : 0< margin) :
    ∃ δ : ℝ,0<δ ∧ δ< margin ∧ ∀ i,normal i+δ*weight i≠0 := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let forbidden : Set ℝ := ⋃ i : ι,if weight i=0 then ∅ else {-normal i/weight i}
  have hf : forbidden.Finite := Set.finite_iUnion (fun i => by
    split_ifs
    · exact finite_empty
    · exact finite_singleton _)
  obtain ⟨δ,hδ,havoid⟩ := (Ioo_infinite hmargin).exists_notMem_finite hf
  refine ⟨δ,hδ.1,hδ.2,?_⟩
  intro i he
  by_cases hw : weight i=0
  · have hn : normal i=0 := by simpa only [hw,mul_zero,add_zero] using he
    exact hzero i hn hw
  · apply havoid
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [ite_eq_right hw,mem_singleton_iff]
    apply (eq_div_iff hw).mpr
    linarith only [he]
end CurveComplex.HyperellipticModel
