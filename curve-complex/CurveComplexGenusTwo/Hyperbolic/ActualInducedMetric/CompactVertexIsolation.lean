import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSeamIsolation

namespace CurveComplex.Hyperbolic
open Set Topology

theorem Hexagon.embedded_vertex_local_isolation (P : Hexagon) (hP : P.IsEmbedded)
    (i : Fin 6) : ∃ ε : ℝ, 0 < ε ∧
      ∀ j : Fin 6, j ≠ i → j ≠ i - 1 →
        Disjoint (Metric.ball (P.vertex i) ε) (P.edge j) := by
  have hn (j : Fin 6) (hj : j ≠ i) (hj' : j ≠ i - 1) :
      P.vertex i ∉ P.edge j := by
    intro hxj
    have hxi : P.vertex i ∈ P.edge i := by
      change dist (P.vertex i) (P.vertex i) +
        dist (P.vertex i) (P.vertex (i + 1)) = _
      simp
    have he := (hP i j hj.symm ⟨hxi, hxj⟩).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with he | he
    · exact hj (P.injective he).symm
    · have hi := P.injective he
      apply hj'
      fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hi
  let U := ⋂ j : Fin 6,
    if j = i ∨ j = i - 1 then Set.univ else (P.edge j)ᶜ
  have hopen : IsOpen U := isOpen_iInter_of_finite fun j => by
    by_cases hj : j = i ∨ j = i - 1
    · simp [hj]
    · simpa [hj] using (P.edge_isClosed j).isOpen_compl
  have hxu : P.vertex i ∈ U := by
    apply Set.mem_iInter.mpr
    intro j
    by_cases hj : j = i ∨ j = i - 1
    · simp [hj]
    · simpa [hj] using hn j (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h))
  obtain ⟨ε, he, hball⟩ := Metric.isOpen_iff.mp hopen (P.vertex i) hxu
  refine ⟨ε, he, ?_⟩
  intro j hj hj'
  apply Set.disjoint_left.mpr
  intro z hz hzj
  have hzU := Set.mem_iInter.mp (hball hz) j
  have hznot : z ∉ P.edge j := by simp_all
  exact hznot hzj

end CurveComplex.Hyperbolic
