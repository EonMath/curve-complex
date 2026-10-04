import CurveComplexGenusTwo.Hyperbolic.FiniteRightHexagon
namespace CurveComplex.Hyperbolic
open Set Topology

theorem Hexagon.embedded_side_local_isolation (P : Hexagon) (hP : P.IsEmbedded)
    (i : Fin 6) (x : H2) (hx : x ∈ P.edge i)
    (hxi : x ≠ P.vertex i) (hxn : x ≠ P.vertex (i + 1)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ j : Fin 6, j ≠ i → Disjoint (Metric.ball x ε) (P.edge j) := by
  have hn (j : Fin 6) (hj : j ≠ i) : x ∉ P.edge j := by
    intro hxj
    have he := hP i j hj.symm ⟨hx, hxj⟩
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    exact he.1.elim hxi hxn
  let U := ⋂ j : Fin 6, if j = i then Set.univ else (P.edge j)ᶜ
  have hopen : IsOpen U := isOpen_iInter_of_finite fun j => by
    by_cases hj : j = i
    · simp [hj]
    · simpa [hj] using (P.edge_isClosed j).isOpen_compl
  have hxu : x ∈ U := by
    apply Set.mem_iInter.mpr
    intro j
    by_cases hj : j = i
    · simp [hj]
    · simpa [hj] using hn j hj
  obtain ⟨ε, he, hball⟩ := Metric.isOpen_iff.mp hopen x hxu
  refine ⟨ε, he, ?_⟩
  intro j hj
  apply Set.disjoint_left.mpr
  intro z hz hzj
  have hzU := Set.mem_iInter.mp (hball hz) j
  have hznot : z ∉ P.edge j := by simpa [hj] using hzU
  exact hznot hzj

end CurveComplex.Hyperbolic

