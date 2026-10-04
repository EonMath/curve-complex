import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.UnmarkedLoopDiscDecomposition
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {S : Type} [TopologicalSpace S]

theorem unmarked_common_base_opposite_side_nested
    (a b : C(Interval,S))
    (hmeet : Set.range a ∩ Set.range b = {a 0})
    (A : UnmarkedLoopDiscDecomposition a)
    (B : UnmarkedLoopDiscDecomposition b)
    (i j : Fin 2) (hij : i ≠ j)
    (hbi : Set.range b \ {a 0} ⊆ A.side i) :
    ∃ k : Fin 2, A.side j ⊆ B.side k ∧
      Set.range a \ {a 0} ⊆ B.side k := by
  have hAij : Disjoint (A.side i) (A.side j) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact A.disjoint
    · exact A.disjoint.symm
    · exact False.elim (hij rfl)
  have hAjavoid : A.side j ⊆ (Set.range b)ᶜ := by
    intro x hxj hxb
    by_cases he : x = a 0
    · exact (A.discs j).component.2.2.1 hxj
        (he ▸ Set.mem_range_self (0 : Interval))
    · exact Set.disjoint_left.mp hAij (hbi ⟨hxb, by simpa using he⟩) hxj
  obtain ⟨x, hxj⟩ := (A.discs j).component.1
  let C := connectedComponentIn (Set.range b)ᶜ x
  have hC : IsComplementComponent (Set.range b) C :=
    complementComponent_iff_componentIn.mpr ⟨x, hAjavoid hxj, rfl⟩
  obtain ⟨k, hk⟩ := (B.all_components C).mp hC
  have hAjB : A.side j ⊆ B.side k := by
    rw [← hk]
    exact (A.discs j).component.2.1.isPreconnected.subset_connectedComponentIn hxj hAjavoid
  refine ⟨k, hAjB, ?_⟩
  intro y hy
  have hyclA : y ∈ closure (A.side j) := by
    apply frontier_subset_closure
    rw [(A.discs j).boundary]
    exact hy.1
  have hyclB : y ∈ closure (B.side k) := closure_mono hAjB hyclA
  rw [(B.discs k).closure_eq] at hyclB
  rcases hyclB with hyB | hyb
  · exact hyB
  · have hybase : y ∈ ({a 0} : Set S) := hmeet ▸ ⟨hy.1, hyb⟩
    exact False.elim (hy.2 hybase)

end CurveComplex.HyperellipticModel
