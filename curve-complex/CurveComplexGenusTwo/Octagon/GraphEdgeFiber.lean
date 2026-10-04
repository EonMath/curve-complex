import CurveComplexGenusTwo.Octagon.GraphInterface

namespace CurveComplex.Octagon.AttachingMap

theorem graphEdgeMap_fiber (i j : Fin 4) (t u : unitInterval) :
    graphEdgeMap (i, t) = graphEdgeMap (j, u) ↔
      (i = j ∧ t = u) ∨ ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) := by
  have hindex_inj : Function.Injective graphEdgeIndex := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [graphEdgeIndex] at h ⊢
  have hindex_pair_ne : ∀ a b : Fin 4, graphEdgeIndex b ≠ pair (graphEdgeIndex a) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [graphEdgeIndex, pair] at h
  have hvertex (a : Fin 4) (v : unitInterval) (hv : v = 0 ∨ v = 1) :
      mk (side (graphEdgeIndex a) v) = mk (vertexPoint 0) := by
    have hmem : side (graphEdgeIndex a) v ∈ vertexSet :=
      (side_mem_vertexSet_iff _ _).mpr hv
    rw [← vertex_fiber_eq_vertexSet 0] at hmem
    exact hmem
  constructor
  · intro h
    have hmk := (graphEdgeMap_eq_iff_mk_side_eq).mp h
    by_cases ht0 : t = 0
    · have hu : u = 0 ∨ u = 1 := by
        have hmem : side (graphEdgeIndex j) u ∈
            mk ⁻¹' ({mk (vertexPoint 0)} : Set Surface) := by
          change mk (side (graphEdgeIndex j) u) = mk (vertexPoint 0)
          exact hmk.symm.trans (hvertex i t (Or.inl ht0))
        rw [vertex_fiber_eq_vertexSet] at hmem
        exact (side_mem_vertexSet_iff _ _).mp hmem
      exact Or.inr ⟨Or.inl ht0, hu⟩
    by_cases ht1 : t = 1
    · have hu : u = 0 ∨ u = 1 := by
        have hmem : side (graphEdgeIndex j) u ∈
            mk ⁻¹' ({mk (vertexPoint 0)} : Set Surface) := by
          change mk (side (graphEdgeIndex j) u) = mk (vertexPoint 0)
          exact hmk.symm.trans (hvertex i t (Or.inr ht1))
        rw [vertex_fiber_eq_vertexSet] at hmem
        exact (side_mem_vertexSet_iff _ _).mp hmem
      exact Or.inr ⟨Or.inr ht1, hu⟩
    have hmem : side (graphEdgeIndex j) u ∈
        mk ⁻¹' ({mk (side (graphEdgeIndex i) t)} : Set Surface) := hmk.symm
    rw [edge_interior_fiber_eq_pair _ _ ht0 ht1] at hmem
    rcases Set.mem_insert_iff.mp hmem with hsame | hpair
    · rcases side_eq_same_or_endpoints _ _ _ _ hsame with ⟨hij, htu⟩ | hend
      · exact Or.inl ⟨hindex_inj hij.symm, htu.symm⟩
      · exact False.elim (ht0 (hend.2.resolve_right ht1))
    · have hp : side (graphEdgeIndex j) u =
          side (pair (graphEdgeIndex i)) (unitInterval.symm t) :=
        Set.mem_singleton_iff.mp hpair
      rcases side_eq_same_or_endpoints _ _ _ _ hp with ⟨hij, _⟩ | hend
      · exact False.elim (hindex_pair_ne i j hij)
      · have hu : u = 0 ∨ u = 1 := hend.1
        have ht : unitInterval.symm t = 0 ∨ unitInterval.symm t = 1 := hend.2
        rcases ht with ht | ht
        · exact False.elim (ht1 (by simpa using congrArg unitInterval.symm ht))
        · exact False.elim (ht0 (by simpa using congrArg unitInterval.symm ht))
  · rintro (⟨rfl, rfl⟩ | ⟨ht, hu⟩)
    · rfl
    · apply (graphEdgeMap_eq_iff_mk_side_eq).mpr
      exact (hvertex i t ht).trans (hvertex j u hu).symm

end CurveComplex.Octagon.AttachingMap
