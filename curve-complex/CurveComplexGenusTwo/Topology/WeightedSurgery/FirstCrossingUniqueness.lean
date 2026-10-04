import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers

namespace CurveComplex.HyperellipticModel.ArcSurgery

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem firstCrossing_point_unmarked (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
    anchor.val.map x.t ∉ M.cover.branch := by
  intro hb
  rcases anchor.val.marked_only_at_ends x.t hb with h | h
  · have hv := congrArg Subtype.val h
    have ht := x.t_interior.1
    change x.t.val = 0 at hv
    linarith
  · have hv := congrArg Subtype.val h
    have ht := x.t_interior.2
    change x.t.val = 1 at hv
    linarith

theorem firstCrossing_point_mem_crossings (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) :
    anchor.val.map x.t ∈ crossings M anchor (P.rep x.selected) := by
  have hu := firstCrossing_point_unmarked M anchor F P x
  constructor
  · exact ⟨⟨x.t, rfl⟩, hu⟩
  · exact ⟨⟨x.s, x.same_point.symm⟩, hu⟩

theorem firstCrossing_unique (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x y : FirstCrossing M anchor F P) : x = y := by
  have ht : x.t = y.t := by
    apply Subtype.ext
    have hx := (firstCrossing_point_mem_crossings M anchor F P x).2
    have hy := (firstCrossing_point_mem_crossings M anchor F P y).2
    rcases lt_trichotomy x.t.val y.t.val with h | h | h
    · exact False.elim (y.first x.selected x.t x.t_interior.1 h hx)
    · exact h
    · exact False.elim (x.first y.selected y.t y.t_interior.1 h hy)
  have hsel : x.selected = y.selected := by
    by_contra hn
    have hdis := P.distinct_crossings x.selected y.selected hn
    have hx := firstCrossing_point_mem_crossings M anchor F P x
    have hy := firstCrossing_point_mem_crossings M anchor F P y
    rw [← ht] at hy
    exact Set.disjoint_left.mp hdis hx hy
  have hs : x.s = y.s := by
    have hpoint : (P.rep x.selected).val.map x.s = (P.rep x.selected).val.map y.s := by
      rw [← x.same_point, hsel, ← y.same_point, ht]
    rcases (P.rep x.selected).val.injective_except_loop_closure x.s y.s hpoint with h | h | h
    · exact h
    · have hv := congrArg Subtype.val h.1
      change x.s.val = 0 at hv
      have hp := x.s_interior.1
      exact False.elim (by linarith)
    · have hv := congrArg Subtype.val h.1
      change x.s.val = 1 at hv
      have hp := x.s_interior.2
      exact False.elim (by linarith)
  cases x
  cases y
  simp_all

end CurveComplex.HyperellipticModel.ArcSurgery
