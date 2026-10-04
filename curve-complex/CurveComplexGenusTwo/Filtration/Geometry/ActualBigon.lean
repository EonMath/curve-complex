import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives

namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Two genuine disjoint-interior non-loop arcs with the same ordered ends form a Jordan curve. -/
theorem actual_parallel_pair_curve (M : HyperellipticModel E S)
    (a b : NonLoopArc M)
    (h0 : a.val.map 0 = b.val.map 0) (h1 : a.val.map 1 = b.val.map 1)
    (hd : Disjoint (a.val.image \ (M.cover.branch : Set S))
      (b.val.image \ (M.cover.branch : Set S))) :
    ∃ c : Curve S, c.image = a.val.image ∪ b.val.image := by
  letI : T2Space S := M.sphere.symm.t2Space
  let f : C(Interval, S) := ⟨a.val.map, a.val.continuous⟩
  let g : C(Interval, S) := ⟨b.val.map, b.val.continuous⟩
  have hinter : ∀ t u : Interval, f t = g u →
      (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
    intro t u he
    change a.val.map t = b.val.map u at he
    have hb : a.val.map t ∈ M.cover.branch := by
      by_contra hn
      exact Set.disjoint_left.mp hd ⟨⟨t, rfl⟩, hn⟩
        ⟨⟨u, he.symm⟩, by change a.val.map t ∉ M.cover.branch; exact hn⟩
    have hb' : b.val.map u ∈ M.cover.branch := he ▸ hb
    rcases a.val.marked_only_at_ends t hb with ht | ht <;>
      rcases b.val.marked_only_at_ends u hb' with hu | hu
    · exact Or.inl ⟨ht, hu⟩
    · subst t
      subst u
      exact False.elim (a.property (he.trans h1.symm))
    · subst t
      subst u
      exact False.elim (a.property (h0.trans he.symm))
    · exact Or.inr ⟨ht, hu⟩
  exact CurveComplex.exists_curve_of_two_arcs f g a.injective b.injective h0 h1 hinter

/-- Source endpoint objects are unordered; reversing one actual parametrization resolves the two orientations. -/
theorem actual_parallel_pair_curve_unordered (M : HyperellipticModel E S)
    (a b : NonLoopArc M) (hends : markedArcEndset a.val = markedArcEndset b.val)
    (hd : Disjoint (a.val.image \ (M.cover.branch : Set S))
      (b.val.image \ (M.cover.branch : Set S))) :
    ∃ c : Curve S, c.image = a.val.image ∪ b.val.image := by
  classical
  change ({a.val.map 0, a.val.map 1} : Finset S) = {b.val.map 0, b.val.map 1} at hends
  have hmem0 : a.val.map 0 = b.val.map 0 ∨ a.val.map 0 = b.val.map 1 := by
    have h : a.val.map 0 ∈ ({b.val.map 0, b.val.map 1} : Finset S) :=
      hends ▸ (by simp)
    simpa using h
  rcases hmem0 with h0 | h0
  · have hmem1 : a.val.map 1 = b.val.map 0 ∨ a.val.map 1 = b.val.map 1 := by
      have h : a.val.map 1 ∈ ({b.val.map 0, b.val.map 1} : Finset S) :=
        hends ▸ (by simp)
      simpa using h
    have h1 : a.val.map 1 = b.val.map 1 := by
      rcases hmem1 with h | h
      · exact False.elim (a.property (h0.trans h.symm))
      · exact h
    exact actual_parallel_pair_curve M a b h0 h1 hd
  · have hmemB : b.val.map 0 = a.val.map 0 ∨ b.val.map 0 = a.val.map 1 := by
      have h : b.val.map 0 ∈ ({a.val.map 0, a.val.map 1} : Finset S) :=
        hends.symm ▸ (by simp)
      simpa using h
    have h1 : a.val.map 1 = b.val.map 0 := by
      rcases hmemB with h | h
      · exact False.elim (b.property (h.trans h0))
      · exact h.symm
    let br : MarkedArc M := {
      map := fun t => b.val.map (unitInterval.symm t)
      continuous := b.val.continuous.comp unitInterval.continuous_symm
      injective_except_loop_closure := fun t u h =>
        Or.inl (unitInterval.symm_bijective.injective (b.injective h))
      start_marked := by
        convert b.val.end_marked using 1
        congr 1
        apply Subtype.ext
        norm_num [unitInterval.coe_symm_eq]
      end_marked := by
        convert b.val.start_marked using 1
        congr 1
        apply Subtype.ext
        norm_num [unitInterval.coe_symm_eq]
      marked_only_at_ends := by
        intro t ht
        rcases b.val.marked_only_at_ends (unitInterval.symm t) ht with h | h
        · exact Or.inr (unitInterval.symm_eq_zero.mp h)
        · exact Or.inl (unitInterval.symm_eq_one.mp h) }
    have hbr : br.map 0 ≠ br.map 1 := by
      dsimp [br]
      simp only [unitInterval.symm_zero, unitInterval.symm_one]
      convert Ne.symm b.property using 1 <;> congr 1 <;> apply Subtype.ext <;> norm_num
    have hbrimg : br.image = b.val.image := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨unitInterval.symm t, rfl⟩
      · rintro ⟨t, rfl⟩
        refine ⟨unitInterval.symm t, ?_⟩
        simp only [br, unitInterval.symm_symm]
    have hdbr : Disjoint (a.val.image \ (M.cover.branch : Set S))
        (br.image \ (M.cover.branch : Set S)) := by rw [hbrimg]; exact hd
    obtain ⟨c, hc⟩ := actual_parallel_pair_curve M a ⟨br, hbr⟩
      (by simpa only [br, unitInterval.symm_zero] using h0)
      (by simpa only [br, unitInterval.symm_one] using h1) hdbr
    exact ⟨c, hc.trans (congrArg (fun Z => a.val.image ∪ Z) hbrimg)⟩


end CurveComplex.HyperellipticModel
