import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport

open Set
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Isolate an actual marked vertex from all central arc portions and every
nonincident arc simultaneously. This is derived from the caller's actual
parametrizations, including loops, without any local-star hypothesis. -/
theorem actual_endpoint_isolation
    (M : HyperellipticModel E S) (ι : Type) [Fintype ι]
    (a : ι → EssentialMarkedArc M) (p : S) (hp : p ∈ M.cover.branch)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      (∀ i t, r ≤ (t : Interval).val → t.val ≤ 1 - r → (a i).val.map t ∉ U) ∧
      (∀ i, (a i).val.map ⟨0, by norm_num⟩ ≠ p →
        (a i).val.map ⟨1, by norm_num⟩ ≠ p → Disjoint (a i).val.image U) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let middle : Set Interval := {t | r ≤ t.val ∧ t.val ≤ 1 - r}
  have hmidclosed : IsClosed middle :=
    (isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)
  let K : ι → Set S := fun i =>
    (a i).val.map '' middle ∪
      if (a i).val.map ⟨0, by norm_num⟩ = p ∨
        (a i).val.map ⟨1, by norm_num⟩ = p then ∅ else (a i).val.image
  have hKcompact : ∀ i, IsCompact (K i) := by
    intro i
    apply IsCompact.union (hmidclosed.isCompact.image (a i).val.continuous)
    split_ifs
    · exact isCompact_empty
    · exact isCompact_range (a i).val.continuous
  have hpK : ∀ i, p ∉ K i := by
    intro i
    rintro (hmid | hnoninc)
    · obtain ⟨t, ht, heq⟩ := hmid
      have hmarked := heq ▸ hp
      rcases (a i).val.marked_only_at_ends t hmarked with h0 | h1
      · subst t
        have hx := ht.1
        change r ≤ 0 at hx
        linarith
      · subst t
        have hx := ht.2
        change 1 ≤ 1 - r at hx
        linarith
    · dsimp [K] at hnoninc
      split_ifs at hnoninc with hi
      · exact hnoninc
      · obtain ⟨t, ht⟩ := hnoninc
        have hmarked := ht ▸ hp
        rcases (a i).val.marked_only_at_ends t hmarked with h0 | h1
        · subst t; exact hi (Or.inl ht)
        · subst t; exact hi (Or.inr ht)
  let U := W ∩ (⋃ i, K i)ᶜ
  refine ⟨U, hW.inter (isCompact_iUnion hKcompact).isClosed.isOpen_compl, ?_,
    inter_subset_left, ?_, ?_⟩
  · exact ⟨hpW, fun hi => by obtain ⟨i, hi⟩ := mem_iUnion.mp hi; exact hpK i hi⟩
  · intro i t ht0 ht1 hu
    exact hu.2 (mem_iUnion.mpr ⟨i, Or.inl ⟨t, ⟨ht0, ht1⟩, rfl⟩⟩)
  · intro i hi0 hi1
    apply Set.disjoint_left.mpr
    intro x hx hu
    apply hu.2
    apply mem_iUnion.mpr
    refine ⟨i, Or.inr ?_⟩
    rw [if_neg (not_or.mpr ⟨hi0, hi1⟩)]
    exact hx

#print axioms actual_endpoint_isolation
end CurveComplex.HyperellipticModel
