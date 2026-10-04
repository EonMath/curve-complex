import Mathlib.Algebra.BigOperators.Group.Finset.Basic

private theorem actual_finite_supported_index_sum {E : Type} [DecidableEq E]
    (U T : Finset E) (hTU : T ⊆ U) (d : T → ℤ) (g : ↥U → ℤ)
    (hg : ∀ q, g q = if hq : q.val ∈ T then d ⟨q.val,hq⟩ else 0) :
    (∑ q : ↥U, g q) = ∑ q : T, d q := by
  classical
  let d₀ (x : E) : ℤ := if hx : x ∈ T then d ⟨x,hx⟩ else 0
  have hleft : (∑ q : ↥U, g q) = ∑ x ∈ U, d₀ x := by
    calc
      _ = ∑ q : ↥U, d₀ q.val := Finset.sum_congr rfl (fun q _ => hg q)
      _ = _ := Finset.sum_coe_sort (U) d₀
  have hright : (∑ q : T, d q) = ∑ x ∈ T, d₀ x := by
    calc
      _ = ∑ q : T, d₀ q.val := by
        apply Finset.sum_congr rfl
        intro q _
        simp only [d₀,dif_pos q.property]
      _ = _ := Finset.sum_coe_sort T d₀
  rw [hleft,hright]
  symm
  apply Finset.sum_subset hTU
  intro x _ hx
  simp only [d₀,dif_neg hx]


private theorem actual_union_supported_index_sum {E : Type} [DecidableEq E]
    (S T : Finset E) (d : T → ℤ) (g : ↥(S ∪ T) → ℤ)
    (hg : ∀ q, g q = if hq : q.val ∈ T then d ⟨q.val,hq⟩ else 0) :
    (∑ q : ↥(S ∪ T), g q) = ∑ q : T, d q := by
  classical
  let d₀ (x : E) : ℤ := if hx : x ∈ T then d ⟨x,hx⟩ else 0
  have hleft : (∑ q : ↥(S ∪ T), g q) = ∑ x ∈ S ∪ T, d₀ x := by
    calc
      _ = ∑ q : ↥(S ∪ T), d₀ q.val := Finset.sum_congr rfl (fun q _ => hg q)
      _ = _ := Finset.sum_coe_sort (S ∪ T) d₀
  have hright : (∑ q : T, d q) = ∑ x ∈ T, d₀ x := by
    calc
      _ = ∑ q : T, d₀ q.val := by
        apply Finset.sum_congr rfl
        intro q _
        simp only [d₀,dif_pos q.property]
      _ = _ := Finset.sum_coe_sort T d₀
  rw [hleft,hright]
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro x _ hx
  simp only [d₀,dif_neg hx]
