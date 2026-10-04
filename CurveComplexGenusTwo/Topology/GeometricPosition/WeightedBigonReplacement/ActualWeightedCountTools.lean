import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Set
open scoped BigOperators
namespace CurveComplex

theorem actual_arc_endpoint_incidence_split
    {S : Type*} (A D : Set S) [DecidablePred (· ∈ D)] (u z : S) (huz : u ≠ z)
    (hu : u ∈ A) (hz : z ∈ A) (hf : (A ∩ D).Finite) :
    (A ∩ D).ncard = ((A \ {u,z}) ∩ D).ncard +
      (if u ∈ D then 1 else 0)+(if z ∈ D then 1 else 0) := by
  classical
  have hsplit : A ∩ D = ((A \ {u,z}) ∩ D) ∪ ({u,z} ∩ D) := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha,hd⟩
      by_cases he : x = u ∨ x = z
      · exact Or.inr ⟨he,hd⟩
      · exact Or.inl ⟨⟨ha,he⟩,hd⟩
    · rintro (⟨⟨ha,he⟩,hd⟩ | ⟨he,hd⟩)
      · exact ⟨ha,hd⟩
      · rcases he with rfl | rfl
        · exact ⟨hu,hd⟩
        · exact ⟨hz,hd⟩
  have hd : Disjoint ((A \ {u,z}) ∩ D) ({u,z} ∩ D) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.1.2 hy.1
  have hsub : ((A \ {u,z}) ∩ D) ⊆ A ∩ D := fun x hx => ⟨hx.1.1,hx.2⟩
  have hpair : ({u,z} ∩ D).ncard = (if u ∈ D then 1 else 0)+(if z ∈ D then 1 else 0) := by
    by_cases huD : u ∈ D <;> by_cases hzD : z ∈ D
    · have he : ({u,z} ∩ D : Set S) = {u,z} := by ext x; simp only [Set.mem_inter_iff]; aesop
      rw [he,Set.ncard_pair huz]
      simp [huD,hzD]
    · have he : ({u,z} ∩ D : Set S) = {u} := by ext x; simp only [Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff]; aesop
      rw [he]; simp [huD,hzD]
    · have he : ({u,z} ∩ D : Set S) = {z} := by ext x; simp only [Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff]; aesop
      rw [he]; simp [huD,hzD]
    · have he : ({u,z} ∩ D : Set S) = ∅ := by ext x; simp only [Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false]; aesop
      rw [he]; simp [huD,hzD]
  have he : (A ∩ D).ncard = ((A \ {u,z}) ∩ D).ncard + ({u,z} ∩ D).ncard := by
    rw [hsplit]
    exact Set.ncard_union_eq hd (hf.subset hsub) (((Set.finite_singleton z).insert u).inter_of_left D)
  rw [he,hpair]
  omega

theorem actual_cheaper_side_row_drop
    {J : Type*} [Fintype J] [DecidableEq J]
    (v w : J) (hvw : v ≠ w) (old new F G offset : J → ℕ)
    (hpair : new w + 2 = old w)
    (hold : ∀ j, j ≠ v → j ≠ w → old j = F j + offset j)
    (hnew : ∀ j, j ≠ v → j ≠ w → new j ≤ G j + offset j)
    (hcheap : (∑ j, if j = v ∨ j = w then 0 else G j) ≤
      ∑ j, if j = v ∨ j = w then 0 else F j) :
    (∑ j, if v = j then 0 else new j) <
      ∑ j, if v = j then 0 else old j := by
  classical
  have hsplit (f : J → ℕ) :
      (∑ j, if v = j then 0 else f j) =
        f w + ∑ j, if j = v ∨ j = w then 0 else f j := by
    have he (j : J) : (if v = j then 0 else f j) =
        (if j = w then f w else 0) + (if j = v ∨ j = w then 0 else f j) := by
      by_cases hjv : j = v <;> by_cases hjw : j = w <;> simp_all [eq_comm]
    simp_rw [he,Finset.sum_add_distrib]
    simp
  have hOld : (∑ j, if j = v ∨ j = w then 0 else old j) =
      (∑ j, if j = v ∨ j = w then 0 else F j) +
      ∑ j, if j = v ∨ j = w then 0 else offset j := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h
    · simp
    · exact hold j (fun hjv => h (Or.inl hjv)) (fun hjw => h (Or.inr hjw))
  have hNew : (∑ j, if j = v ∨ j = w then 0 else new j) ≤
      (∑ j, if j = v ∨ j = w then 0 else G j) +
      ∑ j, if j = v ∨ j = w then 0 else offset j := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with h
    · simp
    · exact hnew j (fun hjv => h (Or.inl hjv)) (fun hjw => h (Or.inr hjw))
  rw [hsplit old,hsplit new,hOld]
  omega

end CurveComplex
