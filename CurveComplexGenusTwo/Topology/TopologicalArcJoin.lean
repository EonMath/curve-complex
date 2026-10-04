import Schoenflies.JordanClosed
import Schoenflies.Concatenate
import Schoenflies.Subarc
open Set unitInterval
namespace Schoenflies

/-- Loop erasure for two topological arcs: no polygonality hypothesis. -/
theorem exists_arc_in_union_of_arcs {A B : Set Plane} {a c b : Plane}
    (hA : IsArcBetween A a c) (hB : IsArcBetween B c b) (hab : a ≠ b) :
    ∃ C ⊆ A ∪ B, IsArcBetween C a b := by
  by_cases haB : a ∈ B
  · obtain ⟨C, hCB, hC⟩ := hB.isArc.exists_isArcBetween_subset haB hB.right_mem hab
    exact ⟨C, hCB.trans subset_union_right, hC⟩
  obtain ⟨f, hf, hi, hfr, hf0, hf1⟩ := hA
  let S : Set I := {t | f t ∈ B}
  have hc : Continuous (fun t : I => f t) := continuousOn_iff_continuous_domRestrict.mp hf
  have hSclosed : IsClosed S := hB.isArc.isCompact.isClosed.preimage hc
  have hSne : S.Nonempty := ⟨⟨1, by simp⟩, by simpa [S, hf1] using hB.left_mem⟩
  obtain ⟨t, htS, htmin⟩ := hSclosed.isCompact.exists_isLeast hSne
  have htB : f t ∈ B := htS
  have ht0 : 0 < (t : ℝ) := by
    by_contra h
    have heq : (t : ℝ) = 0 := le_antisymm (not_lt.mp h) t.property.1
    exact haB (by simpa [heq, hf0] using htB)
  let C : Set Plane := f '' Icc 0 (t : ℝ)
  have hC : IsArcBetween C a (f t) := by
    rw [← hf0]
    simpa [C, uIcc_of_le ht0.le] using
      isArcBetween_subarc_of_injOn_I hf hi (by simp) t.property (ne_of_lt ht0)
  have hCA : C ⊆ A := by
    rw [← hfr]
    exact image_mono (by intro s hs; exact ⟨hs.1, hs.2.trans t.property.2⟩)
  have hmeet : ∀ x ∈ C, x ∈ B → x = f t := by
    rintro x ⟨s, hs, rfl⟩ hsB
    have hsI : s ∈ I := ⟨hs.1, hs.2.trans t.property.2⟩
    have hts : (t : ℝ) ≤ s := htmin (show (⟨s, hsI⟩ : I) ∈ S from hsB)
    rw [le_antisymm hs.2 hts]
  by_cases htb : f t = b
  · exact ⟨C, hCA.trans subset_union_left, htb ▸ hC⟩
  obtain ⟨D, hDB, hD⟩ := hB.isArc.exists_isArcBetween_subset htB hB.right_mem htb
  exact ⟨C ∪ D, union_subset_union hCA hDB,
    hC.concatenate hD (fun x hx hxD => hmeet x hx (hDB hxD))⟩
end Schoenflies
#print axioms Schoenflies.exists_arc_in_union_of_arcs

namespace Schoenflies
/-- Two arbitrary topological access arcs can be joined through the connected
arc complement and simplified, giving a Jordan completion. Access need not be
polygonal or straight near the endpoints. -/
theorem jordan_completion_of_access_arcs
    {P E₁ E₂ : Set Plane} {a b u v : Plane}
    (hP : IsArcBetween P a b)
    (hE₁ : IsArcBetween E₁ a u) (hE₂ : IsArcBetween E₂ b v)
    (hu : u ∉ P) (hv : v ∉ P)
    (havoid₁ : E₁ \ {a} ⊆ Pᶜ) (havoid₂ : E₂ \ {b} ⊆ Pᶜ) :
    ∃ A : Set Plane, IsArcBetween A a b ∧
      A ∩ P = {a, b} ∧ IsJordanCurve (A ∪ P) := by
  have hab : a ≠ b := hP.ne
  have hjoin : ∃ A : Set Plane, IsArcBetween A a b ∧ A \ {a, b} ⊆ Pᶜ := by
    by_cases huv : u = v
    · obtain ⟨A, hAsub, hA⟩ := exists_arc_in_union_of_arcs hE₁ (huv ▸ hE₂.reverse) hab
      refine ⟨A, hA, ?_⟩
      intro x hx
      rcases hAsub hx.1 with hx₁ | hx₂
      · exact havoid₁ ⟨hx₁, fun h => hx.2 (Or.inl (by simpa using h))⟩
      · exact havoid₂ ⟨hx₂, fun h => hx.2 (Or.inr h)⟩
    · obtain ⟨Q, _, hQ, hQsub⟩ := arc_complement_poly hP.isArc huv hu hv
      have hav : a ≠ v := fun h => hv (h ▸ hP.left_mem)
      obtain ⟨C, hCsub, hC⟩ := exists_arc_in_union_of_arcs hE₁ hQ hav
      obtain ⟨A, hAsub, hA⟩ := exists_arc_in_union_of_arcs hC hE₂.reverse hab
      refine ⟨A, hA, ?_⟩
      intro x hx
      rcases hAsub hx.1 with hxC | hx₂
      · rcases hCsub hxC with hx₁ | hxQ
        · exact havoid₁ ⟨hx₁, fun h => hx.2 (Or.inl (by simpa using h))⟩
        · exact hQsub hxQ
      · exact havoid₂ ⟨hx₂, fun h => hx.2 (Or.inr h)⟩
  obtain ⟨A, hA, havoid⟩ := hjoin
  have hmeet : A ∩ P = {a, b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra h
      exact havoid ⟨hx.1, h⟩ hx.2
    · rintro x (rfl | rfl)
      · exact ⟨hA.left_mem, hP.left_mem⟩
      · exact ⟨hA.right_mem, hP.right_mem⟩
  refine ⟨A, hA, hmeet, IsJordanCurve.of_two_arcs hA hP.reverse ?_⟩
  intro x hxA hxP
  have := hmeet ▸ (show x ∈ A ∩ P from ⟨hxA, hxP⟩)
  simpa using this
end Schoenflies
#print axioms Schoenflies.jordan_completion_of_access_arcs
