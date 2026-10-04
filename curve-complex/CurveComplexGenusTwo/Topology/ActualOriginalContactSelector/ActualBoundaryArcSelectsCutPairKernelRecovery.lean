import Schoenflies.GeneralCrosscut
import Schoenflies.FaceCyclesProof
namespace CurveComplex.LocalSurgery
open Set Schoenflies
/-- Extracts the boundary-arc choice already proved locally in CrosscutEncloses. -/
theorem actualBoundaryArcSelectsCutPair {C A : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A p q) (hAC : A⊆C) :
    ∃ B,IsCutPair C p q A B := by
  have hpq : p≠q := by
    obtain ⟨f,hc,hi,him,hp,hq⟩ := hA
    intro he
    have hh := hi (by norm_num) (by norm_num) (hp.trans (he.trans hq.symm))
    norm_num at hh
  obtain ⟨B₁,B₂,hB1,hB2,hBunion,hBinter⟩ := hC.two_arcs
    (hAC hA.left_mem) (hAC hA.right_mem) hpq
  have key : ∀ A : Set Plane,IsArcBetween A p q → A⊆C → A⊆B₁ ∨ A⊆B₂ := by
    intro A hAar hAC
    obtain ⟨hconn, hne⟩ := hAar.preconnected_diff
    have hsub : A \ {p, q} ⊆ B₁ᶜ ∪ B₂ᶜ := by
      intro w hw
      by_cases h1 : w ∈ B₁
      · by_cases h2 : w ∈ B₂
        · exact absurd (show w ∈ ({p, q} : Set Plane) by rw [← hBinter]; exact ⟨h1, h2⟩) hw.2
        · exact Or.inr h2
      · exact Or.inl h1
    have hnone : ¬ ((A \ {p, q}) ∩ (B₁ᶜ ∩ B₂ᶜ)).Nonempty := by
      rintro ⟨w, hw, h1, h2⟩
      have hwC : w ∈ C := hAC hw.1
      rw [← hBunion] at hwC
      exact hwC.elim h1 h2
    have hends : ∀ B : Set Plane, p ∈ B → q ∈ B → A \ {p, q} ⊆ B → A ⊆ B := by
      intro B hpB hqB hsub' w hw
      by_cases hwpq : w ∈ ({p, q} : Set Plane)
      · rcases hwpq with rfl | rfl
        exacts [hpB, hqB]
      · exact hsub' ⟨hw, hwpq⟩
    by_cases hcase : ((A \ {p, q}) ∩ B₁ᶜ).Nonempty
    · refine Or.inr (hends B₂ hB2.left_mem hB2.right_mem fun w hw => ?_)
      by_contra hwB2
      exact hnone (hconn _ _ hB1.isArc.isClosed.isOpen_compl hB2.isArc.isClosed.isOpen_compl
        hsub hcase ⟨w, hw, hwB2⟩)
    · refine Or.inl (hends B₁ hB1.left_mem hB1.right_mem fun w hw => ?_)
      by_contra hwB1
      exact hcase ⟨w, hw, hwB1⟩
  rcases key A hA hAC with hsub | hsub
  · have he : A=B₁ := hB1.eq_of_subset hA hsub
    subst A
    exact ⟨B₂,hB1,hB2,hBunion,hBinter⟩
  · have he : A=B₂ := hB2.eq_of_subset hA hsub
    subst A
    exact ⟨B₁,hB2,hB1,by simpa only [union_comm] using hBunion,
      by simpa only [inter_comm] using hBinter⟩
end CurveComplex.LocalSurgery
