import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace CurveComplex.HyperellipticModel

private theorem deck_image_inter_ncard
    {E : Type} (deck : E → E) (hinv : ∀ x, deck (deck x) = x)
    (A B : Set E) :
    (deck '' A ∩ deck '' B).ncard = (A ∩ B).ncard := by
  have hinj : Function.Injective deck := by
    intro x y h
    simpa only [hinv] using congrArg deck h
  rw [← Set.image_inter hinj]
  exact Set.ncard_image_of_injective _ hinj

theorem paired_crosspair_ncard_symmetry
    {E : Type} (deck : E → E) (hinv : ∀ x, deck (deck x) = x)
    (A0 A1 B0 B1 : Set E)
    (hA : deck '' A0 = A1) (hB : deck '' B0 = B1) :
    (A0 ∩ B0).ncard = (A1 ∩ B1).ncard ∧
      (A0 ∩ B1).ncard = (A1 ∩ B0).ncard := by
  have hA' : deck '' A1 = A0 := by
    rw [← hA, Set.image_image]
    simp [hinv]
  have hB' : deck '' B1 = B0 := by
    rw [← hB, Set.image_image]
    simp [hinv]
  constructor
  · simpa only [hA, hB] using (deck_image_inter_ncard deck hinv A0 B0).symm
  · simpa only [hA, hB'] using (deck_image_inter_ncard deck hinv A0 B1).symm

theorem paired_total_intersection_ncard
    {E : Type} (deck : E → E) (hinv : ∀ x, deck (deck x) = x)
    (A0 A1 B0 B1 : Set E)
    (hA : deck '' A0 = A1) (hB : deck '' B0 = B1)
    (hAd : Disjoint A0 A1) (hBd : Disjoint B0 B1)
    (h00 : (A0 ∩ B0).Finite) (h01 : (A0 ∩ B1).Finite)
    (h10 : (A1 ∩ B0).Finite) (h11 : (A1 ∩ B1).Finite) :
    ((A0 ∪ A1) ∩ (B0 ∪ B1)).ncard =
      2 * ((A0 ∩ B0).ncard + (A0 ∩ B1).ncard) := by
  have hd01 : Disjoint (A0 ∩ B0) (A0 ∩ B1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hBd hx.2 hy.2
  have hd23 : Disjoint (A1 ∩ B0) (A1 ∩ B1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hBd hx.2 hy.2
  have hdRows : Disjoint ((A0 ∩ B0) ∪ (A0 ∩ B1))
      ((A1 ∩ B0) ∪ (A1 ∩ B1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      exact Set.disjoint_left.mp hAd hx.1 hy.1
  have hSplit : (A0 ∪ A1) ∩ (B0 ∪ B1) =
      ((A0 ∩ B0) ∪ (A0 ∩ B1)) ∪ ((A1 ∩ B0) ∪ (A1 ∩ B1)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [hSplit,
    Set.ncard_union_eq hdRows (h00.union h01) (h10.union h11),
    Set.ncard_union_eq hd01 h00 h01,
    Set.ncard_union_eq hd23 h10 h11]
  obtain ⟨hdiag, hoff⟩ := paired_crosspair_ncard_symmetry deck hinv A0 A1 B0 B1 hA hB
  omega

theorem paired_disk_boundary_contacts_finite
    {E : Type} (A0 A1 B0 B1 F G : Set E)
    (hF : F ⊆ A0) (hG : G ⊆ B0)
    (h01 : (A0 ∩ B1).Finite) (h10 : (A1 ∩ B0).Finite) :
    ((F ∩ B1) ∪ (G ∩ A1)).Finite := by
  have hFB : (F ∩ B1).Finite := h01.subset (Set.inter_subset_inter_left _ hF)
  have hGA : (G ∩ A1).Finite := by
    apply h10.subset
    intro x hx
    exact ⟨hx.2,hG hx.1⟩
  exact hFB.union hGA

theorem strict_crosspair_count_of_subdisk_missing_corner
    {E : Type} (X D D' : Set E)
    (hX : X.Finite) (hsub : D' ⊆ D)
    (x : E) (hx : x ∈ X ∩ D) (hmiss : x ∉ D') :
    (X ∩ D').ncard < (X ∩ D).ncard := by
  apply Set.ncard_lt_ncard
  · apply Set.ssubset_iff_subset_ne.mpr
    constructor
    · exact Set.inter_subset_inter_right _ hsub
    · intro heq
      exact hmiss (heq ▸ hx).2
  · exact hX.subset Set.inter_subset_left

end CurveComplex.HyperellipticModel
