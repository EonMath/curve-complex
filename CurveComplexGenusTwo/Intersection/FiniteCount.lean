import Mathlib

/-!
Finite-set count underlying Lemma 5.1. The branch-cover geometry must establish
the fiber hypotheses for its actual projection map before applying this lemma.
-/

namespace CurveComplex.Intersection

variable {S C : Type*} (π : C → S) (B : Set S)

/-- A branched double cover has one point over each branch point and two over
each ordinary point. This is the precise fiber-count part of the local model. -/
def HasBranchFiberCounts : Prop :=
  (∀ x ∈ B, (π ⁻¹' {x}).ncard = 1) ∧
  (∀ x ∉ B, (π ⁻¹' {x}).ncard = 2)

/-- A marked ambient isotopy fixes the endpoint set of any arc. Its geometric
application uses the endpoint image law for ambient images of arcs. -/
theorem endpoint_image_fixed
    (f : S → S) (hf : ∀ b ∈ B, f b = b)
    (endpoints : Set S) (hends : endpoints ⊆ B) :
    f '' endpoints = endpoints := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [hf y (hends hy)] using hy
  · intro hx
    exact ⟨x, hx, hf x (hends hx)⟩

/-- The projection restricts to a bijection between ramification points and
branch points. For the genus-two cover this is `π|W : W ≃ B` in Lemma 2.10. -/
theorem branch_restriction_bijective
    (hbranch : ∀ b ∈ B, ∃! w : C, π w = b) :
    Function.Bijective
      (fun w : {w : C // π w ∈ B} =>
        (⟨π w.val, w.property⟩ : {b : S // b ∈ B})) := by
  constructor
  · intro w₁ w₂ heq
    apply Subtype.ext
    have hp : π w₁.val = π w₂.val := congrArg Subtype.val heq
    obtain ⟨u, hu, huniq⟩ := hbranch (π w₁.val) w₁.property
    exact (huniq w₁.val rfl).trans (huniq w₂.val hp.symm).symm
  · intro b
    obtain ⟨w, hw, _⟩ := hbranch b.val b.property
    exact ⟨⟨w, hw ▸ b.property⟩, Subtype.ext hw⟩

/-- The intersection of two full inverse images is the full inverse image of
the intersection. No transversality is needed for this set identity. -/
theorem preimage_intersection (α β : Set S) :
    (π ⁻¹' α) ∩ (π ⁻¹' β) = π ⁻¹' (α ∩ β) := by
  exact (Set.preimage_inter).symm

/-- The numerical content of Lemma 5.1, with its geometric hypotheses exposed:
the intersection downstairs is finite, its marked points are precisely the
shared endpoints, and every unmarked intersection lies in both interiors. -/
theorem local_count_of_fibers
    (α β interiorα interiorβ : Set S)
    (hfinite : (α ∩ β).Finite)
    (hdecomp : α ∩ β =
      (interiorα ∩ interiorβ) ∪ (α ∩ β ∩ B))
    (hdisj : Disjoint (interiorα ∩ interiorβ) B)
    (hπ : HasBranchFiberCounts π B) :
    ((π ⁻¹' α) ∩ (π ⁻¹' β)).ncard =
      2 * (interiorα ∩ interiorβ).ncard + (α ∩ β ∩ B).ncard := by
  classical
  let I := interiorα ∩ interiorβ
  let E := α ∩ β ∩ B
  have hIfin : I.Finite := hfinite.subset (by rw [hdecomp]; exact Set.subset_union_left)
  have hEfin : E.Finite := hfinite.subset (by intro x hx; exact hx.1)
  have hIE : Disjoint I E := hdisj.mono_right (by intro x hx; exact hx.2)
  have hsplit : hfinite.toFinset = hIfin.toFinset ∪ hEfin.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_union]
    rw [hdecomp]
    rfl
  have hfiber (x : S) (hx : x ∈ α ∩ β) : (π ⁻¹' {x}).Finite := by
    by_cases hB : x ∈ B
    · exact Set.finite_of_ncard_pos (by rw [hπ.1 x hB]; omega)
    · exact Set.finite_of_ncard_pos (by rw [hπ.2 x hB]; omega)
  have hcount : (π ⁻¹' (α ∩ β)).ncard =
      ∑ x ∈ hfinite.toFinset, (π ⁻¹' {x}).ncard := by
    convert Finset.card_preimage_eq_sum_card_image_eq
      (s := hfinite.toFinset) (f := π) (by
        intro x hx
        simpa only [Set.preimage, Set.mem_singleton_iff] using
          hfiber x (by simpa using hx)) using 1
    · simp
    · apply Finset.sum_congr rfl
      intro x hx
      rfl
  rw [preimage_intersection, hcount, hsplit, Finset.sum_union]
  · have hI : (∑ x ∈ hIfin.toFinset, (π ⁻¹' {x}).ncard) = 2 * I.ncard := by
      calc
        _ = ∑ x ∈ hIfin.toFinset, 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hπ.2 x (by
            intro hB
            exact Set.disjoint_left.mp hdisj (by simpa [I] using hx) hB)
        _ = 2 * I.ncard := by simp [Set.ncard_eq_toFinset_card I hIfin, mul_comm]
    have hE : (∑ x ∈ hEfin.toFinset, (π ⁻¹' {x}).ncard) = E.ncard := by
      calc
        _ = ∑ x ∈ hEfin.toFinset, 1 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hπ.1 x (by have := (by simpa using hx : x ∈ E); exact this.2)
        _ = E.ncard := by simp [Set.ncard_eq_toFinset_card E hEfin]
    simp [hI, hE, I, E]
  · simpa only [Set.Finite.disjoint_toFinset] using hIE

/-- For two distinct two-element endpoint sets, the number of shared
endpoints is at most one. This is the finite-set part of §6.1. -/
theorem endpoint_count_le_one_iff_ne
    [DecidableEq S] (a b : Finset S) (ha : a.card = 2) (hb : b.card = 2) :
    (a ∩ b).card ≤ 1 ↔ a ≠ b := by
  constructor
  · intro h hab
    subst b
    simp [ha] at h
  · intro h
    have hsub : a ∩ b ⊆ a := Finset.inter_subset_left
    have hle : (a ∩ b).card ≤ 2 := ha ▸ Finset.card_le_card hsub
    rcases lt_or_eq_of_le hle with hlt | heq
    · omega
    · have : a ∩ b = a := Finset.eq_of_subset_of_card_le hsub (by omega)
      have hab : a ⊆ b := by simpa using congrArg (fun s : Finset S => s ⊆ b) this
      exact False.elim (h (Finset.eq_of_subset_of_card_le hab (by omega)))

/-- The arithmetic consequence used in Corollary 5.7. -/
theorem intersection_le_one_iff (j e i : ℕ)
    (hformula : i = 2 * j + e) :
    i ≤ 1 ↔ j = 0 ∧ e ≤ 1 := by
  omega

end CurveComplex.Intersection
