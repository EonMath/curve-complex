import ActualCover
import BranchData

namespace AlternatingSphereCover

/-- A representative on either closed hemisphere above an equatorial point. -/
def equatorRaw (p : Sphere) (hp : height p = 0) (north sheet : Bool) : Raw :=
  ⟨(p, north, sheet), by cases north <;> simp [hp]⟩

/-- The quotient's exact equatorial gluing rule: a positive seam arc swaps
the sheets, while a branch point identifies all four incident banks. -/
theorem equator_glue (p : Sphere) (hp : height p = 0) (s t : Bool) :
    (Quotient.mk setoid (equatorRaw p hp true s) : Total) =
      Quotient.mk setoid (equatorRaw p hp false t) ↔
      branch p ∨ t = s ^^ decide (0 < seamPolynomial p) := by
  rw [Quotient.eq]
  change Rel (equatorRaw p hp true s) (equatorRaw p hp false t) ↔ _
  simp [Rel, label, equatorRaw]
  by_cases h : 0 < seamPolynomial p <;> cases s <;> cases t <;> simp [h]

theorem equator_glue_positive (p : Sphere) (hp : height p = 0)
    (hb : ¬ branch p) (hpos : 0 < seamPolynomial p) (s t : Bool) :
    (Quotient.mk setoid (equatorRaw p hp true s) : Total) =
      Quotient.mk setoid (equatorRaw p hp false t) ↔ t = !s := by
  have h := equator_glue p hp s t
  cases s <;> cases t <;> simpa [hb, hpos] using h

theorem equator_glue_nonpositive (p : Sphere) (hp : height p = 0)
    (hb : ¬ branch p) (hpos : ¬ 0 < seamPolynomial p) (s t : Bool) :
    (Quotient.mk setoid (equatorRaw p hp true s) : Total) =
      Quotient.mk setoid (equatorRaw p hp false t) ↔ t = s := by
  simpa [hb, hpos] using equator_glue p hp s t

/-- Every total-space point is represented by one of the four closed
hemisphere sheets. -/
theorem total_four_hemisphere_quotient (z : Total) :
    ∃ p : Sphere, ∃ north sheet : Bool,
      ∃ hp : (if north then 0 ≤ height p else height p ≤ 0),
        z = Quotient.mk setoid (⟨(p, north, sheet), hp⟩ : Raw) := by
  induction z using Quotient.inductionOn with
  | h x =>
    refine ⟨x.val.1, x.val.2.1, x.val.2.2, x.property, ?_⟩
    rfl

/-- The unique quotient point over each of the six branch points. -/
noncomputable def ramificationPoint (i : Fin 6) : Total :=
  Classical.choose (projection_surjective (branchPoint i))

theorem projection_ramificationPoint (i : Fin 6) :
    projection (ramificationPoint i) = branchPoint i :=
  Classical.choose_spec (projection_surjective (branchPoint i))

theorem ramificationPoint_injective : Function.Injective ramificationPoint := by
  intro i j h
  apply branchPoint_injective
  rw [← projection_ramificationPoint i, ← projection_ramificationPoint j, h]

theorem fixed_iff_ramificationPoint (z : Total) :
    deck z = z ↔ z ∈ Set.range ramificationPoint := by
  rw [fixed_iff_branch, branch_iff_mem_range]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h := projection_ramificationPoint i
    have hb : branch (branchPoint i) :=
      (branch_iff_mem_range _).mpr ⟨i, rfl⟩
    exact (branch_fiber_unique hb).unique h hi.symm
  · rintro ⟨i, rfl⟩
    exact ⟨i, (projection_ramificationPoint i).symm⟩

noncomputable def ramificationFinset : Finset Total := by
  classical
  exact Finset.univ.image ramificationPoint

theorem ramificationFinset_card : ramificationFinset.card = 6 := by
  classical
  rw [ramificationFinset, Finset.card_image_of_injective _ ramificationPoint_injective]
  simp

theorem mem_ramificationFinset_iff_fixed (z : Total) :
    z ∈ ramificationFinset ↔ deck z = z := by
  classical
  rw [ramificationFinset, Finset.mem_image]
  simpa only [Finset.mem_univ, true_and, Set.mem_range] using
    (fixed_iff_ramificationPoint z).symm

theorem total_nonempty : Nonempty Total := ⟨ramificationPoint 0⟩

end AlternatingSphereCover
