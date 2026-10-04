import RegionalDecreaseSupport

open CurveComplex Set Topology RegionalTotalDecrease
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

namespace RegionalNormalizationAccounting

/-- Each redraw contact is charged either to its unchanged original point or
to the original contact indexing its patch. One final contact per charged
patch suffices; disjoint patches and a no-triple condition are unnecessary. -/
theorem finite_ncard_le_of_contact_patch_cover
    {X : Type*} (old patched final : Set X) (Q : ↥patched → Set X)
    (hold : old.Finite) (hpatched : patched ⊆ old)
    (hcover : final ⊆ (old \ patched) ∪ ⋃ p, Q p)
    (hunique : ∀ p, (Q p).Subsingleton) :
    final.Finite ∧ final.ncard ≤ old.ncard := by
  classical
  have patch (x : X) (hx : x ∈ final) (he : x ∉ old \ patched) :
      ∃ p, x ∈ Q p := Set.mem_iUnion.mp ((hcover hx).resolve_left he)
  let charge : X → X := fun x =>
    if he : x ∈ old \ patched then x
    else if hx : x ∈ final then (patch x hx he).choose.val else x
  have hcharge : Set.MapsTo charge final old := by
    intro x hx
    by_cases he : x ∈ old \ patched
    · simpa only [charge,dite_eq_left he] using he.1
    · simpa only [charge,dite_eq_right he,dite_eq_left hx] using
        hpatched (patch x hx he).choose.property
  have hinj : Set.InjOn charge final := by
    intro x hx y hy hxy
    by_cases he : x ∈ old \ patched
    · by_cases hf : y ∈ old \ patched
      · simpa only [charge,dite_eq_left he,dite_eq_left hf] using hxy
      · have hh : x = (patch y hy hf).choose.val := by
          simpa only [charge,dite_eq_left he,dite_eq_right hf,dite_eq_left hy] using hxy
        exact (he.2 (hh ▸ (patch y hy hf).choose.property)).elim
    · by_cases hf : y ∈ old \ patched
      · have hh : (patch x hx he).choose.val = y := by
          simpa only [charge,dite_eq_right he,dite_eq_left hx,dite_eq_left hf] using hxy
        exact (hf.2 (hh ▸ (patch x hx he).choose.property)).elim
      · have hh : (patch x hx he).choose = (patch y hy hf).choose := by
          apply Subtype.ext
          simpa only [charge,dite_eq_right he,dite_eq_left hx,dite_eq_right hf,dite_eq_left hy] using hxy
        apply hunique (patch x hx he).choose (patch x hx he).choose_spec
        simpa only [hh] using (patch y hy hf).choose_spec
  exact ⟨Set.Finite.of_injOn hcharge hinj hold,
    Set.ncard_le_ncard_of_injOn charge hcharge hinj hold⟩

/-- The original invariant gives finite contacts on the literal augmented
family, with the observer at `none` and no claim on the diagonal. -/
theorem invariant_augmented_contacts_finite
    {X ι : Type*} [TopologicalSpace X]
    (r : ι → C(Interval,X)) (α : C(Interval,X)) (h : FamilyInvariant r α) :
    ∀ i j : Option ι, i ≠ j →
      (range (augmented r α i) ∩ range (augmented r α j)).Finite := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => exact h.2.2.2.2 j
  | some i =>
    cases j with
    | none =>
      change (range (r i) ∩ range α).Finite
      rw [inter_comm]
      exact h.2.2.2.2 i
    | some j => exact h.1 i j (fun he => hij (congrArg some he))

/-- The full finite family has only finitely many whole-range contact sites. -/
theorem finite_distinct_contact_locus
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    (a : κ → C(Interval,X))
    (hf : ∀ i j, i ≠ j → (range (a i) ∩ range (a j)).Finite) :
    (⋃ i, ⋃ j, if i = j then ∅ else range (a i) ∩ range (a j)).Finite := by
  classical
  exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => by
    split_ifs with hij
    · exact Set.finite_empty
    · exact hf i j hij

end RegionalNormalizationAccounting
