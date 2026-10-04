import Mathlib

namespace CurveComplex.HyperellipticModel.ArcSurgery

private theorem two_direction_anchor_side_balance
    (aOff aSide bOff bSide aNew bNew : ℕ)
    (haMin : aOff + aSide ≤ aNew)
    (hbMin : bOff + bSide ≤ bNew)
    (haBound : aNew ≤ aOff + bSide)
    (hbBound : bNew ≤ bOff + aSide) :
    aSide = bSide := by
  omega

private theorem two_direction_incident_drop
    (aOff aSide bOff bSide aNew bNew aPairNew bPairNew pairOld : ℕ)
    (haBound : aNew ≤ aOff + bSide)
    (hbBound : bNew ≤ bOff + aSide)
    (haPairDrop : aPairNew < pairOld)
    (hbPairDrop : bPairNew < pairOld) :
    (aNew + aPairNew) + (bNew + bPairNew) <
      (aOff + aSide + pairOld) + (bOff + bSide + pairOld) := by
  omega

private theorem one_direction_incident_drop
    (aOff aSide bOff bSide aNew bNew aPairNew bPairNew pairOld : ℕ)
    (haBound : aNew ≤ aOff + bSide)
    (hbBound : bNew ≤ bOff + aSide)
    (haPairDrop : aPairNew < pairOld)
    (hbPairDrop : bPairNew < pairOld) :
    aNew + aPairNew < aOff + aSide + pairOld ∨
      bNew + bPairNew < bOff + bSide + pairOld := by
  have hsum := two_direction_incident_drop aOff aSide bOff bSide
    aNew bNew aPairNew bPairNew pairOld haBound hbBound haPairDrop hbPairDrop
  omega

theorem incident_row_split_at_selected_pair
    {I : Type*} [Fintype I] [DecidableEq I]
    (v w : I) (hvw : v ≠ w) (f : I → ℕ) :
    (∑ j ∈ Finset.univ.erase v, f j) =
      f w + ∑ j ∈ (Finset.univ.erase v).erase w, f j := by
  have hw : w ∈ (Finset.univ : Finset I).erase v :=
    Finset.mem_erase.mpr ⟨hvw.symm, Finset.mem_univ _⟩
  calc
    (∑ j ∈ Finset.univ.erase v, f j) =
        (∑ j ∈ (Finset.univ.erase v).erase w, f j) + f w :=
      (Finset.sum_erase_add (Finset.univ.erase v) f hw).symm
    _ = f w + ∑ j ∈ (Finset.univ.erase v).erase w, f j := by ac_rfl

theorem sum_except_two_eq_sum_remaining_subtype
    {I : Type*} [Fintype I] [DecidableEq I]
    (v w : I) (f : I → ℕ) :
    (∑ j ∈ (Finset.univ.erase v).erase w, f j) =
      ∑ j : {j : I // j ≠ v ∧ j ≠ w}, f j.val := by
  classical
  apply Finset.sum_subtype
  intro j
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

theorem sum_option_erase_none
    {J : Type*} [Fintype J] [DecidableEq J] (f : Option J → ℕ) :
    (∑ j ∈ (Finset.univ : Finset (Option J)).erase none, f j) =
      ∑ j : J, f (some j) := by
  classical
  have h := (Finset.sum_erase_add Finset.univ f (Finset.mem_univ (none : Option J)))
  rw [Fintype.sum_option] at h
  omega

theorem two_direction_finite_family_count_drop
    {J S : Type*} [Fintype J] [DecidableEq J]
    (anchorIndex : J) (a b aNew bNew aSide bSide : J → Set S)
    (haFinite : ∀ j, (a j).Finite)
    (hbFinite : ∀ j, (b j).Finite)
    (haBound : ∀ j, (aNew j).ncard ≤
      (a j \ aSide j).ncard + (b j ∩ bSide j).ncard)
    (hbBound : ∀ j, (bNew j).ncard ≤
      (b j \ bSide j).ncard + (a j ∩ aSide j).ncard)
    (haMin : (a anchorIndex).ncard ≤ (aNew anchorIndex).ncard)
    (hbMin : (b anchorIndex).ncard ≤ (bNew anchorIndex).ncard)
    (pairOld pairANew pairBNew : ℕ)
    (haPairDrop : pairANew < pairOld)
    (hbPairDrop : pairBNew < pairOld) :
    pairANew + ∑ j ∈ Finset.univ.erase anchorIndex, (aNew j).ncard <
        pairOld + ∑ j ∈ Finset.univ.erase anchorIndex, (a j).ncard ∨
    pairBNew + ∑ j ∈ Finset.univ.erase anchorIndex, (bNew j).ncard <
        pairOld + ∑ j ∈ Finset.univ.erase anchorIndex, (b j).ncard := by
  have haAll : (∑ j : J, (aNew j).ncard) ≤
      (∑ j : J, (a j \ aSide j).ncard) +
      (∑ j : J, (b j ∩ bSide j).ncard) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => haBound j)
  have hbAll : (∑ j : J, (bNew j).ncard) ≤
      (∑ j : J, (b j \ bSide j).ncard) +
      (∑ j : J, (a j ∩ aSide j).ncard) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hbBound j)
  have haPartition : (∑ j : J, (a j ∩ aSide j).ncard) +
      (∑ j : J, (a j \ aSide j).ncard) =
      ∑ j : J, (a j).ncard := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (haFinite j)
  have hbPartition : (∑ j : J, (b j ∩ bSide j).ncard) +
      (∑ j : J, (b j \ bSide j).ncard) =
      ∑ j : J, (b j).ncard := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (hbFinite j)
  have haSplit : (∑ j : J, (a j).ncard) =
      (∑ j ∈ Finset.univ.erase anchorIndex, (a j).ncard) +
      (a anchorIndex).ncard :=
    (Finset.sum_erase_add Finset.univ (fun j => (a j).ncard)
      (Finset.mem_univ anchorIndex)).symm
  have hbSplit : (∑ j : J, (b j).ncard) =
      (∑ j ∈ Finset.univ.erase anchorIndex, (b j).ncard) +
      (b anchorIndex).ncard :=
    (Finset.sum_erase_add Finset.univ (fun j => (b j).ncard)
      (Finset.mem_univ anchorIndex)).symm
  have haNewSplit : (∑ j : J, (aNew j).ncard) =
      (∑ j ∈ Finset.univ.erase anchorIndex, (aNew j).ncard) +
      (aNew anchorIndex).ncard :=
    (Finset.sum_erase_add Finset.univ (fun j => (aNew j).ncard)
      (Finset.mem_univ anchorIndex)).symm
  have hbNewSplit : (∑ j : J, (bNew j).ncard) =
      (∑ j ∈ Finset.univ.erase anchorIndex, (bNew j).ncard) +
      (bNew anchorIndex).ncard :=
    (Finset.sum_erase_add Finset.univ (fun j => (bNew j).ncard)
      (Finset.mem_univ anchorIndex)).symm
  omega

end CurveComplex.HyperellipticModel.ArcSurgery
