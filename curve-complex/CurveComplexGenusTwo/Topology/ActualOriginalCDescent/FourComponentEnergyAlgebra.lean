import Mathlib.Data.Set.Card
import Mathlib.Tactic
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.CrosspairEnergy

namespace CurveComplex.HyperellipticModel

private theorem four_weighted_energy_eq_twice_union
    {E : Type} (A B : Fin 2 → Set E)
    (hA : Disjoint (A 0) (A 1)) (hB : Disjoint (B 0) (B 1))
    (hfin : ∀ i j, ((A i) ∩ (B j)).Finite) :
    (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
      if p = q then 0 else
        ((if p.1 then B p.2 else A p.2) ∩
          (if q.1 then B q.2 else A q.2)).ncard) =
      2 * (((A 0 ∪ A 1) ∩ (B 0 ∪ B 1)).ncard) := by
  classical
  have h00 : ((A 0) ∩ (B 0)).Finite := hfin 0 0
  have h01 : ((A 0) ∩ (B 1)).Finite := hfin 0 1
  have h10 : ((A 1) ∩ (B 0)).Finite := hfin 1 0
  have h11 : ((A 1) ∩ (B 1)).Finite := hfin 1 1
  have hAF : ((A 0) ∩ (A 1)).ncard = 0 := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hA]
    simp
  have hBF : ((B 0) ∩ (B 1)).ncard = 0 := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hB]
    simp
  have hAD : Disjoint ((A 0 ∩ B 0) ∪ (A 0 ∩ B 1))
      ((A 1 ∩ B 0) ∪ (A 1 ∩ B 1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      exact Set.disjoint_left.mp hA hx.1 hy.1
  have hB0 : Disjoint (A 0 ∩ B 0) (A 0 ∩ B 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hB hx.2 hy.2
  have hB1 : Disjoint (A 1 ∩ B 0) (A 1 ∩ B 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hB hx.2 hy.2
  have hsplit : (A 0 ∪ A 1) ∩ (B 0 ∪ B 1) =
      ((A 0 ∩ B 0) ∪ (A 0 ∩ B 1)) ∪
        ((A 1 ∩ B 0) ∪ (A 1 ∩ B 1)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [hsplit, Set.ncard_union_eq hAD (h00.union h01) (h10.union h11),
    Set.ncard_union_eq hB0 h00 h01,
    Set.ncard_union_eq hB1 h10 h11]
  simp only [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, hAF, hBF, Set.inter_comm]
  omega

theorem four_union_crosspair_eq_sum
    {E : Type} (A B : Fin 2 → Set E)
    (hA : Disjoint (A 0) (A 1)) (hB : Disjoint (B 0) (B 1))
    (hfin : ∀ i j, ((A i) ∩ (B j)).Finite) :
    ((A 0 ∪ A 1) ∩ (B 0 ∪ B 1)).ncard =
      ((A 0 ∩ B 0).ncard + (A 0 ∩ B 1).ncard) +
      ((A 1 ∩ B 0).ncard + (A 1 ∩ B 1).ncard) := by
  have hAD : Disjoint ((A 0 ∩ B 0) ∪ (A 0 ∩ B 1))
      ((A 1 ∩ B 0) ∪ (A 1 ∩ B 1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      exact Set.disjoint_left.mp hA hx.1 hy.1
  have hB0 : Disjoint (A 0 ∩ B 0) (A 0 ∩ B 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hB hx.2 hy.2
  have hB1 : Disjoint (A 1 ∩ B 0) (A 1 ∩ B 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hB hx.2 hy.2
  have hsplit : (A 0 ∪ A 1) ∩ (B 0 ∪ B 1) =
      ((A 0 ∩ B 0) ∪ (A 0 ∩ B 1)) ∪
        ((A 1 ∩ B 0) ∪ (A 1 ∩ B 1)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [hsplit, Set.ncard_union_eq hAD
    ((hfin 0 0).union (hfin 0 1)) ((hfin 1 0).union (hfin 1 1)),
    Set.ncard_union_eq hB0 (hfin 0 0) (hfin 0 1),
    Set.ncard_union_eq hB1 (hfin 1 0) (hfin 1 1)]

theorem four_weighted_energy_strict_implies_union_drop
    {E : Type} (A B A' B' : Fin 2 → Set E)
    (hA : Disjoint (A 0) (A 1)) (hB : Disjoint (B 0) (B 1))
    (hA' : Disjoint (A' 0) (A' 1)) (hB' : Disjoint (B' 0) (B' 1))
    (hfin : ∀ i j, ((A i) ∩ (B j)).Finite)
    (hfin' : ∀ i j, ((A' i) ∩ (B' j)).Finite)
    (hdrop :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then B' p.2 else A' p.2) ∩
            (if q.1 then B' q.2 else A' q.2)).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then B p.2 else A p.2) ∩
            (if q.1 then B q.2 else A q.2)).ncard)) :
    ((A' 0 ∪ A' 1) ∩ (B' 0 ∪ B' 1)).ncard <
      ((A 0 ∪ A 1) ∩ (B 0 ∪ B 1)).ncard := by
  rw [four_weighted_energy_eq_twice_union A' B' hA' hB' hfin',
    four_weighted_energy_eq_twice_union A B hA hB hfin] at hdrop
  omega

theorem paired_first_family_one_component_drop
    {E : Type} (deck : E → E) (hinv : ∀ x, deck (deck x) = x)
    (A0 A1 B0 B1 C0 C1 : Set E)
    (hDA : deck '' A0 = A1) (hDB : deck '' B0 = B1)
    (hDC : deck '' C0 = C1)
    (hAd : Disjoint A0 A1) (hBd : Disjoint B0 B1)
    (hMutAd : Disjoint C0 A1) (hNewAd : Disjoint C0 C1)
    (hOldFin : ∀ i j : Fin 2,
      ((![(A0), A1] i) ∩ (![B0, B1] j)).Finite)
    (hMutFin : ∀ j : Fin 2, (C0 ∩ (![B0, B1] j)).Finite)
    (hNewFin : ∀ j : Fin 2, (C1 ∩ (![B0, B1] j)).Finite)
    (hdrop :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![B0, B1] p.2) else (![C0, A1] p.2)) ∩
            (if q.1 then (![B0, B1] q.2) else (![C0, A1] q.2))).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![B0, B1] p.2) else (![A0, A1] p.2)) ∩
            (if q.1 then (![B0, B1] q.2) else (![A0, A1] q.2))).ncard)) :
    ((C0 ∪ C1) ∩ (B0 ∪ B1)).ncard <
      ((A0 ∪ A1) ∩ (B0 ∪ B1)).ncard := by
  have hMutFin' : ∀ i j : Fin 2,
      ((![(C0), A1] i) ∩ (![B0, B1] j)).Finite := by
    intro i j
    fin_cases i
    · exact hMutFin j
    · exact hOldFin 1 j
  have hMutDrop := four_weighted_energy_strict_implies_union_drop
    (![A0, A1]) (![B0, B1]) (![C0, A1]) (![B0, B1])
    hAd hBd hMutAd hBd hOldFin hMutFin' hdrop
  have hOldRows := paired_crosspair_ncard_symmetry deck hinv A0 A1 B0 B1 hDA hDB
  have hOldEq := paired_total_intersection_ncard deck hinv A0 A1 B0 B1
    hDA hDB hAd hBd (hOldFin 0 0) (hOldFin 0 1)
    (hOldFin 1 0) (hOldFin 1 1)
  have hMutEq := four_union_crosspair_eq_sum
    (![C0, A1]) (![B0, B1]) hMutAd hBd hMutFin'
  have hNewFin' : ∀ i j : Fin 2,
      ((![(C0), C1] i) ∩ (![B0, B1] j)).Finite := by
    intro i j
    fin_cases i
    · exact hMutFin j
    · exact hNewFin j
  have hNewEq := paired_total_intersection_ncard deck hinv C0 C1 B0 B1
    hDC hDB hNewAd hBd (hMutFin 0) (hMutFin 1)
    (hNewFin 0) (hNewFin 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hMutDrop hMutEq
  omega

theorem paired_second_family_one_component_drop
    {E : Type} (deck : E → E) (hinv : ∀ x, deck (deck x) = x)
    (A0 A1 B0 B1 C0 C1 : Set E)
    (hDA : deck '' A0 = A1) (hDB : deck '' B0 = B1)
    (hDC : deck '' C0 = C1)
    (hAd : Disjoint A0 A1) (hBd : Disjoint B0 B1)
    (hMutBd : Disjoint C0 B1) (hNewBd : Disjoint C0 C1)
    (hOldFin : ∀ i j : Fin 2,
      ((![(A0), A1] i) ∩ (![B0, B1] j)).Finite)
    (hMutFin : ∀ i : Fin 2, ((![A0, A1] i) ∩ C0).Finite)
    (hNewFin : ∀ i : Fin 2, ((![A0, A1] i) ∩ C1).Finite)
    (hdrop :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![C0, B1] p.2) else (![A0, A1] p.2)) ∩
            (if q.1 then (![C0, B1] q.2) else (![A0, A1] q.2))).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![B0, B1] p.2) else (![A0, A1] p.2)) ∩
            (if q.1 then (![B0, B1] q.2) else (![A0, A1] q.2))).ncard)) :
    ((A0 ∪ A1) ∩ (C0 ∪ C1)).ncard <
      ((A0 ∪ A1) ∩ (B0 ∪ B1)).ncard := by
  have hMutFin' : ∀ i j : Fin 2,
      ((![(A0), A1] i) ∩ (![C0, B1] j)).Finite := by
    intro i j
    fin_cases j
    · exact hMutFin i
    · exact hOldFin i 1
  have hMutDrop := four_weighted_energy_strict_implies_union_drop
    (![A0, A1]) (![B0, B1]) (![A0, A1]) (![C0, B1])
    hAd hBd hAd hMutBd hOldFin hMutFin' hdrop
  have hOldRows := paired_crosspair_ncard_symmetry deck hinv A0 A1 B0 B1 hDA hDB
  have hOldEq := paired_total_intersection_ncard deck hinv A0 A1 B0 B1
    hDA hDB hAd hBd (hOldFin 0 0) (hOldFin 0 1)
    (hOldFin 1 0) (hOldFin 1 1)
  have hMutEq := four_union_crosspair_eq_sum
    (![A0, A1]) (![C0, B1]) hAd hMutBd hMutFin'
  have hNewEq := paired_total_intersection_ncard deck hinv C0 C1 A0 A1
    hDC hDA hNewBd hAd
    (by rw [Set.inter_comm C0 A0]; simpa using hMutFin 0)
    (by rw [Set.inter_comm C0 A1]; simpa using hMutFin 1)
    (by rw [Set.inter_comm C1 A0]; simpa using hNewFin 0)
    (by rw [Set.inter_comm C1 A1]; simpa using hNewFin 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hMutDrop hMutEq
  rw [Set.inter_comm (C0 ∪ C1) (A0 ∪ A1)] at hNewEq
  simp only [Set.inter_comm C0 A0, Set.inter_comm C0 A1] at hNewEq
  omega

theorem paired_partner_crosspair_finite
    {E : Type} (deck : E → E) (hinv : ∀ x, deck (deck x) = x)
    (C0 C1 B0 B1 : Set E)
    (hDC : deck '' C0 = C1) (hDB : deck '' B0 = B1)
    (hFin0 : (C0 ∩ B0).Finite) (hFin1 : (C0 ∩ B1).Finite) :
    (C1 ∩ B0).Finite ∧ (C1 ∩ B1).Finite := by
  have hinj : Function.Injective deck := by
    intro x y h
    simpa only [hinv] using congrArg deck h
  have hBrev : deck '' B1 = B0 := by
    rw [← hDB, Set.image_image]
    simp [hinv]
  constructor
  · have h := hFin1.image deck
    rwa [Set.image_inter hinj, hDC, hBrev] at h
  · have h := hFin0.image deck
    rwa [Set.image_inter hinj, hDC, hDB] at h

end CurveComplex.HyperellipticModel
