import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualPartitionedSublevelEuler
import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseRegularValueWindows
import Mathlib.Data.Finset.Sort

open Set

noncomputable section

private theorem ordered_critical_values_partition
    {E : Type*} [DecidableEq E] (F : E → ℝ) (Z : Finset E) :
    ∃ (N : ℕ) (v : Fin N ↪o ℝ) (S : ℕ → Finset E),
      (∀ i (hi : i < N) q, q ∈ S i ↔ q ∈ Z ∧ F q = v ⟨i, hi⟩) ∧
      Set.PairwiseDisjoint (↑(Finset.range N)) S ∧
      (Finset.range N).biUnion S = Z ∧
      (∀ q ∈ Z, ∃ i : Fin N, F q = v i) ∧
      ∀ i : Fin N, ∃ q ∈ Z, F q = v i := by
  classical
  let V := Z.image F
  let N := V.card
  let v : Fin N ↪o ℝ := V.orderEmbOfFin rfl
  let S : ℕ → Finset E := fun i => if hi : i < N then
    Z.filter (fun q => F q = v ⟨i, hi⟩) else ∅
  have hS (i : ℕ) (hi : i < N) (q : E) :
      q ∈ S i ↔ q ∈ Z ∧ F q = v ⟨i, hi⟩ := by simp [S, hi]
  have hvalues (q : E) (hq : q ∈ Z) : ∃ i : Fin N, F q = v i := by
    let a : V := ⟨F q, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    refine ⟨(V.orderIsoOfFin rfl).symm a, ?_⟩
    exact (congrArg Subtype.val ((V.orderIsoOfFin rfl).apply_symm_apply a)).symm
  refine ⟨N, v, S, hS, ?_, ?_, hvalues, ?_⟩
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro q hqi hqj
    have hv := (hS i (Finset.mem_range.mp hi) q).mp hqi
    have hw := (hS j (Finset.mem_range.mp hj) q).mp hqj
    have he := v.injective (hv.2.symm.trans hw.2)
    exact hij (congrArg Fin.val he)
  · ext q
    constructor
    · intro hq
      obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp hq
      exact ((hS i (Finset.mem_range.mp hi) q).mp hqi).1
    · intro hq
      obtain ⟨i, hi⟩ := hvalues q hq
      exact Finset.mem_biUnion.mpr ⟨i.val, Finset.mem_range.mpr i.isLt,
        (hS i.val i.isLt q).mpr ⟨hq, hi⟩⟩
  · intro i
    exact Finset.mem_image.mp (V.orderEmbOfFin_mem rfl i)

#print axioms ordered_critical_values_partition

private theorem ordered_values_separating_cuts
    {N : ℕ} (hN : 0 < N) (v : Fin N ↪o ℝ) (A B : ℝ)
    (hA : ∀ i : Fin N, A < v i) (hB : ∀ i : Fin N, v i < B) :
    ∃ a : ℕ → ℝ, a 0 = A ∧ a N = B ∧
      ∀ i (hi : i < N), a i < v ⟨i, hi⟩ ∧ v ⟨i, hi⟩ < a (i + 1) ∧
        ∀ j : Fin N, v j ∈ Icc (a i) (a (i + 1)) ↔ j.val = i := by
  let a : ℕ → ℝ := fun i => if h0 : i = 0 then A else if h : i < N then
    (v ⟨i - 1, by omega⟩ + v ⟨i, h⟩) / 2 else B
  have hleft (i : ℕ) (hi : i < N) : a i < v ⟨i, hi⟩ := by
    by_cases h0 : i = 0
    · simp only [a, dite_eq_left h0]
      exact hA _
    · simp only [a, dite_eq_right h0, dite_eq_left hi]
      have hm : v ⟨i - 1, by omega⟩ < v ⟨i, hi⟩ :=
        v.strictMono (by change i - 1 < i; omega)
      linarith
  have hright (i : ℕ) (hi : i < N) : v ⟨i, hi⟩ < a (i + 1) := by
    have h0 : i + 1 ≠ 0 := by omega
    by_cases h : i + 1 < N
    · simp only [a, dite_eq_right h0, dite_eq_left h, Nat.add_sub_cancel]
      have hm : v ⟨i, hi⟩ < v ⟨i + 1, h⟩ :=
        v.strictMono (by change i < i + 1; omega)
      linarith
    · simp only [a, dite_eq_right h0, dite_eq_right h]
      exact hB _
  refine ⟨a, by simp [a], by simp [a, ne_of_gt hN], ?_⟩
  intro i hi
  refine ⟨hleft i hi, hright i hi, ?_⟩
  intro j
  constructor
  · intro hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hji | hij
    · have h0 : i ≠ 0 := by omega
      have hprev : v j ≤ v ⟨i - 1, by omega⟩ :=
        v.monotone (by change j.val ≤ i - 1; omega)
      have hlt : v ⟨i - 1, by omega⟩ < v ⟨i, hi⟩ :=
        v.strictMono (by change i - 1 < i; omega)
      have ha := hj.1
      simp only [a, dite_eq_right h0, dite_eq_left hi] at ha
      linarith
    · have h0 : i + 1 ≠ 0 := by omega
      have hin : i + 1 < N := by omega
      have hnext : v ⟨i + 1, hin⟩ ≤ v j :=
        v.monotone (by change i + 1 ≤ j.val; omega)
      have hlt : v ⟨i, hi⟩ < v ⟨i + 1, hin⟩ :=
        v.strictMono (by change i < i + 1; omega)
      have ha := hj.2
      simp only [a, dite_eq_right h0, dite_eq_left hin, Nat.add_sub_cancel] at ha
      linarith
  · intro he
    have hj : j = ⟨i, hi⟩ := Fin.ext he
    rw [hj]
    exact ⟨(hleft i hi).le, (hright i hi).le⟩

#print axioms ordered_values_separating_cuts

private theorem retained_nonempty_critical_value_windows
    {E : Type*} [DecidableEq E] (F : E → ℝ) (Z : Finset E) (hZ : Z.Nonempty)
    (A B : ℝ) (hA : ∀ q ∈ Z, A < F q) (hB : ∀ q ∈ Z, F q < B) :
    ∃ (N : ℕ) (_ : 0 < N) (v : Fin N ↪o ℝ)
      (S : ℕ → Finset E) (a : ℕ → ℝ) (η : Fin N → ℝ),
      a 0 = A ∧ a N = B ∧
      (∀ i (hi : i < N) q, q ∈ S i ↔ q ∈ Z ∧ F q = v ⟨i, hi⟩) ∧
      Set.PairwiseDisjoint (↑(Finset.range N)) S ∧
      (Finset.range N).biUnion S = Z ∧
      (∀ i : Fin N, 0 < η i ∧ a i.val < v i - η i ∧
        v i + η i < a (i.val + 1)) ∧
      (∀ i : Fin N, ∀ q ∈ Z,
        F q ∈ Icc (a i.val) (a (i.val + 1)) ↔ q ∈ S i.val) ∧
      ∀ i : Fin N, ∀ ε : ℝ, 0 < ε → ε < η i →
        (∀ q ∈ Z, F q ∈ Icc (v i - η i) (v i + η i) ↔ q ∈ S i.val) ∧
        (∀ q ∈ Z, F q ∉ Icc (a i.val) (v i - ε)) ∧
        (∀ q ∈ Z, F q ∉ Icc (v i + ε) (a (i.val + 1))) := by
  classical
  obtain ⟨N, v, S, hS, hd, hc, hvalues, hsurj⟩ := ordered_critical_values_partition F Z
  obtain ⟨q, hq⟩ := hZ
  obtain ⟨j, _⟩ := hvalues q hq
  have hN : 0 < N := Nat.zero_lt_of_lt j.isLt
  have hAv (i : Fin N) : A < v i := by
    obtain ⟨q, hq, he⟩ := hsurj i
    rw [← he]
    exact hA q hq
  have hBv (i : Fin N) : v i < B := by
    obtain ⟨q, hq, he⟩ := hsurj i
    rw [← he]
    exact hB q hq
  obtain ⟨a, ha0, haN, hacut⟩ := ordered_values_separating_cuts hN v A B hAv hBv
  let η : Fin N → ℝ := fun i =>
    min ((v i - a i.val) / 2) ((a (i.val + 1) - v i) / 2)
  have hη (i : Fin N) : 0 < η i ∧ a i.val < v i - η i ∧
      v i + η i < a (i.val + 1) := by
    obtain ⟨hl, hr, _⟩ := hacut i.val i.isLt
    have he : 0 < η i := by dsimp [η]; positivity
    have hl' := min_le_left ((v i - a i.val) / 2) ((a (i.val + 1) - v i) / 2)
    have hr' := min_le_right ((v i - a i.val) / 2) ((a (i.val + 1) - v i) / 2)
    dsimp [η] at he ⊢
    exact ⟨he, by linarith, by linarith⟩
  have hcut (i : Fin N) (q : E) (hq : q ∈ Z) :
      F q ∈ Icc (a i.val) (a (i.val + 1)) ↔ q ∈ S i.val := by
    obtain ⟨j, hj⟩ := hvalues q hq
    rw [hj, (hacut i.val i.isLt).2.2 j, hS i.val i.isLt q]
    constructor
    · intro he
      exact ⟨hq, hj.trans (congrArg v (Fin.ext he))⟩
    · intro he
      exact congrArg Fin.val (v.injective (hj.symm.trans he.2))
  refine ⟨N, hN, v, S, a, η, ha0, haN, hS, hd, hc, hη, hcut, ?_⟩
  intro i ε hε hεη
  obtain ⟨hiη, hil, hir⟩ := hη i
  have hnear (q : E) (hq : q ∈ Z) :
      F q ∈ Icc (v i - η i) (v i + η i) ↔ q ∈ S i.val := by
    constructor
    · intro hn
      exact (hcut i q hq).mp ⟨by linarith [hn.1], by linarith [hn.2]⟩
    · intro hs
      have he := ((hS i.val i.isLt q).mp hs).2
      rw [he]
      exact ⟨by linarith, by linarith⟩
  refine ⟨hnear, ?_, ?_⟩
  · intro q hq hn
    have hs := (hcut i q hq).mp ⟨hn.1, by linarith [hn.2]⟩
    have he := ((hS i.val i.isLt q).mp hs).2
    linarith [hn.2]
  · intro q hq hn
    have hs := (hcut i q hq).mp ⟨by linarith [hn.1], hn.2⟩
    have he := ((hS i.val i.isLt q).mp hs).2
    linarith [hn.1]

#print axioms retained_nonempty_critical_value_windows
