import CurveComplexGenusTwo.Topology.CurveCombinatorics

namespace CurveComplexGenusTwo.Topology

theorem fareyAdjacent_symm {a b : FareySlope} :
    FareyAdjacent a b → FareyAdjacent b a := by
  cases a with
  | none =>
    cases b with
    | none => simp [FareyAdjacent]
    | some q => simpa [FareyAdjacent] using id
  | some p =>
    cases b with
    | none => simpa [FareyAdjacent] using id
    | some q =>
      intro h
      dsimp [FareyAdjacent] at h ⊢
      have heq : q.num * (p.den : ℤ) - p.num * (q.den : ℤ) =
          -(p.num * (q.den : ℤ) - q.num * (p.den : ℤ)) := by ring
      rw [heq, Int.natAbs_neg]
      exact h

theorem fareyAdjacent_irrefl (a : FareySlope) :
    ¬ FareyAdjacent a a := by
  cases a with
  | none => simp [FareyAdjacent]
  | some p => simp [FareyAdjacent]

theorem fareyAdjacent_none_int (n : ℤ) :
    FareyAdjacent none (some (n : ℚ)) := by
  simp [FareyAdjacent]

theorem fareyAdjacent_int_none (n : ℤ) :
    FareyAdjacent (some (n : ℚ)) none := by
  simp [FareyAdjacent]

theorem fareyAdjacent_int_iff (m n : ℤ) :
    FareyAdjacent (some (m : ℚ)) (some (n : ℚ)) ↔
      (m - n).natAbs = 1 := by
  simp [FareyAdjacent]

theorem fareyAdjacent_same_denominator
    (p q : ℚ) (hden : p.den = q.den)
    (hadj : FareyAdjacent (some p) (some q)) :
    p.den = 1 := by
  dsimp [FareyAdjacent] at hadj
  have hfactor : p.num * (q.den : ℤ) - q.num * (p.den : ℤ) =
      (p.num - q.num) * (p.den : ℤ) := by
    rw [← hden]
    ring
  rw [hfactor, Int.natAbs_mul] at hadj
  have hdvd : p.den ∣ 1 := by
    rw [← hadj]
    simpa using (dvd_mul_left p.den (p.num - q.num).natAbs)
  exact Nat.dvd_one.mp hdvd

theorem fareyAdjacent_denominator_ne
    (p q : ℚ) (hp : 1 < p.den) (hden : p.den = q.den) :
    ¬ FareyAdjacent (some p) (some q) := by
  intro h
  have hdone := fareyAdjacent_same_denominator p q hden h
  omega

/-- Infinity is placed in the denominator-one layer. -/
def fareyDenominator : FareySlope → ℕ
  | none => 1
  | some q => q.den

theorem fareyFace_atMostOne_of_denominator_gt_one
    (s : Finset FareySlope) (hs : FareyFace s)
    (d : ℕ) (hd : 1 < d)
    (a b : FareySlope) (ha : a ∈ s) (hb : b ∈ s)
    (hda : fareyDenominator a = d)
    (hdb : fareyDenominator b = d) : a = b := by
  by_contra hab
  have hadj : FareyAdjacent a b := hs ha hb hab
  cases a with
  | none =>
    simp [fareyDenominator] at hda
    omega
  | some p =>
    cases b with
    | none =>
      simp [fareyDenominator] at hdb
      omega
    | some q =>
      have hp : 1 < p.den := by
        change p.den = d at hda
        omega
      have hpq : p.den = q.den := by
        simpa [fareyDenominator] using hda.trans hdb.symm
      exact fareyAdjacent_denominator_ne p q hp hpq hadj

end CurveComplexGenusTwo.Topology
