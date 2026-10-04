import CurveComplexGenusTwo.Topology.CurveCombinatorics

namespace CurveComplexGenusTwo.Topology

private theorem farey_integer_parent_certificate (n : ℤ) (d : ℕ)
    (hd : 1 < d) (hc : Nat.Coprime n.natAbs d) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ b < d ∧
      a * (d : ℤ) - n * (b : ℤ) = 1 := by
  have hgcd : Int.gcd n (d : ℤ) = 1 := by
    simpa [Int.gcd, Int.natAbs_natCast] using hc
  let x := Int.gcdA n d
  let y := Int.gcdB n d
  have hbez : n * x + (d : ℤ) * y = 1 := by
    simpa [x, y, hgcd] using (Int.gcd_eq_gcd_ab n (d : ℤ)).symm
  let b : ℤ := (-x) % d
  let k : ℤ := (-x) / d
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (by omega)
  have hbd : b < d := Int.emod_lt _ (by omega)
  have hsplit : b + (d : ℤ) * k = -x := by
    simp only [b, k, Int.emod_def]
    ring
  have heq : (y - n * k) * (d : ℤ) - n * b = 1 := by
    calc
      _ = (d : ℤ) * y - n * (b + (d : ℤ) * k) := by ring
      _ = (d : ℤ) * y + n * x := by rw [hsplit]; ring
      _ = 1 := by linarith [hbez]
  have hbpos : 0 < b := by
    by_contra h
    have hbzero : b = 0 := by omega
    have hdvd : (d : ℤ) ∣ (1 : ℤ) := by
      refine ⟨y - n * k, ?_⟩
      rw [hbzero] at heq
      simpa only [mul_zero, sub_zero, mul_comm] using heq.symm
    have : d ∣ 1 := by exact_mod_cast hdvd
    have : d = 1 := Nat.dvd_one.mp this
    omega
  refine ⟨y - n * k, b.toNat, ?_, ?_, ?_⟩
  · omega
  · omega
  · simpa [Int.toNat_of_nonneg hb0] using heq

private theorem farey_integer_parent_unique (n : ℤ) (d : ℕ)
    (hc : Nat.Coprime n.natAbs d)
    {a c : ℤ} {b e : ℕ} (hb0 : 0 < b) (hbd : b < d)
    (he0 : 0 < e) (hed : e < d)
    (hab : a * (d : ℤ) - n * b = 1)
    (hce : c * (d : ℤ) - n * e = 1) : a = c ∧ b = e := by
  have hgcd : Int.gcd (d : ℤ) n = 1 := by
    simpa [Int.gcd, Int.natAbs_natCast] using hc.symm
  have hmul : (d : ℤ) ∣ ((b : ℤ) - e) * n := by
    refine ⟨a - c, ?_⟩
    nlinarith [hab, hce]
  have hdiv : (d : ℤ) ∣ (b : ℤ) - e :=
    Int.dvd_of_dvd_mul_left_of_gcd_one hmul hgcd
  have hdiff : (b : ℤ) - e = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdiv
    rw [abs_lt]
    constructor <;> omega
  constructor
  · have : (a - c) * (d : ℤ) = 0 := by
      calc
        _ = (a * (d : ℤ) - n * b) - (c * (d : ℤ) - n * e) +
            n * ((b : ℤ) - e) := by ring
        _ = 0 := by rw [hab, hce, hdiff]; ring
    have hdne : (d : ℤ) ≠ 0 := by omega
    have : a - c = 0 := (mul_eq_zero.mp this).resolve_right hdne
    omega
  · exact_mod_cast sub_eq_zero.mp hdiff

private theorem farey_det_coprime (a n : ℤ) (b d : ℕ)
    (hdet : a * (d : ℤ) - n * b = 1) :
    Nat.Coprime a.natAbs b := by
  have hdiv : (Int.gcd a (b : ℤ) : ℤ) ∣ (1 : ℤ) := by
    rw [← hdet]
    exact dvd_sub
      (dvd_mul_of_dvd_left (Int.gcd_dvd_left a (b : ℤ)) _)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right a (b : ℤ)) _)
  have hgcd : Int.gcd a (b : ℤ) = 1 := by
    have : Int.gcd a (b : ℤ) ∣ 1 := by exact_mod_cast hdiv
    exact Nat.dvd_one.mp this
  simpa [Int.gcd, Int.natAbs_natCast] using hgcd

/-- A reduced rational of denominator greater than one has an explicit Farey
parent pair. The last clause identifies the entire lower-denominator link. -/
theorem farey_parents_and_lower_link (p : ℚ) (hp : 1 < p.den) :
    ∃ l r : ℚ,
      l.den < p.den ∧ r.den < p.den ∧
      FareyAdjacent (some l) (some p) ∧
      FareyAdjacent (some r) (some p) ∧
      FareyAdjacent (some l) (some r) ∧
      l ≠ r ∧
      l.num + r.num = p.num ∧ l.den + r.den = p.den ∧
      (∀ s : FareySlope, (match s with | none => False | some q => q.den < p.den) →
        (FareyAdjacent s (some p) ↔ s = some l ∨ s = some r)) := by
  obtain ⟨a, b, hb0, hbd, hab⟩ :=
    farey_integer_parent_certificate p.num p.den hp p.reduced
  let c : ℤ := p.num - a
  let e : ℕ := p.den - b
  have he0 : 0 < e := by omega
  have hed : e < p.den := by omega
  have hsumden : b + e = p.den := by omega
  have hsumdet : c * (p.den : ℤ) - p.num * e = -1 := by
    dsimp [c, e]
    have hcast : ((p.den - b : ℕ) : ℤ) = (p.den : ℤ) - b := by omega
    rw [hcast]
    nlinarith [hab]
  have hrcoprime : Nat.Coprime c.natAbs e := by
    have h : (-c) * (p.den : ℤ) - (-p.num) * e = 1 := by
      nlinarith [hsumdet]
    simpa using farey_det_coprime (-c) (-p.num) e p.den h
  have hlcoprime : Nat.Coprime a.natAbs b :=
    farey_det_coprime a p.num b p.den hab
  let l : ℚ := (a : ℚ) / b
  let r : ℚ := (c : ℚ) / e
  have hlnum : l.num = a := by
    simpa [l] using Rat.num_div_eq_of_coprime (a := a) (b := (b : ℤ))
      (by omega) (by simpa using hlcoprime)
  have hlden : l.den = b := by
    have h := Rat.den_div_eq_of_coprime (a := a) (b := (b : ℤ))
      (by omega) (by simpa using hlcoprime)
    have : (l.den : ℤ) = b := by simpa [l] using h
    exact_mod_cast this
  have hrnum : r.num = c := by
    simpa [r] using Rat.num_div_eq_of_coprime (a := c) (b := (e : ℤ))
      (by omega) (by simpa using hrcoprime)
  have hrden : r.den = e := by
    have h := Rat.den_div_eq_of_coprime (a := c) (b := (e : ℤ))
      (by omega) (by simpa using hrcoprime)
    have : (r.den : ℤ) = e := by simpa [r] using h
    exact_mod_cast this
  have hla : FareyAdjacent (some l) (some p) := by
    dsimp [FareyAdjacent]
    rw [hlnum, hlden, hab]
    norm_num
  have hra : FareyAdjacent (some r) (some p) := by
    dsimp [FareyAdjacent]
    rw [hrnum, hrden, hsumdet]
    norm_num
  have hlr : FareyAdjacent (some l) (some r) := by
    dsimp [FareyAdjacent]
    rw [hlnum, hlden, hrnum, hrden]
    have : a * (e : ℤ) - c * (b : ℤ) = 1 := by
      dsimp [c, e]
      have hcast : ((p.den - b : ℕ) : ℤ) = (p.den : ℤ) - b := by omega
      rw [hcast]
      nlinarith [hab]
    rw [this]
    norm_num
  have hlne : l ≠ r := by
    intro h
    rw [h] at hlr
    simp [FareyAdjacent] at hlr
  refine ⟨l, r, ?_, ?_, hla, hra, hlr, hlne, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [hlnum, hrnum]
    dsimp [c]
    omega
  · rw [hlden, hrden]
    exact hsumden
  · intro s hs
    cases s with
    | none => simp at hs
    | some q =>
      simp only [Option.some.injEq]
      constructor
      · intro hq
        have hqden : q.den < p.den := hs
        dsimp [FareyAdjacent] at hq
        have hsign : q.num * (p.den : ℤ) - p.num * q.den = 1 ∨
            q.num * (p.den : ℤ) - p.num * q.den = -1 := by
          omega
        rcases hsign with hplus | hminus
        · have h := farey_integer_parent_unique p.num p.den p.reduced
            (by exact q.den_pos) hqden hb0 hbd hplus hab
          left
          apply Rat.ext
          · simpa [hlnum] using h.1
          · simpa [hlden] using h.2
        · have h := farey_integer_parent_unique (-p.num) p.den
            (by simpa using p.reduced) (by exact q.den_pos) hqden
            he0 hed (a := -q.num) (c := -c)
            (by nlinarith [hminus]) (by nlinarith [hsumdet])
          right
          apply Rat.ext
          · have : q.num = c := by omega
            simpa [hrnum] using this
          · simpa [hrden] using h.2
      · rintro (rfl | rfl)
        · exact hla
        · exact hra

theorem farey_infinity_not_lower_neighbor (p : ℚ) (hp : 1 < p.den) :
    ¬ FareyAdjacent none (some p) := by
  simpa [FareyAdjacent] using (show p.den ≠ 1 by omega)

theorem farey_lower_link_is_parent_edge (p : ℚ) (hp : 1 < p.den) :
    ∃ l r : ℚ, l ≠ r ∧ FareyFace ({some l, some r} : Finset FareySlope) ∧
      (l.num + r.num : ℚ) / (l.den + r.den : ℚ) = p ∧
      ∀ s : FareySlope,
        (FareyAdjacent s (some p) ∧
          (match s with | none => False | some q => q.den < p.den)) ↔
        s ∈ ({some l, some r} : Finset FareySlope) := by
  obtain ⟨l, r, hld, hrd, hlp, hrp, hlr, hne, hnum, hden, hlink⟩ :=
    farey_parents_and_lower_link p hp
  have hrl : FareyAdjacent (some r) (some l) := by
    dsimp [FareyAdjacent] at hlr ⊢
    rw [show r.num * (l.den : ℤ) - l.num * (r.den : ℤ) =
      -(l.num * (r.den : ℤ) - r.num * (l.den : ℤ)) by ring,
      Int.natAbs_neg]
    exact hlr
  have hface : FareyFace ({some l, some r} : Finset FareySlope) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hlr
    · exact hrl
    · exact False.elim (hab rfl)
  have hmed : (l.num + r.num : ℚ) / (l.den + r.den : ℚ) = p := by
    rw [← Int.cast_add, ← Nat.cast_add, hnum, hden]
    exact Rat.num_div_den p
  refine ⟨l, r, hne, hface, hmed, ?_⟩
  intro s
  constructor
  · rintro ⟨hadj, hsmall⟩
    have h := (hlink s hsmall).mp hadj
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  · intro hs
    have h : s = some l ∨ s = some r := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hs
    rcases h with rfl | rfl
    · exact ⟨hlp, hld⟩
    · exact ⟨hrp, hrd⟩

end CurveComplexGenusTwo.Topology
