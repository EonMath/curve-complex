import CurveComplexGenusTwo.Topology.FareyScheduledFinite

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

theorem fareySchedulePhase_lower (n : ℕ) (hn : 0 < n) :
    fareySchedulePhase n
        ⟨1 / ((n + 1 : ℕ) : ℝ), by
          constructor
          · positivity
          · apply (div_le_iff₀ (by positivity)).2
            norm_num⟩ =
      ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  dsimp [fareySchedulePhase]
  have hnR : (0 : ℝ) < n := by positivity
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hcalc :
      (n : ℝ) * (n + 1) * (1 / ((n + 1 : ℕ) : ℝ)) - n = 0 := by
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
    field_simp
    ring
  rw [hcalc]
  norm_num

theorem fareySchedulePhase_upper (n : ℕ) (hn : 0 < n) :
    fareySchedulePhase n
        ⟨1 / (n : ℝ), by
          constructor
          · positivity
          · apply (div_le_iff₀ (by positivity)).2
            simpa using (show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)⟩ =
      ⟨1, by norm_num⟩ := by
  apply Subtype.ext
  dsimp [fareySchedulePhase]
  have hnR : (0 : ℝ) < n := by positivity
  have hcalc : (n : ℝ) * (n + 1) * (1 / (n : ℝ)) - n = 1 := by
    field_simp
    ring
  rw [hcalc]
  norm_num

theorem fareyFiniteSchedule_window_lower (n : ℕ) (x : fareyStage (n + 2)) :
    fareyFiniteSchedule (n + 2) x
        ⟨1 / ((n + 3 : ℕ) : ℝ), by
          constructor
          · positivity
          · apply (div_le_iff₀ (by positivity)).2
            norm_num
            linarith
            ⟩ = x.1 := by
  have hle : (1 / ((n + 3 : ℕ) : ℝ) : ℝ) ≤
      1 / ((n + 3 : ℕ) : ℝ) := le_rfl
  simp only [fareyFiniteSchedule, hle, ↓reduceIte]

theorem fareyFiniteSchedule_window_upper (n : ℕ) (x : fareyStage (n + 2))
    (t : ConeTime) (ht : (t : ℝ) = 1 / ((n + 2 : ℕ) : ℝ)) :
    fareyFiniteSchedule (n + 2) x t =
      fareyStageStep (n + 2) (by omega) x ⟨1, by norm_num⟩ := by
  have hnot : ¬ ((t : ℝ) ≤ 1 / ((n + 3 : ℕ) : ℝ)) := by
    rw [ht]
    apply not_le_of_gt
    apply one_div_lt_one_div_of_lt (by positivity)
    exact_mod_cast (by omega : n + 2 < n + 3)
  have hle : (t : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) := ht.le
  have hphase : fareySchedulePhase (n + 2) t = ⟨1, by norm_num⟩ := by
    have ht' : t = (⟨1 / ((n + 2 : ℕ) : ℝ), by
      constructor
      · positivity
      · apply (div_le_iff₀ (by positivity)).2
        norm_num
        linarith⟩ : ConeTime) := Subtype.ext ht
    rw [ht']
    exact fareySchedulePhase_upper (n + 2) (by omega)
  simp only [fareyFiniteSchedule, hnot, hle, ↓reduceIte, hphase]

theorem fareySchedulePhase_continuous (n : ℕ) :
    Continuous (fareySchedulePhase n) := by
  apply Continuous.subtype_mk
  fun_prop

theorem fareyFiniteSchedule_early (n : ℕ) (x : fareyStage (n + 1))
    (t : ConeTime) (ht : (t : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ)) :
    fareyFiniteSchedule (n + 1) x t = x.1 := by
  cases n with
  | zero =>
      have ht' : (t : ℝ) ≤ (1 / 2 : ℝ) := by simpa using ht
      simp [fareyFiniteSchedule]
      intro hlt
      exact False.elim (not_lt_of_ge (by simpa only [one_div] using ht') hlt)
  | succ n =>
      have ht' : (t : ℝ) ≤ 1 / ((n + 3 : ℕ) : ℝ) := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ht
      simp only [fareyFiniteSchedule]
      split_ifs
      rfl

theorem fareyFiniteSchedule_succ_restrict (n : ℕ) (x : fareyStage n)
    (t : ConeTime) :
    fareyFiniteSchedule (n + 1)
      ⟨x.1, fareyStage_mono (by omega) x.2⟩ t =
      fareyFiniteSchedule n x t := by
  cases n with
  | zero =>
      have h : fareyFiniteSchedule 1
          ⟨x.1, fareyStage_mono (by omega) x.2⟩ t =
          fareyFiniteSchedule 0 x t := by
        rw [fareyFiniteSchedule.eq_2, fareyFiniteSchedule.eq_1]
      exact h
  | succ k =>
      have hlow : x.1 ∈ fareyStage (k + 2 - 1) := by
        simp [show k + 2 - 1 = k + 1 by omega]
      have hfixed (u : ConeTime) :
          fareyStageStep (k + 2) (by omega)
            ⟨x.1, fareyStage_mono (by omega) x.2⟩ u = x.1 :=
        fareyStageStep_fixed_of_lower (k + 2) (by omega)
          ⟨x.1, fareyStage_mono (by omega) x.2⟩ hlow u
      have hend :
          (⟨fareyStageStep (k + 2) (by omega)
            ⟨x.1, fareyStage_mono (by omega) x.2⟩ ⟨1, by norm_num⟩,
            fareyStageStep_maps_down (k + 2) (by omega)
              ⟨x.1, fareyStage_mono (by omega) x.2⟩⟩ :
              fareyStage (k + 1)) = x := by
        apply Subtype.ext
        exact hfixed ⟨1, by norm_num⟩
      change fareyFiniteSchedule (k + 2)
        ⟨x.1, fareyStage_mono (by omega) x.2⟩ t =
          fareyFiniteSchedule (k + 1) x t
      by_cases hfirst : (t : ℝ) ≤ 1 / ((k + 3 : ℕ) : ℝ)
      · have hbound : (t : ℝ) ≤ 1 / ((k + 2 : ℕ) : ℝ) := by
          apply hfirst.trans
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (by omega : k + 2 ≤ k + 3)
        rw [fareyFiniteSchedule_early k x t hbound]
        simp only [fareyFiniteSchedule, hfirst, ↓reduceIte]
      · by_cases hsecond : (t : ℝ) ≤ 1 / ((k + 2 : ℕ) : ℝ)
        · rw [fareyFiniteSchedule_early k x t hsecond]
          simp only [fareyFiniteSchedule, hfirst, hsecond, ↓reduceIte]
          exact hfixed (fareySchedulePhase (k + 2) t)
        · simp only [fareyFiniteSchedule, hfirst, hsecond, ↓reduceIte]
          rw [hend]

theorem fareyFiniteSchedule_restrict {m n : ℕ} (hmn : m ≤ n)
    (x : fareyStage m) (t : ConeTime) :
    fareyFiniteSchedule n ⟨x.1, fareyStage_mono hmn x.2⟩ t =
      fareyFiniteSchedule m x t := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hmono : x.1 ∈ fareyStage n := fareyStage_mono hmn x.2
      calc
        fareyFiniteSchedule (n + 1)
            ⟨x.1, fareyStage_mono (by omega) x.2⟩ t =
          fareyFiniteSchedule n ⟨x.1, hmono⟩ t :=
            fareyFiniteSchedule_succ_restrict n ⟨x.1, hmono⟩ t
        _ = fareyFiniteSchedule m x t := ih

end CurveComplexGenusTwo.Topology
