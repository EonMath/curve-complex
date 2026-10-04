import CurveComplexGenusTwo.Topology.FareyScheduledFinite

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- Adjacent-stage compatibility propagates to every inclusion of denominator
stages.  This is the exact compatibility needed by the weak-realization
quotient construction. -/
theorem fareyFiniteSchedule_coherent_of_adjacent
    (hadj : ∀ (n : ℕ) (x : fareyStage n) (t : ConeTime),
      fareyFiniteSchedule (n + 1)
        ⟨x.1, fareyStage_mono (Nat.le_succ n) x.2⟩ t =
          fareyFiniteSchedule n x t) :
    ∀ {m n : ℕ} (hmn : m ≤ n) (x : fareyStage m) (t : ConeTime),
      fareyFiniteSchedule m x t =
        fareyFiniteSchedule n
          ⟨x.1, fareyStage_mono hmn x.2⟩ t := by
  intro m n hmn x t
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hmono : x.1 ∈ fareyStage n := fareyStage_mono hmn x.2
      calc
        fareyFiniteSchedule m x t =
            fareyFiniteSchedule n ⟨x.1, hmono⟩ t := ih
        _ = fareyFiniteSchedule (n + 1)
              ⟨x.1, fareyStage_mono (Nat.le_succ n) hmono⟩ t :=
            (hadj n ⟨x.1, hmono⟩ t).symm

/-- Every finite schedule ends at the fan apex. -/
theorem fareyFiniteSchedule_one (n : ℕ) (x : fareyStage n) :
    fareyFiniteSchedule n x ⟨1, by norm_num⟩ = fareyStageOneApex.1 := by
  induction n using Nat.twoStepInduction with
  | zero =>
      have hphase : fareySchedulePhase 1 ⟨1, by norm_num⟩ =
          ⟨1, by norm_num⟩ := by
        apply Subtype.ext
        norm_num [fareySchedulePhase]
      simp only [fareyFiniteSchedule, show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num,
        ↓reduceIte, hphase, fareyStageOneInterpolate_one]
  | one =>
      have hphase : fareySchedulePhase 1 ⟨1, by norm_num⟩ =
          ⟨1, by norm_num⟩ := by
        apply Subtype.ext
        norm_num [fareySchedulePhase]
      simp only [fareyFiniteSchedule, show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num,
        ↓reduceIte, hphase, fareyStageOneInterpolate_one]
  | more n _ ih =>
      have hfirst : ¬ ((1 : ℝ) ≤ 1 / ((n + 3 : ℕ) : ℝ)) := by
        apply not_le_of_gt
        simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
          (by exact_mod_cast (by omega : 1 < n + 3) : (1 : ℝ) < (n + 3 : ℕ)))
      have hsecond : ¬ ((1 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ)) := by
        apply not_le_of_gt
        simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
          (by exact_mod_cast (by omega : 1 < n + 2) : (1 : ℝ) < (n + 2 : ℕ)))
      simp only [fareyFiniteSchedule, hfirst, hsecond, ↓reduceIte]
      exact ih _

/-- The global scheduled contraction follows from the two remaining finite
stage checks: joint continuity and adjacent-stage compatibility. -/
theorem exists_continuous_fareyFiniteSchedule
    (hcont : ∀ n : ℕ,
      Continuous (fun p : fareyStage n × ConeTime =>
        fareyFiniteSchedule n p.1 p.2))
    (hadj : ∀ (n : ℕ) (x : fareyStage n) (t : ConeTime),
      fareyFiniteSchedule (n + 1)
        ⟨x.1, fareyStage_mono (Nat.le_succ n) x.2⟩ t =
          fareyFiniteSchedule n x t) :
    ∃ f : RealizationPoint fareyComplex × ConeTime →
        RealizationPoint fareyComplex,
      Continuous f ∧
      (∀ x : RealizationPoint fareyComplex,
        f (x, ⟨0, by norm_num⟩) = x) ∧
      (∀ x : RealizationPoint fareyComplex,
        f (x, ⟨1, by norm_num⟩) = fareyStageOneApex.1) ∧
      (∀ (n : ℕ) (x : fareyStage n) (t : ConeTime),
        f (x, t) = fareyFiniteSchedule n x t) := by
  obtain ⟨f, hfcont, hfstage⟩ :=
    exists_continuous_fareyHomotopy_of_coherent_stages
      (fun n p => fareyFiniteSchedule n p.1 p.2) hcont
      (fareyFiniteSchedule_coherent_of_adjacent hadj)
  refine ⟨f, hfcont, ?_, ?_, hfstage⟩
  · intro x
    obtain ⟨n, hn⟩ := fareyStage_exhaustive x
    let y : fareyStage n := ⟨x, hn⟩
    simpa only [fareyFiniteSchedule_zero] using
      (hfstage n y ⟨0, by norm_num⟩)
  · intro x
    obtain ⟨n, hn⟩ := fareyStage_exhaustive x
    let y : fareyStage n := ⟨x, hn⟩
    rw [hfstage n y ⟨1, by norm_num⟩, fareyFiniteSchedule_one]

/-- The assembled map is a homotopy from the identity on the actual weak
realization to the denominator-one fan apex. -/
theorem exists_fareyFiniteScheduleHomotopy
    (hcont : ∀ n : ℕ,
      Continuous (fun p : fareyStage n × ConeTime =>
        fareyFiniteSchedule n p.1 p.2))
    (hadj : ∀ (n : ℕ) (x : fareyStage n) (t : ConeTime),
      fareyFiniteSchedule (n + 1)
        ⟨x.1, fareyStage_mono (Nat.le_succ n) x.2⟩ t =
          fareyFiniteSchedule n x t) :
    ∃ H : ContinuousMap.Homotopy
        (ContinuousMap.id (RealizationPoint fareyComplex))
        (ContinuousMap.const (RealizationPoint fareyComplex) fareyStageOneApex.1),
      ∀ (n : ℕ) (x : fareyStage n) (t : ConeTime),
        H (t, x.1) = fareyFiniteSchedule n x t := by
  obtain ⟨f, hfcont, hfzero, hfone, hfstage⟩ :=
    exists_continuous_fareyFiniteSchedule hcont hadj
  let H : ContinuousMap.Homotopy
      (ContinuousMap.id (RealizationPoint fareyComplex))
      (ContinuousMap.const (RealizationPoint fareyComplex) fareyStageOneApex.1) := {
    toFun := fun p => f (p.2, p.1)
    continuous_toFun := hfcont.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := hfzero
    map_one_left := hfone
  }
  exact ⟨H, hfstage⟩

end CurveComplexGenusTwo.Topology
