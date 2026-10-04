import CurveComplexGenusTwo.Topology.FareyStageAssembly
import CurveComplexGenusTwo.Topology.FareyGlobalContinuity

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The endpoint of the finite, descending sequence of parent collapses.
At level `n+2` the top denominator is removed before the recursion starts
at level `n+1`.  The codomain is the actual denominator-one stage. -/
noncomputable def fareyFiniteEndpoint : (n : ℕ) → fareyStage n → fareyStage 1
  | 0 => fun x => ⟨x.1, fareyStage_mono (by omega) x.2⟩
  | 1 => id
  | n + 2 => fun x =>
      fareyFiniteEndpoint (n + 1)
        ⟨fareyStageStep (n + 2) (by omega) x ⟨1, by norm_num⟩,
          fareyStageStep_maps_down (n + 2) (by omega) x⟩

theorem fareyFiniteEndpoint_one (x : fareyStage 1) :
    fareyFiniteEndpoint 1 x = x := rfl

theorem fareyFiniteEndpoint_succ_restrict (n : ℕ)
    (x : fareyStage n) :
    fareyFiniteEndpoint (n + 1)
      ⟨x.1, fareyStage_mono (by omega) x.2⟩ =
      fareyFiniteEndpoint n x := by
  induction n with
  | zero =>
      apply Subtype.ext
      rfl
  | succ n ih =>
      have hn : 1 < n + 2 := by omega
      have hidx : n + 2 - 1 = n + 1 := by omega
      have hfixed := fareyStageStep_fixed_of_lower (n + 2) hn
        (⟨x.1, fareyStage_mono (by omega) x.2⟩ : fareyStage (n + 2))
        (by simpa only [hidx] using x.2)
        (⟨1, by norm_num⟩ : ConeTime)
      simp only [fareyFiniteEndpoint]
      have harg :
          (⟨fareyStageStep (n + 2) hn
              ⟨x.1, fareyStage_mono (by omega) x.2⟩ ⟨1, by norm_num⟩,
              fareyStageStep_maps_down (n + 2) hn
                ⟨x.1, fareyStage_mono (by omega) x.2⟩⟩ : fareyStage (n + 1)) = x := by
        apply Subtype.ext
        exact hfixed
      exact congrArg (fareyFiniteEndpoint (n + 1)) harg

theorem fareyFiniteEndpoint_restrict {m n : ℕ} (hmn : m ≤ n)
    (x : fareyStage m) :
    fareyFiniteEndpoint n ⟨x.1, fareyStage_mono hmn x.2⟩ =
      fareyFiniteEndpoint m x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hmono : x.1 ∈ fareyStage n := fareyStage_mono hmn x.2
      calc
        fareyFiniteEndpoint (n + 1)
            ⟨x.1, fareyStage_mono (by omega) x.2⟩ =
          fareyFiniteEndpoint n ⟨x.1, hmono⟩ :=
            fareyFiniteEndpoint_succ_restrict n ⟨x.1, hmono⟩
        _ = fareyFiniteEndpoint m x := ih

/-- Clamp the affine clock for the denominator-`n` window
`[1/(n+1), 1/n]` to the unit interval. -/
noncomputable def fareySchedulePhase (n : ℕ) (t : ConeTime) : ConeTime :=
  ⟨max 0 (min 1 (((n : ℝ) * (n + 1) * (t : ℝ)) - n)),
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩

/-- Recursive finite-stage schedule. The top denominator is removed in its
own window; the recursion is called only after its time-one endpoint has
landed in the next lower stage. -/
noncomputable def fareyFiniteSchedule :
    (n : ℕ) → fareyStage n → ConeTime → RealizationPoint fareyComplex
  | 0, x, t =>
      if (t : ℝ) ≤ (1 / 2 : ℝ) then x.1
      else (fareyStageOneInterpolate
        (fareySchedulePhase 1 t,
          ⟨x.1, fareyStage_mono (by omega) x.2⟩)).1
  | 1, x, t =>
      if (t : ℝ) ≤ (1 / 2 : ℝ) then x.1
      else (fareyStageOneInterpolate (fareySchedulePhase 1 t, x)).1
  | n + 2, x, t =>
      if (t : ℝ) ≤ (1 / ((n + 3 : ℕ) : ℝ)) then x.1
      else if (t : ℝ) ≤ (1 / ((n + 2 : ℕ) : ℝ)) then
        fareyStageStep (n + 2) (by omega) x (fareySchedulePhase (n + 2) t)
      else
        fareyFiniteSchedule (n + 1)
          ⟨fareyStageStep (n + 2) (by omega) x ⟨1, by norm_num⟩,
            fareyStageStep_maps_down (n + 2) (by omega) x⟩ t
termination_by n => n

theorem fareyFiniteSchedule_zero (n : ℕ) (x : fareyStage n) :
    fareyFiniteSchedule n x ⟨0, by norm_num⟩ = x.1 := by
  cases n with
  | zero =>
      simp [fareyFiniteSchedule]
  | succ n =>
      cases n with
      | zero => simp [fareyFiniteSchedule]
      | succ n =>
          have h : (0 : ℝ) ≤ 1 / ((n + 3 : ℕ) : ℝ) := by positivity
          have hnpos : ¬ ((n : ℝ) + 3 < 0) := by
            intro hneg
            have : (0 : ℝ) ≤ n := by positivity
            linarith
          simp only [fareyFiniteSchedule]
          simp [h, hnpos]

end CurveComplexGenusTwo.Topology
