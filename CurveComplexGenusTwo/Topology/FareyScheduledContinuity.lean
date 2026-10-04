import CurveComplexGenusTwo.Topology.FareyStepContinuity
import CurveComplexGenusTwo.Topology.FareyCoherenceWave10

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

private theorem continuous_if_coneTime_le
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (c : ℝ) (f g : X × ConeTime → Y)
    (hf : Continuous f) (hg : Continuous g)
    (hboundary : ∀ q : X × ConeTime, (q.2 : ℝ) = c → f q = g q) :
    Continuous (fun q : X × ConeTime =>
      if (q.2 : ℝ) ≤ c then f q else g q) := by
  classical
  apply Continuous.if ?_ hf hg
  intro q hq
  have htime : Continuous (fun q : X × ConeTime => (q.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hq' : (q.2 : ℝ) ∈ frontier (Set.Iic c) :=
    htime.frontier_preimage_subset (Set.Iic c) hq
  exact hboundary q ((Set.mem_singleton_iff.mp (frontier_Iic_subset c hq')))

private theorem fareyFiniteSchedule_continuous_zero :
    Continuous (fun q : fareyStage 0 × ConeTime =>
      fareyFiniteSchedule 0 q.1 q.2) := by
  classical
  let f : fareyStage 0 × ConeTime → RealizationPoint fareyComplex :=
    fun q => q.1.1
  let g : fareyStage 0 × ConeTime → RealizationPoint fareyComplex :=
    fun q => (fareyStageOneInterpolate
      (fareySchedulePhase 1 q.2,
        ⟨q.1.1, fareyStage_mono (by omega) q.1.2⟩)).1
  have hf : Continuous f := continuous_subtype_val.comp continuous_fst
  have hcast : Continuous (fun x : fareyStage 0 =>
      (⟨x.1, fareyStage_mono (by omega) x.2⟩ : fareyStage 1)) := by
    exact Continuous.subtype_mk continuous_subtype_val _
  have hg : Continuous g := by
    apply continuous_subtype_val.comp
    apply fareyStageOneInterpolate_continuous.comp
    exact ((fareySchedulePhase_continuous 1).comp continuous_snd).prodMk
      (hcast.comp continuous_fst)
  have hboundary : ∀ q : fareyStage 0 × ConeTime,
      (q.2 : ℝ) = (1 / 2 : ℝ) → f q = g q := by
    intro q hq
    have ht : q.2 = (⟨1 / 2, by norm_num⟩ : ConeTime) := Subtype.ext hq
    change q.1.1 = (fareyStageOneInterpolate
      (fareySchedulePhase 1 q.2,
        ⟨q.1.1, fareyStage_mono (by omega) q.1.2⟩)).1
    rw [ht]
    have hp : fareySchedulePhase 1 ⟨1 / 2, by norm_num⟩ =
        ⟨0, by norm_num⟩ := by
      apply Subtype.ext
      norm_num [fareySchedulePhase]
    rw [hp, fareyStageOneInterpolate_zero]
  convert continuous_if_coneTime_le (1 / 2 : ℝ) f g hf hg hboundary using 1
  funext q
  simp only [fareyFiniteSchedule, f, g]

private theorem fareyFiniteSchedule_continuous_one :
    Continuous (fun q : fareyStage 1 × ConeTime =>
      fareyFiniteSchedule 1 q.1 q.2) := by
  classical
  let f : fareyStage 1 × ConeTime → RealizationPoint fareyComplex :=
    fun q => q.1.1
  let g : fareyStage 1 × ConeTime → RealizationPoint fareyComplex :=
    fun q => (fareyStageOneInterpolate
      (fareySchedulePhase 1 q.2, q.1)).1
  have hf : Continuous f := continuous_subtype_val.comp continuous_fst
  have hg : Continuous g := by
    apply continuous_subtype_val.comp
    apply fareyStageOneInterpolate_continuous.comp
    exact ((fareySchedulePhase_continuous 1).comp continuous_snd).prodMk
      continuous_fst
  have hboundary : ∀ q : fareyStage 1 × ConeTime,
      (q.2 : ℝ) = (1 / 2 : ℝ) → f q = g q := by
    intro q hq
    have ht : q.2 = (⟨1 / 2, by norm_num⟩ : ConeTime) := Subtype.ext hq
    change q.1.1 = (fareyStageOneInterpolate
      (fareySchedulePhase 1 q.2, q.1)).1
    rw [ht]
    have hp : fareySchedulePhase 1 ⟨1 / 2, by norm_num⟩ =
        ⟨0, by norm_num⟩ := by
      apply Subtype.ext
      norm_num [fareySchedulePhase]
    rw [hp, fareyStageOneInterpolate_zero]
  convert continuous_if_coneTime_le (1 / 2 : ℝ) f g hf hg hboundary using 1
  funext q
  simp only [fareyFiniteSchedule, f, g]

/-- The recursive schedule is jointly continuous on every denominator stage.
The two splice equalities are the zero/one endpoint laws for the stage move
and the early-identity law for the already collapsed lower-stage schedule. -/
theorem fareyFiniteSchedule_continuous (k : ℕ) :
    Continuous (fun q : fareyStage k × ConeTime =>
      fareyFiniteSchedule k q.1 q.2) := by
  induction k using Nat.twoStepInduction with
  | zero => exact fareyFiniteSchedule_continuous_zero
  | one => exact fareyFiniteSchedule_continuous_one
  | more n _ ih =>
      classical
      let endpoint : fareyStage (n + 2) → fareyStage (n + 1) :=
        fun x => ⟨fareyStageStep (n + 2) (by omega) x ⟨1, by norm_num⟩,
          fareyStageStep_maps_down (n + 2) (by omega) x⟩
      have he : Continuous endpoint := by
        apply Continuous.subtype_mk
        exact (fareyStageStep_continuous (n + 2) (by omega)).comp
          (continuous_id.prodMk continuous_const)
      let f0 : fareyStage (n + 2) × ConeTime → RealizationPoint fareyComplex :=
        fun q => q.1.1
      let f1 : fareyStage (n + 2) × ConeTime → RealizationPoint fareyComplex :=
        fun q => fareyStageStep (n + 2) (by omega) q.1
          (fareySchedulePhase (n + 2) q.2)
      let f2 : fareyStage (n + 2) × ConeTime → RealizationPoint fareyComplex :=
        fun q => fareyFiniteSchedule (n + 1) (endpoint q.1) q.2
      have hc0 : Continuous f0 := continuous_subtype_val.comp continuous_fst
      have hc1 : Continuous f1 :=
        (fareyStageStep_continuous (n + 2) (by omega)).comp
          (continuous_fst.prodMk
            ((fareySchedulePhase_continuous (n + 2)).comp continuous_snd))
      have hc2 : Continuous f2 := by
        exact ih.comp ((he.comp continuous_fst).prodMk continuous_snd)
      have hupper : ∀ q : fareyStage (n + 2) × ConeTime,
          (q.2 : ℝ) = 1 / ((n + 2 : ℕ) : ℝ) → f1 q = f2 q := by
        intro q ht
        have hp : fareySchedulePhase (n + 2) q.2 = ⟨1, by norm_num⟩ := by
          have hq : q.2 = (⟨1 / ((n + 2 : ℕ) : ℝ), by
              constructor
              · positivity
              · apply (div_le_iff₀ (by positivity)).2
                norm_num
                linarith⟩ : ConeTime) := Subtype.ext ht
          rw [hq]
          exact fareySchedulePhase_upper (n + 2) (by omega)
        change fareyStageStep (n + 2) (by omega) q.1
            (fareySchedulePhase (n + 2) q.2) =
          fareyFiniteSchedule (n + 1) (endpoint q.1) q.2
        rw [hp]
        have hle : (q.2 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) := ht.le
        rw [fareyFiniteSchedule_early n (endpoint q.1) q.2 hle]
      have hinner : Continuous (fun q : fareyStage (n + 2) × ConeTime =>
          if (q.2 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) then f1 q else f2 q) :=
        continuous_if_coneTime_le _ f1 f2 hc1 hc2 hupper
      have hlower : ∀ q : fareyStage (n + 2) × ConeTime,
          (q.2 : ℝ) = 1 / ((n + 3 : ℕ) : ℝ) →
          f0 q = (if (q.2 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) then f1 q else f2 q) := by
        intro q ht
        have hle : (q.2 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) := by
          rw [ht]
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast (by omega : n + 2 ≤ n + 3)
        simp only [hle, ↓reduceIte]
        have hp : fareySchedulePhase (n + 2) q.2 = ⟨0, by norm_num⟩ := by
          have hq : q.2 = (⟨1 / (((n + 2) + 1 : ℕ) : ℝ), by
              constructor
              · positivity
              · apply (div_le_iff₀ (by positivity)).2
                norm_num
                linarith⟩ : ConeTime) := by
            apply Subtype.ext
            simpa [Nat.add_assoc] using ht
          rw [hq]
          exact fareySchedulePhase_lower (n + 2) (by omega)
        change q.1.1 = fareyStageStep (n + 2) (by omega) q.1
          (fareySchedulePhase (n + 2) q.2)
        rw [hp, fareyStageStep_zero]
      have hc : Continuous (fun q : fareyStage (n + 2) × ConeTime =>
          if (q.2 : ℝ) ≤ 1 / ((n + 3 : ℕ) : ℝ) then f0 q
          else if (q.2 : ℝ) ≤ 1 / ((n + 2 : ℕ) : ℝ) then f1 q else f2 q) :=
        continuous_if_coneTime_le _ f0 _ hc0 hinner hlower
      convert hc using 1
      funext q
      simp only [fareyFiniteSchedule, f0, f1, f2, endpoint]

end CurveComplexGenusTwo.Topology
