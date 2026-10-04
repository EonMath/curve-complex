import CurveComplexGenusTwo.Topology.FareyWeakAssembly
import CurveComplexGenusTwo.Topology.FareyScheduledContinuity

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The scheduled Farey collapse assembles to a homotopy on the full weak
geometric realization. -/
theorem fareyFiniteScheduleHomotopy :
    ∃ H : ContinuousMap.Homotopy
        (ContinuousMap.id (RealizationPoint fareyComplex))
        (ContinuousMap.const (RealizationPoint fareyComplex) fareyStageOneApex.1),
      ∀ (n : ℕ) (x : fareyStage n) (t : ConeTime),
        H (t, x.1) = fareyFiniteSchedule n x t := by
  apply exists_fareyFiniteScheduleHomotopy fareyFiniteSchedule_continuous
  intro n x t
  exact fareyFiniteSchedule_succ_restrict n x t

/-- The actual weak realization of the filled Farey complex is contractible. -/
theorem fareyRealization_contractible :
    ContractibleSpace (RealizationPoint fareyComplex) := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨fareyStageOneApex.1, ?_⟩
  exact ⟨fareyFiniteScheduleHomotopy.choose⟩

end CurveComplexGenusTwo.Topology
