import CurveComplexGenusTwo.Topology.FareyGlobalFiltration
import CurveComplexGenusTwo.Topology.FareyStageHomotopy

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- A coherent family of jointly continuous maps on the denominator stages
assembles to a jointly continuous map on the entire weak realization. -/
theorem exists_continuous_fareyHomotopy_of_coherent_stages
    {Y : Type*} [TopologicalSpace Y]
    (stageMap : ∀ n : ℕ, fareyStage n × ConeTime → Y)
    (hcont : ∀ n : ℕ, Continuous (stageMap n))
    (hcompat : ∀ {m n : ℕ} (hmn : m ≤ n) (x : fareyStage m) (t : ConeTime),
      stageMap m (x, t) =
        stageMap n (⟨x.1, fareyStage_mono hmn x.2⟩, t)) :
    ∃ f : RealizationPoint fareyComplex × ConeTime → Y,
      Continuous f ∧
        ∀ (n : ℕ) (x : fareyStage n) (t : ConeTime), f (x, t) = stageMap n (x, t) := by
  classical
  let f : RealizationPoint fareyComplex × ConeTime → Y := fun p =>
    let n := Classical.choose (fareyStage_exhaustive p.1)
    stageMap n (⟨p.1, Classical.choose_spec (fareyStage_exhaustive p.1)⟩, p.2)
  have hf (n : ℕ) (x : fareyStage n) (t : ConeTime) :
      f (x, t) = stageMap n (x, t) := by
    let m := Classical.choose (fareyStage_exhaustive x.1)
    let y : fareyStage m :=
      ⟨x.1, Classical.choose_spec (fareyStage_exhaustive x.1)⟩
    let z : fareyStage (max m n) :=
      ⟨x.1, fareyStage_mono (le_max_left m n) y.2⟩
    have hm : stageMap m (y, t) = stageMap (max m n) (z, t) :=
      hcompat (le_max_left m n) y t
    have hn : stageMap n (x, t) = stageMap (max m n) (z, t) := by
      convert hcompat (le_max_right m n) x t using 1
    exact hm.trans hn.symm
  refine ⟨f, ?_, hf⟩
  apply continuous_fareyHomotopy_of_stages f
  intro n
  convert hcont n using 1
  funext p
  exact hf n p.1 p.2

end CurveComplexGenusTwo.Topology
