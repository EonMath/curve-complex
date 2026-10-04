import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualLocalCoverAreaCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualRamificationAreaNullCandidate
import Mathlib.Topology.Compactness.Lindelof

namespace CurveComplex.Hyperbolic
open Set Topology MeasureTheory
open scoped NNReal ENNReal MeasureTheory

set_option maxHeartbeats 2000000 in
theorem actual_branched_cover_normalized_total_area {E S B : Type}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace S] [T2Space S]
    [MetricSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (q : BranchedDoubleCover E S) (identify : S ≃ₜ B)
    (hlocal : ∀ x : E, x ∉ q.ramification → ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist y z = dist (identify (q.projection y)) (identify (q.projection z))) :
    (μHE[2] : Measure E) univ = 2 * (μHE[2] : Measure B) univ := by
  classical
  let p : E → B := fun x => identify (q.projection x)
  let K : Set B := identify '' (q.branch : Set S)
  have hKfinite : K.Finite := q.branch.finite_toSet.image identify
  have hKzero : (μHE[2] : Measure B) K = 0 := finite_set_normalized_area_zero K hKfinite
  have hpK : p ⁻¹' K = q.ramification := by
    ext x
    change (identify (q.projection x) ∈ identify '' (q.branch : Set S)) ↔
      q.projection x ∈ (q.branch : Set S)
    exact identify.injective.mem_set_image
  have hpKzero : (μHE[2] : Measure E) (p ⁻¹' K) = 0 := by
    rw [hpK]; exact finite_set_normalized_area_zero _ q.actual_ramification_finite
  have hp : Continuous p := identify.continuous.comp q.projection_continuous
  have hnonempty : Nonempty B := by
    have hn : q.branch.Nonempty := Finset.card_pos.mp (by rw [q.branch_card]; norm_num)
    obtain ⟨b, hb⟩ := hn
    exact ⟨identify b⟩
  letI := hnonempty
  have hloc (b : B) : ∃ V : Set B, IsOpen V ∧ V ⊆ Kᶜ ∧
      (b ∉ K → b ∈ V) ∧ ∀ s : Set B, MeasurableSet s → s ⊆ V →
      (μHE[2] : Measure E) (p ⁻¹' s) = 2 * (μHE[2] : Measure B) s := by
    by_cases hb : b ∈ K
    · refine ⟨∅, isOpen_empty, empty_subset _, ?_, ?_⟩
      · exact fun h => (h hb).elim
      · intro s hs hse
        have hse' : s = ∅ := subset_empty_iff.mp hse
        simp [hse']
    · have hb' : identify.symm b ∉ (q.branch : Set S) := by
        intro h
        exact hb ⟨identify.symm b, h, identify.apply_symm_apply b⟩
      obtain ⟨V, hV, hbin, havoid, hmass⟩ :=
        actual_unramified_local_cover_normalized_area q identify hlocal (identify.symm b) hb'
      refine ⟨V, hV, havoid, ?_, hmass⟩
      intro _; simpa using hbin
  choose U hUopen hUavoid hUin hUmass using hloc
  have hcover : Kᶜ ⊆ ⋃ b, U b := by
    intro b hb
    exact mem_iUnion.mpr ⟨b, hUin b hb⟩
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof Kᶜ).indexed_countable_subcover U hUopen hcover
  let V : ℕ → Set B := disjointed (fun n => U (f n))
  have hVsub (n : ℕ) : V n ⊆ U (f n) := disjointed_subset _ n
  have hVmeas (n : ℕ) : MeasurableSet (V n) :=
    MeasurableSet.disjointed (fun n => (hUopen (f n)).measurableSet) n
  have hVdisj : Pairwise (fun i j => Disjoint (V i) (V j)) := disjoint_disjointed _
  have hVunion : ⋃ n, V n = Kᶜ := by
    rw [iUnion_disjointed]
    exact subset_antisymm (iUnion_subset fun n => hUavoid (f n)) hf
  have hpremeas (n : ℕ) : MeasurableSet (p ⁻¹' V n) := (hVmeas n).preimage hp.measurable
  have hpredisj : Pairwise (fun i j => Disjoint (p ⁻¹' V i) (p ⁻¹' V j)) := by
    intro i j hij; exact (hVdisj hij).preimage p
  have hmass : (μHE[2] : Measure E) (p ⁻¹' Kᶜ) = 2 * (μHE[2] : Measure B) Kᶜ := by
    rw [← hVunion, preimage_iUnion, measure_iUnion hpredisj hpremeas,
      measure_iUnion hVdisj hVmeas]
    simp_rw [hUmass _ _ (hVmeas _) (hVsub _)]
    exact ENNReal.tsum_mul_left
  have he : (μHE[2] : Measure E) (p ⁻¹' Kᶜ) = (μHE[2] : Measure E) univ := by
    simpa only [compl_eq_univ_sdiff, preimage_sdiff, preimage_univ] using
      (measure_sdiff_null hpKzero (s := (univ : Set E)))
  have hb : (μHE[2] : Measure B) Kᶜ = (μHE[2] : Measure B) univ := by
    simpa only [compl_eq_univ_sdiff] using (measure_sdiff_null hKzero (s := (univ : Set B)))
  rwa [he, hb] at hmass

end CurveComplex.Hyperbolic
