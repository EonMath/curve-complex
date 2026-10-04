import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Complex

open Set

theorem actual_finite_core_state_induction
    {ι X : Type*} (a0 : X) (S : Finset ι)
    (P : ι → X → Prop) (update : X → ι → ℂ → X)
    (hzero : ∀ a i, update a i 0 = a)
    (hlocal : ∀ a i (r : ℝ), 0 < r →
      ∃ c : ℂ, ‖c‖ < r ∧ P i (update a i c))
    (hstable : ∀ a i j, IsOpen {c : ℂ | P j (update a i c)}) :
    ∃ a : X, ∀ i ∈ S, P i a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨a0, by simp⟩
  | @insert i T hi ih =>
      obtain ⟨a, ha⟩ := ih
      let U : Set ℂ := ⋂ j ∈ (T : Set ι), {c | P j (update a i c)}
      have hU : IsOpen U :=
        isOpen_biInter_finset (fun j hj => hstable a i j)
      have h0 : (0 : ℂ) ∈ U := by
        simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
        intro j hj
        rw [hzero]
        exact ha j hj
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h0
      obtain ⟨c, hc, hnew⟩ := hlocal a i r hr
      refine ⟨update a i c, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hnew
      · have hcU : c ∈ U :=
          hball (by simpa only [Metric.mem_ball, dist_zero_right] using hc)
        simp only [U, Set.mem_iInter, Set.mem_ofPred_eq] at hcU
        exact hcU j hj

