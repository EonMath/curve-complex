import AlignmentTerminalExtensionScaffold
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalBRecognitionConsumer
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open Set Topology CurveComplex
open scoped Manifold ContDiff

-- Private source-faithfulness candidate. The disk exclusion is the literal
-- boundaryParallel witness from SourceC0FiniteCurveLoopSurgery.lean.
theorem actual_original_finite_essential_proper_arc_systems_simultaneous_alignment
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (J : Type) [Fintype J] (a b : J → C(Interval, ↥Q)),
      (∀ i, IsEmbedding (a i) ∧ IsEmbedding (b i)) →
      (∀ i, a i 0 ∈ B ∧ a i 1 ∈ B ∧ b i 0 ∈ B ∧ b i 1 ∈ B) →
      (∀ i t, t ∈ Set.Ioo (0 : Interval) 1 → a i t ∉ B ∧ b i t ∉ B) →
      (∀ i, ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧
        (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range (a i) ∪ Set.range c) →
      (∀ i, ¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧
        (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range (b i) ∪ Set.range c) →
      (∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j)) ∧
        Disjoint (Set.range (b i)) (Set.range (b j))) →
      (∀ i j, i ≠ j → ¬ ∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' Set.range (a i) = Set.range (a j)) →
      (∀ i, ∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' Set.range (a i) = Set.range (b i)) →
      ∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        ∀ i, H.finalMap '' Set.range (a i) = Set.range (b i) := by
  classical
  intro Q B J instJ a b hemb hends hmid haessential hbessential
    hdisjoint hdistinct hclasses
  have hpartial : ∀ P : Finset J, ∃ H : AmbientIsotopy ↥Q,
      (∀ t, (fun y => H.map (t,y)) '' B = B) ∧
      ∀ j ∈ P, H.finalMap '' Set.range (a j) = Set.range (b j) := by
    intro P
    induction P using Finset.induction_on with
    | empty =>
        refine ⟨AmbientIsotopy.identity ↥Q, ?_, ?_⟩
        · intro t
          exact Set.image_id B
        · intro j hj
          simp at hj
    | @insert i P hi ih =>
        obtain ⟨H,hHB,hProcessed⟩ := ih
        obtain ⟨K,hKB,hRestored,hNew⟩ :=
          original_disjoint_essential_arc_system_partial_alignment_terminal_extension
            S g hg hS x R hR htarget J a b hemb hends hmid
            haessential hbessential hdisjoint hdistinct hclasses
            P i hi H hHB hProcessed
        refine ⟨H.compose K,
          CoherentEndpointMotion.boundary_preserving_motion_compose B H K hHB hKB, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [AmbientIsotopy.compose_finalMap, Set.image_comp]
          exact hNew
        · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hProcessed j hj]
          exact hRestored j hj
  obtain ⟨H,hHB,hAligned⟩ := hpartial Finset.univ
  exact ⟨H,hHB,fun j => hAligned j (Finset.mem_univ j)⟩
