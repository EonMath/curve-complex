import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQEssentialToF

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_Q_essential_same_trace_branch_is_F_essential
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (F B : Set S)
    (hFQ : F ⊆ (openDisk S x R)ᶜ)
    (hB : B = boundaryCircle S x R)
    (aF : C(Interval,↥F)) (aQ : ProperArc S x R)
    (haimage : ∀ t, (aF t).val = (aQ.val t).val)
    (haess : ¬ boundaryParallel S x R aQ) :
    ¬ ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
      (∀ t, (b t).val ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range aF ∪ Set.range b := by
  intro hp
  apply haess
  obtain ⟨b,hb,hbb,d,hd,he⟩ :=
    regional_F_boundary_parallel_implies_Q_parallel F (openDisk S x R)ᶜ B
      hFQ aF aQ.val haimage hp
  refine ⟨b,hb,?_,d,hd,he⟩
  intro t
  change (b t).val ∈ boundaryCircle S x R
  exact hB ▸ hbb t

#print axioms regional_Q_essential_same_trace_branch_is_F_essential
