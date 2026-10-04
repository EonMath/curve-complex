import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_Q_boundary_parallel_same_range
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (a b : ProperArc S x R)
    (hrange : Set.range a.val = Set.range b.val) :
    boundaryParallel S x R a ↔ boundaryParallel S x R b := by
  constructor
  · rintro ⟨v,hv,hvB,d,hd,hdimage⟩
    exact ⟨v,hv,hvB,d,hd,by rw [← hrange]; exact hdimage⟩
  · rintro ⟨v,hv,hvB,d,hd,hdimage⟩
    exact ⟨v,hv,hvB,d,hd,by rw [hrange]; exact hdimage⟩

theorem regional_original_Q_essential_same_range
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (a b : ProperArc S x R)
    (hrange : Set.range a.val = Set.range b.val)
    (ha : ¬ boundaryParallel S x R a) :
    ¬ boundaryParallel S x R b := by
  exact (regional_original_Q_boundary_parallel_same_range x R a b hrange).mpr.mt ha

#print axioms regional_original_Q_boundary_parallel_same_range
#print axioms regional_original_Q_essential_same_range
