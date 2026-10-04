import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_F_proper_branch_to_Q
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ)
    (F : Set S)
    (hFQ : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (B : Set S)
    (hB : B = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (hBQ : B ⊆ frontier F)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (ha0 : (a 0).val ∈ B) (ha1 : (a 1).val ∈ B)
    (hap : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∉ frontier F) :
    ∃ q : ProperArc S x R,
      ∀ t : Interval, q.val t = ⟨(a t).val,hFQ (a t).property⟩ := by
  let i : C(↥F,Q S x R) :=
    ⟨fun y => ⟨y.val,hFQ y.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hi : Topology.IsEmbedding i := by
    apply Topology.IsEmbedding.of_comp i.continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  let q : ProperArc S x R :=
    ⟨i.comp a,hi.comp ha,by
        change (a 0).val ∈ boundaryCircle S x R
        simpa only [hB,boundaryCircle] using ha0,
      by
        change (a 1).val ∈ boundaryCircle S x R
        simpa only [hB,boundaryCircle] using ha1,
      (fun t ht hb => hap t ht (hBQ (hB ▸ hb)))⟩
  exact ⟨q,fun _ => rfl⟩

#print axioms regional_original_F_proper_branch_to_Q
