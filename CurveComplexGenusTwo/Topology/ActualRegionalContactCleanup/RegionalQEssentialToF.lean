import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_F_boundary_parallel_implies_Q_parallel
    {S : Type} [TopologicalSpace S] (F Q B : Set S)
    (hFQ : F ⊆ Q)
    (aF : C(Interval,↥F)) (aQ : C(Interval,↥Q))
    (haimage : ∀ t, (aF t).val = (aQ t).val)
    (hparallel :
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range aF ∪ Set.range b) :
      ∃ b : C(Interval,↥Q), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥Q),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range aQ ∪ Set.range b := by
  obtain ⟨b,hb,hbB,d,hd,hdimage⟩ := hparallel
  let i : C(↥F,↥Q) :=
    ⟨fun y => ⟨y.val,hFQ y.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hi : Topology.IsEmbedding i := by
    apply Topology.IsEmbedding.of_comp i.continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  let bQ : C(Interval,↥Q) := i.comp b
  let dQ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥Q) :=
    i.comp d
  refine ⟨bQ,hi.comp hb,hbB,dQ,hi.comp hd,?_⟩
  change (i ∘ d) '' {z | z.val ∈
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    Set.range aQ ∪ Set.range bQ
  have himage : (i ∘ d) '' {z | z.val ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      i '' (d '' {z | z.val ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    simpa only [Function.comp_def] using
      (Set.image_image i d
        {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}).symm
  rw [himage]
  change i '' (d '' {z | z.val ∈
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) =
    Set.range aQ ∪ Set.range bQ
  rw [hdimage,Set.image_union]
  have hA : i '' Set.range aF = Set.range aQ := by
    ext y
    constructor
    · rintro ⟨z,⟨t,rfl⟩,rfl⟩
      exact ⟨t,Subtype.ext (haimage t).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨aF t,⟨t,rfl⟩,Subtype.ext (haimage t)⟩
  have hB : i '' Set.range b = Set.range bQ := by
    ext y
    constructor
    · rintro ⟨z,⟨t,rfl⟩,rfl⟩
      exact ⟨t,rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨b t,⟨t,rfl⟩,rfl⟩
  rw [hA,hB]

#print axioms regional_F_boundary_parallel_implies_Q_parallel
