import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalBandTranslation

open CurveComplex Set Topology

theorem regional_original_proper_arc_supported_ambient_copy
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image)
    (a : C(Interval, ↥F)) (ha : Topology.IsEmbedding a)
    (ha0 : (a 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (ha1 : (a 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (hap : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    (O : Set ↥F) (hO : IsOpen O) (haO : Set.range a ⊆ O)
    {ι : Type} [Fintype ι] (face : ι → C(Interval,↥F))
    (hfaceAvoid : ∀ i, Disjoint O (Set.range (face i))) :
    ∃ b : C(Interval, ↥F),
      Topology.IsEmbedding b ∧
      (b 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (b 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
      Disjoint (Set.range a) (Set.range b) ∧
      Set.range b ⊆ O ∧
      (∀ i, Disjoint (Set.range b) (Set.range (face i))) ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) ''
            {y : ↥F | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
              Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R} =
          {y : ↥F | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
              Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}) ∧
        (∀ t, (fun y => H.map (t,y)) ''
            {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a = Set.range b ∧
        (∀ t y, y ∉ O → H.map (t,y) = y) ∧
        (∀ i t s, H.map (t,face i s) = face i s) := by
  let : ClosedSurface S := Classical.choice hS.2.1
  let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  have hBF : B ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  obtain ⟨N,hN,hNc,hNend,hNint,hNopen⟩ :=
    regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier
      a ha ha0 ha1 hap
  obtain ⟨b,hb,hb0,hb1,hbp,hba,hbO,H,hHB,hHF,hHmove,hHout⟩ :=
    regional_proper_strip_supported_ambient_parallel_copy F B hFcompact hBF
      a N hN hNc hNend hNint hNopen O hO haO
  refine ⟨b,hb,hb0,hb1,hbp,hba,hbO,?_,H,hHB,hHF,hHmove,hHout,?_⟩
  · intro i
    exact (hfaceAvoid i).mono_left hbO
  · intro i t s
    exact hHout t (face i s)
      (fun hf => Set.disjoint_left.mp (hfaceAvoid i) hf (Set.mem_range_self s))

#print axioms regional_original_proper_arc_supported_ambient_copy
