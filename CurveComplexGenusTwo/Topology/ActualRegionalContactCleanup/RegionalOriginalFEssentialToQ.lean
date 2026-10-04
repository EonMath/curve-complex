import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOriginalQFrontier
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalQParallelReflectsF

open CurveComplex Set Topology

theorem regional_original_F_essential_arc_is_Q_essential
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (_hg : 2 ≤ g) (hS : IsGenus S g)
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
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (ha0 : (a 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (ha1 : (a 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (hap : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    (haess : ¬ ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
      (∀ t, (b t).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a ∪ Set.range b) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let inclusion : C(↥F,↥Q) :=
      ⟨fun y => ⟨y.val,houtside y.property⟩,
        continuous_subtype_val.subtype_mk _⟩
    let qa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
      ⟨inclusion.comp a,
        (Topology.IsEmbedding.of_comp inclusion.continuous
          continuous_subtype_val Topology.IsEmbedding.subtypeVal).comp ha,
        ha0,ha1,
        (fun t ht hb => hap t ht (by rw [hfrontier]; exact Or.inl hb))⟩
    ¬ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryParallel S x R qa := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
  let inclusion : C(↥F,↥Q) :=
    ⟨fun y => ⟨y.val,houtside y.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hi : Topology.IsEmbedding inclusion := by
    apply Topology.IsEmbedding.of_comp inclusion.continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  have hBF : B ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  let qa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨inclusion.comp a,hi.comp ha,ha0,ha1,
      (fun t ht hb => hap t ht (hBF hb))⟩
  change ¬ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryParallel S x R qa
  have hBQ : B ⊆ frontier Q := by
    rw [regional_original_chart_Q_frontier
      (chartAt (EuclideanSpace ℝ (Fin 2)) x)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R hR htarget]
  have hBdisj : ∀ i, Disjoint B (c i).val.image :=
    fun i => (hbaseDisjoint i).symm
  intro hparallel
  apply haess
  exact regional_Q_boundary_parallel_reflects_F Q F B hBQ hbase
    hFcompact.isClosed J c hBdisj hfrontier a ha0 ha1 hap
    qa.val (fun _ => rfl) hparallel

#print axioms regional_original_F_essential_arc_is_Q_essential
