import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalEndpointFixedPushOff
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip

open CurveComplex Set Topology
open scoped Manifold ContDiff

namespace RegionalEmbeddedFamily

theorem original_region_proper_arc_has_fixed_endpoint_clean_push_off
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
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F) :
    ∃ (q : C(Interval, ↥F)) (H : C(Interval × Interval, ↥F)),
      Topology.IsEmbedding q ∧
      q 0 = a 0 ∧ q 1 = a 1 ∧
      (∀ s ∈ Set.Ioo (0 : Interval) 1,
        (q s).val ∉ frontier F) ∧
      (∀ s t, a s = q t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      (∀ s, H (0,s) = a s ∧ H (1,s) = q s) ∧
      (∀ t, Topology.IsEmbedding (fun s => H (t,s))) ∧
      (∀ t, H (t,0) = a 0 ∧ H (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (H (t,s)).val ∉ frontier F) := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨E, hE, hcenter, hend, hint, hopen⟩ :=
    regional_original_proper_arc_has_F_strip
      S g hg hS x R hR htarget F hFcompact hbase houtside J c
      hbaseDisjoint hfrontier a ha ha0 ha1 haClear
  exact embedded_strip_tapered_fixed_endpoint_push_off F a E hE hcenter
    (fun s hs w hf =>
      ((mem_frontier_iff_notMem_interior (interior_subset (hint s hs w))).mp hf)
        (hint s hs w))

end RegionalEmbeddedFamily
