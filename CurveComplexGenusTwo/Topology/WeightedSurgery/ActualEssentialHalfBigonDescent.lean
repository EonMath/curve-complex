import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialHalfBigonSubdisk

namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual half-bigon subdisk loses the original unmarked corner.
Thus the disk crossing energy strictly decreases despite permitting the
shared marked corner in the closed disk. -/
theorem actual_essential_half_bigon_obstruction_strict_total_descent
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
    (hsystem : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (i j : ι) (hji : j ≠ i)
    (firstSide g : C(Interval,S)) (hg : IsEmbedding g)
    (hfirst : range firstSide ⊆ (old i).val.image) (hgnew : range g ⊆ a.val.image)
    (hzero : firstSide 0 = g 0) (hone : firstSide 1 = g 1)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S))
    (hmarkCorner : ∀ p ∈ range d, p ∈ (M.cover.branch : Set S) → p = g 0)
    (hlastFree : g 1 ∉ (M.cover.branch : Set S))
    (hboundary : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      range firstSide ∪ range g)
    (hfinite : ∀ k, (ArcSurgery.crossings M (old k) a).Finite)
    (hin : ((old j).val.image ∩
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
    ∃ (f g' : C(Interval,S))
      (d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)),
      IsEmbedding f ∧ IsEmbedding g' ∧ IsEmbedding d' ∧
      f 0 ≠ f 1 ∧ g' 0 = f 0 ∧ g' 1 = f 1 ∧
      range f ⊆ (old j).val.image ∧ range g' ⊆ a.val.image ∧
      range f ∩ range g' = {f 0,f 1} ∧
      d' '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range f ∪ range g' ∧
      range d' ⊆ range d ∧ g 1 ∉ range d' ∧
      Disjoint (d' '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S) ∧
      (∀ p ∈ range d', p ∈ (M.cover.branch : Set S) → p = g 0) ∧
      (∀ p ∈ range d', p ∈ (M.cover.branch : Set S) → p = f 0 ∨ p = f 1) ∧
      (∑ k, (ArcSurgery.crossings M (old k) a ∩ range d').ncard) <
        ∑ k, (ArcSurgery.crossings M (old k) a ∩ range d).ncard := by
  classical
  obtain ⟨f,g',d',hf,hg',hd',hfne,hg0,hg1,hfon,hgon,hsides,hbd,hsub,hmissing,hmarks',hcorner',hcorners'⟩ :=
    actual_essential_half_bigon_obstruction_produces_subdisk M old hsystem a i j hji
      firstSide g hg hfirst hgnew hzero hone d hd hmarks hmarkCorner hlastFree hboundary hin
  refine ⟨f,g',d',hf,hg',hd',hfne,hg0,hg1,hfon,hgon,hsides,hbd,hsub,hmissing,hmarks',hcorner',hcorners',?_⟩
  have hsubrow (k : ι) :
      ArcSurgery.crossings M (old k) a ∩ range d' ⊆
        ArcSurgery.crossings M (old k) a ∩ range d :=
    fun p hp => ⟨hp.1,hsub hp.2⟩
  have hfiniteRow (k : ι) : (ArcSurgery.crossings M (old k) a ∩ range d).Finite :=
    (hfinite k).subset inter_subset_left
  apply Finset.sum_lt_sum
  · intro k _
    exact ncard_le_ncard (hsubrow k) (hfiniteRow k)
  · refine ⟨i,Finset.mem_univ i,?_⟩
    apply ncard_lt_ncard _ (hfiniteRow i)
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hsubrow i,?_⟩
    intro heq
    have hgK : g 1 ∈ range d := image_subset_range _ _
      (hboundary.symm ▸ (show g 1 ∈ range firstSide ∪ range g from Or.inr ⟨1,rfl⟩))
    have hcorner : g 1 ∈ ArcSurgery.crossings M (old i) a ∩ range d :=
      ⟨⟨⟨hfirst ⟨1,hone⟩,hlastFree⟩,hgnew ⟨1,rfl⟩,hlastFree⟩,hgK⟩
    rw [← heq] at hcorner
    exact hmissing hcorner.2

#print axioms actual_essential_half_bigon_obstruction_strict_total_descent
end CurveComplex.HyperellipticModel
