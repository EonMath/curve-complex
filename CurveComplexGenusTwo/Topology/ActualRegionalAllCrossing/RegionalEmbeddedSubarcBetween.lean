import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFiniteMovieAssembly
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

theorem regional_embedded_subarc_between
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : C(Interval,X)) (ha : Topology.IsEmbedding a)
    (s t : Interval) (hst : s ≠ t) :
    ∃ first : Path (a s) (a t), Topology.IsEmbedding first ∧
      Set.range first ⊆ Set.range a := by
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · obtain ⟨first,hfirst,hrange,_⟩ :=
      LocalSurgery.actual_embedded_affine_subarc a ha s t hlt
    exact ⟨first,hfirst,hrange.trans (Set.image_subset_range a _)⟩
  · obtain ⟨first,hfirst,hrange,_⟩ :=
      LocalSurgery.actual_embedded_affine_subarc a ha t s hgt
    refine ⟨first.symm,?_,?_⟩
    · exact hfirst.comp unitInterval.symmHomeomorph.isEmbedding
    · simpa only [Path.symm_range] using hrange.trans (Set.image_subset_range a _)

end RegionalEmbeddedFamily
