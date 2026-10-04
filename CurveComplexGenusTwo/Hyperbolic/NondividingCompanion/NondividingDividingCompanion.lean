import CurveComplexGenusTwo.Hyperbolic.NondividingCompanion.ActualNondividingCurveHasSingleCrossingDualREQUEST
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryInput
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualBandBase
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualUnorientedOutsideBands
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.ActualBandBoundary
import CurveComplexGenusTwo.Topology.PositionExtension.TwistedBandReflection

namespace CurveComplex.Hyperbolic
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_nondividing_essential_curve_disjoint_dividing_curve
    (M : HyperellipticModel E S) (c : Curve E) (hc : Essential c)
    (hndiv : ¬ DividingCurve c) :
    ∃ y : Curve E, Essential y ∧ DividingCurve y ∧ Disjoint c.image y.image := by
  classical
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hns : Nonseparating c := by
    simpa only [Nonseparating, DividingCurve, not_not] using hndiv
  obtain ⟨e, he, hezero⟩ :=
    LocalSurgery.actual_original_essential_circle_has_annular_collar
      E 2 (by norm_num) M.genusTwo ⟨c, hc⟩
  let left : Set.Ioo (-1 : ℝ) 1 := ⟨-1/2, by norm_num⟩
  let right : Set.Ioo (-1 : ℝ) 1 := ⟨1/2, by norm_num⟩
  have havoid (s : Set.Ioo (-1 : ℝ) 1) (hs : (s : ℝ) ≠ 0) :
      e (s, (1 : Circle)) ∉ c.image := by
    rintro ⟨w, hw⟩
    have hz := he.injective (hw.symm.trans (hezero w).symm)
    exact hs (congrArg (fun z : Set.Ioo (-1 : ℝ) 1 × Circle => (z.1 : ℝ)) hz)
  have hleft : e (left, (1 : Circle)) ∉ c.image := havoid left (by norm_num [left])
  have hright : e (right, (1 : Circle)) ∉ c.image := havoid right (by norm_num [right])
  let connector : Path (e (left, (1 : Circle))) (e (right, (1 : Circle))) :=
    source_nonseparating_complement_path E c hns _ _ hleft hright
  have hconnector (t : Interval) : connector t ∉ c.image :=
    source_nonseparating_complement_path_avoids E c hns _ _ hleft hright t
  -- Exact geometric residual: embed and close an opposite-side connector,
  -- retaining the original c and one genuine local crossing.
  have hdual : ∃ b : Curve E, ∃ ht : Transverse c b,
      ht.1.toFinset.card = 1 :=
    actual_nondividing_essential_curve_has_single_crossing_dual M c hc hndiv
  obtain ⟨b, ht, hcount⟩ := hdual
  obtain ⟨D⟩ := exists_oneCrossingBandBase c b ht hcount
  obtain ⟨U⟩ := exists_actual_unoriented_outside_bands D
  have hfirst : U.firstFlip = false := by
    cases hh : U.firstFlip
    · rfl
    · obtain ⟨x, ⟨W⟩⟩ := GenusOrientationCandidate.first_twisted_band_local_reflection D U hh
      exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 M.genusTwo x
        (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W)
  have hsecond : U.secondFlip = false := by
    cases hh : U.secondFlip
    · rfl
    · obtain ⟨x, ⟨W⟩⟩ := GenusOrientationCandidate.second_twisted_band_local_reflection D U hh
      exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 M.genusTwo x
        (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W)
  let B : CompatibleOutsideBands D := {
    first := U.first, second := U.second
    first_embedded := U.first_embedded, second_embedded := U.second_embedded
    first_center := U.first_center, second_center := U.second_center
    first_bottom := U.first_bottom
    first_top := by
      intro w
      simpa only [hfirst, flipBandWidth, Bool.false_eq_true, ↓reduceIte] using U.first_top w
    second_left := U.second_left
    second_right := by
      intro w
      simpa only [hsecond, flipBandWidth, Bool.false_eq_true, ↓reduceIte] using U.second_right w
    bands_disjoint := U.bands_disjoint
    first_square := U.first_square, second_square := U.second_square }
  obtain ⟨y, hfront, hcy, _⟩ :=
    essential_frontier_of_actual_compatible_bands (by norm_num : 2 ≤ 2) M.genusTwo D B
  let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
  obtain ⟨hcompact, _, hinside, _⟩ :=
    FrontierHeaders.exists_frontier_circle_of_compatibleOutsideBands D B
  have hclosed : IsClosed N := hcompact.isClosed
  have hinterior : (interior N).Nonempty :=
    ⟨c.map 1, hinside (Or.inl (Set.mem_range_self _))⟩
  have hexterior : Nᶜ.Nonempty := by
    by_contra hempty
    have hn : N = Set.univ := Set.eq_univ_iff_forall.mpr (by
      intro x
      by_contra hx
      exact hempty ⟨x, hx⟩)
    have hyempty : y.val.image = ∅ := by
      rw [← hfront]
      change frontier N = ∅
      rw [hn, frontier_univ]
    have hyone : y.val.map 1 ∈ y.val.image := Set.mem_range_self _
    rw [hyempty] at hyone
    exact hyone
  refine ⟨y.val, y.property, ?_, hcy⟩
  change ¬ IsConnected y.val.imageᶜ
  intro hconnected
  have hcover : y.val.imageᶜ ⊆ interior N ∪ Nᶜ := by
    rw [← hfront]
    intro x hx
    by_cases hxN : x ∈ N
    · left
      by_contra hxi
      exact hx (by
        rw [frontier, hclosed.closure_eq]
        exact ⟨hxN, hxi⟩)
    · exact Or.inr hxN
  have hdisjoint : Disjoint (interior N) Nᶜ :=
    Set.disjoint_left.mpr (fun _ hx hxc => hxc (interior_subset hx))
  rcases hconnected.isPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl
      hdisjoint hcover with hi | ho
  · obtain ⟨x, hx⟩ := hexterior
    have hxy : x ∈ y.val.imageᶜ := by
      rw [← hfront]
      exact fun hh => hx (hclosed.frontier_subset hh)
    exact hx (interior_subset (hi hxy))
  · obtain ⟨x, hx⟩ := hinterior
    have hxy : x ∈ y.val.imageᶜ := by
      rw [← hfront]
      intro hh
      rw [frontier] at hh
      exact hh.2 hx
    exact ho hxy (interior_subset hx)

end CurveComplex.Hyperbolic
