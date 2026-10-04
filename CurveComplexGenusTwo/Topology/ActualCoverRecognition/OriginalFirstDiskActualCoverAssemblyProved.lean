import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalActualCoverRecognitionProved
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalBRecognitionConsumer
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskNullCurveBridge
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCountableUniversalCoverHeader
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCoverDomainTransportHeader
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalSphereCoverDiskHeader
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter

namespace CurveComplex.LocalSurgery
open scoped Manifold ContDiff
theorem actual_original_returning_subarc_produces_two_curve_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (genus : ℕ) (hgenus : 2 ≤ genus) (hS : CurveComplex.IsGenus S genus)
    (a b : CurveComplex.EssentialCurve S)
    (ht : CurveComplex.Transverse a.val b.val)
    (u z : S) (huz : u ≠ z) (f g : Path u z)
    (hf : Topology.IsEmbedding f)
    (hfcurve : Set.range f ⊆ a.val.image)
    (hgcurve : Set.range g ⊆ b.val.image)
    (hclean : f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.val.imageᶜ)
    (hhom : f.Homotopic g) :
    Nonempty (CurveComplex.LocalSurgery.TwoCurveDisk a.val b.val) := by
  classical
  have hComparison : ∃ g' : Path u z, Topology.IsEmbedding g' ∧
      Set.range g' ⊆ b.val.image ∧ f.Homotopic g' := by
    exact actual_original_returning_comparison_has_embedded_path
      S genus hgenus hS a b ht u z huz f g hf hfcurve hgcurve hclean hhom
  obtain ⟨g',hg',hg'curve,hhom'⟩ := hComparison
  obtain ⟨c,hc,hcnull⟩ := actual_embedded_homotopic_clean_paths_produce_null_curve
    b.val u z huz f g' hf hg' hg'curve hclean hhom'
  let U := Σ y : S, Path.Homotopic.Quotient u y
  obtain ⟨t,hCover⟩ := closed_surface_actual_second_countable_universal_cover u
  letI : TopologicalSpace U := t
  rcases hCover with ⟨hSC,hT2,hChart,hSimply,hQuot,hSurj,hLift⟩
  letI : SecondCountableTopology U := hSC
  letI : T2Space U := hT2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U := hChart.some
  letI : SimplyConnectedSpace U := hSimply
  let p : U → S := Sigma.fst
  have hModel : Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) ∨
      Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₜ U) := by
    exact closed_surface_simply_connected_cover_plane_or_sphere p hQuot.isCoveringMap hSurj
  have hDisc : BoundsDisc c := by
    rcases hModel with hPlane | hSphere
    · obtain ⟨e⟩ := hPlane
      obtain ⟨action,hq⟩ := actual_quotient_cover_domain_homeomorph_transport p hQuot e
      letI := action
      exact CurveComplex.boundsDisc_of_nullhomotopic_planar_quotient_cover_complete
        (p ∘ e) hq c hcnull
    · obtain ⟨e⟩ := hSphere
      obtain ⟨action,hq⟩ := actual_quotient_cover_domain_homeomorph_transport p hQuot e
      letI := action
      exact boundsDisc_of_nullhomotopic_spherical_quotient_cover_complete
        (p ∘ e) hq c hcnull
  obtain ⟨d,hd,hdb⟩ := hDisc
  have hSides : Set.range f ∩ Set.range g' = {u,z} := by
    ext x
    constructor
    · rintro ⟨⟨s,hs⟩,⟨v,hv⟩⟩
      by_cases hs0 : s = 0
      · left
        simpa only [hs0,Path.source] using hs.symm
      by_cases hs1 : s = 1
      · right
        simpa only [hs1,Path.target,Set.mem_singleton_iff] using hs.symm
      have hx : x ∈ b.val.imageᶜ := hclean
        ⟨s,⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
          lt_of_le_of_ne s.property.2 hs1⟩,hs⟩
      exact (hx (hg'curve ⟨v,hv⟩)).elim
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · subst x
        exact ⟨⟨0,f.source⟩,⟨0,g'.source⟩⟩
      · have hx' : x = z := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨1,f.target⟩,⟨1,g'.target⟩⟩
  exact ⟨{
    firstCorner := u, secondCorner := z, corners_ne := huz
    firstSide := ⟨f,f.continuous⟩, secondSide := ⟨g',g'.continuous⟩
    first_embedded := hf, second_embedded := hg'
    first_zero := f.source, second_zero := g'.source
    first_one := f.target, second_one := g'.target
    first_on_curve := hfcurve, second_on_curve := hg'curve
    sides_inter := hSides, disk := d, disk_embedded := hd
    boundary_eq := hdb.trans hc }⟩

end CurveComplex.LocalSurgery
