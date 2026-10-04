import CurveComplexGenusTwo.Topology.ActualHaasUniqueness.HaasLocalUniquenessComplete85
import CurveComplexGenusTwo.Hyperbolic.ActualHaasInvariantConstruction.HaasBothOrientationsMinimal
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualInducedClosedHyperbolicMetricProof
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1OriginalGenusAdaptersPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG3.ActualOriginalUnrestrictedG3PROVED
import CurveComplexGenusTwo.Hyperbolic.NondividingCompanion.NondividingDividingCompanion

open Set Topology
open CurveComplex CurveComplex.Hyperbolic
namespace CurveComplex.HyperellipticModel
variable {E : Type} {S : Type}
  [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The original actual deck-invariant representative, using the same cover. -/
theorem essential_curve_has_deck_invariant_representative
    (M : HyperellipticModel E S) (c : EssentialCurve E) :
    ∃ d : EssentialCurve E,
      (essentialCurveSetoid E).r c d ∧
      M.cover.deck '' d.val.image = d.val.image := by
  classical
  let originalCover := M.cover
  let originalSphere := M.sphere
  obtain ⟨atlas,hgenus,H,hdeck,_⟩ := actual_induced_closed_hyperbolic_metric M
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E := atlas
  let N : HyperellipticModel E S :=
    { cover := originalCover, sphere := originalSphere, genusTwo := hgenus }
  have hNisom : letI : MetricSpace E := H.metric; Isometry (N.cover.deck : E → E) := hdeck
  have paired (a b : Curve E)
      (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
      (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
      (hadiv : DividingCurve a) (hbnondiv : ¬ DividingCurve b)
      (hab : Disjoint a.image b.image) :
      N.cover.deck '' a.image = a.image ∧ N.cover.deck '' b.image = b.image := by
    obtain ⟨J,hJinv,hJlocal,hJa,hJb,F,hFcard,hFset,φa,hJaClock,hφaHom,
      ub,eb,φb,hclockb,hJbClock,hφbHom⟩ :=
      haas_both_orientations_with_v N H a b hageo hbgeo hadiv hbnondiv hab
    have hfix : ∃ F : Finset E, (F : Set E) = {x : E | J x = x} ∧ F.card = 6 :=
      ⟨F,hFset,hFcard⟩
    have hUnique : J = N.cover.deck :=
      actual_genus_two_six_fixed_local_isometry_unique N H hNisom J hJlocal hJinv hfix
    exact ⟨by simpa only [hUnique] using hJa,by simpa only [hUnique] using hJb⟩
  have invariant (a : Curve E)
      (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image) :
      N.cover.deck '' a.image = a.image := by
    have ha : Essential a := actual_simple_closed_geodesic_essential H a hageo
    by_cases hadiv : DividingCurve a
    · obtain ⟨U,V,hU,hV,hUV,hcover,hfrontU,hfrontV,eU,eV⟩ :=
        actual_dividing_essential_curve_two_one_holed_tori N a ha hadiv
      obtain ⟨b,hbgeo,hbnondiv,hbV⟩ :=
        haas_prescribed_v_geodesic_consumer N H a hageo hadiv
          U V hU hV hUV hcover hfrontU hfrontV eV
      have hab : Disjoint a.image b.image := disjoint_left.mpr (by
        intro x hxa hxb
        have hxcompl : x ∈ a.imageᶜ := by rw [←hcover]; exact Or.inr (hbV hxb)
        exact hxcompl hxa)
      exact (paired a b hageo hbgeo hadiv hbnondiv hab).1
    · obtain ⟨y,hy,hydiv,hay⟩ :=
        actual_nondividing_essential_curve_disjoint_dividing_curve N a ha hadiv
      obtain ⟨b,hb,hhom,hparam,_⟩ :=
        essential_curve_geodesic_exists_unique_parametrized_genus_two H y hy N.genusTwo
      have hbgeo := parametrized_closed_geodesic_has_geodesic_image H
        ⟨b.map,b.embedded.continuous⟩ hparam
      have hiso := essential_curves_homotopic_implies_isotopic H y b hy hb hhom
      obtain ⟨I,hI⟩ := hiso
      obtain ⟨e,he⟩ := I.homeomorphism_at ⟨1,by norm_num⟩
      have hefinal : (e : E → E) = I.finalMap := funext he
      have himage : e '' y.image = b.image := by rw [hefinal]; exact hI
      have hbdiv : DividingCurve b := by
        change ¬ IsConnected b.imageᶜ
        rw [←himage,←e.image_compl]
        exact fun hh => hydiv (e.isConnected_image.mp hh)
      have hne : a.image ≠ b.image := by
        intro hh
        apply hadiv
        change ¬ IsConnected a.imageᶜ
        rw [hh]
        exact hbdiv
      have haa := actual_free_homotopic_refl ⟨a.map,a.embedded.continuous⟩
      have hby := actual_free_homotopic_symm ⟨y.map,y.embedded.continuous⟩ ⟨b.map,b.embedded.continuous⟩ hhom
      have hab := actual_distinct_closed_geodesics_disjoint_of_disjoint_classes H a b a y
        ha hb hageo hbgeo hne haa hby hay
      exact (paired b a hbgeo hageo hbdiv hadiv hab.symm).2
  obtain ⟨g,hg,hhom,hparam,_⟩ :=
    essential_curve_geodesic_exists_unique_parametrized_genus_two H c.val c.property N.genusTwo
  have hgeo := parametrized_closed_geodesic_has_geodesic_image H
    ⟨g.map,g.embedded.continuous⟩ hparam
  refine ⟨⟨g,hg⟩,?_,?_⟩
  · exact essential_curves_homotopic_implies_isotopic H c.val g c.property hg hhom
  · exact invariant g hgeo

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.essential_curve_has_deck_invariant_representative
