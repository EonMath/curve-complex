import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

/-!
Statement-only dependency contracts for Fact 3.5 and the topological
joint-minimum step in the lower bound of Theorem 5.5.

Source: curve-complex-formalization/references/curve-complex-genus-two.txt,
lines 308--320 and 906--942. Blueprint: plan_joint_equivariant_minimum/PLAN.md.
All theorem bodies are intentional proof obligations. No definition is replaced.
The original actual_nonloop_pair_minimum_full_preimages is not redeclared here.
-/

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane

/-- U1: use an endpoint parametrization of the second image. The supplied
parametrization of `b` need not have the orientation of `a`. -/
theorem ambient_image_isotopy_has_freely_homotopic_endpoint_curve
    {E : Type} [TopologicalSpace E]
    (a b : Curve E) (hab : AmbientIsotopy.Rel a.image b.image) :
    ∃ b' : Curve E, b'.image = b.image ∧
      FreeHomotopic ⟨a.map, a.embedded.continuous⟩
        ⟨b'.map, b'.embedded.continuous⟩ := by
  obtain ⟨K, hK⟩ := hab
  obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
  have hefinal : (e : E → E) = K.finalMap := funext he
  let b' : Curve E := ⟨e ∘ a.map, e.isEmbedding.comp a.embedded⟩
  have hb' : b'.image = b.image := by
    change Set.range (e ∘ a.map) = b.image
    rw [Set.range_comp, hefinal]
    exact hK
  refine ⟨b', hb', ?_⟩
  refine ⟨⟨fun zt => K.map (zt.2, a.map zt.1),
    K.map.continuous.comp
      (continuous_snd.prodMk (a.embedded.continuous.comp continuous_fst))⟩, ?_, ?_⟩
  · intro z
    exact K.at_zero (a.map z)
  · intro z
    exact (he (a.map z)).symm

section Surface

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- U2: Fact 3.5(G1) uniqueness at the level of ambient-isotopic images. -/
theorem ambient_isotopic_closed_geodesic_images_eq
    (H : ClosedHyperbolicMetric E) (hE : IsGenus E 2)
    (a : EssentialCurve E) (b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.val.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hab : AmbientIsotopy.Rel a.val.image b.image) :
    a.val.image = b.image := by
  obtain ⟨g, _, _, _, huniq⟩ :=
    essential_curve_geodesic_exists_unique_genus_two H a.val a.property hE
  have haa : FreeHomotopic ⟨a.val.map, a.val.embedded.continuous⟩
      ⟨a.val.map, a.val.embedded.continuous⟩ := by
    exact ⟨⟨fun zt => a.val.map zt.1,
      a.val.embedded.continuous.comp continuous_fst⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨b', hb', hhom⟩ :=
    ambient_image_isotopy_has_freely_homotopic_endpoint_curve a.val b hab
  have hb'geo : letI : MetricSpace E := H.metric; IsClosedGeodesic b'.image := by
    simpa only [hb'] using hbgeo
  exact (huniq a.val haa hageo).trans ((huniq b' hhom hb'geo).symm.trans hb')

/-- U3a: an isometry of the supplied metric transports geodesic images. -/
theorem closed_geodesic_image_of_isometry
    (H : ClosedHyperbolicMetric E) (τ : E ≃ₜ E)
    (hτ : letI : MetricSpace E := H.metric; Isometry τ)
    (A : Set E)
    (hA : letI : MetricSpace E := H.metric; IsClosedGeodesic A) :
    letI : MetricSpace E := H.metric; IsClosedGeodesic (τ '' A) := by
  letI : MetricSpace E := H.metric
  obtain ⟨γ, period, hperiod, hcont, hper, himage, hlocal⟩ := hA
  refine ⟨τ ∘ γ, period, hperiod, τ.continuous.comp hcont, ?_, ?_, ?_⟩
  · intro t
    exact congrArg τ (hper t)
  · rw [Set.range_comp, himage]
  · intro t
    obtain ⟨ε, hε, hdist⟩ := hlocal t
    refine ⟨ε, hε, ?_⟩
    intro s u hs hu
    exact (hτ.dist_eq (γ s) (γ u)).trans (hdist s u hs hu)

/-- U3: select a geodesic in one supplied invariant ambient-isotopy class.
The class-fixing hypothesis concerns this `a` alone. -/
theorem fixed_class_has_invariant_geodesic_representative
    (H : ClosedHyperbolicMetric E) (hE : IsGenus E 2)
    (τ : E ≃ₜ E) (hτ : letI : MetricSpace E := H.metric; Isometry τ)
    (a : EssentialCurve E)
    (haτ : AmbientIsotopy.Rel (τ '' a.val.image) a.val.image) :
    ∃ g : EssentialCurve E,
      Quotient.mk (essentialCurveSetoid E) g =
        Quotient.mk (essentialCurveSetoid E) a ∧
      (letI : MetricSpace E := H.metric; IsClosedGeodesic g.val.image) ∧
      τ '' g.val.image = g.val.image := by
  obtain ⟨c, hc, hhom, hcgeo, _⟩ :=
    essential_curve_geodesic_exists_unique_genus_two H a.val a.property hE
  let g : EssentialCurve E := ⟨c, hc⟩
  have hag : AmbientIsotopy.Rel a.val.image g.val.image :=
    essential_curves_homotopic_implies_isotopic H a.val c a.property hc hhom
  let b : Curve E := ⟨τ ∘ g.val.map, τ.isEmbedding.comp g.val.embedded⟩
  have hbimage : b.image = τ '' g.val.image := by
    change Set.range (τ ∘ g.val.map) = τ '' Set.range g.val.map
    exact Set.range_comp _ _
  have htransport : AmbientIsotopy.Rel (τ '' a.val.image) (τ '' g.val.image) := by
    obtain ⟨K, hK⟩ := hag
    let L : AmbientIsotopy E := {
      map := ⟨fun tx => τ (K.map (tx.1, τ.symm tx.2)), by
        exact τ.continuous.comp (K.map.continuous.comp
          (continuous_fst.prodMk (τ.symm.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨k, hk⟩ := K.homeomorphism_at t
        refine ⟨(τ.symm.trans k).trans τ, ?_⟩
        intro x
        change τ (k (τ.symm x)) = τ (K.map (t, τ.symm x))
        rw [hk]
      at_zero := by
        intro x
        change τ (K.map (⟨0, by norm_num⟩, τ.symm x)) = x
        rw [K.at_zero, τ.apply_symm_apply] }
    refine ⟨L, ?_⟩
    change (τ ∘ K.finalMap ∘ τ.symm) '' (τ '' a.val.image) = τ '' g.val.image
    rw [Set.image_comp, Set.image_comp]
    simp only [Set.image_image, τ.symm_apply_apply]
    change (τ ∘ K.finalMap) '' a.val.image = τ '' g.val.image
    rw [Set.image_comp, hK]
  have hgb : AmbientIsotopy.Rel g.val.image b.image := by
    rw [hbimage]
    exact ambientIsotopy_equivalence.trans (ambientIsotopy_equivalence.symm hag)
      (ambientIsotopy_equivalence.trans (ambientIsotopy_equivalence.symm haτ) htransport)
  have hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image := by
    rw [hbimage]
    exact closed_geodesic_image_of_isometry H τ hτ g.val.image hcgeo
  have heq := ambient_isotopic_closed_geodesic_images_eq H hE g b hcgeo hbgeo hgb
  refine ⟨g, (Quotient.sound hag).symm, hcgeo, ?_⟩
  exact hbimage.symm.trans heq.symm

end Surface

end CurveComplex.Hyperbolic.JointMinimum
