import CurveComplexGenusTwo.Topology.Orientation.CircleReflection
import CurveComplexGenusTwo.Topology.Orientation.Radial
import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.CWHurewicz.ConnectingNaturality
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

namespace CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

/-- The actual linear reflection fixing the first coordinate. -/
def planeReflection : C(ℝ × ℝ, ℝ × ℝ) :=
  ⟨fun z => (z.1, -z.2), continuous_fst.prodMk continuous_snd.neg⟩

 theorem planeReflection_preserves_puncture :
    ∀ z ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)),
      planeReflection z ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)) := by
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
  intro h
  apply hz
  apply Prod.ext
  · simpa [planeReflection] using congrArg Prod.fst h
  · have hsecond := congrArg Prod.snd h
    change -z.2 = 0 at hsecond
    exact neg_eq_zero.mp hsecond

noncomputable def circleIntoPlane : C(Circle, ReflectionRadial.PPlane) :=
  (⟨ReflectionRadial.complexPlane, ReflectionRadial.complexPlane.continuous⟩ : C(ReflectionRadial.Punctured ℂ,ReflectionRadial.PPlane)).comp ReflectionRadial.circleInclusion

noncomputable def circlePlaneH1Iso : H Circle 1 ≅ H ReflectionRadial.PPlane 1 :=
  (ReflectionRadial.circlePuncturedIso 1).symm ≪≫
    (CircleHomologyComputation.HF 1).mapIso (TopCat.isoOfHomeo ReflectionRadial.complexPlane)

lemma circleIntoPlane_map_eq :
    (CircleHomologyComputation.HF 1).map (TopCat.ofHom circleIntoPlane) = circlePlaneH1Iso.hom := by
  change _ = (CircleHomologyComputation.HF 1).map (TopCat.ofHom ReflectionRadial.circleInclusion) ≫
    (CircleHomologyComputation.HF 1).map (TopCat.ofHom (⟨ReflectionRadial.complexPlane, ReflectionRadial.complexPlane.continuous⟩ : C(ReflectionRadial.Punctured ℂ,ReflectionRadial.PPlane)))
  rw [← Functor.map_comp]
  rfl

lemma circleIntoPlane_reflection :
    TopCat.ofHom circleIntoPlane ≫ pairMapOnSubspace ({(0,0)}ᶜ : Set (ℝ × ℝ))
      ({(0,0)}ᶜ : Set (ℝ × ℝ)) planeReflection planeReflection_preserves_puncture =
    TopCat.ofHom circleInverse ≫ TopCat.ofHom circleIntoPlane := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change ((z : ℂ).re,-(z : ℂ).im) = (((z⁻¹ : Circle) : ℂ).re,((z⁻¹ : Circle) : ℂ).im)
  rw [Circle.coe_inv_eq_conj]
  rfl

lemma puncturedPlane_reflection_homology :
    (CircleHomologyComputation.HF 1).map
      (pairMapOnSubspace ({(0,0)}ᶜ : Set (ℝ × ℝ)) ({(0,0)}ᶜ : Set (ℝ × ℝ))
        planeReflection planeReflection_preserves_puncture) =
      -(𝟙 (H ReflectionRadial.PPlane 1)) := by
  let F := CircleHomologyComputation.HF 1
  haveI : Epi (F.map (TopCat.ofHom circleIntoPlane)) := by
    rw [circleIntoPlane_map_eq]
    infer_instance
  apply (cancel_epi (F.map (TopCat.ofHom circleIntoPlane))).1
  rw [← F.map_comp,circleIntoPlane_reflection,F.map_comp,
    circleInverse_homologyMap_eq_neg_id,Preadditive.neg_comp,Category.id_comp,
    Preadditive.comp_neg,Category.comp_id]

/-- Reflection acts by negative identity on the actual local degree-two
relative singular homology of the plane. -/
theorem planeReflection_relativeHomologyMap_eq_neg_id :
    pairRelativeHomologyMap ({(0,0)}ᶜ : Set (ℝ × ℝ))
      ({(0,0)}ᶜ : Set (ℝ × ℝ)) planeReflection
      planeReflection_preserves_puncture 2 =
      -(𝟙 (relativeHomology (ℝ × ℝ) ({(0,0)}ᶜ : Set (ℝ × ℝ)) 2)) := by
  let A : Set (ℝ × ℝ) := {(0,0)}ᶜ
  have hz : IsZero (H (ℝ × ℝ) 2) :=
    CircleHomologyComputation.contractible_positive_homology (ℝ × ℝ) 2 (by decide)
  obtain ⟨hzero, hexact⟩ := pairHomology_exact_at_relative (ℝ × ℝ) A 1
  haveI : Mono (relativeConnecting (ℝ × ℝ) A 1) :=
    hexact.mono_g (hz.eq_of_src _ _)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  have hnegative : F.map (pairMapOnSubspace A A planeReflection
      planeReflection_preserves_puncture) = -(𝟙 (H A 1)) := by
    exact puncturedPlane_reflection_homology
  apply (cancel_mono (relativeConnecting (ℝ × ℝ) A 1)).1
  have hn := relativeConnecting_natural A A planeReflection
    planeReflection_preserves_puncture 1
  change relativeConnecting (ℝ × ℝ) A 1 ≫
      F.map (pairMapOnSubspace A A planeReflection planeReflection_preserves_puncture) =
    pairRelativeHomologyMap A A planeReflection planeReflection_preserves_puncture 2 ≫
      relativeConnecting (ℝ × ℝ) A 1 at hn
  rw [hnegative, Preadditive.comp_neg, Category.comp_id] at hn
  simpa only [Preadditive.neg_comp, Category.id_comp] using hn.symm

end CurveComplex.GenusOrientationCandidate
