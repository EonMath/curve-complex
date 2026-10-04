import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

namespace CurveComplex.GenusOrientationCandidate

set_option backward.isDefEq.respectTransparency false

private noncomputable abbrev localH₂ (S : Type) [TopologicalSpace S] (x : S) :=
  relativeHomology S ({x}ᶜ : Set S) 2

private noncomputable abbrev localize (S : Type) [TopologicalSpace S] (x : S) :
    integralHomology S 2 ⟶ localH₂ S x :=
  homologyToRelative S ({x}ᶜ : Set S) 2

/-- This is an exact equivalence for actual singular homology, not an orientation
assumption encoded as a definition. It identifies the geometric vanishing target. -/
private theorem localize_mono_iff_puncture_map_zero
    (S : Type) [TopologicalSpace S] (x : S) :
    Mono (localize S x) ↔ homologyInclusion S ({x}ᶜ : Set S) 2 = 0 := by
  obtain ⟨hz, hexact⟩ := pairHomology_exact_at_absolute S ({x}ᶜ : Set S) 2
  constructor
  · intro h
    letI := h
    apply (cancel_mono (localize S x)).1
    simpa only [CategoryTheory.Limits.zero_comp] using hz
  · intro h
    exact hexact.mono_g h

private theorem localize_fixed_of_homotopic_id
    {S : Type} [TopologicalSpace S] (x : S) (f : C(S, S))
    (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
    (h : ContinuousMap.Homotopic f (ContinuousMap.id S)) :
    localize S x ≫ pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
      localize S x := by
  have hn := pairRelativeHomologyMap_commutes
    ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2
  have hh : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (𝟙 (TopCat.of S))) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      h.some (ModuleCat.of ℤ ℤ) 2
  have hid : HomologicalComplex.homologyMap
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) 2 =
      𝟙 (integralHomology S 2) := by
    change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) = _
    rw [hh]
    exact CategoryTheory.Functor.map_id _ _
  rw [hid] at hn
  change localize S x ≫ pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
    𝟙 (integralHomology S 2) ≫ localize S x at hn
  simpa only [Category.id_comp] using hn

private theorem genus_eq_neg_iff
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (z : integralHomology S 2) :
    z = -z ↔ z = 0 := by
  obtain ⟨e⟩ := hS.2.2.1
  constructor
  · intro hz
    have he : e.hom.hom z = -(e.hom.hom z) := by
      simpa using congrArg e.hom.hom hz
    have he' : (e.hom.hom z : ℤ) = -(e.hom.hom z : ℤ) := he
    change (e.hom.hom z : ℤ) = Int.neg (e.hom.hom z : ℤ) at he'
    have hzero : (e.hom.hom z : ℤ) = 0 := by
      have := eq_neg_iff_add_eq_zero.mp he'
      linarith
    apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
    simpa using hzero
  · rintro rfl
    simp

private theorem no_local_reflection_of_puncture_map_zero
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (x : S)
    (hpuncture : homologyInclusion S ({x}ᶜ : Set S) 2 = 0)
    (f : C(S, S))
    (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
    (h : ContinuousMap.Homotopic f (ContinuousMap.id S)) :
    pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 ≠
      -(𝟙 (localH₂ S x)) := by
  intro hnegative
  haveI : Mono (localize S x) :=
    (localize_mono_iff_puncture_map_zero S x).mpr hpuncture
  obtain ⟨e⟩ := hS.2.2.1
  let z : integralHomology S 2 := e.inv (1 : ℤ)
  have hz : z ≠ 0 := by
    intro hz
    have hi := e.inv_hom_id_apply (1 : ℤ)
    change e.hom z = 1 at hi
    rw [hz] at hi
    simpa using hi
  have he := localize_fixed_of_homotopic_id x f hf h
  rw [hnegative, Preadditive.comp_neg, Category.comp_id] at he
  have hzneg : z = -z := by
    apply (ModuleCat.mono_iff_injective (localize S x)).mp inferInstance
    have hp := congrArg (fun q : integralHomology S 2 ⟶ localH₂ S x => q z) he
    simpa using hp.symm
  exact hz ((genus_eq_neg_iff g hS z).mp hzneg)

structure LocalReflectionWitness
    {S : Type} [TopologicalSpace S] (x : S) where
  map : C(S, S)
  preserves : ∀ y ∈ ({x}ᶜ : Set S), map y ∈ ({x}ᶜ : Set S)
  isotopy : ContinuousMap.Homotopic map (ContinuousMap.id S)
  acts_neg : pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S)
      map preserves 2 = -(𝟙 (localH₂ S x))

theorem no_local_reflection_witness
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (x : S)
    (hpuncture : homologyInclusion S ({x}ᶜ : Set S) 2 = 0)
    (W : LocalReflectionWitness x) : False := by
  exact no_local_reflection_of_puncture_map_zero g hS x hpuncture
    W.map W.preserves W.isotopy W.acts_neg

end CurveComplex.GenusOrientationCandidate
