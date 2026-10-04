import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.FiniteCarrierProved
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.FiniteRealizationCompactHeader
import CurveComplexGenusTwo.CWHurewicz.CWGeometricAlgebra
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface

open CategoryTheory CategoryTheory.Limits Topology
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false
open CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier

/-- Every actual singular homology class is induced from a compact subspace. -/
theorem homology_class_compact_support
    (S : Type) [TopologicalSpace S] (n : ℕ) (z : H S n) :
    ∃ K : Set S, IsCompact K ∧ ∃ w : H K n,
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(K,S)))) w = z := by
  classical
  let X := TopCat.of S
  obtain ⟨c, hc⟩ := CWGeometricChains.cycleClass_surjective (X := S) n z
  obtain ⟨A, hA, hdim, v, hv⟩ := finite_cycle_carrier X n c
  letI : SSet.Finite A := hA
  let P := SSet.toTop.obj A.toSSet
  letI : CompactSpace P := finite_realization_compactSpace A.toSSet
  let p : P ⟶ X := SSet.toTop.map A.ι ≫ sSetTopAdj.counit.app X
  obtain ⟨u, hu⟩ := cycle_realization_push X A n v
  have hcycle : HomologicalComplex.cyclesMap (actualSingularFunctor.map p) n u = c := by
    apply (ModuleCat.mono_iff_injective ((singularChains X).iCycles n)).mp inferInstance
    have hi := congrArg (fun q => q u)
      (HomologicalComplex.cyclesMap_i (actualSingularFunctor.map p) n)
    change (singularChains X).iCycles n
      (HomologicalComplex.cyclesMap (actualSingularFunctor.map p) n u) =
      (actualSingularFunctor.map p).f n ((singularChains P).iCycles n u) at hi
    exact hi.trans (hu.trans hv)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  let qclass : H P n := (singularChains P).homologyπ n u
  have hpclass : F.map p qclass = z := by
    have hn := congrArg (fun q => q u)
      (HomologicalComplex.homologyπ_naturality (actualSingularFunctor.map p) n)
    change F.map p qclass = (singularChains X).homologyπ n
        (HomologicalComplex.cyclesMap (actualSingularFunctor.map p) n u) at hn
    rw [hcycle] at hn
    exact hn.trans hc
  let K : Set S := Set.range p
  have hK : IsCompact K := isCompact_range p.hom.continuous
  let q : C(P,K) := ⟨fun x => ⟨p x, Set.mem_range_self x⟩,
    p.hom.continuous.subtype_mk _⟩
  let j : C(K,S) := ⟨Subtype.val, continuous_subtype_val⟩
  have hfactor : TopCat.ofHom q ≫ TopCat.ofHom j = p := by
    ext x
    rfl
  refine ⟨K, hK, F.map (TopCat.ofHom q) qclass, ?_⟩
  change F.map (TopCat.ofHom j) (F.map (TopCat.ofHom q) qclass) = z
  change (F.map (TopCat.ofHom q) ≫ F.map (TopCat.ofHom j)) qclass = z
  rw [← F.map_comp, hfactor]
  exact hpclass

/-- Vanishing of an actual localized class persists on a neighborhood of the
point, since a puncture-avoiding representative has compact support. -/
theorem homology_localization_zero_locus_open
    (S : Type) [TopologicalSpace S] [T2Space S] (n : ℕ) (z : H S n) :
    IsOpen {x : S | homologyToRelative S ({x}ᶜ : Set S) n z = 0} := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨hzero, hexact⟩ := pairHomology_exact_at_absolute S ({x}ᶜ : Set S) n
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hexact z hx
  obtain ⟨K, hK, v, hv⟩ := homology_class_compact_support
    (↥({x}ᶜ : Set S)) n w
  let L : Set S := Subtype.val '' K
  have hL : IsCompact L := hK.image continuous_subtype_val
  have hxL : x ∈ Lᶜ := by
    rintro ⟨t, ht, he⟩
    have htx : t.val ≠ x := t.property
    exact htx he
  apply Filter.mem_of_superset (hL.isClosed.isOpen_compl.mem_nhds hxL)
  intro y hy
  let jx : C(K, ↥({x}ᶜ : Set S)) := ⟨Subtype.val, continuous_subtype_val⟩
  have havoid (t : K) : t.val.val ∈ ({y}ᶜ : Set S) := by
    change t.val.val ≠ y
    intro he
    exact hy ⟨t.val, t.property, he⟩
  let jy : C(K, ↥({y}ᶜ : Set S)) := ⟨fun t => ⟨t.val.val, havoid t⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk havoid⟩
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  have hcomp : TopCat.ofHom jy ≫ pairInclusion S ({y}ᶜ : Set S) =
      TopCat.ofHom jx ≫ pairInclusion S ({x}ᶜ : Set S) := by
    ext t
    rfl
  let wy : H (↥({y}ᶜ : Set S)) n := F.map (TopCat.ofHom jy) v
  have hfactor : homologyInclusion S ({y}ᶜ : Set S) n wy = z := by
    change (F.map (TopCat.ofHom jy) ≫ F.map (pairInclusion S ({y}ᶜ : Set S))) v = z
    rw [← F.map_comp, hcomp, F.map_comp]
    change homologyInclusion S ({x}ᶜ : Set S) n (F.map (TopCat.ofHom jx) v) = z
    rw [hv]
    exact hw
  change homologyToRelative S ({y}ᶜ : Set S) n z = 0
  rw [← hfactor]
  obtain ⟨hz, he⟩ := pairHomology_exact_at_absolute S ({y}ᶜ : Set S) n
  have hh := congrArg (fun q => q wy) hz
  simpa using hh

end CurveComplex.GenusOrientationCandidate
