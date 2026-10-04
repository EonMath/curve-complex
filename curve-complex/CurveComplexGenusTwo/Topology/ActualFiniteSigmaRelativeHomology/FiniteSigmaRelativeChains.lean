import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Isomorphisms
import CurveComplexGenusTwo.Topology.ActualFiniteDiscDetection.FiniteWithSingletonCandidate

open CategoryTheory
open CurveComplexGenusTwo.CWHurewicz
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

macro "frozen%" n:ident : term =>
  pure (Lean.mkIdent (Lean.Name.str (Lean.Name.num
    ((Lean.Name.str .anonymous "_private").append `CurveComplexGenusTwo.Topology.ActualFiniteDiscDetection.FiniteWithSingletonCandidate) 0)
    n.getId.toString))

namespace FiniteSigmaRelativeChains

noncomputable abbrev decomposition :=
  (frozen% actual_singular_sigma_chains_equiv)

section
variable (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, TopologicalSpace (K i)]
variable (A : ∀ i, Set (K i))

noncomputable def componentChain (n : ℕ) (i : ι) :
    (relativeSingularChains (Σ j, K j) {z | z.2 ∈ A z.1}).X n →ₗ[ℤ]
      (relativeSingularChains (K i) (A i)).X n :=
  (canonicalRelativeProjection (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} n).liftOfSurjective
    (canonicalRelativeProjection_surjective _ _ _) ⟨
      (canonicalRelativeProjection (TopCat.of (K i)) (A i) n).comp
        ((LinearMap.proj i).comp (decomposition ι K n).toLinearMap), by
      intro c hc
      change canonicalRelativeProjection (TopCat.of (K i)) (A i) n
        ((decomposition ι K n c) i) = 0
      have hs : c ∈ excisionSubspaceChains (TopCat.of (Σ j, K j))
          {z | z.2 ∈ A z.1} n := by
        rwa [canonicalRelativeProjection_kernel] at hc
      have hi := ((frozen% actual_singular_sigma_subspace_chains_supported_iff)
        ι K A n c).mp hs i
      rwa [← canonicalRelativeProjection_kernel] at hi⟩

theorem componentChain_projection (n : ℕ) (i : ι)
    (c : (TopCat.toSSet.obj (TopCat.of (Σ j, K j))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    componentChain ι K A n i
      (canonicalRelativeProjection (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} n c) =
    canonicalRelativeProjection (TopCat.of (K i)) (A i) n
      ((decomposition ι K n c) i) := by
  exact LinearMap.equivOfSurjective_apply _ _

noncomputable def componentMap (i : ι) :
    relativeSingularChains (Σ j, K j) {z | z.2 ∈ A z.1} ⟶
      relativeSingularChains (K i) (A i) where
  f n := ModuleCat.ofHom (componentChain ι K A n i)
  comm' n m hnm := by
    have hnm' : n = m + 1 := hnm.symm
    subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c,rfl⟩ := canonicalRelativeProjection_surjective
      (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} (m+1) x
    symm
    change componentChain ι K A m i
      ((relativeSingularChains (Σ j, K j) {z | z.2 ∈ A z.1}).d (m+1) m
        (canonicalRelativeProjection (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} (m+1) c)) =
      (relativeSingularChains (K i) (A i)).d (m+1) m
        (componentChain ι K A (m+1) i
          (canonicalRelativeProjection (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} (m+1) c))
    rw [canonicalRelativeProjection_boundary (TopCat.of (Σ j, K j))
      {z | z.2 ∈ A z.1} m c, componentChain_projection,
      componentChain_projection, canonicalRelativeProjection_boundary
        (TopCat.of (K i)) (A i) m]
    exact congrArg (canonicalRelativeProjection (TopCat.of (K i)) (A i) m)
      (congrFun ((frozen% actual_singular_sigma_chains_boundary)
        ι K m c) i)


theorem decomposition_push_same (n : ℕ) (i : ι)
    (c : (TopCat.toSSet.obj (TopCat.of (K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    (decomposition ι K n
      (singularFinsuppPush (TopCat.ofHom (ContinuousMap.sigmaMk (X := K) i)) n c)) i = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | single x a =>
    have ha : Finsupp.single x a = a • Finsupp.single x 1 := by simp
    rw [ha]
    simp only [map_smul, Pi.smul_apply]
    congr 1
    have hx : singularFinsuppPush (TopCat.ofHom (ContinuousMap.sigmaMk (X := K) i)) n
        (Finsupp.single x 1) = Finsupp.single
          ((frozen% actual_singular_simplex_sigma_equiv) ι K n |>.symm ⟨i,x⟩) 1 := by
      simp only [singularFinsuppPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [hx]
    exact (frozen% actual_singular_sigma_chains_single_same) ι K n i x

theorem decomposition_push_other (n : ℕ) (i j : ι) (hji : j ≠ i)
    (c : (TopCat.toSSet.obj (TopCat.of (K i))).obj
      (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    (decomposition ι K n
      (singularFinsuppPush (TopCat.ofHom (ContinuousMap.sigmaMk (X := K) i)) n c)) j = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb, add_zero]
  | single x a =>
    have ha : Finsupp.single x a = a • Finsupp.single x 1 := by simp
    rw [ha]
    simp only [map_smul, Pi.smul_apply]
    have hx : singularFinsuppPush (TopCat.ofHom (ContinuousMap.sigmaMk (X := K) i)) n
        (Finsupp.single x 1) = Finsupp.single
          ((frozen% actual_singular_simplex_sigma_equiv) ι K n |>.symm ⟨i,x⟩) 1 := by
      simp only [singularFinsuppPush, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [hx, (frozen% actual_singular_sigma_chains_single_other) ι K n i j hji x]
    exact smul_zero _

noncomputable abbrev inclusionMap (i : ι) :=
  pairRelativeChainMap (A i) {z : Σ j, K j | z.2 ∈ A z.1}
    (ContinuousMap.sigmaMk (X := K) i) (fun _ hx => hx)

theorem inclusion_component_same (i : ι) :
    inclusionMap ι K A i ≫ componentMap ι K A i =
      𝟙 (relativeSingularChains (K i) (A i)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := canonicalRelativeProjection_surjective (TopCat.of (K i)) (A i) n x
  change componentChain ι K A n i ((inclusionMap ι K A i).f n
    (canonicalRelativeProjection (TopCat.of (K i)) (A i) n c)) =
      canonicalRelativeProjection (TopCat.of (K i)) (A i) n c
  rw [(frozen% actual_canonical_relative_projection_pair_natural),
    componentChain_projection, decomposition_push_same]

theorem inclusion_component_other (i j : ι) (hji : j ≠ i) :
    inclusionMap ι K A i ≫ componentMap ι K A j = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := canonicalRelativeProjection_surjective (TopCat.of (K i)) (A i) n x
  change componentChain ι K A n j ((inclusionMap ι K A i).f n
    (canonicalRelativeProjection (TopCat.of (K i)) (A i) n c)) = 0
  rw [(frozen% actual_canonical_relative_projection_pair_natural),
    componentChain_projection, decomposition_push_other ι K n i j hji, map_zero]

theorem component_inclusion_sum :
    (∑ i : ι, componentMap ι K A i ≫ inclusionMap ι K A i) =
      𝟙 (relativeSingularChains (Σ j, K j) {z | z.2 ∈ A z.1}) := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  rw [show (∑ i : ι, componentMap ι K A i ≫ inclusionMap ι K A i).f n =
    ∑ i : ι, (componentMap ι K A i ≫ inclusionMap ι K A i).f n from
      map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply]
  obtain ⟨c,rfl⟩ := canonicalRelativeProjection_surjective
    (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} n x
  change (∑ i : ι, (inclusionMap ι K A i).f n
    (componentChain ι K A n i
      (canonicalRelativeProjection (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} n c))) =
      canonicalRelativeProjection (TopCat.of (Σ j, K j)) {z | z.2 ∈ A z.1} n c
  calc
    _ = ∑ i : ι, canonicalRelativeProjection (TopCat.of (Σ j, K j))
        {z | z.2 ∈ A z.1} n
        (singularFinsuppPush (TopCat.ofHom (ContinuousMap.sigmaMk (X := K) i)) n
          ((decomposition ι K n c) i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [componentChain_projection ι K A n i c]
      exact (frozen% actual_canonical_relative_projection_pair_natural)
        (A i) {z : Σ j, K j | z.2 ∈ A z.1}
        (ContinuousMap.sigmaMk (X := K) i) (fun _ hx => hx) n _
    _ = _ := by
      rw [← map_sum, ← (frozen% actual_singular_sigma_chain_decompose) ι K n c]


noncomputable abbrev componentHomology (n : ℕ) (i : ι) :=
  HomologicalComplex.homologyMap (componentMap ι K A i) n

noncomputable abbrev inclusionHomology (n : ℕ) (i : ι) :=
  pairRelativeHomologyMap (A i) {z : Σ j, K j | z.2 ∈ A z.1}
    (ContinuousMap.sigmaMk (X := K) i) (fun _ hx => hx) n

theorem inclusion_component_same_homology (n : ℕ) (i : ι) :
    inclusionHomology ι K A n i ≫ componentHomology ι K A n i =
      𝟙 (relativeHomology (K i) (A i) n) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (inclusion_component_same ι K A i)
  simpa only [inclusionMap, inclusionHomology, componentHomology, pairRelativeHomologyMap,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] using h

theorem inclusion_component_other_homology (n : ℕ) (i j : ι) (hji : j ≠ i) :
    inclusionHomology ι K A n i ≫ componentHomology ι K A n j = 0 := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (inclusion_component_other ι K A i j hji)
  simpa only [inclusionMap, inclusionHomology, componentHomology, pairRelativeHomologyMap,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero] using h

theorem component_inclusion_sum_homology (n : ℕ) :
    (∑ i : ι, componentHomology ι K A n i ≫ inclusionHomology ι K A n i) =
      𝟙 (relativeHomology (Σ j, K j) {z | z.2 ∈ A z.1} n) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (component_inclusion_sum ι K A)
  have hs : HomologicalComplex.homologyMap
      (∑ i : ι, componentMap ι K A i ≫ inclusionMap ι K A i) n =
      ∑ i : ι, HomologicalComplex.homologyMap
        (componentMap ι K A i ≫ inclusionMap ι K A i) n :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map_sum _ _
  rw [hs] at h
  simpa only [inclusionMap, inclusionHomology, componentHomology, pairRelativeHomologyMap,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] using h

theorem component_inclusion_sum_homology_apply (n : ℕ)
    (r : relativeHomology (Σ j, K j) {z | z.2 ∈ A z.1} n) :
    (∑ i : ι, inclusionHomology ι K A n i (componentHomology ι K A n i r)) = r := by
  have h := congrArg (fun f => f.hom r) (component_inclusion_sum_homology ι K A n)
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

theorem inclusion_component_sum_homology_apply (n : ℕ)
    (h : ∀ i, relativeHomology (K i) (A i) n) (j : ι) :
    componentHomology ι K A n j
      (∑ i : ι, inclusionHomology ι K A n i (h i)) = h j := by
  classical
  rw [map_sum]
  rw [Finset.sum_eq_single j]
  · have hj := congrArg (fun f => f.hom (h j))
      (inclusion_component_same_homology ι K A n j)
    exact hj
  · intro i hi hij
    have hij' := congrArg (fun f => f.hom (h i))
      (inclusion_component_other_homology ι K A n i j (Ne.symm hij))
    exact hij'
  · simp

end
end FiniteSigmaRelativeChains
