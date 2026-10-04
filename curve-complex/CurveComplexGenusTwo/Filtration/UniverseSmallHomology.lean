import CurveComplexGenusTwo.Filtration.UniverseSmallCycle
open CategoryTheory Topology Convexity
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
variable {V : Type u} [LinearOrder V]

noncomputable def rawSingularIterate (K : FiniteComplex V) (n k : ℕ) :=
  Finsupp.toFreeAbelianGroup.comp
    ((singularBarycentricIterate (TopCat.of (geometricRealization K)) n k).toAddMonoidHom.comp
      FreeAbelianGroup.toFinsupp)

noncomputable def rawSingularHomotopyIterate (K : FiniteComplex V) (n k : ℕ) :=
  Finsupp.toFreeAbelianGroup.comp
    ((singularCarrierHomotopyIterate (TopCat.of (geometricRealization K)) n k).toAddMonoidHom.comp
      FreeAbelianGroup.toFinsupp)

theorem rawSingularIterate_boundary (K : FiniteComplex V) (n k : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+1⦌)) :
    singularGeneratorBoundary K n (rawSingularIterate K (n+1) k z) =
      rawSingularIterate K n k (singularGeneratorBoundary K n z) := by
  apply (FreeAbelianGroup.equivFinsupp _).injective
  simp only [FreeAbelianGroup.equivFinsupp_apply, toFinsupp_singularGeneratorBoundary,
    rawSingularIterate, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
  exact singularBarycentricIterate_boundary _ n k _

theorem rawSingularHomotopyIterate_boundary (K : FiniteComplex V) (n k : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+1⦌)) :
    singularGeneratorBoundary K (n+1) (rawSingularHomotopyIterate K (n+1) k z) +
      rawSingularHomotopyIterate K n k (singularGeneratorBoundary K n z) =
      rawSingularIterate K (n+1) k z - z := by
  apply (FreeAbelianGroup.equivFinsupp _).injective
  simp only [FreeAbelianGroup.equivFinsupp_apply, map_add, map_sub,
    toFinsupp_singularGeneratorBoundary, rawSingularHomotopyIterate, rawSingularIterate,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
  exact singularCarrierHomotopyIterate_boundary_succ _ n k _

theorem rawSingularIterate_eventually_starSmall (K : FiniteComplex V) (n : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌)) :
    ∃ k, rawSingularIterate K n k z ∈ (starSmallChainInclusion K n).range := by
  obtain ⟨k, hk⟩ := singularBarycentricIterateList_eventually_starSmall
    (geometricComplex K) n (FreeAbelianGroup.toFinsupp z)
  have heq : ∀ j, singularBarycentricIterateList (TopCat.of (geometricRealization K)) n j
      (FreeAbelianGroup.toFinsupp z) = singularBarycentricIterate
        (TopCat.of (geometricRealization K)) n j (FreeAbelianGroup.toFinsupp z) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp only [singularBarycentricIterateList, singularBarycentricIterate_succ, ih]
  refine ⟨k, exists_starSmallChain_lift K n _ ?_⟩
  intro s hs
  simp only [rawSingularIterate, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, FreeAbelianGroup.toFinsupp_toFreeAbelianGroup] at hs
  rw [← heq k] at hs
  obtain ⟨v, hv⟩ := hk s hs
  exact ⟨v, by simpa only [singularSimplexImage, Set.image_univ] using hv⟩

theorem rawSingularHomotopyIterate_starSmall (K : FiniteComplex V) (n k : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K n)) :
    rawSingularHomotopyIterate K n k (starSmallChainInclusion K n c) ∈
      (starSmallChainInclusion K (n+1)).range := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]; exact AddSubgroup.zero_mem _
  | neg c hc => simpa only [map_neg] using AddSubgroup.neg_mem _ hc
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | of s =>
    obtain ⟨v, hv⟩ := s.2
    apply exists_starSmallChain_lift
    intro t ht
    simp only [starSmallChainInclusion, FreeAbelianGroup.map_of_apply,
      rawSingularHomotopyIterate, AddMonoidHom.comp_apply,
      FreeAbelianGroup.toFinsupp_of, LinearMap.toAddMonoidHom_coe,
      FreeAbelianGroup.toFinsupp_toFreeAbelianGroup] at ht
    have hsingle : SingularChainImageSupported (TopCat.of (geometricRealization K)) n
        (singularSimplexImage K n s.1) (Finsupp.single s.1 1) := by
      intro t ht
      have hts : t = s.1 := (Finsupp.mem_support_single t s.1 1).mp ht |>.1
      subst t
      exact Set.Subset.rfl
    have h := singularCarrierHomotopyIterate_supported
      (TopCat.of (geometricRealization K)) n k (singularSimplexImage K n s.1)
      (Finsupp.single s.1 1) hsingle
    exact ⟨v, (h t ht).trans hv⟩

theorem starSmallCycle_bounds_of_raw_bounds (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1)))
    (hc : starSmallBoundary K n c = 0)
    (hb : starSmallChainInclusion K (n+1) c ∈ singularPositiveBoundaries K n) :
    ∃ b : FreeAbelianGroup (StarSmallSimplex K (n+2)), starSmallBoundary K (n+1) b = c := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨k, b', hb'⟩ := rawSingularIterate_eventually_starSmall K (n+2) b
  obtain ⟨h, hh⟩ := rawSingularHomotopyIterate_starSmall K (n+1) k c
  refine ⟨b' - h, ?_⟩
  apply starSmallChainInclusion_injective K (n+1)
  rw [starSmallChainInclusion_boundary, map_sub, hb', hh, map_sub,
    rawSingularIterate_boundary, hb]
  have hz : singularGeneratorBoundary K n (starSmallChainInclusion K (n+1) c) = 0 := by
    rw [← starSmallChainInclusion_boundary, hc, map_zero]
  have he := rawSingularHomotopyIterate_boundary K n k
    (starSmallChainInclusion K (n+1) c)
  rw [hz, map_zero, add_zero] at he
  rw [he]
  abel

 theorem singularPositiveCycle_has_smallComplex_representative
    (K : FiniteComplex V) (n : ℕ) (z : singularPositiveCycles K n) :
    ∃ c : FreeAbelianGroup (StarSmallSimplex K (n+1)),
      starSmallBoundary K n c = 0 ∧
      starSmallChainInclusion K (n+1) c - z.1 ∈ singularPositiveBoundaries K n := by
  obtain ⟨z', hz', hsmall⟩ := singularPositiveCycle_has_starSmall_representative K n z
  obtain ⟨c, hc, he⟩ := exists_starSmallCycle_lift K n z' (by
    intro s hs
    obtain ⟨v, hv⟩ := hsmall s hs
    exact ⟨v, by simpa only [singularSimplexImage, Set.image_univ] using hv⟩)
  exact ⟨c, hc, by simpa only [he] using hz'⟩

#print axioms starSmallCycle_bounds_of_raw_bounds
#print axioms singularPositiveCycle_has_smallComplex_representative
end CurveGenusTwo.Filtration.UniverseSubdivision
