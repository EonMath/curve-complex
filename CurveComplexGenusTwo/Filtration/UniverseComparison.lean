import CurveComplexGenusTwo.Filtration.UniverseComparisonReduction
open CategoryTheory Topology Convexity
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
variable {V : Type u} [LinearOrder V]

theorem affine_barycentricFlag_starSmall (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (π : Equiv.Perm (Fin (n+1))) :
    ∃ v : ActiveVertex K, singularSimplexImage K n
      (barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ)) ⊆
        CurveComplex.openVertexStar (geometricComplex K) v := by
  have hcard : σ.1.card = n+1 := by rcases σ.2.2 with h | h <;> omega
  have hnonempty : σ.1.Nonempty := Finset.card_pos.mp (by omega)
  let τ := activeFace K σ.1 σ.2.1
  have hτcard : τ.card = n+1 := (activeFace_card K σ.1 σ.2.1).trans hcard
  refine ⟨τ.orderEmbOfFin hτcard (π 0), ?_⟩
  rintro x ⟨t, rfl⟩
  change 0 < (CurveComplex.affineSingular τ
    (activeFace_mem_geometricComplex K σ.1 σ.2.1 hnonempty) hτcard
      (barycentricFlag n π t)).weight (τ.orderEmbOfFin hτcard (π 0))
  rw [CurveComplex.affineSingular_weight_ordered]
  exact barycentricFlag_first_weight_pos n π t

theorem rawSingularSubdivision_affine_starSmall (K : FiniteComplex V) (n : ℕ)
    (c : chains K (n:ℤ)) :
    rawSingularSubdivision K n (simplicialToSingularGenerators K n c) ∈
      (starSmallChainInclusion K n).range := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]; exact AddSubgroup.zero_mem _
  | neg c hc => simpa only [map_neg] using AddSubgroup.neg_mem _ hc
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | of σ =>
    simp only [simplicialToSingularGenerators_of, rawSingularSubdivision, AddMonoidHom.comp_apply,
      FreeAbelianGroup.toFinsupp_of, LinearMap.toAddMonoidHom_coe, singularBarycentricFinsupp_single,
      map_sum, map_zsmul, Finsupp.toFreeAbelianGroup_single, one_smul]
    apply AddSubgroup.sum_mem
    intro π hπ
    apply AddSubgroup.zsmul_mem
    exact ⟨FreeAbelianGroup.of ⟨_, affine_barycentricFlag_starSmall K n σ π⟩, rfl⟩

end CurveGenusTwo.Filtration.UniverseSubdivision

namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
open CurveComplexGenusTwo.CWHurewicz
variable {V : Type u} [LinearOrder V]

noncomputable def affineSmallSubdivision (K : FiniteComplex V) (n : ℕ) :
    chains K (n:ℤ) →+ FreeAbelianGroup (StarSmallSimplex K n) :=
  FreeAbelianGroup.lift fun σ => ∑ π : Equiv.Perm (Fin (n+1)),
    (π.sign : ℤ) • FreeAbelianGroup.of
      ⟨barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ),
        affine_barycentricFlag_starSmall K n σ π⟩

theorem affineSmallSubdivision_inclusion (K : FiniteComplex V) (n : ℕ)
    (c : chains K (n:ℤ)) :
    starSmallChainInclusion K n (affineSmallSubdivision K n c) =
      rawSingularSubdivision K n (simplicialToSingularGenerators K n c) := by
  have he : (starSmallChainInclusion K n).comp (affineSmallSubdivision K n) =
      (rawSingularSubdivision K n).comp (simplicialToSingularGenerators K n) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp only [AddMonoidHom.comp_apply, affineSmallSubdivision, FreeAbelianGroup.lift_apply_of,
      simplicialToSingularGenerators_of, rawSingularSubdivision,
      FreeAbelianGroup.toFinsupp_of, LinearMap.toAddMonoidHom_coe, singularBarycentricFinsupp_single,
      map_sum, map_zsmul, Finsupp.toFreeAbelianGroup_single, one_smul,
      starSmallChainInclusion, FreeAbelianGroup.map_of_apply]
  exact DFunLike.congr_fun he c

theorem affineSmallSubdivision_boundary (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n+1:ℕ):ℤ)) :
    starSmallBoundary K n (affineSmallSubdivision K (n+1) c) =
      affineSmallSubdivision K n (positiveBoundary K n c) := by
  apply starSmallChainInclusion_injective K n
  rw [starSmallChainInclusion_boundary, affineSmallSubdivision_inclusion,
    rawSingularSubdivision_boundary, ← simplicialToSingular_boundary, affineSmallSubdivision_inclusion]

noncomputable def simplicialCarrierComposite (K : FiniteComplex V) (n : ℕ) :
    chains K (n:ℤ) →+ chains K (n:ℤ) :=
  (normalizedStarSmallApproximation K n).comp (affineSmallSubdivision K n)

theorem simplicialCarrierComposite_boundary (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n+1:ℕ):ℤ)) :
    positiveBoundary K n (simplicialCarrierComposite K (n+1) c) =
      simplicialCarrierComposite K n (positiveBoundary K n c) := by
  simp only [simplicialCarrierComposite, AddMonoidHom.comp_apply]
  rw [normalizedStarSmallApproximation_boundary, affineSmallSubdivision_boundary]

end CurveGenusTwo.Filtration.UniverseSubdivision

namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
variable {V : Type u} [LinearOrder V]

/-- The full subcomplex consisting of the faces of one finite simplex. -/
def fullFaceComplex (σ : Finset V) : FiniteComplex V where
  simplices := {τ | τ ⊆ σ}
  down_closed := by intro τ υ hsub hτ; exact hsub.trans hτ

theorem fullFaceComplex_subcomplex (K : FiniteComplex V) (σ : Finset V) (hσ : σ ∈ K) :
    (fullFaceComplex σ).simplices ⊆ K.simplices :=
  fun _ hτ => K.down_closed hτ hσ

theorem fullFaceComplex_isNonemptyCone (σ : Finset V) (hne : σ.Nonempty) :
    IsNonemptyCone (fullFaceComplex σ) := by
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, Finset.singleton_subset_iff.mpr hv, ?_⟩
  intro τ hτ
  exact Finset.insert_subset hv hτ

theorem chainInclusion_range_mono_of_subcomplex (L M K : FiniteComplex V)
    (hLM : L.simplices ⊆ M.simplices) (hLK : L.simplices ⊆ K.simplices)
    (hMK : M.simplices ⊆ K.simplices) (q : ℤ) :
    (chainInclusion L K hLK q).range ≤ (chainInclusion M K hMK q).range := by
  have he : (chainInclusion M K hMK q).comp (chainInclusion L M hLM q) =
      chainInclusion L K hLK q := by
    apply FreeAbelianGroup.lift_ext
    intro s
    rfl
  rintro c ⟨a, rfl⟩
  exact ⟨chainInclusion L M hLM q a, DFunLike.congr_fun he a⟩

end CurveGenusTwo.Filtration.UniverseSubdivision
namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
open CurveComplexGenusTwo.CWHurewicz
variable {V : Type u} [LinearOrder V]

theorem affine_flag_carrier_in_fullFace (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (π : Equiv.Perm (Fin (n+1))) :
    (realizationCarrier K (singularSimplexImage K n
      (barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ)))).simplices ⊆
      (fullFaceComplex σ.1).simplices := by
  rintro τ ⟨x, hx, hpos⟩
  obtain ⟨t, rfl⟩ := hx
  intro v hv
  obtain ⟨ha, hp⟩ := hpos v hv
  apply simplexAtSingular_support_subset K n σ (barycentricFlag n π t)
  apply Finset.mem_image.mpr
  refine ⟨⟨v, ha⟩, ?_, rfl⟩
  apply (CurveComplex.mem_supportFinset_iff_pos _ _ _).mpr
  exact hp

theorem affineSmallSubdivision_of (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) : affineSmallSubdivision K n (FreeAbelianGroup.of σ) =
      ∑ π : Equiv.Perm (Fin (n+1)), (π.sign : ℤ) • FreeAbelianGroup.of
        (⟨barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ),
          affine_barycentricFlag_starSmall K n σ π⟩ : StarSmallSimplex K n) := by
  unfold affineSmallSubdivision
  rw [FreeAbelianGroup.lift_apply_of]

set_option maxHeartbeats 200000 in
theorem simplicialCarrierComposite_carried (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) :
    simplicialCarrierComposite K n (FreeAbelianGroup.of σ) ∈
      (chainInclusion (fullFaceComplex σ.1) K (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)).range := by
  change affineSmallSubdivision K n (FreeAbelianGroup.of σ) ∈
    ((chainInclusion (fullFaceComplex σ.1) K (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)).range).comap
      (normalizedStarSmallApproximation K n)
  rw [affineSmallSubdivision_of]
  apply AddSubgroup.sum_mem
  intro π hπ
  apply AddSubgroup.zsmul_mem
  exact chainInclusion_range_mono_of_subcomplex _ _ K
    (affine_flag_carrier_in_fullFace K n σ π)
    (realizationCarrier_subcomplex K _) (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)
    (normalizedStarSmallApproximation_carried K n
      ⟨_, affine_barycentricFlag_starSmall K n σ π⟩)

end CurveGenusTwo.Filtration.UniverseSubdivision

namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
variable {V : Type u} [LinearOrder V]

private theorem inverse_cast_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range := by cases h; rfl

theorem boundaries_nat_eq_positiveBoundary_range (K : FiniteComplex V) (n : ℕ) :
    boundaries K (n:ℤ) = (positiveBoundary K n).range := by
  have h : ((n:ℤ)+1-1) = (n:ℤ) := by omega
  have h' : (((n+1:ℕ):ℤ)-1) = (n:ℤ) := by omega
  change Eq.mp (congrArg (fun k : ℤ => AddSubgroup (chains K k)) h)
      (boundary K ((n:ℤ)+1)).range =
    (Eq.mp (congrArg (fun k : ℤ => chains K ((n+1:ℕ):ℤ) →+ chains K k) h')
      (boundary K ((n+1:ℕ):ℤ))).range
  exact inverse_cast_range h (boundary K ((n:ℤ)+1))

theorem fullFace_carried_top_cycle_zero (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (c : chains K (n:ℤ))
    (hc : boundary K (n:ℤ) c = 0)
    (hcar : c ∈ (chainInclusion (fullFaceComplex σ.1) K
      (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)).range) : c = 0 := by
  let L := fullFaceComplex σ.1
  let hLK := fullFaceComplex_subcomplex K σ.1 σ.2.1
  have hcard : σ.1.card = n+1 := by rcases σ.2.2 with h | h <;> omega
  have hne : σ.1.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hcar
  have hacycle : a ∈ cycles L (n:ℤ) := by
    change boundary L (n:ℤ) a = 0
    apply carrierChainInclusion_injective L K hLK ((n:ℤ)-1)
    have hcomm := DFunLike.congr_fun (chainInclusion_boundary L K hLK (n:ℤ)) a
    change boundary K (n:ℤ) (chainInclusion L K hLK (n:ℤ) a) =
      chainInclusion L K hLK ((n:ℤ)-1) (boundary L (n:ℤ) a) at hcomm
    rw [ha, hc] at hcomm
    simpa only [map_zero] using hcomm.symm
  letI := nonemptyCone_reducedHomology L (fullFaceComplex_isNonemptyCone σ.1 hne) (n:ℤ) (by omega)
  have hzero : (QuotientAddGroup.mk (⟨a, hacycle⟩ : cycles L (n:ℤ)) : reducedHomology L (n:ℤ)) = 0 :=
    Subsingleton.elim _ _
  have hb := (QuotientAddGroup.eq_zero_iff (⟨a, hacycle⟩ : cycles L (n:ℤ))).mp hzero
  change a ∈ boundaries L (n:ℤ) at hb
  rw [boundaries_nat_eq_positiveBoundary_range] at hb
  obtain ⟨b, hb⟩ := hb
  letI : IsEmpty (SimplexAt L ((n+1:ℕ):ℤ)) := ⟨by
    intro τ
    have hle : τ.1.card ≤ σ.1.card := Finset.card_le_card τ.2.1
    rcases τ.2.2 with h | h <;> omega⟩
  have hbzero : b = 0 := Subsingleton.elim _ _
  rw [hbzero, map_zero] at hb
  rw [← ha, ← hb, map_zero]

theorem boundary_zero_augmentation (K : FiniteComplex V) (v : ActiveVertex K)
    (c : chains K 0) :
    boundary K 0 c = RawCone.aug c • FreeAbelianGroup.of
      (⟨∅, K.down_closed (Finset.empty_subset _) v.2, Or.inl ⟨rfl, rfl⟩⟩ : SimplexAt K (-1)) := by
  classical
  have he : (∅ : Finset V) ∈ K := K.down_closed (Finset.empty_subset _) v.2
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | of σ =>
    have hc : σ.1.card = 1 := by rcases σ.2.2 with h | h <;> omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
    simp [boundary, faceBoundary, hw, he, RawCone.aug, Finset.filter_singleton]
  | neg c hc => simp only [map_neg, hc, neg_smul]
  | add c d hc hd => simp only [map_add, hc, hd, add_smul]

theorem normalizedStarSmallApproximation_zero_aug (K : FiniteComplex V)
    (c : FreeAbelianGroup (StarSmallSimplex K 0)) :
    RawCone.aug (normalizedStarSmallApproximation K 0 c) =
      RawCone.aug (starSmallChainInclusion K 0 c) := by
  have he : RawCone.aug.comp (normalizedStarSmallApproximation K 0) =
      RawCone.aug.comp (starSmallChainInclusion K 0) := by
    apply FreeAbelianGroup.lift_ext
    intro s
    obtain ⟨v, hv⟩ := normalizedStarSmallApproximation_zero K s
    simp only [AddMonoidHom.comp_apply, hv, RawCone.aug, FreeAbelianGroup.lift_apply_of,
      starSmallChainInclusion, FreeAbelianGroup.map_of_apply]
  exact DFunLike.congr_fun he c

end CurveGenusTwo.Filtration.UniverseSubdivision
namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
open CurveComplexGenusTwo.CWHurewicz
variable {V : Type u} [LinearOrder V]

theorem rawSingularSubdivision_degree_zero (K : FiniteComplex V)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋0⦌)) :
    rawSingularSubdivision K 0 c = c := by
  simp only [rawSingularSubdivision, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    singularBarycentricFinsupp_degree_zero, Finsupp.toFreeAbelianGroup_toFinsupp]

theorem simplicialCarrierComposite_zero_aug (K : FiniteComplex V) (c : chains K 0) :
    RawCone.aug (simplicialCarrierComposite K 0 c) = RawCone.aug c := by
  change RawCone.aug (normalizedStarSmallApproximation K 0 (affineSmallSubdivision K 0 c)) = _
  rw [normalizedStarSmallApproximation_zero_aug, affineSmallSubdivision_inclusion,
    rawSingularSubdivision_degree_zero]
  have he : RawCone.aug.comp (simplicialToSingularGenerators K 0) = RawCone.aug := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp only [AddMonoidHom.comp_apply, simplicialToSingularGenerators_of, RawCone.aug, FreeAbelianGroup.lift_apply_of]
  exact DFunLike.congr_fun he c

/-- The normalized carried approximation of one barycentric subdivision of
an affine simplicial chain is exactly that original chain. -/
theorem simplicialCarrierComposite_eq_id (K : FiniteComplex V) (n : ℕ)
    (c : chains K (n:ℤ)) : simplicialCarrierComposite K n c = c := by
  suffices he : simplicialCarrierComposite K n = AddMonoidHom.id _ by rw [he]; rfl
  induction n with
  | zero =>
    apply FreeAbelianGroup.lift_ext
    intro σ
    apply sub_eq_zero.mp
    apply fullFace_carried_top_cycle_zero K 0 σ
    · have hc : σ.1.card = 1 := by rcases σ.2.2 with h | h <;> omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
      have hav : ({v} : Finset V) ∈ K := hv ▸ σ.2.1
      change boundary K 0 (simplicialCarrierComposite K 0 (FreeAbelianGroup.of σ) - FreeAbelianGroup.of σ) = 0
      have haug : RawCone.aug (simplicialCarrierComposite K 0 (FreeAbelianGroup.of σ) - FreeAbelianGroup.of σ) = 0 := by
        exact (map_sub RawCone.aug _ _).trans
          (sub_eq_zero.mpr (simplicialCarrierComposite_zero_aug K (FreeAbelianGroup.of σ)))
      exact (boundary_zero_augmentation K ⟨v, hav⟩ _).trans
        ((congrArg (fun t : ℤ => t • (FreeAbelianGroup.of ⟨∅, K.down_closed (Finset.empty_subset _) hav, Or.inl ⟨rfl, rfl⟩⟩ : chains K (-1))) haug).trans (zero_smul _ _))
    · apply AddSubgroup.sub_mem
      · exact simplicialCarrierComposite_carried K 0 σ
      · exact ⟨FreeAbelianGroup.of ⟨σ.1, Finset.Subset.refl _, σ.2.2⟩, rfl⟩
  | succ n ih =>
    apply FreeAbelianGroup.lift_ext
    intro σ
    apply sub_eq_zero.mp
    apply fullFace_carried_top_cycle_zero K (n+1) σ
    · apply (positiveBoundary_eq_zero_iff K n _).mp
      rw [map_sub, simplicialCarrierComposite_boundary, ih 0]
      simp
    · apply AddSubgroup.sub_mem
      · exact simplicialCarrierComposite_carried K (n+1) σ
      · exact ⟨FreeAbelianGroup.of ⟨σ.1, Finset.Subset.refl _, σ.2.2⟩, rfl⟩

#print axioms simplicialCarrierComposite_eq_id
end CurveGenusTwo.Filtration.UniverseSubdivision

namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
variable {V : Type u} [LinearOrder V]

/-- Producer B in universe zero, using the actual normalized reverse map. -/
theorem positiveCyclesMap_reflects_boundaries :
    ∀ (K : FiniteComplex V) (n : ℕ) (c : cycles K ((n+1:ℕ):ℤ)),
      (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n →
        c.1 ∈ boundaries K ((n+1:ℕ):ℤ) := by
  intro K n c hc
  let a := affineSmallSubdivision K (n+1) c.1
  have hacycle : starSmallBoundary K n a = 0 := by
    rw [affineSmallSubdivision_boundary,
      (positiveBoundary_eq_zero_iff K n c.1).mpr c.2, map_zero]
  have haraw : starSmallChainInclusion K (n+1) a ∈ singularPositiveBoundaries K n := by
    obtain ⟨b, hb⟩ := hc
    refine ⟨rawSingularSubdivision K (n+2) b, ?_⟩
    rw [rawSingularSubdivision_boundary, hb]
    exact (affineSmallSubdivision_inclusion K (n+1) c.1).symm
  obtain ⟨b, hb⟩ := starSmallCycle_bounds_of_raw_bounds K n a hacycle haraw
  rw [boundaries_nat_eq_positiveBoundary_range]
  refine ⟨normalizedStarSmallApproximation K (n+2) b, ?_⟩
  rw [normalizedStarSmallApproximation_boundary, hb]
  exact simplicialCarrierComposite_eq_id K (n+1) c.1

#print axioms positiveCyclesMap_reflects_boundaries
end CurveGenusTwo.Filtration.UniverseSubdivision
