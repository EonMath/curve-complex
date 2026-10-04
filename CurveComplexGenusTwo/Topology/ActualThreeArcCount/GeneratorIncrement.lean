import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.RingTheory.PrincipalIdealDomain
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHZero

open Set CategoryTheory Topology CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

/-- An integral exact step with a rank-one connecting coordinate contributes at
most one generator, without requiring the old module to be finitely generated. -/
theorem one_generator_modulo_exact_image
    {R : Type} [CommRing R] [IsPrincipalIdealRing R]
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (d : N →ₗ[R] R)
    (hexact : LinearMap.ker d ≤ LinearMap.range f) :
    ∃ z : N, ∀ y : N, ∃ m : M, ∃ k : R, y = f m + k • z := by
  let J : Ideal R := LinearMap.range d
  obtain ⟨z, hz⟩ := Submodule.IsPrincipal.generator_mem J
  refine ⟨z, fun y => ?_⟩
  obtain ⟨k, hk⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator J).mp
    (show d y ∈ J from ⟨y, rfl⟩)
  have hzero : d (y - k • z) = 0 := by
    rw [map_sub, map_smul, hz]
    exact sub_eq_zero.mpr hk
  obtain ⟨m, hm⟩ := hexact (LinearMap.mem_ker.mpr hzero)
  exact ⟨m, k, by rw [hm]; exact (sub_add_cancel y (k • z)).symm⟩

/-- The same step bounds the generators of the image in a fixed ambient module.
This is the form used while restoring successive proper-arc strips. -/
theorem ambient_image_generators_successor
    {R : Type} [CommRing R] [IsPrincipalIdealRing R]
    {M N A : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup A] [Module R A]
    (f : M →ₗ[R] N) (d : N →ₗ[R] R) (a : N →ₗ[R] A)
    (hexact : LinearMap.ker d ≤ LinearMap.range f)
    (n : ℕ) (v : Fin n → A)
    (hgen : ∀ m, a (f m) ∈ Submodule.span R (Set.range v)) :
    ∃ w : Fin (n + 1) → A, ∀ y, a y ∈ Submodule.span R (Set.range w) := by
  obtain ⟨z, hz⟩ := one_generator_modulo_exact_image f d hexact
  let w : Fin (n + 1) → A := Fin.cons (a z) v
  refine ⟨w, fun y => ?_⟩
  obtain ⟨m, k, rfl⟩ := hz y
  rw [map_add, map_smul]
  apply Submodule.add_mem
  · exact (Submodule.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨i.succ, by simp [w]⟩)) (hgen m)
  · apply (Submodule.span R (Set.range w)).smul_mem k
    exact Submodule.subset_span ⟨0, by simp [w]⟩

/-- Adding an open contractible strip whose overlap has two contractible
components adds at most one generator modulo the previous inclusion image. -/
theorem mv_one_generator_modulo_old_image
    (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hVzero : ∀ z : H V 1, z = 0)
    (e : ContinuousMap.HomotopyEquiv ↥(U ∩ V) CircleHomologyComputation.Two) :
    ∃ z : H X 1, ∀ y : H X 1, ∃ m : H U 1, ∃ k : ℤ,
      y = homologyInclusion X U 1 m + k • z := by
  let δ := actualMVConnecting X U V hU hV hcover 0
  let c := homotopyHomologyIso e 0 ≪≫ CircleHomologyComputation.twoHomologyIso
  let d : H X 1 →ₗ[ℤ] ℤ :=
    (LinearMap.fst ℤ ℤ ℤ).comp (c.toLinearEquiv.toLinearMap.comp δ.hom)
  have hc : c.hom ≫ CircleHomologyComputation.coordinateSum =
      (TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
    dsimp only [c, Iso.trans_hom]
    rw [Category.assoc, CircleHomologyComputation.twoHomologyIso_sum]
    exact CircleHomologyComputation.augmentation_naturality (TopCat.ofHom e.toFun)
  have hexact : LinearMap.ker d ≤ LinearMap.range (homologyInclusion X U 1).hom := by
    intro y hy
    have hd : (c.hom (δ y)).1 = 0 := LinearMap.mem_ker.mp hy
    have hδ : actualMVDifference X U V 0 (δ y) = 0 :=
      congrArg (fun f => f y) (actualMVConnecting_difference X U V hU hV hcover 0)
    have hleft : actualSubsetHomologyMap X (U ∩ V) U Set.inter_subset_left 0 (δ y) = 0 := by
      rw [actualMVDifference_apply] at hδ
      exact congrArg Prod.fst hδ
    have haug : (TopCat.of ↥(U ∩ V)).singularHomology₀ε (ModuleCat.of ℤ ℤ) (δ y) = 0 := by
      have hn := CircleHomologyComputation.augmentation_naturality
        (singularSubsetInclusion X (U ∩ V) U Set.inter_subset_left)
      have h := congrArg (fun f => f (δ y)) hn
      change (TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ)
        (actualSubsetHomologyMap X (U ∩ V) U Set.inter_subset_left 0 (δ y)) = _ at h
      rw [hleft, map_zero] at h
      exact h.symm
    have hsum : (c.hom (δ y)).1 + (c.hom (δ y)).2 = 0 := by
      have h := congrArg (fun f => f (δ y)) hc
      exact h.trans haug
    have hz : δ y = 0 := by
      apply c.toLinearEquiv.injective
      rw [map_zero]
      apply Prod.ext
      · exact hd
      · change (c.hom (δ y)).2 = 0
        simpa only [hd, zero_add] using hsum
    obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (actualMV_exact_ambient X U V hU hV hcover 0) y hz
    refine ⟨q.1, ?_⟩
    rw [actualMVSum_apply, hVzero q.2, map_zero, add_zero] at hq
    exact hq
  obtain ⟨z, hz⟩ := one_generator_modulo_exact_image (homologyInclusion X U 1).hom d hexact
  refine ⟨z, fun y => ?_⟩
  obtain ⟨m, k, hk⟩ := hz y
  refine ⟨m, k, hk.trans ?_⟩
  congr 1
  exact int_smul_eq_zsmul (inferInstance : Module ℤ (H X 1)) k z

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
