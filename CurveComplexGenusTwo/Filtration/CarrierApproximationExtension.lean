import CurveComplexGenusTwo.Filtration.CarriedFilling
import CurveComplexGenusTwo.Filtration.StarSmallChainBridge

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

theorem carrierChainInclusion_range_mono (K : FiniteComplex V)
    {S T : Set (geometricRealization K)} (hST : S ⊆ T) (q : ℤ) :
    (chainInclusion (realizationCarrier K S) K (realizationCarrier_subcomplex K S) q).range ≤
      (chainInclusion (realizationCarrier K T) K (realizationCarrier_subcomplex K T) q).range := by
  have h : (chainInclusion (realizationCarrier K T) K (realizationCarrier_subcomplex K T) q).comp
      (chainInclusion (realizationCarrier K S) (realizationCarrier K T)
        (realizationCarrier_mono K hST) q) =
      chainInclusion (realizationCarrier K S) K (realizationCarrier_subcomplex K S) q := by
    apply FreeAbelianGroup.lift_ext
    intro s
    rfl
  rintro c ⟨a, rfl⟩
  refine ⟨chainInclusion (realizationCarrier K S) (realizationCarrier K T)
    (realizationCarrier_mono K hST) q a, ?_⟩
  exact DFunLike.congr_fun h a

/-- Extend a carried map once its prescribed generator boundaries are cycles. -/
theorem exists_starSmall_carried_extension_of_cycles (K : FiniteComplex V) (n : ℕ)
    (q : ℤ) (hq : 0 ≤ q)
    (f : FreeAbelianGroup (StarSmallSimplex K n) →+ chains K (q-1))
    (hcycle : ∀ c : FreeAbelianGroup (StarSmallSimplex K (n+1)),
      boundary K (q-1) (f (starSmallBoundary K n c)) = 0)
    (hcarried : ∀ s : StarSmallSimplex K n, f (FreeAbelianGroup.of s) ∈
      (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
        (realizationCarrier_subcomplex K _) (q-1)).range) :
    ∃ F : FreeAbelianGroup (StarSmallSimplex K (n+1)) →+ chains K q,
      (∀ c, boundary K q (F c) = f (starSmallBoundary K n c)) ∧
      (∀ s : StarSmallSimplex K (n+1), F (FreeAbelianGroup.of s) ∈
        (chainInclusion (realizationCarrier K (singularSimplexImage K (n+1) s.1)) K
          (realizationCarrier_subcomplex K _) q).range) := by
  classical
  have fill (s : StarSmallSimplex K (n+1)) :
      ∃ d : chains (realizationCarrier K (singularSimplexImage K (n+1) s.1)) q,
        boundary K q (chainInclusion _ K (realizationCarrier_subcomplex K _) q d) =
          f (starSmallBoundary K n (FreeAbelianGroup.of s)) := by
    obtain ⟨v, hv⟩ := s.2
    apply exists_realizationCarrier_filling K _ _ v hv q hq
    · exact hcycle _
    · rw [starSmallBoundary_of, map_sum]
      apply AddSubgroup.sum_mem
      intro i hi
      rw [map_zsmul]
      apply AddSubgroup.zsmul_mem
      apply carrierChainInclusion_range_mono K (singularSimplexImage_face_subset K n s.1 i)
      exact hcarried (starSmallFace K n i s)
    · exact ⟨(TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K))
        (.op ⦋n+1⦌) s.1) (.single 0), ⟨.single 0, rfl⟩⟩
  choose d hd using fill
  let F : FreeAbelianGroup (StarSmallSimplex K (n+1)) →+ chains K q :=
    FreeAbelianGroup.lift fun s => chainInclusion _ K (realizationCarrier_subcomplex K _) q (d s)
  refine ⟨F, ?_, ?_⟩
  · have h : (boundary K q).comp F = f.comp (starSmallBoundary K n) := by
      apply FreeAbelianGroup.lift_ext
      intro s
      simp only [AddMonoidHom.comp_apply, F, FreeAbelianGroup.lift_apply_of]
      exact hd s
    exact fun c => DFunLike.congr_fun h c
  · intro s
    exact ⟨d s, by simp only [F, FreeAbelianGroup.lift_apply_of]⟩

/-- One induction step of the carrier-based simplicial approximation.
The boundary-square equation, face-carrier monotonicity, and actual carrier
acyclicity supply the next chain map without any approximation assumption. -/
theorem exists_starSmall_carried_extension (K : FiniteComplex V) (n : ℕ)
    (q : ℤ) (hq : 0 ≤ q)
    (f : FreeAbelianGroup (StarSmallSimplex K (n+1)) →+ chains K (q-1))
    (g : FreeAbelianGroup (StarSmallSimplex K n) →+ chains K (q-1-1))
    (hcomm : ∀ c, boundary K (q-1) (f c) = g (starSmallBoundary K n c))
    (hcarried : ∀ s : StarSmallSimplex K (n+1), f (FreeAbelianGroup.of s) ∈
      (chainInclusion (realizationCarrier K (singularSimplexImage K (n+1) s.1)) K
        (realizationCarrier_subcomplex K _) (q-1)).range) :
    ∃ F : FreeAbelianGroup (StarSmallSimplex K (n+2)) →+ chains K q,
      (∀ c, boundary K q (F c) = f (starSmallBoundary K (n+1) c)) ∧
      (∀ s : StarSmallSimplex K (n+2), F (FreeAbelianGroup.of s) ∈
        (chainInclusion (realizationCarrier K (singularSimplexImage K (n+2) s.1)) K
          (realizationCarrier_subcomplex K _) q).range) := by
  classical
  have fill (s : StarSmallSimplex K (n+2)) :
      ∃ d : chains (realizationCarrier K (singularSimplexImage K (n+2) s.1)) q,
        boundary K q (chainInclusion _ K (realizationCarrier_subcomplex K _) q d) =
          f (starSmallBoundary K (n+1) (FreeAbelianGroup.of s)) := by
    obtain ⟨v, hv⟩ := s.2
    apply exists_realizationCarrier_filling K _ _ v hv q hq
    · rw [hcomm, starSmallBoundary_squared, map_zero]
    · rw [starSmallBoundary_of, map_sum]
      apply AddSubgroup.sum_mem
      intro i hi
      rw [map_zsmul]
      apply AddSubgroup.zsmul_mem
      apply carrierChainInclusion_range_mono K (singularSimplexImage_face_subset K (n+1) s.1 i)
      exact hcarried (starSmallFace K (n+1) i s)
    · exact ⟨(TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K))
        (.op ⦋n+2⦌) s.1) (.single 0), ⟨.single 0, rfl⟩⟩
  choose d hd using fill
  let F : FreeAbelianGroup (StarSmallSimplex K (n+2)) →+ chains K q :=
    FreeAbelianGroup.lift fun s => chainInclusion _ K (realizationCarrier_subcomplex K _) q (d s)
  refine ⟨F, ?_, ?_⟩
  · have h : (boundary K q).comp F = f.comp (starSmallBoundary K (n+1)) := by
      apply FreeAbelianGroup.lift_ext
      intro s
      simp only [AddMonoidHom.comp_apply, F, FreeAbelianGroup.lift_apply_of]
      exact hd s
    exact fun c => DFunLike.congr_fun h c
  · intro s
    exact ⟨d s, by simp only [F, FreeAbelianGroup.lift_apply_of]⟩

#print axioms exists_starSmall_carried_extension
end CurveGenusTwo.Filtration
