import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
theorem chain_expansion (S : SSet.{0}) (n : ℕ)
    (a : (S.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    ∃ c : S _⦋n⦌ →₀ ℤ,
      a = ∑ s ∈ c.support, c s • (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1 := by
  classical
  let e : (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ≅
      ModuleCat.of ℤ (S _⦋n⦌ →₀ ℤ) :=
    (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (S _⦋n⦌))
  have hb (s : S _⦋n⦌) : e.hom ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) =
      Finsupp.single s 1 := by
    have h := (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (S _⦋n⦌)) ⟨s⟩
    exact congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ _ => f.hom 1) h
  let c := e.hom a
  refine ⟨c, ?_⟩
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change c = e.hom.hom _
  rw [map_sum]
  simp only [map_zsmul, hb, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (Finsupp.sum_single c).symm
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
