import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualConjugatePeriodCanonical85
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open scoped Manifold ContDiff Bundle Simplicial TensorProduct
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

noncomputable def actualHodgePeriod {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (ActualCanonicalSection E × ActualCanonicalSection E) →ₗ[ℝ]
      Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1) where
  toFun p := actualSectionPeriodDual p.1 + actualConjugatePeriodDual p.2
  map_add' p q := by
    simp [Prod.fst_add, Prod.snd_add, add_add_add_comm]
  map_smul' r p := by
    apply LinearMap.ext
    intro x
    simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.add_apply,
      LinearMap.smul_apply]
    change (actualSectionPeriodDual ((r : ℂ) • p.1)) x +
      (actualConjugatePeriodDual ((r : ℂ) • p.2)) x = _
    rw [map_smul, LinearMap.map_smulₛₗ]
    simp [smul_add, Complex.conj_ofReal]

theorem actualHodgePeriod_apply {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) (c : ℂ)
    (x : CurveComplex.integralHomology E 1) :
    actualHodgePeriod (s, t) (c ⊗ₜ[ℤ] x) =
      c * (actualSectionPeriodOnProject s x +
        star (actualSectionPeriodOnProject t x)) := by
  rw [show actualHodgePeriod (s, t) =
    actualSectionPeriodDual s + actualConjugatePeriodDual t from rfl]
  rw [LinearMap.add_apply, actualSectionPeriodDual_tmul,
    actualConjugatePeriodDual_tmul, mul_add]

theorem actualCanonicalSection_finrank_two_of_hodge_bijective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E)
    (hHodge : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      Function.Bijective (actualHodgePeriod (E := E))) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Module.finrank ℂ (ActualCanonicalSection E) = 2 := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : Module.Finite ℂ
      (Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1)) :=
    Module.Finite.of_basis (genus_two_complex_h1_dual_basis E hg)
  letI : Module.Finite ℝ
      (Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1)) :=
    FiniteDimensional.trans ℝ ℂ _
  letI : Module.Finite ℝ
      (ActualCanonicalSection E × ActualCanonicalSection E) :=
    Module.Finite.of_injective actualHodgePeriod hHodge.1
  letI : Module.Finite ℝ (ActualCanonicalSection E) :=
    Module.Finite.of_injective
      (LinearMap.inl ℝ (ActualCanonicalSection E) (ActualCanonicalSection E))
      (by intro s t h; exact congrArg Prod.fst h)
  have hfin := (LinearEquiv.ofBijective actualHodgePeriod hHodge).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex,
    finrank_real_of_complex,
    genus_two_complex_h1_dual_finrank_four E hg] at hfin
  omega

theorem actualCanonicalSection_finrank_le_two_of_hodge_injective
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E)
    (hHodge : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      Function.Injective (actualHodgePeriod (E := E))) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Module.finrank ℂ (ActualCanonicalSection E) ≤ 2 := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : Module.Finite ℂ
      (Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1)) :=
    Module.Finite.of_basis (genus_two_complex_h1_dual_basis E hg)
  letI : Module.Finite ℝ
      (Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1)) :=
    FiniteDimensional.trans ℝ ℂ _
  letI : Module.Finite ℝ
      (ActualCanonicalSection E × ActualCanonicalSection E) :=
    Module.Finite.of_injective actualHodgePeriod hHodge
  letI : Module.Finite ℝ (ActualCanonicalSection E) :=
    Module.Finite.of_injective
      (LinearMap.inl ℝ (ActualCanonicalSection E) (ActualCanonicalSection E))
      (by intro s t h; exact congrArg Prod.fst h)
  have hfin := LinearMap.finrank_le_finrank_of_injective hHodge
  rw [Module.finrank_prod, finrank_real_of_complex,
    finrank_real_of_complex,
    genus_two_complex_h1_dual_finrank_four E hg] at hfin
  omega

theorem actualCanonicalSection_basis_of_hodge_injective_and_lower_bound
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2)
    (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A;
      IsManifold 𝓘(ℂ) ∞ E)
    (hHodge : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      Function.Injective (actualHodgePeriod (E := E)))
    (hLower : letI : ChartedSpace ℂ E := A
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      2 ≤ Module.finrank ℂ (ActualCanonicalSection E)) :
    letI : ChartedSpace ℂ E := A
    letI : IsManifold 𝓘(ℂ) ∞ E := hA
    Nonempty (Module.Basis (Fin 2) ℂ (ActualCanonicalSection E)) := by
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  have hUpper := actualCanonicalSection_finrank_le_two_of_hodge_injective
    E hg A hA hHodge
  have hEq : Module.finrank ℂ (ActualCanonicalSection E) = 2 :=
    Nat.le_antisymm hUpper hLower
  letI : Module.Finite ℂ (ActualCanonicalSection E) :=
    Module.finite_of_finrank_pos (by omega)
  exact ⟨Module.finBasisOfFinrankEq ℂ (ActualCanonicalSection E) hEq⟩

end CanonicalDimensionTwo
