import CurveComplexGenusTwo.Filtration.RawSingularBridge
import CurveComplexGenusTwo.Filtration.StarSmallSubdivision

open CategoryTheory Topology Convexity
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

theorem singularPositiveCycle_has_starSmall_representative
    (K : FiniteComplex V) (n : ℕ) (z : singularPositiveCycles K n) :
    ∃ z' : singularPositiveCycles K n,
      z'.1 - z.1 ∈ singularPositiveBoundaries K n ∧
      ∀ y ∈ (FreeAbelianGroup.toFinsupp z'.1).support,
        ∃ v : ActiveVertex K,
          (TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K))
            (.op ⦋n + 1⦌) y) '' Set.univ ⊆
              CurveComplex.openVertexStar (geometricComplex K) v := by
  let X := TopCat.of (geometricRealization K)
  let c := FreeAbelianGroup.toFinsupp z.1
  have hc : singularBoundaryFinsupp X n c = 0 := by
    rw [← toFinsupp_singularGeneratorBoundary]
    have hz : singularGeneratorBoundary K n z.1 = 0 := z.2
    rw [hz, map_zero]
  obtain ⟨k, hk⟩ := singularBarycentricIterateList_eventually_starSmall
    (geometricComplex K) (n + 1) c
  have hlist : ∀ (d j : ℕ)
      (a : (TopCat.toSSet.obj X) _⦋d⦌ →₀ ℤ),
      singularBarycentricIterateList X d j a = singularBarycentricIterate X d j a := by
    intro d j a
    induction j with
    | zero => rfl
    | succ j ih => simp only [singularBarycentricIterateList,
        singularBarycentricIterate_succ, ih]
  let c' := singularBarycentricIterate X (n + 1) k c
  let z' := Finsupp.toFreeAbelianGroup c'
  have hz' : z' ∈ singularPositiveCycles K n := by
    change singularGeneratorBoundary K n z' = 0
    apply (FreeAbelianGroup.equivFinsupp _).injective
    simp only [FreeAbelianGroup.equivFinsupp_apply, map_zero,
      toFinsupp_singularGeneratorBoundary]
    dsimp only [z']
    rw [FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
    dsimp only [c']
    rw [singularBarycentricIterate_boundary, hc, map_zero]
  refine ⟨⟨z', hz'⟩, ?_, ?_⟩
  · refine ⟨Finsupp.toFreeAbelianGroup
      (singularCarrierHomotopyIterate X (n + 1) k c), ?_⟩
    apply (FreeAbelianGroup.equivFinsupp _).injective
    change FreeAbelianGroup.toFinsupp _ = FreeAbelianGroup.toFinsupp _
    rw [toFinsupp_singularGeneratorBoundary]
    simp only [FreeAbelianGroup.toFinsupp_toFreeAbelianGroup, map_sub]
    dsimp only [z']
    rw [FreeAbelianGroup.toFinsupp_toFreeAbelianGroup]
    have h := singularCarrierHomotopyIterate_boundary_succ X n k c
    simpa only [hc, map_zero, add_zero] using h
  · intro y hy
    apply hk y
    dsimp only [z'] at hy
    rw [FreeAbelianGroup.toFinsupp_toFreeAbelianGroup] at hy
    rw [hlist]
    exact hy
end CurveGenusTwo.Filtration
