import CurveComplexGenusTwo.Filtration.CarrierApproximationNatural

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

/-- Data maintained in each degree of the recursive carrier approximation. -/
structure StarSmallApproximationStage (K : FiniteComplex V) (n : ℕ) where
  map : FreeAbelianGroup (StarSmallSimplex K n) →+ chains K (n:ℤ)
  carried : ∀ s : StarSmallSimplex K n, map (FreeAbelianGroup.of s) ∈
    (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
      (realizationCarrier_subcomplex K _) (n:ℤ)).range
  cycle : ∀ c : FreeAbelianGroup (StarSmallSimplex K (n+1)),
    boundary K (n:ℤ) (map (starSmallBoundary K n c)) = 0

noncomputable def starSmallApproximationZero (K : FiniteComplex V) :
    StarSmallApproximationStage K 0 where
  map := (exists_starSmall_zero_approximation K).choose
  carried := (exists_starSmall_zero_approximation K).choose_spec.1
  cycle := (exists_starSmall_zero_approximation K).choose_spec.2

noncomputable def starSmallApproximationNext (K : FiniteComplex V) (n : ℕ)
    (a : StarSmallApproximationStage K n) : StarSmallApproximationStage K (n+1) where
  map := (exists_starSmall_carried_extension_natural K n a.map a.cycle a.carried).choose
  carried := (exists_starSmall_carried_extension_natural K n a.map a.cycle a.carried).choose_spec.2
  cycle := by
    intro c
    apply (positiveBoundary_eq_zero_iff K n _).mp
    rw [(exists_starSmall_carried_extension_natural K n a.map a.cycle a.carried).choose_spec.1,
      starSmallBoundary_squared, map_zero]

theorem starSmallApproximationNext_boundary (K : FiniteComplex V) (n : ℕ)
    (a : StarSmallApproximationStage K n)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1))) :
    positiveBoundary K n ((starSmallApproximationNext K n a).map c) =
      a.map (starSmallBoundary K n c) :=
  (exists_starSmall_carried_extension_natural K n a.map a.cycle a.carried).choose_spec.1 c

noncomputable def starSmallApproximationStage (K : FiniteComplex V) :
    (n : ℕ) → StarSmallApproximationStage K n :=
  Nat.rec (starSmallApproximationZero K) (fun n a => starSmallApproximationNext K n a)

/-- A genuine carrier-based map from star-small singular chains to simplicial
chains, defined in every nonnegative degree. -/
noncomputable def starSmallSimplicialApproximation (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup (StarSmallSimplex K n) →+ chains K (n:ℤ) :=
  (starSmallApproximationStage K n).map

theorem starSmallSimplicialApproximation_carried (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K n) :
    starSmallSimplicialApproximation K n (FreeAbelianGroup.of s) ∈
      (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
        (realizationCarrier_subcomplex K _) (n:ℤ)).range :=
  (starSmallApproximationStage K n).carried s

theorem starSmallSimplicialApproximation_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1))) :
    positiveBoundary K n (starSmallSimplicialApproximation K (n+1) c) =
      starSmallSimplicialApproximation K n (starSmallBoundary K n c) :=
  starSmallApproximationNext_boundary K n (starSmallApproximationStage K n) c

noncomputable def starSmallSimplicialCyclesMap (K : FiniteComplex V) (n : ℕ) :
    (starSmallBoundary K n).ker →+ cycles K ((n+1:ℕ):ℤ) :=
  ((starSmallSimplicialApproximation K (n+1)).comp (starSmallBoundary K n).ker.subtype).codRestrict
    (cycles K ((n+1:ℕ):ℤ)) (by
      intro c
      change boundary K ((n+1:ℕ):ℤ) (starSmallSimplicialApproximation K (n+1) c.1) = 0
      apply (positiveBoundary_eq_zero_iff K n _).mp
      rw [starSmallSimplicialApproximation_boundary, show starSmallBoundary K n c.1 = 0 from c.2,
        map_zero])

#print axioms starSmallSimplicialApproximation
#print axioms starSmallSimplicialApproximation_boundary
#print axioms starSmallSimplicialCyclesMap
end CurveGenusTwo.Filtration
