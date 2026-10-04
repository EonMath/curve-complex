import CurveComplexGenusTwo.Filtration.CarrierApproximationBase
open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

private theorem castHom_apply {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by cases h; rfl

private theorem castHom_eq_zero_iff {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x = 0 ↔ f x = 0 := by cases h; rfl

theorem positiveBoundary_eq_zero_iff (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n+1:ℕ):ℤ)) :
    positiveBoundary K n c = 0 ↔ boundary K ((n+1:ℕ):ℤ) c = 0 := by
  unfold positiveBoundary
  exact castHom_eq_zero_iff (show (((n+1:ℕ):ℤ)-1) = (n:ℤ) by omega) _ _

theorem exists_starSmall_carried_extension_natural (K : FiniteComplex V) (n : ℕ)
    (f : FreeAbelianGroup (StarSmallSimplex K n) →+ chains K (n:ℤ))
    (hcycle : ∀ c : FreeAbelianGroup (StarSmallSimplex K (n+1)),
      boundary K (n:ℤ) (f (starSmallBoundary K n c)) = 0)
    (hcarried : ∀ s : StarSmallSimplex K n, f (FreeAbelianGroup.of s) ∈
      (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
        (realizationCarrier_subcomplex K _) (n:ℤ)).range) :
    ∃ F : FreeAbelianGroup (StarSmallSimplex K (n+1)) →+ chains K ((n+1:ℕ):ℤ),
      (∀ c, positiveBoundary K n (F c) = f (starSmallBoundary K n c)) ∧
      (∀ s : StarSmallSimplex K (n+1), F (FreeAbelianGroup.of s) ∈
        (chainInclusion (realizationCarrier K (singularSimplexImage K (n+1) s.1)) K
          (realizationCarrier_subcomplex K _) ((n+1:ℕ):ℤ)).range) := by
  have hidx : (((n+1:ℕ):ℤ)-1) = (n:ℤ) := by omega
  let e : chains K (((n+1:ℕ):ℤ)-1) ≃+ chains K (n:ℤ) :=
    AddEquiv.cast (M := chains K) hidx
  let f' := e.symm.toAddMonoidHom.comp f
  have hc' : ∀ c : FreeAbelianGroup (StarSmallSimplex K (n+1)),
      boundary K (((n+1:ℕ):ℤ)-1) (f' (starSmallBoundary K n c)) = 0 := by
    intro c
    have aux (i j : ℤ) (h : i = j) (a : chains K j) (ha : boundary K j a = 0) :
        boundary K i ((AddEquiv.cast (M := chains K) h).symm a) = 0 := by
      cases h
      exact ha
    exact aux _ _ hidx _ (hcycle c)
  have hf' : ∀ s : StarSmallSimplex K n, f' (FreeAbelianGroup.of s) ∈
      (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
        (realizationCarrier_subcomplex K _) (((n+1:ℕ):ℤ)-1)).range := by
    intro s
    have aux (i j : ℤ) (h : i = j) (a : chains K j)
        (ha : a ∈ (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
          (realizationCarrier_subcomplex K _) j).range) :
        (AddEquiv.cast (M := chains K) h).symm a ∈
          (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
            (realizationCarrier_subcomplex K _) i).range := by
      cases h
      exact ha
    exact aux _ _ hidx _ (hcarried s)
  obtain ⟨F, hF, hcar⟩ := exists_starSmall_carried_extension_of_cycles K n
    ((n+1:ℕ):ℤ) (by omega) f' hc' hf'
  refine ⟨F, ?_, hcar⟩
  intro c
  unfold positiveBoundary
  rw [castHom_apply hidx, hF]
  exact e.apply_symm_apply _

#print axioms exists_starSmall_carried_extension_natural
end CurveGenusTwo.Filtration
