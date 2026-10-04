import CurveComplexGenusTwo.Filtration.CarrierApproximationExtension

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

/-- A vertex in the common open star is a vertex of the actual image carrier. -/
theorem starSmallSimplex_exists_carried_vertex (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K n) :
    ∃ v : ActiveVertex K, ({v.1} : Finset V) ∈
      realizationCarrier K (singularSimplexImage K n s.1) := by
  obtain ⟨v, hv⟩ := s.2
  refine ⟨v, ?_⟩
  let x := (TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) (.op ⦋n⦌) s.1)
    (.single 0)
  have hx : x ∈ singularSimplexImage K n s.1 := ⟨.single 0, rfl⟩
  refine ⟨x, hx, ?_⟩
  intro w hw
  have hwv := Finset.mem_singleton.mp hw
  subst w
  exact ⟨v.2, hv hx⟩

theorem exists_starSmall_zero_approximation (K : FiniteComplex V) :
    ∃ f : FreeAbelianGroup (StarSmallSimplex K 0) →+ chains K 0,
      (∀ s : StarSmallSimplex K 0, f (FreeAbelianGroup.of s) ∈
        (chainInclusion (realizationCarrier K (singularSimplexImage K 0 s.1)) K
          (realizationCarrier_subcomplex K _) 0).range) ∧
      (∀ c : FreeAbelianGroup (StarSmallSimplex K 1),
        boundary K 0 (f (starSmallBoundary K 0 c)) = 0) := by
  classical
  choose v hv using starSmallSimplex_exists_carried_vertex K 0
  let σ (s : StarSmallSimplex K 0) : SimplexAt K 0 :=
    ⟨{(v s).1}, (v s).2, Or.inr ⟨by omega, by simp⟩⟩
  let f : FreeAbelianGroup (StarSmallSimplex K 0) →+ chains K 0 :=
    FreeAbelianGroup.lift (fun s => FreeAbelianGroup.of (σ s))
  have heq (s t : StarSmallSimplex K 0) :
      boundary K 0 (f (FreeAbelianGroup.of s)) =
        boundary K 0 (f (FreeAbelianGroup.of t)) := by
    have he : (∅ : Finset V) ∈ K := K.down_closed (Finset.empty_subset _) (v s).2
    simp [f, σ, boundary, faceBoundary, he, Finset.filter_singleton]
  refine ⟨f, ?_, ?_⟩
  · intro s
    refine ⟨FreeAbelianGroup.of (⟨{(v s).1}, hv s,
      Or.inr ⟨by omega, by simp⟩⟩ : SimplexAt _ 0), ?_⟩
    rfl
  · intro c
    have h : ((boundary K 0).comp f).comp (starSmallBoundary K 0) = 0 := by
      apply FreeAbelianGroup.lift_ext
      intro s
      change boundary K 0 (f (starSmallBoundary K 0 (FreeAbelianGroup.of s))) = 0
      rw [starSmallBoundary_of, Fin.sum_univ_two]
      simp only [map_add, map_zsmul]
      norm_num
      rw [heq (starSmallFace K 0 0 s) (starSmallFace K 0 1 s), add_neg_cancel]
    exact DFunLike.congr_fun h c

#print axioms exists_starSmall_zero_approximation
end CurveGenusTwo.Filtration
