import CurveComplexGenusTwo.Foundations.RealizationCarrier

open CategoryTheory Topology Convexity
open scoped Simplicial
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

def singularSimplexImage (K : FiniteComplex V) (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) :
    Set (geometricRealization K) :=
  Set.range (TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) (.op ⦋n⦌) s)

def StarSmallSimplex (K : FiniteComplex V) (n : ℕ) :=
  {s : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌ //
    ∃ v : ActiveVertex K, singularSimplexImage K n s ⊆
      CurveComplex.openVertexStar (geometricComplex K) v}

theorem singularSimplexImage_face_subset (K : FiniteComplex V) (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    singularSimplexImage K n ((TopCat.toSSet.obj
      (TopCat.of (geometricRealization K))).δ i s) ⊆ singularSimplexImage K (n + 1) s := by
  rintro x ⟨t, rfl⟩
  refine ⟨StdSimplex.map i.succAbove t, ?_⟩
  exact (TopCat.toSSetObjEquiv_δ_apply _ _ _).symm

noncomputable def starSmallFace (K : FiniteComplex V) (n : ℕ) (i : Fin (n + 2))
    (s : StarSmallSimplex K (n + 1)) : StarSmallSimplex K n :=
  ⟨(TopCat.toSSet.obj (TopCat.of (geometricRealization K))).δ i s.1, by
    obtain ⟨v, hv⟩ := s.2
    exact ⟨v, (singularSimplexImage_face_subset K n s.1 i).trans hv⟩⟩

theorem starSmallFace_carrier_subset (K : FiniteComplex V) (n : ℕ)
    (i : Fin (n + 2)) (s : StarSmallSimplex K (n + 1)) :
    (realizationCarrier K (singularSimplexImage K n (starSmallFace K n i s).1)).simplices ⊆
      (realizationCarrier K (singularSimplexImage K (n + 1) s.1)).simplices := by
  exact realizationCarrier_mono K (singularSimplexImage_face_subset K n s.1 i)

theorem starSmallSimplex_carrier_isNonemptyCone (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K n) :
    IsNonemptyCone (realizationCarrier K (singularSimplexImage K n s.1)) := by
  obtain ⟨v, hv⟩ := s.2
  apply realizationCarrier_isNonemptyCone K _ _ v hv
  exact ⟨(TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K))
    (.op ⦋n⦌) s.1) (.single 0), ⟨.single 0, rfl⟩⟩
end CurveGenusTwo.Filtration
