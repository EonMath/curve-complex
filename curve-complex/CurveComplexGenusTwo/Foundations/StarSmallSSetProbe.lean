import CurveComplexGenusTwo.Foundations.StarSmallFaces

open CategoryTheory Topology Convexity
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

noncomputable def starSmallSubcomplex (K : FiniteComplex V) :
    (TopCat.toSSet.obj (TopCat.of (geometricRealization K))).Subcomplex where
  obj Δ := {s | ∃ v : ActiveVertex K,
    Set.range (TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) Δ s) ⊆
      CurveComplex.openVertexStar (geometricComplex K) v}
  map := by
    intro Δ Γ f s hs
    obtain ⟨v, hv⟩ := hs
    refine ⟨v, ?_⟩
    rintro x ⟨t, rfl⟩
    apply hv
    exact ⟨StdSimplex.map f.unop t, (TopCat.toSSetObjEquiv_naturality_apply _ _ _).symm⟩

noncomputable def starSmallBoundary (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup (StarSmallSimplex K (n + 1)) →+
      FreeAbelianGroup (StarSmallSimplex K n) :=
  (AlgebraicTopology.AlternatingFaceMapComplex.objD
    ((starSmallSubcomplex K).toSSet ⋙ AddCommGrpCat.free) n).hom

theorem starSmallBoundary_squared (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n + 2))) :
    starSmallBoundary K n (starSmallBoundary K (n + 1) c) = 0 := by
  have h := AlgebraicTopology.AlternatingFaceMapComplex.d_squared
    ((starSmallSubcomplex K).toSSet ⋙ AddCommGrpCat.free) n
  exact congrArg (fun f => f.hom c) h

theorem starSmallBoundary_of (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K (n + 1)) :
    starSmallBoundary K n (FreeAbelianGroup.of s) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        FreeAbelianGroup.of (starSmallFace K n i s) := by
  classical
  have hs {A B : AddCommGrpCat.{u}} {ι : Type} (t : Finset ι) (f : ι → (A ⟶ B)) :
      (∑ i ∈ t, f i).hom = ∑ i ∈ t, (f i).hom :=
    map_sum AddCommGrpCat.homAddEquiv f t
  change (AlgebraicTopology.AlternatingFaceMapComplex.objD
    ((starSmallSubcomplex K).toSSet ⋙ AddCommGrpCat.free) n).hom
    (FreeAbelianGroup.of s) = _
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  rw [hs]
  change (∑ i : Fin (n + 2),
    ((-1 : ℤ) ^ i.val • (FreeAbelianGroup.map (fun t : StarSmallSimplex K (n + 1) =>
      starSmallFace K n i t)))) (FreeAbelianGroup.of s) = _
  simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply,
    FreeAbelianGroup.map_of_apply]
end CurveGenusTwo.Filtration
