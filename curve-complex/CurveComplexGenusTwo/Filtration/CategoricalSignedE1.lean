import CurveComplexGenusTwo.Filtration.SignedFiltrationSpectralObjectFull
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import CurveComplexGenusTwo.Filtration.E1BridgeAssembly

namespace CurveGenusTwo.Filtration
open CategoryTheory CategoryTheory.Limits ComposableArrows
universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private theorem signedQuotientComplex_d_next
    (K : FiniteComplex V) (a : ArcLabels V B) (p m : ℤ) :
    ((Signed.genericQuotientComplex K a (p - 1) p (by omega)).d (m + 1) m).hom =
      (Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) m).toIntLinearMap := by
  simp only [Signed.genericQuotientComplex, ChainComplex.of_d]
  rfl

private theorem cast_eq_zero_iff_local {ι : Type*} (F : ι → Type*)
    [∀ i, Zero (F i)] {i j : ι} (h : i = j) (x : F i) :
    Eq.mp (congrArg F h) x = 0 ↔ x = 0 := by
  cases h
  rfl

theorem signedQuotientNextCast_ker_eq_boundary_ker
    (K : FiniteComplex V) (a : ArcLabels V B) (p m : ℤ) :
    (Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) m).ker =
      (Signed.genericQuotientBoundary K a (p - 1) p (by omega) (m + 1)).ker := by
  ext x
  simp only [AddMonoidHom.mem_ker,
    Signed.genericQuotientBoundaryNextCast_apply]
  exact cast_eq_zero_iff_local
    (Signed.genericQuotient K a (p - 1) p (by omega))
    (show m + 1 - 1 = m by omega) _

/-- At signed column `p` and bidegree `(p,q)`, Mathlib's categorical
spectral-object homology is the homology of the adjacent signed quotient
chain complex in degree `p+q`. -/
noncomputable def signedColumnHomologyIso
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    ((Signed.filtrationSpectralObject K a).H (-(p + q))).obj
      (mk₁ (homOfLE (show p - 1 ≤ p by omega))) ≅
    ((Signed.genericQuotientComplex K a (p - 1) p (by omega)).sc (p + q)).moduleCatLeftHomologyData.H := by
  dsimp only [Signed.filtrationSpectralObject,
    Signed.filtrationSpectralHomologyFunctor, Signed.filtrationQuotientFunctor,
    Signed.filtrationQuotientObj, Functor.comp_obj, mk₁,
    ComposableArrows.left, ComposableArrows.right,
    ComposableArrows.obj', Mk₁.obj]
  simpa only [neg_neg, HomologicalComplex.homologyFunctor_obj,
    HomologicalComplex.homology] using
    ((Signed.genericQuotientComplex K a (p - 1) p (by omega)).sc
      (p + q)).moduleCatHomologyIso

/-- The abstract homology of a short complex of integer modules identifies
with the quotient of its additive kernel by the incoming additive range. -/
noncomputable def moduleCatHomologyConcreteIso
    (S : ShortComplex (ModuleCat.{u} ℤ)) :
    S.homology ≅
      ModuleCat.of ℤ ((S.g.hom.toAddMonoidHom).ker ⧸
        ((S.f.hom.toAddMonoidHom).range.comap
          (S.g.hom.toAddMonoidHom).ker.subtype)) := by
  let d := S.g.hom.toAddMonoidHom
  let u := S.f.hom.toAddMonoidHom
  letI : Module ℤ ↥S.g.hom.ker := (S.g.hom.ker).module
  let P : AddSubgroup ↥S.g.hom.ker := S.moduleCatToCycles.range.toAddSubgroup
  let Q : AddSubgroup ↥S.g.hom.ker := u.range.comap d.ker.subtype
  have hP : P = Q := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy⟩
  haveI : P.Normal := inferInstance
  haveI : Q.Normal := inferInstance
  let e : (↥S.g.hom.ker ⧸ S.moduleCatToCycles.range) ≃+
      (↥d.ker ⧸ Q) :=
        @QuotientAddGroup.quotientAddEquivOfEq _ _ P Q
          (inferInstance : P.Normal) (inferInstance : Q.Normal) hP
  exact S.moduleCatHomologyIso ≪≫ e.toIntLinearEquiv.toModuleIso

noncomputable def signedQuotientScHomologyPageIso
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    let m := p + q - 1
    let C := Signed.genericQuotientComplex K a (p - 1) p (by omega)
    (C.sc' ((m + 1) + 1) (m + 1) m).homology ≅
      ModuleCat.of ℤ (spectralPageGroup K a 1 p q) := by
  let m := p + q - 1
  let C := Signed.genericQuotientComplex K a (p - 1) p (by omega)
  let S := C.sc' ((m + 1) + 1) (m + 1) m
  have hg : S.g.hom.toAddMonoidHom =
      Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) m := by
    change (((Signed.genericQuotientComplex K a (p - 1) p (by omega)).d (m + 1) m).hom).toAddMonoidHom = _
    rw [signedQuotientComplex_d_next]
    rfl
  have hf : S.f.hom.toAddMonoidHom =
      Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) (m + 1) := by
    change (((Signed.genericQuotientComplex K a (p - 1) p (by omega)).d ((m + 1) + 1) (m + 1)).hom).toAddMonoidHom = _
    rw [signedQuotientComplex_d_next]
    rfl
  have hker :
      (Signed.genericQuotientBoundaryNextCast K a (p - 1) p (by omega) m).ker =
      (Signed.genericQuotientBoundary K a (p - 1) p (by omega) (m + 1)).ker :=
    signedQuotientNextCast_ker_eq_boundary_ker K a p m
  let e := signedAdjacentQuotientHomologyEquiv K a p q
  let e' : ((S.g.hom.toAddMonoidHom).ker ⧸
      ((S.f.hom.toAddMonoidHom).range.comap
        (S.g.hom.toAddMonoidHom).ker.subtype)) ≃+
      spectralPageGroup K a 1 p q := by
    dsimp only [S, C] at hg hf ⊢
    rw [hg, hf]
    change (Signed.genericQuotientBoundaryNextCast K a (p - 1) p (show p - 1 ≤ p by omega) m).ker ⧸
      ((Signed.genericQuotientBoundaryNextCast K a (p - 1) p (show p - 1 ≤ p by omega) (m + 1)).range.comap
        (Signed.genericQuotientBoundaryNextCast K a (p - 1) p (show p - 1 ≤ p by omega) m).ker.subtype) ≃+
      spectralPageGroup K a 1 p q
    dsimp only [m] at hker ⊢
    have hm : p + q - 1 + 1 = p + q := by omega
    rw [hker]
    convert e using 1
    exact congrArg (fun n : ℤ =>
      ((Signed.genericQuotientBoundary K a (p - 1) p (show p - 1 ≤ p by omega) n).ker ⧸
        ((Signed.genericQuotientBoundaryNextCast K a (p - 1) p (show p - 1 ≤ p by omega) n).range.comap
          (Signed.genericQuotientBoundary K a (p - 1) p (show p - 1 ≤ p by omega) n).ker.subtype)) ≃+
        spectralPageGroup K a 1 p q) hm
  exact moduleCatHomologyConcreteIso S ≪≫
    e'.toIntLinearEquiv.toModuleIso

/-- The first homology page of the signed filtration spectral object agrees
with the concrete page in every integer column, including column zero. -/
noncomputable def signedCategoricalE1PageIso
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ) :
    ((Signed.filtrationSpectralObject K a).H (-(p + q))).obj
      (mk₁ (homOfLE (show p - 1 ≤ p by omega))) ≅
        ModuleCat.of ℤ (spectralPageGroup K a 1 p q) := by
  let n := p + q
  let m := p + q - 1
  let C := Signed.genericQuotientComplex K a (p - 1) p (by omega)
  have hm : m + 1 = n := by omega
  exact signedColumnHomologyIso K a p q ≪≫
    (C.sc n).moduleCatHomologyIso.symm ≪≫
    eqToIso (congrArg (fun i : ℤ => C.homology i) hm.symm) ≪≫
    C.homologyIsoSc' ((m + 1) + 1) (m + 1) m
      (by simp only [ChainComplex.prev])
      (by rw [ChainComplex.next]; omega) ≪≫
    signedQuotientScHomologyPageIso K a p q

end CurveGenusTwo.Filtration
