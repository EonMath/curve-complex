import CurveComplexGenusTwo.CWHurewicz.SingularRealization.FiniteRealizationCW
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.FiniteRealizationCompactHeader
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.NormalFormHeaders
open CategoryTheory Convexity Topology
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open SingularApproximation
theorem finite_realization_subcomplex_closedEmbedding (S : SSet.{0}) [S.Finite] (A : S.Subcomplex) :
    IsClosedEmbedding (SSet.toTop.map A.ι) := by
  have hinj (S : SSet.{0}) (A : S.Subcomplex) :
    Function.Injective (SSet.toTop.map A.ι) := by
    intro x y hxy
    obtain ⟨n, s, t, ht, hx⟩ := realization_positive_nondegenerate_representation A.toSSet x
    obtain ⟨m, u, v, hv, hy⟩ := realization_positive_nondegenerate_representation A.toSSet y
    let s' : S.nonDegenerate n := ⟨A.ι.app _ s.val,
      (SSet.nonDegenerate_iff_of_mono A.ι s.val).mpr s.property⟩
    let u' : S.nonDegenerate m := ⟨A.ι.app _ u.val,
      (SSet.nonDegenerate_iff_of_mono A.ι u.val).mpr u.property⟩
    have hpush (l : ℕ) (a : A.toSSet.nonDegenerate l) (z : StdSimplex ℝ (Fin (l + 1))) :
        SSet.toTop.map A.ι
          (SSet.toTop.map (SSet.yonedaEquiv.symm a.val) (⦋l⦌.toTopHomeo.symm z)) =
        SSet.toTop.map (SSet.yonedaEquiv.symm (A.ι.app _ a.val)) (⦋l⦌.toTopHomeo.symm z) := by
      change (SSet.toTop.map (SSet.yonedaEquiv.symm a.val) ≫ SSet.toTop.map A.ι) _ = _
      rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp]
    have he : SSet.toTop.map (SSet.yonedaEquiv.symm s'.val) (⦋n⦌.toTopHomeo.symm t) =
        SSet.toTop.map (SSet.yonedaEquiv.symm u'.val) (⦋m⦌.toTopHomeo.symm v) := by
      rw [← hpush n s t, ← hpush m u v, hx, hy]
      exact hxy
    have h := realization_nondegenerate_interiors_injective S
      (a₁ := ⟨⟨n, s'⟩, ⟨t, ht⟩⟩) (a₂ := ⟨⟨m, u'⟩, ⟨v, hv⟩⟩) he
    have hd : n = m := congrArg (fun z => z.1.1) h
    subst m
    have hsu : s' = u' := eq_of_heq (Sigma.mk.inj (congrArg Sigma.fst h)).2
    have hval := congrArg (fun z : S.nonDegenerate n => z.val) hsu
    change s.val.val = u.val.val at hval
    have hsource : s = u := Subtype.ext (Subtype.ext hval)
    subst u
    have htv : t = v := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h).2)
    subst v
    exact hx.symm.trans hy
  obtain ⟨d, hd⟩ := SSet.hasDimensionLT_of_finite S
  have := hd
  obtain ⟨cw, ht2, _, _⟩ := finite_realization_cw S d
  have := ht2
  have : CompactSpace (SSet.toTop.obj A.toSSet) := finite_realization_compactSpace A.toSSet
  exact (SSet.toTop.map A.ι).hom.continuous.isClosedEmbedding (hinj S A)
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
