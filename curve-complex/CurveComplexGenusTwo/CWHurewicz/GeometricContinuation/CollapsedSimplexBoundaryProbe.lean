import CurveComplexGenusTwo.CWHurewicz.SingularRealization.BoundaryHeaders
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
open CategoryTheory Convexity
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open SingularApproximation
theorem collapsedSimplex_boundary {X : Type} [TopologicalSpace X] (S : SSet.{0}) (n : ℕ) (x : X)
    (g : C(SSet.toTop.obj S, X))
    (hg : ∀ a : SSet.toTop.obj (S.skeleton (n + 1)).toSSet,
      g (SSet.toTop.map (S.skeleton (n + 1)).ι a) = x)
    (s : S _⦋n + 1⦌) (t : StdSimplex ℝ (Fin (n + 2)))
    (ht : ¬ ∀ i, 0 < t.weights i) :
    g (SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n + 1⦌.toTopHomeo.symm t)) = x := by
  obtain ⟨i, v, hd, he⟩ := realization_boundary_finite_nondegenerate_faces S n s t ht
  let a := SSet.S.mk (S.δ i s)
  have ha : a.toN.dim ≤ n := hd
  let b : (S.skeleton (n + 1)).toSSet _⦋a.toN.dim⦌ :=
    ⟨a.toN.simplex, S.mem_skeleton a.toN.simplex (by omega)⟩
  let z := SSet.toTop.map (SSet.yonedaEquiv.symm b) (⦋a.toN.dim⦌.toTopHomeo.symm v)
  have hz : SSet.toTop.map (S.skeleton (n + 1)).ι z =
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n + 1⦌.toTopHomeo.symm t) := by
    change (SSet.toTop.map (SSet.yonedaEquiv.symm b) ≫
      SSet.toTop.map (S.skeleton (n + 1)).ι) (⦋a.toN.dim⦌.toTopHomeo.symm v) = _
    rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp]
    exact he
  rw [← hz]
  exact hg z
theorem unit_characteristic_apply (S : SSet.{0}) (n : ℕ) (s : S _⦋n⦌)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    TopCat.toSSetObjEquiv (SSet.toTop.obj S) (.op ⦋n⦌)
      ((sSetTopAdj.unit.app S).app (.op ⦋n⦌) s) t =
    SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t) := by
  change ((sSetTopAdj.unit.app S).app (.op ⦋n⦌) s).down.hom (ULift.up t) = _
  rw [sSetTopAdj_unit_app_app_down]
  rfl
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
