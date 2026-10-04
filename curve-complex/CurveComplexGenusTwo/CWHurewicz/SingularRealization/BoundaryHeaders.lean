import CurveComplexGenusTwo.CWHurewicz.SingularRealization.GeometryHeaders
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.SingularApproximation

theorem simplex_boundary_face_representation (n : ℕ) (t : StdSimplex ℝ (Fin (n + 2))) (h : ¬ ∀ i, 0 < t.weights i) :
    ∃ (i : Fin (n + 2)) (u : StdSimplex ℝ (Fin (n + 1))), StdSimplex.map (SimplexCategory.δ i) u = t := by
  classical
  push Not at h
  obtain ⟨i, hi⟩ := h
  have hzero : t.weights i = 0 := le_antisymm hi (t.weights_nonneg i)
  have hr : Set.range (SimplexCategory.δ i) = ({i} : Set (Fin (n + 2)))ᶜ := Fin.range_succAbove i
  have ht : t ∈ Set.range (StdSimplex.map (SimplexCategory.δ i)) :=
    (StdSimplex.mem_range_map_iff (SimplexCategory.δ i) t).mpr (by
      intro j hj
      have hji : j = i := by simpa only [hr, Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hj
      simpa only [hji] using hzero)
  obtain ⟨u, hu⟩ := ht
  exact ⟨i, u, hu⟩

theorem realization_boundary_finite_nondegenerate_faces (S : SSet.{0}) (n : ℕ) (s : S _⦋n + 1⦌)
    (t : StdSimplex ℝ (Fin (n + 2))) (h : ¬ ∀ i, 0 < t.weights i) :
    ∃ (i : Fin (n + 2))
      (v : StdSimplex ℝ (Fin ((SSet.S.mk (S.δ i s)).toN.dim + 1))),
      (SSet.S.mk (S.δ i s)).toN.dim ≤ n ∧
      SSet.toTop.map (SSet.yonedaEquiv.symm (SSet.S.mk (S.δ i s)).toN.simplex)
          (⦋(SSet.S.mk (S.δ i s)).toN.dim⦌.toTopHomeo.symm v) =
        SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n + 1⦌.toTopHomeo.symm t) := by
  classical
  push Not at h
  obtain ⟨i, hi⟩ := h
  have hzero : t.weights i = 0 := le_antisymm hi (t.weights_nonneg i)
  have hr : Set.range (SimplexCategory.δ i) = ({i} : Set (Fin (n + 2)))ᶜ := Fin.range_succAbove i
  obtain ⟨u, hu⟩ := (StdSimplex.mem_range_map_iff (SimplexCategory.δ i) t).mpr (by
    intro j hj
    have hji : j = i := by simpa only [hr, Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hj
    simpa only [hji] using hzero)
  let a := SSet.S.mk (S.δ i s)
  let π := a.toNπ
  have hπ : S.map π.op a.toN.simplex = S.δ i s := a.map_toNπ_op_apply
  have hface : SSet.stdSimplex.map (SimplexCategory.δ i) ≫ SSet.yonedaEquiv.symm s =
      SSet.yonedaEquiv.symm (S.δ i s) := (uliftYonedaEquiv_symm_map (SimplexCategory.δ i).op s).symm
  have hroot : SSet.stdSimplex.map π ≫ SSet.yonedaEquiv.symm a.toN.simplex =
      SSet.yonedaEquiv.symm (S.δ i s) := by
    rw [← hπ]
    exact (uliftYonedaEquiv_symm_map π.op a.toN.simplex).symm
  refine ⟨i, StdSimplex.map π u, a.dim_toN_le, ?_⟩
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.map π) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm a.toN.simplex)) (⦋n⦌.toTopHomeo.symm u) = _
  rw [← SSet.toTop.map_comp, hroot, ← hface, SSet.toTop.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm s)
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ i)) (⦋n⦌.toTopHomeo.symm u)) = _
  rw [← SimplexCategory.toTopHomeo_symm_naturality_apply, hu]

end CurveComplexGenusTwo.CWHurewicz.SingularApproximation
