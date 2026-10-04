import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.RawCompactCutQuotient

open Set Topology

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Nonneg := Set.Ici (0 : ℝ)

noncomputable def quadrantFlatten : (Nonneg × Nonneg) ≃ₜ (ℝ × Nonneg) where
  toFun p := (p.1.val - p.2.val,
    ⟨min p.1.val p.2.val, by
      exact le_min (show 0 ≤ p.1.val from p.1.property)
        (show 0 ≤ p.2.val from p.2.property)⟩)
  invFun q :=
    (⟨max q.1 0 + q.2.val, by
      exact add_nonneg (le_max_right _ _) (show 0 ≤ q.2.val from q.2.property)⟩,
     ⟨max (-q.1) 0 + q.2.val, by
      exact add_nonneg (le_max_right _ _) (show 0 ≤ q.2.val from q.2.property)⟩)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      rcases le_total p.1.val p.2.val with h | h
      · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
        ring
    · apply Subtype.ext
      dsimp
      rw [neg_sub]
      rcases le_total p.1.val p.2.val with h | h
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
        ring
      · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
        ring
  right_inv q := by
    apply Prod.ext
    · dsimp
      rcases le_total 0 q.1 with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -q.1 ≤ 0)]
        ring
      · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -q.1)]
        ring
    · apply Subtype.ext
      dsimp
      rcases le_total 0 q.1 with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -q.1 ≤ 0)]
        rw [min_eq_right (by linarith)]
        ring
      · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -q.1)]
        rw [min_eq_left (by linarith)]
        ring
  continuous_toFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.subtype_mk
      fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      fun_prop
    · apply Continuous.subtype_mk
      fun_prop

noncomputable def halfPlaneEuclidean : (ℝ × Nonneg) ≃ₜ EuclideanHalfSpace 2 := by
  let e2 : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow (X := ℝ))
  let h2 : EuclideanHalfSpace 2 ≃ₜ {p : ℝ × ℝ // 0 ≤ p.1} :=
    e2.subtype (fun _ => by rfl)
  let hproduct : (ℝ × Nonneg) ≃ₜ {p : ℝ × ℝ // 0 ≤ p.1} := {
    toFun := fun p => ⟨(p.2.val,p.1),p.2.property⟩
    invFun := fun p => (p.val.2,⟨p.val.1,p.property⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact hproduct.trans h2.symm

noncomputable def quadrantHalfSpace : (Nonneg × Nonneg) ≃ₜ EuclideanHalfSpace 2 :=
  quadrantFlatten.trans halfPlaneEuclidean

theorem halfPlaneEuclidean_coord0 (p : ℝ × Nonneg) :
    (halfPlaneEuclidean p).val 0 = p.2.val := by
  change ((EuclideanSpace.equiv (Fin 2) ℝ).symm
    ((Homeomorph.finTwoArrow (X := ℝ)).symm (p.2.val,p.1))) 0 = p.2.val
  simp [Homeomorph.finTwoArrow, finTwoArrowEquiv]

theorem quadrantHalfSpace_coord0 (p : Nonneg × Nonneg) :
    (quadrantHalfSpace p).val 0 = min p.1.val p.2.val := by
  simpa [quadrantHalfSpace, quadrantFlatten] using
    halfPlaneEuclidean_coord0 (quadrantFlatten p)

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
