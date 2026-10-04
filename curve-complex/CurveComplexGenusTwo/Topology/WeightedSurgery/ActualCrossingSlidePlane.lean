import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlideScalar
import CurveComplexGenusTwo.Topology.ChartLift

namespace CurveComplex.ActualCrossingSlide
open Set Schoenflies
noncomputable section

def rowAmount (a : Amount) (y : ℝ) : Amount := ⟨a.val * tent y, by
  rw [abs_mul, abs_of_nonneg (tent_nonneg y)]
  exact (mul_le_mul_of_nonneg_left (tent_le_one y) (abs_nonneg a.val)).trans_lt
    (by simpa using a.property)⟩

theorem rowAmount_continuous (a : Amount) : Continuous (rowAmount a) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul tent_continuous

def productSlide (a : Amount) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (scalar (rowAmount a p.2).val p.1, p.2)
  invFun p := (scalarInverse (rowAmount a p.2).val p.1, p.2)
  left_inv p := Prod.ext (scalarInverse_left _ (rowAmount a p.2).property p.1) rfl
  right_inv p := Prod.ext (scalarInverse_right _ (rowAmount a p.2).property p.1) rfl
  continuous_toFun := (scalar_continuous.comp
    (((continuous_subtype_val.comp (rowAmount_continuous a)).comp continuous_snd).prodMk
      continuous_fst)).prodMk continuous_snd
  continuous_invFun := (scalarInverse_continuous.comp
    ((rowAmount_continuous a).comp continuous_snd |>.prodMk continuous_fst)).prodMk continuous_snd

def timeAmount (a : Amount) (t : Interval) : Amount := ⟨t.val*a.val, by
  rw [abs_mul, abs_of_nonneg t.property.1]
  exact (mul_le_of_le_one_left (abs_nonneg a.val) t.property.2).trans_lt a.property⟩

def productIsotopy (a : Amount) : AmbientIsotopy (ℝ × ℝ) where
  map := ⟨fun z => productSlide (timeAmount a z.1) z.2, by
    change Continuous (fun z : Interval × (ℝ × ℝ) =>
      (scalar (z.1.val*a.val*tent z.2.2) z.2.1,z.2.2))
    apply Continuous.prodMk _ (continuous_snd.comp continuous_snd)
    exact scalar_continuous.comp ((((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (tent_continuous.comp (continuous_snd.comp continuous_snd))).prodMk
        (continuous_fst.comp continuous_snd))⟩
  homeomorphism_at t := ⟨productSlide (timeAmount a t), fun _ => rfl⟩
  at_zero p := by
    apply Prod.ext
    · simp [productSlide, timeAmount, rowAmount, scalar]
    · rfl

theorem productIsotopy_preserves_second (a : Amount) (t : Interval) (p : ℝ × ℝ) :
    ((productIsotopy a).map (t,p)).2 = p.2 := rfl

theorem productIsotopy_moves_crossing (a : Amount) (t : Interval) :
    (productIsotopy a).map (t,(0,0)) = (t.val*a.val,0) := by
  apply Prod.ext
  · simp [productIsotopy, productSlide, timeAmount, rowAmount, scalar, tent]
  · rfl

theorem productIsotopy_fixed (a : Amount) (t : Interval) (p : ℝ × ℝ)
    (hp : 1 ≤ |p.1| ∨ 1 ≤ |p.2|) : (productIsotopy a).map (t,p) = p := by
  apply Prod.ext
  · change scalar ((timeAmount a t).val * tent p.2) p.1 = p.1
    rcases hp with hx | hy
    · exact scalar_fixed _ _ hx
    · simp [scalar, tent, max_eq_left (by linarith : 1-|p.2| ≤ 0)]
  · rfl

def planeCoordinates : Plane ≃ₜ (ℝ × ℝ) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ (ℝ × ℝ))

def planeIsotopy (a : Amount) : AmbientIsotopy Plane where
  map := ⟨fun z => planeCoordinates.symm ((productIsotopy a).map (z.1,planeCoordinates z.2)),
    planeCoordinates.symm.continuous.comp ((productIsotopy a).map.continuous.comp
      (continuous_fst.prodMk (planeCoordinates.continuous.comp continuous_snd)))⟩
  homeomorphism_at t := ⟨(planeCoordinates.trans (productSlide (timeAmount a t))).trans
    planeCoordinates.symm, fun _ => rfl⟩
  at_zero p := by
    change planeCoordinates.symm ((productIsotopy a).map (⟨0,by norm_num⟩,planeCoordinates p)) = p
    rw [(productIsotopy a).at_zero, planeCoordinates.symm_apply_apply]

theorem planeIsotopy_coordinate (a : Amount) (t : Interval) (p : Plane) :
    planeCoordinates ((planeIsotopy a).map (t,p)) =
      (productIsotopy a).map (t,planeCoordinates p) :=
  planeCoordinates.apply_symm_apply _

theorem planeIsotopy_preserves_second (a : Amount) (t : Interval) (p : Plane) :
    ((planeIsotopy a).map (t,p)) 1 = p 1 := by
  exact congrArg Prod.snd (planeIsotopy_coordinate a t p)

theorem planeIsotopy_fixed (a : Amount) (t : Interval) (p : Plane)
    (hp : p ∉ Plane.closedSquare 0 1) : (planeIsotopy a).map (t,p) = p := by
  apply planeCoordinates.injective
  rw [planeIsotopy_coordinate]
  apply productIsotopy_fixed
  change 1 ≤ |p 0| ∨ 1 ≤ |p 1|
  have h : ¬ (|p 0| ≤ 1 ∧ |p 1| ≤ 1) := by
    intro hh
    apply hp
    simpa only [mem_closedSquare_zero_one, Plane.supNorm, max_le_iff] using hh
  rcases not_and_or.mp h with hx | hy
  · exact Or.inl (le_of_not_ge hx)
  · exact Or.inr (le_of_not_ge hy)

end
end CurveComplex.ActualCrossingSlide
