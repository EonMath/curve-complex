import CurveComplexGenusTwo.Octagon.GraphMV.OverlapHZero

noncomputable section
open CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV
set_option backward.isDefEq.respectTransparency false

/-- The actual overlap augmentation sums the canonical low/high edge coordinates. -/
theorem overlap_augmentation_sum
    (x : H ↥(vertexStar ∩ edgeMiddles) 0) :
    ((TopCat.of ↥(vertexStar ∩ edgeMiddles)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) x =
      ∑ i : Fin 4, (overlapHZeroCoordinates x (i, false) +
        overlapHZeroCoordinates x (i, true)) := by
  classical
  let e := overlapHZeroCoordinates
  let P : Fin 4 × Bool → H ↥(vertexStar ∩ edgeMiddles) 0 := fun p =>
    pointClass (TopCat.toSSet.obj (TopCat.of ↥(vertexStar ∩ edgeMiddles)))
      (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) (1 : ℤ)
  have hp (p : Fin 4 × Bool) : e (P p) = Pi.single p (1 : ℤ) :=
    overlapHZeroCoordinates_point p
  have hdecomp : x = ∑ p : Fin 4 × Bool, (e x p) • P p := by
    apply e.injective
    rw [map_sum]
    simp only [map_zsmul, hp]
    have hsingle (p : Fin 4 × Bool) :
        (e x p) • (Pi.single p (1 : ℤ) : Fin 4 × Bool → ℤ) = Pi.single p (e x p) := by
      funext q
      by_cases h : q = p
      · subst q; simp
      · simp [Pi.single_apply, h]
    simp only [hsingle]
    exact (Finset.univ_sum_single (e x)).symm
  have ha (p : Fin 4 × Bool) :
      ((TopCat.of ↥(vertexStar ∩ edgeMiddles)).singularHomology₀ε
        (ModuleCat.of ℤ ℤ)) (P p) = 1 := by
    have hm : pointClass (TopCat.toSSet.obj (TopCat.of ↥(vertexStar ∩ edgeMiddles)))
        (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) ≫
        ((TopCat.of ↥(vertexStar ∩ edgeMiddles)).singularHomology₀ε
          (ModuleCat.of ℤ ℤ)) = 𝟙 _ := by
      simp [pointClass, TopCat.singularHomology₀ε, SSet.homology₀ε]
    exact congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f (1 : ℤ)) hm
  calc
    _ = ((TopCat.of ↥(vertexStar ∩ edgeMiddles)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) (∑ p : Fin 4 × Bool, (e x p) • P p) := congrArg _ hdecomp
    _ = ∑ p : Fin 4 × Bool, e x p := by
      simp only [map_sum, map_zsmul, ha, smul_eq_mul, mul_one]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool]
      apply Finset.sum_congr rfl
      intro i hi
      exact add_comm _ _

end CurveComplex.Octagon.AttachingMap.GraphMV
