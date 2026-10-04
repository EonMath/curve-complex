import CurveComplexGenusTwo.Octagon.GraphMV.OverlapComponents
import CurveComplexGenusTwo.Octagon.GraphMV.DiscreteHZero

noncomputable section
open CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon.AttachingMap.GraphMV

set_option backward.isDefEq.respectTransparency false

private abbrev Overlap := vertexStar ∩ edgeMiddles
private abbrev ShortInterval := Set.Ioo (1/4 : ℝ) (3/8 : ℝ)

def overlapPoint (p : Fin 4 × Bool) : Overlap :=
  overlapIntervalChart.symm (p.1, p.2, ⟨5/16, by constructor <;> norm_num⟩)

def overlapHZeroCoordinates :
    H Overlap 0 ≃ₗ[ℤ] (Fin 4 × Bool → ℤ) :=
  ((homotopyHomologyIso overlapHomotopyFinBool 0) ≪≫
    finiteDiscreteH0Iso (Fin 4 × Bool)).toLinearEquiv

private theorem overlapHomotopyFinBool_point (p : Fin 4 × Bool) :
    overlapHomotopyFinBool.toFun (overlapPoint p) = p := by
  simp [overlapHomotopyFinBool, overlapPoint]
  change (p.1, p.2) = p
  exact Prod.mk.eta

private theorem overlapPointClass_map (p : Fin 4 × Bool) :
    pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
        (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) ≫
      (homotopyHomologyIso overlapHomotopyFinBool 0).hom =
    pointClass (TopCat.toSSet.obj (TopCat.of (Fin 4 × Bool)))
      (TopCat.toSSetObj₀Equiv.symm p) := by
  change pointClass _ _ ≫
    HomologicalComplex.homologyMap (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom overlapHomotopyFinBool.toFun)) RZ) 0 = _
  rw [pointClass_map]
  congr 1
  apply TopCat.toSSetObj₀Equiv.injective
  exact overlapHomotopyFinBool_point p

theorem overlapHZeroCoordinates_point (p : Fin 4 × Bool) :
    overlapHZeroCoordinates
      (pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
        (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) (1 : ℤ)) =
      Pi.single p (1 : ℤ) := by
  change (pointClass (TopCat.toSSet.obj (TopCat.of Overlap))
    (TopCat.toSSetObj₀Equiv.symm (overlapPoint p)) ≫
      ((homotopyHomologyIso overlapHomotopyFinBool 0).hom ≫
        (finiteDiscreteH0Iso (Fin 4 × Bool)).hom)) (1 : ℤ) = _
  rw [← Category.assoc, overlapPointClass_map]
  exact finiteDiscreteH0Iso_point (Fin 4 × Bool) p

#print axioms overlapHZeroCoordinates_point

end CurveComplex.Octagon.AttachingMap.GraphMV
