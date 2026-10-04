import CurveComplexGenusTwo.Octagon.GraphMV.DiscreteHZero
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers

noncomputable section
open CategoryTheory CategoryTheory.Limits CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.CapBandGeometry
set_option backward.isDefEq.respectTransparency false

def finiteHomotopyHZeroCoordinates {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] [Fintype D] [DiscreteTopology D]
    (e : ContinuousMap.HomotopyEquiv X D) : H X 0 ≃ₗ[ℤ] (D → ℤ) :=
  ((homotopyHomologyIso e 0) ≪≫
    CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso D).toLinearEquiv

theorem finiteHomotopyHZeroCoordinates_point {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] [Fintype D] [DiscreteTopology D] [DecidableEq D]
    (e : ContinuousMap.HomotopyEquiv X D) (p : X) :
    finiteHomotopyHZeroCoordinates e
      (pointClass (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm p) (1 : ℤ)) =
      Pi.single (e.toFun p) (1 : ℤ) := by
  have hmap : pointClass (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSetObj₀Equiv.symm p) ≫ (homotopyHomologyIso e 0).hom =
      pointClass (TopCat.toSSet.obj (TopCat.of D))
        (TopCat.toSSetObj₀Equiv.symm (e.toFun p)) := by
    change pointClass _ _ ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom e.toFun)) RZ) 0 = _
    rw [pointClass_map]
    congr 1
  change (pointClass (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSetObj₀Equiv.symm p) ≫
      ((homotopyHomologyIso e 0).hom ≫
        (CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso D).hom)) (1 : ℤ) = _
  rw [← Category.assoc, hmap]
  exact CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso_point D (e.toFun p)

#print axioms finiteHomotopyHZeroCoordinates_point
end CurveComplex.CapBandGeometry
