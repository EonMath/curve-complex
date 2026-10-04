import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualCylinderThetaExactLoopTransportProof
import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualSquareThetaCover
open Set Topology ContinuousMap CategoryTheory
namespace CurveComplex.Hyperbolic
theorem actual_fundamental_mapOfEq_bijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (E : X ≃ₕ Y) (b : X) (c : Y) (hb : E b=c) :
    Function.Bijective (FundamentalGroup.mapOfEq E.toFun hb) := by
  subst c
  have heq : FundamentalGroup.mapOfEq E.toFun (rfl : E b=E b)=FundamentalGroup.map E.toFun b := by
    apply MonoidHom.ext
    intro v
    rw [FundamentalGroup.mapOfEq_apply]
    simp [FundamentalGroup.map_apply]
  rw [heq]
  let F := FundamentalGroupoidFunctor.equivOfHomotopyEquiv E
  exact ⟨F.functor.map_injective,F.functor.map_surjective⟩
end CurveComplex.Hyperbolic
