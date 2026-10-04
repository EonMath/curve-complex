import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

def DividingCurve (c : Curve E) : Prop :=
  ¬ IsConnected c.imageᶜ

end CurveComplex.Hyperbolic
