import CurveComplexGenusTwo.Octagon.VertexFibers
import CurveComplexGenusTwo.Octagon.PlaneFibers

namespace CurveComplex.Octagon

theorem vertexModel_fiber_iff (p q : vertexModel) :
    vertexModelSource p = vertexModelSource q ↔
      vertexModelPlane p = vertexModelPlane q := by
  exact ⟨vertexModel_source_implies_plane p q, vertexModel_plane_implies_source p q⟩

end CurveComplex.Octagon
