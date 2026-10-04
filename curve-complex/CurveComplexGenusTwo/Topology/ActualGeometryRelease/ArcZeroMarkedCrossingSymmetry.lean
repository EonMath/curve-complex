import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroLocalizedMarkedCrossingRectangle

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

def actualMarkedCrossingSquareSwap :
    {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} ≃ₜ
      {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1} := {
  toEquiv := {
    toFun := fun q => ⟨(q.val.2,q.val.1),q.property.2,q.property.1⟩
    invFun := fun q => ⟨(q.val.2,q.val.1),q.property.2,q.property.1⟩
    left_inv := by intro q; apply Subtype.ext; rfl
    right_inv := by intro q; apply Subtype.ext; rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop }

/-- The actual marked crossing disk is symmetric by a produced square
coordinate exchange. This does not change the ambient arcs or their marks. -/
theorem actual_marked_crossesInDisk_symm
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) (p : S)
    (hc : ArcSurgery.CrossesInDisk M a b p) : ArcSurgery.CrossesInDisk M b a p := by
  obtain ⟨U,hU,hp,hm,e,hzero,ha,hb⟩ := hc
  let e' := e.trans actualMarkedCrossingSquareSwap
  refine ⟨U,hU,hp,hm,e',?_,?_,?_⟩
  · change ((e ⟨p,hp⟩).val.2,(e ⟨p,hp⟩).val.1) = (0,0)
    rw [hzero]
  · intro x
    exact hb x
  · intro x
    exact ha x

#print axioms actual_marked_crossesInDisk_symm
end CurveComplex.HyperellipticModel
