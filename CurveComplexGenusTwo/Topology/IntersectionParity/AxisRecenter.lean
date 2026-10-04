import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
namespace CurveComplex.LocalSurgery

/-- Vertical translation preserves the axis and its two sides. -/
def verticalRecenter (c : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (x.1, x.2 - c)
  invFun x := (x.1, x.2 + c)
  left_inv := by intro x; ext <;> simp
  right_inv := by intro x; ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add continuous_const)

/-- Recenter a straightening chart at an arbitrary point of the axis. -/
def recenterAxisChart {S : Type*} [TopologicalSpace S]
    (h : OpenPartialHomeomorph S (ℝ × ℝ)) (p : S) :
    OpenPartialHomeomorph S (ℝ × ℝ) :=
  h.trans (verticalRecenter (h p).2).toOpenPartialHomeomorph

end CurveComplex.LocalSurgery
