import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares

namespace CurveComplex
open Set Topology Schoenflies

/-- A continuous graph in an actual surface chart crosses its transverse
coordinate axis. The witness is an explicit global graph shear. -/
theorem source_continuous_graph_crossing
    {S : Type} [TopologicalSpace S]
    (a d : Curve S) (E : OpenPartialHomeomorph S Plane) (p : S)
    (hp : p ∈ E.source) (hp0 : E p 0 = 0)
    (g : ℝ → ℝ) (hg : Continuous g) (hp1 : E p 1 = g 0)
    (ha : ∀ x ∈ E.source, x ∈ a.image ↔ E x 0 = 0)
    (hd : ∀ x ∈ E.source, x ∈ d.image ↔ E x 1 = g (E x 0)) :
    CrossesAt a d p := by
  let L : Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let shear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toEquiv := {
      toFun := fun z => (z.1,z.2-g z.1)
      invFun := fun z => (z.1,z.2+g z.1)
      left_inv := by intro z; apply Prod.ext <;> simp
      right_inv := by intro z; apply Prod.ext <;> simp }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := L.trans shear
  let V : Set (ℝ × ℝ) := F '' E.target
  let e : E.source ≃ₜ V := E.toHomeomorphSourceTarget.trans (F.image E.target)
  refine ⟨E.source,V,hp,e,E.open_source,F.isOpenMap _ E.open_target,?_,?_⟩
  · change (E p 0,E p 1-g (E p 0)) = (0,0)
    rw [hp0,hp1]
    simp
  · intro x hx
    change (x ∈ a.image ↔ E x 0 = 0) ∧
      (x ∈ d.image ↔ E x 1-g (E x 0) = 0)
    exact ⟨ha x hx,(hd x hx).trans sub_eq_zero.symm⟩

end CurveComplex
#print axioms CurveComplex.source_continuous_graph_crossing
