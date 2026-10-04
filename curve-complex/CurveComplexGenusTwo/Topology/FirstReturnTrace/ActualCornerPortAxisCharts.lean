import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnSmallPorts
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual plane homeomorphisms normalize a first/closing corner port to zero
while preserving the original normal coordinate. These are genuine charts for
strictly internal finite framing centers. -/
theorem source_corner_port_axis_charts
    {S : Type} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S Plane) (p q : S)
    (hp : p ∈ E.source) (hq : q ∈ E.source)
    (hpaxis : E p 0=0) (hqaxis : E q 1=0) :
    ∃ F G : OpenPartialHomeomorph S Plane,
      F.source=E.source ∧ G.source=E.source ∧ p ∈ F.source ∧ q ∈ G.source ∧ F p=0 ∧ G q=0 ∧
      (∀ x, F x=Plane.mk (E x 1-E p 1) (E x 0)) ∧
      (∀ x, G x=Plane.mk (E x 0-E q 0) (E x 1)) := by
  let J : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun z => Plane.mk (z 1) (z 0)
      invFun := fun z => Plane.mk (z 1) (z 0)
      left_inv := by intro z; ext j; fin_cases j <;> rfl
      right_inv := by intro z; ext j; fin_cases j <;> rfl }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let L := J.trans (Homeomorph.addRight (-(J (E p))))
  let F := E.trans L.toOpenPartialHomeomorph
  let M := Homeomorph.addRight (-(E q))
  let G := E.trans M.toOpenPartialHomeomorph
  have hF (x : S) : F x=Plane.mk (E x 1-E p 1) (E x 0) := by
    change Plane.mk (E x 1) (E x 0) + -Plane.mk (E p 1) (E p 0)=_
    ext j
    fin_cases j
    · change E x 1+ -E p 1=E x 1-E p 1; ring
    · change E x 0+ -E p 0=E x 0; rw [hpaxis]; simp
  have hG (x : S) : G x=Plane.mk (E x 0-E q 0) (E x 1) := by
    change E x + -E q=_
    ext j
    fin_cases j
    · change E x 0+ -E q 0=E x 0-E q 0; ring
    · change E x 1+ -E q 1=E x 1; rw [hqaxis]; simp
  have hFs : F.source=E.source := by simp [F]
  have hGs : G.source=E.source := by simp [G]
  refine ⟨F,G,hFs,hGs,hFs.symm ▸ hp,hGs.symm ▸ hq,?_,?_,hF,hG⟩
  · rw [hF,hpaxis]
    ext j
    fin_cases j <;> simp
  · rw [hG,hqaxis]
    ext j
    fin_cases j <;> simp
end CurveComplex
#print axioms CurveComplex.source_corner_port_axis_charts
