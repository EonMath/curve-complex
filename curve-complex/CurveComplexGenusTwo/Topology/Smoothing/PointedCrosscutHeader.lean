import CurveComplexGenusTwo.Topology.Smoothing.SeedMarkedArcDependency
import CurveComplexGenusTwo.Topology.PrescribedCrosscut

open Set
namespace CurveComplex.SeedProbeHeaders
open Schoenflies

theorem pointed_relative_crosscut_replacement {A B : Set Plane} {a b p : Plane}
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (hpA : p ∈ A \ {a,b}) (hpB : p ∈ B \ {a,b})
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a,b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a,b} ⊆ Plane.openSquare 0 1) :
    ∃ F : Plane ≃ₜ Plane, F p = p ∧ F '' A = B ∧
      ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
  obtain ⟨e⟩ := exists_arcHomeo hA hB
  have hpE : e.toFun p ∈ B \ {a,b} := by
    refine ⟨e.mapsTo hpA.1, ?_⟩
    intro hm
    have hcases : e.toFun p = a ∨ e.toFun p = b := by simpa using hm
    rcases hcases with he | he
    · have hpa : p = a := e.injOn hpA.1 hA.left_mem (he.trans e.map_left.symm)
      exact hpA.2 (by simp [hpa])
    · have hpb : p = b := e.injOn hpA.1 hA.right_mem (he.trans e.map_right.symm)
      exact hpA.2 (by simp [hpb])
  obtain ⟨g, hgp⟩ := exists_marked_arcHomeo hB hpE hpB
  let h : ArcHomeo A B a b a b := {
    toFun := g.toFun ∘ e.toFun
    invFun := e.invFun ∘ g.invFun
    continuousOn_toFun := g.continuousOn_toFun.comp e.continuousOn_toFun e.mapsTo
    continuousOn_invFun := e.continuousOn_invFun.comp g.continuousOn_invFun g.mapsTo_invFun
    leftInvOn := by
      intro x hx
      change e.invFun (g.invFun (g.toFun (e.toFun x))) = x
      rw [g.leftInvOn (e.mapsTo hx), e.leftInvOn hx]
    rightInvOn := by
      intro x hx
      change g.toFun (e.toFun (e.invFun (g.invFun x))) = x
      rw [e.rightInvOn (g.mapsTo_invFun hx), g.rightInvOn hx]
    image_eq := by rw [image_comp, e.image_eq, g.image_eq]
    map_left := by change g.toFun (e.toFun a) = a; rw [e.map_left,g.map_left]
    map_right := by change g.toFun (e.toFun b) = b; rw [e.map_right,g.map_right] }
  obtain ⟨F, hF, hFB, hfix⟩ :=
    prescribed_relative_crosscut_replacement A B a b hA hB ha hb hAi hBi h
  refine ⟨F, ?_, hFB, hfix⟩
  exact (hF p hpA.1).trans hgp

end CurveComplex.SeedProbeHeaders

#print axioms CurveComplex.SeedProbeHeaders.pointed_relative_crosscut_replacement
