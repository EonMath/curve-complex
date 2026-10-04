import CurveComplexGenusTwo.TwoCellDiscPastingNamed
import CurveComplexGenusTwo.ClosedBoundaryLiftNoFullCircleNamed
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S X : Type} [TopologicalSpace E] [TopologicalSpace S] [TopologicalSpace X]
 [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
/-- Two one-mark cell cuts force the full preimage of the outer boundary to have no closed Curve lift.
This is the exact branch-free 2-mark obstruction once the geometric cut package supplies the arguments. -/
theorem two_marked_side_no_full_preimage
 (a : PuncturedCircle M) (K : Set X) (f : C(K,S)) (hf : IsEmbedding f)
 (u v : K) (P χ : Path u v) (Q : Path v u)
 (F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
 (hF : ∀ i, IsEmbedding (F i)) (m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1)
 (hm : ∀ i, ‖(m i).val‖<1)
 (honly : ∀ i z, F i z ∈ M.cover.branch ↔ z=m i)
 (hcell0 : Set.range (fun t => f ((P.trans χ.symm) t))=F 0 '' {z | ‖z.val‖=1})
 (hcell1 : Set.range (fun t => f ((χ.trans Q) t))=F 1 '' {z | ‖z.val‖=1})
 (hcoll0 : ∀ s t, (P.trans χ.symm) s=(P.trans χ.symm) t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
 (hcoll1 : ∀ s t, (χ.trans Q) s=(χ.trans Q) t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
 (hcollOuter : ∀ s t, f ((P.trans Q) s)=f ((P.trans Q) t) → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
 (hOuterRange : Set.range (fun t => f ((P.trans Q) t)) = a.image)
 (c : Curve E) (hc : c.image=M.cover.projection ⁻¹' a.image)
 (γ : C(Interval,E))
 (hγπ : ∀ t, M.cover.projection (γ t)=f ((P.trans Q) t)) : False := by
  let β : C(Interval,S) :=
    ⟨fun t => f ((P.trans Q) t), f.continuous.comp (P.trans Q).continuous⟩
  have hβrange : Set.range β = a.image := by simpa [β] using hOuterRange
  have hβcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    intro s t h
    exact hcollOuter s t h
  have hβends : β 0 = β 1 := by
    change f ((P.trans Q) 0) = f ((P.trans Q) 1)
    rw [(P.trans Q).source, (P.trans Q).target]
  have hclose := two_cell_disc_pasting_closed_lift M K f hf u v P χ Q F hF m hm honly
    hcell0 hcell1 hcoll0 hcoll1 γ hγπ
  exact closed_boundary_lift_no_full_circle M a β hβcoll hβrange γ hγπ hclose.symm c hc
end CurveComplex.HyperellipticModel
