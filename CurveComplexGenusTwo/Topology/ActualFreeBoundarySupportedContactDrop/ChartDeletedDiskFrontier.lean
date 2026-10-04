import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.Plane

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

theorem chart_deleted_disk_complement_frontier
    {S : Type} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane) (p : Plane) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall p R ⊆ E.target) :
    frontier (E.symm '' Metric.ball p R)ᶜ = E.symm '' Metric.sphere p R := by
  let D : Set S := E.symm '' Metric.ball p R
  let K : Set S := E.symm '' Metric.closedBall p R
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (E.continuousOn_symm.mono htarget)
  have hKs : K ⊆ E.source := by
    rintro y ⟨z,hz,rfl⟩
    exact E.map_target (htarget hz)
  have hDK : D ⊆ K := Set.image_mono Metric.ball_subset_closedBall
  have hDs : D ⊆ E.source := hDK.trans hKs
  have hI : E.IsImage D (Metric.ball p R) := by
    intro y hy
    constructor
    · intro hz
      exact ⟨E y,hz,E.left_inv hy⟩
    · rintro ⟨z,hz,rfl⟩
      rwa [E.right_inv (htarget (Metric.ball_subset_closedBall hz))]
  have hfs : frontier D ⊆ E.source :=
    frontier_subset_closure.trans ((hK.isClosed.closure_subset_iff.mpr hDK).trans hKs)
  have hh := hI.frontier.symm_image_eq
  rw [frontier_ball p hR.ne',inter_eq_right.mpr
    (Metric.sphere_subset_closedBall.trans htarget),inter_eq_right.mpr hfs] at hh
  rw [frontier_compl]
  exact hh.symm
end CoherentEndpointMotion
