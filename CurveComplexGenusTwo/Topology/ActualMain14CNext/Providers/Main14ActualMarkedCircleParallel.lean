import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualCircleSquareNormalization
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14FiniteMarkedRadialParallel
import CurveComplexGenusTwo.Topology.ChartLift

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 8000000

/-- Construct an actual marked ambient isotopy moving the original arbitrary
punctured circle to a disjoint parallel circle. Normalization, finite marked
clearance, compact support and global sphere extension are all constructed. -/
theorem actual_marked_punctured_circle_parallel_isotopy
    (M : HyperellipticModel E S) (c : PuncturedCircle M) :
    ∃ G : AmbientIsotopy S,
      (∀ t x, x ∈ M.cover.branch → G.map (t,x) = x) ∧
      Disjoint (G.finalMap '' c.image) c.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨p,hp,F,hFs,hFt,hcsrc,hcimage⟩ := M.actual_punctured_circle_square_normalization c
  let L : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  have hnormL (z : Plane) : ‖L z‖ = Plane.supNorm z := rfl
  let B : Finset (ℝ × ℝ) := (M.cover.branch.filter (· ∈ F.source)).image (fun x => L (F x))
  have hB : ∀ z ∈ B, ‖z‖ ≠ 1 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxbranch,hxsrc⟩ := Finset.mem_filter.mp hx
    intro hn
    have hmodel : F x ∈ modelCurve := by
      change Plane.supNorm (F x) = 1
      rw [← hnormL]; exact hn
    obtain ⟨y,hy,he⟩ := hcimage.symm ▸ hmodel
    have hyx : y = x := F.injOn (hcsrc hy) hxsrc he
    exact Set.disjoint_left.mp c.avoids_branch (hyx ▸ hy) hxbranch
  obtain ⟨ε,hε,hεb,H,hHmarks,hHnorm,hHfar⟩ := actual_finite_marked_radial_parallel B hB
  let P : AmbientIsotopy Plane := {
    map := ⟨fun z => L.symm (H.map (z.1,L z.2)),by fun_prop⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      exact ⟨(L.trans e).trans L.symm,fun x => congrArg L.symm (he (L x))⟩
    at_zero := by
      intro x
      change L.symm (H.map (⟨0,by norm_num⟩,L x)) = x
      rw [H.at_zero,L.symm_apply_apply] }
  have hPfar (t : Interval) (z : Plane) (hz : z ∉ Plane.closedSquare 0 2) : P.map (t,z) = z := by
    have hn : 2 ≤ ‖L z‖ := by
      rw [hnormL]
      have hh : ¬ Plane.supNorm z ≤ 2 := by simpa [Plane.closedSquare,Plane.supDist] using hz
      exact (not_le.mp hh).le
    change L.symm (H.map (t,L z)) = z
    rw [hHfar t _ hn,L.symm_apply_apply]
  obtain ⟨K,G,hcoord,hGU,hGfix⟩ := position_surface_chart_lift S F.source F.target F.open_source
    F.toHomeomorphSourceTarget (Plane.closedSquare 0 2) (isCompact_closedSquare 0 2)
    (by rw [hFt]; exact Set.subset_univ _) P hPfar
  have hPmarks (t : Interval) (x : S) (hx : x ∈ M.cover.branch) (hxsrc : x ∈ F.source) :
      P.map (t,F x) = F x := by
    have hm : L (F x) ∈ B := Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hxsrc⟩,rfl⟩
    change L.symm (H.map (t,L (F x))) = F x
    rw [hHmarks t _ hm,L.symm_apply_apply]
  refine ⟨G,?_,?_⟩
  · intro t x hx
    by_cases hxsrc : x ∈ F.source
    · let u : F.source := ⟨x,hxsrc⟩
      have hKu : K.map (t,u) = u := F.toHomeomorphSourceTarget.injective
        (Subtype.ext ((hcoord t u).trans (hPmarks t x hx hxsrc)))
      exact (hGU t u).trans (congrArg Subtype.val hKu)
    · exact hGfix t x hxsrc
  · apply Set.disjoint_left.mpr
    rintro y ⟨x,hxc,hxy⟩ hyc
    let u : F.source := ⟨x,hcsrc hxc⟩
    have hn (z : S) (hz : z ∈ c.image) : ‖L (F z)‖ = 1 := by
      rw [hnormL]
      exact (show F z ∈ modelCurve from hcimage ▸ Set.mem_image_of_mem F hz)
    have hEval : F (G.finalMap x) = P.finalMap (F x) := by
      calc
        F (G.finalMap x) = F (K.finalMap u).val := congrArg F (hGU ⟨1,by norm_num⟩ u)
        _ = P.finalMap (F x) := hcoord ⟨1,by norm_num⟩ u
    have hnormfinal : ‖L (F (G.finalMap x))‖ = 1+ε := by
      rw [hEval]
      change ‖L (L.symm (H.finalMap (L (F x))))‖ = 1+ε
      rw [L.apply_symm_apply]
      exact hHnorm _ (hn x hxc)
    rw [hxy,hn y hyc] at hnormfinal
    linarith
end CurveComplex.HyperellipticModel
