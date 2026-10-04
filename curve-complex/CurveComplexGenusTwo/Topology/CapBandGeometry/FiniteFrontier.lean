import CurveComplexGenusTwo.Topology.CapBandGeometry.LocalCapSeam
import Mathlib.Analysis.Normed.Module.Connected

open Set Topology
namespace CurveComplex.CapBandGeometry

theorem plane_punctured_ball_connected (c : CapPlane) (r : ℝ) (hr : 0 < r) :
    IsConnected (Metric.ball c r \ {c}) := by
  have hrank : 1 < Module.rank ℝ CapPlane := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hsphere := isPathConnected_sphere hrank (0 : CapPlane) (by norm_num : (0 : ℝ) ≤ 1)
  have hradii := (convex_Ioo (0 : ℝ) r).isPathConnected ⟨r/2, by constructor <;> linarith⟩
  let F : CapPlane × ℝ → CapPlane := fun p => c + p.2 • p.1
  have hF : Continuous F := continuous_const.add (continuous_snd.smul continuous_fst)
  have heq : F '' (Metric.sphere (0 : CapPlane) 1 ×ˢ Ioo (0 : ℝ) r) =
      Metric.ball c r \ {c} := by
    ext x
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa [dist_zero_right] using hu
      have hnorm : ‖t • u‖ = t := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hu', mul_one]
      refine ⟨?_, ?_⟩
      · change dist (c + t • u) c < r
        simpa [dist_eq_norm, hnorm] using ht.2
      · intro he
        have he' : c + t • u = c := he
        have hz : t • u = 0 := add_left_cancel (he'.trans (add_zero c).symm)
        rw [hz, norm_zero] at hnorm
        linarith [ht.1]
    · rintro ⟨hx, hxc⟩
      have hpos : 0 < ‖x-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
      have hhi : ‖x-c‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hx
      refine ⟨(‖x-c‖⁻¹ • (x-c), ‖x-c‖), ⟨?_, ⟨hpos, hhi⟩⟩, ?_⟩
      · change dist (‖x-c‖⁻¹ • (x-c)) 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
      · change c + ‖x-c‖ • ‖x-c‖⁻¹ • (x-c) = x
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
        abel
  rw [← heq]
  exact ((hsphere.prod hradii).image hF).isConnected

/-- In a surface, a regular closed region cannot have a finite nonempty frontier.
This removes finite corners AFTER actual local filling along the open edges. -/
theorem regular_closed_finite_frontier_empty
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    (A : Set S) (hA : IsClosed A) (hreg : closure (interior A) = A)
    (hfin : (frontier A).Finite) : frontier A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let e := chartAt CapPlane x
  let C := frontier A \ {x}
  have hCclosed : IsClosed C := (hfin.subset Set.sdiff_subset).isClosed
  let W : Set S := e.source ∩ Cᶜ
  have hW : IsOpen W := e.open_source.inter hCclosed.isOpen_compl
  have hxW : x ∈ W := ⟨mem_chart_source _ _, by simp [C]⟩
  let Z : Set CapPlane := e.target ∩ e.symm ⁻¹' W
  have hZ : IsOpen Z := e.isOpen_inter_preimage_symm hW
  have hexZ : e x ∈ Z := ⟨e.map_source hxW.1, by
    change e.symm (e x) ∈ W
    rwa [e.left_inv hxW.1]⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hZ (e x) hexZ
  let V : Set S := e.symm '' Metric.ball (e x) r
  have hV : IsOpen V := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (fun y hy => (hball hy).1)
  have hxV : x ∈ V := ⟨e x, Metric.mem_ball_self hr, e.left_inv hxW.1⟩
  have hVW : V ⊆ W := by
    rintro y ⟨z, hz, rfl⟩
    exact (hball hz).2
  have hVp : IsPreconnected (V \ {x}) := by
    have heq : e.symm '' (Metric.ball (e x) r \ {e x}) = V \ {x} := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ?_⟩
        intro hey
        apply hzx
        exact e.symm.injOn (hball hz).1 hexZ.1 (hey.trans (e.left_inv hxW.1).symm)
      · rintro ⟨⟨z, hz, rfl⟩, hzx⟩
        refine ⟨z, ⟨hz, ?_⟩, rfl⟩
        intro he
        exact hzx (he ▸ e.left_inv hxW.1)
    rw [← heq]
    exact (plane_punctured_ball_connected (e x) r hr).2.image e.symm
      (e.symm.continuousOn.mono (fun z hz => (hball hz.1).1))
  have havoid : Disjoint (V \ {x}) (frontier A) := by
    apply Set.disjoint_left.mpr
    intro y hy hyfront
    exact (hVW hy.1).2 ⟨hyfront, hy.2⟩
  have hxclosure : x ∈ closure (interior A) := hreg.symm ▸ hA.frontier_subset hx
  obtain ⟨y, hyV, hyA⟩ := mem_closure_iff.mp hxclosure V hV hxV
  have hyne : y ≠ x := by
    intro hyx
    exact hx.2 (hyx ▸ hyA)
  have hxcompl : x ∈ closure Aᶜ := by
    rw [← frontier_compl] at hx
    exact frontier_subset_closure hx
  obtain ⟨z, hzV, hzA⟩ := mem_closure_iff.mp hxcompl V hV hxV
  have hzne : z ≠ x := by
    intro hzx
    exact hzA (hzx ▸ hA.frontier_subset hx)
  rcases connected_cap_side A (V \ {x}) hVp havoid with hinside | houtside
  · exact hzA (interior_subset (hinside ⟨hzV, hzne⟩))
  · exact (interior_subset (houtside ⟨hyV, hyne⟩)) (interior_subset hyA)

#print axioms regular_closed_finite_frontier_empty
end CurveComplex.CapBandGeometry
