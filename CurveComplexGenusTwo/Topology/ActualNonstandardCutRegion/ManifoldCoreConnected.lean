import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingEssential

open Set Topology
open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

noncomputable section
set_option backward.isDefEq.respectTransparency false

local instance : MetricSpace (EuclideanHalfSpace 2) :=
  inferInstanceAs (MetricSpace {x : EuclideanSpace ℝ (Fin 2) // 0 ≤ x 0})

private theorem connected_dense_set_of_connected_local_pieces
    {K : Type} [TopologicalSpace K] [ConnectedSpace K]
    (D : Set K) (hD : Dense D)
    (hlocal : ∀ x : K, ∃ N : Set K,
      IsOpen N ∧ x ∈ N ∧ IsConnected (N ∩ D)) : IsConnected D := by
  choose N hNo hxN hNc using hlocal
  have hcover : (⋃ x, N x) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, hxN x⟩
  have hcoverc : IsPreconnected (⋃ x, N x) := by
    rw [hcover]
    exact isPreconnected_univ
  have hedge : ∀ i j, (N i ∩ N j).Nonempty →
      ((N i ∩ D) ∩ (N j ∩ D)).Nonempty := by
    intro i j hij
    obtain ⟨z, hzD, hzi, hzj⟩ := hD.exists_mem_open ((hNo i).inter (hNo j)) hij
    exact ⟨z, ⟨hzi, hzD⟩, hzj, hzD⟩
  have hgraph : ∀ i j,
      Relation.ReflTransGen (fun a b => ((N a ∩ D) ∩ (N b ∩ D)).Nonempty) i j := by
    intro i j
    have h := hcoverc.transGen_of_iUnion hNo i j ⟨i, hxN i⟩ ⟨j, hxN j⟩
    exact (Relation.TransGen.mono (fun a b hab => hedge a b hab) i j h).to_reflTransGen
  have hc := IsConnected.iUnion_of_reflTransGen hNc hgraph
  have heq : (⋃ x, N x ∩ D) = D := by
    rw [← Set.iUnion_inter, hcover, Set.univ_inter]
  rwa [heq] at hc

private theorem halfspace_positive_ball_preconnected
    (p : EuclideanHalfSpace 2) (r : ℝ) :
    IsPreconnected {y : EuclideanHalfSpace 2 |
      dist y p < r ∧ 0 < y.val 0} := by
  let P := EuclideanSpace ℝ (Fin 2)
  have himage : (fun y : EuclideanHalfSpace 2 => y.val) ''
      {y : EuclideanHalfSpace 2 | dist y p < r ∧ 0 < y.val 0} =
      Metric.ball p.val r ∩ {y : P | 0 < y 0} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · rintro ⟨hyball, hypositive⟩
      exact ⟨⟨y, hypositive.le⟩, ⟨hyball, hypositive⟩, rfl⟩
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  change IsPreconnected ((fun y : EuclideanHalfSpace 2 => y.val) ''
    {y : EuclideanHalfSpace 2 | dist y p < r ∧ 0 < y.val 0})
  rw [himage]
  have hpositive : Convex ℝ {y : P | 0 < y 0} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x 0 + b * y 0
    rcases eq_or_lt_of_le ha with rfl | hapos
    · have hb1 : b = 1 := by linarith
      simpa [hb1] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos hapos hx) (mul_nonneg hb hy.le)
  exact ((convex_ball p.val r).inter hpositive).isPreconnected

/-- The intrinsic interior of a connected half-space surface is connected.
Its dense-core premise is the one already supplied by the actual compact cut.
The proof uses connected positive half-balls in the literal charts. -/
theorem connected_intrinsic_interior_of_dense
    (K : Type) [TopologicalSpace K] [ConnectedSpace K]
    [ChartedSpace (EuclideanHalfSpace 2) K]
    (hdense : Dense (ModelWithCorners.interior (I := 𝓡∂ 2) K)) :
    IsConnected (ModelWithCorners.interior (I := 𝓡∂ 2) K) := by
  let D := ModelWithCorners.interior (I := 𝓡∂ 2) K
  apply connected_dense_set_of_connected_local_pieces D hdense
  intro x
  let e := chartAt (EuclideanHalfSpace 2) x
  have hxs : x ∈ e.source := mem_chart_source _ _
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxs)
  let B := Metric.ball (e x) r
  let N := e.symm '' B
  have hNo : IsOpen N := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  have hxN : x ∈ N := ⟨e x, Metric.mem_ball_self hr, e.left_inv hxs⟩
  have hpiece : e.symm '' {y : EuclideanHalfSpace 2 |
      dist y (e x) < r ∧ 0 < y.val 0} = N ∩ D := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyball, hypos⟩, rfl⟩
      have hytarget : y ∈ e.target := hball hyball
      refine ⟨⟨y, hyball, rfl⟩, ?_⟩
      apply (isInteriorPoint_iff_any_chart (𝓡∂ 2) (e.map_target hytarget)).mpr
      rw [e.right_inv hytarget, interior_range_modelWithCornersEuclideanHalfSpace]
      exact hypos
    · rintro ⟨⟨y, hyball, rfl⟩, hzD⟩
      have hytarget : y ∈ e.target := hball hyball
      refine ⟨y, ⟨hyball, ?_⟩, rfl⟩
      have hpos := (isInteriorPoint_iff_any_chart (𝓡∂ 2)
        (e.map_target hytarget)).mp hzD
      rw [e.right_inv hytarget, interior_range_modelWithCornersEuclideanHalfSpace] at hpos
      exact hpos
  have hpre : IsPreconnected (N ∩ D) := by
    rw [← hpiece]
    exact (halfspace_positive_ball_preconnected (e x) r).image e.symm
      (e.symm.continuousOn.mono (fun y hy => hball hy.1))
  obtain ⟨z, hzD, hzN⟩ := hdense.exists_mem_open hNo ⟨x, hxN⟩
  exact ⟨N, hNo, hxN, ⟨⟨z, hzN, hzD⟩, hpre⟩⟩

end
end CurveComplexGenusTwo.SourceTopology.ThreeArcCut

#print axioms CurveComplexGenusTwo.SourceTopology.ThreeArcCut.connected_intrinsic_interior_of_dense
