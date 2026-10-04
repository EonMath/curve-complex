import CurveComplexGenusTwo.Octagon.VertexPlaneRange
import CurveComplexGenusTwo.Octagon.VertexStar
import CurveComplexGenusTwo.Octagon.VertexFiberTheorem

namespace CurveComplex.Octagon
set_option backward.isDefEq.respectTransparency false

theorem vertex_euclideanLocalChartAt :
    EuclideanLocalChartAt (mk (vertexPoint 0)) := by
  let e := vertexClosedChart vertexModel_fiber_iff
  have open_image_val {X : Type} [TopologicalSpace X] (S : Set X)
      (A : Set S) (hA : IsOpen A)
      (hsub : (Subtype.val : S → X) '' A ⊆ interior S) :
      IsOpen ((Subtype.val : S → X) '' A) := by
    obtain ⟨O, hO, hOA⟩ :=
      (Topology.IsEmbedding.subtypeVal.isInducing.isOpen_iff).mp hA
    have heq : (Subtype.val : S → X) '' A = O ∩ interior S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨by rw [← hOA] at hy; exact hy, hsub ⟨y, hy, rfl⟩⟩
      · rintro ⟨hxO, hxS⟩
        refine ⟨⟨x, interior_subset hxS⟩, ?_, rfl⟩
        rw [← hOA]
        exact hxO
    rw [heq]
    exact hO.inter isOpen_interior
  have image_homeo {X : Type} [TopologicalSpace X] (S : Set X) (A : Set S) :
      Nonempty (A ≃ₜ ((Subtype.val : S → X) '' A)) := by
    have hi : Topology.IsEmbedding (fun a : A => (a.1 : X)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact ⟨hi.toHomeomorph.trans (Homeomorph.setCongr (by ext x; simp))⟩
  let A : Set (Set.range vertexModelSource) :=
    {x | (x : Surface) ∈ interior (Set.range vertexModelSource) ∧
      (e x : ℂ) ∈ Metric.ball 0 (1 / 4)}
  let B : Set (Set.range vertexModelPlane) := e '' A
  let W : Set Surface := Subtype.val '' A
  let U : Set ℂ := Subtype.val '' B
  have hA : IsOpen A :=
    (isOpen_interior.preimage continuous_subtype_val).inter
      (Metric.isOpen_ball.preimage (continuous_subtype_val.comp e.continuous))
  have hB : IsOpen B := e.isOpenMap _ hA
  have hW : IsOpen W := open_image_val _ A hA (by
    rintro x ⟨a, ha, rfl⟩
    exact ha.1)
  have hU : IsOpen U := open_image_val _ B hB (by
    rintro z ⟨b, ⟨a, ha, hab⟩, rfl⟩
    rw [← hab]
    have hball : Metric.ball (0 : ℂ) (1 / 4) ⊆ interior (Set.range vertexModelPlane) := by
      rw [vertexModelPlane_range]
      exact Metric.ball_subset_interior_closedBall
    exact hball ha.2)
  have hv : mk (vertexPoint 0) ∈ Set.range vertexModelSource :=
    interior_subset vertexModelSource_vertex_interior
  let q : Set.range vertexModelSource := ⟨mk (vertexPoint 0), hv⟩
  have heq : (e q : ℂ) = 0 := by
    change vertexModelPlane (Classical.choose q.property) = 0
    apply (vertexModel_vertex_iff_plane_zero _).mp
    exact Classical.choose_spec q.property
  have hqA : q ∈ A := by
    refine ⟨vertexModelSource_vertex_interior, ?_⟩
    rw [heq]
    exact Metric.mem_ball_self (by norm_num)
  obtain ⟨eW⟩ := image_homeo (Set.range vertexModelSource) A
  obtain ⟨eU⟩ := image_homeo (Set.range vertexModelPlane) B
  let c : W ≃ₜ U := eW.symm.trans ((e.image A).trans eU)
  let V : Set Euclidean2 := complexEuclidean2Homeomorph '' U
  refine ⟨W, V, hW, ⟨q, hqA, rfl⟩,
    complexEuclidean2Homeomorph.isOpenMap _ hU, ?_⟩
  exact ⟨c.trans (complexEuclidean2Homeomorph.image U)⟩

end CurveComplex.Octagon
