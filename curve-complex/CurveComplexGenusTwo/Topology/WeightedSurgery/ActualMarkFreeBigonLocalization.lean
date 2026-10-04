import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEndpointBigonRelativeAlignment
import CurveComplexGenusTwo.Topology.RestrictedLink.OpenEmbeddingFaceHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders

noncomputable section
open Set Topology Schoenflies CurveComplex

namespace CurveComplex

/-- A Jordan curve contained in the closed repair square has its bounded
side in the OPEN repair square, even if it touches the old boundary. -/
theorem actual_jordan_inside_closed_square {C : Set Plane}
    (hC : IsJordanCurve C) (hsub : C ⊆ Plane.closedSquare 0 1) :
    inside C ⊆ Plane.openSquare 0 1 := by
  have hs := jordan_curve_theorem hC
  have hm := jordan_curve_theorem isJordanCurve_modelCurve
  have havoid : outside modelCurve ⊆ Cᶜ := by
    intro z hz hzC
    have hzQ := hsub hzC
    rw [← modelCurve_union_inside] at hzQ
    rcases hzQ with hboundary | hinterior
    · exact hz.1 hboundary
    · exact Set.disjoint_left.mp disjoint_inside_outside hinterior hz
  have hout : outside modelCurve ⊆ outside C := by
    intro z hz
    refine ⟨havoid hz, fun hbdd => hm.not_isBounded_outside (hbdd.subset ?_)⟩
    exact hm.isConnected_outside.isPreconnected.subset_connectedComponentIn hz havoid
  have hbound : modelCurve ⊆ closure (outside C) :=
    ((IsRegionOf.outside modelCurve).subset_closure hm).trans (closure_mono hout)
  intro z hz
  rw [← inside_modelCurve]
  by_contra hn
  by_cases hzb : z ∈ modelCurve
  · have hcl := hbound hzb
    rw [(IsRegionOf.outside C).closure_eq hs] at hcl
    rcases hcl with ho | hc
    · exact Set.disjoint_left.mp disjoint_inside_outside hz ho
    · exact hz.1 hc
  · have ho : z ∈ outside modelCurve := by
      have hu : z ∈ inside modelCurve ∪ outside modelCurve := inside_union_outside modelCurve ▸ hzb
      exact hu.resolve_left hn
    exact Set.disjoint_left.mp disjoint_inside_outside hz (hout ho)

namespace HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual punctured trace is connected and dense in the entire trace,
including coincident endpoints of a loop. -/
theorem actual_bigon_arc_interior_connected_dense
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M) :
    IsConnected (arcInterior M a) ∧ a.val.image ⊆ closure (arcInterior M a) := by
  have hi : a.val.map '' Set.Ioo (0 : Interval) 1 = arcInterior M a := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      intro hb
      rcases a.val.marked_only_at_ends t hb with h | h
      · simpa [h] using ht.1
      · simpa [h] using ht.2
    · rintro ⟨⟨t, rfl⟩, hn⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h
        exact hn ((Subtype.ext h : t = (0 : Interval)) ▸ a.val.start_marked)
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h
        exact hn ((Subtype.ext h : t = (1 : Interval)) ▸ a.val.end_marked)
      refine ⟨t, ?_, rfl⟩
      change (0 : ℝ) < t.val ∧ t.val < 1
      exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
  constructor
  · rw [← hi]
    have hc : IsConnected (Set.Ioo (0 : Interval) 1) :=
      ⟨⟨⟨(1:ℝ)/2, by constructor <;> norm_num⟩, by
          constructor
          · change (0 : ℝ) < 1/2; norm_num
          · change (1 : ℝ)/2 < 1; norm_num⟩, isPreconnected_Ioo⟩
    exact hc.image a.val.map a.val.continuous.continuousOn
  · rintro y ⟨t, ht⟩
    have htcl : t ∈ closure (Set.Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      exact ⟨t.property.1, t.property.2⟩
    have hm := image_closure_subset_closure_image a.val.continuous ⟨t, htcl, rfl⟩
    rw [hi] at hm
    exact ht ▸ hm

/-- Intrusion into an actual bigon traps the entire protected arc interior
and the entire closed trace. Only actual interior-disjointness is used. -/
theorem actual_endpoint_bigon_intruding_arc_localization
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (hca : Disjoint (arcInterior M c) (arcInterior M a))
    (hcb : Disjoint (arcInterior M c) (arcInterior M b))
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (hboundary : a.val.image ∪ b.val.image = f '' modelCurve)
    (hentry : (arcInterior M c ∩ f '' Plane.openSquare 0 1).Nonempty) :
    arcInterior M c ⊆ f '' Plane.openSquare 0 1 ∧
    c.val.image ⊆ f '' Plane.closedSquare 0 1 := by
  letI : T2Space S := M.sphere.symm.t2Space
  have hm := jordan_curve_theorem isJordanCurve_modelCurve
  have hk : IsCompact (closure (inside modelCurve)) := by
    rw [(IsRegionOf.inside modelCurve).closure_eq hm, Set.union_comm, modelCurve_union_inside]
    exact isCompact_closedSquare 0 1
  have hU := open_embedding_bounded_face_transport f hf modelCurve (inside modelCurve)
    (jordan_inside_complement_component isJordanCurve_modelCurve) hm.isOpen_inside hk
    (by rw [hm.frontier_inside])
  rw [inside_modelCurve, ← hboundary] at hU
  have havoid : arcInterior M c ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro z hz hzAB
    rcases hzAB with ha | hb
    · exact Set.disjoint_left.mp hca hz ⟨ha, hz.2⟩
    · exact Set.disjoint_left.mp hcb hz ⟨hb, hz.2⟩
  obtain ⟨hc, hdense⟩ := actual_bigon_arc_interior_connected_dense M c
  obtain ⟨z, hzc, hzU⟩ := hentry
  have heq : f '' Plane.openSquare 0 1 =
      connectedComponentIn (a.val.image ∪ b.val.image)ᶜ z := by
    exact (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (havoid hzc))
      (hU.2.1.isPreconnected.subset_connectedComponentIn hzU hU.2.2.1)
      (connectedComponentIn_subset _ _)).symm
  have hi : arcInterior M c ⊆ f '' Plane.openSquare 0 1 := by
    rw [heq]
    exact hc.isPreconnected.subset_connectedComponentIn hzc havoid
  refine ⟨hi, (hdense.trans (closure_mono hi)).trans ?_⟩
  apply closure_minimal
  · apply Set.image_mono
    intro z hz
    exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hz).le
  · exact ((isCompact_closedSquare 0 1).image hf.continuous).isClosed

#print axioms actual_bigon_arc_interior_connected_dense
#print axioms actual_endpoint_bigon_intruding_arc_localization
end HyperellipticModel
#print axioms actual_jordan_inside_closed_square
end CurveComplex
