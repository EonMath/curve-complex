import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteEventPositionTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEndpointBigonRelativeAlignment

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Minimum zero intrinsic intersection gives literal clearance from the whole
stationary anchor, including the exclusion of its marked endpoint points. -/
theorem actual_zero_intrinsic_position_anchor_clearance
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (v : {v // v ∈ F}) (hv : intersectionNumber M anchor v.val = 0) :
    Disjoint (arcInterior M (P.rep v)) anchor.val.image := by
  have hc : crossings M anchor (P.rep v) = ∅ := by
    apply (Set.ncard_eq_zero (P.finite v)).mp
    rw [actual_position_count_eq_intrinsic M anchor F P v, hv]
  apply Set.disjoint_left.mpr
  intro z hz hza
  have hzC : z ∈ crossings M anchor (P.rep v) := ⟨⟨hza,hz.2⟩,hz⟩
  rw [hc] at hzC
  exact hzC

/-- The actual endpoint-sensitive bigon producer reaches the prescribed target
representative, simultaneously transports the entire source family, and keeps
its minimum-position certificates. The input is a genuine geometric disk chart,
not an ambient move or a target-reaching script. -/
theorem actual_prescribed_zero_bigon_position_transport
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (P Q : FinitePosition M anchor F) (v : {v // v ∈ F})
    (hv : intersectionNumber M anchor v.val = 0)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B = modelCurve)
    (haImage : (P.rep v).val.image = f '' A)
    (hbImage : (Q.rep v).val.image = f '' B)
    (hp : f p ∈ M.cover.branch) (hq : f q ∈ M.cover.branch)
    (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z = p ∨ z = q)
    (hinside : ∀ z ∈ Plane.openSquare 0 1,
      f z ∉ M.cover.branch ∧ f z ∉ anchor.val.image) :
    ∃ G : AmbientIsotopy S,
      ∃ hm : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z,
      ∃ ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image,
        Nonempty (MinimumPositionSystemFamily M anchor F P (timePosition M anchor F P G hm ha 1)) ∧
        ((timePosition M anchor F P G hm ha 1).rep v).val.image = (Q.rep v).val.image ∧
        (∀ t z, z ∈ anchor.val.image → G.map (t,z) = z) := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨G,hm,hfix,hend⟩ := actual_endpoint_bigon_relative_alignment M
    (P.rep v) (Q.rep v) anchor.val.image (isCompact_range anchor.val.continuous).isClosed
    (actual_zero_intrinsic_position_anchor_clearance M anchor F P v hv)
    (actual_zero_intrinsic_position_anchor_clearance M anchor F Q v hv)
    f hf A B p q hA hB hwhole haImage hbImage hp hq hboundary hinside
  have ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image := by
    intro t
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [hfix t x hx] using hx
    · intro hz
      exact ⟨z,hz,hfix t z hz⟩
  refine ⟨G,hm,ha,⟨timePositionSystem M anchor F hF P G hm ha⟩,?_,hfix⟩
  exact (timeTransport_image M G hm 1 (P.rep v)).trans hend

end
end CurveComplex.HyperellipticModel.ArcSurgery
