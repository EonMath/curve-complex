import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualPrescribedBigonPositionTransport

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
noncomputable local instance (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) :=
  instDecidableEqEssentialArcClass_arcSurgeryProducers M

/-- Source simplex membership supplies disjointness of the actual entire
minimum-position representative family. -/
theorem actual_position_family_disjoint
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (P : FinitePosition M anchor F) :
    ∀ v w, v ≠ w → Disjoint (arcInterior M (P.rep v)) (arcInterior M (P.rep w)) := by
  classical
  let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  intro v w hvw
  apply P.simplex_disjoint v w hvw
  apply arcSimplex_down M _ hF
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with hz | hz
  · exact hz ▸ v.property
  · exact hz ▸ w.property

/-- The prescribed final arc is clear of the ORIGINAL already aligned graph;
only equality of images is required, not parametrization equality. -/
theorem actual_target_clearance_from_aligned_images
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (P Q : FinitePosition M anchor F) (v : {v // v ∈ F})
    (haligned : ∀ w, w ≠ v → (P.rep w).val.image = (Q.rep w).val.image) :
    Disjoint (arcInterior M (Q.rep v)) (actualObjectTrace M P.rep (F.erase v.val)) := by
  classical
  let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  apply disjoint_left.mpr
  intro z hz hzGraph
  obtain ⟨w,hw⟩ := mem_iUnion.mp hzGraph
  obtain ⟨hwF,hzw⟩ := mem_iUnion.mp hw
  have hwv : w ≠ v := by
    intro he
    exact (Finset.mem_erase.mp hwF).1 (congrArg Subtype.val he)
  rw [haligned w hwv] at hzw
  exact disjoint_left.mp (actual_position_family_disjoint M anchor F hF Q v w hwv.symm)
    hz ⟨hzw,hz.2⟩

/-- An actual endpoint bigon closes the last mismatch to a PRESCRIBED whole
family Q, while fixing the anchor and every already aligned image throughout.
The ambient isotopy is PRODUCED by the disk crosscut construction. -/
theorem actual_prescribed_zero_bigon_final_alignment
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (P Q : FinitePosition M anchor F) (v : {v // v ∈ F})
    (hv : intersectionNumber M anchor v.val = 0)
    (haligned : ∀ w, w ≠ v → (P.rep w).val.image = (Q.rep w).val.image)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B = modelCurve)
    (haImage : (P.rep v).val.image = f '' A)
    (hbImage : (Q.rep v).val.image = f '' B)
    (hp : f p ∈ M.cover.branch) (hq : f q ∈ M.cover.branch)
    (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z = p ∨ z = q)
    (hinside : ∀ z ∈ Plane.openSquare 0 1,
        f z ∉ M.cover.branch ∧ f z ∉ anchor.val.image ∪ actualObjectTrace M P.rep (F.erase v.val)) :
    ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t z, z ∈ anchor.val.image → G.map (t,z) = z) ∧
      (∀ w, w ≠ v → ∀ t z, z ∈ (P.rep w).val.image → G.map (t,z) = z) ∧
      (∀ w, G.finalMap '' (P.rep w).val.image = (Q.rep w).val.image) ∧
      Nonempty (MinimumPositionSystemFamily M anchor F P Q) := by
  classical
  let : DecidableEq (EssentialArcClass M) := instDecidableEqEssentialArcClass_arcSurgeryProducers M
  let : T2Space S := M.sphere.symm.t2Space
  let J := F.erase v.val
  let graph := actualObjectTrace M P.rep J
  let obstacle := anchor.val.image ∪ graph
  have hPc : IsClosed obstacle := (isCompact_range anchor.val.continuous).isClosed.union
    (actualObjectTrace_compact M P.rep J).isClosed
  have hvJ : v.val ∉ J := Finset.notMem_erase _ _
  have hPclear : Disjoint (arcInterior M (P.rep v)) obstacle :=
    (actual_zero_intrinsic_position_anchor_clearance M anchor F P v hv).union_right
      (actual_next_arc_disjoint_support_graph M P.rep
        (actual_position_family_disjoint M anchor F hF P) J v hvJ)
  have hQclear : Disjoint (arcInterior M (Q.rep v)) obstacle :=
    (actual_zero_intrinsic_position_anchor_clearance M anchor F Q v hv).union_right
      (actual_target_clearance_from_aligned_images M anchor F hF P Q v haligned)
  obtain ⟨G,hm,hfix,hend⟩ := actual_endpoint_bigon_relative_alignment M
    (P.rep v) (Q.rep v) obstacle hPc hPclear hQclear
    f hf A B p q hA hB hwhole haImage hbImage hp hq hboundary hinside
  have hanchor : ∀ t z, z ∈ anchor.val.image → G.map (t,z) = z :=
    fun t z hz => hfix t z (Or.inl hz)
  have hothers : ∀ w, w ≠ v → ∀ t z, z ∈ (P.rep w).val.image → G.map (t,z) = z := by
    intro w hw t z hz
    apply hfix t z
    right
    exact mem_iUnion.mpr ⟨w,mem_iUnion.mpr ⟨Finset.mem_erase.mpr
      ⟨fun he => hw (Subtype.ext he),w.property⟩,hz⟩⟩
  have himages : ∀ w, G.finalMap '' (P.rep w).val.image = (Q.rep w).val.image := by
    intro w
    by_cases hw : w = v
    · subst w; exact hend
    · rw [← haligned w hw]
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        change G.map (1,x) ∈ (P.rep w).val.image
        rw [hothers w hw 1 x hx]
        exact hx
      · intro hz
        exact ⟨z,hz,hothers w hw 1 z hz⟩
  have ha : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image := by
    intro t
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [hanchor t x hx] using hx
    · intro hz
      exact ⟨z,hz,hanchor t z hz⟩
  let H := timePositionSystem M anchor F hF P G hm ha
  have hends : ∀ w, (H.arc 1 w).val.image = (Q.rep w).val.image := by
    intro w
    exact (timeTransport_image M G hm 1 (P.rep w)).trans (himages w)
  exact ⟨G,hm,hanchor,hothers,himages,⟨{
    arc := H.arc
    continuous := H.continuous
    starts := H.starts
    ends := hends
    represents := H.represents
    disjoint := H.disjoint
    finite := H.finite
    minimal := H.minimal }⟩⟩

end
end CurveComplex.HyperellipticModel.ArcSurgery
