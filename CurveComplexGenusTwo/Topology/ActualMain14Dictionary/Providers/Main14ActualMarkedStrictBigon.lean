import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualEquivariantIsotopyDescent

namespace CurveComplex.BranchedDoubleCover
open Set Topology

/-- Actual upstairs and downstairs isotopies commuting with the given
projection carry full preimages to full preimages, at the actual endpoint. -/
theorem commuting_isotopies_full_preimage_transport
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (K : AmbientIsotopy E) (L : AmbientIsotopy S)
    (hcomm : ∀ t x, L.map (t,q.projection x) = q.projection (K.map (t,x)))
    (A : Set S) :
    K.finalMap '' (q.projection ⁻¹' A) = q.projection ⁻¹' (L.finalMap '' A) := by
  classical
  obtain ⟨e,he⟩ := K.homeomorphism_at ⟨1,by norm_num⟩
  obtain ⟨f,hf⟩ := L.homeomorphism_at ⟨1,by norm_num⟩
  ext z; constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨q.projection x,hx,hcomm _ x⟩
  · rintro ⟨s,hs,heq⟩
    have hez : K.finalMap (e.symm z) = z := by
      change K.map (⟨1,by norm_num⟩,e.symm z) = z
      rw [← he,e.apply_symm_apply]
    have hp : q.projection (e.symm z) = s := by
      apply f.injective
      rw [hf,hf,hcomm]
      change q.projection (K.finalMap (e.symm z)) = L.finalMap s
      rw [hez]
      exact heq.symm
    exact ⟨e.symm z,by simpa only [Set.mem_preimage,hp] using hs,hez⟩
end CurveComplex.BranchedDoubleCover

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 4000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]

/-- The actual empty full-preimage bigon produces a marked downstairs ambient
isotopy and a strict crossing decrease of the corresponding upstairs full
preimages. This consumes the constructed paired operation, rather than adding
an equivariant operation to the original source hypotheses. -/
theorem innermost_full_preimage_actual_marked_strict_bigon_operation
    (M : HyperellipticModel E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : LocalSurgery.TwoCurveDisk a.val b.val)
    (c d : PuncturedCircle M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.image)
    (htbase : Transverse c.curve d.curve)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    ∃ a' b' : EssentialCurve E, ∃ L : AmbientIsotopy S,
      ((a'.val.image = M.cover.projection ⁻¹' (L.finalMap '' c.image) ∧ b' = b) ∨
        (b'.val.image = M.cover.projection ⁻¹' (L.finalMap '' d.image) ∧ a' = a)) ∧
      Quotient.mk (essentialCurveSetoid E) a' = Quotient.mk (essentialCurveSetoid E) a ∧
      Quotient.mk (essentialCurveSetoid E) b' = Quotient.mk (essentialCurveSetoid E) b ∧
      Transverse a'.val b'.val ∧
      (a'.val.image ∩ b'.val.image).ncard < (a.val.image ∩ b.val.image).ncard ∧
      (∀ t x, x ∈ M.cover.branch → L.map (t,x) = x) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨a',b',K,hchoice,hca,hcb,ht',hdrop,hKeq,hKram⟩ :=
    M.innermost_full_preimage_actual_equivariant_strict_bigon_operation a b ht B c d ha hb htbase hempty
  obtain ⟨L,hcomm,hmarks⟩ := M.cover.actual_deck_equivariant_isotopy_descends K hKeq hKram
  refine ⟨a',b',L,?_,hca,hcb,ht',hdrop,hmarks⟩
  rcases hchoice with ⟨hi,hb'⟩ | ⟨hi,ha'⟩
  · left
    refine ⟨?_,hb'⟩
    rw [← hi,ha]
    exact M.cover.commuting_isotopies_full_preimage_transport K L hcomm c.image
  · right
    refine ⟨?_,ha'⟩
    rw [← hi,hb]
    exact M.cover.commuting_isotopies_full_preimage_transport K L hcomm d.image
end CurveComplex.HyperellipticModel
