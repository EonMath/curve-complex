import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopUnconditionalZeroContactFullTargetProducerPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopZeroContactTerminalAlignmentPrivate
open Lean Elab Term in
elab "checkedRLOriginalNonloopZeroContactFullTarget" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopUnconditionalZeroContactFullTargetProducerPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_unconditional_zero_contact_full_target_producer_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLOriginalNonloopZeroContactTerminalAlignment" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopZeroContactTerminalAlignmentPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_zero_contact_nonloop_graph_relative_alignment_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLOriginalNonloopEntireFixedSetReverse" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopSelectedEndpointGraphClearancePrivate 0).append
    `actual_entire_fixed_set_ambient_isotopy_reverse_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2000000
private theorem actual_original_nonloop_graph_relative_alignment_private
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val⊆F) (hJT : J⊆T.val)
    (r r0 : {w//w∈F} → EssentialMarkedArc M)
    (hr0 : ∀ w,Quotient.mk (essentialArcSetoid M) (r0 w)=w.val)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (rT : {w//w∈T.val} → EssentialMarkedArc M)
    (hrT : ∀ w,Quotient.mk (essentialArcSetoid M) (rT w)=w.val)
    (hdT : ∀ w z,w≠z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned0 : ∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (u : {w//w∈T.val}) (hu : u.val∉J)
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠
      (r0 ⟨u.val,hTF u.property⟩).val.map 1)
 :
    ∃ H : AmbientIsotopy S,
      (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
      H.finalMap '' (r0 ⟨u.val,hTF u.property⟩).val.image=(rT u).val.image := by
  classical
  obtain ⟨current,I,hcurrent,hcurrentDisjoint,hcurrentAligned,hmI,hGI,himageI,hzero⟩ :=
    checkedRLOriginalNonloopZeroContactFullTarget M p T F J hTF hJT r r0 hr0 hd0
      rT hrT hdT haligned0 hgraph u hu ha
  obtain ⟨K,hmK,hGK,himageK⟩ := checkedRLOriginalNonloopZeroContactTerminalAlignment
    M p T F J hTF hJT r r0 hr0 hd0 current hcurrent hcurrentDisjoint
      hcurrentAligned hgraph u hu ha hzero
  let P : Set S := (M.cover.branch:Set S) ∪ actualObjectTrace M r J
  obtain ⟨R,hRfix,hRinverse⟩ := checkedRLOriginalNonloopEntireFixedSetReverse I P
    (fun t z hz => hz.elim (hmI t z) (hGI t z))
  refine ⟨K.compose R,?_,?_,?_⟩
  · intro t z hz
    change R.map (t,K.map (t,z))=z
    rw [hmK t z hz,hRfix t z (Or.inl hz)]
  · intro t z hz
    change R.map (t,K.map (t,z))=z
    rw [hGK t z hz,hRfix t z (Or.inr hz)]
  · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,himageK,←himageI u]
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      rw [hRinverse]
      exact hx
    · intro hz
      refine ⟨I.finalMap z,⟨z,hz,rfl⟩,hRinverse z⟩

#print axioms actual_original_nonloop_graph_relative_alignment_private
end CurveComplex.HyperellipticModel
