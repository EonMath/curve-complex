import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalLoopUnconditionalZeroContactFullTargetProducerPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopSelectedEndpointGraphClearancePrivate
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ActualSelectedLoopZeroContactAmbientMotion
open Lean Elab Term in
elab "checkedRLOriginalLoopZeroContactFullTargetForAlignment" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalLoopUnconditionalZeroContactFullTargetProducerPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_loop_unconditional_zero_contact_full_target_producer_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLOriginalLoopZeroContactTerminalMotionForAlignment" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ActualSelectedLoopZeroContactAmbientMotion 0).append
    `CurveComplex.HyperellipticModel.actual_selected_loop_zero_contact_ambient_motion_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLOriginalLoopEntireFixedSetReverseForAlignment" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopSelectedEndpointGraphClearancePrivate 0).append
    `actual_entire_fixed_set_ambient_isotopy_reverse_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2000000
private theorem actual_original_loop_graph_relative_alignment_private
    (M : HyperellipticModel E S) (p : ℕ) (hp : 1≤p) (T : ActualStratum M p)
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
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0=(r0 ⟨u.val,hTF u.property⟩).val.map 1) :
    ∃ H : AmbientIsotopy S,
      (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
      H.finalMap '' (r0 ⟨u.val,hTF u.property⟩).val.image=(rT u).val.image := by
  classical
  obtain ⟨current,I,hcurrent,hcurrentDisjoint,hcurrentAligned,hmI,hGI,himageI,hzero⟩ :=
    checkedRLOriginalLoopZeroContactFullTargetForAlignment M p T F J hTF hJT r r0 hr0 hd0
      rT hrT hdT haligned0 hgraph u hu ha
  obtain ⟨K,hmK,hGK,himageK⟩ := checkedRLOriginalLoopZeroContactTerminalMotionForAlignment
    M p hp T current hcurrent hcurrentDisjoint F J hTF hJT r0 hr0 hd0
      hcurrentAligned r hgraph u hu ha hzero
  let H := I.compose K
  have hmH : ∀ t z,z∈M.cover.branch → H.map (t,z)=z := by
    intro t z hz
    change K.map (t,I.map (t,z))=z
    rw [hmI t z hz,hmK t z hz]
  have hGH : ∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z := by
    intro t z hz
    change K.map (t,I.map (t,z))=z
    rw [hGI t z hz,hGK t z hz]
  have himageH : H.finalMap '' (rT u).val.image=(r0 ⟨u.val,hTF u.property⟩).val.image := by
    rw [AmbientIsotopy.compose_finalMap,Set.image_comp,himageI u,himageK]
  let P : Set S := (M.cover.branch:Set S) ∪ actualObjectTrace M r J
  obtain ⟨R,hRfix,hRinverse⟩ := checkedRLOriginalLoopEntireFixedSetReverseForAlignment H P
    (fun t z hz => hz.elim (hmH t z) (hGH t z))
  refine ⟨R,(fun t z hz => hRfix t z (Or.inl hz)),
    (fun t z hz => hRfix t z (Or.inr hz)),?_⟩
  rw [←himageH]
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
    rw [hRinverse]
    exact hx
  · intro hz
    exact ⟨H.finalMap z,⟨z,hz,rfl⟩,hRinverse z⟩

#print axioms actual_original_loop_graph_relative_alignment_private
end CurveComplex.HyperellipticModel
