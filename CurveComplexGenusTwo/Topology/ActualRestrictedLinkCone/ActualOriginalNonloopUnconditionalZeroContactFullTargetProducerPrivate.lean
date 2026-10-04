import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalPositiveNonloopSameClassGraphClearDiskRequest
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGraphClearDiskConditionalFullTargetPrivate

open Lean Elab Term in
elab "checkedRLApprovedDiskUnconditionalNonloopZeroContactAssembly" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGraphClearDiskConditionalFullTargetPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_zero_contact_full_target_of_graph_clear_disk_selection_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1500000
private theorem actual_original_nonloop_unconditional_zero_contact_full_target_producer_private
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
    ∃ s : {w//w∈T.val} → EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      (∀ w,Quotient.mk (essentialArcSetoid M) (s w)=w.val) ∧
      (∀ w z,w≠z → Disjoint (arcInterior M (s w)) (arcInterior M (s z))) ∧
      (∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=s w) ∧
      (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
      (∀ w,H.finalMap '' (rT w).val.image=(s w).val.image) ∧
      ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (s u)=∅ := by
  classical
  apply checkedRLApprovedDiskUnconditionalNonloopZeroContactAssembly M p T F J hTF hJT
    r r0 hr0 hd0 rT hrT hdT haligned0 hgraph u hu ha
  intro current hdCurrent halignedCurrent habCurrent hfiniteCurrent hcrossCurrent q hq
  exact actual_original_positive_nonloop_same_class_entire_pair_and_graph_clear_disk
    M p T F J hTF hJT r r0 current hd0 u hu hdCurrent halignedCurrent hgraph habCurrent
    ha hfiniteCurrent hcrossCurrent q hq

#print axioms actual_original_nonloop_unconditional_zero_contact_full_target_producer_private
end CurveComplex.HyperellipticModel
