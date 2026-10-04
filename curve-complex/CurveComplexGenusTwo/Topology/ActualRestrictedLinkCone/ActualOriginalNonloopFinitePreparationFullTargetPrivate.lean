import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopSelectedEndpointGraphClearancePrivate

open Lean Elab Term in
elab "checkedRLNonloopOriginalFinitePreparation" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualNonloopSelectedEndpointGraphClearancePrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_aligned_disjoint_families_nonloop_relative_finite_preparation_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopFullTargetTransport" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `CurveComplex.HyperellipticModel.actual_original_graph_fixed_motion_transports_full_target_family_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
set_option maxHeartbeats 2600000

private theorem actual_original_nonloop_finite_preparation_full_target_producer_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val⊆F) (hJT : J⊆T.val)
    (r r0 : {w//w∈F} → EssentialMarkedArc M)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (rT : {w//w∈T.val} → EssentialMarkedArc M)
    (hrT : ∀ w,Quotient.mk (essentialArcSetoid M) (rT w)=w.val)
    (hdT : ∀ w z,w≠z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned0 : ∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (u : {w//w∈T.val}) (hu : u.val∉J)
    (hnonloop : (rT u).val.map 0≠(rT u).val.map 1)
    (hends : ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,
      (r0 ⟨u.val,hTF u.property⟩).val.map 1}:Set S)={(rT u).val.map 0,(rT u).val.map 1}) :
    ∃ s : {w//w∈T.val} → EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      (∀ w,Quotient.mk (essentialArcSetoid M) (s w)=w.val) ∧
      (∀ w z,w≠z → Disjoint (arcInterior M (s w)) (arcInterior M (s z))) ∧
      (∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=s w) ∧
      (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
      (∀ w,H.finalMap '' (rT w).val.image=(s w).val.image) ∧
      (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (s u)).Finite ∧
      ∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (s u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (s u) q := by
  classical
  let source : {w//w∈T.val} → EssentialMarkedArc M := fun w => r0 ⟨w.val,hTF w.property⟩
  let J' : Finset {w//w∈T.val} := Finset.univ.filter (fun w => w.val∈J)
  have hju : u∉J' := by simpa only [J',Finset.mem_filter,Finset.mem_univ,true_and] using hu
  have hsd : ∀ i j : {w//w∈T.val},i≠j →
      Disjoint (arcInterior M (source i)) (arcInterior M (source j)) := by
    intro i j hij
    apply hd0
    intro he
    exact hij (Subtype.ext (congrArg (fun w : {w//w∈F} => w.val) he))
  have halign : ∀ w∈J',(rT w).val.image=(source w).val.image := by
    intro w hw
    have hwJ : w.val∈J := (Finset.mem_filter.mp hw).2
    exact congrArg (fun a : EssentialMarkedArc M => a.val.image) (haligned0 w hwJ).symm
  have hP : (⋃ w : {w//w∈J'},(source w.val).val.image)=actualObjectTrace M r J := by
    rw [←hgraph]
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨w,hzw⟩ := mem_iUnion.mp hz
      have hwJ : w.val.val∈J := (Finset.mem_filter.mp w.property).2
      exact mem_iUnion.mpr ⟨⟨w.val.val,hTF w.val.property⟩,mem_iUnion.mpr ⟨hwJ,hzw⟩⟩
    · intro z hz
      obtain ⟨v,hv⟩ := mem_iUnion.mp hz
      obtain ⟨hvJ,hzv⟩ := mem_iUnion.mp hv
      let w : {w//w∈T.val} := ⟨v.val,hJT hvJ⟩
      have hw : w∈J' := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvJ⟩
      have heF : (⟨w.val,hTF w.property⟩ : {w//w∈F})=v := Subtype.ext rfl
      exact mem_iUnion.mpr ⟨⟨w,hw⟩,by simpa only [source,heF] using hzv⟩
  obtain ⟨c,H,hclass,himage,hm,hG,hfin,hcross⟩ :=
    checkedRLNonloopOriginalFinitePreparation M source rT hsd hdT J' u hju halign hnonloop hends
  have hGraph : ∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z := by
    intro t z hz
    apply hG t z
    rw [hP]
    exact hz
  obtain ⟨s,hs,hsd,hsaligned,hsimage⟩ := checkedRLNonloopFullTargetTransport
    M F T.val J hTF hJT r r0 rT hrT hdT haligned0 hgraph H hm hGraph
  have him : (s u).val.image=c.val.image := (hsimage u).trans himage
  have he : ArcSurgery.crossings M (source u) (s u)=ArcSurgery.crossings M (source u) c := by
    unfold ArcSurgery.crossings arcInterior
    rw [him]
  refine ⟨s,H,hs,hsd,hsaligned,hm,hGraph,(fun w => (hsimage w).symm),?_,?_⟩
  · rw [he]
    exact hfin
  · intro q hq
    have hcq := hcross q (he ▸ hq)
    simpa only [ArcSurgery.CrossesInDisk,him] using hcq

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_original_nonloop_finite_preparation_full_target_producer_private
