import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalPositiveLoopGraphFixedFiniteContactCancellationV2
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ZeroContactLoopIntersection

open Lean Elab Term in
elab "checkedRecovery20IsolatedOriginalLoopRelativeFinitePreparation" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `CurveComplex.HyperellipticModel.actual_original_aligned_disjoint_families_loop_relative_finite_preparation_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRecovery20IsolatedOriginalFiniteLoopCancellation" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalPositiveLoopGraphFixedFiniteContactCancellationV2 0).append
    `CurveComplex.HyperellipticModel.actual_original_positive_loop_graph_fixed_finite_contact_cancellation_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRecovery20IsolatedFullTargetFamilyTransport" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `CurveComplex.HyperellipticModel.actual_original_graph_fixed_motion_transports_full_target_family_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
set_option maxHeartbeats 2600000
private theorem actual_original_loop_unconditional_zero_contact_full_target_producer_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
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
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0=(r0 ⟨u.val,hTF u.property⟩).val.map 1) :
    ∃ s : {w//w∈T.val} → EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      (∀ w,Quotient.mk (essentialArcSetoid M) (s w)=w.val) ∧
      (∀ w z,w≠z → Disjoint (arcInterior M (s w)) (arcInterior M (s z))) ∧
      (∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=s w) ∧
      (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
      (∀ w,H.finalMap '' (rT w).val.image=(s w).val.image) ∧
      ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (s u)=∅ := by
  classical
  have hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u) := (hr0 _).trans (hrT u).symm
  have hlooptype := actual_same_class_loop_closure_invariant M (r0 ⟨u.val,hTF u.property⟩) (rT u) hab
  have hbase := actual_same_class_loop_literal_base M (r0 ⟨u.val,hTF u.property⟩) (rT u) ha hab
  have hends : ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,
      (r0 ⟨u.val,hTF u.property⟩).val.map 1}:Set S)=
      {(rT u).val.map 0,(rT u).val.map 1} := by
    rw [←ha,←hlooptype.mp ha,←hbase]
  have actual_original_loop_relative_finite_preparation_consumer
      (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0=
        (r0 ⟨u.val,hTF u.property⟩).val.map 1) :
      ∃ c : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) (rT u) ∧
        H.finalMap '' (rT u).val.image=c.val.image ∧
        (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) c).Finite ∧
        ∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) c,
          ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) c q := by
    let source : {w//w∈T.val} → EssentialMarkedArc M :=
      fun w => r0 ⟨w.val,hTF w.property⟩
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
    have hbLoop : (rT u).val.map 0=(rT u).val.map 1 := hlooptype.mp ha
    have haBase : (source u).val.map 0=(rT u).val.map 0 := by
      have hb0 : (rT u).val.map 0∈
          ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,
            (r0 ⟨u.val,hTF u.property⟩).val.map 1}:Set S) := by
        rw [hends];simp
      have he : (rT u).val.map 0=(r0 ⟨u.val,hTF u.property⟩).val.map 1 := by
        simpa [ha] using hb0
      exact ha.trans he.symm
    obtain ⟨c,H,hclass,himage,hm,hG,hfin,hcross⟩ :=
      checkedRecovery20IsolatedOriginalLoopRelativeFinitePreparation M source rT hsd hdT J' u hju
        halign hbLoop false haBase
    refine ⟨c,H,hclass,himage,hm,?_,hfin,hcross⟩
    intro t z hz
    apply hG t z
    rw [hP]
    exact hz
  have actual_original_loop_unconditional_zero_contact_consumer
      (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0=
        (r0 ⟨u.val,hTF u.property⟩).val.map 1) :
      ∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (rT u).val.image=b'.val.image ∧
        Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
        ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b'=∅ := by
    obtain ⟨c,H,hclass,himage,hm,hG,hfin,hcross⟩ :=
      actual_original_loop_relative_finite_preparation_consumer ha
    let rT' := Function.update rT u c
    have huEq : rT' u=c := Function.update_self _ _ _
    have hwu (w : {w//w∈T.val}) (hw : w.val∈J) : w≠u := by
      intro he
      exact hu (congrArg Subtype.val he ▸ hw)
    have hwEq (w : {w//w∈T.val}) (hw : w.val∈J) : rT' w=rT w :=
      Function.update_of_ne (hwu w hw) _ _
    have haligned' : ∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=rT' w := by
      intro w hw
      rw [hwEq w hw]
      exact haligned0 w hw
    have hdT' : ∀ w : {w//w∈T.val},w.val∈J →
        Disjoint (arcInterior M (rT' w)) (arcInterior M (rT' u)) := by
      intro w hw
      rw [hwEq w hw,huEq]
      apply disjoint_left.mpr
      intro z hzW hzC
      have hzGraph : z∈actualObjectTrace M r J := by
        rw [←hgraph]
        refine mem_iUnion.mpr ⟨⟨w.val,hTF w.property⟩,mem_iUnion.mpr ⟨hw,?_⟩⟩
        rw [haligned0 w hw]
        exact hzW.1
      obtain ⟨y,hy,hyz⟩ := himage.symm ▸ hzC.1
      obtain ⟨e,he⟩ := H.homeomorphism_at (1:Interval)
      have hyEq : y=z := e.injective (by rw [he y,he z,hG 1 z hzGraph];exact hyz)
      exact disjoint_left.mp (hdT w u (hwu w hw)) hzW ⟨hyEq ▸ hy,hzC.2⟩
    have hab' : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
        Quotient.mk (essentialArcSetoid M) (rT' u) := by
      rw [huEq]
      exact hab.trans hclass.symm
    obtain ⟨d,K,hmK,hGK,himageK,hclassK,hzeroK⟩ :=
      checkedRecovery20IsolatedOriginalFiniteLoopCancellation
        M p T F J hTF hJT r r0 rT' hd0 u hu hdT' haligned' hgraph hab' ha
        (by simpa only [huEq] using hfin) (by simpa only [huEq] using hcross)
    refine ⟨d,H.compose K,?_,?_,?_,?_,hzeroK⟩
    · intro t z hz
      change K.map (t,H.map (t,z))=z
      rw [hm t z hz,hmK t z hz]
    · intro t z hz
      change K.map (t,H.map (t,z))=z
      rw [hG t z hz,hGK t z hz]
    · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,himage]
      simpa only [huEq] using himageK
    · have hdClass : Quotient.mk (essentialArcSetoid M) d=Quotient.mk (essentialArcSetoid M) c := by
        simpa only [huEq] using hclassK
      exact hdClass.trans hclass
  obtain ⟨b,H,hm,hG,himage,hclass,hzero⟩ := actual_original_loop_unconditional_zero_contact_consumer ha
  obtain ⟨s,hs,hsd,hsaligned,hsimage⟩ := checkedRecovery20IsolatedFullTargetFamilyTransport
    M F T.val J hTF hJT r r0 rT hrT hdT haligned0 hgraph H hm hG
  refine ⟨s,H,hs,hsd,hsaligned,hm,hG,(fun w => (hsimage w).symm),?_⟩
  have him : (s u).val.image=b.val.image := (hsimage u).trans himage
  have he : ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (s u)=
      ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b := by
    unfold ArcSurgery.crossings arcInterior
    rw [him]
  rw [he]
  exact hzero
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_original_loop_unconditional_zero_contact_full_target_producer_private
