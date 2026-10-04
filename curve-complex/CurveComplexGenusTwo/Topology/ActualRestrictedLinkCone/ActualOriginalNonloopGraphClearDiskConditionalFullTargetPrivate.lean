import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGivenGraphClearDiskStrictDropPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopFiniteContactDescentAssemblyPrivate

open Lean Elab Term in
elab "checkedRLPositiveNonloopGivenDiskDrop" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGivenGraphClearDiskStrictDropPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_given_graph_clear_disk_strict_contact_drop_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLPositiveNonloopStrictDropDescent" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopFiniteContactDescentAssemblyPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_finite_contact_cancellation_of_actual_strict_drop_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLPositiveNonloopFullTargetInitialization" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopUnconditionalFinitePreparationFullTargetPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_unconditional_finite_preparation_full_target_producer_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2600000
private theorem actual_original_nonloop_finite_contact_cancellation_of_graph_clear_disk_selection_private
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hdT : ∀ w : {w // w ∈ T.val},w.val ∈ J → Disjoint (arcInterior M (rT w)) (arcInterior M (rT u)))
    (haligned0 : ∀ w : {w // w ∈ T.val},w.val ∈ J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u))
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠(r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hSelect : ∀ (current : {w // w∈T.val} → EssentialMarkedArc M),
      (∀ w : {w // w∈T.val},w.val∈J → Disjoint (arcInterior M (current w)) (arcInterior M (current u))) →
      (∀ w : {w // w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=current w) →
      Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=Quotient.mk (essentialArcSetoid M) (current u) →
      (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u)).Finite →
      (∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (current u) q) →
      ∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u),
      ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (current u),
        Disjoint D.openInterior
          ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (current u).val.image ∪
            (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        (D.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u) ∨
          D.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u)))
    (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
    (hcross : ∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) q) :
    ∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      (∀ t z,z ∈ M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
      H.finalMap '' (rT u).val.image=b'.val.image ∧
      Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
      ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b'=∅ := by
  classical
  apply checkedRLPositiveNonloopStrictDropDescent M p T F J hTF hJT r r0 rT
    hd0 u hu hdT haligned0 hgraph hab ha
  · intro current hdCurrent halignedCurrent habCurrent hfiniteCurrent hcrossCurrent q hq
    exact checkedRLPositiveNonloopGivenDiskDrop M p T F J hTF hJT r r0 current
      hd0 u hu hdCurrent halignedCurrent hgraph habCurrent ha hfiniteCurrent hcrossCurrent
      (hSelect current hdCurrent halignedCurrent habCurrent hfiniteCurrent hcrossCurrent q hq) q hq
  · exact hfinite
  · exact hcross

private theorem actual_original_nonloop_zero_contact_full_target_of_graph_clear_disk_selection_private
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
    (hSelect : ∀ (current : {w // w∈T.val} → EssentialMarkedArc M),
      (∀ w : {w // w∈T.val},w.val∈J → Disjoint (arcInterior M (current w)) (arcInterior M (current u))) →
      (∀ w : {w // w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=current w) →
      Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=Quotient.mk (essentialArcSetoid M) (current u) →
      (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u)).Finite →
      (∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (current u) q) →
      ∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u),
      ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (current u),
        Disjoint D.openInterior
          ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (current u).val.image ∪
            (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        (D.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u) ∨
          D.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u)))
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
  obtain ⟨prepared,I,hprepared,hpreparedDisjoint,hpreparedAligned,hmI,hGI,himageI,hfinite,hcross⟩ :=
    checkedRLPositiveNonloopFullTargetInitialization M p T F J hTF hJT r r0 hr0 hd0
      rT hrT hdT haligned0 hgraph u hu ha
  have hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (prepared u) :=
    (hr0 _).trans (hprepared u).symm
  have hdSelected : ∀ w : {w//w∈T.val},w.val∈J →
      Disjoint (arcInterior M (prepared w)) (arcInterior M (prepared u)) := by
    intro w hw
    apply hpreparedDisjoint
    intro he
    exact hu (congrArg Subtype.val he ▸ hw)
  obtain ⟨b,K,hmK,hGK,himageK,hclassK,hzeroK⟩ :=
    actual_original_nonloop_finite_contact_cancellation_of_graph_clear_disk_selection_private
      M p T F J hTF hJT r r0 prepared hd0 u hu hdSelected hpreparedAligned hgraph hab ha
      hSelect hfinite hcross
  obtain ⟨s,hs,hsd,hsaligned,hsimage⟩ := checkedRLNonloopFullTargetTransport
    M F T.val J hTF hJT r r0 prepared hprepared hpreparedDisjoint hpreparedAligned hgraph K hmK hGK
  refine ⟨s,I.compose K,hs,hsd,hsaligned,?_,?_,?_,?_⟩
  · intro t z hz
    change K.map (t,I.map (t,z))=z
    rw [hmI t z hz,hmK t z hz]
  · intro t z hz
    change K.map (t,I.map (t,z))=z
    rw [hGI t z hz,hGK t z hz]
  · intro w
    rw [AmbientIsotopy.compose_finalMap,Set.image_comp,himageI w]
    exact (hsimage w).symm
  · have him : (s u).val.image=b.val.image := (hsimage u).trans himageK
    have he : ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (s u)=
        ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b := by
      unfold ArcSurgery.crossings arcInterior
      rw [him]
    rw [he]
    exact hzeroK

#print axioms actual_original_nonloop_finite_contact_cancellation_of_graph_clear_disk_selection_private
#print axioms actual_original_nonloop_zero_contact_full_target_of_graph_clear_disk_selection_private
end CurveComplex.HyperellipticModel
