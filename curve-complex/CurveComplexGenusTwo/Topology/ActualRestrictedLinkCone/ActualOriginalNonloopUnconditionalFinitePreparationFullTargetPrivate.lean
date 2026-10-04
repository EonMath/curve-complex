import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopFinitePreparationFullTargetPrivate

open Lean Elab Term in
elab "checkedRLUnconditionalNonloopPreparedFullTarget" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopFinitePreparationFullTargetPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_finite_preparation_full_target_producer_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
set_option maxHeartbeats 2600000
private theorem actual_original_nonloop_unconditional_finite_preparation_full_target_producer_private
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
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠
      (r0 ⟨u.val,hTF u.property⟩).val.map 1) :
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
  have hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u) := (hr0 _).trans (hrT u).symm
  have he := arcEndpoints_isotopy_invariant M (r0 ⟨u.val,hTF u.property⟩) (rT u) (Quotient.exact hab)
  change ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,
    (r0 ⟨u.val,hTF u.property⟩).val.map 1}:Finset S)={(rT u).val.map 0,(rT u).val.map 1} at he
  have hends : ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,
      (r0 ⟨u.val,hTF u.property⟩).val.map 1}:Set S)={(rT u).val.map 0,(rT u).val.map 1} := by
    have hcoe := congrArg (fun f : Finset S => (f:Set S)) he
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hcoe
  have hn : (rT u).val.map 0≠(rT u).val.map 1 := by
    intro hb
    have h0 : (r0 ⟨u.val,hTF u.property⟩).val.map 0∈
        ({(rT u).val.map 0,(rT u).val.map 1}:Set S) := hends ▸ (by simp)
    have h1 : (r0 ⟨u.val,hTF u.property⟩).val.map 1∈
        ({(rT u).val.map 0,(rT u).val.map 1}:Set S) := hends ▸ (by simp)
    have h0eq : (r0 ⟨u.val,hTF u.property⟩).val.map 0=(rT u).val.map 1 := by simpa [hb] using h0
    have h1eq : (r0 ⟨u.val,hTF u.property⟩).val.map 1=(rT u).val.map 1 := by simpa [hb] using h1
    exact ha (h0eq.trans h1eq.symm)
  exact checkedRLUnconditionalNonloopPreparedFullTarget M p T F J hTF hJT r r0 hd0
    rT hrT hdT haligned0 hgraph u hu hn hends
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_original_nonloop_unconditional_finite_preparation_full_target_producer_private
