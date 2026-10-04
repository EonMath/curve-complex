import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopUnconditionalFinitePreparationFullTargetPrivate

namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2600000
private theorem actual_original_nonloop_finite_contact_cancellation_of_actual_strict_drop_private
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
    (hStep : ∀ (current : {w // w∈T.val} → EssentialMarkedArc M),
      (∀ w : {w // w∈T.val},w.val∈J → Disjoint (arcInterior M (current w)) (arcInterior M (current u))) →
      (∀ w : {w // w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=current w) →
      Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=Quotient.mk (essentialArcSetoid M) (current u) →
      (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u)).Finite →
      (∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (current u) q) →
      ∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u),
      ∃ c : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        (∀ t z,z∈M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z∈actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (current u).val.image=c.val.image ∧
        Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) (current u) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) c).Finite ∧
        (∀ q∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) c,
          ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) c q) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) c).ncard<
          (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (current u)).ncard)
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
  induction hn : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard
      using Nat.strong_induction_on generalizing rT with
  | h n ih =>
    by_cases hzero : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard=0
    · refine ⟨rT u,AmbientIsotopy.identity S,(fun t z hz => rfl),(fun t z hz => rfl),?_,rfl,?_⟩
      · exact Set.image_id _
      · exact (Set.ncard_eq_zero hfinite).mp hzero
    obtain ⟨q,hq⟩ := (Set.ncard_pos hfinite).mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨c,H,hm,hG,himage,hclass,hfin,htrans,hdrop⟩ :=
      hStep rT hdT haligned0 hab hfinite hcross q hq
    let rT' := Function.update rT u c
    have huEq : rT' u=c := Function.update_self _ _ _
    have hwu (w : {w // w ∈ T.val}) (hw : w.val ∈ J) : w≠u := by
      intro he
      exact hu (congrArg Subtype.val he ▸ hw)
    have hwEq (w : {w // w ∈ T.val}) (hw : w.val ∈ J) : rT' w=rT w :=
      Function.update_of_ne (hwu w hw) _ _
    have haligned' : ∀ w : {w // w ∈ T.val},w.val ∈ J → r0 ⟨w.val,hTF w.property⟩=rT' w := by
      intro w hw
      rw [hwEq w hw]
      exact haligned0 w hw
    have hdT' : ∀ w : {w // w ∈ T.val},w.val ∈ J →
        Disjoint (arcInterior M (rT' w)) (arcInterior M (rT' u)) := by
      intro w hw
      rw [hwEq w hw,huEq]
      apply disjoint_left.mpr
      intro z hzW hzC
      have hzGraph : z ∈ actualObjectTrace M r J := by
        rw [←hgraph]
        refine mem_iUnion.mpr ⟨⟨w.val,hTF w.property⟩,mem_iUnion.mpr ⟨hw,?_⟩⟩
        rw [haligned0 w hw]
        exact hzW.1
      obtain ⟨y,hy,hyz⟩ := himage.symm ▸ hzC.1
      obtain ⟨e,he⟩ := H.homeomorphism_at (1:Interval)
      have hyEq : y=z := e.injective (by rw [he y,he z,hG 1 z hzGraph]; exact hyz)
      exact disjoint_left.mp (hdT w hw) hzW ⟨hyEq ▸ hy,hzC.2⟩
    have hab' : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
        Quotient.mk (essentialArcSetoid M) (rT' u) := by
      rw [huEq]
      exact hab.trans hclass.symm
    obtain ⟨d,K,hmK,hGK,himageK,hclassK,hzeroK⟩ :=
      ih (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT' u)).ncard
        (by rw [huEq]; exact hdrop.trans_eq hn) rT' hdT' haligned' hab'
        (by simpa only [huEq] using hfin) (by simpa only [huEq] using htrans) rfl
    refine ⟨d,H.compose K,?_,?_,?_,?_,hzeroK⟩
    · intro t z hz
      change K.map (t,H.map (t,z))=z
      rw [hm t z hz,hmK t z hz]
    · intro t z hz
      change K.map (t,H.map (t,z))=z
      rw [hG t z hz,hGK t z hz]
    · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,himage]
      simpa only [huEq] using himageK
    · have hcClass : Quotient.mk (essentialArcSetoid M) d=Quotient.mk (essentialArcSetoid M) c := by
        simpa only [huEq] using hclassK
      exact hcClass.trans hclass

#print axioms actual_original_nonloop_finite_contact_cancellation_of_actual_strict_drop_private
end CurveComplex.HyperellipticModel
