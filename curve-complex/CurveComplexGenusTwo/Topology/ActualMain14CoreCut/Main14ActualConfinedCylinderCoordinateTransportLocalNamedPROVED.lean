import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualEmbeddedPairTrackInverseLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
-- Recover the actual model coordinates of the WHOLE given source cylinder,
-- then transport through the SAME supplied upstairs annulus embedding B.
theorem actual_confined_cylinder_coordinate_transport {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
    (Φ : C(Circle × Interval,Y)) (hΦ : IsEmbedding Φ)
    (G : C(Circle × Interval,Circle × Interval))
    (q : C(Circle × Interval,Y)) (hq : IsEmbedding q)
    (hconf : Set.range q ⊆ Set.range (Φ.comp G))
    (B : C(Circle × Interval,Z)) (hB : IsEmbedding B) :
    ∃ R : C(Circle × Interval,Circle × Interval), ∃ Q : C(Circle × Interval,Z),
      IsEmbedding R ∧ IsEmbedding Q ∧
      (∀ p, Φ (R p)=q p) ∧ (∀ p, Q p=B (R p)) ∧
      Set.range R ⊆ Set.range G ∧
      (∀ p v, Φ (G v)=q p → R p=G v) := by
  audit_main14_base3
    let e := hΦ.toHomeomorph
    have hrange (p : Circle × Interval) : q p ∈ Set.range Φ := by
      obtain ⟨v,hv⟩ := hconf ⟨p,rfl⟩
      exact ⟨G v,hv⟩
    let s : C(Circle × Interval,Set.range Φ) := ⟨fun p => ⟨q p,hrange p⟩,
      q.continuous.subtype_mk _⟩
    let R : C(Circle × Interval,Circle × Interval) :=
      ⟨fun p => e.symm (s p),e.symm.continuous.comp s.continuous⟩
    have heq (p : Circle × Interval) : Φ (R p)=q p :=
      congrArg Subtype.val (e.apply_symm_apply (s p))
    have hR : IsEmbedding R := by
      refine (R.continuous.isClosedEmbedding ?_).isEmbedding
      intro p v hv
      apply hq.injective
      rw [←heq p,←heq v,hv]
    let Q : C(Circle × Interval,Z) := B.comp R
    refine ⟨R,Q,hR,hB.comp hR,heq,(fun p => rfl),?_,?_⟩
    · rintro x ⟨p,rfl⟩
      obtain ⟨v,hv⟩ := hconf ⟨p,rfl⟩
      exact ⟨v,hΦ.injective (hv.trans (heq p).symm)⟩
    · intro p v hv
      exact hΦ.injective ((heq p).trans hv.symm)
end CurveComplex.HyperellipticModel
