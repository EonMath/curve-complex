import CurveComplexGenusTwo.Dictionary.Circle24.TwoRectangleCylinder
import CurveComplexGenusTwo.Dictionary.Circle24.ActualPrescribedSquareSeam
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 9000000
noncomputable def boundaryUnitSquareRaw (p : Interval × Interval) : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1 :=
  ⟨(2*p.1.val-1,2*p.2.val-1),⟨⟨by linarith [p.1.property.1],by linarith [p.1.property.2]⟩,
    ⟨by linarith [p.2.property.1],by linarith [p.2.property.2]⟩⟩⟩
private theorem boundaryUnitSquareRaw_injective : Function.Injective boundaryUnitSquareRaw := by
  intro p q h
  have hh := congrArg Subtype.val h
  apply Prod.ext <;> apply Subtype.ext
  · have hx := congrArg Prod.fst hh; dsimp [boundaryUnitSquareRaw] at hx; linarith
  · have hy := congrArg Prod.snd hh; dsimp [boundaryUnitSquareRaw] at hy; linarith
private theorem boundaryUnitSquareRaw_surjective : Function.Surjective boundaryUnitSquareRaw := by
  intro z
  let x : Interval := ⟨(z.val.1+1)/2,⟨by linarith [z.property.1.1],by linarith [z.property.1.2]⟩⟩
  let y : Interval := ⟨(z.val.2+1)/2,⟨by linarith [z.property.2.1],by linarith [z.property.2.2]⟩⟩
  refine ⟨(x,y),?_⟩
  apply Subtype.ext
  apply Prod.ext <;> dsimp [boundaryUnitSquareRaw,x,y] <;> ring
private theorem boundaryUnitSquareRaw_continuous : Continuous boundaryUnitSquareRaw := by
  apply Continuous.subtype_mk
  exact (((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const).prodMk
    (((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const)
private theorem raw_left (t : Interval) : boundaryUnitSquareRaw (0,t)=squareLeftSeam t := by
  apply Subtype.ext; apply Prod.ext <;> norm_num [boundaryUnitSquareRaw,squareLeftSeam]
private theorem raw_right (t : Interval) : boundaryUnitSquareRaw (1,unitInterval.symm t)=squareRightSeam t := by
  apply Subtype.ext; apply Prod.ext <;> dsimp [boundaryUnitSquareRaw,squareRightSeam,unitInterval.symm] <;> ring

/-- Glue the two actual square disk charts with their prescribed two seam
lifts. The complete collision relation, including all corners, is exactly
the fixed crossed-end two-rectangle cylinder relation. -/
theorem square_pair_prescribed_seams_cylinder_edge_ranges
    {E : Type} [TopologicalSpace E] [T2Space E] (A B : Set E)
    (D₀ : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ A)
    (D₁ : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ B)
    (η δ : Interval → E)
    (h₀L : ∀ t, (D₀ (squareLeftSeam t)).val=η t)
    (h₁L : ∀ t, (D₁ (squareLeftSeam t)).val=η t)
    (h₀R : ∀ t, (D₀ (squareRightSeam t)).val=δ t)
    (h₁R : ∀ t, (D₁ (squareRightSeam t)).val=δ t)
    (hinter : A ∩ B=Set.range η ∪ Set.range δ) :
    ∃ H : Circle × Interval ≃ₜ ↥(A ∪ B), ∀ r : Interval,
      Set.range (fun z : Circle => (H (z,r)).val)=
        Set.range (fun t : Interval => (D₀ (boundaryUnitSquareRaw (t,r))).val) ∪
        Set.range (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,r))).val) := by
  let j₀ (p : Interval × Interval) : E := (D₀ (boundaryUnitSquareRaw p)).val
  let j₁ (p : Interval × Interval) : E := (D₁ (boundaryUnitSquareRaw (unitInterval.symm p.1,p.2))).val
  have hj₀inj : Function.Injective j₀ :=
    Subtype.val_injective.comp (D₀.injective.comp boundaryUnitSquareRaw_injective)
  have hj₁inj : Function.Injective j₁ := by
    intro p q h
    have he := boundaryUnitSquareRaw_injective (D₁.injective (Subtype.ext h))
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    exact Prod.ext (unitInterval.symm_inj.mp hfst) hsnd
  have hcross (p q : Interval × Interval) : j₀ p=j₁ q ↔
      p.2=q.2 ∧ ((p.1=0 ∧ q.1=1) ∨ (p.1=1 ∧ q.1=0)) := by
    constructor
    · intro h
      have hi : j₀ p ∈ A ∩ B := ⟨(D₀ _).property,h ▸ (D₁ _).property⟩
      rw [hinter] at hi
      rcases hi with ⟨t,ht⟩ | ⟨t,ht⟩
      · have he₀ : boundaryUnitSquareRaw p=squareLeftSeam t := D₀.injective (Subtype.ext (ht.symm.trans (h₀L t).symm))
        have he₁ : boundaryUnitSquareRaw (unitInterval.symm q.1,q.2)=squareLeftSeam t :=
          D₁.injective (Subtype.ext (h.symm.trans (ht.symm.trans (h₁L t).symm)))
        rw [← raw_left t] at he₀ he₁
        have hp := boundaryUnitSquareRaw_injective he₀
        have hq := boundaryUnitSquareRaw_injective he₁
        have hq1 : q.1=1 := by
          have he := congrArg Prod.fst hq
          simpa only [unitInterval.symm_eq_zero] using he
        exact ⟨(congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm,
          Or.inl ⟨congrArg Prod.fst hp,hq1⟩⟩
      · have he₀ : boundaryUnitSquareRaw p=squareRightSeam t := D₀.injective (Subtype.ext (ht.symm.trans (h₀R t).symm))
        have he₁ : boundaryUnitSquareRaw (unitInterval.symm q.1,q.2)=squareRightSeam t :=
          D₁.injective (Subtype.ext (h.symm.trans (ht.symm.trans (h₁R t).symm)))
        rw [← raw_right t] at he₀ he₁
        have hp := boundaryUnitSquareRaw_injective he₀
        have hq := boundaryUnitSquareRaw_injective he₁
        have hq0 : q.1=0 := by
          have he := congrArg Prod.fst hq
          simpa only [unitInterval.symm_eq_one] using he
        exact ⟨(congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm,
          Or.inr ⟨congrArg Prod.fst hp,hq0⟩⟩
    · rintro ⟨hyr,⟨h0,h1⟩ | ⟨h1,h0⟩⟩
      · change (D₀ (boundaryUnitSquareRaw p)).val=(D₁ (boundaryUnitSquareRaw (unitInterval.symm q.1,q.2))).val
        have hp : p=(0,p.2) := Prod.ext h0 rfl
        have hq : (unitInterval.symm q.1,q.2)=(0,p.2) := by simp [h1,← hyr]
        rw [hp,hq,raw_left,h₀L,h₁L]
      · change (D₀ (boundaryUnitSquareRaw p)).val=(D₁ (boundaryUnitSquareRaw (unitInterval.symm q.1,q.2))).val
        have hp : p=(1,p.2) := Prod.ext h1 rfl
        have hq : (unitInterval.symm q.1,q.2)=(1,p.2) := by simp [h0,← hyr]
        have hed : boundaryUnitSquareRaw (1,p.2)=squareRightSeam (unitInterval.symm p.2) := by
          rw [← raw_right,unitInterval.symm_symm]
        rw [hp,hq,hed,h₀R,h₁R]
  let J : C(TwoCylinderRectangles,E) := ⟨fun x => if x.2 then j₁ x.1 else j₀ x.1,by
    apply continuous_prod_of_discrete_right.mpr
    intro b
    cases b
    · exact continuous_subtype_val.comp (D₀.continuous.comp boundaryUnitSquareRaw_continuous)
    · exact continuous_subtype_val.comp (D₁.continuous.comp (boundaryUnitSquareRaw_continuous.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)))⟩
  have hc (x y : TwoCylinderRectangles) : J x=J y ↔ twoRectangleCylinderRel x y := by
    cases hx : x.2 <;> cases hy : y.2 <;>
      simp only [J,ContinuousMap.coe_mk,hx,hy,Bool.false_eq_true,↓reduceIte,twoRectangleCylinderRel] <;> simp
    · exact ⟨fun h => ⟨congrArg Prod.snd (hj₀inj h),congrArg Prod.fst (hj₀inj h)⟩,
        fun h => congrArg j₀ (Prod.ext h.2 h.1)⟩
    · exact hcross x.1 y.1
    · rw [eq_comm,hcross]
      constructor
      · rintro ⟨h,ha | hb⟩
        · exact ⟨h.symm,Or.inr ⟨ha.2,ha.1⟩⟩
        · exact ⟨h.symm,Or.inl ⟨hb.2,hb.1⟩⟩
      · rintro ⟨h,ha | hb⟩
        · exact ⟨h.symm,Or.inr ⟨ha.2,ha.1⟩⟩
        · exact ⟨h.symm,Or.inl ⟨hb.2,hb.1⟩⟩
    · exact ⟨fun h => ⟨congrArg Prod.snd (hj₁inj h),congrArg Prod.fst (hj₁inj h)⟩,
        fun h => congrArg j₁ (Prod.ext h.2 h.1)⟩
  have hr : Set.range J=A ∪ B := by
    ext e
    constructor
    · rintro ⟨x,rfl⟩
      cases hb : x.2
      · exact Or.inl (by simpa only [J,ContinuousMap.coe_mk,hb,Bool.false_eq_true,↓reduceIte] using (D₀ (boundaryUnitSquareRaw x.1)).property)
      · exact Or.inr (by simpa only [J,ContinuousMap.coe_mk,hb,↓reduceIte] using (D₁ (boundaryUnitSquareRaw (unitInterval.symm x.1.1,x.1.2))).property)
    · intro he
      rcases he with he | he
      · obtain ⟨p,hp⟩ := boundaryUnitSquareRaw_surjective (D₀.symm ⟨e,he⟩)
        refine ⟨(p,false),?_⟩
        change (D₀ (boundaryUnitSquareRaw p)).val=e
        rw [hp,D₀.apply_symm_apply]
      · obtain ⟨p,hp⟩ := boundaryUnitSquareRaw_surjective (D₁.symm ⟨e,he⟩)
        refine ⟨((unitInterval.symm p.1,p.2),true),?_⟩
        change (D₁ (boundaryUnitSquareRaw (unitInterval.symm (unitInterval.symm p.1),p.2))).val=e
        rw [unitInterval.symm_symm,hp,D₁.apply_symm_apply]
  let F : TwoRectangleCylinder → E := Quot.lift J (fun x y hxy => (hc x y).mpr hxy)
  have hF : Continuous F := continuous_quot_lift _ J.continuous
  have hinj : Function.Injective F := by
    intro x y
    induction x using Quot.inductionOn with | h x =>
      induction y using Quot.inductionOn with | h y =>
        intro hxy
        exact Quot.sound ((hc x y).mp hxy)
  have hFr : Set.range F=A ∪ B := by
    rw [← hr]
    ext e
    constructor
    · rintro ⟨x,rfl⟩
      induction x using Quot.inductionOn with | h x => exact ⟨x,rfl⟩
    · rintro ⟨x,rfl⟩; exact ⟨Quot.mk twoRectangleCylinderRel x,rfl⟩
  let G : TwoRectangleCylinder → ↥(A ∪ B) := fun x => ⟨F x,hFr ▸ Set.mem_range_self x⟩
  have hG : Continuous G := hF.subtype_mk _
  have hbij : Function.Bijective G := by
    constructor
    · intro x y h; exact hinj (congrArg Subtype.val h)
    · intro y
      have hy : y.val ∈ Set.range F := by rw [hFr]; exact y.property
      obtain ⟨x,hx⟩ := hy
      exact ⟨x,Subtype.ext hx⟩
  let H := (Equiv.ofBijective G hbij).toHomeomorphOfContinuousClosed hG hG.isClosedMap
  obtain ⟨K,hK⟩ := two_rectangle_glued_quotient_homeomorph_cylinder
  let HT := K.symm.trans H
  have hrep (q : TwoRectangleCylinder) : ∃ x, Quot.mk twoRectangleCylinderRel x=q := by
    induction q using Quot.inductionOn with | h x => exact ⟨x,rfl⟩
  have hmap (x : TwoCylinderRectangles) : (HT (K (Quot.mk twoRectangleCylinderRel x))).val=J x := by
    change (H (K.symm (K (Quot.mk twoRectangleCylinderRel x)))).val=J x
    rw [K.symm_apply_apply]
    rfl
  refine ⟨HT,?_⟩
  intro r
  ext e
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨x,hx⟩ := hrep (K.symm (z,r))
    have hkx : K (Quot.mk twoRectangleCylinderRel x)=(z,r) := by rw [hx,K.apply_symm_apply]
    have hxr : x.1.2=r := (hK x).symm.trans (congrArg Prod.snd hkx)
    have he : J x=e := by rw [← hmap x,hkx]; exact hz
    cases hb : x.2
    · left
      refine ⟨x.1.1,?_⟩
      change j₀ (x.1.1,r)=e
      change (if x.2 then j₁ x.1 else j₀ x.1)=e at he
      rw [hb] at he
      change j₀ x.1=e at he
      have hxpair : x.1=(x.1.1,r) := Prod.ext rfl hxr
      exact (congrArg j₀ hxpair).symm.trans he
    · right
      refine ⟨x.1.1,?_⟩
      change j₁ (x.1.1,r)=e
      change (if x.2 then j₁ x.1 else j₀ x.1)=e at he
      rw [hb] at he
      change j₁ x.1=e at he
      have hxpair : x.1=(x.1.1,r) := Prod.ext rfl hxr
      exact (congrArg j₁ hxpair).symm.trans he
  · rintro (⟨t,ht⟩ | ⟨t,ht⟩)
    · let x : TwoCylinderRectangles := ((t,r),false)
      let p := K (Quot.mk twoRectangleCylinderRel x)
      have hp : p=(p.1,r) := Prod.ext rfl (hK x)
      refine ⟨p.1,?_⟩
      change (HT (p.1,r)).val=e
      rw [← hp]
      change (HT (K (Quot.mk twoRectangleCylinderRel x))).val=e
      rw [hmap]
      exact ht
    · let x : TwoCylinderRectangles := ((t,r),true)
      let p := K (Quot.mk twoRectangleCylinderRel x)
      have hp : p=(p.1,r) := Prod.ext rfl (hK x)
      refine ⟨p.1,?_⟩
      change (HT (p.1,r)).val=e
      rw [← hp]
      change (HT (K (Quot.mk twoRectangleCylinderRel x))).val=e
      rw [hmap]
      exact ht
end CurveComplex
#print axioms CurveComplex.square_pair_prescribed_seams_cylinder_edge_ranges
