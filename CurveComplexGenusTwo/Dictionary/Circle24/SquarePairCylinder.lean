import CurveComplexGenusTwo.Dictionary.Circle24.TwoRectangleCylinder
import CurveComplexGenusTwo.Dictionary.Circle24.ActualPrescribedSquareSeam
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 9000000
noncomputable def unitSquareRaw (p : Interval × Interval) : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1 :=
  ⟨(2*p.1.val-1,2*p.2.val-1),⟨⟨by linarith [p.1.property.1],by linarith [p.1.property.2]⟩,
    ⟨by linarith [p.2.property.1],by linarith [p.2.property.2]⟩⟩⟩
private theorem unitSquareRaw_injective : Function.Injective unitSquareRaw := by
  intro p q h
  have hh := congrArg Subtype.val h
  apply Prod.ext <;> apply Subtype.ext
  · have hx := congrArg Prod.fst hh; dsimp [unitSquareRaw] at hx; linarith
  · have hy := congrArg Prod.snd hh; dsimp [unitSquareRaw] at hy; linarith
private theorem unitSquareRaw_surjective : Function.Surjective unitSquareRaw := by
  intro z
  let x : Interval := ⟨(z.val.1+1)/2,⟨by linarith [z.property.1.1],by linarith [z.property.1.2]⟩⟩
  let y : Interval := ⟨(z.val.2+1)/2,⟨by linarith [z.property.2.1],by linarith [z.property.2.2]⟩⟩
  refine ⟨(x,y),?_⟩
  apply Subtype.ext
  apply Prod.ext <;> dsimp [unitSquareRaw,x,y] <;> ring
private theorem unitSquareRaw_continuous : Continuous unitSquareRaw := by
  apply Continuous.subtype_mk
  exact (((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const).prodMk
    (((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const)
private theorem raw_left (t : Interval) : unitSquareRaw (0,t)=squareLeftSeam t := by
  apply Subtype.ext; apply Prod.ext <;> norm_num [unitSquareRaw,squareLeftSeam]
private theorem raw_right (t : Interval) : unitSquareRaw (1,unitInterval.symm t)=squareRightSeam t := by
  apply Subtype.ext; apply Prod.ext <;> dsimp [unitSquareRaw,squareRightSeam,unitInterval.symm] <;> ring

/-- Glue the two actual square disk charts with their prescribed two seam
lifts. The complete collision relation, including all corners, is exactly
the fixed crossed-end two-rectangle cylinder relation. -/
theorem square_pair_prescribed_seams_cylinder
    {E : Type} [TopologicalSpace E] [T2Space E] (A B : Set E)
    (D₀ : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ A)
    (D₁ : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ B)
    (η δ : Interval → E)
    (h₀L : ∀ t, (D₀ (squareLeftSeam t)).val=η t)
    (h₁L : ∀ t, (D₁ (squareLeftSeam t)).val=η t)
    (h₀R : ∀ t, (D₀ (squareRightSeam t)).val=δ t)
    (h₁R : ∀ t, (D₁ (squareRightSeam t)).val=δ t)
    (hinter : A ∩ B=Set.range η ∪ Set.range δ) :
    Nonempty (Circle × Interval ≃ₜ ↥(A ∪ B)) := by
  let j₀ (p : Interval × Interval) : E := (D₀ (unitSquareRaw p)).val
  let j₁ (p : Interval × Interval) : E := (D₁ (unitSquareRaw (unitInterval.symm p.1,p.2))).val
  have hj₀inj : Function.Injective j₀ :=
    Subtype.val_injective.comp (D₀.injective.comp unitSquareRaw_injective)
  have hj₁inj : Function.Injective j₁ := by
    intro p q h
    have he := unitSquareRaw_injective (D₁.injective (Subtype.ext h))
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
      · have he₀ : unitSquareRaw p=squareLeftSeam t := D₀.injective (Subtype.ext (ht.symm.trans (h₀L t).symm))
        have he₁ : unitSquareRaw (unitInterval.symm q.1,q.2)=squareLeftSeam t :=
          D₁.injective (Subtype.ext (h.symm.trans (ht.symm.trans (h₁L t).symm)))
        rw [← raw_left t] at he₀ he₁
        have hp := unitSquareRaw_injective he₀
        have hq := unitSquareRaw_injective he₁
        have hq1 : q.1=1 := by
          have he := congrArg Prod.fst hq
          simpa only [unitInterval.symm_eq_zero] using he
        exact ⟨(congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm,
          Or.inl ⟨congrArg Prod.fst hp,hq1⟩⟩
      · have he₀ : unitSquareRaw p=squareRightSeam t := D₀.injective (Subtype.ext (ht.symm.trans (h₀R t).symm))
        have he₁ : unitSquareRaw (unitInterval.symm q.1,q.2)=squareRightSeam t :=
          D₁.injective (Subtype.ext (h.symm.trans (ht.symm.trans (h₁R t).symm)))
        rw [← raw_right t] at he₀ he₁
        have hp := unitSquareRaw_injective he₀
        have hq := unitSquareRaw_injective he₁
        have hq0 : q.1=0 := by
          have he := congrArg Prod.fst hq
          simpa only [unitInterval.symm_eq_one] using he
        exact ⟨(congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm,
          Or.inr ⟨congrArg Prod.fst hp,hq0⟩⟩
    · rintro ⟨hyr,⟨h0,h1⟩ | ⟨h1,h0⟩⟩
      · change (D₀ (unitSquareRaw p)).val=(D₁ (unitSquareRaw (unitInterval.symm q.1,q.2))).val
        have hp : p=(0,p.2) := Prod.ext h0 rfl
        have hq : (unitInterval.symm q.1,q.2)=(0,p.2) := by simp [h1,← hyr]
        rw [hp,hq,raw_left,h₀L,h₁L]
      · change (D₀ (unitSquareRaw p)).val=(D₁ (unitSquareRaw (unitInterval.symm q.1,q.2))).val
        have hp : p=(1,p.2) := Prod.ext h1 rfl
        have hq : (unitInterval.symm q.1,q.2)=(1,p.2) := by simp [h0,← hyr]
        have hed : unitSquareRaw (1,p.2)=squareRightSeam (unitInterval.symm p.2) := by
          rw [← raw_right,unitInterval.symm_symm]
        rw [hp,hq,hed,h₀R,h₁R]
  let J : C(TwoCylinderRectangles,E) := ⟨fun x => if x.2 then j₁ x.1 else j₀ x.1,by
    apply continuous_prod_of_discrete_right.mpr
    intro b
    cases b
    · exact continuous_subtype_val.comp (D₀.continuous.comp unitSquareRaw_continuous)
    · exact continuous_subtype_val.comp (D₁.continuous.comp (unitSquareRaw_continuous.comp
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
      · exact Or.inl (by simpa only [J,ContinuousMap.coe_mk,hb,Bool.false_eq_true,↓reduceIte] using (D₀ (unitSquareRaw x.1)).property)
      · exact Or.inr (by simpa only [J,ContinuousMap.coe_mk,hb,↓reduceIte] using (D₁ (unitSquareRaw (unitInterval.symm x.1.1,x.1.2))).property)
    · intro he
      rcases he with he | he
      · obtain ⟨p,hp⟩ := unitSquareRaw_surjective (D₀.symm ⟨e,he⟩)
        refine ⟨(p,false),?_⟩
        change (D₀ (unitSquareRaw p)).val=e
        rw [hp,D₀.apply_symm_apply]
      · obtain ⟨p,hp⟩ := unitSquareRaw_surjective (D₁.symm ⟨e,he⟩)
        refine ⟨((unitInterval.symm p.1,p.2),true),?_⟩
        change (D₁ (unitSquareRaw (unitInterval.symm (unitInterval.symm p.1),p.2))).val=e
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
  exact ⟨K.symm.trans H⟩
end CurveComplex
#print axioms CurveComplex.square_pair_prescribed_seams_cylinder
