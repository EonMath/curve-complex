import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualPositivePortsRectangleProducer
namespace CurveComplex
open Set Schoenflies
set_option maxHeartbeats 3500000

/-- Glue ACTUALLY constructed upper and lower rectangles on their literal
middle edge. The resulting full strip preserves the longitudinal center
clock, and its whole image is exactly the union of the actual rectangles. -/
theorem actual_opposite_rectangles_literal_center_full_strip
    (U D : Interval × Interval → Plane)
    (hU : Topology.IsEmbedding U) (hD : Topology.IsEmbedding D)
    (C : Interval → Plane) (hU0 : ∀ t,U (t,0)=C t) (hD0 : ∀ t,D (t,0)=C t)
    (hUy : ∀ z,0≤U z 1) (hDy : ∀ z,D z 1≤0)
    (hUz : ∀ z,U z 1=0 ↔ z.2=0) (hDz : ∀ z,D z 1=0 ↔ z.2=0) :
    ∃ F : Interval × Icc (-1 : ℝ) 1 → Plane, Topology.IsEmbedding F ∧
      (∀ t,F (t,⟨0,by norm_num⟩)=C t) ∧
      (∀ z,F z=if (z.2:ℝ)≤0 then
        D (z.1,projIcc 0 1 zero_le_one (-(z.2:ℝ))) else
        U (z.1,projIcc 0 1 zero_le_one (z.2:ℝ))) ∧
      Set.range F=Set.range U ∪ Set.range D ∧
      (∀ z,F z 1=0 ↔ (z.2:ℝ)=0) := by
  let km : Interval × Icc (-1 : ℝ) 1 → Interval × Interval := fun z =>
    (z.1,projIcc 0 1 zero_le_one (-(z.2:ℝ)))
  let kp : Interval × Icc (-1 : ℝ) 1 → Interval × Interval := fun z =>
    (z.1,projIcc 0 1 zero_le_one (z.2:ℝ))
  have hkm : Continuous km := by dsimp [km]; fun_prop
  have hkp : Continuous kp := by dsimp [kp]; fun_prop
  let F : Interval × Icc (-1 : ℝ) 1 → Plane := fun z =>
    if (z.2:ℝ)≤0 then D (km z) else U (kp z)
  have hkcminus (z) (hz : (z.2:ℝ)≤0) : (km z).2.val=-(z.2:ℝ) := by
    have hmem : -(z.2:ℝ)∈Icc (0:ℝ) 1 := ⟨by linarith,by linarith [z.2.property.1]⟩
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one hmem)
  have hkcplus (z) (hz : 0≤(z.2:ℝ)) : (kp z).2.val=(z.2:ℝ) :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hz,z.2.property.2⟩)
  have hFc : Continuous F := by
    apply continuous_if_le (by fun_prop) continuous_const
      (hD.continuous.comp hkm).continuousOn (hU.continuous.comp hkp).continuousOn
    intro z hz
    have hm : km z=(z.1,0) := Prod.ext rfl (Subtype.ext (by rw [hkcminus z hz.le,hz]; norm_num))
    have hp : kp z=(z.1,0) := Prod.ext rfl (Subtype.ext (by rw [hkcplus z hz.ge,hz]; norm_num))
    change D (km z)=U (kp z)
    rw [hm,hp,hD0,hU0]
  have hFi : Function.Injective F := by
    intro z w he
    by_cases hz : (z.2:ℝ)≤0 <;> by_cases hw : (w.2:ℝ)≤0
    · simp only [F,ite_eq_left hz,ite_eq_left hw] at he
      have hh := hD.injective he
      apply Prod.ext
      · have hfirst := congrArg Prod.fst hh
        exact hfirst
      · apply Subtype.ext
        have hh2 := congrArg (fun v => (v.2:ℝ)) hh
        rw [hkcminus z hz,hkcminus w hw] at hh2
        linarith
    · simp only [F,ite_eq_left hz,ite_eq_right hw] at he
      have hheight := congrArg (fun p : Plane => p 1) he
      have hu := hUy (kp w)
      have hd := hDy (km z)
      have he0 : U (kp w) 1=0 := by linarith
      have hh := congrArg Subtype.val ((hUz _).mp he0)
      rw [hkcplus w (le_of_not_ge hw)] at hh
      change (w.2:ℝ)=0 at hh
      exact False.elim (hw (by linarith))
    · simp only [F,ite_eq_right hz,ite_eq_left hw] at he
      have hheight := congrArg (fun p : Plane => p 1) he
      have hu := hUy (kp z)
      have hd := hDy (km w)
      have he0 : U (kp z) 1=0 := by linarith
      have hh := congrArg Subtype.val ((hUz _).mp he0)
      rw [hkcplus z (le_of_not_ge hz)] at hh
      change (z.2:ℝ)=0 at hh
      exact False.elim (hz (by linarith))
    · simp only [F,ite_eq_right hz,ite_eq_right hw] at he
      have hh := hU.injective he
      apply Prod.ext
      · have hfirst := congrArg Prod.fst hh
        exact hfirst
      · apply Subtype.ext
        have hh2 := congrArg (fun v => (v.2:ℝ)) hh
        rw [hkcplus z (le_of_not_ge hz),hkcplus w (le_of_not_ge hw)] at hh2
        exact hh2
  have hF : Topology.IsEmbedding F := (hFc.isClosedEmbedding hFi).isEmbedding
  refine ⟨F,hF,?_,fun _ => rfl,?_,?_⟩
  · intro t
    change (if (0:ℝ)≤0 then D (km (t,⟨0,by norm_num⟩)) else _) = C t
    rw [ite_eq_left (le_refl _)]
    have hm : km (t,⟨0,by norm_num⟩)=(t,0) :=
      Prod.ext rfl (Subtype.ext (by simp [km,projIcc_of_mem]))
    rw [hm,hD0]
  · ext y
    constructor
    · rintro ⟨z,rfl⟩
      by_cases hz : (z.2:ℝ)≤0
      · exact Or.inr ⟨km z,by simp [F,hz]⟩
      · exact Or.inl ⟨kp z,by simp [F,hz]⟩
    · rintro (⟨z,rfl⟩|⟨z,rfl⟩)
      · let w : Icc (-1 : ℝ) 1 := ⟨z.2,⟨by linarith [z.2.property.1],z.2.property.2⟩⟩
        refine ⟨(z.1,w),?_⟩
        by_cases hz : z.2=0
        · have hw : (w:ℝ)=0 := congrArg Subtype.val hz
          simp only [F,ite_eq_left (show (w:ℝ)≤0 by linarith)]
          have hm : km (z.1,w)=(z.1,0) := Prod.ext rfl
            (Subtype.ext (by rw [hkcminus _ (by linarith),hw]; norm_num))
          rw [hm,hD0]
          have hzz : z=(z.1,0) := Prod.ext rfl hz
          rw [hzz,hU0]
        · have hwpos : 0<(w:ℝ) := lt_of_le_of_ne z.2.property.1
            (fun he => hz (Subtype.ext he.symm))
          simp only [F,ite_eq_right (not_le_of_gt hwpos)]
          apply congrArg U
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact hkcplus _ hwpos.le
      · let w : Icc (-1 : ℝ) 1 := ⟨-(z.2:ℝ),⟨by linarith [z.2.property.2],by linarith [z.2.property.1]⟩⟩
        refine ⟨(z.1,w),?_⟩
        have hw : (w:ℝ)≤0 := by dsimp [w]; linarith [z.2.property.1]
        simp only [F,ite_eq_left hw]
        apply congrArg D
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          rw [hkcminus _ hw]
          dsimp [w]
          ring
  · intro z
    by_cases hz : (z.2:ℝ)≤0
    · simp only [F,ite_eq_left hz,hDz]
      constructor
      · intro hh
        have hv := congrArg Subtype.val hh
        rw [hkcminus z hz] at hv
        change -(z.2:ℝ)=0 at hv
        linarith
      · intro hh
        apply Subtype.ext
        rw [hkcminus z hz,hh]
        norm_num
    · simp only [F,ite_eq_right hz,hUz]
      constructor
      · intro hh
        have hv := congrArg Subtype.val hh
        rw [hkcplus z (le_of_not_ge hz)] at hv
        exact hv
      · intro hh
        apply Subtype.ext
        rw [hkcplus z (le_of_not_ge hz),hh]
        norm_num
end CurveComplex
