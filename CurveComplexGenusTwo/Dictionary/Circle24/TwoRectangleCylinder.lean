import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 6000000
private instance : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩

abbrev TwoCylinderRectangles := (Interval × Interval) × Bool

def twoRectangleCylinderRel (x y : TwoCylinderRectangles) : Prop :=
  x.1.2=y.1.2 ∧ ((x.1.1=y.1.1 ∧ x.2=y.2) ∨
    (x.1.1=0 ∧ y.1.1=1 ∧ x.2≠y.2) ∨
    (x.1.1=1 ∧ y.1.1=0 ∧ x.2≠y.2))

abbrev TwoRectangleCylinder := Quot twoRectangleCylinderRel

private theorem addCircle_two_closed_interval_collision
    (x y : ℝ) (hx : x ∈ Icc (0:ℝ) 2) (hy : y ∈ Icc (0:ℝ) 2) :
    (x:AddCircle (2:ℝ))=(y:AddCircle (2:ℝ)) ↔
      x=y ∨ (x=0 ∧ y=2) ∨ (x=2 ∧ y=0) := by
  constructor
  · intro h
    by_cases hx2 : x=2
    · by_cases hy2 : y=2
      · exact Or.inl (hx2.trans hy2.symm)
      · have hyl : y<2 := lt_of_le_of_ne hy.2 hy2
        have hyzero : y=0 := by
          have hc : (0:AddCircle (2:ℝ))=(y:AddCircle (2:ℝ)) := by
            simpa only [hx2,AddCircle.coe_period] using h
          exact ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=(0:ℝ)) (p:=(2:ℝ))
            (by norm_num) (by simpa using ⟨hy.1,hyl⟩)).mp hc).symm
        exact Or.inr (Or.inr ⟨hx2,hyzero⟩)
    · by_cases hy2 : y=2
      · have hxl : x<2 := lt_of_le_of_ne hx.2 hx2
        have hxzero : x=0 := by
          have hc : (x:AddCircle (2:ℝ))=(0:AddCircle (2:ℝ)) := by
            simpa only [hy2,AddCircle.coe_period] using h
          exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=(0:ℝ)) (p:=(2:ℝ))
            (by simpa using ⟨hx.1,hxl⟩) (by norm_num)).mp hc
        exact Or.inr (Or.inl ⟨hxzero,hy2⟩)
      · exact Or.inl ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a:=(0:ℝ)) (p:=(2:ℝ))
          (by simpa using ⟨hx.1,lt_of_le_of_ne hx.2 hx2⟩)
          (by simpa using ⟨hy.1,lt_of_le_of_ne hy.2 hy2⟩)).mp h)
  · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp [AddCircle.coe_period]

private def twoRectangleAngle (x : TwoCylinderRectangles) : ℝ :=
  x.1.1.val + if x.2 then 1 else 0

private theorem angle_bounds (x : TwoCylinderRectangles) : twoRectangleAngle x ∈ Icc (0:ℝ) 2 := by
  have h : 0 ≤ x.1.1.val ∧ x.1.1.val ≤ 1 := x.1.1.property
  cases hb : x.2 <;> simp [twoRectangleAngle,hb] <;> constructor <;> linarith [h.1,h.2]

private theorem angle_collision (x y : TwoCylinderRectangles) :
    (twoRectangleAngle x:AddCircle (2:ℝ))=(twoRectangleAngle y:AddCircle (2:ℝ)) ↔
      (x.1.1=y.1.1 ∧ x.2=y.2) ∨
      (x.1.1=0 ∧ y.1.1=1 ∧ x.2≠y.2) ∨
      (x.1.1=1 ∧ y.1.1=0 ∧ x.2≠y.2) := by
  rw [addCircle_two_closed_interval_collision _ _ (angle_bounds x) (angle_bounds y)]
  have hx0 : 0 ≤ x.1.1.val := x.1.1.property.1
  have hx1 : x.1.1.val ≤ 1 := x.1.1.property.2
  have hy0 : 0 ≤ y.1.1.val := y.1.1.property.1
  have hy1 : y.1.1.val ≤ 1 := y.1.1.property.2
  cases hxb : x.2 <;> cases hyb : y.2 <;>
    simp [twoRectangleAngle,hxb,hyb] <;> constructor
  all_goals intro h
  · rcases h with h | ⟨h0,h2⟩ | ⟨h2,h0⟩
    · exact Subtype.ext h
    · exfalso; linarith [hy1]
    · exfalso; linarith [hx1]
  · exact Or.inl (congrArg Subtype.val h)
  · rcases h with h | ⟨h0,h2⟩ | ⟨h2,h0⟩
    · right
      exact ⟨Subtype.ext (by change _ = (1:ℝ); linarith),Subtype.ext (by change _ = (0:ℝ); linarith)⟩
    · left
      exact ⟨h0,Subtype.ext (by change _ = (1:ℝ); linarith)⟩
    · exfalso; linarith [hx1]
  · rcases h with ⟨h0,h1⟩ | ⟨h1,h0⟩
    · exact Or.inr (Or.inl ⟨h0,by
        have hh := congrArg Subtype.val h1; change y.1.1.val=1 at hh; linarith⟩)
    · left
      have hh0 := congrArg Subtype.val h0
      have hh1 := congrArg Subtype.val h1
      change y.1.1.val=0 at hh0
      change x.1.1.val=1 at hh1
      linarith
  · rcases h with h | ⟨h0,h2⟩ | ⟨h2,h0⟩
    · left
      exact ⟨Subtype.ext (by change _ = (0:ℝ); linarith),Subtype.ext (by change _ = (1:ℝ); linarith)⟩
    · exfalso; linarith [hx0]
    · right
      exact ⟨Subtype.ext (by change _ = (1:ℝ); linarith),h0⟩
  · rcases h with ⟨h0,h1⟩ | ⟨h1,h0⟩
    · left
      have hh0 := congrArg Subtype.val h0
      have hh1 := congrArg Subtype.val h1
      change x.1.1.val=0 at hh0
      change y.1.1.val=1 at hh1
      linarith
    · exact Or.inr (Or.inr ⟨by
        have hh := congrArg Subtype.val h1; change x.1.1.val=1 at hh; linarith,
        h0⟩)
  · rcases h with h | ⟨h0,h2⟩ | ⟨h2,h0⟩
    · exact Subtype.ext (by linarith)
    · exfalso; linarith [hx0]
    · exfalso; linarith [hy0]
  · left
    have hh := congrArg Subtype.val h
    linarith

/-- The actual two-rectangle gluing with crossed end identifications is the
closed cylinder. The radial coordinate, including both boundary circles,
is retained exactly. -/
theorem two_rectangle_glued_quotient_homeomorph_cylinder :
    ∃ H : TwoRectangleCylinder ≃ₜ Circle × Interval,
      ∀ x : TwoCylinderRectangles, (H (Quot.mk twoRectangleCylinderRel x)).2=x.1.2 := by
  let e : AddCircle (2:ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
  let J : C(TwoCylinderRectangles,Circle × Interval) :=
    ⟨fun x => (e (twoRectangleAngle x:AddCircle (2:ℝ)),x.1.2),by
      apply continuous_prod_of_discrete_right.mpr
      intro b
      have hang : Continuous (fun x : Interval × Interval => twoRectangleAngle (x,b)) := by
        change Continuous (fun x : Interval × Interval => x.1.val + (if b then 1 else 0))
        exact (continuous_subtype_val.comp continuous_fst).add continuous_const
      exact (e.continuous.comp ((AddCircle.continuous_mk' 2).comp hang)).prodMk continuous_snd⟩
  have hcollision (x y) : J x=J y ↔ twoRectangleCylinderRel x y := by
    change (e (twoRectangleAngle x:AddCircle (2:ℝ)),x.1.2)=
      (e (twoRectangleAngle y:AddCircle (2:ℝ)),y.1.2) ↔ _
    rw [Prod.mk.injEq,e.injective.eq_iff,angle_collision]
    exact and_comm
  have hJsurj : Function.Surjective J := by
    rintro ⟨z,t⟩
    obtain ⟨a,ha,hae⟩ := AddCircle.eq_coe_Ico (e.symm z)
    by_cases hle : a ≤ 1
    · let r : Interval := ⟨a,⟨ha.1,hle⟩⟩
      refine ⟨((r,t),false),?_⟩
      apply Prod.ext
      · change e ((a+0:ℝ):AddCircle (2:ℝ))=z
        rw [add_zero,hae,e.apply_symm_apply]
      · rfl
    · let r : Interval := ⟨a-1,⟨by linarith,by linarith [ha.2]⟩⟩
      refine ⟨((r,t),true),?_⟩
      apply Prod.ext
      · change e ((a-1+1:ℝ):AddCircle (2:ℝ))=z
        rw [sub_add_cancel,hae,e.apply_symm_apply]
      · rfl
  let F : TwoRectangleCylinder → Circle × Interval :=
    Quot.lift J (fun x y hxy => (hcollision x y).mpr hxy)
  have hF : Continuous F := continuous_quot_lift _ J.continuous
  have hFbij : Function.Bijective F := by
    constructor
    · intro x y
      induction x using Quot.inductionOn with | h x =>
        induction y using Quot.inductionOn with | h y =>
          intro hxy
          exact Quot.sound ((hcollision x y).mp hxy)
    · intro z
      obtain ⟨x,hx⟩ := hJsurj z
      exact ⟨Quot.mk twoRectangleCylinderRel x,hx⟩
  let H := (Equiv.ofBijective F hFbij).toHomeomorphOfContinuousClosed hF hF.isClosedMap
  exact ⟨H,fun _ => rfl⟩

end CurveComplex
#print axioms CurveComplex.two_rectangle_glued_quotient_homeomorph_cylinder
