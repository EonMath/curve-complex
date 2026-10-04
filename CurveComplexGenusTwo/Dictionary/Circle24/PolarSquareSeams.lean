import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkPolarGluing
import Mathlib.Analysis.Normed.Group.Constructions
open Set Topology
namespace CurveComplex
noncomputable section
set_option maxHeartbeats 9000000

/-- The left and top sides of a square, parameterized over a single interval. -/
def polarSquareHalf (t : ℝ) : ℝ × ℝ :=
  if t≤1/2 then (-1,4*t-1) else (4*t-3,1)

def polarSquareBoundary (t : Interval) (b : Bool) : ℝ × ℝ :=
  if b then -(polarSquareHalf t.val) else polarSquareHalf t.val

def polarSquareMap (x : OneMarkPolarStrip) : ℝ × ℝ :=
  x.1.1.val • polarSquareBoundary x.1.2 x.2

private theorem polarSquareHalf_norm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖polarSquareHalf t‖=1 := by
  unfold polarSquareHalf
  split_ifs with h
  · rw [Prod.norm_mk,Real.norm_eq_abs,Real.norm_eq_abs]
    rw [abs_neg,abs_one,max_eq_left]
    exact abs_le.mpr ⟨by linarith [ht.1],by linarith⟩
  · rw [Prod.norm_mk,Real.norm_eq_abs,Real.norm_eq_abs,abs_one,max_eq_right]
    exact abs_le.mpr ⟨by linarith,by linarith [ht.2]⟩

private theorem polarSquareHalf_injective (t s : ℝ)
    (_ht : t ∈ Icc (0:ℝ) 1) (_hs : s ∈ Icc (0:ℝ) 1)
    (h : polarSquareHalf t=polarSquareHalf s) : t=s := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  unfold polarSquareHalf at h1 h2
  split_ifs at h1 h2 <;> dsimp at h1 h2 <;> linarith

private theorem polarSquareHalf_opposite (t s : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    polarSquareHalf t=-(polarSquareHalf s) ↔ (t=0 ∧ s=1) ∨ (t=1 ∧ s=0) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold polarSquareHalf at h1 h2
    by_cases htl : t≤1/2 <;> by_cases hsl : s≤1/2
    · simp only [ite_eq_left htl,ite_eq_left hsl,Prod.fst_neg,Prod.snd_neg] at h1 h2
      linarith
    · simp only [ite_eq_left htl,ite_eq_right hsl,Prod.fst_neg,Prod.snd_neg] at h1 h2
      exact Or.inl ⟨by linarith,by linarith⟩
    · simp only [ite_eq_right htl,ite_eq_left hsl,Prod.fst_neg,Prod.snd_neg] at h1 h2
      exact Or.inr ⟨by linarith,by linarith⟩
    · simp only [ite_eq_right htl,ite_eq_right hsl,Prod.fst_neg,Prod.snd_neg] at h1 h2
      linarith
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num [polarSquareHalf]

private theorem polarSquareBoundary_norm (t : Interval) (b : Bool) :
    ‖polarSquareBoundary t b‖=1 := by
  cases b <;> simp [polarSquareBoundary,polarSquareHalf_norm t.val t.property]

private theorem polarSquareBoundary_collision (s t : Interval) (b c : Bool) :
    polarSquareBoundary s b=polarSquareBoundary t c ↔
      (s=t ∧ b=c) ∨ (s=0 ∧ t=1 ∧ b≠c) ∨ (s=1 ∧ t=0 ∧ b≠c) := by
  cases b <;> cases c <;> simp only [polarSquareBoundary, Bool.false_eq_true,
    ↓reduceIte,neg_inj] <;> simp
  · constructor
    · intro h; exact Subtype.ext (polarSquareHalf_injective _ _ s.property t.property h)
    · rintro rfl; rfl
  · rw [polarSquareHalf_opposite _ _ s.property t.property]
    constructor
    · rintro (⟨h0,h1⟩ | ⟨h1,h0⟩)
      · exact Or.inl ⟨Subtype.ext h0,Subtype.ext h1⟩
      · exact Or.inr ⟨Subtype.ext h1,Subtype.ext h0⟩
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num
  · rw [neg_eq_iff_eq_neg,polarSquareHalf_opposite _ _ s.property t.property]
    constructor
    · rintro (⟨h0,h1⟩ | ⟨h1,h0⟩)
      · exact Or.inl ⟨Subtype.ext h0,Subtype.ext h1⟩
      · exact Or.inr ⟨Subtype.ext h1,Subtype.ext h0⟩
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num
  · constructor
    · intro h; exact Subtype.ext (polarSquareHalf_injective _ _ s.property t.property h)
    · rintro rfl; rfl

/-- A pointwise square model of the full one-mark polar cell. Its first half
outer edge is one vertical seam; the opposite sheet gives the other seam. -/
theorem polarSquareMap_collision (x y : OneMarkPolarStrip) :
    polarSquareMap x=polarSquareMap y ↔ oneMarkPolarRel x y := by
  have hn (x : OneMarkPolarStrip) : ‖polarSquareMap x‖=x.1.1.val := by
    rw [polarSquareMap,norm_smul,Real.norm_eq_abs,abs_of_nonneg x.1.1.property.1,
      polarSquareBoundary_norm,mul_one]
  constructor
  · intro h
    have hrval : x.1.1.val=y.1.1.val := by rw [← hn x,← hn y,h]
    have hr : x.1.1=y.1.1 := Subtype.ext hrval
    refine ⟨hr,?_⟩
    by_cases hz : x.1.1=0
    · exact Or.inl hz
    · right
      have hne : x.1.1.val≠0 := fun he => hz (Subtype.ext he)
      have hB : polarSquareBoundary x.1.2 x.2=polarSquareBoundary y.1.2 y.2 := by
        apply smul_right_injective (ℝ × ℝ) hne
        simpa only [polarSquareMap,hrval] using h
      exact (polarSquareBoundary_collision _ _ _ _).mp hB
  · rintro ⟨hr,hz | hB⟩
    · simp [polarSquareMap,← hr,hz]
    · unfold polarSquareMap
      rw [hr,(polarSquareBoundary_collision _ _ _ _).mpr hB]

private theorem polarSquareHalf_continuous : Continuous polarSquareHalf := by
  apply continuous_if_le continuous_id continuous_const
    (by fun_prop) (by fun_prop)
  intro t ht
  change t=1/2 at ht
  apply Prod.ext <;> dsimp <;> linarith

private theorem polarSquareMap_continuous : Continuous polarSquareMap := by
  apply continuous_prod_of_discrete_right.mpr
  intro b
  have ht : Continuous (fun x : Interval × Interval => polarSquareHalf x.2.val) :=
    polarSquareHalf_continuous.comp (continuous_subtype_val.comp continuous_snd)
  cases b
  · exact (continuous_subtype_val.comp continuous_fst).smul ht
  · exact (continuous_subtype_val.comp continuous_fst).smul ht.neg

private theorem polarSquareBoundary_surjective (z : ℝ × ℝ) (hz : ‖z‖=1) :
    ∃ t : Interval, ∃ b : Bool, polarSquareBoundary t b=z := by
  have hx : |z.1|≤1 := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs] at hz
    exact (le_max_left _ _).trans_eq hz
  have hy : |z.2|≤1 := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs] at hz
    exact (le_max_right _ _).trans_eq hz
  have hedge : |z.1|=1 ∨ |z.2|=1 := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs] at hz
    rcases le_total |z.1| |z.2| with h | h
    · exact Or.inr (by rwa [max_eq_right h] at hz)
    · exact Or.inl (by rwa [max_eq_left h] at hz)
  rcases abs_le.mp hx with ⟨hx0,hx1⟩
  rcases abs_le.mp hy with ⟨hy0,hy1⟩
  rcases hedge with he | he
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp he with he | he
    · let t : Interval := ⟨(1-z.2)/4,⟨by linarith,by linarith⟩⟩
      refine ⟨t,true,?_⟩
      have ht : t.val≤1/2 := by dsimp [t]; linarith
      simp only [polarSquareBoundary,↓reduceIte,polarSquareHalf,ite_eq_left ht]
      apply Prod.ext <;> dsimp [t] <;> linarith
    · let t : Interval := ⟨(z.2+1)/4,⟨by linarith,by linarith⟩⟩
      refine ⟨t,false,?_⟩
      have ht : t.val≤1/2 := by dsimp [t]; linarith
      simp only [polarSquareBoundary,Bool.false_eq_true,↓reduceIte,polarSquareHalf,ite_eq_left ht]
      apply Prod.ext <;> dsimp [t] <;> linarith
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp he with he | he
    · let t : Interval := ⟨(z.1+3)/4,⟨by linarith,by linarith⟩⟩
      refine ⟨t,false,?_⟩
      by_cases ht : t.val≤1/2
      · have hxt : z.1= -1 := by dsimp [t] at ht; linarith
        simp only [polarSquareBoundary,Bool.false_eq_true,↓reduceIte,polarSquareHalf,ite_eq_left ht]
        apply Prod.ext <;> dsimp [t] <;> linarith
      · simp only [polarSquareBoundary,Bool.false_eq_true,↓reduceIte,polarSquareHalf,ite_eq_right ht]
        apply Prod.ext <;> dsimp [t] <;> linarith
    · let t : Interval := ⟨(3-z.1)/4,⟨by linarith,by linarith⟩⟩
      refine ⟨t,true,?_⟩
      by_cases ht : t.val≤1/2
      · have hxt : z.1=1 := by dsimp [t] at ht; linarith
        simp only [polarSquareBoundary,↓reduceIte,polarSquareHalf,ite_eq_left ht]
        apply Prod.ext <;> dsimp [t] <;> linarith
      · simp only [polarSquareBoundary,↓reduceIte,polarSquareHalf,ite_eq_right ht]
        apply Prod.ext <;> dsimp [t] <;> linarith

/-- Explicit full polar-disk chart to a square; the formula is retained on all
representatives so attaching-edge parameterizations are not discarded. -/
theorem one_mark_polar_cell_square_chart :
    ∃ H : OneMarkPolarCell ≃ₜ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1),
      ∀ x : OneMarkPolarStrip, (H (Quot.mk oneMarkPolarRel x)).val=polarSquareMap x := by
  let R := Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  have hm (x : OneMarkPolarStrip) : polarSquareMap x ∈ R := by
    have hn : ‖polarSquareMap x‖≤1 := by
      rw [polarSquareMap,norm_smul,Real.norm_eq_abs,abs_of_nonneg x.1.1.property.1,
        polarSquareBoundary_norm,mul_one]
      exact x.1.1.property.2
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff] at hn
    exact ⟨abs_le.mp hn.1,abs_le.mp hn.2⟩
  let J : C(OneMarkPolarStrip,R) := ⟨fun x => ⟨polarSquareMap x,hm x⟩,
    polarSquareMap_continuous.subtype_mk _⟩
  have hJs : Function.Surjective J := by
    intro z
    by_cases hz : z.val=0
    · refine ⟨((0,0),false),?_⟩
      apply Subtype.ext
      simp [J,polarSquareMap,hz]
    · let r := ‖z.val‖
      have hr : 0<r := norm_pos_iff.mpr hz
      have hr1 : r≤1 := by
        change ‖z.val‖≤1
        rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff]
        exact ⟨abs_le.mpr z.property.1,abs_le.mpr z.property.2⟩
      have hn : ‖r⁻¹ • z.val‖=1 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
        exact inv_mul_cancel₀ (ne_of_gt hr)
      obtain ⟨t,b,htb⟩ := polarSquareBoundary_surjective (r⁻¹ • z.val) hn
      refine ⟨((⟨r,⟨hr.le,hr1⟩⟩,t),b),?_⟩
      apply Subtype.ext
      change r • polarSquareBoundary t b=z.val
      rw [htb,smul_smul,mul_inv_cancel₀ (ne_of_gt hr),one_smul]
  let F : OneMarkPolarCell → R := Quot.lift J (fun x y hxy =>
    Subtype.ext ((polarSquareMap_collision x y).mpr hxy))
  have hF : Continuous F := continuous_quot_lift _ J.continuous
  have hbij : Function.Bijective F := by
    constructor
    · intro x y
      induction x using Quot.inductionOn with | h x =>
        induction y using Quot.inductionOn with | h y =>
          intro he
          exact Quot.sound ((polarSquareMap_collision x y).mp (congrArg Subtype.val he))
    · intro z
      obtain ⟨x,hx⟩ := hJs z
      exact ⟨Quot.mk oneMarkPolarRel x,hx⟩
  exact ⟨(Equiv.ofBijective F hbij).toHomeomorphOfContinuousClosed hF hF.isClosedMap,fun _ => rfl⟩

end
end CurveComplex
#print axioms CurveComplex.one_mark_polar_cell_square_chart
