import Mathlib
namespace CurveComplex
open Set
set_option maxHeartbeats 1500000

/-- A genuine open chart preserving a local axis sends the two transverse
half-arcs to opposite sides. This follows from connectedness and openness,
not from the zero-set equality alone. -/
theorem actual_axis_chart_transverse_sides
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (r : ℝ) (hr : 0 < r)
    (hsource : Ioo (-r) r ×ˢ Ioo (-r) r ⊆ e.source)
    (haxis : ∀ z ∈ Ioo (-r) r ×ˢ Ioo (-r) r,
      (e z).2 = 0 ↔ z.2 = 0) :
    (0 < (e (0,r/2)).2 ∧ (e (0,-r/2)).2 < 0) ∨
    ((e (0,r/2)).2 < 0 ∧ 0 < (e (0,-r/2)).2) := by
  let O : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
  let U : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo 0 r
  let D : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) 0
  let f : ℝ × ℝ → ℝ := fun z => (e z).2
  have hUc : IsPreconnected U := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hDc : IsPreconnected D := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hUO : U ⊆ O := by
    rintro z ⟨hx,hy⟩
    exact ⟨hx,⟨by linarith [hy.1],hy.2⟩⟩
  have hDO : D ⊆ O := by
    rintro z ⟨hx,hy⟩
    exact ⟨hx,⟨hy.1,by linarith [hy.2]⟩⟩
  have hfc : ContinuousOn f O := continuous_snd.comp_continuousOn
    (e.continuousOn.mono hsource)
  have hUn : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz he
    have hh := (haxis z (hUO hz)).mp he
    exact (ne_of_gt hz.2.1) hh
  have hDn : ∀ z ∈ D, f z ≠ 0 := by
    intro z hz he
    have hh := (haxis z (hDO hz)).mp he
    exact (ne_of_lt hz.2.2) hh
  have hplus : (0,r/2) ∈ U := by
    constructor <;> constructor <;> linarith
  have hminus : (0,-r/2) ∈ D := by
    constructor <;> constructor <;> linarith
  have h0O : (0,0) ∈ O := by
    constructor <;> constructor <;> linarith
  have hf0 : f (0,0) = 0 := (haxis _ h0O).mpr rfl
  have hOi : IsOpen (e '' O) := e.isOpen_image_of_subset_source
    (isOpen_Ioo.prod isOpen_Ioo) hsource
  have he0 : e (0,0) ∈ e '' O := ⟨(0,0),h0O,rfl⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hOi.mem_nhds he0)
  have hzball (s : ℝ) (hs : |s| < ε) :
      ((e (0,0)).1,s) ∈ Metric.ball (e (0,0)) ε := by
    rw [Metric.mem_ball,Prod.dist_eq,dist_self,Real.dist_eq]
    have hzero : (e (0,0)).2 = 0 := hf0
    rw [hzero,sub_zero,max_eq_right (abs_nonneg s)]
    exact hs
  obtain ⟨zpos,hzpos,hezpos⟩ := hball
    (hzball (ε/2) (by rw [abs_of_pos (half_pos hε)]; linarith))
  obtain ⟨zneg,hzneg,hezneg⟩ := hball
    (hzball (-ε/2) (by rw [abs_of_neg (by linarith : -ε/2 < 0)]; linarith))
  have hfp : 0 < f zpos := by
    have hh := congrArg Prod.snd hezpos
    dsimp [f]
    change 0 < (e zpos).2
    rw [hh]
    linarith
  have hfn : f zneg < 0 := by
    have hh := congrArg Prod.snd hezneg
    dsimp [f]
    change (e zneg).2 < 0
    rw [hh]
    linarith
  have not_same_positive (hp : 0 < f (0,r/2)) (hm : 0 < f (0,-r/2)) : False := by
    have hUp : ∀ z ∈ U, 0 < f z := fun z hz =>
      hUc.lt_of_ne (hfc.mono hUO) hUn ⟨(0,r/2),hplus,hp⟩ hz
    have hDp : ∀ z ∈ D, 0 < f z := fun z hz =>
      hDc.lt_of_ne (hfc.mono hDO) hDn ⟨(0,-r/2),hminus,hm⟩ hz
    rcases lt_trichotomy zneg.2 0 with hn | hn | hn
    · have hzD : zneg ∈ D := ⟨hzneg.1,⟨hzneg.2.1,hn⟩⟩
      have hh := hDp _ hzD
      linarith
    · have hh := (haxis zneg hzneg).mpr hn
      change f zneg = 0 at hh
      linarith
    · have hzU : zneg ∈ U := ⟨hzneg.1,⟨hn,hzneg.2.2⟩⟩
      have hh := hUp _ hzU
      linarith
  have not_same_negative (hp : f (0,r/2) < 0) (hm : f (0,-r/2) < 0) : False := by
    have hUp : ∀ z ∈ U, f z < 0 := fun z hz =>
      hUc.gt_of_ne (hfc.mono hUO) hUn ⟨(0,r/2),hplus,hp⟩ hz
    have hDp : ∀ z ∈ D, f z < 0 := fun z hz =>
      hDc.gt_of_ne (hfc.mono hDO) hDn ⟨(0,-r/2),hminus,hm⟩ hz
    rcases lt_trichotomy zpos.2 0 with hn | hn | hn
    · have hzD : zpos ∈ D := ⟨hzpos.1,⟨hzpos.2.1,hn⟩⟩
      have hh := hDp _ hzD
      linarith
    · have hh := (haxis zpos hzpos).mpr hn
      change f zpos = 0 at hh
      linarith
    · have hzU : zpos ∈ U := ⟨hzpos.1,⟨hn,hzpos.2.2⟩⟩
      have hh := hUp _ hzU
      linarith
  rcases lt_or_gt_of_ne (hUn _ hplus) with hp | hp
  · right
    refine ⟨hp,?_⟩
    rcases lt_or_gt_of_ne (hDn _ hminus) with hm | hm
    · exact False.elim (not_same_negative hp hm)
    · exact hm
  · left
    refine ⟨hp,?_⟩
    rcases lt_or_gt_of_ne (hDn _ hminus) with hm | hm
    · exact hm
    · exact False.elim (not_same_positive hp hm)
end CurveComplex
