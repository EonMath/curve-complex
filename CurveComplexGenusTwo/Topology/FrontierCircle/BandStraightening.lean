import CurveComplexGenusTwo.Topology.FrontierCircle.BandLocal
import CurveComplexGenusTwo.Topology.GluedArcBoundary
import Schoenflies.ArcComplement
import Schoenflies.Concatenate
import Schoenflies.SkeletonAccess
import Schoenflies.Accessible
import Schoenflies.Subarc
import Schoenflies.JordanSchoenflies

open Set Metric unitInterval Topology
namespace Schoenflies

/-- A larger interior subarc has a Jordan completion, with the completing arc
meeting the entire original arc only at the two new endpoints. -/
theorem interior_subarc_jordan_completion
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    ∃ u v : ℝ, u ∈ Ioo 0 s ∧ v ∈ Ioo t 1 ∧
      ∃ A : Set Plane, IsArcBetween A (f u) (f v) ∧
        A ∩ (f '' I) = {f u, f v} ∧
        IsJordanCurve (A ∪ (f '' Icc u v)) := by
  have hNoBall : ∀ {f : ℝ → Plane}, ContinuousOn f I → InjOn f I →
      ∀ {t r : ℝ}, t ∈ Ioo (0 : ℝ) 1 → 0 < r →
        ¬ ball (f t) r ⊆ f '' I := by
    intro f hf hi t r ht hr
    intro hsub
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    obtain ⟨δ, hδ, hδspec⟩ := Metric.continuousWithinAt_iff.mp
      (hf t ⟨ht.1.le, ht.2.le⟩) r hr
    let d : ℝ := min δ (min t (1-t)) / 2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdδ : d < δ := by dsimp [d]; have := min_le_left δ (min t (1-t)); linarith
    have hdt : d < t := by dsimp [d]; have := (min_le_right δ (min t (1-t))).trans (min_le_left t (1-t)); linarith
    have hd1 : d < 1-t := by dsimp [d]; have := (min_le_right δ (min t (1-t))).trans (min_le_right t (1-t)); linarith
    have hsI : t-d ∈ I := ⟨by linarith, by linarith [ht.2]⟩
    have huI : t+d ∈ I := ⟨by linarith [ht.1], by linarith⟩
    have hsball : f (t-d) ∈ ball (f t) r := hδspec hsI (by
      rw [Real.dist_eq]; have : t-d-t = -d := by ring
      rw [this, abs_neg, abs_of_pos hd]; exact hdδ)
    have huball : f (t+d) ∈ ball (f t) r := hδspec huI (by
      rw [Real.dist_eq]; have : t+d-t = d := by ring
      rw [this, abs_of_pos hd]; exact hdδ)
    obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hf hi (U := Iio t) isOpen_Iio
    obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hf hi (U := Ioi t) isOpen_Ioi
    let B := ball (f t) r \ {f t}
    have hB : IsPreconnected B := (isConnected_ball_diff_singleton hr).isPreconnected
    have hcover : B ⊆ V₁ ∪ V₂ := by
      rintro z ⟨hz, hzne⟩
      obtain ⟨s, hs, rfl⟩ := hsub hz
      have hst : s ≠ t := by rintro rfl; exact hzne rfl
      rcases lt_or_gt_of_ne hst with h | h
      · left
        have : f s ∈ V₁ ∩ f '' I := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1
      · right
        have : f s ∈ V₂ ∩ f '' I := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1
    have hs : (B ∩ V₁).Nonempty := by
      refine ⟨f (t-d), ⟨hsball, ?_⟩, ?_⟩
      · intro h
        have := hi hsI ⟨ht.1.le, ht.2.le⟩ h
        linarith
      · have : f (t-d) ∈ V₁ ∩ f '' I := by
          rw [← hV₁]; exact ⟨t-d, ⟨show t-d < t by linarith, hsI⟩, rfl⟩
        exact this.1
    have hu : (B ∩ V₂).Nonempty := by
      refine ⟨f (t+d), ⟨huball, ?_⟩, ?_⟩
      · intro h
        have := hi huI ⟨ht.1.le, ht.2.le⟩ h
        linarith
      · have : f (t+d) ∈ V₂ ∩ f '' I := by
          rw [← hV₂]; exact ⟨t+d, ⟨show t < t+d by linarith, huI⟩, rfl⟩
        exact this.1
    obtain ⟨z, hzB, hz₁, hz₂⟩ := hB V₁ V₂ hV₁open hV₂open hcover hs hu
    have hzImage := hsub hzB.1
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzImage⟩
    obtain ⟨u, hu, heq⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzImage⟩
    have := hi hu.2 hs.2 heq
    have hut : t < u := hu.1
    have hst : s < t := hs.1
    linarith
  have hAccessibleInternal : ∀ {f : ℝ → Plane}, ContinuousOn f I → InjOn f I →
      ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → ∀ U : Set ℝ, IsOpen U → t ∈ U →
        ∃ p ∈ f '' (U ∩ I), StronglyAccessible (f '' I)ᶜ p := by
    intro f hf hi t ht U hU htU
    have htI : t ∈ I := ⟨ht.1.le, ht.2.le⟩
    obtain ⟨r, hr, hrsub⟩ := exists_ball_inter_subset_image hf hi hU
      (show f t ∈ f '' (U ∩ I) from ⟨t, ⟨htU, htI⟩, rfl⟩)
    obtain ⟨q, hqball, hq⟩ := Set.not_subset.mp
      (hNoBall hf hi ht (show 0 < r / 3 by linarith))
    have hcompact : IsCompact (f '' I) := isCompact_I.image_of_continuousOn hf
    obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn
      (show (f '' I).Nonempty from ⟨f t, t, htI, rfl⟩)
      (Continuous.continuousOn (continuous_const.dist continuous_id : Continuous (fun z : Plane => dist q z)))
    have hnear : ∀ z ∈ f '' I, dist q p ≤ dist q z := fun z hz => isMinOn_iff.mp hmin z hz
    have hpball : p ∈ ball (f t) r := by
      have hdist : dist q (f t) < r / 3 := hqball
      have hle := hnear (f t) ⟨t, htI, rfl⟩
      have htri := dist_triangle p q (f t)
      rw [dist_comm p q] at htri
      change dist p (f t) < r
      linarith
    exact ⟨p, hrsub ⟨hpball, hp⟩,
      stronglyAccessible_of_isMinOn hq hp hnear (connectedComponentIn_subset _ _)⟩
  have hInternalSplit : ∀ {f : ℝ → Plane}, ContinuousOn f I → InjOn f I →
      ∀ {s t : ℝ}, 0 < s → s < t → t < 1 →
      ∃ u v : ℝ, u ∈ Ioo 0 s ∧ v ∈ Ioo t 1 ∧
        ∃ A : Set Plane, IsArcBetween A (f u) (f v) ∧
          A ∩ (f '' I) = {f u, f v} ∧
          IsJordanCurve (A ∪ (f '' Icc u v)) := by
    intro f hf hi s t hs hst ht
    obtain ⟨p, ⟨u, hu, rfl⟩, hpu⟩ := hAccessibleInternal hf hi
      (show s/2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (Ioo 0 s) isOpen_Ioo ⟨by linarith, by linarith⟩
    obtain ⟨q, ⟨v, hv, rfl⟩, hpv⟩ := hAccessibleInternal hf hi
      (show (t+1)/2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (Ioo t 1) isOpen_Ioo ⟨by linarith, by linarith⟩
    have huv : u < v := hu.1.2.trans (hst.trans hv.1.1)
    have hne : f u ≠ f v := fun h => (ne_of_lt huv) (hi hu.2 hv.2 h)
    have hAccU : PolyAccessible (f '' I)ᶜ (f u) := by
      obtain ⟨z, hz, _, hseg⟩ := hpu.openSegment_subset
      exact PolyAccessible.of_openSegment hz hseg
    have hAccV : PolyAccessible (f '' I)ᶜ (f v) := by
      obtain ⟨z, hz, _, hseg⟩ := hpv.openSegment_subset
      exact PolyAccessible.of_openSegment hz hseg
    have hArc : IsArc (f '' I) := ⟨f, hf, hi, rfl⟩
    obtain ⟨A, _, hA, havoid⟩ := exists_simple_arc_of_polyAccessible
      hArc.isClosed.isOpen_compl (arc_complement hArc).isPreconnected hne hAccU hAccV
    have hmeet : A ∩ (f '' I) = {f u, f v} := by
      apply Subset.antisymm
      · intro z hz
        by_contra h
        exact havoid ⟨hz.1, h⟩ hz.2
      · rintro z (rfl | rfl)
        · exact ⟨hA.left_mem, u, hu.2, rfl⟩
        · exact ⟨hA.right_mem, v, hv.2, rfl⟩
    have hSubarc : IsArcBetween (f '' Icc u v) (f u) (f v) := by
      simpa [uIcc_of_le huv.le] using
        isArcBetween_subarc_of_injOn_I hf hi hu.2 hv.2 (ne_of_lt huv)
    refine ⟨u, v, hu.1, hv.1, A, hA, hmeet,
      IsJordanCurve.of_two_arcs hA hSubarc.reverse ?_⟩
    intro z hzA hzS
    have hzI : z ∈ f '' I := image_mono
      (show Icc u v ⊆ I from fun r hr => ⟨hu.2.1.trans hr.1, hr.2.trans hv.2.2⟩) hzS
    have : z ∈ ({f u, f v} : Set Plane) := hmeet ▸ ⟨hzA, hzI⟩
    simpa using this
  exact hInternalSplit hf hi hs hst ht


/-- The other three sides of the square form the complementary arc to its top edge. -/
theorem isArcBetween_other_three_sides :
    IsArcBetween (sideLeft ∪ (sideBottom ∪ sideRight)) cornerNW cornerNE := by
  apply isArcBetween_sideLeft.concatenate isArcBetween_lowerSides
  rintro z hz (hb | hr)
  · have hx := (mem_sideLeft.mp hz).1
    have hy := (mem_sideBottom.mp hb).1
    ext i
    fin_cases i
    · simpa [cornerSW] using hx
    · simpa [cornerSW] using hy
  · have hx := (mem_sideLeft.mp hz).1
    have hx' := (mem_sideRight.mp hr).1
    linarith

theorem other_three_sides_meet_top :
    (sideLeft ∪ (sideBottom ∪ sideRight)) ∩ sideTop = {cornerNE,cornerNW} := by
  ext z
  constructor
  · rintro ⟨hl | hb | hr,ht⟩
    · right
      exact sideTop_meet_sideLeft z ht hl
    · have h1 := (mem_sideBottom.mp hb).1
      have h2 := (mem_sideTop.mp ht).1
      linarith
    · left
      have hx := (mem_sideRight.mp hr).1
      have hy := (mem_sideTop.mp ht).1
      ext i
      fin_cases i
      · simpa [cornerNE] using hx
      · simpa [cornerNE] using hy
  · rintro (rfl | rfl)
    · exact ⟨isArcBetween_other_three_sides.right_mem,isArcBetween_sideTop.left_mem⟩
    · exact ⟨isArcBetween_other_three_sides.left_mem,isArcBetween_sideTop.right_mem⟩

theorem exists_ambient_straightening_to_top
    {A P : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hmeet : A ∩ P = {a, b})
    (hJ : IsJordanCurve (A ∪ P)) :
    ∃ F : Plane ≃ₜ Plane, F '' P = sideTop := by
  let B : Set Plane := sideLeft ∪ (sideBottom ∪ sideRight)
  let Q : Set Plane := sideTop
  have hB : IsArcBetween B cornerNE cornerNW := by
    simpa [B] using isArcBetween_other_three_sides.reverse
  have hQ : IsArcBetween Q cornerNE cornerNW := by
    simpa [Q] using isArcBetween_sideTop
  have hmeetTarget : B ∩ Q = {cornerNE, cornerNW} :=
    other_three_sides_meet_top
  obtain ⟨e,hArcImage,_,_⟩ :=
    exists_homeomorph_union_arcs_preserving_second hA hP hB hQ hmeet hmeetTarget
  have hModel : B ∪ Q = modelCurve := by
    dsimp [B, Q]
    rw [modelCurve_eq_sides]
    ext z
    simp only [Set.mem_union]
    tauto
  let eModel : ↥(A ∪ P) ≃ₜ ↥modelCurve := e.trans (Homeomorph.setCongr hModel)
  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve eModel
  have hImage : F '' P = Q := by
    ext y
    constructor
    · rintro ⟨x, hxP, rfl⟩
      have hxJ : x ∈ A ∪ P := Or.inr hxP
      have hxArc : (e ⟨x, hxJ⟩ : Plane) ∈ Q := by
        have hmem : (e ⟨x, hxJ⟩ : ↥(B ∪ Q)) ∈ e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P} :=
          ⟨⟨x, hxJ⟩, hxP, rfl⟩
        have hval : (e ⟨x, hxJ⟩ : Plane) ∈ Subtype.val ''
            (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := Set.mem_image_of_mem _ hmem
        rw [hArcImage] at hval
        exact hval
      have hfx : F x = (eModel ⟨x, hxJ⟩ : Plane) := hF ⟨x, hxJ⟩
      have hEmodel : (eModel ⟨x, hxJ⟩ : Plane) = (e ⟨x, hxJ⟩ : Plane) := by rfl
      rw [hfx, hEmodel]
      simpa [Q] using hxArc
    · intro hy
      have hyQ : y ∈ Q := by simpa [Q] using hy
      have hyImage : y ∈ Subtype.val ''
          (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := by rw [hArcImage]; exact hyQ
      obtain ⟨z, hzImage, hzy⟩ := hyImage
      obtain ⟨x, hxP, hzx⟩ := hzImage
      have hxJ : (x : Plane) ∈ A ∪ P := x.property
      refine ⟨(x : Plane), hxP, ?_⟩
      have hFz : F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) :=
        hF ⟨(x : Plane), hxJ⟩
      have hEmodel : (eModel ⟨(x : Plane), hxJ⟩ : Plane) =
          (e ⟨(x : Plane), hxJ⟩ : Plane) := rfl
      have hzx' : (e ⟨(x : Plane), hxJ⟩ : Plane) = (z : Plane) :=
        congrArg Subtype.val hzx
      calc
        F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) := hFz
        _ = (e ⟨(x : Plane), hxJ⟩ : Plane) := hEmodel
        _ = (z : Plane) := hzx'
        _ = y := hzy
  exact ⟨F,hImage⟩

theorem exists_straightening_of_internal_arc
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    ∃ u v : ℝ, u ∈ Ioo 0 s ∧ v ∈ Ioo t 1 ∧
      ∃ F : Plane ≃ₜ Plane, F '' (f '' Icc u v) = sideTop := by
  obtain ⟨u,v,hu,hv,A,hA,hmeet,hJ⟩ := interior_subarc_jordan_completion hf hi hs hst ht
  have huv : u < v := hu.2.trans (hst.trans hv.1)
  have huI : u ∈ I := ⟨hu.1.le,(hu.2.trans (hst.trans ht)).le⟩
  have hvI : v ∈ I := ⟨(hs.trans (hst.trans hv.1)).le,hv.2.le⟩
  have hP : IsArcBetween (f '' Icc u v) (f u) (f v) := by
    simpa [uIcc_of_le huv.le] using isArcBetween_subarc_of_injOn_I hf hi huI hvI huv.ne
  have hmeet' : A ∩ (f '' Icc u v) = {f u,f v} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hmeet ▸ ⟨hz.1, Set.image_mono (Icc_subset_Icc huI.1 hvI.2) hz.2⟩
    · rintro z (rfl | rfl)
      · exact ⟨hA.left_mem,hP.left_mem⟩
      · exact ⟨hA.right_mem,hP.right_mem⟩
  obtain ⟨F,hF⟩ := exists_ambient_straightening_to_top hA hP hmeet' hJ
  exact ⟨u,v,hu,hv,F,hF⟩

/-- An actual rectangular band around a compact internal subarc of an arbitrary
embedded planar interval. The band lies in the prescribed open set and meets
the full original arc in exactly its central core. -/
theorem exists_rectangular_band_internal_planar_arc
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (U : Set Plane) (hU : IsOpen U) (hKU : f '' Icc s t ⊆ U) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      ∃ B : Icc s t × Icc (-δ) δ → Plane,
        Topology.IsEmbedding B ∧ Set.range B ⊆ U ∧
        (∀ z : Icc s t, B (z,⟨0,by constructor <;> linarith⟩) = f z) ∧
        Set.range B ∩ (f '' I) = f '' Icc s t := by
  classical
  obtain ⟨u,v,hu,hv,F,hF⟩ := exists_straightening_of_internal_arc hf hi hs hst ht
  have hstI : Icc s t ⊆ I := Icc_subset_Icc hs.le ht.le
  have huvI : Icc u v ⊆ I := Icc_subset_Icc hu.1.le hv.2.le
  have hstuv : Icc s t ⊆ Icc u v := Icc_subset_Icc hu.2.le hv.1.le
  have hcoord (z : ℝ) (hz : z ∈ Icc u v) : F (f z) 1 = 1 := by
    have hmem : F (f z) ∈ sideTop := hF ▸ ⟨f z,⟨z,hz,rfl⟩,rfl⟩
    exact (mem_sideTop.mp hmem).1
  let bad := f '' (I \ Ioo u v)
  have hbad : IsClosed bad :=
    ((isCompact_I.diff isOpen_Ioo).image_of_continuousOn (hf.mono diff_subset)).isClosed
  let V := U \ bad
  have hV : IsOpen V := hU.sdiff hbad
  have hKV : f '' Icc s t ⊆ V := by
    rintro z ⟨a,ha,rfl⟩
    refine ⟨hKU ⟨a,ha,rfl⟩,?_⟩
    rintro ⟨b,hb,he⟩
    have heq : b = a := hi hb.1 (hstI ha) he
    exact hb.2 (heq ▸ ⟨hu.2.trans_le ha.1,ha.2.trans_lt hv.1⟩)
  have hKc : IsCompact (F '' (f '' Icc s t)) :=
    (isCompact_Icc.image_of_continuousOn (hf.mono hstI)).image F.continuous
  obtain ⟨δ,hδ,hδV⟩ := hKc.exists_cthickening_subset_open
    (F.isOpenMap V hV) (Set.image_mono hKV)
  let B : Icc s t × Icc (-δ) δ → Plane :=
    fun z => F.symm (F (f z.1) + (z.2 : ℝ) • Plane.mk 0 1)
  have hBc : Continuous B := by
    exact F.symm.continuous.comp
      ((F.continuous.comp ((hf.mono hstI).restrict.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_snd).smul continuous_const))
  have hBi : Function.Injective B := by
    intro z w he
    have he' : F (f z.1) + (z.2 : ℝ) • Plane.mk 0 1 =
        F (f w.1) + (w.2 : ℝ) • Plane.mk 0 1 := F.symm.injective he
    have h0 := congrArg (fun a : Plane => a 0) he'
    have h1 := congrArg (fun a : Plane => a 1) he'
    simp at h0 h1
    have heF : F (f z.1) = F (f w.1) := by
      ext i
      fin_cases i
      · exact h0
      · exact (hcoord z.1 (hstuv z.1.property)).trans (hcoord w.1 (hstuv w.1.property)).symm
    have hez : z.1 = w.1 := Subtype.ext (hi (hstI z.1.property) (hstI w.1.property) (F.injective heF))
    have hew : z.2 = w.2 := by
      apply Subtype.ext
      rw [hcoord z.1 (hstuv z.1.property),hcoord w.1 (hstuv w.1.property)] at h1
      linarith
    exact Prod.ext hez hew
  have hBV : Set.range B ⊆ V := by
    rintro z ⟨a,rfl⟩
    have hdist : dist (F (f a.1) + (a.2 : ℝ) • Plane.mk 0 1) (F (f a.1)) ≤ δ := by
      simpa [dist_eq_norm,norm_smul,EuclideanSpace.norm_eq,Fin.sum_univ_two] using
        (abs_le.mpr a.2.property)
    obtain ⟨w,hw,hew⟩ := hδV (mem_cthickening_of_dist_le _ _ δ _
      ⟨f a.1,⟨a.1,a.1.property,rfl⟩,rfl⟩ hdist)
    change F.symm _ ∈ V
    rw [← hew,F.symm_apply_apply]
    exact hw
  have hcenter (z : Icc s t) : B (z,⟨0,by constructor <;> linarith⟩) = f z := by
    simp [B]
  refine ⟨δ,hδ,B,(hBc.isClosedEmbedding hBi).isEmbedding,
    fun z hz => (hBV hz).1,hcenter,?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨⟨a,rfl⟩,w,hw,hew⟩
    have hwuv : w ∈ Icc u v := by
      have hnot : f w ∉ bad := hew.symm ▸ (hBV (Set.mem_range_self a)).2
      have hwin : w ∈ Ioo u v := by
        by_contra h
        exact hnot ⟨w,⟨hw,h⟩,rfl⟩
      exact ⟨hwin.1.le,hwin.2.le⟩
    have he' : F (f w) = F (f a.1) + (a.2 : ℝ) • Plane.mk 0 1 := by
      rw [hew]
      exact F.apply_symm_apply _
    have hy := congrArg (fun x : Plane => x 1) he'
    simp at hy
    rw [hcoord w hwuv,hcoord a.1 (hstuv a.1.property)] at hy
    have ha0 : (a.2 : ℝ) = 0 := by linarith
    refine ⟨a.1,a.1.property,?_⟩
    simp [B,ha0]
  · rintro z ⟨w,hw,rfl⟩
    exact ⟨⟨(⟨w,hw⟩,⟨0,by constructor <;> linarith⟩),hcenter ⟨w,hw⟩⟩,
      w,hstI hw,rfl⟩

/-- Transport of the constructed planar band through an actual surface chart.
The input is only an embedded arc lying in the chart, not a collar witness. -/
theorem exists_rectangular_band_in_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (e : OpenPartialHomeomorph S Plane)
    {f : ℝ → S} (hf : ContinuousOn f I) (hi : InjOn f I)
    (hsource : Set.MapsTo f I e.source)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (U : Set S) (hU : IsOpen U) (hKU : f '' Icc s t ⊆ U) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ,
      ∃ B : Icc s t × Icc (-δ) δ → S,
        Topology.IsEmbedding B ∧ Set.range B ⊆ U ∩ e.source ∧
        (∀ z : Icc s t, B (z,⟨0,by constructor <;> linarith⟩) = f z) ∧
        Set.range B ∩ (f '' I) = f '' Icc s t := by
  let g : ℝ → Plane := e ∘ f
  have hg : ContinuousOn g I := e.continuousOn.comp hf hsource
  have hgi : InjOn g I := by
    intro a ha b hb he
    exact hi ha hb (e.injOn (hsource ha) (hsource hb) he)
  let V := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hstI : Icc s t ⊆ I := Icc_subset_Icc hs.le ht.le
  have hKV : g '' Icc s t ⊆ V := by
    rintro z ⟨a,ha,rfl⟩
    exact ⟨e.map_source (hsource (hstI ha)),by
      change e.symm (e (f a)) ∈ U
      rw [e.left_inv (hsource (hstI ha))]
      exact hKU ⟨a,ha,rfl⟩⟩
  obtain ⟨δ,hδ,B,hB,hBV,hcenter,hmeet⟩ :=
    exists_rectangular_band_internal_planar_arc hg hgi hs hst ht V hV hKV
  have hBt (a) : B a ∈ e.target := (hBV (Set.mem_range_self a)).1
  let B' : Icc s t × Icc (-δ) δ → S := e.symm ∘ B
  have hB'c : Continuous B' := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (e.continuousAt_symm (hBt a)).comp hB.continuous.continuousAt
  have hB'i : Function.Injective B' := by
    intro a b he
    exact hB.injective (e.symm.injOn (hBt a) (hBt b) he)
  have hcenter' (z : Icc s t) : B' (z,⟨0,by constructor <;> linarith⟩) = f z := by
    change e.symm (B _) = f z
    rw [hcenter]
    exact e.left_inv (hsource (hstI z.property))
  refine ⟨δ,hδ,B',(hB'c.isClosedEmbedding hB'i).isEmbedding,?_,hcenter',?_⟩
  · rintro z ⟨a,rfl⟩
    exact ⟨(hBV (Set.mem_range_self a)).2,e.map_target (hBt a)⟩
  · apply Set.Subset.antisymm
    · rintro z ⟨⟨a,rfl⟩,w,hw,hew⟩
      have hgw : g w = B a := by
        change e (f w) = B a
        rw [hew]
        exact e.right_inv (hBt a)
      have hin : B a ∈ Set.range B ∩ g '' I :=
        ⟨Set.mem_range_self a,w,hw,hgw⟩
      rw [hmeet] at hin
      obtain ⟨z,hz,hez⟩ := hin
      refine ⟨z,hz,?_⟩
      have hez' := congrArg e.symm hez
      change e.symm (e (f z)) = B' a at hez'
      rwa [e.left_inv (hsource (hstI hz))] at hez'
    · rintro z ⟨w,hw,rfl⟩
      exact ⟨⟨(⟨w,hw⟩,⟨0,by constructor <;> linarith⟩),hcenter' ⟨w,hw⟩⟩,
        w,hstI hw,rfl⟩

/-- Every interior point of an embedded surface path has an actual rectangular
band in any prescribed ambient open neighborhood. Its central arc is a
symmetric parameter subarc of the given path, and there are no extra returns. -/
theorem exists_local_rectangular_band_on_surface
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {x y : S} (p : Path x y) (hp : Topology.IsEmbedding p)
    (m : unitInterval) (hm0 : 0 < m) (hm1 : m < 1)
    (U : Set S) (hU : IsOpen U) (hmU : p m ∈ U) :
    ∃ η : ℝ, 0 < η ∧ 0 < (m : ℝ)-η ∧ (m : ℝ)+η < 1 ∧
      ∃ δ : ℝ, ∃ hδ : 0 < δ,
        ∃ B : Icc (1/3 : ℝ) (2/3) × Icc (-δ) δ → S,
          Topology.IsEmbedding B ∧ Set.range B ⊆ U ∧
          (∀ z : Icc (1/3 : ℝ) (2/3),
            B (z,⟨0,by constructor <;> linarith⟩) =
              p.extend ((m : ℝ)-η+2*η*(z : ℝ))) ∧
          Set.range B ∩ Set.range p =
            Set.range (fun z : Icc (1/3 : ℝ) (2/3) =>
              p.extend ((m : ℝ)-η+2*η*(z : ℝ))) := by
  classical
  let e := chartAt Plane (p m)
  have hm0' : (0:ℝ) < m := hm0
  have hm1' : (m:ℝ) < 1 := hm1
  have hpm : p.extend (m:ℝ) = p m := p.extend_extends' m
  have hpre : p.extend ⁻¹' (U ∩ e.source) ∈ 𝓝 (m:ℝ) := by
    apply p.extend.continuous.continuousAt.preimage_mem_nhds
    apply (hU.inter e.open_source).mem_nhds
    rw [hpm]
    exact ⟨hmU,mem_chart_source _ _⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hpre
  let η := min r (min (m:ℝ) (1-(m:ℝ))) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηr : η < r := by
    have := min_le_left r (min (m:ℝ) (1-(m:ℝ)))
    dsimp [η]; linarith
  have hηm : η < (m:ℝ) := by
    have := (min_le_right r (min (m:ℝ) (1-(m:ℝ)))).trans (min_le_left _ _)
    dsimp [η]; linarith
  have hηone : η < 1-(m:ℝ) := by
    have := (min_le_right r (min (m:ℝ) (1-(m:ℝ)))).trans (min_le_right _ _)
    dsimp [η]; linarith
  let L := (m:ℝ)-η
  let R := (m:ℝ)+η
  let τ : ℝ → ℝ := fun z => L+2*η*z
  have hτ (z : ℝ) (hz : z ∈ I) : τ z ∈ Icc L R := by
    dsimp [τ,R,L]
    constructor <;> nlinarith [hz.1,hz.2]
  have hL : 0 < L := sub_pos.mpr hηm
  have hR : R < 1 := by dsimp [R]; linarith
  have hLR : L < R := by dsimp [L,R]; linarith
  have hLI : Icc L R ⊆ I := Icc_subset_Icc hL.le hR.le
  have hτI (z : ℝ) (hz : z ∈ I) : τ z ∈ I := hLI (hτ z hz)
  let f : ℝ → S := p.extend ∘ τ
  have hf : ContinuousOn f I := by
    apply Continuous.continuousOn
    exact p.extend.continuous.comp (by dsimp [τ]; fun_prop)
  have hinj : InjOn p.extend I := by
    intro a ha b hb he
    rw [p.extend_apply ha,p.extend_apply hb] at he
    exact congrArg Subtype.val (hp.injective he)
  have hi : InjOn f I := by
    intro a ha b hb he
    have h := hinj (hτI a ha) (hτI b hb) he
    dsimp [τ] at h
    nlinarith
  have hlocal (z : ℝ) (hz : z ∈ Icc L R) : p.extend z ∈ U ∩ e.source := by
    apply hrsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [L,R] at hz
    constructor <;> linarith [hz.1,hz.2]
  have hsource : MapsTo f I e.source := fun z hz => (hlocal _ (hτ z hz)).2
  let bad := p.extend '' (I \ Ioo L R)
  have hbad : IsClosed bad :=
    ((isCompact_I.diff isOpen_Ioo).image p.extend.continuous).isClosed
  let V := U \ bad
  have hV : IsOpen V := hU.sdiff hbad
  have hthird : Icc (1/3:ℝ) (2/3) ⊆ I := by
    intro z hz
    constructor <;> linarith [hz.1,hz.2]
  have hcore (z : ℝ) (hz : z ∈ Icc (1/3:ℝ) (2/3)) : τ z ∈ Ioo L R := by
    dsimp [τ,L,R]
    constructor <;> nlinarith [hz.1,hz.2]
  have hKV : f '' Icc (1/3:ℝ) (2/3) ⊆ V := by
    rintro z ⟨a,ha,rfl⟩
    refine ⟨(hlocal _ (hτ a (hthird ha))).1,?_⟩
    rintro ⟨b,hb,he⟩
    have heq := hinj hb.1 (hτI a (hthird ha)) he
    exact hb.2 (heq ▸ hcore a ha)
  obtain ⟨δ,hδ,B,hB,hBV,hcenter,hmeet⟩ := exists_rectangular_band_in_chart
    e hf hi hsource (s := 1/3) (t := 2/3) (by norm_num) (by norm_num) (by norm_num) V hV hKV
  refine ⟨η,hη,hL,hR,δ,hδ,B,hB,fun z hz => (hBV hz).1.1,hcenter,?_⟩
  have hfimage : f '' Icc (1/3:ℝ) (2/3) =
      Set.range (fun z : Icc (1/3:ℝ) (2/3) => p.extend ((m:ℝ)-η+2*η*(z:ℝ))) := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
    · rintro ⟨a,rfl⟩; exact ⟨a,a.property,rfl⟩
  rw [← hfimage]
  apply Set.Subset.antisymm
  · rintro z ⟨hz,w,rfl⟩
    have hwLR : (w:ℝ) ∈ Ioo L R := by
      by_contra h
      exact (hBV hz).1.2 ⟨w,⟨w.property,h⟩,p.extend_extends' w⟩
    let a : ℝ := ((w:ℝ)-L)/(2*η)
    have ha : a ∈ I := by
      constructor
      · dsimp [a]; exact div_nonneg (by linarith [hwLR.1]) (by positivity)
      · dsimp [a]; apply (div_le_one (by positivity : 0 < 2*η)).mpr
        dsimp [L,R] at *
        linarith [hwLR.2]
    have hτa : τ a = (w:ℝ) := by
      dsimp [τ,a]
      field_simp
      <;> ring
    have hfw : f a = p w := by
      change p.extend (τ a) = p w
      rw [hτa,p.extend_extends']
    exact hmeet ▸ ⟨hz,a,ha,hfw⟩
  · rintro z ⟨a,ha,rfl⟩
    have hzin : f a ∈ Set.range B ∩ f '' I := hmeet.symm ▸ ⟨a,ha,rfl⟩
    refine ⟨hzin.1,⟨τ a,hτI a (hthird ha)⟩,?_⟩
    exact (p.extend_apply (hτI a (hthird ha))).symm

/-- The two actual outside arcs have disjoint rectangular bands around
smaller interior cores. Both bands avoid the crossing square and meet their
respective full outside arcs exactly along their centerlines. -/
theorem outside_arcs_two_rectangular_core_bands
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {x y u v : S} (p : Path x y) (q : Path u v)
    (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
    (D : Set S) (hD : IsCompact D)
    (hpa : Set.range p ∩ D = {x,y}) (hqa : Set.range q ∩ D = {u,v})
    (hpq : Disjoint (Set.range p) (Set.range q)) :
    ∃ ηp ηq : ℝ, 0 < ηp ∧ ηp < 1/2 ∧ 0 < ηq ∧ ηq < 1/2 ∧
      ∃ δp δq : ℝ, ∃ hδp : 0 < δp, ∃ hδq : 0 < δq,
        ∃ (Bp : Icc (1/3:ℝ) (2/3) × Icc (-δp) δp → S)
          (Bq : Icc (1/3:ℝ) (2/3) × Icc (-δq) δq → S),
          Topology.IsEmbedding Bp ∧ Topology.IsEmbedding Bq ∧
          Disjoint (Set.range Bp) (Set.range Bq) ∧
          Disjoint (Set.range Bp) D ∧ Disjoint (Set.range Bq) D ∧
          (∀ z : Icc (1/3:ℝ) (2/3),
            Bp (z,⟨0,by constructor <;> linarith⟩) = p.extend (1/2-ηp+2*ηp*(z:ℝ))) ∧
          (∀ z : Icc (1/3:ℝ) (2/3),
            Bq (z,⟨0,by constructor <;> linarith⟩) = q.extend (1/2-ηq+2*ηq*(z:ℝ))) ∧
          Set.range Bp ∩ Set.range p =
            Set.range (fun z : Icc (1/3:ℝ) (2/3) => p.extend (1/2-ηp+2*ηp*(z:ℝ))) ∧
          Set.range Bq ∩ Set.range q =
            Set.range (fun z : Icc (1/3:ℝ) (2/3) => q.extend (1/2-ηq+2*ηq*(z:ℝ))) := by
  obtain ⟨Np,Nq,hNpc,hNpn,hNqc,hNqn,hpN,hqN,hNpq,hNpD,hNqD⟩ :=
    CurveComplex.outside_arcs_disjoint_compact_connected_cores p q hp hq D hD hpa hqa hpq
      (⟨1/3,by norm_num⟩ : unitInterval) (⟨2/3,by norm_num⟩ : unitInterval)
      (by change (0:ℝ) < 1/3; norm_num)
      (by change (1/3:ℝ) ≤ 2/3; norm_num)
      (by change (2/3:ℝ) < 1; norm_num)
  let m : unitInterval := ⟨1/2,by norm_num⟩
  have hm0 : 0 < m := by change (0:ℝ) < 1/2; norm_num
  have hm1 : m < 1 := by change (1/2:ℝ) < 1; norm_num
  have hmI : m ∈ Icc (⟨1/3,by norm_num⟩ : unitInterval) (⟨2/3,by norm_num⟩ : unitInterval) := by
    constructor <;> change _ ≤ (_:ℝ) <;> norm_num [m]
  obtain ⟨ηp,hηp,hpl,hpr,δp,hδp,Bp,hBp,hBpN,hpc,hpm⟩ :=
    exists_local_rectangular_band_on_surface p hp m hm0 hm1
      (interior Np) isOpen_interior (hpN ⟨m,hmI,rfl⟩)
  obtain ⟨ηq,hηq,hql,hqr,δq,hδq,Bq,hBq,hBqN,hqc,hqm⟩ :=
    exists_local_rectangular_band_on_surface q hq m hm0 hm1
      (interior Nq) isOpen_interior (hqN ⟨m,hmI,rfl⟩)
  have hBpNp : Set.range Bp ⊆ Np := hBpN.trans interior_subset
  have hBqNq : Set.range Bq ⊆ Nq := hBqN.trans interior_subset
  have hηp' : ηp < 1/2 := by change 0 < (1/2:ℝ)-ηp at hpl; linarith
  have hηq' : ηq < 1/2 := by change 0 < (1/2:ℝ)-ηq at hql; linarith
  exact ⟨ηp,ηq,hηp,hηp',hηq,hηq',δp,δq,hδp,hδq,Bp,Bq,hBp,hBq,
    hNpq.mono hBpNp hBqNq,hNpD.mono_left hBpNp,hNqD.mono_left hBqNq,hpc,hqc,hpm,hqm⟩

#print axioms interior_subarc_jordan_completion
#print axioms exists_ambient_straightening_to_top
#print axioms exists_straightening_of_internal_arc
#print axioms exists_rectangular_band_internal_planar_arc
#print axioms exists_rectangular_band_in_chart
#print axioms exists_local_rectangular_band_on_surface
#print axioms outside_arcs_two_rectangular_core_bands
end Schoenflies
