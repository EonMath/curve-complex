import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture
import CurveComplexGenusTwo.Topology.PositionExtension.LocalOrientationAlgebra
import CurveComplexGenusTwo.Topology.PositionExtension.TwistedBandReflection
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart
import CurveComplexGenusTwo.Topology.GlobalArcCollar.AxisFramedStripProducerStatement

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate
set_option maxHeartbeats 3000000
namespace CurveComplex.LocalSurgery
open scoped Manifold ContDiff
open Topology Set Filter unitInterval Schoenflies

/-- Statement-only export of the exact existing local `twisted` interface.
Source body: frozen CircleCollarOriginalPackage.lean lines 376–1062.
No circle, essentiality, genus, orientation, or reflection certificate is input. -/
theorem actual_square_twisted_band_produces_local_reflection
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (ε : ℝ) (hε : 0 < ε)
    (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → S)
    (hsquare : Topology.IsEmbedding square)
    (band : unitInterval × BandWidth → S)
    (hband : Topology.IsEmbedding band)
    (hbottom : ∀ t, band (0,t) = square (squarePort ε hε 2 t))
    (htop : ∀ t, band (1,t) = square (squarePort ε hε 0 (flipBandWidth true t)))
    (hmeet : Set.range band ∩ Set.range square =
      Set.range (fun t => square (squarePort ε hε 2 t)) ∪
      Set.range (fun t => square (squarePort ε hε 0 t))) :
    ∃ x : S, Nonempty (CurveComplex.GenusOrientationCandidate.LocalReflectionWitness x) := by
  classical
  have hrectangle (u : I) (t : BandWidth) :
      (ε/4 * -(t : ℝ), ε * (1 - 2 * (u : ℝ))) ∈
        Metric.closedBall ((0,0) : ℝ × ℝ) ε := by
    simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq,
      sub_zero, max_le_iff]
    constructor
    · calc
        |ε/4 * -(t : ℝ)| = ε/4 * |(t : ℝ)| := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
        _ ≤ ε/4 := by
          have ht := abs_le.mpr t.property
          nlinarith
        _ ≤ ε := by linarith
    · have hu : |1 - 2 * (u : ℝ)| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [u.property.1,u.property.2]
      rw [abs_mul, abs_of_pos hε]
      nlinarith
  let qbase : I × BandWidth → Metric.closedBall ((0,0) : ℝ × ℝ) ε :=
    fun z => ⟨(ε/4 * -(z.2 : ℝ), ε * (1 - 2 * (z.1 : ℝ))),
      hrectangle z.1 z.2⟩
  let Q : I × BandWidth → S := fun z => square (qbase z)
  have hqcont : Continuous qbase := by
    dsimp [qbase]
    fun_prop
  have hqinj : Function.Injective qbase := by
    intro x y hh
    have hp := congrArg Subtype.val hh
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp [qbase] at hx hy
    apply Prod.ext
    · apply Subtype.ext
      have hh := mul_left_cancel₀ hε.ne' hy
      linarith
    · apply Subtype.ext
      have hh := mul_left_cancel₀ (by positivity : ε/4 ≠ 0) hx
      exact neg_injective hh
  have hQembedded : IsEmbedding Q :=
    hsquare.comp (hqcont.isClosedEmbedding hqinj).isEmbedding
  have hQtop (t : BandWidth) : Q (0,t) = band (1,t) := by
    rw [htop]
    change square (qbase (0,t)) = square (squarePort ε hε 0 (flipBandWidth true t))
    apply congrArg square
    apply Subtype.ext
    simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
  have hQbottom (t : BandWidth) : Q (1,t) = band (0,flipBandWidth true t) := by
    rw [hbottom]
    change square (qbase (1,t)) = square (squarePort ε hε 2 (flipBandWidth true t))
    apply congrArg square
    apply Subtype.ext
    simp [qbase,squarePort,crossingEndRectangle,flipBandWidth]
    ring
  have hQinterior (u : I) (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1)
      (t : BandWidth) : Q (u,t) ∉ Set.range band := by
    intro hmem
    have hboth : Q (u,t) ∈ Set.range band ∩ Set.range square :=
      ⟨hmem, ⟨qbase (u,t), rfl⟩⟩
    rw [hmeet] at hboth
    rcases hboth with ⟨v, hv⟩ | ⟨v, hv⟩
    · have heq := hsquare.injective hv
      have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
      simp only [squarePort, crossingEndRectangle, qbase] at hy
      change -(ε + ε / 4 * 0) = ε * (1 - 2 * (u : ℝ)) at hy
      have hh := mul_left_cancel₀ hε.ne' (show ε * (-1) = ε * (1 - 2 * (u : ℝ)) by nlinarith [hy])
      linarith
    · have heq := hsquare.injective hv
      have hy := congrArg (fun z : Metric.closedBall ((0,0) : ℝ × ℝ) ε => (z : ℝ × ℝ).2) heq
      simp only [squarePort, crossingEndRectangle, qbase] at hy
      change ε + ε / 4 * 0 = ε * (1 - 2 * (u : ℝ)) at hy
      have hh := mul_left_cancel₀ hε.ne' (show ε * 1 = ε * (1 - 2 * (u : ℝ)) by simpa using hy)
      linarith
  let P := Set.Icc (0 : ℝ) 2 × BandWidth
  let left : P → S := fun z => band (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
  let right : P → S := fun z => Q (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), z.2)
  let F : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left z else right z
  have hleft : Continuous left := hband.continuous.comp
    ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hright : Continuous right := hQembedded.continuous.comp
    ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk continuous_snd)
  have hFcont : Continuous F := by
    apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
      hleft.continuousOn hright.continuousOn
    intro z hz
    change (z.1 : ℝ) = 1 at hz
    change left z = right z
    dsimp only [left, right]
    rw [hz]
    simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
      projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
    exact (hQtop z.2).symm
  have hFzero (t : BandWidth) : F (⟨0, by norm_num⟩,t) = band (0,t) := by
    simp [F,left]
  have hFtwo (t : BandWidth) : F (⟨2, by norm_num⟩,t) = band (0,flipBandWidth true t) := by
    simp only [F, show ¬ (2:ℝ) ≤ 1 by norm_num, ↓reduceIte, right]
    convert hQbottom t using 1 <;> norm_num [projIcc_of_mem]
  have hFinj (x y : P) (hx0 : 0 < (x.1 : ℝ)) (hx2 : (x.1 : ℝ) < 2)
      (hy0 : 0 < (y.1 : ℝ)) (hy2 : (y.1 : ℝ) < 2) (he : F x = F y) : x = y := by
    have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
        (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
      simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
    have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
        (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
      rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
        constructor <;> linarith [z.1.property.2])]
    dsimp only [F] at he
    split_ifs at he with hx hy hy
    · have hh := hband.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
      · exact congrArg (fun z : I × BandWidth => z.2) hh
    · have hy' : 1 < (y.1 : ℝ) := lt_of_not_ge hy
      have ha := hQinterior (projIcc 0 1 zero_le_one ((y.1 : ℝ)-1))
        (by rw [hclipright y hy']; linarith)
        (by rw [hclipright y hy']; linarith) y.2
      exact False.elim (ha ⟨_, he⟩)
    · have hx' : 1 < (x.1 : ℝ) := lt_of_not_ge hx
      have ha := hQinterior (projIcc 0 1 zero_le_one ((x.1 : ℝ)-1))
        (by rw [hclipright x hx']; linarith)
        (by rw [hclipright x hx']; linarith) x.2
      exact False.elim (ha ⟨_, he.symm⟩)
    · have hh := hQembedded.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
        linarith
      · exact congrArg (fun z : I × BandWidth => z.2) hh
  let f : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    F (projIcc 0 2 (by norm_num) (z 0), projIcc (-1) 1 (by norm_num) (z 1))
  let U : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ∈ Ioo 0 2 ∧ z 1 ∈ Ioo (-1) 1}
  have hUopen : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hfcont : Continuous f := hFcont.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hclip (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ U) :
      (projIcc 0 2 (by norm_num) (z 0) : ℝ) = z 0 ∧
      (projIcc (-1) 1 (by norm_num) (z 1) : ℝ) = z 1 := by
    constructor
    · exact congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨hz.1.1.le,hz.1.2.le⟩)
    · exact congrArg Subtype.val (projIcc_of_mem (by norm_num) ⟨hz.2.1.le,hz.2.2.le⟩)
  have hfinj : InjOn f U := by
    intro x hx y hy he
    have hh := hFinj
      (projIcc 0 2 (by norm_num) (x 0), projIcc (-1) 1 (by norm_num) (x 1))
      (projIcc 0 2 (by norm_num) (y 0), projIcc (-1) 1 (by norm_num) (y 1))
      (by rw [(hclip x hx).1]; exact hx.1.1)
      (by rw [(hclip x hx).1]; exact hx.1.2)
      (by rw [(hclip y hy).1]; exact hy.1.1)
      (by rw [(hclip y hy).1]; exact hy.1.2) he
    have h0 := congrArg (fun z : P => (z.1 : ℝ)) hh
    have h1 := congrArg (fun z : P => (z.2 : ℝ)) hh
    rw [(hclip x hx).1, (hclip y hy).1] at h0
    rw [(hclip x hx).2, (hclip y hy).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hTubeChartOpen : IsOpen (f '' U) :=
    surface_invariance_of_domain_probe f U hUopen hfcont.continuousOn hfinj
  let fU : U → S := fun z => f z
  have hfUopen : IsOpenMap fU := by
    intro V hV
    let W : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' V
    have hW : IsOpen W := hUopen.isOpenMap_subtype_val V hV
    have hWU : W ⊆ U := by
      rintro z ⟨w,hw,rfl⟩
      exact w.property
    have hWi : InjOn f W := hfinj.mono hWU
    have heq : fU '' V = f '' W := by
      simp only [W, Set.image_image]
      rfl
    rw [heq]
    exact surface_invariance_of_domain_probe f W hW hfcont.continuousOn hWi
  have hfUembedded : IsOpenEmbedding fU :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hfcont.comp continuous_subtype_val)
      (by intro x y he; exact Subtype.ext (hfinj x.property y.property he)) hfUopen
  let tubeChart : U ≃ₜ Set.range fU := hfUembedded.isEmbedding.toHomeomorph
  have hMeet : Set.range Q ∩ Set.range band =
      Set.range (fun t => Q (0,t)) ∪ Set.range (fun t => Q (1,t)) := by
    ext z
    constructor
    · rintro ⟨⟨⟨u,t⟩,hu⟩, hBz⟩
      by_cases h0 : u = 0
      · exact Or.inl ⟨t, by simpa [h0] using hu⟩
      by_cases h1 : u = 1
      · exact Or.inr ⟨t, by simpa [h1] using hu⟩
      have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
        intro heq; exact h0 (Subtype.ext heq.symm))
      have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
        intro heq; exact h1 (Subtype.ext heq))
      exact False.elim (hQinterior u hu0 hu1 t (hu.symm ▸ hBz))
    · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
      · exact ⟨⟨(0,t),rfl⟩, ⟨(1,t), (hQtop t).symm⟩⟩
      · exact ⟨⟨(1,t),rfl⟩, ⟨(0,flipBandWidth true t), (hQbottom t).symm⟩⟩
  have hQband (u v : I) (t w : BandWidth) (he : Q (u,t) = band (v,w)) :
      (u = 0 ∧ v = 1 ∧ w = t) ∨
      (u = 1 ∧ v = 0 ∧ w = flipBandWidth true t) := by
    by_cases h0 : u = 0
    · subst u
      have hh := hband.injective ((hQtop t).symm.trans he)
      exact Or.inl ⟨rfl, (congrArg Prod.fst hh).symm,
        (congrArg Prod.snd hh).symm⟩
    by_cases h1 : u = 1
    · subst u
      have hh := hband.injective ((hQbottom t).symm.trans he)
      exact Or.inr ⟨rfl, (congrArg Prod.fst hh).symm,
        (congrArg Prod.snd hh).symm⟩
    have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (by
      intro heq; exact h0 (Subtype.ext heq.symm))
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
      intro heq; exact h1 (Subtype.ext heq))
    exact False.elim (hQinterior u hu0 hu1 t ⟨(v,w),he.symm⟩)
  let left2 : P → S := fun z => Q (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2)
  let right2 : P → S := fun z => band
    (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), flipBandWidth true z.2)
  let G : P → S := fun z => if (z.1 : ℝ) ≤ 1 then left2 z else right2 z
  have hleft2 : Continuous left2 := hQembedded.continuous.comp
    ((continuous_projIcc.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hflip : Continuous (flipBandWidth true) :=
    continuous_subtype_val.neg.subtype_mk _
  have hright2 : Continuous right2 := hband.continuous.comp
    ((continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub continuous_const)).prodMk
      (hflip.comp continuous_snd))
  have hGcont : Continuous G := by
    apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
      hleft2.continuousOn hright2.continuousOn
    intro z hz
    change (z.1 : ℝ) = 1 at hz
    change Q (projIcc 0 1 zero_le_one (z.1 : ℝ), z.2) =
      band (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1), flipBandWidth true z.2)
    rw [hz]
    simp only [sub_self, projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num),
      projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
    exact hQbottom z.2
  have hGinj (x y : P) (hx0 : 0 < (x.1 : ℝ)) (hx2 : (x.1 : ℝ) < 2)
      (hy0 : 0 < (y.1 : ℝ)) (hy2 : (y.1 : ℝ) < 2) (he : G x = G y) : x = y := by
    have hclipleft (z : P) (hz : (z.1 : ℝ) ≤ 1) :
        (projIcc 0 1 zero_le_one (z.1 : ℝ) : ℝ) = (z.1 : ℝ) := by
      simp only [projIcc_of_mem zero_le_one ⟨z.1.property.1, hz⟩]
    have hclipright (z : P) (hz : 1 < (z.1 : ℝ)) :
        (projIcc 0 1 zero_le_one ((z.1 : ℝ)-1) : ℝ) = (z.1 : ℝ)-1 := by
      rw [projIcc_of_mem zero_le_one (show (z.1 : ℝ)-1 ∈ Icc (0:ℝ) 1 by
        constructor <;> linarith [z.1.property.2])]
    dsimp only [G] at he
    split_ifs at he with hx hy hy
    · have hh := hQembedded.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        exact (hclipleft x hx).symm.trans (hh1.trans (hclipleft y hy))
      · exact congrArg (fun z : I × BandWidth => z.2) hh
    · have hh := hQband _ _ _ _ he
      rcases hh with ⟨h0,_,_⟩ | ⟨_,h0,_⟩
      · have hv := congrArg Subtype.val h0
        rw [hclipleft x hx] at hv
        norm_num at hv
        linarith
      · have hv := congrArg Subtype.val h0
        rw [hclipright y (lt_of_not_ge hy)] at hv
        norm_num at hv
        linarith
    · have hh := hQband _ _ _ _ he.symm
      rcases hh with ⟨h0,_,_⟩ | ⟨_,h0,_⟩
      · have hv := congrArg Subtype.val h0
        rw [hclipleft y hy] at hv
        norm_num at hv
        linarith
      · have hv := congrArg Subtype.val h0
        rw [hclipright x (lt_of_not_ge hx)] at hv
        norm_num at hv
        linarith
    · have hh := hband.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh1 := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) hh
        rw [hclipright x (lt_of_not_ge hx), hclipright y (lt_of_not_ge hy)] at hh1
        linarith
      · apply Subtype.ext
        have hh2 := congrArg (fun z : I × BandWidth => (z.2 : ℝ)) hh
        change -(x.2 : ℝ) = -(y.2 : ℝ) at hh2
        exact neg_injective hh2
  let g : EuclideanSpace ℝ (Fin 2) → S := fun z =>
    G (projIcc 0 2 (by norm_num) (z 0), projIcc (-1) 1 (by norm_num) (z 1))
  have hgcont : Continuous g := hGcont.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hginj : InjOn g U := by
    intro x hx y hy he
    have hh := hGinj
      (projIcc 0 2 (by norm_num) (x 0), projIcc (-1) 1 (by norm_num) (x 1))
      (projIcc 0 2 (by norm_num) (y 0), projIcc (-1) 1 (by norm_num) (y 1))
      (by rw [(hclip x hx).1]; exact hx.1.1)
      (by rw [(hclip x hx).1]; exact hx.1.2)
      (by rw [(hclip y hy).1]; exact hy.1.1)
      (by rw [(hclip y hy).1]; exact hy.1.2) he
    have h0 := congrArg (fun z : P => (z.1 : ℝ)) hh
    have h1 := congrArg (fun z : P => (z.2 : ℝ)) hh
    rw [(hclip x hx).1, (hclip y hy).1] at h0
    rw [(hclip x hx).2, (hclip y hy).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hTubeChartOpen2 : IsOpen (g '' U) :=
    surface_invariance_of_domain_probe g U hUopen hgcont.continuousOn hginj
  let gU : U → S := fun z => g z
  have hgUopen : IsOpenMap gU := by
    intro V hV
    let W : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' V
    have hW : IsOpen W := hUopen.isOpenMap_subtype_val V hV
    have hWU : W ⊆ U := by
      rintro z ⟨w,hw,rfl⟩
      exact w.property
    have hWi : InjOn g W := hginj.mono hWU
    have heq : gU '' V = g '' W := by
      simp only [W, Set.image_image]
      rfl
    rw [heq]
    exact surface_invariance_of_domain_probe g W hW hgcont.continuousOn hWi
  have hgUembedded : IsOpenEmbedding gU :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hgcont.comp continuous_subtype_val)
      (by intro x y he; exact Subtype.ext (hginj x.property y.property he)) hgUopen
  let tubeChart2 : U ≃ₜ Set.range gU := hgUembedded.isEmbedding.toHomeomorph
  have hFG (u : I) (hu0 : 0 < (u : ℝ)) (t : BandWidth) :
      F (⟨(u : ℝ)+1, by constructor <;> linarith [u.property.1,u.property.2]⟩, t) =
      G (⟨(u : ℝ), ⟨u.property.1, by linarith [u.property.2]⟩⟩, t) := by
    dsimp only [F,G]
    rw [if_neg (show ¬ (u : ℝ)+1 ≤ 1 by linarith), if_pos u.property.2]
    dsimp only [right,left2]
    simp only [add_sub_cancel_right]
  have hGF (u : I) (hu0 : 0 < (u : ℝ)) (t : BandWidth) :
      F (⟨(u : ℝ), ⟨u.property.1, by linarith [u.property.2]⟩⟩, t) =
      G (⟨(u : ℝ)+1, by constructor <;> linarith [u.property.1,u.property.2]⟩,
        flipBandWidth true t) := by
    dsimp only [F,G]
    rw [if_pos u.property.2, if_neg (show ¬ (u : ℝ)+1 ≤ 1 by linarith)]
    dsimp only [left,right2]
    simp only [add_sub_cancel_right]
    have hflipflip : flipBandWidth true (flipBandWidth true t) = t := by
      apply Subtype.ext
      simp [flipBandWidth]
    rw [hflipflip]
  have hshift (p v : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0 < R)
      (hv : ‖v‖ < R/2) :
      ∃ H : AmbientIsotopy (EuclideanSpace ℝ (Fin 2)),
        (∀ t x, x ∈ Metric.closedBall p (R/2) → H.map (t,x) = x+(t:ℝ) • v) ∧
        (∀ t x, x ∉ Metric.closedBall p R → H.map (t,x) = x) := by
    obtain ⟨K,hflat,hfix⟩ := plane_flat_bump_translation R hR v hv
    let e := Homeomorph.addRight (-p)
    let H : AmbientIsotopy (EuclideanSpace ℝ (Fin 2)) := {
      map := ⟨fun z => K.map (z.1,z.2-p)+p,
        (K.map.continuous.comp (continuous_fst.prodMk
          (continuous_snd.sub continuous_const))).add continuous_const⟩
      homeomorphism_at := fun t => by
        obtain ⟨h,hh⟩ := K.homeomorphism_at t
        refine ⟨(e.trans h).trans e.symm, ?_⟩
        intro x
        simpa [e, Homeomorph.addRight_symm, sub_eq_add_neg] using congrArg (fun y => y+p) (hh (x-p))
      at_zero := fun x => by
        change K.map (⟨0, by norm_num⟩,x-p)+p = x
        rw [K.at_zero]
        module }
    have hdist (x : EuclideanSpace ℝ (Fin 2)) : dist (x-p) 0 = dist x p := by
      rw [_root_.dist_eq_norm, _root_.dist_eq_norm]
      simp
    refine ⟨H, ?_, ?_⟩
    · intro t x hx
      change K.map (t,x-p)+p = x+(t:ℝ) • v
      have hx0 : x-p ∈ Metric.closedBall 0 (R/2) := by
        simpa only [Metric.mem_closedBall, hdist] using hx
      rw [hflat t (x-p) hx0]
      module
    · intro t x hx
      change K.map (t,x-p)+p = x
      have hx0 : x-p ∉ Metric.closedBall 0 R := by
        simpa only [Metric.mem_closedBall, hdist] using hx
      rw [hfix t (x-p) hx0]
      module
  have hpushChart (q : U → S) (hq : IsOpenEmbedding q)
      (p v : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0 < R)
      (hv : ‖v‖ < R/2) (hCU : Metric.closedBall p R ⊆ U) :
      ∃ H : AmbientIsotopy S, ∀ (t : Interval) (x y : U),
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall p (R/2) →
        (y : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2))+(t:ℝ) • v →
        H.map (t,q x) = q y := by
    obtain ⟨L,hL,hfix⟩ := hshift p v R hR hv
    let E : U ≃ₜ Set.range q := hq.isEmbedding.toHomeomorph
    have hsource : IsOpen (Set.range q) := by
      simpa only [Set.image_univ] using hq.isOpenMap Set.univ isOpen_univ
    obtain ⟨K,H,hK,hH,_⟩ := position_surface_chart_lift S (Set.range q) U hsource
      E.symm (Metric.closedBall p R) (isCompact_closedBall _ _) hCU L hfix
    refine ⟨H, ?_⟩
    intro t x y hx hy
    have hcoord : E.symm (K.map (t,E x)) = y := by
      apply Subtype.ext
      have hh := hK t (E x)
      rw [E.symm_apply_apply, hL t (x : EuclideanSpace ℝ (Fin 2)) hx] at hh
      exact hh.trans hy.symm
    have hKy : K.map (t,E x) = E y := by
      apply E.symm.injective
      rw [hcoord,E.symm_apply_apply]
    change H.map (t,(E x : S)) = (E y : S)
    rw [hH t (E x),hKy]
  let p0 : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (1/2) 0
  let v : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (1/16) 0
  have hvnorm : ‖v‖ = 1/16 := by
    have hh := EuclideanSpace.real_norm_sq_eq v
    norm_num [v, Schoenflies.Plane.mk, Fin.sum_univ_two] at hh
    nlinarith [norm_nonneg v]
  have hcenters (n : ℕ) (hn : n ≤ 16) :
      Metric.closedBall (p0+(n:ℝ) • v) (1/4) ⊆ U := by
    intro z hz
    have hd : ‖z-(p0+(n:ℝ) • v)‖ ≤ 1/4 := by
      rw [← _root_.dist_eq_norm]
      exact Metric.mem_closedBall.mp hz
    have hcoord (i : Fin 2) : |z i-(p0+(n:ℝ) • v) i| ≤ 1/4 := by
      have hh := PiLp.norm_apply_le (z-(p0+(n:ℝ) • v)) i
      change |z i-(p0+(n:ℝ) • v) i| ≤ ‖z-(p0+(n:ℝ) • v)‖ at hh
      exact hh.trans hd
    have h0 := abs_le.mp (hcoord 0)
    have h1 := abs_le.mp (hcoord 1)
    have hn' : (n:ℝ) ≤ 16 := by exact_mod_cast hn
    have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    change (0 < z 0 ∧ z 0 < 2) ∧ (-1 < z 1 ∧ z 1 < 1)
    norm_num [p0,v,Schoenflies.Plane.mk] at h0 h1
    constructor <;> constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]
  have hcompose (H K : AmbientIsotopy S) :
      ∃ L : AmbientIsotopy S, ∀ t x, L.map (t,x) = K.map (t,H.map (t,x)) := by
    refine ⟨{ map := ⟨fun z => K.map (z.1,H.map z), K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩, homeomorphism_at := ?_, at_zero := ?_ }, fun t x => rfl⟩
    · intro t
      obtain ⟨hH,hh⟩ := H.homeomorphism_at t
      obtain ⟨hK,hk⟩ := K.homeomorphism_at t
      refine ⟨hH.trans hK, ?_⟩
      intro x
      change hK (hH x) = K.map (t,H.map (t,x))
      rw [hk,hh]
    · intro x
      change K.map (⟨0, by norm_num⟩,H.map (⟨0, by norm_num⟩,x)) = x
      rw [H.at_zero,K.at_zero]
  have hhalf (q : U → S) (hq : IsOpenEmbedding q) :
      ∀ n : ℕ, n ≤ 16 → ∃ H : AmbientIsotopy S, ∀ x y : U,
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall p0 (1/16) →
        (y : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v →
        H.finalMap (q x) = q y := by
    intro n
    induction n with
    | zero =>
      intro hn
      let H : AmbientIsotopy S := {
        map := ⟨Prod.snd, continuous_snd⟩
        homeomorphism_at := fun _ => ⟨Homeomorph.refl S, fun _ => rfl⟩
        at_zero := fun _ => rfl }
      refine ⟨H, ?_⟩
      intro x y hx hy
      have hxy : x = y := Subtype.ext (by simpa using hy.symm)
      rw [← hxy]
      rfl
    | succ n ih =>
      intro hn
      have hn16 : n ≤ 16 := by omega
      obtain ⟨H,hH⟩ := ih hn16
      obtain ⟨K,hK⟩ := hpushChart q hq (p0+(n:ℝ) • v) v (1/4)
        (by norm_num) (by rw [hvnorm]; norm_num) (hcenters n hn16)
      obtain ⟨L,hL⟩ := hcompose H K
      refine ⟨L, ?_⟩
      intro x y hx hy
      have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 2))-p0‖ ≤ 1/16 := by
        rw [← _root_.dist_eq_norm]
        exact Metric.mem_closedBall.mp hx
      have hmid : (x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v ∈
          Metric.closedBall (p0+(n:ℝ) • v) (1/16) := by
        rw [Metric.mem_closedBall,_root_.dist_eq_norm]
        have heq : (x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v-(p0+(n:ℝ) • v) =
            (x : EuclideanSpace ℝ (Fin 2))-p0 := by module
        rw [heq]
        exact hxnorm
      let z : U := ⟨(x : EuclideanSpace ℝ (Fin 2))+(n:ℝ) • v,
        hcenters n hn16 (Metric.closedBall_subset_closedBall (by norm_num) hmid)⟩
      have hzflat : (z : EuclideanSpace ℝ (Fin 2)) ∈
          Metric.closedBall (p0+(n:ℝ) • v) ((1/4)/2) :=
        Metric.closedBall_subset_closedBall (by norm_num) hmid
      have hyz : (y : EuclideanSpace ℝ (Fin 2)) = (z : EuclideanSpace ℝ (Fin 2))+
          ((⟨1,by norm_num⟩ : Interval) : ℝ) • v := by
        rw [hy]
        dsimp [z]
        push_cast
        module
      have hstep := hK (⟨1,by norm_num⟩ : Interval) z y hzflat hyz
      change L.map (⟨1,by norm_num⟩,q x) = q y
      rw [hL]
      change K.finalMap (H.finalMap (q x)) = q y
      rw [hH x z hx rfl]
      exact hstep
  obtain ⟨Hf,hHf⟩ := hhalf fU hfUembedded 16 (by omega)
  obtain ⟨Hg,hHg⟩ := hhalf gU hgUembedded 16 (by omega)
  obtain ⟨H,hH⟩ := hcompose Hf Hg
  have hfcoords (u t : ℝ) (hu : u ∈ Icc (0:ℝ) 2) (ht : t ∈ Icc (-1:ℝ) 1) :
      f (Schoenflies.Plane.mk u t) = F (⟨u,hu⟩,⟨t,ht⟩) := by
    simp [f,Schoenflies.Plane.mk,projIcc_of_mem (show (0:ℝ) ≤ 2 by norm_num) hu,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ht]
  have hgcoords (u t : ℝ) (hu : u ∈ Icc (0:ℝ) 2) (ht : t ∈ Icc (-1:ℝ) 1) :
      g (Schoenflies.Plane.mk u t) = G (⟨u,hu⟩,⟨t,ht⟩) := by
    simp [g,Schoenflies.Plane.mk,projIcc_of_mem (show (0:ℝ) ≤ 2 by norm_num) hu,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ht]
  have hFGcoords (u : I) (hu0 : 0 < (u:ℝ)) (t : BandWidth) :
      f (Schoenflies.Plane.mk ((u:ℝ)+1) t) = g (Schoenflies.Plane.mk u t) := by
    rw [hfcoords _ _ (by constructor <;> linarith [u.property.1,u.property.2]) t.property,
      hgcoords _ _ ⟨u.property.1,by linarith [u.property.2]⟩ t.property]
    exact hFG u hu0 t
  have hGFcoords (u : I) (hu0 : 0 < (u:ℝ)) (t : BandWidth) :
      f (Schoenflies.Plane.mk u t) = g (Schoenflies.Plane.mk ((u:ℝ)+1) (-(t:ℝ))) := by
    rw [hfcoords _ _ ⟨u.property.1,by linarith [u.property.2]⟩ t.property,
      hgcoords _ _ (by constructor <;> linarith [u.property.1,u.property.2])
        (by constructor <;> linarith [t.property.1,t.property.2])]
    exact hGF u hu0 t
  have hnear (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Metric.closedBall p0 (1/16)) :
      z 0 ∈ Ioo (0:ℝ) 1 ∧ z 1 ∈ Ioo (-1:ℝ) 1 := by
    have hd : ‖z-p0‖ ≤ 1/16 := by
      rw [← _root_.dist_eq_norm]
      exact Metric.mem_closedBall.mp hz
    have hcoord (i : Fin 2) : |z i-p0 i| ≤ 1/16 := by
      have hh := PiLp.norm_apply_le (z-p0) i
      change |z i-p0 i| ≤ ‖z-p0‖ at hh
      exact hh.trans hd
    have h0 := abs_le.mp (hcoord 0)
    have h1 := abs_le.mp (hcoord 1)
    norm_num [p0,Schoenflies.Plane.mk] at h0 h1
    constructor <;> constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]
  let w : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk 1 0
  have h16v : (16:ℝ) • v = w := by
    ext i
    fin_cases i <;> norm_num [v,w,Schoenflies.Plane.mk]
  let refl : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => Schoenflies.Plane.mk (z 0) (-(z 1))
  have hreturn (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Metric.closedBall p0 (1/16)) :
      H.finalMap (f z) = f (refl z) := by
    obtain ⟨hz0,hz1⟩ := hnear z hz
    have hzU : z ∈ U := ⟨⟨hz0.1,by linarith [hz0.2]⟩,hz1⟩
    have hzwU : z+w ∈ U := by
      change ((z+w) 0 ∈ Ioo (0:ℝ) 2) ∧ ((z+w) 1 ∈ Ioo (-1:ℝ) 1)
      norm_num [w,Schoenflies.Plane.mk]
      constructor <;> constructor <;> linarith [hz0.1,hz0.2,hz1.1,hz1.2]
    let x : U := ⟨z,hzU⟩
    let y : U := ⟨z+w,hzwU⟩
    have hy : (y : EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2))+(16:ℝ) • v := by
      dsimp [x,y]
      rw [h16v]
    have hfirst := hHf x y hz hy
    have hsecond := hHg x y hz hy
    change Hf.finalMap (f z) = f (z+w) at hfirst
    change Hg.finalMap (g z) = g (z+w) at hsecond
    let u : I := ⟨z 0,⟨hz0.1.le,hz0.2.le⟩⟩
    let t : BandWidth := ⟨z 1,⟨hz1.1.le,hz1.2.le⟩⟩
    have hzmk : Schoenflies.Plane.mk (z 0) (z 1) = z := by
      ext i
      fin_cases i <;> rfl
    have hplus : z+w = Schoenflies.Plane.mk (z 0+1) (z 1) := by
      ext i
      fin_cases i <;> simp [w,Schoenflies.Plane.mk]
    have hfg : f (z+w) = g z := by
      rw [hplus,← hzmk]
      exact hFGcoords u hz0.1 t
    have hgf : g (z+w) = f (refl z) := by
      rw [hplus]
      let tn : BandWidth := ⟨-(z 1),by constructor <;> linarith [hz1.1,hz1.2]⟩
      have hh := hGFcoords u hz0.1 tn
      simpa only [u,tn,refl,neg_neg] using hh.symm
    change H.map (⟨1,by norm_num⟩,f z) = f (refl z)
    rw [hH]
    change Hg.finalMap (Hf.finalMap (f z)) = f (refl z)
    rw [hfirst,hfg,hsecond,hgf]
  have hp0U : p0 ∈ U := by
    apply hcenters 0 (by omega)
    simp
  letI : Nonempty U := ⟨⟨p0,hp0U⟩⟩
  let qE := hfUembedded.toOpenPartialHomeomorph fU
  have hqtarget : qE.target = Set.range fU := by
    simp [qE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  let A : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S := {
    toFun := f
    invFun := fun y => (qE.symm y : EuclideanSpace ℝ (Fin 2))
    source := U
    target := Set.range fU
    map_source' := fun z hz => ⟨⟨z,hz⟩,rfl⟩
    map_target' := fun y hy => (qE.symm y).property
    left_inv' := fun z hz => by
      have hh := hfUembedded.toOpenPartialHomeomorph_left_inv (f := fU) (x := ⟨z,hz⟩)
      exact congrArg Subtype.val hh
    right_inv' := fun y hy => by
      exact hfUembedded.toOpenPartialHomeomorph_right_inv (f := fU) hy
    continuousOn_toFun := hfcont.continuousOn
    continuousOn_invFun := by
      apply continuous_subtype_val.comp_continuousOn
      simpa only [OpenPartialHomeomorph.symm_source,hqtarget] using qE.symm.continuousOn
    open_source := hUopen
    open_target := by simpa only [Set.image_univ] using hfUopen Set.univ isOpen_univ }
  have hAapply (z : EuclideanSpace ℝ (Fin 2)) : A z = f z := rfl
  let x : S := f p0
  have hfixx : H.finalMap x = x := by
    have hh := hreturn p0 (by simp)
    have hrefl : refl p0 = p0 := by ext i; fin_cases i <;> simp [refl,p0,Schoenflies.Plane.mk]
    simpa only [hrefl] using hh
  let Fend : C(S,S) := ⟨H.finalMap,
    H.map.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hpres : ∀ y ∈ ({x}ᶜ : Set S), Fend y ∈ ({x}ᶜ : Set S) := by
    intro y hy
    change y ≠ x at hy
    change Fend y ≠ x
    intro hh
    obtain ⟨e,he⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    apply hy
    apply e.injective
    rw [he,he]
    exact hh.trans hfixx.symm
  have hhom : ContinuousMap.Homotopic Fend (ContinuousMap.id S) := by
    apply ContinuousMap.Homotopic.symm
    exact ⟨{ toContinuousMap := H.map, map_zero_left := H.at_zero, map_one_left := fun _ => rfl }⟩
  let c : (EuclideanSpace ℝ (Fin 2)) ≃ₜ (ℝ × ℝ) := {
    toFun := fun z => (z 0,z 1)
    invFun := fun z => Schoenflies.Plane.mk z.1 z.2
    left_inv := fun z => by ext i; fin_cases i <;> rfl
    right_inv := fun z => by rcases z with ⟨u,t⟩; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let b : (EuclideanSpace ℝ (Fin 2)) ≃ₜ (ℝ × ℝ) :=
    (Homeomorph.addRight (-p0)).trans c
  let e : OpenPartialHomeomorph S (ℝ × ℝ) := A.symm.trans b.toOpenPartialHomeomorph
  have hxsource : x ∈ e.source := ⟨A.map_source hp0U,Set.mem_univ _⟩
  have hex : e x = 0 := by
    change c (A.symm x + -p0) = 0
    have hAx : A.symm x = p0 := A.left_inv hp0U
    rw [hAx,add_neg_cancel]
    rfl
  have hbinv (z : ℝ × ℝ) : b.symm z = Schoenflies.Plane.mk z.1 z.2+p0 := by
    change (Homeomorph.addRight (-p0)).symm (c.symm z) = Schoenflies.Plane.mk z.1 z.2+p0
    rw [Homeomorph.addRight_symm,neg_neg]
    rfl
  have heinv (z : ℝ × ℝ) : e.symm z = f (Schoenflies.Plane.mk z.1 z.2+p0) := by
    change A (b.symm z) = _
    rw [hbinv]
    rfl
  have hsmallball (z : ℝ × ℝ) (hz : z ∈ Metric.closedBall (0 : ℝ × ℝ) (1/64)) :
      Schoenflies.Plane.mk z.1 z.2+p0 ∈ Metric.closedBall p0 (1/16) := by
    have hp : |z.1| ≤ 1/64 ∧ |z.2| ≤ 1/64 := by
      have hd : dist z ((0,0) : ℝ × ℝ) ≤ 1/64 := Metric.mem_closedBall.mp hz
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq] at hd
      simpa only [sub_zero,max_le_iff] using hd
    have h1sq : z.1^2 ≤ (1/64:ℝ)^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg z.1) (by norm_num : (0:ℝ) ≤ 1/64)).mpr hp.1
      simpa only [sq_abs] using hh
    have h2sq : z.2^2 ≤ (1/64:ℝ)^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg z.2) (by norm_num : (0:ℝ) ≤ 1/64)).mpr hp.2
      simpa only [sq_abs] using hh
    have hh := EuclideanSpace.real_norm_sq_eq (Schoenflies.Plane.mk z.1 z.2)
    norm_num [Schoenflies.Plane.mk,Fin.sum_univ_two] at hh
    rw [Metric.mem_closedBall,_root_.dist_eq_norm,add_sub_cancel_right]
    nlinarith [norm_nonneg (Schoenflies.Plane.mk z.1 z.2)]
  have hball : Metric.closedBall (0 : ℝ × ℝ) (1/64) ⊆ e.target := by
    intro z hz
    have hsmall := hsmallball z hz
    have hzU : Schoenflies.Plane.mk z.1 z.2+p0 ∈ U :=
      hcenters 0 (by omega) (by simpa using Metric.closedBall_subset_closedBall (by norm_num : (1/16:ℝ) ≤ 1/4) hsmall)
    change z ∈ Set.univ ∩ b.symm ⁻¹' A.source
    refine ⟨Set.mem_univ _, ?_⟩
    change b.symm z ∈ U
    rw [hbinv]
    exact hzU
  have hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) (1/64),
      Fend (e.symm z) = e.symm (planeReflection z) := by
    intro z hz
    rw [heinv,heinv]
    change H.finalMap (f (Schoenflies.Plane.mk z.1 z.2+p0)) = _
    rw [hreturn _ (hsmallball z (Metric.ball_subset_closedBall hz))]
    apply congrArg f
    ext i
    fin_cases i <;> simp [refl,p0,planeReflection,Schoenflies.Plane.mk]
  have hnegative := chart_reflection_germ_relativeHomologyMap S x e hxsource hex
    Fend hpres (1/64) (by norm_num) hball hgerm
  exact ⟨x,⟨{ map := Fend, preserves := hpres, isotopy := hhom, acts_neg := hnegative }⟩⟩

end CurveComplex.LocalSurgery
