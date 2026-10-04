import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.Basic
namespace CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
open CurveComplex Schoenflies Set _root_.Topology
set_option maxHeartbeats 2000000

/-- Reflection across the literal boundary axis proves relative openness of an
actual embedded half-band, including its whole initial width edge. -/
theorem halfPlaneBandOpenness
    (E : C(CurveComplex.Interval × Icc (-1 : ℝ) 1, Plane))
    (hE : IsEmbedding E)
    (hzero : ∀ w, E (0,w) 0 = 0)
    (hpos : ∀ t : CurveComplex.Interval, 0 < (t:ℝ) → ∀ w, 0 < E (t,w) 0) :
    IsOpen {y : {p : Plane | 0 ≤ p 0} |
      y.val ∈ E '' {z | (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1}} := by
  let k : Plane → CurveComplex.Interval × Icc (-1 : ℝ) 1 := fun z =>
    (projIcc 0 1 zero_le_one |z 0|,projIcc (-1) 1 (by norm_num) (z 1))
  have hkc : Continuous k := by dsimp [k]; fun_prop
  let c : Plane → Plane := E ∘ k
  have hcc : Continuous c := E.continuous.comp hkc
  let neg : Plane → Plane := fun z => Plane.mk (-z 0) (z 1)
  have hnegc : Continuous neg := by dsimp [neg]; fun_prop
  have hnegi : Function.Injective neg := by
    intro z w he
    have h0 := congrArg (fun p : Plane => p 0) he
    have h1 := congrArg (fun p : Plane => p 1) he
    ext j
    fin_cases j
    · change -z 0 = -w 0 at h0
      change z 0 = w 0
      linarith
    · exact h1
  let F : Plane → Plane := fun z => if z 0 ≤ 0 then neg (c z) else c z
  have hc0 (z : Plane) (hz : z 0 = 0) : c z 0 = 0 := by
    have hk0 : (k z).1 = 0 := by
      apply Subtype.ext
      simp [k,hz]
    change E (k z) 0 = 0
    have hk : k z = (0,(k z).2) := Prod.ext hk0 rfl
    rw [hk]
    exact hzero _
  have hFc : Continuous F := by
    apply continuous_if_le (by fun_prop) continuous_const
      (hnegc.comp hcc).continuousOn hcc.continuousOn
    intro z hz
    change neg (c z) = c z
    ext j
    fin_cases j
    · change -(c z 0) = c z 0
      rw [hc0 z hz]
      ring
    · rfl
  let O : Set Plane := {z | |z 0| < 1 ∧ |z 1| < 1}
  have hO : IsOpen O :=
    (isOpen_lt (show Continuous (fun z : Plane => |z 0|) by fun_prop) continuous_const).inter
      (isOpen_lt (show Continuous (fun z : Plane => |z 1|) by fun_prop) continuous_const)
  have hk0 (z : Plane) (hz : z ∈ O) : ((k z).1 : ℝ) = |z 0| := by
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one
      ⟨abs_nonneg _,hz.1.le⟩)
  have hk1 (z : Plane) (hz : z ∈ O) : ((k z).2 : ℝ) = z 1 := by
    exact congrArg Subtype.val (projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
      ⟨(abs_lt.mp hz.2).1.le,(abs_lt.mp hz.2).2.le⟩)
  have hcnonneg (z : Plane) (hz : z ∈ O) : 0 ≤ c z 0 := by
    by_cases he : z 0 = 0
    · rw [hc0 z he]
    · apply (hpos (k z).1 _ (k z).2).le
      rw [hk0 z hz]
      exact abs_pos.mpr he
  have hcpos (z : Plane) (hz : z ∈ O) (hne : z 0 ≠ 0) : 0 < c z 0 := by
    apply hpos (k z).1 _ (k z).2
    rw [hk0 z hz]
    exact abs_pos.mpr hne
  have hFnonneg (z : Plane) (hz : 0 ≤ z 0) : F z = c z := by
    dsimp only [F]
    split_ifs with hn
    · have he : z 0 = 0 := le_antisymm hn hz
      ext j
      fin_cases j
      · change -(c z 0) = c z 0
        rw [hc0 z he]
        ring
      · rfl
    · rfl
  have hFi : InjOn F O := by
    intro z hz w hw he
    dsimp only [F] at he
    split_ifs at he with hnz hnw hnw
    · have hkk := hE.injective (hnegi he)
      have h0 := congrArg (fun p : CurveComplex.Interval × Icc (-1:ℝ) 1 => (p.1:ℝ)) hkk
      have h1 := congrArg (fun p : CurveComplex.Interval × Icc (-1:ℝ) 1 => (p.2:ℝ)) hkk
      rw [hk0 z hz,hk0 w hw,abs_of_nonpos hnz,abs_of_nonpos hnw] at h0
      rw [hk1 z hz,hk1 w hw] at h1
      ext j
      fin_cases j
      · change z 0 = w 0
        linarith
      · exact h1
    · have h0 := congrArg (fun p : Plane => p 0) he
      have hp := hcpos w hw (ne_of_gt (lt_of_not_ge hnw))
      have hn := hcnonneg z hz
      change -(c z 0) = c w 0 at h0
      linarith
    · have h0 := congrArg (fun p : Plane => p 0) he
      have hp := hcpos z hz (ne_of_gt (lt_of_not_ge hnz))
      have hn := hcnonneg w hw
      change c z 0 = -(c w 0) at h0
      linarith
    · have hkk := hE.injective he
      have h0 := congrArg (fun p : CurveComplex.Interval × Icc (-1:ℝ) 1 => (p.1:ℝ)) hkk
      have h1 := congrArg (fun p : CurveComplex.Interval × Icc (-1:ℝ) 1 => (p.2:ℝ)) hkk
      rw [hk0 z hz,hk0 w hw,abs_of_pos (lt_of_not_ge hnz),abs_of_pos (lt_of_not_ge hnw)] at h0
      rw [hk1 z hz,hk1 w hw] at h1
      ext j
      fin_cases j <;> assumption
  have hFO : IsOpen (F '' O) := surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
  have heq : {y : {p : Plane | 0 ≤ p 0} |
      y.val ∈ E '' {z | (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1}} =
      Subtype.val ⁻¹' (F '' O) := by
    ext y
    constructor
    · rintro ⟨z,hz,he⟩
      let v : Plane := Plane.mk z.1 z.2
      have hv : v ∈ O := by
        constructor
        · change |(z.1:ℝ)| < 1
          simpa only [abs_of_nonneg z.1.property.1] using hz.1
        · exact abs_lt.mpr hz.2
      have hkv : k v = z := by
        apply Prod.ext
        · apply Subtype.ext
          rw [hk0 v hv]
          exact abs_of_nonneg z.1.property.1
        · apply Subtype.ext
          exact hk1 v hv
      refine ⟨v,hv,?_⟩
      rw [hFnonneg v z.1.property.1]
      change E (k v) = y.val
      rw [hkv]
      exact he
    · rintro ⟨v,hv,he⟩
      have hnv : 0 ≤ v 0 := by
        by_contra hn
        have hvneg : v 0 < 0 := lt_of_not_ge hn
        have hc := hcpos v hv hvneg.ne
        have hh := congrArg (fun p : Plane => p 0) he
        have hy : 0 ≤ y.val 0 := y.property
        change F v 0 = y.val 0 at hh
        have hf : F v = neg (c v) := if_pos hvneg.le
        rw [hf] at hh
        change -(c v 0) = y.val 0 at hh
        linarith
      refine ⟨k v,⟨?_,?_,?_⟩,?_⟩
      · rw [hk0 v hv]; exact hv.1
      · rw [hk1 v hv]; exact (abs_lt.mp hv.2).1
      · rw [hk1 v hv]; exact (abs_lt.mp hv.2).2
      · exact (hFnonneg v hnv).symm.trans he
  rw [heq]
  exact hFO.preimage continuous_subtype_val
end CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
