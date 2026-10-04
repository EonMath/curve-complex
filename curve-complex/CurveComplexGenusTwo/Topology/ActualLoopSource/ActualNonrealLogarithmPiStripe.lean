import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualContinuousLogarithmStripe
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A genuine continuous nonreal exponential on a positive germ interval
constructs ONE consecutive-π phase stripe. Neither a stripe index nor a
chosen sign bank is assumed. Both branches of the real axis are excluded. -/
theorem actual_nonreal_logarithm_pi_stripe
    (d : ℝ) (hd : 0<d) (L : C(Ioc (0:ℝ) d,ℂ))
    (hnonreal : ∀ t, (Complex.exp (L t)).im≠0) :
    ∃ k : ℤ, ∀ t, (L t).im ∈ Ioo ((k:ℝ)*Real.pi) (((k:ℝ)+1)*Real.pi) := by
  let : ContractibleSpace (Ioc (0:ℝ) d) :=
    (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).contractibleSpace ⟨d,hd,le_rfl⟩
  obtain ⟨n,_,hn⟩ := actual_continuous_logarithm_stripe d hd L
    (fun t => Complex.mem_slitPlane_iff.mpr (Or.inr (hnonreal t)))
  let c : ℝ := (n:ℝ)*(2*Real.pi)
  have havoid (t : Ioc (0:ℝ) d) : (L t).im≠c := by
    intro he
    have hperiod : L t=((L t).re:ℂ)+n*(2*(Real.pi:ℂ)*Complex.I) := by
      apply Complex.ext
      · simp [Complex.mul_re,Complex.mul_im]
      · simpa [Complex.mul_re,Complex.mul_im,c] using he
    have hexp : Complex.exp (L t)=Complex.exp ((L t).re:ℂ) :=
      Complex.exp_eq_exp_iff_exists_int.mpr ⟨n,hperiod⟩
    apply hnonreal t
    rw [hexp]
    simp
  have hc : Continuous (fun t => (L t).im) := Complex.continuous_im.comp L.continuous
  have hcover : range (fun t => (L t).im) ⊆ Iio c ∪ Ioi c := by
    rintro x ⟨t,rfl⟩
    exact lt_or_gt_of_ne (havoid t)
  have hdis : Disjoint (Iio c) (Ioi c) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (show x<c from hx) (show c<x from hy)
  rcases (isPreconnected_range hc).subset_or_subset isOpen_Iio isOpen_Ioi hdis hcover with hlo | hhi
  · refine ⟨2*n-1,?_⟩
    intro t
    have ht := hlo (mem_range_self t)
    have hb := (hn t).1
    change (L t).im<c at ht
    dsimp [c] at ht
    norm_num only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
    constructor <;> nlinarith
  · refine ⟨2*n,?_⟩
    intro t
    have ht := hhi (mem_range_self t)
    have hb := (hn t).2
    change c<(L t).im at ht
    dsimp [c] at ht
    norm_num only [Int.cast_mul,Int.cast_ofNat]
    constructor <;> nlinarith
end CurveComplex.HyperellipticModel
