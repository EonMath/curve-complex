import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualTopologicalUniversalCoverPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualComponentHyperbolicDevelopmentPROVED
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualDevelopedGeodesicLinesReviewRequest
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Quotient
import Mathlib
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
import CurveComplexGenusTwo.Hyperbolic.Stabilizer
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import CurveComplexGenusTwo.Hyperbolic.OriginalG2.DiskEndpointTransport
import CurveComplexGenusTwo.Hyperbolic.OriginalG2.G2DiskCrossing

namespace CurveComplex.Hyperbolic

open Set Topology Filter CurveComplex.LocalSurgery
open scoped Manifold
open Matrix
open scoped MatrixGroups UpperHalfPlane
private theorem periodic_real_lift_homeomorphism
    (f : C(ℝ,ℝ)) (hfi : Function.Injective f) (P : ℝ) (hP : 0 < P)
    (hexp : Function.Periodic (fun t => Circle.exp (f t)) P) :
    ∃ e : ℝ ≃ₜ ℝ, ∀ t, e t = f t := by
  obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp (hexp 0)
  have hdrift : ∀ t : ℝ, f (t+P)=f t+(n:ℝ)*(2*Real.pi) := by
    have hh : (fun t : ℝ => f (t+P)) =
        (fun t => f t+(n:ℝ)*(2*Real.pi)) := by
      refine Circle.isCoveringMap_exp.eq_of_comp_eq
        (f.continuous.comp (continuous_id.add continuous_const))
        (f.continuous.add continuous_const) ?_ 0 ?_
      · funext t
        change Circle.exp (f (t+P))=Circle.exp (f t+(n:ℝ)*(2*Real.pi))
        rw [show Circle.exp (f (t+P))=Circle.exp (f t) from hexp t,
          Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
      · simpa only [zero_add] using hn
    exact fun t => congrFun hh t
  let D : ℝ := (n:ℝ)*(2*Real.pi)
  have hD : D ≠ 0 := by
    intro hz
    have hh := hdrift 0
    change f (0+P)=f 0+D at hh
    rw [hz,add_zero,zero_add] at hh
    exact hP.ne' (hfi hh)
  let err (t : ℝ) := f t-D/P*t
  have herr : Function.Periodic err P := by
    intro t
    dsimp [err,D]
    rw [hdrift]
    field_simp [hP.ne'] <;> ring
  have hmul (k : ℤ) : f ((k:ℝ)*P)=f 0+(k:ℝ)*D := by
    have hh := herr.zsmul k 0
    simp only [zsmul_eq_mul,zero_add] at hh
    dsimp [err] at hh
    have hp : D/P*((k:ℝ)*P)=(k:ℝ)*D := by field_simp [hP.ne']
    rw [hp,mul_zero,sub_zero] at hh
    linarith
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨k,hk⟩ := exists_int_gt ((y-f 0)/|D|)
    obtain ⟨j,hj⟩ := exists_int_lt ((y-f 0)/|D|)
    have habs : 0 < |D| := abs_pos.mpr hD
    have hupper : y < f 0+(k:ℝ)*|D| := by
      have := (div_lt_iff₀ habs).mp hk
      linarith
    have hlower : f 0+(j:ℝ)*|D| < y := by
      have := (lt_div_iff₀ habs).mp hj
      linarith
    rcases le_or_gt 0 D with hpos | hneg
    · rw [abs_of_nonneg hpos] at hupper hlower
      obtain ⟨t,ht⟩ := intermediate_value_univ ((j:ℝ)*P) ((k:ℝ)*P)
        f.continuous (by rw [hmul,hmul]; exact ⟨hlower.le,hupper.le⟩)
      exact ⟨t,ht⟩
    · rw [abs_of_neg hneg] at hupper hlower
      obtain ⟨t,ht⟩ := intermediate_value_univ (((-j:ℤ):ℝ)*P)
        (((-k:ℤ):ℝ)*P) f.continuous
        (by rw [hmul,hmul]; simp only [Int.cast_neg]; constructor <;> nlinarith)
      exact ⟨t,ht⟩
  rcases f.continuous.strictMono_of_inj hfi with hm | ha
  · let e := (hm.orderIsoOfSurjective f hfs).toHomeomorph
    exact ⟨e,fun _ => rfl⟩
  · let e := (StrictMono.orderIsoOfSurjective (β := ℝᵒᵈ) f ha hfs).toHomeomorph
    exact ⟨{ e with toEquiv := e.toEquiv },fun _ => rfl⟩

private theorem anchored_geodesic_line_follows_embedded_boundary
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (p : P → X) (hp : IsCoveringMap p)
    (c : C(Circle,X)) (hc : IsEmbedding c) (γ : C(ℝ,X)) (f : C(ℝ,P))
    (hproj : ∀ t, p (f t) = γ t)
    (hfinj : Function.Injective f)
    (period : ℝ) (hperiod : 0 < period)
    (hγperiod : Function.Periodic γ period)
    (hrange : Set.range γ = Set.range c)
    (L : C(ℝ × Interval,P))
    (hL : ∀ s : ℝ, p (L (s,0)) = c (Circle.exp s))
    (u₀ : ℝ) (hanchor : L (0,0) = f u₀)
    (hγ₀ : γ u₀ = c 1) :
    ∃ ψ : ℝ ≃ₜ ℝ, ψ u₀ = 0 ∧
      (∀ t : ℝ, L (ψ t,0) = f t) ∧
      Set.range (fun s : ℝ => L (s,0)) = Set.range f := by
  have hγmem (t : ℝ) : γ t ∈ Set.range c := by
    rw [←hrange]
    exact Set.mem_range_self t
  let θ : C(ℝ,Circle) :=
    ⟨fun t => hc.toHomeomorph.symm ⟨γ t,hγmem t⟩,
      hc.toHomeomorph.symm.continuous.comp
        (γ.continuous.subtype_mk _)⟩
  have hθ₀ : θ u₀ = 1 := by
    apply hc.injective
    have he := hc.toHomeomorph.apply_symm_apply
      (⟨γ u₀,hγmem u₀⟩ : Set.range c)
    exact (congrArg Subtype.val he).trans hγ₀
  have hbase : Circle.exp 0 = θ u₀ := by simp [hθ₀]
  obtain ⟨ψ,⟨hψ₀,hψ⟩,_⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts θ u₀ 0 hbase
  have hsame : (fun t : ℝ => L (ψ t,0)) = f := by
    refine hp.eq_of_comp_eq
      (L.continuous.comp (ψ.continuous.prodMk continuous_const))
      f.continuous ?_ u₀ ?_
    · funext t
      change p (L (ψ t,0)) = p (f t)
      rw [hL]
      have hθ := congrFun hψ t
      change Circle.exp (ψ t) = θ t at hθ
      rw [hθ]
      have he := hc.toHomeomorph.apply_symm_apply
        (⟨γ t,hγmem t⟩ : Set.range c)
      exact (congrArg Subtype.val he).trans (hproj t).symm
    · simpa [hψ₀] using hanchor
  have hψinj : Function.Injective ψ := by
    intro t u htu
    apply hfinj
    rw [←congrFun hsame t,←congrFun hsame u,htu]
  have hψperiod : Function.Periodic (fun t => Circle.exp (ψ t)) period := by
    intro t
    have heq (v : ℝ) : Circle.exp (ψ v) = θ v := congrFun hψ v
    change Circle.exp (ψ (t+period)) = Circle.exp (ψ t)
    rw [heq,heq]
    apply hc.injective
    have hθ (v : ℝ) : c (θ v) = γ v := by
      have he := hc.toHomeomorph.apply_symm_apply
        (⟨γ v,hγmem v⟩ : Set.range c)
      exact congrArg Subtype.val he
    rw [hθ,hθ,hγperiod]
  obtain ⟨e,he⟩ := periodic_real_lift_homeomorphism
    ψ hψinj period hperiod hψperiod
  refine ⟨e,he u₀ |>.trans hψ₀,?_,?_⟩
  · intro t
    rw [he]
    exact congrFun hsame t
  · apply Set.Subset.antisymm
    · rintro _ ⟨s,rfl⟩
      obtain ⟨t,ht⟩ := e.surjective s
      refine ⟨t,?_⟩
      rw [←ht,he]
      exact (congrFun hsame t).symm
    · rintro _ ⟨t,rfl⟩
      exact ⟨e t,(by rw [he]; exact congrFun hsame t)⟩


private theorem aligned_periodic_strip_axis_translation
    (δ : H2 ≃ᵢ H2) (f : ℝ → H2) (hf : Isometry f)
    (L : C(ℝ × Interval,H2)) (ψ : ℝ ≃ₜ ℝ)
    (halign : ∀ u, L (ψ u,0) = f u)
    (hperiod : ∀ (s : ℝ) (t : Interval),
      L (s+2*Real.pi,t) = δ (L (s,t))) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ u : ℝ, δ (f u) = f (u+c) := by
  let k (u : ℝ) : ℝ := ψ.symm (ψ u+2*Real.pi)
  have hψk (u : ℝ) : ψ (k u) = ψ u+2*Real.pi := by
    exact ψ.apply_symm_apply _
  have hδf (u : ℝ) : δ (f u) = f (k u) := by
    rw [←halign u,←halign (k u),hψk]
    exact (hperiod (ψ u) 0).symm
  have hkmono : StrictMono k := by
    rcases ψ.continuous.strictMono_of_inj ψ.injective with hm | ha
    · intro u v huv
      apply hm.lt_iff_lt.mp
      rw [hψk,hψk]
      simpa only [add_comm] using add_lt_add_right (hm huv) (2*Real.pi)
    · intro u v huv
      apply ha.lt_iff_gt.mp
      rw [hψk,hψk]
      simpa only [add_comm] using add_lt_add_right (ha huv) (2*Real.pi)
  have hkdist (u v : ℝ) : dist (k u) (k v) = dist u v := by
    have h := δ.isometry.dist_eq (f u) (f v)
    rw [hδf,hδf,hf.dist_eq,hf.dist_eq] at h
    exact h
  let c : ℝ := k 0
  have hc : c ≠ 0 := by
    intro hz
    have h := hψk 0
    rw [show k 0 = 0 from hz] at h
    have hpi : (2*Real.pi:ℝ) ≠ 0 := by positivity
    exact hpi (by linarith)
  have hk (u : ℝ) : k u = u+c := by
    have hd := hkdist u 0
    rw [Real.dist_eq,Real.dist_eq,sub_zero] at hd
    rcases le_total 0 u with hu | hu
    · have horder : k 0 ≤ k u := hkmono.monotone hu
      rw [abs_of_nonneg (sub_nonneg.mpr horder),abs_of_nonneg hu] at hd
      dsimp [c]
      linarith
    · have horder : k u ≤ k 0 := hkmono.monotone hu
      rw [abs_of_nonpos (sub_nonpos.mpr horder),abs_of_nonpos hu] at hd
      dsimp [c]
      linarith
  exact ⟨c,hc,fun u => by rw [hδf,hk]⟩

#print axioms aligned_periodic_strip_axis_translation


private theorem aligned_strip_original_stays_bounded_from_axis
    (δ : H2 ≃ᵢ H2) (f : ℝ → H2) (hf : Isometry f)
    (L : C(ℝ × Interval,H2)) (ψ : ℝ ≃ₜ ℝ)
    (c : ℝ) (hc : c ≠ 0)
    (halign : ∀ u, L (ψ u,0) = f u)
    (haxis : ∀ u, δ (f u) = f (u+c))
    (hperiod : ∀ (s : ℝ) (t : Interval),
      L (s+2*Real.pi,t) = δ (L (s,t))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ u : ℝ, dist (L (ψ u,1)) (f u) ≤ B := by
  have hlower_inj : Function.Injective (fun s : ℝ => L (s,0)) := by
    intro s t h
    have h' : f (ψ.symm s) = f (ψ.symm t) := by
      simpa only [←halign,ψ.apply_symm_apply] using h
    exact ψ.symm.injective (hf.injective h')
  have hψshift (u : ℝ) : ψ (u+c) = ψ u+2*Real.pi := by
    apply hlower_inj
    change L (ψ (u+c),0) = L (ψ u+2*Real.pi,0)
    rw [halign,hperiod,halign,haxis]
  let error (u : ℝ) := dist (L (ψ u,1)) (f u)
  have hcont : Continuous error := by
    exact (L.continuous.comp (ψ.continuous.prodMk continuous_const)).dist hf.continuous
  have herror : Function.Periodic error c := by
    intro u
    dsimp [error]
    rw [hψshift,hperiod,←haxis]
    exact δ.isometry.dist_eq _ _
  obtain ⟨B,hB⟩ := (herror.isBounded_of_continuous hc hcont).bddAbove
  have hbound (u : ℝ) : dist (L (ψ u,1)) (f u) ≤ B :=
    hB (Set.mem_range_self u)
  exact ⟨B,(dist_nonneg).trans (hbound 0),hbound⟩


private theorem sl_vertical_real_formula
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    (A • verticalPath t : H2).re =
      (A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1)/
        ((A 1 0)^2*(Real.exp t)^2+(A 1 1)^2) := by
  change ((A • verticalPath t : H2):ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [verticalPath,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.normSq_apply]
  ring

private theorem sl_vertical_denominator_pos
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    0 < (A 1 0)^2*(Real.exp t)^2+(A 1 1)^2 := by
  have hdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  by_cases hc : A 1 0=0
  · have hd : A 1 1 ≠ 0 := by
      intro hd
      rw [hc,hd] at hdet
      norm_num at hdet
    simp only [hc,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,zero_add]
    exact sq_pos_of_ne_zero hd
  · have hp := mul_pos (sq_pos_of_ne_zero hc) (sq_pos_of_pos (Real.exp_pos t))
    nlinarith [sq_nonneg (A 1 1)]

private theorem sl_axis_crossing_changes_real_side
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s t u : ℝ)
    (hst : s < t) (htu : t < u)
    (hcross : (A • verticalPath t : H2).re = 0)
    (hnondegenerate : A 0 0*A 1 0 ≠ 0) :
    (A • verticalPath s : H2).re * (A • verticalPath u : H2).re < 0 := by
  have hNt : A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1=0 := by
    rw [sl_vertical_real_formula] at hcross
    exact (div_eq_zero_iff.mp hcross).resolve_right
      (sl_vertical_denominator_pos A t).ne'
  have hsExp : (Real.exp s)^2 < (Real.exp t)^2 := by
    have h := Real.exp_strictMono hst
    nlinarith [Real.exp_pos s, Real.exp_pos t]
  have huExp : (Real.exp t)^2 < (Real.exp u)^2 := by
    have h := Real.exp_strictMono htu
    nlinarith [Real.exp_pos t, Real.exp_pos u]
  let c : ℝ := A 0 0*A 1 0
  let ds : ℝ := (A 1 0)^2*(Real.exp s)^2+(A 1 1)^2
  let du : ℝ := (A 1 0)^2*(Real.exp u)^2+(A 1 1)^2
  have hds : 0 < ds := sl_vertical_denominator_pos A s
  have hdu : 0 < du := sl_vertical_denominator_pos A u
  have hns : c*(Real.exp s)^2+A 0 1*A 1 1 =
      c*((Real.exp s)^2-(Real.exp t)^2) := by
    dsimp [c]
    nlinarith only [hNt]
  have hnu : c*(Real.exp u)^2+A 0 1*A 1 1 =
      c*((Real.exp u)^2-(Real.exp t)^2) := by
    dsimp [c]
    nlinarith only [hNt]
  have hneg : c*((Real.exp s)^2-(Real.exp t)^2) *
      (c*((Real.exp u)^2-(Real.exp t)^2)) < 0 := by
    have hg : ((Real.exp s)^2-(Real.exp t)^2) *
        ((Real.exp u)^2-(Real.exp t)^2) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hsExp) (sub_pos.mpr huExp)
    have hc : 0 < c^2 := sq_pos_of_ne_zero hnondegenerate
    have hp := mul_neg_of_pos_of_neg hc hg
    nlinarith only [hp]
  rw [sl_vertical_real_formula,sl_vertical_real_formula,hns,hnu]
  rw [div_mul_div_comm]
  exact div_neg_of_neg_of_pos hneg (mul_pos hds hdu)

private theorem ideal_endpoint_im (a c : ℝ) :
    (((a:ℂ)-Complex.I*(c:ℂ))/((a:ℂ)+Complex.I*(c:ℂ))).im =
      (-2*a*c)/(a^2+c^2) := by
  simp only [Complex.div_im,Complex.sub_re,Complex.sub_im,Complex.add_re,
    Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_apply]
  ring

private theorem sl_axis_crossing_endpoint_sign
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re = 0)
    (hnondegenerate : A 0 0*A 1 0 ≠ 0) :
    ((((A 0 0:ℝ):ℂ)-Complex.I*((A 1 0:ℝ):ℂ))/
      (((A 0 0:ℝ):ℂ)+Complex.I*((A 1 0:ℝ):ℂ))).im *
    ((((A 0 1:ℝ):ℂ)-Complex.I*((A 1 1:ℝ):ℂ))/
      (((A 0 1:ℝ):ℂ)+Complex.I*((A 1 1:ℝ):ℂ))).im < 0 := by
  have hNt : A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1=0 := by
    rw [sl_vertical_real_formula] at hcross
    exact (div_eq_zero_iff.mp hcross).resolve_right
      (sl_vertical_denominator_pos A t).ne'
  have hprod : (A 0 0*A 1 0)*(A 0 1*A 1 1) < 0 := by
    have hs : 0 < (Real.exp t)^2 := sq_pos_of_pos (Real.exp_pos t)
    have hc : 0 < (A 0 0*A 1 0)^2 := sq_pos_of_ne_zero hnondegenerate
    have he : (A 0 0*A 1 0)*(A 0 1*A 1 1) =
        -(A 0 0*A 1 0)^2*(Real.exp t)^2 := by
      linear_combination (A 0 0*A 1 0)*hNt
    rw [he]
    nlinarith [mul_pos hc hs]
  rw [ideal_endpoint_im,ideal_endpoint_im,div_mul_div_comm]
  have hnon : (A 0 0*A 1 0)*(A 0 1*A 1 1) ≠ 0 := ne_of_lt hprod
  have ha : A 0 0 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnon).1).1
  have hb : A 0 1 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnon).2).1
  have hdenA : 0 < (A 0 0)^2+(A 1 0)^2 := by
    nlinarith [sq_pos_of_ne_zero ha,sq_nonneg (A 1 0)]
  have hdenB : 0 < (A 0 1)^2+(A 1 1)^2 := by
    nlinarith [sq_pos_of_ne_zero hb,sq_nonneg (A 1 1)]
  apply div_neg_of_neg_of_pos _ (mul_pos hdenA hdenB)
  nlinarith [hprod]

private theorem real_isometry_surjective (f : ℝ → ℝ) (hf : Isometry f) :
    Function.Surjective f := by
  have h01 := hf.dist_eq 1 0
  simp only [Real.dist_eq, sub_zero, abs_one] at h01
  have hsign : f 1-f 0 = 1 ∨ f 1-f 0 = -1 :=
    (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h01
  have heq (t : ℝ) : (f t-f 0)^2=t^2 ∧ (f t-f 1)^2=(t-1)^2 := by
    have h0 := hf.dist_eq t 0
    have h1 := hf.dist_eq t 1
    simp only [Real.dist_eq, sub_zero] at h0 h1
    constructor
    · nlinarith only [sq_abs (f t-f 0),sq_abs t,
        congrArg (fun x : ℝ => x^2) h0]
    · nlinarith only [sq_abs (f t-f 1),sq_abs (t-1),
        congrArg (fun x : ℝ => x^2) h1]
  rcases hsign with hp | hn
  · have hall (t : ℝ) : f t = f 0+t := by
      obtain ⟨h0,h1⟩ := heq t
      nlinarith only [h0,h1,hp]
    intro y
    exact ⟨y-f 0,by rw [hall]; ring⟩
  · have hall (t : ℝ) : f t = f 0-t := by
      obtain ⟨h0,h1⟩ := heq t
      nlinarith only [h0,h1,hn]
    intro y
    exact ⟨f 0-y,by rw [hall]; ring⟩

private theorem vertical_line_range (f : ℝ → H2) (hf : Isometry f)
    (hx : ∀ t, (f t).re = 0) :
    Set.range f = Set.range verticalPath := by
  let L : ℝ → ℝ := fun t => Real.log (f t).im
  have hL : Isometry L := Isometry.of_dist_eq fun t u => by
    change dist (Real.log (f t).im) (Real.log (f u).im) = dist t u
    rw [←UpperHalfPlane.dist_of_re_eq (by rw [hx t,hx u]),hf.dist_eq]
  have hv (t : ℝ) : f t = verticalPath (L t) := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using hx t
    · simp [verticalPath,L,Real.exp_log (f t).im_pos]
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨L t,(hv t).symm⟩
  · rintro ⟨t,rfl⟩
    obtain ⟨u,hu⟩ := real_isometry_surjective L hL t
    exact ⟨u,by rw [hv u,hu]⟩

private theorem sl_distinct_axis_crossing_nondegenerate
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re = 0)
    (hdistinct : Set.range (fun s : ℝ => A • verticalPath s) ≠
      Set.range verticalPath) :
    A 0 0*A 1 0 ≠ 0 := by
  intro hac
  have hNt : A 0 0*A 1 0*(Real.exp t)^2+A 0 1*A 1 1=0 := by
    rw [sl_vertical_real_formula] at hcross
    exact (div_eq_zero_iff.mp hcross).resolve_right
      (sl_vertical_denominator_pos A t).ne'
  have hbd : A 0 1*A 1 1=0 := by
    rw [hac] at hNt
    simpa using hNt
  have hx (s : ℝ) : (A • verticalPath s : H2).re=0 := by
    rw [sl_vertical_real_formula,hac,hbd]
    simp
  have hi : Isometry (fun s : ℝ => A • verticalPath s) :=
    (IsometryEquiv.constSMul A).isometry.comp verticalPath_isometry
  exact hdistinct (vertical_line_range _ hi hx)

private theorem sl_distinct_axis_meeting_endpoint_sign
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ)
    (hcross : (A • verticalPath t : H2).re = 0)
    (hdistinct : Set.range (fun s : ℝ => A • verticalPath s) ≠
      Set.range verticalPath) :
    ((((A 0 0:ℝ):ℂ)-Complex.I*((A 1 0:ℝ):ℂ))/
      (((A 0 0:ℝ):ℂ)+Complex.I*((A 1 0:ℝ):ℂ))).im *
    ((((A 0 1:ℝ):ℂ)-Complex.I*((A 1 1:ℝ):ℂ))/
      (((A 0 1:ℝ):ℂ)+Complex.I*((A 1 1:ℝ):ℂ))).im < 0 :=
  sl_axis_crossing_endpoint_sign A t hcross
    (sl_distinct_axis_crossing_nondegenerate A t hcross hdistinct)

private theorem sl_stabilizer_maps_vertical_one (z : H2)
    (h : dist UpperHalfPlane.I z = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (A • UpperHalfPlane.I : H2) = UpperHalfPlane.I ∧
      (A • verticalPath 1 : H2) = z := by
  let a : ℝ := 1 - Real.exp (1 : ℝ) * z.im
  let b : ℝ := z.re
  by_cases hpole : a = 0 ∧ b = 0
  · have him : z.im = Real.exp (-1 : ℝ) := by
      have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
      have ha : Real.exp (1 : ℝ) * z.im = 1 := by
        dsimp [a] at hpole
        linarith [hpole.1]
      rw [Real.exp_neg, ← one_div]
      exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
    have hz : z = verticalPath (-1) := by
      apply UpperHalfPlane.ext_re_im
      · simpa [verticalPath,b] using hpole.2
      · simpa [verticalPath] using him
    let S : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S
    refine ⟨S,?_,?_⟩
    · have hzero : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      rw [←hzero]
      have hh := modular_S_verticalPath 0
      change (S • verticalPath 0 : H2) = verticalPath (-0) at hh
      simpa only [neg_zero] using hh
    · rw [hz]
      exact modular_S_verticalPath 1
  · have hab : 0 < a^2+b^2 := by
      by_contra hn
      have ha : a=0 := by nlinarith [sq_nonneg a,sq_nonneg b]
      have hb : b=0 := by nlinarith [sq_nonneg a,sq_nonneg b]
      exact hpole ⟨ha,hb⟩
    exact ⟨stabilizerRotation a b hab,stabilizerRotation_fixes_I a b hab,
      stabilizerRotation_maps_vertical_one z h hab⟩

private theorem sl_maps_ordered_unit_pair (x y : H2)
    (hxy : dist x y = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (A • UpperHalfPlane.I : H2) = x ∧
      (A • verticalPath 1 : H2) = y := by
  let A₀ := x.toSL2R
  let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A₀
  have he₀ : e₀ UpperHalfPlane.I = x := x.toSL2R_smul_I
  let w : H2 := e₀.symm y
  have hw : dist UpperHalfPlane.I w = 1 := by
    have hdist := e₀.isometry.dist_eq UpperHalfPlane.I (e₀.symm y)
    rw [e₀.apply_symm_apply,he₀] at hdist
    simpa [w,hxy] using hdist.symm
  obtain ⟨A,hAI,hAV⟩ := sl_stabilizer_maps_vertical_one w hw
  refine ⟨A₀*A,?_,?_⟩
  · rw [mul_smul,hAI]
    exact x.toSL2R_smul_I
  · rw [mul_smul,hAV]
    exact e₀.apply_symm_apply y

private theorem isometric_line_is_sl_axis (f : ℝ → H2) (hf : Isometry f) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ t : ℝ, f t = A • verticalPath t := by
  have h01 : dist (f 0) (f 1) = 1 := by
    simpa using hf.dist_eq 0 1
  obtain ⟨A,hA0,hA1⟩ := sl_maps_ordered_unit_pair (f 0) (f 1) h01
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul A
  have hnorm : Isometry (fun t : ℝ => e.symm (f t)) := e.symm.isometry.comp hf
  have hzero : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have hnorm0 : e.symm (f 0) = verticalPath 0 := by
    rw [←hA0]
    change e.symm (e UpperHalfPlane.I) = verticalPath 0
    rw [e.symm_apply_apply,←hzero]
  have hnorm1 : e.symm (f 1) = verticalPath 1 := by
    rw [←hA1]
    change e.symm (e (verticalPath 1)) = verticalPath 1
    rw [e.symm_apply_apply]
  have hv := isometry_eq_vertical_of_values _ hnorm hnorm0 hnorm1
  refine ⟨A,?_⟩
  intro t
  apply e.symm.injective
  change e.symm (f t) = e.symm (e (verticalPath t))
  rw [e.symm_apply_apply]
  exact hv t

private theorem distinct_isometric_lines_meeting_normalized_endpoint_sign
    (f g : ℝ → H2) (hf : Isometry f) (hg : Isometry g)
    (s t : ℝ) (hmeet : f s = g t)
    (hdistinct : Set.range f ≠ Set.range g) :
    ∃ e : H2 ≃ᵢ H2,
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ u : ℝ, e.symm (f u) = verticalPath u) ∧
      (∀ u : ℝ, e.symm (g u) = A • verticalPath u) ∧
      (∀ u v : ℝ, u < t → t < v →
        (e.symm (g u)).re * (e.symm (g v)).re < 0) ∧
      (((((A 0 0:ℝ):ℂ)-Complex.I*((A 1 0:ℝ):ℂ))/
        (((A 0 0:ℝ):ℂ)+Complex.I*((A 1 0:ℝ):ℂ))).im *
      ((((A 0 1:ℝ):ℂ)-Complex.I*((A 1 1:ℝ):ℂ))/
        (((A 0 1:ℝ):ℂ)+Complex.I*((A 1 1:ℝ):ℂ))).im < 0) := by
  obtain ⟨B,hB⟩ := isometric_line_is_sl_axis f hf
  let e : H2 ≃ᵢ H2 := IsometryEquiv.constSMul B
  have heF (u : ℝ) : e.symm (f u) = verticalPath u := by
    rw [hB]
    change e.symm (e (verticalPath u)) = verticalPath u
    exact e.symm_apply_apply _
  let k : ℝ → H2 := fun u => e.symm (g u)
  have hk : Isometry k := e.symm.isometry.comp hg
  obtain ⟨A,hA⟩ := isometric_line_is_sl_axis k hk
  have hc : (A • verticalPath t : H2).re = 0 := by
    rw [←hA]
    change (e.symm (g t)).re = 0
    rw [←hmeet,heF]
    simp [verticalPath]
  have hd : Set.range (fun u : ℝ => A • verticalPath u) ≠
      Set.range verticalPath := by
    intro heq
    have hrange : Set.range k = Set.range (fun u : ℝ => A • verticalPath u) :=
      congrArg Set.range (funext hA)
    have heq' : Set.range k = Set.range verticalPath := hrange.trans heq
    apply hdistinct
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      have hu : verticalPath u ∈ Set.range k := by
        exact heq'.symm ▸ Set.mem_range_self u
      obtain ⟨v,hv⟩ := hu
      refine ⟨v,?_⟩
      apply e.symm.injective
      simpa only [k,heF] using hv
    · rintro ⟨u,rfl⟩
      have hu : k u ∈ Set.range verticalPath := by
        exact heq' ▸ Set.mem_range_self u
      obtain ⟨v,hv⟩ := hu
      refine ⟨v,?_⟩
      apply e.symm.injective
      simpa only [k,heF] using hv
  refine ⟨e,A,heF,hA,?_,?_⟩
  · intro u v hu hv
    rw [show e.symm (g u) = A • verticalPath u from hA u,
      show e.symm (g v) = A • verticalPath v from hA v]
    exact sl_axis_crossing_changes_real_side A u t v hu hv hc
      (sl_distinct_axis_crossing_nondegenerate A t hc hd)
  · exact sl_distinct_axis_meeting_endpoint_sign A t hc hd

private theorem vertical_coordinate_bounds (z : H2) (t B : ℝ) (_hB : 0 ≤ B)
    (hd : dist z (verticalPath t) ≤ B) :
    Real.exp (t-B) ≤ z.im ∧
      ‖(z : ℂ)‖ ≤ (Real.sinh B+Real.cosh B)*Real.exp t := by
  have hlog := (UpperHalfPlane.dist_log_im_le z (verticalPath t)).trans hd
  simp only [verticalPath,UpperHalfPlane.mk_im,Real.log_exp,Real.dist_eq] at hlog
  have hlower : t-B ≤ Real.log z.im := by
    have h := (abs_le.mp hlog).1
    linarith
  have him : Real.exp (t-B) ≤ z.im := by
    have h := Real.exp_le_exp.mpr hlower
    simpa only [Real.exp_log z.im_pos] using h
  refine ⟨him,?_⟩
  have hball := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hd
  have hcenter : ((verticalPath t).center B : ℂ) =
      ((Real.exp t*Real.cosh B : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [UpperHalfPlane.center,verticalPath,-Complex.ofReal_exp]
  have hnorm : ‖((verticalPath t).center B : ℂ)‖ = Real.exp t*Real.cosh B := by
    rw [hcenter,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
    exact abs_of_pos (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
  have hball' : dist (z : ℂ) ((verticalPath t).center B : ℂ) ≤ Real.exp t*Real.sinh B := by
    simpa [verticalPath] using hball
  calc
    ‖(z : ℂ)‖ ≤ dist (z : ℂ) ((verticalPath t).center B : ℂ)+‖((verticalPath t).center B : ℂ)‖ :=
      by simpa only [dist_zero_right] using dist_triangle (z : ℂ) ((verticalPath t).center B : ℂ) 0
    _ ≤ Real.exp t*Real.sinh B+Real.exp t*Real.cosh B := add_le_add hball' hnorm.le
    _ = (Real.sinh B+Real.cosh B)*Real.exp t := by ring

private theorem cayley_endpoint_bounds (z : H2) :
    dist (cayley z : ℂ) 1 ≤ 2/z.im ∧
      dist (cayley z : ℂ) (-1) ≤ 2*‖(z : ℂ)‖ := by
  have hden : (z : ℂ)+Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,UpperHalfPlane.coe_im,Complex.I_im,Complex.zero_im] at hi
    linarith [z.im_pos]
  have hnorm : z.im+1 ≤ ‖(z : ℂ)+Complex.I‖ := by
    simpa only [Complex.add_im,UpperHalfPlane.coe_im,Complex.I_im] using
      Complex.im_le_norm ((z : ℂ)+Complex.I)
  have hnorm1 : 1 ≤ ‖(z : ℂ)+Complex.I‖ := by linarith [z.im_pos]
  have hminus : (cayley z : ℂ)-1 = (-2*Complex.I)/((z : ℂ)+Complex.I) := by
    change ((z : ℂ)-Complex.I)/((z : ℂ)+Complex.I)-1 = _
    field_simp [hden]; ring
  have hplus : (cayley z : ℂ)-(-1) = (2*(z : ℂ))/((z : ℂ)+Complex.I) := by
    change ((z : ℂ)-Complex.I)/((z : ℂ)+Complex.I)-(-1) = _
    field_simp [hden]; ring
  constructor
  · rw [dist_eq_norm,hminus,norm_div,norm_mul]
    norm_num
    apply div_le_div_of_nonneg_left (by norm_num) z.im_pos
    linarith
  · rw [dist_eq_norm,hplus,norm_div,norm_mul]
    norm_num
    exact div_le_self (by positivity) hnorm1

private theorem bounded_axis_path_has_same_ideal_ends
    (γ : ℝ → H2) (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B)
    (hbounded : ∀ t : ℝ, dist (γ t) (verticalPath (p*t)) ≤ B) :
    Tendsto (fun t => (cayley (γ t) : ℂ)) atTop (𝓝 1) ∧
      Tendsto (fun t => (cayley (γ t) : ℂ)) atBot (𝓝 (-1)) := by
  have hneg : Tendsto (fun t : ℝ => B-p*t) atTop atBot := by
    apply tendsto_atBot.mpr
    intro a
    filter_upwards [eventually_ge_atTop ((B-a)/p)] with t ht
    have h := (div_le_iff₀ hp).mp ht
    linarith
  have hbot : Tendsto (fun t : ℝ => p*t) atBot atBot := by
    apply tendsto_atBot.mpr
    intro a
    filter_upwards [eventually_le_atBot (a/p)] with t ht
    simpa only [mul_comm] using (le_div_iff₀ hp).mp ht
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hzero : Tendsto (fun t : ℝ => 2*Real.exp (B-p*t)) atTop (𝓝 0) := by
      simpa only [mul_zero,Function.comp_def] using
        (Real.tendsto_exp_atBot.comp hneg).const_mul 2
    refine squeeze_zero (fun _ => dist_nonneg) (fun t => ?_) hzero
    have hcoord := (vertical_coordinate_bounds (γ t) (p*t) B hB (hbounded t)).1
    have hbound := (cayley_endpoint_bounds (γ t)).1
    have hquot : 2/Real.exp (p*t-B) = 2*Real.exp (B-p*t) := by
      rw [div_eq_mul_inv,← Real.exp_neg]
      congr 2; ring
    rw [← hquot]
    exact hbound.trans (div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hcoord)
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hzero : Tendsto (fun t : ℝ => 2*(Real.sinh B+Real.cosh B)*Real.exp (p*t)) atBot (𝓝 0) := by
      simpa only [mul_zero,Function.comp_def] using
        (Real.tendsto_exp_atBot.comp hbot).const_mul (2*(Real.sinh B+Real.cosh B))
    refine squeeze_zero (fun _ => dist_nonneg) (fun t => ?_) hzero
    have hcoord := (vertical_coordinate_bounds (γ t) (p*t) B hB (hbounded t)).2
    have hbound := (cayley_endpoint_bounds (γ t)).2
    have h := mul_le_mul_of_nonneg_left hcoord (by norm_num : (0:ℝ) ≤ 2)
    exact hbound.trans (by simpa only [mul_assoc] using h)

private theorem bounded_distance_from_isometric_line_is_proper
    (F : C(ℝ,H2)) (a : ℝ → H2) (ha : Isometry a)
    (B : ℝ) (hbound : ∀ t, dist (F t) (a t) ≤ B) :
    IsProperMap F := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨F.continuous,?_⟩
  intro K hK
  obtain ⟨R,hR⟩ :=
    (hK.image (continuous_id.dist (continuous_const : Continuous (fun _ : H2 => F 0)))).bddAbove
  let C := R+2*B
  have hsubset : F ⁻¹' K ⊆ Set.Icc (-C) C := by
    intro t ht
    have htR : dist (F t) (F 0) ≤ R := hR ⟨F t,ht,rfl⟩
    have hd : dist (a t) (a 0) ≤ B+(R+B) := by
      calc
        dist (a t) (a 0) ≤ dist (a t) (F t)+dist (F t) (a 0) :=
          dist_triangle _ _ _
        _ ≤ B+(dist (F t) (F 0)+dist (F 0) (a 0)) :=
          add_le_add (by simpa only [dist_comm] using hbound t) (dist_triangle _ _ _)
        _ ≤ B+(R+B) := by
          have hzero : dist (F 0) (a 0) ≤ B := hbound 0
          linarith
    rw [ha.dist_eq,Real.dist_eq,sub_zero] at hd
    exact abs_le.mp (by dsimp [C]; linarith : |t| ≤ C)
  exact isCompact_Icc.of_isClosed_subset
    (hK.isClosed.preimage F.continuous) hsubset

private theorem proper_embedded_circle_lift_injective
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (p : P → X) (hp : IsCoveringMap p)
    (c : C(Circle,X)) (hc : IsEmbedding c)
    (F : C(ℝ,P)) (hproper : IsProperMap F)
    (hproj : ∀ t : ℝ, p (F t) = c (Circle.exp t)) :
    Function.Injective F := by
  intro s t hst
  by_contra hne
  have hcircle : Circle.exp s = Circle.exp t := by
    apply hc.injective
    rw [←hproj,←hproj,hst]
  have heq : (fun u : ℝ => F (u+s)) = (fun u : ℝ => F (u+t)) := by
    refine hp.eq_of_comp_eq
      (F.continuous.comp (continuous_id.add continuous_const))
      (F.continuous.comp (continuous_id.add continuous_const)) ?_ 0 ?_
    · funext u
      change p (F (u+s)) = p (F (u+t))
      rw [hproj,hproj,Circle.exp_add,Circle.exp_add,hcircle]
    · simpa only [zero_add] using hst
  have hperiod : Function.Periodic F (t-s) := by
    intro u
    have h := congrFun heq (u-s)
    have hus : u-s+s=u := by ring
    have hut : u-s+t=u+(t-s) := by ring
    rw [hus,hut] at h
    exact h.symm
  have hrange : IsCompact (Set.range F) :=
    hperiod.compact_of_continuous (sub_ne_zero.mpr (by intro h; exact hne h.symm))
      F.continuous
  have hcompact := hproper.isCompact_preimage hrange
  have huniv : F ⁻¹' Set.range F = Set.univ := by ext u; simp
  rw [huniv] at hcompact
  exact noncompact_univ ℝ hcompact

private theorem two_endpoint_compactification
    {X : Type} [TopologicalSpace X] [T2Space X]
    (γ : ℝ → X) (hcontinuous : Continuous γ)
    (hinjective : Function.Injective γ)
    (a b : X) (hab : a ≠ b)
    (hends : ∀ t : ℝ, γ t ≠ a ∧ γ t ≠ b)
    (hbot : Tendsto γ atBot (𝓝 a)) (htop : Tendsto γ atTop (𝓝 b)) :
    ∃ f : C(unitInterval,X), IsEmbedding f ∧ f 0 = a ∧ f 1 = b ∧
      Set.range f = insert a (insert b (Set.range γ)) := by
  let F : EReal → X := EReal.rec a γ b
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    cases x using EReal.rec with
    | bot =>
      apply continuousAt_iff_punctured_nhds.mpr
      rw [EReal.nhdsWithin_bot,tendsto_map'_iff]
      simpa only [F,EReal.rec_bot,EReal.rec_coe,Function.comp_def] using hbot
    | coe r =>
      change Tendsto F (𝓝 (r : EReal)) (𝓝 (F r))
      rw [EReal.nhds_coe,tendsto_map'_iff]
      have hr : Tendsto γ (𝓝 r) (𝓝 (γ r)) := hcontinuous.continuousAt
      simpa only [F,EReal.rec_coe,Function.comp_def] using hr
    | top =>
      apply continuousAt_iff_punctured_nhds.mpr
      rw [EReal.nhdsWithin_top,tendsto_map'_iff]
      simpa only [F,EReal.rec_top,EReal.rec_coe,Function.comp_def] using htop
  have hFinj : Function.Injective F := by
    intro x y h
    cases x using EReal.rec <;> cases y using EReal.rec
    all_goals simp only [F,EReal.rec_bot,EReal.rec_top,EReal.rec_coe] at h
    · rfl
    · exact False.elim ((hends _).1 h.symm)
    · exact False.elim (hab h)
    · exact False.elim ((hends _).1 h)
    · exact congrArg (fun t : ℝ => (t : EReal)) (hinjective h)
    · exact False.elim ((hends _).2 h)
    · exact False.elim (hab h.symm)
    · exact False.elim ((hends _).2 h.symm)
    · rfl
  let coordinate : EReal ≃o unitInterval :=
    EReal.expOrderIso.trans ENNReal.orderIsoUnitIntervalBirational
  let e := coordinate.toHomeomorph
  have he0 : e.symm 0 = (⊥ : EReal) := by
    change coordinate.symm ⊥ = ⊥
    exact coordinate.symm.map_bot
  have he1 : e.symm 1 = (⊤ : EReal) := by
    change coordinate.symm ⊤ = ⊤
    exact coordinate.symm.map_top
  let f : C(unitInterval,X) := ⟨F ∘ e.symm,hF.comp e.symm.continuous⟩
  have hf : IsEmbedding f :=
    (f.continuous.isClosedEmbedding (hFinj.comp e.symm.injective)).isEmbedding
  refine ⟨f,hf,?_,?_,?_⟩
  · change F (e.symm 0) = a
    rw [he0]
    rfl
  · change F (e.symm 1) = b
    rw [he1]
    rfl
  · apply Set.Subset.antisymm
    · rintro _ ⟨t,rfl⟩
      change F (e.symm t) ∈ insert a (insert b (Set.range γ))
      cases e.symm t using EReal.rec with
      | bot => simp [F]
      | coe r => exact Set.mem_insert_of_mem a (Set.mem_insert_of_mem b ⟨r,rfl⟩)
      | top => simp [F]
    · intro z hz
      rcases hz with rfl | hz
      · exact ⟨e ⊥,by change F (e.symm (e ⊥)) = F ⊥; exact congrArg F (e.symm_apply_apply _)⟩
      · rcases hz with rfl | ⟨r,rfl⟩
        · exact ⟨e ⊤,by change F (e.symm (e ⊤)) = F ⊤; exact congrArg F (e.symm_apply_apply _)⟩
        · exact ⟨e r,by change F (e.symm (e r)) = γ r; exact congrArg F (e.symm_apply_apply _)⟩

private theorem source_component_geodesic_lines
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (base : E)
    (γ : C(ℝ,E))
    (himage : Set.range γ ⊆ connectedComponent base)
    (hunit : letI : MetricSpace E := H.metric;
      ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
          dist (γ s) (γ u) = |s-u|) :
    ∃ p : H2 → connectedComponent base,
      ∃ γA : C(ℝ,connectedComponent base),
      (∀ t, (γA t).val = γ t) ∧ IsCoveringMap p ∧
      (∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          @dist E H.metric.toDist (p y).val (p z).val = dist y z) ∧
      ∃ a : {x : H2 // p x ∈ Set.range γA} → ℝ → H2,
        (∀ x, Isometry (a x)) ∧
        p ⁻¹' Set.range γA = ⋃ x, Set.range (a x) := by
  classical
  letI : MetricSpace E := H.metric
  letI : CompactSpace E := H.compact
  have hT2metric : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    infer_instance
  rw [H.compatible] at hT2metric
  letI : T2Space E := hT2metric
  let A := connectedComponent base
  letI : CompactSpace A :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  let U : TopologicalSpace.Opens E := ⟨A,isOpen_connectedComponent⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A :=
    TopologicalSpace.Opens.instChartedSpace U
  let componentMetric : MetricSpace A :=
    MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have componentMetricTopology :
      componentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := componentMetric.replaceTopology componentMetricTopology.symm
  let γA : C(ℝ,A) :=
    ⟨fun t => ⟨γ t,himage (Set.mem_range_self t)⟩,γ.continuous.subtype_mk _⟩
  obtain ⟨coverTopology,hsecond,hhausdorff,hcharted,hsimply,hquot,hsurj,_⟩ :=
    actual_topological_universal_cover (⟨base,mem_connectedComponent⟩ : A)
  letI : TopologicalSpace (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) := coverTopology
  letI : SimplyConnectedSpace (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) := hsimply
  let q : (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) → A := Sigma.fst
  obtain ⟨development,hmetric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H base
      q hquot.isCoveringMap hsurj
  let projection : H2 → A := fun z => q (development.symm z)
  have hcover : IsCoveringMap projection :=
    hquot.isCoveringMap.comp_homeomorph development.symm
  have hlocal : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x∈U ∧
      ∀ y∈U,∀ z∈U,dist (projection y) (projection z)=dist y z := by
    intro x
    obtain ⟨V,hV,hxV,hmetricV⟩ := hmetric (development.symm x)
    refine ⟨development.symm ⁻¹' V,hV.preimage development.symm.continuous,?_,?_⟩
    · simpa only [Set.mem_preimage,development.symm_apply_apply] using hxV
    · intro y hy z hz
      change dist (q (development.symm y)) (q (development.symm z)) = dist y z
      change @dist E H.metric.toDist (q (development.symm y)).val
        (q (development.symm z)).val = dist y z
      simpa only [development.apply_symm_apply] using hmetricV _ hy _ hz
  have hunitA : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
        dist (γA s) (γA u) = |s-u| := by
    intro t
    obtain ⟨ε,hε,hm⟩ := hunit t
    refine ⟨ε,hε,?_⟩
    intro s u hs hu
    change @dist E H.metric.toDist (γ s) (γ u) = |s-u|
    exact hm s u hs hu
  obtain ⟨axes,haxes,hunion⟩ :=
    actual_developed_geodesic_preimage_is_union_complete_lines
      projection hcover hlocal γA hunitA
  exact ⟨projection,γA,(fun _ => rfl),hcover,hlocal,axes,haxes,hunion⟩

private theorem source_closed_geodesic_has_developed_lines
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (c : Curve E) (base : E)
    (hbase : base ∈ c.image)
    (hgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image) :
    ∃ p : H2 → connectedComponent base,
      ∃ γA : C(ℝ,connectedComponent base),
      Subtype.val '' Set.range γA = c.image ∧
      IsCoveringMap p ∧
      (∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          @dist E H.metric.toDist (p y).val (p z).val = dist y z) ∧
      ∃ a : {x : H2 // p x ∈ Set.range γA} → ℝ → H2,
        (∀ x, Isometry (a x)) ∧
        p ⁻¹' Set.range γA = ⋃ x, Set.range (a x) := by
  classical
  letI : MetricSpace E := H.metric
  obtain ⟨path,period,hperiod,hcont,hperiodic,hrange,hunit⟩ := hgeo
  let γ : C(ℝ,E) := ⟨path,hcont⟩
  have hconnected : IsConnected c.image := by
    change IsConnected (Set.range c.map)
    exact isConnected_range c.embedded.continuous
  have himage : Set.range γ ⊆ connectedComponent base := by
    rw [show Set.range γ = c.image from hrange]
    exact hconnected.subset_connectedComponent hbase
  obtain ⟨p,γA,hγA,hp,hloc,a,ha,hu⟩ :=
    source_component_geodesic_lines H base γ himage hunit
  refine ⟨p,γA,?_,hp,hloc,a,ha,hu⟩
  rw [←Set.range_comp]
  have hpath : (Subtype.val ∘ γA) = path := funext hγA
  rw [hpath]
  exact hrange

private theorem source_quotient_cover_transport_to_h2
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (q : P → X) (hq : IsQuotientCoveringMap q (deck q))
    (e : P ≃ₜ H2) :
    IsQuotientCoveringMap (fun z : H2 => q (e.symm z))
      (deck (fun z : H2 => q (e.symm z))) := by
  let p : H2 → X := fun z => q (e.symm z)
  have hp : IsCoveringMap p := hq.isCoveringMap.comp_homeomorph e.symm
  have hsurj : Function.Surjective p := by
    intro x
    obtain ⟨y,hy⟩ := hq.surjective x
    exact ⟨e y,by simpa [p] using hy⟩
  let back (d : deck p) : deck q := by
    let φ : P ≃ₜ P := (e.trans d.val).trans e.symm
    have hφ : φ ∈ deck q := by
      apply deck.mem_iff.mpr
      funext u
      change q (e.symm ((d : H2 ≃ₜ H2) (e u))) = q u
      have hd := deck.proj_smul d (e u)
      change q (e.symm ((d : H2 ≃ₜ H2) (e u))) = q (e.symm (e u)) at hd
      simpa using hd
    exact ⟨φ,hφ⟩
  haveI : IsCancelSMul (deck p) H2 := by
    letI : IsCancelSMul (deck q) P := hq.isCancelSMul
    refine { right_cancel' := ?_ }
    intro d₁ d₂ z h
    have hb : back d₁ = back d₂ := by
      apply IsCancelSMul.right_cancel (back d₁) (back d₂) (e.symm z)
      apply e.injective
      change (d₁ : H2 ≃ₜ H2) z = (d₂ : H2 ≃ₜ H2) z at h
      simpa [back] using h
    apply Subtype.ext
    apply Homeomorph.ext
    intro u
    have hu := congrArg (fun k : deck q => (k : P ≃ₜ P) (e.symm u)) hb
    apply e.symm.injective
    simpa [back] using hu
  apply (isQuotientCoveringMap_iff_isCoveringMap_and p (deck p)).mpr
  refine ⟨hp,hsurj,inferInstance,inferInstance,?_⟩
  intro z w
  constructor
  · intro hzw
    have hqzw : q (e.symm z) = q (e.symm w) := hzw
    obtain ⟨η,hη⟩ := hq.apply_eq_iff_mem_orbit.mp hqzw
    let φ : H2 ≃ₜ H2 := (e.symm.trans η.val).trans e
    have hφ : φ ∈ deck p := by
      apply deck.mem_iff.mpr
      funext u
      change q (e.symm (e ((η : P ≃ₜ P) (e.symm u)))) = q (e.symm u)
      rw [e.symm_apply_apply]
      exact deck.proj_smul η (e.symm u)
    let d : deck p := ⟨φ,hφ⟩
    refine ⟨d,?_⟩
    change e ((η : P ≃ₜ P) (e.symm w)) = z
    apply e.symm.injective
    change (η : P ≃ₜ P) (e.symm w) = e.symm z at hη
    simpa only [e.symm_apply_apply] using hη
  · rintro ⟨d,rfl⟩
    exact deck.proj_smul d w

private theorem source_common_component_developed_cover
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (base : E) :
    ∃ p : H2 → connectedComponent base,
      IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Function.Surjective p ∧
      (∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          @dist E H.metric.toDist (p y).val (p z).val = dist y z) := by
  classical
  letI : CompactSpace E := H.compact
  have hT2metric : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at hT2metric
  letI : T2Space E := hT2metric
  let A := connectedComponent base
  letI : CompactSpace A :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  let U : TopologicalSpace.Opens E := ⟨A,isOpen_connectedComponent⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A :=
    TopologicalSpace.Opens.instChartedSpace U
  obtain ⟨coverTopology,_,_,_,hsimply,hquot,hsurj,_⟩ :=
    actual_topological_universal_cover (⟨base,mem_connectedComponent⟩ : A)
  letI : TopologicalSpace (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) := coverTopology
  letI : SimplyConnectedSpace (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) := hsimply
  let q : (Σ z : A, Path.Homotopic.Quotient
      (⟨base,mem_connectedComponent⟩ : A) z) → A := Sigma.fst
  obtain ⟨development,hmetric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H base
      q hquot.isCoveringMap hsurj
  let p : H2 → A := fun z => q (development.symm z)
  have hpquot : IsQuotientCoveringMap p (deck p) :=
    source_quotient_cover_transport_to_h2 q hquot development
  have hp : IsCoveringMap p :=
    hquot.isCoveringMap.comp_homeomorph development.symm
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨z,hz⟩ := hsurj y
    exact ⟨development z,by simpa [p] using hz⟩
  refine ⟨p,hpquot,hp,hpsurj,?_⟩
  intro x
  obtain ⟨V,hV,hxV,hmetricV⟩ := hmetric (development.symm x)
  refine ⟨development.symm ⁻¹' V,hV.preimage development.symm.continuous,?_,?_⟩
  · simpa only [Set.mem_preimage,development.symm_apply_apply] using hxV
  · intro y hy z hz
    change @dist E H.metric.toDist (q (development.symm y)).val
      (q (development.symm z)).val = dist y z
    simpa only [development.apply_symm_apply] using hmetricV _ hy _ hz

private theorem source_developed_lines_project_onto_path
    {E : Type} [MetricSpace E] (p : H2 → E) (hp : IsCoveringMap p)
    (hmetric : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U, dist (p y) (p z) = dist y z)
    (γ : C(ℝ,E))
    (hunit : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s v : ℝ,
      |s-t| < ε → |v-t| < ε → dist (γ s) (γ v) = |s-v|) :
    ∃ a : {x : H2 // p x ∈ Set.range γ} → ℝ → H2,
      (∀ x, Isometry (a x)) ∧
      (∀ x t, p (a x t) = γ t) ∧
      (∀ x, x.val ∈ Set.range (a x)) ∧
      p ⁻¹' Set.range γ = ⋃ x, Set.range (a x) := by
  classical
  let F := {x : H2 // p x ∈ Set.range γ}
  have hlift (x : F) : ∃ δ : C(ℝ,H2), Isometry δ ∧
      p ∘ δ = γ ∧ x.val ∈ Set.range δ := by
    obtain ⟨t,ht⟩ := x.property
    obtain ⟨δ,⟨hδt,hδp⟩,_⟩ := hp.existsUnique_continuousMap_lifts γ t x.val ht.symm
    have hprojection (u : ℝ) : p (δ u) = γ u := congrFun hδp u
    have hlocal (u : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ s v : ℝ,
        |s-u| < ε → |v-u| < ε → dist (δ s) (δ v) = |s-v| := by
      obtain ⟨ε₀,hε₀,hu⟩ := hunit u
      obtain ⟨U,hU,hδU,hm⟩ := hmetric (δ u)
      obtain ⟨ε₁,hε₁,hball⟩ := Metric.isOpen_iff.mp
        (hU.preimage δ.continuous) u hδU
      refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,?_⟩
      intro s v hs hv
      have hsU : δ s ∈ U := hball (by
        simpa only [Metric.mem_ball,Real.dist_eq] using hs.trans_le (min_le_right _ _))
      have hvU : δ v ∈ U := hball (by
        simpa only [Metric.mem_ball,Real.dist_eq] using hv.trans_le (min_le_right _ _))
      rw [←hm (δ s) hsU (δ v) hvU,hprojection s,hprojection v]
      exact hu s v (hs.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))
    exact ⟨δ,actual_h2_local_unit_geodesic_isometry δ δ.continuous hlocal,
      hδp,⟨t,hδt⟩⟩
  choose δ hδiso hδproj hδrange using hlift
  refine ⟨fun x => δ x,hδiso,?_,hδrange,?_⟩
  · intro x t
    exact congrFun (hδproj x) t
  · ext z
    constructor
    · intro hz
      exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hδrange ⟨z,hz⟩⟩
    · intro hz
      obtain ⟨x,t,rfl⟩ := Set.mem_iUnion.mp hz
      exact ⟨t,(congrFun (hδproj x) t).symm⟩

private theorem source_closed_geodesic_lines_on_fixed_cover
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (c : Curve E) (base : E)
    (hbase : base ∈ c.image)
    (hgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image)
    (p : H2 → connectedComponent base) (hp : IsCoveringMap p)
    (hlocal : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        @dist E H.metric.toDist (p y).val (p z).val = dist y z) :
    ∃ γA : C(ℝ,connectedComponent base),
      Subtype.val '' Set.range γA = c.image ∧
      ∃ period : ℝ, 0 < period ∧ Function.Periodic γA period ∧
      ∃ a : {x : H2 // p x ∈ Set.range γA} → ℝ → H2,
        (∀ x, Isometry (a x)) ∧
        (∀ x t, p (a x t) = γA t) ∧
        (∀ x, x.val ∈ Set.range (a x)) ∧
        p ⁻¹' Set.range γA = ⋃ x, Set.range (a x) := by
  classical
  letI : MetricSpace E := H.metric
  let A := connectedComponent base
  let componentMetric : MetricSpace A :=
    MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have componentMetricTopology :
      componentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := componentMetric.replaceTopology componentMetricTopology.symm
  obtain ⟨path,period,hperiod,hcont,hperiodic,hrange,hunit⟩ := hgeo
  have hconnected : IsConnected c.image := by
    change IsConnected (Set.range c.map)
    exact isConnected_range c.embedded.continuous
  have himage : Set.range path ⊆ A := by
    rw [hrange]
    exact hconnected.subset_connectedComponent hbase
  let γA : C(ℝ,A) :=
    ⟨fun t => ⟨path t,himage (Set.mem_range_self t)⟩,hcont.subtype_mk _⟩
  have hunitA : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s u : ℝ, |s-t| < ε → |u-t| < ε →
        dist (γA s) (γA u) = |s-u| := by
    intro t
    obtain ⟨ε,hε,hm⟩ := hunit t
    refine ⟨ε,hε,?_⟩
    intro s u hs hu
    change @dist E H.metric.toDist (path s) (path u) = |s-u|
    exact hm s u hs hu
  obtain ⟨axes,haxes,hprojection,hanchors,hunion⟩ :=
    source_developed_lines_project_onto_path
      p hp (by
        intro x
        obtain ⟨U,hU,hxU,hm⟩ := hlocal x
        exact ⟨U,hU,hxU,by
          intro y hy z hz
          change @dist E H.metric.toDist (p y).val (p z).val = dist y z
          exact hm y hy z hz⟩) γA hunitA
  refine ⟨γA,?_,period,hperiod,?_,axes,haxes,hprojection,hanchors,hunion⟩
  · rw [←Set.range_comp]
    have hpath : (Subtype.val ∘ γA) = path := rfl
    rw [hpath]
    exact hrange
  · intro t
    apply Subtype.ext
    exact hperiodic t

private theorem source_two_closed_geodesics_have_common_developed_lines
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (x : E) (hxa : x ∈ a.image) (hxb : x ∈ b.image) :
    ∃ p : H2 → connectedComponent x,
      ∃ γa γb : C(ℝ,connectedComponent x),
      IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Function.Surjective p ∧
      (∀ z : H2, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
        ∀ y ∈ U, ∀ w ∈ U,
          @dist E H.metric.toDist (p y).val (p w).val = dist y w) ∧
      Subtype.val '' Set.range γa = a.image ∧
      Subtype.val '' Set.range γb = b.image ∧
      (∃ period : ℝ, 0 < period ∧ Function.Periodic γa period) ∧
      (∃ period : ℝ, 0 < period ∧ Function.Periodic γb period) ∧
      (∃ fa : {z : H2 // p z ∈ Set.range γa} → ℝ → H2,
        (∀ z, Isometry (fa z)) ∧
        (∀ z t, p (fa z t) = γa t) ∧
        (∀ z, z.val ∈ Set.range (fa z)) ∧
        p ⁻¹' Set.range γa = ⋃ z, Set.range (fa z)) ∧
      (∃ fb : {z : H2 // p z ∈ Set.range γb} → ℝ → H2,
        (∀ z, Isometry (fb z)) ∧
        (∀ z t, p (fb z t) = γb t) ∧
        (∀ z, z.val ∈ Set.range (fb z)) ∧
        p ⁻¹' Set.range γb = ⋃ z, Set.range (fb z)) := by
  obtain ⟨p,hpquot,hp,hpsurj,hmetric⟩ := source_common_component_developed_cover H x
  obtain ⟨γa,haimage,pa,hpa,hγaper,fa,hfa,hfaproj,hfaanchor,hfaunion⟩ :=
    source_closed_geodesic_lines_on_fixed_cover H a x hxa hageo p hp hmetric
  obtain ⟨γb,hbimage,pb,hpb,hγbper,fb,hfb,hfbproj,hfbanchor,hfbunion⟩ :=
    source_closed_geodesic_lines_on_fixed_cover H b x hxb hbgeo p hp hmetric
  exact ⟨p,γa,γb,hpquot,hp,hpsurj,hmetric,haimage,hbimage,
    ⟨pa,hpa,hγaper⟩,⟨pb,hpb,hγbper⟩,
    ⟨fa,hfa,hfaproj,hfaanchor,hfaunion⟩,
    ⟨fb,hfb,hfbproj,hfbanchor,hfbunion⟩⟩

private theorem source_distinct_closed_geodesics_have_meeting_distinct_lifts
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hne : a.image ≠ b.image)
    (x : E) (hxa : x ∈ a.image) (hxb : x ∈ b.image) :
    ∃ p : H2 → connectedComponent x,
      ∃ f g : ℝ → H2,
        ∃ γa γb : C(ℝ,connectedComponent x),
        ∃ pa pb : ℝ,
        IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Isometry f ∧ Isometry g ∧
        (∀ z : H2, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
          ∀ y ∈ U, ∀ w ∈ U,
            @dist E H.metric.toDist (p y).val (p w).val = dist y w) ∧
        0 < pa ∧ 0 < pb ∧ Function.Periodic γa pa ∧ Function.Periodic γb pb ∧
        (∀ u, p (f u) = γa u) ∧ (∀ u, p (g u) = γb u) ∧
        Subtype.val '' Set.range γa = a.image ∧
        Subtype.val '' Set.range γb = b.image ∧
        Set.range (fun u => (p (f u)).val) = a.image ∧
        Set.range (fun u => (p (g u)).val) = b.image ∧
        Set.range f ≠ Set.range g ∧
        ∃ s t : ℝ, f s = g t := by
  obtain ⟨p,γa,γb,hpquot,hp,hpsurj,hmetric,haimage,hbimage,
    ⟨pa,hpa,hγaper⟩,⟨pb,hpb,hγbper⟩,
    ⟨fa,hfa,hfaproj,hfaanchor,_⟩,
    ⟨fb,hfb,hfbproj,hfbanchor,_⟩⟩ :=
    source_two_closed_geodesics_have_common_developed_lines
      H a b hageo hbgeo x hxa hxb
  obtain ⟨z,hz⟩ := hpsurj (⟨x,mem_connectedComponent⟩ : connectedComponent x)
  have hza : p z ∈ Set.range γa := by
    have hx : x ∈ Subtype.val '' Set.range γa := by rw [haimage]; exact hxa
    obtain ⟨y,hy,hyx⟩ := hx
    have hpyeq : p z = y := by
      apply Subtype.ext
      exact (congrArg Subtype.val hz).trans hyx.symm
    exact hpyeq ▸ hy
  have hzb : p z ∈ Set.range γb := by
    have hx : x ∈ Subtype.val '' Set.range γb := by rw [hbimage]; exact hxb
    obtain ⟨y,hy,hyx⟩ := hx
    have hpyeq : p z = y := by
      apply Subtype.ext
      exact (congrArg Subtype.val hz).trans hyx.symm
    exact hpyeq ▸ hy
  let ia : {w : H2 // p w ∈ Set.range γa} := ⟨z,hza⟩
  let ib : {w : H2 // p w ∈ Set.range γb} := ⟨z,hzb⟩
  let f : ℝ → H2 := fa ia
  let g : ℝ → H2 := fb ib
  have hprojf : Set.range (fun u => (p (f u)).val) = a.image := by
    have hfun : (fun u => (p (f u)).val) = Subtype.val ∘ γa := by
      funext u
      exact congrArg Subtype.val (hfaproj ia u)
    rw [hfun,Set.range_comp]
    exact haimage
  have hprojg : Set.range (fun u => (p (g u)).val) = b.image := by
    have hfun : (fun u => (p (g u)).val) = Subtype.val ∘ γb := by
      funext u
      exact congrArg Subtype.val (hfbproj ib u)
    rw [hfun,Set.range_comp]
    exact hbimage
  have hfg : Set.range f ≠ Set.range g := by
    intro heq
    have hprojEq := congrArg
      (fun S : Set H2 => (fun w => (p w).val) '' S) heq
    rw [←Set.range_comp,←Set.range_comp] at hprojEq
    exact hne (hprojf.symm.trans (hprojEq.trans hprojg))
  obtain ⟨s,hs⟩ := hfaanchor ia
  obtain ⟨t,ht⟩ := hfbanchor ib
  exact ⟨p,f,g,γa,γb,pa,pb,hpquot,hp,hfa ia,hfb ib,hmetric,hpa,hpb,hγaper,hγbper,
    hfaproj ia,hfbproj ib,haimage,hbimage,hprojf,hprojg,hfg,s,t,hs.trans ht.symm⟩

private theorem source_restrict_homotopy_to_component
    {E : Type} [TopologicalSpace E]
    (f g : C(Circle,E)) (hfg : FreeHomotopic f g)
    (base : E) (hbase : base ∈ Set.range f) :
    ∃ F : C(Circle × Interval,connectedComponent base),
      (∀ z : Circle, (F (z,0)).val = f z) ∧
      (∀ z : Circle, (F (z,1)).val = g z) := by
  obtain ⟨H,hH0,hH1⟩ := hfg
  obtain ⟨z,hz⟩ := hbase
  letI : ContractibleSpace Interval :=
    (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).contractibleSpace
      (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
  have hconnected : IsConnected (Set.range H) := isConnected_range H.continuous
  have hmem : base ∈ Set.range H := ⟨(z,0),(hH0 z).trans hz⟩
  have hcomponent : Set.range H ⊆ connectedComponent base :=
    hconnected.subset_connectedComponent hmem
  exact ⟨⟨fun w => ⟨H w,hcomponent (Set.mem_range_self w)⟩,
    H.continuous.subtype_mk _⟩,hH0,hH1⟩

private theorem source_covering_strip_lift
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (p : P → X) (hp : IsQuotientCoveringMap p (deck p))
    (F : C(Circle × Interval,X)) (x₀ : P)
    (hx₀ : p x₀ = F (1,0)) :
    ∃ L : C(ℝ × Interval,P), ∃ δ : deck p,
      L (0,0) = x₀ ∧
      (∀ (s : ℝ) (t : Interval), p (L (s,t)) = F (Circle.exp s,t)) ∧
      (∀ (s : ℝ) (t : Interval), L (s+2*Real.pi,t) = δ • L (s,t)) := by
  classical
  letI : ContinuousConstSMul (deck p) P := hp.toContinuousConstSMul
  letI : ContractibleSpace Interval :=
    (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).contractibleSpace
      (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
  letI : LocallyPathConnectedSpace Interval :=
    (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).locallyPathConnectedSpace
  let strip : C(ℝ × Interval,X) :=
    ⟨fun st => F (Circle.exp st.1,st.2),
      F.continuous.comp ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hxstrip : p x₀ = strip (0,0) := by simpa [strip] using hx₀
  obtain ⟨L,⟨hL0,hLift⟩,hUnique⟩ :=
    hp.isCoveringMap.existsUnique_continuousMap_lifts strip (0,0) x₀ hxstrip
  have hproject (s : ℝ) (t : Interval) :
      p (L (s,t)) = F (Circle.exp s,t) := congrFun hLift (s,t)
  have hsame : p (L (2*Real.pi,0)) = p (L (0,0)) := by
    rw [hproject,hproject,Circle.exp_two_pi,Circle.exp_zero]
  obtain ⟨δ,hδ⟩ := hp.apply_eq_iff_mem_orbit.mp hsame
  let shifted : C(ℝ × Interval,P) :=
    ⟨fun st => δ⁻¹ • L (st.1+2*Real.pi,st.2),by fun_prop⟩
  have hshift0 : shifted (0,0) = x₀ := by
    change δ⁻¹ • L (0+2*Real.pi,0) = x₀
    rw [zero_add,←hδ,inv_smul_smul]
    exact hL0
  have hshiftproj : p ∘ shifted = strip := by
    funext st
    change p (δ⁻¹ • L (st.1+2*Real.pi,st.2)) = F (Circle.exp st.1,st.2)
    rw [hp.map_smul,hproject,Circle.exp_add_two_pi]
  have hshift : shifted = L := hUnique shifted ⟨hshift0,hshiftproj⟩
  refine ⟨L,δ,hL0,hproject,?_⟩
  intro s t
  have h := congrArg (fun N : C(ℝ × Interval,P) => δ • N (s,t)) hshift
  change δ • (δ⁻¹ • L (s+2*Real.pi,t)) = δ • L (s,t) at h
  simpa only [smul_inv_smul] using h

private theorem source_g2_contact_has_disjoint_original_strip_lifts
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (a b a₀ b₀ : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hne : a.image ≠ b.image)
    (haa : FreeHomotopic ⟨a.map,a.embedded.continuous⟩
      ⟨a₀.map,a₀.embedded.continuous⟩)
    (hbb : FreeHomotopic ⟨b.map,b.embedded.continuous⟩
      ⟨b₀.map,b₀.embedded.continuous⟩)
    (hdis : Disjoint a₀.image b₀.image)
    (x : E) (hxa : x ∈ a.image) (hxb : x ∈ b.image) :
    ∃ p : H2 → connectedComponent x,
      ∃ f g : ℝ → H2,
      ∃ La Lb : C(ℝ × Interval,H2),
      ∃ δa δb : deck p,
      ∃ ψa ψb : ℝ ≃ₜ ℝ,
      ∃ ca cb : ℝ,
      ∃ Ba Bb : ℝ,
      ∃ eA eB : H2 ≃ᵢ H2,
      ∃ arcA arcB : C(unitInterval,ℂ),
      ∃ eDisk : Metric.closedBall (0:ℂ) 1 ≃ₜ Metric.closedBall (0:ℂ) 1,
        IsQuotientCoveringMap p (deck p) ∧ IsCoveringMap p ∧ Isometry f ∧ Isometry g ∧
        Set.range (fun u => (p (f u)).val) = a.image ∧
        Set.range (fun u => (p (g u)).val) = b.image ∧
        Set.range f ≠ Set.range g ∧
        (∃ s t : ℝ, f s = g t) ∧
        (∀ s : ℝ, (p (La (s,0))).val = a.map (Circle.exp s)) ∧
        (∀ s : ℝ, (p (La (s,1))).val = a₀.map (Circle.exp s)) ∧
        (∀ s : ℝ, (p (Lb (s,0))).val = b.map (Circle.exp s)) ∧
        (∀ s : ℝ, (p (Lb (s,1))).val = b₀.map (Circle.exp s)) ∧
        Set.range (fun s : ℝ => La (s,0)) = Set.range f ∧
        Set.range (fun s : ℝ => Lb (s,0)) = Set.range g ∧
        (∀ u : ℝ, La (ψa u,0) = f u) ∧
        (∀ u : ℝ, Lb (ψb u,0) = g u) ∧
        ca ≠ 0 ∧ cb ≠ 0 ∧
        (∀ u : ℝ, (δa : H2 ≃ₜ H2) (f u) = f (u+ca)) ∧
        (∀ u : ℝ, (δb : H2 ≃ₜ H2) (g u) = g (u+cb)) ∧
        0 ≤ Ba ∧ 0 ≤ Bb ∧
        (∀ u : ℝ, dist (La (ψa u,1)) (f u) ≤ Ba) ∧
        (∀ u : ℝ, dist (Lb (ψb u,1)) (g u) ≤ Bb) ∧
        (∀ u : ℝ, eA.symm (f u) = verticalPath u) ∧
        (∀ u : ℝ, eB.symm (g u) = verticalPath u) ∧
        Tendsto (fun u : ℝ => (cayley (eA.symm (La (ψa u,1))) : ℂ))
          atTop (𝓝 1) ∧
        Tendsto (fun u : ℝ => (cayley (eA.symm (La (ψa u,1))) : ℂ))
          atBot (𝓝 (-1)) ∧
        Tendsto (fun u : ℝ => (cayley (eB.symm (Lb (ψb u,1))) : ℂ))
          atTop (𝓝 1) ∧
        Tendsto (fun u : ℝ => (cayley (eB.symm (Lb (ψb u,1))) : ℂ))
          atBot (𝓝 (-1)) ∧
        Function.Injective (fun s : ℝ => La (s,1)) ∧
        Function.Injective (fun s : ℝ => Lb (s,1)) ∧
        IsEmbedding arcA ∧ IsEmbedding arcB ∧
        arcA 0 = -1 ∧ arcA 1 = 1 ∧
        arcB 0 = -1 ∧ arcB 1 = 1 ∧
        Set.range arcA = insert (-1:ℂ) (insert (1:ℂ)
          (Set.range (fun u : ℝ => (cayley (eA.symm (La (ψa u,1))) : ℂ)))) ∧
        Set.range arcB = insert (-1:ℂ) (insert (1:ℂ)
          (Set.range (fun u : ℝ => (cayley (eB.symm (Lb (ψb u,1))) : ℂ)))) ∧
        (∀ z : H2, eDisk (cayley z) = cayley (eA.symm (eB z))) ∧
        (∀ z : Metric.closedBall (0:ℂ) 1,
          ‖(eDisk z:ℂ)‖ = 1 ↔ ‖(z:ℂ)‖ = 1) ∧
        (eDisk ⟨-1,by simp [Metric.mem_closedBall,dist_zero_right]⟩ : ℂ).im *
          (eDisk ⟨1,by simp [Metric.mem_closedBall,dist_zero_right]⟩ : ℂ).im < 0 ∧
        (∀ (s : ℝ) (t : Interval), La (s+2*Real.pi,t) = δa • La (s,t)) ∧
        (∀ (s : ℝ) (t : Interval), Lb (s+2*Real.pi,t) = δb • Lb (s,t)) ∧
        Disjoint (Set.range (fun s : ℝ => La (s,1)))
          (Set.range (fun s : ℝ => Lb (s,1))) := by
  obtain ⟨p,f,g,γa,γb,pa,pb,hpquot,hp,hf,hg,hmetric,hpa,hpb,hγaper,hγbper,
    hfpath,hgpath,haimage,hbimage,hprojf,hprojg,hnefg,hmeet⟩ :=
    source_distinct_closed_geodesics_have_meeting_distinct_lifts
      H a b hageo hbgeo hne x hxa hxb
  let A := connectedComponent x
  let componentMetric : MetricSpace A :=
    MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have componentMetricTopology :
      componentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := componentMetric.replaceTopology componentMetricTopology.symm
  have hlocalMetric : ∀ z : H2, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
      ∀ y ∈ U, ∀ w ∈ U, dist (p y) (p w) = dist y w := by
    intro z
    obtain ⟨U,hU,hzU,hm⟩ := hmetric z
    refine ⟨U,hU,hzU,?_⟩
    intro y hy w hw
    change @dist E H.metric.toDist (p y).val (p w).val = dist y w
    exact hm y hy w hw
  obtain ⟨Fa,hFa0,hFa1⟩ :=
    source_restrict_homotopy_to_component
      ⟨a.map,a.embedded.continuous⟩
      ⟨a₀.map,a₀.embedded.continuous⟩ haa x hxa
  obtain ⟨Fb,hFb0,hFb1⟩ :=
    source_restrict_homotopy_to_component
      ⟨b.map,b.embedded.continuous⟩
      ⟨b₀.map,b₀.embedded.continuous⟩ hbb x hxb
  have ha1 : a.map 1 ∈ Set.range (fun u : ℝ => (p (f u)).val) := by
    rw [hprojf]
    exact Set.mem_range_self 1
  obtain ⟨ua,hua⟩ := ha1
  have hFaAnchor : p (f ua) = Fa (1,0) := by
    apply Subtype.ext
    exact hua.trans (hFa0 1).symm
  obtain ⟨La,δa,hLa0,hLa,hLaPeriod⟩ :=
    source_covering_strip_lift p hpquot Fa (f ua) hFaAnchor
  have hb1 : b.map 1 ∈ Set.range (fun u : ℝ => (p (g u)).val) := by
    rw [hprojg]
    exact Set.mem_range_self 1
  obtain ⟨ub,hub⟩ := hb1
  have hFbAnchor : p (g ub) = Fb (1,0) := by
    apply Subtype.ext
    exact hub.trans (hFb0 1).symm
  obtain ⟨Lb,δb,hLb0,hLb,hLbPeriod⟩ :=
    source_covering_strip_lift p hpquot Fb (g ub) hFbAnchor
  let ca : C(Circle,connectedComponent x) :=
    ⟨fun z => Fa (z,0),Fa.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hca0 (z : Circle) : (ca z).val = a.map z := hFa0 z
  have hcaEmb : IsEmbedding ca := by
    apply IsEmbedding.of_comp ca.continuous continuous_subtype_val
    have heq : Subtype.val ∘ ca = a.map := funext hca0
    simpa only [heq] using a.embedded
  have hcaRange : Set.range γa = Set.range ca := by
    apply (Set.image_injective.mpr Subtype.val_injective)
    rw [haimage,←Set.range_comp]
    have heq : Subtype.val ∘ ca = a.map := funext hca0
    rw [heq]
    rfl
  have hγa0 : γa ua = ca 1 := by
    rw [←hfpath ua]
    exact hFaAnchor
  obtain ⟨ψa,hψa0,hψa,hAlignA⟩ :=
    anchored_geodesic_line_follows_embedded_boundary
      p hp ca hcaEmb γa ⟨f,hf.continuous⟩ hfpath hf.injective
      pa hpa hγaper hcaRange La (fun s => hLa s 0) ua hLa0 hγa0
  let cb : C(Circle,connectedComponent x) :=
    ⟨fun z => Fb (z,0),Fb.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hcb0 (z : Circle) : (cb z).val = b.map z := hFb0 z
  have hcbEmb : IsEmbedding cb := by
    apply IsEmbedding.of_comp cb.continuous continuous_subtype_val
    have heq : Subtype.val ∘ cb = b.map := funext hcb0
    simpa only [heq] using b.embedded
  have hcbRange : Set.range γb = Set.range cb := by
    apply (Set.image_injective.mpr Subtype.val_injective)
    rw [hbimage,←Set.range_comp]
    have heq : Subtype.val ∘ cb = b.map := funext hcb0
    rw [heq]
    rfl
  have hγb0 : γb ub = cb 1 := by
    rw [←hgpath ub]
    exact hFbAnchor
  obtain ⟨ψb,hψb0,hψb,hAlignB⟩ :=
    anchored_geodesic_line_follows_embedded_boundary
      p hp cb hcbEmb γb ⟨g,hg.continuous⟩ hgpath hg.injective
      pb hpb hγbper hcbRange Lb (fun s => hLb s 0) ub hLb0 hγb0
  have hδaIso : Isometry (δa : H2 ≃ₜ H2) := by
    have h := actual_deck_development_isometry p (Homeomorph.refl H2)
      hlocalMetric δa.val (fun z => deck.proj_smul δa z)
    intro z w
    simpa using h.edist_eq z w
  have hδbIso : Isometry (δb : H2 ≃ₜ H2) := by
    have h := actual_deck_development_isometry p (Homeomorph.refl H2)
      hlocalMetric δb.val (fun z => deck.proj_smul δb z)
    intro z w
    simpa using h.edist_eq z w
  let δaI : H2 ≃ᵢ H2 :=
    { δa.val.toEquiv with isometry_toFun := hδaIso }
  let δbI : H2 ≃ᵢ H2 :=
    { δb.val.toEquiv with isometry_toFun := hδbIso }
  obtain ⟨ca,hca,hδaAxis⟩ := aligned_periodic_strip_axis_translation
    δaI f hf La ψa hψa (by
      intro s t
      change La (s+2*Real.pi,t) = δa • La (s,t)
      exact hLaPeriod s t)
  obtain ⟨cb,hcb,hδbAxis⟩ := aligned_periodic_strip_axis_translation
    δbI g hg Lb ψb hψb (by
      intro s t
      change Lb (s+2*Real.pi,t) = δb • Lb (s,t)
      exact hLbPeriod s t)
  obtain ⟨Ba,hBa,hBoundA⟩ := aligned_strip_original_stays_bounded_from_axis
    δaI f hf La ψa ca hca hψa (by simpa using hδaAxis)
      (by intro s t; exact hLaPeriod s t)
  obtain ⟨Bb,hBb,hBoundB⟩ := aligned_strip_original_stays_bounded_from_axis
    δbI g hg Lb ψb cb hcb hψb (by simpa using hδbAxis)
      (by intro s t; exact hLbPeriod s t)
  obtain ⟨sa,sb,hsab⟩ := hmeet
  obtain ⟨eA,M,heA,heG,_,hMsign⟩ :=
    distinct_isometric_lines_meeting_normalized_endpoint_sign
      f g hf hg sa sb hsab hnefg
  let eB : H2 ≃ᵢ H2 := (IsometryEquiv.constSMul M).trans eA
  have heB (u : ℝ) : eB.symm (g u) = verticalPath u := by
    change (IsometryEquiv.constSMul M).symm (eA.symm (g u)) = verticalPath u
    rw [heG]
    exact (IsometryEquiv.constSMul M).symm_apply_apply _
  have hboundnormA (u : ℝ) :
      dist (eA.symm (La (ψa u,1))) (verticalPath u) ≤ Ba := by
    calc
      dist (eA.symm (La (ψa u,1))) (verticalPath u) =
          dist (eA.symm (La (ψa u,1))) (eA.symm (f u)) := by rw [heA]
      _ = dist (La (ψa u,1)) (f u) := eA.symm.isometry.dist_eq _ _
      _ ≤ Ba := hBoundA u
  have hboundnormB (u : ℝ) :
      dist (eB.symm (Lb (ψb u,1))) (verticalPath u) ≤ Bb := by
    calc
      dist (eB.symm (Lb (ψb u,1))) (verticalPath u) =
          dist (eB.symm (Lb (ψb u,1))) (eB.symm (g u)) := by rw [heB]
      _ = dist (Lb (ψb u,1)) (g u) := eB.symm.isometry.dist_eq _ _
      _ ≤ Bb := hBoundB u
  obtain ⟨hAplus,hAminus⟩ := bounded_axis_path_has_same_ideal_ends
    (fun u => eA.symm (La (ψa u,1))) 1 Ba (by norm_num) hBa
    (by intro u; simpa only [one_mul] using hboundnormA u)
  obtain ⟨hBplus,hBminus⟩ := bounded_axis_path_has_same_ideal_ends
    (fun u => eB.symm (Lb (ψb u,1))) 1 Bb (by norm_num) hBb
    (by intro u; simpa only [one_mul] using hboundnormB u)
  let FaOriginal : C(ℝ,H2) :=
    ⟨fun s => La (s,1),La.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let FbOriginal : C(ℝ,H2) :=
    ⟨fun s => Lb (s,1),Lb.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let FaAligned : C(ℝ,H2) :=
    ⟨fun u => La (ψa u,1),FaOriginal.continuous.comp ψa.continuous⟩
  let FbAligned : C(ℝ,H2) :=
    ⟨fun u => Lb (ψb u,1),FbOriginal.continuous.comp ψb.continuous⟩
  have hFaAlignedProper : IsProperMap FaAligned :=
    bounded_distance_from_isometric_line_is_proper FaAligned f hf Ba hBoundA
  have hFbAlignedProper : IsProperMap FbAligned :=
    bounded_distance_from_isometric_line_is_proper FbAligned g hg Bb hBoundB
  have hFaOriginalProper : IsProperMap FaOriginal := by
    have heq : FaOriginal = FaAligned ∘ ψa.symm := by
      funext s
      change La (s,1) = La (ψa (ψa.symm s),1)
      rw [ψa.apply_symm_apply]
    rw [heq]
    exact hFaAlignedProper.comp ψa.symm.isProperMap
  have hFbOriginalProper : IsProperMap FbOriginal := by
    have heq : FbOriginal = FbAligned ∘ ψb.symm := by
      funext s
      change Lb (s,1) = Lb (ψb (ψb.symm s),1)
      rw [ψb.apply_symm_apply]
    rw [heq]
    exact hFbAlignedProper.comp ψb.symm.isProperMap
  let caOriginal : C(Circle,connectedComponent x) :=
    ⟨fun z => Fa (z,1),Fa.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let cbOriginal : C(Circle,connectedComponent x) :=
    ⟨fun z => Fb (z,1),Fb.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hcaOriginalEmb : IsEmbedding caOriginal := by
    apply IsEmbedding.of_comp caOriginal.continuous continuous_subtype_val
    have heq : Subtype.val ∘ caOriginal = a₀.map := funext hFa1
    simpa only [heq] using a₀.embedded
  have hcbOriginalEmb : IsEmbedding cbOriginal := by
    apply IsEmbedding.of_comp cbOriginal.continuous continuous_subtype_val
    have heq : Subtype.val ∘ cbOriginal = b₀.map := funext hFb1
    simpa only [heq] using b₀.embedded
  have hFaOriginalInj : Function.Injective FaOriginal :=
    proper_embedded_circle_lift_injective p hp caOriginal hcaOriginalEmb
      FaOriginal hFaOriginalProper (fun s => hLa s 1)
  have hFbOriginalInj : Function.Injective FbOriginal :=
    proper_embedded_circle_lift_injective p hp cbOriginal hcbOriginalEmb
      FbOriginal hFbOriginalProper (fun s => hLb s 1)
  let diskA : C(ℝ,ℂ) :=
    ⟨fun u => (cayley (eA.symm (La (ψa u,1))) : ℂ),
      continuous_subtype_val.comp (cayley_continuous.comp
        (eA.symm.continuous.comp FaAligned.continuous))⟩
  let diskB : C(ℝ,ℂ) :=
    ⟨fun u => (cayley (eB.symm (Lb (ψb u,1))) : ℂ),
      continuous_subtype_val.comp (cayley_continuous.comp
        (eB.symm.continuous.comp FbAligned.continuous))⟩
  have hDiskAInj : Function.Injective diskA := by
    intro u v huv
    have hcayley : cayley (eA.symm (La (ψa u,1))) =
        cayley (eA.symm (La (ψa v,1))) := Subtype.ext huv
    have hH2 := eA.symm.injective (cayley_injective hcayley)
    exact ψa.injective (hFaOriginalInj hH2)
  have hDiskBInj : Function.Injective diskB := by
    intro u v huv
    have hcayley : cayley (eB.symm (Lb (ψb u,1))) =
        cayley (eB.symm (Lb (ψb v,1))) := Subtype.ext huv
    have hH2 := eB.symm.injective (cayley_injective hcayley)
    exact ψb.injective (hFbOriginalInj hH2)
  have hDiskAOff (u : ℝ) : diskA u ≠ (-1:ℂ) ∧ diskA u ≠ 1 := by
    have hnorm : ‖diskA u‖ < 1 := by
      change ‖(cayley (eA.symm (La (ψa u,1))) : ℂ)‖ < 1
      simpa [cayley,Metric.mem_ball,dist_zero_right] using
        cayley_mem_ball (eA.symm (La (ψa u,1)))
    constructor
    · intro heq
      rw [heq] at hnorm
      norm_num at hnorm
    · intro heq
      rw [heq] at hnorm
      norm_num at hnorm
  have hDiskBOff (u : ℝ) : diskB u ≠ (-1:ℂ) ∧ diskB u ≠ 1 := by
    have hnorm : ‖diskB u‖ < 1 := by
      change ‖(cayley (eB.symm (Lb (ψb u,1))) : ℂ)‖ < 1
      simpa [cayley,Metric.mem_ball,dist_zero_right] using
        cayley_mem_ball (eB.symm (Lb (ψb u,1)))
    constructor
    · intro heq
      rw [heq] at hnorm
      norm_num at hnorm
    · intro heq
      rw [heq] at hnorm
      norm_num at hnorm
  obtain ⟨arcA,hArcA,hArcA0,hArcA1,hArcARange⟩ :=
    two_endpoint_compactification diskA diskA.continuous hDiskAInj
      (-1:ℂ) 1 (by norm_num) hDiskAOff hAminus hAplus
  obtain ⟨arcB,hArcB,hArcB0,hArcB1,hArcBRange⟩ :=
    two_endpoint_compactification diskB diskB.continuous hDiskBInj
      (-1:ℂ) 1 (by norm_num) hDiskBOff hBminus hBplus
  have hsignFactors := hMsign
  rw [ideal_endpoint_im,ideal_endpoint_im] at hsignFactors
  have hfirst : (-2*M 0 0*M 1 0)/(M 0 0^2+M 1 0^2) ≠ 0 :=
    (mul_ne_zero_iff.mp (ne_of_lt hsignFactors)).1
  have hsecond : (-2*M 0 1*M 1 1)/(M 0 1^2+M 1 1^2) ≠ 0 :=
    (mul_ne_zero_iff.mp (ne_of_lt hsignFactors)).2
  have hM00 : M 0 0 ≠ 0 := by
    intro hz
    apply hfirst
    rw [hz]
    norm_num
  have hM11 : M 1 1 ≠ 0 := by
    intro hz
    apply hsecond
    rw [hz]
    norm_num
  obtain ⟨eDisk,hEDisk,hEDiskBoundary⟩ :=
    actual_h2_isometry_closed_disk_extension (IsometryEquiv.constSMul M)
  have hEDiskSign :
      (eDisk ⟨-1,by simp [Metric.mem_closedBall,dist_zero_right]⟩ : ℂ).im *
        (eDisk ⟨1,by simp [Metric.mem_closedBall,dist_zero_right]⟩ : ℂ).im < 0 := by
    obtain ⟨hl,hr⟩ :=
      sl_disk_extension_endpoint_images M hM00 hM11 eDisk hEDisk
    rw [hl,hr,mul_comm]
    exact hMsign
  refine ⟨p,f,g,La,Lb,δa,δb,ψa,ψb,ca,cb,Ba,Bb,eA,eB,arcA,arcB,eDisk,
    hpquot,hp,hf,hg,
    hprojf,hprojg,hnefg,⟨sa,sb,hsab⟩,?_,?_,?_,?_,hAlignA,hAlignB,hψa,hψb,
    hca,hcb,?_,?_,hBa,hBb,hBoundA,hBoundB,heA,heB,
    hAplus,hAminus,hBplus,hBminus,hFaOriginalInj,hFbOriginalInj,
    hArcA,hArcB,hArcA0,hArcA1,hArcB0,hArcB1,
    hArcARange,hArcBRange,?_,hEDiskBoundary,hEDiskSign,
    hLaPeriod,hLbPeriod,?_⟩
  · intro s
    exact (congrArg Subtype.val (hLa s 0)).trans (hFa0 _)
  · intro s
    exact (congrArg Subtype.val (hLa s 1)).trans (hFa1 _)
  · intro s
    exact (congrArg Subtype.val (hLb s 0)).trans (hFb0 _)
  · intro s
    exact (congrArg Subtype.val (hLb s 1)).trans (hFb1 _)
  · exact hδaAxis
  · exact hδbAxis
  · intro z
    change eDisk (cayley z) =
      cayley (eA.symm (eA ((IsometryEquiv.constSMul M) z)))
    rw [eA.symm_apply_apply]
    change eDisk (cayley z) = cayley (M • z)
    exact hEDisk z
  · apply Set.disjoint_left.mpr
    intro z hzLa hzLb
    obtain ⟨s,hs⟩ := hzLa
    obtain ⟨t,ht⟩ := hzLb
    have hza : (p z).val ∈ a₀.image := by
      refine ⟨Circle.exp s,?_⟩
      rw [←hs]
      exact ((congrArg Subtype.val (hLa s 1)).trans (hFa1 _)).symm
    have hzb : (p z).val ∈ b₀.image := by
      refine ⟨Circle.exp t,?_⟩
      rw [←ht]
      exact ((congrArg Subtype.val (hLb t 1)).trans (hFb1 _)).symm
    exact (Set.disjoint_left.mp hdis) hza hzb

theorem source_actual_distinct_closed_geodesics_disjoint_of_disjoint_classes
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (H : ClosedHyperbolicMetric E) (a b a₀ b₀ : Curve E)
    (_ha : Essential a) (_hb : Essential b)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hne : a.image ≠ b.image)
    (haa : FreeHomotopic ⟨a.map,a.embedded.continuous⟩
      ⟨a₀.map,a₀.embedded.continuous⟩)
    (hbb : FreeHomotopic ⟨b.map,b.embedded.continuous⟩
      ⟨b₀.map,b₀.embedded.continuous⟩)
    (hdis : Disjoint a₀.image b₀.image) :
    Disjoint a.image b.image := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨p,f,g,La,Lb,δa,δb,ψa,ψb,ca,cb,Ba,Bb,eA,eB,arcA,arcB,eDisk,
    hpquot,hp,hf,hg,hpa,hpb,hnefg,hmeet,
    hLa0,hLa1,hLb0,hLb1,hRangeA0,hRangeB0,hAlignA,hAlignB,
    hca,hcb,hδa,hδb,hBa,hBb,hBoundA,hBoundB,heA,heB,
    hAplus,hAminus,hBplus,hBminus,hLa1inj,hLb1inj,hArcA,hArcB,
    hArcA0,hArcA1,hArcB0,hArcB1,hArcARange,hArcBRange,
    hEDisk,hEDiskBoundary,hEDiskSign,hPeriodA,hPeriodB,hOriginalDis⟩ :=
    source_g2_contact_has_disjoint_original_strip_lifts
      H a b a₀ b₀ hageo hbgeo hne haa hbb hdis x hxa hxb
  let γ : C(ℝ,ℂ) :=
    ⟨fun u => (cayley (eA.symm (Lb (ψb u,1))) : ℂ),
      continuous_subtype_val.comp (cayley_continuous.comp
        (eA.symm.continuous.comp
          (Lb.continuous.comp (ψb.continuous.prodMk continuous_const))))⟩
  have hγ (u : ℝ) : ‖γ u‖ < 1 := by
    change ‖(cayley (eA.symm (Lb (ψb u,1))) : ℂ)‖ < 1
    simpa only [cayley,Metric.mem_ball,dist_zero_right] using
      cayley_mem_ball (eA.symm (Lb (ψb u,1)))
  have hArcAIn (s : unitInterval) : ‖arcA s‖ ≤ 1 := by
    have hs : arcA s ∈ insert (-1:ℂ) (insert 1
        (Set.range (fun u : ℝ => (cayley (eA.symm (La (ψa u,1))) : ℂ)))) := by
      rw [←hArcARange]
      exact Set.mem_range_self s
    rcases hs with hs | hs
    · rw [hs]; norm_num
    rcases hs with hs | ⟨u,hu⟩
    · rw [hs]; norm_num
    · rw [←hu]
      have hh := cayley_mem_ball (eA.symm (La (ψa u,1)))
      apply le_of_lt
      simpa only [cayley,Metric.mem_ball,dist_zero_right] using hh
  have hArcABoundary (s : unitInterval) (hs : ‖arcA s‖ = 1) :
      arcA s = -1 ∨ arcA s = 1 := by
    have hmem : arcA s ∈ insert (-1:ℂ) (insert 1
        (Set.range (fun u : ℝ => (cayley (eA.symm (La (ψa u,1))) : ℂ)))) := by
      rw [←hArcARange]
      exact Set.mem_range_self s
    rcases hmem with he | he
    · exact Or.inl he
    rcases he with he | ⟨u,hu⟩
    · exact Or.inr he
    · have hh : ‖(cayley (eA.symm (La (ψa u,1))) : ℂ)‖ < 1 := by
        simpa only [cayley,Metric.mem_ball,dist_zero_right] using
          cayley_mem_ball (eA.symm (La (ψa u,1)))
      have heq : ‖(cayley (eA.symm (La (ψa u,1))) : ℂ)‖ = ‖arcA s‖ := by
        simpa only [] using congrArg norm hu
      exact (False.elim ((ne_of_lt hh) (heq.trans hs)))
  let left : Metric.closedBall (0:ℂ) 1 :=
    ⟨-1,by simp [Metric.mem_closedBall,dist_zero_right]⟩
  let right : Metric.closedBall (0:ℂ) 1 :=
    ⟨1,by simp [Metric.mem_closedBall,dist_zero_right]⟩
  let w₁ : ℂ := eDisk left
  let w₂ : ℂ := eDisk right
  have hn₁ : ‖w₁‖=1 := (hEDiskBoundary left).mpr (by simp [left])
  have hn₂ : ‖w₂‖=1 := (hEDiskBoundary right).mpr (by simp [right])
  have hsign : w₁.im*w₂.im < 0 := hEDiskSign
  have hγeq (u : ℝ) : γ u =
      (eDisk (cayley (eB.symm (Lb (ψb u,1)))) : ℂ) := by
    change (cayley (eA.symm (Lb (ψb u,1))) : ℂ) = _
    rw [hEDisk]
    rw [eB.apply_symm_apply]
  have hclosure (l : Filter ℝ) [NeBot l] (v : Metric.closedBall (0:ℂ) 1)
      (hv : Tendsto (fun u : ℝ =>
        (cayley (eB.symm (Lb (ψb u,1))) : ℂ)) l (𝓝 (v:ℂ))) :
      actualComplexSchoenflies (eDisk v:ℂ) ∈
        closure (Set.range (fun u : ℝ => actualComplexSchoenflies (γ u))) := by
    have hsub : Tendsto (fun u : ℝ => cayley (eB.symm (Lb (ψb u,1))))
        l (𝓝 v) := tendsto_subtype_rng.mpr hv
    have htrans : Tendsto (fun u : ℝ =>
        actualComplexSchoenflies (eDisk (cayley (eB.symm (Lb (ψb u,1)))) : ℂ))
        l (𝓝 (actualComplexSchoenflies (eDisk v:ℂ))) :=
      (actualComplexSchoenflies.continuous.continuousAt.tendsto).comp
        ((continuous_subtype_val.continuousAt.tendsto).comp
          (eDisk.continuous.continuousAt.tendsto.comp hsub))
    have hactual : Tendsto (fun u : ℝ => actualComplexSchoenflies (γ u))
        l (𝓝 (actualComplexSchoenflies (eDisk v:ℂ))) := by
      simpa only [hγeq] using htrans
    exact mem_closure_of_tendsto hactual
      (Filter.Eventually.of_forall (fun u => Set.mem_range_self u))
  have hw₁ : actualComplexSchoenflies w₁ ∈
      closure (Set.range (fun u : ℝ => actualComplexSchoenflies (γ u))) :=
    hclosure atBot left (by simpa only [left] using hBminus)
  have hw₂ : actualComplexSchoenflies w₂ ∈
      closure (Set.range (fun u : ℝ => actualComplexSchoenflies (γ u))) :=
    hclosure atTop right (by simpa only [right] using hBplus)
  obtain ⟨z,⟨v,hv⟩,⟨s,hs⟩⟩ :=
    g2_disk_arc_opposite_semicircle_path_intersects arcA hArcA
      hArcA0 hArcA1 hArcAIn hArcABoundary γ hγ
      w₁ w₂ hn₁ hn₂ hsign hw₁ hw₂
  have hznorm : ‖z‖ < 1 := by rw [←hv]; exact hγ v
  have hzA : z ∈ insert (-1:ℂ) (insert 1
      (Set.range (fun u : ℝ => (cayley (eA.symm (La (ψa u,1))) : ℂ)))) := by
    rw [←hArcARange]
    exact ⟨s,hs⟩
  rcases hzA with hzneg | hzA
  · rw [hzneg] at hznorm
    norm_num at hznorm
  rcases hzA with hzpos | ⟨u,hu⟩
  · rw [hzpos] at hznorm
    norm_num at hznorm
  have hLift : La (ψa u,1) = Lb (ψb v,1) := by
    apply eA.symm.injective
    apply cayley_injective
    apply Subtype.ext
    exact hu.trans hv.symm
  exact (Set.disjoint_left.mp hOriginalDis)
    ⟨ψa u,rfl⟩ ⟨ψb v,hLift.symm⟩

#print axioms source_component_geodesic_lines
#print axioms source_closed_geodesic_has_developed_lines
#print axioms source_common_component_developed_cover
#print axioms source_closed_geodesic_lines_on_fixed_cover
#print axioms source_two_closed_geodesics_have_common_developed_lines
#print axioms source_distinct_closed_geodesics_have_meeting_distinct_lifts
#print axioms source_g2_contact_has_disjoint_original_strip_lifts
#print axioms source_actual_distinct_closed_geodesics_disjoint_of_disjoint_classes

end CurveComplex.Hyperbolic
