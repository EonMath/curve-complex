import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import ClassificationOfSurfaces.RepresentativeCarrier
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.PositionExtension.TwistedBandReflection
import Mathlib

open scoped Manifold
namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
set_option maxHeartbeats 1000000

/-- The first a-a pair of a literal nonorientable representative contains
an embedded twisted square/strip. Source: canonical crosscap word geometry.
Caller: the nonorientable branch of actual_compact_cut_boundary_preserving_
orientable_polygon, followed by the existing released twisted-strip reflection
constructor. No orientation or reflection witness is supplied as an input. -/
theorem actual_nonorientable_normal_form_first_crosscap_square_strip
    (p n : ℕ) (hp : 0 < p) :
    ∃ (ε : ℝ) (hε : 0 < ε)
      (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → Quot (NonOrientableRel p n))
      (band : unitInterval × CurveComplex.BandWidth → Quot (NonOrientableRel p n)),
      Topology.IsEmbedding square ∧ Topology.IsEmbedding band ∧
      (∀ t, band (0,t) = square (CurveComplex.squarePort ε hε 2 t)) ∧
      (∀ t, band (1,t) = square (CurveComplex.squarePort ε hε 0
        (CurveComplex.flipBandWidth true t))) ∧
      Set.range band ∩ Set.range square =
        Set.range (fun t => square (CurveComplex.squarePort ε hε 2 t)) ∪
        Set.range (fun t => square (CurveComplex.squarePort ε hε 0 t)) := by
  classical
  let ε : ℝ := 1/4
  have hε : 0 < ε := by norm_num [ε]
  let D := Metric.closedBall ((0,0) : ℝ × ℝ) ε
  let Q := Quot (NonOrientableRel p n)
  let L : ℝ := 2*p+3*n
  have hL : 2 ≤ L := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hnR : (0 : ℝ) ≤ n := by positivity
    dsimp [L]
    linarith
  have hLpos : 0 < L := by linarith
  have coords (v : D) : |v.val.1| ≤ ε ∧ |v.val.2| ≤ ε := by
    simpa only [D, Metric.mem_closedBall, dist_eq_norm, Prod.norm_def,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero,
      Real.norm_eq_abs, max_le_iff] using v.property
  let cap (k : ℝ) (v : D) : Complex.ClosedUnitDisc :=
    ⟨((1-|v.val.2| : ℝ) : ℂ) * (Real.fourierChar ((k+1/2+v.val.1)/L) : ℂ), by
      have hr : 0 ≤ 1-|v.val.2| := by
        have := (coords v).2
        dsimp [ε] at this
        linarith
      simp only [Metric.mem_closedBall, dist_zero_right, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one,
        abs_of_nonneg hr]
      linarith [abs_nonneg v.val.2]⟩
  have hcap (k : ℝ) : Continuous (cap k) := by
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous (fun v : D => ((1-|v.val.2| : ℝ) : ℂ))).mul
      (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop)))
  let q : Complex.ClosedUnitDisc → Q := Quot.mk (NonOrientableRel p n)
  have hq : Continuous q := continuous_quot_mk
  have hBoundaryNorm (r : ℝ) : ‖(Complex.ClosedUnitDisc.bdyPtOfReal r : ℂ)‖ = 1 := by
    exact Circle.norm_coe _
  have hRelBoundary {z w : Complex.ClosedUnitDisc} (h : NonOrientableRel p n z w) :
      ‖(z : ℂ)‖ = 1 ∧ ‖(w : ℂ)‖ = 1 := by
    cases h <;> exact ⟨hBoundaryNorm _, hBoundaryNorm _⟩
  have hEqvInterior {z w : Complex.ClosedUnitDisc}
      (h : Relation.EqvGen (NonOrientableRel p n) z w) :
      (‖(z : ℂ)‖ < 1 ∨ ‖(w : ℂ)‖ < 1) → z = w := by
    induction h with
    | rel z w h =>
      intro hh
      obtain ⟨hz, hw⟩ := hRelBoundary h
      rcases hh with hh | hh <;> linarith
    | refl z => intro _; rfl
    | symm z w h ih =>
      intro hh
      exact (ih hh.symm).symm
    | trans z w v h₁ h₂ ih₁ ih₂ =>
      intro hh
      rcases hh with hz | hv
      · have he := ih₁ (Or.inl hz)
        subst w
        exact ih₂ (Or.inl hz)
      · have he := ih₂ (Or.inr hv)
        subst w
        exact ih₁ (Or.inr hv)
  have hQuotInterior {z w : Complex.ClosedUnitDisc} (hz : ‖(z : ℂ)‖ < 1)
      (he : q z = q w) : z = w :=
    hEqvInterior (Quot.eqvGen_exact he) (Or.inl hz)
  let V : Set Complex.ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
  let W : Set Q := q '' V
  have hpreW : q ⁻¹' W = V := by
    ext z
    constructor
    · rintro ⟨w, hw, he⟩
      have hh : w = z := hQuotInterior hw he
      simpa [← hh] using hw
    · intro hz
      exact ⟨z,hz,rfl⟩
  have hWOpen : IsOpen W := by
    rw [← (isQuotientMap_quot_mk (r := NonOrientableRel p n)).isOpen_preimage, hpreW]
    exact isOpen_lt (by fun_prop) continuous_const
  have hRestrictInjective : Function.Injective (W.restrictPreimage q) := by
    intro z w he
    apply Subtype.ext
    have hz : z.val ∈ V := by rw [← hpreW]; exact z.property
    exact hQuotInterior hz (congrArg Subtype.val he)
  have hRestrictOpen := (isQuotientMap_quot_mk (r := NonOrientableRel p n)).restrictPreimage_isOpen hWOpen
  have hRestrictEmbedding : IsEmbedding (W.restrictPreimage q) := by
    exact (isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
      ⟨hRestrictOpen.continuous, hRestrictInjective,
       hRestrictOpen.isCoinducing.isOpenMap_of_injective hRestrictInjective⟩).isEmbedding
  have hBoundaryParameter {r s : ℝ} (hr : 0 < r ∧ r < L)
      (hs : 0 ≤ s ∧ s ≤ L)
      (he : Complex.ClosedUnitDisc.bdyPtOfReal (r/L) =
        Complex.ClosedUnitDisc.bdyPtOfReal (s/L)) : r = s := by
    have hf : Real.fourierChar (r/L) = Real.fourierChar (s/L) :=
      Subtype.ext (congrArg (fun z : Complex.ClosedUnitDisc => (z:ℂ)) he)
    rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hf
    obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hf
    have hks : r/L = s/L+(k:ℝ) := by
      apply mul_left_cancel₀ (by positivity : (2*Real.pi : ℝ) ≠ 0)
      calc
        2*Real.pi*(r/L) = 2*Real.pi*(s/L)+(k:ℝ)*(2*Real.pi) := hk
        _ = 2*Real.pi*(s/L+(k:ℝ)) := by ring
    have hscaled := congrArg (fun x : ℝ => x*L) hks
    rw [add_mul,div_mul_cancel₀ _ hLpos.ne',div_mul_cancel₀ _ hLpos.ne'] at hscaled
    by_cases hk0 : k=0
    · simpa [hk0] using hscaled
    · have hkcase : k ≤ -1 ∨ 1 ≤ k := by omega
      rcases hkcase with hkneg | hkpos
      · have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast hkneg
        nlinarith
      · have hkR : (1:ℝ) ≤ k := by exact_mod_cast hkpos
        nlinarith
  let bd (r : ℝ) := Complex.ClosedUnitDisc.bdyPtOfReal (r/L)
  have hBdNegative (u : ℝ) : bd (-u) = bd (L-u) := by
    change Complex.ClosedUnitDisc.bdyPtOfReal (-u/L) =
      Complex.ClosedUnitDisc.bdyPtOfReal ((L-u)/L)
    calc
      _ = Complex.ClosedUnitDisc.bdyPtOfReal (-u/L+1) := by
        simpa only [Int.cast_one] using
          (Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-u/L) 1).symm
      _ = _ := by
        congr 1
        field_simp
        ring
  have hRelFirstPair (t : ℝ) (ht : 0 < t ∧ t < 1)
      {z w : Complex.ClosedUnitDisc} (h : NonOrientableRel p n z w)
      (hpair : (z=bd t ∨ z=bd (1+t)) ∨ (w=bd t ∨ w=bd (1+t))) :
      z=bd t ∧ w=bd (1+t) := by
    have htt : 0 < t ∧ t < L := ⟨ht.1,by linarith⟩
    have h1tt : 0 < 1+t ∧ 1+t < L := ⟨by linarith,by linarith⟩
    have hNums {r s : ℝ} (hr : 0 ≤ r ∧ r ≤ L) (hs : 0 ≤ s ∧ s ≤ L)
        (hh : (bd r=bd t ∨ bd r=bd (1+t)) ∨
          (bd s=bd t ∨ bd s=bd (1+t))) :
        r=t ∨ r=1+t ∨ s=t ∨ s=1+t := by
      rcases hh with (hh | hh) | (hh | hh)
      · exact Or.inl (hBoundaryParameter htt hr hh.symm).symm
      · exact Or.inr (Or.inl (hBoundaryParameter h1tt hr hh.symm).symm)
      · exact Or.inr (Or.inr (Or.inl (hBoundaryParameter htt hs hh.symm).symm))
      · exact Or.inr (Or.inr (Or.inr (hBoundaryParameter h1tt hs hh.symm).symm))
    cases h with
    | a x i =>
      have hi : (i:ℝ)+1 ≤ p := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
      have hiNonneg : (0:ℝ) ≤ i := by positivity
      have hx := x.property
      have hnNonneg : (0:ℝ) ≤ n := by positivity
      have hr : 0 ≤ 2*(i:ℝ)+(x:ℝ) ∧ 2*(i:ℝ)+(x:ℝ) ≤ L := by
        dsimp [L]
        constructor <;> nlinarith [hx.1,hx.2]
      have hs : 0 ≤ 2*(i:ℝ)+1+(x:ℝ) ∧ 2*(i:ℝ)+1+(x:ℝ) ≤ L := by
        dsimp [L]
        constructor <;> nlinarith [hx.1,hx.2]
      change (bd (2*(i:ℝ)+(x:ℝ))=bd t ∨ bd (2*(i:ℝ)+(x:ℝ))=bd (1+t)) ∨
        (bd (2*(i:ℝ)+1+(x:ℝ))=bd t ∨ bd (2*(i:ℝ)+1+(x:ℝ))=bd (1+t)) at hpair
      have hn := hNums hr hs hpair
      have hi0 : (i:ℕ)=0 := by
        by_contra hi0
        have hiNat : 1 ≤ (i:ℕ) := by omega
        have hiR : (1:ℝ) ≤ i := by exact_mod_cast hiNat
        rcases hn with hn | hn | hn | hn <;> nlinarith [hx.1,hx.2]
      have hiR : (i:ℝ)=0 := by exact_mod_cast hi0
      have hxt : (x:ℝ)=t := by
        rcases hn with hn | hn | hn | hn <;> nlinarith [hx.1,hx.2]
      constructor <;> change bd _=bd _ <;> congr 1 <;> rw [hiR,hxt] <;> ring
    | c x i =>
      have hi : (i:ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
      have hiNonneg : (0:ℝ) ≤ i := by positivity
      have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
      have hx := x.property
      have hr : 0 ≤ L-(3*(i:ℝ)+(x:ℝ)) ∧ L-(3*(i:ℝ)+(x:ℝ)) ≤ L := by
        dsimp [L]
        constructor <;> nlinarith [hx.1,hx.2]
      have hs : 0 ≤ L-(3*(i:ℝ)+3-(x:ℝ)) ∧ L-(3*(i:ℝ)+3-(x:ℝ)) ≤ L := by
        dsimp [L]
        constructor <;> nlinarith [hx.1,hx.2]
      have hrLow : 2 ≤ L-(3*(i:ℝ)+(x:ℝ)) := by
        dsimp [L]
        nlinarith [hx.1,hx.2]
      have hsLow : 2 ≤ L-(3*(i:ℝ)+3-(x:ℝ)) := by
        dsimp [L]
        nlinarith [hx.1,hx.2]
      change (bd (-(3*(i:ℝ)+(x:ℝ)))=bd t ∨ bd (-(3*(i:ℝ)+(x:ℝ)))=bd (1+t)) ∨
        (bd (-(3*(i:ℝ)+3-(x:ℝ)))=bd t ∨ bd (-(3*(i:ℝ)+3-(x:ℝ)))=bd (1+t)) at hpair
      rw [hBdNegative,hBdNegative] at hpair
      have hn := hNums hr hs hpair
      rcases hn with hn | hn | hn | hn <;> exfalso <;> linarith
  have hEqvFirstPair (t : ℝ) (ht : 0 < t ∧ t < 1)
      {z w : Complex.ClosedUnitDisc} (h : Relation.EqvGen (NonOrientableRel p n) z w) :
      (z=bd t ∨ z=bd (1+t)) ↔ (w=bd t ∨ w=bd (1+t)) := by
    induction h with
    | rel z w h =>
      constructor
      · intro hz
        exact Or.inr (hRelFirstPair t ht h (Or.inl hz)).2
      · intro hw
        exact Or.inl (hRelFirstPair t ht h (Or.inr hw)).1
    | refl z => rfl
    | symm z w h ih => exact ih.symm
    | trans z w v h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  have hQuotFirstPair (t : ℝ) (ht : 0 < t ∧ t < 1)
      (z : Complex.ClosedUnitDisc) : q (bd t)=q z ↔ z=bd t ∨ z=bd (1+t) := by
    constructor
    · intro he
      exact (hEqvFirstPair t ht (Quot.eqvGen_exact he)).mp (Or.inl rfl)
    · rintro (he | he)
      · rw [he]
      · rw [he]
        let x : unitInterval := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
        simpa [bd,L,x] using Quot.sound (NonOrientableRel.a (n:=n) x (⟨0,hp⟩ : Fin p))
  have hCapExactNorm (k : ℝ) (v : D) : ‖(cap k v : ℂ)‖ = 1-|v.val.2| := by
    have hy := (coords v).2
    have hr : 0 ≤ 1-|v.val.2| := by dsimp [ε] at hy; linarith
    change ‖((1-|v.val.2| : ℝ) : ℂ) *
      (Real.fourierChar ((k+1/2+v.val.1)/L) : ℂ)‖ = _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Circle.norm_coe,
      mul_one,abs_of_nonneg hr]
  have hCapSeam (k : ℝ) (v : D) (hy : v.val.2=0) :
      cap k v = bd (k+1/2+v.val.1) := by
    apply Subtype.ext
    simp [cap,bd,hy,Complex.ClosedUnitDisc.bdyPtOfReal]
  have hCapFiber0 (v : D) (z : Complex.ClosedUnitDisc) (he : q (cap 0 v)=q z) :
      z=cap 0 v ∨ (v.val.2=0 ∧ z=cap 1 v) := by
    by_cases hy : v.val.2=0
    · have hx : 0 < 1/2+v.val.1 ∧ 1/2+v.val.1 < 1 := by
        have hh := abs_le.mp (coords v).1
        dsimp [ε] at hh
        constructor <;> linarith
      rw [hCapSeam 0 v hy] at he
      have hz := (hQuotFirstPair (1/2+v.val.1) hx z).mp (by simpa using he)
      rcases hz with hz | hz
      · left
        simpa [hCapSeam 0 v hy] using hz
      · right
        refine ⟨hy,?_⟩
        simpa [hCapSeam 1 v hy,add_assoc] using hz
    · have hn : ‖(cap 0 v : ℂ)‖ < 1 := by
        rw [hCapExactNorm]
        have hh : 0 < |v.val.2| := abs_pos.mpr hy
        linarith
      exact Or.inl (hQuotInterior hn he).symm
  have hCapFiber1 (v : D) (z : Complex.ClosedUnitDisc) (he : q (cap 1 v)=q z) :
      z=cap 1 v ∨ (v.val.2=0 ∧ z=cap 0 v) := by
    by_cases hy : v.val.2=0
    · have hx : 0 < 1/2+v.val.1 ∧ 1/2+v.val.1 < 1 := by
        have hh := abs_le.mp (coords v).1
        dsimp [ε] at hh
        constructor <;> linarith
      have hzero : q (bd (1/2+v.val.1))=q (cap 1 v) := by
        apply (hQuotFirstPair (1/2+v.val.1) hx (cap 1 v)).mpr
        right
        simpa [add_assoc] using hCapSeam 1 v hy
      have hz := (hQuotFirstPair (1/2+v.val.1) hx z).mp (hzero.trans he)
      rcases hz with hz | hz
      · right
        refine ⟨hy,?_⟩
        simpa [hCapSeam 0 v hy] using hz
      · left
        simpa [hCapSeam 1 v hy,add_assoc] using hz
    · have hn : ‖(cap 1 v : ℂ)‖ < 1 := by
        rw [hCapExactNorm]
        have hh : 0 < |v.val.2| := abs_pos.mpr hy
        linarith
      exact Or.inl (hQuotInterior hn he).symm
  have hCapCoordinates (k l : ℝ) (hk : 0 ≤ k ∧ k ≤ 1) (hl : 0 ≤ l ∧ l ≤ 1)
      (u v : D) (he : cap k u=cap l v) :
      k+u.val.1=l+v.val.1 ∧ |u.val.2|=|v.val.2| := by
    have hnorm := congrArg (fun z : Complex.ClosedUnitDisc => ‖(z:ℂ)‖) he
    rw [hCapExactNorm,hCapExactNorm] at hnorm
    have hrad : (1-|u.val.2| : ℝ)=(1-|v.val.2| : ℝ) := hnorm
    have hrpos : 0 < 1-|u.val.2| := by
      have hh := (coords u).2
      dsimp [ε] at hh
      linarith
    have hcomplex := congrArg (fun z : Complex.ClosedUnitDisc => (z:ℂ)) he
    change ((1-|u.val.2| : ℝ):ℂ)*(Real.fourierChar ((k+1/2+u.val.1)/L):ℂ)=
      ((1-|v.val.2| : ℝ):ℂ)*(Real.fourierChar ((l+1/2+v.val.1)/L):ℂ) at hcomplex
    rw [←hrad] at hcomplex
    have hf := mul_left_cancel₀ (by exact_mod_cast hrpos.ne' :
      ((1-|u.val.2| : ℝ):ℂ) ≠ 0) hcomplex
    have hb : bd (k+1/2+u.val.1)=bd (l+1/2+v.val.1) := Subtype.ext hf
    have hu := abs_le.mp (coords u).1
    have hv := abs_le.mp (coords v).1
    dsimp [ε] at hu hv
    have hkR : 0 < k+1/2+u.val.1 ∧ k+1/2+u.val.1 < L := by
      constructor <;> linarith [hk.1,hk.2]
    have hlR : 0 ≤ l+1/2+v.val.1 ∧ l+1/2+v.val.1 ≤ L := by
      constructor <;> linarith [hl.1,hl.2]
    have hangle := hBoundaryParameter hkR hlR hb
    constructor <;> linarith
  have hseam (v : D) (hv : v.val.2 = 0) : q (cap 1 v) = q (cap 0 v) := by
    let t : unitInterval := ⟨1/2+v.val.1, by
      have hx := abs_le.mp (coords v).1
      dsimp [ε] at hx
      constructor <;> linarith⟩
    let i : Fin p := ⟨0,hp⟩
    have hh := Quot.sound (NonOrientableRel.a (n := n) t i)
    change q (Complex.ClosedUnitDisc.bdyPtOfReal ((2*(i:ℝ)+(t:ℝ))/L)) =
      q (Complex.ClosedUnitDisc.bdyPtOfReal ((2*(i:ℝ)+1+(t:ℝ))/L)) at hh
    have h0 : cap 0 v = Complex.ClosedUnitDisc.bdyPtOfReal ((t:ℝ)/L) := by
      apply Subtype.ext
      simp [cap, hv, t, Complex.ClosedUnitDisc.bdyPtOfReal]
    have h1 : cap 1 v = Complex.ClosedUnitDisc.bdyPtOfReal ((1+(t:ℝ))/L) := by
      apply Subtype.ext
      simp only [cap, hv, abs_zero, sub_zero, Complex.ofReal_one, one_mul,
        Complex.ClosedUnitDisc.bdyPtOfReal, t]
      congr 2
      ring
    rw [h1,h0]
    simpa only [i, Fin.val_mk, Nat.cast_zero, mul_zero, zero_add] using hh.symm
  let square : D → Q := fun v => if v.val.2 ≤ 0 then q (cap 1 v) else q (cap 0 v)
  have hSquareContinuous : Continuous square := by
    apply continuous_if_le (by fun_prop) continuous_const
      (hq.comp (hcap 1)).continuousOn (hq.comp (hcap 0)).continuousOn
    intro v hv
    exact hseam v hv
  have hSquareInjective : Function.Injective square := by
    intro u v he
    have hsame (k : ℝ) (hk : 0 ≤ k ∧ k ≤ 1) (hec : cap k u=cap k v) :
        u.val.1=v.val.1 ∧ |u.val.2|=|v.val.2| := by
      have hh := hCapCoordinates k k hk hk u v hec
      exact ⟨by linarith [hh.1],hh.2⟩
    have hdiff (k l : ℝ) (hk : 0 ≤ k ∧ k ≤ 1) (hl : 0 ≤ l ∧ l ≤ 1)
        (hkl : |k-l|=1) (hec : cap k u=cap l v) : False := by
      have hh := hCapCoordinates k l hk hl u v hec
      have hu := abs_le.mp (coords u).1
      have hv := abs_le.mp (coords v).1
      have hkl' := abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hkl
      dsimp [ε] at hu hv
      rcases hkl' with hkl' | hkl' <;> linarith [hh.1]
    dsimp [square] at he
    split_ifs at he with hu hv hv
    · rcases hCapFiber1 u (cap 1 v) he with hec | ⟨hy,hec⟩
      · have hh := hsame 1 (by norm_num) hec.symm
        apply Subtype.ext
        apply Prod.ext
        · exact hh.1
        · simpa only [abs_of_nonpos hu,abs_of_nonpos hv,neg_neg] using congrArg Neg.neg hh.2
      · exact False.elim (hdiff 0 1 (by norm_num) (by norm_num) (by norm_num) hec.symm)
    · rcases hCapFiber1 u (cap 0 v) he with hec | ⟨hy,hec⟩
      · exact False.elim (hdiff 1 0 (by norm_num) (by norm_num) (by norm_num) hec.symm)
      · have hh := hsame 0 (by norm_num) hec.symm
        have hzero : v.val.2=0 := by simpa [hy] using hh.2.symm
        exact False.elim (hv (by rw [hzero]))
    · rcases hCapFiber0 u (cap 1 v) he with hec | ⟨hy,hec⟩
      · exact False.elim (hdiff 0 1 (by norm_num) (by norm_num) (by norm_num) hec.symm)
      · exact False.elim (hu (by rw [hy]))
    · rcases hCapFiber0 u (cap 0 v) he with hec | ⟨hy,hec⟩
      · have hh := hsame 0 (by norm_num) hec.symm
        apply Subtype.ext
        apply Prod.ext
        · exact hh.1
        · simpa only [abs_of_nonneg (not_le.mp hu).le,
            abs_of_nonneg (not_le.mp hv).le] using hh.2
      · exact False.elim (hu (by rw [hy]))
  have hSquareClosedMap : IsClosedMap square := by
    intro C hC
    let Cm := C ∩ {v : D | v.val.2 ≤ 0}
    let Cp := C ∩ {v : D | 0 ≤ v.val.2}
    have hCm : IsClosed Cm := hC.inter (isClosed_le (by fun_prop) continuous_const)
    have hCp : IsClosed Cp := hC.inter (isClosed_le continuous_const (by fun_prop))
    have hpre : q ⁻¹' (square '' C) = cap 1 '' Cm ∪ cap 0 '' Cp := by
      ext z
      constructor
      · rintro ⟨u,hCu,he⟩
        dsimp [square] at he
        split_ifs at he with hy
        · rcases hCapFiber1 u z he with hec | ⟨hy0,hec⟩
          · exact Or.inl ⟨u,⟨hCu,hy⟩,hec.symm⟩
          · exact Or.inr ⟨u,⟨hCu,by change 0 ≤ u.val.2; rw [hy0]⟩,hec.symm⟩
        · rcases hCapFiber0 u z he with hec | ⟨hy0,hec⟩
          · exact Or.inr ⟨u,⟨hCu,(not_le.mp hy).le⟩,hec.symm⟩
          · exact Or.inl ⟨u,⟨hCu,by change u.val.2 ≤ 0; rw [hy0]⟩,hec.symm⟩
      · rintro (⟨u,⟨hCu,hy⟩,rfl⟩ | ⟨u,⟨hCu,hy⟩,rfl⟩)
        · change u.val.2 ≤ 0 at hy
          exact ⟨u,hCu,by simp only [square,if_pos hy]⟩
        · change 0 ≤ u.val.2 at hy
          refine ⟨u,hCu,?_⟩
          by_cases hu : u.val.2 ≤ 0
          · simp only [square,if_pos hu]
            exact hseam u (le_antisymm hu hy)
          · simp only [square,if_neg hu]
    rw [← (isQuotientMap_quot_mk (r := NonOrientableRel p n)).isClosed_preimage,hpre]
    exact (hCm.isCompact.image (hcap 1)).isClosed.union
      (hCp.isCompact.image (hcap 0)).isClosed
  have hSquareEmbedding : IsEmbedding square :=
    (IsClosedEmbedding.of_continuous_injective_isClosedMap
      hSquareContinuous hSquareInjective hSquareClosedMap).isEmbedding
  let a (w : CurveComplex.BandWidth) : Complex.ClosedUnitDisc :=
    cap 1 (CurveComplex.squarePort ε hε 2 w)
  let b (w : CurveComplex.BandWidth) : Complex.ClosedUnitDisc :=
    cap 0 (CurveComplex.squarePort ε hε 0 (CurveComplex.flipBandWidth true w))
  have haContinuous : Continuous a := by
    apply (hcap 1).comp
    apply Continuous.subtype_mk
    have hc := CurveComplex.crossingEndRectangle_continuous ε (2 : Fin 4)
    exact hc.comp (by fun_prop)
  have hbContinuous : Continuous b := by
    apply (hcap 0).comp
    apply Continuous.subtype_mk
    have hc := CurveComplex.crossingEndRectangle_continuous ε (0 : Fin 4)
    apply hc.comp
    apply Continuous.prodMk _ continuous_const
    change Continuous (fun w : CurveComplex.BandWidth =>
      (⟨-(w:ℝ), by constructor <;> linarith [w.property.1,w.property.2]⟩ : CurveComplex.BandWidth))
    fun_prop
  have hnorma (w : CurveComplex.BandWidth) : ‖(a w : ℂ)‖ = 3/4 := by
    norm_num [a,cap,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,ε,norm_mul]
  have hnormb (w : CurveComplex.BandWidth) : ‖(b w : ℂ)‖ = 3/4 := by
    norm_num [b,cap,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,ε,norm_mul]
  let rot : ℂ := (Circle.exp (-(2*Real.pi/L)) : ℂ)
  let phi (w : CurveComplex.BandWidth) : ℝ := 2*Real.pi*((1/2)+(ε/4)*(w:ℝ))/L
  have hRotA (w : CurveComplex.BandWidth) :
      rot * (a w : ℂ) = (3/4 : ℂ) * (Circle.exp (phi w) : ℂ) := by
    simp [a,cap,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,ε,
      Real.fourierChar_apply', rot]
    rw [mul_left_comm, ← Complex.exp_add]
    norm_num
    congr 2
    simp [phi, ε]
    ring
  have hRotB (w : CurveComplex.BandWidth) :
      rot * (b w : ℂ) = (3/4 : ℂ) * (Circle.exp (-phi w) : ℂ) := by
    simp [b,cap,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,ε,
      Real.fourierChar_apply', rot,CurveComplex.flipBandWidth]
    rw [mul_left_comm, ← Complex.exp_add, ← Complex.exp_neg]
    norm_num
    congr 2
    simp [phi, ε]
    ring
  have hPhi (w : CurveComplex.BandWidth) : 0 < phi w ∧ phi w < Real.pi := by
    have hw : -1 ≤ (w:ℝ) ∧ (w:ℝ) ≤ 1 := w.property
    have hbase : 0 < 1/2+(ε/4)*(w:ℝ) ∧ 1/2+(ε/4)*(w:ℝ) < 1 := by
      dsimp [ε]
      constructor <;> linarith
    constructor
    · dsimp [phi]
      exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hbase.1) hLpos
    · dsimp [phi]
      apply (div_lt_iff₀ hLpos).mpr
      nlinarith [Real.pi_pos]
  let chord (v : unitInterval × CurveComplex.BandWidth) : Complex.ClosedUnitDisc :=
    ⟨((1-(v.1:ℝ) : ℝ) : ℂ) * (a v.2 : ℂ) + ((v.1:ℝ) : ℂ) * (b v.2 : ℂ), by
      rw [Metric.mem_closedBall,dist_zero_right]
      have hh := norm_add_le (((1-(v.1:ℝ) : ℝ) : ℂ) * (a v.2 : ℂ))
        (((v.1:ℝ) : ℂ) * (b v.2 : ℂ))
      have hma : ‖((1-(v.1:ℝ) : ℝ) : ℂ) * (a v.2 : ℂ)‖ = (1-(v.1:ℝ))*(3/4) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr v.1.property.2), hnorma]
      have hmb : ‖((v.1:ℝ) : ℂ) * (b v.2 : ℂ)‖ = (v.1:ℝ)*(3/4) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg v.1.property.1, hnormb]
      rw [hma,hmb] at hh
      nlinarith⟩
  have hRotChord (v : unitInterval × CurveComplex.BandWidth) :
      rot * (chord v : ℂ) =
        ((1-(v.1:ℝ) : ℝ) : ℂ) * ((3/4 : ℂ) * (Circle.exp (phi v.2) : ℂ)) +
        ((v.1:ℝ) : ℂ) * ((3/4 : ℂ) * (Circle.exp (-phi v.2) : ℂ)) := by
    change rot * (((1-(v.1:ℝ) : ℝ) : ℂ) * (a v.2 : ℂ) +
      ((v.1:ℝ) : ℂ) * (b v.2 : ℂ)) = _
    calc
      _ = ((1-(v.1:ℝ) : ℝ) : ℂ) * (rot * (a v.2 : ℂ)) +
          ((v.1:ℝ) : ℂ) * (rot * (b v.2 : ℂ)) := by ring
      _ = _ := by rw [hRotA, hRotB]
  have hChordRe (v : unitInterval × CurveComplex.BandWidth) :
      (rot * (chord v : ℂ)).re = (3/4)*Real.cos (phi v.2) := by
    rw [hRotChord]
    simp only [Circle.coe_exp, Complex.add_re, Complex.mul_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    norm_num [Real.cos_neg, Real.sin_neg]
    ring
  have hChordIm (v : unitInterval × CurveComplex.BandWidth) :
      (rot * (chord v : ℂ)).im = (3/4)*(1-2*(v.1:ℝ))*Real.sin (phi v.2) := by
    rw [hRotChord]
    simp only [Circle.coe_exp, Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    norm_num [Real.cos_neg, Real.sin_neg]
    ring
  have hChordNorm (v : unitInterval × CurveComplex.BandWidth) :
      ‖(chord v : ℂ)‖ ≤ 3/4 := by
    change ‖((1-(v.1:ℝ) : ℝ) : ℂ) * (a v.2 : ℂ) + ((v.1:ℝ) : ℂ) * (b v.2 : ℂ)‖ ≤ 3/4
    calc
      _ ≤ ‖((1-(v.1:ℝ) : ℝ) : ℂ) * (a v.2 : ℂ)‖ +
          ‖((v.1:ℝ) : ℂ) * (b v.2 : ℂ)‖ := norm_add_le _ _
      _ = (1-(v.1:ℝ))*(3/4) + (v.1:ℝ)*(3/4) := by
        congr 1
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr v.1.property.2), hnorma]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg v.1.property.1, hnormb]
      _ = 3/4 := by ring
  have hCapNorm (k : ℝ) (v : D) : 3/4 ≤ ‖(cap k v : ℂ)‖ := by
    have hy := (coords v).2
    have hr : 0 ≤ 1-|v.val.2| := by dsimp [ε] at hy; linarith
    change 3/4 ≤ ‖((1-|v.val.2| : ℝ) : ℂ) *
      (Real.fourierChar ((k+1/2+v.val.1)/L) : ℂ)‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
      mul_one, abs_of_nonneg hr]
    dsimp [ε] at hy
    linarith
  have hChordInterior (v : unitInterval × CurveComplex.BandWidth) :
      ‖(chord v : ℂ)‖ < 1 := lt_of_le_of_lt (hChordNorm v) (by norm_num)
  have hChordContinuous : Continuous chord := by
    apply Continuous.subtype_mk
    exact ((by fun_prop : Continuous (fun v : unitInterval × CurveComplex.BandWidth =>
      ((1-(v.1:ℝ) : ℝ) : ℂ))).mul (continuous_subtype_val.comp (haContinuous.comp continuous_snd))).add
      ((by fun_prop : Continuous (fun v : unitInterval × CurveComplex.BandWidth =>
        ((v.1:ℝ) : ℂ))).mul (continuous_subtype_val.comp (hbContinuous.comp continuous_snd)))
  have hChordInjective : Function.Injective chord := by
    intro v w he
    have hre := congrArg (fun z : Complex.ClosedUnitDisc => (rot*(z:ℂ)).re) he
    rw [hChordRe,hChordRe] at hre
    have hc : Real.cos (phi v.2) = Real.cos (phi w.2) := by linarith
    have hephi : phi v.2 = phi w.2 := Real.strictAntiOn_cos.injOn
      ⟨(hPhi v.2).1.le,(hPhi v.2).2.le⟩
      ⟨(hPhi w.2).1.le,(hPhi w.2).2.le⟩ hc
    have hewidth : v.2 = w.2 := by
      apply Subtype.ext
      have hh := congrArg (fun x : ℝ => x*L) hephi
      dsimp [phi] at hh
      rw [div_mul_cancel₀ _ hLpos.ne', div_mul_cancel₀ _ hLpos.ne'] at hh
      dsimp [ε] at hh
      nlinarith [Real.pi_pos]
    have him := congrArg (fun z : Complex.ClosedUnitDisc => (rot*(z:ℂ)).im) he
    rw [hChordIm,hChordIm,hewidth] at him
    have hs : 0 < Real.sin (phi w.2) :=
      Real.sin_pos_of_pos_of_lt_pi (hPhi w.2).1 (hPhi w.2).2
    apply Prod.ext
    · apply Subtype.ext
      nlinarith
    · exact hewidth
  have hChordEmbedding : IsEmbedding chord :=
    (hChordContinuous.isClosedEmbedding hChordInjective).isEmbedding
  let chordInto : unitInterval × CurveComplex.BandWidth → q ⁻¹' W :=
    fun v => ⟨chord v, by rw [hpreW]; exact hChordInterior v⟩
  have hChordIntoContinuous : Continuous chordInto :=
    hChordContinuous.subtype_mk _
  have hChordIntoEmbedding : IsEmbedding chordInto :=
    IsEmbedding.of_comp hChordIntoContinuous continuous_subtype_val hChordEmbedding
  have hBandEmbedding : IsEmbedding (q ∘ chord) := by
    exact (IsEmbedding.subtypeVal.comp (hRestrictEmbedding.comp hChordIntoEmbedding))
  let band : unitInterval × CurveComplex.BandWidth → Q := q ∘ chord
  have hBandContinuous : Continuous band := hq.comp hChordContinuous
  have hABDistinct (w : CurveComplex.BandWidth) : (a w : ℂ) ≠ (b w : ℂ) := by
    intro he
    have hc : chord (0,w) = chord (1,w) := by
      apply Subtype.ext
      simpa [chord] using he
    have hv := congrArg (fun v : unitInterval × CurveComplex.BandWidth => (v.1:ℝ))
      (hChordInjective hc)
    norm_num at hv
  have hChordStrict (v : unitInterval × CurveComplex.BandWidth)
      (hs : 0 < (v.1:ℝ)) (ht : (v.1:ℝ) < 1) : ‖(chord v : ℂ)‖ < 3/4 := by
    have hh := norm_combo_lt_of_ne (hnorma v.2).le (hnormb v.2).le
      (hABDistinct v.2) (sub_pos.mpr ht) hs (by ring : (1-(v.1:ℝ))+(v.1:ℝ)=1)
    simpa only [chord, Complex.real_smul] using hh
  have hbottom (w : CurveComplex.BandWidth) : band (0,w) =
      square (CurveComplex.squarePort ε hε 2 w) := by
    simp [band,chord,square,a,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,hε.le]
  have htop (w : CurveComplex.BandWidth) : band (1,w) =
      square (CurveComplex.squarePort ε hε 0 (CurveComplex.flipBandWidth true w)) := by
    simp [band,chord,square,b,CurveComplex.squarePort,CurveComplex.crossingEndRectangle,
      not_le.mpr hε]
  refine ⟨ε,hε,square,band,?_,?_,hbottom,htop,?_⟩
  · exact hSquareEmbedding
  · exact hBandEmbedding
  · ext z
    constructor
    · rintro ⟨⟨v,rfl⟩,⟨u,heu⟩⟩
      have hlow : 3/4 ≤ ‖(chord v : ℂ)‖ := by
        dsimp [square] at heu
        split_ifs at heu with hy
        · have he := hQuotInterior (hChordInterior v) heu.symm
          rw [he]
          exact hCapNorm 1 u
        · have he := hQuotInterior (hChordInterior v) heu.symm
          rw [he]
          exact hCapNorm 0 u
      have hsEnds : v.1 = 0 ∨ v.1 = 1 := by
        by_cases hs : v.1 = 0
        · exact Or.inl hs
        · right
          apply Subtype.ext
          have hspos : 0 < (v.1:ℝ) := lt_of_le_of_ne v.1.property.1
            (fun he => hs (Subtype.ext he.symm))
          by_contra ht
          have hlt : (v.1:ℝ) < 1 := lt_of_le_of_ne v.1.property.2 ht
          exact (not_lt_of_ge hlow) (hChordStrict v hspos hlt)
      rcases hsEnds with hs | hs
      · left
        exact ⟨v.2, (hbottom v.2).symm.trans (congrArg band (Prod.ext hs.symm rfl))⟩
      · right
        exact ⟨CurveComplex.flipBandWidth true v.2,
          (htop v.2).symm.trans (congrArg band (Prod.ext hs.symm rfl))⟩
    · rintro (⟨w,rfl⟩ | ⟨w,rfl⟩)
      · exact ⟨⟨(0,w),hbottom w⟩,⟨CurveComplex.squarePort ε hε 2 w,rfl⟩⟩
      · have hflip : CurveComplex.flipBandWidth true
            (CurveComplex.flipBandWidth true w) = w := by
          apply Subtype.ext
          simp [CurveComplex.flipBandWidth]
        exact ⟨⟨(1,CurveComplex.flipBandWidth true w),by rw [htop,hflip]⟩,
          ⟨CurveComplex.squarePort ε hε 0 w,rfl⟩⟩


end CurveComplex.Hyperbolic
