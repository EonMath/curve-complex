import CurveComplexGenusTwo.Topology.FareyStageCollapse
import CurveComplexGenusTwo.Foundations.RealizationCW

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

noncomputable def fareyFiniteSimplexInclude
    (σ τ : Finset FareySlope) (hστ : σ ⊆ τ) :
    FiniteSimplex σ → FiniteSimplex τ := by
  classical
  intro x
  refine ⟨fun v => if hv : (v : FareySlope) ∈ σ then x.val ⟨v, hv⟩ else 0, ?_, ?_⟩
  · intro v
    by_cases hv : (v : FareySlope) ∈ σ
    · simpa [hv] using x.property.1 ⟨v, hv⟩
    · simp [hv]
  · have hs :
        (∑ v ∈ τ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0) =
        ∑ v ∈ σ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0 := by
      symm
      apply Finset.sum_subset hστ
      intro v hvτ hvσ
      simp [hvσ]
    have hsumσ :
        (∑ v ∈ σ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0) = 1 := by
      calc
        _ = ∑ v ∈ σ.attach,
              (if hv : (v : FareySlope) ∈ σ then x.val ⟨(v : FareySlope), hv⟩ else 0) := by
                rw [← Finset.sum_attach]
        _ = ∑ v : σ, x.val v := by simp [Finset.univ_eq_attach]
        _ = 1 := x.property.2
    have hsumτ := hs.trans hsumσ
    change (∑ v : τ, if hv : (v : FareySlope) ∈ σ then x.val ⟨(v : FareySlope), hv⟩ else 0) = 1
    calc
      _ = ∑ v ∈ τ.attach,
            (if hv : (v : FareySlope) ∈ σ then x.val ⟨(v : FareySlope), hv⟩ else 0) := by
              simp [Finset.univ_eq_attach]
      _ = ∑ v ∈ τ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0 := by
            exact Finset.sum_attach τ
              (fun v : FareySlope => if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0)
      _ = 1 := hsumτ

theorem fareyFiniteSimplexInclude_faceInclusion
    (σ τ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (hτ : τ ∈ fareyComplex.faces) (hστ : σ ⊆ τ)
    (x : FiniteSimplex σ) :
    faceInclusion fareyComplex τ hτ (fareyFiniteSimplexInclude σ τ hστ x) =
      faceInclusion fareyComplex σ hσ x := by
  apply RealizationPoint.ext
  funext v
  by_cases hvσ : v ∈ σ
  · have hvτ : v ∈ τ := hστ hvσ
    simp [faceInclusion, fareyFiniteSimplexInclude, hvσ, hvτ]
  · simp [faceInclusion, fareyFiniteSimplexInclude, hvσ]

theorem fareyFiniteSimplexInclude_continuous
    (σ τ : Finset FareySlope) (hστ : σ ⊆ τ) :
    Continuous (fareyFiniteSimplexInclude σ τ hστ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  by_cases hv : (v : FareySlope) ∈ σ
  · convert ((continuous_apply (⟨v, hv⟩ : σ)).comp continuous_subtype_val) using 1
    funext a
    simp only [dite_eq_left hv, Function.comp_apply]
  · simpa [fareyFiniteSimplexInclude, hv] using
      (continuous_const : Continuous (fun _ : FiniteSimplex σ => (0 : ℝ)))

-- The facewise affine formula moves the mass of p equally to its two parents.
noncomputable def fareyParentAffine
    (σ : Finset FareySlope) (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (t : ConeTime) (x : FiniteSimplex σ) : FiniteSimplex σ := by
  let f : σ → ℝ := fun w =>
    (if (w : FareySlope) = p then (1 - (t : ℝ)) * x.val w else x.val w) +
      (if (w : FareySlope) = l then (t : ℝ) * x.val ⟨p, hp⟩ / 2 else 0) +
      (if (w : FareySlope) = r then (t : ℝ) * x.val ⟨p, hp⟩ / 2 else 0)
  refine ⟨f, ?_, ?_⟩
  · intro w
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hxw : 0 ≤ x.val w := x.property.1 w
    have hxp : 0 ≤ x.val ⟨p, hp⟩ := x.property.1 _
    by_cases hwp : (w : FareySlope) = p <;>
      by_cases hwl : (w : FareySlope) = l <;>
      by_cases hwr : (w : FareySlope) = r <;>
      simp [f, hwp, hwl, hwr] <;> positivity
  · let hp' : σ := ⟨p, hp⟩
    let hl' : σ := ⟨l, hl⟩
    let hr' : σ := ⟨r, hr⟩
    have hsumP : (∑ w : σ, if (w : FareySlope) = p then
        (t : ℝ) * x.val hp' else 0) = (t : ℝ) * x.val hp' := by
      rw [Finset.sum_eq_single hp']
      · simp [hp']
      · intro b hb hbp
        have hbne : (b : FareySlope) ≠ p := by
          intro h
          exact hbp (Subtype.ext h)
        simp [hbne]
      · intro h
        exact False.elim (h (by simp))
    have hsumL : (∑ w : σ, if (w : FareySlope) = l then
        (t : ℝ) * x.val hp' / 2 else 0) = (t : ℝ) * x.val hp' / 2 := by
      rw [Finset.sum_eq_single hl']
      · simp [hl']
      · intro b hb hbl
        have hbne : (b : FareySlope) ≠ l := by
          intro h
          exact hbl (Subtype.ext h)
        simp [hbne]
      · intro h
        exact False.elim (h (by simp))
    have hsumR : (∑ w : σ, if (w : FareySlope) = r then
        (t : ℝ) * x.val hp' / 2 else 0) = (t : ℝ) * x.val hp' / 2 := by
      rw [Finset.sum_eq_single hr']
      · simp [hr']
      · intro b hb hbr
        have hbne : (b : FareySlope) ≠ r := by
          intro h
          exact hbr (Subtype.ext h)
        simp [hbne]
      · intro h
        exact False.elim (h (by simp))
    have hbase : (∑ w : σ, if (w : FareySlope) = p then
        (1 - (t : ℝ)) * x.val w else x.val w) =
        1 - (t : ℝ) * x.val hp' := by
      have hrewrite (w : σ) :
          (if (w : FareySlope) = p then (1 - (t : ℝ)) * x.val w
            else x.val w) = x.val w -
              (if (w : FareySlope) = p then (t : ℝ) * x.val hp' else 0) := by
        by_cases hwp : (w : FareySlope) = p
        · subst p
          simp
          ring
        · simp [hwp]
      simp_rw [hrewrite]
      rw [Finset.sum_sub_distrib, x.property.2, hsumP]
    change ∑ w : σ, _ = 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hbase, hsumL, hsumR]
    ring

theorem fareyParentAffine_continuous
    (σ : Finset FareySlope) (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r) :
    Continuous (fun q : ConeTime × FiniteSimplex σ =>
      fareyParentAffine σ p l r hp hl hr hpl hpr hlr q.1 q.2) := by
  have ht : Continuous (fun q : ConeTime × FiniteSimplex σ => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx (w : σ) : Continuous (fun q : ConeTime × FiniteSimplex σ => q.2.val w) :=
    (continuous_apply w).comp (continuous_subtype_val.comp continuous_snd)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  have hbase : Continuous (fun q : ConeTime × FiniteSimplex σ =>
      if (w : FareySlope) = p then (1 - (q.1 : ℝ)) * q.2.val w else q.2.val w) := by
    by_cases hwp : (w : FareySlope) = p
    · simp only [hwp, ↓reduceIte]
      convert (continuous_const.sub ht).mul (hx w) using 1
    · simpa [hwp] using hx w
  have hleft : Continuous (fun q : ConeTime × FiniteSimplex σ =>
      if (w : FareySlope) = l then (q.1 : ℝ) * q.2.val ⟨p, hp⟩ / 2 else 0) := by
    by_cases hwl : (w : FareySlope) = l
    · simpa [hwl] using (ht.mul (hx ⟨p, hp⟩)).div_const 2
    · simpa [hwl] using (continuous_const : Continuous fun _ : ConeTime × FiniteSimplex σ => (0 : ℝ))
  have hright : Continuous (fun q : ConeTime × FiniteSimplex σ =>
      if (w : FareySlope) = r then (q.1 : ℝ) * q.2.val ⟨p, hp⟩ / 2 else 0) := by
    by_cases hwr : (w : FareySlope) = r
    · simpa [hwr] using (ht.mul (hx ⟨p, hp⟩)).div_const 2
    · simpa [hwr] using (continuous_const : Continuous fun _ : ConeTime × FiniteSimplex σ => (0 : ℝ))
  change Continuous (fun q : ConeTime × FiniteSimplex σ =>
    ((if (w : FareySlope) = p then (1 - (q.1 : ℝ)) * q.2.val w else q.2.val w) +
      (if (w : FareySlope) = l then (q.1 : ℝ) * q.2.val ⟨p, hp⟩ / 2 else 0)) +
      (if (w : FareySlope) = r then (q.1 : ℝ) * q.2.val ⟨p, hp⟩ / 2 else 0))
  convert (hbase.add hleft).add hright using 1

theorem fareyParentAffine_zero
    (σ : Finset FareySlope) (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (x : FiniteSimplex σ) :
    fareyParentAffine σ p l r hp hl hr hpl hpr hlr ⟨0, by norm_num⟩ x = x := by
  apply Subtype.ext
  funext w
  by_cases hwp : (w : FareySlope) = p <;>
    by_cases hwl : (w : FareySlope) = l <;>
    by_cases hwr : (w : FareySlope) = r <;>
    simp [fareyParentAffine, hwp, hwl, hwr]

theorem continuous_fareyParentAffine_face
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r) :
    Continuous (fun q : ConeTime × FiniteSimplex σ =>
      faceInclusion fareyComplex σ hσ
        (fareyParentAffine σ p l r hp hl hr hpl hpr hlr q.1 q.2)) := by
  exact (continuous_faceInclusion fareyComplex σ hσ).comp
    (fareyParentAffine_continuous σ p l r hp hl hr hpl hpr hlr)

theorem fareyParentAffine_weight
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (t : ConeTime) (x : FiniteSimplex σ) (w : FareySlope) :
    (faceInclusion fareyComplex σ hσ
      (fareyParentAffine σ p l r hp hl hr hpl hpr hlr t x)).weight w =
      (if w = p then (1 - (t : ℝ)) * (faceInclusion fareyComplex σ hσ x).weight w
        else (faceInclusion fareyComplex σ hσ x).weight w) +
      (if w = l then (t : ℝ) * (faceInclusion fareyComplex σ hσ x).weight p / 2
        else 0) +
      (if w = r then (t : ℝ) * (faceInclusion fareyComplex σ hσ x).weight p / 2
        else 0) := by
  by_cases hw : w ∈ σ
  · simp [faceInclusion, fareyParentAffine, hw, hp]
  · have hwp : w ≠ p := by intro h; exact hw (h ▸ hp)
    have hwl : w ≠ l := by intro h; exact hw (h ▸ hl)
    have hwr : w ≠ r := by intro h; exact hw (h ▸ hr)
    simp [faceInclusion, hw, hwp, hwl, hwr]

theorem fareyParentAffine_compatible
    (σ τ : Finset FareySlope)
    (hσ : σ ∈ fareyComplex.faces) (hτ : τ ∈ fareyComplex.faces)
    (p l r : FareySlope)
    (hpσ : p ∈ σ) (hlσ : l ∈ σ) (hrσ : r ∈ σ)
    (hpτ : p ∈ τ) (hlτ : l ∈ τ) (hrτ : r ∈ τ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (t : ConeTime) (x : FiniteSimplex σ) (y : FiniteSimplex τ)
    (hxy : faceInclusion fareyComplex σ hσ x =
      faceInclusion fareyComplex τ hτ y) :
    faceInclusion fareyComplex σ hσ
        (fareyParentAffine σ p l r hpσ hlσ hrσ hpl hpr hlr t x) =
      faceInclusion fareyComplex τ hτ
        (fareyParentAffine τ p l r hpτ hlτ hrτ hpl hpr hlr t y) := by
  apply RealizationPoint.ext
  funext w
  rw [fareyParentAffine_weight, fareyParentAffine_weight, hxy]

theorem fareyParentAffine_top_zero
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (x : FiniteSimplex σ) :
    (faceInclusion fareyComplex σ hσ
      (fareyParentAffine σ p l r hp hl hr hpl hpr hlr ⟨1, by norm_num⟩ x)).weight p = 0 := by
  rw [fareyParentAffine_weight]
  simp [hpl, hpr]

theorem fareyParentAffine_fixes_zero_top_mass
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (p l r : FareySlope)
    (hp : p ∈ σ) (hl : l ∈ σ) (hr : r ∈ σ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (t : ConeTime) (x : FiniteSimplex σ)
    (hzero : x.val ⟨p, hp⟩ = 0) :
    faceInclusion fareyComplex σ hσ
        (fareyParentAffine σ p l r hp hl hr hpl hpr hlr t x) =
      faceInclusion fareyComplex σ hσ x := by
  apply RealizationPoint.ext
  funext w
  rw [fareyParentAffine_weight]
  by_cases hw : w = p
  · subst w
    simp [faceInclusion, hp, hzero]
  · by_cases hwl : w = l
    · subst w
      have hlp : l ≠ p := Ne.symm hpl
      simp [faceInclusion, hl, hlp, hzero]
    · by_cases hwr : w = r
      · subst w
        have hrp : r ≠ p := Ne.symm hpr
        simp [faceInclusion, hr, hrp, hzero]
      · simp [hw, hwl, hwr]

theorem fareyParentAffine_finiteSimplexInclude
    [DecidableEq FareySlope]
    (σ τ : Finset FareySlope) (hστ : σ ⊆ τ)
    (p l r : FareySlope)
    (hpσ : p ∈ σ) (hlσ : l ∈ σ) (hrσ : r ∈ σ)
    (hpτ : p ∈ τ) (hlτ : l ∈ τ) (hrτ : r ∈ τ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (t : ConeTime) (x : FiniteSimplex σ) :
    fareyFiniteSimplexInclude σ τ hστ
        (fareyParentAffine σ p l r hpσ hlσ hrσ hpl hpr hlr t x) =
      fareyParentAffine τ p l r hpτ hlτ hrτ hpl hpr hlr t
        (fareyFiniteSimplexInclude σ τ hστ x) := by
  apply Subtype.ext
  funext w
  by_cases hw : (w : FareySlope) ∈ σ
  · simp [fareyFiniteSimplexInclude, fareyParentAffine, hw, hpσ]
  · by_cases hwp : (w : FareySlope) = p
    · exact False.elim (hw (hwp ▸ hpσ))
    · by_cases hwl : (w : FareySlope) = l
      · exact False.elim (hw (hwl ▸ hlσ))
      · by_cases hwr : (w : FareySlope) = r
        · exact False.elim (hw (hwr ▸ hrσ))
        · simp [fareyFiniteSimplexInclude, fareyParentAffine, hw, hwp, hwl, hwr]

theorem fareyParentAffine_faceInclusionInclude
    [DecidableEq FareySlope]
    (σ τ : Finset FareySlope)
    (hσ : σ ∈ fareyComplex.faces) (hτ : τ ∈ fareyComplex.faces)
    (hστ : σ ⊆ τ)
    (p l r : FareySlope)
    (hpσ : p ∈ σ) (hlσ : l ∈ σ) (hrσ : r ∈ σ)
    (hpτ : p ∈ τ) (hlτ : l ∈ τ) (hrτ : r ∈ τ)
    (hpl : p ≠ l) (hpr : p ≠ r) (hlr : l ≠ r)
    (t : ConeTime) (x : FiniteSimplex σ) :
    faceInclusion fareyComplex τ hτ
        (fareyParentAffine τ p l r hpτ hlτ hrτ hpl hpr hlr t
        (fareyFiniteSimplexInclude σ τ hστ x)) =
      faceInclusion fareyComplex σ hσ
        (fareyParentAffine σ p l r hpσ hlσ hrσ hpl hpr hlr t x) := by
  rw [← fareyParentAffine_finiteSimplexInclude σ τ hστ p l r hpσ hlσ hrσ
    hpτ hlτ hrτ hpl hpr hlr t x]
  exact fareyFiniteSimplexInclude_faceInclusion σ τ hσ hτ hστ _

end CurveComplexGenusTwo.Topology
