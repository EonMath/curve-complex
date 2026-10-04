import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology
open CurveComplex.BranchedDoubleCover

noncomputable def affineAngle (u v : ℝ) : C(Interval, ℝ) :=
  ⟨fun t => (1 - t.val) * u + t.val * v, by fun_prop⟩

lemma affineAngle_injective {u v : ℝ} (huv : u ≠ v) :
    Function.Injective (affineAngle u v) := by
  intro s t h
  apply Subtype.ext
  change (1 - s.val) * u + s.val * v = (1 - t.val) * u + t.val * v at h
  have he : (s.val - t.val) * (v - u) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr huv.symm))

lemma affineCircle_finite_fiber {u v : ℝ} (huv : u ≠ v) (z : Circle) :
    {t : Interval | Circle.exp (affineAngle u v t) = z}.Finite := by
  have hd : IsDiscrete (Circle.exp ⁻¹' {z}) := by
    exact isDiscrete_iff_discreteTopology.mpr
      (Circle.isCoveringMap_exp z).discreteTopology_fiber
  have hp := hd.preimage (affineAngle u v).continuous.continuousOn
    (affineAngle_injective huv)
  exact (isClosed_singleton.preimage
    (Circle.exp.continuous.comp (affineAngle u v).continuous)).isCompact.finite hp

lemma affineBoundary_finite_contacts {Z : Type*} [TopologicalSpace Z]
    {B : Set Z} (β : Circle ≃ₜ B) {u v : ℝ} (huv : u ≠ v)
    (ℓ : C(Interval, Z))
    (hℓ : ∀ t, ℓ t = (β (Circle.exp (affineAngle u v t))).val)
    (P : Set Z) (hP : P.Finite) : {t : Interval | ℓ t ∈ P}.Finite := by
  classical
  have hf (z : Z) : {t : Interval | ℓ t = z}.Finite := by
    by_cases hz : ∃ t, ℓ t = z
    · obtain ⟨t, ht⟩ := hz
      refine (affineCircle_finite_fiber huv (Circle.exp (affineAngle u v t))).subset ?_
      intro s hs
      apply β.injective
      apply Subtype.ext
      rw [← hℓ s, ← hℓ t]
      exact hs.trans ht.symm
    · simpa only [Set.ofPred_false] using (Set.finite_empty : (∅ : Set Interval).Finite)
        |>.subset (by intro t ht; exact False.elim (hz ⟨t, ht⟩))
  convert hP.biUnion (fun z _ => hf z) using 1
  ext t
  simp

lemma affineAngle_intermediate {u v : ℝ} {l r : Interval} (hlr : l ≤ r)
    {w : ℝ} (hw : w ∈ Icc (min (affineAngle u v l) (affineAngle u v r))
      (max (affineAngle u v l) (affineAngle u v r))) :
    ∃ t : Interval, l ≤ t ∧ t ≤ r ∧ affineAngle u v t = w := by
  let f : ℝ → ℝ := fun t => (1 - t) * u + t * v
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hreal : l.val ≤ r.val := hlr
  have he : ∃ t ∈ Icc l.val r.val, f t = w := by
    rcases le_total (affineAngle u v l) (affineAngle u v r) with h | h
    · exact intermediate_value_Icc hreal hfc.continuousOn
        (by rw [min_eq_left h, max_eq_right h] at hw; exact hw)
    · exact intermediate_value_Icc' hreal hfc.continuousOn
        (by rw [min_eq_right h, max_eq_left h] at hw; exact hw)
  obtain ⟨t, ht, he⟩ := he
  exact ⟨⟨t, l.property.1.trans ht.1, ht.2.trans r.property.2⟩, ht.1, ht.2, he⟩

lemma affineAngle_segment_bounds (u v : ℝ) {l r : Interval} (hlr : l ≤ r)
    (t : Interval) : affineAngle u v (intervalAffine l r t) ∈
      Icc (min (affineAngle u v l) (affineAngle u v r))
        (max (affineAngle u v l) (affineAngle u v r)) := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  have he : affineAngle u v (intervalAffine l r t) =
      (1 - t.val) * affineAngle u v l + t.val * affineAngle u v r := by
    simp only [affineAngle, ContinuousMap.coe_mk, intervalAffine]
    ring
  rw [he]
  rcases le_total (affineAngle u v l) (affineAngle u v r) with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor <;> nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h),
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h)]
  · rw [min_eq_right h, max_eq_left h]
    constructor <;> nlinarith [mul_nonneg ht0 (sub_nonneg.mpr h),
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h)]

lemma affineBoundary_segment_embedding {Z : Type*} [TopologicalSpace Z]
    {B : Set Z} (β : Circle ≃ₜ B) {u v : ℝ} (huv : u ≠ v)
    (ℓ : C(Interval, Z))
    (hℓ : ∀ t, ℓ t = (β (Circle.exp (affineAngle u v t))).val)
    {l r : Interval} (hlr : l < r)
    (hspan : max (affineAngle u v l) (affineAngle u v r) -
      min (affineAngle u v l) (affineAngle u v r) < 2 * Real.pi) :
    IsEmbedding (fun t : Interval => ℓ (intervalAffine l r t)) := by
  have hc : Continuous (fun t : Interval => Circle.exp (affineAngle u v (intervalAffine l r t))) := by
    apply Circle.exp.continuous.comp
    apply (affineAngle u v).continuous.comp
    apply Continuous.subtype_mk
    fun_prop
  have hi : Function.Injective (fun t : Interval => Circle.exp (affineAngle u v (intervalAffine l r t))) := by
    intro s t he
    have hq := Circle.exp_injOn_Icc hspan
      (affineAngle_segment_bounds u v hlr.le s)
      (affineAngle_segment_bounds u v hlr.le t) he
    have hp := congrArg Subtype.val (affineAngle_injective huv hq)
    apply Subtype.ext
    change (1 - s.val) * l.val + s.val * r.val =
      (1 - t.val) * l.val + t.val * r.val at hp
    have hr : l.val < r.val := hlr
    nlinarith
  have he := (Topology.IsEmbedding.subtypeVal.comp β.isEmbedding).comp
    (hc.isClosedEmbedding hi).isEmbedding
  simpa only [Function.comp_def, ← hℓ] using he

lemma affineBoundary_one_marker {Z : Type*} [TopologicalSpace Z]
    {B : Set Z} (β : Circle ≃ₜ B) {u v : ℝ} (huv : u ≠ v)
    (ℓ : C(Interval, Z))
    (hℓ : ∀ t, ℓ t = (β (Circle.exp (affineAngle u v t))).val)
    {l r : Interval} (hlr : l < r)
    (havoid : ∀ t : Interval, l < t → t ≤ r → ℓ t ≠ ℓ l) :
    IsEmbedding (fun t : Interval => ℓ (intervalAffine l r t)) := by
  apply affineBoundary_segment_embedding β huv ℓ hℓ hlr
  have hp : 0 < 2 * Real.pi := by positivity
  by_contra hspan
  rcases le_total (affineAngle u v l) (affineAngle u v r) with h | h
  · rw [max_eq_right h, min_eq_left h] at hspan
    obtain ⟨t, ht0, ht1, he⟩ := affineAngle_intermediate hlr.le
      (w := affineAngle u v l + 2 * Real.pi) (by
        rw [min_eq_left h, max_eq_right h]; constructor <;> linarith)
    have hlt : l < t := lt_of_le_of_ne ht0 (by
      intro hlt; subst t; linarith)
    apply havoid t hlt ht1
    rw [hℓ t, hℓ l, he, Circle.exp_add_two_pi]
  · rw [max_eq_left h, min_eq_right h] at hspan
    obtain ⟨t, ht0, ht1, he⟩ := affineAngle_intermediate hlr.le
      (w := affineAngle u v l - 2 * Real.pi) (by
        rw [min_eq_right h, max_eq_left h]; constructor <;> linarith)
    have hlt : l < t := lt_of_le_of_ne ht0 (by
      intro hlt; subst t; linarith)
    apply havoid t hlt ht1
    rw [hℓ t, hℓ l, he, Circle.exp_sub_two_pi]


lemma affineBoundary_two_marker {Z : Type*} [TopologicalSpace Z]
    {B : Set Z} (β : Circle ≃ₜ B) {u v : ℝ} (huv : u ≠ v)
    (ℓ : C(Interval, Z))
    (hℓ : ∀ t, ℓ t = (β (Circle.exp (affineAngle u v t))).val)
    (x₀ x₁ : Z) (hx₀ : x₀ ∈ B) (hx₁ : x₁ ∈ B) (hx : x₀ ≠ x₁)
    {l r : Interval} (hlr : l < r)
    (hl : ℓ l ∈ ({x₀, x₁} : Set Z)) (hr : ℓ r ∈ ({x₀, x₁} : Set Z))
    (havoid : ∀ t : Interval, l < t → t < r → ℓ t ∉ ({x₀, x₁} : Set Z)) :
    IsEmbedding (fun t : Interval => ℓ (intervalAffine l r t)) ∧
      ({ℓ l, ℓ r} : Set Z) = {x₀, x₁} := by
  have hother : ∃ z : B, z.val ∈ ({x₀, x₁} : Set Z) ∧ z.val ≠ ℓ l := by
    rcases Set.mem_insert_iff.mp hl with h | h
    · exact ⟨⟨x₁, hx₁⟩, by simp, by rw [h]; exact hx.symm⟩
    · have h : ℓ l = x₁ := Set.mem_singleton_iff.mp h
      exact ⟨⟨x₀, hx₀⟩, by simp, by rw [h]; exact hx⟩
  obtain ⟨z, hzm, hzne⟩ := hother
  have hcz : β.symm z ≠ Circle.exp (affineAngle u v l) := by
    intro he
    apply hzne
    rw [hℓ l, ← he, β.apply_symm_apply]
  have hp : 0 < 2 * Real.pi := by positivity
  have hspan : max (affineAngle u v l) (affineAngle u v r) -
      min (affineAngle u v l) (affineAngle u v r) < 2 * Real.pi := by
    by_contra hspan
    rcases le_total (affineAngle u v l) (affineAngle u v r) with h | h
    · rw [max_eq_right h, min_eq_left h] at hspan
      obtain ⟨w, hw, hew⟩ := Circle.periodic_exp.exists_mem_Ico hp
        (β.symm z).val.arg (affineAngle u v l)
      have hez : Circle.exp w = β.symm z := hew.symm.trans (Circle.exp_arg _)
      have hwl : affineAngle u v l < w := lt_of_le_of_ne hw.1 (by
        intro he; apply hcz; rw [← hez, he])
      have hwr : w < affineAngle u v r := by linarith [hw.2]
      obtain ⟨t, ht0, ht1, het⟩ := affineAngle_intermediate hlr.le
        (w := w) (by rw [min_eq_left h, max_eq_right h]; exact ⟨hwl.le, hwr.le⟩)
      have hlt : l < t := lt_of_le_of_ne ht0 (by intro he; subst t; linarith)
      have htr : t < r := lt_of_le_of_ne ht1 (by intro he; subst t; linarith)
      apply havoid t hlt htr
      rw [hℓ t, het, hez, β.apply_symm_apply]
      exact hzm
    · rw [max_eq_left h, min_eq_right h] at hspan
      obtain ⟨w, hw, hew⟩ := Circle.periodic_exp.exists_mem_Ioc hp
        (β.symm z).val.arg (affineAngle u v l - 2 * Real.pi)
      have hez : Circle.exp w = β.symm z := hew.symm.trans (Circle.exp_arg _)
      have hwr : w < affineAngle u v l := lt_of_le_of_ne (by linarith [hw.2]) (by
        intro he; apply hcz; rw [← hez, he])
      have hwl : affineAngle u v r < w := by linarith [hw.1]
      obtain ⟨t, ht0, ht1, het⟩ := affineAngle_intermediate hlr.le
        (w := w) (by rw [min_eq_right h, max_eq_left h]; exact ⟨hwl.le, hwr.le⟩)
      have hlt : l < t := lt_of_le_of_ne ht0 (by intro he; subst t; linarith)
      have htr : t < r := lt_of_le_of_ne ht1 (by intro he; subst t; linarith)
      apply havoid t hlt htr
      rw [hℓ t, het, hez, β.apply_symm_apply]
      exact hzm
  have hemb := affineBoundary_segment_embedding β huv ℓ hℓ hlr hspan
  refine ⟨hemb, ?_⟩
  have hne : ℓ l ≠ ℓ r := by
    intro he
    have he' : (fun t : Interval => ℓ (intervalAffine l r t)) 0 =
        (fun t : Interval => ℓ (intervalAffine l r t)) 1 := by simpa [intervalAffine] using he
    exact zero_ne_one (hemb.injective he')
  rcases Set.mem_insert_iff.mp hl with hl | hl <;>
    rcases Set.mem_insert_iff.mp hr with hr | hr
  · exact False.elim (hne (hl.trans hr.symm))
  · have hr := Set.mem_singleton_iff.mp hr
    simp [hl, hr]
  · have hl := Set.mem_singleton_iff.mp hl
    simp [hl, hr, Set.pair_comm]
  · exact False.elim (hne ((Set.mem_singleton_iff.mp hl).trans
      (Set.mem_singleton_iff.mp hr).symm))

end CoherentEndpointMotion.FreeBoundaryContactRepair
