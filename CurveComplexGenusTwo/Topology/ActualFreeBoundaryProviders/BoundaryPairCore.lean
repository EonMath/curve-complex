import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.AffineCircleCore

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology
universe u v

lemma circle_pair_real_lifts
    (q : Fin 2 → C(Interval, Circle)) (hne : ∀ t, q 0 t ≠ q 1 t) :
    ∃ θ : Fin 2 → C(Interval, ℝ),
      (∀ i t, Circle.exp (θ i t) = q i t) ∧
      (∀ t, 0 < θ 1 t - θ 0 t ∧ θ 1 t - θ 0 t < 2 * Real.pi) := by
  classical
  let θ₀ := Circle.isCoveringMap_exp.liftPath (q 0) (q 0 0).val.arg (Circle.exp_arg _).symm
  have hθ₀ (t : Interval) : Circle.exp (θ₀ t) = q 0 t :=
    congrFun (Circle.isCoveringMap_exp.liftPath_lifts ..) t
  have hp : 0 < 2 * Real.pi := by positivity
  obtain ⟨w, hw, hew⟩ := Circle.periodic_exp.exists_mem_Ico hp
    (q 1 0).val.arg (θ₀ 0)
  have hqw : Circle.exp w = q 1 0 := hew.symm.trans (Circle.exp_arg _)
  have hw0 : θ₀ 0 < w := lt_of_le_of_ne hw.1 (by
    intro he; apply hne 0; rw [← hθ₀ 0, ← hqw, he])
  let θ₁ := Circle.isCoveringMap_exp.liftPath (q 1) w hqw.symm
  have hθ₁ (t : Interval) : Circle.exp (θ₁ t) = q 1 t :=
    congrFun (Circle.isCoveringMap_exp.liftPath_lifts ..) t
  have hθ₁0 : θ₁ 0 = w := Circle.isCoveringMap_exp.liftPath_zero ..
  let d : C(Interval, ℝ) := θ₁ - θ₀
  have hd0 : 0 < d 0 ∧ d 0 < 2 * Real.pi := by
    change 0 < θ₁ 0 - θ₀ 0 ∧ θ₁ 0 - θ₀ 0 < 2 * Real.pi
    rw [hθ₁0]; constructor <;> linarith [hw.2]
  have hdz (t : Interval) : d t ≠ 0 := by
    intro he
    apply hne t
    rw [← hθ₀ t, ← hθ₁ t]
    change θ₁ t - θ₀ t = 0 at he
    rw [sub_eq_zero.mp he]
  have hdp (t : Interval) : d t ≠ 2 * Real.pi := by
    intro he
    apply hne t
    rw [← hθ₀ t, ← hθ₁ t]
    change θ₁ t - θ₀ t = 2 * Real.pi at he
    have he' : θ₁ t = θ₀ t + 2 * Real.pi := by linarith
    rw [he', Circle.exp_add_two_pi]
  have hd (t : Interval) : 0 < d t ∧ d t < 2 * Real.pi := by
    constructor
    · by_contra hn
      obtain ⟨s, _, hs⟩ := isPreconnected_univ.intermediate_value
        (a := t) (b := 0) (mem_univ _) (mem_univ _) d.continuous.continuousOn
        (show (0 : ℝ) ∈ Icc (d t) (d 0) from ⟨le_of_not_gt hn, hd0.1.le⟩)
      exact hdz s hs
    · by_contra hn
      obtain ⟨s, _, hs⟩ := isPreconnected_univ.intermediate_value
        (a := 0) (b := t) (mem_univ _) (mem_univ _) d.continuous.continuousOn
        (show 2 * Real.pi ∈ Icc (d 0) (d t) from ⟨hd0.2.le, le_of_not_gt hn⟩)
      exact hdp s hs
  let θ : Fin 2 → C(Interval, ℝ) := fun i => if i = 0 then θ₀ else θ₁
  refine ⟨θ, ?_, ?_⟩
  · intro i t
    fin_cases i
    · exact hθ₀ t
    · exact hθ₁ t
  · exact hd


lemma circle_exp_ne_of_gap {a b : ℝ} (hgap : 0 < b - a ∧ b - a < 2 * Real.pi) :
    Circle.exp a ≠ Circle.exp b := by
  intro he
  have hab : a ≤ b := by linarith [hgap.1]
  have he' := Circle.exp_injOn_Icc hgap.2 (left_mem_Icc.mpr hab)
    (right_mem_Icc.mpr hab) he
  linarith [hgap.1]

lemma interpolate_gap {a b P : ℝ} (ha : a ∈ Ioo 0 P) (hb : b ∈ Ioo 0 P)
    (t : Interval) : (1 - t.val) * a + t.val * b ∈ Ioo 0 P := by
  exact (convex_Ioo (0 : ℝ) P) ha hb (sub_nonneg.mpr t.property.2)
    t.property.1 (by ring)

lemma covering_relative_lift_endpoints {Z : Type u} {Y : Type v}
    [TopologicalSpace Z] [TopologicalSpace Y]
    {τ ℓ : C(Interval, Z)} (J : ContinuousMap.HomotopyRel τ ℓ ({0, 1} : Set Interval))
    (p : Y → Z) (hp : IsCoveringMap p)
    (T : C(Interval, Y)) (hT : ∀ t, p (T t) = τ t) :
    ∃ L : C(Interval, Y), (∀ t, p (L t) = ℓ t) ∧ L 0 = T 0 ∧ L 1 = T 1 := by
  have hτ0 : τ 0 = p (T 0) := (hT 0).symm
  have hℓ0 : ℓ 0 = p (T 0) := (J.fst_eq_snd (by simp)).symm.trans hτ0
  let L := hp.liftPath ℓ (T 0) hℓ0
  have hTeq : T = hp.liftPath τ (T 0) hτ0 := (hp.eq_liftPath_iff' hτ0).mpr
    ⟨funext hT, rfl⟩
  refine ⟨L, fun t => congrFun (hp.liftPath_lifts ..) t, hp.liftPath_zero .., ?_⟩
  rw [hTeq]
  exact (hp.liftPath_apply_one_eq_of_homotopicRel ⟨J⟩ (T 0) hτ0 hℓ0).symm

lemma boundary_pair_affine_normalization {Z : Type u} [TopologicalSpace Z]
    {B : Set Z} (β : Circle ≃ₜ B)
    (τ : Fin 2 → C(Interval, Z))
    (hB : ∀ i t, τ i t ∈ B) (hne : ∀ t, τ 0 t ≠ τ 1 t) :
    ∃ (θ : Fin 2 → C(Interval, ℝ)) (ℓ : Fin 2 → C(Interval, Z))
      (J : ∀ i, ContinuousMap.HomotopyRel (τ i) (ℓ i) ({0, 1} : Set Interval)),
      (∀ i t, (β (Circle.exp (θ i t))).val = τ i t) ∧
      (∀ t, 0 < θ 1 t - θ 0 t ∧ θ 1 t - θ 0 t < 2 * Real.pi) ∧
      (∀ i t, ℓ i t = (β (Circle.exp ((1 - t.val) * θ i 0 + t.val * θ i 1))).val) ∧
      (∀ i, ℓ i 0 = τ i 0 ∧ ℓ i 1 = τ i 1) ∧
      (∀ i r t, J i (r, t) = (β (Circle.exp ((1 - r.val) * θ i t +
        r.val * ((1 - t.val) * θ i 0 + t.val * θ i 1)))).val) ∧
      (∀ i t, J i (0, t) = τ i t ∧ J i (1, t) = ℓ i t) ∧
      (∀ i r, J i (r, 0) = τ i 0 ∧ J i (r, 1) = τ i 1) ∧
      (∀ i r t, J i (r, t) ∈ B) ∧
      (∀ r t, J 0 (r, t) ≠ J 1 (r, t)) ∧
      (∀ t, ℓ 0 t ≠ ℓ 1 t) ∧
      (∀ (Y : Type v) [TopologicalSpace Y] (p : Y → Z), IsCoveringMap p →
        ∀ (T : Fin 2 → C(Interval, Y)), (∀ i t, p (T i t) = τ i t) →
        ∃ L : Fin 2 → C(Interval, Y), (∀ i t, p (L i t) = ℓ i t) ∧
          (∀ i, L i 0 = T i 0 ∧ L i 1 = T i 1)) := by
  classical
  let q : Fin 2 → C(Interval, Circle) := fun i =>
    ⟨fun t => β.symm ⟨τ i t, hB i t⟩, β.symm.continuous.comp
      ((τ i).continuous.subtype_mk _)⟩
  have hqne (t : Interval) : q 0 t ≠ q 1 t := by
    intro he
    apply hne t
    exact congrArg Subtype.val (β.symm.injective he)
  obtain ⟨θ, hθ, hgap⟩ := circle_pair_real_lifts q hqne
  have hτ (i : Fin 2) (t : Interval) : (β (Circle.exp (θ i t))).val = τ i t := by
    rw [hθ i t]; exact congrArg Subtype.val (β.apply_symm_apply _)
  have hβc : Continuous (fun z : Circle => (β z).val) :=
    continuous_subtype_val.comp β.continuous
  let ℓ : Fin 2 → C(Interval, Z) := fun i =>
    ⟨fun t => (β (Circle.exp ((1 - t.val) * θ i 0 + t.val * θ i 1))).val,
      hβc.comp (Circle.exp.continuous.comp (by fun_prop))⟩
  let J : ∀ i, ContinuousMap.HomotopyRel (τ i) (ℓ i) ({0, 1} : Set Interval) :=
    fun i => {
      toHomotopy := {
        toFun := fun rt => (β (Circle.exp ((1 - rt.1.val) * θ i rt.2 +
          rt.1.val * ((1 - rt.2.val) * θ i 0 + rt.2.val * θ i 1)))).val
        continuous_toFun := hβc.comp (Circle.exp.continuous.comp (by fun_prop))
        map_zero_left := by intro t; simp only [show (0 : Interval).val = 0 from rfl, sub_zero,
          one_mul, zero_mul, add_zero]; exact hτ i t
        map_one_left := by intro t; simp only [show (1 : Interval).val = 1 from rfl, sub_self,
          zero_mul, one_mul, zero_add]; rfl }
      prop' := by
        intro r t ht
        rcases Set.mem_insert_iff.mp ht with ht | ht
        · subst t
          have he : (1 - r.val) * θ i (0 : Interval) + r.val *
              ((1 - (0 : Interval).val) * θ i 0 + (0 : Interval).val * θ i 1) = θ i 0 := by
            change (1 - r.val) * θ i 0 + r.val * ((1 - 0) * θ i 0 + 0 * θ i 1) = θ i 0
            ring
          change (β (Circle.exp _)).val = _
          rw [he]; exact hτ i 0
        · have ht := Set.mem_singleton_iff.mp ht
          subst t
          have he : (1 - r.val) * θ i (1 : Interval) + r.val *
              ((1 - (1 : Interval).val) * θ i 0 + (1 : Interval).val * θ i 1) = θ i 1 := by
            change (1 - r.val) * θ i 1 + r.val * ((1 - 1) * θ i 0 + 1 * θ i 1) = θ i 1
            ring
          change (β (Circle.exp _)).val = _
          rw [he]; exact hτ i 1 }
  have hnoncollision (r t : Interval) : J 0 (r, t) ≠ J 1 (r, t) := by
    let a := (1 - r.val) * θ 0 t + r.val * ((1 - t.val) * θ 0 0 + t.val * θ 0 1)
    let b := (1 - r.val) * θ 1 t + r.val * ((1 - t.val) * θ 1 0 + t.val * θ 1 1)
    have hlin := interpolate_gap (hgap 0) (hgap 1) t
    have hfull := interpolate_gap (hgap t) hlin r
    have he : b - a = (1 - r.val) * (θ 1 t - θ 0 t) + r.val *
        ((1 - t.val) * (θ 1 0 - θ 0 0) + t.val * (θ 1 1 - θ 0 1)) := by
      dsimp [a, b]; ring
    have hab : 0 < b - a ∧ b - a < 2 * Real.pi := he ▸ hfull
    intro heq
    apply circle_exp_ne_of_gap hab
    apply β.injective
    exact Subtype.ext heq
  refine ⟨θ, ℓ, J, hτ, hgap, (fun _ _ => rfl), ?_,
    (fun _ _ _ => rfl), ?_, ?_, ?_, hnoncollision, ?_, ?_⟩
  · intro i; constructor <;> simpa [ℓ] using hτ i _
  · intro i t; exact ⟨(J i).apply_zero t, (J i).apply_one t⟩
  · intro i r; exact ⟨(J i).eq_fst r (by simp), (J i).eq_fst r (by simp)⟩
  · intro i r t; exact (β _).property
  · intro t
    simpa only [(J 0).apply_one t, (J 1).apply_one t] using hnoncollision 1 t
  · intro Y inst p hp T hT
    choose L hL h0 h1 using fun i => covering_relative_lift_endpoints (J i) p hp (T i) (hT i)
    exact ⟨L, hL, fun i => ⟨h0 i, h1 i⟩⟩

end CoherentEndpointMotion.FreeBoundaryContactRepair
