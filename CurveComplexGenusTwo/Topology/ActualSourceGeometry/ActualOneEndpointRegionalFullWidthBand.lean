import Mathlib
import Schoenflies.PolyLocal
namespace CurveComplexGenusTwo.SourceTopology
open Set Topology Schoenflies

/-- A full-width initial band for a single actual regional boundary endpoint.
The other connector endpoint need not lie on this boundary. -/
theorem actual_one_endpoint_regional_full_width_band
    {S : Type} [TopologicalSpace S] [T2Space S]
    (R B : Set S) (a : C(unitInterval, R)) (ha : IsEmbedding a)
    (hcontact : ∀ t, (a t).val ∈ B ↔ t = 0)
    (N : OpenPartialHomeomorph S Plane) (η : ℝ)
    (hpN : (a 0).val ∈ N.source) (hN0 : N (a 0).val = 0)
    (hη : 0 < η) (hηtarget : Plane.openSquare 0 η ⊆ N.target)
    (hlocal : ∀ y ∈ N.symm '' Plane.openSquare 0 η,
      (y ∈ Set.range (fun t => (a t).val) ↔ 0 ≤ N y 0 ∧ N y 1 = 0) ∧
      (y ∈ B ↔ N y 0 = 0) ∧
      (y ∈ R ↔ 0 ≤ N y 0) ∧
      (y ∈ interior R ↔ 0 < N y 0)) :
    ∃ b : ℝ, ∃ hb : 0 < b ∧ b < 1,
    ∃ E : C(unitInterval × Icc (-1 : ℝ) 1, R),
      IsEmbedding E ∧
      (∀ t, E (t,⟨0,by norm_num⟩) =
        a ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
      (∀ w, (E (0,w)).val ∈ B) ∧
      (∀ t : unitInterval, 0 < (t:ℝ) → ∀ w,
        (E (t,w)).val ∈ interior R ∧ (E (t,w)).val ∉ B) ∧
      (∀ z, E z ∈ Set.range a ↔ (z.2:ℝ) = 0) ∧
      (∀ z, (E z).val ∈ N.symm '' Plane.openSquare 0 η) := by
  classical
  let f : C(unitInterval, S) := ⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩
  let W := N.symm '' Plane.openSquare 0 η
  have hW : IsOpen W := N.isOpen_image_symm_of_subset_target
    (Plane.isOpen_openSquare 0 η) hηtarget
  have hf0W : f 0 ∈ W := ⟨0, Plane.mem_openSquare_self hη, by
    simpa [f, hN0] using N.left_inv hpN⟩
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage f.continuous).mem_nhds hf0W)
  let b : ℝ := min (r/2) (1/2)
  have hb : 0 < b ∧ b < 1 := ⟨lt_min (half_pos hr) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hbr : b < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let τ : unitInterval → unitInterval := fun t => ⟨b*(t:ℝ),by
    constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩
  have hτc : Continuous τ := by dsimp [τ]; fun_prop
  have hτi : Function.Injective τ := by
    intro t u he
    exact Subtype.ext (mul_left_cancel₀ hb.1.ne' (congrArg Subtype.val he))
  have hfW (t : unitInterval) : f (τ t) ∈ W := by
    apply hrW
    change dist (b*(t:ℝ)) (0:ℝ) < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hb.1.le t.property.1)]
    exact (mul_le_of_le_one_right hb.1.le t.property.2).trans_lt hbr
  have hfN (t : unitInterval) : f (τ t) ∈ N.source := by
    obtain ⟨y,hy,he⟩ := hfW t
    exact he ▸ N.map_target (hηtarget hy)
  let c : unitInterval → Plane := fun t => N (f (τ t))
  have hcc : Continuous c := N.continuousOn.comp_continuous
    (f.continuous.comp hτc) hfN
  have hcsmall (t : unitInterval) : c t ∈ Plane.openSquare 0 η := by
    obtain ⟨y,hy,he⟩ := hfW t
    simpa [c, ← he, N.right_inv (hηtarget hy)] using hy
  have hcaxis (t : unitInterval) : 0 ≤ c t 0 ∧ c t 1 = 0 :=
    (hlocal _ (hfW t)).1.mp ⟨τ t,rfl⟩
  have hc0 : c 0 = 0 := by
    have hτ0 : τ 0 = 0 := Subtype.ext (by change b*0=0; ring)
    simpa [c, hτ0, f] using hN0
  have hcpos (t : unitInterval) (ht : 0 < (t:ℝ)) : 0 < c t 0 := by
    apply lt_of_le_of_ne (hcaxis t).1
    intro he
    have hh := (hcontact (τ t)).mp ((hlocal _ (hfW t)).2.1.mpr he.symm)
    have hh' := congrArg Subtype.val hh
    change b*(t:ℝ) = 0 at hh'
    exact (mul_pos hb.1 ht).ne' hh'
  let k : unitInterval × Icc (-1 : ℝ) 1 → Plane :=
    fun z => Plane.mk (c z.1 0) ((η/2)*(z.2:ℝ))
  have hkc : Continuous k := by
    dsimp [k, Plane.mk]
    fun_prop
  have hk (z : unitInterval × Icc (-1 : ℝ) 1) : k z ∈ Plane.openSquare 0 η := by
    rw [Plane.mem_openSquare_iff]
    intro i
    fin_cases i
    · simpa [k] using (Plane.mem_openSquare_iff 0 η (c z.1)).mp (hcsmall z.1) 0
    · change |(η/2)*(z.2:ℝ) - 0| < η
      rw [sub_zero]
      rw [abs_mul, abs_of_pos (half_pos hη)]
      exact (mul_le_of_le_one_right (half_pos hη).le (abs_le.mpr z.2.property)).trans_lt (by linarith)
  let F := fun z => N.symm (k z)
  have hFc : Continuous F := N.symm.continuousOn.comp_continuous hkc (fun z => hηtarget (hk z))
  have hFW (z) : F z ∈ W := ⟨k z, hk z, rfl⟩
  have hFk (z) : N (F z) = k z := N.right_inv (hηtarget (hk z))
  have hFR (z) : F z ∈ R := (hlocal _ (hFW z)).2.2.1.mpr (by
    rw [hFk]; exact (hcaxis z.1).1)
  let E : C(unitInterval × Icc (-1 : ℝ) 1, R) := ⟨fun z => ⟨F z,hFR z⟩, hFc.subtype_mk _⟩
  have hcenter (t : unitInterval) : E (t,⟨0,by norm_num⟩) = a (τ t) := by
    apply Subtype.ext
    change N.symm (k (t,⟨0,by norm_num⟩)) = f (τ t)
    have he : k (t,⟨0,by norm_num⟩) = c t := by
      ext i
      fin_cases i
      · simp [k]
      · simpa [k] using (hcaxis t).2.symm
    rw [he]
    exact N.left_inv (hfN t)
  have hFi : Function.Injective F := by
    intro z w he
    have hh : k z = k w := (hFk z).symm.trans ((congrArg N he).trans (hFk w))
    have hwidth : (z.2:ℝ) = (w.2:ℝ) := mul_left_cancel₀ (half_pos hη).ne'
      (by simpa [k] using congrArg (fun q : Plane => q 1) hh)
    have hcent : c z.1 = c w.1 := by
      ext i
      fin_cases i
      · simpa [k] using congrArg (fun q : Plane => q 0) hh
      · exact (hcaxis z.1).2.trans (hcaxis w.1).2.symm
    have hpoint : f (τ z.1) = f (τ w.1) := N.injOn (hfN z.1) (hfN w.1) hcent
    exact Prod.ext (hτi (ha.injective (Subtype.ext hpoint))) (Subtype.ext hwidth)
  have hE : IsEmbedding E := (E.continuous.isClosedEmbedding (by
    intro z w he
    exact hFi (congrArg Subtype.val he))).isEmbedding
  refine ⟨b,hb,E,hE,hcenter,?_,?_,?_,hFW⟩
  · intro w
    apply (hlocal _ (hFW (0,w))).2.1.mpr
    rw [hFk]
    change c 0 0 = 0
    rw [hc0]; rfl
  · intro t ht w
    constructor
    · apply (hlocal _ (hFW (t,w))).2.2.2.mpr
      rw [hFk]
      exact hcpos t ht
    · intro hB
      have hh := (hlocal _ (hFW (t,w))).2.1.mp hB
      rw [hFk] at hh
      exact (hcpos t ht).ne' hh
  · intro z
    constructor
    · rintro ⟨t,ht⟩
      have htrace : F z ∈ Set.range (fun t => (a t).val) :=
        ⟨t,congrArg Subtype.val ht⟩
      have hh := ((hlocal _ (hFW z)).1.mp htrace).2
      rw [hFk] at hh
      change (η/2)*(z.2:ℝ) = 0 at hh
      exact (mul_eq_zero.mp hh).resolve_left (half_pos hη).ne'
    · intro hw
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hw)
      refine ⟨τ z.1,?_⟩
      rw [he,hcenter]
end CurveComplexGenusTwo.SourceTopology
