import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import Mathlib.Analysis.Convex.Basic
namespace CurveComplex
open Schoenflies Metric Set
theorem square_marked_supported_isotopy (F : Plane ≃ₜ Plane) (q : Plane)
    (hq : q ∈ Plane.openSquare 0 1) (hFq : F q = q)
    (hFfix : ∀ x, x ∉ Plane.openSquare 0 1 → F x = x) :
    ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
      (∀ t x, x ∉ Plane.openSquare 0 1 → H.map (t,x) = x) ∧
      (∀ t, H.map (t,q) = q) := by
  have marked (R : ℝ) (hR : 0 < R) (q : Plane)
      (F : Plane ≃ₜ Plane) (hFq : F q = q)
      (hFfix : ∀ x, R ≤ ‖x-q‖ → F x = x)
      (C : Set Plane) (hFC : ∀ x, x ∉ C → F x = x)
      (hconv : Convex ℝ C) (hq : q ∈ C) :
      ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
        (∀ t x, x ∉ C → H.map (t,x) = x) ∧
        (∀ t, H.map (t,q) = q) := by
    have centered (R : ℝ) (hR : 0 < R)
        (F : Plane ≃ₜ Plane) (hFzero : F 0 = 0) (hFfix : ∀ x, R ≤ ‖x‖ → F x = x)
        (C : Set Plane) (hFC : ∀ x, x ∉ C → F x = x)
        (hscale : ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x, x ∉ C → t⁻¹ • x ∉ C) :
        ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
          (∀ t x, R ≤ ‖x‖ → H.map (t, x) = x) ∧
          (∀ t x, x ∉ C → H.map (t, x) = x) ∧
          (∀ t, H.map (t, 0) = 0) := by
      have hFbound (x : Plane) (hx : ‖x‖ ≤ R) : ‖F x‖ ≤ R := by
        by_contra hn
        have heq : F x = x := F.injective (hFfix (F x) (le_of_not_ge hn))
        exact hn (by rw [heq]; exact hx)
      have hdisp (x : Plane) : ‖F x - x‖ ≤ 2 * R := by
        by_cases hx : ‖x‖ ≤ R
        · exact (norm_sub_le _ _).trans (by linarith [hFbound x hx])
        · rw [hFfix x (le_of_not_ge hx), sub_self, norm_zero]
          linarith
      let G : Interval × Plane → Plane := fun z =>
        if (z.1 : ℝ) = 0 then z.2 else (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2)
      have hGbound (z : Interval × Plane) :
          dist (G z) z.2 ≤ (2 * R) * (z.1 : ℝ) := by
        by_cases ht : (z.1 : ℝ) = 0
        · simp only [G, ht, ite_true, dist_self, mul_zero, le_refl]
        · dsimp only [G]
          rw [if_neg ht, dist_eq_norm]
          have heq : (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2) - z.2 =
              (z.1 : ℝ) • (F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2) := by
            rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
          rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
          calc
            (z.1 : ℝ) * ‖F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2‖ ≤
                (z.1 : ℝ) * (2 * R) :=
              mul_le_mul_of_nonneg_left (hdisp _) z.1.property.1
            _ = (2 * R) * (z.1 : ℝ) := mul_comm _ _
      have hGc : Continuous G := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases ht : (z.1 : ℝ) = 0
        · have hGz : G z = z.2 := by simp only [G, ht, ite_true]
          change Filter.Tendsto G (nhds z) (nhds (G z))
          rw [hGz, tendsto_iff_dist_tendsto_zero]
          have hlim : Filter.Tendsto
              (fun w : Interval × Plane => (2 * R) * (w.1 : ℝ) + dist w.2 z.2)
              (nhds z) (nhds 0) := by
            have hc : Continuous (fun w : Interval × Plane =>
                (2 * R) * (w.1 : ℝ) + dist w.2 z.2) := by fun_prop
            simpa only [ContinuousAt, ht, mul_zero, dist_self, add_zero] using hc.continuousAt (x := z)
          exact squeeze_zero (fun w => dist_nonneg) (fun w =>
            (dist_triangle (G w) w.2 z.2).trans (add_le_add (hGbound w) le_rfl)) hlim
        · have hc : ContinuousAt
              (fun w : Interval × Plane => (w.1 : ℝ) • F ((w.1 : ℝ)⁻¹ • w.2)) z := by
            fun_prop (disch := assumption)
          apply hc.congr_of_eventuallyEq
          have hevent : ∀ᶠ w : Interval × Plane in nhds z, (w.1 : ℝ) ≠ 0 :=
            (continuous_subtype_val.comp continuous_fst).continuousAt.eventually_ne ht
          exact hevent.mono (fun w hw => if_neg hw)
      refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_, ?_⟩
      · intro t
        by_cases ht : (t : ℝ) = 0
        · exact ⟨Homeomorph.refl _, fun x => by
            change x = G (t, x)
            simp only [G, ht, ite_true]⟩
        · let u : ℝˣ := Units.mk0 (t : ℝ) ht
          let e := ((Homeomorph.smul u⁻¹).trans F).trans (Homeomorph.smul u)
          refine ⟨e, ?_⟩
          intro x
          change (t : ℝ) • F ((t : ℝ)⁻¹ • x) = G (t, x)
          dsimp only [G]
          rw [if_neg ht]
      · intro x
        simp [G]
      · funext x
        simp [AmbientIsotopy.finalMap, G]
      · intro t x hx
        change G (t, x) = x
        by_cases ht : (t : ℝ) = 0
        · simp only [G, ht, ite_true]
        · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
          have hlarge : R ≤ ‖(t : ℝ)⁻¹ • x‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), inv_mul_eq_div]
            apply (le_div_iff₀ htpos).mpr
            nlinarith [t.property.2]
          simp only [G, if_neg ht, hFfix _ hlarge, smul_smul, mul_inv_cancel₀ ht, one_smul]
      · intro t x hx
        change G (t, x) = x
        by_cases ht : (t : ℝ) = 0
        · simp only [G, ht, ite_true]
        · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
          have hout := hscale (t : ℝ) htpos t.property.2 x hx
          simp only [G, if_neg ht, hFC _ hout, smul_smul, mul_inv_cancel₀ ht, one_smul]
      · intro t
        change G (t, 0) = 0
        simp [G, hFzero]
    let e : Plane ≃ₜ Plane := {
      toFun := fun x => x-q
      invFun := fun x => x+q
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      continuous_toFun := continuous_id.sub continuous_const
      continuous_invFun := continuous_id.add continuous_const }
    let K : Plane ≃ₜ Plane := (e.symm.trans F).trans e
    let D : Set Plane := {x | x+q ∈ C}
    have kzero : K 0 = 0 := by simp [K,e,hFq]
    have kfix : ∀ x, R ≤ ‖x‖ → K x = x := by
      intro x hx
      have hf : F (x+q) = x+q := hFfix _ (by simpa using hx)
      simp [K,e,hf]
    have kout : ∀ x, x ∉ D → K x = x := by
      intro x hx
      have hf := hFC (x+q) hx
      simp [K,e,hf]
    have scale : ∀ t : ℝ, 0<t → t≤1 → ∀ x, x∉D → t⁻¹ • x ∉D := by
      intro t ht ht1 x hx hin
      have hp : t⁻¹ • x + q ∈ C := hin
      have hm := hconv.add_smul_sub_mem hq hp (show t ∈ Icc (0:ℝ) 1 from ⟨ht.le,ht1⟩)
      have he : q + t • (t⁻¹ • x + q - q) = x+q := by
        rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_comm]
      rw [he] at hm
      exact hx hm
    obtain ⟨H, hfinal, hball, hout, hzero⟩ := centered R hR K kzero kfix D kout scale
    let L : AmbientIsotopy Plane := {
      map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
        e.symm.continuous.comp (H.map.continuous.comp
          (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨h,hh⟩ := H.homeomorphism_at t
        exact ⟨(e.trans h).trans e.symm, fun x => congrArg e.symm (hh (e x))⟩
      at_zero := by
        intro x
        change e.symm (H.map (⟨0,by norm_num⟩,e x)) = x
        rw [H.at_zero, e.symm_apply_apply] }
    refine ⟨L, ?_, ?_, ?_⟩
    · funext x
      change e.symm (H.finalMap (e x)) = F x
      rw [hfinal]
      simp [K,e]
    · intro t x hx
      change e.symm (H.map (t,e x)) = x
      rw [hout t (e x) (by simpa [D,e] using hx), e.symm_apply_apply]
    · intro t
      change e.symm (H.map (t,e q)) = q
      have heq : e q = 0 := by simp [e]
      rw [heq,hzero]
      simp [e]
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball q).mp (Plane.isBounded_closedSquare 0 1)
  have qclosed : q ∈ Plane.closedSquare 0 1 :=
    mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hq).le
  have hRpos : 0 < R := by simpa using hR qclosed
  have hball : ∀ x, R ≤ ‖x-q‖ → F x = x := by
    intro x hx
    apply hFfix x
    intro hin
    have hb := hR (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hin).le)
    exact not_lt_of_ge hx (by simpa [dist_eq_norm] using hb)
  exact marked R hRpos q F hFq hball (Plane.openSquare 0 1) hFfix
    (Plane.convex_openSquare 0 1) hq
end CurveComplex
