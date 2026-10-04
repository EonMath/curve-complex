import CurveComplexGenusTwo.Topology.Smoothing.FiniteActualStarRadialization
import CurveComplexGenusTwo.Foundations.Definitions
open Set Metric Schoenflies CurveComplex
set_option maxHeartbeats 600000

theorem supported_pointed_plane_isotopy (o : Plane) (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
    (hFo : F o = o) (hfix : ∀ x, x ∉ ball o R → F x = x) :
    ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
      (∀ t, H.map (t,o) = o) ∧ ∀ t x, x ∉ ball o R → H.map (t,x) = x := by
  have zero (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
      (hFfix : ∀ x, R ≤ ‖x‖ → F x = x) (hFzero : F 0 = 0) :
      ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
        (∀ t x, R ≤ ‖x‖ → H.map (t,x) = x) ∧ ∀ t, H.map (t,0) = 0 := by
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
    refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_⟩
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
    · intro t
      change G (t,0) = 0
      by_cases ht : (t:ℝ) = 0
      · simp only [G,ht,ite_true]
      · simp only [G,if_neg ht,smul_zero,hFzero]
  have conjugate {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (e : X ≃ₜ Y) (H : AmbientIsotopy Y) :
      ∃ K : AmbientIsotopy X, ∀ t x, K.map (t,x) = e.symm (H.map (t,e x)) := by
    refine ⟨{ map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
      e.symm.continuous.comp (H.map.continuous.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩,
              homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
    · intro t
      obtain ⟨h,hh⟩ := H.homeomorphism_at t
      exact ⟨(e.trans h).trans e.symm,fun x => congrArg e.symm (hh (e x))⟩
    · intro x
      change e.symm (H.map (⟨0,by norm_num⟩,e x)) = x
      rw [H.at_zero,e.symm_apply_apply]
  let E : Plane ≃ₜ Plane := Homeomorph.addLeft (-o)
  have hEo : E o = 0 := by simp [E]
  have hEinv : E.symm 0 = o := by
    apply E.injective
    rw [E.apply_symm_apply,hEo]
  have hdist : ∀ x, dist (E x) 0 = dist x o := by
    intro x
    simp [E,dist_eq_norm,sub_eq_add_neg,add_comm]
  let A : Plane ≃ₜ Plane := (E.symm.trans F).trans E
  have hA0 : A 0 = 0 := by
    change E (F (E.symm 0)) = 0
    rw [hEinv,hFo,hEo]
  have hAfix : ∀ x, R ≤ ‖x‖ → A x = x := by
    intro x hx
    have hxout : E.symm x ∉ ball o R := by
      have hh := hdist (E.symm x)
      rw [E.apply_symm_apply,dist_zero_right] at hh
      simp only [mem_ball]
      exact not_lt.mpr (hh ▸ hx)
    change E (F (E.symm x)) = x
    rw [hfix _ hxout,E.apply_symm_apply]
  obtain ⟨H,hHF,hHfix,hH0⟩ := zero R hR A hAfix hA0
  obtain ⟨K,hK⟩ := conjugate E H
  refine ⟨K,?_,?_,?_⟩
  · funext x
    change K.map (⟨1,by norm_num⟩,x) = F x
    rw [hK]
    change E.symm (H.finalMap (E x)) = F x
    rw [hHF]
    change E.symm (E (F (E.symm (E x)))) = F x
    rw [E.symm_apply_apply,E.symm_apply_apply]
  · intro t
    rw [hK,hEo,hH0,hEinv]
  · intro t x hx
    rw [hK]
    have hxnorm : R ≤ ‖E x‖ := by
      have hh := hdist x
      rw [dist_zero_right] at hh
      exact not_lt.mp (by simpa only [mem_ball,← hh] using hx)
    rw [hHfix t _ hxnorm,E.symm_apply_apply]

#print axioms supported_pointed_plane_isotopy
