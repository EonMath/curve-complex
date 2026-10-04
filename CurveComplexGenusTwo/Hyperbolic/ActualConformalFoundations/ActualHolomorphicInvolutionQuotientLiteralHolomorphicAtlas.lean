import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.CauchyIntegral
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.HolomorphicLocalSquareQuotientDescent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualHolomorphicInvolutionQuotientPowerChartCover
open Set Filter Topology
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
theorem actual_holomorphic_involution_quotient_literal_holomorphic_atlas {E B : Type*} [TopologicalSpace E] [T2Space E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] [TopologicalSpace B]
    (f : E ≃ₜ E) (hinv : Function.Involutive f)
    (hfinite : {x | f x = x}.Finite) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (p : E → B) (hp : IsOpenQuotientMap p)
    (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x) :
    ∃ (charts : B → OpenPartialHomeomorph B ℂ) (A : ChartedSpace ℂ B),
      A.chartAt = charts ∧ A.atlas = Set.range charts ∧
      letI : ChartedSpace ℂ B := A
      IsManifold 𝓘(ℂ) ∞ B ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ p ∧
      ∀ b, ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E) (n : ℕ),
        IsOpen U ∧ (chartAt ℂ b).source = p '' U ∧
        (n = 1 ∨ n = 2) ∧
        (∀ x ∈ U, (chartAt ℂ b) (p x) = (e x) ^ n) ∧
        (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
        (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) := by
  exact (open Filter Topology in by
    classical
    have target_formula   
        (p : E → B) (e : OpenPartialHomeomorph E ℂ)
        (c : OpenPartialHomeomorph B ℂ) (U : Set E) (n : ℕ)
        (hsource : c.source = p '' U)
        (hformula : ∀ x ∈ U, c (p x) = (e x) ^ n) :
        c.target = (fun z : ℂ => z ^ n) '' (e '' U) := by
      rw [← c.image_source_eq_target, hsource, Set.image_image]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, (hformula x hx).symm⟩
      · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, hformula x hx⟩
    have square_domain   
        (f : E → E) (p : E → B) (e : OpenPartialHomeomorph E ℂ)
        (c : OpenPartialHomeomorph B ℂ) (U : Set E)
        (hstable : MapsTo f U U) (hneg : ∀ x ∈ U, e (f x) = -e x)
        (htarget : c.target = (fun z : ℂ => z ^ 2) '' (e '' U)) :
        (fun z : ℂ => z ^ 2) ⁻¹' c.target = e '' U := by
      ext z
      constructor
      · intro hz
        rw [htarget] at hz
        rcases hz with ⟨v, ⟨x, hx, hex⟩, hv⟩
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv with hv | hv
        · exact ⟨x, hx, hex.trans hv⟩
        · refine ⟨f x, hstable hx, ?_⟩
          rw [hneg x hx, hex, hv, neg_neg]
      · rintro ⟨x, hx, rfl⟩
        rw [htarget]
        exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
    have lifted_holomorphic   
        (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f)
        (p : E → B) 
        (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
        (e : OpenPartialHomeomorph E ℂ) (c : OpenPartialHomeomorph B ℂ)
        (V : Set E) (hV : IsOpen V) (n : ℕ)
        (hsource : c.source = p '' V)
        (hformula : ∀ x ∈ V, c (p x) = (e x) ^ n)
        (he : ∀ x ∈ V, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x)
        (a : ℂ → E) (z : ℂ) (ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 a z)
        (hz : p (a z) ∈ c.source) :
        DifferentiableAt ℂ (fun w => c (p (a w))) z := by
      rw [hsource] at hz
      obtain ⟨y, hy, hpy⟩ := hz
      rcases (hfiber (a z) y).mp hpy with h | h
      · subst y
        have hhol : ContDiffAt ℂ 1 (e ∘ a) z := (he (a z) hy |>.comp z ha).contDiffAt
        have hd : DifferentiableAt ℂ (fun w => (e (a w)) ^ n) z :=
          (hhol.pow n).differentiableAt (by norm_num)
        apply hd.congr_of_eventuallyEq
        have hv : ∀ᶠ w in nhds z, a w ∈ V :=
          ha.continuousAt.tendsto.eventually (hV.mem_nhds hy)
        filter_upwards [hv] with w hw
        exact hformula (a w) hw
      · have hyf : f (a z) ∈ V := h ▸ hy
        have hfa : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 (f ∘ a) z := (hmap (a z)).comp z ha
        have hhol : ContDiffAt ℂ 1 (e ∘ (f ∘ a)) z :=
          (he (f (a z)) hyf |>.comp z hfa).contDiffAt
        have hd : DifferentiableAt ℂ (fun w => (e (f (a w))) ^ n) z :=
          (hhol.pow n).differentiableAt (by norm_num)
        apply hd.congr_of_eventuallyEq
        have hv : ∀ᶠ w in nhds z, f (a w) ∈ V :=
          hfa.continuousAt.tendsto.eventually (hV.mem_nhds hyf)
        filter_upwards [hv] with w hw
        have hp : p (f (a w)) = p (a w) := (hfiber (a w) (f (a w))).mpr (Or.inr rfl)
        rw [← hp]
        exact hformula (f (a w)) hw
    have overlap_holomorphic    
        (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f)
        (p : E → B) (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
        (eA eB : OpenPartialHomeomorph E ℂ) (cA cB : OpenPartialHomeomorph B ℂ)
        (UA UB : Set E) (nA nB : ℕ)
        (hUA : UA ⊆ eA.source) (hUB : IsOpen UB)
        (hsourceA : cA.source = p '' UA) (hsourceB : cB.source = p '' UB)
        (hformulaA : ∀ x ∈ UA, cA (p x) = (eA x) ^ nA)
        (hformulaB : ∀ x ∈ UB, cB (p x) = (eB x) ^ nB)
        (hB : ∀ x ∈ UB, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 eB x)
        (hAinv : ∀ w ∈ eA '' UA, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 eA.symm w)
        (hnA : nA = 1 ∨ (nA = 2 ∧ MapsTo f UA UA ∧ ∀ x ∈ UA, eA (f x) = -eA x)) :
        ContDiffOn ℂ ∞ (fun z => cB (cA.symm z))
          (cA.target ∩ cA.symm ⁻¹' cB.source) := by
      let s := cA.target ∩ cA.symm ⁻¹' cB.source
      let F : ℂ → ℂ := fun z => cB (cA.symm z)
      have hs : IsOpen s := cA.isOpen_inter_preimage_symm cB.open_source
      have hc : ContinuousOn F s :=
        cB.continuousOn.comp (cA.symm.continuousOn.mono inter_subset_left) (fun _ h => h.2)
      have htarget := target_formula p eA cA UA nA hsourceA hformulaA
      have hpull (z : ℂ) (hz : z ∈ eA '' UA) (hzs : z ^ nA ∈ s) :
          DifferentiableAt ℂ (fun w => F (w ^ nA)) z := by
        obtain ⟨x, hx, hex⟩ := hz
        have hzmem : z ∈ eA.target := hex ▸ eA.map_source (hUA hx)
        have hza : eA.symm z = x := by rw [← hex, eA.left_inv (hUA hx)]
        have hca : cA.symm (z ^ nA) = p x := by
          rw [← hex, ← hformulaA x hx]
          exact cA.left_inv (hsourceA ▸ mem_image_of_mem p hx)
        have hd := lifted_holomorphic f hmap p hfiber eB cB UB hUB nB
          hsourceB hformulaB hB eA.symm z (hAinv z ⟨x, hx, hex⟩)
          (by simpa [hza, hca] using hzs.2)
        apply hd.congr_of_eventuallyEq
        have hU : ∀ᶠ w in nhds z, eA.symm w ∈ UA := by
          have hopen : IsOpen (eA '' UA) := by
            -- The domain is also the inverse image of the open downstairs source under power.
            rcases hnA with h | ⟨h, hstable, hneg⟩
            · have heq : cA.target = eA '' UA := by simpa [h, pow_one] using htarget
              rw [← heq]
              exact cA.open_target
            · rw [← square_domain f p eA cA UA hstable hneg (by simpa [h] using htarget)]
              exact cA.open_target.preimage (continuous_id.pow 2)
          have hev : ∀ᶠ w in nhds z, w ∈ eA '' UA := hopen.mem_nhds ⟨x, hx, hex⟩
          filter_upwards [hev] with w hw
          obtain ⟨v, hv, rfl⟩ := hw
          simpa [eA.left_inv (hUA hv)] using hv
        have ht : ∀ᶠ w in nhds z, w ∈ eA.target := eA.open_target.mem_nhds hzmem
        filter_upwards [hU, ht] with w hw hwt
        dsimp [F]
        rw [← eA.right_inv hwt, ← hformulaA (eA.symm w) hw,
          cA.left_inv (hsourceA ▸ mem_image_of_mem p hw)]
        rw [eA.left_inv (hUA hw)]
      have hd : DifferentiableOn ℂ F s := by
        rcases hnA with h | ⟨h, hstable, hneg⟩
        · intro z hz
          have hzimage : z ∈ eA '' UA := by
            have hzT := hz.1
            rw [htarget] at hzT
            simpa [h, pow_one] using hzT
          simpa [h, pow_one] using (hpull z hzimage (by simpa [h] using hz)).differentiableWithinAt
        · apply holomorphic_local_square_quotient_descent F s hs hc
          intro z hz
          have hzimage : z ∈ eA '' UA := by
            rw [← square_domain f p eA cA UA hstable hneg (by simpa [h] using htarget)]
            exact hz.1
          simpa [h] using (hpull z hzimage (by simpa [h] using hz)).differentiableWithinAt
      exact hd.contDiffOn hs
    have literal_atlas    
        (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f)
        (p : E → B) (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
        (charts : B → OpenPartialHomeomorph B ℂ)
        (hcharts : ∀ b, b ∈ (charts b).source ∧
          ∃ (q : E) (e : OpenPartialHomeomorph E ℂ) (U : Set E) (n : ℕ),
            p q = b ∧ IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧
            ((n = 1 ∧ f q ≠ q) ∨ (n = 2 ∧ f q = q ∧ e q = 0 ∧ MapsTo f U U ∧
              (∀ x ∈ U, e (f x) = -e x))) ∧
            (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
            (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
            (charts b).source = p '' U ∧
            (∀ x ∈ U, (charts b) (p x) = (e x) ^ n)) :
        ∃ A : ChartedSpace ℂ B, A.chartAt = charts ∧ A.atlas = Set.range charts ∧
          letI : ChartedSpace ℂ B := A
          IsManifold 𝓘(ℂ) ∞ B := by
      classical
      let A : ChartedSpace ℂ B := {
        atlas := Set.range charts
        chartAt := charts
        mem_chart_source := fun b => (hcharts b).1
        chart_mem_atlas := fun b => ⟨b, rfl⟩ }
      letI : ChartedSpace ℂ B := A
      refine ⟨A, rfl, rfl, ?_⟩
      apply isManifold_of_contDiffOn
      intro c d hc hd
      obtain ⟨a, rfl⟩ := hc
      obtain ⟨b, rfl⟩ := hd
      obtain ⟨qA, eA, UA, nA, hpA, hopenA, hqA, hUA, hnA, heA, hAinv, hsourceA, hformulaA⟩ :=
        (hcharts a).2
      obtain ⟨qB, eB, UB, nB, hpB, hopenB, hqB, hUB, hnB, heB, hBinv, hsourceB, hformulaB⟩ :=
        (hcharts b).2
      have hpower : nA = 1 ∨ (nA = 2 ∧ MapsTo f UA UA ∧ ∀ x ∈ UA, eA (f x) = -eA x) := by
        rcases hnA with h | h
        · exact Or.inl h.1
        · exact Or.inr ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩
      have h := overlap_holomorphic f hmap p hfiber eA eB (charts a) (charts b)
        UA UB nA nB hUA hopenB hsourceA hsourceB hformulaA hformulaB heB hAinv hpower
      intro z hz
      simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Function.comp_def, id_eq, Set.range_id, Set.preimage_id, Set.inter_univ, OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] using h z hz.1
    have lifted_smooth   
        (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f)
        (p : E → B) 
        (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
        (e : OpenPartialHomeomorph E ℂ) (c : OpenPartialHomeomorph B ℂ)
        (V : Set E) (hV : IsOpen V) (n : ℕ)
        (hsource : c.source = p '' V)
        (hformula : ∀ x ∈ V, c (p x) = (e x) ^ n)
        (he : ∀ x ∈ V, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x)
        (a : ℂ → E) (z : ℂ) (ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 a z)
        (hz : p (a z) ∈ c.source) :
        ContDiffAt ℂ 1 (fun w => c (p (a w))) z := by
      rw [hsource] at hz
      obtain ⟨y, hy, hpy⟩ := hz
      rcases (hfiber (a z) y).mp hpy with h | h
      · subst y
        have hhol : ContDiffAt ℂ 1 (e ∘ a) z := (he (a z) hy |>.comp z ha).contDiffAt
        have hd : ContDiffAt ℂ 1 (fun w => (e (a w)) ^ n) z := hhol.pow n
        apply hd.congr_of_eventuallyEq
        have hv : ∀ᶠ w in nhds z, a w ∈ V :=
          ha.continuousAt.tendsto.eventually (hV.mem_nhds hy)
        filter_upwards [hv] with w hw
        exact hformula (a w) hw
      · have hyf : f (a z) ∈ V := h ▸ hy
        have hfa : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 (f ∘ a) z := (hmap (a z)).comp z ha
        have hhol : ContDiffAt ℂ 1 (e ∘ (f ∘ a)) z :=
          (he (f (a z)) hyf |>.comp z hfa).contDiffAt
        have hd : ContDiffAt ℂ 1 (fun w => (e (f (a w))) ^ n) z := hhol.pow n
        apply hd.congr_of_eventuallyEq
        have hv : ∀ᶠ w in nhds z, f (a w) ∈ V :=
          hfa.continuousAt.tendsto.eventually (hV.mem_nhds hyf)
        filter_upwards [hv] with w hw
        have hp : p (f (a w)) = p (a w) := (hfiber (a w) (f (a w))).mpr (Or.inr rfl)
        rw [← hp]
        exact hformula (f (a w)) hw
    have complex_smooth_upgrade (g : ℂ → ℂ) (z : ℂ)
        (h : ContDiffAt ℂ 1 g z) : ContDiffAt ℂ ∞ g z := by
      obtain ⟨u, hu, hzu, hgu⟩ := h.contDiffOn' le_rfl (by simp)
      have hgu' : ContDiffOn ℂ 1 g u := by simpa using hgu
      have hd : DifferentiableOn ℂ g u := hgu'.differentiableOn (by norm_num)
      exact (hd.contDiffOn hu).contDiffAt (hu.mem_nhds hzu)
    have projection_holomorphic   
          [ChartedSpace ℂ B]
        [IsManifold 𝓘(ℂ) ∞ B]
        (f : E ≃ₜ E) (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f)
        (p : E → B) (hp : Continuous p)
        (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
        (hcharts : ∀ b, ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E) (n : ℕ),
          IsOpen U ∧ (chartAt ℂ b).source = p '' U ∧
          (∀ x ∈ U, (chartAt ℂ b) (p x) = (e x) ^ n) ∧
          (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x)) :
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ p := by
      intro x
      obtain ⟨e, U, n, hU, hsource, hformula, he⟩ := hcharts (p x)
      let a := chartAt ℂ x
      have hx : x ∈ a.source := mem_chart_source ℂ x
      have ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 a.symm (a x) :=
        (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ∞)
          (IsManifold.chart_mem_maximalAtlas x) (a.map_source hx)).of_le (by simp)
      have hlift : ContDiffAt ℂ 1 (fun w => (chartAt ℂ (p x)) (p (a.symm w))) (a x) :=
        lifted_smooth f hmap p hfiber e (chartAt ℂ (p x)) U hU n hsource hformula he
          a.symm (a x) ha (by simpa [a.left_inv hx] using mem_chart_source ℂ (p x))
      have hsmooth := complex_smooth_upgrade _ _ hlift
      apply (contMDiffAt_iff_of_mem_source (mem_chart_source ℂ x)
        (mem_chart_source ℂ (p x))).mpr
      refine ⟨hp.continuousAt, ?_⟩
      simpa [a, extChartAt, OpenPartialHomeomorph.extend, Function.comp_def]
        using hsmooth.contDiffWithinAt (s := Set.range (𝓘(ℂ) : ℂ → ℂ))

    obtain ⟨charts, hcharts⟩ := actual_holomorphic_involution_quotient_power_chart_cover
      f hinv hfinite hmap p hp hfiber
    have hmap1 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 f := hmap.of_le (by simp)
    obtain ⟨A, hAt, hAtlas, hManifold⟩ := literal_atlas f hmap1 p hfiber charts hcharts
    letI : ChartedSpace ℂ B := A
    letI : IsManifold 𝓘(ℂ) ∞ B := hManifold
    have hlocal : ∀ b, ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E) (n : ℕ),
        IsOpen U ∧ (chartAt ℂ b).source = p '' U ∧
        (n = 1 ∨ n = 2) ∧
        (∀ x ∈ U, (chartAt ℂ b) (p x) = (e x) ^ n) ∧
        (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
        (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) := by
      intro b
      obtain ⟨q, e, U, n, hpq, hU, hqU, hUe, hn, he, hei, hc, hpow⟩ := (hcharts b).2
      have hn' : n = 1 ∨ n = 2 := hn.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      have hchart : chartAt ℂ b = charts b := congrFun hAt b
      exact ⟨e, U, n, hU, hchart.symm ▸ hc, hn', hchart.symm ▸ hpow, he, hei⟩
    have hphol : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ p := by
      apply projection_holomorphic f hmap1 p hp.continuous hfiber
      intro b
      obtain ⟨e, U, n, hU, hc, hn, hpow, he, hei⟩ := hlocal b
      exact ⟨e, U, n, hU, hc, hpow, he⟩
    exact ⟨charts, A, hAt, hAtlas, hManifold, hphol, hlocal⟩
  )
