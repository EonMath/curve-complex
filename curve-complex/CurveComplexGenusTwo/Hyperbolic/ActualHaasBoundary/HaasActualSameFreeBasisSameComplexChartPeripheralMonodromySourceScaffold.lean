import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualSameComplexChartLiteralCylinderPeripheralConjugacySourceReviewRequest
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualSameFreeBasisLiteralLoopWordSuppliedMonodromyReviewRequest
open Set Topology
open CurveComplex.Hyperbolic
set_option maxHeartbeats 6000000
theorem actual_same_free_basis_same_complex_chart_peripheral_monodromy_source {U C K : Type} [TopologicalSpace U] [TopologicalSpace C]
    [SimplyConnectedSpace C] [Group K]
    (a : MulAction K C) (q : C → U) (hq : letI := a;IsQuotientCoveringMap q K)
    (f : U ≃ₜ ActualPuncturedCylinder) (o : q ⁻¹' {f.symm actualPantsBase})
    (B : FreeGroup (Fin 2) ≃* Kᵐᵒᵖ)
    (hB : ∀i : Fin 2,
      let ε : ℝ := if i=0 then -1 else 1
      let hε : ε≠0 := by dsimp [ε];split <;> norm_num
      let chart : ContinuousMap ActualPuncturedCylinder U := ⟨f.symm,f.symm.continuous⟩
      let stem := Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart
      let loop := Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart
      @SMul.smul K C a.toSMul (B (FreeGroup.of i)).unop
        (hq.isCoveringMap.monodromy stem o).val=
        (hq.isCoveringMap.monodromy loop (hq.isCoveringMap.monodromy stem o)).val)
    (ep : ActualPuncturedCylinder ≃ₜ {z : ℂ // z≠0 ∧ z≠1})
    (hep : ∀z : ActualPuncturedCylinder,(ep z).val=(Real.exp z.val.2:ℂ)*(z.val.1:ℂ)) :
    ∃z : ActualPuncturedCylinder,(ep z).val=1+((1/4:ℝ):ℂ) ∧
    ∃γ : Path z z,
      (∀t : unitInterval,(ep (γ t)).val=1+((1/4:ℝ):ℂ)*(Circle.exp (2*Real.pi*(t:ℝ)):ℂ)) ∧
    ∃stem : Path (f.symm actualPantsBase) (f.symm z),
      @SMul.smul K C a.toSMul (B ((FreeGroup.of 1)⁻¹*FreeGroup.of 0)).unop o.val=
        (hq.isCoveringMap.monodromy
          ⟦stem.trans ((γ.map f.symm.continuous).symm.trans stem.symm)⟧ o).val := by
  letI := a
  have hWhisker {u v : U} (S : Path.Homotopic.Quotient u v)
      (L : Path.Homotopic.Quotient v v) (x : q ⁻¹' {u}) (δ : K)
      (hδ : @SMul.smul K C a.toSMul δ (hq.isCoveringMap.monodromy S x).val=
        (hq.isCoveringMap.monodromy L (hq.isCoveringMap.monodromy S x)).val) :
      @SMul.smul K C a.toSMul δ x.val=
        (hq.isCoveringMap.monodromy (S.trans (L.trans S.symm)) x).val := by
    change (hq.toPermFiber u δ x).val=_
    apply congrArg Subtype.val
    apply (hq.isCoveringMap.monodromy_bijective S).1
    rw [hq.monodromy_toPermFiber]
    have ht : (S.trans (L.trans S.symm)).trans S=S.trans L := by
      simp only [Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.trans_refl]
    rw [←hq.isCoveringMap.monodromy_trans_apply,ht,
      hq.isCoveringMap.monodromy_trans_apply]
    exact Subtype.ext hδ
  let chart : ContinuousMap ActualPuncturedCylinder U := ⟨f.symm,f.symm.continuous⟩
  have hgen (i : Fin 2) :
      let ε : ℝ := if i=0 then -1 else 1
      let hε : ε≠0 := by dsimp [ε];split <;> norm_num
      @SMul.smul K C a.toSMul (B (FreeGroup.of i)).unop o.val=
        (hq.isCoveringMap.monodromy ⟦(actualPantsBoundaryLoop ε hε).map chart.continuous⟧ o).val := by
    intro ε hε
    have hH := hWhisker (Path.Homotopic.Quotient.map ⟦actualPantsStem ε hε⟧ chart)
      (Path.Homotopic.Quotient.map ⟦actualPantsHorizontalLoop ε hε⟧ chart)
      o (B (FreeGroup.of i)).unop (hB i)
    change @SMul.smul K C a.toSMul (B (FreeGroup.of i)).unop o.val=
      (hq.isCoveringMap.monodromy ⟦((actualPantsStem ε hε).map chart.continuous).trans
        (((actualPantsHorizontalLoop ε hε).map chart.continuous).trans
          ((actualPantsStem ε hε).map chart.continuous).symm)⟧ o).val at hH
    simpa only [actualPantsBoundaryLoop,Path.map_trans,←Path.map_symm] using hH
  have h₀ := hgen 0
  have h₁ := hgen 1
  dsimp only at h₀ h₁
  have hmono := actual_same_free_basis_literal_loop_word_supplied_monodromy a q hq
    (f.symm actualPantsBase) o B
    ⟦(actualPantsBoundaryLoop (-1) (by norm_num)).map chart.continuous⟧
    ⟦(actualPantsBoundaryLoop 1 (by norm_num)).map chart.continuous⟧ h₀ h₁
  obtain ⟨z,hz,γ,hγ,stem,hword⟩ :=
    actual_same_complex_chart_literal_cylinder_peripheral_conjugacy_source
      (1/4) (by norm_num) (by norm_num) ep hep
  refine ⟨z,hz,γ,hγ,stem.map f.symm.continuous,?_⟩
  have hh : Path.Homotopic.Quotient.mk
      (((actualPantsBoundaryLoop (-1) (by norm_num)).trans
        (actualPantsBoundaryLoop 1 (by norm_num)).symm).map chart.continuous)=
      Path.Homotopic.Quotient.mk ((stem.trans (γ.symm.trans stem.symm)).map chart.continuous) :=
    Quotient.sound (hword.map chart)
  change (Path.Homotopic.Quotient.mk
      (((actualPantsBoundaryLoop (-1) (by norm_num)).trans
        (actualPantsBoundaryLoop 1 (by norm_num)).symm).map chart.continuous))=
      Path.Homotopic.Quotient.mk ((stem.trans (γ.symm.trans stem.symm)).map chart.continuous) at hh
  simp only [Path.map_trans,←Path.map_symm,Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm] at hh
  simp only [Path.Homotopic.Quotient.mk'_eq_mk,Path.Homotopic.Quotient.mk''_eq_mk] at hmono
  rw [hh] at hmono
  exact hmono
