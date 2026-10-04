import Mathlib
import Mathlib.Topology.Semicontinuity.Michael
namespace CurveComplex
open Set
open Filter Topology
open scoped unitInterval
set_option maxHeartbeats 1000000

/-- Continuously narrow an actual band away from a closed forbidden set,
while preserving both prescribed terminal widths exactly. Terminal corners
may lie in the forbidden set; every earlier full width slice avoids it. -/
theorem actual_continuous_longitudinal_width_taper
    {S : Type} [TopologicalSpace S]
    (N : C(unitInterval × Icc (-1 : ℝ) 1, S))
    (J : Set S) (hJ : IsClosed J)
    (rPlus rMinus : ℝ)
    (hrPlus : 0 < rPlus ∧ rPlus ≤ 1)
    (hrMinus : 0 < rMinus ∧ rMinus ≤ 1)
    (hcenter : ∀ t, N (t, ⟨0, by norm_num⟩) ∉ J)
    (hterminal : ∀ w : Icc (-1 : ℝ) 1,
      -rMinus < (w : ℝ) → (w : ℝ) < rPlus → N (1, w) ∉ J) :
    ∃ βPlus βMinus : C(unitInterval, ℝ),
    ∃ hβ : ∀ t, (0 < βPlus t ∧ βPlus t ≤ 1) ∧
      (0 < βMinus t ∧ βMinus t ≤ 1),
      βPlus 1 = rPlus ∧ βMinus 1 = rMinus ∧
      ∀ t : unitInterval, (t : ℝ) < 1 → ∀ w : Icc (-1 : ℝ) 1,
        N (t, ⟨if (w : ℝ) ≤ 0 then βMinus t * (w : ℝ)
          else βPlus t * (w : ℝ), by
            split_ifs with hw
            · constructor <;> nlinarith [(hβ t).2.1, (hβ t).2.2,
                w.property.1, w.property.2]
            · constructor <;> nlinarith [(hβ t).1.1, (hβ t).1.2,
                w.property.1, w.property.2]⟩) ∉ J := by
  classical
  have one_sided {S : Type} [TopologicalSpace S]
      (N : C(unitInterval × unitInterval,S)) (J : Set S) (hJ : IsClosed J)
      (r : ℝ) (hr : 0<r ∧ r≤1)
      (hcenter : ∀ t,N (t,0)∉J)
      (hend : ∀ w : unitInterval,(w:ℝ)<r → N (1,w)∉J) :
      ∃ β : unitInterval → ℝ, Continuous β ∧
        (∀ t,0<β t ∧ β t≤1) ∧ β 1=r ∧
        ∀ t : unitInterval,t<1 → ∀ w : unitInterval,(w:ℝ)≤β t → N (t,w)∉J := by
    classical
    have hopen : IsOpen (N ⁻¹' Jᶜ) := hJ.isOpen_compl.preimage N.continuous
    have hprod : (Set.univ : Set unitInterval) ×ˢ ({0} : Set unitInterval) ⊆ N ⁻¹' Jᶜ := by
      rintro ⟨t,w⟩ ⟨ht,hw⟩
      obtain rfl := Set.mem_singleton_iff.mp hw
      exact hcenter t
    obtain ⟨U,V,hU,hV,hall,hzero,hUV⟩ := generalized_tube_lemma
      isCompact_univ isCompact_singleton hopen hprod
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hzero (Set.mem_singleton _)))
    let δ : ℝ := min (ε/2) (r/2)
    have hδ : 0<δ := lt_min (half_pos hε) (half_pos hr.1)
    have hδr : δ<r := (min_le_right _ _).trans_lt (by linarith [hr.1])
    have hδε : δ<ε := (min_le_left _ _).trans_lt (by linarith)
    have hglobal : ∀ t : unitInterval,∀ w : unitInterval,(w:ℝ)≤δ → N (t,w)∉J := by
      intro t w hw
      apply hUV
      refine ⟨hall (Set.mem_univ _),hball ?_⟩
      change dist (w:ℝ) 0<ε
      rw [Real.dist_eq,sub_zero,abs_of_nonneg w.property.1]
      exact hw.trans_lt hδε
    let C : unitInterval → Set ℝ := fun t => Icc δ r ∩
      ⋂ w : unitInterval, if N (t,w)∈J then Iic (w:ℝ) else univ
    have hCmem (t : unitInterval) (q : ℝ) : q∈C t ↔
        δ≤q ∧ q≤r ∧ ∀ w : unitInterval,(w:ℝ)<q → N (t,w)∉J := by
      constructor
      · rintro ⟨hq,hall⟩
        refine ⟨hq.1,hq.2,?_⟩
        intro w hw hb
        have hh := Set.mem_iInter.mp hall w
        simp only [if_pos hb,Set.mem_Iic] at hh
        linarith
      · rintro ⟨hq0,hqr,hs⟩
        refine ⟨⟨hq0,hqr⟩,Set.mem_iInter.mpr ?_⟩
        intro w
        by_cases hb : N (t,w)∈J
        · simp only [if_pos hb,Set.mem_Iic]
          exact le_of_not_gt (fun hh => hs w hh hb)
        · simp [hb]
    have hδC (t : unitInterval) : δ∈C t :=
      (hCmem t δ).mpr ⟨le_rfl,hδr.le,fun w hw => hglobal t w hw.le⟩
    let F : unitInterval → Set ℝ := fun t => if t=1 then {r} else C t
    have hnonempty (t : unitInterval) : (F t).Nonempty := by
      by_cases ht : t=1
      · exact ⟨r,by simp [F,ht]⟩
      · exact ⟨δ,by simpa [F,ht] using hδC t⟩
    have hconvex (t : unitInterval) : Convex ℝ (F t) := by
      by_cases ht : t=1
      · simpa [F,ht] using (convex_singleton r : Convex ℝ ({r}:Set ℝ))
      · simp only [F,if_neg ht]
        apply (convex_Icc δ r).inter
        apply convex_iInter
        intro w
        split_ifs
        · exact convex_Iic _
        · exact convex_univ
    have hclosed (t : unitInterval) : IsClosed (F t) := by
      by_cases ht : t=1
      · simpa [F,ht] using (isClosed_singleton : IsClosed ({r}:Set ℝ))
      · simp only [F,if_neg ht]
        apply isClosed_Icc.inter
        apply isClosed_iInter
        intro w
        split_ifs
        · exact isClosed_Iic
        · exact isClosed_univ
    have hhemi : LowerHemicontinuous F := by
      rw [lowerHemicontinuous_iff]
      intro t
      rw [lowerHemicontinuousAt_iff]
      intro W hW hmeet
      obtain ⟨z,hz,hzW⟩ := hmeet
      have hzbounds : δ≤z ∧ z≤r := by
        by_cases ht : t=1
        · have hzR : z=r := by simpa [F,ht] using hz
          rw [hzR]
          exact ⟨hδr.le,le_rfl⟩
        · have hh := (hCmem t z).mp (by simpa [F,ht] using hz)
          exact ⟨hh.1,hh.2.1⟩
      have hzsafe : ∀ w : unitInterval,(w:ℝ)<z → N (t,w)∉J := by
        by_cases ht : t=1
        · have hzR : z=r := by simpa [F,ht] using hz
          subst t
          simpa [hzR] using hend
        · exact ((hCmem t z).mp (by simpa [F,ht] using hz)).2.2
      by_cases hzδ : z=δ
      · have ht : t≠1 := by
          intro he
          have hzR : z=r := by simpa [F,he] using hz
          linarith
        have hne : ∀ᶠ t' in 𝓝 t, t' ≠ 1 :=
          (isClosed_singleton.isOpen_compl.mem_nhds ht)
        filter_upwards [hne] with t' ht'
        exact ⟨δ,by simpa [F,ht'] using hδC t',hzδ ▸ hzW⟩
      · have hδz : δ<z := lt_of_le_of_ne hzbounds.1 (Ne.symm hzδ)
        obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hzW)
        let s : ℝ := max δ (z-η/2)
        have hδs : δ ≤ s := le_max_left _ _
        have hsz : s<z := max_lt hδz (by linarith)
        have hsW : s∈W := hηball (by
          rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (by linarith)]
          have hh : z-η/2 ≤ s := le_max_right _ _
          linarith)
        have hs0 : 0 ≤ s := hδ.le.trans hδs
        have hs1 : s≤1 := hsz.le.trans (hzbounds.2.trans hr.2)
        let sw : unitInterval := ⟨s,hs0,hs1⟩
        have hcompact : ({t}:Set unitInterval) ×ˢ Icc (0:unitInterval) sw ⊆ N ⁻¹' Jᶜ := by
          rintro ⟨t',w⟩ ⟨ht',hw⟩
          obtain rfl := Set.mem_singleton_iff.mp ht'
          exact hzsafe w (lt_of_le_of_lt hw.2 hsz)
        obtain ⟨A,D,hA,hD,htA,hsub,hAD⟩ := generalized_tube_lemma
          isCompact_singleton isCompact_Icc hopen hcompact
        have hnear : ∀ᶠ t' in 𝓝 t,t'∈A := hA.mem_nhds (htA (Set.mem_singleton _))
        have hsC (t' : unitInterval) (ht' : t'∈A) : s∈C t' := by
          apply (hCmem t' s).mpr
          refine ⟨hδs,hsz.le.trans hzbounds.2,?_⟩
          intro w hw
          apply hAD
          exact ⟨ht',hsub ⟨w.property.1,hw.le⟩⟩
        by_cases ht : t=1
        · have hrW : r∈W := by
            have hzR : z=r := by simpa [F,ht] using hz
            rwa [hzR] at hzW
          filter_upwards [hnear] with t' ht'
          by_cases ht1 : t'=1
          · exact ⟨r,by simp [F,ht1],hrW⟩
          · exact ⟨s,by simpa [F,ht1] using hsC t' ht',hsW⟩
        · have hne : ∀ᶠ t' in 𝓝 t, t' ≠ 1 :=
            isClosed_singleton.isOpen_compl.mem_nhds ht
          filter_upwards [hnear,hne] with t' ht' ht1
          exact ⟨s,by simpa [F,ht1] using hsC t' ht',hsW⟩
    obtain ⟨μ,hμc,hμ⟩ := hhemi.exists_continuous_selection hnonempty hconvex hclosed
    have hμbounds (t : unitInterval) : δ≤μ t ∧ μ t≤r := by
      by_cases ht : t=1
      · have hh : μ t=r := by simpa [F,ht] using hμ t
        rw [hh]
        exact ⟨hδr.le,le_rfl⟩
      · exact ⟨((hCmem t _).mp (by simpa [F,ht] using hμ t)).1,
          ((hCmem t _).mp (by simpa [F,ht] using hμ t)).2.1⟩
    let β : unitInterval → ℝ := fun t => μ t*((1+(t:ℝ))/2)
    refine ⟨β,by dsimp [β]; fun_prop,?_,?_,?_⟩
    · intro t
      have hp : 0<μ t := hδ.trans_le (hμbounds t).1
      constructor
      · dsimp [β]
        exact mul_pos hp (by have ht0 := t.property.1; positivity)
      · dsimp [β]
        have hle := (hμbounds t).2.trans hr.2
        nlinarith [t.property.1,t.property.2]
    · have hh : μ 1=r := by simpa [F] using hμ 1
      dsimp [β]
      rw [hh]
      norm_num
    · intro t ht w hw
      have htne : t≠1 := ht.ne
      have hsafe := ((hCmem t _).mp (by simpa [F,htne] using hμ t)).2.2
      apply hsafe w
      have hp : 0<μ t := hδ.trans_le (hμbounds t).1
      have hlt : (t:ℝ)<1 := ht
      dsimp [β] at hw
      nlinarith

  let Nplus : C(unitInterval × unitInterval,S) :=
    ⟨fun z => N (z.1,⟨(z.2:ℝ),by constructor <;> linarith [z.2.property.1,z.2.property.2]⟩),by
      apply N.continuous.comp
      apply Continuous.prodMk continuous_fst
      apply Continuous.subtype_mk
      fun_prop⟩
  let Nminus : C(unitInterval × unitInterval,S) :=
    ⟨fun z => N (z.1,⟨-(z.2:ℝ),by constructor <;> linarith [z.2.property.1,z.2.property.2]⟩),by
      apply N.continuous.comp
      apply Continuous.prodMk continuous_fst
      apply Continuous.subtype_mk
      fun_prop⟩
  have hplusCenter : ∀ t,Nplus (t,0)∉J := by
    intro t
    simpa [Nplus] using hcenter t
  have hminusCenter : ∀ t,Nminus (t,0)∉J := by
    intro t
    simpa [Nminus] using hcenter t
  have hplusEnd : ∀ w : unitInterval,(w:ℝ)<rPlus → Nplus (1,w)∉J := by
    intro w hw
    exact hterminal ⟨(w:ℝ),by constructor <;> linarith [w.property.1,w.property.2]⟩
      (by linarith [hrMinus.1,w.property.1]) hw
  have hminusEnd : ∀ w : unitInterval,(w:ℝ)<rMinus → Nminus (1,w)∉J := by
    intro w hw
    exact hterminal ⟨-(w:ℝ),by constructor <;> linarith [w.property.1,w.property.2]⟩
      (by linarith) (by linarith [hrPlus.1,w.property.1])
  obtain ⟨bp,hbpC,hbp,hbp1,hbpClear⟩ :=
    one_sided Nplus J hJ rPlus hrPlus hplusCenter hplusEnd
  obtain ⟨bm,hbmC,hbm,hbm1,hbmClear⟩ :=
    one_sided Nminus J hJ rMinus hrMinus hminusCenter hminusEnd
  let βPlus : C(unitInterval,ℝ) := ⟨bp,hbpC⟩
  let βMinus : C(unitInterval,ℝ) := ⟨bm,hbmC⟩
  have hβ : ∀ t,(0<βPlus t ∧ βPlus t≤1) ∧ (0<βMinus t ∧ βMinus t≤1) :=
    fun t => ⟨hbp t,hbm t⟩
  refine ⟨βPlus,βMinus,hβ,hbp1,hbm1,?_⟩
  intro t ht w
  have htI : t<(1:unitInterval) := ht
  by_cases hw : (w:ℝ)≤0
  · let v : unitInterval := ⟨-(bm t*(w:ℝ)),by
      constructor
      · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hbm t).1.le hw)
      · nlinarith [(hbm t).1,(hbm t).2,w.property.1]⟩
    have hv : (v:ℝ)≤bm t := by
      dsimp [v]
      nlinarith [(hbm t).1,w.property.1]
    have hh := hbmClear t htI v hv
    simpa only [ite_eq_left hw,Nminus,ContinuousMap.coe_mk,v,Subtype.coe_mk,neg_neg,
      βMinus] using hh
  · let v : unitInterval := ⟨bp t*(w:ℝ),by
      constructor
      · exact mul_nonneg (hbp t).1.le (le_of_not_ge hw)
      · nlinarith [(hbp t).1,(hbp t).2,w.property.2]⟩
    have hv : (v:ℝ)≤bp t := by
      dsimp [v]
      nlinarith [(hbp t).1,w.property.2]
    have hh := hbpClear t htI v hv
    simpa only [ite_eq_right hw,Nplus,ContinuousMap.coe_mk,v,Subtype.coe_mk,
      βPlus] using hh

end CurveComplex
