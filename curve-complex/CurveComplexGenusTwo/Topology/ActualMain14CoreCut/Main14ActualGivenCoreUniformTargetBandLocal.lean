import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualComparisonPolarEmbeddingLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualEmbeddedAnnulusComplementComponentLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 5000000

-- The whole target near-core band lies in the SAME actual G interior image.
example (M : HyperellipticModel E S)
    (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
    (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/4 ∧
      ∀ z (u : Interval), |(u:ℝ)-1/2| ≤ δ →
        ∃ p : Circle × Interval, 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1 ∧ G p=(z,u) := by
  audit_main14_base3
    have hPolar : ∃ P : C(Circle × Interval,Plane), IsEmbedding P := by
      let f : C(Circle × Interval,ℂ) :=
        ⟨fun p => (1+(p.2:ℝ)) • (p.1:ℂ),by fun_prop⟩
      let P : C(Circle × Interval,Plane) :=
        ⟨fun p => Plane.mk (f p).re (f p).im,by fun_prop⟩
      have hi : Function.Injective P := by
        rintro ⟨z,u⟩ ⟨w,v⟩ he
        have hf : f (z,u)=f (w,v) := by
          apply Complex.ext
          · exact congrArg (fun x : Plane => x 0) he
          · exact congrArg (fun x : Plane => x 1) he
        have hu : u=v := by
          have hn := congrArg norm hf
          have hr : 0 < 1+(u:ℝ) := by linarith [u.property.1]
          have hs : 0 < 1+(v:ℝ) := by linarith [v.property.1]
          change ‖(1+(u:ℝ)) • (z:ℂ)‖ = ‖(1+(v:ℝ)) • (w:ℂ)‖ at hn
          simp only [norm_smul,Circle.norm_coe,mul_one,Real.norm_eq_abs,
            abs_of_pos hr,abs_of_pos hs] at hn
          apply Subtype.ext
          linarith
        subst v
        have hr : (1+(u:ℝ)) ≠ 0 := by linarith [u.property.1]
        have hz : (z:ℂ)=(w:ℂ) := by
          have hh := congrArg (fun x : ℂ => (1+(u:ℝ))⁻¹ • x) hf
          change (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (z:ℂ)) =
            (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (w:ℂ)) at hh
          simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hh
        exact Prod.ext (Subtype.ext hz) rfl
      exact ⟨P,(P.continuous.isClosedEmbedding hi).isEmbedding⟩
    letI : ChartedSpace Plane S := M.sphere.symm.chartedSpace
    have hOpen (q : C(Circle × Interval,S)) (hq : IsEmbedding q) :
        IsOpen (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
      let Qmiddle := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
      change IsOpen Qmiddle
      rw [isOpen_iff_forall_mem_open]
      rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩
      let k : Plane → S := fun x => q (z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1))
      let O : Set Plane := {x | x 0 ∈ Set.Ioo (-1:ℝ) 1 ∧ x 1 ∈ Set.Ioo (0:ℝ) 1}
      have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
        (isOpen_Ioo.preimage (by fun_prop))
      have hk : Continuous k := q.continuous.comp
        ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
          (continuous_projIcc.comp (by fun_prop)))
      have hki : InjOn k O := by
        intro x hx y hy he
        have hh := hq.injective he
        have h0 : Circle.exp (x 0)=Circle.exp (y 0) := mul_left_cancel (congrArg Prod.fst hh)
        have hlen : (1:ℝ)-(-1)<2*Real.pi := by linarith [Real.pi_gt_three]
        have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩ ⟨hy.1.1.le,hy.1.2.le⟩ h0
        have h1 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
        simp only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,
          Set.projIcc_of_mem zero_le_one ⟨hy.2.1.le,hy.2.2.le⟩] at h1
        ext i
        fin_cases i
        · exact h0'
        · exact h1
      have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
      have hsub : k '' O ⊆ Qmiddle := by
        rintro y ⟨x,hx,rfl⟩
        refine ⟨(z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1)),?_,rfl⟩
        change 0 < (Set.projIcc 0 1 zero_le_one (x 1):ℝ) ∧
          (Set.projIcc 0 1 zero_le_one (x 1):ℝ)<1
        simpa only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,Set.mem_Ioo] using hx.2
      refine ⟨k '' O,hsub,hopen,?_⟩
      refine ⟨Plane.mk 0 (t:ℝ),⟨by norm_num [O],⟨ht0,ht1⟩⟩,?_⟩
      simp [k,Set.projIcc_of_mem zero_le_one t.property]

    obtain ⟨P,hP⟩ := hPolar
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by rw [M.cover.branch_card];norm_num)
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=2+1) := ⟨by simp⟩
    let chart := stereographic' 2 (M.sphere w)
    have hs : chart.source={M.sphere w}ᶜ := stereographic'_source _
    have ht : chart.target=Set.univ := stereographic'_target _
    let es : {x : S // x ≠ w} ≃ₜ chart.source := M.sphere.subtype
      (fun x => by simp only [hs,Set.mem_compl_iff,Set.mem_singleton_iff,M.sphere.injective.eq_iff])
    let e : {x : S // x ≠ w} ≃ₜ Plane := es.trans
      (chart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
    let Φ : C(Circle × Interval,S) := ⟨fun p => (e.symm (P p)).val,
      continuous_subtype_val.comp (e.symm.continuous.comp P.continuous)⟩
    have hΦ : IsEmbedding Φ := IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hP)
    let c : Interval := ⟨1/2,by norm_num⟩
    let O := G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    let Q : C(Circle × Interval,S) := Φ.comp G
    have hQ : IsEmbedding Q := hΦ.comp hGe
    have hEq : O=Φ ⁻¹' (Q '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
      ext x
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hp,rfl⟩
      · rintro ⟨p,hp,he⟩
        exact ⟨p,hp,hΦ.injective he⟩
    have ho : IsOpen O := by
      rw [hEq]
      have hopen := hOpen Q hQ
      have he : {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}=
          Set.univ ×ˢ Set.Ioo (0:Interval) 1 := by ext p;simp
      rw [he] at hopen
      exact hopen.preimage Φ.continuous
    have hmid : (Set.univ : Set Circle) ×ˢ {c} ⊆ O := by
      rintro ⟨z,u⟩ ⟨hz,hu⟩
      have he : u=c := hu
      subst u
      refine ⟨(r.symm z,c),⟨Set.mem_univ _,?_⟩,?_⟩
      · constructor
        · change (0:ℝ)<1/2;norm_num
        · change (1/2:ℝ)<1;norm_num
      · rw [hcore,r.apply_symm_apply]
    obtain ⟨D,V,hD,hV,hall,hcV,hDV⟩ := generalized_tube_lemma
      (isCompact_univ : IsCompact (Set.univ : Set Circle))
      (isCompact_singleton : IsCompact ({c}:Set Interval)) ho hmid
    let clip : ℝ → Interval := Set.projIcc 0 1 (by norm_num)
    have hclip : Continuous clip := continuous_projIcc
    have hpre : IsOpen (clip ⁻¹' V) := hV.preimage hclip
    have hcclip : clip (1/2)=c := Set.projIcc_of_mem (by norm_num)
      (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
    have hcpre : (1/2:ℝ) ∈ clip ⁻¹' V := by
      change clip (1/2) ∈ V
      rw [hcclip]
      exact hcV (Set.mem_singleton c)
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre (1/2) hcpre
    let δ : ℝ := min (ε/2) (1/8)
    have hd : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hsmall : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    refine ⟨δ,hd,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
    intro z u hu
    have hb : (u:ℝ) ∈ Metric.ball (1/2) ε := by
      rw [Metric.mem_ball,Real.dist_eq]
      exact hu.trans_lt hsmall
    have hv : u ∈ V := by
      have hh := hball hb
      change clip (u:ℝ) ∈ V at hh
      have huclip : clip (u:ℝ)=u := Set.projIcc_of_mem (by norm_num) u.property
      rw [huclip] at hh
      exact hh
    have hmem : (z,u) ∈ O := hDV (show (z,u) ∈ D ×ˢ V from ⟨hall (Set.mem_univ z),hv⟩)
    obtain ⟨p,hp,he⟩ := hmem
    exact ⟨p,by exact hp.2.1,by exact hp.2.2,he⟩
end CurveComplex.HyperellipticModel
