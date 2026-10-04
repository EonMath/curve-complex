import CurveComplexGenusTwo.Cover.ActualWholeBankSectorSide
import Mathlib
open Set Metric Topology
namespace AlternatingSphereCover
/-- Explicit radial normalization of the two literal corner-crossing runs in
our pinned cut-disk square. Conjugating the verified boundary collar by the
inverse chart places it on the SAME original source run. No supplied chart or
normalization certificate is an assumption. -/
theorem actual_corner_boundary_run_radial_normalization :
    ∀ k : Fin 2,
    let o : ℝ × ℝ := if k=0 then (3/10,6/7) else (1/3,4/7)
    let L : (ℝ × ℝ) → (ℝ × ℝ) := if k=0 then
      fun v => (-(10/3)*v.1+7*v.2,(5/3)*v.1+(7/2)*v.2)
      else fun v => ((3/2)*v.1+(7/3)*v.2,(3/4)*v.1-(7/6)*v.2)
    let P : Set (unitInterval × unitInterval) := Set.ofPred (fun z => if k=0 then
      (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
      (z.1.val=0 ∧ 6/7≤z.2.val ∧ z.2.val≤1)
      else (z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
      (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1))
    ∃ h : (unitInterval × unitInterval) ≃ₜ (unitInterval × unitInterval),
      (∀ z, let w := (gaugeRescale
        (L '' (Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)))
        (closedBall (0 : ℝ × ℝ) 1) (L (z.1.val-o.1,z.2.val-o.2)));
        ((h z).1.val,(h z).2.val)=((w.1+1)/2,(w.2+1)/2)) ∧
      h '' P=Set.ofPred (fun z : unitInterval × unitInterval =>
        z.1.val=1 ∧ (1/4:ℝ)≤z.2.val ∧ z.2.val≤3/4) := by
  have hSquareRadialChart :
      ∀ o : ℝ × ℝ, (0<o.1 ∧ o.1<1 ∧ 0<o.2 ∧ o.2<1) →
      ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∃ H : (unitInterval × unitInterval) ≃ₜ (unitInterval × unitInterval),
        ∀ z, let w := (gaugeRescale
          (L '' (Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)))
          (closedBall (0 : ℝ × ℝ) 1) (L (z.1.val-o.1,z.2.val-o.2)));
          ((H z).1.val,(H z).2.val)=((w.1+1)/2,(w.2+1)/2) := by
    intro o ho L
    let r : Set (ℝ × ℝ) := Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)
    let s := L '' r
    let t : Set (ℝ × ℝ) := closedBall 0 1
    have hrc : Convex ℝ r := (convex_Icc _ _).prod (convex_Icc _ _)
    have hsc : Convex ℝ s := hrc.linear_image L.toLinearMap
    have hrcompact : IsCompact r := isCompact_Icc.prod isCompact_Icc
    have hscompact : IsCompact s := hrcompact.image L.continuous
    have hr0 : r∈𝓝 (0:ℝ × ℝ) := by
      have hopen := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        (show (0:ℝ × ℝ)∈Ioo (-o.1) (1-o.1) ×ˢ Ioo (-o.2) (1-o.2) from by
          change (-o.1<0 ∧ 0<1-o.1) ∧ (-o.2<0 ∧ 0<1-o.2)
          constructor <;> constructor <;> linarith [ho.1,ho.2.1,ho.2.2.1,ho.2.2.2])
      exact Filter.mem_of_superset hopen (by
        rintro z ⟨hz,hw⟩
        exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
    have hs0 : s∈𝓝 (0:ℝ × ℝ) := by
      have h := L.toHomeomorph.isOpenMap.image_mem_nhds hr0
      change L '' r∈𝓝 (L 0) at h
      simpa only [map_zero] using h
    have hsb : Bornology.IsVonNBounded ℝ s := NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
    have htc : Convex ℝ t := convex_closedBall _ _
    have ht0 : t∈𝓝 (0:ℝ × ℝ) := closedBall_mem_nhds _ (by norm_num)
    have htb : Bornology.IsVonNBounded ℝ t := NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall
    let g := gaugeRescaleHomeomorph s t hsc hs0 hsb htc ht0 htb
    have himage : g '' s=t := by
      have h := image_gaugeRescaleHomeomorph_closure hsc hs0 hsb htc ht0 htb
      rw [hscompact.isClosed.closure_eq,isClosed_closedBall.closure_eq] at h
      exact h
    let f : (unitInterval × unitInterval) → ↥r := fun z =>
      ⟨(z.1.val-o.1,z.2.val-o.2),⟨
        ⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
        ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩⟩
    let fi : ↥r → (unitInterval × unitInterval) := fun z =>
      (⟨z.val.1+o.1,⟨by linarith [z.property.1.1],by linarith [z.property.1.2]⟩⟩,
       ⟨z.val.2+o.2,⟨by linarith [z.property.2.1],by linarith [z.property.2.2]⟩⟩)
    let e : (unitInterval × unitInterval) ≃ₜ ↥r := {
      toFun := f
      invFun := fi
      left_inv := by intro z;apply Prod.ext <;> apply Subtype.ext <;> dsimp [f,fi] <;> ring
      right_inv := by intro z;apply Subtype.ext;apply Prod.ext <;> dsimp [f,fi] <;> ring
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_fst.subtype_val.sub continuous_const).prodMk
          (continuous_snd.subtype_val.sub continuous_const)
      continuous_invFun := by
        apply Continuous.prodMk
        · exact ((continuous_subtype_val.fst.add continuous_const).subtype_mk _)
        · exact ((continuous_subtype_val.snd.add continuous_const).subtype_mk _) }
    let G := e.trans ((L.toHomeomorph.image r).trans
      ((g.image s).trans (Homeomorph.setCongr himage)))
    have qData : ∃ Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval),
      ∀ z, (Q z).1.val = (z.val.1 + 1)/2 ∧ (Q z).2.val = (z.val.2 + 1)/2 := by
      have bounds (z : Metric.closedBall (0 : ℝ × ℝ) 1) :
          (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
        have h := z.property
        simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using h
      let F : Metric.closedBall (0 : ℝ × ℝ) 1 → unitInterval × unitInterval :=
        fun z => (⟨(z.val.1+1)/2,⟨by linarith [(bounds z).1.1],by linarith [(bounds z).1.2]⟩⟩,
          ⟨(z.val.2+1)/2,⟨by linarith [(bounds z).2.1],by linarith [(bounds z).2.2]⟩⟩)
      let G : unitInterval × unitInterval → Metric.closedBall (0 : ℝ × ℝ) 1 :=
        fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
          simp only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
          exact ⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
            ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩⟩
      have hF : Continuous F := by
        apply Continuous.prodMk
        · apply Continuous.subtype_mk
          exact ((continuous_fst.comp continuous_subtype_val).add_const 1).div_const 2
        · apply Continuous.subtype_mk
          exact ((continuous_snd.comp continuous_subtype_val).add_const 1).div_const 2
      have hG : Continuous G := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · exact ((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const
        · exact ((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const
      let Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval) := {
        toFun := F
        invFun := G
        left_inv := by
          intro z
          apply Subtype.ext
          apply Prod.ext
          all_goals (dsimp [F,G]; ring)
        right_inv := by
          intro z
          apply Prod.ext
          all_goals (apply Subtype.ext; dsimp [F,G]; ring)
        continuous_toFun := hF
        continuous_invFun := hG }
      exact ⟨Q,fun _ => ⟨rfl,rfl⟩⟩
    obtain ⟨Q,hQ⟩ := qData
    exact ⟨G.trans Q,fun z => by
      apply Prod.ext
      · exact (hQ (G z)).1
      · exact (hQ (G z)).2⟩
  let Lcorner0 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun v => (-(10/3)*v.1+7*v.2,(5/3)*v.1+(7/2)*v.2)
    invFun := fun v => ((3/20)*(2*v.2-v.1),(v.1+2*v.2)/14)
    left_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    right_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    map_add' := by intro v w;apply Prod.ext <;> dsimp <;> ring
    map_smul' := by intro c v;apply Prod.ext <;> dsimp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hCorner0ActualRadialChart := hSquareRadialChart
    (3/10,6/7) (by norm_num) Lcorner0
  let Lcorner1 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun v => ((3/2)*v.1+(7/3)*v.2,(3/4)*v.1-(7/6)*v.2)
    invFun := fun v => ((v.1+2*v.2)/3,(3/14)*(v.1-2*v.2))
    left_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    right_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    map_add' := by intro v w;apply Prod.ext <;> dsimp <;> ring
    map_smul' := by intro c v;apply Prod.ext <;> dsimp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hCorner1ActualRadialChart := hSquareRadialChart
    (1/3,4/7) (by norm_num) Lcorner1
  have hGaugeLinearTransport :
      ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∀ r : Set (ℝ × ℝ), ∀ x : ℝ × ℝ,
        gauge (L '' r) (L x)=gauge r x := by
    intro L r x
    have he : Set.ofPred (fun a : ℝ => a∈Ioi 0 ∧ a⁻¹ • L x∈L '' r)=
        Set.ofPred (fun a : ℝ => a∈Ioi 0 ∧ a⁻¹ • x∈r) := by
      ext a
      constructor
      · rintro ⟨ha,z,hz,hzx⟩
        have hz' : z=a⁻¹ • x := L.injective (by simpa using hzx)
        exact ⟨ha,hz' ▸ hz⟩
      · rintro ⟨ha,hx⟩
        exact ⟨ha,a⁻¹ • x,hx,by simp⟩
    rw [gauge_def',he,←gauge_def']
  have hShiftedSquareFrontier :
      ∀ o : ℝ × ℝ, ∀ z : unitInterval × unitInterval,
        (z.1.val-o.1,z.2.val-o.2)∈frontier
          (Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)) ↔
        z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1 := by
    intro o z
    rw [(isClosed_Icc.prod isClosed_Icc).frontier_eq,interior_prod_eq,interior_Icc,interior_Icc]
    constructor
    · rintro ⟨hz,hni⟩
      by_contra hn
      push Not at hn
      apply hni
      constructor <;> constructor
      · have h : 0<z.1.val := lt_of_le_of_ne z.1.property.1 (Ne.symm hn.1)
        linarith
      · have h : z.1.val<1 := lt_of_le_of_ne z.1.property.2 hn.2.1
        linarith
      · have h : 0<z.2.val := lt_of_le_of_ne z.2.property.1 (Ne.symm hn.2.2.1)
        linarith
      · have h : z.2.val<1 := lt_of_le_of_ne z.2.property.2 hn.2.2.2
        linarith
    · intro hz
      refine ⟨⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
        ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩,?_⟩
      rintro ⟨hx,hy⟩
      change -o.1<z.1.val-o.1 ∧ z.1.val-o.1<1-o.1 at hx
      change -o.2<z.2.val-o.2 ∧ z.2.val-o.2<1-o.2 at hy
      rcases hz with hz|hz|hz|hz <;> linarith
  have hCorner0Cone (z : unitInterval × unitInterval) :
      let w := Lcorner0 (z.1.val-3/10,z.2.val-6/7)
      2*abs w.2≤w.1 ↔ z.1.val≤3/10 ∧ 6/7≤z.2.val := by
    dsimp [Lcorner0]
    rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_mul,abs_le]
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
  have hCorner1Cone (z : unitInterval × unitInterval) :
      let w := Lcorner1 (z.1.val-1/3,z.2.val-4/7)
      2*abs w.2≤w.1 ↔ 1/3≤z.1.val ∧ 4/7≤z.2.val := by
    dsimp [Lcorner1]
    rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_mul,abs_le]
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
  have hRadialBoundaryCone :
      ∀ o : ℝ × ℝ, (0<o.1 ∧ o.1<1 ∧ 0<o.2 ∧ o.2<1) →
      ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∀ z : unitInterval × unitInterval,
        let r := Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)
        let w := L (z.1.val-o.1,z.2.val-o.2)
        let W := gaugeRescale (L '' r) (closedBall (0:ℝ × ℝ) 1) w
        (W.1=1 ∧ (-1/2:ℝ)≤W.2 ∧ W.2≤1/2) ↔
        ((z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1) ∧ 2*abs w.2≤w.1) := by
    intro o ho L z
    dsimp only
    let r : Set (ℝ × ℝ) := Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)
    let w := L (z.1.val-o.1,z.2.val-o.2)
    let t : Set (ℝ × ℝ) := closedBall 0 1
    let W := gaugeRescale (L '' r) t w
    change (W.1=1 ∧ (-1/2:ℝ)≤W.2 ∧ W.2≤1/2) ↔
      ((z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1) ∧ 2*abs w.2≤w.1)
    have hrc : Convex ℝ r := (convex_Icc _ _).prod (convex_Icc _ _)
    have hr0 : r∈𝓝 (0:ℝ × ℝ) := by
      have hopen := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        (show (0:ℝ × ℝ)∈Ioo (-o.1) (1-o.1) ×ˢ Ioo (-o.2) (1-o.2) from by
          change (-o.1<0 ∧ 0<1-o.1) ∧ (-o.2<0 ∧ 0<1-o.2)
          constructor <;> constructor <;> linarith [ho.1,ho.2.1,ho.2.2.1,ho.2.2.2])
      exact Filter.mem_of_superset hopen (by
        rintro v ⟨hv,hv'⟩
        exact ⟨⟨hv.1.le,hv.2.le⟩,⟨hv'.1.le,hv'.2.le⟩⟩)
    have hgt (v : ℝ × ℝ) : gauge t v=‖v‖ := by
      simp only [t,gauge_closedBall (by norm_num : (0:ℝ)≤1),div_one]
    have hWformula (hs : gauge (L '' r) w=1) : W=‖w‖⁻¹ • w := by
      change gaugeRescale (L '' r) t w=_
      rw [gaugeRescale_def,hs,hgt]
      simp only [one_div]
    constructor
    · rintro ⟨hWx,hWyl,hWyu⟩
      have hwne : w≠0 := by
        intro hw
        have hzero : W=0 := by dsimp [W];rw [hw,gaugeRescale_zero]
        have hc := congrArg Prod.fst hzero
        rw [hWx] at hc
        norm_num at hc
      have hwp : 0<‖w‖ := norm_pos_iff.mpr hwne
      have hWnorm : ‖W‖=1 := by
        rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hWx]
        norm_num
        rw [abs_le]
        constructor <;> linarith
      have hgs : gauge (L '' r) w=1 := by
        have hh := gauge_gaugeRescale' (L '' r) (show gauge t w≠0 from by rw [hgt];exact ne_of_gt hwp)
        change gauge t W=gauge (L '' r) w at hh
        rw [hgt,hWnorm] at hh
        exact hh.symm
      have hfr : (z.1.val-o.1,z.2.val-o.2)∈frontier r := by
        apply (gauge_eq_one_iff_mem_frontier hrc hr0).mp
        rw [←hGaugeLinearTransport L r]
        exact hgs
      have hb := (hShiftedSquareFrontier o z).mp hfr
      have hx : w.1=‖w‖ := by
        have hh := hWx
        rw [hWformula hgs] at hh
        change ‖w‖⁻¹*w.1=1 at hh
        have hh' : w.1/‖w‖=1 := by simpa only [inv_mul_eq_div] using hh
        have he := (div_eq_iff (ne_of_gt hwp)).mp hh'
        simpa using he
      have hy : -‖w‖/2≤w.2 ∧ w.2≤‖w‖/2 := by
        rw [hWformula hgs] at hWyl hWyu
        change (-1/2:ℝ)≤‖w‖⁻¹*w.2 at hWyl
        change ‖w‖⁻¹*w.2≤(1/2:ℝ) at hWyu
        have hl : (-1/2:ℝ)≤w.2/‖w‖ := by simpa only [inv_mul_eq_div] using hWyl
        have hu : w.2/‖w‖≤(1/2:ℝ) := by simpa only [inv_mul_eq_div] using hWyu
        have hl' := (le_div_iff₀ hwp).mp hl
        have hu' := (div_le_iff₀ hwp).mp hu
        constructor <;> linarith
      refine ⟨hb,?_⟩
      rw [←hx] at hy
      have habs : abs w.2≤w.1/2 := by
        apply abs_le.mpr
        constructor <;> linarith [hy.1,hy.2]
      linarith
    · rintro ⟨hb,hcone⟩
      have hfr := (hShiftedSquareFrontier o z).mpr hb
      have hgs : gauge (L '' r) w=1 := by
        rw [hGaugeLinearTransport L r]
        exact (gauge_eq_one_iff_mem_frontier hrc hr0).mpr hfr
      have hwne : w≠0 := by
        intro hw
        rw [hw,gauge_zero] at hgs
        norm_num at hgs
      have hxnonneg : 0≤w.1 := by nlinarith [abs_nonneg w.2]
      have hyle : abs w.2≤w.1 := by nlinarith [abs_nonneg w.2]
      have hnorm : ‖w‖=w.1 := by
        rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hxnonneg,max_eq_left hyle]
      have hxp : 0<w.1 := by rw [←hnorm];exact norm_pos_iff.mpr hwne
      rw [hWformula hgs,hnorm]
      change w.1⁻¹*w.1=1 ∧ (-1/2:ℝ)≤w.1⁻¹*w.2 ∧ w.1⁻¹*w.2≤1/2
      refine ⟨inv_mul_cancel₀ (ne_of_gt hxp),?_,?_⟩
      · rw [inv_mul_eq_div]
        apply (le_div_iff₀ hxp).mpr
        have hneg := neg_abs_le w.2
        linarith
      · rw [inv_mul_eq_div]
        apply (div_le_iff₀ hxp).mpr
        have hpos := le_abs_self w.2
        linarith
  obtain ⟨H0,hH0⟩ := hCorner0ActualRadialChart
  have hBand0 (z : unitInterval × unitInterval) :
      ((H0 z).1.val=1 ∧ (1/4:ℝ)≤(H0 z).2.val ∧ (H0 z).2.val≤3/4) ↔
      ((z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
       (z.1.val=0 ∧ 6/7≤z.2.val ∧ z.2.val≤1)) := by
    let w := Lcorner0 (z.1.val-3/10,z.2.val-6/7)
    let W := gaugeRescale
      (Lcorner0 '' (Icc (-(3/10:ℝ)) (1-3/10) ×ˢ Icc (-(6/7:ℝ)) (1-6/7)))
      (closedBall (0:ℝ × ℝ) 1) w
    have hh := hH0 z
    have hx : (H0 z).1.val=(W.1+1)/2 := congrArg Prod.fst hh
    have hy : (H0 z).2.val=(W.2+1)/2 := congrArg Prod.snd hh
    rw [hx,hy]
    have hband : ((W.1+1)/2=1 ∧ (1/4:ℝ)≤(W.2+1)/2 ∧ (W.2+1)/2≤3/4) ↔
        (W.1=1 ∧ (-1/2:ℝ)≤W.2 ∧ W.2≤1/2) := by
      constructor <;> rintro ⟨ha,hb,hc⟩ <;> refine ⟨?_,?_,?_⟩ <;> linarith
    rw [hband]
    have hrad := hRadialBoundaryCone (3/10,6/7) (by norm_num) Lcorner0 z
    change (W.1=1 ∧ (-1/2:ℝ)≤W.2 ∧ W.2≤1/2) ↔
      ((z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1) ∧ 2*abs w.2≤w.1) at hrad
    have hc := hCorner0Cone z
    change 2*abs w.2≤w.1 ↔ z.1.val≤3/10 ∧ 6/7≤z.2.val at hc
    rw [hrad,hc]
    constructor
    · rintro ⟨hb,hcx,hcy⟩
      rcases hb with hb|hb|hb|hb
      · exact Or.inr ⟨hb,hcy,z.2.property.2⟩
      · exfalso;linarith
      · exfalso;linarith
      · exact Or.inl ⟨hb,z.1.property.1,hcx⟩
    · rintro (⟨hy,hxl,hxu⟩|⟨hx,hyl,hyu⟩)
      · exact ⟨Or.inr (Or.inr (Or.inr hy)),hxu,by linarith⟩
      · exact ⟨Or.inl hx,by linarith,hyl⟩
  obtain ⟨H1,hH1⟩ := hCorner1ActualRadialChart
  have hBand1 (z : unitInterval × unitInterval) :
      ((H1 z).1.val=1 ∧ (1/4:ℝ)≤(H1 z).2.val ∧ (H1 z).2.val≤3/4) ↔
      ((z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
       (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1)) := by
    let w := Lcorner1 (z.1.val-1/3,z.2.val-4/7)
    let W := gaugeRescale
      (Lcorner1 '' (Icc (-(1/3:ℝ)) (1-1/3) ×ˢ Icc (-(4/7:ℝ)) (1-4/7)))
      (closedBall (0:ℝ × ℝ) 1) w
    have hh := hH1 z
    have hx : (H1 z).1.val=(W.1+1)/2 := congrArg Prod.fst hh
    have hy : (H1 z).2.val=(W.2+1)/2 := congrArg Prod.snd hh
    rw [hx,hy]
    have hband : ((W.1+1)/2=1 ∧ (1/4:ℝ)≤(W.2+1)/2 ∧ (W.2+1)/2≤3/4) ↔
        (W.1=1 ∧ (-1/2:ℝ)≤W.2 ∧ W.2≤1/2) := by
      constructor <;> rintro ⟨ha,hb,hc⟩ <;> refine ⟨?_,?_,?_⟩ <;> linarith
    rw [hband]
    have hrad := hRadialBoundaryCone (1/3,4/7) (by norm_num) Lcorner1 z
    change (W.1=1 ∧ (-1/2:ℝ)≤W.2 ∧ W.2≤1/2) ↔
      ((z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1) ∧ 2*abs w.2≤w.1) at hrad
    have hc := hCorner1Cone z
    change 2*abs w.2≤w.1 ↔ 1/3≤z.1.val ∧ 4/7≤z.2.val at hc
    rw [hrad,hc]
    constructor
    · rintro ⟨hb,hcx,hcy⟩
      rcases hb with hb|hb|hb|hb
      · exfalso;linarith
      · exact Or.inr ⟨hb,hcy,z.2.property.2⟩
      · exfalso;linarith
      · exact Or.inl ⟨hb,hcx,z.1.property.2⟩
    · rintro (⟨hy,hxl,hxu⟩|⟨hx,hyl,hyu⟩)
      · exact ⟨Or.inr (Or.inr (Or.inr hy)),hxl,by linarith⟩
      · exact ⟨Or.inr (Or.inl hx),by linarith,hyl⟩
  intro k
  fin_cases k
  · dsimp only
    refine ⟨H0,hH0,?_⟩
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hBand0 w).mpr hw
    · intro hz
      obtain ⟨w,rfl⟩ := H0.surjective z
      exact ⟨w,(hBand0 w).mp hz,rfl⟩
  · dsimp only
    refine ⟨H1,hH1,?_⟩
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hBand1 w).mpr hw
    · intro hz
      obtain ⟨w,rfl⟩ := H1.surjective z
      exact ⟨w,(hBand1 w).mp hz,rfl⟩
end AlternatingSphereCover
